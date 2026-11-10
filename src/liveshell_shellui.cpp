/*
 * liveshell_shellui.cpp — LiveShell: PS5 animated wallpaper, the part injected into SceShellUI.
 * The daemon (liveshell_daemon.cpp) injects this as an ELF. GPL-3.0; built on OnionHEN
 * (aydencharles/onionHEN) — its injector, detour library, and the way it drives ShellUI's Mono.
 *
 * Plays the user's video behind the home screen using Sony's own PUI.UI3.VideoView + Sce.Vsh.Video
 * VideoPlayer, added to the BGLayer scene (BGLayerPlugin.RootWidget). Hard-won rules:
 *   - every BGLayer/video call on ShellUI's UI thread (we detour PUI.Application.Update)
 *   - pin every Mono object we keep a raw pointer to (the GC moves objects)
 *   - never call VideoPlayer.GetPlayerStatus from the UI thread (deadlock)
 *   - SetLoop(true) on view.VideoPlayer a moment after start; if a loop still ends, Play(0)
 *   - Full HD video only (1080p, up to 60 fps); 4K does not open in ShellUI's player
 *
 * The daemon writes the clip path to /system_tmp/liveshell/video.txt (ShellUI cannot read /data; the
 * video folder is nullfs-mounted into the sandboxes at /system_ex/vsh_asset/wallpaper).
 * Log: /system_tmp/liveshell/shellui.log.
 */
#include <atomic>
#include <cmath>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cctype>
#include <cstring>
#include <string>
#include <dirent.h>
#include <fcntl.h>
#include <initializer_list>
#include <pthread.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <time.h>
#include <unistd.h>

#include <ps5/kernel.h>

#include <onion/detour.h>

extern "C" {
int       get_module_handle(pid_t pid, const char* module_name);
uintptr_t set_ucred_to_ptrace(void);
uintptr_t set_proc_authid(pid_t pid, uintptr_t new_authid);
int       sceKernelSendNotificationRequest(int, void*, size_t, int);
}

// libonion_detour reads these as weak externs that the host module must define. Left undefined,
// the weak symbol sits at address 0 and the first InstallDetour crashes ShellUI.
int (*sceKernelMprotect)(void* addr, size_t len, int prot) = nullptr;
bool has_hv_bypass = false;

namespace {

constexpr const char* kPathFile   = "/system_tmp/liveshell/video.txt";
constexpr const char* kOptsFile   = "/system_tmp/liveshell/opts.txt"; // the small settings, "name<TAB>value" lines
constexpr const char* kLogFile    = "/system_tmp/liveshell/shellui.log";
constexpr const char* kGuardFile  = "/system_tmp/liveshell/video_trying";
constexpr const char* kStatusFile = "/system_tmp/liveshell/status.txt";
constexpr const char* kDimFile    = "/system_tmp/liveshell/dim.txt";
constexpr const char* kVolumeFile = "/system_tmp/liveshell/volume.txt";

// /system_tmp holds only ~33 files for the whole console (issue #14), so the small settings are lines of one
// file, opts.txt. opt_open("/system_tmp/liveshell/dim.txt") gives that one value, read like the file was.
struct OptFile {
	char   v[128];
	size_t pos;
};

OptFile* opt_open(const char* path) {
	const char* base = strrchr(path, '/');
	base             = base != nullptr ? base + 1 : path;
	FILE* f          = fopen(kOptsFile, "r");
	if (f == nullptr) {
		return nullptr;
	}
	static thread_local OptFile slots[4];
	static thread_local int     slot = 0;
	char                        line[256];
	OptFile*                    out = nullptr;
	const size_t                bl  = strlen(base);
	while (out == nullptr && fgets(line, sizeof(line), f) != nullptr) {
		if (strncmp(line, base, bl) == 0 && line[bl] == '\t') {
			out = &slots[slot = (slot + 1) % 4];
			snprintf(out->v, sizeof(out->v), "%s", line + bl + 1);
			out->pos = 0;
		}
	}
	fclose(f);
	return out;
}

// The readers only ever scan "%d" fields: one int per "%d" in fmt, like fscanf's count.
int opt_scanf(OptFile* f, const char* fmt, ...) {
	va_list ap;
	va_start(ap, fmt);
	int         got = 0;
	const char* at  = f->v + f->pos;
	for (const char* c = fmt; (c = strstr(c, "%d")) != nullptr; c += 2) {
		char*      end = nullptr;
		const long n   = strtol(at, &end, 10);
		if (end == at) {
			break;
		}
		*va_arg(ap, int*) = static_cast<int>(n);
		at                = end;
		++got;
	}
	va_end(ap);
	f->pos = static_cast<size_t>(at - f->v);
	return got;
}

int opt_getc(OptFile* f) {
	return f->v[f->pos] != 0 ? static_cast<unsigned char>(f->v[f->pos++]) : EOF;
}

void opt_close(OptFile*) {}
constexpr off_t       kLogMaxSize = 12 * 1024; // ShellUI's files stop growing at ~16 KB (test v11-9)

// ---- logging ---------------------------------------------------------------------------------
int  g_log   = -1;
long g_t0_ms = 0;
int  g_tick  = 0; // UI frames since injection
std::atomic<int> g_vol_req{100}; // % sound of clips that have it (volume.txt)
int              g_vol_applied = -1;
bool             g_clip_silent = false; // the playing clip has no sound track
volatile bool    g_stalled     = false; // the video stopped moving (e.g. after rest mode): restart it
float            g_aud_now     = 0.0f;  // the playing clip's volume right now (fades toward the setting)
int              g_aud_set     = -1;    // last value sent to SetVolume
bool             g_aud_muted   = false; // SetIsMuted state of the playing clip
volatile bool    g_focus_new   = false; // a tile was just highlighted: decide about the PS5 music now

long now_ms() {
	timespec ts {};
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return static_cast<long>(ts.tv_sec) * 1000 + ts.tv_nsec / 1000000;
}

// ShellUI may only write ~16 KB of files per run (status.txt vanished and the log froze mid-session,
// test v11-8), so status, focus and log lines go to the payload over a local UDP socket instead:
// "S<status>", "F<title id>", "L<log line>". Files are only the fallback.
int         g_ui_sock = -1;
sockaddr_in g_ui_addr {};

void ui_channel_open() {
	g_ui_sock = socket(AF_INET, SOCK_DGRAM, 0);
	if (g_ui_sock >= 0) {
		g_ui_addr.sin_family      = AF_INET;
		g_ui_addr.sin_port        = htons(9051);
		g_ui_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	}
}

bool to_payload(char kind, const char* text, size_t len) {
	if (g_ui_sock < 0) {
		return false;
	}
	char buf[1500];
	if (len > sizeof(buf) - 1) {
		len = sizeof(buf) - 1;
	}
	buf[0] = kind;
	memcpy(buf + 1, text, len);
	if (sendto(g_ui_sock, buf, len + 1, 0, reinterpret_cast<sockaddr*>(&g_ui_addr), sizeof(g_ui_addr)) ==
	    static_cast<ssize_t>(len + 1)) {
		return true;
	}
	// Broken (rest mode): a new socket, at most once a second, then try again.
	static long last_reopen = 0;
	if (now_ms() - last_reopen < 1000) {
		return false;
	}
	last_reopen = now_ms();
	close(g_ui_sock);
	ui_channel_open();
	return g_ui_sock >= 0 &&
	       sendto(g_ui_sock, buf, len + 1, 0, reinterpret_cast<sockaddr*>(&g_ui_addr), sizeof(g_ui_addr)) ==
	           static_cast<ssize_t>(len + 1);
}

void wp_log(const char* fmt, ...) {
	if (g_log < 0 && g_ui_sock < 0) {
		return;
	}
	char line[1400];
	const int head = snprintf(line, sizeof(line), "[%6ld ms] ", now_ms() - g_t0_ms);
	va_list   args;
	va_start(args, fmt);
	int n = vsnprintf(line + head, sizeof(line) - 1 - head, fmt, args);
	va_end(args);
	if (n < 0) {
		return;
	}
	n += head;
	if (n > static_cast<int>(sizeof(line)) - 2) {
		n = static_cast<int>(sizeof(line)) - 2;
	}
	line[n++] = '\n';
	if (to_payload('L', line, static_cast<size_t>(n)) || g_log < 0) {
		return;
	}
	struct stat st {};
	if (fstat(g_log, &st) == 0 && st.st_size > kLogMaxSize) {
		(void)ftruncate(g_log, 0);
		(void)lseek(g_log, 0, SEEK_SET);
	}
	(void)write(g_log, line, static_cast<size_t>(n));
}

// What the daemon sees: playing <path> / starting / stopping / stopped / failed <rc>.
char g_last_status[600] = {};

void write_status(const char* fmt, ...) {
	char    text[600];
	va_list args;
	va_start(args, fmt);
	const int n = vsnprintf(text, sizeof(text) - 1, fmt, args);
	va_end(args);
	if (n < 0) {
		return;
	}
	const size_t len = strlen(text);
	snprintf(g_last_status, sizeof(g_last_status), "%s", text);
	if (!to_payload('S', text, len)) {
		text[len]    = '\n';
		const int fd = open(kStatusFile, O_WRONLY | O_CREAT | O_TRUNC, 0666);
		if (fd >= 0) {
			(void)write(fd, text, len + 1);
			close(fd);
		}
		text[len] = 0;
	}
	wp_log("status: %s", text);
}

void notify(const char* text) {
	struct {
		char unused[45];
		char message[3075];
	} req = {};
	snprintf(req.message, sizeof(req.message), "%s", text);
	sceKernelSendNotificationRequest(0, &req, sizeof(req), 0);
}

// ---- Mono ------------------------------------------------------------------------------------
using Obj = void*;
Obj    (*mono_get_root_domain)();
Obj    (*mono_thread_attach)(Obj domain);
Obj    (*mono_domain_assembly_open)(Obj domain, const char* name);
Obj    (*mono_assembly_get_image)(Obj assembly);
Obj    (*mono_class_from_name)(Obj image, const char* name_space, const char* name);
Obj    (*mono_class_get_method_from_name)(Obj klass, const char* name, int param_count);
Obj    (*mono_class_get_property_from_name)(Obj klass, const char* name);
Obj    (*mono_class_get_field_from_name)(Obj klass, const char* name);
Obj    (*mono_class_get_parent)(Obj klass);
Obj    (*mono_property_get_get_method)(Obj prop);
Obj    (*mono_property_get_set_method)(Obj prop);
Obj    (*mono_runtime_invoke)(Obj method, Obj obj, void** params, Obj* exc);
Obj    (*mono_object_new)(Obj domain, Obj klass);
Obj    (*mono_string_new)(Obj domain, const char* text);
void*  (*mono_object_unbox)(Obj obj);
Obj    (*mono_object_to_string)(Obj obj, Obj* exc);
char*  (*mono_string_to_utf8)(Obj str);
uint32_t (*mono_gchandle_new)(Obj obj, int pinned);
int64_t (*mono_gc_get_heap_size)()                          = nullptr; // optional: memory notes (kept players)
int64_t (*mono_gc_get_used_size)()                          = nullptr; // optional: memory notes - what is really alive
int (*sceKernelAvailableFlexibleMemorySize)(size_t* size) = nullptr; // optional: memory notes (kept players)
Obj    (*mono_method_desc_new)(const char* name, int include_namespace);
Obj    (*mono_method_desc_search_in_class)(Obj desc, Obj klass);
void   (*mono_method_desc_free)(Obj desc);
void*  (*mono_compile_method)(Obj method);
void   (*mono_field_get_value)(Obj obj, Obj field, void* value);
void   (*mono_field_set_value)(Obj obj, Obj field, void* value);
Obj    (*mono_get_corlib)();
void*  (*mono_class_get_type)(Obj klass);
Obj    (*mono_type_get_object)(Obj domain, void* type);
Obj    (*mono_method_get_object)(Obj domain, Obj method, Obj klass);
// Optional (diagnostics only): list a class's properties.
Obj         (*mono_class_get_properties)(Obj klass, void** iter);
const char* (*mono_property_get_name)(Obj prop);
Obj         (*mono_class_get_methods)(Obj klass, void** iter);
const char* (*mono_method_get_name)(Obj method);
int         (*mono_image_get_table_rows)(Obj image, int table);
Obj         (*mono_object_get_class)(Obj obj);
Obj         (*mono_class_get_fields)(Obj klass, void** iter);
const char* (*mono_field_get_name)(Obj field);
Obj         (*mono_method_signature)(Obj method);
Obj         (*mono_signature_get_return_type)(Obj sig);
char*       (*mono_type_get_name)(Obj type);
Obj         (*mono_class_from_mono_type)(Obj type);
int         (*mono_class_is_enum)(Obj klass);
int         (*mono_class_is_valuetype)(Obj klass);
Obj         (*mono_class_vtable)(Obj domain, Obj klass);
void        (*mono_field_static_get_value)(Obj vtable, Obj field, void* value);
Obj         (*mono_signature_get_params)(Obj sig, void** iter);
void        (*mono_method_get_param_names)(Obj method, const char** names);
Obj         (*mono_class_get)(Obj image, uint32_t token);
#ifdef LIVESHELL_RESEARCH_RETRO
Obj         (*mono_array_new)(Obj domain, Obj eclass, uintptr_t n);
Obj         (*mono_get_byte_class)();
#endif
#ifdef LIVESHELL_RESEARCH_DUMP
void        (*mono_assembly_foreach)(void (*func)(void* assembly, void* data), void* data);
const char* (*mono_image_get_name)(Obj image);
#endif
const char* (*mono_class_get_name)(Obj klass);

std::atomic<const char*> g_step{"start"};

// The class probes (every property / field / method of Sony's classes, used to write this file) stay out
// of a release's log: true only for development builds.
constexpr bool kProbeLogs = false;

// Heartbeat: if our thread crashes at a step, the heartbeat stops at the same moment; if it is stuck
// in a step while ShellUI keeps running until something kills it, the heartbeat keeps going.
void* heartbeat_thread(void*) {
	const char* last = nullptr;
	for (int i = 0; i < 100; ++i) { // ~70 s: a new step at once, the same step every 10 s
		const char* step = g_step.load();
		if (step != last || i % 10 == 0) {
			wp_log("heartbeat, step: %s", step);
			last = step;
		}
		usleep(i < 40 ? 250 * 1000 : 1000 * 1000);
	}
	return nullptr;
}

// Early after power-on (issue #16) the home screen died during these lookups: log each one then, so the last
// line names the call that killed it. Later starts stay quiet.
bool early_boot() {
	timespec up {};
	clock_gettime(CLOCK_MONOTONIC, &up);
	return up.tv_sec < 300;
}

template <typename T>
bool resolve(int handle, T& fn, const char* name) {
	g_step.store(name);
	static const bool early = early_boot();
	if (early) {
		wp_log("early boot: dlsym %s", name);
	}
	fn = reinterpret_cast<T>(kernel_dynlib_dlsym(-1, static_cast<uint32_t>(handle), name));
	if (fn == nullptr) {
		wp_log("missing Mono symbol: %s", name);
	}
	return fn != nullptr;
}
#define RESOLVE(f) ok &= resolve(lib, f, #f)

// Caller holds the raised authid (get_module_handle / dlsym across modules need it).
bool resolve_kernel() {
	g_step.store("get_module_handle(libkernel_sys)");
	const int lib = get_module_handle(getpid(), "libkernel_sys.sprx");
	if (lib <= 0) {
		wp_log("libkernel_sys handle %d", lib);
		return false;
	}
	sceKernelMprotect = reinterpret_cast<int (*)(void*, size_t, int)>(
	    kernel_dynlib_dlsym(-1, static_cast<uint32_t>(lib), "sceKernelMprotect"));
	sceKernelAvailableFlexibleMemorySize = reinterpret_cast<int (*)(size_t*)>(
	    kernel_dynlib_dlsym(-1, static_cast<uint32_t>(lib), "sceKernelAvailableFlexibleMemorySize"));
	wp_log("libkernel_sys handle %d, sceKernelMprotect %p, flexible memory query %p", lib, reinterpret_cast<void*>(sceKernelMprotect),
	       reinterpret_cast<void*>(sceKernelAvailableFlexibleMemorySize));
	return sceKernelMprotect != nullptr;
}

bool resolve_mono() {
	g_step.store("get_module_handle(libmonosgen)");
	wp_log("looking up libmonosgen");
	const int lib = get_module_handle(getpid(), "libmonosgen-2.0.sprx");
	wp_log("libmonosgen handle %d, resolving symbols", lib);
	bool            ok         = lib > 0;
	if (ok) {
		RESOLVE(mono_get_root_domain);
		RESOLVE(mono_thread_attach);
		RESOLVE(mono_domain_assembly_open);
		RESOLVE(mono_assembly_get_image);
		RESOLVE(mono_class_from_name);
		RESOLVE(mono_class_get_method_from_name);
		RESOLVE(mono_class_get_property_from_name);
		RESOLVE(mono_class_get_field_from_name);
		RESOLVE(mono_class_get_parent);
		RESOLVE(mono_property_get_get_method);
		RESOLVE(mono_property_get_set_method);
		RESOLVE(mono_runtime_invoke);
		RESOLVE(mono_object_new);
		RESOLVE(mono_string_new);
		RESOLVE(mono_object_unbox);
		RESOLVE(mono_object_to_string);
		RESOLVE(mono_string_to_utf8);
		RESOLVE(mono_gchandle_new);
		resolve(lib, mono_gc_get_heap_size, "mono_gc_get_heap_size"); // optional
		resolve(lib, mono_gc_get_used_size, "mono_gc_get_used_size"); // optional
		RESOLVE(mono_method_desc_new);
		RESOLVE(mono_method_desc_search_in_class);
		RESOLVE(mono_method_desc_free);
		RESOLVE(mono_compile_method);
		RESOLVE(mono_field_get_value);
		RESOLVE(mono_field_set_value);
		RESOLVE(mono_get_corlib);
		RESOLVE(mono_class_get_type);
		RESOLVE(mono_type_get_object);
		RESOLVE(mono_method_get_object);
		resolve(lib, mono_class_get_properties, "mono_class_get_properties");
		resolve(lib, mono_property_get_name, "mono_property_get_name");
		resolve(lib, mono_class_get_methods, "mono_class_get_methods");
		resolve(lib, mono_method_get_name, "mono_method_get_name");
		resolve(lib, mono_image_get_table_rows, "mono_image_get_table_rows");
		resolve(lib, mono_object_get_class, "mono_object_get_class");
		resolve(lib, mono_class_get_fields, "mono_class_get_fields");
		resolve(lib, mono_field_get_name, "mono_field_get_name");
		resolve(lib, mono_method_signature, "mono_method_signature");
		resolve(lib, mono_signature_get_return_type, "mono_signature_get_return_type");
		resolve(lib, mono_type_get_name, "mono_type_get_name");
		resolve(lib, mono_class_from_mono_type, "mono_class_from_mono_type");
		resolve(lib, mono_class_is_enum, "mono_class_is_enum");
		resolve(lib, mono_class_is_valuetype, "mono_class_is_valuetype");
		resolve(lib, mono_class_vtable, "mono_class_vtable");
		resolve(lib, mono_field_static_get_value, "mono_field_static_get_value");
		resolve(lib, mono_signature_get_params, "mono_signature_get_params");
		resolve(lib, mono_method_get_param_names, "mono_method_get_param_names");
		resolve(lib, mono_class_get, "mono_class_get");
		resolve(lib, mono_class_get_name, "mono_class_get_name");
#ifdef LIVESHELL_RESEARCH_RETRO
		resolve(lib, mono_array_new, "mono_array_new");
		resolve(lib, mono_get_byte_class, "mono_get_byte_class");
#endif
#ifdef LIVESHELL_RESEARCH_DUMP
		resolve(lib, mono_assembly_foreach, "mono_assembly_foreach");
		resolve(lib, mono_image_get_name, "mono_image_get_name");
#endif
	}
	wp_log("libmonosgen handle %d, symbols %s", lib, ok ? "ok" : "MISSING");
	return ok;
}

#undef RESOLVE

Obj g_domain = nullptr;

// ---- Mono helpers ----------------------------------------------------------------------------

void log_exception(const char* what, Obj exc) {
	if (exc == nullptr) {
		return;
	}
	Obj         inner = nullptr;
	Obj         text  = mono_object_to_string(exc, &inner);
	const char* utf8  = text != nullptr ? mono_string_to_utf8(static_cast<char*>(text)) : nullptr;
	wp_log("%s threw: %s", what, utf8 != nullptr ? utf8 : "(no text)");
}

bool invoke(Obj method, Obj obj, void** args, const char* what, Obj* result = nullptr) {
	if (method == nullptr) {
		wp_log("no method for %s", what);
		return false;
	}
	Obj exc = nullptr;
	Obj ret = mono_runtime_invoke(method, obj, args, &exc);
	log_exception(what, exc);
	if (result != nullptr) {
		*result = exc == nullptr ? ret : nullptr;
	}
	return exc == nullptr;
}

Obj property_get(Obj klass, Obj obj, const char* name) {
	Obj prop = mono_class_get_property_from_name(klass, name);
	Obj get  = prop != nullptr ? mono_property_get_get_method(prop) : nullptr;
	if (get == nullptr) {
		wp_log("no getter %s", name);
		return nullptr;
	}
	Obj exc    = nullptr;
	Obj result = mono_runtime_invoke(get, obj, nullptr, &exc);
	log_exception(name, exc);
	return exc != nullptr ? nullptr : result;
}

bool property_set(Obj klass, Obj obj, const char* name, void* value) {
	Obj prop = mono_class_get_property_from_name(klass, name);
	Obj set  = prop != nullptr ? mono_property_get_set_method(prop) : nullptr;
	if (set == nullptr) {
		wp_log("no setter %s", name);
		return false;
	}
	void* args[1] = {value};
	Obj   exc     = nullptr;
	mono_runtime_invoke(set, obj, args, &exc);
	log_exception(name, exc);
	return exc == nullptr;
}

// ---- video sound (test v11-12) ----------------------------------------------------------------
// The clip's sound plays, and Sony's home music goes quiet by itself while our player runs (the
// player suppresses the system BGM). It was quiet though: read the player's volume and raise it.
const char* type_name_of(Obj type) {
	const char* n = type != nullptr && mono_type_get_name != nullptr ? mono_type_get_name(type) : nullptr;
	return n != nullptr ? n : "?";
}

const char* param0_type(Obj method) {
	if (method == nullptr || mono_method_signature == nullptr || mono_signature_get_params == nullptr) {
		return "?";
	}
	void* iter = nullptr;
	return type_name_of(mono_signature_get_params(mono_method_signature(method), &iter));
}

// Sound setting on the playing clip's player. VideoPlayer.SetVolume takes an int 0..100 (100 by
// default, test v11-12); Mute also sets SetIsMuted so nothing at all comes through.
// Our player silences the PS5's background music while it plays (a game's own theme, e.g. ASTRO's
// PLAYROOM, played ~0.5 s and stopped, test v11-14). Muted: let that music play on.
void set_bgm_suppression(Obj klass, Obj player, bool muted) {
	bool  disabled = muted;
	void* args[1]  = {&disabled};
	invoke(mono_class_get_method_from_name(klass, "SetBGMSuppressionDisabled", 1), player, args,
	       "SetBGMSuppressionDisabled");
}

// fast.txt lists clips without a sound track as "!<path>" (the payload reads the mp4).
bool clip_is_silent(const char* path) {
	FILE* f = fopen("/system_tmp/liveshell/fast.txt", "r");
	if (f == nullptr) {
		return false;
	}
	char line[600];
	bool silent = false;
	while (!silent && fgets(line, sizeof(line), f) != nullptr) {
		line[strcspn(line, "\r\n")] = 0;
		silent = line[0] == '!' && strcmp(line + 1, path) == 0;
	}
	fclose(f);
	return silent;
}

void player_volume(Obj klass, Obj player, int percent) {
	int   v       = percent;
	void* args[1] = {&v};
	invoke(mono_class_get_method_from_name(klass, "SetVolume", 1), player, args, "SetVolume");
}

void player_mute(Obj klass, Obj player, bool muted) {
	bool  m       = muted;
	void* args[1] = {&m};
	invoke(mono_class_get_method_from_name(klass, "SetIsMuted", 1), player, args, "SetIsMuted");
}

// Mute + current fade volume + BGM suppression on a player. Init/Play RESET mute and volume (test
// v11-17: set before Init, read back unmuted at 100), so this runs before Init, right after Play and
// again when the player settles (frame 15).
void assert_sound(Obj klass, Obj player) {
	g_aud_muted = g_vol_req.load() == 0;
	player_mute(klass, player, g_aud_muted);
	g_aud_set = static_cast<int>(g_aud_now + 0.5f);
	player_volume(klass, player, g_aud_set);
	set_bgm_suppression(klass, player, g_aud_muted || g_clip_silent);
}

Obj open_image(const char* path) {
	Obj assembly = mono_domain_assembly_open(g_domain, path);
	Obj image    = assembly != nullptr ? mono_assembly_get_image(assembly) : nullptr;
	if (image == nullptr) {
		wp_log("cannot open assembly %s", path);
	}
	return image;
}

uint64_t get_method_address(Obj image, const char* name_space, const char* class_name,
                            const char* method_name, int param_count) {
	Obj klass = mono_class_from_name(image, name_space, class_name);
	if (klass == nullptr) {
		wp_log("class %s.%s not found", name_space, class_name);
		return 0;
	}
	Obj method = mono_class_get_method_from_name(klass, method_name, param_count);
	if (method == nullptr) {
		wp_log("method %s.%s.%s(%d) not found", name_space, class_name, method_name, param_count);
		return 0;
	}
	return reinterpret_cast<uint64_t>(mono_compile_method(method));
}

Obj find_method_up(Obj klass, const char* name, int argc) {
	for (Obj k = klass; k != nullptr; k = mono_class_get_parent != nullptr ? mono_class_get_parent(k) : nullptr) {
		Obj m = mono_class_get_method_from_name(k, name, argc);
		if (m != nullptr) {
			return m;
		}
	}
	return nullptr;
}

Obj method_by_desc(Obj klass, const char* desc_text) {
	Obj desc   = mono_method_desc_new(desc_text, 1);
	Obj method = desc != nullptr ? mono_method_desc_search_in_class(desc, klass) : nullptr;
	if (desc != nullptr) {
		mono_method_desc_free(desc);
	}
	if (method == nullptr) {
		wp_log("method %s not found", desc_text);
	}
	return method;
}

Obj construct_pinned(Obj klass, Obj ctor, void** args, const char* what) {
	Obj obj = mono_object_new(g_domain, klass);
	if (obj == nullptr) {
		return nullptr;
	}
	mono_gchandle_new(obj, 1);
	if (!invoke(ctor, obj, args, what)) {
		return nullptr;
	}
	return obj;
}

// ---- BGLayer setup ---------------------------------------------------------------------------
bool g_installed = false;
Obj  g_plugin    = nullptr;

int install_bglayer() {
	Obj image = open_image("/system_ex/common_ex/lib/Sce.Vsh.ShellUI.BGLayer.dll");
	if (image == nullptr) {
		return 2;
	}
	Obj plugin_class = mono_class_from_name(image, "Sce.Vsh.ShellUI.BGLayer", "BGLayerPlugin");
	if (plugin_class == nullptr) {
		wp_log("BGLayerPlugin class not found");
		return 3;
	}
	g_plugin = property_get(plugin_class, nullptr, "Instance");
	if (g_plugin == nullptr) {
		wp_log("BGLayerPlugin.Instance is null");
		return 4;
	}
	mono_gchandle_new(g_plugin, 1);
	g_installed = true;
	return 0;
}

// ---- noop Action (for PlayStateChanged) ------------------------------------------------------

Obj make_noop_action() {
	Obj corlib         = mono_get_corlib();
	Obj action_class   = mono_class_from_name(corlib, "System", "Action");
	Obj thread_class   = mono_class_from_name(corlib, "System.Threading", "Thread");
	Obj delegate_class = mono_class_from_name(corlib, "System", "Delegate");
	if (action_class == nullptr || thread_class == nullptr || delegate_class == nullptr) {
		return nullptr;
	}
	Obj barrier = mono_class_get_method_from_name(thread_class, "MemoryBarrier", 0);
	Obj desc    = mono_method_desc_new(":CreateDelegate(System.Type,System.Reflection.MethodInfo)", 1);
	Obj create  = desc != nullptr ? mono_method_desc_search_in_class(desc, delegate_class) : nullptr;
	if (desc != nullptr) {
		mono_method_desc_free(desc);
	}
	if (barrier == nullptr || create == nullptr) {
		return nullptr;
	}
	void* args[2] = {mono_type_get_object(g_domain, mono_class_get_type(action_class)),
	                 mono_method_get_object(g_domain, barrier, thread_class)};
	Obj action = nullptr;
	invoke(create, nullptr, args, "Delegate.CreateDelegate", &action);
	if (action != nullptr) {
		mono_gchandle_new(action, 1);
	}
	return action;
}

// ---- video: InitialBootPlayer route ----------------------------------------------------------
// Sony's own boot-movie widget drives the whole VideoView lifecycle itself. We redirect its
// private GetVideoPath to our clip (for our instance only) and let it handle Create/Play/loop.

char g_video_path[512] = {};
// Resume after a game (experimental): the clip that stopped and where (ms). Used once, by the same clip only.
char     g_resume_clip[512] = {};
uint64_t g_resume_pos       = 0;

bool resume_on() {
	OptFile* f  = opt_open("/system_tmp/liveshell/resume.txt");
	int   on = 0;
	if (f != nullptr) {
		if (opt_scanf(f, "%d", &on) != 1) {
			on = 0;
		}
		opt_close(f);
	}
	return on == 1;
}
bool g_mode_sony       = false;

Obj  g_boot_class      = nullptr;
Obj  g_boot_player     = nullptr;
Obj  g_boot_root       = nullptr;
Obj  g_widget_class    = nullptr;
Obj  g_videoview_class = nullptr;
Obj  g_vplayer_class   = nullptr;
Obj  g_state_field     = nullptr;
Obj  g_state_action    = nullptr;
int  g_boot_frames     = 0;
int  g_boot_state      = -1;
int  g_boot_restarts   = 0;
int  g_boot_quick      = 0;
int  g_boot_started    = 0;

int  g_boot_end_frame      = -1;
int  g_boot_dispose_frame  = -1;
bool g_boot_dispose_called = false;
bool g_boot_loop_set       = false;

using VoidMethodFn = void (*)(Obj self);
VoidMethodFn g_on_end_orig       = nullptr;
VoidMethodFn g_dispose_self_orig = nullptr;

void OnEnd_Hook(Obj self) {
	g_on_end_orig(self);
	if (self != nullptr && self == g_boot_player) {
		g_boot_end_frame = g_boot_frames;
		if (g_boot_restarts < 6) {
			wp_log("video: OnEnd (frame %d, %d after start)", g_boot_frames, g_boot_frames - g_boot_started);
		}
	}
}

void DisposeSelf_Hook(Obj self) {
	const bool ours = self != nullptr && self == g_boot_player;
	g_dispose_self_orig(self);
	if (ours) {
		g_boot_dispose_frame = g_boot_frames;
		if (g_boot_restarts < 6) {
			wp_log("video: DisposeSelf (frame %d)", g_boot_frames);
		}
	}
}

using GetVideoPathFn = void (*)(Obj self, Obj* path, Obj* content_type);
GetVideoPathFn g_get_video_path_orig = nullptr;
int g_path_calls = 0;

void GetVideoPath_Hook(Obj self, Obj* path, Obj* content_type) {
	const bool ours = self != nullptr && self == g_boot_player;
	if (ours) {
		*path         = mono_string_new(g_domain, g_video_path);
		*content_type = mono_string_new(g_domain, "video/mp4");
	} else {
		g_get_video_path_orig(self, path, content_type);
	}
	if (++g_path_calls <= 12) {
		const char* given = (path != nullptr && *path != nullptr)
		                        ? mono_string_to_utf8(static_cast<char*>(*path))
		                        : nullptr;
		wp_log("GetVideoPath #%d self %p ours %d -> %s", g_path_calls,
		       self, ours ? 1 : 0, given != nullptr ? given : "(null)");
	}
}

int create_boot_player() {
	wp_log("video: creating InitialBootPlayer");
	void* ctor_args[1] = {g_boot_root};
	Obj   player       = mono_object_new(g_domain, g_boot_class);
	if (player == nullptr ||
	    !invoke(mono_class_get_method_from_name(g_boot_class, ".ctor", 1), player, ctor_args,
	            "InitialBootPlayer()")) {
		return 31;
	}
	mono_gchandle_new(player, 1);
	g_boot_player = player;

	if (g_state_action != nullptr) {
		Obj field = mono_class_get_field_from_name(g_boot_class, "PlayStateChanged");
		if (field != nullptr) {
			mono_field_set_value(player, field, g_state_action);
		}
	}
	Obj parent = property_get(g_widget_class, player, "Parent");
	if (parent == nullptr) {
		void* child_args[1] = {player};
		invoke(mono_class_get_method_from_name(g_widget_class, "AppendChild", 1), g_boot_root,
		       child_args, "AppendChild");
	}
	float zero = 0.0f, width = 1920.0f, height = 1080.0f;
	property_set(g_widget_class, player, "X", &zero);
	property_set(g_widget_class, player, "Y", &zero);
	property_set(g_widget_class, player, "Width", &width);
	property_set(g_widget_class, player, "Height", &height);

	if (!invoke(mono_class_get_method_from_name(g_boot_class, "Create", 0), player, nullptr,
	            "InitialBootPlayer.Create")) {
		return 32;
	}
	if (g_videoview_class != nullptr) {
		uint8_t overwrite = 3;
		property_set(g_videoview_class, player, "BlendMode", &overwrite);
	}
	g_boot_state         = -1;
	g_boot_started       = g_boot_frames;
	g_boot_end_frame     = -1;
	g_boot_dispose_frame = -1;
	g_boot_dispose_called = false;
	g_boot_loop_set       = false;
	return 0;
}

int start_video_sony() {
	Obj bg  = open_image("/system_ex/common_ex/lib/Sce.Vsh.ShellUI.BGLayer.dll");
	Obj pui = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	if (bg == nullptr || pui == nullptr) {
		return 21;
	}
	g_boot_class      = mono_class_from_name(bg, "Sce.Vsh.ShellUI.BGLayer", "InitialBootPlayer");
	g_widget_class    = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget");
	g_videoview_class = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "VideoView");
	Obj vp_image      = open_image("/system_ex/common_ex/lib/Sce.Vsh.VideoPlayer.dll");
	g_vplayer_class   = vp_image != nullptr
	                        ? mono_class_from_name(vp_image, "Sce.Vsh.Video", "VideoPlayer")
	                        : nullptr;
	g_state_field     = mono_class_get_field_from_name(g_boot_class, "state");
	Obj scene_class   = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Scene");
	if (g_boot_class == nullptr || g_widget_class == nullptr || scene_class == nullptr) {
		wp_log("video: classes boot %p widget %p scene %p",
		       g_boot_class, g_widget_class, scene_class);
		return 22;
	}

	const uint64_t target =
	    get_method_address(bg, "Sce.Vsh.ShellUI.BGLayer", "InitialBootPlayer", "GetVideoPath", 2);
	if (target == 0 ||
	    !InstallDetour(target, reinterpret_cast<void*>(&GetVideoPath_Hook),
	                   reinterpret_cast<void**>(&g_get_video_path_orig)) ||
	    g_get_video_path_orig == nullptr) {
		wp_log("video: GetVideoPath detour failed (target %#lx)", static_cast<unsigned long>(target));
		return 23;
	}
	const uint64_t on_end =
	    get_method_address(bg, "Sce.Vsh.ShellUI.BGLayer", "InitialBootPlayer", "OnEnd", 0);
	const uint64_t dispose =
	    get_method_address(bg, "Sce.Vsh.ShellUI.BGLayer", "InitialBootPlayer", "DisposeSelf", 0);
	if (on_end == 0 || dispose == 0 ||
	    !InstallDetour(on_end, reinterpret_cast<void*>(&OnEnd_Hook),
	                   reinterpret_cast<void**>(&g_on_end_orig)) ||
	    !InstallDetour(dispose, reinterpret_cast<void*>(&DisposeSelf_Hook),
	                   reinterpret_cast<void**>(&g_dispose_self_orig)) ||
	    g_on_end_orig == nullptr || g_dispose_self_orig == nullptr) {
		wp_log("video: OnEnd/DisposeSelf detour failed (%#lx %#lx)",
		       static_cast<unsigned long>(on_end), static_cast<unsigned long>(dispose));
		return 25;
	}

	g_boot_root = property_get(scene_class, g_plugin, "RootWidget");
	if (g_boot_root == nullptr) {
		return 24;
	}
	mono_gchandle_new(g_boot_root, 1);
	g_state_action = make_noop_action();
	wp_log("video: InitialBootPlayer route ready, GetVideoPath hooked, action %p", g_state_action);

	const int rc = create_boot_player();
	if (rc == 0) {
		wp_log("video: InitialBootPlayer created for %s", g_video_path);
	}
	return rc;
}

// ---- video: own player route -----------------------------------------------------------------
// VideoPlayer(CreateOptionParam) + VideoView(PlayOptionParam). Everything pinned, on the UI
// thread, no per-frame calls into VideoPlayer. SetLoop on view.VideoPlayer once it exists.

Obj g_own_player   = nullptr;
Obj g_own_view     = nullptr;
Obj g_own_play0    = nullptr;
int g_own_frames   = 0;
extern bool g_hidden;       // hidden on purpose (Settings, our window, PS Store only)
extern int  g_hide_changed; // the tick it last changed
int g_own_logs     = 0;
int g_own_restarts = 0;
bool g_own_loop_set = false;


void set_blend(Obj view, bool overwrite);

// 4K (v1.4): Sony's player gets a UHD decoder only for a stream (an http uri), not for a file path - the
// payload streams 4K clips on 127.0.0.1:9050/uhd/<file>. The recipe: the parameterless
// CreateOptionParam (Sony's defaults) + createMode Playback + frameBufferSize 1920x1080 + coreResourceType UHD.
// With a game open the PS5 gives the home screen no UHD decoder ("close this game..."): a 4K clip hides then,
// as "Hide while a game is open" does (the game's art shows), and comes back when the game closes.
bool g_play_uhd          = false; // the running player streams a 4K clip
bool g_on_fallback       = false; // a 4K clip is chosen but a game is open: hidden until it closes
bool g_start_nothing     = false; // the last start played nothing on purpose (lift the black at once)
char g_play_path[512]    = {};    // what plays
char g_uhd_name[256]     = {};    // the 4K clip's file name (its stream address)

void begin_swap(const char* path);
extern bool g_stopping; // defined further down (the watchdog needs them)
extern int  g_switch_at;

// fast.txt: "^<path>\t<file name>\t" for every 4K clip.
bool uhd_lookup(const char* path, char* name, size_t nn, char* copy, size_t cn) {
	FILE* f = fopen("/system_tmp/liveshell/fast.txt", "r");
	if (f == nullptr) {
		return false;
	}
	char line[1400];
	bool found = false;
	while (!found && fgets(line, sizeof(line), f) != nullptr) {
		line[strcspn(line, "\r\n")] = 0;
		char* tab1 = line[0] == '^' ? strchr(line, '\t') : nullptr;
		if (tab1 == nullptr) {
			continue;
		}
		*tab1 = 0;
		if (strcmp(line + 1, path) != 0) {
			continue;
		}
		char* tab2 = strchr(tab1 + 1, '\t');
		if (tab2 != nullptr) {
			*tab2 = 0;
		}
		snprintf(name, nn, "%s", tab1 + 1);
		snprintf(copy, cn, "%s", tab2 != nullptr ? tab2 + 1 : "");
		found = true;
	}
	fclose(f);
	return found;
}

// A game is open: in front, or still running in the background (the payload's check, every second).
bool game_alive() {
	OptFile* f = opt_open("/system_tmp/liveshell/gamealive.txt");
	if (f == nullptr) {
		return false;
	}
	const int c = opt_getc(f);
	opt_close(f);
	return c == '1';
}

// The LiveShell window is in front (the payload's check, every second): the video behind it is paused.
bool window_open() {
	OptFile* f = opt_open("/system_tmp/liveshell/window.txt");
	if (f == nullptr) {
		return false;
	}
	const int c = opt_getc(f);
	opt_close(f);
	return c == '1';
}

// A 4K clip that cannot play right now: a game is open (it hides; the game's art shows).
bool uhd_blocked(const char* path) {
	char name[256], copy[512];
	return uhd_lookup(path, name, sizeof(name), copy, sizeof(copy)) && game_alive();
}

// A field by its name, or with Sony's leading underscore.
bool set_option_field(Obj klass, Obj obj, const char* name, void* value) {
	Obj f = mono_class_get_field_from_name(klass, name);
	if (f == nullptr) {
		char alt[64];
		snprintf(alt, sizeof(alt), "_%s", name);
		f = mono_class_get_field_from_name(klass, alt);
	}
	if (f == nullptr) {
		wp_log("4k: no field %s in CreateOptionParam", name);
		return false;
	}
	mono_field_set_value(obj, f, value);
	return true;
}

bool unpark(const char* path, Obj player_class, Obj view_class); // kept players (v1.7.0), below
bool park_current();
void park_tick();

int start_own_player() {
	Obj pui   = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	Obj video = open_image("/system_ex/common_ex/lib/Sce.Vsh.VideoPlayer.dll");
	if (pui == nullptr || video == nullptr) {
		return 40;
	}
	Obj view_class   = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "VideoView");
	Obj option_class = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "VideoView/PlayOptionParam");
	Obj player_class = mono_class_from_name(video, "Sce.Vsh.Video", "VideoPlayer");
	Obj create_class = mono_class_from_name(video, "Sce.Vsh.Video", "VideoPlayer/CreateOptionParam");
	Obj widget_class = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget");
	Obj scene_class  = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Scene");
	if (view_class == nullptr || option_class == nullptr || player_class == nullptr ||
	    create_class == nullptr || widget_class == nullptr || scene_class == nullptr) {
		wp_log("own player: classes missing");
		return 41;
	}
	g_videoview_class = view_class;
	if (unpark(g_play_path[0] != 0 ? g_play_path : g_video_path, player_class, view_class)) {
		return 0; // a kept player of this clip: no new one
	}

	Obj     uri          = mono_string_new(g_domain, g_play_path[0] != 0 ? g_play_path : g_video_path);
	Obj     content_type = mono_string_new(g_domain, "video/mp4");
	Obj     user_agent   = mono_string_new(g_domain, "");
	// coreType BE, playback, 1920x1080 output, canvas, FullHD decoder (ShellUI gets no UHD decoder;
	// 4K is for a later release, see PROGRESS.md "4K test").
	int     core_type = 1, create_mode = 1, frame_size = 1, render_buffer = 0, core_resource = 3;
	int     on_active = 4, on_inactive = 2, handler_mode = 0;
	uint32_t device_id = 0;
	void*   create_args[12] = {uri,            &core_type,     &create_mode,  &frame_size,
	                           &render_buffer,  &core_resource, content_type,  &on_active,
	                           &on_inactive,    &handler_mode,  user_agent,    &device_id};
	Obj create_opt = nullptr;
	if (g_play_uhd) {
		// 4K: Sony's parameterless ctor (its defaults), then only these four.
		create_opt = construct_pinned(create_class, mono_class_get_method_from_name(create_class, ".ctor", 0), nullptr,
		                              "CreateOptionParam()");
		if (create_opt == nullptr) {
			wp_log("4k: no parameterless CreateOptionParam ctor");
			return 42;
		}
		char address[400];
		int at = snprintf(address, sizeof(address), "http://127.0.0.1:9050/uhd/");
		for (const char* c = g_uhd_name; *c != 0 && at < static_cast<int>(sizeof(address)) - 4; ++c) {
			const unsigned char u = static_cast<unsigned char>(*c);
			at += isalnum(u) || u == '-' || u == '_' || u == '.' ? snprintf(address + at, 2, "%c", u)
			                                                     : snprintf(address + at, 4, "%%%02X", u);
		}
		Obj stream = mono_string_new(g_domain, address);
		int mode = 1, fb = 1, res = 4; // Playback, 1920x1080 output, UHD decoder
		set_option_field(create_class, create_opt, "uri", stream);
		set_option_field(create_class, create_opt, "createMode", &mode);
		set_option_field(create_class, create_opt, "frameBufferSize", &fb);
		set_option_field(create_class, create_opt, "coreResourceType", &res);
		wp_log("4k: %s over %s (UHD decoder)", g_video_path, address);
	} else {
		create_opt = construct_pinned(
		    create_class, mono_class_get_method_from_name(create_class, ".ctor", 12),
		    create_args, "CreateOptionParam");
	}
	if (create_opt == nullptr) {
		return 42;
	}

	void* player_args[1] = {create_opt};
	Obj   player         = construct_pinned(
	    player_class,
	    method_by_desc(player_class, ":.ctor(Sce.Vsh.Video.VideoPlayer/CreateOptionParam)"),
	    player_args, "VideoPlayer");
	if (player == nullptr) {
		return 43;
	}

	Obj option = construct_pinned(
	    option_class, mono_class_get_method_from_name(option_class, ".ctor", 0),
	    nullptr, "PlayOptionParam");
	if (option == nullptr) {
		return 44;
	}

	void* view_args[1] = {option};
	Obj   view         = construct_pinned(
	    view_class,
	    method_by_desc(view_class, ":.ctor(Sce.PlayStation.PUI.UI3.VideoView/PlayOptionParam)"),
	    view_args, "VideoView");
	if (view == nullptr) {
		return 45;
	}

	float   zero = 0.0f, width = 1920.0f, height = 1080.0f;
	uint8_t overwrite = 3;
	property_set(widget_class, view, "X", &zero);
	property_set(widget_class, view, "Y", &zero);
	property_set(widget_class, view, "Width", &width);
	property_set(widget_class, view, "Height", &height);
	property_set(widget_class, view, "Opacity", &zero); // focus_tick fades it in
	(void)overwrite;
	set_blend(view, false); // normal while it fades in; overwrite once fully shown (focus_tick)

	bool  update_player      = true;
	void* set_player_args[2] = {player, &update_player};
	if (!invoke(mono_class_get_method_from_name(view_class, "SetPlayer", 2), view, set_player_args,
	            "SetPlayer")) {
		return 46;
	}

	Obj root = property_get(scene_class, g_plugin, "RootWidget");
	if (root == nullptr) {
		return 47;
	}
	mono_gchandle_new(root, 1);
	void* child_args[1] = {view};
	if (!invoke(mono_class_get_method_from_name(widget_class, "AppendChild", 1), root, child_args,
	            "AppendChild")) {
		return 48;
	}

	// Before it starts: muted = the PS5's own music (a game's theme) is not cut off.
	g_clip_silent = clip_is_silent(g_play_path[0] != 0 ? g_play_path : g_video_path);
	set_bgm_suppression(player_class, player, g_vol_req.load() == 0 || g_clip_silent);
	// Sound from the very first frame as set: muted stays muted, otherwise it starts at 0 and fades
	// in (sound_tick). Applied ~0.25 s late before, so a muted clip was heard for a moment (v11-16).
	g_aud_now = 0.0f;
	assert_sound(player_class, player);
	if (g_clip_silent) {
		wp_log("sound: clip has no sound track, PS5 music allowed");
	}
	bool  load         = true;
	void* init_args[1] = {&load};
	invoke(mono_class_get_method_from_name(player_class, "Init", 1), player, init_args, "Init");
	// Resume after a game: the same clip goes on where it stopped (VideoView.Play(ulong ms)); else from the start.
	uint64_t from = resume_on() && g_resume_pos > 0 && strcmp(g_resume_clip, g_video_path) == 0 && !g_play_uhd ? g_resume_pos : 0; // 4K: from 0
	g_resume_pos  = 0; // once
	Obj   play_at = from > 0 ? method_by_desc(view_class, ":Play(ulong)") : nullptr;
	void* at_args[1] = {&from};
	if (play_at != nullptr && invoke(play_at, view, at_args, "VideoView.Play(pos)")) {
		wp_log("resume: %s from %llu ms", g_video_path, static_cast<unsigned long long>(from));
	} else if (!invoke(mono_class_get_method_from_name(view_class, "Play", 0), view, nullptr, "VideoView.Play")) {
		return 49;
	}
	assert_sound(player_class, player); // Play reset it

	bool  loop         = true;
	void* loop_args[1] = {&loop};
	invoke(mono_class_get_method_from_name(player_class, "SetLoop", 1), player, loop_args,
	       "SetLoop");

	g_own_player    = player;
	g_own_view      = view;
	g_own_play0     = method_by_desc(view_class, ":Play(ulong)");
	g_vplayer_class = player_class;
	wp_log("own player: playing %s (loop, opaque, pinned)", g_video_path);
	return 0;
}

// ---- UI-thread tick: loop the Sony-route player ----------------------------------------------

void video_report() {
	if (g_boot_player == nullptr) {
		return;
	}
	++g_boot_frames;

	if (g_boot_frames % 120 == 60 && g_boot_frames < 300 && g_videoview_class != nullptr && g_boot_restarts < 2) {
		Obj pos = property_get(g_videoview_class, g_boot_player, "Position");
		Obj dur = property_get(g_videoview_class, g_boot_player, "Duration");
		wp_log("player: pos %llu dur %llu ms (frame %d)",
		       pos != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(pos)) : 0ULL,
		       dur != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(dur)) : 0ULL,
		       g_boot_frames - g_boot_started);
	}

	if (g_boot_frames % 30 == 0 && g_state_field != nullptr && g_boot_restarts < 6) {
		int state = -1;
		mono_field_get_value(g_boot_player, g_state_field, &state);
		if (state != g_boot_state) {
			wp_log("video: state %d (frame %d)", state, g_boot_frames - g_boot_started);
			g_boot_state = state;
		}
	}

	// SetLoop(true) on view.VideoPlayer once it exists — the seamless-loop fix.
	if (!g_boot_loop_set && g_vplayer_class != nullptr && g_boot_frames % 30 == 15) {
		Obj inner = property_get(g_videoview_class, g_boot_player, "VideoPlayer");
		if (inner != nullptr) {
			g_boot_loop_set    = true;
			bool  loop         = true;
			void* loop_args[1] = {&loop};
			const bool ok = invoke(mono_class_get_method_from_name(g_vplayer_class, "SetLoop", 1),
			                       inner, loop_args, "VideoPlayer.SetLoop");
			if (g_boot_restarts < 6) {
				wp_log("video: SetLoop(true) on view.VideoPlayer %s (frame %d)",
				       ok ? "ok" : "failed", g_boot_frames - g_boot_started);
			}
		}
	}

	// Fallback: Dispose the finished player 1.5 s after OnEnd, then recreate 30 frames later.
	if (g_boot_end_frame >= 0 && g_boot_dispose_frame < 0 && !g_boot_dispose_called &&
	    g_boot_frames - g_boot_end_frame >= 90) {
		g_boot_dispose_called = true;
		Obj dispose = find_method_up(g_boot_class, "Dispose", 0);
		if (g_boot_restarts < 6) {
			wp_log("video: disposing finished player (method %p)", dispose);
		}
		invoke(dispose, g_boot_player, nullptr, "Widget.Dispose");
		if (g_boot_dispose_frame < 0) {
			g_boot_dispose_frame = g_boot_frames;
		}
		return;
	}
	if (g_boot_dispose_frame < 0 || g_boot_frames - g_boot_dispose_frame < 30) {
		return;
	}
	if (g_boot_dispose_frame - g_boot_started < 120 && ++g_boot_quick >= 3) {
		wp_log("video: ends too fast, loop stopped");
		g_boot_player = nullptr;
		return;
	}
	++g_boot_restarts;
	const int rc = create_boot_player();
	if (g_boot_restarts <= 5) {
		wp_log("video: loop %d: new player (rc %d)", g_boot_restarts, rc);
	}
	if (rc != 0) {
		g_boot_player = nullptr;
	}
}

// ---- UI-thread tick: own-player route --------------------------------------------------------

void own_player_report() {
	if (g_own_view == nullptr) {
		return;
	}
	++g_own_frames;

	// SetLoop on the VideoView's own VideoPlayer once it appears.
	if (!g_own_loop_set && g_own_frames >= 15 && g_own_frames % 15 == 0 &&
	    g_vplayer_class != nullptr) {
		Obj inner = property_get(g_videoview_class, g_own_view, "VideoPlayer");
		if (inner != nullptr) {
			g_own_loop_set     = true;
			bool  loop         = true;
			void* loop_args[1] = {&loop};
			const bool ok = invoke(mono_class_get_method_from_name(g_vplayer_class, "SetLoop", 1),
			                       inner, loop_args, "VideoPlayer.SetLoop (view)");
			wp_log("own player: SetLoop(true) on view.VideoPlayer %s (frame %d, same %d)",
			       ok ? "ok" : "failed", g_own_frames, inner == g_own_player ? 1 : 0);
			assert_sound(g_vplayer_class, inner); // settled: make sure nothing reset it
		}
	}

	// Fallback loop: only if the video is STUCK at the end (still there half a second later).
	// The player sits on the last frame for a moment before its own seamless loop; a Play(0) then
	// was a hard restart = visible quality drop at that loop (test 23).
	if (g_own_frames % 15 == 0 && g_own_play0 != nullptr) {
		Obj p = property_get(g_videoview_class, g_own_view, "Position");
		Obj d = property_get(g_videoview_class, g_own_view, "Duration");
		const unsigned long long pos =
		    p != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(p)) : 0;
		const unsigned long long dur =
		    d != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(d)) : 0;
		static int at_end = 0;
		at_end = dur > 0 && pos >= dur ? at_end + 1 : 0;
		// "Next video when one ends" (issue #11): ~0.7 s before the end, once per loop, the payload hears
		// which clip ended (it decides whether to change; it ignores this when the option is off).
		static bool end_sent = false;
		if (dur > 2000 && pos + 700 >= dur && !end_sent) {
			end_sent = true;
			to_payload('E', g_video_path, strlen(g_video_path));
		} else if (dur > 0 && pos < dur / 2) {
			end_sent = false;
		}
		// Watchdog: the position has not moved for ~3 s (not at the end): after rest mode the
		// player stays frozen and nothing restarted it (user report). Restart the clip.
		static unsigned long long last_pos = ~0ull;
		static int                frozen   = 0;
		frozen   = pos == last_pos && !(dur > 0 && pos >= dur) ? frozen + 1 : 0;
		last_pos = pos;
		// A clip that never shows a frame (0 ms, e.g. a file this player cannot decode) was restarted every
		// 3 s forever. 3 tries per clip, then it is left alone.
		static char zero_clip[512] = {};
		static int  zero_tries     = 0;
		if (pos > 0) {
			zero_tries = 0;
		}
		// Our window in front: Sony pauses the video behind it. No restart while it is open; when it closes,
		// a video that is still paused plays on at once (it stayed frozen until the watchdog restarted it).
		static bool win = false, win_resume = false;
		static int  win_closed = -100000;
		const bool  w = window_open();
		if (w != win) {
			win = w;
			wp_log("window %s", w ? "in front: video paused behind it" : "closed");
			if (!w) {
				win_closed = g_own_frames;
				win_resume = true;
			}
		}
		if (win_resume && !win && g_own_frames - win_closed >= 30) {
			win_resume = false;
			if (frozen >= 1 && !(dur > 0 && pos >= dur)) {
				const bool played = invoke(mono_class_get_method_from_name(g_videoview_class, "Play", 0), g_own_view, nullptr,
				                           "VideoView.Play (window closed)");
				wp_log("window closed: the paused video plays on (%s)", played ? "ok" : "failed");
				frozen = 0;
			}
		}
		if (g_hidden || g_tick - g_hide_changed < 180 || win || g_own_frames - win_closed < 180) {
			frozen = 0; // paused on purpose (hidden, or behind our window): that is no freeze
		}
		// Never opened (no duration 5 s after the start, e.g. a 4K stream started while a game was still
		// letting go of the decoder): black until a tile move. Start it fresh, at most 3 times per clip -
		// a paused or hidden video always knows its duration, so this is never a pause on purpose.
		static char never_clip[512] = {};
		static int  never_tries     = 0;
		if (dur == 0 && pos == 0 && g_own_frames >= 300 && g_own_frames % 300 == 0 && !win && !g_stopping && g_switch_at < 0) {
			if (strcmp(never_clip, g_video_path) != 0) {
				snprintf(never_clip, sizeof(never_clip), "%s", g_video_path);
				never_tries = 0;
			}
			if (never_tries < 3) {
				++never_tries;
				wp_log("watchdog: %s never opened (5 s) - starting it fresh (%d/3)", g_video_path, never_tries);
				begin_swap(g_video_path);
			}
		}
		if (frozen >= (g_play_uhd ? 24 : 12) && !g_stalled) { // a 4K stream: 6 s (it was restarted while fine)
			frozen = 0;
			if (!(pos == 0 && strcmp(zero_clip, g_video_path) == 0 && zero_tries >= 3)) {
				if (pos == 0) {
					if (strcmp(zero_clip, g_video_path) != 0) {
						snprintf(zero_clip, sizeof(zero_clip), "%s", g_video_path);
						zero_tries = 0;
					}
					if (++zero_tries >= 3) {
						wp_log("watchdog: %s never shows a frame - not restarted any more", g_video_path);
					}
				}
				g_stalled = true;
				wp_log("watchdog: video frozen at %llu/%llu ms for 3 s, restarting it", pos, dur);
			}
		}
		if (at_end >= 3) {
			at_end = 0;
			unsigned long long zero = 0;
			void*              args[1] = {&zero};
			invoke(g_own_play0, g_own_view, args, "VideoView.Play(0)");
			if (++g_own_restarts <= 5) {
				wp_log("own player: at end (%llu/%llu), restarted from 0", pos, dur);
			}
		}
	}

	if (g_own_logs >= 2 || g_own_frames % 120 != 0) { // twice: it plays and moves on
		return;
	}
	++g_own_logs;
	Obj pos = property_get(g_videoview_class, g_own_view, "Position");
	Obj dur = property_get(g_videoview_class, g_own_view, "Duration");
	wp_log("own player: pos %llu dur %llu ms",
	       pos != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(pos)) : 0ULL,
	       dur != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(dur)) : 0ULL);
}

// ---- dim layer: a black panel over the video so the home screen stays readable ----------------
// The BGLayer is a PUI.UI3 scene. Which UI3 class can draw a plain colour is not known for sure,
// so a few candidates are tried and their properties logged (the log tells the next build).

std::atomic<int>  g_dim_req{-1};
std::atomic<int>  g_tint_req{0}; // Picture -> Colour: 0 neutral (black dim), 1 warm, 2 cool, 3 rose, 4 teal, 5 violet
std::atomic<bool> g_dim_new{false};
Obj               g_dim_panel   = nullptr;
Obj               g_dim_root    = nullptr;
Obj               g_dim_class   = nullptr;
Obj               g_ui3_widget  = nullptr;
Obj               g_color_class = nullptr;
const char*       g_dim_prop    = nullptr; // the colour property that worked
bool              g_dim_tried   = false;
int               g_dim_shown   = -1;
float             g_black_now   = 0.0f;    // game launch: our dim panel going to black
bool              g_lfx_glowing = false;   // the launch effect's light bloom owns the panel colour

bool video_active();

void log_properties(Obj klass, const char* label) {
	if (mono_class_get_properties == nullptr || mono_property_get_name == nullptr) {
		return;
	}
	for (Obj k = klass; k != nullptr; k = mono_class_get_parent(k)) {
		char   line[1200];
		size_t n    = 0;
		void*  iter = nullptr;
		line[0]     = 0;
		while (Obj p = mono_class_get_properties(k, &iter)) {
			const char* name = mono_property_get_name(p);
			const int   w    = snprintf(line + n, sizeof(line) - n, "%s ", name != nullptr ? name : "?");
			if (w < 0 || n + static_cast<size_t>(w) >= sizeof(line)) {
				break;
			}
			n += static_cast<size_t>(w);
		}
		if (kProbeLogs) {
			wp_log("props %s (level %p): %s", label, k, line);
		}
	}
}

// Probe for "home screen only": which BGLayer calls happen when Settings etc. open.
void log_methods(Obj klass, const char* label) {
	if (mono_class_get_methods == nullptr || mono_method_get_name == nullptr || klass == nullptr) {
		return;
	}
	char   line[1300];
	size_t n    = 0;
	void*  iter = nullptr;
	line[0]     = 0;
	while (Obj m = mono_class_get_methods(klass, &iter)) {
		const char* name = mono_method_get_name(m);
		const int   w    = snprintf(line + n, sizeof(line) - n, "%s ", name != nullptr ? name : "?");
		if (w < 0 || n + static_cast<size_t>(w) >= sizeof(line)) {
			break;
		}
		n += static_cast<size_t>(w);
	}
	if (kProbeLogs) {
		wp_log("methods %s: %s", label, line);
	}
}

// Every class in the BGLayer assembly (type-definition table; row 1 is <Module>).
void log_all_classes(Obj image) {
	if (mono_image_get_table_rows == nullptr || mono_class_get == nullptr || mono_class_get_name == nullptr) {
		return;
	}
	const int rows = mono_image_get_table_rows(image, 2 /* MONO_TABLE_TYPEDEF */);
	char      line[1300];
	size_t    n = 0;
	line[0]     = 0;
	for (int i = 2; i <= rows; ++i) {
		Obj         k    = mono_class_get(image, 0x02000000u | static_cast<uint32_t>(i));
		const char* name = k != nullptr ? mono_class_get_name(k) : nullptr;
		const int   w    = snprintf(line + n, sizeof(line) - n, "%s ", name != nullptr ? name : "?");
		if (w < 0 || n + static_cast<size_t>(w) >= sizeof(line)) {
			wp_log("classes BGLayer: %s", line);
			n       = 0;
			line[0] = 0;
			--i;
			continue;
		}
		n += static_cast<size_t>(w);
	}
	wp_log("classes BGLayer (%d rows): %s", rows, line);
}

// Live watch of BGLayerPlugin's state-like properties: logs only when a value changes, so opening
// Settings shows which value flips. Read-only getters, once a second, on the UI thread.
Obj  g_watch_class = nullptr;
char g_watch_last[1300];
int  g_watch_logs = 0;

bool watch_name(const char* n) {
	if (strstr(n, "Transition") != nullptr || strstr(n, "Gen2") != nullptr) {
		return false; // change with every focused game tile / VR only: noise
	}
	for (const char* key : {"Visible", "Mode", "State", "Active", "Show", "Focus", "Hidden", "Hide", "Enable", "Type", "Kind", "Layer", "Current", "Dim", "Blur", "Mask", "Skip"}) {
		if (strstr(n, key) != nullptr) {
			return true;
		}
	}
	return false;
}

void watch_tick() {
	if (g_watch_class == nullptr || g_plugin == nullptr || g_watch_logs >= 300 || mono_class_get_properties == nullptr) {
		return;
	}
	char   line[1300];
	size_t n    = 0;
	void*  iter = nullptr;
	line[0]     = 0;
	while (Obj p = mono_class_get_properties(g_watch_class, &iter)) {
		const char* name = mono_property_get_name(p);
		Obj         get  = mono_property_get_get_method(p);
		if (name == nullptr || get == nullptr || !watch_name(name)) {
			continue;
		}
		Obj         exc = nullptr;
		Obj         val = mono_runtime_invoke(get, g_plugin, nullptr, &exc);
		const char* txt = "?";
		if (exc != nullptr) {
			txt = "(throws)";
		} else if (val == nullptr) {
			txt = "null";
		} else {
			Obj inner = nullptr;
			Obj str   = mono_object_to_string(val, &inner);
			const char* u = str != nullptr && inner == nullptr ? mono_string_to_utf8(static_cast<char*>(str)) : nullptr;
			txt = u != nullptr ? u : "?";
		}
		const int w = snprintf(line + n, sizeof(line) - n, "%s=%.40s ", name, txt);
		if (w < 0 || n + static_cast<size_t>(w) >= sizeof(line)) {
			break;
		}
		n += static_cast<size_t>(w);
	}
	if (strcmp(line, g_watch_last) != 0) {
		memcpy(g_watch_last, line, sizeof(g_watch_last));
		++g_watch_logs;
		wp_log("watch: %s", line);
	}
}

// "Home screen only": BGLayerPlugin.LayerManager_LayerApplicationIdChangedAction runs when the
// foreground layer (home, Settings, library, ...) changes. Its parameters are not known yet, so the
// hook passes up to five integer-register arguments through untouched and logs them.
using LayerChangedFn = void (*)(Obj self, uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e);
LayerChangedFn g_layer_changed_orig = nullptr;
int            g_layer_logs         = 0;

void LayerChanged_Hook(Obj self, uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
	if (g_layer_logs < 200) {
		++g_layer_logs;
		wp_log("layer app changed: a=%#lx b=%#lx c=%#lx (frame %d)", static_cast<unsigned long>(a),
		       static_cast<unsigned long>(b), static_cast<unsigned long>(c), g_boot_frames);
	}
	g_layer_changed_orig(self, a, b, c, d, e);
}

void hook_layer_changes(Obj bg) {
	Obj klass  = mono_class_from_name(bg, "Sce.Vsh.ShellUI.BGLayer", "BGLayerPlugin");
	Obj method = klass != nullptr ? mono_class_get_method_from_name(klass, "LayerManager_LayerApplicationIdChangedAction", -1) : nullptr;
	if (method == nullptr) {
		wp_log("layer hook: method not found");
		return;
	}
	const uint64_t  addr       = reinterpret_cast<uint64_t>(mono_compile_method(method));
	const uintptr_t old_authid = set_ucred_to_ptrace(); // code-page mprotect needs it, as in main()
	const bool      ok         = addr != 0 && InstallDetour(addr, reinterpret_cast<void*>(&LayerChanged_Hook),
	                                                 reinterpret_cast<void**>(&g_layer_changed_orig)) &&
	                g_layer_changed_orig != nullptr;
	if (old_authid != 0) {
		set_proc_authid(getpid(), old_authid);
	}
	wp_log("layer hook: %s (%#lx)", ok ? "installed" : "FAILED", static_cast<unsigned long>(addr));
}

// Scene watch: the BGLayer root's children (class, Visible, ChildrenCount), logged on change.
Obj  g_scene_root = nullptr;
char g_scene_last[1300];
int  g_scene_logs = 0;

bool unbox_bool(Obj o) {
	return o != nullptr && *static_cast<uint8_t*>(mono_object_unbox(o)) != 0;
}

int unbox_int(Obj o) {
	return o != nullptr ? *static_cast<int*>(mono_object_unbox(o)) : -1;
}

void scene_tick() {
	if (g_scene_logs >= 300 || mono_object_get_class == nullptr || mono_class_get_name == nullptr) {
		return;
	}
	if (g_scene_root == nullptr) {
		Obj pui   = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
		Obj scene = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Scene") : nullptr;
		if (g_ui3_widget == nullptr && pui != nullptr) {
			g_ui3_widget = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget");
		}
		g_scene_root = scene != nullptr && g_plugin != nullptr ? property_get(scene, g_plugin, "RootWidget") : nullptr;
		if (g_scene_root == nullptr || g_ui3_widget == nullptr) {
			g_scene_logs = 300;
			wp_log("scene watch: no root");
			return;
		}
		mono_gchandle_new(g_scene_root, 1);
	}
	char   line[1300];
	size_t n = 0;
	line[0]  = 0;
	int count = 0;
	for (Obj w = property_get(g_ui3_widget, g_scene_root, "FirstChild"); w != nullptr && count < 30;
	     w = property_get(g_ui3_widget, w, "NextSibling"), ++count) {
		Obj         k    = mono_object_get_class(w);
		const char* name = k != nullptr ? mono_class_get_name(k) : "?";
		const int   wr   = snprintf(line + n, sizeof(line) - n, "%s:%d/%d ", name, unbox_bool(property_get(g_ui3_widget, w, "Visible")) ? 1 : 0,
		                            unbox_int(property_get(g_ui3_widget, w, "ChildrenCount")));
		if (wr < 0 || n + static_cast<size_t>(wr) >= sizeof(line)) {
			break;
		}
		n += static_cast<size_t>(wr);
	}
	if (strcmp(line, g_scene_last) != 0) {
		memcpy(g_scene_last, line, sizeof(g_scene_last));
		++g_scene_logs;
		wp_log("scene: %s", line);
	}
}

// Layer / app managers elsewhere in ShellUI: list interesting class names, then watch every
// property of singleton-like managers and log changes (opening Settings should flip one).
struct Watched {
	Obj         klass;
	Obj         inst;
	char        name[64];
	char        last[1300];
};
Watched g_watched[8];
int     g_watched_count = 0;
int     g_manager_logs  = 0;

bool name_has(const char* n, std::initializer_list<const char*> keys) {
	for (const char* k : keys) {
		if (strstr(n, k) != nullptr) {
			return true;
		}
	}
	return false;
}

void probe_assembly(const char* dll) {
	if (mono_image_get_table_rows == nullptr || mono_class_get == nullptr || mono_class_get_name == nullptr) {
		return;
	}
	char path[160];
	snprintf(path, sizeof(path), "/system_ex/common_ex/lib/%s.dll", dll);
	Obj image = open_image(path);
	if (image == nullptr) {
		return;
	}
	const int rows = mono_image_get_table_rows(image, 2);
	char      line[1300];
	size_t    n = 0;
	line[0]     = 0;
	for (int i = 2; i <= rows; ++i) {
		Obj         k    = mono_class_get(image, 0x02000000u | static_cast<uint32_t>(i));
		const char* name = k != nullptr ? mono_class_get_name(k) : nullptr;
		if (name == nullptr || name[0] == '<' || !name_has(name, {"Layer", "Focus", "Foreground", "Active", "Scene", "Page", "Screen", "Home", "Setting", "Shell", "AppManager", "Navigation"})) {
			continue;
		}
		const int w = snprintf(line + n, sizeof(line) - n, "%s ", name);
		if (w > 0 && n + static_cast<size_t>(w) < sizeof(line)) {
			n += static_cast<size_t>(w);
		}
		if (g_watched_count < 8 && name_has(name, {"LayerManager", "AppManager", "FocusManager", "ForegroundManager", "SceneManager", "NavigationManager", "ShellAppManager"})) {
			Obj prop = mono_class_get_property_from_name(k, "Instance");
			Obj get  = prop != nullptr ? mono_property_get_get_method(prop) : nullptr;
			Obj exc  = nullptr;
			Obj inst = get != nullptr ? mono_runtime_invoke(get, nullptr, nullptr, &exc) : nullptr;
			wp_log("manager %s.%s: Instance %p", dll, name, exc == nullptr ? inst : nullptr);
			Watched& w2 = g_watched[g_watched_count++];
			w2.klass    = k;
			w2.inst     = exc == nullptr ? inst : nullptr; // null: static properties only
			if (w2.inst != nullptr) {
				mono_gchandle_new(w2.inst, 1);
			}
			snprintf(w2.name, sizeof(w2.name), "%s", name);
			w2.last[0] = 0;
		}
	}
	wp_log("classes %s (%d rows): %s", dll, rows, line);
}

void managers_tick() {
	for (int i = 0; i < g_watched_count && g_manager_logs < 400; ++i) {
		Watched& w = g_watched[i];
		if (w.inst == nullptr) {
			continue; // no singleton: instance getters on null would only throw (or worse)
		}
		char     line[1300];
		size_t   n    = 0;
		void*    iter = nullptr;
		line[0]       = 0;
		while (Obj p = mono_class_get_properties(w.klass, &iter)) {
			const char* name = mono_property_get_name(p);
			Obj         get  = mono_property_get_get_method(p);
			if (name == nullptr || get == nullptr || strcmp(name, "Instance") == 0) {
				continue;
			}
			Obj         exc = nullptr;
			Obj         val = mono_runtime_invoke(get, w.inst, nullptr, &exc);
			const char* txt = "?";
			if (exc != nullptr) {
				continue;
			} else if (val == nullptr) {
				txt = "null";
			} else {
				Obj         inner = nullptr;
				Obj         str   = mono_object_to_string(val, &inner);
				const char* u     = str != nullptr && inner == nullptr ? mono_string_to_utf8(static_cast<char*>(str)) : nullptr;
				txt               = u != nullptr ? u : "?";
			}
			const int wr = snprintf(line + n, sizeof(line) - n, "%s=%.40s ", name, txt);
			if (wr < 0 || n + static_cast<size_t>(wr) >= sizeof(line)) {
				break;
			}
			n += static_cast<size_t>(wr);
		}
		if (strcmp(line, w.last) != 0) {
			memcpy(w.last, line, sizeof(w.last));
			++g_manager_logs;
			wp_log("mgr %s: %s", w.name, line);
		}
	}
}

void log_fields(Obj klass, const char* label) {
	if (mono_class_get_fields == nullptr || mono_field_get_name == nullptr) {
		return;
	}
	char   line[1300];
	size_t n    = 0;
	void*  iter = nullptr;
	line[0]     = 0;
	while (Obj f = mono_class_get_fields(klass, &iter)) {
		const char* name = mono_field_get_name(f);
		const int   w    = snprintf(line + n, sizeof(line) - n, "%s ", name != nullptr ? name : "?");
		if (w < 0 || n + static_cast<size_t>(w) >= sizeof(line)) {
			break;
		}
		n += static_cast<size_t>(w);
	}
	if (kProbeLogs) {
		wp_log("fields %s: %s", label, line);
	}
}

// Where does ShellUI keep "which layer / app is in front"? Full member lists of the candidates.
void probe_focus_classes() {
	struct Target {
		const char* dll;
		const char* name;
	};
	static const Target kTargets[] = {
	    {"Sce.Vsh.ShellUI.AppSystem", "LayerManager"},           {"Sce.Vsh.ShellUI.AppSystem", "ShellAppManager"},
	    {"Sce.Vsh.ShellUI.AppSystem", "FocusLayer"},             {"Sce.Vsh.ShellUI.AppSystem", "ProcessFocusController"},
	    {"Sce.Vsh.ShellUI.AppSystem", "LayerMediator"},          {"Sce.Vsh.ShellUI.ReactNativeShellApp", "SettingsSceneView"},
	};
	for (const Target& t : kTargets) {
		char path[160];
		snprintf(path, sizeof(path), "/system_ex/common_ex/lib/%s.dll", t.dll);
		Obj       image = open_image(path);
		Obj       klass = nullptr;
		const int rows  = image != nullptr && mono_image_get_table_rows != nullptr ? mono_image_get_table_rows(image, 2) : 0;
		for (int i = 2; i <= rows && klass == nullptr; ++i) {
			Obj         k = mono_class_get(image, 0x02000000u | static_cast<uint32_t>(i));
			const char* n = k != nullptr ? mono_class_get_name(k) : nullptr;
			if (n != nullptr && strcmp(n, t.name) == 0) {
				klass = k;
			}
		}
		if (klass == nullptr) {
			wp_log("focus probe: %s not found", t.name);
			continue;
		}
		log_methods(klass, t.name);
		log_properties(klass, t.name);
		log_fields(klass, t.name);
	}
}

void probe_bglayer() {
	probe_focus_classes();
	Obj bg = open_image("/system_ex/common_ex/lib/Sce.Vsh.ShellUI.BGLayer.dll");
	if (bg == nullptr) {
		return;
	}
	hook_layer_changes(bg);
	g_watch_class = mono_class_from_name(bg, "Sce.Vsh.ShellUI.BGLayer", "BGLayerPlugin");
	for (const char* name : {"BGLayerPlugin", "BGLayerManager", "BGLayerScene", "BGLayerController", "WallpaperManager", "Wallpaper"}) {
		Obj klass = mono_class_from_name(bg, "Sce.Vsh.ShellUI.BGLayer", name);
		if (klass == nullptr) {
			wp_log("probe: BGLayer.%s not found", name);
			continue;
		}
		log_methods(klass, name);
		void*  iter = nullptr;
		char   line[1300];
		size_t n = 0;
		line[0]  = 0;
		while (Obj p = mono_class_get_properties != nullptr ? mono_class_get_properties(klass, &iter) : nullptr) {
			const int w = snprintf(line + n, sizeof(line) - n, "%s ", mono_property_get_name(p));
			if (w < 0 || n + static_cast<size_t>(w) >= sizeof(line)) {
				break;
			}
			n += static_cast<size_t>(w);
		}
		if (kProbeLogs) {
			wp_log("props %s: %s", name, line);
		}
	}
}

bool has_setter(Obj klass, const char* name) {
	Obj prop = mono_class_get_property_from_name(klass, name);
	return prop != nullptr && mono_property_get_set_method(prop) != nullptr;
}

// A pinned, boxed UIColor(0, 0, 0, alpha); returns the unboxed value to pass to a setter.
void* black(float alpha, bool pin = true) {
	float r = 0.0f, g = 0.0f, b = 0.0f;
	Obj   boxed = mono_object_new(g_domain, g_color_class);
	if (boxed == nullptr) {
		return nullptr;
	}
	if (pin) {
		mono_gchandle_new(boxed, 1);
	}
	void* raw     = mono_object_unbox(boxed);
	void* args[4] = {&r, &g, &b, &alpha};
	return invoke(mono_class_get_method_from_name(g_color_class, ".ctor", 4), raw, args, "UIColor()") ? raw : nullptr;
}

// The dim layer's colour: black, or a tint (Picture -> Colour). Dimmed, the tint gets darker (a colour grade).
void* tinted(float alpha) {
	static const float kTint[6][3] = {{0, 0, 0}, {1.0f, 0.55f, 0.2f}, {0.25f, 0.5f, 1.0f}, {1.0f, 0.35f, 0.6f}, {0.1f, 0.85f, 0.75f}, {0.55f, 0.35f, 1.0f}};
	const int t = g_tint_req.load();
	if (t <= 0 || t > 5 || g_color_class == nullptr) {
		return black(alpha);
	}
	const float d = alpha < 0.22f ? 0.0f : (alpha - 0.22f) / 0.78f; // how much dim on top of the tint
	float       r = kTint[t][0] * (1.0f - 0.85f * d), g = kTint[t][1] * (1.0f - 0.85f * d), b = kTint[t][2] * (1.0f - 0.85f * d);
	float       a = alpha;
	Obj         boxed = mono_object_new(g_domain, g_color_class);
	if (boxed == nullptr) {
		return black(alpha);
	}
	mono_gchandle_new(boxed, 1);
	void* raw     = mono_object_unbox(boxed);
	void* args[4] = {&r, &g, &b, &a};
	return invoke(mono_class_get_method_from_name(g_color_class, ".ctor", 4), raw, args, "UIColor(tint)") ? raw : black(alpha);
}

bool create_dim_panel() {
	g_dim_tried = true;
	Obj pui = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	if (pui == nullptr) {
		return false;
	}
	g_ui3_widget      = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget");
	g_color_class     = mono_class_from_name(pui, "Sce.PlayStation.PUI", "UIColor");
	Obj scene_class   = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Scene");
	if (g_ui3_widget == nullptr || g_color_class == nullptr || scene_class == nullptr) {
		wp_log("dim: classes widget %p color %p scene %p", g_ui3_widget, g_color_class, scene_class);
		return false;
	}
	log_properties(g_ui3_widget, "UI3.Widget");
	g_dim_root = property_get(scene_class, g_plugin, "RootWidget");
	if (g_dim_root == nullptr) {
		return false;
	}
	mono_gchandle_new(g_dim_root, 1);

	static const char* const kClasses[] = {"Panel", "Rectangle", "ColorRect", "Plane", "Box", "Widget"};
	static const char* const kColors[]  = {"BackgroundColor", "Color", "FillColor", "BaseColor"};
	for (const char* name : kClasses) {
		Obj klass = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", name);
		if (klass == nullptr) {
			wp_log("dim: UI3.%s not found", name);
			continue;
		}
		const char* prop = nullptr;
		for (const char* c : kColors) {
			if (has_setter(klass, c)) {
				prop = c;
				break;
			}
		}
		if (klass != g_ui3_widget) {
			log_properties(klass, name);
		}
		if (prop == nullptr) {
			wp_log("dim: UI3.%s has no colour property", name);
			continue;
		}
		Obj ctor  = mono_class_get_method_from_name(klass, ".ctor", 0);
		Obj panel = ctor != nullptr ? construct_pinned(klass, ctor, nullptr, name) : nullptr;
		if (panel == nullptr) {
			wp_log("dim: UI3.%s cannot be created", name);
			continue;
		}
		float zero = 0.0f, width = 1920.0f, height = 1080.0f;
		property_set(g_ui3_widget, panel, "X", &zero);
		property_set(g_ui3_widget, panel, "Y", &zero);
		property_set(g_ui3_widget, panel, "Width", &width);
		property_set(g_ui3_widget, panel, "Height", &height);
		if (has_setter(klass, "BackgroundVisibility")) {
			bool on = true;
			property_set(klass, panel, "BackgroundVisibility", &on);
		}
		void* color = black(0.0f);
		if (color == nullptr || !property_set(klass, panel, prop, color)) {
			wp_log("dim: UI3.%s.%s cannot be set", name, prop);
			continue;
		}
		void* child[1] = {panel};
		if (!invoke(find_method_up(g_ui3_widget, "AppendChild", 1), g_dim_root, child, "AppendChild(dim)")) {
			continue;
		}
		g_dim_panel = panel;
		g_dim_class = klass;
		g_dim_prop  = prop;
		wp_log("dim: using UI3.%s.%s", name, prop);
		return true;
	}
	wp_log("dim: no usable UI3 class, dim unavailable");
	return false;
}

// Keep the panel above the video: a (re)started video view is appended after it.
void raise_dim() {
	if (g_dim_panel == nullptr) {
		return;
	}
	void* child[1] = {g_dim_panel};
	// UI3.Widget has no RemoveChild (test v11-9); take it out by whichever detach method exists.
	static Obj detach = nullptr;
	static bool looked = false;
	if (!looked) {
		looked = true;
		for (const char* n : {"RemoveFromParent", "RemoveChild", "Remove", "DetachFromParent"}) {
			detach = find_method_up(g_ui3_widget, n, strcmp(n, "RemoveChild") == 0 ? 1 : 0);
			if (detach != nullptr) {
				wp_log("dim: detach with %s", n);
				break;
			}
		}
	}
	if (detach != nullptr) {
		const bool by_parent = mono_method_get_name != nullptr && strcmp(mono_method_get_name(detach), "RemoveChild") == 0;
		if (by_parent) {
			invoke(detach, g_dim_root, child, "RemoveChild(dim)");
		} else {
			invoke(detach, g_dim_panel, nullptr, "detach(dim)");
		}
	}
	invoke(find_method_up(g_ui3_widget, "AppendChild", 1), g_dim_root, child, "AppendChild(dim)");
}

// Dim only while our video plays; Sony's own wallpaper is left alone.
void refresh_dim() {
	if (g_black_now > 0.0f || g_lfx_glowing) {
		return; // the game-launch fade (or the launch effect's light) owns the panel colour
	}
	int want = video_active() ? g_dim_req.load() : 0;
	if (video_active() && g_tint_req.load() != 0 && want < 22) {
		want = 22; // a colour needs a layer that draws, even with Dim off
	}
	if (want < 0 || want == g_dim_shown) {
		return;
	}
	if (g_dim_panel == nullptr) {
		if (want == 0 || g_dim_tried || !create_dim_panel()) {
			return;
		}
	}
	void* color = tinted(static_cast<float>(want) / 100.0f);
	if (color != nullptr && property_set(g_dim_class, g_dim_panel, g_dim_prop, color)) {
		g_dim_shown = want;
		wp_log("dim: %d%%", want);
	}
}

// ---- looks: bottom fade, top fade, vignette, haze ---------------------------------------------
// Built from plain UI3 Panels (the class dim proved), as children of the dim panel so they stay
// above the video after a switch and fade out with it in Settings. A gradient = many thin bands.

constexpr const char* kLooksFile = "/system_tmp/liveshell/looks.txt";
enum Look { kBottom = 0, kTop = 1, kVignette = 2, kHaze = 3, kLooks = 4 };
std::atomic<int> g_look_req[kLooks];
int              g_look_shown[kLooks] = {-1, -1, -1, -1};
constexpr int    kLookMax = 292; // panels per look (the vignette: 72 strips x 4 edges)
Obj              g_look_panels[kLooks][kLookMax];
float            g_look_weight[kLooks][kLookMax];
int              g_look_count[kLooks] = {};
bool             g_look_built[kLooks] = {};

void* tint(float r, float g, float b, float a) {
	Obj boxed = mono_object_new(g_domain, g_color_class);
	if (boxed == nullptr) {
		return nullptr;
	}
	mono_gchandle_new(boxed, 1);
	void* raw     = mono_object_unbox(boxed);
	void* args[4] = {&r, &g, &b, &a};
	return invoke(mono_class_get_method_from_name(g_color_class, ".ctor", 4), raw, args, "UIColor()") ? raw : nullptr;
}

bool add_band(Look look, float x, float y, float w, float h, float weight) {
	if (g_look_count[look] >= kLookMax) {
		return false;
	}
	Obj ctor  = mono_class_get_method_from_name(g_dim_class, ".ctor", 0);
	Obj panel = ctor != nullptr ? construct_pinned(g_dim_class, ctor, nullptr, "look band") : nullptr;
	if (panel == nullptr) {
		return false;
	}
	property_set(g_ui3_widget, panel, "X", &x);
	property_set(g_ui3_widget, panel, "Y", &y);
	property_set(g_ui3_widget, panel, "Width", &w);
	property_set(g_ui3_widget, panel, "Height", &h);
	if (has_setter(g_dim_class, "BackgroundVisibility")) {
		bool on = true;
		property_set(g_dim_class, panel, "BackgroundVisibility", &on);
	}
	void* clear = tint(0.0f, 0.0f, 0.0f, 0.0f);
	if (clear != nullptr) {
		property_set(g_dim_class, panel, g_dim_prop, clear);
	}
	void* child[1] = {panel};
	if (!invoke(find_method_up(g_ui3_widget, "AppendChild", 1), g_dim_panel, child, "AppendChild(look)")) {
		return false;
	}
	g_look_panels[look][g_look_count[look]] = panel;
	g_look_weight[look][g_look_count[look]] = weight;
	++g_look_count[look];
	return true;
}

float smooth(float t) {
	return t * t * (3.0f - 2.0f * t);
}

void build_look(Look look) {
	g_look_built[look] = true;
	const float W = 1920.0f, H = 1080.0f;
	if (look == kBottom || look == kTop) {
		// 16 bands over the bottom 45 % / top 30 %, darker towards the edge.
		const int   n     = 16;
		const float span  = look == kBottom ? H * 0.45f : H * 0.30f;
		const float band  = span / n;
		for (int i = 0; i < n; ++i) {
			const float edge = smooth(static_cast<float>(i + 1) / n); // 0 inside .. 1 at the edge
			const float y    = look == kBottom ? H - span + i * band : (n - 1 - i) * band;
			add_band(look, 0.0f, y, W, band + 1.0f, edge);
		}
	} else if (look == kVignette) {
		// 72 thin strips per edge (~5 x 3 px), darkest at the edge, fading out over ~384 x 224 px. The step from
		// one strip to the next stays below ~2.4 % (k^2: no steep start at the edge), too small to see as a band:
		// 10 wide rings showed boxes (v1.5.0), 32 strips with k^3 still showed steps (user). Top / bottom run the
		// full width, left / right the full height: they overlap in the corners (a little darker), no seams.
		const int   rings = 72;
		const float tx = 384.0f / rings, ty = 224.0f / rings;
		for (int i = 0; i < rings; ++i) {
			const float k  = 1.0f - static_cast<float>(i) / rings;
			const float wt = k * k;
			add_band(look, 0.0f, i * ty, W, ty, wt);              // top
			add_band(look, 0.0f, H - (i + 1) * ty, W, ty, wt);    // bottom
			add_band(look, i * tx, 0.0f, tx, H, wt);              // left
			add_band(look, W - (i + 1) * tx, 0.0f, tx, H, wt);    // right
		}
	} else {
		add_band(look, 0.0f, 0.0f, W, H, 1.0f); // haze: one white veil
	}
	wp_log("look %d: %d panels", static_cast<int>(look), g_look_count[look]);
}

void refresh_looks() {
	if (g_dim_panel == nullptr) {
		if (g_dim_tried || !video_active()) {
			return;
		}
		create_dim_panel();
		if (g_dim_panel == nullptr) {
			return;
		}
	}
	for (int l = 0; l < kLooks; ++l) {
		const int want = video_active() ? g_look_req[l].load() : 0;
		if (want < 0 || want == g_look_shown[l]) {
			continue;
		}
		if (want > 0 && !g_look_built[l]) {
			build_look(static_cast<Look>(l));
		}
		g_look_shown[l] = want;
		// Strength per level: Light / Strong.
		const float max_a = l == kHaze ? (want >= 2 ? 0.35f : 0.18f)
		                  : l == kVignette ? (want >= 2 ? 0.85f : 0.55f)
		                                   : (want >= 2 ? 0.85f : 0.55f);
		const float c = l == kHaze ? 1.0f : 0.0f;
		for (int i = 0; i < g_look_count[l]; ++i) {
			void* col = tint(c, c, c, want > 0 ? max_a * g_look_weight[l][i] : 0.0f);
			if (col != nullptr) {
				property_set(g_dim_class, g_look_panels[l][i], g_dim_prop, col);
			}
		}
		wp_log("look %d: level %d", l, want);
	}
}

// ---- "In menus: hide" -------------------------------------------------------------------------
// LayerManager.s_curFocusLayer (static, enum FocusLayer { None, Game, TopMenu, ShellApp }) says
// which layer has focus. ShellApp = Settings and the other system apps: hide our video (and the
// dim panel) there so the stock background shows; home (TopMenu) shows it again.

constexpr const char* kMenusFile = "/system_tmp/liveshell/menus.txt";
std::atomic<int> g_menus_req{0}; // 0 show in menus, 1 hide in menus
constexpr const char* kStoreOnlyFile = "/system_tmp/liveshell/storeonly.txt";
std::atomic<bool> g_store_only{false}; // PS Store only: the video shows only on the Store tile
bool              g_tile_hide = false;  // Store only + another tile highlighted: video faded out
bool              g_pergame_hide = false; // Videos per game only + a tile without its own video: faded out
bool              g_pergame_load = false; // Videos per game only + its clip not loaded yet: black until it is
bool              g_pergame_dark = false; // Videos per game only, onto a tile without a video: black, then its art
bool fast_lookup(const char* tid, char* out, size_t n); // below, with the fast switch
Obj  g_focus_field  = nullptr;
Obj  g_focus_vtable = nullptr;
int  g_shellapp_val = -1;
int  g_game_val     = -1;
int  g_focus_now    = -1;
bool g_focus_ready  = false;
bool g_focus_failed = false;
bool g_hidden       = false;
Obj  g_hidden_view  = nullptr;
int  g_hide_changed = 0;
float g_opacity     = -1.0f;
float g_view_op     = -1.0f; // video opacity actually set
float g_view_in     = 1.0f;  // a new video's own fade-in, 0..1
bool  g_was_game    = false;
bool  g_hold_black  = false; // back from a game, video not restarted yet: our panel stays black
int   g_hold_start  = 0;
int   g_hold_view_tick = -1;
int   g_switch_at      = -1;  // quick swap (same folder): tick the fade to black started
char  g_switch_path[512] = {};
// Fast per-game switch (test v11-8): ShellUI picks the highlighted game's clip itself.
char  g_fast_tid[16] = {};
int   g_fast_at      = -1; // tick the highlighted tile changed (-1 = decided)
bool  g_self_started = false; // started on the return from a game, the payload has not confirmed yet

// "Hide while a game is open" (option): the payload writes 1 while a game is open in the background;
// then ShellUI does not start a video by itself (return from a game, tile move) - Sony's art stays.
bool game_open_hold() {
	OptFile* f = opt_open("/system_tmp/liveshell/gameopen.txt");
	int   v = 0;
	if (f != nullptr) {
		if (opt_scanf(f, "%d", &v) != 1) {
			v = 0;
		}
		opt_close(f);
	}
	return v == 1;
}
void  stop_video();
int   start_video();

Obj find_class(const char* dll, const char* name) {
	char path[160];
	snprintf(path, sizeof(path), "/system_ex/common_ex/lib/%s.dll", dll);
	Obj       image = open_image(path);
	const int rows  = image != nullptr && mono_image_get_table_rows != nullptr ? mono_image_get_table_rows(image, 2) : 0;
	for (int i = 2; i <= rows; ++i) {
		Obj         k = mono_class_get(image, 0x02000000u | static_cast<uint32_t>(i));
		const char* n = k != nullptr ? mono_class_get_name(k) : nullptr;
		if (n != nullptr && strcmp(n, name) == 0) {
			return k;
		}
	}
	return nullptr;
}

void setup_focus() {
	g_focus_ready = true;
	Obj lm        = find_class("Sce.Vsh.ShellUI.AppSystem", "LayerManager");
	Obj fl        = find_class("Sce.Vsh.ShellUI.AppSystem", "FocusLayer");
	g_focus_field = lm != nullptr ? mono_class_get_field_from_name(lm, "s_curFocusLayer") : nullptr;
	g_focus_vtable = lm != nullptr && mono_class_vtable != nullptr ? mono_class_vtable(g_domain, lm) : nullptr;
	Obj fl_vt     = fl != nullptr && mono_class_vtable != nullptr ? mono_class_vtable(g_domain, fl) : nullptr;
	Obj sa        = fl != nullptr ? mono_class_get_field_from_name(fl, "ShellApp") : nullptr;
	if (sa != nullptr && fl_vt != nullptr && mono_field_static_get_value != nullptr) {
		mono_field_static_get_value(fl_vt, sa, &g_shellapp_val);
		Obj gf = mono_class_get_field_from_name(fl, "Game");
		if (gf != nullptr) {
			mono_field_static_get_value(fl_vt, gf, &g_game_val);
		}
	}
	g_focus_failed = g_focus_field == nullptr || g_focus_vtable == nullptr || g_shellapp_val < 0;
	wp_log("focus: LayerManager %p field %p vtable %p, ShellApp = %d%s", lm, g_focus_field, g_focus_vtable, g_shellapp_val,
	       g_focus_failed ? " -> hide in menus unavailable" : "");
}

void set_visible(Obj w, bool on) {
	if (w != nullptr && g_ui3_widget != nullptr) {
		property_set(g_ui3_widget, w, "Visible", &on);
	}
}

// LayerManager.s_logFocusApplicationName: the focused app's name, read when focus changes.
Obj  g_appname_field = nullptr;
bool g_is_settings   = false;
float g_fade         = 0.0f; // 0 = video fully shown, 1 = fully hidden
std::atomic<int> g_lfx_req{0}; // game launch effect: 0 default (the fade), 1 cinematic, 2 soft focus
bool  g_was_game_back = false; // the next clip that starts is the return from a game (launch transition)
bool  g_lfx_game      = false; // our layers are fading out because a game starts (launch transition)

void read_focus_app(char* out, size_t size) {
	out[0] = 0;
	if (g_appname_field == nullptr) {
		Obj lm          = find_class("Sce.Vsh.ShellUI.AppSystem", "LayerManager");
		g_appname_field = lm != nullptr ? mono_class_get_field_from_name(lm, "s_logFocusApplicationName") : nullptr;
	}
	Obj str = nullptr;
	if (g_appname_field != nullptr) {
		mono_field_static_get_value(g_focus_vtable, g_appname_field, &str);
	}
	const char* u = str != nullptr ? mono_string_to_utf8(static_cast<char*>(str)) : nullptr;
	snprintf(out, size, "%s", u != nullptr ? u : "");
}

// Which system app is in front: ShellAppManager.s_focusLayerAppId, LayerManager.s_lastFocusedApplicationId
// and ShellAppManager.GetLastShellAppTitleId(). Logged to tell Settings from Search etc.
int g_ids_at = -1;

void log_focus_ids(const char* when) {
	static Obj sam = nullptr, sam_vt = nullptr, f_app = nullptr, f_last = nullptr, m_title = nullptr;
	static bool ready = false;
	if (!ready) {
		ready  = true;
		sam    = find_class("Sce.Vsh.ShellUI.AppSystem", "ShellAppManager");
		sam_vt = sam != nullptr && mono_class_vtable != nullptr ? mono_class_vtable(g_domain, sam) : nullptr;
		f_app  = sam != nullptr ? mono_class_get_field_from_name(sam, "s_focusLayerAppId") : nullptr;
		Obj lm = find_class("Sce.Vsh.ShellUI.AppSystem", "LayerManager");
		f_last = lm != nullptr ? mono_class_get_field_from_name(lm, "s_lastFocusedApplicationId") : nullptr;
		m_title = sam != nullptr ? mono_class_get_method_from_name(sam, "GetLastShellAppTitleId", 0) : nullptr;
	}
	int app_id = -1, last_id = -1;
	if (f_app != nullptr && sam_vt != nullptr) {
		mono_field_static_get_value(sam_vt, f_app, &app_id);
	}
	if (f_last != nullptr) {
		mono_field_static_get_value(g_focus_vtable, f_last, &last_id);
	}
	const char* title = nullptr;
	if (m_title != nullptr) {
		Obj exc = nullptr;
		Obj str = mono_runtime_invoke(m_title, nullptr, nullptr, &exc);
		title   = exc == nullptr && str != nullptr ? mono_string_to_utf8(static_cast<char*>(str)) : nullptr;
	}
	wp_log("focus ids (%s): shellapp id %#x, last focused app %#x, last shell app title '%s'", when,
	       static_cast<unsigned>(app_id), static_cast<unsigned>(last_id), title != nullptr ? title : "?");
}

bool contains_nocase(const char* hay, const char* needle) {
	for (const char* h = hay; *h != 0; ++h) {
		size_t i = 0;
		while (needle[i] != 0 && h[i] != 0 && tolower(static_cast<unsigned char>(h[i])) == tolower(static_cast<unsigned char>(needle[i]))) {
			++i;
		}
		if (needle[i] == 0) {
			return true;
		}
	}
	return false;
}

// VideoView.BlendMode: 3 = overwrite (what we use, opaque). The "normal" value is read from the
// enum (Normal / Half / Alpha / Blend), logged once.
int  g_blend_normal = -2;

void set_blend(Obj view, bool overwrite) {
	if (g_videoview_class == nullptr) {
		return;
	}
	if (g_blend_normal == -2) {
		g_blend_normal = -1;
		Obj prop = mono_class_get_property_from_name(g_videoview_class, "BlendMode");
		Obj get  = prop != nullptr ? mono_property_get_get_method(prop) : nullptr;
		Obj t    = get != nullptr && mono_method_signature != nullptr ? mono_signature_get_return_type(mono_method_signature(get)) : nullptr;
		Obj ek   = t != nullptr && mono_class_from_mono_type != nullptr ? mono_class_from_mono_type(t) : nullptr;
		Obj vt   = ek != nullptr && mono_class_vtable != nullptr ? mono_class_vtable(g_domain, ek) : nullptr;
		if (ek != nullptr) {
			log_fields(ek, "BlendMode");
		}
		for (const char* n : {"Normal", "Half", "Alpha", "Blend", "AlphaBlend"}) {
			Obj f = ek != nullptr && vt != nullptr ? mono_class_get_field_from_name(ek, n) : nullptr;
			if (f != nullptr) {
				int v = 0; // byte-sized enum: only the low byte is written
				mono_field_static_get_value(vt, f, &v);
				v &= 0xFF;
				g_blend_normal = v;
				wp_log("blend: normal = %s (%d)", n, v);
				break;
			}
		}
	}
	if (g_blend_normal < 0) {
		return;
	}
	uint8_t mode = overwrite ? 3 : static_cast<uint8_t>(g_blend_normal);
	property_set(g_videoview_class, view, "BlendMode", &mode);
}

// ---- cross-fade swap: the new clip starts while the old one still plays -----------------------
// The new view is appended on top, fades in over the old one, then the old one is removed: no black
// at all. Needs a second decoder for a moment; if the new clip does not open within ~1 s, fall back
// to the black swap for the rest of the session.
Obj  g_old_view     = nullptr;
Obj  g_old_player   = nullptr;
int  g_xfade_tick   = -1;
bool g_xfade_decoding = false; // the new clip decodes smoothly: start the dip transition
int  g_xf_start      = 0;     // tick the dip started
constexpr int kDipFrames = 54; // ~0.9 s clean cross-fade with a hint of dark in the middle
bool g_xfade_broken = true; // cross-fade off (test v11-6: Sony's art showed); quick swap only

void dispose_view(Obj view) {
	if (view == nullptr || g_videoview_class == nullptr) {
		return;
	}
	Obj stop    = find_method_up(g_videoview_class, "Stop", 0);
	Obj dispose = find_method_up(g_videoview_class, "Dispose", 0);
	if (stop != nullptr) {
		invoke(stop, view, nullptr, "VideoView.Stop (old)");
	}
	invoke(dispose, view, nullptr, "VideoView.Dispose (old)");
}

void xfade_start() {
	g_old_view     = g_own_view;
	g_old_player   = g_own_player;
	g_own_view     = nullptr; // start_own_player builds a fresh view; the old one keeps playing
	g_own_player   = nullptr;
	g_own_frames   = g_own_logs = g_own_restarts = 0;
	g_own_loop_set = false;
	snprintf(g_video_path, sizeof(g_video_path), "%s", g_switch_path);
	if (start_video() != 0 || g_own_view == nullptr) {
		wp_log("cross-fade: new clip did not start, black swap instead");
		dispose_view(g_own_view);
		g_own_view     = g_old_view;
		g_own_player   = g_old_player;
		g_old_view     = g_old_player = nullptr;
		g_xfade_broken = true;
		g_switch_at    = g_tick; // black swap path
		return;
	}
	g_xfade_tick     = g_tick;
	g_xfade_decoding = false;
	wp_log("cross-fade: started");
}

void xfade_tick() {
	if (g_xfade_tick < 0 || g_own_view == nullptr) {
		return;
	}
	const int t = g_tick - g_xfade_tick;
	if (!g_xfade_decoding) {
		if (t % 5 != 0) {
			return;
		}
		Obj q = property_get(g_videoview_class, g_own_view, "Position");
		const unsigned long long pos = q != nullptr ? *static_cast<unsigned long long*>(mono_object_unbox(q)) : 0;
		if (pos >= 150) {
			g_xfade_decoding = true; // decoding smoothly now: focus_tick runs the dip transition
			g_xf_start       = g_tick;
			wp_log("cross-fade: new clip decoding after %d frames", t);
		} else if (t >= 90) {
			// No second decoder: undo, then black swap from now on.
			wp_log("cross-fade: new clip not decoding after %d frames, black swap instead", t);
			dispose_view(g_own_view);
			g_own_view     = g_old_view;
			g_own_player   = g_old_player;
			g_old_view     = g_old_player = nullptr;
			g_xfade_tick   = -1;
			g_xfade_broken = true;
			g_switch_at    = g_tick;
		}
		return;
	}
	if (g_tick - g_xf_start >= kDipFrames) {
		dispose_view(g_old_view); // the new clip fully covers it
		g_old_view = g_old_player = nullptr;
		g_xfade_tick = -1;
		wp_log("cross-fade: done after %d frames", t);
	}
}

void focus_tick() {
	if (!g_focus_ready) {
		setup_focus();
	}
	// No focus info: never hide, but still run the fade below (new videos start at opacity 0).
	int focus = -2;
	if (!g_focus_failed) {
		mono_field_static_get_value(g_focus_vtable, g_focus_field, &focus);
	}
	if (focus != g_focus_now && !g_focus_failed) {
		g_focus_now = focus;
		char app[128];
		read_focus_app(app, sizeof(app));
		// The name is "ReactNativePlugin" for Settings, Search and the rest alike (test 20), so for
		// now every system app counts; the ids below tell Settings apart for the next build.
		g_is_settings = focus == g_shellapp_val;
		wp_log("focus layer: %d, app '%s'", focus, app);
	}
	if (g_ids_at >= 0 && g_tick >= g_ids_at) {
		g_ids_at = -1;
		log_focus_ids("+0.5 s");
	}
	// Two reasons to fade our layers out:
	//  - a game / app is being started (focus Game): at once, quick (~0.5 s). Sony's "can't run this
	//    app" dialog was hidden under our layers while the game pause had not kicked in yet (test 24).
	//  - Settings with "Hide in Settings" on: focus flips before Settings is drawn, so a short wait,
	//    then a slow eased fade (~1 s). Back home: eased fade in (~0.7 s).
	Obj        view    = g_own_view != nullptr ? g_own_view : g_boot_player;
	const bool game    = g_game_val >= 0 && focus == g_game_val;
	// PS Store only: every tile but the Store (NPXS40047) shows Sony's own background; the video keeps
	// playing hidden and muted, so the Store tile gets it back at once (no restart, no black).
	// Videos per game only: a tile without its own video ("*=hide") hides the running one the same way, and a tile
	// whose clip is not loaded yet stays hidden until its swap is done (it showed the OLD clip's paused frame).
	static char hide_tid[32]   = {1, 0};
	static char tile_clip[512] = {};
	static bool pg_on          = false;
	if (strcmp(hide_tid, g_fast_tid) != 0 || g_tick % 60 == 0) {
		snprintf(hide_tid, sizeof(hide_tid), "%s", g_fast_tid);
		char p[512] = {};
		fast_lookup(g_fast_tid, p, sizeof(p)); // a clip, "hide", or "-" (another folder: the payload switches it)
		snprintf(tile_clip, sizeof(tile_clip), "%s", p);
		char m[512];
		pg_on = fast_lookup("", m, sizeof(m)) && strcmp(m, "hide") == 0; // the main entry: "*=hide"
	}
	{
		const bool was      = g_pergame_hide;
		const bool was_load = g_pergame_load;
		const bool other    = pg_on && tile_clip[0] != 0 && strcmp(tile_clip, g_video_path) != 0;
		// No video here: black first (~0.4 s: Sony's art behind us is still the previous tile's, its crossfade
		// lags), then our layers fade out from black into this tile's art.
		static bool pg_want_hide  = false;
		static int  pg_hide_since = 0;
		const bool  want_hide     = other && strcmp(tile_clip, "hide") == 0;
		if (want_hide && !pg_want_hide) {
			pg_hide_since = g_tick;
		}
		pg_want_hide   = want_hide;
		g_pergame_hide = want_hide && (g_fade >= 1.0f || g_tick - pg_hide_since >= 24);
		g_pergame_dark = want_hide && g_fade < 1.0f;
		g_pergame_load      = other && strcmp(tile_clip, "hide") != 0;  // its own video comes: black until it draws
		if (was != g_pergame_hide || was_load != g_pergame_load) {
			wp_log("per game only: %s %s", g_fast_tid[0] != 0 ? g_fast_tid : "(no game)",
			       !g_pergame_hide ? (g_pergame_load ? "loads its video - black until it draws" : "shows its video")
			                       : "has no video - hidden");
		}
	}
	g_tile_hide        = (g_store_only.load() && strcmp(g_fast_tid, "NPXS40047") != 0) || g_pergame_hide;
	const bool hide    = game || (g_menus_req.load() == 1 && g_is_settings && view != nullptr) ||
	                  (g_tile_hide && view != nullptr);
	if (hide != g_hidden) {
		g_hidden       = hide;
		g_hide_changed = g_tick;
		wp_log("layers %s (%s)", hide ? "fading out" : "fading in",
		       game ? "game" : g_pergame_hide ? "no video of its own" : g_tile_hide ? "not the PS Store" : hide ? "settings" : "home");
	}
	if (view != g_hidden_view) {
		g_hidden_view = view;
		g_opacity     = -1.0f; // new view: apply again
		g_view_op     = -1.0f;
		// A freshly started video (boot, switch, back from a game) fades in on its own instead of
		// popping in at full strength (test 28: after "Closing..." it appeared at once).
		g_view_in = view != nullptr ? 0.0f : 1.0f;
		if (view != nullptr && g_hold_black) {
			// Under the black cover: full strength at once, so lifting the black never shows what is
			// behind (a half-faded clip let Sony's game art blink through, test v11-7).
			g_view_in = 1.0f;
		}
	}
	// Back from a game while "Pause while a game runs" has the video stopped: Sony's background
	// showed until the video restarted (test 29). Hold black instead until the video is back
	// (max ~5 s), then cross-fade into it (or, with no video coming, into Sony's background).
	if (game) {
		if (g_self_started && video_active()) {
			// started on the return from a game, but the payload never said the game was closed: the game
			// is in front again -> stop it (no video behind a game: it needs the decoder)
			wp_log("game in front again before the payload's check: stopping the video started here");
			stop_video();
			write_status("stopped");
		}
		g_self_started = false;
		g_was_game     = true;
	} else if (g_was_game) {
		g_was_game      = false;
		g_was_game_back = true; // the clip that comes back settles in (launch transition)
		// "Hide while a game is open" holds the video back: no video is coming, so no black hold either -
		// the game's art shows at once (user: it stayed black until moving around).
		if (view == nullptr && !game_open_hold() && !uhd_blocked(g_video_path)) {
			g_hold_black     = true;
			g_hold_start     = g_tick;
			g_hold_view_tick = -1;
			if (g_dim_panel == nullptr && !g_dim_tried) {
				create_dim_panel();
			}
			// Start the video right here, as a tile move does (fast_tick: nothing playing -> start the
			// tile's clip): waiting for the payload's game check kept the screen black ~5 s (test 25).
			g_fast_at      = g_tick - 12;
			g_self_started = true;
			wp_log("back from a game: starting the video here");
		}
	}
	// Starting a game: fade to black (~0.35 s), hold black (~1.5 s) while the game starts, then
	// let go (an error dialog becomes readable then; test 25).
	// Starting a game: no black any more (user, test 30): our layers fade out slowly (below) and
	// the game's own launch background shows through.
	float to_black = 0.0f;
	if (g_on_fallback && g_tick % 60 == 0 && g_switch_at < 0 && g_video_path[0] != 0 && !game_alive()) {
		g_on_fallback = false;
		wp_log("4k: the game closed - back to the 4K clip");
		begin_swap(g_video_path);
	}
	if (g_switch_at >= 0 && !g_xfade_broken && g_xfade_tick < 0 && g_own_view != nullptr) {
		g_switch_at = -1;
		xfade_start();
	}
	xfade_tick();
	if (g_switch_at >= 0) {
		const int t = g_tick - g_switch_at;
		if (t < 7) { // fade to black ~0.12 s
			const float k = static_cast<float>(t) / 7.0f;
			to_black      = k * k * (3.0f - 2.0f * k);
		} else if (g_aud_now > 0.5f && g_own_player != nullptr && t < 40) {
			to_black = 1.0f; // black already; the old clip's sound is still fading out (quick moves cut it)
		} else {
			// Black now: swap the clip at once (no 2 s release wait; same folder stays mounted), then
			// hold black until the new view is there and cross-fade into it.
			g_switch_at = -1;
			if (!park_current()) { // the clip you leave is kept (v1.7.0); else stopped as before
				stop_video();
			}
			if (g_switch_path[0] == 0) { // a tile without video: no new clip, lift the black at once
				write_status("stopped");
				g_hold_black     = true;
				g_hold_start     = g_tick;
				g_hold_view_tick = g_tick;
				to_black         = 1.0f;
				return;
			}
			snprintf(g_video_path, sizeof(g_video_path), "%s", g_switch_path);
			start_video();
			g_hold_black     = true;
			g_hold_start     = g_tick;
			g_hold_view_tick = -1;
			to_black         = 1.0f;
		}
	} else if (g_xfade_tick >= 0 && g_xfade_decoding) {
		// Game-to-game transition, like the Settings fade but short: dark peaks halfway (70 %).
		const float k = static_cast<float>(g_tick - g_xf_start) / static_cast<float>(kDipFrames);
		to_black      = k >= 1.0f ? 0.0f : 0.25f * sinf(3.14159265f * k);
	} else if (g_hold_black && !(hide && game)) {
		if (g_hold_view_tick < 0 && view != nullptr && true) { // every frame: lift the black as soon as it draws
			// Lift the black only once the new clip really draws frames.
			bool drawing = view != g_own_view || g_videoview_class == nullptr;
			if (!drawing) {
				Obj q = property_get(g_videoview_class, view, "Position");
				drawing = q != nullptr && *static_cast<unsigned long long*>(mono_object_unbox(q)) >= 40;
			}
			if (drawing) {
				g_hold_view_tick = g_tick;
				// How long the decoder took for its first frames (0.4 s normally; slower after rest).
				wp_log("shown: first frames %d ms after the start", (g_tick - g_hold_start) * 1000 / 60);
			}
		}
		if (g_hold_view_tick < 0 && g_start_nothing) {
			g_hold_view_tick = g_tick; // 4K + a game open: hidden (the game's art), not black
		}
		if (g_hold_view_tick < 0 && g_tick - g_hold_start > 300) {
			g_hold_view_tick = g_tick; // no video came: let Sony's background show after all
		}
		if (g_hold_view_tick < 0) {
			to_black = 1.0f;
		} else {
			const int t = g_tick - g_hold_view_tick;
			if (t >= 12) { // black -> video ~0.2 s
				g_hold_black = false;
			} else {
				const float k = static_cast<float>(t) / 12.0f;
				to_black      = 1.0f - k * k * (3.0f - 2.0f * k);
			}
		}
	}
	if (g_pergame_load || g_pergame_dark) {
		to_black = 1.0f; // per game only: the tile's clip is loading, or black before (and while) fading to its art
	}
	if (to_black != g_black_now && g_dim_panel != nullptr && g_dim_class != nullptr) {
		g_black_now   = to_black;
		const float d = video_active() ? static_cast<float>(g_dim_req.load() < 0 ? 0 : g_dim_req.load()) / 100.0f : 0.0f;
		void*       c = black(d + (1.0f - d) * to_black, false);
		if (c != nullptr) {
			property_set(g_dim_class, g_dim_panel, g_dim_prop, c);
		}
		g_dim_shown = to_black > 0.0f ? -2 : -1; // refresh_dim puts the real dim back afterwards
	}
	g_lfx_game = hide && game;
	if (hide) {
		if (game) {
			const float step = g_lfx_req.load() != 0 ? 1.0f / 90.0f : 1.0f / 72.0f; // ~1.5 s with an effect, ~1.2 s
			g_fade = g_fade + step > 1.0f ? 1.0f : g_fade + step;
		} else if (g_tile_hide) {
			g_fade = g_fade + 1.0f / 15.0f > 1.0f ? 1.0f : g_fade + 1.0f / 15.0f; // ~0.25 s, at once
		} else if (g_tick - g_hide_changed >= 9) {
			g_fade = g_fade + 1.0f / 60.0f > 1.0f ? 1.0f : g_fade + 1.0f / 60.0f;
		}
	} else {
		g_fade = g_fade - 1.0f / 24.0f < 0.0f ? 0.0f : g_fade - 1.0f / 24.0f;
	}
	const bool xfading = g_xfade_tick >= 0;
	if (xfading && !g_xfade_decoding) {
		g_view_in = 0.0f; // invisible until it decodes smoothly
	} else if (xfading) {
		// The new clip rises during the middle half of the dip, while the panel is darkest.
		const float t = static_cast<float>(g_tick - g_xf_start) - 4.0f;
		g_view_in     = t <= 0.0f ? 0.0f : (t >= 44.0f ? 1.0f : t / 44.0f);
	} else {
		const float step = xfading ? 1.0f / 36.0f : 1.0f / 30.0f;
		g_view_in        = g_view_in + step > 1.0f ? 1.0f : g_view_in + step;
	}
	// Going out: ease-in-out (slow start, slow end). Coming back home: ease-out, i.e. our layers
	// cover Sony's background almost at once and then settle (test 26).
	float next;
	if (hide && g_lfx_game && g_lfx_req.load() != 0) {
		// a launch effect: the picture stays while the push / defocus builds up, then fades (from 40%)
		float q = (g_fade - 0.4f) / 0.6f;
		q       = q < 0.0f ? 0.0f : (q > 1.0f ? 1.0f : q);
		next    = 1.0f - q * q * (3.0f - 2.0f * q);
	} else if (hide) {
		const float eased = g_fade < 0.5f ? 4.0f * g_fade * g_fade * g_fade
		                                  : 1.0f - (-2.0f * g_fade + 2.0f) * (-2.0f * g_fade + 2.0f) * (-2.0f * g_fade + 2.0f) / 2.0f;
		next = 1.0f - eased;
	} else {
		next = 1.0f - g_fade * g_fade * g_fade;
	}
	// Cross-fade: smoothstep (soft start + soft end, like Sony's art fade); a lone new clip: ease-out.
	const float vi      = xfading ? g_view_in * g_view_in * (3.0f - 2.0f * g_view_in)
	                              : 1.0f - (1.0f - g_view_in) * (1.0f - g_view_in) * (1.0f - g_view_in);
	float       view_op = next * vi;
	if (g_pergame_load || g_pergame_dark) {
		view_op = 0.0f; // per game only, black over the art: the paused clip under it must not show through
	}
	if (view != nullptr && view_op != g_view_op) {
		const bool was_full = g_view_op >= 1.0f || g_view_op < 0.0f;
		g_view_op           = view_op;
		// "Overwrite" blending replaces what is behind the video, so Sony's background stayed
		// invisible until the end of a fade and then popped in (test 24). Blend normally while
		// fading, overwrite again once fully shown.
		if (view_op < 1.0f && was_full) {
			set_blend(view, false);
		} else if (view_op >= 1.0f) {
			set_blend(view, true);
		}
		property_set(g_ui3_widget, view, "Opacity", &view_op);
	}
	if (next != g_opacity) {
		g_opacity = next;
		if (g_dim_panel != nullptr) {
			property_set(g_ui3_widget, g_dim_panel, "Opacity", &next);
		}
	}
}

// ---- parallax --------------------------------------------------------------------------------
// When the home screen moves between game tiles, BGLayerPlugin.TransitionType briefly becomes
// CustomImageSlideInLeft / Right. The video (drawn a bit larger so no edge shows) then shifts a
// few pixels that way and eases back: a depth effect. One property write per frame while moving.

constexpr const char* kParallaxFile = "/system_tmp/liveshell/parallax.txt";
constexpr float       kOverX = 36.0f, kOverY = 20.0f; // extra size on each side while parallax is on
std::atomic<int> g_parallax_req{0};
bool  g_px_ready     = false;
Obj   g_px_getter    = nullptr;
int   g_px_left      = -1;
int   g_px_right     = -1;
int   g_px_last      = -1;
float g_px           = 0.0f;
float g_px_target    = 0.0f;
int   g_px_kick_tick = -1000;
int   g_px_on        = -1; // what the view is set up for (-1 unknown)
Obj   g_px_view      = nullptr;

void setup_parallax() {
	g_px_ready  = true;
	Obj pk      = g_plugin != nullptr ? mono_object_get_class(g_plugin) : nullptr;
	Obj prop    = pk != nullptr ? mono_class_get_property_from_name(pk, "TransitionType") : nullptr;
	g_px_getter = prop != nullptr ? mono_property_get_get_method(prop) : nullptr;
	Obj t       = g_px_getter != nullptr && mono_method_signature != nullptr ? mono_signature_get_return_type(mono_method_signature(g_px_getter)) : nullptr;
	Obj ek      = t != nullptr && mono_class_from_mono_type != nullptr ? mono_class_from_mono_type(t) : nullptr;
	Obj vt      = ek != nullptr && mono_class_vtable != nullptr ? mono_class_vtable(g_domain, ek) : nullptr;
	Obj fl      = ek != nullptr ? mono_class_get_field_from_name(ek, "CustomImageSlideInLeft") : nullptr;
	Obj fr      = ek != nullptr ? mono_class_get_field_from_name(ek, "CustomImageSlideInRight") : nullptr;
	if (vt != nullptr && fl != nullptr && fr != nullptr) {
		mono_field_static_get_value(vt, fl, &g_px_left);
		mono_field_static_get_value(vt, fr, &g_px_right);
	}
	wp_log("parallax: TransitionType getter %p, SlideInLeft %d, SlideInRight %d", g_px_getter, g_px_left, g_px_right);
}

void place_view(Obj view, bool parallax, float shift) {
	float x = parallax ? -kOverX + shift : 0.0f, y = parallax ? -kOverY : 0.0f;
	float w = parallax ? 1920.0f + 2 * kOverX : 1920.0f, h = parallax ? 1080.0f + 2 * kOverY : 1080.0f;
	property_set(g_ui3_widget, view, "X", &x);
	property_set(g_ui3_widget, view, "Y", &y);
	property_set(g_ui3_widget, view, "Width", &w);
	property_set(g_ui3_widget, view, "Height", &h);
}

// ---- game-launch transition --------------------------------------------------------------------
float g_lfx_scale  = 1.0f;       // what the view is sized to now
float g_lfx_back   = 1.0f;       // back from a game: 0 -> 1 while the wallpaper settles in
Obj   g_lfx_view   = nullptr;

// The video's box: scale sx / sy around the point (ax, ay) of the screen (0..1), then moved by dx / dy pixels.
// Scale 1 + no move = parallax's own placement.
void lfx_place(Obj view, float sx, float sy, float ax, float ay, float dx, float dy) {
	const float bw = g_px_on == 1 ? 1920.0f + 2 * kOverX : 1920.0f, bh = g_px_on == 1 ? 1080.0f + 2 * kOverY : 1080.0f;
	const float bx = g_px_on == 1 ? -kOverX + g_px : 0.0f, by = g_px_on == 1 ? -kOverY : 0.0f;
	const float px = 1920.0f * ax, py = 1080.0f * ay;
	float w = bw * sx, h = bh * sy, x = px + (bx - px) * sx + dx, y = py + (by - py) * sy + dy;
	if (w < 2.0f) {
		w = 2.0f;
	}
	if (h < 2.0f) {
		h = 2.0f;
	}
	property_set(g_ui3_widget, view, "X", &x);
	property_set(g_ui3_widget, view, "Y", &y);
	property_set(g_ui3_widget, view, "Width", &w);
	property_set(g_ui3_widget, view, "Height", &h);
}

// One frame of an effect. out: leaving for a game, k = g_fade 0 -> 1. back: k = 1 -> 0 while it settles in.
// s = scale around the centre, glow = white light over the picture (0..1).
struct Lfx {
	float s = 1.0f, glow = 0.0f;
};
Lfx lfx_frame(int mode, float k, bool out) {
	Lfx         f;
	const float e = k * k * (3.0f - 2.0f * k); // smoothstep: soft start, soft end
	if (!out) {                                 // coming back: settle from a touch closer
		f.s = mode == 1 ? 1.0f + 0.035f * k : 1.0f; // Cinematic settles back in
		return f;
	}
	switch (mode) {
	case 1: // Cinematic: a slow push-in, then (focus_tick) the fade
		f.s = 1.0f + 0.08f * e;
		break;
	case 2: // Slow fade: the picture holds, then (focus_tick) fades slowly
		break;
	default:
		break;
	}
	return f;
}

float g_lfx_sig  = 0.0f;

void* white(float alpha) {
	float r = 1.0f, g = 1.0f, b = 1.0f;
	Obj   boxed = g_color_class != nullptr ? mono_object_new(g_domain, g_color_class) : nullptr;
	if (boxed == nullptr) {
		return nullptr;
	}
	void* raw     = mono_object_unbox(boxed);
	void* args[4] = {&r, &g, &b, &alpha};
	return invoke(mono_class_get_method_from_name(g_color_class, ".ctor", 4), raw, args, "UIColor()") ? raw : nullptr;
}

void launchfx_tick() {
	Obj       view = g_own_view != nullptr ? g_own_view : g_boot_player;
	const int mode = g_lfx_req.load();
	if (view == nullptr || g_ui3_widget == nullptr) {
		g_lfx_view = nullptr;
		return;
	}
	if (view != g_lfx_view) { // a new clip: back from a game it settles in, otherwise nothing
		g_lfx_view  = view;
		g_lfx_sig   = 0.0f;
		g_lfx_back  = g_was_game_back && mode != 0 ? 0.0f : 1.0f;
		g_was_game_back = false;
	}
	Lfx  f;
	bool active = false;
	if (mode != 0 && g_lfx_game) {
		f      = lfx_frame(mode, g_fade, true);
		active = true;
	} else if (g_lfx_back < 1.0f) {
		g_lfx_back += 1.0f / 54.0f; // ~0.9 s
		if (g_lfx_back > 1.0f) {
			g_lfx_back = 1.0f;
		}
		const float o = 1.0f - (1.0f - g_lfx_back) * (1.0f - g_lfx_back) * (1.0f - g_lfx_back); // ease-out
		f      = lfx_frame(mode, 1.0f - o, false);
		active = true;
	}
	const float sig = active ? 1.0f + f.s * 13.0f + f.glow * 5.0f : 0.0f;
	if (sig == g_lfx_sig) {
		return;
	}
	g_lfx_sig = sig;
	if (!active || f.s == 1.0f) {
		place_view(view, g_px_on == 1, g_px_on == 1 ? g_px : 0.0f); // parallax's own placement
	} else {
		lfx_place(view, f.s, f.s, 0.5f, 0.5f, 0.0f, 0.0f);
	}
	(void)active;
	if (active && f.glow > 0.004f && g_dim_panel != nullptr && g_dim_class != nullptr && g_dim_prop != nullptr) {
		void* c = white(f.glow);
		if (c != nullptr) {
			property_set(g_dim_class, g_dim_panel, g_dim_prop, c);
			g_lfx_glowing = true; // refresh_dim keeps its hands off meanwhile
			g_dim_shown   = -2;
		}
	} else if (g_lfx_glowing) {
		g_lfx_glowing = false;
		g_dim_shown   = -1; // refresh_dim puts the real dim colour back
	}
}

void parallax_tick() {
	Obj       view = g_own_view != nullptr ? g_own_view : g_boot_player;
	const int on   = g_parallax_req.load() == 1 && view != nullptr ? 1 : 0;
	if (view == nullptr) {
		return;
	}
	if (on != g_px_on || view != g_px_view) {
		g_px_on   = on;
		g_px_view = view;
		g_px = g_px_target = 0.0f;
		place_view(view, on == 1, 0.0f);
		wp_log("parallax: %s", on ? "on" : "off");
	}
	if (!on) {
		return;
	}
	if (!g_px_ready) {
		setup_parallax();
	}
	if (g_px_getter == nullptr || g_px_left < 0) {
		return;
	}
	Obj exc = nullptr;
	Obj val = mono_runtime_invoke(g_px_getter, g_plugin, nullptr, &exc);
	const int type = exc == nullptr && val != nullptr ? *static_cast<int*>(mono_object_unbox(val)) : -1;
	if (type != g_px_last) {
		g_px_last = type;
		if (type == g_px_left || type == g_px_right) {
			g_px_target    = type == g_px_left ? 22.0f : -22.0f;
			g_px_kick_tick = g_tick;
		}
	}
	if (g_tick - g_px_kick_tick > 10) {
		g_px_target = 0.0f; // after the nudge, settle back
	}
	const float speed = g_px_target != 0.0f ? 0.18f : 0.07f;
	const float next  = g_px + (g_px_target - g_px) * speed;
	if (next > -0.05f && next < 0.05f && g_px_target == 0.0f) {
		if (g_px != 0.0f) {
			g_px = 0.0f;
			place_view(view, true, 0.0f);
		}
		return;
	}
	g_px = next;
	float x = -kOverX + g_px;
	property_set(g_ui3_widget, view, "X", &x);
}

// ---- v1.1: per-game backgrounds (highlighted tile) and the game-music block --------------------

bool detour_method(const char* dll, const char* klass_name, const char* method, int argc, void* hook, void** orig) {
	Obj k = find_class(dll, klass_name);
	Obj m = k != nullptr ? mono_class_get_method_from_name(k, method, argc) : nullptr;
	const uint64_t addr = m != nullptr ? reinterpret_cast<uint64_t>(mono_compile_method(m)) : 0;
	const uintptr_t old_authid = set_ucred_to_ptrace();
	const bool ok = addr != 0 && InstallDetour(addr, hook, orig) && *orig != nullptr;
	if (old_authid != 0) {
		set_proc_authid(getpid(), old_authid);
	}
	wp_log("hook %s.%s(%d): %s", klass_name, method, argc, ok ? "installed" : "FAILED");
	return ok;
}

// BGLayerPlugin.SetBackgroundTransition(BackgroundTransitionParam): runs when a home tile gets
// focus. Log AppName / DeeplinkUrl / NextImageUri to learn how to read the focused game.
using SetBgFn = uint64_t (*)(Obj self, Obj param);
SetBgFn g_setbg_orig = nullptr;
Obj     g_setbg_class = nullptr;

const char* prop_text(Obj obj, const char* name) {
	Obj v = property_get(g_setbg_class, obj, name);
	if (v == nullptr) {
		return "";
	}
	Obj         inner = nullptr;
	Obj         str   = mono_object_to_string(v, &inner);
	const char* u     = str != nullptr && inner == nullptr ? mono_string_to_utf8(static_cast<char*>(str)) : nullptr;
	return u != nullptr ? u : "?";
}

std::string title_in(const char* t); // below (a title id inside Sony's text)

uint64_t SetBg_Hook(Obj self, Obj param) {
	if (param != nullptr) {
		if (g_setbg_class == nullptr) {
			g_setbg_class = mono_object_get_class(param);
		}
		// The highlighted tile's art: /user/appmeta/<TID>/pic0.dds or /user/app/<TID>/sce_sys/pic0.dds;
		// non-game tiles use bg_hub_default. Tell the payload which game is highlighted.
		const char* img = prop_text(param, "NextImageUri");
		std::string tid;
		bool        any = img != nullptr && img[0] != 0;
		if (any) {
			// The id right after the folder, or a step further: games on extended storage keep theirs in
			// /user/appmeta/external/CUSA12345/ (that gave "external/" before, issue #3).
			for (const char* key : {"/user/appmeta/", "/user/app/"}) {
				const char* p = strstr(img, key);
				if (p != nullptr && tid.empty()) {
					tid = title_in(p + strlen(key));
				}
			}
			// The PlayStation Store tile (NPXS40047, from app.db) shows Sony's bg_NPXS40047 texture:
			// it can get its own video like a game (user request, v1.2).
			if (tid.empty() && strstr(img, "bg_NPXS40047") != nullptr) {
				tid = "NPXS40047";
			}
		}
		// Apps with only a pic0.png (homebrew like Overdrive, no pic0.dds) were not recognised (user,
		// v1.2): look for a title id in Sony's other picture fields too. Only a real id counts: tiles
		// with no id anywhere (media apps) behave exactly as in v1.1 (the first try switched them).
		if (tid.empty()) {
			for (const char* field : {"NextBlurImageUri", "NextFallbackImageUri", "NextOverlayImageUri"}) {
				const char* v = prop_text(param, field);
				if (tid.empty() && v != nullptr && v[0] != 0 && v[0] != '?' && strstr(v, "bg_hub") == nullptr &&
				    strstr(v, "bg_NPXS") == nullptr) {
					tid = title_in(v);
				}
			}
			if (!tid.empty()) {
				any = true;
			}
		}
		if (any) {
			static std::string last = "?";
			if (tid != last) {
				last = tid;
				snprintf(g_fast_tid, sizeof(g_fast_tid), "%s", tid.c_str());
				g_fast_at = g_tick;
				g_focus_new = true;
				if (!to_payload('F', tid.c_str(), tid.size())) {
					if (FILE* f = fopen("/system_tmp/liveshell/focus_game.txt", "w")) {
						fprintf(f, "%s\n", tid.c_str());
						fclose(f);
					}
				}
			}
		}
	}
	return g_setbg_orig(self, param);
}

using Gen6 = uint64_t (*)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
Gen6 g_sysbgm_orig = nullptr;

// A title id inside Sony's text (PPSA01325, CUSA12345, ...): 4 capitals + 5 digits.
std::string title_in(const char* t) {
	for (const char* q = t; q != nullptr && q[0] != 0; ++q) {
		bool ok = true;
		for (int i = 0; i < 9 && ok; ++i) {
			ok = i < 4 ? (q[i] >= 'A' && q[i] <= 'Z') : (q[i] >= '0' && q[i] <= '9');
		}
		if (ok && !(q[9] >= '0' && q[9] <= '9') && (q == t || !(q[-1] >= 'A' && q[-1] <= 'Z'))) {
			return std::string(q, 9);
		}
	}
	return {};
}

std::string obj_text(Obj o) {
	if (o == nullptr) {
		return {};
	}
	Obj         inner = nullptr;
	Obj         str   = mono_object_to_string(o, &inner);
	const char* u     = str != nullptr && inner == nullptr ? mono_string_to_utf8(static_cast<char*>(str)) : nullptr;
	return u != nullptr ? u : std::string();
}

bool fast_lookup(const char* tid, char* out, size_t n); // below, with the fast switch

int g_bgm_logs = 0;

// SceneControlModule.SetSystemBgm(JObject arg, IPromise promise): Sony starts the highlighted tile's
// music here, the same instant the tile is highlighted (test v11-16), so our player can only silence
// it ~0.4 s later = a blip of e.g. ASTRO's theme. When that tile's clip has sound (and Sound is not
// Mute) the call is answered (promise resolved) but not run. Only when the call itself names the
// title, so another tile's music is never blocked by mistake.
uint64_t setsysbgm_hook(uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e, uint64_t f) {
	const std::string text = obj_text(reinterpret_cast<Obj>(b));
	const std::string tid  = title_in(text.c_str());
	char              path[512];
	const bool block = !tid.empty() && g_own_player != nullptr && g_vol_req.load() > 0 &&
	                   !(g_store_only.load() && tid != "NPXS40047") &&
	                   fast_lookup(tid.c_str(), path, sizeof(path)) && path[0] == '/' && !clip_is_silent(path);
	if (block && g_bgm_logs < 20) {
		++g_bgm_logs;
		wp_log("bgm SetSystemBgm (tick %d) tile '%s' -> %s: %.240s", g_tick, tid.c_str(), block ? "BLOCKED" : "runs",
		       text.c_str());
	}
	if (!block) {
		return g_sysbgm_orig(a, b, c, d, e, f);
	}
	Obj promise = reinterpret_cast<Obj>(c);
	Obj pk      = promise != nullptr ? mono_object_get_class(promise) : nullptr;
	Obj resolve = pk != nullptr ? mono_class_get_method_from_name(pk, "Resolve", 1) : nullptr;
	void* args[1] = {nullptr};
	if (resolve == nullptr || !invoke(resolve, promise, args, "IPromise.Resolve")) {
		wp_log("bgm: could not answer the promise, letting Sony's call run");
		return g_sysbgm_orig(a, b, c, d, e, f);
	}
	return 0;
}

// Highlighted tile -> per-game clip; SetSystemBgm (JObject, IPromise: this + 2 pointers) -> game music.
int g_sysbgm_at = -1; // when to hook SetSystemBgm

void avatar_tick();

#ifdef LIVESHELL_RESEARCH_RETRO
// ---- RESEARCH BUILD ONLY: a Game Boy on the home screen (games on the home screen, in development) ----
// The payload runs the emulator (liveshell_retro.c) and sends every frame here (UDP 127.0.0.1:9053, 3 packets of
// 48 lines, one byte per pixel: the shade 0..3); this module turns it into Game Boy green and puts it into the
// texture. Before: a 60 fps test pattern proved the picture can change every frame (SetPixels ~0.05 ms).
// A Game Boy sized texture (160 x 144, RGBA: Sce.PlayStation.Core.Graphics.Texture2D) in an image box on the
// wallpaper layer, 3x (480 x 432), new pixels every frame (SetPixels from a byte[] we write straight into).
// The log says how many frames per second the pixels changed and how long SetPixels took.
constexpr int kRw = 160, kRh = 144;
Obj   g_rt_tex = nullptr, g_rt_set = nullptr, g_rt_arr = nullptr, g_rt_box = nullptr;
// two pictures, in turn: one on screen, one written (shown at the next refresh)
constexpr int kRtPics = 2;
Obj   g_rt_pic[kRtPics] {}, g_rt_asset[kRtPics] {}, g_pop_img = nullptr;
int   g_rt_npic = 1;
int   g_rt_frame = 0, g_rt_start = 0, g_rt_fail = 0;
long  g_rt_t0 = 0, g_rt_us = 0, g_rt_n = 0;

// A method by name, parameter count and the type name of one parameter (overloads with the same count).
Obj method_where(Obj klass, const char* name, int argc, int at, const char* type) {
	void* iter = nullptr;
	while (Obj m = mono_class_get_methods(klass, &iter)) {
		const char* n = mono_method_get_name(m);
		if (n == nullptr || strcmp(n, name) != 0) {
			continue;
		}
		Obj   sig = mono_method_signature(m);
		void* pi  = nullptr;
		int   i = 0, hit = 0;
		while (Obj t = mono_signature_get_params(sig, &pi)) {
			const char* tn = type_name_of(t);
			if (i == at && strstr(tn, type) != nullptr) {
				hit = 1;
			}
			++i;
		}
		if (i == argc && hit) {
			return m;
		}
	}
	return nullptr;
}

uint16_t          g_rf[144 * 160];     // the latest whole frame from the payload (RGB565)
char              g_rf_title[96] = "Game Boy"; // the game's name (from the payload)
// the menu's game list (from the payload): names, which one is loaded
constexpr int     kMaxGames = 200;
char              g_gl_name[kMaxGames][96];
int               g_gl_con[kMaxGames]; // its console: 0 Game Boy, 1 Game Boy Color
std::atomic<int>  g_gl_total{0}, g_gl_cur{-1}, g_gl_new{0};
std::atomic<int>  g_rf_title_new{0};
std::atomic<uint32_t> g_rf_ready{0};   // its number + 1 (0: none yet)
std::atomic<uint32_t> g_rf_seq{0};     // odd while g_rf is being written (the reader copies again: no torn frames)

void* retro_rx_thread(void*) {
	const int   s = socket(AF_INET, SOCK_DGRAM, 0);
	sockaddr_in a {};
	a.sin_family      = AF_INET;
	a.sin_port        = htons(9053);
	a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (s < 0 || bind(s, reinterpret_cast<sockaddr*>(&a), sizeof(a)) != 0) {
		wp_log("retro: cannot listen on 9053");
		return nullptr;
	}
	static uint8_t  pkt[6 + 24 * 160 * 2 + 1];
	static uint16_t part_buf[144 * 160];
	uint32_t       cur = 0;
	int            parts = 0;
	for (;;) {
		const ssize_t n = recv(s, pkt, sizeof(pkt), 0);
		if (n > 1 && pkt[0] == 'L') { // the game list: "L<total>\t<loaded>\t<first>\n" + "<id>\t<console>\t<name>\n" ...
			pkt[n < static_cast<ssize_t>(sizeof(pkt)) ? n : sizeof(pkt) - 1] = 0;
			char* line = reinterpret_cast<char*>(pkt) + 1;
			const int total = atoi(line);
			char* t1 = strchr(line, '\t');
			const int cur = t1 != nullptr ? atoi(t1 + 1) : -1;
			for (char* nl = strchr(line, '\n'); nl != nullptr;) {
				char* row = nl + 1;
				nl        = strchr(row, '\n');
				if (nl == nullptr) {
					break;
				}
				*nl = 0;
				char* tab = strchr(row, '\t');
				char* tab2 = tab != nullptr ? strchr(tab + 1, '\t') : nullptr;
				const int id = atoi(row);
				if (tab2 != nullptr && id >= 0 && id < kMaxGames) {
					g_gl_con[id] = atoi(tab + 1) == 1 ? 1 : 0;
					snprintf(g_gl_name[id], sizeof(g_gl_name[id]), "%s", tab2 + 1);
				}
			}
			g_gl_total.store(total < kMaxGames ? total : kMaxGames);
			g_gl_cur.store(cur);
			g_gl_new.store(1);
			continue;
		}
		if (n > 1 && n < 96 && pkt[0] == 'T') { // the game's name
			memcpy(g_rf_title, pkt + 1, static_cast<size_t>(n - 1));
			g_rf_title[n - 1] = 0;
			g_rf_title_new.store(1);
			continue;
		}
		if (n != static_cast<ssize_t>(6 + 24 * 160 * 2) || pkt[0] != 'H' || pkt[5] > 5) {
			continue;
		}
		uint32_t f = 0;
		memcpy(&f, pkt + 1, 4);
		if (f != cur) {
			cur   = f;
			parts = 0;
		}
		memcpy(part_buf + pkt[5] * 24 * 160, pkt + 6, 24 * 160 * 2);
		parts |= 1 << pkt[5];
		if (parts == 0x3F) {
			g_rf_seq.fetch_add(1); // odd: writing
			memcpy(g_rf, part_buf, sizeof(g_rf));
			g_rf_seq.fetch_add(1); // even: done
			g_rf_ready.store(f + 1);
		}
	}
	return nullptr;
}

// ---- controls: hold R3 0.5 s -> the controller plays the game (and back) ----
struct PadData { // Sce.PlayStation.Core.Input.GamePadData
	bool     Skip;
	uint32_t Buttons, ButtonsPrev, ButtonsDown, ButtonsUp;
	float    LeftX, LeftY, RightX, RightY;
};
using GetDataFn = PadData (*)(int device);
GetDataFn   g_getdata_orig = nullptr;
bool        g_game_mode = false; // playing (the pop-up)
std::atomic<int> g_mode{0};      // 0 home screen, 1 LiveShell Menu, 2 playing
std::atomic<uint32_t> g_menu_keys{0}; // menu presses (edges) for the frame tick: bit 0 up, 1 down, 2 left, 3 right, 4 cross, 5 circle
long        g_r3_since  = 0;
bool        g_r3_done   = false;
int         g_joy_sock  = -1;
sockaddr_in g_joy_to {};

void joy_send(char kind, uint8_t value) {
	if (g_joy_sock < 0) {
		g_joy_sock               = socket(AF_INET, SOCK_DGRAM, 0);
		g_joy_to.sin_family      = AF_INET;
		g_joy_to.sin_port        = htons(9054);
		g_joy_to.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	}
	const char pkt[2] = {kind, static_cast<char>(value)};
	(void)sendto(g_joy_sock, pkt, 2, 0, reinterpret_cast<sockaddr*>(&g_joy_to), sizeof(g_joy_to));
}

PadData GetData_Hook(int device) {
	PadData d = g_getdata_orig(device);
	if (d.Buttons & 0x8000u) { // R3 held
		const long t = now_ms();
		if (g_r3_since == 0) {
			g_r3_since = t;
		} else if (!g_r3_done && t - g_r3_since >= 500) {
			g_r3_done   = true;
			const int m = g_mode.load();
			// home -> menu, menu -> home, playing -> menu (the game pauses)
			g_mode.store(m == 1 ? 0 : 1);
			g_game_mode = false;
			joy_send('M', 0);
			joy_send('J', 0xFF);
			if (m == 0) {
				joy_send('Q', 0);
			}
			wp_log("retro: %s", m == 1 ? "menu closed" : "LiveShell Menu");
		}
	} else {
		g_r3_since = 0;
		g_r3_done  = false;
	}
	if (g_mode.load() == 0) {
		return d;
	}
	if (g_mode.load() == 1) { // the menu: presses (with repeat while held) for the frame tick; the home screen sees nothing
		static uint32_t held = 0;
		static long     since = 0, rep_at = 0;
		const uint32_t  dirs  = d.Buttons & 0xFu;
		const uint32_t  now_b = d.Buttons;
		const long      tm    = now_ms();
		uint32_t        keys  = 0;
		auto edge = [&](uint32_t mask) { return (now_b & mask) && !(held & mask); };
		if (edge(0x2u)) keys |= 1;
		if (edge(0x8u)) keys |= 2;
		if (edge(0x1u)) keys |= 4;
		if (edge(0x4u)) keys |= 8;
		if (edge(0x80u)) keys |= 16;
		if (edge(0x40u)) keys |= 32;
		if (dirs != (held & 0xFu)) {
			since = tm, rep_at = tm + 380;
		} else if (dirs != 0 && tm >= rep_at) { // held: repeat up / down
			rep_at = tm + 110;
			keys |= (dirs & 0x2u ? 1 : 0) | (dirs & 0x8u ? 2 : 0);
		}
		(void)since;
		held = now_b;
		if (keys != 0) {
			g_menu_keys.fetch_or(keys);
		}
		d.Buttons &= 0x8000u;
		d.ButtonsPrev = d.ButtonsDown = d.ButtonsUp = 0;
		d.LeftX = d.LeftY = d.RightX = d.RightY = 0.0f;
		return d;
	}
	// playing: Game Boy buttons (0 = pressed): d-pad / left stick, cross or circle = A, square or triangle = B,
	// Options = START, Create = SELECT
	const uint32_t b = d.Buttons;
	uint8_t        j = 0xFF;
	if ((b & 0x80u) || (b & 0x40u)) j &= ~0x01; // A
	if ((b & 0x10u) || (b & 0x20u)) j &= ~0x02; // B
	if (b & 0x200u) j &= ~0x04;                 // SELECT
	if (b & 0x100u) j &= ~0x08;                 // START
	if ((b & 0x4u) || d.LeftX > 0.5f) j &= ~0x10;  // right
	if ((b & 0x1u) || d.LeftX < -0.5f) j &= ~0x20; // left
	if ((b & 0x2u) || d.LeftY < -0.5f) j &= ~0x40; // up
	if ((b & 0x8u) || d.LeftY > 0.5f) j &= ~0x80;  // down
	static uint8_t last = 0xFF;
	static long    sent = 0;
	const long     now  = now_ms();
	if (j != last || now - sent >= 100) {
		joy_send('J', j);
		last = j;
		sent = now;
	}
	// the home screen sees an idle controller (R3 stays visible: holding it again gives it back)
	d.Buttons &= 0x8000u;
	d.ButtonsPrev = d.ButtonsDown = d.ButtonsUp = 0;
	d.LeftX = d.LeftY = d.RightX = d.RightY = 0.0f;
	return d;
}

// The pop-up: a container (a dim over everything + the game 5x, 800 x 720, in the middle) appended as the LAST
// child of the home screen's own scene (the AppScene in SceneManager's render list): drawn on top of the home
// screen's content. Shown / hidden with Visible from the frame tick. (A scene of our own was Show()n "ok" but
// never drawn: only scenes registered with the home screen's scene system are.)
Obj  g_pop_box = nullptr, g_pop_wk = nullptr, g_pop_host = nullptr;
bool g_pop_on  = false;

Obj prop_up(Obj obj, const char* name) { // a property's value, looked up in the class and its parents
	for (Obj k = obj != nullptr ? mono_object_get_class(obj) : nullptr; k != nullptr; k = mono_class_get_parent(k)) {
		Obj prop = mono_class_get_property_from_name(k, name);
		Obj get  = prop != nullptr ? mono_property_get_get_method(prop) : nullptr;
		if (get != nullptr) {
			Obj exc = nullptr;
			Obj r   = mono_runtime_invoke(get, obj, nullptr, &exc);
			return exc == nullptr ? r : nullptr;
		}
	}
	return nullptr;
}

bool prop_set_up(Obj obj, const char* name, void* value) { // set a property found in the class or its parents
	for (Obj k = obj != nullptr ? mono_object_get_class(obj) : nullptr; k != nullptr; k = mono_class_get_parent(k)) {
		Obj prop = mono_class_get_property_from_name(k, name);
		Obj set  = prop != nullptr ? mono_property_get_set_method(prop) : nullptr;
		if (set != nullptr) {
			void* args[1] = {value};
			return invoke(set, obj, args, name);
		}
	}
	wp_log("no setter %s (in any parent)", name);
	return false;
}

// The home screen's scene root: the first AppScene in SceneManager's render list.
Obj home_scene_root(Obj pui) {
	Obj sm   = mono_class_from_name(pui, "Sce.PlayStation.PUI", "SceneManager");
	Obj ip   = sm != nullptr ? mono_class_get_property_from_name(sm, "Instance") : nullptr;
	Obj ig   = ip != nullptr ? mono_property_get_get_method(ip) : nullptr;
	Obj exc  = nullptr;
	Obj inst = ig != nullptr ? mono_runtime_invoke(ig, nullptr, nullptr, &exc) : nullptr;
	Obj list = exc == nullptr && inst != nullptr ? prop_up(inst, "RenderList") : nullptr;
	Obj cnt  = list != nullptr ? prop_up(list, "Count") : nullptr;
	Obj item = list != nullptr ? mono_class_get_method_from_name(mono_object_get_class(list), "get_Item", 1) : nullptr;
	const int n = cnt != nullptr ? *reinterpret_cast<int*>(static_cast<char*>(cnt) + 16) : 0;
	for (int i = 0; i < n && item != nullptr; ++i) {
		void* args[1] = {&i};
		Obj   e       = nullptr;
		Obj   sc      = mono_runtime_invoke(item, list, args, &e);
		const char* cn = e == nullptr && sc != nullptr ? mono_class_get_name(mono_object_get_class(sc)) : nullptr;
		if (cn != nullptr && strcmp(cn, "AppScene") == 0) {
			return prop_up(sc, "RootWidget");
		}
	}
	return nullptr;
}

void retro_popup_setup(Obj pui, Obj asset, Obj wk) {
	Obj bk  = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "ImageBox");
	Obj box = mono_object_new(g_domain, wk);
	Obj wc  = mono_class_get_method_from_name(wk, ".ctor", 0);
	if (box == nullptr || wc == nullptr || !invoke(wc, box, nullptr, "Widget(pop)")) {
		wp_log("retro: no pop-up container");
		return;
	}
	mono_gchandle_new(box, 1);
	float z = 0.0f, fw = 1920.0f, fh = 1080.0f;
	property_set(wk, box, "X", &z);
	property_set(wk, box, "Y", &z);
	property_set(wk, box, "Width", &fw);
	property_set(wk, box, "Height", &fh);
	Obj  apnd  = find_method_up(wk, "AppendChild", 1);
	bool dimok = false;
	if (g_dim_class != nullptr && g_dim_prop != nullptr) { // the dim: as the wallpaper's dim layer
		Obj dim = mono_object_new(g_domain, g_dim_class);
		Obj dc  = mono_class_get_method_from_name(g_dim_class, ".ctor", 0);
		if (dim != nullptr && dc != nullptr && invoke(dc, dim, nullptr, "dim()")) {
			property_set(wk, dim, "X", &z);
			property_set(wk, dim, "Y", &z);
			property_set(wk, dim, "Width", &fw);
			property_set(wk, dim, "Height", &fh);
			if (has_setter(g_dim_class, "BackgroundVisibility")) {
				bool on = true;
				property_set(g_dim_class, dim, "BackgroundVisibility", &on);
			}
			void* c    = black(0.72f);
			void* a[1] = {dim};
			dimok      = c != nullptr && property_set(g_dim_class, dim, g_dim_prop, c) && invoke(apnd, box, a, "AppendChild(pop dim)");
		}
	}
	{ // the bezel: a retro frame around the screen (drawn for LiveShell, written by the payload)
		Obj bz = bk != nullptr ? mono_object_new(g_domain, bk) : nullptr;
		Obj zc = bk != nullptr ? mono_class_get_method_from_name(bk, ".ctor", 0) : nullptr;
		Obj ld = bk != nullptr ? find_method_up(bk, "LoadAsync", 1) : nullptr;
		if (bz != nullptr && zc != nullptr && invoke(zc, bz, nullptr, "ImageBox(bezel)")) {
			mono_gchandle_new(bz, 1);
			float bx = 420.0f, by = 48.0f, bw2 = 1080.0f, bh2 = 984.0f;
			property_set(wk, bz, "X", &bx);
			property_set(wk, bz, "Y", &by);
			property_set(wk, bz, "Width", &bw2);
			property_set(wk, bz, "Height", &bh2);
			void* la[1] = {mono_string_new(g_domain, "/system_ex/vsh_asset/wallpaper/.retroui/bezel.png")};
			if (ld != nullptr) {
				invoke(ld, bz, la, "ImageBox.LoadAsync(bezel)");
			}
			void* ba[1] = {bz};
			invoke(apnd, box, ba, "AppendChild(bezel)");
		}
	}
	Obj big = bk != nullptr ? mono_object_new(g_domain, bk) : nullptr;
	Obj bc  = bk != nullptr ? mono_class_get_method_from_name(bk, ".ctor", 0) : nullptr;
	if (big == nullptr || bc == nullptr || !invoke(bc, big, nullptr, "ImageBox(pop)")) {
		return;
	}
	mono_gchandle_new(big, 1);
	g_pop_img = big;
	property_set(bk, big, "Image", asset); // the same texture as the mini screen
	float x = 480.0f, y = 108.0f, w = 960.0f, h = 864.0f; // 6x: the whole Game Boy screen, sharp
	property_set(wk, big, "X", &x);
	property_set(wk, big, "Y", &y);
	property_set(wk, big, "Width", &w);
	property_set(wk, big, "Height", &h);
	void* a[1] = {big};
	invoke(apnd, box, a, "AppendChild(pop game)");
	bool off = false;
	prop_set_up(box, "Visible", &off);
	g_pop_box = box;
	g_pop_wk  = wk;
	wp_log("retro: pop-up ready (dim %s)", dimok ? "on" : "none");
}

// ---- the card: in the middle of the home screen when you stop playing (6 s) ----
Obj g_card = nullptr, g_card_title = nullptr, g_label_class = nullptr;
int g_card_until = 0;

void* rgba(float r, float g, float b, float a) { // a UIColor
	Obj boxed = g_color_class != nullptr ? mono_object_new(g_domain, g_color_class) : nullptr;
	if (boxed == nullptr) {
		return nullptr;
	}
	mono_gchandle_new(boxed, 1);
	void* raw     = mono_object_unbox(boxed);
	void* args[4] = {&r, &g, &b, &a};
	return invoke(mono_class_get_method_from_name(g_color_class, ".ctor", 4), raw, args, "UIColor()") ? raw : nullptr;
}

Obj add_widget(Obj klass, Obj parent, Obj wk, float x, float y, float w, float h) {
	Obj o = klass != nullptr ? mono_object_new(g_domain, klass) : nullptr;
	Obj c = klass != nullptr ? mono_class_get_method_from_name(klass, ".ctor", 0) : nullptr;
	if (o == nullptr || c == nullptr || !invoke(c, o, nullptr, "new widget")) {
		return nullptr;
	}
	mono_gchandle_new(o, 1);
	prop_set_up(o, "X", &x);
	prop_set_up(o, "Y", &y);
	prop_set_up(o, "Width", &w);
	prop_set_up(o, "Height", &h);
	if (parent != nullptr) {
		void* a[1] = {o};
		invoke(find_method_up(wk, "AppendChild", 1), parent, a, "AppendChild(card)");
	}
	return o;
}

Obj add_label(Obj parent, Obj wk, float y, float h, const char* text, float grey) {
	Obj l = add_widget(g_label_class, parent, wk, 24.0f, y, 472.0f, h);
	if (l != nullptr) {
		prop_set_up(l, "Text", mono_string_new(g_domain, text));
		if (void* c = rgba(grey, grey, grey, 1.0f)) {
			prop_set_up(l, "TextColor", c);
		}
	}
	return l;
}

void retro_card_setup(Obj pui, Obj asset, Obj wk) {
	g_label_class = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Label");
	Obj bk        = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "ImageBox");
	Obj card      = add_widget(wk, nullptr, wk, 700.0f, 250.0f, 520.0f, 560.0f); // the middle of the screen
	if (card == nullptr) {
		return;
	}
	if (g_dim_class != nullptr && g_dim_prop != nullptr) { // its background: a dark panel
		Obj bg = add_widget(g_dim_class, card, wk, 0.0f, 0.0f, 520.0f, 560.0f);
		if (bg != nullptr) {
			if (has_setter(g_dim_class, "BackgroundVisibility")) {
				bool on = true;
				property_set(g_dim_class, bg, "BackgroundVisibility", &on);
			}
			if (void* c = rgba(0.07f, 0.07f, 0.08f, 0.94f)) {
				property_set(g_dim_class, bg, g_dim_prop, c);
			}
		}
	}
	Obj img = add_widget(bk, card, wk, 20.0f, 20.0f, 480.0f, 432.0f); // the paused game, 3x
	if (img != nullptr) {
		prop_set_up(img, "Image", asset);
	}
	g_card_title = add_label(card, wk, 466.0f, 40.0f, g_rf_title, 1.0f);
	add_label(card, wk, 506.0f, 34.0f, "Hold R3 to play", 0.62f);
	bool off = false;
	prop_set_up(card, "Visible", &off);
	g_card = card;
	wp_log("retro: card ready (label %p)", g_label_class);
}

// Put a widget on top of the home screen's own scene (its last child) and show / hide it.
void show_on_home(Obj w, bool on) {
	if (w == nullptr) {
		return;
	}
	if (on) {
		Obj pui  = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
		Obj root = pui != nullptr ? home_scene_root(pui) : nullptr;
		if (root != nullptr) {
			if (prop_up(w, "Parent") != nullptr) {
				invoke(find_method_up(g_pop_wk, "RemoveFromParent", 0), w, nullptr, "RemoveFromParent");
			}
			void* a[1] = {w};
			invoke(find_method_up(g_pop_wk, "AppendChild", 1), root, a, "AppendChild(home)");
		}
	}
	prop_set_up(w, "Visible", &on);
}

// ---- the LiveShell Menu: consoles left, the games as a list of names right ----
constexpr int kRows = 7;
Obj   g_menu = nullptr, g_panel_class = nullptr;
const char* g_panel_prop = nullptr;
constexpr int kCons = 2;
const char* const kConName[kCons] = {"Game Boy", "Game Boy Color"};
Obj   g_con_bg[kCons] {}, g_con_label[kCons] {}, g_con_count[kCons] {}, g_head = nullptr, g_empty = nullptr;
int   g_con = 0; // the chosen console
Obj   g_row_bg[kRows] {}, g_row_name[kRows] {}, g_row_tag[kRows] {};
int   g_sel = 0, g_top = 0, g_focus = 1; // selected game, first row shown, focus: 0 consoles / 1 games

void* ui_font(int size, bool bold) { // a UIFont (a struct: boxed, the data passed)
	static Obj fk = nullptr;
	if (fk == nullptr) {
		Obj pui = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
		fk      = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "UIFont") : nullptr;
	}
	Obj boxed = fk != nullptr ? mono_object_new(g_domain, fk) : nullptr;
	if (boxed == nullptr) {
		return nullptr;
	}
	mono_gchandle_new(boxed, 1);
	void* raw     = mono_object_unbox(boxed);
	int   style = 0, weight = bold ? 2 : 1;
	void* args[3] = {&size, &style, &weight};
	return invoke(mono_class_get_method_from_name(fk, ".ctor", 3), raw, args, "UIFont()") ? raw : nullptr;
}

Obj panel(Obj parent, Obj wk, float x, float y, float w, float h, float grey, float alpha, float radius = 0.0f) {
	Obj p = add_widget(g_panel_class, parent, wk, x, y, w, h);
	if (p != nullptr) {
		if (radius > 0.0f) {
			prop_set_up(p, "BorderRadius", &radius);
		}
		if (has_setter(g_panel_class, "BackgroundVisibility")) {
			bool on = true;
			property_set(g_panel_class, p, "BackgroundVisibility", &on);
		}
		if (void* c = rgba(grey, grey, grey, alpha)) {
			property_set(g_panel_class, p, g_panel_prop, c);
		}
	}
	return p;
}

void tint(Obj p, float grey, float alpha) {
	if (p != nullptr) {
		if (void* c = rgba(grey, grey, grey, alpha)) {
			property_set(g_panel_class, p, g_panel_prop, c);
		}
	}
}

Obj text(Obj parent, Obj wk, float x, float y, float w, float h, const char* t, int size, bool bold, float grey) {
	Obj l = add_widget(g_label_class, parent, wk, x, y, w, h);
	if (l != nullptr) {
		if (void* f = ui_font(size, bold)) {
			prop_set_up(l, "Font", f);
		}
		prop_set_up(l, "Text", mono_string_new(g_domain, t));
		if (void* c = rgba(grey, grey, grey, 1.0f)) {
			prop_set_up(l, "TextColor", c);
		}
	}
	return l;
}

void set_text(Obj l, const char* t, float grey) {
	if (l != nullptr) {
		prop_set_up(l, "Text", mono_string_new(g_domain, t));
		if (void* c = rgba(grey, grey, grey, 1.0f)) {
			prop_set_up(l, "TextColor", c);
		}
	}
}

void retro_menu_setup(Obj pui, Obj wk) {
	g_label_class = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Label");
	if (g_color_class == nullptr) {
		g_color_class = mono_class_from_name(pui, "Sce.PlayStation.PUI", "UIColor");
	}
	// a widget that can be filled with a colour (as the dim layer finds it)
	static const char* const kClasses[] = {"Panel", "Rectangle", "ColorRect", "Plane", "Box", "Widget"};
	static const char* const kColors[]  = {"BackgroundColor", "Color", "FillColor", "BaseColor"};
	for (const char* cn : kClasses) {
		Obj k = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", cn);
		for (const char* c : kColors) {
			if (k != nullptr && g_panel_prop == nullptr && has_setter(k, c)) {
				g_panel_class = k;
				g_panel_prop  = c;
			}
		}
		if (g_panel_prop != nullptr) {
			break;
		}
	}
	if (g_panel_class == nullptr || g_label_class == nullptr || g_color_class == nullptr) {
		wp_log("retro: menu classes panel %p label %p colour %p", g_panel_class, g_label_class, g_color_class);
		return;
	}
	Obj m = add_widget(wk, nullptr, wk, 0.0f, 0.0f, 1920.0f, 1080.0f);
	if (m == nullptr) {
		return;
	}
	panel(m, wk, 0.0f, 0.0f, 1920.0f, 1080.0f, 0.0f, 0.6f); // the home screen a little darker behind it
	// the card: solid, rounded, in the middle; everything else inside it
	Obj card = panel(m, wk, 440.0f, 220.0f, 1040.0f, 640.0f, 0.07f, 1.0f, 28.0f);
	if (card == nullptr) {
		return;
	}
	text(card, wk, 40.0f, 30.0f, 600.0f, 50.0f, "PlayShell", 34, true, 1.0f);
	g_head = text(card, wk, 40.0f, 80.0f, 600.0f, 32.0f, "Game Boy", 20, false, 0.6f);
	panel(card, wk, 40.0f, 126.0f, 960.0f, 2.0f, 0.2f, 1.0f); // divider
	// the consoles
	for (int c = 0; c < kCons; ++c) {
		const float y   = 148.0f + c * 106.0f;
		g_con_bg[c]     = panel(card, wk, 40.0f, y, 250.0f, 96.0f, 0.14f, 1.0f, 16.0f);
		{ // the console's icon (drawn for LiveShell, written by the payload)
			Obj bk = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "ImageBox");
			Obj ib = add_widget(bk, card, wk, 52.0f, y + 16.0f, 64.0f, 64.0f);
			Obj ld = bk != nullptr ? find_method_up(bk, "LoadAsync", 1) : nullptr;
			if (ib != nullptr && ld != nullptr) {
				void* a[1] = {mono_string_new(g_domain, c == 0 ? "/system_ex/vsh_asset/wallpaper/.retroui/console_gb.png"
				                                               : "/system_ex/vsh_asset/wallpaper/.retroui/console_gbc.png")};
				invoke(ld, ib, a, "ImageBox.LoadAsync(console)");
			}
		}
		g_con_label[c] = text(card, wk, 126.0f, y + 16.0f, 160.0f, 32.0f, kConName[c], 19, true, 1.0f); // full names
		g_con_count[c] = text(card, wk, 128.0f, y + 52.0f, 156.0f, 28.0f, "0 games", 18, false, 0.6f);
	}
	// the games
	for (int i = 0; i < kRows; ++i) {
		const float y = 148.0f + i * 58.0f;
		g_row_bg[i]   = panel(card, wk, 310.0f, y, 690.0f, 50.0f, 0.14f, 1.0f, 12.0f);
		g_row_name[i] = text(card, wk, 332.0f, y + 9.0f, 520.0f, 34.0f, "", 22, false, 1.0f);
		g_row_tag[i]  = text(card, wk, 870.0f, y + 12.0f, 120.0f, 28.0f, "", 18, false, 0.6f);
	}
	g_empty = text(card, wk, 310.0f, 156.0f, 690.0f, 80.0f, "No games yet. Put your games (.gb / .gbc) in /data/LiveShell/roms", 20, false, 0.7f);
	// the footer: the hints on their own bar
	panel(card, wk, 0.0f, 572.0f, 1040.0f, 68.0f, 0.12f, 1.0f, 28.0f); // rounded like the card at the bottom
	panel(card, wk, 0.0f, 572.0f, 1040.0f, 34.0f, 0.12f, 1.0f);        // square at the top
	// the hints: button icon + word (the icons: drawn for LiveShell, written by the payload)
	{
		Obj bk = mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "ImageBox");
		Obj ld = bk != nullptr ? find_method_up(bk, "LoadAsync", 1) : nullptr;
		static const char* const icon[3] = {"cross", "circle", "r3"};
		static const char* const word[3] = {"Play", "Close", "Hold  Menu"};
		float x = 40.0f;
		for (int i = 0; i < 3; ++i) {
			Obj ib = add_widget(bk, card, wk, x, 588.0f, 36.0f, 36.0f);
			if (ib != nullptr && ld != nullptr) {
				char path[96];
				snprintf(path, sizeof(path), "/system_ex/vsh_asset/wallpaper/.retroui/%s.png", icon[i]);
				void* a[1] = {mono_string_new(g_domain, path)};
				invoke(ld, ib, a, "ImageBox.LoadAsync(icon)");
			}
			text(card, wk, x + 46.0f, 592.0f, 160.0f, 32.0f, word[i], 20, false, 0.88f);
			x += i == 1 ? 200.0f : 170.0f;
		}
	}
	bool off = false;
	prop_set_up(m, "Visible", &off);
	g_menu = m;
	wp_log("retro: menu ready (panel %s.%s)", mono_class_get_name(g_panel_class), g_panel_prop);
}

// The chosen console's games (ids in list order).
int con_games(int con, int* ids) {
	const int total = g_gl_total.load();
	int       k     = 0;
	for (int id = 0; id < total; ++id) {
		if (g_gl_con[id] == con) {
			ids[k++] = id;
		}
	}
	return k;
}

void menu_render() {
	static int ids[kMaxGames];
	const int  total = con_games(g_con, ids), cur = g_gl_cur.load();
	g_sel = total > 0 ? std::max(0, std::min(g_sel, total - 1)) : 0;
	if (g_sel < g_top) {
		g_top = g_sel;
	} else if (g_sel >= g_top + kRows) {
		g_top = g_sel - kRows + 1;
	}
	for (int c = 0; c < kCons; ++c) {
		static int tmp[kMaxGames];
		const int  k = con_games(c, tmp);
		char       n[24];
		snprintf(n, sizeof(n), "%d game%s", k, k == 1 ? "" : "s");
		const bool chosen = c == g_con;
		set_text(g_con_count[c], n, chosen ? 0.8f : 0.6f);
		// the chosen one lighter; brighter still while the consoles have the focus
		tint(g_con_bg[c], chosen ? (g_focus == 0 ? 0.36f : 0.24f) : 0.12f, 1.0f);
		set_text(g_con_label[c], kConName[c], chosen ? 1.0f : 0.75f);
	}
	char head[64];
	snprintf(head, sizeof(head), "%s  -  %d game%s", kConName[g_con], total, total == 1 ? "" : "s");
	set_text(g_head, head, 0.6f);
	bool show_empty = total == 0;
	prop_set_up(g_empty, "Visible", &show_empty);
	for (int i = 0; i < kRows; ++i) {
		const int  row = g_top + i;
		bool       vis = row < total;
		prop_set_up(g_row_bg[i], "Visible", &vis);
		prop_set_up(g_row_name[i], "Visible", &vis);
		prop_set_up(g_row_tag[i], "Visible", &vis);
		if (!vis) {
			continue;
		}
		const int  id = ids[row];
		const bool on = g_focus == 1 && row == g_sel;
		tint(g_row_bg[i], on ? 1.0f : 0.13f, 1.0f);
		set_text(g_row_name[i], g_gl_name[id], on ? 0.0f : 1.0f);
		set_text(g_row_tag[i], id == cur ? "Continue" : "", on ? 0.3f : 0.6f);
	}
}

// From the frame tick: open / close, the presses, the list.
void retro_menu_tick() {
	static int shown = 0;
	const int  mode  = g_mode.load();
	if (g_menu == nullptr) {
		return;
	}
	if ((mode == 1) != (shown == 1)) {
		shown = mode == 1;
		if (shown) {
			const int cur = g_gl_cur.load();
			if (cur >= 0 && cur < kMaxGames) { // on the game you were playing, in its console
				static int ids[kMaxGames];
				g_con         = g_gl_con[cur];
				const int k   = con_games(g_con, ids);
				for (int i = 0; i < k; ++i) {
					if (ids[i] == cur) {
						g_sel = i;
					}
				}
			}
			g_focus = 1;
			menu_render();
		}
		show_on_home(g_menu, shown == 1);
	}
	if (mode != 1) {
		g_menu_keys.store(0);
		return;
	}
	const uint32_t keys = g_menu_keys.exchange(0);
	bool           redo = g_gl_new.exchange(0) != 0;
	static int     ids[kMaxGames];
	const int      total = con_games(g_con, ids);
	// up / down: the games, or (focus on the consoles) the console - its list shows at once
	if (keys & 1) { if (g_focus == 1) --g_sel; else if (g_con > 0) { --g_con; g_sel = g_top = 0; } redo = true; }
	if (keys & 2) { if (g_focus == 1) ++g_sel; else if (g_con < kCons - 1) { ++g_con; g_sel = g_top = 0; } redo = true; }
	if (keys & 4) { g_focus = 0; redo = true; }
	if (keys & 8) { g_focus = total > 0 ? 1 : 0; redo = true; }
	if (keys & 32) { // Circle: close
		g_mode.store(0);
		return;
	}
	if ((keys & 16) && g_focus == 0) {
		g_focus = total > 0 ? 1 : 0;
		redo    = true;
		(void)total;
	} else if ((keys & 16) && total > 0) { // Cross: play it
		char cmd[16];
		const int id = ids[std::max(0, std::min(g_sel, total - 1))];
		const int k  = snprintf(cmd, sizeof(cmd), "P%d", id);
		if (g_joy_sock < 0) {
			joy_send('J', 0xFF);
		}
		(void)sendto(g_joy_sock, cmd, static_cast<size_t>(k), 0, reinterpret_cast<sockaddr*>(&g_joy_to), sizeof(g_joy_to));
		g_mode.store(2);
		g_game_mode = true;
		wp_log("retro: play %s", g_gl_name[id]);
		return;
	}
	if (redo) {
		menu_render();
	}
}

// From the frame tick (the UI thread): the pop-up follows the controller mode. Shown: (again) the last child of
// the home screen's scene, so it is on top of whatever the home screen added since.
void retro_popup_tick(bool playing) {
	if (g_rf_title_new.exchange(0) && g_card_title != nullptr) {
		prop_set_up(g_card_title, "Text", mono_string_new(g_domain, g_rf_title));
	}
	if (g_card_until != 0 && g_tick >= g_card_until) { // the card's 6 s are over
		g_card_until = 0;
		show_on_home(g_card, false);
	}
	if (g_pop_box == nullptr || playing == g_pop_on) {
		return;
	}
	g_pop_on = playing;
	if (g_own_player != nullptr && g_vplayer_class != nullptr) { // the game's sound alone while playing
		player_mute(g_vplayer_class, g_own_player, playing || g_aud_muted);
		set_bgm_suppression(g_vplayer_class, g_own_player, playing ? false : (g_aud_muted || g_clip_silent));
		wp_log("retro: wallpaper sound %s, home music %s", playing ? "muted" : "back", playing ? "held back" : "as before");
	}
	if (playing) { // playing: no card
		g_card_until = 0;
		show_on_home(g_card, false);
	}
	if (playing) {
		Obj pui  = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
		Obj root = pui != nullptr ? home_scene_root(pui) : nullptr;
		if (root != nullptr) {
			Obj   rm      = find_method_up(g_pop_wk, "RemoveFromParent", 0);
			Obj   parent  = prop_up(g_pop_box, "Parent");
			void* a[1]    = {g_pop_box};
			if (parent != nullptr && rm != nullptr) {
				invoke(rm, g_pop_box, nullptr, "RemoveFromParent(pop)");
			}
			invoke(find_method_up(g_pop_wk, "AppendChild", 1), root, a, "AppendChild(pop)");
			g_pop_host = root;
		}
		wp_log("retro: pop-up on the home screen's scene (%s)", root != nullptr ? "found" : "NOT found");
	}
	bool vis = playing;
	const bool ok = prop_set_up(g_pop_box, "Visible", &vis);
	wp_log("retro: pop-up %s (%s)", playing ? "shown" : "hidden", ok ? "ok" : "FAILED");
}

// ---- the game's sound, played from inside the home screen (the PS5 lets the home screen be heard) ----
// the PS5's audio out, looked up in the home screen's own libSceAudioOut (no link: normal builds stay as they are)
int (*sceAudioOutInit)(void)                                                                         = nullptr;
int (*sceAudioOutOpen)(int32_t user_id, int32_t type, int32_t index, uint32_t len, uint32_t freq, uint32_t param) = nullptr;
int (*sceAudioOutOutput)(int32_t handle, const void* buf)                                            = nullptr;

void* retro_sound_thread(void*) {
	const int   s = socket(AF_INET, SOCK_DGRAM, 0);
	sockaddr_in a {};
	a.sin_family      = AF_INET;
	a.sin_port        = htons(9055);
	a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	int big = 256 * 1024;
	setsockopt(s, SOL_SOCKET, SO_RCVBUF, &big, sizeof(big));
	if (s < 0 || bind(s, reinterpret_cast<sockaddr*>(&a), sizeof(a)) != 0) {
		wp_log("retro: sound: cannot listen on 9055");
		return nullptr;
	}
	// looking up / loading modules in the home screen needs the raised authid (as for Mono's functions)
	const uintptr_t old = set_ucred_to_ptrace();
	int lib = get_module_handle(getpid(), "libSceAudioOut.sprx");
	if (lib <= 0) { // not loaded in the home screen: load it (as the payload loads system libraries for the tile)
		const int kh   = get_module_handle(getpid(), "libkernel_sys.sprx");
		using LoadFn   = int (*)(const char*, size_t, const void*, uint32_t, const void*, int*);
		LoadFn    load = kh > 0 ? reinterpret_cast<LoadFn>(kernel_dynlib_dlsym(-1, static_cast<uint32_t>(kh), "sceKernelLoadStartModule")) : nullptr;
		for (const char* root : {"/system/common/lib/", "/system/priv/lib/", "/system_ex/common_ex/lib/"}) {
			if (load == nullptr || lib > 0) {
				break;
			}
			char path[96];
			snprintf(path, sizeof(path), "%slibSceAudioOut.sprx", root);
			int       res = 0;
			const int id  = load(path, 0, nullptr, 0, nullptr, &res);
			wp_log("retro: sound: load %s -> %#x (res %d)", path, static_cast<unsigned>(id), res);
			if (id >= 0) {
				lib = get_module_handle(getpid(), "libSceAudioOut.sprx");
				lib = lib > 0 ? lib : id;
			}
		}
	}
	const bool found = lib > 0 && resolve(lib, sceAudioOutInit, "sceAudioOutInit") && resolve(lib, sceAudioOutOpen, "sceAudioOutOpen") &&
	                   resolve(lib, sceAudioOutOutput, "sceAudioOutOutput");
	if (old != 0) {
		set_proc_authid(getpid(), old);
	}
	if (!found) {
		wp_log("retro: sound: libSceAudioOut not found in the home screen (handle %d)", lib);
		return nullptr;
	}
	wp_log("retro: sound: libSceAudioOut handle %d", lib);
	const int init = sceAudioOutInit();
	const int port = sceAudioOutOpen(0xff, 0, 0, 256, 48000, 1); // system user, main port, S16 stereo, 48 kHz
	wp_log("retro: sound: init %#x, port %#x (in the home screen)", init, port);
	if (port < 0) {
		return nullptr;
	}
	constexpr unsigned kRing = 16384; // stereo frames (~0.34 s)
	static int16_t     ring[kRing * 2];
	static int16_t     grain[256 * 2];
	static uint8_t     pkt[1 + 1024 * 4];
	unsigned           w = 0, r = 0;
	long               last_audio = 0;
	for (;;) {
		ssize_t n;
		while ((n = recv(s, pkt, sizeof(pkt), MSG_DONTWAIT)) > 1) {
			if (pkt[0] != 'A') {
				continue;
			}
			const int16_t* smp    = reinterpret_cast<const int16_t*>(pkt + 1);
			const unsigned frames = static_cast<unsigned>(n - 1) / 4;
			for (unsigned i = 0; i < frames; ++i) {
				if (w - r >= kRing) {
					++r; // full: the oldest goes
				}
				ring[(w % kRing) * 2]     = smp[i * 2];
				ring[(w % kRing) * 2 + 1] = smp[i * 2 + 1];
				++w;
			}
			last_audio = now_ms();
		}
		// a little in hand before playing (no crackle at the start); paused / no game: silence
		const bool play = g_mode.load() == 2 && now_ms() - last_audio < 200 && w - r >= 256;
		for (int i = 0; i < 256; ++i) {
			if (play && r != w) {
				grain[i * 2]     = ring[(r % kRing) * 2];
				grain[i * 2 + 1] = ring[(r % kRing) * 2 + 1];
				++r;
			} else {
				grain[i * 2] = grain[i * 2 + 1] = 0;
			}
		}
		if (g_mode.load() != 2) {
			r = w; // nothing old plays when it goes on
		}
		if (sceAudioOutOutput(port, grain) < 0) { // waits for the previous grain: it sets the pace
			usleep(5000);
		}
	}
	return nullptr;
}

bool retro_setup() {
	void* lib = nullptr;
	(void)lib;
	Obj core = open_image("/system_ex/common_ex/lib/Sce.PlayStation.Core.dll");
	Obj pui  = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	Obj tk   = core != nullptr ? mono_class_from_name(core, "Sce.PlayStation.Core.Graphics", "Texture2D") : nullptr;
	Obj ak   = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI", "ImageAsset") : nullptr;
	Obj bk   = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "ImageBox") : nullptr;
	if (tk == nullptr || ak == nullptr || bk == nullptr || mono_array_new == nullptr || mono_get_byte_class == nullptr) {
		wp_log("retro: classes tex %p asset %p box %p, array_new %p", tk, ak, bk, reinterpret_cast<void*>(mono_array_new));
		return false;
	}
	// texture: new Texture2D(160, 144, false, PixelFormat.Rgba)
	Obj tex  = mono_object_new(g_domain, tk);
	Obj tctr = mono_class_get_method_from_name(tk, ".ctor", 4);
	int w = kRw, h = kRh, fmt = 1; // PixelFormat.Rgba
	bool no = false;
	void* targs[4] = {&w, &h, &no, &fmt};
	if (tex == nullptr || tctr == nullptr || !invoke(tctr, tex, targs, "Texture2D(160,144,Rgba)")) {
		return false;
	}
	g_rt_set = method_where(tk, "SetPixels", 2, 1, "System.Array");
	g_rt_arr = mono_array_new(g_domain, mono_get_byte_class(), static_cast<uintptr_t>(kRw * kRh * 4));
	// asset + image box on the wallpaper layer
	Obj actr  = method_where(ak, ".ctor", 1, 0, "Texture");
	Obj asset = mono_object_new(g_domain, ak);
	void* aargs[1] = {tex};
	if (g_rt_set == nullptr || g_rt_arr == nullptr || actr == nullptr || asset == nullptr || !invoke(actr, asset, aargs, "ImageAsset(Texture)")) {
		wp_log("retro: SetPixels %p array %p asset ctor %p", g_rt_set, g_rt_arr, actr);
		return false;
	}
	Obj box  = mono_object_new(g_domain, bk);
	Obj bctr = mono_class_get_method_from_name(bk, ".ctor", 0);
	if (box == nullptr || bctr == nullptr || !invoke(bctr, box, nullptr, "ImageBox()")) {
		return false;
	}
	mono_gchandle_new(tex, 1);
	mono_gchandle_new(g_rt_arr, 1);
	mono_gchandle_new(asset, 1);
	g_rt_pic[0]   = tex;
	g_rt_asset[0] = asset;
	for (int i = 1; i < kRtPics; ++i) { // the other pictures (if one cannot be made: fewer, as before)
		Obj   t = mono_object_new(g_domain, tk);
		Obj   a = t != nullptr ? mono_object_new(g_domain, ak) : nullptr;
		void* ta[1] = {t};
		if (a == nullptr || !invoke(tctr, t, targs, "Texture2D(more)") || !invoke(actr, a, ta, "ImageAsset(more)")) {
			break;
		}
		mono_gchandle_new(t, 1);
		mono_gchandle_new(a, 1);
		g_rt_pic[i]   = t;
		g_rt_asset[i] = a;
		g_rt_npic     = i + 1;
	}
	wp_log("retro: %d pictures", g_rt_npic);
	mono_gchandle_new(box, 1);
	property_set(bk, box, "Image", asset);
	// the wallpaper's own layers (the dim layer sits above the video; else the scene root / boot root)
	Obj wk = g_ui3_widget != nullptr ? g_ui3_widget : mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget");
	Obj vparent = g_own_view != nullptr ? property_get(wk, g_own_view, "Parent") : nullptr; // right above the video
	Obj parent  = vparent != nullptr ? vparent : g_dim_root != nullptr ? g_dim_root : g_scene_root != nullptr ? g_scene_root : g_boot_root;
	float x = 1550.0f, y = 740.0f, bw = 320.0f, bh = 288.0f; // the mini screen: bottom right, 2x (the game paused)
	property_set(wk, box, "X", &x);
	property_set(wk, box, "Y", &y);
	property_set(wk, box, "Width", &bw);
	property_set(wk, box, "Height", &bh);
	void* cargs[1] = {box};
	(void)cargs;
	// the menu and the pop-up go on the home screen's own scene (not the wallpaper's layer): PlayShell works with
	// the wallpaper off too
	const bool ok = parent != nullptr || home_scene_root(pui) != nullptr;
	wp_log("retro: parent %s (dim %p scene %p boot %p)", parent == nullptr ? "none (wallpaper off: the home screen's scene)" : parent == vparent ? "the video's layer" : parent == g_dim_root ? "dim layer" : parent == g_scene_root ? "scene root" : "boot root",
	       g_dim_root, g_scene_root, g_boot_root);
	g_rt_tex = ok ? tex : nullptr; // not ready: retro_tick tries again in 5 s
	g_rt_box = box;
	wp_log("retro: PlayShell %s", ok ? "ready" : "NOT ready (no home screen scene yet: tried again later)");
	pthread_t rt, st;
	if (ok && pthread_create(&rt, nullptr, retro_rx_thread, nullptr) == 0) {
		pthread_detach(rt);
	}
	if (ok && pthread_create(&st, nullptr, retro_sound_thread, nullptr) == 0) {
		pthread_detach(st);
	}
	if (ok) {
		retro_popup_setup(pui, asset, wk);
		retro_menu_setup(pui, wk);
		detour_method("Sce.PlayStation.Core", "GamePad", "GetData", 1, reinterpret_cast<void*>(&GetData_Hook),
		              reinterpret_cast<void**>(&g_getdata_orig));
	}
	return ok;
}

// Every frame: a moving pattern (scrolling colour bars + a bouncing white square) into the texture.
void retro_tick() {
	if (g_rt_fail > 3) {
		return;
	}
	if (g_rt_tex == nullptr) {
		if (g_rt_start == 0) {
			g_rt_start = g_tick + 240; // ~4 s after the module started (the wallpaper's video is up)
		}
		if (g_tick >= g_rt_start && !retro_setup()) {
			++g_rt_fail;
			g_rt_start = g_tick + 300;
		}
		return;
	}
	g_game_mode = g_mode.load() == 2;
	retro_menu_tick();
	retro_popup_tick(g_game_mode);
	static uint32_t shown = 0;
	const uint32_t  ready = g_rf_ready.load();
	if (ready == 0 || ready == shown) {
		return; // no new frame from the payload yet
	}
	shown = ready;
	// one whole frame: copied again if the receiver wrote a new one meanwhile (a torn frame flickered at the top)
	static uint16_t frame[kRw * kRh];
	for (int tries = 0; tries < 4; ++tries) {
		const uint32_t a = g_rf_seq.load();
		if (a & 1) {
			continue;
		}
		memcpy(frame, g_rf, sizeof(frame));
		if (g_rf_seq.load() == a) {
			break;
		}
	}
	static int on = 0, pending = -1;
	if (pending >= 0 && g_pop_img != nullptr) { // the frame written last refresh goes on screen now
		prop_set_up(g_pop_img, "Image", g_rt_asset[pending]);
		on      = pending;
		pending = -1;
	}
	const int w   = (on + 1) % g_rt_npic; // the picture not on screen
	Obj       arr = g_rt_arr;
	uint8_t*  px  = reinterpret_cast<uint8_t*>(static_cast<char*>(arr) + 32); // MonoArray data (64-bit)
	for (int i = 0; i < kRw * kRh; ++i) { // RGB565 -> RGBA
		const uint16_t v = frame[i];
		const int      r = v >> 11, g = (v >> 5) & 63, b = v & 31;
		px[i * 4]     = static_cast<uint8_t>((r << 3) | (r >> 2));
		px[i * 4 + 1] = static_cast<uint8_t>((g << 2) | (g >> 4));
		px[i * 4 + 2] = static_cast<uint8_t>((b << 3) | (b >> 2));
		px[i * 4 + 3] = 255;
	}
	const long t = now_ms();
	struct timespec a {}, b {};
	clock_gettime(CLOCK_MONOTONIC, &a);
	int        level   = 0;
	void*      args[2] = {&level, arr};
	Obj        exc     = nullptr;
	// two pictures: the frame goes into the one not on screen; it is shown at the NEXT refresh (its upload to the
	// graphics chip is done by then - shown at once, the top rows were sometimes new and the rest old: a flicker
	// at the top while things moved)
	mono_runtime_invoke(g_rt_set, g_rt_pic[w], args, &exc);
	if (exc == nullptr && g_rt_npic > 1) {
		pending = w;
	}
	clock_gettime(CLOCK_MONOTONIC, &b);
	if (exc != nullptr) {
		log_exception("Texture2D.SetPixels", exc);
		g_rt_fail = 99;
		return;
	}
	g_rt_us += (b.tv_sec - a.tv_sec) * 1000000L + (b.tv_nsec - a.tv_nsec) / 1000;
	++g_rt_n;
	if (g_rt_t0 == 0) {
		g_rt_t0 = t;
	} else if (t - g_rt_t0 >= 2000) {
		static int logs = 0;
		if (logs++ < 30) {
			wp_log("retro: %ld frames in %ld ms (%.1f fps), SetPixels %ld us avg", g_rt_n, t - g_rt_t0, g_rt_n * 1000.0 / (t - g_rt_t0),
			       g_rt_us / g_rt_n);
		}
		g_rt_t0 = t, g_rt_n = 0, g_rt_us = 0;
	}
}
#endif

void v11_setup() {
	detour_method("Sce.Vsh.ShellUI.BGLayer", "BGLayerPlugin", "SetBackgroundTransition", 1,
	              reinterpret_cast<void*>(&SetBg_Hook), reinterpret_cast<void**>(&g_setbg_orig));
	// ~10 s later, when the home screen is up: the tested v1.1 builds hooked it then; hooking it at
	// setup is the main change in the build that froze ShellUI on load (v1.1-rc3).
	g_sysbgm_at = g_tick + 600;
}

void sysbgm_tick() {
	if (g_sysbgm_at < 0 || g_tick < g_sysbgm_at) {
		return;
	}
	g_sysbgm_at = -1;
	detour_method("Sce.Vsh.ShellUI.ReactNativeShellApp", "SceneControlModule", "SetSystemBgm", 2,
	              reinterpret_cast<void*>(&setsysbgm_hook), reinterpret_cast<void**>(&g_sysbgm_orig));
}

// ---- crash-loop guard ------------------------------------------------------------------------

bool guard_exists() {
	struct stat st {};
	return stat(kGuardFile, &st) == 0;
}

bool guard_create() {
	mkdir("/system_tmp/liveshell", 0777);
	const int fd = open(kGuardFile, O_WRONLY | O_CREAT | O_TRUNC, 0666);
	if (fd < 0) {
		return false;
	}
	close(fd);
	return true;
}

void* guard_thread(void*) {
	sleep(20);
	unlink(kGuardFile);
	wp_log("video: alive after 20 s, guard removed");
	return nullptr;
}

// ---- choose the video clip -------------------------------------------------------------------

bool choose_video() {
	g_video_path[0] = 0;
	FILE*       f      = fopen(kPathFile, "r");
	const int   ferr   = errno;
	char        got[48] = "";
	if (f != nullptr) {
		char line[512] = {};
		if (fgets(line, sizeof(line), f) != nullptr) {
			line[strcspn(line, "\r\n")] = 0;
			snprintf(got, sizeof(got), "%s", line);
			if (line[0] == '/') {
				snprintf(g_video_path, sizeof(g_video_path), "%s", line);
			}
		}
		char mode[64] = {};
		if (fgets(mode, sizeof(mode), f) != nullptr) {
			mode[strcspn(mode, "\r\n")] = 0;
			g_mode_sony = strcmp(mode, "mode=sony") == 0;
		}
		fclose(f);
	}
	if (g_video_path[0] == 0) {
		if (f == nullptr) {
			wp_log("video: no path in %s (cannot open it: errno %d)", kPathFile, ferr);
		} else {
			wp_log("video: no path in %s (it says '%s')", kPathFile, got);
		}
		return false;
	}
	struct stat st {};
	const bool visible = stat(g_video_path, &st) == 0;
	wp_log("video: clip %s (%s), route %s", g_video_path, visible ? "found" : "NOT FOUND",
	       g_mode_sony ? "Sony InitialBootPlayer" : "own player");
	return visible;
}

// ---- PUI.Application.Update detour (our UI-thread tick) --------------------------------------

std::atomic<bool> g_pending{false};
std::atomic<bool> g_video_wanted{false};

// Requests from the window: the watcher thread copies the path file's first line here.
pthread_mutex_t   g_req_lock = PTHREAD_MUTEX_INITIALIZER;
char              g_req_line[512] = {};
std::atomic<bool> g_req_new{false};
bool              g_have_req   = false;
char              g_req_take[512] = {};
bool              g_stopping   = false;
int               g_stop_tick  = 0;
bool              g_welcomed   = false;

bool video_active() {
	return g_own_view != nullptr || g_boot_player != nullptr;
}

// Stop the current clip. Called on the UI thread only. The player itself is not disposed here:
// the view owns it, and a second Dispose on it is not known to be safe.
// ---- kept players (v1.7.0) --------------------------------------------------------------------
// A tile swap used to destroy the clip's player and build a new one every time. Now the player you leave is
// KEPT: paused, hidden (opacity 0), muted - and coming back to that clip just plays it again (~70 ms, 4K
// ~0.15 s; the decoder probe showed 6 FullHD + 3 UHD extra players alive with no limit). Up to kParkMax are
// kept, the oldest go first; the newest 4K one is kept over older 1080p ones: while one 4K player lives, the
// decoder stays in 4K mode and a NEW 4K clip starts in ~0.2 s instead of ~1.1 s. The black fade of a swap is
// untouched: only "destroy + build" became "keep + reuse". Every other stop (a game, off, the window, a
// restart) frees them all: a game needs the memory, and the PS5 refuses 4K next to a running game anyway.
// The 4K warm-up: with a 4K clip for some game and no 4K player alive, one is made hidden and paused in a
// calm moment, so even the FIRST 4K tile starts fast.
struct Parked {
	Obj  view = nullptr, player = nullptr;
	char path[512] {};
	bool uhd  = false;
	int  used = 0;
};
constexpr int kParkMax = 6; // user 2026-11-10 (was 5)
Parked        g_parked[kParkMax];
int           g_last_swap  = 0;     // tick of the last swap (the warm-up waits for a calm moment)
Parked        g_warm;               // a 4K player being made hidden (moves -> paused -> kept)
long          g_warm_t0    = 0;
int           g_warm_fails = 0;
char          g_warm_bad[512] {};   // a 4K clip that would not play hidden: not tried again

Obj widget_cls() {
	static Obj w = nullptr;
	if (w == nullptr) {
		Obj pui = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
		w       = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget") : nullptr;
	}
	return w;
}

// "free 412 MB, heap 96 MB": ShellUI's free memory and the home screen's object heap - over a long session
// these must stay flat (kept players are not a leak). "?" = the PS5 did not give that number.
const char* mem_note() {
	static char note[80];
	size_t      flex = 0;
	const bool  f    = sceKernelAvailableFlexibleMemorySize != nullptr && sceKernelAvailableFlexibleMemorySize(&flex) == 0;
	const long long heap = mono_gc_get_heap_size != nullptr ? static_cast<long long>(mono_gc_get_heap_size()) : -1;
	const long long used = mono_gc_get_used_size != nullptr ? static_cast<long long>(mono_gc_get_used_size()) : -1;
	char a[24], b[24], c[24];
	snprintf(a, sizeof(a), f ? "%zu MB" : "?", flex >> 20);
	snprintf(b, sizeof(b), heap >= 0 ? "%lld MB" : "?", heap >> 20);
	snprintf(c, sizeof(c), used >= 0 ? "%lld MB" : "?", used >> 20);
	snprintf(note, sizeof(note), "free %s, heap used %s of %s", a, c, b);
	return note;
}

int kept_count() {
	int n = 0;
	for (const Parked& p : g_parked) {
		n += p.view != nullptr ? 1 : 0;
	}
	return n;
}

long park_ms() {
	timespec t {};
	clock_gettime(CLOCK_MONOTONIC, &t);
	return static_cast<long>(t.tv_sec) * 1000 + t.tv_nsec / 1000000;
}

void player_call(Obj player, Obj view, const char* name) { // Pause / Play: the player's own, else the view's
	Obj m = player != nullptr ? find_method_up(mono_object_get_class(player), name, 0) : nullptr;
	if (m == nullptr || !invoke(m, player, nullptr, name)) {
		invoke(find_method_up(g_videoview_class, name, 0), view, nullptr, name);
	}
}

void hide_player(Obj view, Obj player) {
	float zero = 0.0f;
	bool  yes  = true;
	set_blend(view, false); // an "overwrite" view must not draw at opacity 0
	property_set(widget_cls(), view, "Opacity", &zero);
	player_call(player, view, "Pause");
	if (player != nullptr) {
		void* m[1] = {&yes};
		invoke(mono_class_get_method_from_name(mono_object_get_class(player), "SetIsMuted", 1), player, m, "SetIsMuted (kept)");
		set_bgm_suppression(mono_object_get_class(player), player, false); // a kept clip never holds the PS5's music
	}
}

void free_parked(const char* why) {
	int n = 0;
	for (Parked& p : g_parked) {
		if (p.view != nullptr) {
			dispose_view(p.view);
			++n;
		}
		p = Parked();
	}
	if (g_warm.view != nullptr) {
		dispose_view(g_warm.view);
		g_warm = Parked();
		++n;
	}
	if (n > 0) {
		wp_log("kept players: %d freed (%s)", n, why);
	}
}

bool any_uhd_alive() {
	if (g_own_view != nullptr && g_play_uhd) {
		return true;
	}
	for (const Parked& p : g_parked) {
		if (p.view != nullptr && p.uhd) {
			return true;
		}
	}
	return g_warm.view != nullptr;
}

// Room for one more: the oldest goes, but the newest 4K one stays (it keeps the decoder in 4K mode).
Parked* park_slot() {
	Parked* best      = nullptr;
	int     uhd_count = 0, newest_uhd = -1;
	for (Parked& p : g_parked) {
		if (p.view == nullptr) {
			return &p;
		}
		if (p.uhd) {
			++uhd_count;
			newest_uhd = std::max(newest_uhd, p.used);
		}
	}
	for (Parked& p : g_parked) {
		if (p.uhd && p.used == newest_uhd) {
			continue;
		}
		if (best == nullptr || p.used < best->used) {
			best = &p;
		}
	}
	if (best == nullptr) {
		best = &g_parked[0];
	}
	dispose_view(best->view);
	*best = Parked();
	return best;
}

void keep_player(Obj view, Obj player, const char* path, bool uhd) {
	for (Parked& p : g_parked) { // the same clip kept twice: the older one goes
		if (p.view != nullptr && strcmp(p.path, path) == 0) {
			dispose_view(p.view);
			p = Parked();
		}
	}
	Parked* s = park_slot();
	s->view   = view;
	s->player = player;
	s->uhd    = uhd;
	s->used   = g_tick;
	snprintf(s->path, sizeof(s->path), "%s", path);
}

// The swap's "stop": the clip you leave is kept instead of destroyed. false = nothing to keep (stop_video then).
bool park_current() {
	g_last_swap = g_tick;
	if (g_own_view == nullptr || g_boot_player != nullptr || g_old_view != nullptr || g_stopping || game_alive()) {
		return false;
	}
	Obj view = g_own_view, player = g_own_player;
	g_own_view = g_own_player = nullptr; // own_player_report stops touching it
	const char* cur = g_play_path[0] != 0 ? g_play_path : g_video_path;
	Obj         d   = g_videoview_class != nullptr ? property_get(g_videoview_class, view, "Duration") : nullptr;
	const bool  opened = d != nullptr && *static_cast<unsigned long long*>(mono_object_unbox(d)) > 0;
	if (strcmp(cur, g_switch_path) == 0 || !opened) {
		// a restart of the SAME clip (the watchdog) or a player that never opened: keeping it would hand the
		// broken player straight back - it goes, the clip starts fresh
		dispose_view(view);
		g_own_frames = g_own_logs = g_own_restarts = 0;
		g_own_loop_set = false;
		wp_log("not kept: %s (%s)", cur, opened ? "the same clip starts fresh" : "it never opened");
		return true;
	}
	hide_player(view, player);
	keep_player(view, player, g_play_path[0] != 0 ? g_play_path : g_video_path, g_play_uhd);
	g_own_frames = g_own_logs = g_own_restarts = 0;
	g_own_loop_set = false;
	wp_log("kept: %s%s", g_play_path[0] != 0 ? g_play_path : g_video_path, g_play_uhd ? " (4K)" : "");
	return true;
}

// start_own_player: a kept player of this clip plays again instead of a new one. true = it is the wallpaper now.
bool unpark(const char* path, Obj player_class, Obj view_class) {
	Parked* found = nullptr;
	for (Parked& p : g_parked) {
		if (p.view != nullptr && strcmp(p.path, path) == 0) {
			found = &p;
		}
	}
	if (found == nullptr) {
		return false;
	}
	const long t0 = park_ms();
	Obj view = found->view, player = found->player;
	*found = Parked();
	float zero = 0.0f;
	property_set(widget_cls(), view, "Opacity", &zero); // focus_tick fades it in, as a new one
	g_clip_silent = clip_is_silent(path);
	set_bgm_suppression(player_class, player, g_vol_req.load() == 0 || g_clip_silent);
	g_aud_now = 0.0f;
	assert_sound(player_class, player);
	player_call(player, view, "Play"); // from the start, as every clip starts
	assert_sound(player_class, player); // Play reset it
	g_own_player    = player;
	g_own_view      = view;
	g_own_play0     = method_by_desc(view_class, ":Play(ulong)");
	g_vplayer_class = player_class;
	wp_log("own player: kept one plays again: %s (%ld ms)", path, park_ms() - t0);
	return true;
}

// The 4K warm-up. Hidden + muted, built like start_own_player's 4K one; once it moves it is paused and kept.
bool warm_make(const char* path, const char* name) {
	Obj pui   = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	Obj video = open_image("/system_ex/common_ex/lib/Sce.Vsh.VideoPlayer.dll");
	Obj view_class   = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "VideoView") : nullptr;
	Obj option_class = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "VideoView/PlayOptionParam") : nullptr;
	Obj player_class = video != nullptr ? mono_class_from_name(video, "Sce.Vsh.Video", "VideoPlayer") : nullptr;
	Obj create_class = video != nullptr ? mono_class_from_name(video, "Sce.Vsh.Video", "VideoPlayer/CreateOptionParam") : nullptr;
	Obj widget_class = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Widget") : nullptr;
	Obj scene_class  = pui != nullptr ? mono_class_from_name(pui, "Sce.PlayStation.PUI.UI3", "Scene") : nullptr;
	if (view_class == nullptr || option_class == nullptr || player_class == nullptr || create_class == nullptr || widget_class == nullptr ||
	    scene_class == nullptr) {
		return false;
	}
	Obj create_opt = construct_pinned(create_class, mono_class_get_method_from_name(create_class, ".ctor", 0), nullptr, "warm CreateOptionParam()");
	if (create_opt == nullptr) {
		return false;
	}
	char address[400];
	int  at = snprintf(address, sizeof(address), "http://127.0.0.1:9050/uhd/");
	for (const char* c = name; *c != 0 && at < static_cast<int>(sizeof(address)) - 4; ++c) {
		const unsigned char u = static_cast<unsigned char>(*c);
		at += isalnum(u) || u == '-' || u == '_' || u == '.' ? snprintf(address + at, 2, "%c", u) : snprintf(address + at, 4, "%%%02X", u);
	}
	int mode = 1, fb = 1, res = 4; // Playback, 1920x1080 output, UHD decoder
	set_option_field(create_class, create_opt, "uri", mono_string_new(g_domain, address));
	set_option_field(create_class, create_opt, "createMode", &mode);
	set_option_field(create_class, create_opt, "frameBufferSize", &fb);
	set_option_field(create_class, create_opt, "coreResourceType", &res);
	void* pa[1]     = {create_opt};
	Obj   player    = construct_pinned(player_class, method_by_desc(player_class, ":.ctor(Sce.Vsh.Video.VideoPlayer/CreateOptionParam)"), pa, "warm VideoPlayer");
	Obj   option    = player != nullptr ? construct_pinned(option_class, mono_class_get_method_from_name(option_class, ".ctor", 0), nullptr, "warm PlayOptionParam") : nullptr;
	void* va[1]     = {option};
	Obj   view      = option != nullptr ? construct_pinned(view_class, method_by_desc(view_class, ":.ctor(Sce.PlayStation.PUI.UI3.VideoView/PlayOptionParam)"), va, "warm VideoView") : nullptr;
	if (view == nullptr) {
		return false;
	}
	float zero = 0.0f, width = 1920.0f, height = 1080.0f;
	property_set(widget_class, view, "X", &zero);
	property_set(widget_class, view, "Y", &zero);
	property_set(widget_class, view, "Width", &width);
	property_set(widget_class, view, "Height", &height);
	property_set(widget_class, view, "Opacity", &zero);
	set_blend(view, false);
	bool  yes   = true;
	void* sp[2] = {player, &yes};
	Obj   root  = property_get(scene_class, g_plugin, "RootWidget");
	void* ca[1] = {view};
	if (!invoke(mono_class_get_method_from_name(view_class, "SetPlayer", 2), view, sp, "warm SetPlayer") || root == nullptr ||
	    !invoke(mono_class_get_method_from_name(widget_class, "AppendChild", 1), root, ca, "warm AppendChild")) {
		dispose_view(view);
		return false;
	}
	set_bgm_suppression(player_class, player, false);
	void* m[1] = {&yes};
	invoke(mono_class_get_method_from_name(player_class, "SetIsMuted", 1), player, m, "warm SetIsMuted");
	invoke(mono_class_get_method_from_name(player_class, "Init", 1), player, m, "warm Init");
	invoke(mono_class_get_method_from_name(view_class, "Play", 0), view, nullptr, "warm Play");
	invoke(mono_class_get_method_from_name(player_class, "SetIsMuted", 1), player, m, "warm SetIsMuted");
	invoke(mono_class_get_method_from_name(player_class, "SetLoop", 1), player, m, "warm SetLoop");
	g_warm.view   = view;
	g_warm.player = player;
	g_warm.uhd    = true;
	snprintf(g_warm.path, sizeof(g_warm.path), "%s", path);
	return true;
}

// Once a second: free everything while a game is in front; warm a 4K player in a calm moment.
void park_tick() {
	if (g_tick % 60 != 30) {
		return;
	}
	if (game_alive()) {
		free_parked("a game is open");
		return;
	}
	for (Parked& p : g_parked) { // unused for 10 min: let it go (the 4K warm-up makes a new one when needed)
		if (p.view != nullptr && g_tick - p.used > 10 * 60 * 60) {
			wp_log("kept: %s unused for 10 min, freed", p.path);
			dispose_view(p.view);
			p = Parked();
		}
	}
	if (g_warm.view != nullptr) { // being made: does it move?
		Obj            p   = g_videoview_class != nullptr ? property_get(g_videoview_class, g_warm.view, "Position") : nullptr;
		const uint64_t pos = p != nullptr ? *static_cast<uint64_t*>(mono_object_unbox(p)) : 0;
		if (pos > 0) {
			hide_player(g_warm.view, g_warm.player);
			wp_log("4k warm-up: %s ready after %ld ms (kept, paused)", g_warm.path, park_ms() - g_warm_t0);
			keep_player(g_warm.view, g_warm.player, g_warm.path, true);
			g_warm = Parked();
		} else if (park_ms() - g_warm_t0 > 10000) {
			wp_log("4k warm-up: %s did not play hidden - not tried again", g_warm.path);
			snprintf(g_warm_bad, sizeof(g_warm_bad), "%s", g_warm.path);
			dispose_view(g_warm.view);
			g_warm = Parked();
			++g_warm_fails;
		}
		return;
	}
	// calm: playing, no swap for 3 s, not black, not stopping, nothing 4K alive, few failures
	if (g_warm_fails >= 3 || g_stopping || g_switch_at >= 0 || g_hold_black || g_tick - g_last_swap < 180 || // also when nothing plays (Videos per game only)
	    any_uhd_alive() || g_videoview_class == nullptr) {
		return;
	}
	// a 4K clip some game uses (fast.txt: "TITLE=<clip>" lines, "^<clip>\t<name>\t" = 4K)
	FILE* f = fopen("/system_tmp/liveshell/fast.txt", "r");
	if (f == nullptr) {
		return;
	}
	char line[700], name[256] = {}, pick[512] = {};
	static char games[160][512]; // every game with a clip (was 8: the 4K ones came later and were never seen)
	int  ng = 0;
	static char uhd[64][2][256];
	int  nu = 0;
	while (fgets(line, sizeof(line), f) != nullptr) {
		line[strcspn(line, "\r\n")] = 0;
		char* eq = strchr(line, '=');
		if (line[0] == '^' && nu < 64) {
			char* t1 = strchr(line, '\t');
			if (t1 != nullptr) {
				*t1      = 0;
				char* t2 = strchr(t1 + 1, '\t');
				if (t2 != nullptr) {
					*t2 = 0;
				}
				snprintf(uhd[nu][0], sizeof(uhd[nu][0]), "%s", line + 1);
				snprintf(uhd[nu][1], sizeof(uhd[nu][1]), "%s", t1 + 1);
				++nu;
			}
		} else if (eq != nullptr && line[0] != '*' && ng < 160) {
			snprintf(games[ng++], sizeof(games[0]), "%s", eq + 1);
		}
	}
	fclose(f);
	for (int g = 0; g < ng && pick[0] == 0; ++g) {
		for (int u = 0; u < nu; ++u) {
			if (strcmp(games[g], uhd[u][0]) == 0 && strcmp(games[g], g_warm_bad) != 0) {
				snprintf(pick, sizeof(pick), "%s", uhd[u][0]);
				snprintf(name, sizeof(name), "%s", uhd[u][1]);
				break;
			}
		}
	}
	if (pick[0] == 0) {
		return; // no game has a 4K clip: nothing to warm
	}
	g_warm_t0 = park_ms();
	if (warm_make(pick, name)) {
		wp_log("4k warm-up: making %s hidden", pick);
	} else {
		wp_log("4k warm-up: %s could not be made", pick);
		++g_warm_fails;
	}
}

void stop_video() {
	free_parked("stop");
	if (g_old_view != nullptr) { // a cross-fade was running: the old clip goes too
		dispose_view(g_old_view);
		g_old_view = g_old_player = nullptr;
		g_xfade_tick = -1;
	}
	if (g_own_view != nullptr) {
		Obj view   = g_own_view;
		g_own_view = nullptr; // own_player_report stops touching it from now on
		g_own_player = nullptr;
		// Resume after a game: where this clip was (not near its end - the loop starts over anyway)
		g_resume_pos = 0;
		if (resume_on() && g_videoview_class != nullptr) {
			Obj p = property_get(g_videoview_class, view, "Position");
			Obj d = property_get(g_videoview_class, view, "Duration");
			const uint64_t pos = p != nullptr ? *static_cast<uint64_t*>(mono_object_unbox(p)) : 0;
			const uint64_t dur = d != nullptr ? *static_cast<uint64_t*>(mono_object_unbox(d)) : 0;
			if (pos > 1000 && (dur == 0 || pos + 1500 < dur)) {
				g_resume_pos = pos;
				snprintf(g_resume_clip, sizeof(g_resume_clip), "%s", g_video_path);
				wp_log("resume: %s stopped at %llu of %llu ms", g_video_path, static_cast<unsigned long long>(pos),
				       static_cast<unsigned long long>(dur));
			}
		}
		Obj stop    = find_method_up(g_videoview_class, "Stop", 0);
		Obj dispose = find_method_up(g_videoview_class, "Dispose", 0);
		wp_log("stop: own view, Stop %p Dispose %p", stop, dispose);
		if (stop != nullptr) {
			invoke(stop, view, nullptr, "VideoView.Stop");
		}
		invoke(dispose, view, nullptr, "VideoView.Dispose");
	}
	if (g_boot_player != nullptr) {
		Obj player    = g_boot_player;
		g_boot_player = nullptr;
		Obj dispose   = find_method_up(g_boot_class, "Dispose", 0);
		wp_log("stop: boot player, Dispose %p", dispose);
		invoke(dispose, player, nullptr, "InitialBootPlayer.Dispose");
	}
	g_own_frames = g_own_logs = g_own_restarts = 0;
	g_own_loop_set = false;
}

int start_video() {
	// 4K clip: the UHD stream; with a game open nothing (hidden, the game's art shows) until it closes.
	char name[256] = {}, copy[512] = {};
	g_play_uhd = g_on_fallback = g_start_nothing = false;
	snprintf(g_play_path, sizeof(g_play_path), "%s", g_video_path);
	if (!g_mode_sony && uhd_lookup(g_video_path, name, sizeof(name), copy, sizeof(copy))) {
		if (!game_alive()) {
			g_play_uhd = true;
			snprintf(g_uhd_name, sizeof(g_uhd_name), "%s", name);
		} else {
			g_on_fallback = g_start_nothing = true;
			wp_log("4k: hidden while a game is open (%s)", g_video_path);
			write_status("stopped");
			return 0;
		}
	}
	write_status("starting");
	const int rc = g_mode_sony ? start_video_sony() : start_own_player();
	wp_log("video: start result %d (%s)", rc, g_video_path);
	if (rc == 0) {
		write_status("playing %s", g_video_path);
		raise_dim();
		if (!g_welcomed) {
			g_welcomed = true;
			notify("Welcome to LiveShell Engine 📺");
		}
	} else {
		write_status("failed %d", rc);
		char text[80];
		snprintf(text, sizeof(text), "LiveShell Engine: the video could not start (%d)", rc);
		notify(text);
	}
	return rc;
}

// Quick swap to a clip in the mounted folder: fade to black, swap, lift the black once it draws.
void begin_swap(const char* path) {
	snprintf(g_switch_path, sizeof(g_switch_path), "%s", path);
	if (g_switch_at >= 0) {
		return; // already fading to black: it takes the new path
	}
	g_switch_at = g_hold_black ? g_tick - 7 : g_tick; // already black: swap at once
	wp_log("quick swap to %s", g_switch_path);
}

// The payload's map (fast.txt): "*=<main clip>", then "TITLEID=<clip>"; "-" = it must remount
// first and switches itself.
bool fast_lookup(const char* tid, char* out, size_t n) {
	FILE* f = fopen("/system_tmp/liveshell/fast.txt", "r");
	if (f == nullptr) {
		return false;
	}
	char         line[600];
	char         main_clip[512] = {};
	bool         found          = false;
	const size_t tl             = strlen(tid);
	out[0]                      = 0;
	while (fgets(line, sizeof(line), f) != nullptr) {
		line[strcspn(line, "\r\n")] = 0;
		if (line[0] == '*' && line[1] == '=') {
			snprintf(main_clip, sizeof(main_clip), "%s", line + 2);
		} else if (tl > 0 && strncmp(line, tid, tl) == 0 && line[tl] == '=') {
			snprintf(out, n, "%s", line + tl + 1);
			found = true;
		}
	}
	fclose(f);
	if (!found) {
		snprintf(out, n, "%s", main_clip);
	}
	return out[0] == '/' || strcmp(out, "off") == 0 || strcmp(out, "hide") == 0; // off = wallpaper off, hide = per game only
}

// Restart a frozen clip (watchdog above) with the normal swap, on the home screen only (a game in
// front may pause it on purpose).
void stall_tick() {
	if (!g_stalled) {
		return;
	}
	if (!video_active() || g_stopping || g_switch_at >= 0 || g_hidden || g_is_settings) {
		g_stalled = false; // a game / Settings / system app in front may pause it on purpose
		return;
	}
	g_stalled = false;
	begin_swap(g_video_path);
}

// ~0.25 s on the same tile: switch to its clip right here, no round trip through the payload.
void fast_tick() {
	if (g_fast_at < 0 || g_tick - g_fast_at < 12) { // ~0.2 s on the tile
		return;
	}
	g_fast_at = -1;
	char path[512];
	if (g_stopping || !fast_lookup(g_fast_tid, path, sizeof(path))) {
		return;
	}
	if (strcmp(path, "hide") == 0) { // Videos per game only, no clip of its own: hidden (focus tick), nothing stops
		return;
	}
	if (strcmp(path, "off") == 0) { // "Main video" off and no clip of its own: fade to Sony's background
		if (video_active() && !(g_switch_at >= 0 && g_switch_path[0] == 0)) {
			wp_log("fast: %s has no video, stopping", g_fast_tid[0] != 0 ? g_fast_tid : "(no game)");
			g_switch_path[0] = 0;
			if (g_switch_at < 0) {
				g_switch_at = g_hold_black ? g_tick - 7 : g_tick;
			}
		}
		return;
	}
	if (!video_active()) { // nothing playing (a tile without video before): start it right here
		struct stat st0 {};
		if (g_switch_at < 0 && stat(path, &st0) == 0 && !game_open_hold() && uhd_blocked(path)) {
			// 4K + a game open: hidden; nothing to start on any tile move; the game's end brings it back.
			if (strcmp(path, g_video_path) != 0 || !g_on_fallback) {
				snprintf(g_video_path, sizeof(g_video_path), "%s", path);
				g_on_fallback = true;
				wp_log("4k: %s hidden while a game is open", path);
			}
			g_start_nothing = true; // nothing comes: no black hold
		} else if (g_switch_at < 0 && stat(path, &st0) == 0 && !game_open_hold()) {
			wp_log("fast: %s, starting %s", g_fast_tid[0] != 0 ? g_fast_tid : "(no game)", path);
			snprintf(g_video_path, sizeof(g_video_path), "%s", path);
			start_video();
		}
		return;
	}
	if (strcmp(path, g_switch_at >= 0 ? g_switch_path : g_video_path) == 0) {
		return;
	}
	struct stat st {};
	if (stat(path, &st) == 0) {
		wp_log("fast: %s", g_fast_tid[0] != 0 ? g_fast_tid : "(no game)");
		begin_swap(path);
	}
}

// The moment a tile is highlighted Sony starts its music (SceneControlModule.SetSystemBgm, same
// frame, test v11-16), ~0.4 s before our swap. So the CURRENT player already holds the PS5 music
// back or lets it play, as the next tile's clip will: no burst of game music, no gap.
void focus_sound_tick() {
	if (!g_focus_new) {
		return;
	}
	g_focus_new = false;
	char path[512];
	if (g_own_player == nullptr || g_vplayer_class == nullptr || !fast_lookup(g_fast_tid, path, sizeof(path))) {
		return;
	}
	const bool ours = path[0] == '/' && g_vol_req.load() > 0 && !clip_is_silent(path) && // its sound replaces it
	                  !(g_store_only.load() && strcmp(g_fast_tid, "NPXS40047") != 0);
	set_bgm_suppression(g_vplayer_class, g_own_player, !ours);
	wp_log("sound: %s highlighted (tick %d) -> PS5 music %s", g_fast_tid[0] != 0 ? g_fast_tid : "(no game)", g_tick,
	       ours ? "held back" : "allowed");
}

// Sound fades: out with the fade to black of a swap (~0.17 s), in over ~0.5 s for a new clip or
// a new setting. Mute = SetIsMuted at once.
void sound_tick() {
	if (g_own_player == nullptr || g_vplayer_class == nullptr) {
		return;
	}
	const int  want  = g_vol_req.load();
	const bool muted = want == 0;
	if (muted != g_aud_muted) {
		g_aud_muted = muted;
		player_mute(g_vplayer_class, g_own_player, muted);
		set_bgm_suppression(g_vplayer_class, g_own_player, muted || g_clip_silent);
		wp_log("sound: %s", muted ? "muted, PS5 music allowed" : "on");
	}
	static bool tile_hidden = false;
	if (g_tile_hide != tile_hidden) {
		tile_hidden = g_tile_hide;
		set_bgm_suppression(g_vplayer_class, g_own_player, tile_hidden || muted || g_clip_silent);
	}
	const float goal = g_switch_at >= 0 || g_tile_hide ? 0.0f : static_cast<float>(want);
	if (g_aud_now < goal) {
		g_aud_now = g_aud_now + 2.4f > goal ? goal : g_aud_now + 2.4f; // in: 100 % in ~0.7 s
	} else if (g_aud_now > goal) {
		g_aud_now = g_aud_now - 8.5f < goal ? goal : g_aud_now - 8.5f; // out: 100 % in ~0.2 s
	}
	const int v = static_cast<int>(g_aud_now + 0.5f);
	if (v != g_aud_set) {
		g_aud_set = v;
		player_volume(g_vplayer_class, g_own_player, v);
	}
}

// Switching (UI thread): stop the old clip, give the decoder ~2 s to let go of the file (the daemon
// unmounts its folder after "stopped"), then start the new one if the request is a path.
void handle_requests() {
	if (g_req_new.exchange(false, std::memory_order_acq_rel)) {
		pthread_mutex_lock(&g_req_lock);
		memcpy(g_req_take, g_req_line, sizeof(g_req_take));
		pthread_mutex_unlock(&g_req_lock);
		g_have_req     = true;
		g_self_started = false; // the payload has spoken
		wp_log("request: '%s'", g_req_take);
	}
	if (!g_have_req) {
		return;
	}
	if (strncmp(g_req_take, "switch:", 7) == 0) {
		if (g_xfade_tick >= 0) {
			return; // a cross-fade is still running: take this request when it is done
		}
		memmove(g_req_take, g_req_take + 7, strlen(g_req_take + 7) + 1);
		struct stat sw {};
		if (video_active() && !g_stopping && stat(g_req_take, &sw) == 0) {
			g_have_req = false;
			// The fast switch usually got there first: same clip = nothing to do.
			if (strcmp(g_req_take, g_switch_at >= 0 ? g_switch_path : g_video_path) != 0) {
				begin_swap(g_req_take);
			}
			return;
		}
		// nothing playing: normal path below
	}
	if (!g_stopping && video_active() && g_req_take[0] == '/' && g_switch_at < 0 &&
	    strcmp(g_req_take, g_video_path) == 0) {
		g_have_req = false; // already playing it (e.g. started on the return from a game): no restart
		return;
	}
	if (!g_stopping && video_active()) {
		stop_video();
		g_stopping  = true;
		g_stop_tick = g_tick;
		write_status("stopping");
		return;
	}
	if (g_stopping) {
		if (g_tick - g_stop_tick < 120) {
			return;
		}
		g_stopping = false;
		write_status("stopped");
	}
	g_have_req = false;
	if (g_req_take[0] != '/') {
		write_status("stopped");
		return;
	}
	struct stat st {};
	if (stat(g_req_take, &st) != 0) {
		wp_log("request: %s not visible", g_req_take);
		write_status("failed notfound");
		return;
	}
	snprintf(g_video_path, sizeof(g_video_path), "%s", g_req_take);
	start_video();
}

using UpdateFn = void (*)(Obj self);
UpdateFn g_update_orig = nullptr;

void Update_Hook(Obj self) {
	g_update_orig(self);
	++g_tick;
	video_report();
	own_player_report();
	if (g_installed) {
		handle_requests();
		focus_sound_tick();
		fast_tick();
		park_tick();
		sysbgm_tick();
		stall_tick();
		sound_tick();
		refresh_dim();
		refresh_looks();
		if (true) { // every frame: the menu fade needs it (just a static field read)
			focus_tick();
			parallax_tick();
			avatar_tick();
#ifdef LIVESHELL_RESEARCH_RETRO
			retro_tick();
#endif
			launchfx_tick();
		}
	}

	if (!g_pending.exchange(false, std::memory_order_acq_rel)) {
		return;
	}
	if (g_installed) {
		return;
	}
	const int rc = install_bglayer();
	wp_log("setup done (%d)", rc);
	if (rc == 0) {
		v11_setup();
	}
	if (rc != 0) {
		write_status("failed setup %d", rc);
		char text[80];
		snprintf(text, sizeof(text), "LiveShell Engine could not start (%d)", rc);
		notify(text);
		return;
	}
	if (!g_video_wanted.load(std::memory_order_acquire)) {
		write_status("stopped");
		return;
	}
	start_video();
	pthread_t gt;
	if (pthread_create(&gt, nullptr, guard_thread, nullptr) == 0) {
		pthread_detach(gt);
	}
}

// ---- background thread: choose clip, then watch the path file for the window's requests ------

void read_request_line(char* out, size_t size) {
	out[0]  = 0;
	FILE* f = fopen(kPathFile, "r");
	if (f == nullptr) {
		return;
	}
	if (fgets(out, static_cast<int>(size), f) != nullptr) {
		out[strcspn(out, "\r\n")] = 0;
	}
	fclose(f);
}

#ifdef LIVESHELL_RESEARCH_DUMP
// RESEARCH BUILD ONLY (animated avatars, v1.6.0): every loaded assembly's image (MonoImage raw_data, the
// decrypted IL the runtime reads) goes to the payload over UDP 127.0.0.1:9052, which writes
// /data/LiveShell/dump/<name>.dll, for reading on a PC. Not in normal builds.
int g_dump_sock = -1;

void dump_image(void* assembly, void*) {
	Obj         image = mono_assembly_get_image(static_cast<Obj>(assembly));
	const char* name  = image != nullptr && mono_image_get_name != nullptr ? mono_image_get_name(image) : nullptr;
	if (name == nullptr) {
		return;
	}
	const uint8_t* raw = *reinterpret_cast<const uint8_t* const*>(static_cast<const char*>(image) + 16);
	const uint32_t len = *reinterpret_cast<const uint32_t*>(static_cast<const char*>(image) + 24);
	if (raw == nullptr || len < 512 || len > (64u << 20) || raw[0] != 'M' || raw[1] != 'Z') {
		wp_log("dump: %s: no image (raw %p, len %u)", name, raw, len);
		return;
	}
	sockaddr_in a {};
	a.sin_family      = AF_INET;
	a.sin_port        = htons(9052);
	a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	static char pkt[64 + 8 + 8192]; // FreeBSD: a UDP datagram is at most ~9 KB (net.inet.udp.maxdgram)
	for (uint32_t off = 0; off < len; off += 8192) {
		const uint32_t n = len - off < 8192 ? len - off : 8192;
		memset(pkt, 0, 64);
		snprintf(pkt, 64, "%s", name);
		memcpy(pkt + 64, &off, 4);
		memcpy(pkt + 68, &len, 4);
		memcpy(pkt + 72, raw + off, n);
		for (int t = 0; t < 50 && sendto(g_dump_sock, pkt, 72 + n, 0, reinterpret_cast<sockaddr*>(&a), sizeof(a)) < 0; ++t) {
			usleep(20 * 1000);
		}
		usleep(1500);
	}
	wp_log("dump: %s %u bytes sent", name, len);
}

void* dump_thread(void*) {
	mono_thread_attach(g_domain);
	sleep(25); // the home screen loads its assemblies first
	g_dump_sock = socket(AF_INET, SOCK_DGRAM, 0);
	if (g_dump_sock < 0 || mono_assembly_foreach == nullptr) {
		wp_log("dump: not possible (socket %d, foreach %p)", g_dump_sock, reinterpret_cast<void*>(mono_assembly_foreach));
		return nullptr;
	}
	for (int round = 0; round < 2; ++round) { // twice: assemblies loaded later (a second pass sends them too)
		mono_assembly_foreach(dump_image, nullptr);
		wp_log("dump: round %d done", round + 1);
		sleep(60);
	}
	return nullptr;
}
#endif


// ---- animated avatars (v1.6.0) --------------------------------------------------------------
// The home screen loads every avatar as "profilecache:image/face/default?userid=<id>&size=<ss|m|..>" through
// ImageAsset.LoadAsync(uri, action, option), from React Native's image views (set_Source) and PUI image boxes
// (ImageBox.LoadAsync). From the start every image box that loads an avatar is remembered with its address.
// A user with /data/LiveShell/video/.avatars/<id>.png (ShellUI sees that folder as
// /system_ex/vsh_asset/wallpaper/.avatars) gets that picture instead, decoded as an animated PNG
// (ImageOptions.IsAnimatedImage; the image box loops it). When the file appears or changes, a hidden image box
// decodes it (a fraction of a second) and then every remembered avatar of that user switches at once; when it
// goes, they all load Sony's again. Until a new one is decoded, new loads get <id>_still.png (its first
// picture). Users without one: nothing changes (the hooks only note which boxes show avatars).
// Avatars already on screen before that (loaded before LiveShell watched: at its start, or the login screen
// after rest mode) are found by walking every scene's widgets (SceneManager.Instance.SceneLayers ->
// RootWidget -> FirstChildBase / NextSiblingBase): at the start, now and then, and when an avatar changes.
// "?ts=<time>" (as Sony does for game icons): a new file is not taken from the image cache.
constexpr const char* kAvatarDir = "/system_ex/vsh_asset/wallpaper/.avatars";
using AssetLoadFn = Obj (*)(Obj uri, Obj action, Obj option);
using SetSourceFn = void (*)(Obj self, Obj source);
using BoxLoadFn   = void (*)(Obj self, Obj uri, Obj action, Obj option, bool set_image);
AssetLoadFn      g_assetload_orig = nullptr;
SetSourceFn      g_setsrc_orig    = nullptr;
BoxLoadFn        g_boxload2_orig = nullptr, g_boxload3_orig = nullptr;
thread_local Obj g_loading_view   = nullptr; // the image box whose load is running
Obj              g_opt_class      = nullptr;
bool             g_avatar_hooked  = false;

struct AvatarView {
	Obj  view = nullptr;
	char uri[160] {}; // Sony's address for it (loaded again when the animated avatar goes)
};

struct Avatar {
	long       user   = 0;
	long       mtime  = 0;       // of <id>.png shown now (0: Sony's avatar)
	long       want   = 0;       // of <id>.png being decoded
	Obj        box    = nullptr; // hidden ImageBox decoding it
	int        since  = 0;
	AvatarView views[16] {};
	int        nviews = 0;
};
Avatar g_avatars[8];

// A System.String's text as ASCII (no allocation: called for every picture the home screen loads).
size_t mono_ascii(Obj str, char* out, size_t cap) {
	const int32_t   len = *reinterpret_cast<const int32_t*>(static_cast<const char*>(str) + 16);
	const uint16_t* ch  = reinterpret_cast<const uint16_t*>(static_cast<const char*>(str) + 20);
	size_t          n   = 0;
	for (int32_t i = 0; i < len && n + 1 < cap; ++i) {
		out[n++] = ch[i] < 0x80 ? static_cast<char>(ch[i]) : '?';
	}
	out[n] = 0;
	return n;
}

// ImageOptions set to decode an animated PNG: a copy of Sony's (it may be shared by other pictures) or new.
Obj anim_option(Obj option) {
	if (g_opt_class == nullptr) {
		g_opt_class = find_class("Sce.PlayStation.PUI", "ImageOptions");
	}
	if (g_opt_class == nullptr) {
		return nullptr;
	}
	Obj opt = nullptr;
	if (option != nullptr) {
		Obj clone = mono_class_get_method_from_name(mono_object_get_class(option), "Clone", 0);
		if (clone == nullptr || !invoke(clone, option, nullptr, "ImageOptions.Clone", &opt)) {
			opt = nullptr;
		}
	}
	if (opt == nullptr) {
		opt      = mono_object_new(g_domain, g_opt_class);
		Obj ctor = mono_class_get_method_from_name(g_opt_class, ".ctor", 0);
		if (opt == nullptr || ctor == nullptr || !invoke(ctor, opt, nullptr, "ImageOptions()")) {
			return nullptr;
		}
	}
	bool yes  = true;
	int  mode = 2; // ImageAnimationDecodeMode.ProgressiveDecode
	property_set(g_opt_class, opt, "IsAnimatedImage", &yes);
	property_set(g_opt_class, opt, "AnimationDecodeMode", &mode);
	return opt;
}

// The user's animated avatar: 0 = none, else its file time; uri = the still or the animation.
long avatar_uri(long user, bool still, char* uri, size_t cap) {
	char        path[128];
	struct stat st {};
	snprintf(path, sizeof(path), "%s/%ld.png", kAvatarDir, user);
	if (user <= 0 || stat(path, &st) != 0 || st.st_size <= 64) {
		return 0;
	}
	const long t = static_cast<long>(st.st_mtime);
	snprintf(path, sizeof(path), "%s/%ld%s.png", kAvatarDir, user, still ? "_still" : "");
	snprintf(uri, cap, "%s?ts=%ld", path, t);
	return t;
}

Avatar* avatar_of(long user) {
	for (Avatar& a : g_avatars) {
		if (a.user == user) {
			return &a;
		}
	}
	for (Avatar& a : g_avatars) {
		if (a.user == 0) {
			a.user = user;
			return &a;
		}
	}
	return nullptr;
}

// The user an avatar address belongs to: "profilecache:image/face/...?userid=<id>" (what is loaded) or the
// profile cache's own file ".../profile/0x<id in hex>/avatar...", which a box shown before may hold; else 0.
long face_user(const char* text) {
	const char* face = strstr(text, "profilecache:image/face/");
	const char* id   = face != nullptr ? strstr(face, "userid=") : nullptr;
	if (id != nullptr) {
		return strtol(id + 7, nullptr, 10);
	}
	const char* dir = strstr(text, "/profile/0x");
	if (dir != nullptr && strstr(dir, "/avatar") != nullptr) {
		return strtol(dir + 9, nullptr, 16);
	}
	return 0;
}

void remember_view(Avatar& a, Obj view, const char* uri) {
	for (int i = 0; i < a.nviews; ++i) {
		if (a.views[i].view == view) {
			snprintf(a.views[i].uri, sizeof(a.views[i].uri), "%s", uri);
			return;
		}
	}
	mono_gchandle_new(view, 1);
	AvatarView& v = a.views[a.nviews < 16 ? a.nviews++ : (g_tick % 16)];
	v.view        = view;
	snprintf(v.uri, sizeof(v.uri), "%s", uri);
}

// view.LoadAsync(uri, null, option, true); without an option: view.LoadAsync(uri) (Sony's own defaults)
bool view_load(Obj view, const char* uri, Obj opt) {
	const int argc = opt != nullptr ? 4 : 1;
	Obj       load = nullptr;
	for (Obj k = mono_object_get_class(view); k != nullptr && load == nullptr; k = mono_class_get_parent(k)) {
		load = mono_class_get_method_from_name(k, "LoadAsync", argc);
	}
	bool  yes     = true;
	void* args[4] = {mono_string_new(g_domain, uri), nullptr, opt, &yes};
	return load != nullptr && invoke(load, view, args, "ImageBox.LoadAsync");
}

// Show a remembered avatar view again. React Native's image view (the round, masked avatar) sets its picture
// again from a copy of its own Source (same address: the image hook makes it the animated avatar, or Sony's
// when there is none), so it draws its mask again too - loading a picture into it underneath does not show.
// A plain image box loads `uri` itself (Sony's own address when going back).
bool refresh_view(Obj view, const char* uri, bool animated) {
	Obj src_get = nullptr, src_set = nullptr;
	for (Obj k = mono_object_get_class(view); k != nullptr && src_set == nullptr; k = mono_class_get_parent(k)) {
		Obj prop = mono_class_get_property_from_name(k, "Source");
		if (prop != nullptr) {
			src_get = mono_property_get_get_method(prop);
			src_set = mono_property_get_set_method(prop);
		}
	}
	if (src_get != nullptr && src_set != nullptr) {
		Obj exc = nullptr;
		Obj src = mono_runtime_invoke(src_get, view, nullptr, &exc);
		if (exc == nullptr && src != nullptr) {
			Obj clone = nullptr;
			for (Obj k = mono_object_get_class(src); k != nullptr && clone == nullptr; k = mono_class_get_parent(k)) {
				clone = mono_class_get_method_from_name(k, "DeepClone", 0);
			}
			Obj copy = nullptr;
			if (clone != nullptr && invoke(clone, src, nullptr, "JToken.DeepClone", &copy) && copy != nullptr) {
				void*      args[1] = {copy};
				const bool ok      = invoke(src_set, view, args, "ReactImageBox.Source");
				static int logged  = 0;
				if (logged++ < 8) {
					wp_log("avatar: view %p set again through its Source (%s)", view, ok ? "ok" : "FAILED");
				}
				return ok;
			}
		}
	}
	return view_load(view, uri, animated ? anim_option(nullptr) : nullptr);
}

// ---- animated game tiles (v1.7.0) ----------------------------------------------------------
// /data/LiveShell/video/.tiles/<TITLE ID>.png (an animated PNG the daemon made; ShellUI sees it as kTileDir)
// replaces that tile's icon0.png. Sony loads tile icons through ImageAsset.LoadAsync like avatars
// ("/user/app/<ID>/sce_sys/icon0.png?ts=..+336_336_KeepFitSize_Bc7U", the PS Store
// "/system_ex/rnps/apps/NPXS40047/appdb/default/icon0.png?ts=.."): the address becomes ours, without Sony's
// ending, with a NEW animated ImageOptions. Sony's tile options squash the picture into a BC7 texture: a copy
// of them (as avatars use) froze the tile on its first picture after the Media tab. Stable address, like
// avatars. Tiles already on screen are switched by the widget walk; a removed / changed file switches them back
// / again (the folder's time is watched, so a pick shows within a moment).
constexpr const char* kTileDir = "/system_ex/vsh_asset/wallpaper/.tiles";
struct TileOrig {
	char tid[10];
	char uri[200]; // Sony's address for the tile, loaded again when ours goes
};
TileOrig g_tile_orig[1024]; // any number of games (user)
int      g_ntile_orig = 0, g_tile_logs = 0;
long     g_tiles_mtime = -2;

// The title id in a tile icon address: ".../app/<ID>/..", ".../apps/<ID>/..", ".../appmeta/<ID>/..", ".tiles/<ID>.png"
bool tile_id(const char* u, char* id) {
	const char* keys[] = {"/app/", "/apps/", "/appmeta/", "/.tiles/"};
	for (const char* k : keys) {
		const char* a = strstr(u, k);
		if (a == nullptr) {
			continue;
		}
		a += strlen(k);
		size_t n = 0;
		while (n < 9 && isalnum(static_cast<unsigned char>(a[n]))) {
			id[n] = a[n];
			++n;
		}
		id[n] = 0;
		if (n == 9 && !isalnum(static_cast<unsigned char>(a[9]))) {
			return true;
		}
	}
	return false;
}

// Our animated tile for this title: its address (with the file time, as avatars), or false when there is none.
bool tile_file(const char* id, char* out, size_t cap) {
	char        path[96];
	struct stat st {};
	snprintf(path, sizeof(path), "%s/%s.png", kTileDir, id);
	if (stat(path, &st) != 0 || st.st_size <= 64) {
		return false;
	}
	snprintf(out, cap, "%s?ts=%ld", path, static_cast<long>(st.st_mtime));
	return true;
}

void remember_tile(const char* id, const char* uri) {
	for (int i = 0; i < g_ntile_orig; ++i) {
		if (strcmp(g_tile_orig[i].tid, id) == 0) {
			snprintf(g_tile_orig[i].uri, sizeof(g_tile_orig[i].uri), "%s", uri);
			return;
		}
	}
	TileOrig& o = g_tile_orig[g_ntile_orig < 1024 ? g_ntile_orig++ : (g_tick % 1024)];
	snprintf(o.tid, sizeof(o.tid), "%s", id);
	snprintf(o.uri, sizeof(o.uri), "%s", uri);
}

const char* tile_orig(const char* id) {
	for (int i = 0; i < g_ntile_orig; ++i) {
		if (strcmp(g_tile_orig[i].tid, id) == 0) {
			return g_tile_orig[i].uri;
		}
	}
	return nullptr;
}

bool tiles_exist() {
	bool any = false;
	if (DIR* d = opendir(kTileDir)) {
		while (dirent* e = readdir(d)) {
			any = any || strstr(e->d_name, ".png") != nullptr;
		}
		closedir(d);
	}
	return any;
}


Obj AssetLoad_Hook(Obj uri, Obj action, Obj option) {
	char       u[200], ours[200];
	const bool text = uri != nullptr && mono_ascii(uri, u, sizeof(u)) > 0;
	if (text && strstr(u, kTileDir) != nullptr) { // our tile again (a box loading our address): animated
		Obj opt = anim_option(nullptr);
		return g_assetload_orig(uri, action, opt != nullptr ? opt : option);
	}
	if (text && strstr(u, "icon0.png") != nullptr) { // a tile icon: ours when there is one
		char id[10];
		if (tile_id(u, id) && tile_file(id, ours, sizeof(ours))) {
			Obj opt = anim_option(nullptr); // new: not a copy of Sony's (BC7: a still picture)
			if (opt != nullptr) {
				remember_tile(id, u);
				if (g_tile_logs++ < 20) {
					wp_log("tile: %s -> %s", u, ours);
				}
				return g_assetload_orig(mono_string_new(g_domain, ours), action, opt);
			}
		}
	}
	if (text && strstr(u, kAvatarDir) != nullptr && strstr(u, "_still") == nullptr) { // ours (set in a Source): animated
		Obj opt = anim_option(option);
		return g_assetload_orig(uri, action, opt != nullptr ? opt : option);
	}
	const long user = text ? face_user(u) : 0;
	Avatar*    a    = user > 0 ? avatar_of(user) : nullptr;
	if (a == nullptr) {
		return g_assetload_orig(uri, action, option);
	}
	if (g_loading_view != nullptr) {
		remember_view(*a, g_loading_view, u);
	}
	const long t = avatar_uri(user, false, ours, sizeof(ours));
	if (t != 0 && a->mtime == t) { // decoded: the animation
		Obj opt = anim_option(option);
		if (opt != nullptr) {
			return g_assetload_orig(mono_string_new(g_domain, ours), action, opt);
		}
	} else if (t != 0) { // new, still decoding: its first picture
		avatar_uri(user, true, ours, sizeof(ours));
		return g_assetload_orig(mono_string_new(g_domain, ours), action, option);
	}
	return g_assetload_orig(uri, action, option);
}

void BoxLoad2_Hook(Obj self, Obj uri, Obj action, Obj option, bool set_image) {
	Obj before     = g_loading_view;
	g_loading_view = self;
	g_boxload2_orig(self, uri, action, option, set_image);
	g_loading_view = before;
}

void BoxLoad3_Hook(Obj self, Obj uri, Obj action, Obj option, bool set_image) {
	Obj before     = g_loading_view;
	g_loading_view = self;
	g_boxload3_orig(self, uri, action, option, set_image);
	g_loading_view = before;
}

// A Source (JObject) with its "uri" replaced: Newtonsoft's JObject.Parse of the changed text.
Obj g_jparse = nullptr;

Obj source_with_uri(Obj source, const char* uri) {
	Obj  inner = nullptr;
	Obj  str   = mono_object_to_string(source, &inner);
	char text[1024];
	if (str == nullptr || inner != nullptr || mono_ascii(str, text, sizeof(text)) >= sizeof(text) - 1) {
		return nullptr;
	}
	char* key = strstr(text, "\"uri\"");
	char* q1  = key != nullptr ? strchr(key + 5, '"') : nullptr;
	char* q2  = q1 != nullptr ? strchr(q1 + 1, '"') : nullptr;
	if (q2 == nullptr) {
		return nullptr;
	}
	char out[1400];
	snprintf(out, sizeof(out), "%.*s%s%s", static_cast<int>(q1 + 1 - text), text, uri, q2);
	if (g_jparse == nullptr) {
		Obj jo   = nullptr;
		Obj nimg = open_image("/system_ex/common_ex/lib/Newtonsoft.Json.PlayStation.dll");
		jo       = nimg != nullptr ? mono_class_from_name(nimg, "Newtonsoft.Json.Linq", "JObject") : nullptr;
		g_jparse = jo != nullptr ? mono_class_get_method_from_name(jo, "Parse", 1) : nullptr;
	}
	Obj   parsed  = nullptr;
	void* args[1] = {mono_string_new(g_domain, out)};
	return g_jparse != nullptr && invoke(g_jparse, nullptr, args, "JObject.Parse", &parsed) ? parsed : nullptr;
}

// React Native's image view: Sony's avatar address -> ours once decoded, ours -> Sony's when it is gone. The
// change is made in the Source itself: for Sony's address the image cache hands back Sony's picture without
// loading anything (so the image hook alone never sees it for an avatar already shown).
void SetSource_Hook(Obj self, Obj source) {
	Obj before     = g_loading_view;
	g_loading_view = self;
	Obj use        = source;
	Obj inner      = nullptr;
	Obj str        = source != nullptr ? mono_object_to_string(source, &inner) : nullptr;
	char text[400], uri[200];
	if (str != nullptr && inner == nullptr && mono_ascii(str, text, sizeof(text)) > 0) {
		const long face = face_user(text);
		const char* mine = strstr(text, kAvatarDir);
		const long  user = face > 0 ? face : mine != nullptr ? strtol(mine + strlen(kAvatarDir) + 1, nullptr, 10) : 0;
		Avatar*     a    = user > 0 ? avatar_of(user) : nullptr;
		const long  t    = a != nullptr ? avatar_uri(user, false, uri, sizeof(uri)) : 0;
		if (a != nullptr && face > 0) {
			const char* f = strstr(text, "profilecache:");
			const char* e = f != nullptr ? strchr(f, '"') : nullptr;
			char        fu[160];
			snprintf(fu, sizeof(fu), "%.*s", e != nullptr ? static_cast<int>(e - f) : 0, f != nullptr ? f : "");
			remember_view(*a, self, fu);
			if (t != 0 && a->mtime == t) {
				Obj changed = source_with_uri(source, uri);
				use         = changed != nullptr ? changed : source;
			}
		} else if (a != nullptr && mine != nullptr && (t == 0 || a->mtime != t)) { // ours, but gone or changed
			const char* back = nullptr;
			for (int i = 0; i < a->nviews && back == nullptr; ++i) {
				back = a->views[i].view == self && a->views[i].uri[0] != 0 ? a->views[i].uri : nullptr;
			}
			char dflt[120];
			snprintf(dflt, sizeof(dflt), "profilecache:image/face/default?userid=%ld&size=m&salt=1", user);
			Obj changed = source_with_uri(source, t != 0 && a->mtime == t ? uri : back != nullptr ? back : dflt);
			use         = changed != nullptr ? changed : source;
		}
	}
	g_setsrc_orig(self, use);
	g_loading_view = before;
}

// ---- avatars already on screen: walk the widgets ----
struct ClassGetters {
	Obj klass = nullptr, first = nullptr, next = nullptr, image = nullptr;
};
ClassGetters g_cg[96];
int          g_ncg = 0;
Obj          g_asset_class = nullptr, g_asset_uri = nullptr;

// A property's getter, looked up in the class and then its parents (the lookup itself stays in one class).
Obj getter(Obj klass, const char* name) {
	for (Obj k = klass; k != nullptr; k = mono_class_get_parent(k)) {
		Obj prop = mono_class_get_property_from_name(k, name);
		Obj get  = prop != nullptr ? mono_property_get_get_method(prop) : nullptr;
		if (get != nullptr) {
			return get;
		}
	}
	return nullptr;
}

int  g_scan_logs = 0;               // the first walks log what they saw
int  g_scan_widgets = 0, g_scan_boxes = 0;
char g_scan_sample[600];

const ClassGetters* getters_of(Obj klass) {
	for (int i = 0; i < g_ncg; ++i) {
		if (g_cg[i].klass == klass) {
			return &g_cg[i];
		}
	}
	if (g_ncg >= 96) {
		return nullptr;
	}
	ClassGetters& c = g_cg[g_ncg++];
	c.klass         = klass;
	c.first         = getter(klass, "FirstChildBase");
	c.next          = getter(klass, "NextSiblingBase");
	c.image         = getter(klass, "Image");
	return &c;
}

Obj call0(Obj method, Obj obj) {
	Obj exc = nullptr;
	Obj r   = method != nullptr && obj != nullptr ? mono_runtime_invoke(method, obj, nullptr, &exc) : nullptr;
	return exc != nullptr ? nullptr : r;
}

void avatar_switch(Avatar& a, Obj view);

// One widget: an image box showing Sony's avatar is remembered (and switched when the user has one ready).
int scan_widget(Obj w, int depth, int& budget) {
	int found = 0;
	while (w != nullptr && budget-- > 0) {
		const ClassGetters* c = getters_of(mono_object_get_class(w));
		if (c == nullptr) {
			return found;
		}
		++g_scan_widgets;
		if (c->image != nullptr) {
			Obj asset = call0(c->image, w);
			if (asset != nullptr && mono_object_get_class(asset) == g_asset_class) {
				Obj  uri = call0(g_asset_uri, asset);
				char u[200];
				u[0] = 0;
				const long user = uri != nullptr && mono_ascii(uri, u, sizeof(u)) > 0 ? face_user(u) : 0;
				++g_scan_boxes;
				if (g_scan_logs < 3 && strlen(g_scan_sample) + strlen(u) + 4 < sizeof(g_scan_sample) &&
				    (strstr(u, "profile") != nullptr || strstr(u, "face") != nullptr || g_scan_boxes <= 6)) {
					strcat(g_scan_sample, u);
					strcat(g_scan_sample, " | ");
				}
				Avatar*    a    = user > 0 ? avatar_of(user) : nullptr;
				if (a != nullptr) {
					remember_view(*a, w, u);
					avatar_switch(*a, w);
					++found;
				}
				if (strstr(u, kTileDir) != nullptr || strstr(u, "icon0.png") != nullptr) { // a game tile
					char id[10], tu[200];
					if (tile_id(u, id)) {
						const bool  have = tile_file(id, tu, sizeof(tu));
						const bool  ours = strstr(u, kTileDir) != nullptr;
						const char* back = ours && !have ? tile_orig(id) : nullptr;
						if (back != nullptr) { // removed: Sony's icon again
							const bool ok = view_load(w, back, nullptr);
							if (g_tile_logs++ < 40) {
								wp_log("tile: %s back to %s: %s", id, back, ok ? "ok" : "FAILED");
							}
						} else if (have && strcmp(u, tu) != 0) { // new, or changed: ours (animated)
							if (!ours) {
								remember_tile(id, u);
							}
							const bool ok = view_load(w, tu, anim_option(nullptr));
							if (g_tile_logs++ < 40) {
								wp_log("tile: box %s -> %s: %s", id, tu, ok ? "ok" : "FAILED");
							}
						}
					}
				}
			}
		}
		if (depth < 64 && c->first != nullptr) {
			found += scan_widget(call0(c->first, w), depth + 1, budget);
		}
		w = c->next != nullptr ? call0(c->next, w) : nullptr;
	}
	return found;
}

int avatar_scan() {
	if (g_asset_class == nullptr) {
		g_asset_class = find_class("Sce.PlayStation.PUI", "ImageAsset");
		g_asset_uri   = g_asset_class != nullptr ? getter(g_asset_class, "Uri") : nullptr;
	}
	Obj sm   = find_class("Sce.PlayStation.PUI", "SceneManager");
	Obj ig   = sm != nullptr ? getter(sm, "Instance") : nullptr;
	Obj exc0 = nullptr;
	Obj inst = ig != nullptr ? mono_runtime_invoke(ig, nullptr, nullptr, &exc0) : nullptr; // static
	if (exc0 != nullptr || inst == nullptr || g_asset_class == nullptr) {
		return -1;
	}
	int  found = 0, budget = 30000, nscenes = 0;
	Obj  seen[96];
	char info[700];
	info[0]          = 0;
	g_scan_widgets   = g_scan_boxes = 0;
	g_scan_sample[0] = 0;
	const char* lists[3] = {"SceneLayers", "RenderList", "OverlayList"};
	for (const char* ln : lists) {
		Obj layers = call0(getter(sm, ln), inst);
		if (layers == nullptr) {
			continue;
		}
		Obj       lk    = mono_object_get_class(layers);
		Obj       count = call0(getter(lk, "Count"), layers);
		Obj       item  = mono_class_get_method_from_name(lk, "get_Item", 1);
		const int n     = count != nullptr ? *reinterpret_cast<int*>(static_cast<char*>(count) + 16) : 0;
		for (int i = 0; i < n && i < 64 && item != nullptr; ++i) {
			void* args[1] = {&i};
			Obj   exc     = nullptr;
			Obj   scene   = mono_runtime_invoke(item, layers, args, &exc);
			bool  dup     = exc != nullptr || scene == nullptr;
			for (int k = 0; k < nscenes && !dup; ++k) {
				dup = seen[k] == scene;
			}
			if (dup || nscenes >= 96) {
				continue;
			}
			seen[nscenes++] = scene;
			Obj         root = call0(getter(mono_object_get_class(scene), "RootWidget"), scene);
			const int   w0   = g_scan_widgets;
			found += scan_widget(root, 0, budget);
			const char* sn   = mono_class_get_name(mono_object_get_class(scene));
			const char* rn   = root != nullptr ? mono_class_get_name(mono_object_get_class(root)) : "-";
			char        one[96];
			snprintf(one, sizeof(one), "%s/%s:%s:%d ", ln[0] == 'S' ? "L" : ln[0] == 'R' ? "R" : "O", sn != nullptr ? sn : "?",
			         rn != nullptr ? rn : "?", g_scan_widgets - w0);
			if (strlen(info) + strlen(one) + 1 < sizeof(info)) {
				strcat(info, one);
			}
		}
	}
	if (g_scan_logs++ < 3) {
		wp_log("avatar scan: %d scenes, %d widgets, %d image boxes, %d avatars; scenes: %.500s", nscenes, g_scan_widgets, g_scan_boxes,
		       found, info);
		wp_log("avatar scan seen: %.560s", g_scan_sample);
	}
	return found;
}

void avatar_hooks() {
	g_avatar_hooked = true;
	detour_method("Sce.PlayStation.PUI", "ImageAsset", "LoadAsync", 3, reinterpret_cast<void*>(&AssetLoad_Hook),
	              reinterpret_cast<void**>(&g_assetload_orig));
	detour_method("ReactNative.PUI", "ReactImageBox", "set_Source", 1, reinterpret_cast<void*>(&SetSource_Hook),
	              reinterpret_cast<void**>(&g_setsrc_orig));
	// image boxes outside React Native (the top bar's avatar): UI2 and UI3 ImageBox.LoadAsync(uri, action, option, set)
	Obj         pui   = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	const char* ns[2] = {"Sce.PlayStation.PUI.UI2", "Sce.PlayStation.PUI.UI3"};
	void*       hk[2] = {reinterpret_cast<void*>(&BoxLoad2_Hook), reinterpret_cast<void*>(&BoxLoad3_Hook)};
	void**      og[2] = {reinterpret_cast<void**>(&g_boxload2_orig), reinterpret_cast<void**>(&g_boxload3_orig)};
	for (int i = 0; i < 2; ++i) {
		Obj             k    = pui != nullptr ? mono_class_from_name(pui, ns[i], "ImageBox") : nullptr;
		Obj             m    = k != nullptr ? mono_class_get_method_from_name(k, "LoadAsync", 4) : nullptr;
		const uint64_t  addr = m != nullptr ? reinterpret_cast<uint64_t>(mono_compile_method(m)) : 0;
		const uintptr_t old  = set_ucred_to_ptrace();
		const bool      ok   = addr != 0 && InstallDetour(addr, hk[i], og[i]) && *og[i] != nullptr;
		if (old != 0) {
			set_proc_authid(getpid(), old);
		}
		wp_log("hook %s.ImageBox.LoadAsync(4): %s", ns[i], ok ? "installed" : "FAILED");
	}
	// avatar files already there: decoded from now on (users seen later start theirs when first shown)
	if (DIR* d = opendir(kAvatarDir)) {
		while (dirent* e = readdir(d)) {
			const long u = strtol(e->d_name, nullptr, 10);
			if (u > 0 && strstr(e->d_name, "_still") == nullptr) {
				avatar_of(u);
			}
		}
		closedir(d);
	}
}

// Sony's own "this user's profile changed" signal (what follows a new PSN avatar): every avatar of that user
// on screen is loaded again, with a new address (so not from the image cache), through the image hook - the
// animated one, or Sony's when it is gone. At most every 4 s per user.
void profile_changed(long user) {
	static Obj    notify = nullptr, inst_get = nullptr;
	static bool   looked = false;
	static long   last_user[8] {};
	static int    last_tick[8] {};
	if (!looked) {
		looked = true;
		Obj k    = find_class("Sce.Vsh.ShellUI.ProfileCache", "ProfileCacheManager");
		notify   = k != nullptr ? mono_class_get_method_from_name(k, "NotifyUpdateProfileCacheVersion", 1) : nullptr;
		inst_get = k != nullptr ? getter(k, "Instance") : nullptr;
	}
	int slot = 0;
	while (slot < 7 && last_user[slot] != 0 && last_user[slot] != user) {
		++slot;
	}
	if (last_user[slot] == user && g_tick - last_tick[slot] < 240) {
		return;
	}
	last_user[slot] = user;
	last_tick[slot] = g_tick;
	Obj        exc  = nullptr;
	Obj        inst = inst_get != nullptr ? mono_runtime_invoke(inst_get, nullptr, nullptr, &exc) : nullptr; // static
	int        uid  = static_cast<int>(user);
	void*      args[1] = {&uid};
	const bool ok   = inst != nullptr && exc == nullptr && notify != nullptr && invoke(notify, inst, args, "NotifyUpdateProfileCacheVersion");
	wp_log("avatar: user %ld - the profile-changed signal %s", user, ok ? "sent" : "FAILED");
}

// A view showing Sony's avatar for a user whose animated one is decoded: switch it now.
void avatar_switch(Avatar& a, Obj view) {
	char       uri[200];
	const long t = avatar_uri(a.user, false, uri, sizeof(uri));
	if (t != 0 && a.mtime == t) {
		refresh_view(view, uri, true);
		profile_changed(a.user);
	}
}

int g_scan_next = 0; // tick of the next walk over the widgets

// Every ~0.25 s: a new, changed or removed avatar file -> decode it, then switch every avatar of that user.
void avatar_tick() {
	if (!g_avatar_hooked) {
		if (g_tick >= 120) { // ~2 s after the module's start: from then on every avatar shown is remembered
			avatar_hooks();
			g_scan_next = g_tick + 60;
		}
		return;
	}
	if (g_tick % 15 == 0) { // the tiles folder changed (a pick, a removal): walk the screen now
		struct stat st {};
		const long  m = stat(kTileDir, &st) == 0 ? static_cast<long>(st.st_mtime) : -1;
		if (m != g_tiles_mtime) {
			if (g_tiles_mtime != -2) {
				g_scan_next = g_tick + 1;
			}
			g_tiles_mtime = m;
		}
	}
	if (g_scan_next != 0 && g_tick >= g_scan_next) {
		DIR* d   = opendir(kAvatarDir);
		bool any = false;
		if (d != nullptr) {
			while (dirent* e = readdir(d)) {
				any = any || strtol(e->d_name, nullptr, 10) > 0;
			}
			closedir(d);
		}
		g_scan_next = g_tick + 1200; // ~20 s (only walks while someone has an animated avatar)
		any = any || g_ntile_orig > 0 || tiles_exist(); // animated tiles: walked too
		if (any) {
			const int n = avatar_scan();
			static int logged = 0;
			if (logged++ < 5) {
				wp_log("avatar: %d avatars on screen", n);
			}
		}
	}
	if (g_tick % 15 != 0) {
		return;
	}
	for (Avatar& a : g_avatars) {
		if (a.user <= 0) {
			continue;
		}
		char       uri[200];
		const long t = avatar_uri(a.user, false, uri, sizeof(uri));
		if (t == 0 && a.mtime != 0) { // removed: Sony's avatar everywhere again
			a.mtime = a.want = 0;
			int n = 0;
			for (int i = 0; i < a.nviews; ++i) {
				n += refresh_view(a.views[i].view, a.views[i].uri, false) ? 1 : 0;
			}
			wp_log("avatar: user %ld back to the PSN avatar (%d views)", a.user, n);
			profile_changed(a.user);
			continue;
		}
		if (t == 0 || t == a.mtime) {
			continue;
		}
		if (a.want != t) { // new or changed: decode it in a hidden image box (and find the avatars shown now)
			avatar_scan();
			Obj k = find_class("Sce.PlayStation.PUI", "ImageBox");
			Obj c = k != nullptr ? mono_class_get_method_from_name(k, ".ctor", 0) : nullptr;
			Obj b = k != nullptr ? mono_object_new(g_domain, k) : nullptr;
			if (b == nullptr || c == nullptr || !invoke(c, b, nullptr, "ImageBox()")) {
				continue;
			}
			mono_gchandle_new(b, 1);
			a.box   = b;
			a.want  = t;
			a.since = g_tick;
			view_load(b, uri, anim_option(nullptr));
			continue;
		}
		Obj       frames = property_get(mono_object_get_class(a.box), a.box, "FrameCount");
		const int fc     = frames != nullptr ? *reinterpret_cast<int*>(static_cast<char*>(frames) + 16) : 0;
		if (fc > 1 || g_tick - a.since > 300) { // decoded (or 5 s: switch anyway, the views decode it themselves)
			a.mtime = t;
			int n   = 0;
			for (int i = 0; i < a.nviews; ++i) {
				n += refresh_view(a.views[i].view, uri, true) ? 1 : 0;
			}
			wp_log("avatar: user %ld animated, %d views switched (%d frames, %d ticks)", a.user, n, fc, g_tick - a.since);
			profile_changed(a.user);
		}
	}
}

void* wallpaper_thread(void*) {
	sleep(3); // was 5: a quicker first picture
	char seen[512];
	read_request_line(seen, sizeof(seen));
	// PS Store only, read BEFORE the first clip starts: the loop below only reads it every 0.3 s, so
	// the video showed on the highlighted tile for a moment after loading the ELF (user, v1.2).
	// Start hidden then; the Store tile fades it in as usual.
	if (OptFile* f = opt_open(kStoreOnlyFile)) {
		int on = 0;
		if (opt_scanf(f, "%d", &on) == 1 && on == 1) {
			g_store_only.store(true);
			g_fade = 1.0f;
			wp_log("PS Store only: on from the start (video starts hidden)");
		}
		opt_close(f);
	}
	if (guard_exists()) {
		wp_log("video: last attempt did not survive (%s still there)", kGuardFile);
	} else if (!choose_video()) {
		// strict: the configured video or nothing
	} else {
		// ShellUI often may not create files any more (its ~16 KB write budget, test v11-24): the video
		// then waited for the first tile change. Start anyway; the payload stops crash loops itself.
		if (!guard_create()) {
			wp_log("video: cannot write %s, starting anyway", kGuardFile);
		}
		g_video_wanted.store(true, std::memory_order_release);
	}
	g_pending.store(true, std::memory_order_release);
	wp_log("queued for the UI thread");

	char now[512];
	for (;;) {
		usleep(300 * 1000);
		if (OptFile* f = opt_open(kDimFile)) {
			int dim = -1;
			if (opt_scanf(f, "%d", &dim) == 1 && dim >= 0 && dim <= 90 && dim != g_dim_req.load()) {
				g_dim_req.store(dim);
				wp_log("dim request: %d%%", dim);
			}
			opt_close(f);
		}
		// Repeat the status every ~2 s: a payload started while we already play learns it at once
		// (it waited 40 s for a change before, test v11-24).
		static int status_beat = 0;
		if (++status_beat >= 7 && g_last_status[0] != 0) {
			status_beat = 0;
			to_payload('S', g_last_status, strlen(g_last_status));
		}
		if (OptFile* f = opt_open(kVolumeFile)) {
			int vol = -1;
			if (opt_scanf(f, "%d", &vol) == 1 && vol >= 0 && vol <= 100 && vol != g_vol_req.load()) {
				g_vol_req.store(vol);
			}
			opt_close(f);
		}
		if (OptFile* f = opt_open(kStoreOnlyFile)) {
			int on = 0;
			if (opt_scanf(f, "%d", &on) == 1 && (on == 0 || on == 1) && (on == 1) != g_store_only.load()) {
				g_store_only.store(on == 1);
				wp_log("PS Store only: %s", on ? "on" : "off");
			}
			opt_close(f);
		}
		if (OptFile* f = opt_open(kMenusFile)) {
			int menus = 0;
			if (opt_scanf(f, "%d", &menus) == 1 && (menus == 0 || menus == 1) && menus != g_menus_req.load()) {
				g_menus_req.store(menus);
				wp_log("menus request: %s", menus ? "hide" : "show");
			}
			opt_close(f);
		}
		if (OptFile* f = opt_open("/system_tmp/liveshell/tint.txt")) {
			int tn = 0;
			if (opt_scanf(f, "%d", &tn) == 1 && tn >= 0 && tn <= 5 && tn != g_tint_req.load()) {
				g_tint_req.store(tn);
				g_dim_shown = -1; // refresh_dim paints the new colour
				wp_log("colour: %d", tn);
			}
			opt_close(f);
		}
		if (OptFile* f = opt_open("/system_tmp/liveshell/launchfx.txt")) {
			int lf = 0;
			if (opt_scanf(f, "%d", &lf) == 1 && lf >= 0 && lf <= 2 && lf != g_lfx_req.load()) {
				g_lfx_req.store(lf);
				wp_log("launch effect: %d", lf);
			}
			opt_close(f);
		}
		if (OptFile* f = opt_open(kParallaxFile)) {
			int px = 0;
			if (opt_scanf(f, "%d", &px) == 1 && (px == 0 || px == 1) && px != g_parallax_req.load()) {
				g_parallax_req.store(px);
				wp_log("parallax request: %d", px);
			}
			opt_close(f);
		}
		if (OptFile* f = opt_open(kLooksFile)) {
			int v[kLooks] = {-1, -1, -1, -1};
			if (opt_scanf(f, "%d %d %d %d", &v[0], &v[1], &v[2], &v[3]) == 4) {
				for (int l = 0; l < kLooks; ++l) {
					if (v[l] >= 0 && v[l] <= 2 && v[l] != g_look_req[l].load()) {
						g_look_req[l].store(v[l]);
						wp_log("look request: %d -> %d", l, v[l]);
					}
				}
			}
			opt_close(f);
		}
		read_request_line(now, sizeof(now));
		if (now[0] == 0 || strcmp(now, seen) == 0) {
			continue;
		}
		memcpy(seen, now, sizeof(seen));
		pthread_mutex_lock(&g_req_lock);
		memcpy(g_req_line, now, sizeof(g_req_line));
		pthread_mutex_unlock(&g_req_lock);
		g_req_new.store(true, std::memory_order_release);
	}
	return nullptr;
}

} // namespace

// ---- entry point (called by the daemon's injector) -------------------------------------------

extern "C" int main(int argc, char const* argv[]) {
	(void)argc;
	(void)argv;

	mkdir("/system_tmp/liveshell", 0777);
	g_log   = open(kLogFile, O_WRONLY | O_CREAT | O_TRUNC, 0666);
	g_t0_ms = now_ms();
	ui_channel_open();
	const pid_t pid = getpid();
	wp_log("LiveShell ShellUI module starting (pid %d)", static_cast<int>(pid));

	// The injector is still inside ShellUI for a few ms after starting this thread (breakpoint,
	// register restore, detach). Kernel reads cut by that stop hung the whole process (tests 2, 4, 5),
	// so touch nothing until it is long gone.
	usleep(1500 * 1000);
	wp_log("injector gone, starting");

	pthread_t hb;
	if (pthread_create(&hb, nullptr, heartbeat_thread, nullptr) == 0) {
		pthread_detach(hb);
	}

	// Raised authid for the whole setup, like OnionHEN's toolbox: symbol lookups and the detour's
	// code-page mprotect need it. Dropped once the hook is in.
	g_step.store("set_ucred_to_ptrace");
	const uintptr_t old_authid = set_ucred_to_ptrace();
	wp_log("authid raised (old %#lx)", static_cast<unsigned long>(old_authid));
	auto fail = [&](const char* text, int rc) {
		wp_log("setup failed: %s", text);
		if (old_authid != 0) {
			set_proc_authid(pid, old_authid);
		}
		notify(text);
		return rc;
	};

	if (!resolve_kernel()) {
		return fail("LiveShell Engine could not start (kernel symbols missing)", 1);
	}
	if (!resolve_mono()) {
		return fail("LiveShell Engine could not start (Mono symbols missing)", 1);
	}
	g_step.store("mono_get_root_domain / mono_thread_attach");
	g_domain = mono_get_root_domain();
	mono_thread_attach(g_domain);
	wp_log("Mono domain %p, thread attached", g_domain);

	g_step.store("mprotect probe");
	char probe[100];
	has_hv_bypass = sceKernelMprotect(probe, sizeof(probe), 0x7) == 0;
	wp_log("mprotect probe: has_hv_bypass=%d", has_hv_bypass ? 1 : 0);

	g_step.store("open PUI assembly");
	Obj pui_image = open_image("/system_ex/common_ex/lib/Sce.PlayStation.PUI.dll");
	wp_log("PUI image %p", pui_image);
	if (pui_image == nullptr) {
		return fail("LiveShell Engine could not start (PUI not found)", 2);
	}
	g_step.store("compile Application.Update");
	const uint64_t update_addr =
	    get_method_address(pui_image, "Sce.PlayStation.PUI", "Application", "Update", 0);
	wp_log("Application.Update compiled at %#lx", static_cast<unsigned long>(update_addr));
	if (update_addr == 0) {
		return fail("LiveShell Engine could not start (Update not found)", 3);
	}
	g_step.store("InstallDetour(Application.Update)");
	if (!InstallDetour(update_addr, reinterpret_cast<void*>(&Update_Hook),
	                   reinterpret_cast<void**>(&g_update_orig)) ||
	    g_update_orig == nullptr) {
		// Another tool (a HEN or toolbox) hooks the same Application.Update and, loaded first, its jump
		// sits at the start: a second detour there fails ("hook failed", v1.1 next to OnionHEN; issue #8).
		// Follow that jump and hook the function it leads to: LiveShell -> that tool -> Sony.
		g_update_orig = nullptr;
		const uint64_t page = update_addr & ~static_cast<uint64_t>(0x3fff);
		if (sceKernelMprotect != nullptr) {
			(void)sceKernelMprotect(reinterpret_cast<void*>(page), 0x8000, 0x7); // execute-only code: readable first
		}
		const uint8_t* b = reinterpret_cast<const uint8_t*>(update_addr);
		wp_log("Application.Update starts with %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
		       b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9], b[10], b[11], b[12], b[13]);
		// The jump's target lives in that tool's own memory (another ELF), execute-only too: it must be made
		// readable before the detour can copy its first bytes (after rest mode OnionHEN is back first and the
		// chain failed: "no other hook to chain after"). Up to 3 jumps in a row (two tools chained).
		auto jump_target = [](uint64_t at) -> uint64_t {
			const uint8_t* c = reinterpret_cast<const uint8_t*>(at);
			uint64_t       t = 0;
			if (c[0] == 0xe9) { // jmp rel32
				int32_t rel = 0;
				memcpy(&rel, c + 1, 4);
				t = at + 5 + static_cast<int64_t>(rel);
			} else if (c[0] == 0xff && c[1] == 0x25 && c[2] == 0 && c[3] == 0 && c[4] == 0 && c[5] == 0) { // jmp [rip]
				memcpy(&t, c + 6, 8);
			} else if (c[0] == 0x48 && c[1] == 0xb8 && c[10] == 0xff && c[11] == 0xe0) { // mov rax, imm64; jmp rax
				memcpy(&t, c + 2, 8);
			}
			return t;
		};
		uint64_t next = jump_target(update_addr);
		// Best: the other tool's hook is "jmp [rip+0] <address>" at the start of Update. Point that address at
		// us and call the old one when we are done: Sony -> LiveShell -> that tool -> Sony. Only these 8 bytes
		// in Sony's page change (writable: we hook there anyway); the other tool's code is never touched (after
		// rest mode OnionHEN's toolbox is back first, and patching its code failed: "chaining ... failed").
		if (next != 0 && b[0] == 0xff && b[1] == 0x25 && b[2] == 0 && b[3] == 0 && b[4] == 0 && b[5] == 0) {
			g_update_orig       = reinterpret_cast<UpdateFn>(next);
			const uint64_t mine = reinterpret_cast<uint64_t>(&Update_Hook);
			memcpy(reinterpret_cast<void*>(update_addr + 6), &mine, sizeof(mine));
			uint64_t now = 0;
			memcpy(&now, reinterpret_cast<const void*>(update_addr + 6), sizeof(now));
			if (now == mine) {
				wp_log("Application.Update already hooked by another tool: its jump now leads to us first, then to it (%#lx)",
				       static_cast<unsigned long>(next));
				next = 0; // done
			} else {
				g_update_orig = nullptr;
			}
		}
		for (int depth = 0; next != 0 && g_update_orig == nullptr && depth < 3; ++depth) {
			if (sceKernelMprotect != nullptr) {
				(void)sceKernelMprotect(reinterpret_cast<void*>(next & ~static_cast<uint64_t>(0x3fff)), 0x8000, 0x7);
			}
			if (InstallDetour(next, reinterpret_cast<void*>(&Update_Hook), reinterpret_cast<void**>(&g_update_orig)) &&
			    g_update_orig != nullptr) {
				break;
			}
			g_update_orig = nullptr;
			const uint64_t further = jump_target(next);
			wp_log("Application.Update: chaining at %#lx failed, next jump %#lx", static_cast<unsigned long>(next),
			       static_cast<unsigned long>(further));
			next = further;
		}
		if (g_update_orig == nullptr) {
			wp_log("Application.Update: no other hook to chain after (next %#lx)", static_cast<unsigned long>(next));
			write_status("failed hook"); // the payload restarts the home screen once (an old module holds the hook)
			return fail("LiveShell Engine could not start (hook failed)", 4);
		}
		if (next != 0) {
			wp_log("Application.Update already hooked by another tool: chained after it at %#lx",
			       static_cast<unsigned long>(next));
		}
	}
	wp_log("PUI.Application.Update hooked");
	g_step.store("hooked, waiting for UI ticks");

	if (old_authid != 0) {
		set_proc_authid(pid, old_authid);
	}

	pthread_t thread;
	if (pthread_create(&thread, nullptr, wallpaper_thread, nullptr) == 0) {
		pthread_detach(thread);
	} else {
		wp_log("wallpaper_thread start failed");
	}
#ifdef LIVESHELL_RESEARCH_DUMP
	pthread_t dt;
	if (pthread_create(&dt, nullptr, dump_thread, nullptr) == 0) {
		pthread_detach(dt);
	}
#endif
	wp_log("init done");

	// Never return: the injected ELF (and the detour hook code in it) must stay alive, the same
	// way OnionHEN's toolbox parks its main thread.
	for (;;) {
		sleep(60);
	}
}
