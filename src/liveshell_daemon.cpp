/*
 * liveshell_daemon.cpp - LiveShell: the payload the user loads with their ELF launcher.
 * Lists the user's clips, mounts the chosen clip's folder into the system paths ShellUI's video
 * service can read, injects liveshell_shellui.elf into SceShellUI, adds the LiveShell tile to the
 * home screen and serves its window (liveshell_web.cpp). Stays alive to re-inject after ShellUI
 * restarts. GPL-3.0; built on OnionHEN (aydencharles/onionHEN, v0.9.0-beta2).
 *
 * Files:
 *   /data/LiveShell/video/          clips (also <USB>/LiveShell/video)
 *   /data/LiveShell/config.txt      enabled=1 / video=<path>   (written by the window)
 *   /data/LiveShell/liveshell.log   this log + copies of the ShellUI log
 *   /system_tmp/liveshell/video.txt   what ShellUI should play: a path or "off"
 *   /system_tmp/liveshell/status.txt  what ShellUI is doing: playing <path> / stopped / failed <rc>
 */
#include "liveshell.hpp"
#include "zstd_decompress.h"

#include <algorithm>
#include <cmath>
#include <map>
#include <set>
#include <arpa/inet.h>
#include <cctype>
#include <cerrno>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <dirent.h>
#include <fcntl.h>
#include <atomic>
#include <mutex>
#include <netinet/in.h>
#include <pthread.h>
#include <strings.h>
#include <sys/mount.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <unistd.h>

#include <signal.h>

#include "onion/log.h"
#include "onion/proc_query.h"

extern "C" {
bool      Inject_Toolbox(int pid, uint8_t* elf);
int       pt_detach(pid_t pid, int sig);
uintptr_t set_ucred_to_ptrace(void);
uintptr_t set_proc_authid(pid_t pid, uintptr_t new_authid);
int       sceKernelTerminateProcess(int pid, int* ret);
int       sceSystemServiceGetAppIdOfRunningBigApp(void);
int       sceSystemServiceGetAppTitleId(int app_id, char* title_id);
int       kernel_dynlib_handle(pid_t pid, const char* basename, uint32_t* handle);
int       sceKernelOpenEventFlag(intptr_t* event_flag, const char* name);
int       sceKernelPollEventFlag(intptr_t event_flag, uint64_t bits, unsigned int wait_mode, uint64_t* result);
int       sceKernelCloseEventFlag(intptr_t event_flag);
int  sceKernelSendNotificationRequest(int, void*, size_t, int);
int  sceUserServiceInitialize(void* params);
int  sceUserServiceGetForegroundUser(int32_t* user_id);
int  sceUserServiceGetUserName(int32_t user_id, char* name, size_t size);
extern uint8_t liveshell_shellui_elf_start[];
}

__asm__(".section .rodata\n"
        ".global liveshell_shellui_elf_start\n"
        ".type   liveshell_shellui_elf_start, @object\n"
        ".align  16\n"
        "liveshell_shellui_elf_start:\n"
        ".incbin \"" LIVESHELL_SHELLUI_ELF "\"\n"
        ".previous\n");

#ifdef LIVESHELL_RESEARCH_RETRO
extern "C" int retro_start(void (*log_line)(const char* line), void (*notify_line)(const char* line)); // liveshell_retro.c
#endif

namespace liveshell {
namespace {

constexpr const char* kMountPoint     = "/system_ex/vsh_asset/wallpaper";
constexpr const char* kPathFile       = "/system_tmp/liveshell/video.txt";
constexpr const char* kStatusFile     = "/system_tmp/liveshell/status.txt";
constexpr const char* kShellUiLog     = "/system_tmp/liveshell/shellui.log";
constexpr const char* kDimFile        = "/system_tmp/liveshell/dim.txt";
constexpr const char* kVolumeFile     = "/system_tmp/liveshell/volume.txt";
constexpr const char* kMenusFile      = "/system_tmp/liveshell/menus.txt";
constexpr const char* kStoreOnlyFile  = "/system_tmp/liveshell/storeonly.txt";
constexpr const char* kLooksFile      = "/system_tmp/liveshell/looks.txt";
constexpr const char* kPlaylistsBak  = "/data/LiveShell/playlists.bak"; // the playlists before the last save
constexpr const char* kParallaxFile   = "/system_tmp/liveshell/parallax.txt";
constexpr const char* kLogFile        = "/data/LiveShell/liveshell.log";
constexpr const char* kConfigFile     = "/data/LiveShell/config.txt";
constexpr const char* kOurMarker      = "/system_tmp/liveshell/injected";
constexpr const char* kOnionToolbox   = "/system_tmp/onionhen/ready/toolbox";
constexpr int         kOnionCtrlPort  = 9048;
constexpr off_t       kLogMaxSize     = 512 * 1024;
constexpr long        kCrashWindowSec = 120;
constexpr const char* kEarlyCrashFile = "/data/LiveShell/early_crash"; // liveshell.elf: the home screen crashed soon after we joined
std::atomic<bool>     g_planned_restart{false}; // we restarted ShellUI ourselves: not a crash
std::atomic<bool>     g_replaced{false};        // a newer LiveShell (another build) asked us to stop: no "stopped" notice
// Runs next to OnionHEN (tested 2026-10-15): no "OnionHEN is running" refusal any more.
constexpr bool        kOnionGuard     = false;

volatile bool g_running        = true;
volatile bool g_stop_requested = false; // stop came from the user (port 9049), not from a crash
int           g_log     = -1;
std::mutex    g_log_lock;

// Control state; g_ctl guards everything below it.
std::mutex  g_ctl;
bool        g_enabled  = true;
bool        g_user_off = false; // the signed-in user is switched off in Settings -> Users (nothing saved changes)
std::string g_off_users;        // ",<id>,<id>," users LiveShell does not play for
struct Playlist {
	std::string              name;
	bool                     on      = false;
	int                      every   = 5;     // minutes
	bool                     shuffle = false;
	std::vector<std::string> videos;          // real paths
};
std::vector<Playlist> g_playlists;     // one is on at most (guarded by g_ctl)
time_t                g_cycle_at = 0;  // when the main wallpaper last changed (by hand or by a playlist)
std::atomic<int32_t> g_fg_user {-1}; // the signed-in console user (-1 = not known yet)
int         g_dim      = 25;    // default on: clips are often bright
int         g_volume   = 100;   // sound of clips that have it, 0..100 %
int         g_looks[4] = {0, 0, 0, 0}; // bottom fade, top fade, vignette, haze: 0 off, 1 light, 2 strong
bool        g_shuffle  = false; // a random clip each time the payload starts (off by default)
bool        g_main_video = true; // off = only tiles with their own video play one
bool        g_game_videos = true; // off = per-game videos ignored (games.txt kept)
bool        g_game_pause = true; // no video while a game runs
bool        g_menu_hide  = true;  // hide the video in Settings / system apps (default: safer)
bool        g_store_only = false; // video only while the PS Store tile is highlighted (off by default)
bool        g_parallax   = false; // nudge the video when moving between home tiles
bool        g_auto_match = false; // Auto-match (off by default, user)
int         g_tint       = 0;     // Picture -> Colour: 0 neutral, 1 warm, 2 cool, 3 rose, 4 teal, 5 violet
int         g_autonext   = 0;     // Auto-next (no playlist on): 0 off, 1 in order, 2 shuffle (issue #11)
std::atomic<bool> g_ended{false};    // ShellUI: the main clip is about to end
std::string       g_ended_clip;      // ... this one (shown path; guarded by g_ui_lock)
int         g_launchfx   = 0;     // game launch effect: 0 fade, 1 dive, 2 pull back (ShellUI reads launchfx.txt)
bool        g_resume     = false; // Resume after a game (experimental, off by default): ShellUI reads resume.txt
bool        g_game_running = false;
bool        g_game_hide    = false; // option: no video on the home screen while a game is open (suspended)
bool        g_game_open    = false; // a game is open, in front or suspended in the background
constexpr const char* kGameOpenFile = "/system_tmp/liveshell/gameopen.txt"; // ShellUI: do not start a video
std::string g_game_title;
std::string g_override;     // per-game clip playing instead of g_current ("" = main wallpaper)
volatile bool g_focus_recheck = false; // games.txt changed: re-evaluate the highlighted game now
std::string g_current;          // real path of the chosen clip
std::string g_mounted_folder;   // folder currently mounted on kMountPoint
bool        g_injected = false; // the ShellUI module is running (it reacts to the path file)

// ---- small file helpers ----------------------------------------------------------------------

// /system_tmp holds only ~33 files for the whole console (issue #14: OnionHEN + LiveShell ran out). The small
// per-setting files ShellUI polls live in ONE file, opts.txt: "name<TAB>value" lines.
constexpr const char* kOptsFile = "/system_tmp/liveshell/opts.txt";
constexpr const char* kOptNames[] = {"dim.txt", "volume.txt", "menus.txt", "storeonly.txt", "looks.txt", "parallax.txt", "resume.txt", "launchfx.txt", "tint.txt", "gameopen.txt", "gamealive.txt", "window.txt"};

const char* opt_name(const char* path) {
	const char* base = strrchr(path, '/');
	base             = base != nullptr ? base + 1 : path;
	if (strncmp(path, "/system_tmp/liveshell/", 22) != 0) {
		return nullptr;
	}
	for (const char* n : kOptNames) {
		if (strcmp(base, n) == 0) {
			return n;
		}
	}
	return nullptr;
}

bool write_raw(const char* path, const std::string& text, int& err) {
	const int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0666); // in place: no extra file slot needed
	err          = fd < 0 ? errno : 0;
	bool ok      = fd >= 0 && write(fd, text.data(), text.size()) == static_cast<ssize_t>(text.size());
	if (fd >= 0) {
		err = ok ? 0 : errno;
		close(fd);
	}
	return ok;
}

// A failed write is logged once per file (issue #14: we could not tell whether it worked).
bool write_text(const char* path, const std::string& text) {
	int         err  = 0;
	bool        ok   = false;
	const char* name = opt_name(path);
	if (name != nullptr) {
		static std::mutex                         olock;
		static std::map<std::string, std::string> opts;
		std::lock_guard<std::mutex>               g(olock);
		std::string value = text.substr(0, text.find('\n'));
		opts[name]        = value;
		std::string all;
		for (const auto& kv : opts) {
			all += kv.first + "\t" + kv.second + "\n";
		}
		ok   = write_raw(kOptsFile, all, err);
		path = kOptsFile;
	} else {
		ok = write_raw(path, text, err);
	}
	if (!ok) {
		static std::mutex            lock;
		static std::set<std::string> told;
		std::lock_guard<std::mutex>  g(lock);
		if (told.insert(path).second) {
			log("write failed: %s (errno %d%s)", path, err, err == ENOSPC ? ": /system_tmp is full" : "");
		}
	}
	return ok;
}

std::string read_text(const char* path, size_t max = 4096) {
	const int fd = open(path, O_RDONLY);
	if (fd < 0) {
		return {};
	}
	std::string text(max, '\0');
	const ssize_t n = read(fd, &text[0], max);
	close(fd);
	text.resize(n > 0 ? static_cast<size_t>(n) : 0);
	return text;
}

std::string first_line(const std::string& text) {
	return text.substr(0, text.find_first_of("\r\n"));
}

bool exists(const char* path) {
	struct stat st {};
	return stat(path, &st) == 0;
}

void send_notification(const char* text, bool icon) {
	// Layout of the system's notification request (0xC30 bytes).
	struct Request {
		int32_t type, req_id, priority, msg_id, target_id, user_id, unk1, unk2, app_id, error_num, unk3;
		char    use_icon_image_uri;
		char    message[1024];
		char    uri[1024];
		char    unused[1027];
	};
	static_assert(sizeof(Request) == 0xC30, "notification request layout");
	Request req {};
	req.target_id = -1;
	snprintf(req.message, sizeof(req.message), "%s", text);
	if (icon) {
		req.use_icon_image_uri = 1;
		snprintf(req.uri, sizeof(req.uri), "%s", "cxml://psnotification/tex_icon_system");
	}
	sceKernelSendNotificationRequest(0, &req, sizeof(req), 0);
	log("notify: %s", text);
}

// ---- OnionHEN guard + markers ----------------------------------------------------------------

bool onion_daemon_answers() {
	const int s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0) {
		return false;
	}
	sockaddr_in addr = {};
	addr.sin_family      = AF_INET;
	addr.sin_port        = htons(kOnionCtrlPort);
	addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	const bool up = connect(s, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) == 0;
	close(s);
	return up;
}

long read_pid_file(const char* path) {
	const std::string text = read_text(path, 31);
	return text.empty() ? -1 : strtol(text.c_str(), nullptr, 10);
}

// ---- clips + mounting ------------------------------------------------------------------------

bool is_mp4(const char* name) {
	const size_t n = strlen(name);
	return n > 4 && name[0] != '.' && strcasecmp(name + n - 4, ".mp4") == 0;
}

std::string folder_of(const std::string& path) {
	return path.substr(0, path.rfind('/'));
}

std::string name_of(const std::string& path) {
	return path.substr(path.rfind('/') + 1);
}

bool mount_window_at(const char* mount_point, const char* source) {
	mkdir(mount_point, 0777);
	(void)unmount(mount_point, MNT_FORCE);
	char fstype[] = "nullfs", fspath_key[] = "fspath", target_key[] = "target", fstype_key[] = "fstype";
	char fspath[256], target[256];
	snprintf(fspath, sizeof(fspath), "%s", mount_point);
	snprintf(target, sizeof(target), "%s", source);
	iovec iov[] = {
	    {fstype_key, sizeof(fstype_key)}, {fstype, sizeof(fstype)},
	    {fspath_key, sizeof(fspath_key)}, {fspath, strlen(fspath) + 1},
	    {target_key, sizeof(target_key)}, {target, strlen(target) + 1},
	};
	if (nmount(iov, sizeof(iov) / sizeof(iov[0]), MNT_RDONLY) != 0) {
		log("nullfs mount %s -> %s failed (errno %d)", source, mount_point, errno);
		return false;
	}
	return true;
}

// /system_ex/vsh_asset/wallpaper is NOT Sony's: on the dev console it was made once while OnionHEN had
// /system_ex writable, so every test found it. A normal PS5 has no such folder and /system_ex is
// read-only -> "nullfs mount ... failed (errno 2)" and no video (GitHub issue #2). Make it once the
// way OnionHEN's bootstrapper does: remount /system_ex writable in place (it stays so, as with
// OnionHEN, which relies on that), add only this one empty folder, never touch Sony's files.
bool remount_system_ex_writable() {
	char k_fstype[] = "fstype", v_fstype[] = "exfatfs", k_fspath[] = "fspath", v_fspath[] = "/system_ex";
	char k_from[] = "from", v_from[] = "/dev/ssd0.system_ex", k_large[] = "large", v_yes[] = "yes";
	char k_tz[] = "timezone", v_tz[] = "static", k_async[] = "async", k_acl[] = "ignoreacl";
	iovec iov[] = {
	    {k_fstype, sizeof(k_fstype)}, {v_fstype, sizeof(v_fstype)}, {k_fspath, sizeof(k_fspath)},
	    {v_fspath, sizeof(v_fspath)}, {k_from, sizeof(k_from)},     {v_from, sizeof(v_from)},
	    {k_large, sizeof(k_large)},   {v_yes, sizeof(v_yes)},       {k_tz, sizeof(k_tz)},
	    {v_tz, sizeof(v_tz)},         {k_async, sizeof(k_async)},   {nullptr, 0},
	    {k_acl, sizeof(k_acl)},       {nullptr, 0},
	};
	return nmount(iov, sizeof(iov) / sizeof(iov[0]), MNT_UPDATE) == 0;
}

bool ensure_mount_point() {
	struct stat st {};
	if (stat(kMountPoint, &st) == 0 && S_ISDIR(st.st_mode)) {
		return true;
	}
	if (mkdir(kMountPoint, 0777) == 0) {
		log("made %s", kMountPoint);
		return true;
	}
	const int first = errno;
	if (!remount_system_ex_writable()) {
		log("cannot make %s (errno %d): /system_ex remount failed (errno %d)", kMountPoint, first, errno);
		return false;
	}
	if (mkdir(kMountPoint, 0777) != 0 && errno != EEXIST) {
		log("cannot make %s after remounting /system_ex (errno %d)", kMountPoint, errno);
		return false;
	}
	log("made %s (/system_ex remounted writable, as OnionHEN does)", kMountPoint);
	return true;
}

// System processes each see their own sandbox view (/mnt/sandbox/<id>/...): a mount on the real
// /system_ex does not show there, so the window is opened in every sandbox too.
void mount_window_everywhere(const std::string& folder) {
	if (!ensure_mount_point()) {
		notify("LiveShell Engine could not prepare its video folder. Log: /data/LiveShell/liveshell.log");
		return;
	}
	if (!mount_window_at(kMountPoint, folder.c_str())) {
		return;
	}
	int  mounted = 0, tried = 0;
	DIR* dir     = opendir("/mnt/sandbox");
	if (dir != nullptr) {
		while (dirent* e = readdir(dir)) {
			if (e->d_name[0] == '.') {
				continue;
			}
			char point[512];
			snprintf(point, sizeof(point), "/mnt/sandbox/%s/system_ex/vsh_asset/wallpaper", e->d_name);
			struct stat st {};
			if (stat(point, &st) != 0 || !S_ISDIR(st.st_mode)) {
				continue;
			}
			++tried;
			mounted += mount_window_at(point, folder.c_str()) ? 1 : 0;
		}
		closedir(dir);
	}
	g_mounted_folder = folder;
	log("%s mounted on %s (+ %d of %d sandboxes)", folder.c_str(), kMountPoint, mounted, tried);
}

void unmount_window_everywhere() {
	int  done = 0;
	DIR* dir  = opendir("/mnt/sandbox");
	if (dir != nullptr) {
		while (dirent* e = readdir(dir)) {
			if (e->d_name[0] == '.') {
				continue;
			}
			char point[512];
			snprintf(point, sizeof(point), "/mnt/sandbox/%s/system_ex/vsh_asset/wallpaper", e->d_name);
			done += unmount(point, MNT_FORCE) == 0 ? 1 : 0;
		}
		closedir(dir);
	}
	const int main_rc = unmount(kMountPoint, MNT_FORCE);
	g_mounted_folder.clear();
	log("window closed (%s, %d sandboxes)", main_rc == 0 ? "main ok" : "main not mounted", done);
}

// Like OnionHEN's shutdown: end SceShellUI so the system starts a clean one (no module, no video).
void restart_shellui() {
	const pid_t pid = onion_find_pid("SceShellUI");
	if (pid <= 1) {
		log("restart: SceShellUI not found");
		return;
	}
	constexpr uintptr_t kDecidAuthId = 0x4800000000000022ULL; // needed for sceKernelTerminateProcess
	const uintptr_t     old          = set_proc_authid(getpid(), kDecidAuthId);
	int                 ret          = 0;
	const int           rc           = sceKernelTerminateProcess(static_cast<int>(pid), &ret);
	set_proc_authid(getpid(), old);
	if (rc != 0) {
		log("restart: TerminateProcess(%d) rc %d ret %d, SIGKILL instead", static_cast<int>(pid), rc, ret);
		kill(pid, SIGKILL);
	}
	log("restart: SceShellUI %d ended, the system starts a new one", static_cast<int>(pid));
}

// ---- config ----------------------------------------------------------------------------------

std::string looks_text() {
	return std::to_string(g_looks[0]) + " " + std::to_string(g_looks[1]) + " " + std::to_string(g_looks[2]) + " " + std::to_string(g_looks[3]);
}

void write_looks() {
	write_text(kLooksFile, looks_text() + "\n");
}

void load_config() {
	const std::string text = read_text(kConfigFile);
	size_t            pos  = 0;
	while (pos < text.size()) {
		const size_t      end  = text.find('\n', pos);
		const std::string line = first_line(text.substr(pos, end == std::string::npos ? std::string::npos : end - pos));
		if (line.rfind("enabled=", 0) == 0) {
			g_enabled = line.substr(8) != "0";
		} else if (line.rfind("video=", 0) == 0) {
			g_current = line.substr(6);
		} else if (line.rfind("dim=", 0) == 0) {
			g_dim = std::max(0, std::min(80, atoi(line.c_str() + 4)));
		} else if (line.rfind("volume=", 0) == 0) {
			g_volume = std::max(0, std::min(100, atoi(line.c_str() + 7)));
		} else if (line.rfind("looks=", 0) == 0) {
			sscanf(line.c_str() + 6, "%d %d %d %d", &g_looks[0], &g_looks[1], &g_looks[2], &g_looks[3]);
			for (int& v : g_looks) {
				v = std::max(0, std::min(2, v));
			}
			g_looks[0] = g_looks[1] = 0; // bottom / top fade were removed (user)
		} else if (line.rfind("gamevideos=", 0) == 0) {
			g_game_videos = line.substr(11) != "0";
		} else if (line.rfind("mainvideo=", 0) == 0) {
			// ignored: an old "Main video" switch (removed in v1.2) - its own key below since v1.4
		} else if (line.rfind("pergameonly=", 0) == 0) {
			g_main_video = line.substr(12) == "0"; // 1 = "Videos per game only" (v1.4: hides, no stop/start)
		} else if (line.rfind("shuffle=", 0) == 0) {
			g_shuffle = line.substr(8) != "0";
		} else if (line.rfind("parallax=", 0) == 0) {
			g_parallax = line.substr(9) != "0";
		} else if (line.rfind("gamehide=", 0) == 0) {
			g_game_hide = line.substr(9) != "0";
		} else if (line.rfind("offusers=", 0) == 0) {
			g_off_users = line.substr(9);
		} else if (line.rfind("tint=", 0) == 0) {
			g_tint = std::max(0, std::min(5, atoi(line.c_str() + 5)));
		} else if (line.rfind("launchfx=", 0) == 0) {
			g_launchfx = std::max(0, std::min(2, atoi(line.c_str() + 9)));
		} else if (line.rfind("autonext=", 0) == 0) {
			g_autonext = std::max(0, std::min(2, atoi(line.c_str() + 9)));
		} else if (line.rfind("resume=", 0) == 0) {
			g_resume = line.substr(7) == "1";
		} else if (line.rfind("automatch=", 0) == 0) {
			g_auto_match = false; // Auto-match: no switch since v1.7.0, parked for a later release (user) - off even if it was on
		} else if (line.rfind("menuhide=", 0) == 0) {
			g_menu_hide = line.substr(9) != "0";
		} else if (line.rfind("storeonly=", 0) == 0) {
			g_store_only = line.substr(10) != "0";
		} else if (line.rfind("gamepause=", 0) == 0) {
			g_game_pause = true; // always on: games get the video decoder; an old "0" is ignored
		}
		if (end == std::string::npos) {
			break;
		}
		pos = end + 1;
	}
	log("config: enabled=%d video=%s dim=%d shuffle=%d gamepause=%d", g_enabled ? 1 : 0, g_current.c_str(), g_dim,
	    g_shuffle ? 1 : 0, g_game_pause ? 1 : 0);
	write_text(kDimFile, std::to_string(g_dim) + "\n");
	write_text(kVolumeFile, std::to_string(g_volume) + "\n");
	write_text(kMenusFile, g_menu_hide ? "1\n" : "0\n");
	write_text(kStoreOnlyFile, g_store_only ? "1\n" : "0\n");
	write_looks();
	write_text(kParallaxFile, g_parallax ? "1\n" : "0\n");
	write_text("/system_tmp/liveshell/resume.txt", g_resume ? "1\n" : "0\n");
	write_text("/system_tmp/liveshell/launchfx.txt", std::to_string(g_launchfx) + "\n");
	write_text("/system_tmp/liveshell/tint.txt", std::to_string(g_tint) + "\n");
}

void save_config() {
	write_text(kConfigFile, std::string("enabled=") + (g_enabled ? "1" : "0") + "\nvideo=" + g_current + "\ndim=" + std::to_string(g_dim) + "\nvolume=" + std::to_string(g_volume) + "\nlooks=" + looks_text() +
	                            "\nshuffle=" + (g_shuffle ? "1" : "0") + "\nmainvideo=1\npergameonly=" + (g_main_video ? "0" : "1") + "\ngamevideos=" + (g_game_videos ? "1" : "0") + "\ngamepause=" + (g_game_pause ? "1" : "0") + "\nmenuhide=" + (g_menu_hide ? "1" : "0") + "\nstoreonly=" + (g_store_only ? "1" : "0") + "\nparallax=" + (g_parallax ? "1" : "0") + "\nautomatch=" + (g_auto_match ? "1" : "0") + "\nresume=" + (g_resume ? "1" : "0") + "\nlaunchfx=" + std::to_string(g_launchfx) + "\nautonext=" + std::to_string(g_autonext) + "\ntint=" + std::to_string(g_tint) + "\noffusers=" + g_off_users + "\ngamehide=" + (g_game_hide ? "1" : "0") + "\n");
}

// ---- telling ShellUI what to play ------------------------------------------------------------

// ---- messages from our ShellUI module (UDP 127.0.0.1:9051) ------------------------------------
// ShellUI may only write ~16 KB of files per run (test v11-8: status.txt vanished, every switch took
// the slow path), so it sends "S<status>", "F<title id>", "L<log line>" here instead.
constexpr int         kUiPort    = 9051;
constexpr const char* kUiLogFile = "/data/LiveShell/shellui.log";
std::mutex            g_ui_lock;
std::string           g_ui_status, g_ui_focus;
bool                  g_ui_status_set = false, g_ui_focus_set = false;
std::atomic<long>     g_ui_bytes{0}; // everything received: ShellUI is alive when this grows

void ui_forget_status() {
	std::lock_guard<std::mutex> lock(g_ui_lock);
	g_ui_status_set = false;
	g_ui_status.clear();
}

void ui_set_focus(const std::string& tid) {
	std::lock_guard<std::mutex> lock(g_ui_lock);
	g_ui_focus     = tid;
	g_ui_focus_set = true;
}

std::string shellui_status() {
	{
		std::lock_guard<std::mutex> lock(g_ui_lock);
		if (g_ui_status_set) {
			return g_ui_status;
		}
	}
	return first_line(read_text(kStatusFile, 700));
}

std::string shellui_focus() {
	{
		std::lock_guard<std::mutex> lock(g_ui_lock);
		if (g_ui_focus_set) {
			return g_ui_focus;
		}
	}
	return first_line(read_text("/system_tmp/liveshell/focus_game.txt", 64));
}

int open_ui_port() {
	const int   s = socket(AF_INET, SOCK_DGRAM, 0);
	sockaddr_in a {};
	a.sin_family      = AF_INET;
	a.sin_port        = htons(kUiPort);
	a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (s < 0 || bind(s, reinterpret_cast<sockaddr*>(&a), sizeof(a)) != 0) {
		log("ui channel: bind failed (errno %d), ShellUI falls back to files", errno);
		if (s >= 0) {
			close(s);
		}
		return -1;
	}
	timeval tv {1, 0}; // recv wakes up every second: rest mode / reopen checks
	setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
	return s;
}

#ifdef LIVESHELL_RESEARCH_DUMP
// RESEARCH BUILD ONLY: the ShellUI module's assembly images (UDP 9052: 64-byte name, offset, total, data)
// -> /data/LiveShell/dump/<name>.dll; "<name>: complete" in the log once every byte came.
void* dump_rx_thread(void*) {
	mkdir("/data/LiveShell/dump", 0777);
	const int   s = socket(AF_INET, SOCK_DGRAM, 0);
	sockaddr_in a {};
	a.sin_family      = AF_INET;
	a.sin_port        = htons(9052);
	a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	int big = 16 << 20;
	setsockopt(s, SOL_SOCKET, SO_RCVBUF, &big, sizeof(big));
	if (s < 0 || bind(s, reinterpret_cast<sockaddr*>(&a), sizeof(a)) != 0) {
		log("dump: bind 9052 failed (errno %d)", errno);
		return nullptr;
	}
	static char             buf[72 + 8192];
	std::map<std::string, uint64_t> got;
	while (g_running) {
		const ssize_t n = recv(s, buf, sizeof(buf), 0);
		if (n <= 72) {
			continue;
		}
		char name[65] = {};
		memcpy(name, buf, 64);
		for (char* c = name; *c; ++c) {
			if (*c == '/' || *c == '\\') {
				*c = '_';
			}
		}
		uint32_t off = 0, total = 0;
		memcpy(&off, buf + 64, 4);
		memcpy(&total, buf + 68, 4);
		const std::string path = std::string("/data/LiveShell/dump/") + name + ".dll";
		const int         fd   = open(path.c_str(), O_WRONLY | O_CREAT, 0666);
		if (fd < 0) {
			continue;
		}
		(void)pwrite(fd, buf + 72, static_cast<size_t>(n - 72), off);
		close(fd);
		uint64_t& g = got[name];
		const uint64_t before = g;
		g += static_cast<uint64_t>(n - 72);
		if (before < total && g >= total) {
			log("dump: %s complete (%u bytes)", name, total);
		}
	}
	return nullptr;
}
#endif

void* ui_thread(void*) {
	int       s  = -1, fails = 0, epoch = net_epoch(); // reopened after rest mode (see power_thread)
	const int lf = open(kUiLogFile, O_WRONLY | O_CREAT | O_TRUNC, 0666);
	char      buf[1600];
	while (g_running) {
		if (s >= 0 && epoch != net_epoch()) {
			log("ui channel: reopening after rest mode");
			close(s);
			s = -1;
		}
		if (s < 0) {
			epoch = net_epoch();
			s     = open_ui_port();
			if (s < 0) {
				sleep(2);
				continue;
			}
			fails = 0;
		}
		const ssize_t n = recv(s, buf, sizeof(buf) - 1, 0);
		if (n < 0) {
			if (errno == EAGAIN || errno == EWOULDBLOCK) {
				continue; // the 1 s timeout
			}
			if (++fails >= 40) {
				log("ui channel broken (errno %d), reopening", errno);
				close(s);
				s = -1;
			}
			usleep(50 * 1000);
			continue;
		}
		fails = 0;
		if (n == 0) {
			continue;
		}
		g_ui_bytes += n;
		if (buf[0] == 'E') { // the main clip is about to end (Next video when one ends)
			std::lock_guard<std::mutex> lock(g_ui_lock);
			g_ended_clip.assign(buf + 1, static_cast<size_t>(n - 1));
			g_ended = true;
		} else if (buf[0] == 'S' || buf[0] == 'F') {
			std::lock_guard<std::mutex> lock(g_ui_lock);
			(buf[0] == 'S' ? g_ui_status : g_ui_focus).assign(buf + 1, static_cast<size_t>(n - 1));
			(buf[0] == 'S' ? g_ui_status_set : g_ui_focus_set) = true;
		} else if (buf[0] == 'L' && lf >= 0) {
			struct stat st {};
			if (fstat(lf, &st) == 0 && st.st_size > 2 * 1024 * 1024) {
				(void)ftruncate(lf, 0);
				(void)lseek(lf, 0, SEEK_SET);
			}
			(void)write(lf, buf + 1, static_cast<size_t>(n - 1));
		}
	}
	return nullptr;
}

// Wait until ShellUI no longer holds a clip (so its folder can be unmounted safely).
bool wait_shellui_stopped(int timeout_ms) {
	for (int waited = 0; waited < timeout_ms; waited += 100) {
		const std::string st = shellui_status();
		if (st.rfind("playing", 0) != 0 && st.rfind("starting", 0) != 0 && st.rfind("stopping", 0) != 0) {
			return true;
		}
		usleep(100 * 1000);
	}
	return false;
}

// The folder we mount for a clip: the whole video tree (internal video folder, or the USB liveshell
// folder), so clips in game subfolders (video/PPSA01234/) share one mount and can cross-fade.
std::string mount_base(const std::string& clip) {
	const std::string internal = "/data/LiveShell/video";
	if (clip.rfind(internal + "/", 0) == 0) {
		return internal;
	}
	if (clip.rfind("/mnt/usb", 0) == 0) {
		const size_t a = clip.find('/', 5);               // after "/mnt/"
		const size_t b = a == std::string::npos ? a : clip.find('/', a + 1); // end of the liveshell folder
		if (b != std::string::npos) {
			return clip.substr(0, b);
		}
	}
	return folder_of(clip);
}

std::string shown_path(const std::string& clip) {
	return std::string(kMountPoint) + clip.substr(mount_base(clip).size());
}

// write_fast_map(): below, with games.txt (declared in liveshell.hpp)

bool apply_inner(std::string& error);

// PS Store only works on its own, like the main video: ONE clip plays (hidden on other tiles), so
// nothing ever swaps. It is the clip chosen for the Store (games.txt NPXS40047), else the main one.
// (The first try kept the main clip and swapped on the Store tile: its first frame showed, user.)
std::string store_clip() {
	const std::string c = saved_game_clip("NPXS40047");
	return !c.empty() && exists(c.c_str()) ? c : g_current; // 4K too: one clip, never swapped (like the main one)
}

// Caller holds g_ctl. Every change also refreshes ShellUI's fast-switch map.
// The wallpaper plays: switched on, and the signed-in user is not switched off (Settings -> Users). Caller holds g_ctl.
bool on_now() {
	return g_enabled && !g_user_off;
}

bool apply_locked(std::string& error) {
	write_fast_map(); // first: a changed setting reaches the tiles at once (apply_inner can wait ~8 s for a busy home screen)
	const bool ok = apply_inner(error);
	write_fast_map(); // again: apply_inner may have changed what is mounted
	return ok;
}

bool apply_inner(std::string& error) {
	// The tile's own clip wins; otherwise the main one, unless "Main video" is off (then nothing).
	const std::string clip = g_store_only ? store_clip()
	                         : !g_override.empty() ? g_override : (g_main_video ? g_current : std::string());
	// Videos per game only, a tile without a video: ShellUI hides the running one (fast.txt "*=hide"); stopping it
	// here was what made the old "Main video off" flash on every tile move.
	if (!g_store_only && !g_main_video && g_override.empty() && on_now()) {
		return true;
	}
	// Same folder while a clip plays: quick swap in ShellUI (fade to black, swap, fade in), no
	// release wait: the folder stays mounted (the full stop took ~4 s per switch, test v11-4).
	if (g_injected && on_now() && !(g_game_pause && g_game_running) && !(g_game_hide && g_game_open) &&
	    !clip.empty() && exists(clip.c_str()) &&
	    mount_base(clip) == g_mounted_folder &&
	    (shellui_status().rfind("playing", 0) == 0 || shellui_status().rfind("starting", 0) == 0)) {
		// "starting" too: ShellUI's own fast switch may be mid-swap (test v11-9: that moment sent us
		// down the slow path, ~2.5 s of black).
		const std::string shown = shown_path(clip);
		write_text(kPathFile, "switch:" + shown + "\n");
		log("apply: quick swap to %s", clip.c_str());
		return true;
	}
	const bool want_video = on_now() && !(g_game_pause && g_game_running) && !(g_game_hide && g_game_open) &&
	                        !clip.empty() && exists(clip.c_str());
	if (want_video && g_injected && mount_base(clip) == g_mounted_folder) {
		const std::string st = shellui_status();
		if (st.empty() || st.rfind("stopped", 0) == 0) {
			write_text(kPathFile, shown_path(clip) + "\n"); // nothing to release first
			log("apply: start %s (folder already mounted)", clip.c_str());
			return true;
		}
	}
	if (g_injected) {
		write_text(kPathFile, "off\n");
		if (!wait_shellui_stopped(8000)) {
			error = "The home screen did not release the old video";
			log("apply: ShellUI still busy (%s)", shellui_status().c_str());
			return false;
		}
	}
	if (!want_video) {
		write_text(kPathFile, "off\n");
		log("apply: video off");
		return true;
	}
	const std::string folder = mount_base(clip);
	if (folder != g_mounted_folder || !g_injected) {
		mount_window_everywhere(folder); // also refreshes the sandboxes before a (re)injection
	}
	const std::string shown = shown_path(clip);
	write_text(kPathFile, shown + "\n");
	log("apply: %s (shown as %s)", clip.c_str(), shown.c_str());
	return true;
}

// ---- injection -------------------------------------------------------------------------------

off_t file_size(const char* path) {
	struct stat st {};
	return stat(path, &st) == 0 ? st.st_size : -1;
}

// The injector stops ShellUI (ptrace), runs a stager up to a breakpoint and detaches. If that
// detach does not take, the whole ShellUI stays stopped (our module's heartbeat log freezes after
// ~2 ms) until the system kills it. Detect that and let it run again.
void unfreeze_if_stuck(pid_t pid) {
	usleep(400 * 1000);
	const off_t first = file_size(kShellUiLog) + g_ui_bytes;
	usleep(2600 * 1000); // the module waits 1.5 s, then logs ~4 lines/s
	const off_t second = file_size(kShellUiLog) + g_ui_bytes;
	if (second > first) {
		log("ShellUI is running (log %ld -> %ld bytes)", static_cast<long>(first), static_cast<long>(second));
		return;
	}
	log("ShellUI looks FROZEN after injection (log stuck at %ld bytes): detaching again + SIGCONT",
	    static_cast<long>(second));
	const uintptr_t old_authid = set_ucred_to_ptrace();
	const int       det        = pt_detach(pid, 0);
	const int       det_errno  = errno;
	const int       cont       = kill(pid, SIGCONT);
	if (old_authid != 0) {
		set_proc_authid(getpid(), old_authid);
	}
	usleep(1000 * 1000);
	const off_t third = file_size(kShellUiLog) + g_ui_bytes;
	log("unfreeze: detach %d (errno %d), SIGCONT %d, log now %ld bytes (%s)", det, det_errno, cont,
	    static_cast<long>(third), third > second ? "RUNNING again" : "still stuck");
}

// A just-started ShellUI is patched by kstuff once its trophy libraries are mapped; OnionHEN waits for
// the same libraries before injecting. We injected at once: right after a ShellUI restart that froze
// ShellUI every time (v1.1-rc3, "FROZEN after injection", then the crash guard). Wait the same way.
void wait_shellui_ready(pid_t pid) {
	bool waited = false;
	for (const char* name : {"libSceNpTrophy.sprx", "libSceNpTrophy2.sprx"}) {
		int i = 0;
		for (; i < 60; ++i) { // max 30 s each, like kstuff
			uint32_t handle = 0xffffffffu;
			if (kernel_dynlib_handle(pid, name, &handle) == 0 && handle != 0xffffffffu) {
				break;
			}
			if (kill(pid, 0) != 0) {
				return; // gone; the caller notices
			}
			waited = true;
			usleep(500 * 1000);
		}
		if (i == 60) {
			log("ShellUI %d: %s still not loaded after 30 s, injecting anyway", static_cast<int>(pid), name);
		} else if (i > 0) {
			log("ShellUI %d: %s loaded after %d ms", static_cast<int>(pid), name, i * 500);
		}
	}
	if (waited) {
		sleep(3); // a fresh ShellUI: let kstuff finish with it
	}
}

pid_t inject_shellui() {
	const pid_t pid = onion_find_pid("SceShellUI");
	if (pid <= 0) {
		log("SceShellUI not found");
		return 0;
	}
	if (kOnionGuard && (onion_daemon_answers() || read_pid_file(kOnionToolbox) == pid)) {
		notify("LiveShell Engine can't run while OnionHEN is running.");
		return -1;
	}
	if (read_pid_file(kOurMarker) == pid) {
		log("already injected in ShellUI pid %d", static_cast<int>(pid));
		return pid;
	}
	wait_shellui_ready(pid);
	unlink(kStatusFile);
	ui_forget_status();
	log("injecting into SceShellUI pid %d", static_cast<int>(pid));
	if (!Inject_Toolbox(static_cast<int>(pid), liveshell_shellui_elf_start)) {
		log("injection FAILED");
		notify("LiveShell Engine could not start (injection failed).");
		return -1;
	}
	write_text(kOurMarker, std::to_string(pid));
	log("injected into ShellUI pid %d", static_cast<int>(pid));
	unfreeze_if_stuck(pid);
	return pid;
}

void copy_shellui_log() {
	std::string text = read_text(kUiLogFile, 2 * 1024 * 1024);
	if (text.size() > 64 * 1024) {
		text.erase(0, text.size() - 64 * 1024); // the end matters
	}
	if (text.empty()) {
		text = read_text(kShellUiLog, 64 * 1024);
	}
	if (text.empty()) {
		return;
	}
	std::lock_guard<std::mutex> lock(g_log_lock);
	const char* head = "--- ShellUI log ---\n";
	(void)write(g_log, head, strlen(head));
	(void)write(g_log, text.data(), text.size());
}

// ---- stop port (tools/stop_liveshell.bat) ----------------------------------------------------

// ---- rest mode -------------------------------------------------------------------------------
// The system's power state (event flag "SceSystemStateMgrInfo", low 16 bits: 1000 working, 500 rest,
// 300 going to rest), read the way OnionHEN does. Waking up: wait 1 s for the network, then every
// listener reopens (net_epoch) - sockets from before rest are dead (user report: dead after waking).
std::atomic<int>    g_net_epoch{0};
std::atomic<bool>   g_sleeping{false}; // the PS5 is in (or going to) rest mode
std::atomic<time_t> g_rest_seen{0};    // last time rest mode started or ended

// Wake our own listeners: a blocked accept()/recv() returns and sees the new epoch (the window took
// ~2 min to reopen after waking: accept's timeout did not fire, test v1.1-rc).
void poke_ports() {
	for (const int port : {kWebPort, kStopPort}) {
		const int   s = socket(AF_INET, SOCK_STREAM, 0);
		sockaddr_in a {};
		a.sin_family      = AF_INET;
		a.sin_port        = htons(static_cast<uint16_t>(port));
		a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
		if (s >= 0) {
			if (connect(s, reinterpret_cast<sockaddr*>(&a), sizeof(a)) == 0) {
				const char* poke = "poke\n";
				(void)write(s, poke, strlen(poke));
			}
			close(s);
		}
	}
	const int   u = socket(AF_INET, SOCK_DGRAM, 0);
	sockaddr_in a {};
	a.sin_family      = AF_INET;
	a.sin_port        = htons(kUiPort);
	a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (u >= 0) {
		(void)sendto(u, "P", 1, 0, reinterpret_cast<sockaddr*>(&a), sizeof(a));
		close(u);
	}
}

void* power_thread(void*) {
	intptr_t flag     = -1;
	bool     sleeping = false;
	while (g_running) {
		usleep(200 * 1000);
		if (flag < 0 && sceKernelOpenEventFlag(&flag, "SceSystemStateMgrInfo") < 0) {
			flag = -1;
			sleep(5);
			continue;
		}
		uint64_t bits = 0;
		if (sceKernelPollEventFlag(flag, UINT64_MAX, 2 /* OR */, &bits) < 0) {
			sceKernelCloseEventFlag(flag);
			flag = -1;
			continue;
		}
		const unsigned state = static_cast<unsigned>(bits & 0xffff);
		// Every change, to the ms (rest / wake problems: which codes, when).
		static unsigned last_state = 0;
		if (state != last_state) {
			timespec ts {};
			clock_gettime(CLOCK_MONOTONIC, &ts);
			log("power state %u -> %u (t=%ld.%03ld s)", last_state, state, static_cast<long>(ts.tv_sec), ts.tv_nsec / 1000000);
			last_state = state;
		}
		if (state == 500 || state == 300) {
			if (!sleeping) {
				log("rest: going to rest mode (%u)", state);
				// Rest mode ends ShellUI: not a crash. Without this the crash guard of a video started < 20 s
				// before stayed, and after waking the video did not start ("last attempt did not survive").
				unlink("/system_tmp/liveshell/video_trying");
				g_rest_seen = time(nullptr);
			}
			sleeping   = true;
			g_sleeping = true;
		} else if (state == 1000 && sleeping) {
			sleeping    = false;
			g_rest_seen = time(nullptr);
			log("rest: awake again, reopening ports in 1 s");
			sleep(1);
			++g_net_epoch;
			poke_ports();
			g_sleeping = false; // the re-inject loop may go on now
		}
	}
	return nullptr;
}

int open_stop_port() {
	const int s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0) {
		return -1;
	}
	int on = 1;
	setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));
	sockaddr_in addr = {};
	addr.sin_family      = AF_INET;
	addr.sin_port        = htons(kStopPort);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);
	if (bind(s, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) != 0 || listen(s, 1) != 0) {
		log("stop port %d unavailable (errno %d)", kStopPort, errno);
		close(s);
		return -1;
	}
	timeval tv {1, 0}; // accept wakes up every second: rest mode / reopen checks
	setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
	return s;
}

// Loading the ELF while LiveShell already runs: ask the running one to leave (handover above), so
// this one gets the ports (they were "unavailable", and the status went to the old one, test v11-24).
// This build, so a handover can tell old from new ("handover <build>").
constexpr const char* kBuild = __DATE__ " " __TIME__;

bool take_over_running() {
	auto connect_stop = []() -> int {
		const int   s = socket(AF_INET, SOCK_STREAM, 0);
		sockaddr_in a {};
		a.sin_family      = AF_INET;
		a.sin_port        = htons(kStopPort);
		a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
		if (s >= 0 && connect(s, reinterpret_cast<sockaddr*>(&a), sizeof(a)) == 0) {
			return s;
		}
		if (s >= 0) {
			close(s);
		}
		return -1;
	};
	const int s = connect_stop();
	if (s < 0) {
		return false; // nothing running
	}
	const std::string hello = std::string("handover ") + kBuild + "\n";
	(void)write(s, hello.data(), hello.size());
	char          reply[16] = {};
	timeval       tv {2, 0};
	setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
	const ssize_t got = recv(s, reply, sizeof(reply) - 1, 0);
	close(s);
	if (got < 8 || memcmp(reply, "handover", 8) != 0) {
		log("handover: the running LiveShell is another build: it stops normally (ShellUI restarts)");
	}
	for (int i = 0; i < 150; ++i) { // until its ports are free (max 15 s: a normal stop restarts ShellUI)
		const int t = connect_stop();
		if (t < 0) {
			return true;
		}
		close(t);
		usleep(100 * 1000);
	}
	return true;
}

void* stop_thread(void*) {
	int s = -1, fails = 0, epoch = net_epoch(); // reopened after rest mode (see power_thread)
	while (g_running) {
		if (s >= 0 && epoch != net_epoch()) {
			log("stop port: reopening after rest mode");
			close(s);
			s = -1;
		}
		if (s < 0) {
			epoch = net_epoch();
			s     = open_stop_port();
			if (s < 0) {
				sleep(2);
				continue;
			}
			fails = 0;
		}
		const int c = accept(s, nullptr, nullptr);
		if (c < 0) {
			if (errno == EAGAIN || errno == EWOULDBLOCK) {
				continue; // the 1 s timeout
			}
			if (++fails >= 30) {
				log("stop port broken (errno %d), reopening", errno);
				close(s);
				s = -1;
			}
			usleep(100 * 1000);
			continue;
		}
		fails = 0;
		// A new LiveShell sends "handover": leave quietly (no ShellUI restart, mounts stay) so it can
		// take the ports. The stop tools send nothing -> after 0.3 s it is a normal stop.
		timeval rt {0, 300 * 1000};
		setsockopt(c, SOL_SOCKET, SO_RCVTIMEO, &rt, sizeof(rt));
		char          hello[48] = {};
		const ssize_t got       = recv(c, hello, sizeof(hello) - 1, 0);
		// Only the same build leaves quietly: ShellUI keeps the module the old one injected, so a
		// different build stops normally (ShellUI restarts, the new one injects its own module).
		if (got >= 4 && memcmp(hello, "poke", 4) == 0) {
			close(c); // our own wake-up nudge (poke_ports)
			continue;
		}
		if (got >= 8 && memcmp(hello, "handover", 8) == 0 && strstr(hello, kBuild) != nullptr) {
			const char* ok = "handover\n";
			(void)write(c, ok, strlen(ok));
			close(c);
			log("handover: a new LiveShell takes over, leaving");
			_exit(0);
		}
		if (c >= 0) {
			const char* msg = "stopping\n";
			(void)write(c, msg, strlen(msg));
			close(c);
			g_stop_requested = true;
			g_running        = false;
			g_replaced       = got >= 8 && memcmp(hello, "handover", 8) == 0; // another build replaces us
			log(g_replaced ? "stop: a newer LiveShell (another build) replaces this one" : "stop command received");
		}
	}
	close(s);
	return nullptr;
}

// A HEN's toolbox (etaHEN / OnionHEN) must be in the home screen before LiveShell hooks it (etaHEN checks that the
// functions are untouched; both clashed with a LiveShell injecting at the same moment). After rest mode, and at
// the first start too (Payload Manager autoload: LiveShell right after the HEN, issue #16). first: a toolbox that
// is already in the home screen means no wait at all.
void wait_for_hen_toolboxes(bool first) {
	// etaHEN running: its toolbox checks that the home screen's functions are untouched before it hooks
	// them. After rest mode LiveShell was back first, the check failed ("Failed to load the etaHEN
	// toolbox") and the home screen crashed. Wait until its toolbox is in the new one (its pid file
	// /system_tmp/etahen-<fw>-toolbox.pid shows it), max 45 s, then 5 s - as at boot, where etaHEN is first.
	// etaHEN runs = its service socket answers (the socket file stays after it exits).
	bool eta = false;
	{
		const int u = socket(AF_UNIX, SOCK_STREAM, 0);
		sockaddr_un a {};
		a.sun_family = AF_UNIX;
		snprintf(a.sun_path, sizeof(a.sun_path), "%s", "/system_tmp/etaHEN_crit_service");
		eta = u >= 0 && connect(u, reinterpret_cast<sockaddr*>(&a), sizeof(a)) == 0;
		if (u >= 0) {
			close(u);
		}
	}
	if (eta) {
		const pid_t ui = onion_find_pid("SceShellUI");
		auto toolbox_in = [&]() {
			bool in = false;
			if (DIR* d = opendir("/system_tmp")) {
				while (dirent* e = readdir(d)) {
					const std::string n = e->d_name;
					if (n.rfind("etahen-", 0) == 0 && n.size() > 12 && n.compare(n.size() - 12, 12, "-toolbox.pid") == 0) {
						in = in || read_pid_file(("/system_tmp/" + n).c_str()) == ui;
					}
				}
				closedir(d);
			}
			return in;
		};
		if (!(first && toolbox_in())) {
			int w = 0;
			while (g_running && w < 90 && ui > 0 && !toolbox_in()) {
				usleep(500 * 1000);
				++w;
			}
			log("etaHEN: its toolbox %s in the home screen, injecting in 5 s", toolbox_in() ? "is online" : "did not come (45 s)");
			sleep(5);
		}
	}
	// OnionHEN / HyperHEN running: its toolbox goes into the new home screen too. Injecting while it is still
	// setting up there crashed the home screen once ("software system error" after waking, LiveShell
	// in 2 s after "Toolbox online"); with HyperHEN it ended in "hook failed" (issue #20: HyperHEN is
	// built on OnionHEN, same ready files, its own folder). Wait until its toolbox is online in this one
	// (max 45 s), then 5 s. Only when that HEN really runs: its ready file holds its pid and stays after it exits.
	struct Hen {
		const char* name;
		const char* daemon;
		const char* toolbox;
	};
	static const Hen hens[] = {
		{"OnionHEN", "/system_tmp/onionhen/ready/daemon", kOnionToolbox},
		{"HyperHEN", "/system_tmp/hyperhen/ready/daemon", "/system_tmp/hyperhen/ready/toolbox"},
	};
	for (const Hen& h : hens) {
		const long hen_pid = read_pid_file(h.daemon);
		if (hen_pid <= 0 || kill(static_cast<pid_t>(hen_pid), 0) != 0) {
			continue;
		}
		const pid_t ui = onion_find_pid("SceShellUI");
		if (first && ui > 0 && read_pid_file(h.toolbox) == ui) {
			continue;
		}
		int w = 0;
		while (g_running && w < 90 && ui > 0 && read_pid_file(h.toolbox) != ui) {
			usleep(500 * 1000);
			++w;
		}
		log("%s: its toolbox %s in the home screen, injecting in 5 s", h.name,
		    ui > 0 && read_pid_file(h.toolbox) == ui ? "is online" : "did not come (45 s)");
		sleep(5);
	}
}

// Self-recovery (issue #14): the payload wants a video (video.txt holds a path) but ShellUI keeps saying
// "stopped". What the user's off / on toggle did: "off", a moment, the path again. At most 3 in 5 minutes.
void* recovery_thread(void*) {
	int    stuck = 0;
	time_t tries[3] {};
	while (g_running) {
		sleep(2);
		std::string want = read_text(kPathFile, 1024);
		want             = want.substr(0, want.find('\n'));
		const bool wants = want.rfind("/", 0) == 0 || want.rfind("switch:/", 0) == 0;
		bool live;
		{
			std::lock_guard<std::mutex> lock(g_ctl);
			live = g_injected && !g_game_open; // a game open: 4K / Hide while a game is open start nothing on purpose
		}
		{
			// Only the home screen we are really in counts (after a restart the new one has no module yet).
			const pid_t ui = onion_find_pid("SceShellUI");
			live           = live && ui > 0 && read_pid_file(kOurMarker) == ui;
		}
		// An old LiveShell module (another build, parked by a soft stop next to OnionHEN) already holds the home
		// screen's hook: the new one could not start. Restart the home screen once and inject fresh.
		// Also: a module we reuse ("already injected") that never reports - one that failed before - is dead.
		static bool hook_fixed = false;
		static int  silent     = 0;
		silent = live && !g_sleeping && shellui_status().empty() ? silent + 1 : 0;
		if (!hook_fixed && (shellui_status().rfind("failed hook", 0) == 0 || silent >= 6)) { // 12 s: a working one reports every 2 s
			hook_fixed = true;
			// Never with OnionHEN running: restarting the home screen throws its toolbox out too (it came back
			// after rest mode, "toolbox restart", then a crash). There the hook has to work next to it.
			const long onion = read_pid_file("/system_tmp/onionhen/ready/daemon");
			if (onion > 0 && kill(static_cast<pid_t>(onion), 0) == 0) {
				log("the home screen's LiveShell module %s, OnionHEN runs: no home screen restart (it would take OnionHEN's toolbox down)",
				    silent >= 6 ? "never answers" : "could not hook");
				continue;
			}
			log("the home screen's LiveShell module %s: restarting the home screen once to start clean",
			    silent >= 6 ? "never answers" : "could not hook (an old module holds it)");
			g_planned_restart = true;
			restart_shellui();
			continue;
		}
		if (!live || g_sleeping || !wants || shellui_status().rfind("stopped", 0) != 0) {
			stuck = 0;
			continue;
		}
		if (++stuck < 4) { // 8 s
			continue;
		}
		stuck            = 0;
		const time_t now = time(nullptr);
		int          n   = 0;
		for (const time_t t : tries) {
			n += t != 0 && now - t < 300;
		}
		if (n >= 3) {
			continue; // it did not help: no loop
		}
		for (time_t& t : tries) {
			if (t == 0 || now - t >= 300) {
				t = now;
				break;
			}
		}
		const std::string path = want.rfind("switch:", 0) == 0 ? want.substr(7) : want;
		log("recovery: video.txt asks for %s but the home screen says stopped: off, then again", path.c_str());
		{
			std::lock_guard<std::mutex> lock(g_ctl);
			write_text(kPathFile, "off\n");
		}
		sleep(2);
		{
			std::lock_guard<std::mutex> lock(g_ctl);
			if (read_text(kPathFile, 1024).rfind("off", 0) == 0) { // nothing else asked meanwhile
				write_text(kPathFile, path + "\n");
			}
		}
	}
	return nullptr;
}

// After the first start: wait for the video to show, then add the tile (never in the video's way).
void* after_start_thread(void*) {
	bool want_video;
	{
		std::lock_guard<std::mutex> lock(g_ctl);
		want_video = on_now() && !g_current.empty();
	}
	if (want_video) {
		for (int i = 0; i < 400 && shellui_status().rfind("playing", 0) != 0; ++i) {
			usleep(100 * 1000);
		}
		log("after start: ShellUI status '%s'", shellui_status().c_str());
		sleep(2);
	}
	const int rc = install_tile();
	if (rc == 1) {
		notify("LiveShell Engine was added to your home screen.");
	} else if (rc < 0) {
		notify_plain("LiveShell Engine: could not add the home screen tile (see liveshell.log).");
	}
	return nullptr;
}

void start_thread(void* (*fn)(void*)) {
	pthread_t t;
	if (pthread_create(&t, nullptr, fn, nullptr) == 0) {
		pthread_detach(t);
	}
}

} // namespace

// ---- shared API ------------------------------------------------------------------------------

void log(const char* fmt, ...) {
	if (g_log < 0) {
		return;
	}
	char line[600];
	const time_t now = time(nullptr);
	tm           t {};
	localtime_r(&now, &t);
	const int head = static_cast<int>(strftime(line, sizeof(line), "%H:%M:%S ", &t));
	va_list   args;
	va_start(args, fmt);
	int n = vsnprintf(line + head, sizeof(line) - 2 - head, fmt, args);
	va_end(args);
	if (n < 0) {
		return;
	}
	n = std::min(n + head, static_cast<int>(sizeof(line)) - 2);
	line[n++] = '\n';
	std::lock_guard<std::mutex> lock(g_log_lock);
	struct stat st {};
	if (fstat(g_log, &st) == 0 && st.st_size > kLogMaxSize) {
		(void)ftruncate(g_log, 0);
		(void)lseek(g_log, 0, SEEK_SET);
	}
	(void)write(g_log, line, static_cast<size_t>(n));
}

void notify(const char* text) {
	send_notification(text, true);
}

void notify_plain(const char* text) {
	send_notification(text, false);
}

// Favorites (v1.4): /data/LiveShell/favorites.txt, one clip path per line; pinned at the top of the list.
constexpr const char* kFavFile = "/data/LiveShell/favorites.txt";
std::mutex            g_fav_lock;

std::vector<std::string> favorites() {
	std::lock_guard<std::mutex> lock(g_fav_lock);
	const std::string           text = read_text(kFavFile, 64 * 1024);
	std::vector<std::string>    out;
	size_t                      pos = 0;
	while (pos < text.size()) {
		const size_t end = text.find('\n', pos);
		std::string  line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
		if (!line.empty()) {
			out.push_back(line);
		}
		if (end == std::string::npos) {
			break;
		}
		pos = end + 1;
	}
	return out;
}

void set_favorite(const std::string& path, bool on) {
	std::vector<std::string> now = favorites();
	std::lock_guard<std::mutex> lock(g_fav_lock);
	now.erase(std::remove(now.begin(), now.end(), path), now.end());
	if (on) {
		now.push_back(path);
	}
	std::string text;
	for (const std::string& f : now) {
		text += f + "\n";
	}
	write_text(kFavFile, text);
}

std::vector<Video> list_videos() {
	std::vector<Video> all;
	auto scan = [&](const std::string& folder, const std::string& where) {
		DIR* dir = opendir(folder.c_str());
		if (dir == nullptr) {
			return;
		}
		// By date then name here; the whole list is put newest first at the end (all folders together).
		std::vector<std::pair<long long, Video>> found;
		while (dirent* e = readdir(dir)) {
			if (is_mp4(e->d_name)) {
				Video       v {folder + "/" + e->d_name, e->d_name, where};
				struct stat st {};
				found.push_back({stat(v.path.c_str(), &st) == 0 ? static_cast<long long>(st.st_mtime) : 0LL, v});
			}
		}
		closedir(dir);
		std::sort(found.begin(), found.end(), [](const std::pair<long long, Video>& a, const std::pair<long long, Video>& b) {
			return a.first != b.first ? a.first > b.first : strcasecmp(a.second.name.c_str(), b.second.name.c_str()) < 0;
		});
		for (const auto& f : found) {
			all.push_back(f.second);
		}
	};
	// Game folders (named after a title id) inside a video folder: their clips are listed too.
	auto scan_games = [&](const std::string& folder, const std::string& where) {
		if (DIR* dir = opendir(folder.c_str())) {
			std::vector<std::string> subs;
			while (dirent* e = readdir(dir)) {
				if (is_title_id(e->d_name)) {
					subs.push_back(folder + "/" + e->d_name);
				}
			}
			closedir(dir);
			std::sort(subs.begin(), subs.end());
			for (const std::string& s : subs) {
				scan(s, where);
			}
		}
	};
	scan("/data/LiveShell/video", "Internal");
	scan_games("/data/LiveShell/video", "Internal");
	// USB: a folder called liveshell in any capitalisation (the drive's file system is case
	// sensitive here), clips directly inside it and/or in a "video" subfolder.
	auto subdir = [](const std::string& parent, const char* want) {
		std::string found;
		if (DIR* dir = opendir(parent.c_str())) {
			while (dirent* e = readdir(dir)) {
				if (strcasecmp(e->d_name, want) == 0) {
					found = parent + "/" + e->d_name;
					break;
				}
			}
			closedir(dir);
		}
		return found;
	};
	for (int i = 0; i < 8; ++i) {
		const std::string where = "USB " + std::to_string(i + 1);
		const std::string root  = subdir("/mnt/usb" + std::to_string(i), "liveshell");
		if (root.empty()) {
			continue;
		}
		scan(root, where);
		scan_games(root, where);
		const std::string video = subdir(root, "video");
		if (!video.empty()) {
			scan(video, where);
			scan_games(video, where);
		}
	}
	// One list, newest first wherever it is (a new clip on USB is at the top too); same date: as scanned.
	std::vector<std::pair<long long, Video>> dated;
	for (const Video& v : all) {
		struct stat st {};
		dated.push_back({stat(v.path.c_str(), &st) == 0 ? static_cast<long long>(st.st_mtime) : 0LL, v});
	}
	std::stable_sort(dated.begin(), dated.end(),
	                 [](const std::pair<long long, Video>& a, const std::pair<long long, Video>& b) { return a.first > b.first; });
	all.clear();
	for (const auto& d : dated) {
		all.push_back(d.second);
	}
	// Favorites first (newest first among them too), until un-favorited.
	const std::vector<std::string> fav = favorites();
	std::stable_partition(all.begin(), all.end(),
	                      [&](const Video& v) { return std::find(fav.begin(), fav.end(), v.path) != fav.end(); });
	return all;
}

// The console's LAN address: a UDP "connect" picks the outgoing interface without sending anything.
std::string lan_ip() {
	const int s = socket(AF_INET, SOCK_DGRAM, 0);
	if (s < 0) {
		return {};
	}
	sockaddr_in to {};
	to.sin_family      = AF_INET;
	to.sin_port        = htons(53);
	to.sin_addr.s_addr = htonl(0x08080808);
	sockaddr_in me {};
	socklen_t   len = sizeof(me);
	char        ip[INET_ADDRSTRLEN] = {};
	if (connect(s, reinterpret_cast<sockaddr*>(&to), sizeof(to)) == 0 &&
	    getsockname(s, reinterpret_cast<sockaddr*>(&me), &len) == 0) {
		inet_ntop(AF_INET, &me.sin_addr, ip, sizeof(ip));
	}
	close(s);
	return ip;
}

State get_state() {
	State st;
	st.ip = lan_ip();
	{
		std::lock_guard<std::mutex> lock(g_ctl);
		st.enabled = g_enabled;
		st.current = g_current;
		st.dim     = g_dim;
		st.volume  = g_volume;
		for (int l = 0; l < 4; ++l) {
			st.looks[l] = g_looks[l];
		}
		st.shuffle    = g_shuffle;
		st.main_video = g_main_video;
		st.game_videos = g_game_videos;
		st.game_pause = g_game_pause;
		st.menu_hide  = g_menu_hide;
		st.store_only = g_store_only;
		st.parallax   = g_parallax;
		st.auto_match = g_auto_match;
		st.resume     = g_resume;
		st.launchfx   = g_launchfx;
		st.autonext   = g_autonext;
		st.pl_bak     = exists(kPlaylistsBak);
		st.tint       = g_tint;
		for (const Playlist& p : g_playlists) {
			if (p.on) {
				st.playlist = p.name;
			}
		}
		st.game_hide  = g_game_hide;
		st.game       = g_game_running ? g_game_title : std::string();
	}
	st.status = shellui_status();
	st.videos = list_videos();
	return st;
}

void save_user_wall(const std::string& path); // Users: the signed-in user's own main wallpaper

bool select_video(const std::string& path, std::string& error) {
	if (!exists(path.c_str())) {
		error = "That video is gone";
		return false;
	}
	if (refuse_4k(path, error)) {
		return false;
	}
	std::lock_guard<std::mutex> lock(g_ctl);
	const bool was_4k = clip_is_big(g_current);
	g_current  = path;
	g_enabled  = true;
	g_cycle_at = time(nullptr);
	save_user_wall(path); // this user's own wallpaper
	save_config(); // g_override stays: a highlighted game's own clip wins over the main video
	(void)was_4k; // v1.7.0: a 4K main no longer pauses videos per game (kept players + 4K warm-up)
	return apply_locked(error);
}

int net_epoch() {
	return g_net_epoch.load();
}

void set_dim(int percent) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_dim = std::max(0, std::min(80, percent));
	save_config();
	write_text(kDimFile, std::to_string(g_dim) + "\n");
	log("dim: %d%%", g_dim);
}

void set_volume(int percent) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_volume = std::max(0, std::min(100, percent));
	save_config();
	write_text(kVolumeFile, std::to_string(g_volume) + "\n");
	log("volume: %d%%", g_volume);
}

void set_look(const std::string& key, int level) {
	static const char* const kKeys[4] = {"bottom", "top", "vignette", "haze"};
	std::lock_guard<std::mutex> lock(g_ctl);
	for (int l = 0; l < 4; ++l) {
		if (key == kKeys[l]) {
			g_looks[l] = std::max(0, std::min(2, level));
			save_config();
			write_looks();
			log("look %s: %d", kKeys[l], g_looks[l]);
		}
	}
}

void set_tint(int t) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_tint = std::max(0, std::min(5, t));
	save_config();
	write_text("/system_tmp/liveshell/tint.txt", std::to_string(g_tint) + "\n");
	log("colour: %d", g_tint);
}

void set_autonext(int mode) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_autonext = std::max(0, std::min(2, mode));
	save_config();
	log("auto-next: %s", g_autonext == 0 ? "off" : g_autonext == 1 ? "in order" : "shuffle");
}

void set_launchfx(int mode) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_launchfx = std::max(0, std::min(2, mode));
	save_config();
	write_text("/system_tmp/liveshell/launchfx.txt", std::to_string(g_launchfx) + "\n");
	log("launch effect: %d", g_launchfx);
}

bool set_enabled(bool on, std::string& error) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_enabled = on;
	if (on && (g_current.empty() || !exists(g_current.c_str()))) {
		const std::vector<Video> videos = list_videos();
		g_current = videos.empty() ? std::string() : videos.front().path;
	}
	save_config();
	return apply_locked(error);
}

// ---- Playlists -----------------------------------------------------------------------------------
constexpr const char* kPlaylistsFile = "/data/LiveShell/playlists.txt";

// P/V lines -> playlists (also the page's POST). Bad lines are skipped; at most one stays on.
std::vector<Playlist> parse_playlists(const std::string& text) {
	std::vector<Playlist> out;
	size_t pos = 0;
	while (pos < text.size() && out.size() <= 60) {
		size_t end = text.find('\n', pos);
		if (end == std::string::npos) {
			end = text.size();
		}
		std::string line = text.substr(pos, end - pos);
		if (!line.empty() && line.back() == '\r') {
			line.pop_back();
		}
		pos = end + 1;
		std::vector<std::string> f;
		for (size_t a = 0;;) {
			const size_t t = line.find('\t', a);
			f.push_back(line.substr(a, t == std::string::npos ? std::string::npos : t - a));
			if (t == std::string::npos) {
				break;
			}
			a = t + 1;
		}
		if (f[0] == "P" && f.size() >= 5) {
			Playlist p;
			for (const char ch : f[1].substr(0, 40)) {
				p.name += static_cast<unsigned char>(ch) < 0x20 || ch == '"' || ch == '\\' ? ' ' : ch;
			}
			if (p.name.empty()) {
				p.name = "Playlist";
			}
			p.on      = f[2] == "1";
			p.every   = f[3] == "0" ? 0 : std::max(1, std::min(240, atoi(f[3].c_str()))); // 0: when each video ends
			p.shuffle = f[4] == "1";
			out.push_back(p);
		} else if (f[0] == "V" && f.size() >= 2 && !out.empty() && out.back().videos.size() < 5000 &&
		           f[1].rfind("/", 0) == 0 && f[1].find("..") == std::string::npos && is_mp4(f[1].c_str())) {
			out.back().videos.push_back(f[1]);
		}
	}
	bool seen_on = false;
	for (Playlist& p : out) {
		p.on    = p.on && !seen_on;
		seen_on = seen_on || p.on;
	}
	return out;
}

std::string playlists_text(const std::vector<Playlist>& pls) {
	std::string t;
	for (const Playlist& p : pls) {
		t += "P\t" + p.name + "\t" + (p.on ? "1" : "0") + "\t" + std::to_string(p.every) + "\t" + (p.shuffle ? "1" : "0") + "\n";
		for (const std::string& v : p.videos) {
			t += "V\t" + v + "\n";
		}
	}
	return t;
}

void load_playlists_locked() { // caller holds g_ctl
	const std::string text = read_text(kPlaylistsFile, 2 * 1024 * 1024);
	g_playlists            = parse_playlists(text);
	if (g_playlists.empty() && (!exists(kPlaylistsFile) || !text.empty())) { // gone or unreadable (an empty file = deleted on purpose)
		const std::string bak = read_text(kPlaylistsBak, 2 * 1024 * 1024);
		std::vector<Playlist> back = parse_playlists(bak);
		if (!back.empty() && write_text(kPlaylistsFile, bak)) {
			g_playlists = back;
			log("playlists: %s, %zu restored from the backup", text.empty() ? "file missing" : "file unreadable", back.size());
		}
	}
	g_cycle_at = time(nullptr);
}

// "Undo last change": the backup and the list swap places (so a second press redoes).
bool restore_playlists(std::string& error) {
	std::lock_guard<std::mutex> lock(g_ctl);
	if (!exists(kPlaylistsBak)) {
		error = "No earlier playlists to go back to";
		return false;
	}
	const std::string now = read_text(kPlaylistsFile, 2 * 1024 * 1024), bak = read_text(kPlaylistsBak, 2 * 1024 * 1024);
	if (!write_text(kPlaylistsFile, bak) || !write_text(kPlaylistsBak, now)) {
		error = "Could not restore the playlists";
		return false;
	}
	g_playlists = parse_playlists(bak);
	g_cycle_at  = time(nullptr);
	log("playlists: undo, %zu playlists back", g_playlists.size());
	return true;
}

// Playlists per user is gone: playlists made that way (playlists_<user id>.txt) join the shared list once.
void merge_user_playlists() {
	std::vector<Playlist>    all = parse_playlists(read_text(kPlaylistsFile, 2 * 1024 * 1024));
	std::vector<std::string> files;
	if (DIR* d = opendir("/data/LiveShell")) {
		while (dirent* e = readdir(d)) {
			const std::string fn = e->d_name;
			if (fn.rfind("playlists_", 0) == 0 && fn.size() > 14 && fn.compare(fn.size() - 4, 4, ".txt") == 0) {
				files.push_back("/data/LiveShell/" + fn);
			}
		}
		closedir(d);
	}
	if (files.empty()) {
		return;
	}
	auto same = [](Playlist p) { p.on = false; return playlists_text({p}); };
	bool has_on = false;
	for (const Playlist& p : all) {
		has_on = has_on || p.on;
	}
	for (const std::string& file : files) {
		for (Playlist& p : parse_playlists(read_text(file.c_str(), 2 * 1024 * 1024))) {
			bool dup = false;
			for (const Playlist& q : all) {
				dup = dup || same(q) == same(p);
			}
			if (!dup && all.size() < 60) {
				p.on   = p.on && !has_on;
				has_on = has_on || p.on;
				all.push_back(p);
			}
		}
	}
	if (write_text(kPlaylistsFile, playlists_text(all))) {
		for (const std::string& file : files) {
			unlink(file.c_str());
		}
	}
	log("playlists: %zu files of per-user playlists merged, %zu playlists", files.size(), all.size());
}

void load_playlists() {
	std::lock_guard<std::mutex> lock(g_ctl);
	merge_user_playlists();
	load_playlists_locked();
}

bool set_playlists(const std::string& text, std::string& error) {
	std::vector<Playlist> pls = parse_playlists(text);
	std::lock_guard<std::mutex> lock(g_ctl);
	std::string before, after;
	for (const Playlist& p : g_playlists) {
		before += p.on ? p.name : "";
	}
	for (const Playlist& p : pls) {
		after += p.on ? p.name : "";
	}
	g_playlists = pls;
	if (before != after) {
		g_cycle_at = time(nullptr); // a playlist (re)starts: its first change after its own wait
	}
	const std::string old_text = read_text(kPlaylistsFile, 2 * 1024 * 1024), new_text = playlists_text(g_playlists);
	if (old_text != new_text && exists(kPlaylistsFile)) {
		write_text(kPlaylistsBak, old_text); // the list before this save (Undo, and the start-up restore)
	}
	if (!write_text(kPlaylistsFile, new_text)) {
		error = "Could not save the playlists";
		return false;
	}
	log("playlists: %zu saved, on: %s", g_playlists.size(), after.empty() ? "none" : after.c_str());
	return true;
}

std::string playlists_json() {
	std::lock_guard<std::mutex> lock(g_ctl);
	std::string j = "[";
	for (size_t i = 0; i < g_playlists.size(); ++i) {
		const Playlist& p = g_playlists[i];
		j += std::string(i ? "," : "") + "{\"name\":\"" + p.name + "\",\"on\":" + (p.on ? "true" : "false") + ",\"every\":" +
		     std::to_string(p.every) + ",\"shuffle\":" + (p.shuffle ? "true" : "false") + ",\"videos\":[";
		for (size_t k = 0; k < p.videos.size(); ++k) {
			std::string v;
			for (const char ch : p.videos[k]) {
				v += ch == '"' || ch == '\\' ? '_' : ch;
			}
			j += std::string(k ? "," : "") + "\"" + v + "\"";
		}
		j += "]}";
	}
	return j + "]";
}

// ---- Users: LiveShell only for the console users that are on --------------------------------------
std::mutex g_users_lock; // users.txt, userwall.txt

std::string user_name(int32_t id) {
	char name[64] {};
	return sceUserServiceGetUserName(id, name, sizeof(name)) == 0 ? std::string(name) : std::string();
}

// Remembers a user (id=name per line), so Settings can list everyone who signed in since LiveShell came.
void remember_user(int32_t id, const std::string& name) {
	std::lock_guard<std::mutex> lock(g_users_lock);
	const std::string text = read_text("/data/LiveShell/users.txt", 16 * 1024);
	const std::string key  = std::to_string(id) + "=";
	if (("\n" + text).find("\n" + key) == std::string::npos && !name.empty()) {
		write_text("/data/LiveShell/users.txt", text + key + name + "\n");
	}
}

// Each user's own main wallpaper: userwall.txt "id=path", written whenever the main wallpaper changes.
std::string user_wall(int32_t id) {
	std::lock_guard<std::mutex> lock(g_users_lock);
	const std::string text = "\n" + read_text("/data/LiveShell/userwall.txt", 64 * 1024);
	const std::string key  = "\n" + std::to_string(id) + "=";
	const size_t      at   = text.find(key);
	if (at == std::string::npos) {
		return {};
	}
	const size_t end = text.find('\n', at + key.size());
	return text.substr(at + key.size(), end == std::string::npos ? std::string::npos : end - at - key.size());
}

void save_user_wall(const std::string& path) {
	const int32_t id = g_fg_user.load();
	if (id < 0) {
		return;
	}
	std::lock_guard<std::mutex> lock(g_users_lock);
	const std::string text = read_text("/data/LiveShell/userwall.txt", 64 * 1024);
	std::string out, key = std::to_string(id) + "=";
	size_t pos = 0;
	while (pos < text.size()) {
		const size_t end = text.find('\n', pos);
		const std::string line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
		if (!line.empty() && line.rfind(key, 0) != 0) {
			out += line + "\n";
		}
		if (end == std::string::npos) {
			break;
		}
		pos = end + 1;
	}
	write_text("/data/LiveShell/userwall.txt", out + key + path + "\n");
}

// The user's PS5 profile picture (only users with an online profile have one).
std::string user_avatar(int id) {
	char path[96];
	snprintf(path, sizeof(path), "/system_data/priv/cache/profile/0x%08X/avatar.png", static_cast<unsigned>(id));
	return read_text(path, 2 * 1024 * 1024);
}

// ---- animated avatars (v1.6.0) --------------------------------------------------------------
// A user's animated avatar: /data/LiveShell/video/.avatars/<id>.png (an animated PNG; the ShellUI module shows it
// in place of the PSN avatar) and <id>_still.png, its first picture as a plain PNG (the same file without the
// animation chunks: shown at once while the animation decodes). The video folder is mounted where ShellUI can
// read it; its video list takes only .mp4 files.
constexpr const char* kAvatarDir = "/data/LiveShell/video/.avatars"; // hidden: the files LiveShell shows, one per user

std::string avatar_path(int id, bool still) {
	char path[96];
	snprintf(path, sizeof(path), "%s/%u%s.png", kAvatarDir, static_cast<unsigned>(id), still ? "_still" : "");
	return path;
}

bool has_anim_avatar(int id) {
	struct stat st {};
	return stat(avatar_path(id, false).c_str(), &st) == 0 && st.st_size > 64;
}

bool write_file_atomic(const std::string& path, const std::string& data) {
	const std::string tmp = path + ".part";
	const int         fd  = open(tmp.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0666);
	if (fd < 0) {
		return false;
	}
	const bool ok = write(fd, data.data(), data.size()) == static_cast<ssize_t>(data.size());
	close(fd);
	if (!ok || rename(tmp.c_str(), path.c_str()) != 0) {
		unlink(tmp.c_str());
		return false;
	}
	return true;
}

bool save_avatar(int id, const std::string& png, std::string& error) {
	std::string still, anim;
	error.clear();
	if (id <= 0) {
		error = "No such user";
		return false;
	}
	// rebuilt: whole frames, a centred square (partial frames left black gaps on the PS5), see liveshell_apng.cpp
	const time_t t0 = time(nullptr);
	if (!apng_rebuild(png, anim, still, error)) {
		return false;
	}
	mkdir(kAvatarDir, 0777);
	// the still first: the ShellUI module serves it until the animation is decoded
	if (!write_file_atomic(avatar_path(id, true), still) || !write_file_atomic(avatar_path(id, false), anim)) {
		error = "Cannot write to " + std::string(kAvatarDir);
		return false;
	}
	log("avatar: user %d, %zu bytes -> %zu (still %zu), %ld s", id, png.size(), anim.size(), still.size(), static_cast<long>(time(nullptr) - t0));
	return true;
}

// Which library file a user's avatar came from (<id>.src next to it): the Avatar page marks it "In use".
std::string avatar_src_file(int id) {
	char path[96];
	snprintf(path, sizeof(path), "%s/%u.src", kAvatarDir, static_cast<unsigned>(id));
	return path;
}

void note_avatar_src(int id, const std::string& from) {
	write_file_atomic(avatar_src_file(id), from);
}

bool delete_avatar(int id) {
	unlink(avatar_src_file(id).c_str());
	const bool a = unlink(avatar_path(id, false).c_str()) == 0;
	const bool b = unlink(avatar_path(id, true).c_str()) == 0;
	log("avatar: user %d removed", id);
	return a || b;
}

std::string anim_avatar(int id) {
	return read_text(avatar_path(id, false).c_str(), 16 * 1024 * 1024);
}

// The APNG library (the page's "Choose Avatar"): /data/LiveShell/avatar (uploads land there) and on USB a folder
// called liveshell (any capitalisation) or its "avatar" subfolder. Only animated PNGs (an acTL chunk near the start).
constexpr const char* kApngDir = "/data/LiveShell/avatar";
// Animated tiles have their own library (user, v1.7.0): /data/LiveShell/icons, on USB liveshell/icons or icons.
constexpr const char* kIconDir = "/data/LiveShell/icons";

// An animated PNG (an acTL chunk near the start) or a GIF: what "Choose Avatar" lists.
bool is_apng(const std::string& path) {
	const size_t l   = path.size();
	auto         ext = [&](const char* e) { const size_t k = strlen(e); return l > k && strcasecmp(path.c_str() + l - k, e) == 0; };
	if (ext(".gif")) {
		const std::string head = read_text(path.c_str(), 16);
		return head.compare(0, 4, "GIF8") == 0;
	}
	if (!ext(".png") && !ext(".apng")) {
		return false;
	}
	const std::string head = read_text(path.c_str(), 4096);
	return head.size() > 40 && head.compare(1, 3, "PNG") == 0 && head.find("acTL") != std::string::npos;
}

bool apng_allowed(const std::string& path) {
	return path.find("..") == std::string::npos &&
	       (path.rfind(std::string(kApngDir) + "/", 0) == 0 || path.rfind(std::string(kIconDir) + "/", 0) == 0 ||
	        path.rfind("/data/LiveShell/video/.tiles/", 0) == 0 ||
	        path.rfind("/mnt/usb", 0) == 0) && is_apng(path);
}

std::string apngs_json(bool icons) {
	std::string out;
	auto js = [](const std::string& v) { // a JSON string (paths and names: no control characters)
		std::string q = "\"";
		for (const char c : v) {
			if (c == '"' || c == '\\') {
				q += '\\';
			}
			if (static_cast<unsigned char>(c) >= 0x20) {
				q += c;
			}
		}
		return q + "\"";
	};
	auto scan = [&](const std::string& folder, const std::string& where) {
		DIR* dir = opendir(folder.c_str());
		if (dir == nullptr) {
			return;
		}
		std::vector<std::string> names;
		while (dirent* e = readdir(dir)) {
			if (e->d_name[0] != '.' && is_apng(folder + "/" + e->d_name)) {
				names.push_back(e->d_name);
			}
		}
		closedir(dir);
		std::sort(names.begin(), names.end());
		for (const std::string& n : names) {
			struct stat st {};
			const std::string path = folder + "/" + n;
			stat(path.c_str(), &st);
			out += std::string(out.empty() ? "" : ",") + "{\"path\":" + js(path) + ",\"name\":" +
			       js(n.substr(0, n.rfind('.'))) + ",\"where\":" + js(where) + ",\"size\":" +
			       std::to_string(static_cast<long long>(st.st_size)) + "}";
		}
	};
	auto subdir = [](const std::string& parent, const char* want) {
		std::string found;
		if (DIR* dir = opendir(parent.c_str())) {
			while (dirent* e = readdir(dir)) {
				if (strcasecmp(e->d_name, want) == 0) {
					found = parent + "/" + e->d_name;
					break;
				}
			}
			closedir(dir);
		}
		return found;
	};
	if (icons) { // animated tiles: /data/LiveShell/icons, USB liveshell/icons/ and icons/
		mkdir(kIconDir, 0777);
		scan(kIconDir, "Internal");
		for (int i = 0; i < 8; ++i) {
			const std::string drive = "/mnt/usb" + std::to_string(i), where = "USB " + std::to_string(i + 1);
			const std::string root  = subdir(drive, "liveshell");
			const std::string sub   = root.empty() ? std::string() : subdir(root, "icons");
			if (!sub.empty()) {
				scan(sub, where);
			}
			const std::string top = subdir(drive, "icons");
			if (!top.empty()) {
				scan(top, where);
			}
		}
		return "[" + out + "]";
	}
	scan(kApngDir, "Internal");
	for (int i = 0; i < 8; ++i) { // USB: liveshell/, liveshell/avatar/ and avatar/ at the top of the drive
		const std::string drive = "/mnt/usb" + std::to_string(i), where = "USB " + std::to_string(i + 1);
		const std::string root  = subdir(drive, "liveshell");
		if (!root.empty()) {
			scan(root, where);
			const std::string sub = subdir(root, "avatar");
			if (!sub.empty()) {
				scan(sub, where);
			}
		}
		const std::string top = subdir(drive, "avatar");
		if (!top.empty()) {
			scan(top, where);
		}
	}
	return "[" + out + "]";
}

// The pickers' previews: a 128 px copy of a library file, still moving (the originals are up to 16 MB each - a
// grid of them made the picker slow). Made once, kept in /data/LiveShell/.thumbs/<hash>_<file time>.png;
// one at a time (each one decodes the whole animation).
constexpr const char* kThumbDir = "/data/LiveShell/.thumbs";
std::mutex            g_thumb_lock;

std::string apng_thumb(const std::string& path) {
	struct stat st {};
	if (!apng_allowed(path) || stat(path.c_str(), &st) != 0) {
		return std::string();
	}
	uint32_t hash = 2166136261u;
	for (const char c : path) {
		hash = (hash ^ static_cast<unsigned char>(c)) * 16777619u;
	}
	char cached[128];
	snprintf(cached, sizeof(cached), "%s/%08x_%ld.png", kThumbDir, hash, static_cast<long>(st.st_mtime));
	std::lock_guard<std::mutex> lock(g_thumb_lock);
	std::string                 out = read_text(cached, 16 * 1024 * 1024);
	if (!out.empty()) {
		return out;
	}
	static std::set<std::string> failed; // path + file time: not decoded again until the file changes
	const std::string            key = std::string(cached);
	if (failed.count(key) != 0) {
		return std::string();
	}
	std::string still, error;
	if (!apng_rebuild(read_text(path.c_str(), 64 * 1024 * 1024), out, still, error, 128)) { // tiles can pass 16 MB
		log("thumb: %s: %s", path.c_str(), error.c_str());
		failed.insert(key);
		return std::string();
	}
	mkdir(kThumbDir, 0777);
	write_file_atomic(cached, out);
	return out;
}

std::string read_apng(const std::string& path) {
	return apng_allowed(path) ? read_text(path.c_str(), 16 * 1024 * 1024) : std::string();
}

bool set_avatar_from(int id, const std::string& path, std::string& error) {
	const std::string png = read_apng(path);
	if (png.empty()) {
		error = "That APNG is not there any more";
		return false;
	}
	if (!save_avatar(id, png, error)) {
		return false;
	}
	note_avatar_src(id, path);
	return true;
}

// ---- animated game tiles (v1.7.0) -----------------------------------------------------------
// /data/LiveShell/video/.tiles/<TITLE ID>.png: an animation from the APNG library, rebuilt (whole frames, centred
// square, at most 512 px like the PS5's own icons; any number of games) - the ShellUI module shows it in place
// of that game's tile icon. <ID>.src = the library file it came from (the picker marks it "In use").
constexpr const char* kTilesDir = "/data/LiveShell/video/.tiles";

bool tile_id_ok(const std::string& tid) {
	if (tid.size() != 9) {
		return false;
	}
	for (const char c : tid) {
		if (!isalnum(static_cast<unsigned char>(c))) {
			return false;
		}
	}
	return true;
}

// Already tile-ready (what make_tile.py / make_icons.py write): a square APNG of at most 512 px, 8-bit RGB / RGBA,
// not interlaced, every frame the whole picture (no offset, no dispose, "source" blend), every frame fitting the
// home screen's memory like the converter's own. Then it is used as it is: no 2-7 s rebuild on the PS5 (which also
// made the file bigger, so the home screen took longer to show it).
bool apng_ready(const std::string& png) {
	auto be32 = [&](size_t at) {
		return static_cast<uint32_t>(static_cast<unsigned char>(png[at])) << 24 | static_cast<uint32_t>(static_cast<unsigned char>(png[at + 1])) << 16 |
		       static_cast<uint32_t>(static_cast<unsigned char>(png[at + 2])) << 8 | static_cast<uint32_t>(static_cast<unsigned char>(png[at + 3]));
	};
	if (png.size() < 64 || png.compare(1, 3, "PNG") != 0 || png.compare(12, 4, "IHDR") != 0) {
		return false;
	}
	const uint32_t w = be32(16), h = be32(20);
	const int      depth = static_cast<unsigned char>(png[24]), type = static_cast<unsigned char>(png[25]), lace = static_cast<unsigned char>(png[28]);
	if (w != h || w == 0 || w > 512 || depth != 8 || (type != 2 && type != 6) || lace != 0) {
		return false;
	}
	size_t   at     = 8;
	uint32_t frames = 0;
	bool     actl   = false;
	while (at + 12 <= png.size()) {
		const uint32_t len = be32(at);
		if (at + 12 + static_cast<size_t>(len) > png.size()) {
			return false;
		}
		const std::string kind = png.substr(at + 4, 4);
		if (kind == "acTL") {
			actl = true;
		} else if (kind == "fcTL") {
			if (len < 26 || be32(at + 12) == 0xFFFFFFFFu || be32(at + 12 + 4) != w || be32(at + 12 + 8) != h || be32(at + 12 + 12) != 0 ||
			    be32(at + 12 + 16) != 0 || png[at + 12 + 24] != 0 || png[at + 12 + 25] != 0) {
				return false; // a part of the picture, disposed or blended: the converter makes whole frames of it
			}
			++frames;
		} else if (kind == "IEND") {
			break;
		}
		at += 12 + len;
	}
	return actl && frames > 0 && static_cast<uint64_t>(w) * h * 4 * frames <= (64ull << 20);
}

bool set_tile_from(const std::string& tid, const std::string& path, std::string& error) {
	if (!tile_id_ok(tid)) {
		error = "No such game";
		return false;
	}
	const std::string png = read_apng(path);
	if (png.empty()) {
		error = "That animation is not there any more";
		return false;
	}
	std::string  anim, still;
	const time_t t0    = time(nullptr);
	const bool   as_is = apng_ready(png);
	if (as_is) {
		anim = png;
	} else if (!apng_rebuild(png, anim, still, error)) {
		return false;
	}
	mkdir(kTilesDir, 0777);
	const std::string base = std::string(kTilesDir) + "/" + tid;
	if (!write_file_atomic(base + ".png", anim)) {
		error = "Cannot write to " + std::string(kTilesDir);
		return false;
	}
	write_file_atomic(base + ".src", path);
	log("tile: %s <- %s, %zu bytes -> %zu%s, %ld s", tid.c_str(), path.c_str(), png.size(), anim.size(), as_is ? " (tile-ready: as it is)" : "",
	    static_cast<long>(time(nullptr) - t0));
	return true;
}

bool delete_tile(const std::string& tid) {
	if (!tile_id_ok(tid)) {
		return false;
	}
	const std::string base = std::string(kTilesDir) + "/" + tid;
	unlink((base + ".src").c_str());
	const bool ok = unlink((base + ".png").c_str()) == 0;
	log("tile: %s back to its own icon", tid.c_str());
	return ok;
}

std::string tiles_json() {
	std::string out;
	if (DIR* d = opendir(kTilesDir)) {
		while (dirent* e = readdir(d)) {
			const std::string n = e->d_name;
			if (n.size() != 13 || n.compare(9, 4, ".png") != 0 || !tile_id_ok(n.substr(0, 9))) {
				continue;
			}
			std::string src = "\"";
			for (const char c : read_text((std::string(kTilesDir) + "/" + n.substr(0, 9) + ".src").c_str(), 1024)) {
				if (c == '"' || c == '\\') {
					src += '\\';
				}
				if (static_cast<unsigned char>(c) >= 0x20) {
					src += c;
				}
			}
			out += std::string(out.empty() ? "" : ",") + "\"" + n.substr(0, 9) + "\":" + src + "\"";
		}
		closedir(d);
	}
	return "{" + out + "}";
}

// An uploaded APNG / GIF goes into the library too (name from the page, plain characters only).
std::string keep_apng(const std::string& name, const std::string& png, bool icons) {
	std::string n;
	for (const char c : name) {
		n += isalnum(static_cast<unsigned char>(c)) || c == '-' || c == '_' ? c : c == ' ' ? '-' : '\0';
		if (!n.empty() && n.back() == '\0') {
			n.pop_back();
		}
	}
	if (n.empty() || n.size() > 80) {
		n = (icons ? "icon-" : "avatar-") + std::to_string(static_cast<long long>(time(nullptr)));
	}
	const char* dir = icons ? kIconDir : kApngDir;
	mkdir(dir, 0777);
	const std::string path = std::string(dir) + "/" + n + (png.compare(0, 4, "GIF8") == 0 ? ".gif" : ".png");
	return write_file_atomic(path, png) ? path : std::string();
}

// Every account on the console (user_list.dat), with its name: Settings -> Users lists them all from the start.
void load_all_users() {
	const std::string list = read_text("/system_data/priv/home/user_list.dat", 4096);
	std::string       out;
	std::set<uint32_t> seen; // the 16 slots only: after them the file keeps the id the NEXT new account gets
	for (size_t at = 0; at + 4 <= list.size() && at < 16 * 4; at += 4) {
		const uint32_t id = static_cast<uint32_t>(static_cast<unsigned char>(list[at])) |
		                    static_cast<uint32_t>(static_cast<unsigned char>(list[at + 1])) << 8 |
		                    static_cast<uint32_t>(static_cast<unsigned char>(list[at + 2])) << 16 |
		                    static_cast<uint32_t>(static_cast<unsigned char>(list[at + 3])) << 24;
		if (id == 0 || id == 0xFFFFFFFFu || id > 0x7FFFFFFFu || !seen.insert(id).second) {
			continue;
		}
		std::string name = user_name(static_cast<int32_t>(id));
		if (name.empty()) { // not signed in: the name in its config.dat
			char path[96];
			snprintf(path, sizeof(path), "/system_data/priv/home/%x/config.dat", id);
			const std::string cfg = read_text(path, 64);
			for (size_t k = 4; k < cfg.size() && k < 4 + 32 && cfg[k] != 0; ++k) {
				name += cfg[k] == '\n' || cfg[k] == '=' ? ' ' : cfg[k];
			}
		}
		if (!name.empty()) {
			out += std::to_string(id) + "=" + name + "\n";
		}
	}
	if (out.empty()) {
		return; // the list could not be read: users.txt stays as it is (users who signed in)
	}
	std::lock_guard<std::mutex> lock(g_users_lock);
	write_text("/data/LiveShell/users.txt", out);
	log("users: %s", out.c_str());
}

bool user_is_off(int32_t id) {
	return g_off_users.find("," + std::to_string(id) + ",") != std::string::npos;
}

bool set_user_on(int id, bool on) {
	std::lock_guard<std::mutex> lock(g_ctl);
	const std::string key = "," + std::to_string(id) + ",";
	if (g_off_users.empty()) {
		g_off_users = ",";
	}
	const size_t at = g_off_users.find(key);
	if (on && at != std::string::npos) {
		g_off_users.erase(at, key.size() - 1);
	} else if (!on && at == std::string::npos) {
		g_off_users += std::to_string(id) + ",";
	}
	if (g_off_users == ",") {
		g_off_users.clear();
	}
	save_config();
	const bool off = g_fg_user >= 0 && user_is_off(g_fg_user);
	log("users: %d %s (off: %s)", id, on ? "on" : "off", g_off_users.c_str());
	if (off != g_user_off) {
		g_user_off = off;
		std::string error;
		apply_locked(error);
	}
	return true;
}

std::string users_json() {
	std::string text, out;
	int32_t     now = -1;
	{
		std::lock_guard<std::mutex> lock(g_users_lock);
		text = read_text("/data/LiveShell/users.txt", 16 * 1024);
		now  = g_fg_user.load();
	}
	std::lock_guard<std::mutex> lock(g_ctl);
	size_t pos = 0;
	while (pos < text.size()) {
		const size_t end = text.find('\n', pos), eq = text.find('=', pos);
		const std::string line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
		if (eq != std::string::npos && eq < (end == std::string::npos ? text.size() : end)) {
			const int id = atoi(line.c_str());
			std::string name;
			for (const char ch : line.substr(eq - pos + 1)) {
				name += ch == '"' || ch == '\\' ? ' ' : ch;
			}
			out += std::string(out.empty() ? "" : ",") + "{\"id\":" + std::to_string(id) + ",\"name\":\"" + name + "\",\"on\":" +
			       (user_is_off(id) ? "false" : "true") + ",\"now\":" + (id == now ? "true" : "false") +
			       ",\"anim\":" + (has_anim_avatar(id) ? "true" : "false");
			std::string src;
			for (const char ch : read_text(avatar_src_file(id).c_str(), 400)) {
				src += ch == '"' || ch == '\\' || static_cast<unsigned char>(ch) < 0x20 ? '_' : ch;
			}
			out += ",\"avsrc\":\"" + (has_anim_avatar(id) ? src : std::string()) + "\"}";
		}
		if (end == std::string::npos) {
			break;
		}
		pos = end + 1;
	}
	return "[" + out + "]";
}

bool set_option(const std::string& key, bool on, std::string& error) {
	std::lock_guard<std::mutex> lock(g_ctl);
	if (key == "mainvideo") {
		// on = the main video on every tile; off = "Videos per game only" (needs videos per game on)
		g_main_video = on;
		if (!on) {
			g_game_videos = true;
		}
		save_config();
		log("option mainvideo=%d (videos per game only %s)", on ? 1 : 0, on ? "off" : "ON");
		g_focus_recheck = true;
		return !g_injected || apply_locked(error);
	}
	if (key == "shuffle") {
		g_shuffle = on;
	} else if (key == "gamevideos") {
		g_game_videos = on || !g_main_video; // per game only needs them
		save_config();
		log("option gamevideos=%d", on ? 1 : 0);
		g_focus_recheck = true; // the highlighted tile decides again
		return !g_injected || apply_locked(error);
	} else if (key == "gamepause") {
		g_game_pause = true; // not a setting any more (always on)
		(void)on;
	} else if (key == "resume") {
		g_resume = on;
		write_text("/system_tmp/liveshell/resume.txt", on ? "1\n" : "0\n");
	} else if (key == "automatch") {
		g_auto_match = on;
	} else if (key == "parallax") {
		g_parallax = on;
		write_text(kParallaxFile, on ? "1\n" : "0\n");
	} else if (key == "gamehide") {
		g_game_hide = on;
		write_game_open();
		save_config();
		log("option gamehide=%d", on ? 1 : 0);
		return !g_injected || apply_locked(error); // a game open right now: the video goes / comes back
	} else if (key == "menuhide") {
		g_menu_hide = on;
		write_text(kMenusFile, on ? "1\n" : "0\n");
	} else if (key == "storeonly") {
		// PS Store only: ShellUI hides (fades + mutes) the video on every other tile; per-game videos
		// are not used. The player keeps running, so coming back to the Store is instant.
		g_store_only = on;
		write_text(kStoreOnlyFile, on ? "1\n" : "0\n");
		g_focus_recheck = true;
		save_config();
		log("option storeonly=%d", on ? 1 : 0);
		return !g_injected || apply_locked(error); // the Store's clip (or the normal one) now
	} else {
		error = "Unknown setting";
		return false;
	}
	save_config();
	log("option %s=%d", key.c_str(), on ? 1 : 0);
	// Pausing for a game that is running right now takes effect at once.
	return key != "gamepause" || !g_game_running || !g_injected || apply_locked(error);
}

bool delete_video(const std::string& path, std::string& error) {
	std::lock_guard<std::mutex> lock(g_ctl);
	if (path == g_current) {
		// Release it on the home screen first: switch to another clip (or off).
		std::string next;
		for (const Video& v : list_videos()) {
			if (v.path != path) {
				next = v.path;
				break;
			}
		}
		g_current = next;
		save_config();
		if (!apply_locked(error)) {
			return false;
		}
	}
	const std::string cover = path.substr(0, path.rfind('.')) + ".png";
	const bool        ok    = unlink(path.c_str()) == 0;
	unlink(cover.c_str());
	log("delete %s: %s", path.c_str(), ok ? "done" : strerror(errno));
	if (ok) {
		set_favorite(path, false);
		// Games that used it go back to the main video (the Library showed the deleted name).
		const std::string text = read_text("/data/LiveShell/games.txt", 64 * 1024);
		std::string       out;
		int               freed = 0;
		size_t            pos   = 0;
		while (pos < text.size()) {
			const size_t      end  = text.find('\n', pos);
			const std::string line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
			const size_t      eq   = line.find('=');
			if (eq != std::string::npos && line.substr(eq + 1) == path) {
				++freed;
			} else if (!line.empty()) {
				out += line + "\n";
			}
			if (end == std::string::npos) {
				break;
			}
			pos = end + 1;
		}
		if (freed > 0) {
			write_text("/data/LiveShell/games.txt", out);
			write_text("/system_tmp/liveshell/games.txt", out);
			if (g_override == path) {
				g_override.clear();
			}
			g_focus_recheck = true;
			write_fast_map();
			log("delete: %d game(s) used it, back to the main video", freed);
		}
	}
	if (!ok) {
		error = "The file could not be deleted";
	}
	return ok;
}

bool reset_settings(std::string& error) {
	std::lock_guard<std::mutex> lock(g_ctl);
	g_enabled    = true;
	g_dim        = 25;
	g_volume     = 100;
	write_text(kVolumeFile, "100\n");
	for (int& v : g_looks) {
		v = 0;
	}
	write_looks();
	g_shuffle    = false;
	g_main_video = true;
	g_game_videos = true;
	g_game_pause = true;
	g_menu_hide  = true;
	g_store_only = false;
	write_text(kStoreOnlyFile, "0\n");
	g_parallax   = false;
	write_text(kParallaxFile, "0\n");
	g_auto_match = false;
	g_resume     = false;
	write_text("/system_tmp/liveshell/resume.txt", "0\n");
	g_launchfx   = 0;
	g_autonext   = 0;
	write_text("/system_tmp/liveshell/launchfx.txt", "0\n");
	g_tint       = 0;
	write_text("/system_tmp/liveshell/tint.txt", "0\n");
	for (Playlist& p : g_playlists) {
		p.on = false; // reset: playlists are kept, none plays
	}
	g_off_users.clear();
	g_user_off = false;
	g_game_hide  = false;
	write_game_open();
	write_text(kMenusFile, "1\n");
	if (g_current.empty() || !exists(g_current.c_str())) {
		const std::vector<Video> videos = list_videos();
		g_current = videos.empty() ? std::string() : videos.front().path;
	}
	save_config();
	write_text(kDimFile, std::to_string(g_dim) + "\n");
	log("settings reset");
	return apply_locked(error);
}

void request_shutdown() {
	log("shutdown requested from the window");
	g_stop_requested = true;
	g_running        = false;
}

// Per-game backgrounds: /data/LiveShell/games.txt, one "TITLEID=/path/clip.mp4" per line.
constexpr const char* kGamesFile = "/data/LiveShell/games.txt";

std::string games_text() {
	return read_text(kGamesFile, 64 * 1024);
}

// Tiles with no background texture of their own (web-app tiles like Payload Manager, homebrew with only
// a pic0.png like Overdrive) make Sony load its generic bg_hub_default: no title id anywhere, so their
// video never played (v1.2 research). Give such a tile Sony's own default background as pic0.dds
// (same format as games', decoded here from Sony's file - nothing of Sony's is shipped): it looks the
// same as before, and Sony now loads it from the tile's own folder, i.e. with its id. Never overwrites.
void ensure_tile_background(const std::string& tid) {
	if (tid.empty() || tid == "NPXS40047") {
		return;
	}
	const std::string meta = "/user/appmeta/" + tid, app = "/user/app/" + tid + "/sce_sys";
	if (exists((meta + "/pic0.dds").c_str()) || exists((app + "/pic0.dds").c_str())) {
		return; // has its own background
	}
	// Where Sony looks: the app's metadata folder (app.db metaDataPath). Homebrew like Overdrive has an
	// appmeta folder too, but its metaDataPath is /user/app/<id>/sce_sys - a pic0.dds in appmeta was
	// never read (v1.2, app.db pic0Info stayed empty). So sce_sys first, appmeta only if it is missing.
	struct stat st {};
	const std::string dir = stat(app.c_str(), &st) == 0 && S_ISDIR(st.st_mode) ? app
	                        : stat(meta.c_str(), &st) == 0 && S_ISDIR(st.st_mode) ? meta
	                                                                              : std::string();
	if (dir.empty()) {
		log("tile background %s: no app folder", tid.c_str());
		return;
	}
	const std::string zst = read_text("/system_ex/vsh_asset/bg_hub_default.dds.zst", 16 * 1024 * 1024);
	const size_t      n   = zst.empty() ? 0 : liveshell_zstd_size(zst.data(), zst.size());
	if (n < 1024 * 1024 || n > 64 * 1024 * 1024) {
		log("tile background %s: Sony's default background not readable (%zu -> %zu)", tid.c_str(), zst.size(), n);
		return;
	}
	std::string dds(n, '\0');
	if (liveshell_zstd_decode(&dds[0], n, zst.data(), zst.size()) != n || dds.compare(0, 4, "DDS ") != 0) {
		log("tile background %s: could not decode Sony's default background", tid.c_str());
		return;
	}
	const std::string tmp = dir + "/pic0.dds.liveshell", out = dir + "/pic0.dds";
	if (!write_text(tmp.c_str(), dds) || rename(tmp.c_str(), out.c_str()) != 0) {
		unlink(tmp.c_str());
		log("tile background %s: cannot write %s (errno %d)", tid.c_str(), out.c_str(), errno);
		return;
	}
	log("tile background %s: gave it Sony's default background (%s)", tid.c_str(), out.c_str());
	// Sony reads a tile's background info once and caches it: a tile that just got one only sends its id
	// once the home screen restarts - shutting LiveShell down does that (user). Say so, once.
	std::string name = tid;
	for (const Game& g : list_games()) {
		if (g.tid == tid) {
			name = g.name;
			break;
		}
	}
	notify_plain((name + " is ready for its own video. Shut down LiveShell Engine and load it again to see it.").c_str());
}

void set_game_background(const std::string& tid, const std::string& path) {
	if (!path.empty()) {
		ensure_tile_background(tid); // before the lock: decoding takes a moment
	}
	std::lock_guard<std::mutex> lock(g_ctl);
	std::string out;
	const std::string text = read_text(kGamesFile, 64 * 1024);
	size_t      pos  = 0;
	while (pos < text.size()) {
		const size_t      end  = text.find('\n', pos);
		const std::string line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
		if (!line.empty() && line.rfind(tid + "=", 0) != 0) {
			out += line + "\n";
		}
		if (end == std::string::npos) {
			break;
		}
		pos = end + 1;
	}
	if (!path.empty()) {
		out += tid + "=" + path + "\n";
	}
	write_text(kGamesFile, out);
	write_text("/system_tmp/liveshell/games.txt", out);
	write_fast_map();
	g_focus_recheck = true;
	log("game background %s -> %s", tid.c_str(), path.empty() ? "main wallpaper" : path.c_str());
	if (g_store_only && tid == "NPXS40047" && g_injected) {
		std::string error;
		apply_locked(error);
	}
}

// ShellUI's fast switch (test v11-8): it picks the highlighted game's clip itself from this map
// instead of waiting for our round trip. "*=<main clip>", then "TITLEID=<clip>", as ShellUI sees them;
// "-" = needs a remount first (we do that one). Caller holds g_ctl.
// Is the sound track only silence? The track's own frames (the sample table: stsc + stsz + stco/co64 of the track
// whose hdlr is at hdlr_at), measured by byte entropy: silence is padding (<= 2.8 bits/byte on 54 silent
// wallpapers), real sound looks random (>= 6.1). Unreadable: not silent.
bool track_is_silent(int fd, const std::string& moov, size_t hdlr_at) {
	const size_t n    = moov.size();
	const size_t trak = moov.rfind("trak", hdlr_at);
	if (trak == std::string::npos || trak < 4) {
		return false;
	}
	auto be = [&](size_t at, int k) -> uint64_t {
		uint64_t v = 0;
		for (int i = 0; i < k; ++i) {
			v = (v << 8) | (at + i < n ? static_cast<unsigned char>(moov[at + i]) : 0);
		}
		return v;
	};
	const size_t end   = std::min(n, trak - 4 + static_cast<size_t>(be(trak - 4, 4)));
	auto         box   = [&](const char* type) -> size_t { // the payload (after the type), inside this track
		const size_t at = moov.find(type, trak);
		return at != std::string::npos && at + 12 <= end ? at + 4 : std::string::npos;
	};
	const size_t stsz = box("stsz"), stsc = box("stsc"), stco = box("stco"), co64 = box("co64");
	if (stsz == std::string::npos || stsc == std::string::npos || (stco == std::string::npos && co64 == std::string::npos)) {
		return false;
	}
	const bool     wide     = stco == std::string::npos;
	const size_t   co       = wide ? co64 : stco;
	const uint64_t chunks   = be(co + 4, 4);
	const uint64_t one_size = be(stsz + 4, 4), samples = be(stsz + 8, 4);
	const uint64_t stsc_n   = be(stsc + 4, 4);
	if (chunks == 0 || stsc_n == 0 || co + 8 + chunks * (wide ? 8 : 4) > end || stsc + 8 + stsc_n * 12 > end ||
	    (one_size == 0 && stsz + 12 + samples * 4 > end)) {
		return false;
	}
	// Frames this small carry nothing: silence (real AAC sound needs hundreds of bytes a frame).
	uint64_t total = 0;
	if (one_size != 0) {
		total = one_size * samples;
	} else {
		for (uint64_t k = 0; k < samples; ++k) {
			total += be(stsz + 12 + k * 4, 4);
		}
	}
	if (samples > 0 && total / samples <= 32) {
		return true;
	}
	// ~48 pieces over the whole track (a clip can be silent with sound only in parts): any piece that looks like
	// real sound (byte entropy >= 4.5 bits) = sound. Silence is padding (<= 2.8).
	const uint64_t step  = chunks / 48 > 0 ? chunks / 48 : 1;
	uint64_t       sample = 0, entry = 0;
	int            looked = 0;
	std::string    piece;
	for (uint64_t c = 1; c <= chunks; ++c) {
		while (entry + 1 < stsc_n && be(stsc + 8 + (entry + 1) * 12, 4) <= c) {
			++entry;
		}
		const uint64_t per = be(stsc + 8 + entry * 12 + 4, 4);
		uint64_t       len = 0;
		for (uint64_t k = 0; k < per && sample + k < samples; ++k) {
			len += one_size != 0 ? one_size : be(stsz + 12 + (sample + k) * 4, 4);
		}
		sample += per;
		if ((c - 1) % step != 0 || len < 256) {
			continue;
		}
		piece.resize(static_cast<size_t>(std::min<uint64_t>(len, 2048)));
		const off_t at = static_cast<off_t>(be(co + 8 + (c - 1) * (wide ? 8 : 4), wide ? 8 : 4));
		if (pread(fd, &piece[0], piece.size(), at) != static_cast<ssize_t>(piece.size())) {
			continue;
		}
		++looked;
		size_t hist[256] = {};
		for (const char ch : piece) {
			++hist[static_cast<unsigned char>(ch)];
		}
		double bits = 0.0;
		for (const size_t h : hist) {
			if (h != 0) {
				const double q = static_cast<double>(h) / static_cast<double>(piece.size());
				bits -= q * log2(q);
			}
		}
		if (bits >= 4.5) {
			return false; // real sound here
		}
	}
	return looked > 0; // nothing readable: not silent (the old behaviour)
}

// Does the clip have a sound track you can hear? An mp4 'hdlr' box of type 'soun' inside 'moov', and not only
// silence (track_is_silent). Cached by size + date; unreadable = assume sound (the old behaviour). Caller holds g_ctl.
bool clip_has_audio(const std::string& path) {
	static std::map<std::string, std::pair<long long, bool>> cache;
	struct stat st {};
	if (stat(path.c_str(), &st) != 0) {
		return true;
	}
	const long long stamp = static_cast<long long>(st.st_size) * 31 + static_cast<long long>(st.st_mtime);
	auto            hit   = cache.find(path);
	if (hit != cache.end() && hit->second.first == stamp) {
		return hit->second.second;
	}
	bool      audio = true;
	const int fd    = open(path.c_str(), O_RDONLY);
	if (fd >= 0) {
		long long off = 0;
		unsigned char h[16];
		while (off + 8 <= static_cast<long long>(st.st_size) && pread(fd, h, 8, off) == 8) {
			long long size = (static_cast<long long>(h[0]) << 24) | (h[1] << 16) | (h[2] << 8) | h[3];
			long long head = 8;
			if (size == 1) {
				if (pread(fd, h + 8, 8, off + 8) != 8) {
					break;
				}
				size = 0;
				for (int i = 8; i < 16; ++i) {
					size = (size << 8) | h[i];
				}
				head = 16;
			} else if (size == 0) {
				size = static_cast<long long>(st.st_size) - off;
			}
			if (size < head) {
				break;
			}
			if (memcmp(h + 4, "moov", 4) == 0) {
				const size_t n = static_cast<size_t>(std::min<long long>(size, 8 * 1024 * 1024));
				std::string  moov(n, '\0');
				if (pread(fd, &moov[0], n, off) == static_cast<ssize_t>(n)) {
					audio = false;
					for (size_t at = moov.find("hdlr"); at != std::string::npos; at = moov.find("hdlr", at + 4)) {
						if (at + 16 <= n && moov.compare(at + 12, 4, "soun") == 0) {
							audio = !track_is_silent(fd, moov, at); // a track of silence is "no sound"
							break;
						}
					}
				}
				break;
			}
			off += size;
		}
		close(fd);
	}
	cache[path] = {stamp, audio};
	return audio;
}

namespace {

// What the clip's video track is, from its header ('moov' only, a few KB): the coded picture size, codec,
// level, bit depth and colour format. Cached by size + date (web thread + control thread).
struct ClipInfo {
	bool        read   = false; // a video track was found
	std::string codec;          // "avc", "hevc" or another sample entry type ("vp09", "av01"...)
	uint32_t    w = 0, h = 0;
	int         level  = 0;     // H.264: 42 = 4.2; HEVC: level_idc (123 = 4.1)
	int         bits   = 8;     // bit depth (luma)
	int         chroma = 1;     // 1 = 4:2:0, 2 = 4:2:2, 3 = 4:4:4
	bool        cut    = false; // the file ends before its last box does
	bool        frag   = false; // fragmented MP4 (samples in moof boxes - streaming downloads): Sony's player refuses it
};

ClipInfo clip_info(const std::string& path) {
	static std::map<std::string, std::pair<long long, ClipInfo>> cache;
	static std::mutex                                              cache_lock;
	std::lock_guard<std::mutex>                                    guard(cache_lock);
	ClipInfo                                                       ci;
	struct stat                                                    st {};
	if (stat(path.c_str(), &st) != 0) {
		return ci;
	}
	const long long stamp = static_cast<long long>(st.st_size) * 31 + static_cast<long long>(st.st_mtime);
	auto            hit   = cache.find(path);
	if (hit != cache.end() && hit->second.first == stamp) {
		return hit->second.second;
	}
	const int fd = open(path.c_str(), O_RDONLY);
	if (fd >= 0) {
		long long     off = 0;
		unsigned char h[16];
		while (off + 8 <= static_cast<long long>(st.st_size) && pread(fd, h, 8, off) == 8) {
			long long size = (static_cast<long long>(h[0]) << 24) | (h[1] << 16) | (h[2] << 8) | h[3];
			long long head = 8;
			if (size == 1) {
				if (pread(fd, h + 8, 8, off + 8) != 8) {
					break;
				}
				size = 0;
				for (int i = 8; i < 16; ++i) {
					size = (size << 8) | h[i];
				}
				head = 16;
			} else if (size == 0) {
				size = static_cast<long long>(st.st_size) - off;
			}
			if (size < head) {
				break;
			}
			if (off + size > static_cast<long long>(st.st_size)) {
				ci.cut = true; // a box runs past the end: the download was cut off
				break;
			}
			if (memcmp(h + 4, "moov", 4) == 0) {
				const size_t n = static_cast<size_t>(std::min<long long>(size, 8 * 1024 * 1024));
				std::string  moov(n, '\0');
				if (pread(fd, &moov[0], n, off) == static_cast<ssize_t>(n)) {
					ci.frag = moov.find("mvex") != std::string::npos; // "movie extends": the samples come in moof boxes
					auto u8 = [&](size_t at) -> int { return at < n ? static_cast<unsigned char>(moov[at]) : 0; };
					auto be16 = [&](size_t at) -> uint32_t { return (static_cast<uint32_t>(u8(at)) << 8) | static_cast<uint32_t>(u8(at + 1)); };
					auto be32 = [&](size_t at) -> uint32_t { return (be16(at) << 16) | be16(at + 2); };
					// The picture the decoder gets: the video sample entry's width/height (16 bits each, 24 bytes
					// after its type). Not tkhd: that is the DISPLAY size, a little over 1920 for a 1920x1080
					// clip with non-square pixels (Floating Island: 1945x1080), which plays fine.
					for (const char* type : {"avc1", "avc3", "hvc1", "hev1", "vp09", "av01", "mp4v", "mjpg"}) {
						const size_t at = moov.find(type);
						if (at == std::string::npos || at < 4 || at + 32 > n) {
							continue;
						}
						ci.read  = true;
						ci.w     = be32(at + 28) >> 16;
						ci.h     = be32(at + 28) & 0xFFFF;
						const bool avc = type[1] == 'v' && type[2] == 'c';
						const bool hevc = type[0] == 'h';
						ci.codec = avc ? "avc" : hevc ? "hevc" : type;
						// Its decoder settings box follows within the sample entry.
						const size_t cfg = moov.find(avc ? "avcC" : "hvcC", at);
						if ((avc || hevc) && cfg != std::string::npos && cfg < at + 512) {
							const size_t p = cfg + 4; // the box's payload
							if (avc) {
								const int profile = u8(p + 1);
								ci.level          = u8(p + 3);
								if ((u8(p + 5) & 0x1F) > 0 && be16(p + 6) >= 4) {
									ci.level = u8(p + 6 + 2 + 3); // the SPS's own level (what the decoder reads; the box's copy can differ)
								}
								ci.bits           = profile == 110 || profile == 122 || profile == 244 ? 10 : 8;
								ci.chroma         = profile == 122 ? 2 : profile == 244 ? 3 : 1;
								if (profile == 100 || profile == 110 || profile == 122 || profile == 244) {
									// High profiles: chroma format + bit depth after the SPS / PPS lists
									size_t q = p + 6;
									for (int k = u8(p + 5) & 0x1F; k > 0 && q + 2 <= n; --k) {
										q += 2 + be16(q);
									}
									if (q < n) {
										for (int k = u8(q++); k > 0 && q + 2 <= n; --k) {
											q += 2 + be16(q);
										}
									}
									if (q + 3 <= n && (u8(q) & 0xFC) == 0xFC) { // reserved bits set = the fields are there
										ci.chroma = u8(q) & 3;
										ci.bits   = 8 + (u8(q + 1) & 7);
									}
								}
							} else {
								ci.level  = u8(p + 12);
								ci.chroma = u8(p + 16) & 3;
								ci.bits   = 8 + (u8(p + 17) & 7);
								if ((u8(p + 1) & 0x1F) == 2) { // Main 10
									ci.bits = std::max(ci.bits, 10);
								}
							}
						}
						break;
					}
					if (!ci.read) { // no video sample entry found: the track header
						for (size_t at = moov.find("tkhd"); at != std::string::npos && at >= 4; at = moov.find("tkhd", at + 4)) {
							const size_t box = at - 4;
							const size_t wat = box + (moov[at + 4] == 1 ? 96 : 84);
							if (wat + 8 <= n) {
								ci.w = std::max(ci.w, be32(wat) >> 16);
								ci.h = std::max(ci.h, be32(wat + 4) >> 16);
							}
						}
					}
				}
			}
			off += size; // on to the end: a cut-off file shows in its last box
		}
		close(fd);
	}
	cache[path] = {stamp, ci};
	return ci;
}

} // namespace

// Is the clip bigger than 1080p (4K is not supported: ShellUI's player gets a Full HD decoder only)?
bool clip_is_big(const std::string& path) {
	const ClipInfo ci  = clip_info(path);
	const bool     big = ci.w > 1920 || ci.h > 1088;
	return big;
}

// The badge in the video lists: "4K", "2K", "FHD", "HD" or "" (smaller / unknown).
std::string clip_res(const std::string& path) {
	const ClipInfo ci = clip_info(path);
	const unsigned a  = std::max(ci.w, ci.h), b = std::min(ci.w, ci.h); // portrait clips too
	if (a == 0) {
		return {};
	}
	return a >= 3800 || b >= 2100 ? "4K" : a >= 2500 || b >= 1400 ? "2K" : a >= 1900 || b >= 1060 ? "FHD" : a >= 1260 || b >= 700 ? "HD" : "";
}

// "Can I play this?": why the PS5 will not play the clip ("" = it plays, or its header could not be read).
// Limits: H.264 up to level 4.2, HEVC up to level 4.1, 8-bit 4:2:0, at most 1920x1088.
std::string clip_problem(const std::string& path) {
	const ClipInfo ci = clip_info(path);
	char           why[96] = {};
	if (ci.cut) {
		return "The file is cut off - download it again";
	}
	if (ci.frag) {
		return "Fragmented MP4 - press Convert it on your phone or PC, or download it again";
	}
	const bool uhd = ci.w > 1920 || ci.h > 1088; // 4K: the UHD decoder (H.264 up to 5.2, HEVC up to 5.1)
	if (ci.w > 3840 || ci.h > 2160) {
		snprintf(why, sizeof(why), "Too big (%ux%u) - max 3840x2160", ci.w, ci.h);
	} else if (!ci.read) {
		return {};
	} else if (ci.codec != "avc" && ci.codec != "hevc") {
		snprintf(why, sizeof(why), "%s video - needs H.264 or HEVC",
		         ci.codec == "vp09" ? "VP9" : ci.codec == "av01" ? "AV1" : ci.codec == "mp4v" ? "MPEG-4" : ci.codec.c_str());
	} else if (ci.bits > 8) {
		snprintf(why, sizeof(why), "%d-bit colour - needs 8-bit", ci.bits);
	} else if (ci.chroma == 2 || ci.chroma == 3) {
		snprintf(why, sizeof(why), "%s colour - needs 4:2:0", ci.chroma == 2 ? "4:2:2" : "4:4:4");
	} else if (ci.codec == "avc" && ci.level > (uhd ? 52 : 42)) {
		snprintf(why, sizeof(why), "H.264 level %d.%d - max %s", ci.level / 10, ci.level % 10, uhd ? "5.2" : "4.2");
	} else if (ci.codec == "hevc" && ci.level > (uhd ? 153 : 123)) {
		snprintf(why, sizeof(why), "HEVC level %d.%d - max %s", ci.level / 30, ci.level % 30 / 3, uhd ? "5.1" : "4.1");
	}
	return why;
}

void write_fast_map() {
	// Wallpaper off: every tile "off", so ShellUI starts nothing by itself (a highlighted tile or the
	// return from a game started the video again while Settings still said off).
	if (!on_now()) {
		write_text("/system_tmp/liveshell/fast.txt", "*=off\n");
		return;
	}
	auto shown = [](const std::string& clip) -> std::string {
		if (clip.empty() || g_mounted_folder.empty() || mount_base(clip) != g_mounted_folder || !exists(clip.c_str())) {
			return "-";
		}
		return shown_path(clip);
	};
	std::string       out  = "*=" + (g_store_only ? shown(store_clip()) : g_main_video ? shown(g_current) : std::string("hide")) + "\n";
	const std::string text = g_game_videos && !g_store_only ? read_text(kGamesFile, 64 * 1024) : std::string(); // 4K per game too (v1.7.0)
	size_t            pos  = 0;
	while (pos < text.size()) {
		const size_t      end  = text.find('\n', pos);
		const std::string line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
		const size_t      eq   = line.find('=');
		if (eq != std::string::npos && eq > 0) { // the PS Store tile too (v1.7.0); in "PS Store only" mode this list is empty
			out += line.substr(0, eq) + "=" + shown(line.substr(eq + 1)) + "\n";
		}
		if (end == std::string::npos) {
			break;
		}
		pos = end + 1;
	}
	// "!<clip>" = no sound track: ShellUI lets the PS5's own music (a game's theme) play with it.
	// "^<clip>\t<file name>\t" = a 4K clip: ShellUI streams it (UHD); it hides while a game is open.
	for (const Video& v : list_videos()) {
		if (g_mounted_folder.empty() || mount_base(v.path) != g_mounted_folder) {
			continue;
		}
		if (!clip_has_audio(v.path)) {
			out += "!" + shown_path(v.path) + "\n";
		}
		if (clip_is_big(v.path)) {
			out += "^" + shown_path(v.path) + "\t" + v.name + "\t\n";
		}
	}
	write_text("/system_tmp/liveshell/fast.txt", out);
}

// ShellUI cannot read /data: it gets a copy of games.txt to label the menu item (Set / Remove).
void mirror_games() {
	write_text("/system_tmp/liveshell/games.txt", read_text(kGamesFile, 64 * 1024));

}


// ---- installed games (Games tab) ----------------------------------------------------------------

// PS4 titles keep their name in param.sfo (binary); PS5 titles in param.json.
std::string sfo_title(const std::string& path) {
	const std::string d = read_text(path.c_str(), 64 * 1024);
	if (d.size() < 20 || d.compare(0, 4, std::string("\0PSF", 4)) != 0) {
		return {};
	}
	auto u16 = [&](size_t o) { return static_cast<uint32_t>(static_cast<uint8_t>(d[o]) | static_cast<uint8_t>(d[o + 1]) << 8); };
	auto u32 = [&](size_t o) { return u16(o) | u16(o + 2) << 16; };
	const uint32_t keys = u32(8), data = u32(12), count = u32(16);
	for (uint32_t i = 0; i < count && 20 + i * 16 + 16 <= d.size(); ++i) {
		const size_t   e   = 20 + i * 16;
		const uint32_t ko  = keys + u16(e), len = u32(e + 4), dof = data + u32(e + 12);
		if (ko < d.size() && strcmp(d.c_str() + ko, "TITLE") == 0 && dof + len <= d.size()) {
			return std::string(d.c_str() + dof);
		}
	}
	return {};
}

std::string json_title(const std::string& path) {
	const std::string d = read_text(path.c_str(), 256 * 1024);
	// Prefer en-US, else the first titleName.
	size_t at = d.find("\"en-US\"");
	at        = d.find("\"titleName\"", at == std::string::npos ? 0 : at);
	if (at == std::string::npos) {
		at = d.find("\"titleName\"");
	}
	if (at == std::string::npos) {
		return {};
	}
	const size_t q1 = d.find('"', d.find(':', at) + 1);
	const size_t q2 = q1 == std::string::npos ? q1 : d.find('"', q1 + 1);
	return q2 == std::string::npos ? std::string() : d.substr(q1 + 1, q2 - q1 - 1);
}

bool is_title_id(const char* n) {
	if (strlen(n) != 9) {
		return false;
	}
	for (int i = 0; i < 4; ++i) {
		if (!isupper(static_cast<unsigned char>(n[i]))) {
			return false;
		}
	}
	for (int i = 4; i < 9; ++i) {
		if (!isdigit(static_cast<unsigned char>(n[i]))) {
			return false;
		}
	}
	return strncmp(n, "NPXS", 4) != 0 && strcmp(n, "LVSH00001") != 0;
}

std::vector<Game> list_games() {
	std::vector<Game> out;
	// Games on the console, then games on extended storage (their metadata: /user/appmeta/external).
	for (const char* folder : {"/user/appmeta", "/user/appmeta/external"}) {
		DIR* dir = opendir(folder);
		if (dir == nullptr) {
			continue;
		}
		while (dirent* e = readdir(dir)) {
			if (!is_title_id(e->d_name) ||
			    std::any_of(out.begin(), out.end(), [&](const Game& g) { return g.tid == e->d_name; })) {
				continue;
			}
			const std::string base = std::string(folder) + "/" + e->d_name;
			std::string       name = json_title(base + "/param.json");
			if (name.empty()) {
				name = sfo_title(base + "/param.sfo");
			}
			if (name.empty()) {
				continue; // no title: not a game we can show (e.g. tools, leftovers)
			}
			out.push_back({e->d_name, name});
		}
		closedir(dir);
	}
	// Homebrew tiles (Payload Manager, etaHEN Toolbox, PKG Manager ...) have no /user/appmeta folder:
	// their name is in /user/app/<id>/sce_sys/param.json (9 apps were missing from the Library, user).
	if (DIR* apps = opendir("/user/app")) {
		while (dirent* e = readdir(apps)) {
			if (!is_title_id(e->d_name) ||
			    std::any_of(out.begin(), out.end(), [&](const Game& g) { return g.tid == e->d_name; })) {
				continue;
			}
			const std::string name = json_title(std::string("/user/app/") + e->d_name + "/sce_sys/param.json");
			if (!name.empty()) {
				out.push_back({e->d_name, name});
			}
		}
		closedir(apps);
	}
	std::sort(out.begin(), out.end(), [](const Game& a, const Game& b) { return strcasecmp(a.name.c_str(), b.name.c_str()) < 0; });
	return out;
}

// ---- per-game playback: the highlighted game's clip -----------------------------------------
// ShellUI writes the highlighted title id to focus_game.txt ("" for non-game tiles). After ~1 s on
// the same tile, play that game's clip (games.txt) instead of the main one; elsewhere, the main one.
// What PLAYS for a tile: its saved clip, unless "Videos per game" is off (then the main one).
std::string game_clip(const std::string& tid) {
	// v1.7.0: 4K per game is back (kept players + the 4K warm-up make switching fast).
	return g_game_videos && !g_store_only ? saved_game_clip(tid) : std::string(); // the PS Store tile too (v1.7.0)
}

// 4K plays (v1.4, UHD stream); bigger than 4K does not: say so instead of a black screen. True = refused
// (error set + PS5 notifications). Takes no lock.
bool refuse_4k(const std::string& path, std::string& error) {
	const ClipInfo ci = clip_info(path);
	if (ci.w <= 3840 && ci.h <= 2160) {
		return false;
	}
	error = "Videos bigger than 4K are not supported. Use a 4K or 1080p video.";
	notify("Videos bigger than 4K are not supported");
	notify("Use a 4K or 1080p video.");
	return true;
}

// The clip saved for a tile in games.txt (the Library list shows it even when switched off).
std::string saved_game_clip(const std::string& tid) {
	if (tid.empty()) {
		return {};
	}
	const std::string text = read_text("/data/LiveShell/games.txt", 64 * 1024);
	const size_t      at   = text.find(tid + "=");
	if (at == std::string::npos || (at > 0 && text[at - 1] != '\n')) {
		return {};
	}
	const size_t end = text.find('\n', at);
	return text.substr(at + tid.size() + 1, end == std::string::npos ? std::string::npos : end - at - tid.size() - 1);
}


void* focus_thread(void*) {
	std::string seen, pending, match; // match: a newly decided game tile for Auto-match (checked outside g_ctl)
	long        changed_ms = 0;
	auto        now_ms     = [] {
        timespec ts {};
        clock_gettime(CLOCK_MONOTONIC, &ts);
        return static_cast<long>(ts.tv_sec) * 1000 + ts.tv_nsec / 1000000;
	};
	while (g_running) {
		usleep(200 * 1000);
		const std::string tid = shellui_focus();
		if (tid != seen) {
			seen       = tid;
			changed_ms = now_ms();
			continue;
		}
		if (g_focus_recheck) {
			g_focus_recheck = false;
			pending         = "?"; // games.txt changed: decide again for the same tile
		}
		if (now_ms() - changed_ms < 250 || tid == pending) {
			continue;
		}
		std::string clip = game_clip(tid);
		if (!clip.empty() && !exists(clip.c_str())) {
			clip.clear();
		}
		std::lock_guard<std::mutex> lock(g_ctl);
		if (!g_injected || !on_now() || g_game_running) {
			continue; // not now: decide again once we can switch (pending unchanged)
		}
		if (tid != pending) {
			write_text("/data/LiveShell/last_game.txt", tid + "\n"); // the PS5 comes back to this tile
		}
		pending = tid;
		if (clip == g_override) {
			continue;
		}
		g_override = clip;
		log("per-game: %s -> %s", tid.empty() ? "(no game)" : tid.c_str(), clip.empty() ? "main wallpaper" : clip.c_str());
		std::string error;
		if (!apply_locked(error)) {
			log("per-game: %s", error.c_str());
		}
	}
	return nullptr;
}

// Users: who is signed in (every 2 s). A user switched off in Settings gets the normal PS5 background.
void* user_thread(void*) {
	sceUserServiceInitialize(nullptr); // "already initialized" is fine
	load_all_users();                  // every account, not only the ones that signed in since LiveShell came
	int32_t last = -2;
	long    list_mtime = 0;
	while (g_running) {
		struct stat ls {};
		if (stat("/system_data/priv/home/user_list.dat", &ls) == 0 && static_cast<long>(ls.st_mtime) != list_mtime) {
			if (list_mtime != 0) {
				load_all_users(); // an account was added or deleted
			}
			list_mtime = static_cast<long>(ls.st_mtime);
		}
		int32_t id = -1;
		if (sceUserServiceGetForegroundUser(&id) == 0 && id >= 0 && id != last) {
			last = id;
			const std::string name = user_name(id);
			remember_user(id, name);
			g_fg_user = id;
			const std::string mine = user_wall(id); // this user's own main wallpaper
			std::lock_guard<std::mutex> lock(g_ctl);
			const bool off = user_is_off(id);
			log("users: %s (%d) signed in%s", name.c_str(), id, off ? " - LiveShell is off for this user" : "");
			bool redo = off != g_user_off;
			g_user_off = off;
			if (!mine.empty() && mine != g_current && exists(mine.c_str())) {
				g_current = mine;
				save_config();
				log("users: %s's own wallpaper %s", name.c_str(), mine.c_str());
				redo = true;
			}
			if (redo) {
				std::string error;
				apply_locked(error);
			}
		}
		sleep(2);
	}
	return nullptr;
}

// Playlists: the one that is on changes the main wallpaper every N minutes (in order or shuffled), through its
// videos that are still there and play. Not while a game runs or the wallpaper is off / hidden; a hand pick starts
// the wait again. Only the main wallpaper: a tile's own video still wins on that tile.
void* cycle_thread(void*) {
	while (g_running) {
		sleep(5);
		std::string current;
		Playlist    pl;
		{
			std::lock_guard<std::mutex> lock(g_ctl);
			const Playlist* on = nullptr;
			for (const Playlist& p : g_playlists) {
				on = p.on ? &p : on;
			}
			if (on == nullptr || !on_now() || !g_injected || g_game_running || g_game_open || g_store_only || !g_main_video) {
				if (on == nullptr || g_cycle_at == 0) {
					g_cycle_at = time(nullptr);
				}
				continue;
			}
			if (on->every == 0 || time(nullptr) - g_cycle_at < static_cast<time_t>(on->every) * 60) { // 0: when it ends
				continue;
			}
			current = g_current;
			pl      = *on;
		}
		std::vector<std::string> pool;
		for (const std::string& v : pl.videos) {
			if (exists(v.c_str()) && clip_problem(v).empty() && std::find(pool.begin(), pool.end(), v) == pool.end()) {
				pool.push_back(v);
			}
		}
		std::lock_guard<std::mutex> lock(g_ctl);
		g_cycle_at = time(nullptr);
		if (pool.empty() || current != g_current || (pool.size() == 1 && pool[0] == current)) {
			continue; // nothing to change to, or the user just picked one
		}
		auto next = pool.begin();
		if (pl.shuffle && pool.size() > 1) {
			do {
				next = pool.begin() + static_cast<long>(static_cast<unsigned>(rand()) % pool.size());
			} while (*next == current);
		} else {
			const auto at = std::find(pool.begin(), pool.end(), current);
			next          = at == pool.end() || at + 1 == pool.end() ? pool.begin() : at + 1;
		}
		g_current = *next;
		save_config();
		save_user_wall(g_current);
		log("playlist %s: next wallpaper %s", pl.name.c_str(), g_current.c_str());
		std::string error;
		if (!apply_locked(error)) {
			log("cycle: %s", error.c_str());
		}
	}
	return nullptr;
}

// A video ended (issue #11): a playlist that is on with Change "When it ends" -> its next video (in order, or
// shuffled with its Shuffle switch); no playlist on -> Auto-next (in order / shuffled) through all videos.
// Shuffled = every video once before any repeats (a "bag"). Anything else: the clip just loops.
void* autonext_thread(void*) {
	std::vector<std::string> bag;
	while (g_running) {
		usleep(200 * 1000);
		if (!g_ended.exchange(false)) {
			continue;
		}
		std::string ended;
		{
			std::lock_guard<std::mutex> lock(g_ui_lock);
			ended = g_ended_clip;
		}
		std::vector<std::string> pool;
		int                      mode = 0;
		std::string              current;
		{
			std::lock_guard<std::mutex> lock(g_ctl);
			const Playlist* on = nullptr;
			for (const Playlist& p : g_playlists) {
				on = p.on ? &p : on;
			}
			mode = on != nullptr ? (on->every == 0 ? (on->shuffle ? 2 : 1) : 0) : g_autonext;
			if (mode == 0 || !on_now() || !g_injected || g_game_running || g_game_open || g_store_only || !g_main_video ||
			    !g_override.empty() || g_current.empty() ||
			    ended.substr(ended.rfind('/') + 1) != g_current.substr(g_current.rfind('/') + 1)) { // by name: 4K plays from a stream address
				continue; // off, or not the main wallpaper that ended (a game's own video, PS Store only ...)
			}
			current = g_current;
			if (on != nullptr) {
				pool = on->videos;
			}
		}
		if (pool.empty()) {
			for (const Video& v : list_videos()) {
				pool.push_back(v.path);
			}
		}
		pool.erase(std::remove_if(pool.begin(), pool.end(), [](const std::string& v) { return !exists(v.c_str()); }), pool.end());
		if (pool.size() < 2) {
			continue;
		}
		std::string next;
		if (mode == 2) {
			for (int guard = 0; next.empty() && guard < 2 * static_cast<int>(pool.size()) + 2; ++guard) {
				bag.erase(std::remove_if(bag.begin(), bag.end(),
				                         [&](const std::string& v) { return std::find(pool.begin(), pool.end(), v) == pool.end(); }),
				          bag.end());
				if (bag.empty()) { // a new round: every video once, the one playing not first
					bag = pool;
					for (size_t i = bag.size() - 1; i > 0; --i) {
						std::swap(bag[i], bag[static_cast<size_t>(rand()) % (i + 1)]);
					}
					if (bag.back() == current) {
						std::swap(bag.front(), bag.back());
					}
				}
				const std::string c = bag.back();
				bag.pop_back();
				if (c != current && clip_problem(c).empty()) {
					next = c;
				}
			}
		} else {
			const auto at = std::find(pool.begin(), pool.end(), current);
			size_t     i  = at == pool.end() ? pool.size() - 1 : static_cast<size_t>(at - pool.begin());
			for (size_t k = 0; k < pool.size() && next.empty(); ++k) {
				i = (i + 1) % pool.size();
				if (pool[i] != current && clip_problem(pool[i]).empty()) {
					next = pool[i];
				}
			}
		}
		if (next.empty()) {
			continue;
		}
		std::lock_guard<std::mutex> lock(g_ctl);
		if (g_current != current) {
			continue; // the user picked one meanwhile
		}
		g_current  = next;
		g_cycle_at = time(nullptr);
		save_config();
		save_user_wall(g_current);
		log("video ended, next (%s): %s", mode == 1 ? "in order" : "shuffled", g_current.c_str());
		std::string error;
		if (!apply_locked(error)) {
			log("next video: %s", error.c_str());
		}
	}
	return nullptr;
}

// "Hide while a game is open": ShellUI must not start a video by itself (return from a game, tile move)
// while this file says 1. Caller holds g_ctl.
void write_game_open() {
	write_text(kGameOpenFile, g_game_hide && g_game_open ? "1\n" : "0\n");
	write_text("/system_tmp/liveshell/gamealive.txt", g_game_open ? "1\n" : "0\n"); // 4K: no UHD decoder then
}

// A game (not a system app, not our own window) is running: no video, the game gets the decoder.
// "Running" = in front (the PS5 reports no running big app while it is suspended on the home screen).
// "Open" = in front, or its app still answers in the background: for "Hide while a game is open".
void* game_thread(void*) {
	bool last = false, last_open = false;
	int  open_app = -1;
	char open_id[32] {};
	{
		std::lock_guard<std::mutex> lock(g_ctl);
		g_game_open = false;
		write_game_open(); // a file from an earlier run must not hold the video back
	}
	while (g_running) {
		sleep(1); // 2 s before: the video came back late after a game
		const int   app = sceSystemServiceGetAppIdOfRunningBigApp();
		char        id[32] {};
		const bool  now = app >= 0 && sceSystemServiceGetAppTitleId(app, id) == 0 && id[0] != 0 &&
		                 strncmp(id, "NPXS", 4) != 0 && strcmp(id, "LVSH00001") != 0;
		if (now) {
			open_app = app;
			snprintf(open_id, sizeof(open_id), "%s", id);
		}
		char       again[32] {};
		const bool open = now || (open_app >= 0 && sceSystemServiceGetAppTitleId(open_app, again) == 0 &&
		                          strcmp(again, open_id) == 0);
		if (!open) {
			open_app = -1;
		}
		// Our own window in front (the home screen behind it pauses the video): ShellUI must not take that for
		// a frozen video, and plays it on when the window closes.
		static int last_win = -1;
		const int  win      = page_open() || (app >= 0 && strcmp(id, "LVSH00001") == 0) ? 1 : 0;
		if (win != last_win) {
			last_win = win;
			write_text("/system_tmp/liveshell/window.txt", win != 0 ? "1\n" : "0\n");
			log("window %s", win != 0 ? "in front" : "closed");
		}
		if (now == last && open == last_open) {
			continue;
		}
		std::lock_guard<std::mutex> lock(g_ctl);
		if (now != last) {
			g_game_running = now;
			g_game_title   = now ? id : "";
			log("game %s (%s)", now ? "started" : "closed", now ? id : "-");
		}
		if (open != last_open) {
			log("game %s", open ? "open" : "no longer open (closed for good)");
		}
		last        = now;
		last_open   = open;
		g_game_open = open;
		write_game_open();
		if (g_injected) {
			std::string error;
			if (!apply_locked(error)) {
				log("game pause: %s", error.c_str());
			}
		}
	}
	return nullptr;
}

} // namespace liveshell

using namespace liveshell;

int main() {
	mkdir("/data/LiveShell", 0777);
	mkdir("/data/LiveShell/video", 0777);
	mkdir("/system_tmp/liveshell", 0777);
	// The files ShellUI cannot do without get their slot first (/system_tmp: ~33 files for everyone).
	for (const char* f : {kPathFile, kOptsFile, "/system_tmp/liveshell/fast.txt", "/system_tmp/liveshell/games.txt"}) {
		if (!exists(f)) {
			write_text(f, f == kPathFile ? "off\n" : "");
		}
	}
	// The old per-setting files of an earlier version (each took a slot).
	for (const char* n : kOptNames) {
		unlink((std::string("/system_tmp/liveshell/") + n).c_str());
	}
	// Loading the payload = try again: a crash marker from an earlier run must not keep the video
	// off until the next reboot.
	unlink("/system_tmp/liveshell/video_trying");
	g_log = open(kLogFile, O_WRONLY | O_CREAT | O_TRUNC, 0666);
	log("LiveShell starting");
	if (take_over_running()) {
		log("handover: took over from the LiveShell that was running");
	}
	// The injector's own steps (attach / load / stager / detach) go here.
	unlink("/data/LiveShell/inject.log");
	onion_log_configure("liveshell", "/data/LiveShell/inject.log");
	onion_log_set_level(ONION_LOG_DEBUG);

	if (kOnionGuard && onion_daemon_answers()) {
		notify("LiveShell Engine can't run while OnionHEN is running.");
		return 1;
	}

	std::vector<Video> videos = list_videos();
	log("%zu video(s) found", videos.size());
	{
		std::lock_guard<std::mutex> lock(g_ctl);
		load_config();
		const bool chosen_ok = std::any_of(videos.begin(), videos.end(), [](const Video& v) { return v.path == g_current; });
		if (!chosen_ok) {
			g_current = videos.empty() ? std::string() : videos.front().path;
		}
		if (g_shuffle && videos.size() > 1) {
			// Random clip on every start, never the same one twice in a row.
			srand(static_cast<unsigned>(time(nullptr)) ^ static_cast<unsigned>(getpid()));
			std::vector<std::string> others;
			for (const Video& v : videos) {
				if (v.path != g_current) {
					others.push_back(v.path);
				}
			}
			g_current = others[static_cast<size_t>(rand()) % others.size()];
			save_config();
			log("shuffle: %s", g_current.c_str());
		}
		// Start with the clip of the game the home screen will highlight: the PS5 comes back to the
		// last focused tile, which we noted (focus info only arrives once the user moves).
		const std::string last = first_line(read_text("/data/LiveShell/last_game.txt", 64));
		const std::string lclip = game_clip(last);
		if (!lclip.empty() && exists(lclip.c_str())) {
			g_override = lclip;
			write_text("/system_tmp/liveshell/focus_game.txt", last + "\n");
			ui_set_focus(last);
			log("start: last highlighted game %s -> %s", last.c_str(), lclip.c_str());
		}
		std::string error;
		apply_locked(error); // not injected yet: just mounts + writes the path file
	}
	if (videos.empty()) {
		notify_plain("No video found. Put an .mp4 in /data/LiveShell/video or in a liveshell folder on a USB drive.");
	}

	start_thread(ui_thread); // before the injection: ShellUI talks to us from its first line
#ifdef LIVESHELL_RESEARCH_DUMP
	start_thread(dump_rx_thread);
#endif
	start_thread(power_thread);
	start_thread(stop_thread);
	start_web_server();
#ifdef LIVESHELL_RESEARCH_RETRO
	retro_start([](const char* line) { log("%s", line); }, [](const char* line) { notify(line); });
#endif

#ifdef LIVESHELL_FAST
	// liveshell-fast.elf: no wait after power-on, the wallpaper starts at once (user: two versions from v1.6.0).
	unlink(kEarlyCrashFile); // the safe build's note: not used here
#else
	// liveshell.elf: right after the PS5 was turned on, the home screen is still starting up and a HEN's toolbox
	// takes longer to get in: a jailbreak + OnionHEN + LiveShell in the first minutes crashed the home screen;
	// 5 min after power-on it was fine (issue #16). Inject no earlier than 2 min after power-on (5 min after a
	// crash last time).
	{
		timespec up {};
		clock_gettime(CLOCK_MONOTONIC, &up);
		const bool crashed_before = exists(kEarlyCrashFile);
		const long kSettled       = crashed_before ? 300 : 120;
		if (crashed_before) {
			log("last time the home screen crashed soon after LiveShell joined it: waiting until 5 min after power-on");
		}
		if (up.tv_sec < kSettled) {
			log("the PS5 was turned on %ld s ago: waiting %ld s more before joining the home screen", static_cast<long>(up.tv_sec),
			    kSettled - static_cast<long>(up.tv_sec));
			for (long left = kSettled - up.tv_sec; left > 0 && g_running; --left) {
				sleep(1);
			}
		}
	}
#endif
	wait_for_hen_toolboxes(true); // autoload: the HEN loaded just before may still be putting its toolbox in
	pid_t last_pid = inject_shellui();
	if (last_pid < 0) {
		return 3;
	}
	{
		std::lock_guard<std::mutex> lock(g_ctl);
		g_injected = last_pid > 0;
	}
	start_thread(after_start_thread);
	// Picks saved before this build: give their tiles a background too (only where one is missing).
	{
		const std::string text = read_text("/data/LiveShell/games.txt", 64 * 1024);
		size_t            pos  = 0;
		while (pos < text.size()) {
			const size_t      end  = text.find('\n', pos);
			const std::string line = text.substr(pos, end == std::string::npos ? std::string::npos : end - pos);
			const size_t      eq   = line.find('=');
			if (eq != std::string::npos && eq > 0) {
				ensure_tile_background(line.substr(0, eq));
			}
			if (end == std::string::npos) {
				break;
			}
			pos = end + 1;
		}
	}
	mirror_games();
	start_thread(game_thread);
	start_thread(focus_thread);
	load_playlists();
	start_thread(user_thread);
	start_thread(cycle_thread);
	start_thread(autonext_thread);
	start_thread(recovery_thread);

	// Re-inject after ShellUI restarts. A restart soon after an injection means our module crashed
	// it: stop for good instead of crash-looping the console.
	time_t injected_at = time(nullptr);
	while (g_running) {
		sleep(5);
#ifndef LIVESHELL_FAST
		if (time(nullptr) - injected_at > kCrashWindowSec && exists(kEarlyCrashFile)) {
			unlink(kEarlyCrashFile);
			log("the home screen runs fine with LiveShell: back to the normal wait after power-on");
		}
#endif
		if (!g_running) {
			break;
		}
		pid_t current = onion_find_pid("SceShellUI");
		if (current <= 0 || current == last_pid) {
			continue;
		}
		const long alive = static_cast<long>(time(nullptr) - injected_at);
		log("ShellUI restarted: was %d, now %d (%ld s after injection)", static_cast<int>(last_pid),
		    static_cast<int>(current), alive);
		copy_shellui_log();
		// Rest mode restarts ShellUI itself (it went down 5 s after "going to rest", and our crash
		// guard stopped LiveShell for good, test v1.1-rc2). Not a crash: wait until the PS5 is awake,
		// then inject into the new ShellUI (OnionHEN re-injects after resume the same way).
		const bool by_rest = g_sleeping || time(nullptr) - g_rest_seen.load() < 60;
		if (by_rest) {
			log("ShellUI restarted by rest mode: injecting again once the PS5 is awake");
			while (g_running && g_sleeping) {
				sleep(1);
			}
			if (!g_running) {
				break;
			}
			sleep(10); // as OnionHEN after a resume (resume_reinject_delay_seconds=10)
			const pid_t now = onion_find_pid("SceShellUI");
			if (now > 0) {
				current = now;
			}
		}
		if (g_planned_restart.exchange(false)) {
			log("ShellUI restarted by LiveShell (old module cleared): injecting again");
		} else if (!by_rest && alive < kCrashWindowSec) {
#ifndef LIVESHELL_FAST
			write_text(kEarlyCrashFile, std::to_string(alive) + "\n"); // next start waits longer after power-on
#endif
			// Once per session: the home screen may simply have still been starting up. Give the new one a minute,
			// then try again (it used to stop until the ELF was loaded again).
			static bool retried = false;
			if (retried) {
				log("ShellUI died %ld s after injection again: treating it as a crash, not re-injecting", alive);
				notify("LiveShell Engine stopped: the home screen crashed. Log: /data/LiveShell/liveshell.log");
				break;
			}
			retried = true;
			log("ShellUI died %ld s after injection: trying once more in 60 s", alive);
			for (int k = 0; k < 60 && g_running; ++k) {
				sleep(1);
			}
			const pid_t now = onion_find_pid("SceShellUI");
			if (now > 0) {
				current = now;
			}
		}
		sleep(3); // let the new ShellUI settle
		wait_for_hen_toolboxes(false);
		{
			std::lock_guard<std::mutex> lock(g_ctl);
			g_injected = false; // the new ShellUI has no module yet: no waiting for it to let go
			std::string error;
			apply_locked(error); // fresh sandbox: mount the window again
		}
		last_pid    = inject_shellui();
		injected_at = time(nullptr);
		if (last_pid <= 0) {
			break;
		}
		std::lock_guard<std::mutex> lock(g_ctl);
		g_injected = true;
	}

	copy_shellui_log();
	// With OnionHEN running, restarting ShellUI would take OnionHEN's toolbox down too. Soft stop
	// instead: video off, looks off, folder unmounted; the idle module stays parked in ShellUI and
	// the next start reuses it (the marker stays, so no second injection).
	const pid_t ui    = onion_find_pid("SceShellUI");
	const bool  onion = onion_daemon_answers() || (ui > 0 && read_pid_file(kOnionToolbox) == ui);
	if (g_stop_requested && onion) {
		write_text(kDimFile, "0\n");
		write_text(kLooksFile, "0 0 0 0\n");
		write_text(kParallaxFile, "0\n");
		write_text(kPathFile, "off\n");
		if (!wait_shellui_stopped(8000)) {
			log("soft stop: ShellUI still holds the video (%s)", shellui_status().c_str());
		}
		unmount_window_everywhere();
		log("LiveShell stopped (soft: OnionHEN keeps running, the idle module stays in ShellUI)");
		if (!g_replaced) {
			notify("LiveShell Engine stopped."); // not when a newer LiveShell takes over (it says it started)
		}
		_exit(0); // see below
	}
	write_text(kPathFile, "off\n");
	if (g_stop_requested) {
		restart_shellui();
		sleep(2);
	}
	unmount_window_everywhere();
	unlink(kOurMarker);
	unlink(kStatusFile);
	ui_forget_status();
	log("LiveShell stopped");
	if (!g_replaced) {
		notify("LiveShell Engine stopped."); // not when a newer LiveShell takes over (it says it started)
	}
	// _exit, not return: with libSceNet/libSceHttp linked, a normal exit hung in their
	// shutdown and the process stayed alive holding ports 9049/9050/9051 - the next LiveShell got a white
	// window and no shutdown (v1.3 test).
	_exit(0);
}
