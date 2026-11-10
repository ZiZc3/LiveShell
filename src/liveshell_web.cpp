/*
 * liveshell_web.cpp - the LiveShell window: a small HTTP server on kWebPort (the home-screen tile
 * opens it in the browser view). The page is liveshell_page.html, embedded at build time. GPL-3.0.
 *
 *   GET /               the page
 *   GET /icon.png       app icon
 *   GET /thumb?i=N      <clip>.png next to the clip (a still the page grabbed once), 404 if none
 *   GET /video?i=N      the clip itself, with Range support (the page's live preview)
 *   GET /api/state      {"enabled","status","current","videos":[...]}
 *   GET /api/select?i=N play clip N (index into videos)
 *   GET /api/fav?i=N&v=1 favorite (pinned at the top) / v=0 not
 *   GET /api/on|off     wallpaper on / off
 *   GET /api/dim?v=N    darken the video by N % (0..80) so the home screen stays readable
 *   GET /api/volume?v=N sound of clips that have it, N % (0..100)
 */
#include "liveshell.hpp"

#include <algorithm>
#include <atomic>
#include <ctime>
#include <arpa/inet.h>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <mutex>
#include <netinet/in.h>
#include <pthread.h>
#include <string>
#include <strings.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>

extern "C" {
extern const uint8_t liveshell_icon_png[];
extern const uint8_t liveshell_icon_png_end[];
extern const uint8_t liveshell_page_html[];
extern const uint8_t liveshell_page_html_end[];
extern const uint8_t liveshell_remote_html[];
extern const uint8_t liveshell_remote_html_end[];
}

__asm__(".section .rodata\n"
        ".global liveshell_page_html\n"
        ".global liveshell_page_html_end\n"
        ".align  16\n"
        "liveshell_page_html:\n"
        ".incbin \"" LIVESHELL_PAGE_HTML "\"\n"
        "liveshell_page_html_end:\n"
        ".previous\n");

// Page for phones / PCs on the LAN (upload, play, delete, on/off): liveshell_remote.html.
__asm__(".section .rodata\n"
        ".global liveshell_remote_html\n"
        ".global liveshell_remote_html_end\n"
        ".align  16\n"
        "liveshell_remote_html:\n"
        ".incbin \"" LIVESHELL_REMOTE_HTML "\"\n"
        "liveshell_remote_html_end:\n"
        ".previous\n");

namespace liveshell {
namespace {

constexpr size_t kMaxThumb = 2 * 1024 * 1024;
constexpr long   kMinThumb = 3000; // smaller = a blank (black) frame: ignore it, grab again

std::string json_str(const std::string& s) {
	std::string out = "\"";
	for (const char c : s) {
		if (c == '"' || c == '\\') {
			out += '\\';
			out += c;
		} else if (c == '\n') {
			out += "\\n"; // games.txt lines: dropped before, so the picker never marked the chosen clip
		} else if (static_cast<unsigned char>(c) >= 0x20) {
			out += c;
		}
	}
	return out + "\"";
}

std::string state_json() {
	const State st = get_state();
	std::string j  = std::string("{\"enabled\":") + (st.enabled ? "true" : "false") + ",\"dim\":" + std::to_string(st.dim) + ",\"volume\":" + std::to_string(st.volume) +
	                ",\"looks\":[" + std::to_string(st.looks[0]) + "," + std::to_string(st.looks[1]) + "," + std::to_string(st.looks[2]) + "," + std::to_string(st.looks[3]) + "]" + ",\"shuffle\":" + (st.shuffle ? "true" : "false") + ",\"mainvideo\":" + (st.main_video ? "true" : "false") + ",\"gamevideos\":" + (st.game_videos ? "true" : "false") + ",\"gamepause\":" + (st.game_pause ? "true" : "false") + ",\"menuhide\":" + (st.menu_hide ? "true" : "false") + ",\"storeonly\":" + (st.store_only ? "true" : "false") + ",\"parallax\":" + (st.parallax ? "true" : "false") + ",\"automatch\":" + (st.auto_match ? "true" : "false") + ",\"resume\":" + (st.resume ? "true" : "false") + ",\"launchfx\":" + std::to_string(st.launchfx) + ",\"autonext\":" + std::to_string(st.autonext) + ",\"plbak\":" + (st.pl_bak ? "true" : "false") + ",\"tint\":" + std::to_string(st.tint) + ",\"playlist\":" + json_str(st.playlist) + ",\"users\":" + users_json() + ",\"gamehide\":" + (st.game_hide ? "true" : "false") +
	                ",\"ip\":" + json_str(st.ip) + ",\"port\":" + std::to_string(kWebPort) + ",\"games\":" + json_str(games_text()) + ",\"game\":" + json_str(st.game) + ",\"status\":" + json_str(st.status) + ",\"current\":" + json_str(st.current) + ",\"main4k\":false,\"videos\":[";
	const std::vector<std::string> fav = favorites();
	for (size_t i = 0; i < st.videos.size(); ++i) {
		const Video& v = st.videos[i];
		j += (i ? ",{" : "{");
		struct stat fs {};
		const long long size = stat(v.path.c_str(), &fs) == 0 ? static_cast<long long>(fs.st_size) : 0;
		struct stat ts {};
		const std::string cover = v.path.substr(0, v.path.rfind('.')) + ".png";
		const bool        thumb = stat(cover.c_str(), &ts) == 0 && ts.st_size >= kMinThumb;
		j += "\"name\":" + json_str(v.name) + ",\"where\":" + json_str(v.where) + ",\"path\":" + json_str(v.path) +
		     ",\"size\":" + std::to_string(size) + ",\"thumb\":" + (thumb ? "true" : "false") +
		     ",\"fav\":" + (std::find(fav.begin(), fav.end(), v.path) != fav.end() ? "true" : "false") +
		     ",\"why\":" + json_str(clip_problem(v.path)) + ",\"k4\":" + (clip_is_big(v.path) ? "true" : "false") + ",\"res\":" + json_str(clip_res(v.path)) + ",\"snd\":" + (clip_has_audio(v.path) ? "true" : "false") + "}";
	}
	return j + "]}";
}

std::string result_json(bool ok, const std::string& error) {
	return ok ? "{\"ok\":true}" : "{\"ok\":false,\"error\":" + json_str(error) + "}";
}

void send_all(int fd, const void* data, size_t len) {
	const auto* p = static_cast<const uint8_t*>(data);
	while (len > 0) {
		const ssize_t n = send(fd, p, len, 0);
		if (n <= 0) {
			return;
		}
		p += n;
		len -= static_cast<size_t>(n);
	}
}

// cache = false: always asked again (the default); true: the browser keeps it a day (game icons).
void reply(int fd, const char* status, const char* type, const void* body, size_t len, bool cache = false) {
	char      head[256];
	const int n = snprintf(head, sizeof(head),
	                       "HTTP/1.1 %s\r\nContent-Type: %s\r\nContent-Length: %zu\r\n"
	                       "Cache-Control: %s\r\nConnection: close\r\n\r\n",
	                       status, type, len, cache ? "max-age=86400" : "no-store");
	send_all(fd, head, static_cast<size_t>(n));
	send_all(fd, body, len);
}

void reply_json(int fd, const std::string& json) {
	reply(fd, "200 OK", "application/json", json.data(), json.size());
}

void reply_404(int fd) {
	reply(fd, "404 Not Found", "text/plain", "not found", 9);
}

int index_arg(const std::string& query) {
	const size_t pos = query.find("i=");
	return pos == std::string::npos ? -1 : atoi(query.c_str() + pos + 2);
}

bool video_at(int i, Video& out) {
	const std::vector<Video> videos = list_videos();
	if (i < 0 || i >= static_cast<int>(videos.size())) {
		return false;
	}
	out = videos[static_cast<size_t>(i)];
	return true;
}

void serve_thumb(int fd, int i) {
	Video v;
	if (!video_at(i, v)) {
		reply_404(fd);
		return;
	}
	const std::string path = v.path.substr(0, v.path.rfind('.')) + ".png";
	struct stat       st {};
	if (stat(path.c_str(), &st) != 0 || st.st_size < kMinThumb || static_cast<size_t>(st.st_size) > kMaxThumb) {
		reply_404(fd);
		return;
	}
	std::string data(static_cast<size_t>(st.st_size), '\0');
	const int   f  = open(path.c_str(), O_RDONLY);
	const bool  ok = f >= 0 && read(f, &data[0], data.size()) == static_cast<ssize_t>(data.size());
	if (f >= 0) {
		close(f);
	}
	if (!ok) {
		reply_404(fd);
		return;
	}
	reply(fd, "200 OK", "image/png", data.data(), data.size());
}

// 4K stream with the index first (v1.4): a clip with its moov box at the END makes Sony's player read the end of
// the stream before the first frame (Luna: 1.2 s, the same clip with moov first 0.6 s). The stream is the same
// file with moov moved right after ftyp and its chunk offsets moved on by moov's size - built on the fly from the
// file (nothing on disk changes). Anything unusual: the file as it is.
struct FastStart {
	std::string path;
	long long   stamp = -1;
	long long   size = 0, head = 0, moov_at = 0, moov_len = 0; // head = the end of ftyp (where moov goes)
	std::string moov;                                           // patched moov; empty = serve the file as it is
};
std::mutex g_fs_lock;
std::atomic<long> g_page_seen {0}; // last /api/state from the console itself (our window)
FastStart  g_fs;

uint64_t be(const unsigned char* p, int n) {
	uint64_t v = 0;
	for (int k = 0; k < n; ++k) {
		v = (v << 8) | p[k];
	}
	return v;
}

// stco / co64 offsets in [head, moov_at) move on by add; containers are walked down to stbl.
bool patch_moov(std::string& m, size_t at, size_t end, long long head, long long moov_at, long long add) {
	while (at + 8 <= end) {
		auto*    p    = reinterpret_cast<unsigned char*>(&m[at]);
		uint64_t size = be(p, 4);
		size_t   hdr  = 8;
		if (size == 1) {
			if (at + 16 > end) {
				return false;
			}
			size = be(p + 8, 8);
			hdr  = 16;
		} else if (size == 0) {
			size = end - at;
		}
		if (size < hdr || at + size > end) {
			return false;
		}
		const std::string type(m, at + 4, 4);
		if (type == "trak" || type == "mdia" || type == "minf" || type == "stbl" || type == "edts" || type == "mvex") {
			if (!patch_moov(m, at + hdr, at + size, head, moov_at, add)) {
				return false;
			}
		} else if (type == "stco" || type == "co64") {
			const int    w = type == "stco" ? 4 : 8;
			if (at + hdr + 8 > at + size) {
				return false;
			}
			const uint64_t count = be(p + hdr + 4, 4);
			if (hdr + 8 + count * w > size) {
				return false;
			}
			for (uint64_t k = 0; k < count; ++k) {
				unsigned char* e = p + hdr + 8 + k * w;
				uint64_t       v = be(e, w);
				if (static_cast<long long>(v) >= head && static_cast<long long>(v) < moov_at) {
					v += static_cast<uint64_t>(add);
					if (w == 4 && v > 0xFFFFFFFFull) {
						return false; // would need co64: serve the file as it is
					}
				}
				for (int b = w - 1; b >= 0; --b) {
					e[b] = static_cast<unsigned char>(v & 0xFF);
					v >>= 8;
				}
			}
		}
		at += static_cast<size_t>(size);
	}
	return at == end;
}

// Fills fs for path (cached by size + date). fs.moov empty = the file already has moov first, or it is unusual.
void fast_start(const std::string& path, const struct stat& st, FastStart& fs) {
	const long long stamp = static_cast<long long>(st.st_size) * 31 + static_cast<long long>(st.st_mtime);
	if (g_fs.path == path && g_fs.stamp == stamp) {
		fs = g_fs;
		return;
	}
	fs       = FastStart {};
	fs.path  = path;
	fs.stamp = stamp;
	fs.size  = static_cast<long long>(st.st_size);
	const int f = open(path.c_str(), O_RDONLY);
	if (f >= 0) {
		long long     off = 0, mdat = -1;
		unsigned char h[16];
		while (off + 8 <= fs.size && pread(f, h, 16, off) >= 8) {
			long long size = static_cast<long long>(be(h, 4)), hdr = 8;
			if (size == 1) {
				size = static_cast<long long>(be(h + 8, 8));
				hdr  = 16;
			} else if (size == 0) {
				size = fs.size - off;
			}
			if (size < hdr || off + size > fs.size) {
				break;
			}
			if (off == 0 && memcmp(h + 4, "ftyp", 4) == 0) {
				fs.head = size;
			} else if (memcmp(h + 4, "mdat", 4) == 0 && mdat < 0) {
				mdat = off;
			} else if (memcmp(h + 4, "moov", 4) == 0) {
				if (mdat >= 0 && size <= 32 * 1024 * 1024) { // after the data: worth moving
					std::string m(static_cast<size_t>(size), '\0');
					if (pread(f, &m[0], m.size(), off) == static_cast<ssize_t>(m.size()) &&
					    patch_moov(m, static_cast<size_t>(hdr), m.size(), fs.head, off, size)) {
						fs.moov_at  = off;
						fs.moov_len = size;
						fs.moov     = m;
					}
				}
				break;
			}
			off += size;
		}
		close(f);
	}
	if (!fs.moov.empty()) {
		log("web: 4K stream of %s with its index first (%lld bytes moved)", path.c_str(), fs.moov_len);
	}
	g_fs = fs;
}

// Bytes [at, at+n) of the stream: ftyp | moov | what was between ftyp and moov | what came after moov.
ssize_t fast_read(int f, const FastStart& fs, char* out, size_t n, long long at) {
	if (fs.moov.empty()) {
		return pread(f, out, n, at);
	}
	size_t done = 0;
	while (done < n && at < fs.size) {
		long long seg_end, src;
		if (at < fs.head) {
			seg_end = fs.head;
			src     = at;
		} else if (at < fs.head + fs.moov_len) {
			const size_t k = static_cast<size_t>(at - fs.head);
			const size_t c = std::min(n - done, fs.moov.size() - k);
			memcpy(out + done, fs.moov.data() + k, c);
			done += c;
			at += static_cast<long long>(c);
			continue;
		} else if (at < fs.moov_at + fs.moov_len) {
			seg_end = fs.moov_at + fs.moov_len;
			src     = at - fs.moov_len; // the bytes between ftyp and the old moov, now after the new one
		} else {
			seg_end = fs.size;
			src     = at; // after the old moov: same place
		}
		const size_t  want = static_cast<size_t>(std::min<long long>(static_cast<long long>(n - done), seg_end - at));
		const ssize_t got  = pread(f, out + done, want, src);
		if (got <= 0) {
			break;
		}
		done += static_cast<size_t>(got);
		at += got;
	}
	return static_cast<ssize_t>(done);
}

// Video preview: WebKit only plays media from servers that answer Range requests (206).
void serve_video(int fd, int i, const char* request, bool log_it = false, bool fast = false) {
	Video v;
	struct stat st {};
	if (!video_at(i, v) || stat(v.path.c_str(), &st) != 0 || st.st_size <= 0) {
		reply_404(fd);
		return;
	}
	const long long size  = static_cast<long long>(st.st_size);
	long long       first = 0, last = size - 1;
	bool            range = false;
	if (const char* r = strcasestr(request, "\nRange: bytes=")) {
		r += 14;
		char* end = nullptr;
		if (*r == '-') { // suffix: last N bytes
			const long long n = strtoll(r + 1, nullptr, 10);
			first             = n > 0 && n < size ? size - n : 0;
		} else {
			first = strtoll(r, &end, 10);
			if (end != nullptr && *end == '-' && end[1] >= '0' && end[1] <= '9') {
				last = strtoll(end + 1, nullptr, 10);
			}
		}
		if (first < 0 || first >= size) {
			char      head[160];
			const int n = snprintf(head, sizeof(head),
			                       "HTTP/1.1 416 Range Not Satisfiable\r\nContent-Range: bytes */%lld\r\n"
			                       "Content-Length: 0\r\nConnection: close\r\n\r\n",
			                       size);
			send_all(fd, head, static_cast<size_t>(n));
			return;
		}
		if (last >= size) {
			last = size - 1;
		}
		range = true;
	}
	const int f = open(v.path.c_str(), O_RDONLY);
	if (f < 0) {
		reply_404(fd);
		return;
	}
	FastStart fs; // 4K stream: the index first (moov at the end otherwise)
	if (fast) {
		std::lock_guard<std::mutex> lock(g_fs_lock);
		fast_start(v.path, st, fs);
	}
	char      head[320];
	const int n = range ? snprintf(head, sizeof(head),
	                               "HTTP/1.1 206 Partial Content\r\nContent-Type: video/mp4\r\nAccept-Ranges: bytes\r\n"
	                               "Content-Range: bytes %lld-%lld/%lld\r\nContent-Length: %lld\r\nConnection: close\r\n\r\n",
	                               first, last, size, last - first + 1)
	                    : snprintf(head, sizeof(head),
	                               "HTTP/1.1 200 OK\r\nContent-Type: video/mp4\r\nAccept-Ranges: bytes\r\n"
	                               "Content-Length: %lld\r\nConnection: close\r\n\r\n",
	                               size);
	send_all(fd, head, static_cast<size_t>(n));
	static thread_local char buf[64 * 1024];
	long long at = first;
	long long left = last - first + 1;
	timeval   t0 {};
	gettimeofday(&t0, nullptr);
	int why = 0; // 0 done, 1 read, 2 send (closed / timed out)
	int err = 0;
	while (left > 0) {
		const size_t  want = left < static_cast<long long>(sizeof(buf)) ? static_cast<size_t>(left) : sizeof(buf);
		const ssize_t got  = fast_read(f, fs, buf, want, at);
		if (got <= 0) {
			why = 1;
			break;
		}
		if (send(fd, buf, static_cast<size_t>(got), 0) != got) {
			why = 2;
			err = errno;
			break; // end of file, or the browser closed the connection (normal when it seeks)
		}
		left -= got;
		at += got;
	}
	close(f);
	if (log_it) {
		timeval t1 {};
		gettimeofday(&t1, nullptr);
		const long ms = (t1.tv_sec - t0.tv_sec) * 1000 + (t1.tv_usec - t0.tv_usec) / 1000;
		log("web: home_bg %s bytes %lld-%lld: sent %lld in %ld ms, %s (errno %d)", range ? "range" : "full", first, last,
		    (last - first + 1) - left, ms, why == 0 ? "done" : why == 1 ? "read stopped" : "player stopped reading / closed", err);
	}
}

// POST /thumb?i=N: the page grabbed a still from the clip; keep it as <clip>.png so it is grabbed once.
void save_thumb(int fd, int i, const char* headers, const char* body, size_t have) {
	Video       v;
	const char* cl   = strcasestr(headers, "\nContent-Length:");
	const long  size = cl != nullptr ? strtol(cl + 16, nullptr, 10) : 0;
	if (!video_at(i, v) || size < kMinThumb || static_cast<size_t>(size) > kMaxThumb) {
		reply_json(fd, result_json(false, "bad thumbnail"));
		return;
	}
	std::string data(body, have < static_cast<size_t>(size) ? have : static_cast<size_t>(size));
	char        chunk[16 * 1024];
	while (data.size() < static_cast<size_t>(size)) {
		const ssize_t got = recv(fd, chunk, sizeof(chunk), 0);
		if (got <= 0) {
			reply_json(fd, result_json(false, "upload cut"));
			return;
		}
		data.append(chunk, static_cast<size_t>(got));
	}
	data.resize(static_cast<size_t>(size));
	const std::string path = v.path.substr(0, v.path.rfind('.')) + ".png";
	const int         f    = open(path.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0666);
	const bool ok = f >= 0 && write(f, data.data(), data.size()) == static_cast<ssize_t>(data.size());
	if (f >= 0) {
		close(f);
	}
	log("web: thumbnail %s (%zu bytes) %s", path.c_str(), data.size(), ok ? "saved" : "NOT saved");
	reply_json(fd, result_json(ok, "cannot write the thumbnail"));
}

std::string url_decode(const std::string& raw) {
	std::string out;
	for (size_t k = 0; k < raw.size(); ++k) {
		char c = raw[k];
		if (c == '%' && k + 2 < raw.size() && isxdigit(static_cast<unsigned char>(raw[k + 1])) &&
		    isxdigit(static_cast<unsigned char>(raw[k + 2]))) {
			c = static_cast<char>(strtol(raw.substr(k + 1, 2).c_str(), nullptr, 16));
			k += 2;
		} else if (c == '+') {
			c = ' ';
		}
		out += c;
	}
	return out;
}

// Upload from a phone / PC: POST /api/upload?name=<file>.mp4, raw body. Only plain file names,
// only .mp4, only into /data/LiveShell/video; written as .part and renamed when complete.
void save_upload(int fd, const std::string& query, const char* headers, const char* body, size_t have) {
	const size_t      at  = query.find("name=");
	const std::string raw = at == std::string::npos ? "" : url_decode(query.substr(at + 5, query.find('&', at) - (at + 5)));
	std::string       name;
	for (const char c : raw) {
		if (isalnum(static_cast<unsigned char>(c)) || c == '-' || c == '_' || c == '.') {
			name += c;
		} else if (c == ' ') {
			name += '-';
		}
	}
	while (!name.empty() && name[0] == '.') {
		name.erase(0, 1);
	}
	if (name.size() > 120) {
		name = name.substr(name.size() - 120);
	}
	const bool      is_mp4 = name.size() > 4 && strcasecmp(name.c_str() + name.size() - 4, ".mp4") == 0;
	const char*     cl     = strcasestr(headers, "\nContent-Length:");
	const long long size   = cl != nullptr ? strtoll(cl + 16, nullptr, 10) : 0;
	if (!is_mp4 || size <= 0 || size > 8LL * 1024 * 1024 * 1024) {
		reply_json(fd, result_json(false, "Only .mp4 files can be uploaded"));
		return;
	}
	const std::string path = "/data/LiveShell/video/" + name;
	const std::string part = path + ".part";
	const int         f    = open(part.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0666);
	if (f < 0) {
		reply_json(fd, result_json(false, "Cannot write to /data/LiveShell/video"));
		return;
	}
	log("upload %s: %lld bytes", name.c_str(), size);
	long long    done  = 0;
	bool         ok    = true;
	const size_t first = have < static_cast<size_t>(size) ? have : static_cast<size_t>(size);
	if (first > 0) {
		ok   = write(f, body, first) == static_cast<ssize_t>(first);
		done = static_cast<long long>(first);
	}
	static thread_local char chunk[256 * 1024];
	while (ok && done < size) {
		const size_t  want = size - done < static_cast<long long>(sizeof(chunk)) ? static_cast<size_t>(size - done) : sizeof(chunk);
		const ssize_t got  = recv(fd, chunk, want, 0);
		if (got <= 0) {
			ok = false;
			break;
		}
		ok = write(f, chunk, static_cast<size_t>(got)) == got;
		done += got;
	}
	close(f);
	if (!ok || done != size || rename(part.c_str(), path.c_str()) != 0) {
		unlink(part.c_str());
		log("upload %s: FAILED at %lld of %lld bytes", name.c_str(), done, size);
		reply_json(fd, result_json(false, "Upload stopped before the end"));
		return;
	}
	log("upload %s: done", name.c_str());
	reply_json(fd, result_json(true, ""));
}

bool from_lan(int fd) {
	sockaddr_in peer {};
	socklen_t   len = sizeof(peer);
	return getpeername(fd, reinterpret_cast<sockaddr*>(&peer), &len) == 0 && peer.sin_addr.s_addr != htonl(INADDR_LOOPBACK);
}

void handle(int fd) {
	char          buf[4096];
	const ssize_t n = recv(fd, buf, sizeof(buf) - 1, 0);
	if (n <= 0) {
		return;
	}
	buf[n] = 0;
	const bool post = strncmp(buf, "POST ", 5) == 0;
	if (!post && strncmp(buf, "GET ", 4) != 0) {
		reply(fd, "405 Method Not Allowed", "text/plain", "", 0);
		return;
	}
	const char*  head_end = strstr(buf, "\r\n\r\n");
	const char*  body     = head_end != nullptr ? head_end + 4 : buf + n;
	const size_t have     = static_cast<size_t>(buf + n - body);
	char* target = buf + (post ? 5 : 4);
	char* end    = strpbrk(target, " \r\n");
	const char* headers = "";
	if (end != nullptr) {
		*end    = 0;
		headers = end + 1;
	}
	std::string       path(target), query;
	const size_t      q = path.find('?');
	if (q != std::string::npos) {
		query = path.substr(q + 1);
		path.resize(q);
	}

	std::string error;
	if (post) {
		if (path == "/api/upload") {
			save_upload(fd, query, headers, body, have);
		} else if (path == "/api/avatar") { // ?id=<user id>, raw body: an (animated) PNG, at most 16 MB
			const char* cl   = strcasestr(headers, "\nContent-Length:");
			const long  size = cl != nullptr ? strtol(cl + 16, nullptr, 10) : 0;
			const size_t id  = query.find("id=");
			if (size <= 0 || size > 16 * 1024 * 1024 || id == std::string::npos) {
				reply_json(fd, result_json(false, size > 16 * 1024 * 1024 ? "The picture is too big (16 MB at most)" : "No picture"));
			} else {
				std::string data(body, have < static_cast<size_t>(size) ? have : static_cast<size_t>(size));
				static thread_local char chunk[64 * 1024];
				while (data.size() < static_cast<size_t>(size)) {
					const size_t  want = std::min(sizeof(chunk), static_cast<size_t>(size) - data.size());
					const ssize_t got  = recv(fd, chunk, want, 0);
					if (got <= 0) {
						break;
					}
					data.append(chunk, static_cast<size_t>(got));
				}
				std::string err = data.size() == static_cast<size_t>(size) ? "" : "Upload stopped before the end";
				const bool  ok  = err.empty() && save_avatar(atoi(query.c_str() + id + 3), data, err);
				const size_t nm = query.find("name=");
				if (ok) {
					const std::string kept = keep_apng(nm == std::string::npos ? "" : url_decode(query.substr(nm + 5, query.find('&', nm) - (nm + 5))), data);
					note_avatar_src(atoi(query.c_str() + id + 3), kept);
				}
				reply_json(fd, result_json(ok, err));
			}
		} else if (path == "/api/icon") { // ?name=<name>[&tid=<TITLE ID>], raw body: an APNG / GIF -> the icons library (+ that game's tile)
			const char* cl   = strcasestr(headers, "\nContent-Length:");
			const long  size = cl != nullptr ? strtol(cl + 16, nullptr, 10) : 0;
			if (size <= 0 || size > 16 * 1024 * 1024) {
				reply_json(fd, result_json(false, size > 16 * 1024 * 1024 ? "The picture is too big (16 MB at most)" : "No picture"));
			} else {
				std::string data(body, have < static_cast<size_t>(size) ? have : static_cast<size_t>(size));
				static thread_local char chunk[64 * 1024];
				while (data.size() < static_cast<size_t>(size)) {
					const size_t  want = std::min(sizeof(chunk), static_cast<size_t>(size) - data.size());
					const ssize_t got  = recv(fd, chunk, want, 0);
					if (got <= 0) {
						break;
					}
					data.append(chunk, static_cast<size_t>(got));
				}
				std::string err = data.size() == static_cast<size_t>(size) ? "" : "Upload stopped before the end";
				const bool  gif = data.compare(0, 4, "GIF8") == 0;
				const bool  png = data.size() > 40 && data.compare(1, 3, "PNG") == 0 && data.find("acTL") < 4096;
				if (err.empty() && !gif && !png) {
					err = "That is not an animated PNG or GIF";
				}
				const size_t      nm   = query.find("name="), id = query.find("tid=");
				const std::string kept = err.empty() ? keep_apng(nm == std::string::npos ? "" : url_decode(query.substr(nm + 5, query.find('&', nm) - (nm + 5))), data, true) : "";
				if (err.empty() && kept.empty()) {
					err = "Cannot write to the icons folder";
				}
				const bool ok = err.empty() && (id == std::string::npos || set_tile_from(query.substr(id + 4, 9), kept, err));
				reply_json(fd, result_json(ok, err));
			}
		} else if (path == "/thumb") {
			save_thumb(fd, index_arg(query), headers, body, have);
		} else if (path == "/api/playlists") { // the page's whole set of playlists (P/V lines)
			const char* cl   = strcasestr(headers, "\nContent-Length:");
			const long  size = cl != nullptr ? strtol(cl + 16, nullptr, 10) : 0;
			std::string data(body, have < static_cast<size_t>(std::max(0L, size)) ? have : static_cast<size_t>(std::max(0L, size)));
			char        chunk[16 * 1024];
			while (size > 0 && size <= 2 * 1024 * 1024 && data.size() < static_cast<size_t>(size)) {
				const ssize_t got = recv(fd, chunk, sizeof(chunk), 0);
				if (got <= 0) {
					break;
				}
				data.append(chunk, static_cast<size_t>(got));
			}
			const bool ok = size > 0 && size <= 2 * 1024 * 1024 && data.size() >= static_cast<size_t>(size) &&
			                set_playlists(data.substr(0, static_cast<size_t>(size)), error);
			reply_json(fd, result_json(ok, error.empty() ? "The playlists did not arrive" : error));
		} else {
			reply_404(fd);
		}
	} else if (path == "/api/log") {
		// Page-side problems (video preview, stills) end up in liveshell.log.
		const std::string raw = query.rfind("m=", 0) == 0 ? query.substr(2) : query;
		std::string       m;
		for (size_t k = 0; k < raw.size(); ++k) {
			char c = raw[k];
			if (c == '%' && k + 2 < raw.size() + 0 && isxdigit(static_cast<unsigned char>(raw[k + 1])) &&
			    isxdigit(static_cast<unsigned char>(raw[k + 2]))) {
				c = static_cast<char>(strtol(raw.substr(k + 1, 2).c_str(), nullptr, 16));
				k += 2;
			} else if (c == '+') {
				c = ' ';
			}
			m += static_cast<unsigned char>(c) < 0x20 ? '?' : c;
		}
		log("page: %s", m.substr(0, 300).c_str());
		reply_json(fd, result_json(true, error));
	} else if ((path == "/" || path == "/index.html") && from_lan(fd)) {
		// Opened from a phone / PC: the remote page (upload, play, delete, on/off).
		reply(fd, "200 OK", "text/html; charset=utf-8", liveshell_remote_html,
		      static_cast<size_t>(liveshell_remote_html_end - liveshell_remote_html));
	} else if (path == "/" || path == "/index.html" || path == "/ps5") {
		reply(fd, "200 OK", "text/html; charset=utf-8", liveshell_page_html,
		      static_cast<size_t>(liveshell_page_html_end - liveshell_page_html));
	} else if (path == "/icon.png") {
		reply(fd, "200 OK", "image/png", liveshell_icon_png,
		      static_cast<size_t>(liveshell_icon_png_end - liveshell_icon_png));
	} else if (path == "/video") {
		serve_video(fd, index_arg(query), headers);
	} else if (path.rfind("/uhd/", 0) == 0 && !from_lan(fd)) {
		// A 4K clip for the home screen's player (only from the console itself): Sony's player gets a UHD
		// decoder for a stream, not for a file path.
		const std::string        want = url_decode(path.substr(5));
		const std::vector<Video> vs   = list_videos();
		int                      at   = -1;
		for (size_t k = 0; k < vs.size() && at < 0; ++k) {
			if (vs[k].name == want) {
				at = static_cast<int>(k);
			}
		}
		timeval long_wait {60, 0}; // the player stops reading while its buffer is full: wait for it (10 s cut it)
		setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &long_wait, sizeof(long_wait));
		serve_video(fd, at, headers, false, true);
	} else if (path == "/thumb") {
		serve_thumb(fd, index_arg(query));
	} else if (path == "/api/state") {
		if (!from_lan(fd)) {
			g_page_seen = static_cast<long>(time(nullptr)); // our window on the PS5 polls every second
		}
		reply_json(fd, state_json());
	} else if (path == "/api/select") {
		Video v;
		const bool ok = video_at(index_arg(query), v) ? select_video(v.path, error) : (error = "No such video", false);
		log("web: select %s -> %s", v.path.c_str(), ok ? "ok" : error.c_str());
		reply_json(fd, result_json(ok, error));
	} else if (path == "/api/fav") {
		// /api/fav?i=N&v=1 (v=0: un-favorite)
		Video      v;
		const bool ok = video_at(index_arg(query), v);
		if (ok) {
			set_favorite(v.path, query.find("v=1") != std::string::npos);
		}
		reply_json(fd, result_json(ok, "No such video"));
	} else if (path == "/api/dim") {
		const size_t pos = query.find("v=");
		set_dim(pos == std::string::npos ? 25 : atoi(query.c_str() + pos + 2));
		reply_json(fd, result_json(true, error));
	} else if (path == "/api/playlists") {
		reply_json(fd, playlists_json());
	} else if (path == "/api/playlists/restore") {
		const bool ok = restore_playlists(error);
		reply_json(fd, result_json(ok, error));
	} else if (path == "/useravatar") { // ?id=<user id>: the PS5 profile picture
		const size_t      id  = query.find("id=");
		const std::string png = id == std::string::npos ? std::string() : user_avatar(atoi(query.c_str() + id + 3));
		if (png.empty()) {
			reply_404(fd);
		} else {
			reply(fd, "200 OK", "image/png", png.data(), png.size(), true);
		}
	} else if (path == "/avatar_anim") { // ?id=<user id>: the user's animated avatar (the page shows it)
		const size_t      id  = query.find("id=");
		const std::string png = id == std::string::npos ? std::string() : anim_avatar(atoi(query.c_str() + id + 3));
		if (png.empty()) {
			reply_404(fd);
		} else {
			reply(fd, "200 OK", "image/png", png.data(), png.size(), false);
		}
	} else if (path == "/api/apngs") { // the APNG library for "Choose Avatar"
		reply_json(fd, apngs_json(query.find("k=icons") != std::string::npos)); // ?k=icons: the animated tiles' library
	} else if (path == "/apng") { // ?p=<path>: one of them (the picker shows it)
		const size_t      at  = query.find("p=");
		const std::string png = at == std::string::npos ? std::string() : read_apng(url_decode(query.substr(at + 2, query.find('&', at) - (at + 2))));
		if (png.empty()) {
			reply_404(fd);
		} else {
			reply(fd, "200 OK", "image/png", png.data(), png.size(), true);
		}
	} else if (path == "/api/avatar_set") { // ?id=<user id>&p=<path>: that APNG as the user's avatar
		const size_t id = query.find("id="), at = query.find("p=");
		const bool   ok = id != std::string::npos && at != std::string::npos &&
		                set_avatar_from(atoi(query.c_str() + id + 3), url_decode(query.substr(at + 2, query.find('&', at) - (at + 2))), error);
		reply_json(fd, result_json(ok, error));
	} else if (path == "/apngthumb") { // ?p=<library file>: its small moving preview (the pickers)
		const size_t      at  = query.find("p=");
		const std::string png = at == std::string::npos ? std::string() : apng_thumb(url_decode(query.substr(at + 2, query.find('&', at) - (at + 2))));
		if (png.empty()) {
			reply_404(fd);
		} else {
			reply(fd, "200 OK", "image/png", png.data(), png.size(), true);
		}
	} else if (path == "/api/tile_set") { // ?tid=<TITLE ID>&p=<library file>: that animation on the game's tile
		const size_t id = query.find("tid="), at = query.find("p=");
		const bool   ok = id != std::string::npos && at != std::string::npos &&
		                set_tile_from(query.substr(id + 4, 9), url_decode(query.substr(at + 2, query.find('&', at) - (at + 2))), error);
		reply_json(fd, result_json(ok, error));
	} else if (path == "/api/tile_del") { // ?tid=<TITLE ID>: the tile's own icon again
		const size_t id = query.find("tid=");
		reply_json(fd, result_json(id != std::string::npos && delete_tile(query.substr(id + 4, 9)), "No animated tile"));
	} else if (path == "/api/tiles") { // {"<TITLE ID>":"<library file>",..}
		reply_json(fd, tiles_json());
	} else if (path == "/api/avatar_del") { // ?id=<user id>: back to the PSN avatar
		const size_t id = query.find("id=");
		reply_json(fd, result_json(id != std::string::npos && delete_avatar(atoi(query.c_str() + id + 3)), "No animated avatar"));
	} else if (path == "/api/user") { // ?id=<user id>&on=0|1
		const size_t id = query.find("id="), on = query.find("on=");
		const bool   ok = id != std::string::npos && set_user_on(atoi(query.c_str() + id + 3), on != std::string::npos && query[on + 3] == '1');
		reply_json(fd, result_json(ok, error));
	} else if (path == "/api/tint") { // ?v=0..5
		const size_t v = query.find("v=");
		set_tint(v == std::string::npos ? 0 : atoi(query.c_str() + v + 2));
		reply_json(fd, result_json(true, error));
	} else if (path == "/api/autonext") { // ?m=0|1|2
		const size_t m = query.find("m=");
		set_autonext(m == std::string::npos ? 0 : atoi(query.c_str() + m + 2));
		reply_json(fd, result_json(true, error));
	} else if (path == "/api/launchfx") { // ?m=0|1|2
		const size_t m = query.find("m=");
		set_launchfx(m == std::string::npos ? 0 : atoi(query.c_str() + m + 2));
		reply_json(fd, result_json(true, error));
	} else if (path == "/api/volume") {
		const size_t pos = query.find("v=");
		set_volume(pos == std::string::npos ? 100 : atoi(query.c_str() + pos + 2));
		reply_json(fd, result_json(true, error));
	} else if (path == "/api/look") {
		// /api/look?k=bottom&v=2
		const size_t k = query.find("k="), v = query.find("v=");
		const std::string key = k == std::string::npos ? "" : query.substr(k + 2, query.find('&', k) - (k + 2));
		set_look(key, v == std::string::npos ? 0 : atoi(query.c_str() + v + 2));
		reply_json(fd, result_json(true, error));
	} else if (path == "/api/games") {
		// The PS Store tile first: it can have its own video and animated tile like any game (v1.7.0)
		std::string j = "[{\"tid\":\"NPXS40047\",\"name\":\"PlayStation Store\",\"clip\":" + json_str(saved_game_clip("NPXS40047")) + "}";
		for (const Game& g : list_games()) {
			if (g.tid == "NPXS40047") {
				continue;
			}
			j += (j.size() > 1 ? "," : "");
			j += "{\"tid\":" + json_str(g.tid) + ",\"name\":" + json_str(g.name) + ",\"clip\":" + json_str(saved_game_clip(g.tid)) + "}";
		}
		reply_json(fd, j + "]");
	} else if (path == "/gameicon") {
		const size_t      t   = query.find("tid=");
		const std::string tid = t == std::string::npos ? "" : query.substr(t + 4, 9);
		std::string       png = tid == "NPXS40047" ? "/system_ex/rnps/apps/NPXS40047/appdb/default/icon0.png" : "/user/appmeta/" + tid + "/icon0.png";
		struct stat       ps {};
		if (stat(png.c_str(), &ps) != 0) {
			png = "/user/appmeta/external/" + tid + "/icon0.png"; // a game on extended storage
		}
		if (stat(png.c_str(), &ps) != 0) {
			png = "/user/app/" + tid + "/sce_sys/icon0.png"; // homebrew tiles: no appmeta folder
		}
		struct stat       st {};
		std::string       data;
		if (is_title_id(tid.c_str()) && stat(png.c_str(), &st) == 0 && st.st_size > 0 && st.st_size < 4 * 1024 * 1024) {
			data.resize(static_cast<size_t>(st.st_size));
			const int f = open(png.c_str(), O_RDONLY);
			size_t    got = 0;
			if (f >= 0) { // in pieces: the PS Store's icon (a system folder) never came back in one read
				while (got < data.size()) {
					const ssize_t n = read(f, &data[got], data.size() - got);
					if (n <= 0) {
						break;
					}
					got += static_cast<size_t>(n);
				}
				close(f);
			}
			if (got != data.size()) {
				data.clear();
			}
		}
		if (data.empty() && tid == "NPXS40047") { // once: why the PS Store icon could not be read
			static bool told = false;
			if (!told) {
				told        = true;
				const int e = stat(png.c_str(), &st) == 0 ? 0 : errno;
				log("library: PS Store icon %s not readable (stat errno %d, size %lld)", png.c_str(), e, static_cast<long long>(e == 0 ? st.st_size : -1));
			}
		}
		if (data.empty()) {
			reply_404(fd);
		} else {
			reply(fd, "200 OK", "image/png", data.data(), data.size(), true); // kept a day: not fetched on every visit
		}
	} else if (path == "/api/gamebg") {
		// /api/gamebg?tid=PPSA01234&i=N  (i=-1: main wallpaper)
		const size_t t = query.find("tid="), k = query.find("i=");
		std::string tid = t == std::string::npos ? "" : query.substr(t + 4, query.find('&', t) - (t + 4));
		tid.erase(std::remove_if(tid.begin(), tid.end(), [](char c) { return !isalnum(static_cast<unsigned char>(c)); }), tid.end());
		Video v;
		const int i = k == std::string::npos ? -1 : atoi(query.c_str() + k + 2);
		const bool  ok  = !tid.empty() && (i < 0 || video_at(i, v));
		std::string err = "Unknown game or video";
		bool        big = ok && i >= 0 && refuse_4k(v.path, err); // bigger than 4K (notifies)
		if (ok && !big) {
			set_game_background(tid, i < 0 ? std::string() : v.path);
		}
		reply_json(fd, result_json(ok && !big, err));
	} else if (path == "/api/set") {
		// /api/set?k=shuffle&v=1
		const size_t k = query.find("k="), v = query.find("v=");
		const std::string key = k == std::string::npos ? "" : query.substr(k + 2, query.find('&', k) - (k + 2));
		const bool ok = set_option(key, v != std::string::npos && query[v + 2] == '1', error);
		reply_json(fd, result_json(ok, error));
	} else if (path == "/api/delete") {
		Video v;
		const bool ok = video_at(index_arg(query), v) ? delete_video(v.path, error) : (error = "No such video", false);
		reply_json(fd, result_json(ok, error));
	} else if (path == "/api/reset") {
		const bool ok = reset_settings(error);
		reply_json(fd, result_json(ok, error));
	} else if (path == "/api/shutdown") {
		reply_json(fd, result_json(true, error));
		request_shutdown();
	} else if (path == "/api/on" || path == "/api/off") {
		const bool on = path == "/api/on";
		const bool ok = set_enabled(on, error);
		log("web: %s -> %s", on ? "on" : "off", ok ? "ok" : error.c_str());
		reply_json(fd, result_json(ok, error));
	} else {
		reply_404(fd);
	}
}

void* connection_thread(void* arg) {
	const int c = static_cast<int>(reinterpret_cast<intptr_t>(arg));
	handle(c);
	close(c);
	return nullptr;
}

int open_web_port() {
	const int s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0) {
		log("web: socket failed (errno %d)", errno);
		return -1;
	}
	int on = 1;
	setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));
	sockaddr_in addr     = {};
	addr.sin_family      = AF_INET;
	addr.sin_port        = htons(kWebPort);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);
	if (bind(s, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) != 0 || listen(s, 8) != 0) {
		log("web: port %d unavailable (errno %d)", kWebPort, errno);
		close(s);
		return -1;
	}
	timeval tv {1, 0}; // accept wakes up every second: rest mode / reopen checks
	setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
	log("web: window on port %d", kWebPort);
	return s;
}

void* server_thread(void*) {
	// Rest mode kills listening sockets (user report: the window was dead after waking the PS5):
	// when accept keeps failing, open the port again.
	int s = -1, fails = 0, epoch = net_epoch();
	for (;;) {
		if (s >= 0 && epoch != net_epoch()) {
			log("web: reopening the window port after rest mode");
			close(s);
			s = -1;
		}
		if (s < 0) {
			epoch = net_epoch();
			s     = open_web_port();
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
			if (++fails >= 30) { // ~3 s of errors
				log("web: port broken (errno %d), reopening", errno);
				close(s);
				s = -1;
			}
			usleep(100 * 1000);
			continue;
		}
		fails = 0;
		timeval tv {10, 0};
		setsockopt(c, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
		setsockopt(c, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
		// One thread per connection: a video stream must not hold up the page's API calls.
		pthread_t t;
		if (pthread_create(&t, nullptr, connection_thread, reinterpret_cast<void*>(static_cast<intptr_t>(c))) == 0) {
			pthread_detach(t);
		} else {
			handle(c);
			close(c);
		}
	}
	return nullptr;
}

} // namespace

// The LiveShell window is open on the PS5: its page asked for the state in the last 3 s.
bool page_open() {
	return static_cast<long>(time(nullptr)) - g_page_seen.load() <= 3;
}

void start_web_server() {
	pthread_t t;
	if (pthread_create(&t, nullptr, server_thread, nullptr) == 0) {
		pthread_detach(t);
	} else {
		log("web: thread start failed");
	}
}

} // namespace liveshell
