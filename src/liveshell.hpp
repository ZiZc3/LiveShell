// LiveShell daemon: shared declarations (daemon, web window, home-screen tile). GPL-3.0.
#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace liveshell {

constexpr int         kWebPort  = 9050;
constexpr int         kStopPort = 9049;
constexpr const char* kWebUrl   = "http://127.0.0.1:9050/";

void log(const char* fmt, ...) __attribute__((format(printf, 1, 2)));
void notify(const char* text);       // system icon
void notify_plain(const char* text); // text only (debug style)

struct Video {
	std::string path;   // real path, e.g. /data/LiveShell/video/x.mp4
	std::string name;   // file name
	std::string where;  // "Internal" or "USB 1"..
};

struct Game {
	std::string tid;   // e.g. PPSA01234
	std::string name;  // title from param.json / param.sfo
};

struct State {
	bool               enabled = true;
	int                dim     = 25; // % black over the video (home screen readability)
	int                volume  = 100; // % sound of clips that have it
	int                looks[4] = {0, 0, 0, 0}; // bottom fade, top fade, vignette, haze
	std::string        ip;                      // console LAN address (remote page on phone / PC)
	bool               shuffle    = false; // random clip on every start
	bool               main_video = true;  // off = only tiles with their own video
	bool               game_videos = true; // off = per-game videos ignored
	bool               game_pause = true;  // no video while a game runs
	bool               menu_hide  = true;  // hide the video in Settings / system apps
	bool               store_only = false; // video only on the PS Store tile
	bool               parallax   = false; // nudge the video when moving between home tiles
	bool               resume     = false; // Resume after a game
	int                launchfx   = 0;
	int                autonext   = 0;     // Auto-next: 0 off, 1 in order, 2 shuffle
	bool               pl_bak     = false; // playlists.bak exists: "Undo last change"
	int                tint       = 0;     // Picture -> Colour     // game launch effect: 0 fade, 1 dive, 2 pull back
	bool               auto_match = false; // not used in this source
	bool               game_hide  = false; // no video on the home screen while a game is open
	std::string        playlist;           // the playlist that is on ("" = none)
	std::string        game;               // title id of the running game ("" = none)
	std::string        current;  // real path of the chosen clip ("" = none)
	std::string        status;   // ShellUI status line: playing / stopped / failed / starting
	std::vector<Video> videos;
};

std::vector<Video> list_videos();
State              get_state();
// Pick a clip / switch on or off. Safe to call from any thread; blocks until ShellUI let go of
// the old clip (a few seconds at most). Returns false with a reason on failure.
bool select_video(const std::string& path, std::string& error);
bool set_enabled(bool on, std::string& error);
void set_launchfx(int mode);
void set_autonext(int mode);                            // Auto-next: 0 off, 1 in order, 2 shuffle
void set_tint(int t);
bool restore_playlists(std::string& error);            // Playlists: undo the last change (swap with playlists.bak)                                   // Picture -> Colour: 0 neutral .. 5 violet                            // game launch effect: 0 fade, 1 dive, 2 pull back
std::string playlists_json();                           // [{"name":..,"on":..,"every":..,"shuffle":..,"videos":[paths]},..]
bool set_playlists(const std::string& text, std::string& error); // the page's whole set (P/V lines)
bool set_user_on(int id, bool on);                      // Users: LiveShell for this console user or not
std::string users_json();                               // [{"id":..,"name":"..","on":true,"now":true},..]
std::string user_avatar(int id);                        // the user's profile picture (PNG, "" = none)
bool        save_avatar(int id, const std::string& png, std::string& error); // the user's animated avatar (PNG)
bool        apng_rebuild(const std::string& in, std::string& anim, std::string& still, std::string& error, uint32_t max_side = 512); // liveshell_apng.cpp
std::string apng_thumb(const std::string& path);         // a small moving preview of a library file (cached; "" = not allowed)
bool        set_tile_from(const std::string& tid, const std::string& path, std::string& error); // animated game tile from the library
bool        delete_tile(const std::string& tid);       // the tile's own icon again
std::string tiles_json();                              // {"<TITLE ID>":"<library file>",..}
bool        delete_avatar(int id);
std::string anim_avatar(int id);                        // the user's animated avatar file ("" = none)
std::string apngs_json(bool icons = false);             // the APNG library (avatars, or icons = animated tiles; storage + USB): [{"path","name","where","size"},..]
std::string read_apng(const std::string& path);         // one of them ("" = not allowed / not there)
bool        set_avatar_from(int id, const std::string& path, std::string& error);
std::string keep_apng(const std::string& name, const std::string& png, bool icons = false); // an upload into the library (avatars or icons; its path)
void        note_avatar_src(int id, const std::string& from);          // the library file a user's avatar came from
void set_dim(int percent); // 0..80
// Bumped after the PS5 wakes from rest mode: every listening socket closes and opens again.
int  net_epoch();
void set_volume(int percent); // 0..100
void set_look(const std::string& key, int level); // "bottom", "top", "vignette", "haze"; 0..2
bool set_option(const std::string& key, bool on, std::string& error); // "shuffle", "gamepause", "menuhide", "parallax"
bool delete_video(const std::string& path, std::string& error);
bool reset_settings(std::string& error);
void request_shutdown(); // same as the stop port: payload ends, ShellUI restarts clean
void* game_thread(void*);
// Per-game backgrounds (v1.1)
std::string games_text();                                          // games.txt contents
void        set_game_background(const std::string& tid, const std::string& path); // "" = main wallpaper
std::vector<Game> list_games();                   // installed games (/user/appmeta)
std::string       game_clip(const std::string& tid); // its clip from games.txt ("" = main wallpaper)
std::string       saved_game_clip(const std::string& tid); // saved choice, even when per-game videos are off
bool              is_title_id(const char* name);
void*             focus_thread(void*);
void              mirror_games();
bool              clip_is_big(const std::string& path); // bigger than 1080p (4K: not supported)
std::string       clip_problem(const std::string& path); // why the PS5 will not play it ("" = plays / unknown)
std::string       clip_res(const std::string& path);     // "4K" / "2K" / "FHD" / "HD" / "" (list badges)
bool              clip_has_audio(const std::string& path); // it has a sound track (the list's sound badge)
std::vector<std::string> favorites();                // favorite clip paths (pinned at the top of the list)
void              set_favorite(const std::string& path, bool on);
bool              refuse_4k(const std::string& path, std::string& error); // 4K: not supported (notifies)
void              write_game_open(); // ShellUI hint for "Hide while a game is open"; caller holds g_ctl
void              write_fast_map(); // ShellUI's fast-switch map; caller holds g_ctl

void start_web_server();
bool page_open(); // the LiveShell window's page is polling (it is open on the PS5)

// Home-screen tile that opens kWebUrl. Returns 1 = newly added, 0 = was already there, -1 = failed.
int install_tile();

} // namespace liveshell
