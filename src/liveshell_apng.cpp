// LiveShell Engine - animated avatars: an APNG or GIF rebuilt for the PS5's image box (v1.6.0).
//
// Many APNG makers store only the changed part of a frame (a smaller frame at an offset, drawn over the last
// one, cleared or restored after). The home screen's decoder leaves those parts black: gaps that move. So the
// avatar is rebuilt here: every frame composed in full (dispose / blend as the file says), cut to a centred
// square, at most kMaxSide pixels, and written again as an APNG of whole frames (and its first frame as a
// plain PNG: shown while the animation decodes). A GIF is read the same way and comes out as such an APNG.
// PNG: 8-bit grey / RGB / palette / grey+alpha / RGBA, not interlaced. Deflate / inflate: miniz (public domain).
#include "liveshell.hpp"
#include "miniz.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace liveshell {
namespace {

constexpr uint32_t kMaxSide    = 512;         // the biggest avatar the home screen draws is far smaller
constexpr uint64_t kMaxDecoded = 64ull << 20; // every frame stays decoded in the home screen's memory
const uint8_t      kSig[8]     = {0x89, 'P', 'N', 'G', '\r', '\n', 0x1a, '\n'};

uint32_t rd32(const uint8_t* p) {
	return (static_cast<uint32_t>(p[0]) << 24) | (static_cast<uint32_t>(p[1]) << 16) | (static_cast<uint32_t>(p[2]) << 8) | p[3];
}

uint16_t rd16(const uint8_t* p) {
	return static_cast<uint16_t>((p[0] << 8) | p[1]);
}

void put32(std::string& s, uint32_t v) {
	s += static_cast<char>(v >> 24);
	s += static_cast<char>(v >> 16);
	s += static_cast<char>(v >> 8);
	s += static_cast<char>(v);
}

void put16(std::string& s, uint16_t v) {
	s += static_cast<char>(v >> 8);
	s += static_cast<char>(v);
}

void chunk(std::string& out, const char* type, const std::string& data) {
	put32(out, static_cast<uint32_t>(data.size()));
	const size_t at = out.size();
	out.append(type, 4);
	out += data;
	put32(out, static_cast<uint32_t>(mz_crc32(MZ_CRC32_INIT, reinterpret_cast<const unsigned char*>(out.data() + at), data.size() + 4)));
}

// One RGBA picture (side x side) as a zlib stream of filtered rows (Sub filter: small, fast).
bool encode(const std::vector<uint8_t>& px, uint32_t side, std::string& z) {
	const size_t         row = static_cast<size_t>(side) * 4;
	std::vector<uint8_t> raw((row + 1) * side);
	for (uint32_t y = 0; y < side; ++y) {
		uint8_t*       o  = &raw[y * (row + 1)];
		const uint8_t* in = &px[y * row];
		o[0]              = 1;
		for (size_t i = 0; i < row; ++i) {
			o[1 + i] = static_cast<uint8_t>(in[i] - (i >= 4 ? in[i - 4] : 0));
		}
	}
	mz_ulong n = mz_compressBound(static_cast<mz_ulong>(raw.size()));
	z.resize(n);
	if (mz_compress2(reinterpret_cast<unsigned char*>(&z[0]), &n, raw.data(), static_cast<mz_ulong>(raw.size()), 6) != MZ_OK) {
		return false;
	}
	z.resize(n);
	return true;
}

// The centred square of the canvas' rectangle (cx, cy, cw, ch), scaled to side x side (area average when
// smaller, nearest when bigger).
void square(const std::vector<uint8_t>& canvas, uint32_t w, uint32_t cx, uint32_t cy, uint32_t cw, uint32_t ch, uint32_t side,
            std::vector<uint8_t>& out) {
	const uint32_t src = std::min(cw, ch), x0 = cx + (cw - src) / 2, y0 = cy + (ch - src) / 2;
	out.assign(static_cast<size_t>(side) * side * 4, 0);
	const double k = static_cast<double>(src) / side;
	for (uint32_t y = 0; y < side; ++y) {
		const uint32_t sy0 = static_cast<uint32_t>(y * k), sy1 = std::max(sy0 + 1, std::min(src, static_cast<uint32_t>((y + 1) * k)));
		for (uint32_t x = 0; x < side; ++x) {
			const uint32_t sx0 = static_cast<uint32_t>(x * k), sx1 = std::max(sx0 + 1, std::min(src, static_cast<uint32_t>((x + 1) * k)));
			uint32_t       sum[4] = {0, 0, 0, 0}, cnt = 0;
			for (uint32_t sy = sy0; sy < sy1; ++sy) {
				const uint8_t* p = &canvas[((static_cast<size_t>(y0) + sy) * w + x0 + sx0) * 4];
				for (uint32_t sx = sx0; sx < sx1; ++sx, p += 4, ++cnt) {
					sum[0] += p[0], sum[1] += p[1], sum[2] += p[2], sum[3] += p[3];
				}
			}
			uint8_t* o = &out[(static_cast<size_t>(y) * side + x) * 4];
			for (int c = 0; c < 4; ++c) {
				o[c] = static_cast<uint8_t>(sum[c] / std::max(cnt, 1u));
			}
		}
	}
}

// The new APNG: whole frames of the composed picture (fcTL: whole picture, no dispose, source).
struct Writer {
	uint32_t     w = 0, h = 0, side = 0, seq = 0, done = 0;
	uint32_t     max_side = kMaxSide; // smaller for the pickers' previews
	std::string *anim = nullptr, *still = nullptr;
	std::vector<uint8_t> out;

	bool begin(uint32_t width, uint32_t height, size_t frames, uint32_t plays, std::string& error) {
		w = width, h = height;
		side = std::min({w, h, max_side});
		while (side > 96 && static_cast<uint64_t>(side) * side * 4 * frames > kMaxDecoded) {
			side = side * 7 / 8; // long animations: smaller, so every frame fits in the home screen's memory
		}
		if (static_cast<uint64_t>(side) * side * 4 * frames > kMaxDecoded) {
			error = "Too many frames (" + std::to_string(frames) + "): make it shorter";
			return false;
		}
		std::string ihdr;
		put32(ihdr, side), put32(ihdr, side);
		ihdr += '\x08', ihdr += '\x06', ihdr += '\0', ihdr += '\0', ihdr += '\0';
		anim->assign(reinterpret_cast<const char*>(kSig), 8);
		chunk(*anim, "IHDR", ihdr);
		std::string actl;
		put32(actl, static_cast<uint32_t>(frames)), put32(actl, plays);
		chunk(*anim, "acTL", actl);
		still->assign(reinterpret_cast<const char*>(kSig), 8);
		chunk(*still, "IHDR", ihdr);
		return true;
	}

	bool add(const std::vector<uint8_t>& canvas, uint16_t dn, uint16_t dd, std::string& error) {
		square(canvas, w, 0, 0, w, h, side, out);
		std::string z;
		if (!encode(out, side, z)) {
			error = "The avatar could not be written";
			return false;
		}
		std::string fc;
		put32(fc, seq++), put32(fc, side), put32(fc, side), put32(fc, 0), put32(fc, 0);
		put16(fc, dn), put16(fc, dd ? dd : 100);
		fc += '\0', fc += '\0';
		chunk(*anim, "fcTL", fc);
		if (done++ == 0) {
			chunk(*anim, "IDAT", z);
			chunk(*still, "IDAT", z);
			chunk(*still, "IEND", "");
		} else {
			std::string fd;
			put32(fd, seq++);
			fd += z;
			chunk(*anim, "fdAT", fd);
		}
		return true;
	}

	void end() {
		chunk(*anim, "IEND", "");
	}
};

// ---- PNG / APNG ----

struct Frame {
	uint32_t w = 0, h = 0, x = 0, y = 0;
	uint16_t dn = 1, dd = 10;
	uint8_t  dispose = 0, blend = 0;
	std::string data; // the zlib stream (IDAT / fdAT data joined)
};

uint8_t paeth(int a, int b, int c) {
	const int p = a + b - c, pa = std::abs(p - a), pb = std::abs(p - b), pc = std::abs(p - c);
	return static_cast<uint8_t>(pa <= pb && pa <= pc ? a : pb <= pc ? b : c);
}

// One frame's pixels as RGBA (w * h * 4); false on a broken stream.
bool decode(const Frame& f, int ctype, const uint8_t* pal, int npal, const uint8_t* trns, int ntrns, std::vector<uint8_t>& rgba) {
	const int    ch  = ctype == 0 ? 1 : ctype == 2 ? 3 : ctype == 3 ? 1 : ctype == 4 ? 2 : 4;
	const size_t row = static_cast<size_t>(f.w) * ch;
	std::vector<uint8_t> raw((row + 1) * f.h);
	mz_ulong n = static_cast<mz_ulong>(raw.size());
	if (mz_uncompress(raw.data(), &n, reinterpret_cast<const unsigned char*>(f.data.data()), static_cast<mz_ulong>(f.data.size())) != MZ_OK ||
	    n != raw.size()) {
		return false;
	}
	std::vector<uint8_t> prev(row, 0), cur(row);
	rgba.assign(static_cast<size_t>(f.w) * f.h * 4, 0);
	for (uint32_t y = 0; y < f.h; ++y) {
		const uint8_t  ft = raw[y * (row + 1)];
		const uint8_t* in = &raw[y * (row + 1) + 1];
		for (size_t i = 0; i < row; ++i) {
			const int a = i >= static_cast<size_t>(ch) ? cur[i - ch] : 0, b = prev[i], c = i >= static_cast<size_t>(ch) ? prev[i - ch] : 0;
			cur[i]      = static_cast<uint8_t>(in[i] + (ft == 1 ? a : ft == 2 ? b : ft == 3 ? (a + b) / 2 : ft == 4 ? paeth(a, b, c) : 0));
		}
		uint8_t* o = &rgba[static_cast<size_t>(y) * f.w * 4];
		for (uint32_t x = 0; x < f.w; ++x, o += 4) {
			const uint8_t* p = &cur[static_cast<size_t>(x) * ch];
			if (ctype == 0) {
				o[0] = o[1] = o[2] = p[0];
				o[3] = ntrns >= 2 && rd16(trns) == p[0] ? 0 : 255;
			} else if (ctype == 2) {
				o[0] = p[0], o[1] = p[1], o[2] = p[2];
				o[3] = ntrns >= 6 && rd16(trns) == p[0] && rd16(trns + 2) == p[1] && rd16(trns + 4) == p[2] ? 0 : 255;
			} else if (ctype == 3) {
				const int k = p[0] < npal ? p[0] : 0;
				o[0] = pal[k * 3], o[1] = pal[k * 3 + 1], o[2] = pal[k * 3 + 2];
				o[3] = k < ntrns ? trns[k] : 255;
			} else if (ctype == 4) {
				o[0] = o[1] = o[2] = p[0];
				o[3] = p[1];
			} else {
				memcpy(o, p, 4);
			}
		}
		prev.swap(cur);
	}
	return true;
}

bool png_rebuild(const std::string& in, Writer& wr, std::string& error) {
	const uint8_t* b = reinterpret_cast<const uint8_t*>(in.data());
	uint32_t       w = 0, h = 0, plays = 0;
	int            depth = 0, ctype = -1, interlace = 0, npal = 0, ntrns = 0;
	uint8_t        pal[768] {}, trns[256] {};
	std::vector<Frame> frames;
	bool           animated = false, seen_idat = false, idat_is_frame = false;
	Frame          plain; // a plain PNG / the default image
	for (size_t at = 8; at + 12 <= in.size();) {
		const uint32_t len = rd32(b + at);
		if (len > in.size() - at - 12) {
			error = "The picture file is cut off";
			return false;
		}
		const char*    t = reinterpret_cast<const char*>(b + at + 4);
		const uint8_t* d = b + at + 8;
		if (!memcmp(t, "IHDR", 4) && len >= 13) {
			w = rd32(d), h = rd32(d + 4), depth = d[8], ctype = d[9], interlace = d[12];
		} else if (!memcmp(t, "PLTE", 4)) {
			npal = static_cast<int>(std::min<uint32_t>(len, 768) / 3);
			memcpy(pal, d, static_cast<size_t>(npal) * 3);
		} else if (!memcmp(t, "tRNS", 4)) {
			ntrns = static_cast<int>(std::min<uint32_t>(len, 256));
			memcpy(trns, d, static_cast<size_t>(ntrns));
		} else if (!memcmp(t, "acTL", 4) && len >= 8) {
			animated = true;
			plays    = rd32(d + 4);
		} else if (!memcmp(t, "fcTL", 4) && len >= 26) {
			Frame f;
			f.w = rd32(d + 4), f.h = rd32(d + 8), f.x = rd32(d + 12), f.y = rd32(d + 16);
			f.dn = rd16(d + 20), f.dd = rd16(d + 22), f.dispose = d[24], f.blend = d[25];
			if (!seen_idat) {
				idat_is_frame = true;
			}
			frames.push_back(f);
		} else if (!memcmp(t, "IDAT", 4)) {
			seen_idat = true;
			plain.data.append(reinterpret_cast<const char*>(d), len);
			if (idat_is_frame && frames.size() == 1) {
				frames[0].data.append(reinterpret_cast<const char*>(d), len);
			}
		} else if (!memcmp(t, "fdAT", 4) && len > 4 && !frames.empty()) {
			frames.back().data.append(reinterpret_cast<const char*>(d + 4), len - 4);
		} else if (!memcmp(t, "IEND", 4)) {
			break;
		}
		at += 12 + len;
	}
	if (w == 0 || h == 0 || w > 4096 || h > 4096 || ctype < 0) {
		error = "The picture's size could not be read";
		return false;
	}
	if (depth != 8 || interlace != 0 || ctype == 1 || ctype == 5 || ctype > 6) {
		error = "Only 8-bit, non-interlaced PNGs work (16-bit and interlaced do not)";
		return false;
	}
	if (!animated || frames.empty()) { // a plain PNG: one frame
		plain.w = w, plain.h = h;
		frames.assign(1, plain);
	}
	frames.erase(std::remove_if(frames.begin(), frames.end(), [&](const Frame& f) {
		             return f.data.empty() || f.w == 0 || f.h == 0 || f.x + f.w > w || f.y + f.h > h;
	             }),
	             frames.end());
	if (frames.empty()) {
		error = "The animation's frames could not be read";
		return false;
	}
	if (!wr.begin(w, h, frames.size(), plays, error)) {
		return false;
	}
	std::vector<uint8_t> canvas(static_cast<size_t>(w) * h * 4, 0), saved, px;
	for (size_t i = 0; i < frames.size(); ++i) {
		const Frame& f = frames[i];
		if (!decode(f, ctype, pal, npal, trns, ntrns, px)) {
			error = "Frame " + std::to_string(i + 1) + " of the animation is broken";
			return false;
		}
		const uint8_t dispose = i == 0 && f.dispose == 2 ? 1 : f.dispose;
		if (dispose == 2) {
			saved = canvas;
		}
		for (uint32_t y = 0; y < f.h; ++y) { // draw the frame on the canvas
			uint8_t*       c = &canvas[((static_cast<size_t>(f.y) + y) * w + f.x) * 4];
			const uint8_t* p = &px[static_cast<size_t>(y) * f.w * 4];
			for (uint32_t x = 0; x < f.w; ++x, c += 4, p += 4) {
				if (f.blend == 0 || p[3] == 255) {
					memcpy(c, p, 4);
				} else if (p[3] != 0) { // "over": the frame's pixel on what is there
					const int a = p[3], ia = 255 - a, oa = a + c[3] * ia / 255;
					for (int k = 0; k < 3; ++k) {
						c[k] = static_cast<uint8_t>(oa ? (p[k] * a + c[k] * c[3] * ia / 255) / oa : 0);
					}
					c[3] = static_cast<uint8_t>(oa);
				}
			}
		}
		if (!wr.add(canvas, f.dn, f.dd, error)) {
			return false;
		}
		if (dispose == 1) { // cleared to transparent after it was shown
			for (uint32_t y = 0; y < f.h; ++y) {
				memset(&canvas[((static_cast<size_t>(f.y) + y) * w + f.x) * 4], 0, static_cast<size_t>(f.w) * 4);
			}
		} else if (dispose == 2) {
			canvas.swap(saved);
		}
	}
	wr.end();
	return true;
}

// ---- GIF ----

struct GifImage {
	uint32_t x = 0, y = 0, w = 0, h = 0;
	bool     interlaced = false;
	int      transparent = -1, dispose = 0;
	uint16_t delay = 10; // 1/100 s
	const uint8_t* palette = nullptr;
	int      colors = 0, min_code = 0;
	std::vector<uint8_t> lzw; // the image's data blocks joined
};

// LZW codes -> palette indices (w * h); false on broken data.
bool lzw_decode(const GifImage& im, std::vector<uint8_t>& idx) {
	const size_t want = static_cast<size_t>(im.w) * im.h;
	idx.clear();
	idx.reserve(want);
	if (im.min_code < 2 || im.min_code > 8) {
		return false;
	}
	const int clear = 1 << im.min_code, eoi = clear + 1;
	std::vector<uint16_t> prefix(4096);
	std::vector<uint8_t>  suffix(4096), stack(4097);
	int    size = im.min_code + 1, next = clear + 2, old = -1;
	uint8_t first = 0;
	uint32_t bits = 0;
	int    nbits = 0;
	for (size_t p = 0; p < im.lzw.size() && idx.size() < want;) {
		while (nbits < size && p < im.lzw.size()) {
			bits |= static_cast<uint32_t>(im.lzw[p++]) << nbits;
			nbits += 8;
		}
		if (nbits < size) {
			break;
		}
		int code = static_cast<int>(bits & ((1u << size) - 1));
		bits >>= size;
		nbits -= size;
		if (code == clear) {
			size = im.min_code + 1, next = clear + 2, old = -1;
			continue;
		}
		if (code == eoi) {
			break;
		}
		if (old < 0) {
			if (code >= clear) {
				return false;
			}
			idx.push_back(static_cast<uint8_t>(code));
			old = first = static_cast<uint8_t>(code);
			continue;
		}
		int in = code, sp = 0;
		if (code >= next) { // the KwKwK case
			if (code > next) {
				return false;
			}
			stack[sp++] = first;
			code        = old;
		}
		while (code >= clear) {
			if (sp >= 4096) {
				return false;
			}
			stack[sp++] = suffix[code];
			code        = prefix[code];
		}
		first       = static_cast<uint8_t>(code);
		stack[sp++] = first;
		while (sp > 0 && idx.size() < want) {
			idx.push_back(stack[--sp]);
		}
		if (next < 4096) {
			prefix[next] = static_cast<uint16_t>(old);
			suffix[next] = first;
			++next;
			if (next == (1 << size) && size < 12) {
				++size;
			}
		}
		old = in;
	}
	idx.resize(want, 0); // a short image: the rest stays the first colour (browsers do the same)
	return true;
}

bool gif_rebuild(const std::string& in, Writer& wr, std::string& error) {
	const uint8_t* b = reinterpret_cast<const uint8_t*>(in.data());
	const size_t   n = in.size();
	if (n < 13) {
		error = "The GIF is cut off";
		return false;
	}
	const uint32_t w = b[6] | (b[7] << 8), h = b[8] | (b[9] << 8);
	size_t         at = 13;
	const uint8_t* gct = nullptr;
	int            gcolors = 0;
	if (b[10] & 0x80) {
		gcolors = 2 << (b[10] & 7);
		gct     = b + 13;
		at += static_cast<size_t>(gcolors) * 3;
	}
	std::vector<GifImage> images;
	GifImage              next; // the graphic control extension applies to the next image
	uint32_t              plays = 0;
	auto blocks = [&](std::vector<uint8_t>* into) { // data sub-blocks; false when cut off
		while (at < n) {
			const uint8_t len = b[at++];
			if (len == 0) {
				return true;
			}
			if (at + len > n) {
				return false;
			}
			if (into != nullptr) {
				into->insert(into->end(), b + at, b + at + len);
			}
			at += len;
		}
		return false;
	};
	while (at < n && b[at] != 0x3B) {
		if (b[at] == 0x21 && at + 2 < n) { // extension
			const uint8_t label = b[at + 1];
			at += 2;
			if (label == 0xF9 && at + 6 <= n && b[at] >= 4) {
				next.dispose     = (b[at + 1] >> 2) & 7;
				next.delay       = static_cast<uint16_t>(b[at + 2] | (b[at + 3] << 8));
				next.transparent = (b[at + 1] & 1) ? b[at + 4] : -1;
			} else if (label == 0xFF && at + 15 < n && !memcmp(b + at + 1, "NETSCAPE2.0", 11) && b[at + 12] >= 3) {
				plays = static_cast<uint32_t>(b[at + 14] | (b[at + 15] << 8));
			}
			if (!blocks(nullptr)) {
				break;
			}
		} else if (b[at] == 0x2C && at + 10 <= n) { // image
			GifImage im = next;
			next        = GifImage();
			im.x = b[at + 1] | (b[at + 2] << 8), im.y = b[at + 3] | (b[at + 4] << 8);
			im.w = b[at + 5] | (b[at + 6] << 8), im.h = b[at + 7] | (b[at + 8] << 8);
			const uint8_t flags = b[at + 9];
			im.interlaced       = (flags & 0x40) != 0;
			at += 10;
			im.palette = gct, im.colors = gcolors;
			if (flags & 0x80) {
				im.colors  = 2 << (flags & 7);
				im.palette = b + at;
				at += static_cast<size_t>(im.colors) * 3;
			}
			if (at >= n) {
				break;
			}
			im.min_code = b[at++];
			if (!blocks(&im.lzw)) {
				if (im.lzw.empty()) {
					break;
				}
				images.push_back(std::move(im)); // a cut-off last frame: keep what is there
				break;
			}
			images.push_back(std::move(im));
		} else {
			break;
		}
	}
	if (w == 0 || h == 0 || w > 4096 || h > 4096 || images.empty()) {
		error = "The GIF could not be read";
		return false;
	}
	if (!wr.begin(w, h, images.size(), plays, error)) {
		return false;
	}
	std::vector<uint8_t> canvas(static_cast<size_t>(w) * h * 4, 0), saved, idx;
	for (size_t i = 0; i < images.size(); ++i) {
		const GifImage& im = images[i];
		if (im.palette == nullptr || !lzw_decode(im, idx)) {
			error = "Frame " + std::to_string(i + 1) + " of the GIF is broken";
			return false;
		}
		if (im.dispose == 3) {
			saved = canvas;
		}
		for (uint32_t r = 0; r < im.h; ++r) {
			uint32_t y = r; // interlaced rows come in 4 passes: 0, 4, 2, 1 (every 8, 8, 4, 2)
			if (im.interlaced) {
				const uint32_t p1 = (im.h + 7) / 8, p2 = (im.h + 3) / 8, p3 = (im.h + 1) / 4;
				y = r < p1 ? r * 8 : r < p1 + p2 ? (r - p1) * 8 + 4 : r < p1 + p2 + p3 ? (r - p1 - p2) * 4 + 2 : (r - p1 - p2 - p3) * 2 + 1;
			}
			if (im.y + y >= h) {
				continue;
			}
			for (uint32_t x = 0; x < im.w && im.x + x < w; ++x) {
				const int k = idx[static_cast<size_t>(r) * im.w + x];
				if (k == im.transparent || k >= im.colors) {
					continue;
				}
				uint8_t* c = &canvas[((static_cast<size_t>(im.y) + y) * w + im.x + x) * 4];
				c[0] = im.palette[k * 3], c[1] = im.palette[k * 3 + 1], c[2] = im.palette[k * 3 + 2], c[3] = 255;
			}
		}
		// GIF delays of 0 or 1 hundredths: browsers play them at 1/10 s
		if (!wr.add(canvas, im.delay < 2 ? 10 : im.delay, 100, error)) {
			return false;
		}
		if (im.dispose == 2) { // cleared (to transparent, as browsers do) after it was shown
			for (uint32_t y = im.y; y < im.y + im.h && y < h; ++y) {
				const uint32_t x1 = std::min(w, im.x + im.w);
				if (im.x < x1) {
					memset(&canvas[(static_cast<size_t>(y) * w + im.x) * 4], 0, static_cast<size_t>(x1 - im.x) * 4);
				}
			}
		} else if (im.dispose == 3) {
			canvas.swap(saved);
		}
	}
	wr.end();
	return true;
}

} // namespace

bool apng_rebuild(const std::string& in, std::string& anim, std::string& still, std::string& error, uint32_t max_side) {
	const bool png = in.size() >= 60 && memcmp(in.data(), kSig, 8) == 0;
	const bool gif = in.size() >= 13 && (in.compare(0, 6, "GIF89a") == 0 || in.compare(0, 6, "GIF87a") == 0);
	if (!png && !gif) {
		error = "That is not an APNG or GIF picture";
		return false;
	}
	Writer wr;
	wr.anim  = &anim;
	wr.still    = &still;
	wr.max_side = max_side;
	return png ? png_rebuild(in, wr, error) : gif_rebuild(in, wr, error);
}

} // namespace liveshell
