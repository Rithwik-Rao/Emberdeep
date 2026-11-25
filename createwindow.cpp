// ============================================================================
//  EMBERDEEP  -  a dark-fantasy 2D roguelike in ONE file
//
//  Libraries : GLFW, GLAD (OpenGL 3.3 core), GLM        (matches your CMakeLists)
//
//  CONTROLS
//    W A S D / arrows ... move            Mouse ........ aim
//    Left mouse ......... cast            Space / RMB .. dash (i-frames)
//    1 2 3 / click ...... pick a boon     ESC .......... pause      (Q quits from pause)
//    F11 ................ toggle fullscreen
//
//  CO-OP  (2-4 players, host-authoritative, plain TCP - no extra libraries needed)
//    host :  press H on the title screen          (or start with:  emberdeep host)
//    join :  press J, type the host's IP, ENTER   (or start with:  emberdeep join 192.168.1.20)
//    The host's screen shows its IP and port (TCP 7777).  Same network: just connect.
//    Over the internet: forward TCP 7777 on the host's router, or use a VPN such as
//    Tailscale / ZeroTier / Hamachi.  On Windows add ws2_32 to target_link_libraries.
//    Friends can join at any time; a downed player is revived when a room is cleared.
//
//  THE GAME
//    Descend through procedurally generated crypts. Every room seals behind you
//    until its monsters are dead. Cleared rooms may drop a Rune - take it to pick
//    one of three boons and build a run. Each floor ends in a boss. Die and the
//    dungeon is gone forever.
//
//  THE TECH (everything is procedural - no image / font / model files)
//    * all sprites are generated in code as pixel art (auto outlines + shading)
//      and packed into a texture atlas at start-up, a 5x7 font included
//    * the game renders at 480x270 and is upscaled with a "sharp bilinear" filter
//    * true dynamic 2D lighting: per-pixel soft shadows sphere-traced through a
//      distance field of the dungeon walls, up to 40 coloured lights at once
//      (player lantern, torches, projectiles, explosions, portals ...)
//    * HDR rendering, additive emissive pass, 3-level gaussian bloom, ACES tone
//      mapping, chromatic aberration, shockwave refraction, vignette, film grain
//    * trauma-based screen shake, hit-stop, slow motion, dissolve deaths,
//      afterimage dashes, persistent blood decals, lightning arcs, damage numbers
//    * flow-field pathfinding, 14 stackable boons, 6 monster types, 2 bosses
//    * online co-op: host runs the game and streams state snapshots + effect events;
//      each client moves its own player locally (instant controls) and replays the rest
// ============================================================================

#define GLM_FORCE_CTOR_INIT   // zero-initialise glm vectors / matrices

// ---- sockets (online co-op).  On Windows add  ws2_32  to target_link_libraries (see notes).
#ifdef _WIN32
  #ifndef NOMINMAX
    #define NOMINMAX
  #endif
  #ifndef WIN32_LEAN_AND_MEAN
    #define WIN32_LEAN_AND_MEAN
  #endif
  #include <winsock2.h>
  #include <ws2tcpip.h>
  #ifdef _MSC_VER
    #pragma comment(lib, "ws2_32.lib")
  #endif
  typedef SOCKET sock_t;
  typedef int    sock_len_t;
  static const sock_t BAD_SOCK = INVALID_SOCKET;
  #define NET_SEND_FLAGS 0
#else
  #include <sys/types.h>
  #include <sys/socket.h>
  #include <netinet/in.h>
  #include <netinet/tcp.h>
  #include <arpa/inet.h>
  #include <netdb.h>
  #include <unistd.h>
  #include <fcntl.h>
  #include <errno.h>
  typedef int       sock_t;
  typedef socklen_t sock_len_t;
  static const sock_t BAD_SOCK = -1;
  #ifdef MSG_NOSIGNAL
    #define NET_SEND_FLAGS MSG_NOSIGNAL
  #else
    #define NET_SEND_FLAGS 0
  #endif
#endif

#include <glad/glad.h>
#include <GLFW/glfw3.h>

#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <csignal>
#include <cstring>
#include <random>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using glm::mat4;
using glm::vec2;
using glm::vec3;
using glm::vec4;

static constexpr int   VW = 480, VH = 270;      // virtual (pixel-art) resolution
static constexpr int   TS = 16;                  // tile size in virtual pixels
static constexpr int   MAPW = 112, MAPH = 63;     // dungeon size in tiles
static constexpr int   SDF_S = 4;                // distance-field texels per tile
static constexpr int   MAX_LIGHTS = 40;
static constexpr float PI = 3.14159265358979f;

// ============================================================================
//  small utilities
// ============================================================================
static std::mt19937 gRng(std::random_device{}());
static float rf(float a, float b) { return std::uniform_real_distribution<float>(a, b)(gRng); }
static int   ri(int a, int b)     { return std::uniform_int_distribution<int>(a, b)(gRng); }
static bool  chance(float p)      { return rf(0.f, 1.f) < p; }

static float clampf(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }
static int   clampi(int v, int a, int b)       { return v < a ? a : (v > b ? b : v); }
static float lerpf(float a, float b, float t)   { return a + (b - a) * t; }
static float len2(vec2 v)                       { return std::sqrt(v.x * v.x + v.y * v.y); }
static float dot2(vec2 a, vec2 b)               { return a.x * b.x + a.y * b.y; }
static vec2  norm2(vec2 v)                      { float l = len2(v); return l > 1e-5f ? v / l : vec2(0.f, 0.f); }
static vec2  angVec(float a)                    { return vec2(std::cos(a), std::sin(a)); }
static vec2  perp2(vec2 v)                      { return vec2(-v.y, v.x); }
static vec3  mix3(vec3 a, vec3 b, float t)      { return a + (b - a) * t; }
static float smooth01(float t)                  { t = clampf(t, 0.f, 1.f); return t * t * (3.f - 2.f * t); }

static uint32_t hash2(int x, int y, int s) {
    uint32_t h = (uint32_t)x * 374761393u + (uint32_t)y * 668265263u + (uint32_t)s * 2246822519u;
    h = (h ^ (h >> 13)) * 1274126177u;
    return h ^ (h >> 16);
}
static float hashf(int x, int y, int s) { return (float)(hash2(x, y, s) & 0xFFFF) / 65535.f; }

// ============================================================================
//  pixel-art canvas (procedural sprites)
// ============================================================================
struct Col { int r, g, b; };
static Col mulc(Col c, float f) { return {clampi((int)(c.r * f), 0, 255), clampi((int)(c.g * f), 0, 255), clampi((int)(c.b * f), 0, 255)}; }
static Col mixc(Col a, Col b, float t) {
    return {(int)(a.r + (b.r - a.r) * t), (int)(a.g + (b.g - a.g) * t), (int)(a.b + (b.b - a.b) * t)};
}

struct Px { uint8_t r = 0, g = 0, b = 0, a = 0, e = 0; };   // e = emissive amount

struct Canvas {
    int w, h;
    std::vector<Px> d;
    Canvas(int W = 16, int H = 16) : w(W), h(H), d((size_t)W * H) {}
    bool in(int x, int y) const { return x >= 0 && y >= 0 && x < w && y < h; }
    Px&       at(int x, int y)       { return d[(size_t)y * w + x]; }
    const Px& at(int x, int y) const { return d[(size_t)y * w + x]; }
    bool solid(int x, int y) const { return in(x, y) && at(x, y).a > 0; }

    void set(int x, int y, Col c, int e = 0) {
        if (!in(x, y)) return;
        Px& p = at(x, y);
        p.r = (uint8_t)c.r; p.g = (uint8_t)c.g; p.b = (uint8_t)c.b; p.a = 255; p.e = (uint8_t)e;
    }
    void erase(int x, int y) { if (in(x, y)) at(x, y) = Px(); }
    void rect(int x, int y, int rw, int rh, Col c, int e = 0) {
        for (int j = 0; j < rh; j++) for (int i = 0; i < rw; i++) set(x + i, y + j, c, e);
    }
    void ellipse(float cx, float cy, float rx, float ry, Col c, int e = 0) {
        for (int y = 0; y < h; y++) for (int x = 0; x < w; x++) {
            float dx = (x + 0.5f - cx) / rx, dy = (y + 0.5f - cy) / ry;
            if (dx * dx + dy * dy <= 1.f) set(x, y, c, e);
        }
    }
    void ellipseGrad(float cx, float cy, float rx, float ry, Col top, Col bot, int e = 0) {
        for (int y = 0; y < h; y++) for (int x = 0; x < w; x++) {
            float dx = (x + 0.5f - cx) / rx, dy = (y + 0.5f - cy) / ry;
            if (dx * dx + dy * dy <= 1.f) set(x, y, mixc(top, bot, (dy + 1.f) * 0.5f), e);
        }
    }
    void eraseEllipse(float cx, float cy, float rx, float ry) {
        for (int y = 0; y < h; y++) for (int x = 0; x < w; x++) {
            float dx = (x + 0.5f - cx) / rx, dy = (y + 0.5f - cy) / ry;
            if (dx * dx + dy * dy <= 1.f) erase(x, y);
        }
    }
    void line(int x0, int y0, int x1, int y1, Col c, int e = 0) {
        int dx = std::abs(x1 - x0), dy = -std::abs(y1 - y0), sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
        int err = dx + dy;
        for (;;) {
            set(x0, y0, c, e);
            if (x0 == x1 && y0 == y1) break;
            int e2 = 2 * err;
            if (e2 >= dy) { err += dy; x0 += sx; }
            if (e2 <= dx) { err += dx; y0 += sy; }
        }
    }
    void tri(float x0, float y0, float x1, float y1, float x2, float y2, Col c, int e = 0) {
        for (int y = 0; y < h; y++) for (int x = 0; x < w; x++) {
            float px = x + 0.5f, py = y + 0.5f;
            float d0 = (px - x1) * (y0 - y1) - (x0 - x1) * (py - y1);
            float d1 = (px - x2) * (y1 - y2) - (x1 - x2) * (py - y2);
            float d2 = (px - x0) * (y2 - y0) - (x2 - x0) * (py - y0);
            bool neg = d0 < 0 || d1 < 0 || d2 < 0, pos = d0 > 0 || d1 > 0 || d2 > 0;
            if (!(neg && pos)) set(x, y, c, e);
        }
    }
};

static Canvas transposed(const Canvas& c) {
    Canvas t(c.h, c.w);
    for (int y = 0; y < c.h; y++) for (int x = 0; x < c.w; x++) t.at(y, x) = c.at(x, y);
    return t;
}
static Canvas scaled2(const Canvas& c) {
    Canvas t(c.w * 2, c.h * 2);
    for (int y = 0; y < t.h; y++) for (int x = 0; x < t.w; x++) t.at(x, y) = c.at(x / 2, y / 2);
    return t;
}

// light from the top-left: lighten lit edges, darken the far edges
static void shadeEdges(Canvas& c, float hi = 1.28f, float lo = 0.68f) {
    Canvas src = c;
    for (int y = 0; y < c.h; y++) for (int x = 0; x < c.w; x++) {
        if (!src.solid(x, y) || src.at(x, y).e > 0) continue;
        bool tl = !src.solid(x - 1, y) || !src.solid(x, y - 1);
        bool br = !src.solid(x + 1, y) || !src.solid(x, y + 1);
        Px& p = c.at(x, y);
        float f = (br && !tl) ? lo : ((tl && !br) ? hi : 1.f);
        p.r = (uint8_t)clampi((int)(p.r * f), 0, 255);
        p.g = (uint8_t)clampi((int)(p.g * f), 0, 255);
        p.b = (uint8_t)clampi((int)(p.b * f), 0, 255);
    }
}
// 1-pixel outline tinted by the neighbouring colour
static void outlineC(Canvas& c, float f = 0.26f) {
    Canvas src = c;
    static const int dx[4] = {1, -1, 0, 0}, dy[4] = {0, 0, 1, -1};
    for (int y = 0; y < c.h; y++) for (int x = 0; x < c.w; x++) {
        if (src.solid(x, y)) continue;
        for (int k = 0; k < 4; k++) {
            int nx = x + dx[k], ny = y + dy[k];
            if (!src.solid(nx, ny)) continue;
            const Px& n = src.at(nx, ny);
            if (n.e > 0) c.set(x, y, Col{14, 10, 22}, 0);
            else c.set(x, y, mulc(Col{n.r, n.g, n.b}, f), 0);
            break;
        }
    }
}
static void finishSprite(Canvas& c) { shadeEdges(c); outlineC(c); }

// ---------------------------------------------------------------- tiles ----
static Canvas genFloor(int v) {
    Canvas c(16, 16);
    Col base{94, 90, 104};
    for (int y = 0; y < 16; y++) for (int x = 0; x < 16; x++)
        c.set(x, y, mulc(base, 0.86f + 0.22f * hashf(x, y, 3 + v)));
    for (int i = 0; i < 16; i++) {
        c.set(i, 15, mulc(base, 0.52f)); c.set(15, i, mulc(base, 0.58f));
        c.set(i, 0, mulc(base, 1.12f));  c.set(0, i, mulc(base, 1.08f));
    }
    if (v == 1) for (int x = 0; x < 9; x++) c.set(x, 8, mulc(base, 0.6f));
    if (v == 0) for (int y = 8; y < 16; y++) c.set(8, y, mulc(base, 0.62f));
    std::mt19937 r(900 + v * 31);
    auto R = [&](int a, int b) { return std::uniform_int_distribution<int>(a, b)(r); };
    if (v == 2) {                                   // crack
        int x = R(4, 11), y = 1;
        for (int i = 0; i < 15; i++) {
            c.set(x, y, mulc(base, 0.4f));
            y++; x += R(-1, 1); x = clampi(x, 1, 14);
            if (R(0, 3) == 0) c.set(x + 1, y, mulc(base, 0.5f));
        }
    } else if (v == 3) {                            // pebbles
        for (int k = 0; k < 4; k++) {
            int px = R(2, 12), py = R(2, 12);
            c.rect(px, py, 2, 2, mulc(base, 1.25f));
            c.set(px + 1, py + 2, mulc(base, 0.5f)); c.set(px + 2, py + 1, mulc(base, 0.5f));
        }
    } else if (v == 4) {                            // moss
        for (int y = 1; y < 15; y++) for (int x = 1; x < 15; x++) {
            float dx = (x - 8.f) / 7.f, dy = (y - 8.f) / 7.f;
            if (dx * dx + dy * dy < 1.f && hashf(x / 2, y / 2, 77) > 0.42f)
                c.set(x, y, mulc(Col{64, 118, 66}, 0.8f + 0.4f * hashf(x, y, 9)));
        }
    } else if (v == 5) {                            // old bones
        Col bone{214, 208, 182};
        c.line(3, 11, 11, 7, bone); c.line(3, 12, 11, 8, mulc(bone, 0.8f));
        c.rect(2, 10, 2, 3, bone); c.rect(11, 6, 2, 3, bone);
    }
    return c;
}

static Canvas genCap(int mask) {                    // bit0 N, bit1 E, bit2 S, bit3 W = floor next to it
    Canvas c(16, 16);
    Col base{60, 56, 74};
    for (int y = 0; y < 16; y++) for (int x = 0; x < 16; x++)
        c.set(x, y, mulc(base, 0.82f + 0.3f * hashf(x, y, 41)));
    for (int i = 0; i < 16; i++) {
        if (mask & 1)  { c.set(i, 0, mulc(base, 2.0f));  c.set(i, 1, mulc(base, 1.4f)); }
        if (mask & 2)  { c.set(15, i, mulc(base, 0.7f)); c.set(14, i, mulc(base, 1.25f)); }
        if (mask & 8)  { c.set(0, i, mulc(base, 1.9f));  c.set(1, i, mulc(base, 1.35f)); }
        if (mask & 4)  { c.set(i, 15, mulc(base, 0.6f)); }
    }
    return c;
}

static Canvas genFace(int v) {
    Canvas c(16, 16);
    Col mortar{30, 26, 40}, brick{104, 90, 108};
    for (int y = 0; y < 16; y++) for (int x = 0; x < 16; x++) {
        int row = y / 4, off = (row % 2) * 4 + v * 3;
        int bx = (x + off) % 8;
        bool seam = (y % 4 == 3) || bx == 7;
        if (seam) c.set(x, y, mortar);
        else c.set(x, y, mulc(brick, 0.82f + 0.32f * hashf((x + off) / 8, row, 13 + v)));
        if (y == 0) c.set(x, y, mulc(brick, 0.7f));
        if (y >= 13) { Px& p = c.at(x, y); p.r = (uint8_t)(p.r * 0.68f); p.g = (uint8_t)(p.g * 0.68f); p.b = (uint8_t)(p.b * 0.68f); }
    }
    return c;
}

static Canvas genTorch(int f) {
    Canvas c(16, 16);
    Col iron{54, 50, 64};
    c.rect(7, 9, 2, 6, iron);
    c.rect(5, 8, 6, 2, mulc(iron, 1.5f));
    c.set(5, 7, iron); c.set(10, 7, iron);
    static const int sway[4] = {0, 1, 0, -1}, hgt[4] = {0, 1, 0, -1};
    int sx = sway[f], hh = hgt[f];
    c.ellipse(8.f + sx * 0.6f, 5.2f, 2.5f, 3.4f + hh * 0.4f, Col{255, 120, 24}, 255);
    c.ellipse(8.f + sx * 0.4f, 5.8f, 1.6f, 2.4f + hh * 0.3f, Col{255, 200, 90}, 255);
    c.ellipse(8.f + sx * 0.2f, 6.3f, 0.8f, 1.4f, Col{255, 248, 210}, 255);
    c.set(8 + sx, 1 - (hh > 0 ? 1 : 0), Col{255, 150, 40}, 255);
    return c;
}

static Canvas genGateV() {
    Canvas c(16, 16);
    Col iron{86, 84, 100};
    for (int b = 0; b < 4; b++) {
        int bx = 1 + b * 4;
        c.rect(bx, 0, 2, 16, iron);
        c.rect(bx, 0, 1, 16, mulc(iron, 1.4f));
        c.set(bx, 7, Col{255, 70, 40}, 255); c.set(bx + 1, 7, Col{255, 70, 40}, 255);
    }
    c.rect(0, 2, 16, 2, mulc(iron, 0.7f));
    c.rect(0, 12, 16, 2, mulc(iron, 0.7f));
    outlineC(c);
    return c;
}

static Canvas genPedestal() {
    Canvas c(16, 16);
    Col st{110, 106, 124};
    c.rect(3, 9, 10, 6, st); c.rect(2, 13, 12, 2, mulc(st, 0.8f)); c.rect(4, 7, 8, 2, mulc(st, 1.15f));
    for (int y = 7; y < 15; y++) for (int x = 2; x < 14; x++)
        if (c.solid(x, y)) { Px& p = c.at(x, y); float k = 0.9f + 0.2f * hashf(x, y, 5); p.r = (uint8_t)clampi((int)(p.r * k), 0, 255); p.g = (uint8_t)clampi((int)(p.g * k), 0, 255); p.b = (uint8_t)clampi((int)(p.b * k), 0, 255); }
    c.set(7, 10, Col{170, 120, 255}, 255); c.set(8, 10, Col{170, 120, 255}, 255);
    c.set(7, 11, Col{170, 120, 255}, 255); c.set(8, 11, Col{170, 120, 255}, 255);
    shadeEdges(c); outlineC(c);
    return c;
}

// ------------------------------------------------------------ characters ---
static Canvas genPlayer(int frame, bool walk, int variant = 0) {
    Canvas c(16, 16);
    static const Col cl0[4] = {{58, 68, 134}, {146, 54, 66}, {48, 120, 80}, {122, 84, 162}};
    static const Col cl1[4] = {{98, 114, 184}, {204, 98, 104}, {92, 172, 120}, {176, 132, 214}};
    static const Col cl2[4] = {{34, 38, 88}, {90, 30, 44}, {28, 76, 54}, {76, 50, 110}};
    static const Col eyeC[4] = {{120, 255, 255}, {255, 190, 110}, {200, 255, 130}, {255, 150, 230}};
    Col cloak = cl0[variant & 3], cloakL = cl1[variant & 3], cloakD = cl2[variant & 3], faceC{10, 6, 20}, boot{46, 32, 46};
    Col eye = eyeC[variant & 3];
    int bob = walk ? ((frame == 1 || frame == 3) ? 1 : 0) : (frame == 1 ? 1 : 0);
    for (int y = 7; y <= 13; y++) {
        float hw = 2.7f + (y - 7) * 0.55f;
        for (int x = 0; x < 16; x++) {
            float dx = x + 0.5f - 7.6f;
            if (std::fabs(dx) > hw) continue;
            float t = (dx + hw) / (2.f * hw);
            Col col = mixc(cloakL, cloakD, t);
            if (((x + y) & 1) && t > 0.55f) col = mulc(col, 0.85f);
            c.set(x, y + bob, col);
        }
    }
    c.rect(5, 10 + bob, 6, 1, Col{190, 140, 60});                       // belt
    c.ellipse(8.4f, 4.6f + bob, 3.7f, 4.0f, cloak);                     // hood
    c.set(4, 6 + bob, cloak); c.set(3, 7 + bob, cloakD); c.set(4, 7 + bob, cloakD);
    c.ellipse(10.3f, 5.3f + bob, 2.1f, 2.5f, faceC);                    // face void
    c.set(9, 5 + bob, eye, 255);                                        // eyes
    c.set(11, 5 + bob, eye, 255);
    c.set(11, 8 + bob, cloakD); c.set(12, 8 + bob, cloakD);             // arm
    c.set(13, 9 + bob, Col{70, 60, 50});                                // lantern ring
    c.rect(12, 10 + bob, 3, 3, Col{70, 58, 46});                        // lantern
    c.set(13, 11 + bob, Col{255, 214, 120}, 255);
    c.set(12, 11 + bob, Col{255, 160, 60}, 220); c.set(14, 11 + bob, Col{255, 160, 60}, 220);
    c.set(13, 10 + bob, Col{255, 160, 60}, 200); c.set(13, 12 + bob, Col{255, 160, 60}, 200);
    int lx = 6, rx = 9;
    bool liftL = false, liftR = false;
    if (walk) {
        static const int offs[4] = {-1, 0, 1, 0};
        lx += offs[frame]; rx -= offs[frame];
        liftL = (frame == 1); liftR = (frame == 3);
    }
    c.rect(lx, liftL ? 14 : 14, 2, liftL ? 1 : 2, boot);
    c.rect(rx, liftR ? 14 : 14, 2, liftR ? 1 : 2, boot);
    finishSprite(c);
    return c;
}

static Canvas genSlime(int frame, bool isSmall) {
    Canvas c(16, 16);
    float s = isSmall ? 0.66f : 1.f;
    float ry = (frame == 0 ? 5.6f : 4.5f) * s + (isSmall ? 0.4f : 0.f);
    float rx = (frame == 0 ? 6.0f : 7.2f) * s;
    float cy = 14.4f - ry;
    c.ellipseGrad(8.f, cy, rx, ry, Col{150, 240, 150}, Col{34, 130, 80});
    // translucent inner core
    c.ellipse(8.f, cy + ry * 0.25f, rx * 0.45f, ry * 0.4f, Col{60, 170, 100}, 90);
    c.rect((int)(8 - rx * 0.55f), (int)(cy - ry * 0.55f), 2, 1, Col{235, 255, 235});   // highlight
    int ex = (int)(8 - 2 * s - 0.5f), ey = (int)(cy - ry * 0.15f);
    c.set(ex, ey, Col{12, 22, 18}); c.set(ex, ey + 1, Col{12, 22, 18});
    c.set(ex + 4, ey, Col{12, 22, 18}); c.set(ex + 4, ey + 1, Col{12, 22, 18});
    c.set(ex + 1, ey, Col{240, 255, 240}); c.set(ex + 5, ey, Col{240, 255, 240});
    finishSprite(c);
    return c;
}

static Canvas genBat(int frame) {
    Canvas c(16, 16);
    Col wing{84, 52, 112}, wingD{50, 30, 76}, body{60, 40, 80};
    float tip = frame == 0 ? 2.f : 12.f;
    c.tri(6.5f, 7.f, 0.f, tip, 5.f, 11.f, wing);
    c.tri(9.5f, 7.f, 16.f, tip, 11.f, 11.f, wing);
    c.line(6, 7, 1, (int)tip, wingD); c.line(9, 7, 14, (int)tip, wingD);
    c.ellipse(8.f, 8.f, 2.4f, 3.4f, body);
    c.set(6, 4, body); c.set(9, 4, body); c.set(6, 3, body); c.set(9, 3, body);
    c.set(7, 7, Col{255, 70, 70}, 255); c.set(9, 7, Col{255, 70, 70}, 255);
    c.set(7, 10, Col{240, 240, 240}); c.set(9, 10, Col{240, 240, 240});
    finishSprite(c);
    return c;
}

static Canvas genSkeleton(int frame) {
    Canvas c(16, 16);
    Col bone{232, 226, 200}, boneD{176, 168, 146};
    int bob = frame == 1 ? 1 : 0;
    c.ellipse(7.5f, 4.5f + bob, 3.2f, 3.2f, bone);
    c.rect(6, 7 + bob, 4, 2, boneD);                                     // jaw
    c.rect(5, 4 + bob, 2, 2, Col{16, 8, 20}); c.rect(8, 4 + bob, 2, 2, Col{16, 8, 20});
    c.set(6, 5 + bob, Col{255, 70, 60}, 255); c.set(9, 5 + bob, Col{255, 70, 60}, 255);
    c.rect(7, 9 + bob, 1, 4, boneD);                                     // spine
    for (int i = 0; i < 2; i++) c.rect(5, 9 + i * 2 + bob, 5, 1, bone);  // ribs
    c.rect(5, 12 + bob, 5, 1, boneD);
    int a = frame == 0 ? 0 : 1;
    c.rect(5 + a, 13, 1, 2, bone); c.rect(9 - a, 13, 1, 2, bone);        // legs
    c.set(5 + a, 15, boneD); c.set(9 - a, 15, boneD);
    c.line(9, 9 + bob, 12, 9 + bob, boneD);                              // arm
    // bow
    for (int a2 = -70; a2 <= 70; a2 += 10) {
        float r = a2 * PI / 180.f;
        c.set(12 + (int)std::lround(std::cos(r) * 2.4f), 9 + bob + (int)std::lround(std::sin(r) * 5.f), Col{138, 90, 52});
    }
    c.line(13, 5 + bob, 13, 13 + bob, Col{230, 230, 220});
    finishSprite(c);
    return c;
}

static Canvas genMage(int frame) {
    Canvas c(16, 16);
    Col robe{108, 44, 142}, robeD{60, 20, 90};
    int bob = frame == 1 ? 1 : 0;
    for (int y = 5; y <= 14; y++) {
        float hw = 2.f + (y - 5) * 0.46f;
        for (int x = 0; x < 16; x++) {
            float dx = x + 0.5f - 8.f;
            if (std::fabs(dx) > hw) continue;
            if (y == 14 && ((x + frame) & 1)) continue;                  // ragged hem
            float t = (dx + hw) / (2.f * hw);
            c.set(x, y - bob + 1, mixc(mulc(robe, 1.3f), robeD, t));
        }
    }
    c.ellipse(8.f, 4.6f + 1 - bob, 3.3f, 3.5f, robe);
    c.ellipse(8.f, 5.2f + 1 - bob, 2.1f, 2.1f, Col{10, 4, 18});
    c.set(7, 5 + 1 - bob, Col{255, 80, 220}, 255); c.set(9, 5 + 1 - bob, Col{255, 80, 220}, 255);
    c.set(3, 9 - bob, Col{150, 140, 160}); c.set(13, 9 - bob, Col{150, 140, 160});
    c.ellipse(13.5f, 6.f - bob, 1.6f, 1.6f, Col{200, 120, 255}, 255);
    c.set(13, 6 - bob, Col{255, 230, 255}, 255);
    finishSprite(c);
    return c;
}

static Canvas genBrute(int frame) {
    Canvas c(24, 24);
    Col st{126, 120, 138}, stD{80, 74, 94};
    int bob = frame == 1 ? 1 : 0;
    int la = frame == 0 ? 0 : 1;
    c.rect(7 + la, 18, 4, 5, stD); c.rect(13 - la, 18, 4, 5, stD);
    c.ellipseGrad(12.f, 13.f + bob, 8.5f, 7.5f, mulc(st, 1.15f), stD);
    c.ellipse(4.5f, 12.f + bob, 3.6f, 3.6f, st); c.ellipse(19.5f, 12.f + bob, 3.6f, 3.6f, st);
    c.ellipse(3.5f, 18.f + bob, 3.2f, 3.4f, mulc(st, 0.9f)); c.ellipse(20.5f, 18.f + bob, 3.2f, 3.4f, mulc(st, 0.9f));
    c.ellipse(12.f, 5.5f + bob, 4.2f, 3.6f, mulc(st, 1.05f));
    c.set(10, 5 + bob, Col{255, 150, 40}, 255); c.set(11, 5 + bob, Col{255, 150, 40}, 255);
    c.set(13, 5 + bob, Col{255, 150, 40}, 255); c.set(14, 5 + bob, Col{255, 150, 40}, 255);
    // glowing cracks
    c.line(12, 9 + bob, 10, 13 + bob, Col{255, 120, 30}, 255);
    c.line(10, 13 + bob, 12, 17 + bob, Col{255, 120, 30}, 255);
    c.line(11, 11 + bob, 15, 14 + bob, Col{255, 90, 20}, 255);
    c.line(4, 10 + bob, 5, 14 + bob, Col{255, 120, 30}, 255);
    finishSprite(c);
    return c;
}

static Canvas genKing(int frame) {
    Canvas c(32, 32);
    float ry = frame == 0 ? 10.f : 8.6f, rx = frame == 0 ? 13.f : 14.4f;
    float cy = 29.f - ry;
    c.ellipseGrad(16.f, cy, rx, ry, Col{140, 235, 150}, Col{30, 120, 76});
    c.ellipse(16.f, cy + ry * 0.2f, rx * 0.55f, ry * 0.5f, Col{50, 150, 96}, 70);
    for (int i = 0; i < 6; i++) c.set(8 + i * 3, (int)(cy + 2 + (i % 3)), Col{210, 255, 210});   // bubbles
    c.rect(11, (int)(cy - ry) + 1, 10, 3, Col{244, 200, 62});                                      // crown
    for (int i = 0; i < 3; i++) c.tri(11.f + i * 4.5f, (float)((int)(cy - ry) + 1), 13.f + i * 4.5f, (float)((int)(cy - ry) - 4), 15.f + i * 4.5f, (float)((int)(cy - ry) + 1), Col{244, 200, 62});
    c.set(13, (int)(cy - ry) + 2, Col{255, 60, 80}, 255); c.set(16, (int)(cy - ry) + 2, Col{80, 160, 255}, 255); c.set(19, (int)(cy - ry) + 2, Col{255, 60, 80}, 255);
    int ey = (int)(cy - 1);
    c.ellipse(11.5f, (float)ey, 2.6f, 2.8f, Col{245, 250, 240}); c.ellipse(20.5f, (float)ey, 2.6f, 2.8f, Col{245, 250, 240});
    c.rect(12, ey, 2, 2, Col{140, 10, 20}, 255); c.rect(19, ey, 2, 2, Col{140, 10, 20}, 255);
    c.line(8, ey - 4, 13, ey - 2, Col{20, 60, 40}); c.line(24, ey - 4, 19, ey - 2, Col{20, 60, 40});
    c.line(12, ey + 6, 20, ey + 6, Col{20, 70, 46});
    finishSprite(c);
    return c;
}

static Canvas genLich(int frame) {
    Canvas c(32, 32);
    Col cl{34, 46, 72}, clL{66, 90, 130};
    for (int y = 12; y <= 30; y++) {
        float hw = 5.f + (y - 12) * 0.46f;
        for (int x = 0; x < 32; x++) {
            float dx = x + 0.5f - 16.f;
            if (std::fabs(dx) > hw) continue;
            if (y >= 28 && (((x + frame * 2) / 2) & 1)) continue;        // tattered hem
            float t = (dx + hw) / (2.f * hw);
            c.set(x, y, mixc(clL, cl, t));
        }
    }
    for (int i = 0; i < 4; i++) c.rect(13, 15 + i * 2, 6, 1, Col{120, 255, 230}, 120);     // glowing ribs
    c.ellipse(16.f, 9.f, 5.2f, 5.6f, Col{230, 226, 205});                // skull
    c.rect(13, 13, 6, 2, Col{184, 178, 156});
    c.rect(12, 7, 3, 3, Col{8, 10, 18}); c.rect(17, 7, 3, 3, Col{8, 10, 18});
    c.rect(13, 8, 1, 2, Col{110, 255, 230}, 255); c.rect(18, 8, 1, 2, Col{110, 255, 230}, 255);
    // crown
    c.rect(11, 2, 10, 2, Col{60, 64, 90});
    for (int i = 0; i < 4; i++) c.tri(11.f + i * 3.f, 2.f, 12.5f + i * 3.f, -1.f, 14.f + i * 3.f, 2.f, Col{60, 64, 90});
    c.set(13, 3, Col{110, 255, 230}, 255); c.set(16, 3, Col{110, 255, 230}, 255); c.set(19, 3, Col{110, 255, 230}, 255);
    // hands + orbs
    int hy = 17 + (frame == 1 ? 1 : 0);
    c.rect(5, hy, 2, 3, Col{214, 208, 184}); c.rect(25, hy, 2, 3, Col{214, 208, 184});
    c.ellipse(4.f, (float)hy - 3.f, 2.6f, 2.6f, Col{110, 255, 230}, 255);
    c.ellipse(28.f, (float)hy - 3.f, 2.6f, 2.6f, Col{110, 255, 230}, 255);
    c.set(4, hy - 4, Col{230, 255, 250}, 255); c.set(28, hy - 4, Col{230, 255, 250}, 255);
    finishSprite(c);
    return c;
}

// ------------------------------------------------------------ small things -
static Canvas genStaff() {
    Canvas c(16, 5);
    c.rect(0, 2, 12, 1, Col{126, 84, 48});
    c.rect(0, 3, 12, 1, Col{84, 54, 32});
    c.rect(3, 2, 1, 2, Col{200, 160, 70});
    c.set(11, 0, Col{210, 170, 70}); c.set(11, 4, Col{210, 170, 70}); c.set(12, 1, Col{210, 170, 70}); c.set(12, 3, Col{210, 170, 70});
    c.ellipse(13.f, 2.5f, 2.2f, 2.2f, Col{130, 240, 255}, 255);
    c.set(13, 2, Col{255, 255, 255}, 255);
    return c;
}

static Canvas genHeart(int kind) {                 // 0 full, 1 half, 2 empty
    static const char* pat[8] = {".xx...xx.", "xhxx.xxxx", "xxxxxxxxx", "xxxxxxxxx", ".xxxxxxx.", "..xxxxx..", "...xxx...", "....x...."};
    Canvas c(9, 8);
    for (int y = 0; y < 8; y++) for (int x = 0; x < 9; x++) {
        char ch = pat[y][x];
        if (ch == '.') continue;
        bool leftHalf = x < 5;
        if (kind == 0) c.set(x, y, ch == 'h' ? Col{255, 170, 180} : Col{224, 38, 62}, 90);
        else if (kind == 1) { if (leftHalf) c.set(x, y, ch == 'h' ? Col{255, 170, 180} : Col{224, 38, 62}, 90); else c.set(x, y, Col{50, 24, 40}); }
        else c.set(x, y, Col{50, 24, 40});
    }
    return c;
}

static Canvas genSoul(int f) {
    Canvas c(6, 6);
    c.ellipse(3.f, 3.4f, 1.7f, 2.2f, Col{130, 230, 255}, 255);
    c.set(3, 3, Col{255, 255, 255}, 255);
    c.set(f % 2 ? 2 : 4, 0, Col{100, 200, 255}, 255);
    c.set(3, 5, Col{80, 160, 230}, 255);
    return c;
}

static Canvas genRune() {
    Canvas c(12, 12);
    for (int y = 0; y < 12; y++) for (int x = 0; x < 12; x++) {
        float dx = std::fabs(x + 0.5f - 6.f), dy = std::fabs(y + 0.5f - 6.f);
        float m = dx + dy;
        if (m <= 5.6f) c.set(x, y, m <= 2.6f ? Col{245, 225, 255} : Col{150, 92, 255}, 255);
    }
    return c;
}

static Canvas genOrb() {                            // white, tinted by vertex colour
    Canvas c(8, 8);
    c.ellipse(4.f, 4.f, 3.7f, 3.7f, Col{170, 170, 170}, 255);
    c.ellipse(4.f, 4.f, 2.4f, 2.4f, Col{225, 225, 225}, 255);
    c.ellipse(4.f, 4.f, 1.2f, 1.2f, Col{255, 255, 255}, 255);
    return c;
}

static Canvas genArrow() {
    Canvas c(12, 5);
    c.rect(0, 2, 9, 1, Col{210, 210, 200}, 255);
    c.tri(8.f, 0.f, 12.f, 2.5f, 8.f, 5.f, Col{255, 255, 255}, 255);
    c.set(0, 1, Col{190, 190, 190}, 255); c.set(0, 3, Col{190, 190, 190}, 255);
    c.set(1, 1, Col{190, 190, 190}, 255); c.set(1, 3, Col{190, 190, 190}, 255);
    return c;
}

static Canvas genDot() { Canvas c(2, 2); c.rect(0, 0, 2, 2, Col{255, 255, 255}); return c; }

static Canvas genSoft(int n) {                      // radial falloff, white
    Canvas c(n, n);
    for (int y = 0; y < n; y++) for (int x = 0; x < n; x++) {
        float dx = (x + 0.5f - n * 0.5f) / (n * 0.5f), dy = (y + 0.5f - n * 0.5f) / (n * 0.5f);
        float d = std::sqrt(dx * dx + dy * dy);
        float a = clampf(1.f - d, 0.f, 1.f); a = a * a;
        Px& p = c.at(x, y); p.r = p.g = p.b = 255; p.a = (uint8_t)(a * 255.f);
    }
    return c;
}

static Canvas genRing(int n) {                      // thin soft ring
    Canvas c(n, n);
    for (int y = 0; y < n; y++) for (int x = 0; x < n; x++) {
        float dx = (x + 0.5f - n * 0.5f) / (n * 0.5f), dy = (y + 0.5f - n * 0.5f) / (n * 0.5f);
        float d = std::sqrt(dx * dx + dy * dy);
        float a = clampf(1.f - std::fabs(d - 0.86f) / 0.12f, 0.f, 1.f);
        Px& p = c.at(x, y); p.r = p.g = p.b = 255; p.a = (uint8_t)(a * 255.f); p.e = 255;
    }
    return c;
}

static Canvas genShadow() {
    Canvas c(16, 8);
    for (int y = 0; y < 8; y++) for (int x = 0; x < 16; x++) {
        float dx = (x + 0.5f - 8.f) / 8.f, dy = (y + 0.5f - 4.f) / 4.f;
        float a = clampf(1.f - std::sqrt(dx * dx + dy * dy), 0.f, 1.f);
        Px& p = c.at(x, y); p.r = p.g = p.b = 0; p.a = (uint8_t)(clampf(a * 1.8f, 0.f, 1.f) * 190.f);
    }
    return c;
}

static Canvas genRuneRing() {                       // summoning circle
    Canvas c(64, 64);
    auto plot = [&](float x, float y, int e) { int ix = (int)x, iy = (int)y; if (c.in(ix, iy)) { Px& p = c.at(ix, iy); p.r = p.g = p.b = 255; p.a = 255; p.e = (uint8_t)e; } };
    for (int i = 0; i < 360; i++) {
        float a = i * PI / 180.f;
        plot(32 + std::cos(a) * 30.f, 32 + std::sin(a) * 30.f, 255);
        if (i % 4 == 0) plot(32 + std::cos(a) * 27.f, 32 + std::sin(a) * 27.f, 200);
        if ((i / 15) % 2 == 0) plot(32 + std::cos(a) * 22.f, 32 + std::sin(a) * 22.f, 220);
    }
    for (int k = 0; k < 8; k++) {
        float a = k * PI / 4.f;
        for (int r = 10; r < 20; r++) plot(32 + std::cos(a) * r, 32 + std::sin(a) * r, 255);
        for (int r = 0; r < 4; r++) plot(32 + std::cos(a + 0.2f) * (20 + r), 32 + std::sin(a + 0.2f) * (20 + r), 255);
    }
    return c;
}

static Canvas genCrosshair() {
    Canvas c(9, 9);
    Col w{255, 255, 255};
    for (int i = 0; i < 2; i++) { c.set(4, i, w, 255); c.set(4, 8 - i, w, 255); c.set(i, 4, w, 255); c.set(8 - i, 4, w, 255); }
    c.set(4, 4, w, 255);
    return c;
}

static Canvas genPot() {
    Canvas c(12, 12);
    c.ellipseGrad(6.f, 7.f, 4.8f, 4.8f, Col{206, 118, 78}, Col{120, 60, 46});
    c.rect(3, 2, 6, 2, Col{214, 132, 88});
    c.rect(4, 1, 4, 1, Col{170, 96, 64});
    c.rect(3, 6, 6, 1, Col{90, 44, 36});
    c.set(3, 5, Col{255, 200, 150});
    finishSprite(c);
    return c;
}

// --------------------------------------------------------------- icons -----
enum Boon { B_TWIN, B_SWIFT, B_HEAVY, B_PIERCE, B_RICOCHET, B_HEART, B_BOOTS, B_SEEKER, B_CHAIN, B_VOLATILE, B_FROST, B_WISPS, B_VAMP, B_LANTERN, B_COUNT };

static const char* kIcons[B_COUNT][8] = {
    {"..#..#..", ".###.###", "..#..#..", "..#..#..", "..#..#..", "..#..#..", "........", "........"},   // twin
    {"....##..", "...##...", "..##....", ".######.", "...##...", "..##....", ".##.....", "........"},   // swift
    {"...##...", "...##...", "...##...", "...##...", "..####..", ".######.", "...##...", "...##..."},   // heavy
    {"......#.", ".....##.", "########", ".....##.", "......#.", "........", "........", "........"},   // pierce
    {"##......", ".##.....", "..##....", "...##.##", "....###.", "...##...", "..##....", ".##....."},   // ricochet
    {".##..##.", "########", "########", "########", ".######.", "..####..", "...##...", "........"},   // heart
    {"..##....", "..##....", "..##....", "..####..", "..#####.", ".#######", "........", "........"},   // boots
    {"...##...", "..#..#..", ".#.##.#.", "##.##.##", ".#.##.#.", "..#..#..", "...##...", "........"},   // seeker
    {".....##.", "....##..", "...###..", "..##.##.", ".##...##", "......#.", ".....#..", "........"},   // chain
    {"#..##..#", ".#.##.#.", "..####..", "###..###", "###..###", "..####..", ".#.##.#.", "#..##..#"},   // volatile
    {"...##...", "#..##..#", ".#.##.#.", "..####..", "########", "..####..", ".#.##.#.", "#..##..#"},   // frost
    {"..#..#..", ".#....#.", "........", "#..##..#", "#..##..#", "........", ".#....#.", "..#..#.."},   // wisps
    {"...##...", "...##...", "..####..", ".######.", ".######.", ".######.", "..####..", "........"},   // vamp
    {"...##...", "..####..", "..#..#..", "..#..#..", "..####..", "..####..", "...##...", "........"},   // lantern
};

static Canvas genIcon(int b) {
    Canvas c(8, 8);
    for (int y = 0; y < 8; y++) for (int x = 0; x < 8; x++)
        if (kIcons[b][y][x] == '#') c.set(x, y, Col{255, 255, 255}, 255);
    return scaled2(c);
}

// ---------------------------------------------------------------- font -----
struct Glyph { char c; uint8_t r[7]; };
static const Glyph kFont[] = {
    {'0',{0x0E,0x11,0x13,0x15,0x19,0x11,0x0E}}, {'1',{0x04,0x0C,0x04,0x04,0x04,0x04,0x0E}},
    {'2',{0x0E,0x11,0x01,0x02,0x04,0x08,0x1F}}, {'3',{0x1E,0x01,0x01,0x0E,0x01,0x01,0x1E}},
    {'4',{0x02,0x06,0x0A,0x12,0x1F,0x02,0x02}}, {'5',{0x1F,0x10,0x1E,0x01,0x01,0x11,0x0E}},
    {'6',{0x06,0x08,0x10,0x1E,0x11,0x11,0x0E}}, {'7',{0x1F,0x01,0x02,0x04,0x08,0x08,0x08}},
    {'8',{0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E}}, {'9',{0x0E,0x11,0x11,0x0F,0x01,0x02,0x0C}},
    {'A',{0x0E,0x11,0x11,0x1F,0x11,0x11,0x11}}, {'B',{0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E}},
    {'C',{0x0E,0x11,0x10,0x10,0x10,0x11,0x0E}}, {'D',{0x1E,0x11,0x11,0x11,0x11,0x11,0x1E}},
    {'E',{0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F}}, {'F',{0x1F,0x10,0x10,0x1E,0x10,0x10,0x10}},
    {'G',{0x0E,0x11,0x10,0x17,0x11,0x11,0x0F}}, {'H',{0x11,0x11,0x11,0x1F,0x11,0x11,0x11}},
    {'I',{0x0E,0x04,0x04,0x04,0x04,0x04,0x0E}}, {'J',{0x07,0x02,0x02,0x02,0x02,0x12,0x0C}},
    {'K',{0x11,0x12,0x14,0x18,0x14,0x12,0x11}}, {'L',{0x10,0x10,0x10,0x10,0x10,0x10,0x1F}},
    {'M',{0x11,0x1B,0x15,0x15,0x11,0x11,0x11}}, {'N',{0x11,0x19,0x15,0x13,0x11,0x11,0x11}},
    {'O',{0x0E,0x11,0x11,0x11,0x11,0x11,0x0E}}, {'P',{0x1E,0x11,0x11,0x1E,0x10,0x10,0x10}},
    {'Q',{0x0E,0x11,0x11,0x11,0x15,0x12,0x0D}}, {'R',{0x1E,0x11,0x11,0x1E,0x14,0x12,0x11}},
    {'S',{0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E}}, {'T',{0x1F,0x04,0x04,0x04,0x04,0x04,0x04}},
    {'U',{0x11,0x11,0x11,0x11,0x11,0x11,0x0E}}, {'V',{0x11,0x11,0x11,0x11,0x11,0x0A,0x04}},
    {'W',{0x11,0x11,0x11,0x15,0x15,0x1B,0x11}}, {'X',{0x11,0x11,0x0A,0x04,0x0A,0x11,0x11}},
    {'Y',{0x11,0x11,0x0A,0x04,0x04,0x04,0x04}}, {'Z',{0x1F,0x01,0x02,0x04,0x08,0x10,0x1F}},
    {'.',{0x00,0x00,0x00,0x00,0x00,0x0C,0x0C}}, {',',{0x00,0x00,0x00,0x00,0x0C,0x04,0x08}},
    {':',{0x00,0x0C,0x0C,0x00,0x0C,0x0C,0x00}}, {'!',{0x04,0x04,0x04,0x04,0x04,0x00,0x04}},
    {'?',{0x0E,0x11,0x01,0x02,0x04,0x00,0x04}}, {'-',{0x00,0x00,0x00,0x1F,0x00,0x00,0x00}},
    {'+',{0x00,0x04,0x04,0x1F,0x04,0x04,0x00}}, {'/',{0x01,0x02,0x02,0x04,0x08,0x08,0x10}},
    {'%',{0x19,0x1A,0x02,0x04,0x08,0x0B,0x13}}, {'\'',{0x04,0x04,0x08,0x00,0x00,0x00,0x00}},
    {'(',{0x02,0x04,0x08,0x08,0x08,0x04,0x02}}, {')',{0x08,0x04,0x02,0x02,0x02,0x04,0x08}},
    {'<',{0x02,0x04,0x08,0x10,0x08,0x04,0x02}}, {'>',{0x08,0x04,0x02,0x01,0x02,0x04,0x08}},
    {'=',{0x00,0x00,0x1F,0x00,0x1F,0x00,0x00}}, {'*',{0x04,0x15,0x0E,0x1F,0x0E,0x15,0x04}},
    {'#',{0x0A,0x0A,0x1F,0x0A,0x1F,0x0A,0x0A}},
};

// ============================================================================
//  texture atlas + sprite registry
// ============================================================================
struct SpriteRect { float u0, v0, u1, v1; int w, h; bool emissive; };

struct Atlas {
    static constexpr int W = 512, H = 512;
    std::vector<Px> px = std::vector<Px>((size_t)W * H);
    std::vector<SpriteRect> rects;
    int cx = 1, cy = 1, rowH = 0;

    int add(const Canvas& c) {
        if (cx + c.w + 1 > W) { cx = 1; cy += rowH + 1; rowH = 0; }
        if (cy + c.h + 1 > H) { std::fprintf(stderr, "atlas full\n"); std::exit(1); }
        bool em = false;
        for (int y = 0; y < c.h; y++) for (int x = 0; x < c.w; x++) {
            px[(size_t)(cy + y) * W + (cx + x)] = c.at(x, y);
            if (c.at(x, y).e > 0 && c.at(x, y).a > 0) em = true;
        }
        SpriteRect r{(float)cx / W, (float)cy / H, (float)(cx + c.w) / W, (float)(cy + c.h) / H, c.w, c.h, em};
        rects.push_back(r);
        cx += c.w + 1;
        rowH = std::max(rowH, c.h);
        return (int)rects.size() - 1;
    }
};

struct Art {
    int floorT[6], cap[16], face[3], torch[4], gateV = 0, gateH = 0, pedestal = 0;
    int player[4][6];
    int slime[2], slimeS[2], bat[2], skel[2], mage[2], brute[2], king[2], lich[2];
    int staff = 0, heart[3], soul[4], rune = 0, orb = 0, arrow = 0, dot = 0, soft = 0, softBig = 0, ring = 0, shadow = 0, runeRing = 0, crosshair = 0, pot = 0;
    int font[128];
    int icon[B_COUNT];
};
static Art ART;
static Atlas gAtlas;

static void buildArt() {
    Atlas& A = gAtlas;
    for (int i = 0; i < 6; i++) ART.floorT[i] = A.add(genFloor(i));
    for (int i = 0; i < 16; i++) ART.cap[i] = A.add(genCap(i));
    for (int i = 0; i < 3; i++) ART.face[i] = A.add(genFace(i));
    for (int i = 0; i < 4; i++) ART.torch[i] = A.add(genTorch(i));
    ART.gateV = A.add(genGateV());
    ART.gateH = A.add(transposed(genGateV()));
    ART.pedestal = A.add(genPedestal());
    for (int v = 0; v < 4; v++) {
        ART.player[v][0] = A.add(genPlayer(0, false, v)); ART.player[v][1] = A.add(genPlayer(1, false, v));
        for (int i = 0; i < 4; i++) ART.player[v][2 + i] = A.add(genPlayer(i, true, v));
    }
    for (int i = 0; i < 2; i++) {
        ART.slime[i] = A.add(genSlime(i, false)); ART.slimeS[i] = A.add(genSlime(i, true));
        ART.bat[i] = A.add(genBat(i)); ART.skel[i] = A.add(genSkeleton(i)); ART.mage[i] = A.add(genMage(i));
        ART.brute[i] = A.add(genBrute(i)); ART.king[i] = A.add(genKing(i)); ART.lich[i] = A.add(genLich(i));
    }
    ART.staff = A.add(genStaff());
    for (int i = 0; i < 3; i++) ART.heart[i] = A.add(genHeart(i));
    for (int i = 0; i < 4; i++) ART.soul[i] = A.add(genSoul(i));
    ART.rune = A.add(genRune()); ART.orb = A.add(genOrb()); ART.arrow = A.add(genArrow());
    ART.dot = A.add(genDot()); ART.soft = A.add(genSoft(32)); ART.softBig = A.add(genSoft(64));
    ART.ring = A.add(genRing(64)); ART.shadow = A.add(genShadow());
    ART.runeRing = A.add(genRuneRing()); ART.crosshair = A.add(genCrosshair()); ART.pot = A.add(genPot());
    for (int i = 0; i < 128; i++) ART.font[i] = -1;
    for (const Glyph& g : kFont) {
        Canvas c(5, 7);
        for (int y = 0; y < 7; y++) for (int x = 0; x < 5; x++)
            if (g.r[y] & (0x10 >> x)) c.set(x, y, Col{255, 255, 255}, 255);
        ART.font[(int)g.c] = A.add(c);
    }
    for (int i = 0; i < B_COUNT; i++) ART.icon[i] = A.add(genIcon(i));
}
static const SpriteRect& SR(int id) { return gAtlas.rects[(size_t)id]; }

// ============================================================================
//  GLSL
// ============================================================================
static const char* kHeader =
    "#version 330 core\n"
    "#define MAXL 40\n";

static const char* kFullscreenVS = R"GLSL(
out vec2 vUV;
void main() {
    vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));
    vUV = p;
    gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);
}
)GLSL";

// ---------------------------------------------------------------- sprites ---
static const char* kSpriteVS = R"GLSL(
layout(location = 0) in vec2 aPos;
layout(location = 1) in vec2 aUV;
layout(location = 2) in vec4 aCol;
layout(location = 3) in vec4 aFx;      // x flash, y dissolve, z seed, w surface type
uniform mat4 uProj;
out vec2 vUV;
out vec4 vCol;
out vec4 vFx;
void main() {
    vUV = aUV; vCol = aCol; vFx = aFx;
    gl_Position = uProj * vec4(aPos, 0.0, 1.0);
}
)GLSL";

static const char* kSpriteFS = R"GLSL(
in vec2 vUV;
in vec4 vCol;
in vec4 vFx;
out vec4 FragColor;
uniform sampler2D uAtlas;
uniform sampler2D uEmis;
uniform int uMode;   // 0 albedo(opaque)  1 alpha-blended  2 emissive layer  3 additive colour

float hash(vec2 p) {
    vec3 p3 = fract(vec3(p.xyx) * 0.1031);
    p3 += dot(p3, p3.yzx + 33.33);
    return fract((p3.x + p3.y) * p3.z);
}

void main() {
    vec4 t = texture(uAtlas, vUV);
    if ((uMode == 0 || uMode == 2) && t.a < 0.5) discard;
    float edge = 0.0;
    if (vFx.y > 0.0) {                                   // dissolve
        float n = hash(floor(vUV * 512.0) + vec2(vFx.z));
        if (n < vFx.y) discard;
        edge = 1.0 - smoothstep(0.0, 0.16, n - vFx.y);
    }
    vec3 base = mix(t.rgb * vCol.rgb, vec3(1.0), vFx.x);
    if (uMode == 0) {
        FragColor = vec4(mix(base, vec3(1.0, 0.6, 0.2), edge), vFx.w);
    } else if (uMode == 1) {
        FragColor = vec4(base, t.a * vCol.a);
    } else if (uMode == 2) {
        float m = texture(uEmis, vUV).r;
        vec3 e = t.rgb * vCol.rgb * m * vCol.a + vec3(1.0, 0.5, 0.15) * edge * 2.5 * vCol.a;
        FragColor = vec4(e, 1.0);
    } else {
        FragColor = vec4(t.rgb * vCol.rgb * t.a * vCol.a, 1.0);
    }
}
)GLSL";

// ---------------------------------------------------------------- lighting --
static const char* kLightFS = R"GLSL(
in vec2 vUV;
out vec4 FragColor;
uniform sampler2D uAlbedo;
uniform sampler2D uSdf;
uniform vec2  uCam;
uniform vec2  uMapPx;
uniform vec2  uRes;
uniform vec3  uAmbient;
uniform int   uCount;
uniform vec4  uL0[MAXL];     // xy position, z radius, w casts shadow
uniform vec3  uL1[MAXL];     // colour * intensity

float sdf(vec2 p) { return textureLod(uSdf, p / uMapPx, 0.0).r; }

// soft shadow: sphere-trace the wall distance field from the pixel towards the light
float shadowAt(vec2 p, vec2 lp, float k) {
    vec2 d = lp - p;
    float dist = length(d);
    if (dist < 2.0) return 1.0;
    vec2 dir = d / dist;
    float t = 3.0, res = 1.0;
    for (int i = 0; i < 30; i++) {
        float h = sdf(p + dir * t);
        res = min(res, k * h / t);
        if (res < 0.02) return 0.0;
        t += clamp(h, 1.5, 22.0);
        if (t >= dist - 1.0) break;
    }
    return smoothstep(0.0, 1.0, clamp(res, 0.0, 1.0));
}

void main() {
    vec4 a = texture(uAlbedo, vUV);
    vec2 wp = uCam + vec2(vUV.x * uRes.x, (1.0 - vUV.y) * uRes.y);
    float st = a.a;                       // 1 = floor / things, 0.5 = wall face, 0 = wall top / void
    bool cap  = st < 0.25;
    bool face = st >= 0.25 && st < 0.75;

    vec3 L = uAmbient;
    vec2 sp = wp;                          // where we sample shadows from
    if (face) sp = vec2(wp.x, (floor(wp.y / 16.0) + 1.0) * 16.0 + 2.0);
    else if (!cap && sdf(wp) < 1.0) {      // sprite overhanging a wall: use its feet
        sp.y += 8.0;
        if (sdf(sp) < 1.0) sp.y += 8.0;
    }

    if (cap) {
        for (int i = 0; i < MAXL; i++) {
            if (i >= uCount) break;
            float dist = length(uL0[i].xy - wp);
            float r = uL0[i].z;
            if (dist >= r) continue;
            float att = 1.0 - dist / r;
            L += uL1[i] * att * att * 0.20;
        }
    } else {
        for (int i = 0; i < MAXL; i++) {
            if (i >= uCount) break;
            vec2 lp = uL0[i].xy;
            float r = uL0[i].z;
            vec2 d = lp - wp;
            float dist = length(d);
            if (dist >= r) continue;
            float att = 1.0 - dist / r;
            att *= att;
            float sh = (uL0[i].w > 0.5) ? shadowAt(sp, lp, 7.0) : 1.0;
            float facing = 1.0;
            if (face) facing = clamp(d.y / max(dist, 1.0) * 1.3 + 0.25, 0.0, 1.0);
            L += uL1[i] * att * sh * facing;
        }
    }
    vec3 col = a.rgb * L;
    if (st > 0.75) col *= mix(0.62, 1.0, smoothstep(0.0, 12.0, sdf(wp)));   // contact shadow near walls
    FragColor = vec4(col, 1.0);
}
)GLSL";

// ---------------------------------------------------------------- post ------
static const char* kBrightFS = R"GLSL(
in vec2 vUV;
out vec4 FragColor;
uniform sampler2D uTex;
uniform vec2 uTexel;
void main() {
    vec3 c = texture(uTex, vUV + uTexel * vec2(-0.5, -0.5)).rgb
           + texture(uTex, vUV + uTexel * vec2( 0.5, -0.5)).rgb
           + texture(uTex, vUV + uTexel * vec2(-0.5,  0.5)).rgb
           + texture(uTex, vUV + uTexel * vec2( 0.5,  0.5)).rgb;
    c *= 0.25;
    float br = max(c.r, max(c.g, c.b));
    float k = smoothstep(1.0, 2.1, br);
    FragColor = vec4(min(c * k, vec3(16.0)), 1.0);
}
)GLSL";

static const char* kBlurFS = R"GLSL(
in vec2 vUV;
out vec4 FragColor;
uniform sampler2D uTex;
uniform vec2 uDir;
const float W[5] = float[5](0.227027, 0.1945946, 0.1216216, 0.054054, 0.016216);
void main() {
    vec3 r = texture(uTex, vUV).rgb * W[0];
    for (int i = 1; i < 5; i++) {
        r += texture(uTex, vUV + uDir * float(i)).rgb * W[i];
        r += texture(uTex, vUV - uDir * float(i)).rgb * W[i];
    }
    FragColor = vec4(r, 1.0);
}
)GLSL";

static const char* kCompFS = R"GLSL(
in vec2 vUV;
out vec4 FragColor;
uniform sampler2D uScene;
uniform sampler2D uB0;
uniform sampler2D uB1;
uniform sampler2D uB2;
uniform vec2  uRes;
uniform float uScale;        // window pixels per virtual pixel
uniform float uTime;
uniform float uAberr;
uniform float uFlash;
uniform float uFade;
uniform float uBloom;
uniform vec3  uTint;
uniform vec4  uSW[4];        // shockwave: uv.xy, radius(px), strength(px)

vec3 aces(vec3 x) { return clamp((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14), 0.0, 1.0); }
float hash(vec2 p) {
    vec3 p3 = fract(vec3(p.xyx) * 0.1031);
    p3 += dot(p3, p3.yzx + 33.33);
    return fract((p3.x + p3.y) * p3.z);
}
vec2 sharpUV(vec2 uv) {      // "sharp bilinear": crisp pixels without shimmering edges
    vec2 texel = uv * uRes;
    vec2 fl = floor(texel);
    vec2 s = fract(texel);
    vec2 rr = vec2(0.5 - 0.5 / max(uScale, 1.0));
    vec2 cd = s - 0.5;
    vec2 f = (cd - clamp(cd, -rr, rr)) * max(uScale, 1.0) + 0.5;
    return (fl + f) / uRes;
}

void main() {
    vec2 uv = vUV;
    vec2 off = vec2(0.0);
    for (int i = 0; i < 4; i++) {
        vec4 w = uSW[i];
        if (w.w > 0.0) {
            vec2 d = (uv - w.xy) * uRes;
            float dist = length(d);
            float ring = exp(-pow((dist - w.z) / 8.0, 2.0));
            off += (d / max(dist, 0.001)) * ring * w.w / uRes;
        }
    }
    uv += off;
    vec2 c = vUV - 0.5;
    float r2 = dot(c, c);
    vec2 ca = c * (0.0009 + uAberr + r2 * 0.0035);
    vec2 suv = sharpUV(uv);
    vec3 col;
    col.r = texture(uScene, suv + ca).r;
    col.g = texture(uScene, suv).g;
    col.b = texture(uScene, suv - ca).b;

    vec3 bloom = texture(uB0, uv).rgb * 0.22 + texture(uB1, uv).rgb * 0.32 + texture(uB2, uv).rgb * 0.46;
    col += bloom * uBloom;
    col += vec3(1.0, 0.10, 0.06) * uFlash * (0.15 + r2 * 2.6);

    col *= uTint;
    col = aces(col * 0.92);
    col = pow(col, vec3(1.0 / 2.2));
    col *= 1.0 - 0.60 * smoothstep(0.18, 0.78, length(c * vec2(1.0, 0.9)));
    col += (hash(gl_FragCoord.xy + fract(uTime) * 91.0) - 0.5) * 0.022;
    col *= uFade;
    FragColor = vec4(col, 1.0);
}
)GLSL";

// ============================================================================
//  GL helpers
// ============================================================================
static GLuint compileShader(GLenum type, const std::string& src) {
    GLuint s = glCreateShader(type);
    const char* c = src.c_str();
    glShaderSource(s, 1, &c, nullptr);
    glCompileShader(s);
    GLint ok = 0;
    glGetShaderiv(s, GL_COMPILE_STATUS, &ok);
    if (!ok) {
        char log[4096];
        glGetShaderInfoLog(s, sizeof(log), nullptr, log);
        std::fprintf(stderr, "Shader compile error:\n%s\n", log);
        std::exit(1);
    }
    return s;
}
static GLuint makeProgram(const char* vsBody, const char* fsBody) {
    GLuint vs = compileShader(GL_VERTEX_SHADER,   std::string(kHeader) + vsBody);
    GLuint fs = compileShader(GL_FRAGMENT_SHADER, std::string(kHeader) + fsBody);
    GLuint p = glCreateProgram();
    glAttachShader(p, vs); glAttachShader(p, fs);
    glLinkProgram(p);
    GLint ok = 0;
    glGetProgramiv(p, GL_LINK_STATUS, &ok);
    if (!ok) {
        char log[4096];
        glGetProgramInfoLog(p, sizeof(log), nullptr, log);
        std::fprintf(stderr, "Program link error:\n%s\n", log);
        std::exit(1);
    }
    glDeleteShader(vs); glDeleteShader(fs);
    return p;
}
static GLint uloc(GLuint p, const char* n) { return glGetUniformLocation(p, n); }
static void uFloat(GLuint p, const char* n, float v)  { glUniform1f(uloc(p, n), v); }
static void uInt(GLuint p, const char* n, int v)      { glUniform1i(uloc(p, n), v); }
static void uVec2(GLuint p, const char* n, vec2 v)    { glUniform2f(uloc(p, n), v.x, v.y); }
static void uVec3(GLuint p, const char* n, vec3 v)    { glUniform3f(uloc(p, n), v.x, v.y, v.z); }
static void uMat4(GLuint p, const char* n, const mat4& m) { glUniformMatrix4fv(uloc(p, n), 1, GL_FALSE, glm::value_ptr(m)); }

struct RT {
    GLuint fbo = 0, tex = 0;
    int w = 0, h = 0;
};
static RT makeRT(int w, int h, GLint ifmt, GLenum fmt, GLenum type, GLint filter) {
    RT r;
    r.w = w; r.h = h;
    glGenTextures(1, &r.tex);
    glBindTexture(GL_TEXTURE_2D, r.tex);
    glTexImage2D(GL_TEXTURE_2D, 0, ifmt, w, h, 0, fmt, type, nullptr);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, filter);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, filter);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    glGenFramebuffers(1, &r.fbo);
    glBindFramebuffer(GL_FRAMEBUFFER, r.fbo);
    glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, r.tex, 0);
    if (glCheckFramebufferStatus(GL_FRAMEBUFFER) != GL_FRAMEBUFFER_COMPLETE)
        std::fprintf(stderr, "Warning: framebuffer incomplete (%dx%d)\n", w, h);
    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    return r;
}

// ============================================================================
//  vertex batches
// ============================================================================
struct Vert { float x, y, u, v, r, g, b, a, f0, f1, f2, f3; };

struct Batch {
    std::vector<Vert> v;
    GLuint vao = 0, vbo = 0;

    void init() {
        glGenVertexArrays(1, &vao);
        glGenBuffers(1, &vbo);
        glBindVertexArray(vao);
        glBindBuffer(GL_ARRAY_BUFFER, vbo);
        const GLsizei stride = sizeof(Vert);
        glEnableVertexAttribArray(0); glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, stride, (void*)0);
        glEnableVertexAttribArray(1); glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, stride, (void*)(2 * sizeof(float)));
        glEnableVertexAttribArray(2); glVertexAttribPointer(2, 4, GL_FLOAT, GL_FALSE, stride, (void*)(4 * sizeof(float)));
        glEnableVertexAttribArray(3); glVertexAttribPointer(3, 4, GL_FLOAT, GL_FALSE, stride, (void*)(8 * sizeof(float)));
        glBindVertexArray(0);
        v.reserve(60000);
    }
    void clear() { v.clear(); }

    // (cx, cy) is the sprite centre in screen pixels.  rot = 0 snaps to the pixel grid.
    void quad(int spr, float cx, float cy, float w, float h, float rot, bool flipX, bool flipY,
              vec4 col, vec4 fx = vec4(0.f, 0.f, 0.f, 1.f)) {
        const SpriteRect& s = SR(spr);
        float u0 = s.u0, u1 = s.u1, v0 = s.v0, v1 = s.v1;
        if (flipX) std::swap(u0, u1);
        if (flipY) std::swap(v0, v1);
        float hx = w * 0.5f, hy = h * 0.5f;
        if (rot == 0.f) { cx = std::floor(cx - hx + 0.5f) + hx; cy = std::floor(cy - hy + 0.5f) + hy; }
        const float px[4] = {-hx, hx, hx, -hx}, py[4] = {-hy, -hy, hy, hy};
        const float uu[4] = {u0, u1, u1, u0}, vv[4] = {v0, v0, v1, v1};
        float cs = std::cos(rot), sn = std::sin(rot);
        Vert q[4];
        for (int i = 0; i < 4; i++)
            q[i] = {cx + px[i] * cs - py[i] * sn, cy + px[i] * sn + py[i] * cs, uu[i], vv[i],
                    col.x, col.y, col.z, col.w, fx.x, fx.y, fx.z, fx.w};
        v.push_back(q[0]); v.push_back(q[1]); v.push_back(q[2]);
        v.push_back(q[0]); v.push_back(q[2]); v.push_back(q[3]);
    }
    // explicit-UV quad (used for the minimap texture)
    void rawQuad(float x0, float y0, float x1, float y1, float u0, float v0, float u1, float v1, vec4 c) {
        const Vert q[4] = {{x0, y0, u0, v1, c.x, c.y, c.z, c.w, 0.f, 0.f, 0.f, 1.f}, {x1, y0, u1, v1, c.x, c.y, c.z, c.w, 0.f, 0.f, 0.f, 1.f},
                           {x1, y1, u1, v0, c.x, c.y, c.z, c.w, 0.f, 0.f, 0.f, 1.f}, {x0, y1, u0, v0, c.x, c.y, c.z, c.w, 0.f, 0.f, 0.f, 1.f}};
        v.push_back(q[0]); v.push_back(q[1]); v.push_back(q[2]);
        v.push_back(q[0]); v.push_back(q[2]); v.push_back(q[3]);
    }
    // natural-size sprite
    void spr(int id, float cx, float cy, vec4 col, bool flipX = false, float rot = 0.f, float scale = 1.f,
             vec4 fx = vec4(0.f, 0.f, 0.f, 1.f)) {
        const SpriteRect& s = SR(id);
        quad(id, cx, cy, s.w * scale, s.h * scale, rot, flipX, false, col, fx);
    }
    // a coloured line segment (uses the white dot sprite)
    void seg(vec2 a, vec2 b, float width, vec4 col) {
        vec2 d = b - a;
        float l = len2(d);
        if (l < 0.01f) return;
        quad(ART.dot, (a.x + b.x) * 0.5f, (a.y + b.y) * 0.5f, l, width, std::atan2(d.y, d.x), false, false, col);
    }
    void flush() {
        if (v.empty()) return;
        glBindVertexArray(vao);
        glBindBuffer(GL_ARRAY_BUFFER, vbo);
        glBufferData(GL_ARRAY_BUFFER, v.size() * sizeof(Vert), v.data(), GL_STREAM_DRAW);
        glDrawArrays(GL_TRIANGLES, 0, (GLsizei)v.size());
    }
};

// ============================================================================
//  Renderer: albedo pass -> lighting pass -> emissive/additive pass -> HUD ->
//            bloom -> composite
// ============================================================================
struct LightRec { vec2 p; float r; vec3 c; float shadow; };

struct FrameParams {
    vec2  cam = vec2(0.f, 0.f);
    vec3  ambient = vec3(0.f, 0.f, 0.f), tint = vec3(1.f, 1.f, 1.f);
    float time = 0.f, aberr = 0.f, flash = 0.f, fade = 1.f, bloom = 1.f;
    std::vector<LightRec> lights;
    vec4  sw[4];
};

struct Renderer {
    GLuint pSprite = 0, pLight = 0, pBright = 0, pBlur = 0, pComp = 0;
    GLuint texAtlas = 0, texEmis = 0, texSdf = 0, texMini = 0, emptyVAO = 0;
    RT albedo, lit, ping[3][2];
    Batch bTiles, bDecal, bEnt, bFx, bEmis, bAdd, bHud, bHudBack, bMini;
    mat4 proj;

    void init() {
        pSprite = makeProgram(kSpriteVS, kSpriteFS);
        pLight  = makeProgram(kFullscreenVS, kLightFS);
        pBright = makeProgram(kFullscreenVS, kBrightFS);
        pBlur   = makeProgram(kFullscreenVS, kBlurFS);
        pComp   = makeProgram(kFullscreenVS, kCompFS);
        glGenVertexArrays(1, &emptyVAO);
        proj = glm::ortho(0.f, (float)VW, (float)VH, 0.f);

        // atlas textures
        std::vector<uint8_t> rgba((size_t)Atlas::W * Atlas::H * 4), em((size_t)Atlas::W * Atlas::H);
        for (size_t i = 0; i < gAtlas.px.size(); i++) {
            const Px& p = gAtlas.px[i];
            rgba[i * 4] = p.r; rgba[i * 4 + 1] = p.g; rgba[i * 4 + 2] = p.b; rgba[i * 4 + 3] = p.a;
            em[i] = p.e;
        }
        glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
        glGenTextures(1, &texAtlas);
        glBindTexture(GL_TEXTURE_2D, texAtlas);
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA8, Atlas::W, Atlas::H, 0, GL_RGBA, GL_UNSIGNED_BYTE, rgba.data());
        setupTex(GL_NEAREST);
        glGenTextures(1, &texEmis);
        glBindTexture(GL_TEXTURE_2D, texEmis);
        glTexImage2D(GL_TEXTURE_2D, 0, GL_R8, Atlas::W, Atlas::H, 0, GL_RED, GL_UNSIGNED_BYTE, em.data());
        setupTex(GL_NEAREST);

        glGenTextures(1, &texSdf);
        glBindTexture(GL_TEXTURE_2D, texSdf);
        std::vector<float> blank((size_t)MAPW * SDF_S * MAPH * SDF_S, 0.f);
        glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, MAPW * SDF_S, MAPH * SDF_S, 0, GL_RED, GL_FLOAT, blank.data());
        setupTex(GL_LINEAR);

        glGenTextures(1, &texMini);
        glBindTexture(GL_TEXTURE_2D, texMini);
        std::vector<uint8_t> mblank((size_t)MAPW * MAPH * 4, 0);
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA8, MAPW, MAPH, 0, GL_RGBA, GL_UNSIGNED_BYTE, mblank.data());
        setupTex(GL_NEAREST);

        albedo = makeRT(VW, VH, GL_RGBA8, GL_RGBA, GL_UNSIGNED_BYTE, GL_NEAREST);
        lit    = makeRT(VW, VH, GL_RGBA16F, GL_RGBA, GL_FLOAT, GL_LINEAR);
        for (int L = 0; L < 3; L++) {
            int bw = std::max(1, VW >> (L + 1)), bh = std::max(1, VH >> (L + 1));
            ping[L][0] = makeRT(bw, bh, GL_RGBA16F, GL_RGBA, GL_FLOAT, GL_LINEAR);
            ping[L][1] = makeRT(bw, bh, GL_RGBA16F, GL_RGBA, GL_FLOAT, GL_LINEAR);
        }
        bTiles.init(); bDecal.init(); bEnt.init(); bFx.init(); bEmis.init(); bAdd.init(); bHud.init(); bHudBack.init(); bMini.init();
    }
    static void setupTex(GLint filter) {
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, filter);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, filter);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    }
    void uploadSdf(const std::vector<float>& d) {
        glBindTexture(GL_TEXTURE_2D, texSdf);
        glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, MAPW * SDF_S, MAPH * SDF_S, 0, GL_RED, GL_FLOAT, d.data());
    }
    void uploadMini(const std::vector<uint8_t>& d) {
        glBindTexture(GL_TEXTURE_2D, texMini);
        glTexSubImage2D(GL_TEXTURE_2D, 0, 0, 0, MAPW, MAPH, GL_RGBA, GL_UNSIGNED_BYTE, d.data());
    }
    void clearBatches() { bTiles.clear(); bDecal.clear(); bEnt.clear(); bFx.clear(); bEmis.clear(); bAdd.clear(); bHud.clear(); bHudBack.clear(); bMini.clear(); }

    void bindSpriteState(int mode) {
        glUseProgram(pSprite);
        uMat4(pSprite, "uProj", proj);
        uInt(pSprite, "uAtlas", 0);
        uInt(pSprite, "uEmis", 1);
        uInt(pSprite, "uMode", mode);
        glActiveTexture(GL_TEXTURE0); glBindTexture(GL_TEXTURE_2D, texAtlas);
        glActiveTexture(GL_TEXTURE1); glBindTexture(GL_TEXTURE_2D, texEmis);
        glActiveTexture(GL_TEXTURE0);
    }
    void fullscreen() { glBindVertexArray(emptyVAO); glDrawArrays(GL_TRIANGLES, 0, 3); }

    // Run every pass; the batches must already be filled.
    void render(const FrameParams& fp, int winW, int winH) {
        glDisable(GL_DEPTH_TEST);
        glDisable(GL_CULL_FACE);

        // 1) albedo (+ surface type in alpha)
        glBindFramebuffer(GL_FRAMEBUFFER, albedo.fbo);
        glViewport(0, 0, VW, VH);
        glClearColor(0.f, 0.f, 0.f, 0.f);
        glClear(GL_COLOR_BUFFER_BIT);
        glDisable(GL_BLEND);
        bindSpriteState(0);
        bTiles.flush();
        glEnable(GL_BLEND);
        glBlendFuncSeparate(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA, GL_ZERO, GL_ONE);   // keep surface-type alpha
        bindSpriteState(1);
        bDecal.flush();
        glDisable(GL_BLEND);
        bindSpriteState(0);
        bEnt.flush();
        glEnable(GL_BLEND);
        bindSpriteState(1);
        bFx.flush();
        glDisable(GL_BLEND);

        // 2) lighting
        glBindFramebuffer(GL_FRAMEBUFFER, lit.fbo);
        glViewport(0, 0, VW, VH);
        glUseProgram(pLight);
        glActiveTexture(GL_TEXTURE0); glBindTexture(GL_TEXTURE_2D, albedo.tex);
        glActiveTexture(GL_TEXTURE1); glBindTexture(GL_TEXTURE_2D, texSdf);
        glActiveTexture(GL_TEXTURE0);
        uInt(pLight, "uAlbedo", 0);
        uInt(pLight, "uSdf", 1);
        uVec2(pLight, "uCam", fp.cam);
        uVec2(pLight, "uMapPx", vec2((float)(MAPW * TS), (float)(MAPH * TS)));
        uVec2(pLight, "uRes", vec2((float)VW, (float)VH));
        uVec3(pLight, "uAmbient", fp.ambient);
        int n = std::min((int)fp.lights.size(), MAX_LIGHTS);
        uInt(pLight, "uCount", n);
        float l0[MAX_LIGHTS * 4], l1[MAX_LIGHTS * 3];
        for (int i = 0; i < n; i++) {
            const LightRec& L = fp.lights[(size_t)i];
            l0[i * 4] = L.p.x; l0[i * 4 + 1] = L.p.y; l0[i * 4 + 2] = L.r; l0[i * 4 + 3] = L.shadow;
            l1[i * 3] = L.c.x; l1[i * 3 + 1] = L.c.y; l1[i * 3 + 2] = L.c.z;
        }
        if (n > 0) {
            glUniform4fv(uloc(pLight, "uL0"), n, l0);
            glUniform3fv(uloc(pLight, "uL1"), n, l1);
        }
        fullscreen();

        // 3) emissive layers + additive effects
        glEnable(GL_BLEND);
        glBlendFunc(GL_ONE, GL_ONE);
        bindSpriteState(2);
        bEmis.flush();
        bindSpriteState(3);
        bAdd.flush();
        // 4) HUD (normal alpha blending, still HDR so it glows)
        glBlendFuncSeparate(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA, GL_ONE, GL_ONE_MINUS_SRC_ALPHA);
        bindSpriteState(1);
        bHudBack.flush();
        if (!bMini.v.empty()) {                      // minimap texture drawn between the frame and the HUD
            glActiveTexture(GL_TEXTURE0); glBindTexture(GL_TEXTURE_2D, texMini);
            bMini.flush();
            glBindTexture(GL_TEXTURE_2D, texAtlas);
        }
        bHud.flush();
        glDisable(GL_BLEND);

        // 5) bloom
        glBindVertexArray(emptyVAO);
        glActiveTexture(GL_TEXTURE0);
        glBindFramebuffer(GL_FRAMEBUFFER, ping[0][0].fbo);
        glViewport(0, 0, ping[0][0].w, ping[0][0].h);
        glUseProgram(pBright);
        glBindTexture(GL_TEXTURE_2D, lit.tex);
        uInt(pBright, "uTex", 0);
        uVec2(pBright, "uTexel", vec2(1.f / VW, 1.f / VH));
        glDrawArrays(GL_TRIANGLES, 0, 3);

        glUseProgram(pBlur);
        uInt(pBlur, "uTex", 0);
        auto pass = [&](const RT& src, const RT& dst, vec2 dir) {
            glBindFramebuffer(GL_FRAMEBUFFER, dst.fbo);
            glViewport(0, 0, dst.w, dst.h);
            glBindTexture(GL_TEXTURE_2D, src.tex);
            uVec2(pBlur, "uDir", dir);
            glDrawArrays(GL_TRIANGLES, 0, 3);
        };
        const int iters[3] = {2, 3, 4};
        for (int L = 0; L < 3; L++) {
            if (L > 0) pass(ping[L - 1][0], ping[L][0], vec2(0.f, 0.f));
            float bw = (float)ping[L][0].w, bh = (float)ping[L][0].h;
            for (int i = 0; i < iters[L]; i++) {
                pass(ping[L][0], ping[L][1], vec2(1.f / bw, 0.f));
                pass(ping[L][1], ping[L][0], vec2(0.f, 1.f / bh));
            }
        }

        // 6) composite to the window, letter-boxed to 16:9
        glBindFramebuffer(GL_FRAMEBUFFER, 0);
        glViewport(0, 0, winW, winH);
        glClearColor(0.f, 0.f, 0.f, 1.f);
        glClear(GL_COLOR_BUFFER_BIT);
        float scale = std::min((float)winW / VW, (float)winH / VH);
        int dw = (int)(VW * scale), dh = (int)(VH * scale);
        glViewport((winW - dw) / 2, (winH - dh) / 2, dw, dh);
        glUseProgram(pComp);
        glActiveTexture(GL_TEXTURE0); glBindTexture(GL_TEXTURE_2D, lit.tex);
        glActiveTexture(GL_TEXTURE1); glBindTexture(GL_TEXTURE_2D, ping[0][0].tex);
        glActiveTexture(GL_TEXTURE2); glBindTexture(GL_TEXTURE_2D, ping[1][0].tex);
        glActiveTexture(GL_TEXTURE3); glBindTexture(GL_TEXTURE_2D, ping[2][0].tex);
        uInt(pComp, "uScene", 0); uInt(pComp, "uB0", 1); uInt(pComp, "uB1", 2); uInt(pComp, "uB2", 3);
        uVec2(pComp, "uRes", vec2((float)VW, (float)VH));
        uFloat(pComp, "uScale", scale);
        uFloat(pComp, "uTime", fp.time);
        uFloat(pComp, "uAberr", fp.aberr);
        uFloat(pComp, "uFlash", fp.flash);
        uFloat(pComp, "uFade", fp.fade);
        uFloat(pComp, "uBloom", fp.bloom);
        uVec3(pComp, "uTint", fp.tint);
        float sw[16];
        for (int i = 0; i < 4; i++) { sw[i * 4] = fp.sw[i].x; sw[i * 4 + 1] = fp.sw[i].y; sw[i * 4 + 2] = fp.sw[i].z; sw[i * 4 + 3] = fp.sw[i].w; }
        glUniform4fv(uloc(pComp, "uSW"), 4, sw);
        fullscreen();
        glActiveTexture(GL_TEXTURE0);
    }
};

// ============================================================================
//  Dungeon generation
// ============================================================================
enum RoomType { R_START, R_COMBAT, R_TREASURE, R_BOSS };
enum TileKind : uint8_t { K_VOID = 0, K_FLOOR = 1, K_FACE = 2, K_CAP = 3 };

struct Room {
    int x = 0, y = 0, w = 0, h = 0;                 // interior, in tiles
    int type = R_COMBAT;
    int cellX = 0, cellY = 0;
    bool cleared = false, active = false, explored = false, waveSpawned = false;
    int wave = 0, waves = 1;
    float waveT = 0.f;
    std::vector<int> gates;                          // tile indices of this room's doorway
    vec2 center() const { return vec2((x + w * 0.5f) * TS, (y + h * 0.5f) * TS); }
    bool contains(vec2 p, float margin) const {
        return p.x >= x * TS + margin && p.x < (x + w) * TS - margin && p.y >= y * TS + margin && p.y < (y + h) * TS - margin;
    }
};

struct Torch { int tx, ty; float phase; };
struct PropSpawn { vec2 pos = vec2(0.f, 0.f); };

struct Theme { const char* name; vec3 tint, ambient, torch; };
static const Theme kThemes[3] = {
    {"THE CRYPT",      vec3(0.80f, 0.90f, 1.15f), vec3(0.080f, 0.090f, 0.160f), vec3(1.00f, 0.60f, 0.26f)},
    {"MOSSY CAVERNS",  vec3(0.82f, 1.06f, 0.82f), vec3(0.050f, 0.115f, 0.080f), vec3(0.45f, 1.00f, 0.62f)},
    {"EMBER HALLS",    vec3(1.12f, 0.86f, 0.80f), vec3(0.135f, 0.050f, 0.050f), vec3(1.00f, 0.34f, 0.14f)},
};

struct Dungeon {
    std::vector<uint8_t> solid, gate, closed, gateHoriz, kind, variant, explored;
    std::vector<int8_t>  roomAt;
    std::vector<Room>    rooms;
    std::vector<Torch>   torches;
    std::vector<PropSpawn> props;
    std::vector<float>   sdf;
    std::vector<int16_t> flow;
    vec2 startPos = vec2(0.f, 0.f), portalPos = vec2(0.f, 0.f);
    int theme = 0, gen = 0;

    static int idx(int x, int y) { return y * MAPW + x; }
    static bool inb(int x, int y) { return x >= 0 && y >= 0 && x < MAPW && y < MAPH; }
    bool blocked(int x, int y) const { return !inb(x, y) || solid[(size_t)idx(x, y)] || closed[(size_t)idx(x, y)]; }
    bool blockedPx(float px, float py) const { return blocked((int)std::floor(px / TS), (int)std::floor(py / TS)); }

    int roomIndexAt(vec2 p, float margin = 0.f) const {
        for (size_t i = 0; i < rooms.size(); i++) if (rooms[i].contains(p, margin)) return (int)i;
        return -1;
    }

    // line of sight between two points (walls and closed gates block)
    bool los(vec2 a, vec2 b) const {
        vec2 d = b - a;
        float l = len2(d);
        int n = (int)(l / 4.f) + 1;
        for (int i = 1; i < n; i++) {
            vec2 p = a + d * ((float)i / n);
            if (blockedPx(p.x, p.y)) return false;
        }
        return true;
    }

    void generate(int floorNo) {
        gen++;
        const int CW = 4, CH = 3, CSX = MAPW / CW, CSY = MAPH / CH;
        const size_t N = (size_t)MAPW * MAPH;
        solid.assign(N, 1); gate.assign(N, 0); closed.assign(N, 0); gateHoriz.assign(N, 0);
        kind.assign(N, K_VOID); variant.assign(N, 0); explored.assign(N, 0); roomAt.assign(N, -1);
        rooms.clear(); torches.clear(); props.clear();
        theme = (floorNo - 1) % 3;

        // ---- choose which grid cells hold a room (random growth => connected) ----
        int nRooms = clampi(6 + floorNo, 7, 10);
        std::vector<int> cellRoom((size_t)CW * CH, -1);
        struct Cell { int x, y; };
        std::vector<Cell> cells;
        std::vector<std::pair<int, int>> edges;
        cells.push_back({ri(0, CW - 1), ri(0, CH - 1)});
        cellRoom[(size_t)(cells[0].y * CW + cells[0].x)] = 0;
        static const int ddx[4] = {1, -1, 0, 0}, ddy[4] = {0, 0, 1, -1};
        for (int guard = 0; (int)cells.size() < nRooms && guard < 5000; guard++) {
            int p = ri(0, (int)cells.size() - 1), k = ri(0, 3);
            int nx = cells[(size_t)p].x + ddx[k], ny = cells[(size_t)p].y + ddy[k];
            if (nx < 0 || ny < 0 || nx >= CW || ny >= CH || cellRoom[(size_t)(ny * CW + nx)] >= 0) continue;
            cellRoom[(size_t)(ny * CW + nx)] = (int)cells.size();
            edges.push_back({p, (int)cells.size()});
            cells.push_back({nx, ny});
        }
        for (size_t i = 0; i < cells.size(); i++) for (size_t j = i + 1; j < cells.size(); j++) {   // extra loops
            if (std::abs(cells[i].x - cells[j].x) + std::abs(cells[i].y - cells[j].y) != 1) continue;
            bool have = false;
            for (auto& e : edges) if ((e.first == (int)i && e.second == (int)j) || (e.first == (int)j && e.second == (int)i)) have = true;
            if (!have && chance(0.22f)) edges.push_back({(int)i, (int)j});
        }

        // ---- carve rooms ----
        for (size_t i = 0; i < cells.size(); i++) {
            Room r;
            r.cellX = cells[i].x; r.cellY = cells[i].y;
            r.w = ri(11, CSX - 6); r.h = ri(9, CSY - 6);
            r.x = r.cellX * CSX + ri(3, CSX - 3 - r.w);
            r.y = r.cellY * CSY + ri(3, CSY - 3 - r.h);
            for (int y = r.y; y < r.y + r.h; y++) for (int x = r.x; x < r.x + r.w; x++) {
                solid[(size_t)idx(x, y)] = 0;
                roomAt[(size_t)idx(x, y)] = (int8_t)i;
            }
            rooms.push_back(r);
        }

        // ---- corridors (3 tiles wide) with a gateway on each end ----
        auto carve = [&](int x0, int y0, int x1, int y1) {
            for (int y = std::max(1, y0); y <= std::min(MAPH - 2, y1); y++)
                for (int x = std::max(1, x0); x <= std::min(MAPW - 2, x1); x++) solid[(size_t)idx(x, y)] = 0;
        };
        auto addGate = [&](int room, int x0, int y0, int x1, int y1, bool horiz) {
            for (int y = y0; y <= y1; y++) for (int x = x0; x <= x1; x++) {
                size_t i = (size_t)idx(x, y);
                gate[i] = 1; gateHoriz[i] = horiz ? 1 : 0;
                rooms[(size_t)room].gates.push_back((int)i);
            }
        };
        for (auto& e : edges) {
            int a = e.first, b = e.second;
            if (cells[(size_t)a].y == cells[(size_t)b].y) {                         // horizontal neighbours
                int l = cells[(size_t)a].x < cells[(size_t)b].x ? a : b, r = l == a ? b : a;
                Room& L = rooms[(size_t)l]; Room& R = rooms[(size_t)r];
                int ya = ri(L.y + 2, L.y + L.h - 3), yb = ri(R.y + 2, R.y + R.h - 3);
                int xs = L.x + L.w, xe = R.x - 1, mx = (xs + xe) / 2;
                carve(xs, ya - 1, mx + 1, ya + 1);
                carve(mx - 1, std::min(ya, yb) - 1, mx + 1, std::max(ya, yb) + 1);
                carve(mx - 1, yb - 1, xe, yb + 1);
                addGate(l, xs, ya - 1, xs, ya + 1, true);
                addGate(r, xe, yb - 1, xe, yb + 1, true);
            } else {                                                                // vertical neighbours
                int t = cells[(size_t)a].y < cells[(size_t)b].y ? a : b, bo = t == a ? b : a;
                Room& T = rooms[(size_t)t]; Room& B = rooms[(size_t)bo];
                int xa = ri(T.x + 2, T.x + T.w - 3), xb = ri(B.x + 2, B.x + B.w - 3);
                int ys = T.y + T.h, ye = B.y - 1, my = (ys + ye) / 2;
                carve(xa - 1, ys, xa + 1, my + 1);
                carve(std::min(xa, xb) - 1, my - 1, std::max(xa, xb) + 1, my + 1);
                carve(xb - 1, my - 1, xb + 1, ye);
                addGate(t, xa - 1, ys, xa + 1, ys, false);
                addGate(bo, xb - 1, ye, xb + 1, ye, false);
            }
        }

        // ---- room roles ----
        int n = (int)rooms.size();
        std::vector<std::vector<int>> adj((size_t)n);
        for (auto& e : edges) { adj[(size_t)e.first].push_back(e.second); adj[(size_t)e.second].push_back(e.first); }
        std::vector<int> dist((size_t)n, -1);
        std::vector<int> q; q.push_back(0); dist[0] = 0;
        for (size_t qi = 0; qi < q.size(); qi++)
            for (int nb : adj[(size_t)q[qi]]) if (dist[(size_t)nb] < 0) { dist[(size_t)nb] = dist[(size_t)q[qi]] + 1; q.push_back(nb); }
        int boss = 1;
        for (int i = 1; i < n; i++) if (dist[(size_t)i] > dist[(size_t)boss]) boss = i;
        int treasure = -1;
        for (int i = 1; i < n; i++)
            if (i != boss && adj[(size_t)i].size() == 1 && (treasure < 0 || dist[(size_t)i] > dist[(size_t)treasure])) treasure = i;
        if (treasure < 0) for (int i = 1; i < n; i++) if (i != boss) { treasure = i; break; }
        for (int i = 0; i < n; i++) {
            Room& r = rooms[(size_t)i];
            r.type = i == 0 ? R_START : (i == boss ? R_BOSS : (i == treasure ? R_TREASURE : R_COMBAT));
            r.waves = r.type == R_BOSS ? 1 : (floorNo >= 3 ? 3 : 2);
            r.cleared = (r.type == R_START || r.type == R_TREASURE);
        }

        // ---- pillars for cover (also great shadow casters) ----
        for (auto& r : rooms) {
            if (r.type != R_COMBAT && r.type != R_BOSS) continue;
            if (r.w < 13 || r.h < 10) continue;
            int np = ri(1, 3);
            std::vector<std::pair<int, int>> placed;
            for (int k = 0; k < np * 6 && (int)placed.size() < np; k++) {
                int px = ri(r.x + 3, r.x + r.w - 5), py = ri(r.y + 3, r.y + r.h - 5);
                bool ok = true;
                for (int gi : r.gates) {
                    int gx = gi % MAPW, gy = gi / MAPW;
                    if (std::abs(gx - px) < 6 && std::abs(gy - py) < 6) ok = false;
                }
                for (auto& pp : placed) if (std::abs(pp.first - px) < 5 && std::abs(pp.second - py) < 5) ok = false;
                if (r.type == R_BOSS && std::abs(px - (r.x + r.w / 2)) < 4 && std::abs(py - (r.y + r.h / 2)) < 4) ok = false;
                if (!ok) continue;
                placed.push_back({px, py});
                for (int y = py; y < py + 2; y++) for (int x = px; x < px + 2; x++) solid[(size_t)idx(x, y)] = 1;
            }
        }

        // ---- classify tiles for rendering ----
        for (int y = 0; y < MAPH; y++) for (int x = 0; x < MAPW; x++) {
            size_t i = (size_t)idx(x, y);
            if (!solid[i]) { kind[i] = K_FLOOR; continue; }
            if (inb(x, y + 1) && !solid[(size_t)idx(x, y + 1)]) { kind[i] = K_FACE; variant[i] = (uint8_t)ri(0, 2); continue; }
            bool nearFloor = false;
            for (int dy = -2; dy <= 2 && !nearFloor; dy++) for (int dx = -2; dx <= 2; dx++)
                if (inb(x + dx, y + dy) && !solid[(size_t)idx(x + dx, y + dy)]) { nearFloor = true; break; }
            kind[i] = nearFloor ? K_CAP : K_VOID;
        }
        for (int y = 0; y < MAPH; y++) for (int x = 0; x < MAPW; x++) {
            size_t i = (size_t)idx(x, y);
            if (kind[i] == K_FLOOR) {
                int roll = ri(0, 99);
                variant[i] = roll < 38 ? 0 : roll < 76 ? 1 : roll < 84 ? 2 : roll < 91 ? 3 : roll < 97 ? 4 : 5;
            } else if (kind[i] == K_CAP) {
                int m = 0;
                if (inb(x, y - 1) && !solid[(size_t)idx(x, y - 1)]) m |= 1;
                if (inb(x + 1, y) && !solid[(size_t)idx(x + 1, y)]) m |= 2;
                if (inb(x, y + 1) && !solid[(size_t)idx(x, y + 1)]) m |= 4;
                if (inb(x - 1, y) && !solid[(size_t)idx(x - 1, y)]) m |= 8;
                variant[i] = (uint8_t)m;
            }
        }

        // ---- torches on the north walls ----
        for (auto& r : rooms) {
            int step = (r.type == R_COMBAT) ? 5 : 3;
            for (int x = r.x + 1 + ri(0, 1); x < r.x + r.w - 1; x += step) {
                int ty = r.y - 1;
                if (inb(x, ty) && kind[(size_t)idx(x, ty)] == K_FACE && !gate[(size_t)idx(x, ty)])
                    torches.push_back({x, ty, rf(0.f, 6.28f)});
            }
        }

        // ---- breakable pots ----
        for (auto& r : rooms) {
            if (r.type != R_COMBAT && r.type != R_TREASURE) continue;
            int np = ri(1, 4);
            for (int k = 0; k < np; k++) {
                int tx = ri(r.x + 1, r.x + r.w - 2), ty = ri(r.y + 1, r.y + r.h - 2);
                if (solid[(size_t)idx(tx, ty)]) continue;
                props.push_back({vec2(tx * TS + 8.f, ty * TS + 8.f)});
            }
        }

        startPos = rooms[0].center();
        portalPos = rooms[(size_t)boss].center();
        computeSdf();
    }

    // distance (in pixels) to the nearest wall tile, sampled at SDF_S texels per tile
    void computeSdf() {
        const int SW = MAPW * SDF_S, SH = MAPH * SDF_S, R = 4;
        sdf.assign((size_t)SW * SH, 0.f);
        const float texel = (float)TS / SDF_S;
        for (int ty = 0; ty < SH; ty++) for (int tx = 0; tx < SW; tx++) {
            float px = (tx + 0.5f) * texel, py = (ty + 0.5f) * texel;
            int cx = (int)(px / TS), cy = (int)(py / TS);
            float best = (float)(R * TS);
            for (int dy = -R; dy <= R; dy++) for (int dx = -R; dx <= R; dx++) {
                int x = cx + dx, y = cy + dy;
                bool sol = !inb(x, y) || solid[(size_t)idx(x, y)];
                if (!sol) continue;
                float ax = (float)(x * TS), ay = (float)(y * TS);
                float ddx = std::max(std::max(ax - px, 0.f), px - (ax + TS));
                float ddy = std::max(std::max(ay - py, 0.f), py - (ay + TS));
                float d = std::sqrt(ddx * ddx + ddy * ddy);
                if (d < best) best = d;
            }
            sdf[(size_t)ty * SW + tx] = best;
        }
    }

    // ---- flow field: BFS distance (in tiles) to the player over walkable tiles ----
    void computeFlow(const std::vector<vec2>& targets) {
        const int INF = 30000;
        flow.assign((size_t)MAPW * MAPH, (int16_t)INF);
        std::vector<int> q;
        q.reserve((size_t)MAPW * MAPH);
        for (const vec2& target : targets) {
            int tx = clampi((int)(target.x / TS), 0, MAPW - 1), ty = clampi((int)(target.y / TS), 0, MAPH - 1);
            if (flow[(size_t)idx(tx, ty)] == 0) continue;
            q.push_back(idx(tx, ty));
            flow[(size_t)idx(tx, ty)] = 0;
        }
        for (size_t qi = 0; qi < q.size(); qi++) {
            int cur = q[qi], cx = cur % MAPW, cy = cur / MAPW;
            static const int dx4[4] = {1, -1, 0, 0}, dy4[4] = {0, 0, 1, -1};
            for (int k = 0; k < 4; k++) {
                int nx = cx + dx4[k], ny = cy + dy4[k];
                if (blocked(nx, ny)) continue;
                size_t ni = (size_t)idx(nx, ny);
                if (flow[ni] != INF) continue;
                flow[ni] = (int16_t)(flow[(size_t)cur] + 1);
                q.push_back((int)ni);
            }
        }
    }
    vec2 flowDir(vec2 pos) const {
        int cx = clampi((int)(pos.x / TS), 0, MAPW - 1), cy = clampi((int)(pos.y / TS), 0, MAPH - 1);
        int best = flow.empty() ? 30000 : flow[(size_t)idx(cx, cy)];
        int bx = cx, by = cy;
        for (int dy = -1; dy <= 1; dy++) for (int dx = -1; dx <= 1; dx++) {
            if (!dx && !dy) continue;
            int nx = cx + dx, ny = cy + dy;
            if (blocked(nx, ny)) continue;
            if (dx && dy && (blocked(cx + dx, cy) || blocked(cx, cy + dy))) continue;
            int v = flow[(size_t)idx(nx, ny)];
            if (v < best) { best = v; bx = nx; by = ny; }
        }
        if (bx == cx && by == cy) return vec2(0.f, 0.f);
        return norm2(vec2(bx * TS + 8.f, by * TS + 8.f) - pos);
    }
};

// ============================================================================
//  Game logic (no OpenGL in here - the renderer only reads this state)
//  Works for 1..4 players:  NR_SOLO (offline), NR_HOST (runs the real game and
//  broadcasts it), NR_CLIENT (a thin replica that predicts only its own player).
// ============================================================================
enum Mode { M_TITLE, M_PLAY, M_BOON, M_DEAD, M_PAUSE };
enum EType { E_SLIME, E_SLIME_S, E_BAT, E_ARCHER, E_MAGE, E_BRUTE, E_KING, E_LICH, E_COUNT };
enum BulletKind { BK_PLAYER, BK_ORB, BK_ARROW, BK_SLIME, BK_LICH };
enum PartKind { PK_SPARK, PK_EMBER, PK_SMOKE, PK_DEBRIS, PK_GLOW };
enum PickKind { PU_HEART, PU_SOUL, PU_RUNE };
enum NetRole { NR_SOLO, NR_HOST, NR_CLIENT };
enum FxType { FX_SPARK = 1, FX_BURST, FX_EMBER, FX_SMOKE, FX_DEBRIS, FX_GLOW, FX_DECAL, FX_SHOCK, FX_BOOM, FX_TEXT, FX_ZAP };

static constexpr int MAX_PLAYERS = 4;
static constexpr int NET_PORT = 7777;
static constexpr int NET_VERSION = 1;

struct EDef { const char* name; float hp, r, speed; int contact, cost, souls; };
static const EDef kEDef[E_COUNT] = {
    {"SLIME",           4.0f,  6.0f, 52.f, 1, 1, 1},
    {"SLIMELING",       2.0f,  4.0f, 66.f, 1, 1, 1},
    {"BAT",             2.5f,  5.0f, 80.f, 1, 1, 1},
    {"SKELETON",        4.0f,  5.0f, 40.f, 1, 2, 2},
    {"CULTIST",         5.0f,  5.0f, 34.f, 1, 3, 3},
    {"BRUTE",          18.0f,  9.0f, 38.f, 2, 4, 5},
    {"THE SLIME KING", 90.0f, 14.0f, 0.f,  2, 0, 30},
    {"THE HOLLOW KING",110.0f,11.0f, 0.f,  2, 0, 40},
};

struct BoonInfo { const char* name; const char* l1; const char* l2; vec3 col; int maxStacks; };
static const BoonInfo kBoons[B_COUNT] = {
    {"TWIN BOLTS",      "+1 PROJECTILE",  "SHOTS FAN OUT",   vec3(0.4f, 0.9f, 1.0f), 3},
    {"SWIFT CASTING",   "+25% FIRE RATE", "STACKS",          vec3(1.0f, 0.9f, 0.3f), 4},
    {"HEAVY HEX",       "+40% DAMAGE",    "SLOWER CASTING",  vec3(1.0f, 0.4f, 0.3f), 4},
    {"PIERCING GAZE",   "SHOTS PIERCE",   "+2 ENEMIES",      vec3(0.6f, 0.8f, 1.0f), 3},
    {"RICOCHET",        "SHOTS BOUNCE",   "OFF WALLS +2",    vec3(0.5f, 1.0f, 0.6f), 3},
    {"EMBER HEART",     "+2 MAX HEALTH",  "HEAL FULLY",      vec3(1.0f, 0.3f, 0.4f), 5},
    {"WIND BOOTS",      "+15% MOVE SPEED","FASTER DASH",     vec3(0.7f, 1.0f, 0.9f), 3},
    {"SEEKER SIGIL",    "SHOTS HOME IN",  "ON ENEMIES",      vec3(1.0f, 0.5f, 1.0f), 3},
    {"CHAIN LIGHTNING", "HITS ARC TO A",  "NEARBY ENEMY",    vec3(0.7f, 0.7f, 1.0f), 3},
    {"VOLATILE CORE",   "SHOTS EXPLODE",  "ON IMPACT",       vec3(1.0f, 0.6f, 0.2f), 3},
    {"FROSTBITE",       "HITS SLOW",      "ENEMIES",         vec3(0.6f, 0.9f, 1.0f), 3},
    {"WISP COMPANIONS", "ORBITING WISPS", "BURN FOES",       vec3(0.5f, 1.0f, 0.8f), 3},
    {"VAMPIRIC SOUL",   "HEART DROP",     "CHANCE ON KILL",  vec3(0.9f, 0.2f, 0.4f), 4},
    {"LANTERN OIL",     "BIGGER LIGHT",   "PICKUP MAGNET",   vec3(1.0f, 0.8f, 0.4f), 3},
};

// ------------------------------------------------------- byte (de)serialiser
struct ByteWriter {
    std::vector<uint8_t> b;
    void u8(int v)  { b.push_back((uint8_t)(v & 255)); }
    void u16(int v) { b.push_back((uint8_t)(v & 255)); b.push_back((uint8_t)((v >> 8) & 255)); }
    void u32(uint32_t v) { for (int i = 0; i < 4; i++) b.push_back((uint8_t)((v >> (8 * i)) & 255)); }
    void i16(int v) { u16(clampi(v, -32768, 32767) & 0xFFFF); }
    void f32(float f) { uint32_t u; std::memcpy(&u, &f, 4); u32(u); }
    void v2(vec2 v) { f32(v.x); f32(v.y); }
    void v3(vec3 v) { f32(v.x); f32(v.y); f32(v.z); }
    void pos(vec2 p) { i16((int)std::lround(p.x * 16.f)); i16((int)std::lround(p.y * 16.f)); }
    void str(const std::string& s) { size_t n = std::min<size_t>(s.size(), 255); u8((int)n); for (size_t i = 0; i < n; i++) b.push_back((uint8_t)s[i]); }
    void raw(const uint8_t* p, size_t n) { b.insert(b.end(), p, p + n); }
    void clear() { b.clear(); }
};
struct ByteReader {
    const uint8_t* d; size_t n; size_t i = 0; bool ok = true;
    ByteReader(const uint8_t* dd, size_t nn) : d(dd), n(nn) {}
    bool need(size_t k) { if (i + k > n) { ok = false; i = n; return false; } return true; }
    int u8()  { if (!need(1)) return 0; return d[i++]; }
    int u16() { if (!need(2)) return 0; int v = d[i] | (d[i + 1] << 8); i += 2; return v; }
    uint32_t u32() { if (!need(4)) return 0; uint32_t v = (uint32_t)d[i] | ((uint32_t)d[i + 1] << 8) | ((uint32_t)d[i + 2] << 16) | ((uint32_t)d[i + 3] << 24); i += 4; return v; }
    int i16() { int v = u16(); return v >= 32768 ? v - 65536 : v; }
    float f32() { uint32_t u = u32(); float f; std::memcpy(&f, &u, 4); return f; }
    vec2 v2() { float x = f32(); float y = f32(); return vec2(x, y); }
    vec3 v3() { float x = f32(); float y = f32(); float z = f32(); return vec3(x, y, z); }
    vec2 pos() { float x = (float)i16() / 16.f; float y = (float)i16() / 16.f; return vec2(x, y); }
    std::string str() { int l = u8(); std::string s; if (!need((size_t)l)) return s; s.assign((const char*)d + i, (size_t)l); i += (size_t)l; return s; }
    const uint8_t* raw(size_t k) { if (!need(k)) return nullptr; const uint8_t* p = d + i; i += k; return p; }
    bool done() const { return i >= n; }
};

struct Input {
    vec2 move = vec2(0.f, 0.f), aim = vec2(VW * 0.5f, VH * 0.5f);
    bool fire = false, dash = false, start = false, pause = false, click = false, confirm = false, quit = false;
    bool hostKey = false, joinKey = false, backspace = false, enter = false;
    int pick = -1, menuMove = 0;
    std::string typed;
};

struct Stats {
    int   shots = 1, pierce = 0, bounce = 0, chain = 0, vol = 0, wisps = 0, maxHp = 6, maxDash = 2;
    float fireInt = 0.3f, dmg = 1.f, bulletSpeed = 250.f, homing = 0.f, frost = 0.f, vamp = 0.f;
    float light = 1.f, magnet = 40.f, moveSpeed = 78.f, dashCd = 1.f;
};

struct Player {
    vec2  pos = vec2(0.f, 0.f), vel = vec2(0.f, 0.f), kb = vec2(0.f, 0.f), dashDir = vec2(0.f, 0.f), aimDir = vec2(1.f, 0.f), tpos = vec2(0.f, 0.f);
    float r = 4.5f, fireT = 0.f, dashT = 0.f, invuln = 0.f, animT = 0.f, ghostT = 0.f, dashRecharge = 0.f, wispAng = 0.f, muzzle = 0.f;
    int   hp = 6, maxHp = 6, dashCharges = 2, slot = 0, dashCount = 0, dashSeen = 0;
    int   boon[B_COUNT] = {};
    int   boonChoice[3] = {0, 0, 0}, boonChoices = 0;
    bool  active = false, dead = false, visible = true, facingLeft = false, moving = false, fireHeld = false, choosing = false, dashing = false;
    Stats st;
};

struct Enemy {
    int   id = 0, type = 0, state = 0, counter = 0, pat = 0, room = -1, lastHit = 0;
    vec2  pos = vec2(0.f, 0.f), kb = vec2(0.f, 0.f), dir = vec2(0.f, 0.f), tpos = vec2(0.f, 0.f);
    float hp = 1.f, maxHp = 1.f, r = 5.f, t = 0.f, flash = 0.f, spawn = 0.f, slow = 0.f, aiT = 0.f, patT = 0.f, fireT = 0.f;
    float spiral = 0.f, dissolve = 0.f, dyingT = 0.f, wispCd = 0.f, phase = 0.f, warn = 0.f, strafe = 1.f, seed = 0.f;
    bool  dying = false, faceLeft = false, boss = false;
};

struct Bullet {
    vec2  pos = vec2(0.f, 0.f), vel = vec2(0.f, 0.f);
    float r = 3.f, dmg = 1.f, life = 2.f, homing = 0.f, frost = 0.f, trail = 0.f;
    bool  friendly = false, dead = false, crit = false;
    int   kind = 0, pierce = 0, bounce = 0, chain = 0, vol = 0, nhit = 0, owner = 0;
    vec3  col = vec3(1.f, 1.f, 1.f);
    int   hit[6] = {0, 0, 0, 0, 0, 0};
};

struct Pickup { int type = 0; vec2 pos = vec2(0.f, 0.f), vel = vec2(0.f, 0.f); float t = 0.f; bool dead = false; };
struct Prop   { vec2 pos = vec2(0.f, 0.f); int hp = 1; float shake = 0.f; bool dead = false; };
struct Part   { vec2 p = vec2(0.f, 0.f), v = vec2(0.f, 0.f); float life = 1.f, maxLife = 1.f, size = 1.f, drag = 0.f, grow = 0.f, alpha = 1.f, seed = 0.f; vec3 col = vec3(1.f, 1.f, 1.f); int kind = 0; };
struct FloatText { vec2 p = vec2(0.f, 0.f); float life = 1.f, maxLife = 1.f; std::string s; vec3 col = vec3(1.f, 1.f, 1.f); int scale = 1; };
struct Zap  { vec2 a = vec2(0.f, 0.f), b = vec2(0.f, 0.f); float life = 0.2f; vec3 col = vec3(1.f, 1.f, 1.f); int seed = 0; };
struct Wave { vec2 pos = vec2(0.f, 0.f); float age = 0.f, dur = 0.5f, maxR = 60.f, strength = 4.f; };
struct Boom { vec2 pos = vec2(0.f, 0.f); float life = 0.3f, maxLife = 0.3f, radius = 60.f; vec3 col = vec3(1.f, 1.f, 1.f); };
struct Decal { vec2 p = vec2(0.f, 0.f); vec3 col = vec3(1.f, 1.f, 1.f); float size = 2.f, alpha = 0.8f; };
struct Ghost { vec2 pos = vec2(0.f, 0.f); float life = 0.25f; bool left = false; int frame = 0, slot = 0; };
struct Spawner { int type; vec2 pos; float delay; int room; };

static void loadBest(int& best) {
    best = 0;
    if (FILE* f = std::fopen("emberdeep.sav", "rb")) { int v = 0; if (std::fread(&v, sizeof(int), 1, f) == 1 && v > 0 && v < 100000000) best = v; std::fclose(f); }
}
static void saveBest(int best) {
    if (FILE* f = std::fopen("emberdeep.sav", "wb")) { std::fwrite(&best, sizeof(int), 1, f); std::fclose(f); }
}

// ------------------------------------------------ networking hooks (see below)
struct Game;
struct NetState;
static bool netStartHost(Game& g, int port);
static bool netStartJoin(Game& g, const std::string& addr);
static void netShutdown(Game& g);
static void netPollHost(Game& g);
static void netSendHost(Game& g, float dt);
static void netPollClient(Game& g);
static void netSendClient(Game& g, float dt, const Input& in);
static void netHostFloor(Game& g);
static void netHostBanner(Game& g, int slot, const std::string& t, const std::string& sub, float dur, vec3 col);
static void netHostBoonOffer(Game& g, int slot);
static void netHostHurt(Game& g, int slot, int dmg, vec2 kb);
static void netHostTeleport(Game& g, int slot, vec2 pos);
static void netClientBoonPick(Game& g, int pickSlot);

struct Game {
    // records an effect call (only the outermost one) so the host can replay it on every client
    struct FxScope {
        Game& g; bool rec;
        explicit FxScope(Game& gg) : g(gg), rec(gg.fxRecord && gg.fxDepth == 0) { g.fxDepth++; }
        ~FxScope() { g.fxDepth--; }
    };

    Dungeon D;
    int   role = NR_SOLO, mode = M_TITLE, floorNo = 1, me = 0;
    float time = 0.f;
    Player players[MAX_PLAYERS];
    std::vector<Enemy>     en;
    std::vector<Bullet>    bullets;
    std::vector<Pickup>    pickups;
    std::vector<Prop>      props;
    std::vector<Part>      parts;
    std::vector<FloatText> texts;
    std::vector<Zap>       zaps;
    std::vector<Wave>      waves;
    std::vector<Boom>      booms;
    std::vector<Decal>     decals;
    std::vector<Ghost>     ghosts;
    std::vector<Spawner>   pend;
    size_t decalHead = 0;

    vec2  cam = vec2(0.f, 0.f), camI = vec2(0.f, 0.f), aimWorld = vec2(0.f, 0.f), aimScreen = vec2(VW * 0.5f, VH * 0.5f);
    float trauma = 0.f, hitstop = 0.f, timeScale = 1.f, redFlash = 0.f, fade = 1.f, deadT = 0.f, flowT = 0.f, runTime = 0.f;
    int   souls = 0, kills = 0, best = 0, nextId = 1, clearedCombat = 0, boonSel = 0;
    bool  portalOpen = false, descending = false, miniDirty = true, newBest = false, pendingNewRun = false;
    std::string banner, bannerSub;
    float bannerT = 0.f, bannerDur = 1.f;
    vec3  bannerCol = vec3(1.f, 1.f, 1.f);
    float introT = 0.f;

    // networking / menu state
    NetState*   net = nullptr;
    std::string netStatus, joinText;
    bool        joinEditing = false;
    ByteWriter  fxW;
    int         fxDepth = 0;
    bool        fxRecord = false;

    // -------------------------------------------------------------- setup ---
    Game() {
        loadBest(best);
        newRun();
        mode = M_TITLE;
    }

    Player& L() { return players[me]; }
    const Player& L() const { return players[me]; }
    int score() const { return souls * 10 + (floorNo - 1) * 250 + kills * 5; }
    int activeCount() const { int n = 0; for (auto& p : players) if (p.active) n++; return n; }
    int aliveCount() const { int n = 0; for (auto& p : players) if (p.active && !p.dead) n++; return n; }

    Player* nearestAlive(vec2 pos, float* outDist = nullptr) {
        Player* best_ = nullptr; float bd = 1e9f;
        for (auto& p : players) {
            if (!p.active || p.dead) continue;
            float d = len2(p.pos - pos);
            if (d < bd) { bd = d; best_ = &p; }
        }
        if (outDist) *outDist = bd;
        return best_;
    }
    float nearestDist(vec2 pos) { float d = 1e9f; nearestAlive(pos, &d); return d; }
    float playerScale() const { return 1.f + 0.6f * (float)(std::max(1, activeCount()) - 1); }

    void recompute(Player& p) {
        const int* b = p.boon;
        Stats& s = p.st;
        s.shots = 1 + b[B_TWIN];
        s.fireInt = 0.30f / (1.f + 0.25f * b[B_SWIFT]) * (1.f + 0.12f * b[B_HEAVY]);
        s.dmg = 1.f + 0.4f * b[B_HEAVY];
        s.pierce = 2 * b[B_PIERCE];
        s.bounce = 2 * b[B_RICOCHET];
        s.homing = (float)b[B_SEEKER];
        s.chain = b[B_CHAIN];
        s.vol = b[B_VOLATILE];
        s.frost = (float)b[B_FROST];
        s.wisps = 2 * b[B_WISPS];
        s.vamp = 0.05f * b[B_VAMP];
        s.light = 1.f + 0.22f * b[B_LANTERN];
        s.magnet = 40.f + 36.f * b[B_LANTERN];
        s.moveSpeed = 78.f * (1.f + 0.15f * b[B_BOOTS]);
        s.dashCd = 1.0f * std::pow(0.85f, (float)b[B_BOOTS]);
        s.maxHp = 6 + 2 * b[B_HEART];
        s.maxDash = 2;
        p.maxHp = s.maxHp;
    }

    void resetPlayer(int slot) {
        Player p;
        p.slot = slot; p.active = true;
        recompute(p);
        p.hp = p.maxHp; p.dashCharges = p.st.maxDash;
        players[slot] = p;
    }

    void newRun() {
        souls = 0; kills = 0; clearedCombat = 0; runTime = 0.f; newBest = false;
        for (int i = 0; i < MAX_PLAYERS; i++) {
            if (i == 0 || (role == NR_HOST && players[i].active)) resetPlayer(i);
            else players[i] = Player();
        }
        me = 0;
        timeScale = 1.f; redFlash = 0.f; trauma = 0.f; hitstop = 0.f; deadT = 0.f; descending = false;
        pendingNewRun = true;
        startFloor(1);
        fade = 1.f;
    }

    void startFloor(int n) {
        floorNo = n;
        D.generate(n);
        en.clear(); bullets.clear(); pickups.clear(); props.clear(); parts.clear(); texts.clear();
        zaps.clear(); waves.clear(); booms.clear(); decals.clear(); ghosts.clear(); pend.clear(); decalHead = 0;
        for (int i = 0; i < MAX_PLAYERS; i++) {
            Player& p = players[i];
            if (!p.active) continue;
            p.pos = D.startPos + vec2((i - 1.5f) * 12.f, 0.f);
            p.tpos = p.pos; p.vel = vec2(0.f, 0.f); p.kb = vec2(0.f, 0.f);
            if (p.dead) { p.dead = false; p.hp = std::max(2, p.maxHp / 2); }
            p.visible = true; p.choosing = false; p.invuln = 0.f; p.dashT = 0.f; p.dashing = false;
            p.hp = std::min(p.maxHp, p.hp + (n > 1 ? 2 : 0));
            p.dashCharges = p.st.maxDash;
        }
        cam = L().pos; camI = vec2(std::floor(cam.x - VW * 0.5f), std::floor(cam.y - VH * 0.5f));
        portalOpen = false; flowT = 0.f; miniDirty = true; introT = 0.f;
        for (auto& p : D.props) { Prop pr; pr.pos = p.pos; props.push_back(pr); }
        for (auto& r : D.rooms) if (r.type == R_TREASURE) {
            Pickup pu; pu.type = PU_RUNE; pu.pos = r.center() + vec2(0.f, -4.f); pickups.push_back(pu);
        }
        D.rooms[0].explored = true;
        revealAround();
        char buf[64];
        std::snprintf(buf, sizeof(buf), "DEPTH %d", n);
        setBannerLocal(buf, kThemes[D.theme].name, 2.4f, vec3(1.f, 0.85f, 0.6f));
        if (role == NR_HOST) { netHostFloor(*this); pendingNewRun = false; }
    }

    void setBannerLocal(const std::string& t, const std::string& sub, float dur, vec3 col) {
        banner = t; bannerSub = sub; bannerT = dur; bannerDur = dur; bannerCol = col;
    }
    // everybody (slot -1) or a single player
    void setBanner(const std::string& t, const std::string& sub, float dur, vec3 col, int slot = -1) {
        if (slot < 0 || slot == me) setBannerLocal(t, sub, dur, col);
        if (role == NR_HOST) netHostBanner(*this, slot, t, sub, dur, col);
    }

    // ---------------------------------------------------------- collision ---
    bool blockedCircle(vec2 p, float r) const {
        int x0 = (int)std::floor((p.x - r) / TS), x1 = (int)std::floor((p.x + r) / TS);
        int y0 = (int)std::floor((p.y - r) / TS), y1 = (int)std::floor((p.y + r) / TS);
        for (int y = y0; y <= y1; y++) for (int x = x0; x <= x1; x++) {
            if (!D.blocked(x, y)) continue;
            float cx = clampf(p.x, (float)(x * TS), (float)(x * TS + TS)), cy = clampf(p.y, (float)(y * TS), (float)(y * TS + TS));
            float dx = p.x - cx, dy = p.y - cy;
            if (dx * dx + dy * dy < r * r) return true;
        }
        return false;
    }
    void moveCircle(vec2& p, vec2 d, float r, bool* hx = nullptr, bool* hy = nullptr) const {
        if (d.x != 0.f) {
            int n = (int)std::ceil(std::fabs(d.x) / 2.f); float s = d.x / n;
            for (int i = 0; i < n; i++) { vec2 q = p; q.x += s; if (!blockedCircle(q, r)) p = q; else { if (hx) *hx = true; break; } }
        }
        if (d.y != 0.f) {
            int n = (int)std::ceil(std::fabs(d.y) / 2.f); float s = d.y / n;
            for (int i = 0; i < n; i++) { vec2 q = p; q.y += s; if (!blockedCircle(q, r)) p = q; else { if (hy) *hy = true; break; } }
        }
    }

    // ------------------------------------------------------------ effects ---
    // Every primitive below is also written to fxW when this machine is the host,
    // so clients can reproduce the same effect locally (positions + parameters only).
    void addPart(const Part& p) { if (parts.size() < 5500) parts.push_back(p); }
    void spark(vec2 p, vec2 v, float life, float size, vec3 col) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_SPARK); fxW.v2(p); fxW.v2(v); fxW.f32(life); fxW.f32(size); fxW.v3(col); }
        Part q; q.p = p; q.v = v; q.life = q.maxLife = life; q.size = size; q.col = col; q.kind = PK_SPARK; q.drag = 2.2f; addPart(q);
    }
    void burst(vec2 p, int n, float speed, vec3 col, float life = 0.5f, float size = 1.6f) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_BURST); fxW.v2(p); fxW.u8(n); fxW.f32(speed); fxW.v3(col); fxW.f32(life); fxW.f32(size); }
        for (int i = 0; i < n; i++) spark(p, angVec(rf(0.f, 2.f * PI)) * (speed * rf(0.25f, 1.f)), life * rf(0.6f, 1.2f), size * rf(0.7f, 1.2f), col * rf(0.8f, 1.3f));
    }
    void ember(vec2 p, vec3 col, float life = 1.4f) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_EMBER); fxW.v2(p); fxW.v3(col); fxW.f32(life); }
        Part q; q.p = p; q.v = vec2(rf(-6.f, 6.f), rf(-18.f, -8.f)); q.life = q.maxLife = life * rf(0.7f, 1.2f); q.size = 1.f; q.col = col; q.kind = PK_EMBER; q.seed = rf(0.f, 6.28f); addPart(q);
    }
    void smoke(vec2 p, vec2 v, float life, float size, float shade, float alpha = 0.5f) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_SMOKE); fxW.v2(p); fxW.v2(v); fxW.f32(life); fxW.f32(size); fxW.f32(shade); fxW.f32(alpha); }
        Part q; q.p = p; q.v = v; q.life = q.maxLife = life; q.size = size; q.grow = size * 0.9f / life; q.col = vec3(shade, shade, shade * 1.05f); q.alpha = alpha; q.kind = PK_SMOKE; q.drag = 2.f; addPart(q);
    }
    void debris(vec2 p, vec2 v, vec3 col, float life = 0.7f) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_DEBRIS); fxW.v2(p); fxW.v2(v); fxW.v3(col); fxW.f32(life); }
        Part q; q.p = p; q.v = v; q.life = q.maxLife = life; q.size = (float)ri(1, 2); q.col = col; q.kind = PK_DEBRIS; q.drag = 3.f; addPart(q);
    }
    void glowPuff(vec2 p, float life, float size, vec3 col) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_GLOW); fxW.v2(p); fxW.f32(life); fxW.f32(size); fxW.v3(col); }
        Part q; q.p = p; q.life = q.maxLife = life; q.size = size; q.col = col; q.kind = PK_GLOW; addPart(q);
    }
    void addDecal(vec2 p, vec3 col, float size) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_DECAL); fxW.v2(p); fxW.v3(col); fxW.f32(size); }
        Decal d; d.p = p; d.col = col; d.size = size; d.alpha = rf(0.55f, 0.9f);
        if (decals.size() < 900) decals.push_back(d); else { decals[decalHead] = d; decalHead = (decalHead + 1) % decals.size(); }
    }
    // screen shake that fades with distance from this machine's camera (online play)
    void traumaNear(vec2 p, float amount) {
        vec2 c = cam;
        float prox = clampf(1.f - len2(p - c) / 320.f, 0.f, 1.f);
        trauma = std::min(1.f, trauma + amount * prox);
    }
    void shock(vec2 p, float maxR, float strength, float dur) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_SHOCK); fxW.v2(p); fxW.f32(maxR); fxW.f32(strength); fxW.f32(dur); }
        Wave w; w.pos = p; w.maxR = maxR; w.strength = strength; w.dur = dur; waves.push_back(w);
        if (waves.size() > 8) waves.erase(waves.begin());
        if (role != NR_SOLO && strength >= 3.f) traumaNear(p, std::min(0.45f, strength * 0.06f));
    }
    void boom(vec2 p, float radius, vec3 col, float life = 0.35f) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_BOOM); fxW.v2(p); fxW.f32(radius); fxW.v3(col); fxW.f32(life); }
        Boom b; b.pos = p; b.radius = radius; b.col = col; b.life = b.maxLife = life; booms.push_back(b);
        if (booms.size() > 12) booms.erase(booms.begin());
    }
    void addText(vec2 p, const std::string& s_, vec3 col, int scale = 1, float life = 0.8f) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_TEXT); fxW.v2(p); fxW.v3(col); fxW.u8(scale); fxW.f32(life); fxW.str(s_); }
        FloatText t; t.p = p; t.s = s_; t.col = col; t.scale = scale; t.life = t.maxLife = life; texts.push_back(t);
        if (texts.size() > 40) texts.erase(texts.begin());
    }
    void zap(vec2 a, vec2 b, vec3 col) {
        FxScope s(*this);
        if (s.rec) { fxW.u8(FX_ZAP); fxW.v2(a); fxW.v2(b); fxW.v3(col); }
        Zap z; z.a = a; z.b = b; z.col = col; z.seed = ri(0, 9999); zaps.push_back(z);
    }
    void addTrauma(float t) { if (role == NR_SOLO) trauma = std::min(1.f, trauma + t); }
    void hitStop(float t) { if (role == NR_SOLO) hitstop = std::max(hitstop, t); }
    void slowMo(float ts) { if (role == NR_SOLO) timeScale = ts; }

    // plays back a batch of recorded effects (client side)
    void applyFx(ByteReader& r) {
        bool saved = fxRecord; fxRecord = false;
        while (!r.done() && r.ok) {
            int t = r.u8();
            switch (t) {
                case FX_SPARK: { vec2 p = r.v2(); vec2 v = r.v2(); float l = r.f32(), s = r.f32(); vec3 c = r.v3(); if (r.ok) spark(p, v, l, s, c); } break;
                case FX_BURST: { vec2 p = r.v2(); int n = r.u8(); float sp = r.f32(); vec3 c = r.v3(); float l = r.f32(), s = r.f32(); if (r.ok) burst(p, n, sp, c, l, s); } break;
                case FX_EMBER: { vec2 p = r.v2(); vec3 c = r.v3(); float l = r.f32(); if (r.ok) ember(p, c, l); } break;
                case FX_SMOKE: { vec2 p = r.v2(); vec2 v = r.v2(); float l = r.f32(), s = r.f32(), sh = r.f32(), a = r.f32(); if (r.ok) smoke(p, v, l, s, sh, a); } break;
                case FX_DEBRIS: { vec2 p = r.v2(); vec2 v = r.v2(); vec3 c = r.v3(); float l = r.f32(); if (r.ok) debris(p, v, c, l); } break;
                case FX_GLOW: { vec2 p = r.v2(); float l = r.f32(), s = r.f32(); vec3 c = r.v3(); if (r.ok) glowPuff(p, l, s, c); } break;
                case FX_DECAL: { vec2 p = r.v2(); vec3 c = r.v3(); float s = r.f32(); if (r.ok) addDecal(p, c, s); } break;
                case FX_SHOCK: { vec2 p = r.v2(); float a = r.f32(), b = r.f32(), c = r.f32(); if (r.ok) shock(p, a, b, c); } break;
                case FX_BOOM: { vec2 p = r.v2(); float rad = r.f32(); vec3 c = r.v3(); float l = r.f32(); if (r.ok) boom(p, rad, c, l); } break;
                case FX_TEXT: { vec2 p = r.v2(); vec3 c = r.v3(); int sc = r.u8(); float l = r.f32(); std::string s = r.str(); if (r.ok) addText(p, s, c, sc, l); } break;
                case FX_ZAP: { vec2 a = r.v2(); vec2 b = r.v2(); vec3 c = r.v3(); if (r.ok) zap(a, b, c); } break;
                default: r.ok = false; break;
            }
        }
        fxRecord = saved;
    }

    vec3 bloodColor(int type) const {
        switch (type) {
            case E_SLIME: case E_SLIME_S: case E_KING: return vec3(0.35f, 1.0f, 0.45f);
            case E_BAT: return vec3(0.8f, 0.4f, 1.0f);
            case E_ARCHER: return vec3(1.0f, 0.95f, 0.8f);
            case E_MAGE: return vec3(1.0f, 0.4f, 0.9f);
            case E_BRUTE: return vec3(1.0f, 0.55f, 0.15f);
            default: return vec3(0.4f, 1.0f, 0.9f);
        }
    }

    // ---------------------------------------------------------- spawning ----
    void queueSpawn(int type, vec2 pos, float delay, int room) { pend.push_back({type, pos, delay, room}); }
    void flushSpawns() {
        for (auto& s : pend) {
            Enemy e;
            const EDef& df = kEDef[s.type];
            e.id = nextId++; e.type = s.type; e.pos = s.pos; e.tpos = s.pos; e.r = df.r;
            e.hp = e.maxHp = df.hp * (1.f + 0.30f * (floorNo - 1)) * (e.boss ? 1.f : 1.f) * (s.type >= E_KING ? playerScale() : (1.f + 0.25f * (playerScale() - 1.f)));
            e.spawn = s.delay; e.room = s.room; e.aiT = rf(0.3f, 1.1f); e.phase = rf(0.f, 6.28f); e.seed = (float)ri(0, 999);
            e.boss = (s.type == E_KING || s.type == E_LICH);
            e.strafe = chance(0.5f) ? 1.f : -1.f;
            en.push_back(e);
        }
        pend.clear();
    }

    vec2 findSpawnPos(const Room& r, float minPlayerDist) {
        for (int k = 0; k < 40; k++) {
            vec2 p((r.x + 2 + ri(0, r.w - 5)) * TS + 8.f, (r.y + 2 + ri(0, r.h - 5)) * TS + 8.f);
            if (blockedCircle(p, 8.f)) continue;
            if (nearestDist(p) < minPlayerDist) continue;
            bool ok = true;
            for (auto& e : en) if (!e.dying && len2(e.pos - p) < 20.f) ok = false;
            for (auto& s : pend) if (len2(s.pos - p) < 20.f) ok = false;
            if (ok) return p;
        }
        return r.center();
    }

    void spawnWave(Room& r, int roomIdx) {
        if (r.type == R_BOSS) {
            int bt = (floorNo % 2 == 1) ? E_KING : E_LICH;
            queueSpawn(bt, r.center(), 1.9f, roomIdx);
            introT = 2.6f;
            setBanner(kEDef[bt].name, "AWAKENS", 2.6f, vec3(1.f, 0.35f, 0.3f));
            addTrauma(0.5f);
            shock(r.center(), 150.f, 6.f, 1.0f);
            flushSpawns();
            return;
        }
        float budget = (3.f + floorNo * 1.6f + r.wave * 1.5f + (r.w * r.h > 220 ? 1.f : 0.f)) * (1.f + 0.5f * (playerScale() - 1.f));
        std::vector<int> pool = {E_SLIME, E_SLIME, E_BAT, E_BAT};
        if (floorNo >= 2) { pool.push_back(E_ARCHER); pool.push_back(E_ARCHER); pool.push_back(E_BRUTE); }
        if (floorNo >= 3) { pool.push_back(E_MAGE); pool.push_back(E_MAGE); }
        int count = 0;
        int cap = 11 + 3 * (activeCount() - 1);
        while (budget > 0.f && count < cap) {
            int t = pool[(size_t)ri(0, (int)pool.size() - 1)];
            if (kEDef[t].cost > budget) {
                bool found = false;
                for (int tries = 0; tries < 6 && !found; tries++) { t = pool[(size_t)ri(0, (int)pool.size() - 1)]; if (kEDef[t].cost <= budget) found = true; }
                if (!found) break;
            }
            queueSpawn(t, findSpawnPos(r, 90.f), 0.7f + 0.1f * count, roomIdx);
            budget -= (float)kEDef[t].cost;
            count++;
        }
        flushSpawns();
    }

    void lockRoom(Room& r, bool lock) {
        for (int gi : r.gates) {
            D.closed[(size_t)gi] = lock ? 1 : 0;
            vec2 c((gi % MAPW) * TS + 8.f, (gi / MAPW) * TS + 8.f);
            for (int k = 0; k < 7; k++) spark(c + vec2(rf(-6.f, 6.f), rf(-6.f, 6.f)), angVec(rf(0.f, 6.28f)) * rf(10.f, 60.f), rf(0.3f, 0.7f), 1.5f, lock ? vec3(2.2f, 0.5f, 0.3f) : vec3(0.6f, 1.6f, 2.2f));
            for (int k = 0; k < 2; k++) smoke(c, vec2(rf(-10.f, 10.f), rf(-10.f, 10.f)), 0.6f, 6.f, 0.4f, 0.4f);
        }
        if (!r.gates.empty()) addTrauma(0.2f);
    }

    void revivePlayers(vec2 at) {
        for (auto& p : players) {
            if (!p.active || !p.dead) continue;
            p.dead = false; p.visible = true; p.hp = 2; p.invuln = 2.f; p.pos = at + vec2((p.slot - 1.5f) * 10.f, 0.f); p.tpos = p.pos;
            p.vel = vec2(0.f, 0.f); p.kb = vec2(0.f, 0.f);
            burst(p.pos, 30, 90.f, vec3(1.2f, 2.0f, 2.8f), 0.8f, 1.8f);
            boom(p.pos, 100.f, vec3(1.0f, 1.6f, 2.4f), 0.6f);
            if (role == NR_HOST) netHostTeleport(*this, p.slot, p.pos);
        }
    }

    void clearRoom(Room& r, int roomIdx) {
        r.cleared = true; r.active = false;
        lockRoom(r, false);
        vec2 c = r.center();
        revivePlayers(c);
        if (r.type == R_BOSS) {
            portalOpen = true;
            D.portalPos = c;
            Pickup pu; pu.type = PU_RUNE; pu.pos = c + vec2(28.f, 0.f); pickups.push_back(pu);
            dropHearts(c + vec2(-28.f, 0.f), 2);
            setBanner("THE GUARDIAN FALLS", "THE PORTAL AWAITS", 3.2f, vec3(0.5f, 1.f, 0.9f));
            shock(c, 200.f, 7.f, 1.2f);
            boom(c, 140.f, vec3(1.5f, 1.2f, 2.0f), 1.0f);
        } else {
            clearedCombat++;
            bool rune = clearedCombat == 1 || (clearedCombat % 2 == 0) || chance(0.3f);
            if (rune) { Pickup pu; pu.type = PU_RUNE; pu.pos = c; pickups.push_back(pu); }
            if (chance(0.45f)) dropHearts(c + vec2(rf(-20.f, 20.f), rf(-12.f, 12.f)), 1);
            for (int i = 0; i < 4; i++) dropSoul(c + vec2(rf(-24.f, 24.f), rf(-16.f, 16.f)), vec2(rf(-30.f, 30.f), rf(-30.f, 30.f)));
            setBanner("ROOM CLEARED", rune ? "A RUNE APPEARS" : "THE WAY IS OPEN", 2.0f, vec3(0.7f, 1.f, 0.8f));
        }
        (void)roomIdx;
    }

    void dropSoul(vec2 p, vec2 v) { Pickup pu; pu.type = PU_SOUL; pu.pos = p; pu.vel = v; pu.t = rf(0.f, 5.f); pickups.push_back(pu); }
    void dropHearts(vec2 p, int n) { for (int i = 0; i < n; i++) { Pickup pu; pu.type = PU_HEART; pu.pos = p + vec2(i * 10.f, 0.f); pu.vel = vec2(rf(-20.f, 20.f), rf(-20.f, 20.f)); pickups.push_back(pu); } }

    void revealAround() {
        for (auto& p : players) {
            if (!p.active || p.dead) continue;
            int cx = (int)(p.pos.x / TS), cy = (int)(p.pos.y / TS);
            for (int dy = -8; dy <= 8; dy++) for (int dx = -9; dx <= 9; dx++) {
                int x = cx + dx, y = cy + dy;
                if (!Dungeon::inb(x, y) || dx * dx + dy * dy > 72) continue;
                size_t i = (size_t)Dungeon::idx(x, y);
                if (!D.explored[i] && !D.solid[i]) { D.explored[i] = 1; miniDirty = true; }
            }
        }
    }

    // -------------------------------------------------------------- combat --
    void addEnemyBullet(vec2 p, vec2 dir, float speed, int kind, float dmg = 1.f) {
        Bullet b; b.pos = p; b.vel = dir * speed; b.kind = kind; b.dmg = dmg; b.life = 5.f; b.friendly = false;
        switch (kind) {
            case BK_ORB:   b.col = vec3(1.0f, 0.25f, 0.65f); b.r = 3.f; break;
            case BK_ARROW: b.col = vec3(1.0f, 0.92f, 0.65f); b.r = 2.5f; break;
            case BK_SLIME: b.col = vec3(0.35f, 1.0f, 0.4f);  b.r = 3.5f; break;
            default:       b.col = vec3(0.3f, 1.0f, 0.85f);  b.r = 3.f; break;
        }
        bullets.push_back(b);
    }
    void ring(vec2 p, int n, float speed, int kind, float off = 0.f) {
        for (int i = 0; i < n; i++) addEnemyBullet(p, angVec(off + i * 2.f * PI / n), speed, kind);
    }

    void playerShoot(Player& p) {
        vec2 d = p.aimDir;
        const Stats& st = p.st;
        float base = std::atan2(d.y, d.x);
        int n = st.shots;
        for (int i = 0; i < n; i++) {
            float a = base + (i - (n - 1) * 0.5f) * 0.14f + rf(-0.025f, 0.025f);
            Bullet b;
            b.friendly = true; b.kind = BK_PLAYER; b.owner = p.slot;
            b.pos = p.pos + d * 11.f + vec2(0.f, -3.f);
            b.vel = angVec(a) * st.bulletSpeed;
            b.r = 3.f; b.life = 1.0f;
            b.crit = chance(0.08f);
            b.dmg = st.dmg * (b.crit ? 2.f : 1.f);
            b.pierce = st.pierce; b.bounce = st.bounce; b.homing = st.homing; b.chain = st.chain; b.vol = st.vol; b.frost = st.frost;
            vec3 tint = p.slot == 0 ? vec3(0.35f, 0.85f, 1.0f) : (p.slot == 1 ? vec3(1.0f, 0.62f, 0.35f) : (p.slot == 2 ? vec3(0.6f, 1.0f, 0.45f) : vec3(0.9f, 0.55f, 1.0f)));
            b.col = b.crit ? vec3(1.0f, 0.9f, 0.4f) : mix3(tint, vec3(1.0f, 0.5f, 0.9f), clampf(st.dmg - 1.f, 0.f, 1.5f) / 1.5f * 0.6f);
            bullets.push_back(b);
        }
        p.muzzle = 1.f;
        vec2 mp = p.pos + d * 14.f + vec2(0.f, -3.f);
        for (int i = 0; i < 4; i++) spark(mp, angVec(base + rf(-0.5f, 0.5f)) * rf(40.f, 120.f), rf(0.1f, 0.25f), 1.2f, vec3(0.5f, 1.4f, 2.2f));
        boom(mp, 46.f, vec3(0.3f, 0.8f, 1.2f), 0.09f);
        addTrauma(0.012f);
    }

    void killEnemy(Enemy& e) {
        if (e.dying) return;
        const EDef& df = kEDef[e.type];
        e.dying = true; e.dyingT = 0.f; kills++;
        vec3 bc = bloodColor(e.type);
        int n = e.boss ? 120 : 26;
        burst(e.pos, n, e.boss ? 150.f : 90.f, bc * 2.f, 0.7f, 1.8f);
        for (int i = 0; i < (e.boss ? 24 : 6); i++) smoke(e.pos + vec2(rf(-4.f, 4.f), rf(-4.f, 4.f)), angVec(rf(0.f, 6.28f)) * rf(10.f, 40.f), rf(0.5f, 1.0f), rf(4.f, 8.f), 0.5f, 0.5f);
        for (int i = 0; i < (e.boss ? 20 : 5); i++) debris(e.pos, angVec(rf(0.f, 6.28f)) * rf(30.f, 110.f), bc * 0.55f);
        for (int i = 0; i < (e.boss ? 26 : 7); i++) addDecal(e.pos + vec2(rf(-e.r, e.r) * 1.6f, rf(-e.r, e.r)), bc * 0.5f, (float)ri(1, e.boss ? 4 : 3));
        boom(e.pos, e.boss ? 160.f : 70.f, bc * 1.8f, e.boss ? 0.8f : 0.3f);
        shock(e.pos, e.boss ? 190.f : 46.f, e.boss ? 7.f : 2.5f, e.boss ? 1.1f : 0.35f);
        hitStop(e.boss ? 0.25f : 0.045f);
        addTrauma(e.boss ? 1.f : 0.14f);
        if (e.boss) slowMo(0.3f);
        for (int i = 0; i < df.souls; i++) dropSoul(e.pos + vec2(rf(-4.f, 4.f), rf(-4.f, 4.f)), angVec(rf(0.f, 6.28f)) * rf(20.f, 70.f));
        const Player& killer = players[clampi(e.lastHit, 0, MAX_PLAYERS - 1)];
        if (chance(killer.st.vamp + 0.03f)) dropHearts(e.pos, 1);
        if (e.type == E_SLIME) for (int i = 0; i < 2; i++) queueSpawn(E_SLIME_S, e.pos + angVec(i * PI + rf(0.f, 1.f)) * 7.f, 0.12f, e.room);
        if (e.boss) {
            for (auto& o : en) if (!o.dying && !o.boss && o.room == e.room) killEnemy(o);
            for (auto& b : bullets) if (!b.friendly) { b.dead = true; burst(b.pos, 3, 40.f, b.col * 2.f, 0.4f); }
        }
    }

    void damageEnemy(Enemy& e, float dmg, vec2 dir, float kb, bool crit, float frost, int owner) {
        if (e.dying || e.spawn > 0.f) return;
        e.hp -= dmg;
        e.flash = 1.f;
        e.lastHit = owner;
        if (!e.boss) e.kb += dir * kb;
        if (frost > 0.f) e.slow = 1.2f + frost * 0.5f;
        vec3 bc = bloodColor(e.type);
        burst(e.pos, crit ? 9 : 5, 70.f, bc * 2.2f, 0.35f, 1.4f);
        for (int i = 0; i < 2; i++) addDecal(e.pos + vec2(rf(-6.f, 6.f), rf(-3.f, 6.f)), bc * 0.45f, (float)ri(1, 2));
        char buf[16];
        std::snprintf(buf, sizeof(buf), "%d", std::max(1, (int)std::lround(dmg)));
        addText(e.pos + vec2(rf(-4.f, 4.f), -e.r - 6.f), buf, crit ? vec3(2.4f, 2.0f, 0.5f) : vec3(2.2f, 2.2f, 2.4f), crit ? 2 : 1, 0.7f);
        hitStop(crit ? 0.05f : 0.018f);
        if (e.hp <= 0.f) killEnemy(e);
    }

    void explodeAt(vec2 p, int level, bool fromPlayer, int owner) {
        float rad = 26.f + 7.f * level;
        boom(p, rad * 2.6f, vec3(2.4f, 1.1f, 0.35f), 0.4f);
        shock(p, rad * 1.5f, 3.2f, 0.45f);
        burst(p, 30, 130.f, vec3(2.6f, 1.2f, 0.4f), 0.55f, 1.8f);
        for (int i = 0; i < 6; i++) smoke(p + vec2(rf(-3.f, 3.f), rf(-3.f, 3.f)), angVec(rf(0.f, 6.28f)) * rf(10.f, 45.f), rf(0.5f, 0.9f), rf(4.f, 7.f), 0.35f, 0.5f);
        addTrauma(0.2f);
        if (!fromPlayer) return;
        float dmg = players[clampi(owner, 0, MAX_PLAYERS - 1)].st.dmg * 0.7f;
        for (auto& e : en) {
            if (e.dying || e.spawn > 0.f) continue;
            float d = len2(e.pos - p);
            if (d < rad + e.r) damageEnemy(e, dmg, norm2(e.pos - p), 90.f, false, 0.f, owner);
        }
    }

    void hurtPlayer(Player& p, int dmg, vec2 from) {
        if (!p.active || p.dead || p.choosing || p.invuln > 0.f || p.dashT > 0.f) return;
        if (mode == M_DEAD) return;
        p.hp -= dmg;
        p.invuln = 1.2f;
        vec2 kbv = norm2(p.pos - from) * 190.f;
        if (p.slot == me) { redFlash = 1.f; addTrauma(0.65f); hitStop(0.09f); p.kb += kbv; }
        else if (role == NR_HOST) netHostHurt(*this, p.slot, dmg, kbv);
        burst(p.pos, 18, 110.f, vec3(2.4f, 0.4f, 0.4f), 0.5f, 1.8f);
        shock(p.pos, 80.f, 5.f, 0.45f);
        boom(p.pos, 80.f, vec3(2.0f, 0.3f, 0.3f), 0.3f);
        addText(p.pos + vec2(0.f, -14.f), "-" + std::to_string(dmg), vec3(2.6f, 0.5f, 0.5f), 2, 0.9f);
        for (int i = 0; i < 4; i++) addDecal(p.pos + vec2(rf(-6.f, 6.f), rf(-2.f, 6.f)), vec3(0.5f, 0.05f, 0.08f), (float)ri(1, 3));
        if (p.hp <= 0) die(p);
    }

    void die(Player& p) {
        p.hp = 0; p.dead = true; p.visible = false; p.choosing = false;
        burst(p.pos, 80, 140.f, vec3(1.2f, 1.8f, 2.8f), 1.0f, 1.8f);
        burst(p.pos, 30, 90.f, vec3(2.8f, 0.5f, 0.4f), 0.8f, 1.8f);
        boom(p.pos, 150.f, vec3(1.4f, 1.6f, 2.4f), 0.9f);
        shock(p.pos, 220.f, 7.f, 1.0f);
        addTrauma(1.f);
        if (p.slot == me && mode == M_BOON) mode = M_PLAY;
        if (aliveCount() == 0) gameOver();
    }
    void gameOver() {
        mode = M_DEAD; deadT = 0.f;
        slowMo(0.2f);
        if (score() > best) { best = score(); newBest = true; saveBest(best); }
    }

    void pickBoons(Player& p) {
        std::vector<int> pool;
        for (int i = 0; i < B_COUNT; i++) if (p.boon[i] < kBoons[i].maxStacks) pool.push_back(i);
        for (int i = (int)pool.size() - 1; i > 0; i--) std::swap(pool[(size_t)i], pool[(size_t)ri(0, i)]);
        p.boonChoices = std::min(3, (int)pool.size());
        for (int i = 0; i < p.boonChoices; i++) p.boonChoice[i] = pool[(size_t)i];
        if (p.boonChoices == 0) return;
        p.choosing = true;
        if (p.slot == me) { mode = M_BOON; boonSel = 0; }
        else if (role == NR_HOST) netHostBoonOffer(*this, p.slot);
    }
    void takeBoon(Player& p, int slotPick) {
        if (!p.choosing || slotPick < 0 || slotPick >= p.boonChoices) return;
        int b = p.boonChoice[slotPick];
        p.boon[b]++;
        recompute(p);
        if (b == B_HEART) p.hp = p.maxHp; else p.hp = std::min(p.hp, p.maxHp);
        p.dashCharges = std::min(p.dashCharges, p.st.maxDash);
        p.choosing = false;
        p.invuln = std::max(p.invuln, 0.6f);
        burst(p.pos, 50, 120.f, kBoons[b].col * 2.4f, 0.8f, 1.8f);
        boom(p.pos, 140.f, kBoons[b].col * 1.6f, 0.7f);
        shock(p.pos, 120.f, 5.f, 0.8f);
        addTrauma(0.3f);
        setBanner(kBoons[b].name, "ACQUIRED", 1.6f, kBoons[b].col, p.slot);
        if (p.slot == me) mode = M_PLAY;
        slowMo(0.35f);
    }
    vec2 cardPos(int i) const { return vec2(36.f + i * 140.f, 62.f); }
    static vec2 cardSize() { return vec2(128.f, 150.f); }

    // ------------------------------------------------------- player update --
    // Movement is decided by the machine that owns the player (the host for slot 0,
    // each client for its own slot), then reported to the host.
    void controlLocal(Player& p, float dt, const Input& in, bool allow, bool fx) {
        vec2 ad = aimWorld - p.pos;
        if (len2(ad) > 3.f) p.aimDir = norm2(ad);
        p.facingLeft = p.aimDir.x < 0.f;
        vec2 mv = allow ? in.move : vec2(0.f, 0.f);
        if (len2(mv) > 1.f) mv = norm2(mv);
        p.moving = len2(mv) > 0.1f;
        p.animT += dt * (p.moving ? 1.f : 0.5f);
        if (allow && in.dash && p.dashT <= 0.f && p.dashCharges > 0) {
            p.dashDir = p.moving ? norm2(mv) : p.aimDir;
            p.dashT = 0.19f; p.dashCharges--; p.dashRecharge = 0.f; p.dashCount++;
            if (role != NR_CLIENT) p.invuln = std::max(p.invuln, 0.25f);
            if (fx) { shock(p.pos, 40.f, 3.f, 0.3f); burst(p.pos, 10, 60.f, vec3(0.5f, 1.4f, 2.2f), 0.3f, 1.4f); addTrauma(0.05f); }
        }
        vec2 vel;
        if (p.dashT > 0.f) {
            p.dashT -= dt;
            vel = p.dashDir * (270.f + 20.f * p.boon[B_BOOTS]);
        } else {
            vec2 target = mv * p.st.moveSpeed;
            p.vel += (target - p.vel) * std::min(1.f, 14.f * dt);
            vel = p.vel;
        }
        p.kb *= std::max(0.f, 1.f - 9.f * dt);
        moveCircle(p.pos, (vel + p.kb) * dt, p.r);
        if (p.dashCharges < p.st.maxDash) {
            p.dashRecharge += dt;
            if (p.dashRecharge >= p.st.dashCd) {
                p.dashRecharge = 0.f; p.dashCharges++;
                burst(p.pos, 6, 40.f, vec3(0.5f, 1.4f, 2.2f), 0.3f, 1.2f);
            }
        }
    }

    // server-side per-player logic (timers + shooting), for every player
    void playerLogic(Player& p, float dt, bool wantFire) {
        p.invuln = std::max(0.f, p.invuln - dt);
        p.muzzle = std::max(0.f, p.muzzle - dt * 9.f);
        p.fireT -= dt;
        p.wispAng += dt * 2.6f;
        if (wantFire && p.fireT <= 0.f && !p.choosing && !p.dead) { playerShoot(p); p.fireT = p.st.fireInt; }
    }

    vec2 wispPos(const Player& p, int i) const {
        float a = p.wispAng + i * 2.f * PI / std::max(1, p.st.wisps);
        return p.pos + angVec(a) * (26.f + 3.f * std::sin(p.wispAng * 2.f + i)) + vec2(0.f, -3.f);
    }

    // ------------------------------------------------------- enemy update ---
    vec2 chaseDir(const Enemy& e, vec2 dp, bool los) const {
        if (los) return dp;
        vec2 f = D.flowDir(e.pos);
        return len2(f) < 0.01f ? dp : f;
    }

    bool teleportNear(Enemy& e, vec2 target, float rmin, float rmax) {
        for (int k = 0; k < 14; k++) {
            vec2 p = target + angVec(rf(0.f, 6.28f)) * rf(rmin, rmax);
            if (blockedCircle(p, e.r + 2.f) || !D.los(p, target)) continue;
            int ri_ = D.roomIndexAt(p, 6.f);
            if (ri_ != e.room && e.room >= 0) continue;
            burst(e.pos, 14, 60.f, vec3(1.6f, 0.5f, 2.0f), 0.4f, 1.4f);
            e.pos = p;
            burst(e.pos, 14, 60.f, vec3(1.6f, 0.5f, 2.0f), 0.4f, 1.4f);
            return true;
        }
        return false;
    }

    void updateEnemy(Enemy& e, float dt) {
        const EDef& df = kEDef[e.type];
        e.t += dt;
        e.flash = std::max(0.f, e.flash - dt * 6.f);
        e.warn = std::max(0.f, e.warn - dt * 3.f);
        e.wispCd = std::max(0.f, e.wispCd - dt);
        if (e.dying) { e.dyingT += dt; return; }
        if (e.spawn > 0.f) {
            e.spawn -= dt;
            e.dissolve = clampf(e.spawn / 0.6f, 0.f, 1.f);
            return;
        }
        e.dissolve = 0.f;
        e.slow = std::max(0.f, e.slow - dt);
        e.kb *= std::max(0.f, 1.f - 10.f * dt);

        Player* tp = nearestAlive(e.pos);
        if (!tp) return;                                   // nobody left to chase
        vec2 tpos = tp->pos;
        vec2 toP = tpos - e.pos;
        float dist = len2(toP);
        vec2 dp = dist > 0.01f ? toP / dist : vec2(1.f, 0.f);
        bool los = D.los(e.pos, tpos);
        vec2 chase = chaseDir(e, dp, los);
        float sp = df.speed * (e.slow > 0.f ? 0.55f : 1.f);
        vec2 move(0.f, 0.f);
        bool hx = false, hy = false;
        e.faceLeft = toP.x < 0.f;
        bool phase2 = e.hp < e.maxHp * 0.5f;
        e.aiT -= dt;

        switch (e.type) {
        case E_SLIME: case E_SLIME_S:
            if (e.state == 0) {
                if (e.aiT <= 0.f) { e.state = 1; e.aiT = 0.38f; e.dir = chase; }
            } else {
                move = e.dir * sp * 2.4f;
                if (e.aiT <= 0.f) { e.state = 0; e.aiT = rf(0.45f, 0.9f); for (int i = 0; i < 3; i++) smoke(e.pos + vec2(rf(-3.f, 3.f), 4.f), vec2(rf(-12.f, 12.f), rf(-6.f, 0.f)), 0.4f, 2.5f, 0.5f, 0.3f); }
            }
            break;
        case E_BAT:
            if (e.state == 0) {
                move = chase * sp + perp2(dp) * std::sin(e.t * 5.f + e.phase) * sp * 0.9f;
                if (e.aiT <= 0.f && dist < 150.f && los) { e.state = 1; e.aiT = 0.5f; e.dir = dp; e.warn = 1.f; }
            } else if (e.state == 1) {
                move = e.dir * sp * 3.1f;
                if (e.aiT <= 0.f) { e.state = 2; e.aiT = 0.7f; }
            } else {
                move = -dp * sp * 0.9f + perp2(dp) * std::sin(e.t * 7.f) * sp * 0.6f;
                if (e.aiT <= 0.f) { e.state = 0; e.aiT = rf(1.2f, 2.2f); }
            }
            break;
        case E_ARCHER:
            if (e.state == 0) {
                if (dist < 85.f) move = -dp * sp;
                else if (dist > 135.f || !los) move = chase * sp;
                else move = perp2(dp) * e.strafe * sp * 0.7f;
                if (chance(dt * 0.4f)) e.strafe = -e.strafe;
                if (e.aiT <= 0.f && los && dist < 200.f) { e.state = 1; e.aiT = 0.5f; e.warn = 1.f; e.dir = dp; }
            } else {
                move = vec2(0.f, 0.f);
                e.warn = 1.f;
                if (e.aiT <= 0.f) {
                    addEnemyBullet(e.pos + dp * 8.f, dp, 150.f, BK_ARROW);
                    e.state = 0; e.aiT = rf(1.4f, 2.1f);
                }
            }
            break;
        case E_MAGE:
            if (e.state == 0) {
                move = perp2(dp) * e.strafe * sp * 0.5f + (dist < 80.f ? -dp * sp : (dist > 140.f ? chase * sp * 0.7f : vec2(0.f, 0.f)));
                if (e.aiT <= 0.f) { e.state = 1; e.aiT = 0.35f; }
            } else if (e.state == 1) {
                e.dissolve = 1.f - clampf(e.aiT / 0.35f, 0.f, 1.f);
                if (e.aiT <= 0.f) { teleportNear(e, tpos, 70.f, 130.f); e.state = 2; e.aiT = 0.35f; }
            } else if (e.state == 2) {
                e.dissolve = clampf(e.aiT / 0.35f, 0.f, 1.f);
                if (e.aiT <= 0.f) { e.state = 3; e.aiT = 0.4f; e.warn = 1.f; }
            } else {
                e.warn = 1.f;
                if (e.aiT <= 0.f) {
                    e.counter++;
                    if (e.counter % 2 == 0) ring(e.pos, floorNo >= 4 ? 12 : 8, 78.f, BK_ORB, rf(0.f, 6.28f));
                    else { float a = std::atan2(dp.y, dp.x); for (int i = -2; i <= 2; i++) addEnemyBullet(e.pos, angVec(a + i * 0.2f), 95.f, BK_ORB); }
                    burst(e.pos, 10, 60.f, vec3(2.0f, 0.5f, 2.0f), 0.3f, 1.4f);
                    e.state = 0; e.aiT = rf(2.0f, 3.0f);
                }
            }
            break;
        case E_BRUTE:
            if (e.state == 0) {
                move = chase * sp;
                if (e.aiT <= 0.f && dist < 140.f && los) { e.state = 1; e.aiT = 0.7f; e.dir = dp; }
            } else if (e.state == 1) {
                e.warn = 1.f; e.dir = dp;
                if (e.aiT <= 0.f) { e.state = 2; e.aiT = 0.9f; addTrauma(0.1f); }
            } else if (e.state == 2) {
                move = e.dir * 200.f;
            } else {
                if (e.aiT <= 0.f) { e.state = 0; e.aiT = rf(1.2f, 2.0f); }
            }
            break;
        case E_KING:
            if (e.state == 0) {
                if (e.aiT <= 0.f) { e.state = 1; e.aiT = 0.55f; e.dir = chase; e.counter++; }
            } else {
                move = e.dir * (phase2 ? 200.f : 150.f);
                if (e.aiT <= 0.f) {
                    e.state = 0; e.aiT = phase2 ? 0.5f : 0.9f;
                    ring(e.pos, phase2 ? 18 : 12, 74.f, BK_SLIME, rf(0.f, 6.28f));
                    shock(e.pos, 120.f, 5.f, 0.6f); addTrauma(0.4f);
                    for (int i = 0; i < 14; i++) smoke(e.pos + vec2(rf(-10.f, 10.f), 6.f), angVec(rf(0.f, 6.28f)) * rf(20.f, 60.f), 0.6f, 5.f, 0.45f, 0.4f);
                    if (e.counter % 3 == 0) for (int i = 0; i < (phase2 ? 4 : 2); i++) queueSpawn(E_SLIME_S, e.pos + angVec(rf(0.f, 6.28f)) * 26.f, 0.5f, e.room);
                    if (e.counter % 2 == 0) { float a = std::atan2(dp.y, dp.x); for (int i = -1; i <= 1; i++) addEnemyBullet(e.pos, angVec(a + i * 0.25f), 110.f, BK_SLIME); }
                }
            }
            break;
        case E_LICH:
            if (e.state == 0) {
                if (dist < 90.f) move = -dp * 40.f; else if (dist > 150.f) move = chase * 40.f;
                move += perp2(dp) * e.strafe * 22.f;
                if (chance(dt * 0.3f)) e.strafe = -e.strafe;
                if (e.aiT <= 0.f) {
                    e.state = 1; e.pat = e.counter % 4; e.counter++; e.warn = 1.f;
                    e.patT = e.pat == 0 ? (phase2 ? 3.8f : 3.2f) : e.pat == 1 ? 2.4f : e.pat == 2 ? 0.9f : 1.7f;
                    e.fireT = 0.f; e.spiral = rf(0.f, 6.28f);
                    if (e.pat == 2) {
                        Room& rm = D.rooms[(size_t)std::max(0, e.room)];
                        for (int i = 0; i < (phase2 ? 3 : 2); i++) queueSpawn(chance(0.5f) ? E_BAT : E_ARCHER, findSpawnPos(rm, 60.f), 0.6f, e.room);
                    }
                }
            } else {
                move = perp2(dp) * e.strafe * 18.f;
                e.patT -= dt; e.fireT -= dt; e.warn = 0.6f;
                if (e.pat == 0 && e.fireT <= 0.f) {
                    e.fireT = phase2 ? 0.06f : 0.08f; e.spiral += 0.46f;
                    int arms = phase2 ? 2 : 1;
                    for (int a = 0; a < arms; a++) addEnemyBullet(e.pos, angVec(e.spiral + a * PI), 70.f, BK_LICH);
                } else if (e.pat == 1 && e.fireT <= 0.f) {
                    e.fireT = 0.75f; e.spiral += 0.17f;
                    ring(e.pos, 20, 84.f, BK_LICH, e.spiral);
                } else if (e.pat == 3 && e.fireT <= 0.f) {
                    e.fireT = 0.5f;
                    float a = std::atan2(dp.y, dp.x);
                    for (int i = -3; i <= 3; i++) addEnemyBullet(e.pos, angVec(a + i * 0.15f), 108.f, BK_LICH);
                }
                if (e.patT <= 0.f) {
                    e.state = 0; e.aiT = phase2 ? 0.8f : 1.4f;
                    if (phase2) { burst(e.pos, 20, 80.f, vec3(0.5f, 2.0f, 1.8f), 0.4f, 1.4f); teleportNear(e, tpos, 80.f, 130.f); }
                }
            }
            break;
        default: break;
        }

        moveCircle(e.pos, (move + e.kb) * dt, e.r, &hx, &hy);

        if (e.type == E_BRUTE && e.state == 2 && (hx || hy)) {
            e.state = 3; e.aiT = 1.1f;
            addTrauma(0.45f); shock(e.pos, 110.f, 5.f, 0.5f);
            ring(e.pos, 8, 70.f, BK_ORB, rf(0.f, 6.28f));
            for (int i = 0; i < 10; i++) debris(e.pos + e.dir * 8.f, angVec(rf(0.f, 6.28f)) * rf(30.f, 100.f), vec3(0.4f, 0.38f, 0.45f));
            burst(e.pos + e.dir * 8.f, 20, 100.f, vec3(2.6f, 1.2f, 0.4f), 0.5f, 1.6f);
        }
        // contact damage against every player
        if (!e.dying && e.spawn <= 0.f && e.dissolve < 0.5f) {
            for (auto& p : players) {
                if (!p.active || p.dead) continue;
                float cr = e.r * 0.8f + p.r;
                if (len2(p.pos - e.pos) < cr) {
                    int dmg = df.contact;
                    if (e.type == E_BRUTE && e.state != 2) dmg = 1;
                    hurtPlayer(p, dmg, e.pos);
                }
            }
        }
    }

    // ------------------------------------------------------- bullet update --
    void updateBullets(float dt) {
        for (auto& b : bullets) {
            if (b.dead) continue;
            b.life -= dt;
            if (b.life <= 0.f) { b.dead = true; if (b.friendly && b.vol) explodeAt(b.pos, b.vol, true, b.owner); continue; }
            if (b.friendly && b.homing > 0.f) {
                Enemy* best_ = nullptr; float bd = 130.f;
                for (auto& e : en) {
                    if (e.dying || e.spawn > 0.f) continue;
                    float d = len2(e.pos - b.pos);
                    if (d < bd) { bd = d; best_ = &e; }
                }
                if (best_) {
                    float sp = len2(b.vel);
                    vec2 want = norm2(best_->pos - b.pos), cur = norm2(b.vel);
                    vec2 nd = norm2(cur + want * (b.homing * 5.f * dt));
                    b.vel = nd * sp;
                }
            }
            int steps = (int)std::ceil(len2(b.vel) * dt / 2.5f);
            if (steps < 1) steps = 1;
            vec2 stepv = b.vel * dt / (float)steps;
            for (int s = 0; s < steps && !b.dead; s++) {
                b.pos += stepv;
                if (blockedCircle(b.pos, b.friendly ? 2.f : 1.5f)) {
                    if (b.friendly && b.bounce > 0) {
                        b.bounce--;
                        b.pos -= stepv;
                        vec2 px = b.pos + vec2(stepv.x, 0.f), py = b.pos + vec2(0.f, stepv.y);
                        bool bx = blockedCircle(px, 2.f), by = blockedCircle(py, 2.f);
                        if (bx || (!bx && !by)) b.vel.x = -b.vel.x;
                        if (by || (!bx && !by)) b.vel.y = -b.vel.y;
                        stepv = b.vel * dt / (float)steps;
                        burst(b.pos, 5, 60.f, b.col * 2.f, 0.25f, 1.2f);
                    } else {
                        b.dead = true;
                        burst(b.pos, b.friendly ? 6 : 4, 60.f, b.col * 2.2f, 0.3f, 1.3f);
                        boom(b.pos, 36.f, b.col * 0.8f, 0.12f);
                        if (b.friendly && b.vol) explodeAt(b.pos, b.vol, true, b.owner);
                    }
                    continue;
                }
                if (b.friendly) {
                    for (auto& e : en) {
                        if (e.dying || e.spawn > 0.f) continue;
                        if (len2(e.pos - b.pos) > e.r + b.r) continue;
                        bool seen = false;
                        for (int k = 0; k < b.nhit; k++) if (b.hit[k] == e.id) seen = true;
                        if (seen) continue;
                        if (b.nhit < 6) b.hit[b.nhit++] = e.id;
                        vec2 kd = norm2(b.vel);
                        damageEnemy(e, b.dmg, kd, 55.f, b.crit, b.frost, b.owner);
                        if (b.chain > 0) {
                            Enemy* tgt = nullptr; float bd = 80.f;
                            for (auto& o : en) {
                                if (o.dying || o.spawn > 0.f || o.id == e.id) continue;
                                float d = len2(o.pos - e.pos);
                                if (d < bd) { bd = d; tgt = &o; }
                            }
                            if (tgt) {
                                zap(e.pos, tgt->pos, vec3(0.6f, 0.8f, 2.6f));
                                boom(tgt->pos, 50.f, vec3(0.5f, 0.7f, 2.0f), 0.2f);
                                damageEnemy(*tgt, std::max(1.f, b.dmg * 0.5f * b.chain), norm2(tgt->pos - e.pos), 30.f, false, 0.f, b.owner);
                            }
                        }
                        if (b.pierce > 0) { b.pierce--; }
                        else {
                            b.dead = true;
                            if (b.vol) explodeAt(b.pos, b.vol, true, b.owner);
                        }
                        break;
                    }
                    for (auto& p : props) {
                        if (p.dead) continue;
                        if (len2(p.pos - b.pos) < 7.f + b.r) { breakProp(p); if (b.pierce <= 0) b.dead = true; }
                    }
                } else {
                    for (auto& p : players) {
                        if (!p.active || p.dead || b.dead) continue;
                        if (len2(p.pos - b.pos) < p.r + b.r && p.invuln <= 0.f && p.dashT <= 0.f && !p.choosing) {
                            hurtPlayer(p, (int)b.dmg, b.pos - b.vel * 0.05f);
                            b.dead = true;
                        }
                    }
                    for (auto& p : players) {
                        if (!p.active || p.dead || b.dead) continue;
                        for (int w = 0; w < p.st.wisps && !b.dead; w++)
                            if (len2(wispPos(p, w) - b.pos) < 7.f) { b.dead = true; burst(b.pos, 6, 50.f, b.col * 2.f, 0.25f, 1.2f); }
                    }
                }
            }
        }
        bullets.erase(std::remove_if(bullets.begin(), bullets.end(), [](const Bullet& b) { return b.dead; }), bullets.end());
    }

    void breakProp(Prop& p) {
        if (p.dead) return;
        p.dead = true;
        for (int i = 0; i < 12; i++) debris(p.pos, angVec(rf(0.f, 6.28f)) * rf(20.f, 90.f), vec3(0.65f, 0.34f, 0.24f) * rf(0.7f, 1.2f), rf(0.5f, 0.9f));
        for (int i = 0; i < 3; i++) smoke(p.pos, vec2(rf(-10.f, 10.f), rf(-10.f, 0.f)), 0.6f, 4.f, 0.5f, 0.35f);
        addTrauma(0.06f);
        if (chance(0.55f)) for (int i = 0; i < ri(1, 3); i++) dropSoul(p.pos, angVec(rf(0.f, 6.28f)) * rf(20.f, 50.f));
        if (chance(0.10f)) dropHearts(p.pos, 1);
    }

    // ------------------------------------------------------ pickups update --
    void updatePickups(float dt) {
        for (auto& p : pickups) {
            if (p.dead) continue;
            p.t += dt;
            p.pos += p.vel * dt;
            p.vel *= std::max(0.f, 1.f - 3.f * dt);
            if (blockedCircle(p.pos, 3.f)) { p.pos -= p.vel * dt; p.vel = vec2(0.f, 0.f); }
            float dist = 1e9f;
            Player* q = nearestAlive(p.pos, &dist);
            if (!q) continue;
            vec2 d = q->pos - p.pos;
            if (p.type == PU_SOUL) {
                float mg = q->st.magnet;
                if (dist < mg) p.vel += norm2(d) * (260.f * dt * (1.f + (mg - dist) / mg));
                if (dist < 9.f) {
                    p.dead = true; souls++;
                    burst(p.pos, 5, 50.f, vec3(0.8f, 1.8f, 2.6f), 0.3f, 1.2f);
                }
            } else if (p.type == PU_HEART) {
                // the closest player who actually needs healing gets it
                Player* needy = nullptr; float nd = 1e9f;
                for (auto& pp : players) if (pp.active && !pp.dead && pp.hp < pp.maxHp) { float dd = len2(pp.pos - p.pos); if (dd < nd) { nd = dd; needy = &pp; } }
                if (needy) {
                    if (nd < 28.f) p.vel += norm2(needy->pos - p.pos) * (200.f * dt);
                    if (nd < 10.f) {
                        p.dead = true; needy->hp = std::min(needy->maxHp, needy->hp + 2);
                        burst(p.pos, 18, 70.f, vec3(2.6f, 0.5f, 0.7f), 0.5f, 1.6f);
                        boom(p.pos, 60.f, vec3(2.0f, 0.4f, 0.5f), 0.3f);
                        addText(needy->pos + vec2(0.f, -14.f), "+1 HEART", vec3(2.4f, 0.8f, 1.0f), 1, 1.0f);
                    }
                }
            } else {   // rune
                if (dist < 12.f && !q->choosing) {
                    p.dead = true;
                    burst(p.pos, 40, 100.f, vec3(1.8f, 1.0f, 3.0f), 0.7f, 1.6f);
                    boom(p.pos, 120.f, vec3(1.4f, 0.8f, 2.4f), 0.5f);
                    shock(p.pos, 90.f, 4.f, 0.6f);
                    pickBoons(*q);
                }
            }
        }
        pickups.erase(std::remove_if(pickups.begin(), pickups.end(), [](const Pickup& p) { return p.dead; }), pickups.end());
    }

    // -------------------------------------------------------- room update ---
    void updateRooms(float dt) {
        for (auto& p : players) {
            if (!p.active || p.dead) continue;
            int ri_ = D.roomIndexAt(p.pos, 12.f);
            if (ri_ < 0) continue;
            Room& er = D.rooms[(size_t)ri_];
            if (!er.explored) {
                er.explored = true;
                for (int y = er.y - 1; y <= er.y + er.h; y++) for (int x = er.x - 1; x <= er.x + er.w; x++)
                    if (Dungeon::inb(x, y) && !D.solid[(size_t)Dungeon::idx(x, y)]) D.explored[(size_t)Dungeon::idx(x, y)] = 1;
                miniDirty = true;
            }
            if (!er.cleared && !er.active && (er.type == R_COMBAT || er.type == R_BOSS)) {
                er.active = true; er.wave = 0; er.waveSpawned = false; er.waveT = 0.8f;
                lockRoom(er, true);
                shock(p.pos, 100.f, 4.f, 0.5f);
            }
        }
        for (size_t i = 0; i < D.rooms.size(); i++) {
            Room& r = D.rooms[i];
            if (!r.active) continue;
            r.waveT -= dt;
            if (!r.waveSpawned && r.waveT <= 0.f && r.wave < r.waves) {
                spawnWave(r, (int)i);
                r.waveSpawned = true;
                if (r.type == R_COMBAT && r.waves > 1) {
                    char buf[32]; std::snprintf(buf, sizeof(buf), "WAVE %d", r.wave + 1);
                    setBanner(buf, "", 1.2f, vec3(1.f, 0.7f, 0.5f));
                }
            }
            if (r.waveSpawned) {
                int alive = 0;
                for (auto& e : en) if (e.room == (int)i && !e.dying) alive++;
                for (auto& s : pend) if (s.room == (int)i) alive++;
                if (alive == 0) {
                    r.wave++; r.waveSpawned = false; r.waveT = 1.0f;
                    if (r.wave >= r.waves) clearRoom(r, (int)i);
                }
            }
        }
    }

    // ----------------------------------------------- cosmetics (never networked)
    // Continuous effects are derived from state on every machine instead of being sent.
    void updateCosmetics(float dt) {
        if (dt <= 0.f) return;
        bool saved = fxRecord; fxRecord = false;
        for (auto& p : players) {
            if (!p.active || !p.visible || p.dead) continue;
            if (chance(dt * 6.f)) ember(p.pos + vec2(rf(-10.f, 10.f), rf(-12.f, 4.f)), vec3(2.0f, 1.2f, 0.5f), 1.2f);
            if (p.moving && p.dashT <= 0.f && chance(dt * 5.f)) smoke(p.pos + vec2(rf(-2.f, 2.f), 6.f), vec2(rf(-6.f, 6.f), rf(-4.f, 0.f)), 0.45f, 2.5f, 0.55f, 0.28f);
            if (p.dashT > 0.f) {
                p.ghostT -= dt;
                if (p.ghostT <= 0.f) { p.ghostT = 0.025f; Ghost g; g.pos = p.pos; g.left = p.facingLeft; g.life = 0.28f; g.slot = p.slot; ghosts.push_back(g); }
            }
            for (int w = 0; w < p.st.wisps; w++)
                if (chance(dt * 20.f)) spark(wispPos(p, w), vec2(rf(-10.f, 10.f), rf(-10.f, 10.f)), 0.3f, 1.3f, vec3(0.4f, 2.0f, 1.6f));
        }
        for (auto& b : bullets) {
            if (parts.size() > 4200) break;
            if (chance(dt / (b.friendly ? 0.025f : 0.045f)))
                spark(b.pos, vec2(rf(-8.f, 8.f), rf(-8.f, 8.f)), b.friendly ? 0.22f : 0.3f, 1.35f, b.col * 1.4f);
        }
        for (auto& e : en) {
            if (e.dying || e.spawn <= 0.f) continue;
            if (chance(dt * 40.f)) { float a = rf(0.f, 6.28f); vec2 sp = e.pos + angVec(a) * rf(4.f, e.r + 8.f); spark(sp, (e.pos - sp) * 3.f, 0.4f, 1.3f, vec3(1.6f, 0.5f, 2.2f)); }
        }
        if (portalOpen && chance(dt * 30.f)) { float a = rf(0.f, 6.28f); vec2 pp = D.portalPos + angVec(a) * rf(14.f, 26.f); spark(pp, perp2(angVec(a)) * 30.f - angVec(a) * 14.f, 0.7f, 1.4f, vec3(0.8f, 1.6f, 3.0f)); }
        if (chance(dt * 5.f)) {
            for (auto& t : D.torches) {
                vec2 tp(t.tx * TS + 8.f, t.ty * TS + 14.f);
                if (len2(tp - cam) < 260.f && chance(0.08f)) ember(tp + vec2(rf(-2.f, 2.f), 4.f), kThemes[D.theme].torch * 2.4f, 1.6f);
            }
        }
        fxRecord = saved;
    }

    void updateParticles(float dt, float worldTime) {
        for (auto& q : parts) {
            q.life -= dt;
            q.v *= std::max(0.f, 1.f - q.drag * dt);
            if (q.kind == PK_EMBER) q.v.y -= 6.f * dt * (0.5f + 0.5f * std::sin(worldTime * 3.f + q.seed));
            q.p += q.v * dt;
            q.size += q.grow * dt;
            if (q.kind == PK_DEBRIS && q.life <= 0.f && blockedCircle(q.p, 1.f) == false && chance(0.5f)) {
                bool saved = fxRecord; fxRecord = false; addDecal(q.p, q.col * 0.8f, q.size); fxRecord = saved;
            }
        }
        parts.erase(std::remove_if(parts.begin(), parts.end(), [](const Part& q) { return q.life <= 0.f; }), parts.end());
        for (auto& t : texts) { t.life -= dt; t.p.y -= 18.f * dt; }
        texts.erase(std::remove_if(texts.begin(), texts.end(), [](const FloatText& t) { return t.life <= 0.f; }), texts.end());
        for (auto& z : zaps) z.life -= dt;
        zaps.erase(std::remove_if(zaps.begin(), zaps.end(), [](const Zap& z) { return z.life <= 0.f; }), zaps.end());
        for (auto& w : waves) w.age += dt;
        waves.erase(std::remove_if(waves.begin(), waves.end(), [](const Wave& w) { return w.age >= w.dur; }), waves.end());
        for (auto& b : booms) b.life -= dt;
        booms.erase(std::remove_if(booms.begin(), booms.end(), [](const Boom& b) { return b.life <= 0.f; }), booms.end());
        for (auto& g : ghosts) g.life -= dt;
        ghosts.erase(std::remove_if(ghosts.begin(), ghosts.end(), [](const Ghost& g) { return g.life <= 0.f; }), ghosts.end());
        for (auto& p : props) p.shake = std::max(0.f, p.shake - dt * 4.f);
        props.erase(std::remove_if(props.begin(), props.end(), [](const Prop& p) { return p.dead; }), props.end());
    }

    vec2 camTarget() {
        const Player& l = L();
        if (l.active && !l.dead) return l.pos + (aimWorld - l.pos) * 0.16f;
        float d; Player* o = nearestAlive(l.pos, &d);
        return o ? o->pos : l.pos;
    }

    void updateCamera(float dt) {
        vec2 target = camTarget();
        if (mode == M_TITLE) {
            const Room& r = D.rooms[0];
            target = r.center() + vec2(std::sin(time * 0.25f) * 40.f, std::cos(time * 0.2f) * 18.f);
        }
        cam += (target - cam) * std::min(1.f, 6.f * dt);
        cam.x = clampf(cam.x, VW * 0.5f, MAPW * TS - VW * 0.5f);
        cam.y = clampf(cam.y, VH * 0.5f, MAPH * TS - VH * 0.5f);
        float tr = trauma * trauma;
        vec2 shake(std::sin(time * 71.f) * 6.f * tr, std::sin(time * 83.f + 1.7f) * 6.f * tr);
        camI = vec2(std::floor(cam.x - VW * 0.5f + shake.x + 0.5f), std::floor(cam.y - VH * 0.5f + shake.y + 0.5f));
    }

    // ------------------------------------------------------- menus / flow ---
    void startHost() {
        if (!netStartHost(*this, NET_PORT)) { netStatus = "COULD NOT OPEN PORT " + std::to_string(NET_PORT); return; }
        role = NR_HOST; me = 0;
        newRun();
        mode = M_PLAY; fade = 0.f;
        netStatus = "HOSTING ON PORT " + std::to_string(NET_PORT);
    }
    void startJoin(const std::string& addr) {
        role = NR_CLIENT;
        if (!netStartJoin(*this, addr)) { role = NR_SOLO; if (netStatus.empty()) netStatus = "COULD NOT CONNECT"; return; }
        netStatus = "CONNECTING...";
    }
    void returnToTitle(const std::string& msg) {
        netShutdown(*this);
        role = NR_SOLO;
        for (auto& p : players) p = Player();
        newRun();
        mode = M_TITLE; fade = 0.f;
        netStatus = msg;
    }

    void boonUi(const Input& in, bool& picked, int& pickSlot) {
        Player& p = L();
        picked = false; pickSlot = -1;
        if (in.menuMove != 0 && p.boonChoices > 0) boonSel = (boonSel + in.menuMove + p.boonChoices) % p.boonChoices;
        int pick = in.pick;
        for (int i = 0; i < p.boonChoices; i++) {
            vec2 c = cardPos(i), s = cardSize();
            if (in.aim.x >= c.x && in.aim.x <= c.x + s.x && in.aim.y >= c.y && in.aim.y <= c.y + s.y) { boonSel = i; if (in.click) pick = i; }
        }
        if (in.confirm) pick = boonSel;
        if (pick >= 0 && pick < p.boonChoices) { picked = true; pickSlot = pick; }
    }

    void updateTitle(float realDt, const Input& in) {
        fade = std::min(1.f, fade + realDt * 1.5f);
        if (joinEditing) {
            for (char c : in.typed) if (((c >= '0' && c <= '9') || c == '.' || c == ':' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '-') && joinText.size() < 40) joinText.push_back(c);
            if (in.backspace && !joinText.empty()) joinText.pop_back();
            if (in.enter) { joinEditing = false; if (!joinText.empty()) startJoin(joinText); }
            if (in.pause) joinEditing = false;
        } else {
            if (in.hostKey) startHost();
            else if (in.joinKey) { joinEditing = true; netStatus.clear(); }
            else if (in.start || in.click) { newRun(); mode = M_PLAY; fade = 0.f; netStatus.clear(); }
        }
        updateParticles(realDt, time);
        if (chance(realDt * 14.f)) { Room& r = D.rooms[0]; ember(vec2((float)((r.x + ri(0, r.w)) * TS), (float)((r.y + ri(0, r.h)) * TS)), vec3(2.0f, 1.2f, 0.5f), 2.5f); }
        updateCamera(realDt);
    }

    // ------------------------------------------------------ the main update --
    void update(float realDt, const Input& in) {
        realDt = std::min(realDt, 1.f / 20.f);
        time += realDt;
        aimScreen = in.aim;
        aimWorld = camI + in.aim;
        trauma = std::max(0.f, trauma - realDt * 0.9f);
        redFlash = std::max(0.f, redFlash - realDt * 2.2f);
        bannerT = std::max(0.f, bannerT - realDt);
        if (role != NR_SOLO) { hitstop = 0.f; timeScale = 1.f; }
        if (mode != M_DEAD) timeScale += (1.f - timeScale) * std::min(1.f, 2.5f * realDt);

        if (role == NR_CLIENT) { updateClient(realDt, in); return; }
        if (role == NR_HOST) { fxRecord = true; netPollHost(*this); }

        if (mode == M_TITLE) { fxRecord = false; updateTitle(realDt, in); return; }

        if (in.pause) { if (mode == M_PAUSE) mode = M_PLAY; else if (mode == M_PLAY) mode = M_PAUSE; }
        bool freeze = role == NR_SOLO && (mode == M_PAUSE || mode == M_BOON);
        if (mode == M_BOON) {
            fade = std::min(1.f, fade + realDt * 1.6f);
            bool picked; int slot;
            boonUi(in, picked, slot);
            if (picked) takeBoon(L(), slot);
        }
        if (freeze) {
            if (mode == M_BOON) { updateParticles(realDt * 0.3f, time); updateCamera(realDt); }
            return;
        }

        // ---------------- PLAY / DEAD / (BOON + PAUSE while hosting) ----------------
        float dt = realDt * timeScale;
        if (hitstop > 0.f) { hitstop -= realDt; dt = 0.f; }

        if (mode == M_DEAD) {
            deadT += realDt;
            if (role == NR_SOLO) {
                timeScale = deadT < 1.2f ? 0.22f : std::min(1.f, timeScale + realDt * 0.8f);
                dt = realDt * timeScale;
            }
            if (deadT > 1.8f && (in.start || in.click)) { newRun(); mode = M_PLAY; fade = 0.f; return; }
        } else {
            runTime += dt;
        }

        if (descending) {
            fade -= realDt * 1.7f;
            if (fade <= 0.f) { descending = false; startFloor(floorNo + 1); fade = 0.f; }
        } else fade = std::min(1.f, fade + realDt * 1.6f);

        if (dt > 0.f) {
            if (mode != M_DEAD) {
                bool allow = (mode == M_PLAY);
                for (int i = 0; i < MAX_PLAYERS; i++) {
                    Player& p = players[i];
                    if (!p.active || p.dead) continue;
                    if (i == me) {
                        controlLocal(p, dt, in, allow && !p.choosing, true);
                        playerLogic(p, dt, allow && in.fire);
                    } else {
                        playerLogic(p, dt, p.fireHeld);
                        p.animT += dt * (p.moving ? 1.f : 0.5f);
                    }
                }
                updateRooms(dt);
                revealAround();
            }
            flowT -= dt;
            if (flowT <= 0.f) {
                flowT = 0.22f;
                std::vector<vec2> targets;
                for (auto& p : players) if (p.active && !p.dead) targets.push_back(p.pos);
                if (!targets.empty()) D.computeFlow(targets);
            }
            for (size_t i = 0; i < en.size(); i++) updateEnemy(en[i], dt);
            for (size_t i = 0; i < en.size(); i++) for (size_t j = i + 1; j < en.size(); j++) {
                Enemy &a = en[i], &b = en[j];
                if (a.dying || b.dying || a.spawn > 0.f || b.spawn > 0.f) continue;
                vec2 d = a.pos - b.pos; float dist = len2(d), md = a.r + b.r;
                if (dist < md && dist > 0.01f) {
                    vec2 push = d / dist * ((md - dist) * 0.5f * std::min(1.f, 10.f * dt));
                    if (!a.boss) moveCircle(a.pos, push, a.r);
                    if (!b.boss) moveCircle(b.pos, -push, b.r);
                }
            }
            flushSpawns();
            if (mode != M_DEAD) for (auto& p : players) {
                if (!p.active || p.dead) continue;
                for (int w = 0; w < p.st.wisps; w++) {
                    vec2 wp = wispPos(p, w);
                    for (auto& e : en) {
                        if (e.dying || e.spawn > 0.f || e.wispCd > 0.f) continue;
                        if (len2(e.pos - wp) < e.r + 5.f) { e.wispCd = 0.4f; damageEnemy(e, 1.f, norm2(e.pos - wp), 50.f, false, 0.f, p.slot); }
                    }
                }
            }
            updateBullets(dt);
            updatePickups(dt);
            en.erase(std::remove_if(en.begin(), en.end(), [](const Enemy& e) { return e.dying && e.dyingT > 0.4f; }), en.end());
            if (portalOpen && mode != M_DEAD && !descending) {
                for (auto& p : players) {
                    if (!p.active || p.dead) continue;
                    if (len2(p.pos - D.portalPos) < 14.f) {
                        descending = true;
                        burst(p.pos, 40, 100.f, vec3(1.2f, 1.8f, 3.0f), 0.8f, 1.6f);
                        shock(p.pos, 160.f, 6.f, 0.8f);
                        break;
                    }
                }
            }
        }
        updateCosmetics(dt);
        updateParticles(dt, time);
        updateCamera(realDt);
        if (role == NR_HOST) netSendHost(*this, realDt);
    }

    // ------------------------------------------------------- client update --
    // The client does not simulate monsters or bullets: it displays what the host
    // sends and only moves its own player (movement is client-authoritative).
    void updateClient(float realDt, const Input& in) {
        fxRecord = false;
        netPollClient(*this);
        if (role != NR_CLIENT) return;                     // the connection was lost
        bool joined = mode != M_TITLE;
        if (!joined) {
            fade = std::min(1.f, fade + realDt * 1.5f);
            if (in.pause) { returnToTitle(""); return; }
            updateParticles(realDt, time);
            updateCamera(realDt);
            return;
        }
        if (in.pause) { if (mode == M_PAUSE) mode = M_PLAY; else if (mode == M_PLAY) mode = M_PAUSE; }
        if (mode == M_DEAD) deadT += realDt;
        if (descending) fade = std::max(0.f, fade - realDt * 1.7f); else fade = std::min(1.f, fade + realDt * 1.6f);
        if (mode == M_BOON) {
            bool picked; int slot;
            boonUi(in, picked, slot);
            if (picked) { netClientBoonPick(*this, slot); L().choosing = false; mode = M_PLAY; }
        }
        Player& me_ = L();
        bool allow = (mode == M_PLAY) && !me_.dead && !me_.choosing;
        if (me_.active && !me_.dead) controlLocal(me_, realDt, in, allow, false);
        me_.invuln = std::max(0.f, me_.invuln - realDt);
        me_.muzzle = std::max(0.f, me_.muzzle - realDt * 9.f);
        me_.wispAng += realDt * 2.6f;
        me_.fireHeld = allow && in.fire;
        // smooth everything that came from the host
        float k = std::min(1.f, 14.f * realDt);
        for (auto& p : players) {
            if (!p.active || p.slot == me) continue;
            if (len2(p.tpos - p.pos) > 60.f) p.pos = p.tpos; else p.pos += (p.tpos - p.pos) * k;
            p.animT += realDt * (p.moving ? 1.f : 0.5f);
            p.wispAng += realDt * 2.6f;
            p.muzzle = std::max(0.f, p.muzzle - realDt * 9.f);
        }
        for (auto& e : en) {
            e.t += realDt;
            if (len2(e.tpos - e.pos) > 48.f) e.pos = e.tpos; else e.pos += (e.tpos - e.pos) * k;
        }
        for (auto& b : bullets) b.pos += b.vel * realDt;
        for (auto& p : pickups) p.t += realDt;
        updateCosmetics(realDt);
        updateParticles(realDt, time);
        updateCamera(realDt);
        netSendClient(*this, realDt, in);
    }
};

// ============================================================================
//  Networking: host-authoritative co-op over plain TCP (no extra libraries)
//
//   host   runs the real simulation, accepts up to 3 friends, sends
//          * a FLOOR message whenever a new floor starts (the whole dungeon)
//          * a SNAPSHOT 30x per second (players, monsters, bullets, pickups ...)
//          * FX events (hits, deaths, explosions ... so clients can reproduce them)
//   client sends its own player's state (position, aim, buttons) ~60x per second
//          and replays what the host sends.  Movement is client-authoritative
//          (instant controls); damage, loot and AI are host-authoritative.
// ============================================================================
enum NetMsgType {
    S_HELLO = 1, S_FLOOR, S_SNAP, S_FX, S_BANNER, S_BOON, S_HURT, S_TELEPORT, S_EXPLORED, S_FULL,
    C_JOIN = 20, C_STATE, C_BOON
};

static void netPlatformInit() {
    static bool done = false;
    if (done) return;
    done = true;
#ifdef _WIN32
    WSADATA w;
    WSAStartup(MAKEWORD(2, 2), &w);
#else
    std::signal(SIGPIPE, SIG_IGN);
#endif
}
static bool sockWouldBlock() {
#ifdef _WIN32
    int e = WSAGetLastError();
    return e == WSAEWOULDBLOCK || e == WSAEINPROGRESS || e == WSAEALREADY;
#else
    return errno == EWOULDBLOCK || errno == EAGAIN || errno == EINPROGRESS || errno == EINTR;
#endif
}
static void sockClose(sock_t& s) {
    if (s == BAD_SOCK) return;
#ifdef _WIN32
    closesocket(s);
#else
    ::close(s);
#endif
    s = BAD_SOCK;
}
static bool sockNonBlocking(sock_t s) {
#ifdef _WIN32
    u_long m = 1;
    return ioctlsocket(s, FIONBIO, &m) == 0;
#else
    int f = fcntl(s, F_GETFL, 0);
    return f >= 0 && fcntl(s, F_SETFL, f | O_NONBLOCK) == 0;
#endif
}
static void sockNoDelay(sock_t s) {
    int one = 1;
    setsockopt(s, IPPROTO_TCP, TCP_NODELAY, (const char*)&one, sizeof(one));
}

// best-effort local LAN address, shown to the host so friends know what to type
static std::string netLocalIp() {
    netPlatformInit();
    std::string out = "UNKNOWN";
    sock_t s = socket(AF_INET, SOCK_DGRAM, 0);
    if (s == BAD_SOCK) return out;
    sockaddr_in a;
    std::memset(&a, 0, sizeof(a));
    a.sin_family = AF_INET; a.sin_port = htons(53);
    inet_pton(AF_INET, "8.8.8.8", &a.sin_addr);
    if (connect(s, (sockaddr*)&a, sizeof(a)) == 0) {
        sockaddr_in me_; sock_len_t l = sizeof(me_);
        if (getsockname(s, (sockaddr*)&me_, &l) == 0) {
            char buf[64];
            if (inet_ntop(AF_INET, &me_.sin_addr, buf, sizeof(buf))) out = buf;
        }
    }
    sockClose(s);
    return out;
}

struct NetMsg { int type = 0; std::vector<uint8_t> data; };

struct Conn {
    sock_t s = BAD_SOCK;
    bool open = false, joined = false;
    std::vector<uint8_t> rx, tx;
    size_t txOff = 0;
    float lastTeleport = 0.f;

    size_t backlog() const { return tx.size() - txOff; }
    void closeConn() { sockClose(s); open = false; }

    void flush() {
        while (open && txOff < tx.size()) {
            int n = (int)::send(s, (const char*)tx.data() + txOff, (int)(tx.size() - txOff), NET_SEND_FLAGS);
            if (n > 0) txOff += (size_t)n;
            else if (n < 0 && sockWouldBlock()) break;
            else { closeConn(); return; }
        }
        if (txOff >= tx.size()) { tx.clear(); txOff = 0; }
        else if (txOff > (1u << 16)) { tx.erase(tx.begin(), tx.begin() + (std::ptrdiff_t)txOff); txOff = 0; }
    }
    void sendMsg(int type, const std::vector<uint8_t>& payload) {
        if (!open) return;
        uint32_t len = (uint32_t)payload.size() + 1u;
        for (int i = 0; i < 4; i++) tx.push_back((uint8_t)((len >> (8 * i)) & 255));
        tx.push_back((uint8_t)type);
        tx.insert(tx.end(), payload.begin(), payload.end());
        if (backlog() > (8u << 20)) { closeConn(); return; }       // a client that cannot keep up is dropped
        flush();
    }
    void sendMsg(int type, const ByteWriter& w) { sendMsg(type, w.b); }

    void recvAll(std::vector<NetMsg>& out) {
        if (!open) return;
        uint8_t buf[16384];
        for (;;) {
            int n = (int)::recv(s, (char*)buf, (int)sizeof(buf), 0);
            if (n > 0) rx.insert(rx.end(), buf, buf + n);
            else if (n == 0) { open = false; break; }
            else { if (sockWouldBlock()) break; open = false; break; }
            if (rx.size() > (16u << 20)) { open = false; break; }
        }
        size_t off = 0;
        while (rx.size() - off >= 5) {
            uint32_t len = (uint32_t)rx[off] | ((uint32_t)rx[off + 1] << 8) | ((uint32_t)rx[off + 2] << 16) | ((uint32_t)rx[off + 3] << 24);
            if (len < 1 || len > (4u << 20)) { open = false; rx.clear(); return; }
            if (rx.size() - off < 4 + (size_t)len) break;
            NetMsg m;
            m.type = rx[off + 4];
            m.data.assign(rx.begin() + (std::ptrdiff_t)(off + 5), rx.begin() + (std::ptrdiff_t)(off + 4 + len));
            out.push_back(std::move(m));
            off += 4 + (size_t)len;
        }
        if (off) rx.erase(rx.begin(), rx.begin() + (std::ptrdiff_t)off);
    }
};

struct NetState {
    bool isHost = false, connecting = false, joined = false, exploredDirty = false;
    sock_t listenSock = BAD_SOCK;
    Conn conns[MAX_PLAYERS];            // host: one connection per remote slot (1..3)
    Conn server;                        // client: the connection to the host
    float connectT = 0.f, snapAcc = 0.f, stateAcc = 0.f, exploredAcc = 0.f;
    uint32_t tick = 0;
};

// ---------------------------------------------------------------- dungeon ----
static void netWriteFloor(Game& g, ByteWriter& w) {
    const Dungeon& D = g.D;
    const size_t N = (size_t)MAPW * MAPH;
    w.u8(D.theme);
    w.pos(D.startPos); w.pos(D.portalPos);
    w.raw(D.solid.data(), N); w.raw(D.gate.data(), N); w.raw(D.gateHoriz.data(), N);
    w.raw(D.kind.data(), N);  w.raw(D.variant.data(), N);
    w.u8((int)D.rooms.size());
    for (const Room& r : D.rooms) {
        w.u8(r.x); w.u8(r.y); w.u8(r.w); w.u8(r.h); w.u8(r.type); w.u8(r.waves);
        w.u16((int)r.gates.size());
        for (int gi : r.gates) w.u16(gi);
    }
    w.u16((int)D.torches.size());
    for (const Torch& t : D.torches) { w.u8(t.tx); w.u8(t.ty); w.u8((int)(clampf(t.phase / 6.4f, 0.f, 0.99f) * 255.f)); }
    w.u16((int)D.props.size());
    for (const PropSpawn& p : D.props) w.pos(p.pos);
}

static bool netReadFloor(Game& g, ByteReader& r) {
    Dungeon& D = g.D;
    const size_t N = (size_t)MAPW * MAPH;
    D.theme = clampi(r.u8(), 0, 2);
    D.startPos = r.pos(); D.portalPos = r.pos();
    auto grab = [&](std::vector<uint8_t>& dst) { const uint8_t* p = r.raw(N); if (p) dst.assign(p, p + N); else dst.assign(N, 0); };
    grab(D.solid); grab(D.gate); grab(D.gateHoriz); grab(D.kind); grab(D.variant);
    int nr = r.u8();
    D.rooms.clear();
    for (int i = 0; i < nr && r.ok; i++) {
        Room rm;
        rm.x = r.u8(); rm.y = r.u8(); rm.w = r.u8(); rm.h = r.u8(); rm.type = r.u8(); rm.waves = r.u8();
        rm.cleared = (rm.type == R_START || rm.type == R_TREASURE);
        int ng = r.u16();
        for (int k = 0; k < ng && r.ok; k++) { int gi = r.u16(); if (gi >= 0 && (size_t)gi < N) rm.gates.push_back(gi); }
        D.rooms.push_back(rm);
    }
    D.torches.clear();
    int nt = r.u16();
    for (int i = 0; i < nt && r.ok; i++) { Torch t; t.tx = r.u8(); t.ty = r.u8(); t.phase = (float)r.u8() / 255.f * 6.4f; D.torches.push_back(t); }
    D.props.clear();
    int np = r.u16();
    for (int i = 0; i < np && r.ok; i++) { PropSpawn p; p.pos = r.pos(); D.props.push_back(p); }
    if (!r.ok || D.rooms.empty()) return false;
    for (size_t i = 0; i < N; i++) {                         // never trust the wire: keep every art index in range
        switch (D.kind[i]) {
            case K_FLOOR: D.variant[i] = (uint8_t)(D.variant[i] % 6); break;
            case K_FACE:  D.variant[i] = (uint8_t)(D.variant[i] % 3); break;
            case K_CAP:   D.variant[i] = (uint8_t)(D.variant[i] & 15); break;
            default:      D.kind[i] = K_VOID; D.variant[i] = 0; break;
        }
    }
    for (Room& rm : D.rooms) rm.type = clampi(rm.type, 0, R_BOSS);
    D.closed.assign(N, 0); D.explored.assign(N, 0); D.roomAt.assign(N, -1); D.flow.clear();
    for (size_t i = 0; i < D.rooms.size(); i++) {
        const Room& rm = D.rooms[i];
        for (int y = rm.y; y < rm.y + rm.h; y++) for (int x = rm.x; x < rm.x + rm.w; x++)
            if (Dungeon::inb(x, y)) D.roomAt[(size_t)Dungeon::idx(x, y)] = (int8_t)i;
    }
    D.computeSdf();
    D.gen++;
    return true;
}

// ------------------------------------------------------------ host: sending --
static void netHostFloor(Game& g) {
    NetState* n = g.net;
    if (!n || !n->isHost) return;
    ByteWriter blob;
    bool any = false;
    for (int i = 1; i < MAX_PLAYERS; i++) if (n->conns[i].open && n->conns[i].joined) any = true;
    if (!any) return;
    netWriteFloor(g, blob);
    for (int i = 1; i < MAX_PLAYERS; i++) {
        Conn& c = n->conns[i];
        if (!c.open || !c.joined) continue;
        ByteWriter w;
        w.u8(g.pendingNewRun ? 1 : 0); w.u8(g.floorNo); w.pos(g.players[i].pos);
        w.raw(blob.b.data(), blob.b.size());
        c.sendMsg(S_FLOOR, w);
    }
}
static void netHostBanner(Game& g, int slot, const std::string& t, const std::string& sub, float dur, vec3 col) {
    NetState* n = g.net;
    if (!n || !n->isHost) return;
    ByteWriter w;
    w.str(t); w.str(sub); w.f32(dur); w.v3(col);
    for (int i = 1; i < MAX_PLAYERS; i++)
        if (n->conns[i].open && n->conns[i].joined && (slot < 0 || slot == i)) n->conns[i].sendMsg(S_BANNER, w);
}
static void netHostBoonOffer(Game& g, int slot) {
    NetState* n = g.net;
    if (!n || !n->isHost || slot < 1 || slot >= MAX_PLAYERS || !n->conns[slot].open) return;
    const Player& p = g.players[slot];
    ByteWriter w;
    w.u8(p.boonChoices);
    for (int i = 0; i < 3; i++) w.u8(p.boonChoice[i]);
    n->conns[slot].sendMsg(S_BOON, w);
}
static void netHostHurt(Game& g, int slot, int dmg, vec2 kb) {
    NetState* n = g.net;
    if (!n || !n->isHost || slot < 1 || slot >= MAX_PLAYERS || !n->conns[slot].open) return;
    ByteWriter w;
    w.u8(dmg); w.v2(kb);
    n->conns[slot].sendMsg(S_HURT, w);
}
static void netHostTeleport(Game& g, int slot, vec2 pos) {
    NetState* n = g.net;
    if (!n || !n->isHost || slot < 1 || slot >= MAX_PLAYERS || !n->conns[slot].open) return;
    ByteWriter w;
    w.pos(pos);
    n->conns[slot].sendMsg(S_TELEPORT, w);
}

static void netWriteSnapshot(Game& g, NetState* n, ByteWriter& w) {
    w.u32(++n->tick);
    w.u8((g.portalOpen ? 1 : 0) | (g.mode == M_DEAD ? 2 : 0) | (g.descending ? 4 : 0));
    w.u8(g.floorNo); w.u16(g.souls); w.u16(g.kills);
    w.pos(g.D.portalPos);
    for (int i = 0; i < MAX_PLAYERS; i++) {
        const Player& p = g.players[i];
        int f = (p.active ? 1 : 0) | (p.dead ? 2 : 0) | (p.visible ? 4 : 0) | (p.moving ? 8 : 0) | ((p.dashT > 0.f || p.dashing) ? 16 : 0)
              | (p.facingLeft ? 32 : 0) | (p.invuln > 0.f ? 64 : 0) | (p.choosing ? 128 : 0);
        w.u8(f);
        if (!p.active) continue;
        w.pos(p.pos);
        w.i16((int)std::lround(p.vel.x * 8.f)); w.i16((int)std::lround(p.vel.y * 8.f));
        float ang = std::atan2(p.aimDir.y, p.aimDir.x); if (ang < 0.f) ang += 2.f * PI;
        w.u16((int)(ang / (2.f * PI) * 65535.f));
        w.u8(p.hp); w.u8(p.maxHp); w.u8(p.dashCharges); w.u8(p.st.wisps); w.u8((int)(clampf(p.muzzle, 0.f, 1.f) * 255.f));
        for (int b = 0; b < B_COUNT; b++) w.u8(p.boon[b]);
    }
    int ne = (int)std::min<size_t>(g.en.size(), 700);
    w.u16(ne);
    for (int i = 0; i < ne; i++) {
        const Enemy& e = g.en[(size_t)i];
        w.u16(e.id); w.u8(e.type); w.u8(e.state);
        w.pos(e.pos);
        w.u16((int)std::lround(clampf(e.hp, 0.f, 8000.f) * 8.f)); w.u16((int)std::lround(clampf(e.maxHp, 0.f, 8000.f) * 8.f));
        w.u8((e.dying ? 1 : 0) | (e.faceLeft ? 2 : 0) | (e.slow > 0.f ? 4 : 0) | (e.spawn > 0.f ? 8 : 0));
        w.u8((int)(clampf(e.flash, 0.f, 1.f) * 255.f)); w.u8((int)(clampf(e.warn, 0.f, 1.f) * 255.f));
        w.u8((int)(clampf(e.dissolve, 0.f, 1.f) * 255.f));
        w.u8((int)(clampf(e.dyingT / 0.4f, 0.f, 1.f) * 255.f));
    }
    int nb = (int)std::min<size_t>(g.bullets.size(), 1600);
    w.u16(nb);
    for (int i = 0; i < nb; i++) {
        const Bullet& b = g.bullets[(size_t)i];
        w.pos(b.pos);
        w.i16((int)std::lround(clampf(b.vel.x, -500.f, 500.f) * 64.f)); w.i16((int)std::lround(clampf(b.vel.y, -500.f, 500.f) * 64.f));
        w.u8(b.kind); w.u8((b.friendly ? 1 : 0) | (b.crit ? 2 : 0));
        w.u8((int)(clampf(b.life, 0.f, 5.3f) * 48.f));
        w.u8((int)(clampf(b.col.x, 0.f, 1.f) * 255.f)); w.u8((int)(clampf(b.col.y, 0.f, 1.f) * 255.f)); w.u8((int)(clampf(b.col.z, 0.f, 1.f) * 255.f));
    }
    int np = (int)std::min<size_t>(g.pickups.size(), 300);
    w.u16(np);
    for (int i = 0; i < np; i++) {
        const Pickup& p = g.pickups[(size_t)i];
        w.u8(p.type); w.pos(p.pos); w.u16((int)(std::fmod(p.t, 600.f) * 100.f));
    }
    int npr = (int)std::min<size_t>(g.props.size(), 200);
    w.u16(npr);
    for (int i = 0; i < npr; i++) w.pos(g.props[(size_t)i].pos);
    w.u8((int)g.D.rooms.size());
    for (const Room& r : g.D.rooms) w.u8((r.active ? 1 : 0) | (r.cleared ? 2 : 0) | (r.explored ? 4 : 0));
}

static void netSendHost(Game& g, float dt) {
    NetState* n = g.net;
    if (!n || !n->isHost) return;
    bool any = false;
    for (int i = 1; i < MAX_PLAYERS; i++) if (n->conns[i].open && n->conns[i].joined) any = true;
    if (g.miniDirty) { n->exploredDirty = true; g.miniDirty = false; }
    if (!any) { g.fxW.clear(); return; }
    n->snapAcc += dt; n->exploredAcc += dt;
    if (n->snapAcc < 1.f / 30.f) return;
    n->snapAcc = 0.f;
    ByteWriter snap;
    netWriteSnapshot(g, n, snap);
    ByteWriter explored;
    bool sendExplored = n->exploredDirty && n->exploredAcc > 0.5f;
    if (sendExplored) {
        n->exploredDirty = false; n->exploredAcc = 0.f;
        const size_t N = (size_t)MAPW * MAPH;
        explored.u16((int)N);
        for (size_t i = 0; i < N; i += 8) {
            int byte = 0;
            for (size_t k = 0; k < 8 && i + k < N; k++) if (g.D.explored[i + k]) byte |= 1 << k;
            explored.u8(byte);
        }
    }
    for (int i = 1; i < MAX_PLAYERS; i++) {
        Conn& c = n->conns[i];
        if (!c.open || !c.joined) continue;
        if (c.backlog() > 262144) continue;                          // slow link: skip this update
        if (!g.fxW.b.empty()) c.sendMsg(S_FX, g.fxW);
        c.sendMsg(S_SNAP, snap);
        if (sendExplored) c.sendMsg(S_EXPLORED, explored);
        c.flush();
    }
    g.fxW.clear();
}

// ------------------------------------------------------------ host: receiving --
static void netHostDisconnect(Game& g, NetState* n, int slot) {
    Conn& c = n->conns[slot];
    c.closeConn(); c.joined = false; c.rx.clear(); c.tx.clear(); c.txOff = 0;
    if (g.players[slot].active) {
        g.burst(g.players[slot].pos, 30, 90.f, vec3(1.2f, 1.8f, 2.8f), 0.7f, 1.6f);
        g.players[slot] = Player();
    }
    if (g.mode != M_DEAD && g.mode != M_TITLE && g.aliveCount() == 0) g.gameOver();
}

static void netHostHandle(Game& g, NetState* n, int slot, const NetMsg& m) {
    Conn& c = n->conns[slot];
    ByteReader r(m.data.data(), m.data.size());
    if (m.type == C_JOIN) {
        int ver = r.u8();
        if (ver != NET_VERSION || c.joined) { if (ver != NET_VERSION) c.closeConn(); return; }
        g.resetPlayer(slot);
        Player& p = g.players[slot];
        Player* anchor = g.nearestAlive(g.L().pos);
        vec2 sp = anchor ? anchor->pos + vec2((slot - 1.5f) * 10.f, 8.f) : g.D.startPos;
        if (g.blockedCircle(sp, p.r)) sp = g.D.startPos;
        p.pos = sp; p.tpos = sp;
        c.joined = true;
        ByteWriter w;
        w.u8(slot); w.u8(NET_VERSION);
        c.sendMsg(S_HELLO, w);
        if (g.mode != M_TITLE) {
            ByteWriter fw, blob;
            netWriteFloor(g, blob);
            fw.u8(0); fw.u8(g.floorNo); fw.pos(p.pos);
            fw.raw(blob.b.data(), blob.b.size());
            c.sendMsg(S_FLOOR, fw);
        }
        g.burst(p.pos, 30, 90.f, vec3(1.2f, 2.0f, 2.8f), 0.7f, 1.6f);
    } else if (m.type == C_STATE && c.joined) {
        Player& p = g.players[slot];
        if (!p.active) return;
        int fl = r.u8();
        vec2 np = r.pos();
        float vx = (float)r.i16() / 8.f; float vy = (float)r.i16() / 8.f;
        float ang = (float)r.u16() / 65535.f * 2.f * PI;
        int charges = r.u8(), dashCount = r.u8();
        if (!r.ok || p.dead) return;
        if (!p.choosing) {
            bool ok = !g.blockedCircle(np, std::max(1.f, p.r - 0.8f)) && len2(np - p.pos) < 140.f;
            if (ok) p.pos = np;
            else if (g.time - c.lastTeleport > 0.25f) { c.lastTeleport = g.time; netHostTeleport(g, slot, p.pos); }
        }
        p.vel = vec2(vx, vy);
        p.aimDir = angVec(ang);
        p.fireHeld = (fl & 1) != 0;
        p.dashing = (fl & 2) != 0;
        p.dashT = p.dashing ? 0.05f : 0.f;
        p.moving = (fl & 4) != 0;
        p.facingLeft = (fl & 8) != 0;
        p.dashCharges = clampi(charges, 0, p.st.maxDash);
        if (dashCount != p.dashSeen) {                       // a dash started: show it to everyone
            p.dashSeen = dashCount;
            p.invuln = std::max(p.invuln, 0.25f);
            g.shock(p.pos, 40.f, 3.f, 0.3f);
            g.burst(p.pos, 10, 60.f, vec3(0.5f, 1.4f, 2.2f), 0.3f, 1.4f);
        }
    } else if (m.type == C_BOON && c.joined) {
        int pick = r.u8();
        if (r.ok) g.takeBoon(g.players[slot], pick);
    }
}

static void netPollHost(Game& g) {
    NetState* n = g.net;
    if (!n || !n->isHost) return;
    for (;;) {                                               // new connections
        sockaddr_in a; sock_len_t al = sizeof(a);
        sock_t s = accept(n->listenSock, (sockaddr*)&a, &al);
        if (s == BAD_SOCK) break;
        sockNonBlocking(s); sockNoDelay(s);
        int slot = -1;
        for (int i = 1; i < MAX_PLAYERS; i++) if (!g.players[i].active && !n->conns[i].open) { slot = i; break; }
        if (slot < 0) {
            Conn tmp; tmp.s = s; tmp.open = true;
            tmp.sendMsg(S_FULL, std::vector<uint8_t>());
            tmp.closeConn();
            continue;
        }
        n->conns[slot] = Conn();
        n->conns[slot].s = s; n->conns[slot].open = true;
    }
    for (int i = 1; i < MAX_PLAYERS; i++) {
        Conn& c = n->conns[i];
        if (!c.open && !c.joined) continue;
        std::vector<NetMsg> msgs;
        c.recvAll(msgs);
        for (const NetMsg& m : msgs) netHostHandle(g, n, i, m);
        c.flush();
        if (!c.open) netHostDisconnect(g, n, i);
    }
}

// ------------------------------------------------------------- client side ---
static void netClientBoonPick(Game& g, int pickSlot) {
    NetState* n = g.net;
    if (!n || n->isHost || !n->server.open) return;
    ByteWriter w;
    w.u8(pickSlot);
    n->server.sendMsg(C_BOON, w);
}

static void netSendClient(Game& g, float dt, const Input& /*in*/) {
    NetState* n = g.net;
    if (!n || n->isHost || !n->joined || !n->server.open) return;
    n->stateAcc += dt;
    if (n->stateAcc < 1.f / 60.f) return;
    n->stateAcc = 0.f;
    const Player& p = g.L();
    ByteWriter w;
    w.u8((p.fireHeld ? 1 : 0) | (p.dashT > 0.f ? 2 : 0) | (p.moving ? 4 : 0) | (p.facingLeft ? 8 : 0));
    w.pos(p.pos);
    w.i16((int)std::lround(p.vel.x * 8.f)); w.i16((int)std::lround(p.vel.y * 8.f));
    float ang = std::atan2(p.aimDir.y, p.aimDir.x); if (ang < 0.f) ang += 2.f * PI;
    w.u16((int)(ang / (2.f * PI) * 65535.f));
    w.u8(p.dashCharges); w.u8(p.dashCount & 255);
    n->server.sendMsg(C_STATE, w);
}

static void netReadSnapshot(Game& g, NetState* n, ByteReader& r) {
    (void)n;
    r.u32();
    int flags = r.u8();
    r.u8();                                                  // floor number (the FLOOR message is authoritative)
    int souls = r.u16(), kills = r.u16();
    vec2 portal = r.pos();
    g.souls = souls; g.kills = kills;
    g.portalOpen = (flags & 1) != 0;
    if (g.portalOpen) g.D.portalPos = portal;
    g.descending = (flags & 4) != 0;
    bool over = (flags & 2) != 0;
    if (over && g.mode != M_DEAD) { g.mode = M_DEAD; g.deadT = 0.f; }
    else if (!over && g.mode == M_DEAD) g.mode = M_PLAY;

    for (int i = 0; i < MAX_PLAYERS && r.ok; i++) {
        Player& p = g.players[i];
        int f = r.u8();
        if (!(f & 1)) { if (p.active) p = Player(); continue; }
        bool was = p.active;
        p.active = true; p.slot = i;
        vec2 pos = r.pos();
        float vx = (float)r.i16() / 8.f; float vy = (float)r.i16() / 8.f;
        float ang = (float)r.u16() / 65535.f * 2.f * PI;
        int hp = r.u8(), maxHp = r.u8(), charges = r.u8(), wisps = r.u8(), muzzle = r.u8();
        int boons[B_COUNT];
        for (int b = 0; b < B_COUNT; b++) boons[b] = r.u8();
        if (!r.ok) break;
        bool changed = false;
        for (int b = 0; b < B_COUNT; b++) if (p.boon[b] != boons[b]) { p.boon[b] = boons[b]; changed = true; }
        if (changed || !was) g.recompute(p);
        p.hp = hp; p.maxHp = maxHp; p.dead = (f & 2) != 0; p.visible = (f & 4) != 0;
        p.invuln = (f & 64) ? std::max(p.invuln, 0.1f) : 0.f;
        if (i == g.me) {
            if (!was) { p.pos = pos; p.tpos = pos; }
            if (p.dead) p.pos = pos;
        } else {
            p.tpos = pos; if (!was) p.pos = pos;
            p.vel = vec2(vx, vy); p.aimDir = angVec(ang); p.moving = (f & 8) != 0; p.facingLeft = (f & 32) != 0;
            p.dashT = (f & 16) ? 0.1f : 0.f; p.dashCharges = charges; p.st.wisps = wisps; p.choosing = (f & 128) != 0;
            p.muzzle = std::max(p.muzzle, (float)muzzle / 255.f);
        }
    }

    std::vector<Enemy> en;
    int ne = r.u16();
    std::unordered_map<int, size_t> old;
    for (size_t i = 0; i < g.en.size(); i++) old[g.en[i].id] = i;
    for (int i = 0; i < ne && r.ok; i++) {
        int id = r.u16(), type = r.u8(), state = r.u8();
        vec2 pos = r.pos();
        float hp = (float)r.u16() / 8.f, maxHp = (float)r.u16() / 8.f;
        int fl = r.u8();
        float flash = (float)r.u8() / 255.f, warn = (float)r.u8() / 255.f, dis = (float)r.u8() / 255.f, dy = (float)r.u8() / 255.f * 0.4f;
        if (!r.ok || type >= E_COUNT) { r.ok = false; break; }
        Enemy e;
        auto it = old.find(id);
        if (it != old.end()) e = g.en[it->second];
        else { e.pos = pos; e.phase = (float)(id % 628) / 100.f; }
        e.id = id; e.type = type; e.state = state; e.tpos = pos; e.hp = hp; e.maxHp = maxHp; e.r = kEDef[type].r;
        e.boss = type >= E_KING;
        e.seed = (float)(id % 1000);
        e.dying = (fl & 1) != 0; e.faceLeft = (fl & 2) != 0; e.slow = (fl & 4) ? 1.f : 0.f; e.spawn = (fl & 8) ? 0.5f : 0.f;
        e.flash = flash; e.warn = warn; e.dissolve = dis; e.dyingT = dy;
        en.push_back(e);
    }
    std::vector<Bullet> bl;
    int nb = r.u16();
    for (int i = 0; i < nb && r.ok; i++) {
        Bullet b;
        b.pos = r.pos();
        float vx = (float)r.i16() / 64.f; float vy = (float)r.i16() / 64.f;
        b.vel = vec2(vx, vy);
        b.kind = r.u8();
        int fl = r.u8();
        b.life = (float)r.u8() / 48.f;
        float cr = (float)r.u8() / 255.f, cg = (float)r.u8() / 255.f, cb = (float)r.u8() / 255.f;
        b.col = vec3(cr, cg, cb);
        b.friendly = (fl & 1) != 0; b.crit = (fl & 2) != 0;
        b.r = b.friendly ? 3.f : (b.kind == BK_ARROW ? 2.5f : 3.f);
        bl.push_back(b);
    }
    std::vector<Pickup> pk;
    int np = r.u16();
    for (int i = 0; i < np && r.ok; i++) {
        Pickup p;
        p.type = r.u8(); p.pos = r.pos(); p.t = (float)r.u16() / 100.f;
        pk.push_back(p);
    }
    std::vector<Prop> pr;
    int npr = r.u16();
    for (int i = 0; i < npr && r.ok; i++) { Prop p; p.pos = r.pos(); pr.push_back(p); }
    int nrooms = r.u8();
    std::vector<int> rf_;
    for (int i = 0; i < nrooms && r.ok; i++) rf_.push_back(r.u8());
    if (!r.ok) return;                                       // damaged packet: keep the previous state
    g.en.swap(en); g.bullets.swap(bl); g.pickups.swap(pk); g.props.swap(pr);
    for (size_t i = 0; i < rf_.size() && i < g.D.rooms.size(); i++) {
        Room& rm = g.D.rooms[i];
        rm.active = (rf_[i] & 1) != 0; rm.cleared = (rf_[i] & 2) != 0; rm.explored = (rf_[i] & 4) != 0;
        bool lock = rm.active && !rm.cleared;
        for (int gi : rm.gates) g.D.closed[(size_t)gi] = lock ? 1 : 0;
    }
}

static void netClientHandle(Game& g, NetState* n, const NetMsg& m) {
    ByteReader r(m.data.data(), m.data.size());
    switch (m.type) {
        case S_HELLO: {
            int slot = r.u8(); r.u8();
            if (r.ok && slot >= 0 && slot < MAX_PLAYERS) { g.me = slot; g.netStatus = "CONNECTED - WAITING FOR THE HOST"; }
        } break;
        case S_FULL:
            g.returnToTitle("THE HOST IS FULL");
            break;
        case S_FLOOR: {
            int newRun = r.u8(), floorNo = r.u8();
            vec2 spawn = r.pos();
            if (!r.ok || !netReadFloor(g, r)) { g.returnToTitle("BAD DATA FROM HOST"); return; }
            g.floorNo = floorNo;
            g.en.clear(); g.bullets.clear(); g.pickups.clear(); g.props.clear(); g.parts.clear(); g.texts.clear();
            g.zaps.clear(); g.waves.clear(); g.booms.clear(); g.decals.clear(); g.ghosts.clear(); g.pend.clear(); g.decalHead = 0;
            g.portalOpen = false; g.descending = false; g.deadT = 0.f; g.newBest = false;
            if (newRun) for (auto& p : g.players) if (p.active) { for (int b = 0; b < B_COUNT; b++) p.boon[b] = 0; g.recompute(p); }
            for (auto& p : g.D.props) { Prop pr; pr.pos = p.pos; g.props.push_back(pr); }
            Player& me_ = g.L();
            if (!me_.active) { me_ = Player(); me_.active = true; me_.slot = g.me; g.recompute(me_); me_.hp = me_.maxHp; }
            me_.pos = spawn; me_.tpos = spawn; me_.vel = vec2(0.f, 0.f); me_.kb = vec2(0.f, 0.f); me_.dashT = 0.f;
            me_.dead = false; me_.visible = true; me_.choosing = false; me_.dashCharges = me_.st.maxDash;
            g.cam = spawn; g.camI = vec2(std::floor(g.cam.x - VW * 0.5f), std::floor(g.cam.y - VH * 0.5f));
            g.mode = M_PLAY; g.fade = 0.f; n->joined = true; g.netStatus.clear();
            char buf[64]; std::snprintf(buf, sizeof(buf), "DEPTH %d", floorNo);
            g.setBannerLocal(buf, kThemes[g.D.theme].name, 2.4f, vec3(1.f, 0.85f, 0.6f));
        } break;
        case S_SNAP:
            if (n->joined) netReadSnapshot(g, n, r);
            break;
        case S_FX:
            if (n->joined) g.applyFx(r);
            break;
        case S_BANNER: {
            std::string t = r.str(), sub = r.str(); float dur = r.f32(); vec3 col = r.v3();
            if (r.ok) g.setBannerLocal(t, sub, dur, col);
        } break;
        case S_BOON: {
            Player& p = g.L();
            int cnt = r.u8();
            for (int i = 0; i < 3; i++) p.boonChoice[i] = clampi(r.u8(), 0, B_COUNT - 1);
            if (r.ok && cnt > 0) { p.boonChoices = std::min(3, cnt); p.choosing = true; g.mode = M_BOON; g.boonSel = 0; }
        } break;
        case S_HURT: {
            int dmg = r.u8(); vec2 kb = r.v2();
            if (r.ok) { g.redFlash = 1.f; g.trauma = std::min(1.f, g.trauma + 0.65f); g.L().kb += kb; (void)dmg; }
        } break;
        case S_TELEPORT: {
            vec2 p = r.pos();
            if (r.ok) { g.L().pos = p; g.L().tpos = p; g.L().vel = vec2(0.f, 0.f); g.L().dashT = 0.f; }
        } break;
        case S_EXPLORED: {
            int cnt = r.u16();
            const size_t N = (size_t)MAPW * MAPH;
            if ((size_t)cnt != N || g.D.explored.size() != N) break;
            for (size_t i = 0; i < N; i += 8) {
                int byte = r.u8();
                for (size_t k = 0; k < 8 && i + k < N; k++) g.D.explored[i + k] = (byte >> k) & 1;
            }
        } break;
        default: break;
    }
}

static void netPollClient(Game& g) {
    NetState* n = g.net;
    if (!n || n->isHost) return;
    Conn& c = n->server;
    if (n->connecting) {
        n->connectT += 1.f / 60.f;
        fd_set wset, eset;
        FD_ZERO(&wset); FD_ZERO(&eset);
        FD_SET(c.s, &wset); FD_SET(c.s, &eset);
        timeval tv; tv.tv_sec = 0; tv.tv_usec = 0;
        int rc = select((int)c.s + 1, nullptr, &wset, &eset, &tv);
        if (rc > 0) {
            int err = 0; sock_len_t el = sizeof(err);
            getsockopt(c.s, SOL_SOCKET, SO_ERROR, (char*)&err, &el);
            if (err != 0 || FD_ISSET(c.s, &eset)) { g.returnToTitle("COULD NOT CONNECT"); return; }
            n->connecting = false;
            ByteWriter w;
            w.u8(NET_VERSION);
            c.sendMsg(C_JOIN, w);
        } else if (n->connectT > 8.f) { g.returnToTitle("CONNECTION TIMED OUT"); return; }
        if (n->connecting) return;
    }
    std::vector<NetMsg> msgs;
    c.recvAll(msgs);
    for (const NetMsg& m : msgs) {
        netClientHandle(g, n, m);
        if (g.net != n) return;                              // the handler dropped the connection
    }
    c.flush();
    if (!c.open) g.returnToTitle(n->joined ? "THE HOST LEFT" : "CONNECTION LOST");
}

// ------------------------------------------------------------ start / stop ---
static bool netStartHost(Game& g, int port) {
    netPlatformInit();
    sock_t s = socket(AF_INET, SOCK_STREAM, 0);
    if (s == BAD_SOCK) return false;
#ifndef _WIN32
    int one = 1;
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, (const char*)&one, sizeof(one));
#endif
    sockaddr_in a;
    std::memset(&a, 0, sizeof(a));
    a.sin_family = AF_INET; a.sin_addr.s_addr = htonl(INADDR_ANY); a.sin_port = htons((uint16_t)port);
    if (bind(s, (sockaddr*)&a, sizeof(a)) != 0 || listen(s, 8) != 0) { sockClose(s); return false; }
    sockNonBlocking(s);
    NetState* n = new NetState;
    n->isHost = true; n->listenSock = s;
    g.net = n;
    g.fxRecord = true;
    return true;
}

static bool netStartJoin(Game& g, const std::string& addr) {
    netPlatformInit();
    std::string host = addr;
    int port = NET_PORT;
    size_t colon = addr.rfind(':');
    if (colon != std::string::npos) {
        host = addr.substr(0, colon);
        port = std::atoi(addr.c_str() + colon + 1);
        if (port <= 0 || port > 65535) port = NET_PORT;
    }
    addrinfo hints;
    std::memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET; hints.ai_socktype = SOCK_STREAM;
    addrinfo* res = nullptr;
    if (host.empty() || getaddrinfo(host.c_str(), std::to_string(port).c_str(), &hints, &res) != 0 || !res) { g.netStatus = "BAD ADDRESS"; return false; }
    sock_t s = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (s == BAD_SOCK) { freeaddrinfo(res); g.netStatus = "SOCKET ERROR"; return false; }
    sockNonBlocking(s); sockNoDelay(s);
    int rc = connect(s, res->ai_addr, (int)res->ai_addrlen);
    bool pending = rc != 0;
    if (pending && !sockWouldBlock()) { freeaddrinfo(res); sockClose(s); g.netStatus = "COULD NOT CONNECT"; return false; }
    freeaddrinfo(res);
    NetState* n = new NetState;
    n->isHost = false; n->server.s = s; n->server.open = true; n->connecting = pending;
    g.net = n;
    if (!pending) { ByteWriter w; w.u8(NET_VERSION); n->server.sendMsg(C_JOIN, w); }
    return true;
}

static void netShutdown(Game& g) {
    NetState* n = g.net;
    if (!n) return;
    for (int i = 0; i < MAX_PLAYERS; i++) n->conns[i].closeConn();
    n->server.closeConn();
    sockClose(n->listenSock);
    delete n;
    g.net = nullptr;
    g.fxRecord = false;
    g.fxW.clear();
}
// ============================================================================
//  Scene + HUD construction (turns Game state into sprite batches and lights)
// ============================================================================
static std::string upperStr(const std::string& s) {
    std::string r = s;
    for (auto& c : r) if (c >= 'a' && c <= 'z') c = (char)(c - 32);
    return r;
}

static float textWidth(const std::string& s, int scale) { return s.empty() ? 0.f : (float)s.size() * 6.f * scale - scale; }

// pixel text with a dark outline.  align: 0 left, 1 centre, 2 right.  Colours may be > 1 (HDR glow).
static void drawText(Batch& b, const std::string& str, float x, float y, int scale, vec3 col, float alpha = 1.f, int align = 0, bool outline = true) {
    std::string s = upperStr(str);
    float w = textWidth(s, scale);
    if (align == 1) x -= w * 0.5f; else if (align == 2) x -= w;
    x = std::floor(x); y = std::floor(y);
    auto pass = [&](float ox, float oy, vec4 c) {
        float cx = x + ox;
        for (char ch : s) {
            int id = (unsigned char)ch < 128 ? ART.font[(int)ch] : -1;
            if (id >= 0) b.quad(id, cx + 2.5f * scale, y + oy + 3.5f * scale, 5.f * scale, 7.f * scale, 0.f, false, false, c);
            cx += 6.f * scale;
        }
    };
    if (outline) {
        float o = std::max(1.f, std::floor(scale / 3.f + 0.5f));
        vec4 dk(0.02f, 0.01f, 0.04f, alpha * 0.85f);
        pass(-o, 0.f, dk); pass(o, 0.f, dk); pass(0.f, -o, dk); pass(0.f, o, dk); pass(o, o, dk);
    }
    pass(0.f, 0.f, vec4(col, alpha));
}

static void hudRect(Batch& b, float x, float y, float w, float h, vec3 col, float alpha) {
    b.quad(ART.dot, x + w * 0.5f, y + h * 0.5f, w, h, 0.f, false, false, vec4(col, alpha));
}
static void hudBox(Batch& b, float x, float y, float w, float h, vec3 border, vec3 fill, float alpha) {
    hudRect(b, x, y, w, h, fill, alpha);
    hudRect(b, x, y, w, 1, border, 1.f); hudRect(b, x, y + h - 1, w, 1, border, 1.f);
    hudRect(b, x, y, 1, h, border, 1.f); hudRect(b, x + w - 1, y, 1, h, border, 1.f);
}

static void buildMinimap(const Game& g, std::vector<uint8_t>& px) {
    px.assign((size_t)MAPW * MAPH * 4, 0);
    auto put = [&](int x, int y, int r, int gg, int bb, int a) {
        if (!Dungeon::inb(x, y)) return;
        size_t i = ((size_t)y * MAPW + x) * 4;
        px[i] = (uint8_t)r; px[i + 1] = (uint8_t)gg; px[i + 2] = (uint8_t)bb; px[i + 3] = (uint8_t)a;
    };
    int curR = g.D.roomIndexAt(g.L().pos, 0.f);
    for (int y = 0; y < MAPH; y++) for (int x = 0; x < MAPW; x++) {
        size_t i = (size_t)Dungeon::idx(x, y);
        if (g.D.solid[i]) continue;
        if (!g.D.explored[i]) continue;
        int ra = g.D.roomAt[i];
        int r = 70, gg = 84, b = 130;
        if (ra >= 0) {
            const Room& rm = g.D.rooms[(size_t)ra];
            if (rm.type == R_BOSS) { r = 120; gg = 50; b = 70; }
            else if (rm.type == R_TREASURE) { r = 130; gg = 110; b = 50; }
            if (ra == curR) { r += 60; gg += 60; b += 60; }
        }
        if (g.D.closed[i]) { r = 230; gg = 70; b = 60; }
        put(x, y, r, gg, b, 235);
        static const int dx[4] = {1, -1, 0, 0}, dy[4] = {0, 0, 1, -1};
        for (int k = 0; k < 4; k++) {
            int nx = x + dx[k], ny = y + dy[k];
            if (Dungeon::inb(nx, ny) && g.D.solid[(size_t)Dungeon::idx(nx, ny)]) put(nx, ny, 26, 30, 52, 255);
        }
    }
    if (g.portalOpen) {
        int cx = (int)(g.D.portalPos.x / TS), cy = (int)(g.D.portalPos.y / TS);
        for (int dy = -1; dy <= 1; dy++) for (int dx = -1; dx <= 1; dx++) put(cx + dx, cy + dy, 120, 230, 255, 255);
    }
}

static const vec3 kPlayerCol[4] = {vec3(0.45f, 0.9f, 1.4f), vec3(1.4f, 0.65f, 0.4f), vec3(0.6f, 1.3f, 0.5f), vec3(1.2f, 0.65f, 1.4f)};
struct EntRef { float y; int kind; int i; };

static void buildFrame(Renderer& R, Game& g, FrameParams& fp, const std::vector<uint8_t>* /*unused*/, int /*winW*/, int /*winH*/) {
    R.clearBatches();
    const vec2 cam = g.camI;
    const Theme& th = kThemes[g.D.theme];
    const float t = g.time;
    auto S = [&](vec2 w) { return w - cam; };
    auto onScreen = [&](vec2 p, float m) { vec2 s = p - cam; return s.x > -m && s.y > -m && s.x < VW + m && s.y < VH + m; };

    Batch& tiles = R.bTiles;
    // ------------------------------------------------------------ tiles ----
    int tx0 = std::max(0, (int)std::floor(cam.x / TS)), tx1 = std::min(MAPW - 1, (int)std::floor((cam.x + VW) / TS));
    int ty0 = std::max(0, (int)std::floor(cam.y / TS)), ty1 = std::min(MAPH - 1, (int)std::floor((cam.y + VH) / TS));
    vec4 tint(th.tint.x, th.tint.y, th.tint.z, 1.f);
    for (int y = ty0; y <= ty1; y++) for (int x = tx0; x <= tx1; x++) {
        size_t i = (size_t)Dungeon::idx(x, y);
        float sx = x * TS - cam.x + 8.f, sy = y * TS - cam.y + 8.f;
        switch (g.D.kind[i]) {
            case K_FLOOR: tiles.spr(ART.floorT[g.D.variant[i]], sx, sy, tint, false, 0.f, 1.f, vec4(0.f, 0.f, 0.f, 1.0f)); break;
            case K_FACE:  tiles.spr(ART.face[g.D.variant[i]], sx, sy, tint, false, 0.f, 1.f, vec4(0.f, 0.f, 0.f, 0.5f)); break;
            case K_CAP:   tiles.spr(ART.cap[g.D.variant[i]], sx, sy, tint, false, 0.f, 1.f, vec4(0.f, 0.f, 0.f, 0.0f)); break;
            default: break;
        }
    }
    // torches (brackets on the wall faces + animated flames)
    for (const auto& tr : g.D.torches) {
        if (tr.tx < tx0 - 1 || tr.tx > tx1 + 1 || tr.ty < ty0 - 1 || tr.ty > ty1 + 1) continue;
        int f = ((int)(t * 9.f + tr.phase)) & 3;
        float sx = tr.tx * TS - cam.x + 8.f, sy = tr.ty * TS - cam.y + 8.f;
        tiles.spr(ART.torch[f], sx, sy, vec4(1.f, 1.f, 1.f, 1.f), false, 0.f, 1.f, vec4(0.f, 0.f, 0.f, 0.5f));
        R.bEmis.spr(ART.torch[f], sx, sy, vec4(th.torch.x * 1.5f, th.torch.y * 1.5f, th.torch.z * 1.5f, 1.f));
        R.bAdd.spr(ART.soft, sx, sy - 3.f, vec4(th.torch * 0.5f, 0.55f), false, 0.f, 1.2f);
    }
    // closed gates
    for (const Room& rm : g.D.rooms) for (int gi : rm.gates) {
        if (!g.D.closed[(size_t)gi]) continue;
        int x = gi % MAPW, y = gi / MAPW;
        if (x < tx0 - 1 || x > tx1 + 1 || y < ty0 - 1 || y > ty1 + 1) continue;
        float sx = x * TS - cam.x + 8.f, sy = y * TS - cam.y + 8.f;
        int spr = g.D.gateHoriz[(size_t)gi] ? ART.gateV : ART.gateH;
        tiles.spr(spr, sx, sy, vec4(1.f, 1.f, 1.f, 1.f), false, 0.f, 1.f, vec4(0.f, 0.f, 0.f, 1.f));
        R.bEmis.spr(spr, sx, sy, vec4(1.6f, 0.4f, 0.25f, 0.7f + 0.3f * std::sin(t * 6.f + x)));
    }
    // summoning circles (start = blue, boss = red)
    for (const Room& rm : g.D.rooms) {
        if (rm.type != R_START && rm.type != R_BOSS && rm.type != R_TREASURE) continue;
        vec2 c = S(rm.center());
        if (!onScreen(rm.center(), 60.f)) continue;
        vec3 col = rm.type == R_BOSS ? vec3(1.6f, 0.25f, 0.2f) : (rm.type == R_TREASURE ? vec3(1.5f, 1.0f, 0.3f) : vec3(0.3f, 0.8f, 1.5f));
        float a = rm.type == R_BOSS && rm.active ? 0.8f : 0.38f;
        R.bAdd.quad(ART.runeRing, c.x, c.y + 4.f, 60.f, 60.f, t * 0.25f * (rm.type == R_BOSS ? -1.f : 1.f) + 0.001f, false, false, vec4(col, a * (0.7f + 0.3f * std::sin(t * 2.f))));
    }

    // ----------------------------------------------------------- decals ----
    for (const Decal& d : g.decals) {
        if (!onScreen(d.p, 8.f)) continue;
        R.bDecal.quad(ART.dot, d.p.x - cam.x, d.p.y - cam.y, d.size, d.size, 0.f, false, false, vec4(d.col, d.alpha));
    }

    // ----------------------------------------------- entity gathering ------
    std::vector<EntRef> ents;
    for (int i = 0; i < MAX_PLAYERS; i++) { const Player& p = g.players[i]; if (p.active && p.visible && !p.dead) ents.push_back({p.pos.y + 5.f, 0, i}); }
    for (size_t i = 0; i < g.en.size(); i++) ents.push_back({g.en[i].pos.y + g.en[i].r * 0.9f, 1, (int)i});
    for (size_t i = 0; i < g.pickups.size(); i++) if (g.pickups[i].type != PU_SOUL) ents.push_back({g.pickups[i].pos.y + 4.f, 2, (int)i});
    for (size_t i = 0; i < g.props.size(); i++) ents.push_back({g.props[i].pos.y + 6.f, 3, (int)i});
    for (const Room& rm : g.D.rooms) if (rm.type == R_TREASURE) ents.push_back({rm.center().y + 8.f, 4, 0});
    std::sort(ents.begin(), ents.end(), [](const EntRef& a, const EntRef& b) { return a.y < b.y; });

    auto shadowBlob = [&](vec2 foot, float w) {
        R.bDecal.quad(ART.shadow, foot.x - cam.x, foot.y - cam.y, w, w * 0.45f, 0.f, false, false, vec4(1.f, 1.f, 1.f, 0.85f));
    };
    // blob shadows first (drawn into the decal batch, below everything)
    for (const Player& p : g.players) if (p.active && p.visible && !p.dead) shadowBlob(p.pos + vec2(0.f, 5.f), 13.f);
    for (const Enemy& e : g.en) {
        if (e.dying || e.spawn > 0.f) continue;
        shadowBlob(e.pos + vec2(0.f, e.r * 0.8f), e.r * 2.4f + 4.f);
    }
    for (const Prop& p : g.props) shadowBlob(p.pos + vec2(0.f, 5.f), 12.f);

    // --------------------------------------------------------- entities ----
    for (const EntRef& er : ents) {
        if (er.kind == 0) {                                              // player
            const Player& pl = g.players[er.i];
            bool blink = pl.invuln > 0.f && pl.dashT <= 0.f && (((int)(t * 22.f)) & 1);
            const int* pspr = ART.player[pl.slot & 3];
            int spr = pl.moving ? pspr[2 + ((int)(pl.animT * 10.f) & 3)] : pspr[(int)(pl.animT * 4.f) & 1];
            vec2 p = S(pl.pos);
            vec4 col = pl.dashT > 0.f ? vec4(0.6f, 1.2f, 1.6f, 1.f) : vec4(1.f, 1.f, 1.f, 1.f);
            vec4 fx(blink ? 0.8f : 0.f, 0.f, 0.f, 1.f);
            R.bEnt.quad(spr, p.x, p.y + 5.f - 8.f, 16.f, 16.f, 0.f, pl.facingLeft, false, col, fx);
            R.bEmis.quad(spr, p.x, p.y + 5.f - 8.f, 16.f, 16.f, 0.f, pl.facingLeft, false, vec4(1.f, 1.f, 1.f, 1.f));
            // staff
            float ang = std::atan2(pl.aimDir.y, pl.aimDir.x);
            vec2 sp = p + pl.aimDir * 9.f + vec2(0.f, -3.f);
            R.bEnt.quad(ART.staff, sp.x, sp.y, 16.f, 5.f, ang + 0.0001f, false, pl.facingLeft, vec4(1.f, 1.f, 1.f, 1.f), vec4(0.f, 0.f, 0.f, 1.f));
            R.bEmis.quad(ART.staff, sp.x, sp.y, 16.f, 5.f, ang + 0.0001f, false, pl.facingLeft, vec4(1.f, 1.f, 1.f, 1.f + pl.muzzle * 2.f));
            if (pl.muzzle > 0.f) R.bAdd.spr(ART.soft, sp.x + pl.aimDir.x * 8.f, sp.y + pl.aimDir.y * 8.f, vec4(0.4f, 1.1f, 1.8f, pl.muzzle), false, 0.f, 0.7f);
        } else if (er.kind == 1) {                                       // enemies
            const Enemy& e = g.en[(size_t)er.i];
            int spr = 0; float hover = 0.f;
            int f2 = (int)(e.t * 3.f) & 1;
            switch (e.type) {
                case E_SLIME:   spr = ART.slime[e.state == 1 ? 1 : f2]; break;
                case E_SLIME_S: spr = ART.slimeS[e.state == 1 ? 1 : f2]; break;
                case E_BAT:     spr = ART.bat[(int)(e.t * 14.f) & 1]; hover = -7.f + std::sin(e.t * 6.f + e.phase) * 2.f; break;
                case E_ARCHER:  spr = ART.skel[(int)(e.t * 5.f) & 1]; break;
                case E_MAGE:    spr = ART.mage[f2]; hover = -2.f + std::sin(e.t * 4.f) * 1.5f; break;
                case E_BRUTE:   spr = ART.brute[(int)(e.t * 4.f) & 1]; break;
                case E_KING:    spr = ART.king[e.state == 1 ? 1 : f2]; break;
                default:        spr = ART.lich[f2]; hover = -6.f + std::sin(e.t * 2.5f) * 3.f; break;
            }
            const SpriteRect& sr = SR(spr);
            vec2 foot = S(e.pos) + vec2(0.f, e.r * 0.9f);
            float dis = e.dying ? clampf(e.dyingT / 0.38f, 0.f, 1.f) : e.dissolve;
            vec4 col(1.f, 1.f, 1.f, 1.f);
            if (e.slow > 0.f) col = vec4(0.65f, 0.95f, 1.4f, 1.f);
            float flash = e.flash;
            if (e.warn > 0.f) flash = std::max(flash, e.warn * (0.35f + 0.25f * std::sin(t * 30.f)));
            vec4 fx(flash, dis, e.seed, 1.f);
            bool flip = (e.type == E_MAGE || e.type == E_LICH || e.type == E_KING) ? false : e.faceLeft;
            float cy = foot.y + hover - sr.h * 0.5f;
            R.bEnt.quad(spr, foot.x, cy, (float)sr.w, (float)sr.h, 0.f, flip, false, col, fx);
            R.bEmis.quad(spr, foot.x, cy, (float)sr.w, (float)sr.h, 0.f, flip, false, vec4(1.f, 1.f, 1.f, 1.f), vec4(0.f, dis, e.seed, 1.f));
            if (e.flash > 0.05f) R.bAdd.quad(spr, foot.x, cy, (float)sr.w, (float)sr.h, 0.f, flip, false, vec4(1.6f, 1.6f, 1.6f, e.flash * 0.8f));
            if (e.warn > 0.2f && !e.dying) R.bAdd.spr(ART.soft, foot.x, cy, vec4(1.6f, 0.3f, 0.2f, e.warn * 0.7f), false, 0.f, 1.2f + (e.boss ? 1.5f : 0.f));
        } else if (er.kind == 2) {                                       // heart / rune pickups
            const Pickup& p = g.pickups[(size_t)er.i];
            vec2 s = S(p.pos);
            float bob = std::sin(p.t * 4.f) * 2.f;
            if (p.type == PU_HEART) {
                R.bEnt.spr(ART.heart[0], s.x, s.y - 3.f + bob, vec4(1.f, 1.f, 1.f, 1.f));
                R.bEmis.spr(ART.heart[0], s.x, s.y - 3.f + bob, vec4(1.6f, 0.7f, 0.8f, 1.f));
                R.bAdd.spr(ART.soft, s.x, s.y - 3.f + bob, vec4(1.6f, 0.3f, 0.4f, 0.5f), false, 0.f, 0.7f);
            } else {
                R.bEmis.spr(ART.rune, s.x, s.y - 6.f + bob, vec4(1.6f, 1.2f, 2.4f, 1.f), false, 0.f, 1.f + 0.1f * std::sin(p.t * 8.f));
                R.bAdd.spr(ART.soft, s.x, s.y - 6.f + bob, vec4(1.0f, 0.5f, 2.0f, 0.8f), false, 0.f, 1.5f);
                R.bAdd.quad(ART.ring, s.x, s.y - 6.f + bob, 22.f, 22.f, 0.f, false, false, vec4(1.2f, 0.8f, 2.0f, 0.5f + 0.3f * std::sin(p.t * 5.f)));
            }
        } else if (er.kind == 3) {                                       // pots
            const Prop& p = g.props[(size_t)er.i];
            vec2 s = S(p.pos);
            float sh = p.shake > 0.f ? std::sin(t * 60.f) * p.shake * 2.f : 0.f;
            R.bEnt.spr(ART.pot, s.x + sh, s.y - 1.f, vec4(1.f, 1.f, 1.f, 1.f));
        } else {                                                         // pedestal
            for (const Room& rm : g.D.rooms) if (rm.type == R_TREASURE) {
                vec2 s = S(rm.center());
                R.bEnt.spr(ART.pedestal, s.x, s.y, vec4(1.f, 1.f, 1.f, 1.f));
                R.bEmis.spr(ART.pedestal, s.x, s.y, vec4(1.f, 0.6f, 2.0f, 0.8f));
            }
        }
    }

    // dash afterimages
    for (const Ghost& gh : g.ghosts) {
        float a = clampf(gh.life / 0.28f, 0.f, 1.f);
        vec2 p = S(gh.pos);
        R.bAdd.quad(ART.player[gh.slot & 3][2], p.x, p.y - 3.f, 16.f, 16.f, 0.f, gh.left, false, vec4(kPlayerCol[gh.slot & 3] * 0.9f, a * 0.8f));
    }

    // exit portal
    if (g.portalOpen) {
        vec2 c = S(g.D.portalPos);
        float p = 0.8f + 0.2f * std::sin(t * 3.f);
        R.bAdd.spr(ART.softBig, c.x, c.y - 4.f, vec4(0.4f, 0.9f, 1.8f, 0.9f * p), false, 0.f, 2.2f);
        R.bAdd.quad(ART.runeRing, c.x, c.y, 54.f, 54.f, t * 0.9f, false, false, vec4(0.5f, 1.2f, 2.2f, 0.9f));
        R.bAdd.quad(ART.runeRing, c.x, c.y, 34.f, 34.f, -t * 1.4f, false, false, vec4(1.2f, 0.8f, 2.2f, 0.9f));
        R.bAdd.quad(ART.softBig, c.x, c.y - 30.f, 14.f, 80.f, 0.f, false, false, vec4(0.6f, 1.2f, 2.2f, 0.5f));
    }

    // wisps
    for (const Player& wp : g.players) {
        if (!wp.active || wp.dead || g.mode == M_TITLE) continue;
        for (int w = 0; w < wp.st.wisps; w++) {
            vec2 p = S(g.wispPos(wp, w));
            R.bAdd.spr(ART.soft, p.x, p.y, vec4(0.3f, 1.4f, 1.1f, 0.9f), false, 0.f, 0.6f);
            R.bAdd.quad(ART.orb, p.x, p.y, 5.f, 5.f, 0.f, false, false, vec4(1.4f, 2.4f, 2.0f, 1.f));
        }
    }

    // souls (pure emissive wisps)
    for (const Pickup& p : g.pickups) {
        if (p.type != PU_SOUL) continue;
        vec2 s = S(p.pos);
        if (s.x < -8 || s.y < -8 || s.x > VW + 8 || s.y > VH + 8) continue;
        float bob = std::sin(p.t * 5.f) * 1.5f;
        R.bEmis.spr(ART.soul[((int)(p.t * 8.f)) & 3], s.x, s.y - 3.f + bob, vec4(1.f, 1.f, 1.f, 1.f));
        R.bAdd.spr(ART.soft, s.x, s.y - 3.f + bob, vec4(0.3f, 0.8f, 1.4f, 0.6f), false, 0.f, 0.5f);
    }

    // bullets
    int nb = 0;
    for (const Bullet& b : g.bullets) {
        vec2 s = S(b.pos);
        if (s.x < -10 || s.y < -10 || s.x > VW + 10 || s.y > VH + 10) continue;
        float ang = std::atan2(b.vel.y, b.vel.x);
        float ageK = b.friendly ? 1.f : clampf((5.f - b.life) * 5.f, 0.12f, 1.f);
        if (b.friendly) {
            R.bAdd.quad(ART.orb, s.x, s.y, 11.f, 6.f, ang + 0.0001f, false, false, vec4(b.col * 1.8f, 1.f));
            R.bAdd.spr(ART.soft, s.x, s.y, vec4(b.col * 1.0f, 0.38f), false, 0.f, 0.5f);
        } else if (b.kind == BK_ARROW) {
            R.bAdd.quad(ART.arrow, s.x, s.y, 12.f, 5.f, ang + 0.0001f, false, false, vec4(b.col * 2.0f, 1.f));
            R.bAdd.spr(ART.soft, s.x, s.y, vec4(b.col, 0.22f * ageK), false, 0.f, 0.45f);
        } else {
            float pulse = 1.f + 0.15f * std::sin(t * 18.f + (float)nb);
            R.bAdd.quad(ART.orb, s.x, s.y, 8.f * pulse, 8.f * pulse, 0.f, false, false, vec4(b.col * 1.6f, 1.f));
            R.bAdd.spr(ART.soft, s.x, s.y, vec4(b.col, 0.3f * ageK), false, 0.f, 0.55f);
        }
        nb++;
    }

    // particles
    for (const Part& q : g.parts) {
        vec2 s = S(q.p);
        if (s.x < -10 || s.y < -10 || s.x > VW + 10 || s.y > VH + 10) continue;
        float k = clampf(q.life / q.maxLife, 0.f, 1.f);
        switch (q.kind) {
            case PK_SPARK: { float sz = std::max(1.f, std::floor(q.size * (0.4f + 0.6f * k) + 0.5f)); R.bAdd.quad(ART.dot, s.x, s.y, sz, sz, 0.f, false, false, vec4(q.col, k)); } break;
            case PK_EMBER: R.bAdd.quad(ART.dot, s.x, s.y, 1.f, 1.f, 0.f, false, false, vec4(q.col, k * (0.55f + 0.45f * std::sin(t * 22.f + q.seed)))); break;
            case PK_GLOW:  R.bAdd.spr(ART.soft, s.x, s.y, vec4(q.col, k), false, 0.f, q.size / 32.f); break;
            case PK_SMOKE: R.bFx.quad(ART.soft, s.x, s.y, q.size * 2.f, q.size * 2.f, 0.f, false, false, vec4(q.col, q.alpha * k)); break;
            default:       R.bFx.quad(ART.dot, s.x, s.y, q.size, q.size, 0.f, false, false, vec4(q.col, std::min(1.f, k * 3.f))); break;
        }
    }
    // lightning
    for (const Zap& z : g.zaps) {
        vec2 a = S(z.a), b = S(z.b), prev = a;
        vec2 d = b - a; float l = len2(d); vec2 n = perp2(norm2(d));
        int segs = std::max(3, (int)(l / 7.f));
        int bucket = (int)(t * 40.f);
        float k = clampf(z.life / 0.2f, 0.f, 1.f);
        for (int i = 1; i <= segs; i++) {
            vec2 p = a + d * ((float)i / segs);
            if (i < segs) p += n * ((hashf(z.seed + i, bucket, 3) - 0.5f) * 11.f);
            R.bAdd.seg(prev, p, 1.6f, vec4(z.col * 2.4f, k));
            R.bAdd.seg(prev, p, 4.f, vec4(z.col * 0.7f, k * 0.5f));
            prev = p;
        }
    }
    // explosion halos
    for (const Boom& b : g.booms) {
        float k = clampf(b.life / b.maxLife, 0.f, 1.f);
        vec2 s = S(b.pos);
        R.bAdd.spr(ART.softBig, s.x, s.y, vec4(b.col * 1.0f, k * 0.32f), false, 0.f, b.radius / 64.f * 1.1f * (1.4f - 0.4f * k));
    }

    // ------------------------------------------------------------ lights ---
    std::vector<LightRec>& L = fp.lights;
    L.clear();
    {
        float flick = 0.93f + 0.07f * std::sin(t * 9.f) + 0.04f * std::sin(t * 23.f);
        const Player& lp0 = g.L();
        if ((lp0.active && lp0.visible && !lp0.dead) || g.mode == M_TITLE)
            L.push_back({lp0.pos + vec2(0.f, -4.f), 150.f * lp0.st.light, vec3(1.35f, 0.98f, 0.58f) * flick, 1.f});
        for (int i = 0; i < MAX_PLAYERS; i++) {
            const Player& op = g.players[i];
            if (i == g.me || !op.active || !op.visible || op.dead) continue;
            vec3 warm = vec3(1.35f, 0.98f, 0.58f) * 0.5f + kPlayerCol[i] * 0.45f;
            L.push_back({op.pos + vec2(0.f, -4.f), 130.f * op.st.light, warm * flick, 1.f});
        }
    }
    if (g.mode == M_TITLE) L.push_back({g.aimWorld, 110.f, vec3(1.0f, 0.75f, 0.45f), 1.f});
    for (const auto& tr : g.D.torches) {
        vec2 lp(tr.tx * TS + 8.f, (tr.ty + 1) * TS + 3.f);
        if (!onScreen(lp, 125.f)) continue;
        float fl = 0.88f + 0.12f * std::sin(t * 13.f + tr.phase) + 0.08f * std::sin(t * 31.f + tr.phase * 2.f);
        L.push_back({lp, 120.f, th.torch * (1.05f * fl), 1.f});
    }
    for (const Boom& b : g.booms) {
        float k = clampf(b.life / b.maxLife, 0.f, 1.f);
        if (onScreen(b.pos, b.radius)) L.push_back({b.pos, b.radius * (0.6f + 0.4f * k), b.col * (1.0f * k), 1.f});
    }
    int nbl = 0;
    for (const Bullet& b : g.bullets) {
        if (!onScreen(b.pos, 50.f)) continue;
        if (!b.friendly && (b.life > 4.88f || ((nbl++ & 1) && g.bullets.size() > 20))) continue;
        L.push_back({b.pos, b.friendly ? 46.f : 32.f, b.col * (b.friendly ? 0.75f : 0.55f), 0.f});
    }
    int ns = 0;
    for (const Pickup& p : g.pickups) {
        if (!onScreen(p.pos, 70.f)) continue;
        if (p.type == PU_RUNE) L.push_back({p.pos + vec2(0.f, -6.f), 78.f, vec3(1.0f, 0.55f, 1.8f), 1.f});
        else if (p.type == PU_SOUL && ns < 6) { ns++; L.push_back({p.pos, 28.f, vec3(0.3f, 0.8f, 1.3f), 0.f}); }
        else if (p.type == PU_HEART) L.push_back({p.pos, 34.f, vec3(1.2f, 0.25f, 0.35f), 0.f});
    }
    if (g.portalOpen && onScreen(g.D.portalPos, 150.f)) L.push_back({g.D.portalPos + vec2(0.f, -6.f), 140.f, vec3(0.5f, 1.0f, 1.8f), 1.f});
    for (const Enemy& e : g.en) {
        if (!onScreen(e.pos, 90.f)) continue;
        if (e.spawn > 0.f && !e.dying) L.push_back({e.pos, 46.f, vec3(0.9f, 0.3f, 1.2f) * (1.f - e.spawn / 2.f > 0.f ? 1.f : 0.5f), 0.f});
        else if (e.dying) continue;
        else if (e.type == E_KING) L.push_back({e.pos, 90.f, vec3(0.22f, 0.7f, 0.36f), 1.f});
        else if (e.type == E_LICH) L.push_back({e.pos, 96.f, vec3(0.22f, 0.7f, 0.64f), 1.f});
        else if (e.type == E_MAGE) L.push_back({e.pos, 46.f, vec3(0.8f, 0.3f, 1.0f), 0.f});
        else if (e.type == E_BRUTE) L.push_back({e.pos, 40.f, vec3(1.0f, 0.45f, 0.15f) * (0.5f + e.warn), 0.f});
    }
    for (const Player& wp : g.players) {
        if (!wp.active || wp.dead || g.mode == M_TITLE) continue;
        for (int w = 0; w < wp.st.wisps; w++) L.push_back({g.wispPos(wp, w), 52.f, vec3(0.3f, 1.2f, 1.0f), 0.f});
    }
    for (const Zap& z : g.zaps) L.push_back({(z.a + z.b) * 0.5f, 70.f, z.col * 1.5f * clampf(z.life / 0.2f, 0.f, 1.f), 0.f});
    for (const Ghost& gh : g.ghosts) if (&gh == &g.ghosts.back()) L.push_back({gh.pos, 40.f, vec3(0.2f, 0.7f, 1.2f), 0.f});
    if (L.size() > (size_t)MAX_LIGHTS) {
        vec2 c = cam + vec2(VW * 0.5f, VH * 0.5f);
        std::stable_sort(L.begin() + 1, L.end(), [&](const LightRec& a, const LightRec& b) { return len2(a.p - c) < len2(b.p - c); });
        L.resize((size_t)MAX_LIGHTS);
    }

    // ------------------------------------------------------- frame params --
    fp.cam = cam;
    fp.ambient = th.ambient * (g.mode == M_TITLE ? 1.15f : 1.f);
    fp.tint = vec3(1.0f, 1.0f, 1.0f) * 1.0f + (th.tint - vec3(1.f, 1.f, 1.f)) * 0.25f;
    fp.time = t;
    fp.aberr = g.redFlash * 0.006f + g.trauma * g.trauma * 0.0045f;
    fp.flash = g.redFlash * 0.7f;
    float deadDim = g.mode == M_DEAD ? (1.f - 0.5f * smooth01(g.deadT / 2.f)) : 1.f;
    fp.fade = clampf(g.fade, 0.f, 1.f) * deadDim;
    fp.bloom = 1.0f + 0.35f * g.redFlash;
    for (int i = 0; i < 4; i++) fp.sw[i] = vec4(0.f, 0.f, 0.f, 0.f);
    int wi = 0;
    for (int i = (int)g.waves.size() - 1; i >= 0 && wi < 4; i--, wi++) {
        const Wave& w = g.waves[(size_t)i];
        float k = clampf(w.age / w.dur, 0.f, 1.f);
        vec2 sp = w.pos - cam;
        fp.sw[wi] = vec4(sp.x / VW, 1.f - sp.y / VH, w.maxR * (1.f - (1.f - k) * (1.f - k)), w.strength * (1.f - k));
    }

    // ================================================================ HUD ===
    Batch& H = R.bHud;
    // damage numbers
    for (const FloatText& ft : g.texts) {
        vec2 s = S(ft.p);
        float a = clampf(ft.life / ft.maxLife * 2.f, 0.f, 1.f);
        drawText(H, ft.s, s.x, s.y, ft.scale, ft.col, a, 1);
    }
    const bool inGame = (g.mode == M_PLAY || g.mode == M_PAUSE || g.mode == M_BOON || g.mode == M_DEAD);
    if (inGame) {
        const Player& pl = g.L();
        // hearts
        int nh = pl.maxHp / 2;
        for (int i = 0; i < nh; i++) {
            int kind = pl.hp >= 2 * i + 2 ? 0 : (pl.hp == 2 * i + 1 ? 1 : 2);
            float pulse = (pl.hp <= 2 && kind != 2) ? 1.f + 0.4f * std::sin(t * 9.f) : 1.f;
            H.spr(ART.heart[kind], 13.f + i * 11.f, 12.f, vec4(1.0f * pulse, 0.95f, 0.95f, 1.f));
        }
        // dash pips
        for (int i = 0; i < pl.st.maxDash; i++) {
            bool full = i < pl.dashCharges;
            float frac = (i == pl.dashCharges && pl.dashCharges < pl.st.maxDash) ? clampf(pl.dashRecharge / pl.st.dashCd, 0.f, 1.f) : 0.f;
            float x = 10.f + i * 12.f, y = 22.f;
            hudRect(H, x, y, 9, 4, vec3(0.05f, 0.1f, 0.18f), 0.8f);
            if (full) hudRect(H, x, y, 9, 4, vec3(0.3f, 1.5f, 2.4f), 1.f);
            else if (frac > 0.f) hudRect(H, x, y, 9.f * frac, 4, vec3(0.2f, 0.8f, 1.4f), 1.f);
        }
        H.spr(ART.soul[((int)(t * 8.f)) & 3], 13.f, 36.f, vec4(1.5f, 1.5f, 1.5f, 1.f));
        drawText(H, "x" + std::to_string(g.souls), 20.f, 32.f, 1, vec3(1.0f, 1.9f, 2.6f));
        drawText(H, "DEPTH " + std::to_string(g.floorNo), 8.f, 44.f, 1, vec3(2.2f, 1.7f, 1.0f));
        char sb[32]; std::snprintf(sb, sizeof(sb), "SCORE %d", g.score());
        drawText(H, sb, 8.f, 54.f, 1, vec3(1.5f, 1.5f, 1.8f));

        // boons
        int k = 0;
        for (int i = 0; i < B_COUNT; i++) {
            if (!pl.boon[i]) continue;
            float x = 14.f + k * 20.f, y = VH - 16.f;
            H.spr(ART.icon[i], x, y, vec4(kBoons[i].col * 1.5f, 1.f));
            if (pl.boon[i] > 1) drawText(H, std::to_string(pl.boon[i]), x + 7.f, y + 3.f, 1, vec3(2.4f, 2.4f, 2.4f));
            k++;
        }
        // boss bar
        for (const Enemy& e : g.en) {
            if (!e.boss || e.dying || e.spawn > 0.f) continue;
            float w = 220.f, x = (VW - w) * 0.5f, y = 16.f;
            float f = clampf(e.hp / e.maxHp, 0.f, 1.f);
            drawText(H, kEDef[e.type].name, VW * 0.5f, 4.f, 1, vec3(2.4f, 1.0f, 0.8f), 1.f, 1);
            hudBox(H, x - 1, y - 1, w + 2, 8, vec3(0.5f, 0.2f, 0.2f), vec3(0.04f, 0.02f, 0.03f), 0.85f);
            hudRect(H, x, y, w * f, 6, vec3(2.0f, 0.25f, 0.2f), 1.f);
            hudRect(H, x, y, w * f, 2, vec3(2.8f, 0.9f, 0.6f), 0.8f);
            break;
        }
        // minimap
        float mx = VW - MAPW - 6.f, my = 6.f;
        hudBox(R.bHudBack, mx - 2, my - 2, MAPW + 4, MAPH + 4, vec3(0.25f, 0.3f, 0.5f), vec3(0.02f, 0.03f, 0.06f), 0.6f);
        R.bMini.rawQuad(mx, my, mx + MAPW, my + MAPH, 0.f, 0.f, 1.f, 1.f, vec4(1.f, 1.f, 1.f, 1.f));
        for (int i = 0; i < MAX_PLAYERS; i++) {
            const Player& op = g.players[i];
            if (!op.active || op.dead) continue;
            if (i == g.me && !(((int)(t * 3.f)) & 1)) continue;
            hudRect(H, mx + op.pos.x / TS - 1.f, my + op.pos.y / TS - 1.f, 3, 3, i == g.me ? vec3(2.4f, 2.4f, 0.8f) : kPlayerCol[i] * 1.6f, 1.f);
        }
        // teammates: name tag over their head + a small health row
        {
            int row = 0;
            for (int i = 0; i < MAX_PLAYERS; i++) {
                const Player& op = g.players[i];
                if (i == g.me || !op.active) continue;
                float ty = 66.f + row * 12.f;
                drawText(H, "P" + std::to_string(i + 1), 8.f, ty, 1, kPlayerCol[i] * 1.2f);
                for (int h = 0; h < op.maxHp / 2; h++) {
                    vec3 hc = op.dead ? vec3(0.2f, 0.2f, 0.25f) : (op.hp >= 2 * h + 2 ? vec3(1.8f, 0.3f, 0.4f) : (op.hp == 2 * h + 1 ? vec3(1.6f, 0.8f, 0.3f) : vec3(0.25f, 0.1f, 0.15f)));
                    hudRect(H, 24.f + h * 6.f, ty + 1.f, 5, 5, hc, 1.f);
                }
                if (op.dead) drawText(H, "DOWN", 24.f + (op.maxHp / 2) * 6.f + 4.f, ty, 1, vec3(2.2f, 0.4f, 0.4f));
                else if (op.choosing) drawText(H, "CHOOSING", 24.f + (op.maxHp / 2) * 6.f + 4.f, ty, 1, vec3(1.6f, 1.2f, 2.2f));
                row++;
                if (op.visible && !op.dead) {
                    vec2 sp = S(op.pos);
                    drawText(H, "P" + std::to_string(i + 1), sp.x, sp.y - 20.f, 1, kPlayerCol[i] * 1.3f, 0.9f, 1);
                }
            }
            if (g.role == NR_HOST) {
                static const std::string ip = netLocalIp();
                drawText(H, "HOSTING " + ip + ":" + std::to_string(NET_PORT) + "  PLAYERS " + std::to_string(g.activeCount()) + "/4", VW * 0.5f, VH - 10.f, 1, vec3(1.2f, 1.6f, 2.2f), 0.8f, 1);
            } else if (g.role == NR_CLIENT) {
                drawText(H, "CO-OP - YOU ARE P" + std::to_string(g.me + 1), VW * 0.5f, VH - 10.f, 1, kPlayerCol[g.me] * 1.2f, 0.8f, 1);
            }
            if (pl.dead && g.mode != M_DEAD) {
                hudRect(H, 0, 108, VW, 36, vec3(0.1f, 0.f, 0.02f), 0.5f);
                drawText(H, "YOU ARE DOWN", VW * 0.5f, 116.f, 2, vec3(2.0f, 0.4f, 0.35f), 1.f, 1);
                drawText(H, "CLEARING THE ROOM REVIVES YOU", VW * 0.5f, 134.f, 1, vec3(1.6f, 1.6f, 2.0f), 1.f, 1);
            }
        }
        // banner
        if (g.bannerT > 0.f && g.mode != M_BOON) {
            float a = clampf(std::min(g.bannerT * 3.f, (g.bannerDur - g.bannerT) * 5.f), 0.f, 1.f);
            float slide = (1.f - a) * 6.f;
            drawText(H, g.banner, VW * 0.5f, 62.f + slide, 3, g.bannerCol * 1.25f, a, 1);
            if (!g.bannerSub.empty()) drawText(H, g.bannerSub, VW * 0.5f, 90.f + slide, 1, vec3(1.8f, 1.8f, 2.0f), a, 1);
        }
        // crosshair
        if ((g.mode == M_PLAY || g.mode == M_BOON) && !pl.dead) {
            R.bAdd.spr(ART.crosshair, g.aimScreen.x, g.aimScreen.y, vec4(1.6f, 1.9f, 2.2f, 1.f));
            H.spr(ART.crosshair, g.aimScreen.x, g.aimScreen.y, vec4(1.f, 1.f, 1.f, 0.9f));
        }
    }

    // ------------------------------------------------ boon selection menu --
    if (g.mode == M_BOON) {
        hudRect(H, 0, 0, VW, VH, vec3(0.f, 0.f, 0.02f), 0.72f);
        drawText(H, "CHOOSE A BOON", VW * 0.5f, 26.f, 3, vec3(1.5f, 1.0f, 1.9f), 1.f, 1);
        const Player& mp = g.L();
        for (int i = 0; i < mp.boonChoices; i++) {
            int b = mp.boonChoice[i];
            vec2 c = g.cardPos(i), sz = Game::cardSize();
            bool sel = (i == g.boonSel);
            float lift = sel ? -3.f : 0.f;
            vec3 bc = kBoons[b].col;
            hudBox(H, c.x, c.y + lift, sz.x, sz.y, bc * (sel ? 1.8f : 0.7f), vec3(0.04f, 0.04f, 0.09f), 0.95f);
            if (sel) hudRect(H, c.x + 1, c.y + lift + 1, sz.x - 2, 3, bc * 1.4f, 0.55f);
            H.quad(ART.icon[b], c.x + sz.x * 0.5f, c.y + lift + 32.f, 32.f, 32.f, 0.f, false, false, vec4(bc * 1.8f, 1.f));
            R.bAdd.spr(ART.softBig, c.x + sz.x * 0.5f, c.y + lift + 32.f, vec4(bc, sel ? 0.55f : 0.25f), false, 0.f, 1.1f);
            drawText(H, kBoons[b].name, c.x + sz.x * 0.5f, c.y + lift + 60.f, 1, bc * 2.0f + vec3(0.4f, 0.4f, 0.4f), 1.f, 1);
            drawText(H, kBoons[b].l1, c.x + sz.x * 0.5f, c.y + lift + 82.f, 1, vec3(1.7f, 1.7f, 1.9f), 1.f, 1);
            drawText(H, kBoons[b].l2, c.x + sz.x * 0.5f, c.y + lift + 94.f, 1, vec3(1.7f, 1.7f, 1.9f), 1.f, 1);
            char buf[32]; std::snprintf(buf, sizeof(buf), "OWNED %d/%d", mp.boon[b], kBoons[b].maxStacks);
            drawText(H, buf, c.x + sz.x * 0.5f, c.y + lift + 118.f, 1, vec3(1.0f, 1.0f, 1.3f), 1.f, 1);
            drawText(H, "[" + std::to_string(i + 1) + "]", c.x + sz.x * 0.5f, c.y + lift + 134.f, 1, vec3(2.2f, 2.0f, 1.0f), 1.f, 1);
        }
        drawText(H, "CLICK OR PRESS 1 2 3", VW * 0.5f, 236.f, 1, vec3(1.4f, 1.4f, 1.8f), 0.8f + 0.2f * std::sin(t * 5.f), 1);
    }

    // ---------------------------------------------------------------- pause --
    if (g.mode == M_PAUSE) {
        hudRect(H, 0, 0, VW, VH, vec3(0.f, 0.f, 0.02f), 0.6f);
        drawText(H, "PAUSED", VW * 0.5f, 100.f, 4, vec3(1.4f, 1.4f, 1.8f), 1.f, 1);
        drawText(H, "ESC - RESUME      Q - QUIT", VW * 0.5f, 140.f, 1, vec3(1.8f, 1.8f, 2.2f), 1.f, 1);
    }

    // ---------------------------------------------------------------- title --
    if (g.mode == M_TITLE) {
        float fl = 0.9f + 0.1f * std::sin(t * 7.f) + 0.05f * std::sin(t * 19.f);
        hudRect(H, 0, 30, VW, 92, vec3(0.f, 0.f, 0.02f), 0.55f);
        drawText(H, "EMBERDEEP", VW * 0.5f, 46.f, 8, vec3(1.55f, 0.66f, 0.2f) * fl, 1.f, 1);
        drawText(H, "A LANTERN IN THE DARK", VW * 0.5f, 112.f, 1, vec3(1.8f, 1.5f, 2.0f), 1.f, 1);
        if (g.role == NR_CLIENT) {
            drawText(H, g.netStatus.empty() ? std::string("CONNECTING...") : g.netStatus, VW * 0.5f, 170.f, 1, vec3(2.0f, 2.2f, 2.8f), 0.6f + 0.4f * std::sin(t * 4.f), 1);
            drawText(H, "ESC - CANCEL", VW * 0.5f, 186.f, 1, vec3(1.1f, 1.2f, 1.6f), 0.9f, 1);
        } else if (g.joinEditing) {
            hudRect(H, 100, 150, 280, 58, vec3(0.02f, 0.02f, 0.06f), 0.85f);
            drawText(H, "HOST ADDRESS  (IP OR IP:PORT)", VW * 0.5f, 158.f, 1, vec3(1.8f, 1.8f, 2.4f), 1.f, 1);
            drawText(H, g.joinText + (((int)(t * 2.f)) & 1 ? "_" : " "), VW * 0.5f, 176.f, 2, vec3(2.4f, 2.0f, 1.2f), 1.f, 1);
            drawText(H, "ENTER - CONNECT    ESC - CANCEL", VW * 0.5f, 196.f, 1, vec3(1.2f, 1.3f, 1.7f), 1.f, 1);
        } else {
            drawText(H, "SPACE / CLICK - SOLO DESCENT", VW * 0.5f, 162.f, 1, vec3(2.4f, 2.4f, 2.8f), 0.55f + 0.45f * std::sin(t * 4.f), 1);
            drawText(H, "H - HOST CO-OP      J - JOIN A FRIEND", VW * 0.5f, 180.f, 1, vec3(1.6f, 2.0f, 2.8f), 0.9f, 1);
            if (!g.netStatus.empty()) drawText(H, g.netStatus, VW * 0.5f, 196.f, 1, vec3(2.4f, 1.2f, 0.9f), 1.f, 1);
        }
        drawText(H, "WASD MOVE   MOUSE AIM + CAST   SPACE DASH   F11 FULLSCREEN", VW * 0.5f, 214.f, 1, vec3(1.1f, 1.2f, 1.6f), 0.9f, 1);
        if (g.best > 0) drawText(H, "BEST SCORE " + std::to_string(g.best), VW * 0.5f, 232.f, 1, vec3(1.6f, 2.0f, 2.6f), 1.f, 1);
        R.bAdd.spr(ART.crosshair, g.aimScreen.x, g.aimScreen.y, vec4(1.6f, 1.9f, 2.2f, 1.f));
        H.spr(ART.crosshair, g.aimScreen.x, g.aimScreen.y, vec4(1.f, 1.f, 1.f, 0.9f));
    }

    // ----------------------------------------------------------------- death --
    if (g.mode == M_DEAD && g.deadT > 0.8f) {
        float a = clampf((g.deadT - 0.8f) * 1.5f, 0.f, 1.f);
        hudRect(H, 0, 0, VW, VH, vec3(0.15f, 0.0f, 0.02f), 0.55f * a);
        drawText(H, "YOU HAVE FALLEN", VW * 0.5f, 62.f, 4, vec3(2.3f, 0.26f, 0.2f), a, 1);
        char buf[64];
        std::snprintf(buf, sizeof(buf), "DEPTH %d    KILLS %d    SOULS %d", g.floorNo, g.kills, g.souls);
        drawText(H, buf, VW * 0.5f, 112.f, 1, vec3(2.0f, 1.9f, 2.2f), a, 1);
        std::snprintf(buf, sizeof(buf), "SCORE %d", g.score());
        drawText(H, buf, VW * 0.5f, 132.f, 3, vec3(2.2f, 1.5f, 0.45f), a, 1);
        if (g.newBest) drawText(H, "NEW BEST!", VW * 0.5f, 164.f, 2, vec3(1.2f, 3.0f, 2.2f), a * (0.6f + 0.4f * std::sin(t * 8.f)), 1);
        else { std::snprintf(buf, sizeof(buf), "BEST %d", g.best); drawText(H, buf, VW * 0.5f, 164.f, 1, vec3(1.6f, 1.8f, 2.4f), a, 1); }
        if (g.deadT > 1.8f) drawText(H, g.role == NR_CLIENT ? "WAITING FOR THE HOST TO RESTART" : "PRESS SPACE TO TRY AGAIN", VW * 0.5f, 206.f, 1, vec3(2.4f, 2.4f, 2.8f), 0.55f + 0.45f * std::sin(t * 4.f), 1);
    }
}

// ============================================================================
//  main
// ============================================================================
static std::string gTyped;
static void charCallback(GLFWwindow*, unsigned int c) { if (c >= 32 && c < 127) gTyped.push_back((char)c); }

int main(int argc, char** argv) {
    if (!glfwInit()) { std::fprintf(stderr, "Failed to init GLFW\n"); return 1; }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 3);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
#ifdef __APPLE__
    glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GL_TRUE);
#endif
    GLFWwindow* win = glfwCreateWindow(1280, 720, "EMBERDEEP", nullptr, nullptr);
    if (!win) { std::fprintf(stderr, "Failed to create window\n"); glfwTerminate(); return 1; }
    glfwMakeContextCurrent(win);
    glfwSwapInterval(1);
#ifdef GLAD_GL_H_      // glad 2.x
    if (!gladLoadGL((GLADloadfunc)glfwGetProcAddress)) {
#else                  // glad 1.x (vcpkg default)
    if (!gladLoadGLLoader((GLADloadproc)glfwGetProcAddress)) {
#endif
        std::fprintf(stderr, "Failed to load OpenGL\n");
        return 1;
    }
    std::printf("OpenGL %s | %s\n", (const char*)glGetString(GL_VERSION), (const char*)glGetString(GL_RENDERER));
    glfwSetInputMode(win, GLFW_CURSOR, GLFW_CURSOR_HIDDEN);
    glfwSetCharCallback(win, charCallback);

    buildArt();
    Renderer R;
    R.init();
    Game g;
    // command line:   emberdeep host        |        emberdeep join 192.168.1.20[:7777]
    if (argc >= 2 && std::string(argv[1]) == "host") g.startHost();
    else if (argc >= 3 && std::string(argv[1]) == "join") g.startJoin(argv[2]);
    int lastGen = -1;
    FrameParams fp;
    std::vector<uint8_t> mini;

    bool pH = false, pJ = false, pBack = false;
    bool pF11 = false, fullscreen = false;
    int savedX = 100, savedY = 100, savedW = 1280, savedH = 720;
    bool pShift = false, pSpace = false, pClick = false, pRight = false, pEsc = false, pEnter = false, pQ = false;
    bool pK[3] = {false, false, false}, pL = false, pR = false;
    double last = glfwGetTime();

    while (!glfwWindowShouldClose(win)) {
        glfwPollEvents();
        int fbW = 0, fbH = 0, winW = 0, winH = 0;
        glfwGetFramebufferSize(win, &fbW, &fbH);
        glfwGetWindowSize(win, &winW, &winH);
        if (fbW <= 0 || fbH <= 0 || winW <= 0 || winH <= 0) { glfwWaitEventsTimeout(0.1); last = glfwGetTime(); continue; }

        double now = glfwGetTime();
        float dt = (float)std::min(now - last, 0.05);
        last = now;

        auto key = [&](int k) { return glfwGetKey(win, k) == GLFW_PRESS; };
        Input in;
        in.move.x = ((key(GLFW_KEY_D) || key(GLFW_KEY_RIGHT)) ? 1.f : 0.f) - ((key(GLFW_KEY_A) || key(GLFW_KEY_LEFT)) ? 1.f : 0.f);
        in.move.y = ((key(GLFW_KEY_S) || key(GLFW_KEY_DOWN)) ? 1.f : 0.f) - ((key(GLFW_KEY_W) || key(GLFW_KEY_UP)) ? 1.f : 0.f);

        double mx = 0.0, my = 0.0;
        glfwGetCursorPos(win, &mx, &my);
        float sx = (float)fbW / (float)winW, sy = (float)fbH / (float)winH;
        float scale = std::min((float)fbW / VW, (float)fbH / VH);
        float offX = ((float)fbW - VW * scale) * 0.5f, offY = ((float)fbH - VH * scale) * 0.5f;
        in.aim = vec2(clampf(((float)mx * sx - offX) / scale, 0.f, (float)VW - 1.f), clampf(((float)my * sy - offY) / scale, 0.f, (float)VH - 1.f));

        bool click = glfwGetMouseButton(win, GLFW_MOUSE_BUTTON_LEFT) == GLFW_PRESS;
        bool right = glfwGetMouseButton(win, GLFW_MOUSE_BUTTON_RIGHT) == GLFW_PRESS;
        bool space = key(GLFW_KEY_SPACE);
        bool shift = key(GLFW_KEY_LEFT_SHIFT) || key(GLFW_KEY_RIGHT_SHIFT);
        bool esc = key(GLFW_KEY_ESCAPE), enter = key(GLFW_KEY_ENTER), q = key(GLFW_KEY_Q);
        bool k1 = key(GLFW_KEY_1), k2 = key(GLFW_KEY_2), k3 = key(GLFW_KEY_3);
        bool left = key(GLFW_KEY_LEFT) || key(GLFW_KEY_A), rgt = key(GLFW_KEY_RIGHT) || key(GLFW_KEY_D);

        in.fire = click;
        in.click = click && !pClick;
        in.dash = (space && !pSpace) || (right && !pRight) || (shift && !pShift);
        in.start = (space && !pSpace);
        in.pause = esc && !pEsc;
        bool kH = key(GLFW_KEY_H), kJ = key(GLFW_KEY_J), kBack = key(GLFW_KEY_BACKSPACE);
        in.hostKey = kH && !pH; in.joinKey = kJ && !pJ; in.backspace = kBack && !pBack; in.enter = enter && !pEnter;
        pH = kH; pJ = kJ; pBack = kBack;
        in.typed = gTyped; gTyped.clear();
        in.confirm = (enter && !pEnter) || (space && !pSpace);
        if (k1 && !pK[0]) in.pick = 0;
        if (k2 && !pK[1]) in.pick = 1;
        if (k3 && !pK[2]) in.pick = 2;
        if (left && !pL) in.menuMove = -1;
        if (rgt && !pR) in.menuMove = 1;
        if (q && !pQ && g.mode == M_PAUSE) glfwSetWindowShouldClose(win, GLFW_TRUE);
        if (in.pause && g.mode == M_TITLE && g.role == NR_SOLO && !g.joinEditing) glfwSetWindowShouldClose(win, GLFW_TRUE);
        bool f11 = key(GLFW_KEY_F11);
        if (f11 && !pF11) {                                       // fullscreen toggle
            if (!fullscreen) {
                glfwGetWindowPos(win, &savedX, &savedY);
                glfwGetWindowSize(win, &savedW, &savedH);
                GLFWmonitor* mon = glfwGetPrimaryMonitor();
                const GLFWvidmode* vm = mon ? glfwGetVideoMode(mon) : nullptr;
                if (vm) { glfwSetWindowMonitor(win, mon, 0, 0, vm->width, vm->height, vm->refreshRate); fullscreen = true; }
            } else {
                glfwSetWindowMonitor(win, nullptr, savedX, savedY, savedW, savedH, 0);
                fullscreen = false;
            }
            glfwSwapInterval(1);
        }
        pF11 = f11;
        pShift = shift; pSpace = space; pClick = click; pRight = right; pEsc = esc; pEnter = enter; pQ = q;
        pK[0] = k1; pK[1] = k2; pK[2] = k3; pL = left; pR = rgt;

        g.update(dt, in);

        if (g.D.gen != lastGen) { R.uploadSdf(g.D.sdf); lastGen = g.D.gen; }
        buildFrame(R, g, fp, nullptr, fbW, fbH);
        buildMinimap(g, mini);
        R.uploadMini(mini);
        R.render(fp, fbW, fbH);
        glfwSwapBuffers(win);
    }
    glfwDestroyWindow(win);
    glfwTerminate();
    return 0;
}
