// zgen.cpp -- solver for the zone game G_K exactly as checked by C4W5/Cert/ZoneC.lean; emits a strategy-closed certificate.
// usage: zgen K moves [maxk]     output lines: c0 c1 c2 c3 c4 l0 l1 l2 l3 l4 rep   (columns in bijective base 2, labels 0/1/2)
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <unordered_map>
#include <vector>
#include <string>
typedef unsigned __int128 u128; typedef uint32_t u32;
static int K;
struct P { u32 c[5]; uint8_t l[5]; };
static inline int ht(u32 n) { return 31 - __builtin_clz(n + 1); }
static inline int cell(const P& p, int x, int y) { if (x < 0 || x > 4 || y < 0) return 0; int L = ht(p.c[x]); if (y >= L || y >= K) return 0; return (((p.c[x] + 1) >> (L - 1 - y)) & 1) ? 1 : 2; }
static bool win(const P& p, int c, int who) { int r = ht(p.c[c]) - 1; static const int D[4][2] = {{0,1},{1,0},{1,1},{1,-1}};
  for (auto& d : D) { int n = 1; for (int s = -1; s <= 1; s += 2) { int x = c + s*d[0], y = r + s*d[1]; while (cell(p, x, y) == who) { n++; x += s*d[0]; y += s*d[1]; } } if (n >= 4) return true; }
  return false; }
static inline P push(P p, int c, int black) { p.c[c] = 2 * p.c[c] + 1 + black; return p; }
static inline u128 key(const P& p) { u128 k = 0; for (int i = 0; i < 5; i++) k = (k << 20) | p.c[i]; for (int i = 0; i < 5; i++) k = (k << 2) | p.l[i]; return k; }
struct KH { size_t operator()(u128 k) const { uint64_t a = (uint64_t)k ^ ((uint64_t)(k >> 64) * 0x9E3779B97F4A7C15ULL); a ^= a >> 31; a *= 0xff51afd7ed558ccdULL; a ^= a >> 33; return a; } };
struct M { int8_t fail, hold; int rep; };
static std::unordered_map<u128, M, KH> memo;
static const int ORD[5] = {2, 1, 3, 0, 4};
static bool solve(const P& p, int k);
// Black's non-winning reply e in (p,l): the resulting state, or false if not allowed
static bool outState(const P& p, int e, P& q) { q = p;
  if (p.l[e] == 0) { if (ht(p.c[e]) < K) q = push(p, e, 1); else q.l[e] = 1; return true; }
  if (p.l[e] == 1) { q.l[e] = 2; return true; }
  return false; }
static bool winReply(const P& p, int e) { if (p.l[e] != 0 || ht(p.c[e]) >= K) return false; P q = push(p, e, 1); return win(q, e, 1); }
// choose Black's reply after an event in column c; mustcover: only e == c allowed among non-winning replies; cover: free column (-1 = all free)
static int reply(const P& p1, int c, bool must, int freecol, int k) {
  for (int j = 0; j < 5; j++) { int d = ORD[j]; if (winReply(p1, d)) return d; }
  for (int pass = 0; pass < 2; pass++) for (int j = 0; j < 5; j++) { int d = ORD[j]; if (must && d != c) continue;
      int cost = (freecol < 0 || d == freecol) ? 0 : 1; if (cost != pass || cost > k) continue;
      P q; if (!outState(p1, d, q)) continue; if (solve(q, k - cost)) return d; }
  return -1; }
static bool solve(const P& p, int k) {
  u128 key_ = key(p); auto it = memo.find(key_);
  if (it != memo.end()) { if (k <= it->second.fail) return false; if (k >= it->second.hold) return true; }
  int rep = 0, pw = 1; bool ok = true;
  for (int c = 0; c < 5 && ok; c++, pw *= 5) {
    if (p.l[c] == 0) {
      if (ht(p.c[c]) < K) { P p1 = push(p, c, 0); if (win(p1, c, 2)) { ok = false; break; }
        int e = reply(p1, c, !(ht(p.c[c]) + 5 <= K), c, k); if (e < 0) ok = false; else rep += e * pw; }
      else { P q = p; q.l[c] = 2; if (!solve(q, k)) ok = false; }
    } else if (p.l[c] == 1) { P p1 = p; p1.l[c] = 2; bool all = true; for (int d = 0; d < 5; d++) if (p1.l[d] != 2) all = false;
      if (!all) { int e = reply(p1, c, false, -1, k); if (e < 0) ok = false; else rep += e * pw; } }
  }
  M& m = memo[key_]; if (it == memo.end()) { m.fail = -1; m.hold = 127; m.rep = 0; }
  if (ok) { if (k < m.hold) { m.hold = k; m.rep = rep; } } else if (k > m.fail) m.fail = k;
  return ok;
}
int main(int argc, char** argv) {
  if (argc < 3) return 1; K = atoi(argv[1]); if (K > 18) { fprintf(stderr, "K too large\n"); return 1; }
  std::string ms = argv[2]; P p; memset(&p, 0, sizeof p);
  for (size_t i = 0; i < ms.size(); i++) { int c = ms[i] - '1'; p = push(p, c, i % 2 == 0); }
  int Kb = -1, maxk = argc > 3 ? atoi(argv[3]) : 10;
  for (int k = 0; k <= maxk && Kb < 0; k++) if (solve(p, k)) Kb = k;
  if (Kb < 0) { fprintf(stderr, "NOT HELD within budget %d (solver states %zu)\n", maxk, memo.size()); return 2; }
  std::unordered_map<u128, char, KH> seen; std::vector<P> st; st.push_back(p); seen[key(p)] = 1; size_t n = 0;
  auto add = [&](const P& q) { u128 kq = key(q); if (!seen.count(kq)) { seen[kq] = 1; st.push_back(q); } };
  while (!st.empty()) { P q = st.back(); st.pop_back(); M& mq = memo[key(q)]; int rep = mq.rep; n++;
    if (mq.hold > 100) { fprintf(stderr, "internal: closure state without strategy\n"); return 3; }
    printf("%u %u %u %u %u %d %d %d %d %d %d\n", q.c[0], q.c[1], q.c[2], q.c[3], q.c[4], q.l[0], q.l[1], q.l[2], q.l[3], q.l[4], rep);
    int r = rep; for (int c = 0; c < 5; c++, r /= 5) { int e = r % 5;
      if (q.l[c] == 0) { if (ht(q.c[c]) < K) { P p1 = push(q, c, 0); if (winReply(p1, e)) continue; P o; outState(p1, e, o); add(o); }
                         else { P o = q; o.l[c] = 2; add(o); } }
      else if (q.l[c] == 1) { P p1 = q; p1.l[c] = 2; bool all = true; for (int d = 0; d < 5; d++) if (p1.l[d] != 2) all = false;
                              if (all) continue; if (winReply(p1, e)) continue; P o; outState(p1, e, o); add(o); } } }
  fprintf(stderr, "K=%d %s: zone value <= %d; solver states %zu, certificate %zu states\n", K, ms.c_str(), Kb, memo.size(), n); return 0;
}
