// certgen.cpp -- real-board safety solver that emits a strategy-closed certificate for the Lean checker.
// usage: certgen H moves        (moves: digits 1..5, Black first; White must be to move after them)
// output: one line per certificate position (White to move): c0 c1 c2 c3 c4 rep
//   ci = column in bijective base 2 (push p: 2n+1+[p is Black]);  rep = sum_c reply(c) * 5^c  (reply 0-based).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <unordered_map>
#include <vector>
#include <string>
typedef unsigned __int128 u128; typedef uint32_t u32;
static int H;
struct P { u32 c[5]; };
static inline int ht(u32 n) { return 31 - __builtin_clz(n + 1); }
static inline int cell(const P& p, int x, int y) { if (x < 0 || x > 4 || y < 0) return 0; int L = ht(p.c[x]); if (y >= L || y >= H) return 0; return (((p.c[x] + 1) >> (L - 1 - y)) & 1) ? 1 : 2; }
static bool win(const P& p, int c, int who) { int r = ht(p.c[c]) - 1; static const int D[4][2] = {{0,1},{1,0},{1,1},{1,-1}};
  for (auto& d : D) { int n = 1; for (int s = -1; s <= 1; s += 2) { int x = c + s*d[0], y = r + s*d[1]; while (cell(p, x, y) == who) { n++; x += s*d[0]; y += s*d[1]; } } if (n >= 4) return true; }
  return false; }
static inline P push(P p, int c, int black) { p.c[c] = 2 * p.c[c] + 1 + black; return p; }
static inline u128 key(const P& p) { u128 k = 0; for (int i = 0; i < 5; i++) k = (k << 24) | p.c[i]; return k; }
struct KH { size_t operator()(u128 k) const { uint64_t a = (uint64_t)k ^ ((uint64_t)(k >> 64) * 0x9E3779B97F4A7C15ULL); a ^= a >> 31; a *= 0xff51afd7ed558ccdULL; a ^= a >> 33; return a; } };
struct M { int8_t fail, hold; int rep; };            // budgets: lost with <= fail, held with >= hold (rep valid at hold)
static std::unordered_map<u128, M, KH> memo;
static const int ORD[5] = {2, 1, 3, 0, 4};
// White to move. Black may: win at once (free), cover (free), play anywhere after a cap (free), otherwise pay 1.
static bool solve(const P& p, int k) {
  u128 key_ = key(p); auto it = memo.find(key_);
  if (it != memo.end()) { if (k <= it->second.fail) return false; if (k >= it->second.hold) return true; }
  int rep = 0, pw = 1; bool ok = true;
  for (int c = 0; c < 5 && ok; c++, pw *= 5) { if (ht(p.c[c]) >= H) continue;
    P p1 = push(p, c, 0); if (win(p1, c, 2)) { ok = false; break; }
    bool full = true; for (int d = 0; d < 5; d++) if (ht(p1.c[d]) != H) full = false; if (full) continue;
    int e = -1; bool capped = ht(p1.c[c]) >= H;
    for (int j = 0; j < 5 && e < 0; j++) { int d = ORD[j]; if (ht(p1.c[d]) >= H) continue; P p2 = push(p1, d, 1); if (win(p2, d, 1)) e = d; }
    for (int pass = 0; pass < 2 && e < 0; pass++) for (int j = 0; j < 5 && e < 0; j++) { int d = ORD[j]; if (ht(p1.c[d]) >= H) continue;
        int cost = (d == c || capped) ? 0 : 1; if (cost != pass || cost > k) continue;
        if (solve(push(p1, d, 1), k - cost)) e = d; }
    if (e < 0) ok = false; else rep += e * pw; }
  M& m = memo[key_]; if (it == memo.end()) { m.fail = -1; m.hold = 127; m.rep = 0; }
  if (ok) { if (k < m.hold) { m.hold = k; m.rep = rep; } } else if (k > m.fail) m.fail = k;
  return ok;
}
int main(int argc, char** argv) {
  if (argc < 3) return 1; H = atoi(argv[1]); if (H < 1 || H > 22) { fprintf(stderr, "H must be between 1 and 22 for 24-bit columns\n"); return 1; }
  std::string ms = argv[2]; P p; memset(&p, 0, sizeof p);
  for (size_t i = 0; i < ms.size(); i++) { int c = ms[i] - '1'; if (c < 0 || c >= 5 || ht(p.c[c]) >= H) { fprintf(stderr, "illegal\n"); return 1; } p = push(p, c, i % 2 == 0); if (win(p, c, i % 2 == 0 ? 1 : 2)) { fprintf(stderr, "four in prefix\n"); return 1; } }
  if (ms.size() % 2 == 0) { fprintf(stderr, "White must be to move\n"); return 1; }
  int K = -1; int maxk = argc > 3 ? atoi(argv[3]) : 12;
  for (int k = 0; k <= maxk && K < 0; k++) if (solve(p, k)) K = k;
  if (K < 0) { fprintf(stderr, "UNSAFE within budget %d (solver states %zu)\n", maxk, memo.size()); return 2; }
  std::unordered_map<u128, char, KH> seen; std::vector<P> st; st.push_back(p); seen[key(p)] = 1; size_t n = 0;
  while (!st.empty()) { P q = st.back(); st.pop_back(); M& mq = memo[key(q)]; int rep = mq.rep; n++;
    if (mq.hold > 100) { fprintf(stderr, "internal: closure state without strategy\n"); return 3; }
    printf("%u %u %u %u %u %d\n", q.c[0], q.c[1], q.c[2], q.c[3], q.c[4], rep);
    int r = rep; for (int c = 0; c < 5; c++, r /= 5) { if (ht(q.c[c]) >= H) continue; P p1 = push(q, c, 0);
      bool full = true; for (int d = 0; d < 5; d++) if (ht(p1.c[d]) != H) full = false; if (full) continue;
      int e = r % 5; P p2 = push(p1, e, 1); if (win(p2, e, 1)) continue;
      u128 k = key(p2); if (!seen.count(k)) { seen[k] = 1; st.push_back(p2); } } }
  fprintf(stderr, "budget %d; ", K);
  fprintf(stderr, "SAFE: solver states %zu, certificate %zu positions\n", memo.size(), n); return 0;
}
