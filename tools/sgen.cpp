// sgen.cpp -- solver for the stretch game exactly as checked by C4W5/Cert/StretchC.lean (varsF, normAt, stepOKS);
// emits a strategy-closed certificate.
// usage: sgen D maxk root [root ...]      root = H:moves  (moves: Black first, digits 1..5)
// env: PAID="c.e,..."  restricts paid (non-cover) replies to: White column c (1..5) answered by column e (1..5); default: any.
// output lines: H b0 b1 b2 b3 b4 h0 h1 h2 h3 h4 rep     (black masks, heights; rep = ten base-5 digits, digit 2c+variant)
// Safety is a greatest fixpoint (the abstract graph has cycles): on-stack states are assumed safe; if an assumed state
// fails, all "safe" verdicts stamped while it was on the stack are invalidated.  "unsafe" verdicts are always sound.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <unordered_map>
#include <vector>
#include <string>
#include <algorithm>
typedef uint64_t u64; typedef unsigned __int128 u128; typedef unsigned __int128 MK; static const MK ONE = 1;
static int D;
struct S { int H; MK b[5]; int h[5]; };
static inline MK low(int n) { return n >= 128 ? ~(MK)0 : ((ONE << n) - 1); }
static void chk(const S& s) { if (s.H > 88) { fprintf(stderr, "height overflow\n"); exit(4); } }
static S push(S s, int c, int black) { if (black) s.b[c] |= ONE << s.h[c]; s.h[c]++; return s; }
static MK LM(const S& s) { MK m = ONE | (ONE << s.H);
  for (int c = 0; c < 5; c++) { int h = s.h[c]; MK b = s.b[c]; m |= ONE << h;
    if (h >= 1) m |= ((low(h - 1)) ^ ((b ^ (b >> 1)) & low(h - 1))) << 1; }
  return m; }
static bool clearM(int H, MK lm, int r) { return r <= H && D < r && ((lm >> (r - D)) & low(2 * D + 1)) == 0; }
static S stretch(const S& s, int r) { S q = s; q.H = s.H;
  for (int c = 0; c < 5; c++) if (r < s.h[c]) { MK b = s.b[c];
      q.b[c] = (b & low(r)) | (((b >> r) & 1) << r) | (((b >> (r - 1)) & 1) << (r + 1)) | ((b >> r) << (r + 2)); q.h[c] = s.h[c] + 2; }
  return q; }
static bool eqS(const S& a, const S& b) { for (int c = 0; c < 5; c++) if (a.b[c] != b.b[c] || a.h[c] != b.h[c]) return false; return true; }
static S normAt(const S& s, int x) {
  if (D + 4 <= s.h[x] && 2 <= s.H) { int r = s.h[x] - D - 3; S q = s; q.H = s.H - 2;
    for (int c = 0; c < 5; c++) if (r + 2 < s.h[c]) { q.b[c] = (s.b[c] & low(r)) | ((s.b[c] >> (r + 2)) << r); q.h[c] = s.h[c] - 2; }
    bool wf = true; for (int c = 0; c < 5; c++) if (q.h[c] > q.H || (q.b[c] >> q.h[c])) wf = false;
    if (wf && clearM(q.H, LM(q), r)) { S t = stretch(q, r); if (eqS(t, s)) return q; } }
  return s; }
static int vars(const S& s, int c, int black, S out[2]) { MK lm = LM(s); out[0] = push(s, c, black); int n = 1;
  if (clearM(s.H, lm, s.h[c] + D + 1) && !clearM(s.H, lm, s.h[c] + D + 2)) { S t = stretch(s, s.h[c] + D + 1); t.H = s.H + 2; chk(t); out[1] = push(t, c, black); n = 2; }
  return n; }
static bool and4(MK a, MK b, MK c, MK d) { return (a & b & c & d) != 0; }
static bool four(const S& s, int black) { MK m[5]; for (int c = 0; c < 5; c++) m[c] = black ? s.b[c] : (low(s.h[c]) & ~s.b[c]);
  for (int c = 0; c < 5; c++) if (and4(m[c], m[c] >> 1, m[c] >> 2, m[c] >> 3)) return true;
  for (int c = 0; c < 2; c++) { if (and4(m[c], m[c+1], m[c+2], m[c+3])) return true;
    if (and4(m[c], m[c+1] >> 1, m[c+2] >> 2, m[c+3] >> 3)) return true; if (and4(m[c] >> 3, m[c+1] >> 2, m[c+2] >> 1, m[c+3])) return true; }
  return false; }
static bool full(const S& s) { for (int c = 0; c < 5; c++) if (s.h[c] != s.H) return false; return true; }
// claim criterion, exactly as C4W5/Cert/ClaimC.lean (claimB)
static bool cellBlack(const S& s, int x, int y) { return x >= 0 && x < 5 && y >= 0 && y < s.H && ((s.b[x] >> y) & 1); }
static bool lineOK(const S& s, int q, int h0, int x, int y, int dy) {
  for (int j = 0; j < 4; j++) { int xx = x + j, yy = y + j * dy;
    if (cellBlack(s, xx, yy)) return true; if (xx == q && yy > h0 && ((yy - h0) % 2 + 2) % 2 == 1) return true;
    if (!(xx >= 0 && xx < 5 && yy >= 0 && yy < s.H)) return true; }
  return false; }
static bool linesDead(const S& s, int q, int h0, int c, int r) { static const int DY[3] = {0, 1, -1};
  for (int d = 0; d < 3; d++) for (int i = 0; i < 4; i++) if (!lineOK(s, q, h0, c - i, r - i * DY[d], DY[d])) return false; return true; }
static bool tb(MK b, int r) { return r >= 0 && r < 128 && ((b >> r) & 1); }
static bool claimQ(const S& s, int q) {
  if (s.H % 2) return false; for (int c = 0; c < 5; c++) if (s.h[c] > s.H || (s.b[c] >> s.h[c])) return false;
  if ((s.H - s.h[q]) % 2 != 1) return false; int h0 = s.h[q];
  for (int c = 0; c < 5; c++) { int h = s.h[c]; MK b = s.b[c];
    if (h < s.H && h >= 3 && !tb(b, h - 1) && !tb(b, h - 2) && !tb(b, h - 3)) return false;
    for (int r = 0; r <= s.H; r++) { bool exc = r < h && !tb(b, r) && (r == 0 || !tb(b, r - 1)); bool pot = r == h && h < s.H && (h == 0 || !tb(b, h - 1));
      if ((exc || pot) && !linesDead(s, q, h0, c, r)) return false; } }
  return true; }
static bool NOLEAF = false;
static bool leaf(const S& s) { if (NOLEAF) return false; for (int q = 0; q < 5; q++) if (claimQ(s, q)) return true; return false; }
struct K { u64 w[11]; bool operator==(const K& o) const { return !memcmp(w, o.w, sizeof w); } };
static K key(const S& s) { K k; for (int c = 0; c < 5; c++) { k.w[2*c] = (u64)s.b[c]; k.w[2*c+1] = (u64)(s.b[c] >> 64); } u64 x = s.H; for (int c = 0; c < 5; c++) x = x * 128 + s.h[c]; k.w[10] = x; return k; }
struct KH { size_t operator()(const K& k) const { u64 a = 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 11; i++) { a ^= k.w[i]; a *= 0xff51afd7ed558ccdULL; a ^= a >> 29; } return a; } };
struct M { int8_t fail, hold, onstack, assumed; int rep; u64 stamp; };
static std::unordered_map<K, M, KH> memo;
static u64 clockv = 0; static std::vector<std::pair<u64, u64>> inv; static u64 invals = 0;
static bool invalid(u64 st) { auto it = std::upper_bound(inv.begin(), inv.end(), std::make_pair(st, ~u64{0})); if (it == inv.begin()) return false; --it; return st <= it->second; }
static bool paidAny = true, paidOK[5][5];
// TPAIRS="c.r.d,..." as in sg.cpp: White's stone in column c at row r (1-based; Tn = n below the top; Wn = n below the wall defect) may be answered by column d
static bool TP = false; static std::vector<int> TPL;
static int wallDefect(const S& a) { for (int r = 1; r < a.h[1]; r++) if (((a.b[1] >> (r - 1)) & 1) && ((a.b[1] >> r) & 1)) return r; return 0; }
static bool tpAllowed(const S& a, int c, int d) { if (!TP) return true; int r = a.h[c], t = a.H - r, wd = wallDefect(a) - r;
  for (size_t i = 0; i < TPL.size(); i += 3) if (TPL[i] == c && TPL[i + 2] == d && ((TPL[i + 1] > 0 && TPL[i + 1] < 1000 && TPL[i + 1] == r) || (TPL[i + 1] <= 0 && -TPL[i + 1] == t) || (TPL[i + 1] >= 1000 && TPL[i + 1] - 1000 == wd))) return true;
  return false; }
static const int ORD[5] = {2, 1, 3, 0, 4};
static bool solve(const S& s, int k);
static int reply(const S& n1, int c, int k) {
  S v[2];
  for (int j = 0; j < 5; j++) { int e = ORD[j]; if (n1.h[e] >= n1.H) continue; int n = vars(n1, e, 1, v); bool all = true; for (int i = 0; i < n; i++) if (!four(v[i], 1)) all = false; if (all) return e; }
  bool capped = n1.h[c] >= n1.H;
  for (int pass = 0; pass < 2; pass++) for (int j = 0; j < 5; j++) { int e = ORD[j]; if (n1.h[e] >= n1.H) continue;
      int cost = (capped || e == c) ? 0 : 1; if (cost != pass || cost > k) continue; if (cost && !paidAny && !paidOK[c][e]) continue; if (cost && !tpAllowed(n1, c, e)) continue;
      int n = vars(n1, e, 1, v); bool ok = true;
      for (int i = 0; i < n && ok; i++) if (!four(v[i], 1)) { S o = normAt(v[i], e); if (!leaf(o) && !solve(o, k - cost)) ok = false; }
      if (ok) return e; }
  return -1; }
static bool solve(const S& s, int k) {
  K kk = key(s); { auto it = memo.find(kk);
    if (it != memo.end()) { M& m = it->second; if (k <= m.fail) return false; if (m.hold <= k && !invalid(m.stamp)) return true; if (m.onstack) { m.assumed = 1; return true; } }
    else { M m; m.fail = -1; m.hold = 127; m.onstack = 0; m.assumed = 0; m.rep = 0; m.stamp = 0; memo[kk] = m; } }
  { M& m = memo[kk]; m.onstack = 1; m.assumed = 0; }
  u64 mystamp = ++clockv; int rep = 0, pw = 1; bool ok = true; S v[2];
  for (int c = 0; c < 5; c++, pw *= 25) { if (!ok) break; if (s.h[c] >= s.H) continue; int n = vars(s, c, 0, v);
    for (int i = 0; i < n && ok; i++) { if (four(v[i], 0)) { ok = false; break; } S n1 = normAt(v[i], c); if (full(n1)) continue;
      int e = reply(n1, c, k); if (e < 0) ok = false; else rep += e * pw * (i ? 5 : 1); } }
  M& m = memo[kk]; m.onstack = 0;
  if (ok) { m.hold = k; m.rep = rep; m.stamp = ++clockv; }
  else { if (k > m.fail) m.fail = k; if (m.assumed) { while (!inv.empty() && inv.back().first >= mystamp) inv.pop_back(); inv.push_back({mystamp, clockv}); invals++; } }
  return ok; }
int main(int argc, char** argv) {
  if (argc < 4) return 1; D = atoi(argv[1]); int maxk = atoi(argv[2]);
  NOLEAF = getenv("NOLEAF") != 0;
  if (const char* e = getenv("PAID")) { paidAny = false; memset(paidOK, 0, sizeof paidOK); for (const char* q = e; *q; ) { int a = q[0] - '1', b = q[2] - '1'; paidOK[a][b] = true; q += 3; if (*q == ',') q++; } }
  if (getenv("TPAIRS")) { TP = true; const char* q = getenv("TPAIRS");
    while (*q) { int c = q[0] - '1'; q += 2; int r; if (*q == 'T') r = -atoi(q + 1); else if (*q == 'W') r = 1000 + atoi(q + 1); else r = atoi(q); while (*q != '.') q++; q++; int d = *q - '1'; q++; if (*q == ',') q++; TPL.push_back(c); TPL.push_back(r); TPL.push_back(d); } }
  std::vector<S> roots;
  for (int a = 3; a < argc; a++) { S s; memset(&s, 0, sizeof s); s.H = atoi(argv[a]); const char* ms = strchr(argv[a], ':') + 1;
    for (int i = 0; ms[i]; i++) s = push(s, ms[i] - '1', i % 2 == 0); chk(s); roots.push_back(s); }
  for (auto& r : roots) { int Kb = -1; for (int k = 0; k <= maxk && Kb < 0; k++) if (solve(r, k)) Kb = k;
    if (Kb < 0) { fprintf(stderr, "root %d NOT HELD within budget %d (solver states %zu)\n", (int)(&r - &roots[0]), maxk, memo.size()); return 2; }
    fprintf(stderr, "root %d: budget %d (solver states %zu, invalidations %llu)\n", (int)(&r - &roots[0]), Kb, memo.size(), (unsigned long long)invals); }
  std::vector<std::pair<S, int>> out;
  for (int pass = 0; ; pass++) { out.clear(); bool redo = false; if (pass > 50) { fprintf(stderr, "closure does not stabilise\n"); return 3; }
    std::unordered_map<K, char, KH> seen; std::vector<S> st; for (auto& r : roots) if (!seen.count(key(r))) { seen[key(r)] = 1; st.push_back(r); }
    while (!st.empty() && !redo) { S q = st.back(); st.pop_back(); M* m = &memo[key(q)];
      if (m->hold > 100 || invalid(m->stamp)) { u64 i0 = invals; if (!solve(q, maxk)) { fprintf(stderr, "closure state fails\n"); return 3; } redo = true; (void)i0; break; }
      int rep = m->rep; out.push_back({q, rep}); S v[2], w[2]; int r = rep;
      for (int c = 0; c < 5; c++) { int e0 = r % 5, e1 = (r / 5) % 5; r /= 25; if (q.h[c] >= q.H) continue; int n = vars(q, c, 0, v);
        for (int i = 0; i < n; i++) { S n1 = normAt(v[i], c); if (full(n1)) continue; int e = i ? e1 : e0; int n2 = vars(n1, e, 1, w);
          for (int j = 0; j < n2; j++) { if (four(w[j], 1)) continue; S o = normAt(w[j], e); if (leaf(o)) continue; K ko = key(o); if (!seen.count(ko)) { seen[ko] = 1; st.push_back(o); } } } } }
    if (!redo) break; }
  // final verification of the emitted set, independent of the solver's bookkeeping
  { std::unordered_map<K, char, KH> in; for (auto& o : out) in[key(o.first)] = 1; S v[2], w[2];
    for (auto& o : out) { const S& q = o.first; int r = o.second;
      for (int c = 0; c < 5; c++) { int e0 = r % 5, e1 = (r / 5) % 5; r /= 25; if (q.h[c] >= q.H) continue; int n = vars(q, c, 0, v);
        for (int i = 0; i < n; i++) { if (four(v[i], 0)) { fprintf(stderr, "verify: white four\n"); return 5; } S n1 = normAt(v[i], c); if (full(n1)) continue; int e = i ? e1 : e0;
          if (n1.h[e] >= n1.H) { fprintf(stderr, "verify: illegal reply\n"); return 5; } int n2 = vars(n1, e, 1, w);
          for (int j = 0; j < n2; j++) { if (four(w[j], 1)) continue; S o = normAt(w[j], e); if (!leaf(o) && !in.count(key(o))) { fprintf(stderr, "verify: not closed\n"); return 5; } } } } } }
  auto pr = [](MK v) { char buf[48]; int n = 0; if (!v) buf[n++] = '0'; while (v) { buf[n++] = '0' + (int)(v % 10); v /= 10; } while (n) putchar(buf[--n]); };
  for (auto& o : out) { const S& q = o.first; printf("%d", q.H); for (int c = 0; c < 5; c++) { putchar(' '); pr(q.b[c]); } printf(" %d %d %d %d %d %d\n", q.h[0], q.h[1], q.h[2], q.h[3], q.h[4], o.second); }
  fprintf(stderr, "D=%d: solver states %zu, invalidations %llu, certificate %zu states (verified closed)\n", D, memo.size(), (unsigned long long)invals, out.size()); return 0; }
