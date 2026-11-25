// c4w5_odd_colab.cpp
// High-performance, memory-bounded, multi-threaded ZoneGen & Finite solver
// for 5-column odd-height Connect Four: 5 x (2m + 1).
//
// Compile: g++ -O3 -march=native -std=c++17 -pthread c4w5_odd_colab.cpp -o c4w5_odd_colab
// Usage:   ./c4w5_odd_colab <output_dir> [--smoke]

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <cstdint>
#include <cstring>
#include <algorithm>
#include <chrono>
#include <thread>
#include <mutex>
#include <iomanip>
#include <filesystem>
#include <functional>
#include <atomic>

using namespace std;
namespace fs = std::filesystem;

enum Lab : uint8_t { LOW = 0, ODD = 1, DEAD = 2 };

struct State {
    uint16_t me[5];
    uint16_t opp[5];
    uint8_t h[5];
    uint8_t lab[5];
};

// Fast fixed-memory flat hash table (16 bytes per slot: 12-byte key + 1-byte val + 3-byte pad,
// or simpler: two parallel arrays / packed struct with __uint128_t key + val?
// Even better: for K <= 9, key fits in 60 bits! Store (key << 2) | val in ONE uint64_t (8 bytes/slot)!!
// 64M slots = 512 MB RAM! 256M slots = 2.0 GB RAM! Zero malloc overhead, 5x faster than unordered_map!)
struct FlatTT {
    vector<uint64_t> table;
    uint64_t mask = 0;
    uint64_t used = 0;

    void init(size_t pow2_bits) {
        size_t sz = 1ULL << pow2_bits;
        table.assign(sz, 0ULL);
        mask = sz - 1;
        used = 0;
    }

    inline uint64_t hash64(uint64_t x) const {
        x ^= x >> 30;
        x *= 0xbf58476d1ce4e5b9ULL;
        x ^= x >> 27;
        x *= 0x94d049bb133111ebULL;
        x ^= x >> 31;
        return x;
    }

    // Returns 0 = miss, 1 = SAFE, 2 = UNSAFE
    inline uint8_t probe(uint64_t key60) const {
        uint64_t idx = hash64(key60) & mask;
        for (int step = 0; step < 64; ++step) {
            uint64_t e = table[(idx + step) & mask];
            if (e == 0) return 0;
            if ((e >> 2) == key60) return (uint8_t)(e & 3ULL);
        }
        return 0;
    }

    inline void store(uint64_t key60, uint8_t val) {
        uint64_t idx = hash64(key60) & mask;
        for (int step = 0; step < 64; ++step) {
            uint64_t& e = table[(idx + step) & mask];
            if (e == 0) {
                e = (key60 << 2) | (uint64_t)val;
                used++;
                return;
            }
            if ((e >> 2) == key60) {
                e = (key60 << 2) | (uint64_t)val;
                return;
            }
        }
        // Always-replace at primary slot if probe window full (bounded memory, never OOMs)
        table[idx] = (key60 << 2) | (uint64_t)val;
    }
};

// Pack state for K <= 9 into 60 bits (never 0 because (1<<h) >= 1)
inline uint64_t pack60(const State& s) {
    uint64_t key = 0;
    for (int c = 0; c < 5; ++c) {
        uint64_t colCode = ((1ULL << s.h[c]) | (uint64_t)s.me[c]); // <= 10 bits for K <= 9
        uint64_t entry = (colCode << 2) | (uint64_t)s.lab[c];      // 12 bits
        key = (key << 12) | entry;
    }
    return key;
}

inline uint64_t packCanonical60(const State& s) {
    uint64_t k1 = pack60(s);
    uint64_t k2 = 0;
    for (int c = 4; c >= 0; --c) {
        uint64_t colCode = ((1ULL << s.h[c]) | (uint64_t)s.me[c]);
        uint64_t entry = (colCode << 2) | (uint64_t)s.lab[c];
        k2 = (k2 << 12) | entry;
    }
    return k1 < k2 ? k1 : k2;
}

inline bool hasFour(const uint16_t m[5]) {
    for (int c = 0; c < 5; ++c) {
        uint16_t x = m[c];
        if (x & (x >> 1) & (x >> 2) & (x >> 3)) return true;
    }
    if (m[0] & m[1] & m[2] & m[3]) return true;
    if (m[1] & m[2] & m[3] & m[4]) return true;
    if (m[0] & (m[1] >> 1) & (m[2] >> 2) & (m[3] >> 3)) return true;
    if (m[1] & (m[2] >> 1) & (m[3] >> 2) & (m[4] >> 3)) return true;
    if ((m[0] >> 3) & (m[1] >> 2) & (m[2] >> 1) & m[3]) return true;
    if ((m[1] >> 3) & (m[2] >> 2) & (m[3] >> 1) & m[4]) return true;
    return false;
}

struct Solver {
    int K = 7;
    bool finiteMode = false;
    bool evenEmpty = false; // true: Odd-H Black (ClaimEven); false: Odd-H White (ClaimOdd + optional ZO)
    bool useZO = true;
    bool useCanonical = true;
    uint64_t nodeLimit = 20000000;
    uint64_t nodesVisited = 0;
    uint64_t leafClaimHits = 0;
    uint64_t leafZOHits = 0;
    bool hitLimit = false;
    FlatTT tt;

    // Optional exact policy recording (used for small certificate export)
    bool recordPolicy = false;
    struct PolicyEntry { int8_t reply[5]; };
    unordered_map<uint64_t, PolicyEntry> policy;

    inline bool noTopThreeOpp(const State& s) const {
        for (int c = 0; c < 5; ++c) {
            if (s.h[c] < K && s.h[c] >= 3) {
                uint16_t mask = 7u << (s.h[c] - 3);
                if ((s.opp[c] & mask) == mask) return false;
            }
        }
        return true;
    }

    inline void computeExcPot(const State& s, uint16_t ep[5]) const {
        for (int c = 0; c < 5; ++c) {
            uint16_t o = s.opp[c];
            uint16_t exc = (o & 1u) | (o & (o << 1));
            uint16_t pot = 0;
            if (s.h[c] < K) {
                if (s.h[c] == 0 || ((o >> (s.h[c] - 1)) & 1u)) pot = (uint16_t)(1u << s.h[c]);
            }
            ep[c] = (exc | pot) & ((1u << K) - 1u);
        }
    }

    inline bool allLinesDead(const uint16_t ep[5], const uint16_t blocked[5]) const {
        uint16_t ok[5];
        uint16_t full = (uint16_t)((1u << K) - 1u);
        for (int c = 0; c < 5; ++c) ok[c] = (~blocked[c]) & full;
        if ((ok[0] & ok[1] & ok[2] & ok[3]) & (ep[0] | ep[1] | ep[2] | ep[3])) return false;
        if ((ok[1] & ok[2] & ok[3] & ok[4]) & (ep[1] | ep[2] | ep[3] | ep[4])) return false;
        uint16_t rmask = (K >= 4) ? (uint16_t)((1u << (K - 3)) - 1u) : 0;
        if ((ok[0] & (ok[1] >> 1) & (ok[2] >> 2) & (ok[3] >> 3) & rmask) & ((ep[0] | (ep[1] >> 1) | (ep[2] >> 2) | (ep[3] >> 3)) & rmask)) return false;
        if ((ok[1] & (ok[2] >> 1) & (ok[3] >> 2) & (ok[4] >> 3) & rmask) & ((ep[1] | (ep[2] >> 1) | (ep[3] >> 2) | (ep[4] >> 3)) & rmask)) return false;
        if (((ok[0] >> 3) & (ok[1] >> 2) & (ok[2] >> 1) & ok[3] & rmask) & (((ep[0] >> 3) | (ep[1] >> 2) | (ep[2] >> 1) | ep[3]) & rmask)) return false;
        if (((ok[1] >> 3) & (ok[2] >> 2) & (ok[3] >> 1) & ok[4] & rmask) & (((ep[1] >> 3) | (ep[2] >> 2) | (ep[3] >> 1) | ep[4]) & rmask)) return false;
        return true;
    }

    inline uint16_t claimedColMask(int h0) const {
        uint16_t mask = 0;
        for (int y = h0 + 1; y < K; y += 2) mask |= (uint16_t)(1u << y);
        return mask;
    }

    inline bool hasOddThreatAt(const State& s, int t) const {
        int r = s.h[t] + 1;
        if (r >= K) return false;
        uint16_t m[5];
        for (int c = 0; c < 5; ++c) m[c] = s.me[c];
        m[t] |= (uint16_t)(1u << r);
        if (m[0] & m[1] & m[2] & m[3]) return true;
        if (m[1] & m[2] & m[3] & m[4]) return true;
        if (m[0] & (m[1] >> 1) & (m[2] >> 2) & (m[3] >> 3)) return true;
        if (m[1] & (m[2] >> 1) & (m[3] >> 2) & (m[4] >> 3)) return true;
        if ((m[0] >> 3) & (m[1] >> 2) & (m[2] >> 1) & m[3]) return true;
        if ((m[1] >> 3) & (m[2] >> 2) & (m[3] >> 1) & m[4]) return true;
        return false;
    }

    int isLeaf(const State& s) const { // 0=no, 1=Claim, 2=ZO
        if (!noTopThreeOpp(s)) return 0;
        uint16_t ep[5];
        computeExcPot(s, ep);
        uint16_t blocked[5];
        if (evenEmpty) {
            for (int c = 0; c < 5; ++c) {
                blocked[c] = s.me[c];
                if (s.h[c] < K && ((K - s.h[c]) & 1) == 0) blocked[c] |= claimedColMask(s.h[c]);
            }
            return allLinesDead(ep, blocked) ? 1 : 0;
        } else {
            for (int q = 0; q < 5; ++q) {
                if (s.h[q] < K && ((K - s.h[q]) & 1) == 1) {
                    for (int c = 0; c < 5; ++c) blocked[c] = s.me[c];
                    blocked[q] |= claimedColMask(s.h[q]);
                    if (allLinesDead(ep, blocked)) return 1;
                }
            }
            if (useZO) {
                for (int t = 0; t < 5; ++t) {
                    if (s.h[t] + 2 <= K && ((K - s.h[t]) & 1) == 1 && hasOddThreatAt(s, t)) {
                        for (int c = 0; c < 5; ++c) {
                            blocked[c] = s.me[c];
                            if (c == t) {
                                for (int y = s.h[t] + 1; y < K; ++y) blocked[c] |= (uint16_t)(1u << y);
                            } else if (s.h[c] < K && ((K - s.h[c]) & 1) == 0) {
                                blocked[c] |= claimedColMask(s.h[c]);
                            }
                        }
                        if (allLinesDead(ep, blocked)) return 2;
                    }
                }
            }
            return 0;
        }
    }

    bool canMeWin(const State& s) const {
        for (int e = 0; e < 5; ++e) {
            if ((finiteMode || s.lab[e] == LOW) && s.h[e] < K) {
                uint16_t m[5];
                memcpy(m, s.me, sizeof(m));
                m[e] |= (uint16_t)(1u << s.h[e]);
                if (hasFour(m)) return true;
            }
        }
        return false;
    }

    bool tryMe(const State& s1, int e) {
        State s2 = s1;
        if (finiteMode) {
            if (s1.h[e] < K) { s2.me[e] |= (1u << s2.h[e]); s2.h[e]++; return solve(s2); }
            return false;
        } else {
            if (s1.lab[e] == LOW && s1.h[e] < K) { s2.me[e] |= (1u << s2.h[e]); s2.h[e]++; return solve(s2); }
            if (s1.lab[e] == LOW && s1.h[e] == K) { s2.lab[e] = ODD; return solve(s2); }
            if (s1.lab[e] == ODD) { s2.lab[e] = DEAD; return solve(s2); }
            return false;
        }
    }

    bool solve(const State& s) {
        if (hitLimit) return false;
        if (finiteMode) {
            bool full = true;
            for (int c = 0; c < 5; ++c) if (s.h[c] < K) { full = false; break; }
            if (full) return true;
        } else {
            bool allDead = true;
            for (int c = 0; c < 5; ++c) if (s.lab[c] != DEAD) { allDead = false; break; }
            if (allDead) return true;
        }

        uint64_t key = useCanonical ? packCanonical60(s) : pack60(s);
        uint8_t hit = tt.probe(key);
        if (hit != 0) return hit == 1;

        int lf = isLeaf(s);
        if (lf) {
            if (lf == 1) leafClaimHits++; else leafZOHits++;
            tt.store(key, 1);
            return true;
        }

        if (++nodesVisited > nodeLimit) { hitLimit = true; return false; }

        PolicyEntry pe;
        for (int c = 0; c < 5; ++c) pe.reply[c] = -1;

        const int order[5] = {2, 1, 3, 0, 4};
        for (int idx = 0; idx < 5; ++idx) {
            int c = order[idx];
            if (finiteMode) {
                if (s.h[c] >= K) continue;
                State s1 = s;
                s1.opp[c] |= (1u << s1.h[c]); s1.h[c]++;
                if (hasFour(s1.opp)) { tt.store(key, 2); return false; }
                bool full = true;
                for (int d = 0; d < 5; ++d) if (s1.h[d] < K) { full = false; break; }
                if (full) { pe.reply[c] = -4; continue; }
                if (canMeWin(s1)) { pe.reply[c] = -2; continue; }
                bool ok = false;
                if (s1.h[c] < K && tryMe(s1, c)) { ok = true; pe.reply[c] = c; }
                if (!ok) {
                    for (int j = 0; j < 5; ++j) {
                        int e = order[j];
                        if (e == c) continue;
                        if (tryMe(s1, e)) { ok = true; pe.reply[c] = e; break; }
                        if (hitLimit) return false;
                    }
                }
                if (!ok) { tt.store(key, 2); return false; }
            } else {
                if (s.lab[c] == LOW && s.h[c] < K) {
                    State s1 = s;
                    s1.opp[c] |= (1u << s1.h[c]); s1.h[c]++;
                    if (hasFour(s1.opp)) { tt.store(key, 2); return false; }
                    if (canMeWin(s1)) { pe.reply[c] = -2; continue; }
                    bool ok = false;
                    if (tryMe(s1, c)) { ok = true; pe.reply[c] = c; }
                    else if (s.h[c] + 5 <= K) {
                        for (int j = 0; j < 5; ++j) {
                            int e = order[j];
                            if (e == c) continue;
                            if (tryMe(s1, e)) { ok = true; pe.reply[c] = e; break; }
                            if (hitLimit) return false;
                        }
                    }
                    if (!ok) { tt.store(key, 2); return false; }
                } else if (s.lab[c] == LOW && s.h[c] == K) {
                    State s2 = s; s2.lab[c] = DEAD;
                    if (!solve(s2)) { tt.store(key, 2); return false; }
                    pe.reply[c] = -3;
                } else if (s.lab[c] == ODD) {
                    State s1 = s; s1.lab[c] = DEAD;
                    bool allD = true;
                    for (int d = 0; d < 5; ++d) if (s1.lab[d] != DEAD) { allD = false; break; }
                    if (allD) { pe.reply[c] = -4; continue; }
                    if (canMeWin(s1)) { pe.reply[c] = -2; continue; }
                    bool ok = false;
                    for (int j = 0; j < 5; ++j) {
                        int e = order[j];
                        if (tryMe(s1, e)) { ok = true; pe.reply[c] = e; break; }
                        if (hitLimit) return false;
                    }
                    if (!ok) { tt.store(key, 2); return false; }
                }
            }
        }
        tt.store(key, 1);
        if (recordPolicy) policy[key] = pe;
        return true;
    }

    // Independent verifier + certificate exporter (requires recordPolicy=true, useCanonical=false)
    bool verifyAndExport(const State& root, const string& certPath, size_t& outInternal, size_t& outLeaves) {
        unordered_set<uint64_t> visInt, visLeaf;
        vector<pair<uint64_t, PolicyEntry>> rows;
        function<bool(const State&)> walk = [&](const State& s) -> bool {
            bool allDead = true;
            for (int c = 0; c < 5; ++c) if (s.lab[c] != DEAD) { allDead = false; break; }
            if (allDead) return true;
            uint64_t key = pack60(s);
            if (isLeaf(s)) { visLeaf.insert(key); return true; }
            if (visInt.count(key)) return true;
            auto it = policy.find(key);
            if (it == policy.end()) return false;
            visInt.insert(key);
            rows.push_back({key, it->second});
            const PolicyEntry& pe = it->second;
            for (int c = 0; c < 5; ++c) {
                if (s.lab[c] == LOW && s.h[c] < K) {
                    State s1 = s; s1.opp[c] |= (1u << s1.h[c]); s1.h[c]++;
                    if (hasFour(s1.opp)) return false;
                    if (pe.reply[c] == -2) { if (!canMeWin(s1)) return false; continue; }
                    int e = pe.reply[c];
                    if (e < 0 || e >= 5) return false;
                    if (e != c && !(s.h[c] + 5 <= K)) return false;
                    State s2 = s1;
                    if (s1.lab[e] == LOW && s1.h[e] < K) { s2.me[e] |= (1u << s2.h[e]); s2.h[e]++; }
                    else if (s1.lab[e] == LOW && s1.h[e] == K) { s2.lab[e] = ODD; }
                    else if (s1.lab[e] == ODD) { s2.lab[e] = DEAD; }
                    else return false;
                    if (!walk(s2)) return false;
                } else if (s.lab[c] == LOW && s.h[c] == K) {
                    State s2 = s; s2.lab[c] = DEAD;
                    if (!walk(s2)) return false;
                } else if (s.lab[c] == ODD) {
                    State s1 = s; s1.lab[c] = DEAD;
                    bool allD = true;
                    for (int d = 0; d < 5; ++d) if (s1.lab[d] != DEAD) { allD = false; break; }
                    if (allD) continue;
                    if (pe.reply[c] == -2) { if (!canMeWin(s1)) return false; continue; }
                    int e = pe.reply[c];
                    if (e < 0 || e >= 5) return false;
                    State s2 = s1;
                    if (s1.lab[e] == LOW && s1.h[e] < K) { s2.me[e] |= (1u << s2.h[e]); s2.h[e]++; }
                    else if (s1.lab[e] == LOW && s1.h[e] == K) { s2.lab[e] = ODD; }
                    else if (s1.lab[e] == ODD) { s2.lab[e] = DEAD; }
                    else return false;
                    if (!walk(s2)) return false;
                }
            }
            return true;
        };
        bool ok = walk(root);
        outInternal = visInt.size();
        outLeaves = visLeaf.size();
        if (ok && !certPath.empty()) {
            ofstream ofs(certPath);
            ofs << "# K=" << K << " evenEmpty=" << evenEmpty << " useZO=" << useZO
                << " internal=" << outInternal << " leaves=" << outLeaves << "\n";
            ofs << "# format: key60 r0 r1 r2 r3 r4 (-2=win, -3=boundary_dead, -4=all_dead)\n";
            for (auto& [k, pe] : rows) {
                ofs << k << " " << (int)pe.reply[0] << " " << (int)pe.reply[1] << " "
                    << (int)pe.reply[2] << " " << (int)pe.reply[3] << " " << (int)pe.reply[4] << "\n";
            }
        }
        return ok;
    }
};

State makeMoves(const vector<pair<int,int>>& mv) {
    State s; memset(&s, 0, sizeof(s));
    for (auto [c, p] : mv) {
        if (p == 1) s.me[c] |= (1u << s.h[c]);
        else s.opp[c] |= (1u << s.h[c]);
        s.h[c]++;
    }
    return s;
}

struct TaskResult {
    string group;
    string name;
    string mode;
    int K;
    string status; // SAFE, UNSAFE, LIMIT
    uint64_t nodes;
    uint64_t claimLeaves;
    uint64_t zoLeaves;
    double ms;
    string extra;
};

int main(int argc, char** argv) {
    string outDir = (argc >= 2) ? argv[1] : "./colab_results";
    bool smoke = (argc >= 3 && string(argv[2]) == "--smoke");
    fs::create_directories(outDir);

    unsigned hwThreads = max(1u, thread::hardware_concurrency());
    cout << "=== C4W5 Odd-Height Colab Runner ===\n";
    cout << "Output dir: " << outDir << " | Threads: " << hwThreads << " | Smoke: " << smoke << "\n";

    vector<TaskResult> results;
    mutex resMtx;

    auto addRes = [&](const TaskResult& r) {
        lock_guard<mutex> lk(resMtx);
        results.push_back(r);
        cout << "[" << r.group << "] " << r.name << " (" << r.mode << "=" << r.K << "): "
             << r.status << " | nodes=" << r.nodes << " | " << fixed << setprecision(1) << r.ms << " ms"
             << (r.extra.empty() ? "" : (" | " + r.extra)) << "\n" << flush;
    };

    // ------------------------------------------------------------------
    // TASK 1: Independently verify & export small K=7 closed certificates
    // ------------------------------------------------------------------
    {
        struct CertJob { string name; State root; bool evenEmpty; string fname; };
        vector<CertJob> jobs = {
            {"Black_B2",       makeMoves({{1,1}}),                         true,  "cert_black_B2_K7.txt"},
            {"White_B3_W2",    makeMoves({{2,2},{1,1}}),                   false, "cert_white_B3W2_K7.txt"},
            {"White_B1_W2",    makeMoves({{0,2},{1,1}}),                   false, "cert_white_B1W2_K7.txt"},
            {"White_B2W2_B1W4",makeMoves({{1,2},{1,1},{0,2},{3,1}}),       false, "cert_white_B2W2_B1W4_K7.txt"},
            {"White_B2W2_B3W1",makeMoves({{1,2},{1,1},{2,2},{0,1}}),       false, "cert_white_B2W2_B3W1_K7.txt"},
            {"White_B2W2_B5W1",makeMoves({{1,2},{1,1},{4,2},{0,1}}),       false, "cert_white_B2W2_B5W1_K7.txt"},
        };
        for (auto& j : jobs) {
            Solver sv;
            sv.K = 7; sv.finiteMode = false; sv.evenEmpty = j.evenEmpty;
            sv.useZO = false; sv.useCanonical = false; sv.recordPolicy = true;
            sv.nodeLimit = 2000000; sv.tt.init(20); // 1M slots = 8 MB
            auto t0 = chrono::steady_clock::now();
            bool ok = sv.solve(j.root);
            size_t nInt = 0, nLeaf = 0;
            bool vok = ok ? sv.verifyAndExport(j.root, outDir + "/" + j.fname, nInt, nLeaf) : false;
            double ms = chrono::duration<double, milli>(chrono::steady_clock::now() - t0).count();
            addRes({"Task1_CertExport", j.name, "Zone_K", 7,
                    (ok && vok) ? "SAFE_VERIFIED" : "FAIL",
                    sv.nodesVisited, sv.leafClaimHits, sv.leafZOHits, ms,
                    "internal=" + to_string(nInt) + ",leaves=" + to_string(nLeaf) + ",file=" + j.fname});
        }
    }

    // ------------------------------------------------------------------
    // TASK 2: Finite Board H = 7 Verification (with ClaimEven / ClaimOdd+ZO)
    // ------------------------------------------------------------------
    {
        struct FinJob { string name; State root; bool evenEmpty; };
        vector<FinJob> jobs = {
            {"Black_B2_H7",    makeMoves({{1,1}}),       true},
            {"White_B1_W2_H7", makeMoves({{0,2},{1,1}}), false},
            {"White_B2_W2_H7", makeMoves({{1,2},{1,1}}), false},
            {"White_B2_W5_H7", makeMoves({{1,2},{4,1}}), false},
            {"White_B3_W2_H7", makeMoves({{2,2},{1,1}}), false},
        };
        uint64_t lim = smoke ? 100000 : 15000000;
        size_t ttBits = smoke ? 18 : 24; // 16M slots = 128 MB per job
        for (auto& j : jobs) {
            Solver sv;
            sv.K = 7; sv.finiteMode = true; sv.evenEmpty = j.evenEmpty;
            sv.useZO = true; sv.useCanonical = true;
            sv.nodeLimit = lim; sv.tt.init(ttBits);
            auto t0 = chrono::steady_clock::now();
            bool ok = sv.solve(j.root);
            double ms = chrono::duration<double, milli>(chrono::steady_clock::now() - t0).count();
            addRes({"Task2_FiniteH7", j.name, "Finite_H", 7,
                    sv.hitLimit ? "LIMIT" : (ok ? "SAFE" : "UNSAFE"),
                    sv.nodesVisited, sv.leafClaimHits, sv.leafZOHits, ms, ""});
        }
    }

    // ------------------------------------------------------------------
    // TASK 3A: Deep ZoneGen(K=9, ClaimOdd+ZO) on B2 W2 {B2, B4} & B2 W5 {B1, B4}
    // ------------------------------------------------------------------
    {
        struct ProbeJob { string name; State root; };
        vector<ProbeJob> jobs;
        // B2 W2 B2 W{1,2,4,5} (W3 already UNSAFE at 79k)
        for (int w : {0, 1, 3, 4})
            jobs.push_back({"B2W2B2_W" + to_string(w+1), makeMoves({{1,2},{1,1},{1,2},{w,1}})});
        // B2 W2 B4 W{1,3,5} (W2, W4 already UNSAFE)
        for (int w : {0, 2, 4})
            jobs.push_back({"B2W2B4_W" + to_string(w+1), makeMoves({{1,2},{1,1},{3,2},{w,1}})});
        // B2 W5 B1 W{1,2,4,5}
        for (int w : {0, 1, 3, 4})
            jobs.push_back({"B2W5B1_W" + to_string(w+1), makeMoves({{1,2},{4,1},{0,2},{w,1}})});
        // B2 W5 B4 W{1,2,3,4,5}
        for (int w : {0, 1, 2, 3, 4})
            jobs.push_back({"B2W5B4_W" + to_string(w+1), makeMoves({{1,2},{4,1},{3,2},{w,1}})});

        uint64_t lim = smoke ? 100000 : 40000000;
        unsigned workers = smoke ? 1u : min(hwThreads, 4u); // 4 workers x 256MB = 1 GB RAM (safe on any Colab!)
        size_t ttBits = smoke ? 18 : 25; // 32M slots = 256 MB per worker

        atomic<size_t> nextIdx{0};
        vector<thread> pool;
        for (unsigned t = 0; t < workers; ++t) {
            pool.emplace_back([&]() {
                while (true) {
                    size_t i = nextIdx.fetch_add(1);
                    if (i >= jobs.size()) break;
                    auto& j = jobs[i];
                    Solver sv;
                    sv.K = 9; sv.finiteMode = false; sv.evenEmpty = false;
                    sv.useZO = true; sv.useCanonical = true;
                    sv.nodeLimit = lim; sv.tt.init(ttBits);
                    auto t0 = chrono::steady_clock::now();
                    bool ok = sv.solve(j.root);
                    double ms = chrono::duration<double, milli>(chrono::steady_clock::now() - t0).count();
                    addRes({"Task3A_B2_K9", j.name, "Zone_K", 9,
                            sv.hitLimit ? "LIMIT" : (ok ? "SAFE!!" : "UNSAFE"),
                            sv.nodesVisited, sv.leafClaimHits, sv.leafZOHits, ms, ""});
                }
            });
        }
        for (auto& th : pool) th.join();
    }

    // ------------------------------------------------------------------
    // TASK 3B: Spine Diagnostic U(b) = ofCols [] ((BW)^b) [] [] [] (b=2,3,4)
    // Check if side moves B1, B3, B4, B5 close at K=9 or become immediate ClaimOdd/ZO leaves!
    // ------------------------------------------------------------------
    {
        uint64_t lim = smoke ? 100000 : 10000000;
        size_t ttBits = smoke ? 18 : 23; // 64 MB
        for (int b : {2, 3, 4}) {
            for (int bmv : {0, 2, 3, 4}) { // B1, B3, B4, B5
                bool foundSafe = false;
                for (int wmv : {0, 1, 2, 3, 4}) {
                    State s; memset(&s, 0, sizeof(s));
                    // col 2 (idx 1) has (BW)^b => length 2b (OPP at even 0,2,...,2b-2; ME at odd 1,3,...,2b-1)
                    for (int r = 0; r < 2*b; ++r) {
                        if (r % 2 == 0) s.opp[1] |= (1u << r);
                        else s.me[1] |= (1u << r);
                    }
                    s.h[1] = 2*b;
                    s.opp[bmv] |= (1u << s.h[bmv]); s.h[bmv]++;
                    if (s.h[wmv] >= 9) continue;
                    s.me[wmv] |= (1u << s.h[wmv]); s.h[wmv]++;

                    Solver sv;
                    sv.K = 9; sv.finiteMode = false; sv.evenEmpty = false;
                    sv.useZO = true; sv.useCanonical = true;
                    sv.nodeLimit = lim; sv.tt.init(ttBits);
                    int imm = sv.isLeaf(s);
                    auto t0 = chrono::steady_clock::now();
                    bool ok = sv.solve(s);
                    double ms = chrono::duration<double, milli>(chrono::steady_clock::now() - t0).count();
                    if (ok) {
                        addRes({"Task3B_SpineU", "U(" + to_string(b) + ")_B" + to_string(bmv+1) + "_W" + to_string(wmv+1),
                                "Zone_K", 9, "SAFE!!", sv.nodesVisited, sv.leafClaimHits, sv.leafZOHits, ms,
                                "immLeaf=" + to_string(imm)});
                        foundSafe = true;
                        break;
                    }
                }
                if (!foundSafe) {
                    addRes({"Task3B_SpineU", "U(" + to_string(b) + ")_B" + to_string(bmv+1),
                            "Zone_K", 9, "NONE_FOUND", 0, 0, 0, 0.0, ""});
                }
            }
        }
    }

    // Write summary.txt and results.json
    {
        ofstream stxt(outDir + "/summary.txt");
        ofstream sjson(outDir + "/results.json");
        stxt << "=== C4W5 Odd-Height Colab Experiment Summary ===\n";
        sjson << "[\n";
        for (size_t i = 0; i < results.size(); ++i) {
            auto& r = results[i];
            stxt << "[" << r.group << "] " << r.name << " (" << r.mode << "=" << r.K << "): "
                 << r.status << " | nodes=" << r.nodes << " | claim=" << r.claimLeaves
                 << " | zo=" << r.zoLeaves << " | " << fixed << setprecision(1) << r.ms << " ms"
                 << (r.extra.empty() ? "" : (" | " + r.extra)) << "\n";
            sjson << "  {\"group\":\"" << r.group << "\",\"name\":\"" << r.name
                  << "\",\"mode\":\"" << r.mode << "\",\"K\":" << r.K
                  << ",\"status\":\"" << r.status << "\",\"nodes\":" << r.nodes
                  << ",\"claimLeaves\":" << r.claimLeaves << ",\"zoLeaves\":" << r.zoLeaves
                  << ",\"ms\":" << fixed << setprecision(1) << r.ms
                  << ",\"extra\":\"" << r.extra << "\"}" << (i + 1 < results.size() ? "," : "") << "\n";
        }
        sjson << "]\n";
    }
    cout << "\nALL DONE! Saved summary.txt and results.json to: " << outDir << "\n";
    return 0;
}
