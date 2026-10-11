// Linear-time incremental colouring for Erdős #848, with an operation log for independent replay.
//
// Invariant after processing every n <= N (N = 1..X): the classes partition V ∩ [1,N] into exactly
// c7(N) sets, and inside each class uv+1 is squarefree for all u != v. Hence omega(G_N) <= c7(N).
//
// Operations (logged as binary records of three u64: type, a, b):
//   type 1: open a new class with C7-vertex a  (class index = number of classes so far)
//   type 2: place vertex a into class b
//   type 3: move vertex a into class b (from its current class)
// The log is replayed and re-verified by replay.cpp using an independent squarefree routine.
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <algorithm>
#include <random>
using namespace std;
typedef unsigned long long u64;
typedef __uint128_t u128;

static vector<unsigned> P;
static u64 nTests = 0;
static inline u64 isqrt64(u64 n) { u64 r = (u64)sqrtl((long double)n); while (r * r > n) r--; while ((r + 1) * (r + 1) <= n) r++; return r; }
static inline u64 icbrt64(u64 n) { u64 r = (u64)cbrtl((long double)n); while (r * r * r > n) r--; while ((r + 1) * (r + 1) * (r + 1) <= n) r++; return r; }
static bool nonsqfree(u64 n) {
    nTests++;
    // quick small squares
    if ((n & 3) == 0 || n % 9 == 0 || n % 25 == 0 || n % 49 == 0) return true;
    u64 lim = icbrt64(n);
    for (unsigned p : P) {
        if (p > lim) break;
        if (n % p == 0) { n /= p; if (n % p == 0) return true; }
    }
    if (n > 1) { u64 r = isqrt64(n); if (r * r == n) return true; }
    return false;
}
static long long inv_mod(long long a, long long m) {
    long long old_r = ((a % m) + m) % m, r = m, old_s = 1, s = 0;
    while (r) { long long q = old_r / r, t = old_r - q * r; old_r = r; r = t; t = old_s - q * s; old_s = s; s = t; }
    long long res = old_s % m; if (res < 0) res += m; return res;
}
static inline u64 c7(u64 N) { return N >= 7 ? (N - 7) / 25 + 1 : 0; }

int main(int argc, char** argv) {
    u64 X = strtoull(argv[1], 0, 10);
    const char* logpath = argc > 2 ? argv[2] : nullptr;
    FILE* lg = logpath ? fopen(logpath, "wb") : nullptr;
    auto LOG = [&](u64 t, u64 a, u64 b) { if (lg) { u64 r[3] = {t, a, b}; fwrite(r, sizeof r, 1, lg); } };

    // primes up to X+1 via bit sieve (odd only)
    {
        u64 L = X + 2;
        vector<unsigned char> bits(L / 16 + 2, 0);
        auto isComp = [&](u64 i) { return bits[i >> 4] >> ((i >> 1) & 7) & 1; };
        P.push_back(2);
        for (u64 i = 3; i <= L; i += 2) {
            if (isComp(i)) continue;
            P.push_back((unsigned)i);
            if (i * i <= L) for (u64 j = i * i; j <= L; j += 2 * i) bits[j >> 4] |= 1 << ((j >> 1) & 7);
        }
    }
    fprintf(stderr, "primes: %zu\n", P.size());
    vector<unsigned char> inV(X / 8 + 1, 0);
    auto setV = [&](u64 n) { inV[n >> 3] |= 1 << (n & 7); };
    auto getV = [&](u64 n) { return inV[n >> 3] >> (n & 7) & 1; };
    for (u64 p : P) {
        if (p % 4 != 1) continue;
        u64 pp = p * p, r = 0;
        for (u64 g = 2;; g++) {
            u64 e = (p - 1) / 4, b = g % p, acc = 1;
            while (e) { if (e & 1) acc = (u128)acc * b % p; b = (u128)b * b % p; e >>= 1; }
            if ((u128)acc * acc % p == p - 1) { r = acc; break; }
        }
        u64 c = (((u128)r * r + 1) / p) % p;
        u64 iv = inv_mod((long long)(2 * r % p), (long long)p);
        u64 k = (u128)((p - c) % p) * iv % p;
        u64 root = (r + p * k) % pp;
        u64 roots[2] = {root, pp - root};
        for (u64 rt : roots) for (u64 n = rt; n <= X; n += pp) if (n >= 1) setV(n);
    }
    for (u64 n = 1; n <= min<u64>(X, 300000); n++) if ((bool)getV(n) != nonsqfree(n * n + 1)) { fprintf(stderr, "V mismatch %llu\n", n); return 1; }
    fprintf(stderr, "V built\n");

    vector<vector<u64>> cls;
    vector<int> has18;            // does class contain a vertex ≡ 18 mod 25
    vector<u64> free18;           // classes without a C18 vertex (unordered set)
    vector<long long> posFree;    // position of class in free18, or -1
    auto markFree = [&](size_t c, bool fr) {
        if (fr && posFree[c] < 0) { posFree[c] = free18.size(); free18.push_back(c); }
        if (!fr && posFree[c] >= 0) { size_t i = posFree[c]; size_t last = free18.back(); free18[i] = last; posFree[last] = i; free18.pop_back(); posFree[c] = -1; }
    };
    mt19937_64 rng(2026);
    // conflicts of vertex v with class c (excluding vertex 'skip'); returns count (capped at 2), who = a conflicting vertex
    auto conf = [&](u64 v, size_t c, u64 skip, u64& who) {
        int cnt = 0;
        for (u64 u : cls[c]) { if (u == skip) continue; if (nonsqfree(u * v + 1)) { who = u; if (++cnt >= 2) return 2; } }
        return cnt;
    };
    auto place = [&](u64 v, size_t c) { cls[c].push_back(v); if (v % 25 == 18) { has18[c] = 1; markFree(c, false); } LOG(2, v, c); };
    auto moveTo = [&](u64 u, size_t from, size_t to) {
        auto& A = cls[from]; A.erase(find(A.begin(), A.end(), u));
        cls[to].push_back(u);
        if (u % 25 == 18) { has18[from] = 0; markFree(from, true); has18[to] = 1; markFree(to, false); }
        LOG(3, u, to);
    };
    u64 nV = 0, r1 = 0, r2 = 0, full = 0;
    vector<pair<size_t, u64>> single;
    for (u64 v = 1; v <= X; v++) {
        if (!getV(v)) continue;
        nV++;
        if (v % 25 == 7) { cls.push_back({v}); has18.push_back(0); posFree.push_back(-1); markFree(cls.size() - 1, true); LOG(1, v, cls.size() - 1); continue; }
        size_t K = cls.size();
        if (K == 0) { printf("STUCK (no class) v=%llu\n", v); return 2; }
        bool placed = false; single.clear();
        bool is18 = v % 25 == 18;
        // phase 0 (C18 arrivals): try the C18-free classes first
        if (is18) for (size_t i = 0; i < free18.size() && !placed; i++) {
            size_t c = free18[i]; u64 who = 0; int k = conf(v, c, 0, who);
            if (k == 0) { place(v, c); placed = true; }
        }
        // phase 1: random classes
        for (int t = 0; t < 48 && !placed; t++) {
            size_t c = rng() % K; u64 who = 0; int k = conf(v, c, 0, who);
            if (k == 0) { place(v, c); placed = true; }
            else if (k == 1) single.push_back({c, who});
        }
        // phase 2: move the unique conflicting member u of class c elsewhere
        for (size_t s = 0; s < single.size() && !placed; s++) {
            size_t c = single[s].first; u64 u = single[s].second;
            if (u % 25 == 7) continue;  // C7 anchors cannot move (every class has one)
            if (u % 25 == 18) {
                for (size_t i = 0; i < free18.size() && !placed; i++) {
                    size_t c2 = free18[i]; if (c2 == c) continue;
                    u64 who = 0; if (conf(u, c2, 0, who) == 0) { moveTo(u, c, c2); place(v, c); placed = true; r1++; }
                }
            } else {
                for (int t = 0; t < 48 && !placed; t++) {
                    size_t c2 = rng() % K; if (c2 == c) continue;
                    u64 who = 0; if (conf(u, c2, 0, who) == 0) { moveTo(u, c, c2); place(v, c); placed = true; r1++; }
                }
            }
        }
        // phase 3: two-step chains  v -> c (evict u) ; u -> c2 (evict w) ; w -> c3
        for (size_t s = 0; s < single.size() && !placed; s++) {
            size_t c = single[s].first; u64 u = single[s].second;
            if (u % 25 == 7) continue;
            for (int t = 0; t < 32 && !placed; t++) {
                size_t c2 = rng() % K; if (c2 == c) continue;
                u64 w = 0; if (conf(u, c2, 0, w) != 1) continue;
                if (w % 25 == 7) continue;
                if (u % 25 == 18 && w % 25 != 18 && has18[c2]) continue;  // c2 would hold two C18
                for (int t3 = 0; t3 < 48 && !placed; t3++) {
                    size_t c3;
                    if (w % 25 == 18) { if (free18.empty()) break; c3 = free18[rng() % free18.size()]; }
                    else c3 = rng() % K;
                    if (c3 == c || c3 == c2) continue;
                    u64 who = 0; if (conf(w, c3, 0, who) != 0) continue;
                    moveTo(w, c2, c3); moveTo(u, c, c2); place(v, c); placed = true; r2++;
                }
            }
        }
        // phase 4: exhaustive fallback (one-step moves over all classes)
        if (!placed) {
            full++;
            single.clear();
            for (size_t c = 0; c < K && !placed; c++) {
                u64 who = 0; int k = conf(v, c, 0, who);
                if (k == 0) { place(v, c); placed = true; } else if (k == 1) single.push_back({c, who});
            }
            for (size_t s = 0; s < single.size() && !placed; s++) {
                size_t c = single[s].first; u64 u = single[s].second;
                if (u % 25 == 7) continue;
                for (size_t c2 = 0; c2 < K && !placed; c2++) {
                    if (c2 == c) continue;
                    u64 who = 0; if (conf(u, c2, 0, who) == 0) { moveTo(u, c, c2); place(v, c); placed = true; r1++; }
                }
            }
        }
        if (!placed) { printf("STUCK at v=%llu (classes=%zu)\n", v, K); if (lg) fclose(lg); return 2; }
        if ((nV & ((1 << 21) - 1)) == 0) fprintf(stderr, "  v=%llu nV=%llu r1=%llu r2=%llu full=%llu tests=%llu\n", v, nV, r1, r2, full, nTests);
    }
    size_t mx = 0; for (auto& c : cls) mx = max(mx, c.size());
    printf("X=%llu |V|=%llu classes=%zu (c7=%llu) r1=%llu r2=%llu full=%llu tests=%llu maxClass=%zu OK\n", X, nV, cls.size(), c7(X), r1, r2, full, nTests, mx);
    if (lg) fclose(lg);
    return 0;
}
