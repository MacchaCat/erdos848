// Independent replay verifier for the incremental colouring log produced by incr.cpp.
//
// Squarefreeness is decided by complete factorisation (Miller-Rabin + Pollard-Brent rho),
// a method unrelated to the trial-division test used by incr.cpp. V is recomputed by a
// different sieve (Tonelli-Shanks roots mod p, Newton lifting to p^2), and cross-checked
// against factorisation of n^2+1 for small n.
//
// Checks: (1) new vertices appear in strictly increasing order and are exactly V ∩ [1,X];
// (2) type-1 ops open class #k with a vertex ≡ 7 (mod 25), so #classes after processing N is
//     c7(N); (3) every placement/move puts a vertex into a class none of whose current members
//     u satisfies "u*v+1 non-squarefree". Hence after each N the classes form a proper colouring
//     of G[V ∩ [1,N]] with c7(N) colours, so omega <= c7(N).
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <algorithm>
#include <unordered_map>
using namespace std;
typedef unsigned long long u64;
typedef __uint128_t u128;

static inline u64 mulmod(u64 a, u64 b, u64 m) { return (u128)a * b % m; }
static u64 powmod(u64 a, u64 e, u64 m) { u64 r = 1; a %= m; while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; } return r; }
static bool isPrime(u64 n) {
    if (n < 2) return false;
    for (u64 p : {2ULL, 3ULL, 5ULL, 7ULL, 11ULL, 13ULL, 17ULL, 19ULL, 23ULL, 29ULL, 31ULL, 37ULL}) { if (n % p == 0) return n == p; }
    u64 d = n - 1; int s = 0; while ((d & 1) == 0) { d >>= 1; s++; }
    for (u64 a : {2ULL, 3ULL, 5ULL, 7ULL, 11ULL, 13ULL, 17ULL, 19ULL, 23ULL, 29ULL, 31ULL, 37ULL}) {
        u64 x = powmod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool comp = true;
        for (int r = 1; r < s; r++) { x = mulmod(x, x, n); if (x == n - 1) { comp = false; break; } }
        if (comp) return false;
    }
    return true;
}
static u64 gcdu(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }
static u64 rho(u64 n) {
    if (n % 2 == 0) return 2;
    for (u64 c = 1;; c++) {
        u64 y = 2, x = 2, g = 1, q = 1, ys = 2; u64 m = 128, r = 1;
        auto f = [&](u64 v) { return (mulmod(v, v, n) + c) % n; };
        do {
            x = y; for (u64 i = 0; i < r; i++) y = f(y);
            u64 k = 0;
            while (k < r && g == 1) {
                ys = y;
                for (u64 i = 0; i < min(m, r - k); i++) { y = f(y); q = mulmod(q, x > y ? x - y : y - x, n); }
                g = gcdu(q, n); k += m;
            }
            r <<= 1;
        } while (g == 1);
        if (g == n) { do { ys = f(ys); g = gcdu(x > ys ? x - ys : ys - x, n); } while (g == 1); }
        if (g != n) return g;
    }
}
// returns true iff n has a repeated prime factor
static bool hasSquare(u64 n) {
    // strip small primes first
    static const u64 sp[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97};
    for (u64 p : sp) { if (n % p == 0) { n /= p; if (n % p == 0) return true; } }
    vector<u64> st; if (n > 1) st.push_back(n);
    vector<u64> pr;
    while (!st.empty()) {
        u64 m = st.back(); st.pop_back();
        if (m == 1) continue;
        if (isPrime(m)) { pr.push_back(m); continue; }
        // perfect square check
        u64 r = (u64)__builtin_sqrtl((long double)m); while (r * r > m) r--; while ((r + 1) * (r + 1) <= m) r++;
        if (r * r == m) return true;
        u64 d = rho(m);
        st.push_back(d); st.push_back(m / d);
    }
    sort(pr.begin(), pr.end());
    for (size_t i = 1; i < pr.size(); i++) if (pr[i] == pr[i - 1]) return true;
    return false;
}
static u64 c7(u64 N) { return N >= 7 ? (N - 7) / 25 + 1 : 0; }
// Tonelli-Shanks sqrt of a mod prime p (a is a QR)
static u64 tsqrt(u64 a, u64 p) {
    if (p == 2) return a & 1;
    u64 q = p - 1, s = 0; while ((q & 1) == 0) { q >>= 1; s++; }
    u64 z = 2; while (powmod(z, (p - 1) / 2, p) != p - 1) z++;
    u64 m = s, c = powmod(z, q, p), t = powmod(a, q, p), r = powmod(a, (q + 1) / 2, p);
    while (t != 1) { u64 i = 0, tt = t; while (tt != 1) { tt = mulmod(tt, tt, p); i++; } u64 b = c; for (u64 j = 0; j + i + 1 < m; j++) b = mulmod(b, b, p); m = i; c = mulmod(b, b, p); t = mulmod(t, c, p); r = mulmod(r, b, p); }
    return r;
}

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: replay LOG X\n"); return 1; }
    const char* path = argv[1]; u64 X = strtoull(argv[2], 0, 10);
    // V via Tonelli-Shanks + lifting
    vector<char> comp(X + 2, 0); vector<u64> primes;
    for (u64 i = 2; i <= X + 1; i++) { if (comp[i]) continue; primes.push_back(i); for (u64 j = i * i; j <= X + 1; j += i) comp[j] = 1; }
    vector<char> inV(X + 1, 0);
    for (u64 p : primes) {
        if (p % 4 != 1) continue;
        u64 r = tsqrt(p - 1, p), pp = p * p;
        // lift: R = r + p*t with (r+pt)^2 ≡ -1 mod p^2, solve by trying t (Newton): t = -(r^2+1)/p * (2r)^{-1} mod p
        u64 e = ((u128)r * r + 1) / p % p, inv2r = powmod(2 * r % p, p - 2, p);
        u64 t = mulmod((p - e) % p, inv2r, p);
        u64 R = (r + p * t) % pp;
        if (((u128)R * R + 1) % pp != 0) { fprintf(stderr, "lift failed p=%llu\n", p); return 1; }
        for (u64 rt : {R, pp - R}) for (u64 n = rt; n <= X; n += pp) inV[n] = 1;
    }
    for (u64 n = 1; n <= min<u64>(X, 200000); n++) if ((bool)inV[n] != hasSquare(n * n + 1)) { fprintf(stderr, "V check fail %llu\n", n); return 1; }

    FILE* f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "cannot open log\n"); return 1; }
    fseek(f, 0, SEEK_END); long long fsz = ftell(f); fseek(f, 0, SEEK_SET);
    if (fsz % 24 != 0) { fprintf(stderr, "log size not a multiple of 24\n"); return 1; }
    vector<vector<u64>> cls;
    unordered_map<u64, u64> where; where.reserve(X / 8);
    u64 rec[3], lastNew = 0, ops = 0, tests = 0;
    u64 nextV = 1; while (nextV <= X && !inV[nextV]) nextV++;
    auto checkInto = [&](u64 v, u64 c) {
        if (c >= cls.size()) { fprintf(stderr, "bad class index\n"); exit(1); }
        for (u64 u : cls[c]) { if (u == v) continue; tests++; if (hasSquare(u * v + 1)) { fprintf(stderr, "INVALID: %llu and %llu in class %llu (uv+1 non-squarefree)\n", u, v, c); exit(1); } }
    };
    while (fread(rec, sizeof rec, 1, f) == 1) {
        ops++;
        u64 t = rec[0], v = rec[1], c = rec[2];
        if (t == 1 || t == 2) {
            if (v > X || !inV[v] || v != nextV) { fprintf(stderr, "vertex order mismatch: got %llu expected %llu\n", v, nextV); return 1; }
            nextV++; while (nextV <= X && !inV[nextV]) nextV++;
            if (t == 1) {
                if (v % 25 != 7 || c != cls.size()) { fprintf(stderr, "bad open op\n"); return 1; }
                cls.push_back({v}); where[v] = c;
            } else {
                if (v % 25 == 7) { fprintf(stderr, "C7 vertex placed into old class\n"); return 1; }
                checkInto(v, c); cls[c].push_back(v); where[v] = c;
            }
            if (cls.size() != c7(v)) { fprintf(stderr, "class count %zu != c7(%llu)\n", cls.size(), v); return 1; }
        } else if (t == 3) {
            auto it = where.find(v); if (it == where.end()) { fprintf(stderr, "move of unknown vertex\n"); return 1; }
            u64 from = it->second; if (from == c) { fprintf(stderr, "null move\n"); return 1; }
            checkInto(v, c);
            auto& A = cls[from]; A.erase(find(A.begin(), A.end(), v));
            cls[c].push_back(v); it->second = c;
        } else { fprintf(stderr, "bad op type\n"); return 1; }
    }
    if (nextV <= X) { fprintf(stderr, "log ended early: next vertex %llu not placed\n", nextV); return 1; }
    printf("REPLAY OK: X=%llu ops=%llu classes=%zu (c7=%llu) tests=%llu\n", X, ops, cls.size(), c7(X), tests);
    return 0;
}
