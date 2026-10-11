// Empirical sanity check of the main terms used in n0_v2.py.
// For many witnesses b of each type, count exactly the sets that the casework bounds and compare
// with  C_main * N  (Sawhney-type main term computed for the actual b).  Ratios should be <= ~1.
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <random>
#include <algorithm>
using namespace std;
typedef unsigned long long u64;
static vector<unsigned> P;
static u64 icbrt(u64 n) { u64 r = cbrtl((long double)n); while (r*r*r > n) r--; while ((r+1)*(r+1)*(r+1) <= n) r++; return r; }
static bool nsf(u64 n) {
    u64 lim = icbrt(n);
    for (unsigned p : P) { if (p > lim) break; if (n % p == 0) { n /= p; if (n % p == 0) return true; } }
    if (n > 1) { u64 r = sqrtl((long double)n); while (r*r > n) r--; while ((r+1)*(r+1) <= n) r++; if (r*r == n) return true; }
    return false;
}
static bool isU1cand(u64 x) {   // x^2+1 divisible by p^2 for p ≡ 1 mod 4, p >= 13  (x not ≡ ±7 mod 25 assumed by caller)
    u64 n = x * x + 1;
    if (n % 25 == 0) return false;   // not used for A* (x ≢ ±7 mod 25 means 25 ∤ n)
    return nsf(n);
}
static double mainSaw(u64 q, u64 b) {  // 1 - prod_{p ∤ qb} (1-1/p^2) over p <= 1e5
    double pr = 1;
    for (unsigned p : P) { if (p > 100000) break; if ((q % p) && (b % p)) pr *= 1 - 1.0 / p / p; }
    return 1 - pr;
}
int main(int argc, char** argv) {
    u64 N = strtoull(argv[1], 0, 10); int trials = atoi(argv[2]);
    { u64 L = 2000000; vector<char> c(L + 1, 0); for (u64 i = 2; i <= L; i++) if (!c[i]) { P.push_back(i); for (u64 j = i*i; j <= L; j += i) c[j] = 1; } }
    mt19937_64 rng(7);
    auto inV = [&](u64 x) { return nsf(x * x + 1); };
    auto randV = [&](auto pred) { while (true) { u64 x = 1 + rng() % N; if (pred(x) && inV(x)) return x; } };
    auto mod25 = [](u64 x) { return x % 25; };
    double worst[8] = {0};
    for (int t = 0; t < trials; t++) {
        // (1) I.b: b in A7 sieving class 18 mod 25 ; compare with (1/25)(1-prod_{p∤25b})
        u64 b = randV([&](u64 x) { return mod25(x) == 7; });
        u64 cnt = 0; for (u64 a = 18; a <= N; a += 25) if (nsf(a * b + 1)) cnt++;
        worst[0] = max(worst[0], cnt / (N / 25.0 * mainSaw(25, b)));
        // (2) II: even b in A*, classes 7,18 mod 25 ; main (2/25)(1-prod_{p∤50b...}) (2 | b so excluded)
        b = randV([&](u64 x) { return x % 2 == 0 && mod25(x) != 7 && mod25(x) != 18; });
        cnt = 0; for (u64 a = 7; a <= N; a += 25) { if (nsf(a * b + 1)) cnt++; if (a + 11 <= N && nsf((a + 11) * b + 1)) cnt++; }
        worst[1] = max(worst[1], cnt / (2 * N / 25.0 * mainSaw(25, b)));
        // (3) Lemma C: A*-candidates compatible with even b: x mod 25 ∉ {7,18}, U1, nsf(xb+1)
        cnt = 0; u64 tot = 0;
        for (u64 x = 1; x <= N; x++) { u64 r = mod25(x); if (r == 7 || r == 18) continue; if (!isU1cand(x)) continue; tot++; if (x == b || nsf(x * b + 1)) cnt++; }
        worst[2] = max(worst[2], (double)cnt / N);   // compare with C_lemC ~ printed by n0_v2
        // (4) III: b ≡ 1 mod 4 odd in A*; classes 57,93 mod 100 sieved (excl 2,5)
        b = randV([&](u64 x) { return x % 4 == 1 && mod25(x) != 7 && mod25(x) != 18; });
        cnt = 0; for (u64 a = 57; a <= N; a += 100) { if (nsf(a * b + 1)) cnt++; if (a + 36 <= N && nsf((a + 36) * b + 1)) cnt++; }
        worst[3] = max(worst[3], cnt / (2 * N / 100.0 * mainSaw(100, b)));
        // (5) the 'free' claim: classes 7,43 mod 100 with b ≡ 1 mod 4: all compatible (4 | ab+1)
        bool allfree = true; for (u64 a = 7; a <= N && allfree; a += 100) if ((a * b + 1) % 4) allfree = false;
        for (u64 a = 43; a <= N && allfree; a += 100) if ((a * b + 1) % 4) allfree = false;
        if (!allfree) { printf("free-class claim FAILED\n"); return 1; }
        // (6) III.1 / III.2.b: even classes 32,82,18,68 mod 100 sieved by b≡1 (excl 2,5)
        cnt = 0; for (u64 r0 : {32ULL, 82ULL, 18ULL, 68ULL}) for (u64 a = r0; a <= N; a += 100) if (nsf(a * b + 1)) cnt++;
        worst[4] = max(worst[4], cnt / (4 * N / 100.0 * mainSaw(100, b)));
        // (7) A18 (4 classes mod 100) sieved by even b' in A7 (excl 2,5)
        u64 b2 = randV([&](u64 x) { return x % 2 == 0 && mod25(x) == 7; });
        cnt = 0; for (u64 a = 18; a <= N; a += 25) if (nsf(a * b2 + 1)) cnt++;
        worst[5] = max(worst[5], cnt / (N / 25.0 * mainSaw(50, b2)));
        // (8) Lemma B q=100: A* ⊆ 1 mod 4: count of x ≡ 1 mod 4, x mod 25 ∉{7,18}, U1-cand ; vs (23/100)*0.02735
        if (t == 0) { u64 c8 = 0; for (u64 x = 1; x <= N; x += 4) { u64 r = mod25(x); if (r == 7 || r == 18) continue; if (isU1cand(x)) c8++; } worst[6] = c8 / (23.0 / 100 * 0.0273467 * N); }
    }
    printf("N=%llu trials=%d\n", N, trials);
    printf(" (1) I.b  A18 by b∈A7           max actual/main = %.4f\n", worst[0]);
    printf(" (2) II   A7∪A18 by even b      max actual/main = %.4f\n", worst[1]);
    printf(" (3) II   Lemma C set |.|/N     max = %.5f  (compare 25*C_lemC/25)\n", worst[2]);
    printf(" (4) III  57,93 by b≡1(4)       max actual/main = %.4f\n", worst[3]);
    printf(" (6) III  even classes by b≡1   max actual/main = %.4f\n", worst[4]);
    printf(" (7) III  A18 by even b'∈A7     max actual/main = %.4f\n", worst[5]);
    printf(" (8) LemB q=100 one class mod 4 actual/main      = %.4f\n", worst[6]);
    return 0;
}
