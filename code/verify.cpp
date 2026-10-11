// Exact verification of Erdős #848 for all N <= X.
//
// Claim(N): every A ⊆ [1,N] with ab+1 non-squarefree for all a,b in A (a=b allowed)
// has |A| <= c7(N) := #{n <= N : n ≡ 7 mod 25}.
//
// Vertices: V = {n <= X : n^2+1 non-squarefree}. Edges: ab+1 non-squarefree.
// omega(N) := clique number of G[V ∩ [1,N]]. omega(N) <= omega(N-1) + [N in V].
// c7 is a clique, so omega(N) >= c7(N). Induction: if omega(N-1) = c7(N-1) and
// N in V with N ≢ 7 (mod 25), then c7(N) = c7(N-1) and omega(N) = c7(N) unless there
// is a clique of size c7(N) inside Gamma_<(N) = {u in V, u < N, uN+1 non-squarefree}.
// So it suffices to check, for every v in V, v ≢ 7 (mod 25), v <= X:
//      no clique of size c7(v) in G[Gamma_<(v)].
// (For v ≡ 7 mod 25, c7 increases by 1, so the bound is automatic.)
#include <vector>
#include <thread>
#include <atomic>
#include <mutex>
#include <algorithm>
#include <numeric>
#include <cstdio>
#include <cstdlib>
using namespace std;
typedef unsigned long long u64;
typedef __uint128_t u128;

static vector<u64> primes;

static u64 c7(u64 N) { return N >= 7 ? (N - 7) / 25 + 1 : 0; }

// modular inverse of a mod m (gcd(a,m)=1), returns value in [0,m)
static long long inv_mod(long long a, long long m) {
    long long g = m, x = 0, x1 = 1, a1 = a % m;
    if (a1 < 0) a1 += m;
    long long b = a1;
    // extended Euclid on (b, m)
    long long old_r = b, r = m, old_s = 1, s = 0;
    while (r != 0) {
        long long q = old_r / r;
        long long t = old_r - q * r; old_r = r; r = t;
        t = old_s - q * s; old_s = s; s = t;
    }
    (void)g; (void)x; (void)x1;
    if (old_r != 1) return -1;
    long long res = old_s % m;
    if (res < 0) res += m;
    return res;
}

// independent slow check: is n non-squarefree? (trial division)
static bool nonsqfree_slow(u64 n) {
    for (u64 p : primes) {
        u64 pp = p * p;
        if (pp > n) break;
        if (n % pp == 0) return true;
    }
    return false;
}

int main(int argc, char** argv) {
    u64 X = argc > 1 ? strtoull(argv[1], 0, 10) : 2000;
    int nthreads = argc > 2 ? atoi(argv[2]) : 12;
    bool selfcheck = argc > 3 ? atoi(argv[3]) : 0;

    // primes up to X+1 (p^2 | ab+1 <= X^2+1 implies p <= X+1)
    {
        u64 L = X + 2;
        vector<char> comp(L + 1, 0);
        for (u64 i = 2; i <= L; i++) if (!comp[i]) { primes.push_back(i); for (u64 j = i * i; j <= L; j += i) comp[j] = 1; }
    }
    // V: n^2+1 non-squarefree. Sieve: p^2 | n^2+1 with p ≡ 1 mod 4 (p=2 impossible).
    vector<char> inV(X + 1, 0);
    for (u64 p : primes) {
        u64 pp = p * p;
        if (pp > X * X + 1) break;
        if (p % 4 != 1) continue;
        // find roots of n^2 ≡ -1 mod p^2 by brute force over n < p^2 is too slow for big p;
        // instead: roots mod p via search, then Hensel lift.
        u64 r = 0;
        for (u64 t = 2; t < p; t++) if ((t * t + 1) % p == 0) { r = t; break; }
        // Hensel: n = r + p*k, (r+pk)^2+1 ≡ r^2+1 + 2rpk ≡ 0 mod p^2 -> k ≡ -((r^2+1)/p) * inv(2r) mod p
        u64 c = ((r * r + 1) / p) % p;
        long long iv = inv_mod((long long)(2 * r % p), (long long)p);
        u64 k = ((p - c) % p) * (u64)iv % p;
        u64 root = r + p * k;
        u64 roots[2] = {root % pp, (pp - root % pp) % pp};
        for (u64 rt : roots) for (u64 n = rt; n <= X; n += pp) if (n >= 1) inV[n] = 1;
    }
    vector<u64> V;
    for (u64 n = 1; n <= X; n++) if (inV[n]) V.push_back(n);
    size_t m = V.size();
    vector<int> idx(X + 1, -1);
    for (size_t i = 0; i < m; i++) idx[V[i]] = (int)i;
    fprintf(stderr, "X=%llu |V|=%zu\n", X, m);

    // global adjacency as bitsets over V indices
    size_t GW = (m + 63) / 64;
    vector<vector<u64>> adj(m, vector<u64>(GW, 0));
    {
        atomic<size_t> next(0);
        auto work = [&]() {
            size_t i;
            while ((i = next++) < m) {
                u64 a = V[i];
                for (u64 p : primes) {
                    u64 pp = p * p;
                    if (pp > a * X + 1) break;
                    if (a % p == 0) continue;
                    long long iv = inv_mod((long long)(a % pp), (long long)pp);
                    u64 b0 = (pp - (u64)iv) % pp;  // b ≡ -a^{-1} mod p^2
                    for (u64 b = (b0 == 0 ? pp : b0); b <= X; b += pp)
                        if (inV[b]) { int j = idx[b]; adj[i][j >> 6] |= 1ULL << (j & 63); }
                }
            }
        };
        vector<thread> th; for (int t = 0; t < nthreads; t++) th.emplace_back(work); for (auto& t : th) t.join();
    }
    // symmetry + optional slow self-check of edges
    for (size_t i = 0; i < m; i++) for (size_t j = 0; j < m; j++) {
        bool e1 = adj[i][j >> 6] >> (j & 63) & 1, e2 = adj[j][i >> 6] >> (i & 63) & 1;
        if (e1 != e2) { fprintf(stderr, "asymmetry %zu %zu\n", i, j); return 1; }
        if (selfcheck) {
            bool s = nonsqfree_slow(V[i] * V[j] + 1);
            if (s != e1) { fprintf(stderr, "edge mismatch %llu %llu\n", V[i], V[j]); return 1; }
        }
        if (i == j && !e1) { fprintf(stderr, "loop missing %llu\n", V[i]); return 1; }
    }
    if (selfcheck) fprintf(stderr, "edge self-check passed\n");

    // decision: is there a clique of size K among local candidate set? (bitset BnB with greedy colouring)
    struct Solver {
        int n, W; vector<vector<u64>> g; long long nodes = 0;
        bool expand(vector<u64>& P, int size, int K) {
            nodes++;
            // greedy colouring of P in vertex order
            vector<int> order, col;
            vector<u64> U = P;
            int color = 0;
            int cnt = 0; for (auto w : U) cnt += __builtin_popcountll(w);
            if (size + cnt < K) return false;
            while (true) {
                bool any = false; for (auto w : U) if (w) { any = true; break; }
                if (!any) break;
                color++;
                vector<u64> Q = U;
                for (int wi = 0; wi < W; wi++) {
                    while (Q[wi]) {
                        int b = __builtin_ctzll(Q[wi]);
                        int v = wi * 64 + b;
                        // remove v and its neighbours from Q
                        U[wi] &= ~(1ULL << b);
                        Q[wi] &= ~(1ULL << b);
                        for (int k = wi; k < W; k++) Q[k] &= ~g[v][k];
                        order.push_back(v); col.push_back(color);
                    }
                }
            }
            for (int t = (int)order.size() - 1; t >= 0; t--) {
                if (size + col[t] < K) return false;
                int v = order[t];
                vector<u64> NP(W);
                for (int k = 0; k < W; k++) NP[k] = P[k] & g[v][k];
                if (size + 1 >= K) return true;
                if (expand(NP, size + 1, K)) return true;
                P[v >> 6] &= ~(1ULL << (v & 63));
            }
            return false;
        }
    };

    atomic<size_t> next(0);
    atomic<long long> totalNodes(0);
    atomic<int> failures(0);
    mutex mu;
    vector<pair<u64, long long>> hard;
    auto work = [&]() {
        size_t i;
        while ((i = next++) < m) {
            u64 v = V[i];
            if (v % 25 == 7) continue;
            int K = (int)c7(v);
            // local candidate set: u < v, u ~ v (u != v)
            vector<int> loc;
            for (size_t j = 0; j < i; j++) if (adj[i][j >> 6] >> (j & 63) & 1) loc.push_back((int)j);
            if ((int)loc.size() < K) continue;
            // order: by local degree descending (better colouring)
            int n = loc.size();
            vector<int> deg(n, 0);
            for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (a != b && (adj[loc[a]][loc[b] >> 6] >> (loc[b] & 63) & 1)) deg[a]++;
            vector<int> ord(n); iota(ord.begin(), ord.end(), 0);
            stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return deg[a] > deg[b]; });
            Solver S; S.n = n; S.W = (n + 63) / 64; S.g.assign(n, vector<u64>(S.W, 0));
            for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (a != b) {
                int ga = loc[ord[a]], gb = loc[ord[b]];
                if (adj[ga][gb >> 6] >> (gb & 63) & 1) S.g[a][b >> 6] |= 1ULL << (b & 63);
            }
            vector<u64> P(S.W, 0); for (int a = 0; a < n; a++) P[a >> 6] |= 1ULL << (a & 63);
            bool found = S.expand(P, 0, K);
            totalNodes += S.nodes;
            if (found) { failures++; lock_guard<mutex> lk(mu); fprintf(stderr, "COUNTEREXAMPLE candidate at v=%llu (clique of size %d in Gamma_<(v))\n", v, K); }
            if (S.nodes > 1000) { lock_guard<mutex> lk(mu); hard.push_back({v, S.nodes}); }
        }
    };
    vector<thread> th; for (int t = 0; t < nthreads; t++) th.emplace_back(work); for (auto& t : th) t.join();
    sort(hard.begin(), hard.end(), [](auto& a, auto& b) { return a.second > b.second; });
    fprintf(stderr, "total BnB nodes=%lld, hard cases(>1000 nodes)=%zu\n", (long long)totalNodes, hard.size());
    for (size_t t = 0; t < min<size_t>(hard.size(), 10); t++) fprintf(stderr, "  v=%llu nodes=%lld\n", hard[t].first, hard[t].second);
    printf("X=%llu failures=%d\n", X, (int)failures);
    return failures ? 2 : 0;
}
