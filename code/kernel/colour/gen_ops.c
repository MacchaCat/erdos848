/* Static anchored colouring test: class j is anchored at a_j = 25 j + 7 and may only contain
 * vertices v >= a_j; members pairwise have u v + 1 squarefree.  Vertices: v <= N0 with v^2+1
 * not squarefree.  Greedy first-fit in increasing v.
 *   ./greedy_static N0 > classes.txt   (one class per line: members)  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64; typedef __uint128_t u128;
static int *SP; static int nSP;   /* primes <= 10000 */
static int sqf(u64 n) {           /* n <= 1e12 */
  for (int i = 0; i < nSP; i++) { u64 p = SP[i]; if (p * p * p > n) break;
    if (n % p == 0) { n /= p; if (n % p == 0) return 0; } }
  if (n > 1) { u64 r = (u64)__builtin_sqrtl((long double)n); while (r * r > n) r--; while ((r + 1) * (r + 1) <= n) r++; if (r * r == n) return 0; }
  return 1;
}
static u64 pw(u64 b, u64 e, u64 m) { u64 r = 1 % m; b %= m; while (e) { if (e & 1) r = (u128)r * b % m; b = (u128)b * b % m; e >>= 1; } return r; }
int main(int argc, char **argv) {
  long N0 = atol(argv[1]);
  SP = malloc(sizeof(int) * 2000); nSP = 0;
  for (int n = 2; n <= 10000; n++) { int ok = 1; for (int d = 2; d * d <= n; d++) if (n % d == 0) { ok = 0; break; } if (ok) SP[nSP++] = n; }
  /* vertices via roots of -1 mod p^2 */
  char *isP = calloc(N0 + 2, 1); for (long i = 2; i <= N0 + 1; i++) isP[i] = 1;
  for (long i = 2; i * i <= N0 + 1; i++) if (isP[i]) for (long j = i * i; j <= N0 + 1; j += i) isP[j] = 0;
  char *V = calloc(N0 + 1, 1);
  for (long p = 5; p <= N0 + 1; p += 4) if (isP[p]) {
    u64 r0 = 0; for (u64 g = 2; g < (u64)p; g++) { u64 x = pw(g, (p - 1) / 4, p); if ((u128)x * x % p == (u64)p - 1) { r0 = x; break; } }
    u64 c = ((r0 * r0 + 1) / p) % p, inv = pw(2 * r0 % p, p - 2, p), k = (p - c) % p * inv % p;
    u64 P2 = (u64)p * p, r = (r0 + p * k) % P2;
    if (((u128)r * r + 1) % P2) { fprintf(stderr, "bad root %ld\n", p); return 1; }
    { static FILE *rf = NULL; if (!rf) rf = fopen("roots.txt", "w"); fprintf(rf, "%ld %llu\n", p, (unsigned long long)r); fflush(rf); }
    for (u64 v = r; v <= (u64)N0; v += P2) V[v] = 1;
    for (u64 v = P2 - r; v <= (u64)N0; v += P2) V[v] = 1;
  }
  long nV = 0; for (long v = 1; v <= N0; v++) nV += V[v];
  long nC = (N0 + 18) / 25 + 10;
  long **cls = malloc(sizeof(long *) * nC); int *sz = calloc(nC, sizeof(int)), *cap = calloc(nC, sizeof(int));
  long *e18 = malloc(sizeof(long) * nC);          /* the 18-element of each class or 0 */
  long cnt = 0, L = 1; int nr = 0;
  #define ADD(j, v) do { if (sz[j] == cap[j]) { cap[j] = cap[j] ? 2 * cap[j] : 4; cls[j] = realloc(cls[j], sizeof(long) * cap[j]); } cls[j][sz[j]++] = (v); } while (0)
  /* compatible with all members of class j except `skip` */
  #define COMPAT(j, v, skip) ({ int ok_ = 1; for (int t_ = 0; t_ < sz[j] && ok_; t_++) if (cls[j][t_] != (skip) && !sqf((u64)cls[j][t_] * (v) + 1)) ok_ = 0; ok_; })
  long *prevc = malloc(sizeof(long) * nC), *via = malloc(sizeof(long) * nC); char *seen = malloc(nC);
  for (long v = 1; v <= N0; v++) if (V[v]) {
    int placed = 0;
    if (v % 25 == 7) { cls[cnt] = NULL; cap[cnt] = 0; sz[cnt] = 0; e18[cnt] = 0; ADD(cnt, v); printf("N %ld\n", v); cnt++; continue; }
    for (long j = 0; j < cnt && !placed; j++) {
      if (v % 25 == 18 && e18[j]) continue;
      if (COMPAT(j, v, -1)) { ADD(j, v); if (v % 25 == 18) e18[j] = v; placed = 1; printf("P %ld %ld\n", v, j); }
    }
    if (placed) continue;
    if (v % 25 != 18) { fprintf(stderr, "FAILED (non-18) at %ld\n", v); return 1; }
    /* augmenting path: BFS over classes; from class c we may move its 18-element w to class d
       (d compatible with w ignoring d's own 18-element which then moves on) */
    memset(seen, 0, cnt);
    long *queue = malloc(sizeof(long) * cnt); long qh = 0, qt = 0, found = -1;
    /* start: classes compatible with v ignoring their 18-element */
    for (long j = 0; j < cnt; j++) if (e18[j] && COMPAT(j, v, e18[j])) { seen[j] = 1; prevc[j] = -1; queue[qt++] = j; }
    while (qh < qt && found < 0) {
      long c = queue[qh++]; long w = e18[c];
      for (long d = 0; d < cnt && found < 0; d++) {
        if (seen[d]) continue;
        if (!e18[d]) { if (COMPAT(d, w, -1)) { prevc[d] = c; seen[d] = 1; found = d; } }
        else if (COMPAT(d, w, e18[d])) { seen[d] = 1; prevc[d] = c; queue[qt++] = d; }
      }
    }
    free(queue);
    if (found < 0) { fprintf(stderr, "FAILED (no augmenting path) at %ld\n", v); return 1; }
    /* apply: along the path d <- c <- ... <- start: move e18[c] into d */
    long d = found, len = 0;
    while (d >= 0) {
      long c = prevc[d];
      long w = (c >= 0) ? e18[c] : v;
      /* remove old 18 of d (if any) — it moves further along the path (already handled) */
      if (e18[d] && c >= 0 && 0) {}
      if (c < 0) {   /* d is a start class: v goes into d, its old 18 moved before */
        if (e18[d]) { int wq = 0; for (int t = 0; t < sz[d]; t++) if (cls[d][t] != e18[d]) cls[d][wq++] = cls[d][t]; sz[d] = wq; }
        ADD(d, v); e18[d] = v; printf("P %ld %ld\n", v, d); break;
      }
      if (e18[d]) { int wq = 0; for (int t = 0; t < sz[d]; t++) if (cls[d][t] != e18[d]) cls[d][wq++] = cls[d][t]; sz[d] = wq; }
      ADD(d, w); e18[d] = w; len++; printf("M %ld %ld %ld\n", w, c, d);
      d = c;
    }
    nr++; L = v;
  }
  fprintf(stderr, "classes %ld, augmentations %d\n", cnt, nr);
  return 0;

}
