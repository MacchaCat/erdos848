/* cert.c — exact interval certificate for the lowered analytic threshold (C + GMP + OpenMP).
 *
 * Port of exact.py with the review fix of Lemma C (review_fix.py).  Floating point is used only
 * to CHOOSE parameters (the cut-offs Y, Y' and Pareto pruning of table choices), and for one
 * pre-selection inside a maximum (structures whose float value is below (1-1e-6)*max are not
 * evaluated exactly; float values have relative error < 1e-12, see ex_exact).  Every bound that
 * enters the comparison with (N_lo - 6)/25 is evaluated in exact rational arithmetic (mpq).
 *
 *   ./cert table.txt intervals.txt > out.txt
 *
 * intervals.txt: one interval per line,
 *   Nlo Nhi  [z dA zB dB z1 z2 dC pc pBf] x 5     (cases I.b II III.1 III.2.a III.2.b)
 *   d* = 0 means full inclusion-exclusion; pc = 0 means the default max(2000, 0.3 sqrt N).
 * out: Nlo Nhi ratio_1..ratio_5 ok|FAIL, then a coverage summary.
 */
#include <gmp.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

typedef long long ll;
typedef __int128 i128;

#define PMAX 20000000LL
#define NMAX 160000000LL
#define NCASE 5

/* ---------------------------------------------------------------- primes */
static int *PR, nPR, *P1, nP1;
static i128 *SPI, *SP1I;   /* prefix sums of ceil(SCALE / p^2) */
static double *SPF, *SP1F; /* float prefix sums of 1/p^2 */
static i128 SCALE;
static mpz_t SCALEZ;

static void sieve(void) {
  char *s = calloc(PMAX + 1, 1);
  for (ll i = 2; i * i <= PMAX; i++)
    if (!s[i]) for (ll j = i * i; j <= PMAX; j += i) s[j] = 1;
  nPR = 0; for (ll i = 2; i <= PMAX; i++) if (!s[i]) nPR++;
  PR = malloc(sizeof(int) * nPR); int k = 0;
  for (ll i = 2; i <= PMAX; i++) if (!s[i]) PR[k++] = (int)i;
  free(s);
  nP1 = 0; for (int i = 0; i < nPR; i++) if (PR[i] % 4 == 1 && PR[i] >= 13) nP1++;
  P1 = malloc(sizeof(int) * nP1); k = 0;
  for (int i = 0; i < nPR; i++) if (PR[i] % 4 == 1 && PR[i] >= 13) P1[k++] = PR[i];
  SCALE = 1; for (int i = 0; i < 36; i++) SCALE *= 10;
  mpz_init_set_str(SCALEZ, "1000000000000000000000000000000000000", 10);
  SPI = malloc(sizeof(i128) * (nPR + 1)); SPF = malloc(sizeof(double) * (nPR + 1));
  SPI[0] = 0; SPF[0] = 0;
  for (int i = 0; i < nPR; i++) {
    i128 p2 = (i128)PR[i] * PR[i];
    SPI[i + 1] = SPI[i] + (SCALE + p2 - 1) / p2;
    SPF[i + 1] = SPF[i] + 1.0 / ((double)PR[i] * PR[i]);
  }
  SP1I = malloc(sizeof(i128) * (nP1 + 1)); SP1F = malloc(sizeof(double) * (nP1 + 1));
  SP1I[0] = 0; SP1F[0] = 0;
  for (int i = 0; i < nP1; i++) {
    i128 p2 = (i128)P1[i] * P1[i];
    SP1I[i + 1] = SP1I[i] + (SCALE + p2 - 1) / p2;
    SP1F[i + 1] = SP1F[i] + 1.0 / ((double)P1[i] * P1[i]);
  }
}
/* number of elements <= v (bisect_right) */
static int upto(const int *a, int n, ll v) {
  int lo = 0, hi = n;
  while (lo < hi) { int m = (lo + hi) / 2; if ((ll)a[m] <= v) lo = m + 1; else hi = m; }
  return lo;
}
static void z_set_i128(mpz_t z, i128 v) {
  int neg = v < 0; if (neg) v = -v;
  mpz_set_ui(z, (unsigned long)(v >> 64)); mpz_mul_2exp(z, z, 64);
  mpz_add_ui(z, z, (unsigned long)(v & 0xFFFFFFFFFFFFFFFFULL));
  if (neg) mpz_neg(z, z);
}
/* exact upper bound for sum_{lo < p <= hi, p in list} 1/p^2 (tail beyond PMAX: 1/(PMAX-1)) */
static void s2q(mpq_t out, ll lo, ll hi, int which) {
  mpq_set_ui(out, 0, 1);
  if (hi <= lo) return;
  const int *L = which ? P1 : PR; int n = which ? nP1 : nPR; const i128 *S = which ? SP1I : SPI;
  int a = upto(L, n, lo), b = upto(L, n, hi < PMAX ? hi : PMAX);
  if (b > a) { mpz_t t; mpz_init(t); z_set_i128(t, S[b] - S[a]);
    mpq_set_num(out, t); mpq_set_den(out, SCALEZ); mpq_canonicalize(out); mpz_clear(t); }
  if (hi > PMAX) { mpq_t t; mpq_init(t); mpq_set_ui(t, 1, PMAX - 1); mpq_add(out, out, t); mpq_clear(t); }
}
static double s2f(double lo, double hi, int which) {
  if (hi <= lo) return 0;
  const int *L = which ? P1 : PR; int n = which ? nP1 : nPR; const double *S = which ? SP1F : SPF;
  int a = upto(L, n, (ll)lo), b = upto(L, n, hi < PMAX ? (ll)hi : PMAX);
  double r = S[b] - S[a];
  if (hi > PMAX) r += 1.0 / (PMAX - 1);
  return r;
}
static int warned_cnt = 0;
/* #{p in list : lo < p <= hi}; beyond the table a valid crude bound (odd numbers) */
static ll cntp(ll lo, ll hi, int which) {
  if (hi <= lo) return 0;
  const int *L = which ? P1 : PR; int n = which ? nP1 : nPR;
  if (hi <= PMAX) return upto(L, n, hi) - upto(L, n, lo);
  if (!warned_cnt) { warned_cnt = 1; fprintf(stderr, "warning: EXACT prime count beyond PMAX (crude bound used)\n"); }
  ll base = (lo < PMAX) ? (n - upto(L, n, lo)) : 0;
  ll from = lo > PMAX ? lo : PMAX;
  return base + (hi - from) / 2 + 1;
}
/* float path (parameter choice only) */
static ll cntf(ll lo, ll hi, int which) {
  if (hi <= lo) return 0;
  const int *L = which ? P1 : PR; int n = which ? nP1 : nPR;
  if (hi <= PMAX) return upto(L, n, hi) - upto(L, n, lo);
  ll base = (lo < PMAX) ? (n - upto(L, n, lo)) : 0;
  ll from = lo > PMAX ? lo : PMAX;
  return base + (hi - from) / 2 + 1;
}
static ll isqrtll(ll n) { ll r = (ll)sqrtl((long double)n); while (r * r > n) r--; while ((r + 1) * (r + 1) <= n) r++; return r; }

/* ---------------------------------------------------------------- inclusion-exclusion */
/* vals: ncls / p^2 for p in ps[0..k).  depth 0 or >= k: full IE.  Else Bonferroni at odd depth. */
static void ie_q(mpq_t main, ll *err, const int *ps, int k, int ncls, int depth) {
  mpq_t v, t; mpq_inits(v, t, NULL);
  if (depth <= 0 || depth >= k) {
    mpq_set_ui(t, 1, 1);   /* product of (1 - v) */
    for (int i = 0; i < k; i++) { mpq_set_ui(v, ncls, (unsigned long)ps[i] * ps[i]); mpq_canonicalize(v);
      mpq_t w; mpq_init(w); mpq_set_ui(w, 1, 1); mpq_sub(w, w, v); mpq_mul(t, t, w); mpq_clear(w); }
    mpq_set_ui(main, 1, 1); mpq_sub(main, main, t);
    ll e = 1; for (int i = 0; i < k; i++) e *= (1 + ncls); *err = e - 1;
  } else {
    mpq_t *e = malloc(sizeof(mpq_t) * (depth + 1));
    for (int j = 0; j <= depth; j++) mpq_init(e[j]);
    mpq_set_ui(e[0], 1, 1);
    for (int i = 0; i < k; i++) {
      mpq_set_ui(v, ncls, (unsigned long)ps[i] * ps[i]); mpq_canonicalize(v);
      for (int j = depth; j >= 1; j--) { mpq_mul(t, e[j - 1], v); mpq_add(e[j], e[j], t); }
    }
    mpq_set_ui(main, 0, 1);
    for (int j = 1; j <= depth; j++) { if (j & 1) mpq_add(main, main, e[j]); else mpq_sub(main, main, e[j]); }
    ll er = 0;
    for (int j = 1; j <= depth; j++) { ll c = 1; for (int i = 0; i < j; i++) c = c * (k - i) / (i + 1);
      ll pw = 1; for (int i = 0; i < j; i++) pw *= ncls; er += c * pw; }
    *err = er;
    for (int j = 0; j <= depth; j++) mpq_clear(e[j]);
    free(e);
  }
  mpq_clears(v, t, NULL);
}

/* ---------------------------------------------------------------- Lemma A'' / B per class */
/* excl: bit0 = exclude 2, bit1 = exclude 5 */
static void restricted_q(mpq_t out, int T, int q, int excl, int z, ll pc, const mpq_t L, int dA) {
  int ps[64], k = 0;
  for (int i = 0; i < nPR && PR[i] <= z; i++) {
    if ((excl & 1) && PR[i] == 2) continue;
    if ((excl & 2) && PR[i] == 5) continue;
    ps[k++] = PR[i];
  }
  mpq_t main, s, a; ll err; mpq_inits(main, s, a, NULL);
  ie_q(main, &err, ps, k, 1, dA);
  s2q(s, z, pc, 0);
  mpq_add(a, main, s);
  mpq_mul(a, a, L);
  mpq_set_ui(s, T, q); mpq_canonicalize(s); mpq_mul(out, a, s);
  mpq_set_si(s, (long)(T * (err + cntp(z, pc, 0))), 1); mpq_add(out, out, s);
  mpq_clears(main, s, a, NULL);
}
static void lemB_perclass_q(mpq_t out, int T, int q, int zB, ll pB, const mpq_t L, int dB) {
  int ps[64], k = 0;
  for (int i = 0; i < nP1 && P1[i] <= zB; i++) ps[k++] = P1[i];
  if (pB < zB) pB = zB;
  mpq_t main, s, a; ll err; mpq_inits(main, s, a, NULL);
  ie_q(main, &err, ps, k, 2, dB);
  s2q(s, zB, pB, 1); mpq_add(a, main, s); mpq_add(a, a, s);
  mpq_mul(a, a, L);
  mpq_set_ui(s, T, q); mpq_canonicalize(s); mpq_mul(out, a, s);
  mpq_set_si(s, (long)(T * (err + 2 * cntp(zB, pB, 1))), 1); mpq_add(out, out, s);
  mpq_clears(main, s, a, NULL);
}

/* ---------------------------------------------------------------- U1 tail, Pell (Lemmas H, P) */
static void u1_tail_q(mpq_t out, ll N, ll lo, ll hi) {
  mpq_set_ui(out, 0, 1);
  if (hi <= lo) return;
  ll r1 = isqrtll(N), r2 = isqrtll(2 * N);
  mpq_t s, t; mpq_inits(s, t, NULL);
  ll a = hi < r1 ? hi : r1;
  if (a > lo) { s2q(s, lo, a, 1); mpq_set_si(t, N, 1); mpq_mul(s, s, t);
    mpq_set_si(t, cntp(lo, a, 1), 1); mpq_add(s, s, t); mpq_add(out, out, s); mpq_add(out, out, s); }
  ll b = hi < r2 ? hi : r2, lo2 = lo > r1 ? lo : r1;
  if (b > lo2) { mpq_set_si(t, 2 * cntp(lo2, b, 1), 1); mpq_add(out, out, t); }
  ll lo3 = lo > r2 ? lo : r2;
  if (hi > lo3) { mpq_set_si(t, cntp(lo3, hi, 1), 1); mpq_add(out, out, t); }
  mpq_clears(s, t, NULL);
}
static double u1_tail_f(double N, double lo, double hi) {
  if (hi <= lo) return 0;
  ll r1 = isqrtll((ll)N), r2 = isqrtll((ll)(2 * N));
  double v = 0, a = hi < r1 ? hi : r1;
  if (a > lo) v += 2 * (N * s2f(lo, a, 1) + cntf((ll)lo, (ll)a, 1));
  double b = hi < r2 ? hi : r2, lo2 = lo > r1 ? lo : r1;
  if (b > lo2) v += 2 * cntf((ll)lo2, (ll)b, 1);
  double lo3 = lo > r2 ? lo : r2;
  if (hi > lo3) v += cntf((ll)lo3, (ll)hi, 1);
  return v;
}
#define ADM_P (8 * 3 * 7 * 11 * 19 * 23)
static int *ADMPRE;
static int adm(ll m) { int r = (int)(m % 8); return (r == 1 || r == 2 || r == 5) && m % 3 && m % 7 && m % 11 && m % 19 && m % 23; }
static void adm_init(void) {
  ADMPRE = malloc(sizeof(int) * (ADM_P + 1)); ADMPRE[0] = 0;
  for (ll m = 1; m <= ADM_P; m++) ADMPRE[m] = ADMPRE[m - 1] + adm(m);
}
static ll adm_count(ll M) { return (M / ADM_P) * ADMPRE[ADM_P] + ADMPRE[M % ADM_P]; }
/* Lemma P: #{n <= N : p^2 | n^2+1 for some prime p >= Yq = Yp+1}, exact integers */
static ll pell_exact(ll N, ll Yp) {
  ll Yq = Yp + 1;
  if (Yq < 5) { fprintf(stderr, "pell: Yq < 5\n"); exit(2); }
  i128 NN = (i128)N * N;
  ll M = (ll)((NN + 1) / ((i128)Yq * Yq));
  if (M < 1) return 0;
  ll tot = adm_count(M);
  for (ll m = 1; m <= M; m++) {
    i128 X2 = (i128)m * Yq * Yq - 1, g2 = 4 * (i128)m > 9 ? 4 * (i128)m : 9;
    if (NN < g2 * X2) break;
    if (adm(m)) { ll j = 0; i128 t = X2 * g2; while (t <= NN) { j++; t *= g2; } tot += j; }
  }
  return tot;
}
static double pell_f(double N, double Yp) {
  ll Yq = (ll)floor(Yp) + 1;
  ll M = (ll)(((i128)(ll)N * (ll)N + 1) / ((i128)Yq * Yq));
  if (M < 1) return 0;
  double tot = (double)adm_count(M);
  for (ll m = 1; m <= M; m++) {
    double xlo = sqrt((double)m * Yq * Yq - 1), g = fmax(3.0, 2 * sqrt((double)m));
    if (N / xlo < g) break;
    if (adm(m)) tot += floor(log(N / xlo) / log(g) + 1e-12);
  }
  return tot;
}
static double best_tail_Yp(double N, double pT) {
  double best = -1, bY = 0, Yp = fmax(pT, 300.0);
  while (Yp < 2 * N) {
    double v = u1_tail_f(N, pT, Yp) + pell_f(N, Yp);
    if (best < 0 || v < best) { best = v; bY = Yp; }
    Yp *= 1.05;
  }
  return bY;
}
static void tail_q(mpq_t out, ll N, ll pT) {
  ll Yp = llround(best_tail_Yp((double)N, (double)pT));
  if (Yp < pT) Yp = pT;
  if (Yp < 4) Yp = 4;
  u1_tail_q(out, N, pT, Yp);
  mpq_t t; mpq_init(t); mpq_set_si(t, pell_exact(N, Yp), 1); mpq_add(out, out, t); mpq_clear(t);
}

/* ---------------------------------------------------------------- Lemma C (with the review fix) */
static int S_prefix_len(ll xb, int z2) {
  int n = 0; i128 prod = 1, lim = (i128)xb * xb + 1;
  for (int i = 0; i < nP1; i++) {
    if (P1[i] > z2) break;
    if ((prod * P1[i]) * (prod * P1[i]) > lim) break;
    n++; prod *= P1[i];
  }
  return n;
}
static int cmp_q_desc(const void *a, const void *b) { return -mpq_cmp(*(const mpq_t *)a, *(const mpq_t *)b); }
static void lemC_q(mpq_t out, const mpq_t Leff, int mult, ll xb, int z1, int z2, ll pc, ll pB, int dC) {
  int nS = S_prefix_len(xb, z2);
  ll pB2 = pB > z1 ? pB : z1;
  mpq_t a, t, Q, md, mf, non, alt, whole; mpq_inits(a, t, Q, md, mf, non, alt, whole, NULL);
  /* first term: U1 primes in (z1, pB2], 2*23 classes mod 25 p^2 */
  s2q(a, z1, pB2, 1); mpq_set_ui(t, 46, 25); mpq_mul(a, a, t); mpq_mul(out, a, Leff);
  mpq_set_si(t, 46 * cntp(z1, pB2, 1) * mult, 1); mpq_add(out, out, t);
  int U[64], k = 0;
  for (int i = 0; i < nP1 && P1[i] <= z1; i++) U[k++] = P1[i];
  int nU1z2 = 0; for (int i = 0; i < nP1 && P1[i] <= z2; i++) nU1z2++;
  mpq_t *gs = malloc(sizeof(mpq_t) * (nU1z2 + 1)); int ng = 0;
  /* IE over U and over U \ {p}: cached per removed index (-1 = none) */
  mpq_t *cmd = malloc(sizeof(mpq_t) * (k + 1)), *cmf = malloc(sizeof(mpq_t) * (k + 1));
  ll *ced = malloc(sizeof(ll) * (k + 1)), *cef = malloc(sizeof(ll) * (k + 1));
  for (int r = -1; r < k; r++) {
    int o[64], ko = 0; for (int i = 0; i < k; i++) if (i != r) o[ko++] = U[i];
    mpq_init(cmd[r + 1]); mpq_init(cmf[r + 1]);
    ie_q(cmd[r + 1], &ced[r + 1], o, ko, 2, dC);
    ie_q(cmf[r + 1], &cef[r + 1], o, ko, 2, 0);
  }
  for (int i = 1; i < nPR && PR[i] <= z2; i++) {
    int p2 = PR[i], r = -1;
    for (int j = 0; j < k; j++) if (U[j] == p2) r = j;
    mpq_ptr dmain = cmd[r + 1], fmain = cmf[r + 1]; ll ed = ced[r + 1], ef = cef[r + 1];
    if (p2 == 5) {   /* one whole class mod 25: direct union bound */
      mpq_set_ui(t, 1, 25); mpq_mul(t, t, dmain); mpq_mul(t, t, Leff); mpq_add(out, out, t);
      mpq_set_si(t, ed * mult, 1); mpq_add(out, out, t);
      continue;
    }
    mpq_set_ui(Q, 1, (unsigned long)p2 * p2); mpq_mul(Q, Q, Leff);
    /* (a) union over all classes of C_p2 */
    mpq_mul(non, Q, dmain); mpq_set_si(t, ed * mult, 1); mpq_add(non, non, t);
    /* (b) full IE, three-way */
    mpq_set_ui(t, 23, 25); mpq_mul(alt, Q, t); mpq_mul(alt, alt, fmain); mpq_set_si(t, 3 * ef * mult, 1); mpq_add(alt, alt, t);
    if (mpq_cmp(alt, non) < 0) mpq_set(non, alt);
    /* (c) union inside T25, depth d */
    mpq_set_ui(t, 23, 25); mpq_mul(alt, Q, t); mpq_mul(alt, alt, dmain); mpq_set_si(t, 23 * ed * mult, 1); mpq_add(alt, alt, t);
    if (mpq_cmp(alt, non) < 0) mpq_set(non, alt);
    mpq_add(out, out, non);
    if (p2 % 4 == 1 && p2 >= 13) {   /* U1: gain if p2 in S_b */
      mpq_set_ui(t, 23, 25); mpq_mul(whole, Q, t); mpq_set_si(t, 3 * mult, 1); mpq_add(whole, whole, t);
      mpq_init(gs[ng]); mpq_sub(gs[ng], whole, non);
      if (mpq_sgn(gs[ng]) < 0) mpq_set_ui(gs[ng], 0, 1);
      ng++;
    }
  }
  qsort(gs, ng, sizeof(mpq_t), cmp_q_desc);
  for (int i = 0; i < ng && i < nS; i++) mpq_add(out, out, gs[i]);
  for (int i = 0; i < ng; i++) mpq_clear(gs[i]);
  free(gs);
  /* odd p2 in (z2, pc] */
  s2q(t, z2, pc, 0); mpq_mul(t, t, Leff); mpq_add(out, out, t);
  mpq_set_si(t, cntp(z2, pc, 0) * mult, 1); mpq_add(out, out, t);
  for (int r = 0; r <= k; r++) { mpq_clear(cmd[r]); mpq_clear(cmf[r]); }
  free(cmd); free(cmf); free(ced); free(cef);
  mpq_clears(a, t, Q, md, mf, non, alt, whole, NULL);
}

/* ---------------------------------------------------------------- witness structures, Ex(b) (Lemma E) */
static int WSM = 97, NSM = 24, USE_E2 = 1; static double BR = 1.3;
static const int SMALL[24] = {3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97};
static const int C2[4] = {1, 1, 2, 4}, M2[4] = {1, 2, 4, 8};
/* table */
typedef struct { int e; unsigned mask; ll P, phi, bn; } Disc;
static Disc *DT; static int nDT;
#define HB 22
static int *HT; /* open addressing, key (e<<24)|mask -> index */
static unsigned hkey(int e, unsigned mask) { return ((unsigned)e << 24) | mask; }
static unsigned hh(unsigned k) { return (k * 2654435761u) >> (32 - HB); }
static int disc_find(int e, unsigned mask) {
  unsigned k = hkey(e, mask), h = hh(k);
  while (HT[h] >= 0) { if (hkey(DT[HT[h]].e, DT[HT[h]].mask) == k) return HT[h]; h = (h + 1) & ((1u << HB) - 1); }
  return -1;
}
static int smallidx(int p) { for (int i = 0; i < 24; i++) if (SMALL[i] == p) return i; return -1; }
static void load_table(const char *path) {
  FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
  int cap = 1 << 16; DT = malloc(sizeof(Disc) * cap); nDT = 0;
  char line[4096];
  while (fgets(line, sizeof line, f)) {
    int e, k, off; char *s = line; unsigned mask = 0;
    sscanf(s, "%d %d%n", &e, &k, &off); s += off;
    for (int j = 0; j < k; j++) { int q; sscanf(s, "%d%n", &q, &off); s += off;
      int ix = smallidx(q); if (ix < 0) { fprintf(stderr, "table prime %d not small\n", q); exit(1); } mask |= 1u << ix; }
    Disc d; d.e = e; d.mask = mask;
    sscanf(s, " P=%lld phi=%lld beta0num=%lld", &d.P, &d.phi, &d.bn);
    ll P = M2[e]; for (int j = 0; j < 24; j++) if (mask >> j & 1) P *= SMALL[j];
    if (P != d.P) { fprintf(stderr, "table period mismatch\n"); exit(1); }
    if (nDT == cap) { cap *= 2; DT = realloc(DT, sizeof(Disc) * cap); }
    DT[nDT++] = d;
  }
  fclose(f);
  HT = malloc(sizeof(int) << HB); memset(HT, -1, sizeof(int) << HB);
  for (int i = 0; i < nDT; i++) { unsigned h = hh(hkey(DT[i].e, DT[i].mask));
    while (HT[h] >= 0) h = (h + 1) & ((1u << HB) - 1); HT[h] = i; }
}
/* choice lists per (e, S): (f, disc index or -1 for the trivial choice rho = C2 * 2^|S|) */
typedef struct { int f; int di; double fa, fb; } Choice;
typedef struct { int e; unsigned mask; int off, n; } ChList;
static Choice *CH; static int nCH, capCH;
static ChList *CL; static int nCL, capCL;
static int *CLH; /* hash (e,mask) -> CL index */
static int cl_find(int e, unsigned mask) {
  unsigned k = hkey(e, mask), h = hh(k);
  while (CLH[h] >= 0) { if (hkey(CL[CLH[h]].e, CL[CLH[h]].mask) == k) return CLH[h]; h = (h + 1) & ((1u << HB) - 1); }
  return -1;
}
static int cl_get(int e, unsigned mask) {
  int i = cl_find(e, mask); if (i >= 0) return i;
  int ns = __builtin_popcount(mask);
  Choice tmp[300]; int nt = 0;
  tmp[nt].f = C2[e] << ns; tmp[nt].di = -1; tmp[nt].fa = tmp[nt].f; tmp[nt].fb = 0; nt++;
  if (USE_E2) for (unsigned q = mask;; q = (q - 1) & mask) {   /* all submasks */
    int d = disc_find(e, q);
    if (d >= 0) { Choice c; c.f = 1 << (ns - __builtin_popcount(q)); c.di = d;
      c.fa = c.f * (double)DT[d].phi / DT[d].P; c.fb = c.f * (double)DT[d].bn / DT[d].P; tmp[nt++] = c; }
    if (q == 0) break;
  }
  /* Pareto pruning (always safe: a min over fewer valid bounds is still a valid bound) */
  Choice keep[300]; int nk = 0;
  for (int a = 0; a < nt; a++) {
    int dom = 0;
    for (int b = 0; b < nt && !dom; b++)
      if (b != a && tmp[b].fa <= tmp[a].fa && tmp[b].fb <= tmp[a].fb && (tmp[b].fa < tmp[a].fa || tmp[b].fb < tmp[a].fb || b < a)) dom = 1;
    if (!dom) keep[nk++] = tmp[a];
  }
  if (nCH + nk > capCH) { capCH = 2 * (nCH + nk) + 1024; CH = realloc(CH, sizeof(Choice) * capCH); }
  memcpy(CH + nCH, keep, sizeof(Choice) * nk);
  if (nCL == capCL) { capCL = 2 * capCL + 1024; CL = realloc(CL, sizeof(ChList) * capCL); }
  CL[nCL].e = e; CL[nCL].mask = mask; CL[nCL].off = nCH; CL[nCL].n = nk; nCH += nk;
  unsigned h = hh(hkey(e, mask)); while (CLH[h] >= 0) h = (h + 1) & ((1u << HB) - 1); CLH[h] = nCL;
  return nCL++;
}
/* structures for b <= NMAX, per constraint, sorted by bmin: structures(x) = prefix with bmin <= x */
typedef struct { ll bm; int cl; int u; } Str;
static Str *ST[3]; static int nST[3];
static ll BIGPROD[16]; static int nBIG;
enum { ANY5 = 0, ODD = 1, EVEN = 2 };
static void rec(int ci, int i, ll base, unsigned mask, int e, int cop5, Str **out, int *n, int *cap) {
  if (i == NSM) {
    for (int u = 0; u < nBIG && base * BIGPROD[u] <= NMAX; u++) {
      if (*n == *cap) { *cap = *cap * 2 + 1024; *out = realloc(*out, sizeof(Str) * *cap); }
      (*out)[*n].bm = base * BIGPROD[u]; (*out)[*n].cl = cl_get(e, mask); (*out)[*n].u = u; (*n)++;
    }
    return;
  }
  rec(ci, i + 1, base, mask, e, cop5, out, n, cap);
  if (cop5 && SMALL[i] == 5) return;
  if (base * SMALL[i] <= NMAX) rec(ci, i + 1, base * SMALL[i], mask | (1u << i), e, cop5, out, n, cap);
}
static int cmp_str(const void *a, const void *b) { ll x = ((const Str *)a)->bm, y = ((const Str *)b)->bm; return (x > y) - (x < y); }
static void build_structures(void) {
  BIGPROD[0] = 1; nBIG = 1;
  for (int i = 0; i < nPR && nBIG < 16; i++) if (PR[i] > WSM) {
    if ((i128)BIGPROD[nBIG - 1] * PR[i] > NMAX) break;
    BIGPROD[nBIG] = BIGPROD[nBIG - 1] * PR[i]; nBIG++;
  }
  for (int ci = 0; ci < 3; ci++) {
    int lo = ci == ODD ? 0 : (ci == EVEN ? 1 : 0), hi = ci == ODD ? 0 : 3, cop5 = ci == ANY5;
    Str *out = NULL; int n = 0, cap = 0;
    for (int e = lo; e <= hi; e++) rec(ci, 0, M2[e], 0, e, cop5, &out, &n, &cap);
    qsort(out, n, sizeof(Str), cmp_str);
    ST[ci] = out; nST[ci] = n;
  }
}
static int prefix_len(int ci, ll x) {
  int lo = 0, hi = nST[ci];
  while (lo < hi) { int m = (lo + hi) / 2; if (ST[ci][m].bm <= x) lo = m + 1; else hi = m; }
  return lo;
}
/* float value of structure s at A (B depends on N, bm) */
static inline double str_val(const Str *s, double A, double N) {
  ll bm = s->bm; double B = (double)(isqrtll((ll)N * bm + 1) + 1) / bm + 1;
  const ChList *c = &CL[s->cl]; double m = 1e300;
  for (int j = 0; j < c->n; j++) { const Choice *h = &CH[c->off + j]; double v = h->fa * A + h->fb * B; if (v < m) m = v; }
  return ldexp(m, s->u);
}
static double ex_f(double N, double Y, ll x, int ci) {
  ll M = (ll)floor((N * x + 1) / (Y * Y));
  if (M < 1) return 0;
  double A = (N + 1) / Y + M, mx = 0;
  int n = prefix_len(ci, x);
  for (int i = 0; i < n; i++) { double v = str_val(&ST[ci][i], A, N); if (v > mx) mx = v; }
  return mx;
}
static double mid_f(double N, double pc, double Y) {
  ll r = isqrtll((ll)N);
  if (Y <= r) return N * s2f(pc, Y, 0) + cntf((ll)pc, (ll)Y, 0);
  double lo = pc > r ? pc : r;
  return N * s2f(pc, lo, 0) + cntf((ll)pc, (ll)lo, 0) + cntf((ll)lo, (ll)Y, 0);
}
static ll choose_Y(ll N, ll pc, ll x, int ci) {
  double best = -1, bY = 0, Y = fmax((double)pc, 300.0);
  while (Y < 4.0 * N) {
    double v = mid_f(N, pc, Y) + ex_f(N, Y, x, ci);
    if (best < 0 || v < best) { best = v; bY = Y; }
    Y *= 1.12;
  }
  double Y0 = bY;
  for (int i = -12; i <= 12; i++) {
    double t = Y0 * (1 + 0.01 * i); if (t <= pc) continue;
    double v = mid_f(N, pc, t) + ex_f(N, t, x, ci);
    if (v < best) { best = v; bY = t; }
  }
  ll Yi = llround(bY); if (Yi < pc + 1) Yi = pc + 1;
  return Yi;
}
static void mid_q(mpq_t out, ll N, ll pc, ll Y) {
  ll r = isqrtll(N); mpq_t t; mpq_init(t);
  if (Y <= r) { s2q(out, pc, Y, 0); mpq_set_si(t, N, 1); mpq_mul(out, out, t); mpq_set_si(t, cntp(pc, Y, 0), 1); mpq_add(out, out, t); }
  else { ll lo = pc > r ? pc : r;
    s2q(out, pc, lo, 0); mpq_set_si(t, N, 1); mpq_mul(out, out, t);
    mpq_set_si(t, cntp(pc, lo, 0) + cntp(lo, Y, 0), 1); mpq_add(out, out, t); }
  mpq_clear(t);
}
/* exact max over structures (b <= x, constraint ci) of the E2 bound for |Ex(b)| */
static void ex_q(mpq_t out, ll N, ll Y, ll x, int ci) {
  mpq_set_ui(out, 0, 1);
  ll M = (ll)(((i128)N * x + 1) / ((i128)Y * Y));
  if (M < 1) return;
  mpq_t A, Bup, v, best, t; mpq_inits(A, Bup, v, best, t, NULL);
  mpq_set_ui(A, N + 1, Y); mpq_canonicalize(A); mpq_set_si(t, M, 1); mpq_add(A, A, t);
  double Af = mpq_get_d(A);
  int n = prefix_len(ci, x);
  double *vf = malloc(sizeof(double) * (n ? n : 1)), vmax = 0;
  for (int i = 0; i < n; i++) { vf[i] = str_val(&ST[ci][i], Af, (double)N); if (vf[i] > vmax) vmax = vf[i]; }
  /* float values: few correctly rounded operations on positive numbers, relative error < 1e-12;
     structures below (1 - 1e-6) vmax have exact value below the exact value of the argmax */
  double thr = vmax * (1 - 1e-6);
  for (int i = 0; i < n; i++) {
    if (vf[i] < thr) continue;
    const Str *s = &ST[ci][i]; const ChList *c = &CL[s->cl];
    mpq_set_ui(Bup, isqrtll(N * s->bm + 1) + 1, s->bm); mpq_canonicalize(Bup); mpq_set_ui(t, 1, 1); mpq_add(Bup, Bup, t);
    int first = 1;
    for (int j = 0; j < c->n; j++) {
      const Choice *h = &CH[c->off + j];
      if (h->di < 0) { mpq_set_si(v, h->f, 1); mpq_mul(v, v, A); }
      else { const Disc *d = &DT[h->di];
        mpq_set_si(v, d->phi, 1); mpq_mul(v, v, A); mpq_set_si(t, d->bn, 1); mpq_mul(t, t, Bup); mpq_add(v, v, t);
        mpq_set_si(t, h->f, d->P); mpq_canonicalize(t); mpq_mul(v, v, t); }
      if (first || mpq_cmp(v, best) < 0) { mpq_set(best, v); first = 0; }
    }
    mpq_mul_2exp(best, best, s->u);
    if (mpq_cmp(best, out) > 0) mpq_set(out, best);
  }
  free(vf);
  mpq_clears(A, Bup, v, best, t, NULL);
}

/* ---------------------------------------------------------------- cases */
typedef struct { int z, dA, zB, dB, z1, z2, dC; ll pc; double pBf; } Prm;
static ll pB_of(ll N, int q, const Prm *p) {
  ll v = (ll)(p->pBf * sqrt((double)N * (1 - 23.0 / q) / 22)); return v > 13 ? v : 13;
}
typedef struct { ll xa, xb; } Bucket;
static int buckets(ll N, Bucket *b) {
  int n = 0; ll xa = 1;
  while (xa < N) { ll xb = (ll)floor(xa * BR); if (xb < xa + 1) xb = xa + 1; if (xb > N) xb = N;
    b[n].xa = xa; b[n].xb = xb; n++; xa = xb; }
  return n;
}
/* shared set Sh(x) = Mid + Ex for witnesses b <= x, memoised per (bucket, constraint) */
typedef struct { ll N, pc; int nb; Bucket *b; mpq_t *sh[3]; char *have[3]; } Ctx;
static mpq_ptr SH(Ctx *c, int bi, int ci) {
  if (!c->have[ci][bi]) {
    ll x = c->b[bi].xb, Y = choose_Y(c->N, c->pc, x, ci);
    mpq_t t; mpq_init(t);
    mid_q(c->sh[ci][bi], c->N, c->pc, Y); ex_q(t, c->N, Y, x, ci); mpq_add(c->sh[ci][bi], c->sh[ci][bi], t);
    mpq_clear(t); c->have[ci][bi] = 1;
  }
  return c->sh[ci][bi];
}
static void qN(mpq_t o, ll v) { mpq_set_si(o, v, 1); }

static void eval_case(mpq_t out, int cs, ll N, const Prm *p) {
  Bucket bk[200]; int nb = buckets(N, bk);
  Ctx c; c.N = N; c.pc = p->pc > 0 ? p->pc : ((ll)(0.3 * sqrt((double)N)) > 2000 ? (ll)(0.3 * sqrt((double)N)) : 2000);
  c.nb = nb; c.b = bk;
  for (int ci = 0; ci < 3; ci++) { c.sh[ci] = malloc(sizeof(mpq_t) * nb); c.have[ci] = calloc(nb, 1);
    for (int i = 0; i < nb; i++) mpq_init(c.sh[ci][i]); }
  ll pc = c.pc;
  mpq_t v, w, L, t, tl, best, base; mpq_inits(v, w, L, t, tl, best, base, NULL);
  mpq_t NQ; mpq_init(NQ); qN(NQ, N);
  if (cs == 0) {   /* I.b */
    mpq_set_ui(best, 0, 1);
    for (int i = 0; i < nb; i++) { qN(L, N - bk[i].xa + 1);
      restricted_q(v, 1, 25, 2, p->z, pc, L, p->dA); mpq_add(v, v, SH(&c, i, ANY5));
      if (mpq_cmp(v, best) > 0) mpq_set(best, v); }
    mpq_add(out, best, best);
  } else if (cs == 1) {   /* II */
    ll pB = pB_of(N, 25, p); tail_q(tl, N, pB > p->z1 ? pB : p->z1);
    restricted_q(base, 2, 25, 3, p->z, pc, NQ, p->dA);
    mpq_set_ui(best, 0, 1);
    for (int i = 0; i < nb; i++) {
      mpq_set_si(L, 2 * N - (bk[i].xa - 1), 2); mpq_canonicalize(L);   /* N - (xa-1)/2 */
      lemC_q(v, L, 2, bk[i].xb, p->z1, p->z2, pc, pB, p->dC);
      lemC_q(w, NQ, 1, bk[i].xb, p->z1, p->z2, pc, pB, p->dC);
      if (mpq_cmp(w, v) < 0) mpq_set(v, w);
      mpq_add(v, v, base); mpq_add(v, v, SH(&c, i, EVEN)); mpq_add(v, v, tl);
      if (mpq_cmp(v, best) > 0) mpq_set(best, v);
    }
    mpq_set(out, best);
  } else {
    ll pT = pB_of(N, 100, p); if (p->zB > pT) pT = p->zB; if (p->z1 > pT) pT = p->z1;
    tail_q(tl, N, pT);
    mpq_t shb; mpq_init(shb); mpq_set_ui(shb, 0, 1);   /* max over buckets of Ast + Sh, without tail */
    for (int i = 0; i < nb; i++) {
      qN(L, N - bk[i].xa + 1);
      lemB_perclass_q(v, 23, 100, p->zB, pT, L, p->dB);
      mpq_set_ui(t, 1, 4); mpq_mul(t, t, L);
      lemC_q(w, t, 1, bk[i].xb, p->z1, p->z2, pc, pT, p->dC);
      if (mpq_cmp(w, v) < 0) mpq_set(v, w);
      mpq_add(v, v, SH(&c, i, ODD));
      if (mpq_cmp(v, shb) > 0) mpq_set(shb, v);
    }
    if (cs == 2) {   /* III.1 */
      restricted_q(v, 6, 100, 3, p->z, pc, NQ, p->dA); restricted_q(w, 2, 100, 3, p->z, pc, NQ, p->dA);
      mpq_add(out, v, w); mpq_add(out, out, shb); mpq_add(out, out, shb); mpq_add(out, out, tl);
    } else if (cs == 3) {   /* III.2 beta */
      mpq_set_si(v, N + 100, 100); mpq_canonicalize(v);
      restricted_q(w, 4, 100, 3, p->z, pc, NQ, p->dA);
      mpq_add(out, v, w); mpq_add(out, out, shb); mpq_add(out, out, tl);
    } else {   /* III.2 alpha */
      mpq_t a3, a2; mpq_inits(a3, a2, NULL);
      restricted_q(a3, 2, 100, 3, p->z, pc, NQ, p->dA); mpq_add(a3, a3, shb); mpq_add(a3, a3, tl);
      mpq_set_ui(best, 0, 1);
      for (int i = 0; i < nb; i++) { qN(L, N - bk[i].xa + 1);
        restricted_q(v, 3, 100, 3, p->z, pc, L, p->dA); mpq_add(v, v, SH(&c, i, ANY5));
        if (mpq_cmp(v, best) > 0) mpq_set(best, v); }
      mpq_add(a3, a3, best); mpq_add(a3, a3, best);
      mpq_set_si(a2, N + 100, 100); mpq_canonicalize(a2);
      restricted_q(v, 6, 100, 3, p->z, pc, NQ, p->dA); mpq_add(a2, a2, v); mpq_add(a2, a2, shb); mpq_add(a2, a2, tl);
      restricted_q(w, 1, 100, 3, p->z, pc, NQ, p->dA);
      mpq_set_ui(best, 0, 1);
      for (int i = 0; i < nb; i++) { mpq_set(v, w); mpq_add(v, v, SH(&c, i, ANY5)); if (mpq_cmp(v, best) > 0) mpq_set(best, v); }
      mpq_add(a2, a2, best);
      mpq_set(out, mpq_cmp(a3, a2) < 0 ? a3 : a2);
      mpq_clears(a3, a2, NULL);
    }
    mpq_clear(shb);
  }
  mpq_clears(v, w, L, t, tl, best, base, NQ, NULL);
  for (int ci = 0; ci < 3; ci++) { for (int i = 0; i < nb; i++) mpq_clear(c.sh[ci][i]); free(c.sh[ci]); free(c.have[ci]); }
}

/* ---------------------------------------------------------------- driver */
typedef struct { ll lo, hi; Prm p[NCASE]; double r[NCASE]; int ok; } Iv;
static int cmp_iv(const void *a, const void *b) { ll x = ((const Iv *)a)->lo, y = ((const Iv *)b)->lo; return (x > y) - (x < y); }
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: cert table.txt intervals.txt\n"); return 1; }
  if (getenv("CERT_W")) { WSM = atoi(getenv("CERT_W")); NSM = 0; while (NSM < 24 && SMALL[NSM] <= WSM) NSM++; }
  if (getenv("CERT_E2")) USE_E2 = atoi(getenv("CERT_E2"));
  if (getenv("CERT_BR")) BR = atof(getenv("CERT_BR"));
  fprintf(stderr, "options: W=%d (%d small primes), E2=%d, bucket ratio %.3f\n", WSM, NSM, USE_E2, BR);
  sieve(); adm_init(); load_table(argv[1]);
  CLH = malloc(sizeof(int) << HB); memset(CLH, -1, sizeof(int) << HB);
  build_structures();
  fprintf(stderr, "primes %d, U1 %d, table %d, structures %d/%d/%d, choice lists %d\n",
          nPR, nP1, nDT, nST[0], nST[1], nST[2], nCL);
  FILE *f = fopen(argv[2], "r"); if (!f) { perror(argv[2]); return 1; }
  int cap = 1024, n = 0; Iv *iv = malloc(sizeof(Iv) * cap);
  while (1) {
    Iv x; if (fscanf(f, "%lld %lld", &x.lo, &x.hi) != 2) break;
    for (int c = 0; c < NCASE; c++) { Prm *p = &x.p[c];
      if (fscanf(f, "%d %d %d %d %d %d %d %lld %lf", &p->z, &p->dA, &p->zB, &p->dB, &p->z1, &p->z2, &p->dC, &p->pc, &p->pBf) != 9) { fprintf(stderr, "bad input\n"); return 1; } }
    if (n == cap) { cap *= 2; iv = realloc(iv, sizeof(Iv) * cap); }
    iv[n++] = x;
  }
  fclose(f);
  int done = 0;
  #pragma omp parallel for schedule(dynamic, 1)
  for (int i = 0; i < n; i++) {
    mpq_t v, tgt; mpq_inits(v, tgt, NULL);
    mpq_set_si(tgt, iv[i].lo - 6, 25); mpq_canonicalize(tgt);
    int ok = 1;
    for (int c = 0; c < NCASE; c++) {
      eval_case(v, c, iv[i].hi, &iv[i].p[c]);
      if (mpq_cmp(v, tgt) >= 0) ok = 0;
      mpq_div(v, v, tgt); iv[i].r[c] = mpq_get_d(v);
    }
    iv[i].ok = ok;
    #pragma omp critical
    { done++; printf("%lld %lld %.9f %.9f %.9f %.9f %.9f %s\n", iv[i].lo, iv[i].hi, iv[i].r[0], iv[i].r[1], iv[i].r[2], iv[i].r[3], iv[i].r[4], ok ? "ok" : "FAIL");
      fflush(stdout); }
    mpq_clears(v, tgt, NULL);
  }
  qsort(iv, n, sizeof(Iv), cmp_iv);
  int bad = 0, gaps = 0; double worst = 0;
  for (int i = 0; i < n; i++) { if (!iv[i].ok) bad++;
    for (int c = 0; c < NCASE; c++) if (iv[i].r[c] > worst) worst = iv[i].r[c];
    if (i + 1 < n && iv[i].hi != iv[i + 1].lo) gaps++; }
  printf("SUMMARY intervals %d, failed %d, gaps %d, covered [%lld, %lld], worst ratio %.6f\n",
         n, bad, gaps, n ? iv[0].lo : 0, n ? iv[n - 1].hi : 0, worst);
  return bad || gaps;
}
