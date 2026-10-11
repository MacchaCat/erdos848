/* gen2.c — data for the kernel checker of proof.md §10 (ErdosComp/Check2.lean).
 *
 * Uses the float machinery of cert.c (included below, its main renamed) only to CHOOSE the split
 * points Y (on a fixed geometric grid) and the tail cut-off Y'.  The quantities that the Lean
 * checker verifies are produced here with exactly the checker's formulas:
 *   - the Lemma E2 table (e, Q, P, Ssum, bn), recomputed from scratch;
 *   - the witness structures (e, mask, u, bm) with Pareto-pruned choices, sorted by bm;
 *   - per bucket the claimed Ex numerator En = max_s min_c ceil(value), so that `strOK` holds.
 *
 *   CERT_W=23 CERT_NOB=1 CERT_PMAX=3000 ./gen2 disc_table_97.txt intervals.txt outdir
 *
 * Writes outdir/{disc,strs,iv,points,admpre}.txt.
 */
#include <stdio.h>
#define main cert_main
#include "cert_base.c"
#undef main

#define KE (1LL << 20)
#define DCAP 3000
static const int SW[8] = {3, 5, 7, 11, 13, 17, 19, 23};

/* ------------------------------------------------------------ Lemma E2 table */
typedef struct { int e, qmask; ll P, Ssum, bn; } DE;
static DE DTL[4096]; static int nDTL;

static int rootCnt(ll b, ll m) { int c = 0; for (ll s = 0; s < b; s++) if ((s * s % b) * (m % b) % b == 1 % b) c++; return c; }

static void build_disc(void) {
  nDTL = 0;
  for (int e = 0; e < 4; e++)
    for (int qm = 0; qm < 256; qm++) {
      ll P = 1LL << e;
      for (int i = 0; i < 8; i++) if (qm >> i & 1) P *= SW[i];
      if (P > DCAP) continue;
      ll *g = malloc(sizeof(ll) * (P + 1));
      ll Ssum = 0;
      for (ll m = 1; m <= P; m++) {
        ll v = rootCnt(1LL << e, m);
        for (int i = 0; i < 8; i++) if (qm >> i & 1) v *= rootCnt(SW[i], m);
        g[m] = v; Ssum += v;
      }
      ll G = 0, bn = 0;
      for (ll r = 1; r < P; r++) { G += g[r]; ll t = P * G - Ssum * r; if (t > bn) bn = t; }
      free(g);
      DE d = {e, qm, P, Ssum, bn}; DTL[nDTL++] = d;
    }
}

/* ------------------------------------------------------------ structures */
typedef struct { int e, mask, u; ll bm; int nch; int ch[64]; } SE;
static SE *STL[3]; static int nSTL[3];
static ll bigProdL(int u) { static const ll t[7] = {1, 29, 29LL * 31, 29LL * 31 * 37, 29LL * 31 * 37 * 41, 29LL * 31 * 37 * 41 * 43, 29LL * 31 * 37 * 41 * 43 * 47}; return t[u > 6 ? 6 : u]; }
static int consOKc(int ci, int e, int mask) { return ci == 0 ? !(mask >> 1 & 1) : ci == 1 ? e == 0 : e >= 1; }
static int twoCc(int e) { return e == 3 ? 4 : e == 2 ? 2 : 1; }
static int cmp_se(const void *a, const void *b) {
  const SE *x = a, *y = b;
  if (x->bm != y->bm) return x->bm < y->bm ? -1 : 1;
  if (x->e != y->e) return x->e - y->e;
  if (x->mask != y->mask) return x->mask - y->mask;
  return x->u - y->u;
}
static void build_strs(void) {
  for (int ci = 0; ci < 3; ci++) {
    SE *L = malloc(sizeof(SE) * 8192); int n = 0;
    for (int e = 0; e < 4; e++) for (int mask = 0; mask < 256; mask++) {
      if (!consOKc(ci, e, mask)) continue;
      ll base = 1LL << e; int ns = 0;
      for (int i = 0; i < 8; i++) if (mask >> i & 1) { base *= SW[i]; ns++; }
      /* Pareto choices among table entries (fa, fb) = f (Ssum/P, bn/P), f = 2^(|S|-|Q|);
         the trivial choice twoC(e) 2^|S| (fb = 0) is always tried by the checker */
      int cand[4096], nc = 0;
      for (int j = 0; j < nDTL; j++) if (DTL[j].e == e && (DTL[j].qmask & mask) == DTL[j].qmask) cand[nc++] = j;
      double fa[4096], fb[4096];
      for (int k = 0; k < nc; k++) { const DE *d = &DTL[cand[k]]; int nq = __builtin_popcount(d->qmask);
        double f = ldexp(1.0, ns - nq); fa[k] = f * d->Ssum / d->P; fb[k] = f * (double)d->bn / d->P; }
      double ta = twoCc(e) * ldexp(1.0, ns);
      int keep[64], nk = 0;
      for (int a = 0; a < nc && nk < 64; a++) {
        if (fa[a] >= ta) continue;   /* dominated by the trivial choice */
        int dom = 0;
        for (int b = 0; b < nc && !dom; b++)
          if (b != a && fa[b] <= fa[a] && fb[b] <= fb[a] && (fa[b] < fa[a] || fb[b] < fb[a] || b < a)) dom = 1;
        if (!dom) keep[nk++] = cand[a];
      }
      /* order by fa ascending */
      for (int a = 1; a < nk; a++) for (int b = a; b > 0; b--) {
        const DE *x = &DTL[keep[b - 1]], *y = &DTL[keep[b]];
        double xa = ldexp(1.0, ns - __builtin_popcount(x->qmask)) * x->Ssum / x->P;
        double ya = ldexp(1.0, ns - __builtin_popcount(y->qmask)) * y->Ssum / y->P;
        if (ya < xa) { int t = keep[b]; keep[b] = keep[b - 1]; keep[b - 1] = t; } else break;
      }
      for (int u = 0; u < 6; u++) {
        ll bm = base * bigProdL(u);
        if (bm > NMAX) break;
        SE s; s.e = e; s.mask = mask; s.u = u; s.bm = bm; s.nch = nk; memcpy(s.ch, keep, sizeof(int) * nk);
        L[n++] = s;
      }
    }
    qsort(L, n, sizeof(SE), cmp_se);
    STL[ci] = L; nSTL[ci] = n;
  }
}

/* En for one bucket: max over structures with bm <= xb of min over choices of ceil(value) */
static void en_exact(mpz_t En, int ci, ll N, ll xb, ll Y) {
  mpz_set_ui(En, 0);
  i128 M = ((i128)N * xb + 1) / ((i128)(Y + 1) * (Y + 1));
  mpz_t aN, v, best, num, t; mpz_inits(aN, v, best, num, t, NULL);
  z_set_i128(aN, (i128)N + 1 + M * Y);
  for (int i = 0; i < nSTL[ci]; i++) {
    const SE *s = &STL[ci][i];
    if (s->bm > xb) break;
    int w = __builtin_popcount(s->mask) + s->u;
    mpz_mul_ui(best, aN, twoCc(s->e)); mpz_mul_2exp(best, best, w); mpz_mul_ui(best, best, KE);
    ll bN = isqrtll(N * s->bm + 1) + 1 + s->bm;
    for (int k = 0; k < s->nch; k++) {
      const DE *d = &DTL[s->ch[k]];
      int wq = __builtin_popcount(d->qmask);
      mpz_mul_ui(num, aN, d->Ssum); mpz_mul_ui(num, num, s->bm);
      mpz_set_ui(t, d->bn); mpz_mul_ui(t, t, bN); mpz_mul_ui(t, t, Y); mpz_add(num, num, t);
      mpz_mul_2exp(num, num, w - wq); mpz_mul_ui(num, num, KE);
      mpz_set_ui(t, d->P); mpz_mul_ui(t, t, s->bm);
      mpz_cdiv_q(v, num, t);
      if (mpz_cmp(v, best) < 0) mpz_set(best, v);
    }
    if (mpz_cmp(best, En) > 0) mpz_set(En, best);
  }
  mpz_clears(aN, v, best, num, t, NULL);
}

/* ------------------------------------------------------------ grid of split points */
static ll GRID[4096]; static int nGRID;
static void build_grid(void) {
  nGRID = 0; double g = 100;
  while (g <= PMAX) { ll v = llround(g); if (nGRID == 0 || v != GRID[nGRID - 1]) GRID[nGRID++] = v; g *= 1.02; }
}
static ll snap_best_Y(ll N, ll pc, ll x, int ci) {
  ll Y0 = choose_Y(N, pc, x, ci);
  /* best grid point within a factor 1.15 of the float optimum */
  double best = -1; ll bY = GRID[0];
  for (int i = 0; i < nGRID; i++) {
    if (GRID[i] < Y0 / 1.15 || GRID[i] > Y0 * 1.15) continue;
    double v = mid_f((double)N, (double)pc, (double)GRID[i]) + ex_f((double)N, (double)GRID[i], x, ci);
    if (best < 0 || v < best) { best = v; bY = GRID[i]; }
  }
  return bY;
}
static ll snap_tail_Y(ll N, ll pT) {
  double Y0 = best_tail_Yp((double)N, (double)pT);
  double best = -1; ll bY = GRID[0];
  for (int i = 0; i < nGRID; i++) {
    if (GRID[i] < Y0 / 1.1 || GRID[i] > Y0 * 1.1 || GRID[i] < 4) continue;
    double v = u1_tail_f((double)N, (double)pT, (double)GRID[i]) + pell_f((double)N, (double)GRID[i]);
    if (best < 0 || v < best) { best = v; bY = GRID[i]; }
  }
  return bY;
}

/* Lean buckets */
static int lean_buckets(ll N, Bucket *b) {
  int n = 0; ll xa = 1;
  while (xa < N) { ll xb = xa * 13 / 10; if (xb < xa + 1) xb = xa + 1; if (xb > N) xb = N;
    b[n].xa = xa; b[n].xb = xb; n++; xa = xb; }
  return n;
}

static int nPrimesEx(int z, int ex2, int ex5) { int c = 0; for (int i = 0; i < nPR && PR[i] <= z; i++) { if (ex2 && PR[i] == 2) continue; if (ex5 && PR[i] == 5) continue; c++; } return c; }
static int nU1(int z) { int c = 0; for (int i = 0; i < nP1 && P1[i] <= z; i++) c++; return c; }
static int oddAtLeast(int k) { return k % 2 ? k : k + 1; }

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: gen2 table.txt intervals.txt outdir\n"); return 1; }
  if (getenv("CERT_W")) { WSM = atoi(getenv("CERT_W")); NSM = 0; while (NSM < 24 && SMALL[NSM] <= WSM) NSM++; }
  sieve(); adm_init(); load_table(argv[1]);
  CLH = malloc(sizeof(int) << HB); memset(CLH, -1, sizeof(int) << HB);
  build_structures();
  build_disc(); build_strs(); build_grid();
  fprintf(stderr, "disc %d, strs %d/%d/%d, grid %d\n", nDTL, nSTL[0], nSTL[1], nSTL[2], nGRID);
  char path[4096]; FILE *f;
  snprintf(path, sizeof path, "%s/disc.txt", argv[3]); f = fopen(path, "w");
  for (int j = 0; j < nDTL; j++) fprintf(f, "%d %d %lld %lld %lld\n", DTL[j].e, DTL[j].qmask, DTL[j].P, DTL[j].Ssum, DTL[j].bn);
  fclose(f);
  snprintf(path, sizeof path, "%s/strs.txt", argv[3]); f = fopen(path, "w");
  for (int ci = 0; ci < 3; ci++) {
    fprintf(f, "ci %d %d\n", ci, nSTL[ci]);
    for (int i = 0; i < nSTL[ci]; i++) { const SE *s = &STL[ci][i];
      fprintf(f, "%d %d %d %lld %d", s->e, s->mask, s->u, s->bm, s->nch);
      for (int k = 0; k < s->nch; k++) fprintf(f, " %d", s->ch[k]);
      fprintf(f, "\n"); }
  }
  fclose(f);
  /* prefix table of admissible m */
  snprintf(path, sizeof path, "%s/admpre.txt", argv[3]); f = fopen(path, "w");
  { ll c = 0; for (ll i = 0; i <= 808; i++) { fprintf(f, "%lld\n", c); for (ll m = i * 1000 + 1; m <= (i + 1) * 1000; m++) c += adm(m); } }
  fclose(f);
  /* intervals */
  FILE *in = fopen(argv[2], "r"); if (!in) { perror(argv[2]); return 1; }
  int cap = 1024, n = 0; Iv *iv = malloc(sizeof(Iv) * cap);
  while (1) {
    Iv x; if (fscanf(in, "%lld %lld", &x.lo, &x.hi) != 2) break;
    for (int c = 0; c < NCASE; c++) { Prm *p = &x.p[c];
      if (fscanf(in, "%d %d %d %d %d %d %d %lld %lf", &p->z, &p->dA, &p->zB, &p->dB, &p->z1, &p->z2, &p->dC, &p->pc, &p->pBf) != 9) { fprintf(stderr, "bad input\n"); return 1; } }
    if (n == cap) { cap *= 2; iv = realloc(iv, sizeof(Iv) * cap); }
    iv[n++] = x;
  }
  fclose(in);
  char **outs = calloc(n, sizeof(char *));
  #pragma omp parallel for schedule(dynamic, 1)
  for (int i = 0; i < n; i++) {
    ll N = iv[i].hi;
    size_t sz = 0; char *buf = NULL; FILE *o = open_memstream(&buf, &sz);
    fprintf(o, "IV %lld %lld\n", iv[i].lo, N);
    Bucket bk[400]; int nb = lean_buckets(N, bk);
    mpz_t En; mpz_init(En);
    /* case order: Ib (any5), II (even), III1 (odd), III2b (odd), III2a (odd + any5) */
    static const int cimap[5] = {0, 2, 1, 1, 1};
    for (int c = 0; c < NCASE; c++) {
      const Prm *p = &iv[i].p[c];
      ll pc = p->pc > 0 ? p->pc : ((ll)(0.3 * sqrt((double)N)) > 2000 ? (ll)(0.3 * sqrt((double)N)) : 2000);
      int dA = p->dA ? p->dA : oddAtLeast(nPrimesEx(p->z, 1, 1));
      int dB = p->dB ? p->dB : oddAtLeast(nU1(p->zB));
      int dC = p->dC ? p->dC : oddAtLeast(nU1(p->z1));
      if (dA % 2 == 0) dA++; if (dB % 2 == 0) dB++; if (dC % 2 == 0) dC++;
      ll pB;
      if (c == 1) { pB = pB_of(N, 25, p); if (pB < p->z1) pB = p->z1; }
      else { pB = pB_of(N, 100, p); if (p->zB > pB) pB = p->zB; if (p->z1 > pB) pB = p->z1; }
      ll Yt = 1, Kt = 0;
      if (c >= 1) {
        Yt = snap_tail_Y(N, pB);
        i128 NN = (i128)N * N; ll M = (ll)((NN + 1) / ((i128)(Yt + 1) * (Yt + 1)));
        ll K = 0;
        while (K < M) { i128 G = 4 * (i128)(K + 1) > 9 ? 4 * (i128)(K + 1) : 9;
          i128 X2 = (i128)(K + 1) * (Yt + 1) * (Yt + 1) - 1;
          if (NN / G < X2) break; K++; }
        Kt = K;
      }
      fprintf(o, "P %d %d %d %d %d %d %d %lld %lld %lld %lld\n", p->z, dA, p->zB, dB, p->z1, p->z2, dC, pc, pB, Yt, Kt);
      int nl = c == 4 ? 2 : 1;
      for (int l = 0; l < nl; l++) {
        int ci = l == 0 ? cimap[c] : 0;
        /* cert.c uses ANY5 = 0, ODD = 1, EVEN = 2 like consOK */
        fprintf(o, "B %d", nb);
        for (int b = 0; b < nb; b++) {
          ll Y = snap_best_Y(N, pc, bk[b].xb, ci);
          en_exact(En, ci, N, bk[b].xb, Y);
          fprintf(o, " %lld ", Y); mpz_out_str(o, 10, En);
        }
        fprintf(o, "\n");
      }
    }
    mpz_clear(En);
    fclose(o); outs[i] = buf;
    #pragma omp critical
    { fprintf(stderr, "done %lld\n", iv[i].lo); }
  }
  snprintf(path, sizeof path, "%s/iv.txt", argv[3]); f = fopen(path, "w");
  for (int i = 0; i < n; i++) fputs(outs[i], f);
  fclose(f);
  return 0;
}
