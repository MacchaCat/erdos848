// Independent check of the E2 discrepancy table.
// Line format: e k q_1..q_k P=<P> phi=<phi> beta0num=<bn>
// Claim: with g(m) = #{s mod P : s^2 m == 1 (mod P)}, P = 2^e * prod q_i,
//   sum_{m mod P} g(m) = phi(P),  and  max_{0<=R<P} (P*G(R) - R*phi) <= bn,  G(R) = sum_{1<=m<=R} g(m).
// g is computed by brute force over s for small P (cross-check), and by CRT (r_{2^e} * prod (1+legendre)) otherwise.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int isqr[100][100]; // isqr[q][x] = 1 if x is a nonzero square mod q
static int r2(int e, ll m) {
  if (e == 0) return 1;
  if (e == 1) return (m & 1) ? 1 : 0;
  if (e == 2) return (m % 4 == 1) ? 2 : 0;
  return (m % 8 == 1) ? 4 : 0;
}
int main(int argc, char **argv) {
  for (int q = 3; q < 100; q++) { for (int x = 1; x < q; x++) isqr[q][(x * x) % q] = 1; }
  static char line[4096];
  ll nlines = 0, bad = 0, brute = 0, worst_slack = -1;
  // read all lines first
  int cap = 40000, n = 0;
  char **L = malloc(sizeof(char *) * cap);
  FILE *f = fopen(argv[1], "r");
  while (fgets(line, sizeof line, f)) { L[n++] = strdup(line); }
  fclose(f);
  #pragma omp parallel for schedule(dynamic, 16) reduction(+:bad,brute,nlines)
  for (int i = 0; i < n; i++) {
    int e, k, q[64]; ll P, phi, bn; char *s = L[i]; int off;
    sscanf(s, "%d %d%n", &e, &k, &off); s += off;
    for (int j = 0; j < k; j++) { sscanf(s, "%d%n", &q[j], &off); s += off; }
    sscanf(s, " P=%lld phi=%lld beta0num=%lld", &P, &phi, &bn);
    ll P2 = 1LL << e, Pc = P2, phic = (e == 0) ? 1 : (P2 / 2);
    for (int j = 0; j < k; j++) { Pc *= q[j]; phic *= (q[j] - 1); }
    int ok = (Pc == P) && (phic == phi);
    ll G = 0, mx = 0;  // R = 0 gives 0
    for (ll m = 1; m <= P; m++) {
      int g = r2(e, m % P2);
      for (int j = 0; j < k && g; j++) g *= isqr[q[j]][m % q[j]] ? 2 : 0;
      G += g;
      if (m < P) { ll v = P * G - m * phi; if (v > mx) mx = v; }
    }
    if (G != phi) ok = 0;
    if (mx > bn) ok = 0;
    if (P <= 3000) {  // brute-force g for small P
      brute++;
      ll G2 = 0;
      for (ll m = 1; m <= P; m++) { int c = 0; for (ll t = 0; t < P; t++) if ((t * t % P) * (m % P) % P == 1 % P) c++; G2 += c;
        int g = r2(e, m % P2); for (int j = 0; j < k && g; j++) g *= isqr[q[j]][m % q[j]] ? 2 : 0;
        if (c != g) ok = 0; }
    }
    nlines++;
    if (!ok) { bad++;
      #pragma omp critical
      fprintf(stderr, "BAD line %d: %s  (P=%lld phi=%lld G=%lld mx=%lld bn=%lld)\n", i + 1, L[i], P, phi, G, mx, bn); }
  }
  printf("lines %lld, bad %lld, brute-force cross-checked %lld\n", nlines, bad, brute);
  return bad != 0;
}
