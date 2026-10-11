"""Review fix for Lemma C (exact.lemC) under Bonferroni truncation.

exact.lemC charges each odd p2 != 5 with (23/25)(Leff/p2^2) B_d + 3 E_d.  The factor 23/25 comes
from "all classes minus the classes 7 and 18 mod 25"; the subtracted counts need LOWER bounds,
which an odd-depth truncation B_d does not give.  Valid per-p2 bounds (each class count in the
domain lies in [Leff/Q - mult, Leff/Q + mult] for odd Q):

  (a) union over all classes of C_p2, depth d:   (Leff/p2^2) B_d + E_d * mult
  (b) full inclusion-exclusion, three-way:       (23/25)(Leff/p2^2)(1 - prod(1 - 2/p^2)) + 3 (3^k' - 1) * mult
  (c) union inside T25 directly, depth d:        (23/25)(Leff/p2^2) B_d + 23 E_d * mult

non(p2) = min of (a), (b), (c).  For U1 primes p2 in S_b the term is whole(p2) = (23/25) Leff/p2^2 + 3 mult.
Instead of monotonicity of g = whole - non (Lemma C1), use: |S_b ∩ [1,z2]| <= nS, so
sum_{p in S_b, p <= z2} g(p) <= sum of the nS largest values of max(g, 0) over U1 primes p <= z2.

    python3 review_fix.py cert_best_lo.csv i1 i2 ...     # re-check rows i (0-based) with the fix
    python3 review_fix.py scan in.csv out.csv            # re-check every row (parallel, WORKERS)
"""
import sys, os, json
from fractions import Fraction as F
import exact as X

def lemC_fixed(N, Leff, mult, xb, z1, z2, pc, pB, dC):
    nS = X.S_prefix_len(xb, z2)
    Leff = F(Leff); pB2 = max(pB, z1)
    v = F(2 * 23, 25) * X.s2(z1, pB2, X.P1, X.SP1I) * Leff + 2 * 23 * X.cnt(z1, pB2, X.P1) * mult
    U = [p for p in X.P1 if p <= z1]
    U1set = set(X.P1)
    gs = []
    for p2 in X.PR[1:]:
        if p2 > z2: break
        others = [F(2, p * p) for p in U if p != p2]
        md, ed = X.ie(others, 2, dC)          # depth-d Bonferroni (dC None: full)
        mf, ef = X.ie(others, 2, None)        # full inclusion-exclusion
        Q = F(1, p2 * p2) * Leff
        if p2 == 5:
            v += md * Leff / 25 + ed * mult   # one whole class mod 25, direct
            continue
        non = min(Q * md + ed * mult,
                  F(23, 25) * Q * mf + 3 * ef * mult,
                  F(23, 25) * Q * md + 23 * ed * mult)
        v += non
        if p2 in U1set:
            whole = F(23, 25) * Q + 3 * mult
            gs.append(max(whole - non, F(0)))
    gs.sort(reverse=True)
    v += sum(gs[:nS])
    v += X.s2(z2, pc) * Leff + X.cnt(z2, pc) * mult
    return v

X.lemC = lemC_fixed

def check_row(row):
    Nlo, Nhi, prm = row
    r = X.check(Nlo, Nhi, prm)
    return Nlo, Nhi, {k: float(v) for k, v in r.items()}

def rows(path):
    import csv
    out = []
    with open(path) as f:
        for d in csv.DictReader(f):
            out.append((int(d['Nlo']), int(d['Nhi']), json.loads(d['params'].replace("'", '"'))))
    return out

if __name__ == "__main__":
    if sys.argv[1] == "scan":
        from multiprocessing import Pool
        R = rows(sys.argv[2])
        with Pool(int(os.environ.get("WORKERS", "4"))) as P, open(sys.argv[3], "w") as f:
            for lo, hi, r in P.imap_unordered(check_row, R):
                m = max(r.values())
                f.write("%d,%d,%.9f,%s,%s\n" % (lo, hi, m, "ok" if m < 1 else "FAIL", json.dumps(r))); f.flush()
    else:
        R = rows(sys.argv[1])
        for i in sys.argv[2:]:
            lo, hi, r = check_row(R[int(i)])
            print(lo, hi, " ".join("%s %.4f" % kv for kv in r.items()), flush=True)
