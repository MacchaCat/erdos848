# Threshold computation, version 2: refined casework (mod 4 splitting, shared witness errors, Lemma C).
#
# Notation: for a witness b, an integer a is "compatible" if mu(ab+1) = 0, i.e. p^2 | ab+1 for a
# prime p ∤ b.  We split such p into  small (p <= z, inclusion-exclusion inside each residue class),
# restricted-mid (z < p <= pc, counted inside each residue class), and the SHARED part
#   Mid(b) = {a <= N : p^2 | ab+1 for some pc < p <= Y}   |Mid| <= sum_{pc<p<=Y} (N/p^2 + 1)
#   Ex(b)  = {a <= N : p^2 | ab+1 for some p > Y}         |Ex|  <= rho*(b)(2(N+1)/Y + (Nb+1)/Y^2)
# Mid(b), Ex(b) are sets of integers; they are counted ONCE per witness, whatever parts of A are sieved.
#
# Every bound has the shape  C*N + E(N)  with E nondecreasing in N for fixed parameters.
import math, bisect, sys
from fractions import Fraction

PMAX = 2 * 10**7
sv = bytearray([1]) * (PMAX + 1); sv[0] = sv[1] = 0
for i in range(2, int(PMAX ** 0.5) + 1):
    if sv[i]: sv[i*i::i] = bytearray(len(sv[i*i::i]))
PR = [i for i in range(PMAX + 1) if sv[i]]
del sv
P1 = [p for p in PR if p % 4 == 1 and p >= 13]          # "U1 primes": p ≡ 1 (4), p >= 13
def prefix(lst):
    s = [0.0]; acc = 0.0
    for p in lst: acc += 1.0 / (p * p); s.append(acc)
    return s
SP, SP1 = prefix(PR), prefix(P1)
TAILN = 1.0 / (PMAX - 1)
INF = 1 + 1e-9
def pi(x):
    if x < 2: return 0
    if x <= PMAX: return bisect.bisect_right(PR, x)
    return 1.25506 * x / math.log(x)
def pi1(x):
    if x <= PMAX: return bisect.bisect_right(P1, x)
    return pi(x)
def s2(lo, hi, lst=PR, S=SP):           # sum_{lo<p<=hi, p in lst} 1/p^2   (upper bound)
    if hi <= lo: return 0.0
    a = bisect.bisect_right(lst, lo); b = bisect.bisect_right(lst, min(hi, PMAX))
    r = S[b] - S[a]
    if hi > PMAX: r += TAILN
    return r
def cnt(lo, hi, lst=PR):                # number of p in lst with lo < p <= hi
    if hi <= lo: return 0
    if hi <= PMAX: return bisect.bisect_right(lst, hi) - bisect.bisect_right(lst, lo)
    return pi(hi)                        # crude
def rho_max(N, need_coprime5=False):
    best = 1
    odd = [p for p in PR[1:60] if not (need_coprime5 and p == 5)]
    for c2, f in ((1, 1), (2, 4), (4, 8)):
        prod, w = f, 0
        for p in odd:
            if prod * p > N: break
            prod *= p; w += 1
        if prod <= N: best = max(best, c2 * 2 ** w)
    return best
def prod_small(z, excl, factor=1):      # prod_{p<=z, p∉excl}(1 - factor/p^2), number of primes
    pr = Fraction(1); k = 0
    for p in PR:
        if p > z: break
        if p in excl: continue
        pr *= Fraction(p * p - factor, p * p); k += 1
    return float(pr), k

class Bound:
    def __init__(s): s.C = 0.0; s.E = 0.0
    def add(s, C=0.0, E=0.0): s.C += C * INF; s.E += E * INF + (1 if E else 0); return s

# ---- restricted sieve of the classes T (mod q) by one witness (primes in excl cannot occur) ----
def restricted(B, T, q, excl, z, pc, N):
    pr, k = prod_small(z, excl)
    B.add(C=T / q * (1 - pr), E=T * (2 ** k - 1))
    lo = z
    # z < p <= pc, p ∉ excl (excl only contains 2,5 here, both <= z)
    B.add(C=T / q * s2(lo, pc), E=T * cnt(lo, pc))
# ---- shared part for one witness ----
def shared(B, pc, Y, N, rho):
    B.add(C=s2(pc, Y) + (TAILN if Y > PMAX else 0), E=cnt(pc, Y))
    B.add(E=rho * (2 * (N + 1) / Y + (N * N + 1) / (Y * Y)))
# ---- Lemma B: n mod q in T (|T| classes), p^2 | n^2+1 for a U1 prime ----
def lemB(B, T, q, zB, pB, Yp, N):
    pr = Fraction(1); k = 0
    for p in P1:
        if p > zB: break
        pr *= Fraction(p * p - 2, p * p); k += 1
    B.add(C=T / q * (1 - float(pr)), E=T * (3 ** k - 1))
    pB = max(pB, zB)
    B.add(C=2 * T / q * s2(zB, pB, P1, SP1), E=2 * T * cnt(zB, pB, P1))
    if Yp > pB: B.add(C=2 * s2(pB, Yp, P1, SP1), E=2 * cnt(pB, Yp, P1))
    B.add(E=(math.floor((N * N + 1) / (Yp * Yp)) + 1) * (0.5673 * math.log(2 * N + 1) + 0.5))
# ---- Lemma C: A* (T = 23 classes mod 25) compatible with an even witness b ----
def lemC(B, zB, pB, Yp, z1, z2, pc, N, Sall=False, Nlo=None):
    if Nlo is None: Nlo = N
    # (a) U1-part with large U1 prime p1 > z1 (not intersected with the witness condition)
    pB = max(pB, z1)
    B.add(C=2 * 23 / 25 * s2(z1, pB, P1, SP1), E=2 * 23 * cnt(z1, pB, P1))
    if Yp > pB: B.add(C=2 * s2(pB, Yp, P1, SP1), E=2 * cnt(pB, Yp, P1))
    B.add(E=(math.floor((N * N + 1) / (Yp * Yp)) + 1) * (0.5673 * math.log(2 * N + 1) + 0.5))
    # (b) x in C_{p2} (p2 odd, p2 <= z2) and x in U1 via p1 <= z1
    U1small = [p for p in P1 if p <= z1]
    # Admissible S_b: U1 primes p with b in R_p satisfy prod p^2 | b^2+1 <= N^2+1, so prod_{S_b} p <= sqrt(N^2+1).
    # For each odd p2 <= z2 the bound is  non(p2) + [p2 in S_b] * g(p2),  where g = whole - non.
    # g(p) is decreasing in p (see proof), so  sum_{p in S_b} g(p) <= sum_{i <= |S_b|} max(g(prefix_i), 0)
    # with prefix = smallest U1 primes subject to the product constraint (evaluated at Nhi = N, the largest N).
    S = []; prod = 1
    for p in P1:
        if not Sall and prod * p > math.sqrt(N * N + 1): break
        if p > z2: break
        S.append(p); prod *= p
    k1 = len(U1small)
    for p2 in PR[1:]:
        if p2 > z2: break
        others = [p for p in U1small if p != p2]
        pr = 1.0
        for p in others: pr *= 1 - 2 / p / p
        kk = len(others)
        if p2 == 5:
            B.add(C=1 / 25 * (1 - pr), E=3 ** kk)
            continue
        nonC, nonE = 23 / 25 / p2**2 * (1 - pr), 3 * 3 ** kk
        B.add(C=nonC, E=nonE)
        if p2 in S:
            wholeC, wholeE = 23 / 25 / p2**2, 3
            dC, dE = wholeC - nonC, wholeE - nonE          # dC > 0, dE < 0
            # gain over [Nlo, N]: if positive at Nlo it is dC*n + dE for all n >= Nlo; otherwise bound by dC*n
            if dC * Nlo + dE > 0: B.add(C=dC, E=0); B.E += dE   # exact linear gain (dE negative)
            else: B.add(C=dC, E=0)
    # (c) z2 < p2 <= pc: plain count of the class C_{p2} (not intersected with U1)
    B.add(C=s2(z2, pc), E=cnt(z2, pc))
    # p2 > pc: inside the shared sets Mid(b), Ex(b) of the witness

def best_shared(N, pc, rho):
    best = None; Y = max(pc * 1.0, 1000.0)
    while Y < 4 * N:
        B = Bound(); shared(B, pc, Y, N, rho); v = B.C * N + B.E
        if best is None or v < best[0]: best = (v, Y, B.C, B.E)
        Y *= 1.04
    return best
def best_lemB(N, T, q, zB):
    pB = math.sqrt(N * (1 - T / q) / max(T - 1, 1))
    best = None; Yp = max(pB, 1000.0)
    while Yp < 4 * N:
        B = Bound(); lemB(B, T, q, zB, pB, Yp, N); v = B.C * N + B.E
        if best is None or v < best[0]: best = (v, Yp, B.C, B.E)
        Yp *= 1.04
    return best

def cases(Nlo, Nhi, z=31, pc=None, zB=41, z1=41, z2=1000):
    N = Nhi
    if pc is None: pc = max(2000, int(0.3 * math.sqrt(N)))
    rho = rho_max(N)
    _, Ysh, Csh, Esh = best_shared(N, pc, rho)
    def SH(B): B.add(C=Csh, E=Esh)
    out = {}
    # I.b : witnesses b in A7 (sieves A18), b' in A18 (sieves A7); parity unknown -> excl {5}
    B = Bound(); restricted(B, 1, 25, {5}, z, pc, N); SH(B); restricted(B, 1, 25, {5}, z, pc, N); SH(B); out['I.b'] = B
    # II : even witness b in A*: A7 ∪ A18 (2 classes mod 25, excl {2,5}) + Lemma C for A*
    _, Yp, CB, EB = best_lemB(N, 23, 25, zB)
    B = Bound(); restricted(B, 2, 25, {2, 5}, z, pc, N); SH(B)
    Bc = Bound(); best = None
    lemC(Bc, zB, max(1, math.sqrt(N * (1 - 23 / 25) / 22)), Yp, z1, z2, pc, N, Nlo=Nlo)
    B.add(C=Bc.C, E=Bc.E); out['II'] = B
    # III.1 : b1 ≡ 1, b3 ≡ 3 (mod 4) in A*; A7∪A18 classes mod 100: 6 sieved by b1, 2 by b3; A* odd (23 classes mod 50)
    _, _, CB50, EB50 = best_lemB(N, 23, 50, zB)
    B = Bound(); restricted(B, 6, 100, {2, 5}, z, pc, N); SH(B); restricted(B, 2, 100, {2, 5}, z, pc, N); SH(B); B.add(C=CB50, E=EB50); out['III.1'] = B
    # III.2.a : A* ⊆ one class mod 4 (23 classes mod 100), A7∪A18 odd: 2 classes free, 2 sieved by b
    _, _, CB100, EB100 = best_lemB(N, 23, 100, zB)
    B = Bound(); B.add(C=2 / 100, E=2); restricted(B, 2, 100, {2, 5}, z, pc, N); SH(B); B.add(C=CB100, E=EB100); out['III.2.a'] = B
    # III.2.b : as III.2 but an even b' in A7∪A18: 1 class free, 3 sieved by b, 4 sieved by b'
    B = Bound(); B.add(C=1 / 100, E=1); restricted(B, 3, 100, {2, 5}, z, pc, N); SH(B); restricted(B, 4, 100, {2, 5}, z, pc, N); SH(B); B.add(C=CB100, E=EB100); out['III.2.b'] = B
    target = (Nlo - 6) / 25
    cases.last = dict(pc=pc, Y=Ysh, Yp25=Yp, rho=rho, out={k: (b.C, b.E) for k, b in out.items()})
    return {k: ((b.C * Nlo + b.E) / target, b.C * 25) for k, b in out.items()}

if __name__ == "__main__":
    if sys.argv[1] == "probe":
        for e in [float(x) for x in sys.argv[2:]]:
            N = 10 ** e
            r = cases(N, N)
            print("N=10^%.2f " % e + "  ".join("%s:%.4f(%.3f)" % (k, v[0], v[1]) for k, v in r.items()), flush=True)
    elif sys.argv[1] == "scan":
        # usage: scan Nstart Nend step [certificate.csv]
        # Intervals [Nlo, Nhi] with Nhi = Nlo*step cover [Nstart, Nend] (consecutive intervals share endpoints).
        # For each interval and case we record C (main coefficient), E (error evaluated at Nhi) and
        # ratio = (C*Nlo + E) / ((Nlo-6)/25); the certificate requires ratio < 0.999.
        N = float(sys.argv[2]); Nend = float(sys.argv[3]); step = float(sys.argv[4]); worst = 0; n = 0
        out = open(sys.argv[5], "w") if len(sys.argv) > 5 else None
        names = ["I.b", "II", "III.1", "III.2.a", "III.2.b"]
        if out:
            out.write("Nlo,Nhi,pc,Y_shared,Yprime_B25,rho_max," + ",".join("C_%s,E_%s,ratio_%s" % (k, k, k) for k in names) + "\n")
        while N < Nend:
            Nhi = min(N * step, Nend) if N * step > Nend else N * step
            r = cases(N, Nhi); m = max(v[0] for v in r.values()); worst = max(worst, m); n += 1
            if out:
                L = cases.last
                out.write("%.17g,%.17g,%d,%.17g,%.17g,%d," % (N, Nhi, L["pc"], L["Y"], L["Yp25"], L["rho"]) +
                          ",".join("%.17g,%.17g,%.9f" % (L["out"][k][0], L["out"][k][1], r[k][0]) for k in names) + "\n")
            if m >= 0.999: print("FAIL [%.6g,%.6g] %s" % (N, Nhi, r), flush=True); sys.exit(1)
            N = Nhi
        print("scan OK %.6g..%.6g intervals=%d worst=%.5f" % (float(sys.argv[2]), Nend, n, worst), flush=True)
