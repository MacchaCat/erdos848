"""Exact (rational-arithmetic) verification of the analytic part, N >= 1.6e8.

This re-evaluates every bound of n0_v2.py with exact arithmetic, so the result does not depend on
floating-point rounding:
  * sums of 1/p^2 over primes are bounded ABOVE by sums of ceil(10^40/p^2)/10^40 (Python integers);
  * pi(x) is exact for x <= PMAX; above PMAX we use pi(x) < 1.25506 x / ln x with a rational
    LOWER bound for ln x;
  * ln(2N+1) in the Pell term is replaced by a rational UPPER bound;
  * ln bounds come from mpmath at 60 digits with a 1e-50 safety margin in the safe direction;
  * products of (1 - c/p^2), floors, rho_max, the S_b prefix test (prod^2 <= N^2+1) are exact.
Parameters (Y, Y', p_B, p_c) are integers chosen by the floating-point optimiser of n0_v2.py;
any choice of parameters gives a valid bound, so this choice needs no verification.

Usage:  python3 n0_exact.py scan Nstart Nend step out.csv [--cheb]
        python3 n0_exact.py tail [--cheb]
        add --lean instead of --cheb to use exactly the bounds proved in Lean (Chebyshev prime bound
        and the elementary Pell growth bound of PellTail.lean)
With --cheb the Rosser-Schoenfeld bound is replaced by pi(x) <= sqrt(x) + 2 log(4) x/log x, which
follows from Chebyshev's theta(x) <= x log 4 (available in Mathlib); this is the version intended
for the Lean formalisation.
Each interval [Nlo, Nhi] (integer endpoints, Nhi = floor(Nlo*step), consecutive intervals share
endpoints) is accepted iff for every case
C*Nlo + E(Nhi) < (Nlo-6)/25 and C < 1/25 (Lemma D of proof.md).
"""
import sys, math, bisect
from fractions import Fraction as F
import mpmath
import n0_v2 as M          # only for the prime table and the float parameter optimiser

mpmath.mp.dps = 60
SCALE = 10 ** 40
EPS = F(1, 10 ** 50)
PR, P1, PMAX = M.PR, M.P1, M.PMAX

def prefix_int(lst):
    s = [0]; acc = 0
    for p in lst:
        acc += -(-SCALE // (p * p))          # ceil(SCALE/p^2)
        s.append(acc)
    return s
SPI, SP1I = prefix_int(PR), prefix_int(P1)
TAIL = F(1, PMAX - 1)                         # sum_{n > PMAX} 1/n^2 < 1/(PMAX-1)

def s2(lo, hi, lst=PR, S=SPI):                # upper bound for sum_{lo<p<=hi, p in lst} 1/p^2
    if hi <= lo: return F(0)
    a = bisect.bisect_right(lst, lo); b = bisect.bisect_right(lst, min(hi, PMAX))
    r = F(S[b] - S[a], SCALE)
    if hi > PMAX: r += TAIL
    return r
def ln_lo(x):  return F(str(mpmath.log(mpmath.mpf(x.numerator) / x.denominator))) - EPS
def ln_hi(x):  return F(str(mpmath.log(mpmath.mpf(x.numerator) / x.denominator))) + EPS
def pi_up(x):
    x = F(x)
    if x < 2: return F(0)
    if x <= PMAX: return F(bisect.bisect_right(PR, math.floor(x)))
    return F(125506, 100000) * x / ln_lo(x)
CHEB = False      # --cheb: use only pi(x) <= sqrt(x) + 2 log(4) x / log(x)  (derivable from Mathlib)
LOG4_UP = F(13863, 10000)   # log 4 = 1.38629... < 1.3863
def pi_up_cheb(x):
    """pi(x) <= pi(sqrt x) + theta(x) / log(sqrt x) <= sqrt(x) + 2 log4 * x / log x,
    using Chebyshev's theta(x) <= x log 4 (Mathlib: Chebyshev.theta_le_log4_mul_x)."""
    x = F(x)
    if x < 2: return F(0)
    if x <= PMAX: return F(bisect.bisect_right(PR, math.floor(x)))
    return F(math.isqrt(math.floor(x)) + 1) + 2 * LOG4_UP * x / ln_lo(x)
def set_cheb():
    global CHEB, pi_up
    CHEB = True
    pi_up = pi_up_cheb
    origM = M.pi
    def pi_f(x):
        if x <= M.PMAX: return origM(x)
        return math.isqrt(int(x)) + 1 + 2 * 1.3863 * x / math.log(x)
    M.pi = pi_f          # the float optimiser chooses parameters for the same bound
def pell_lean(N, Yp):
    """Pell tail as proved in Lean (PellTail.lean, pellTail_le):
    #{n <= N : p^2 | n^2+1 for some p > Y'} <= floor((N^2+1)/(Y'+1)^2) * (log_3 N + 1);
    bounded above by (floor((N^2+1)/Y'^2) + 1) * (ln(2N+1)/ln 3 + 1), with 1/ln 3 < 0.9103."""
    m = (N * N + 1) / (Yp * Yp)
    return (math.floor(m) + 1) * (F(9103, 10000) * ln_hi(2 * N + 1) + 1)
def set_lean():
    """--lean: exactly the lemmas available in the Lean development (Chebyshev prime bound,
    elementary Pell growth)."""
    global pell
    set_cheb()
    pell = pell_lean
def pi1_up(x):
    x = F(x)
    if x <= PMAX: return F(bisect.bisect_right(P1, math.floor(x)))
    return pi_up(x)
def cnt(lo, hi, lst=PR):
    lo, hi = F(lo), F(hi)
    if hi <= lo: return F(0)
    if hi <= PMAX: return F(bisect.bisect_right(lst, math.floor(hi)) - bisect.bisect_right(lst, math.floor(lo)))
    return pi_up(hi)
def prod_small(z, excl, c=1):
    pr = F(1); k = 0
    for p in PR:
        if p > z: break
        if p in excl: continue
        pr *= F(p * p - c, p * p); k += 1
    return pr, k
def rho_max(N):
    best = 1
    for c2, f in ((1, 1), (2, 4), (4, 8)):
        prod, w = f, 0
        for p in PR[1:60]:
            if prod * p > N: break
            prod *= p; w += 1
        if prod <= N: best = max(best, c2 * 2 ** w)
    return best

class B:
    def __init__(s): s.C = F(0); s.E = F(0)
    def add(s, C=0, E=0): s.C += F(C); s.E += F(E); return s

def restricted(b, T, q, excl, z, pc):
    pr, k = prod_small(z, excl)
    b.add(C=F(T, q) * (1 - pr), E=T * (2 ** k - 1))
    b.add(C=F(T, q) * s2(z, pc), E=T * cnt(z, pc))
def shared(b, pc, Y, N, rho):
    b.add(C=s2(pc, Y), E=cnt(pc, Y))
    b.add(E=rho * (2 * (N + 1) / Y + (N * N + 1) / (Y * Y)))
def pell(N, Yp):
    m = (N * N + 1) / (Yp * Yp)
    return (math.floor(m) + 1) * (F(5673, 10000) * ln_hi(2 * N + 1) + F(1, 2))
def lemB(b, T, q, zB, pB, Yp, N):
    pr = F(1); k = 0
    for p in P1:
        if p > zB: break
        pr *= F(p * p - 2, p * p); k += 1
    b.add(C=F(T, q) * (1 - pr), E=T * (3 ** k - 1))
    pB = max(pB, zB)
    b.add(C=2 * F(T, q) * s2(zB, pB, P1, SP1I), E=2 * T * cnt(zB, pB, P1))
    if Yp > pB: b.add(C=2 * s2(pB, Yp, P1, SP1I), E=2 * cnt(pB, Yp, P1))
    b.add(E=pell(N, Yp))
def lemC(b, zB, pB, Yp, z1, z2, pc, N, Nlo, Sall=False):
    pB = max(pB, z1)
    b.add(C=2 * F(23, 25) * s2(z1, pB, P1, SP1I), E=2 * 23 * cnt(z1, pB, P1))
    if Yp > pB: b.add(C=2 * s2(pB, Yp, P1, SP1I), E=2 * cnt(pB, Yp, P1))
    b.add(E=pell(N, Yp))
    U1small = [p for p in P1 if p <= z1]
    S = []; prod = 1
    for p in P1:
        if p > z2: break
        if not Sall and (prod * p) ** 2 > N * N + 1: break
        S.append(p); prod *= p
    for p2 in PR[1:]:
        if p2 > z2: break
        others = [p for p in U1small if p != p2]
        pr = F(1)
        for p in others: pr *= F(p * p - 2, p * p)
        kk = len(others)
        if p2 == 5:
            b.add(C=F(1, 25) * (1 - pr), E=3 ** kk); continue
        nonC, nonE = F(23, 25) / (p2 * p2) * (1 - pr), 3 * 3 ** kk
        b.add(C=nonC, E=nonE)
        if p2 in S:
            dC, dE = F(23, 25) / (p2 * p2) - nonC, 3 - nonE
            if dC * Nlo + dE > 0: b.add(C=dC, E=dE)
            else: b.add(C=dC)
    b.add(C=s2(z2, pc), E=cnt(z2, pc))

def params(Nhi_f):
    """integer parameters from the float optimiser (any choice is valid)"""
    pc = max(2000, int(0.3 * math.sqrt(Nhi_f)))
    rho = M.rho_max(Nhi_f)
    Y = int(M.best_shared(Nhi_f, pc, rho)[1])
    YB = {}
    for (T, q) in ((23, 25), (23, 50), (23, 100)):
        YB[q] = int(M.best_lemB(Nhi_f, T, q, 41)[1])
    pB = {q: int(math.sqrt(Nhi_f * (1 - 23 / q) / 22)) for q in (25, 50, 100)}
    return pc, Y, YB, pB

def cases_exact(Nlo, Nhi, pc, Y, YB, pB, z=31, zB=41, z1=41, z2=1000, rho=None, Sall=False):
    N = Nhi
    if rho is None: rho = F(rho_max(math.floor(Nhi)))
    def SH(b): shared(b, pc, Y, N, rho)
    out = {}
    b = B(); restricted(b, 1, 25, {5}, z, pc); SH(b); restricted(b, 1, 25, {5}, z, pc); SH(b); out['I.b'] = b
    b = B(); restricted(b, 2, 25, {2, 5}, z, pc); SH(b)
    lemC(b, zB, pB[25], YB[25], z1, z2, pc, N, Nlo, Sall); out['II'] = b
    def LB(T, q):
        bb = B(); lemB(bb, T, q, zB, pB[q], YB[q], N); return bb
    b = B(); restricted(b, 6, 100, {2, 5}, z, pc); SH(b); restricted(b, 2, 100, {2, 5}, z, pc); SH(b)
    x = LB(23, 50); b.add(C=x.C, E=x.E); out['III.1'] = b
    b = B(); b.add(C=F(2, 100), E=2); restricted(b, 2, 100, {2, 5}, z, pc); SH(b); x = LB(23, 100); b.add(C=x.C, E=x.E); out['III.2.a'] = b
    b = B(); b.add(C=F(1, 100), E=1); restricted(b, 3, 100, {2, 5}, z, pc); SH(b); restricted(b, 4, 100, {2, 5}, z, pc); SH(b)
    x = LB(23, 100); b.add(C=x.C, E=x.E); out['III.2.b'] = b
    return out

NAMES = ["I.b", "II", "III.1", "III.2.a", "III.2.b"]

def scan(Nstart, Nend, step, path):
    Nlo = F(Nstart); Nend = F(Nend); step = F(step); n = 0; worst = F(0)
    with open(path, "w") as f:
        f.write("Nlo_num,Nlo_den,Nhi_num,Nhi_den,pc,Y,YB25,YB50,YB100,pB25,pB50,pB100,rho," +
                ",".join("C_%s,E_%s,ratio_up_%s" % (k, k, k) for k in NAMES) + "\n")
        while Nlo < Nend:
            Nhi = F(min(math.floor(Nlo * step), math.floor(Nend))) if Nlo * step < Nend else Nend   # integer endpoints
            pc, Y, YB, pB = params(float(Nhi))
            rho = rho_max(math.floor(Nhi))
            out = cases_exact(Nlo, Nhi, pc, F(Y), {q: F(v) for q, v in YB.items()}, {q: F(v) for q, v in pB.items()}, rho=F(rho))
            target = (Nlo - 6) / 25
            row = [Nlo.numerator, Nlo.denominator, Nhi.numerator, Nhi.denominator, pc, Y, YB[25], YB[50], YB[100], pB[25], pB[50], pB[100], rho]
            for k in NAMES:
                b = out[k]; r = (b.C * Nlo + b.E) / target
                assert b.C < F(1, 25), (k, float(Nlo))
                if not r < 1:
                    print("FAIL", float(Nlo), float(Nhi), k, float(r)); sys.exit(1)
                worst = max(worst, r)
                row += ["%.25e" % float(b.C), "%.25e" % float(b.E), "%.12f" % (math.ceil(float(r) * 1e12) / 1e12)]
            f.write(",".join(str(v) for v in row) + "\n")
            n += 1; Nlo = Nhi
    print("EXACT scan OK [%.6g, %.6g]: %d intervals, worst ratio %.6f" % (Nstart, float(Nend), n, float(worst)), flush=True)

def tail():
    """N >= NT: evaluate the tail bound exactly at NT (monotonicity of E(N)/N is the analytic part of §6.4)."""
    NT = F(10) ** 60
    lnlnNT = mpmath.log(mpmath.log(mpmath.mpf(10) ** 60))
    assert lnlnNT > mpmath.mpf("4.927")
    expo = F(1950, 10000)
    assert F(str(1.3841 * mpmath.log(2) / mpmath.mpf("4.927"))) + EPS < expo
    # rho* <= 2 * NT^0.195 : rational upper bound
    rho = F(str(mpmath.mpf(2) * mpmath.power(mpmath.mpf(10) ** 60, mpmath.mpf("0.195")))) + 1
    Y = F(math.floor(mpmath.power(mpmath.mpf(10) ** 60, mpmath.mpf("0.7"))))
    pc = 2000
    out = cases_exact(NT, NT, pc, Y, {25: Y, 50: Y, 100: Y}, {25: 2000, 50: 2000, 100: 2000}, rho=rho, Sall=True)
    worst = F(0)
    for k in NAMES:
        b = out[k]; r = (b.C * NT + b.E) / ((NT - 6) / 25)
        print("%-8s 25*C = %.6f   ratio at 10^60 = %.6f" % (k, float(25 * b.C), float(r)))
        assert r < 1; worst = max(worst, r)
    print("EXACT tail OK at N = 10^60 (worst %.6f)" % float(worst))

if __name__ == "__main__":
    if "--cheb" in sys.argv:
        sys.argv.remove("--cheb"); set_cheb()
    if "--lean" in sys.argv:
        sys.argv.remove("--lean"); set_lean()
    if sys.argv[1] == "scan":
        scan(F(sys.argv[2]), F(sys.argv[3]), F(sys.argv[4]), sys.argv[5])
    else:
        tail()
