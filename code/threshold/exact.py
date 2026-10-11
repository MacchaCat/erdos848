"""Exact (rational) re-evaluation of the best combination of improved bounds, for interval certificates.

Independent re-implementation of the formulas (REPORT.md, Lemmas A'', E, P, H, W, C', S) in Fractions.
Only the *choice of parameters* (z, pc, Bonferroni depths, z_B, z1, z2, p_B, and the cut-offs Y, Y'
for every witness bucket) comes from the floating-point optimiser in bounds.py/cases.py; every
choice of parameters gives a valid bound, so these choices need no verification.

One floating-point shortcut is used: inside the max over witness structures in Ex (Lemma E2),
structures whose float value is below (1 - 1e-6) * (float max) are skipped; their exact value is
smaller than the exact max because each float value is the same formula evaluated with a handful
of IEEE operations (relative error < 1e-13).  All structures within 1e-6 of the max are evaluated exactly.

    python3 exact.py check Nlo Nhi            # one interval
    python3 exact.py scan N0 N1 step out.csv  # certificate scan (parallel)
"""
import sys, math, bisect, json, os, time, itertools
from fractions import Fraction as F
from math import isqrt, comb
import bounds as Bd
import cases as C

BEST = dict(cons=True, ex1=True, pell2=True, u1half=True, exavg=True, opt=True, bonf=True,
            minw=True, cases2=True, lcodd=True, w97=True)
PR, P1, PMAX = Bd.PR, Bd.P1, Bd.PMAX
SCALE = 10 ** 40
def _pref(lst):
    s = [0]; a = 0
    for p in lst: a += -(-SCALE // (p * p)); s.append(a)
    return s
SPI, SP1I = _pref(PR), _pref(P1)
TAIL = F(1, PMAX - 1)

def s2(lo, hi, lst=PR, S=SPI):
    if hi <= lo: return F(0)
    a = bisect.bisect_right(lst, lo); b = bisect.bisect_right(lst, min(hi, PMAX))
    r = F(S[b] - S[a], SCALE)
    if hi > PMAX: r += TAIL
    return r
def cnt(lo, hi, lst=PR):
    if hi <= lo: return 0
    assert hi <= PMAX, "prime counts beyond the table are not needed for N <= 1.6e8"
    return bisect.bisect_right(lst, int(hi)) - bisect.bisect_right(lst, int(lo))

def ie(vals, ncls, depth):
    k = len(vals)
    if depth is None or depth >= k:
        pr = F(1)
        for v in vals: pr *= 1 - v
        return 1 - pr, (1 + ncls) ** k - 1
    e = [F(1)] + [F(0)] * depth
    for v in vals:
        for j in range(depth, 0, -1): e[j] += e[j - 1] * v
    return sum((-1) ** (j + 1) * e[j] for j in range(1, depth + 1)), sum(comb(k, j) * ncls ** j for j in range(1, depth + 1))

_cache = {}
def restricted(T, q, excl, z, pc, L, dA):
    key = ('R', T, q, frozenset(excl), z, pc, dA)
    if key not in _cache:
        ps = [p for p in PR if p <= z and p not in excl]
        main, err = ie([F(1, p * p) for p in ps], 1, dA)
        _cache[key] = (T * (main + s2(z, pc)) / q, T * (err + cnt(z, pc)))
    a, c = _cache[key]
    return a * L + c

def lemB_perclass(T, q, zB, pB, L, dB):
    key = ('B', T, q, zB, pB, dB)
    if key not in _cache:
        ps = [p for p in P1 if p <= zB]
        main, err = ie([F(2, p * p) for p in ps], 2, dB)
        pB = max(pB, zB)
        _cache[key] = (T * (main + 2 * s2(zB, pB, P1, SP1I)) / q, T * (err + 2 * cnt(zB, pB, P1)))
    a, c = _cache[key]
    return a * L + c

def u1_tail(N, lo, hi):
    if hi <= lo: return F(0)
    r1 = isqrt(N); r2 = isqrt(2 * N)
    a = min(hi, r1)
    v = 2 * (N * s2(lo, a, P1, SP1I) + cnt(lo, a, P1)) if a > lo else F(0)
    b = min(hi, r2); lo2 = max(lo, r1)
    if b > lo2: v += 2 * cnt(lo2, b, P1)
    lo3 = max(lo, r2)
    if hi > lo3: v += cnt(lo3, hi, P1)
    return v

def adm(m): return m % 8 in (1, 2, 5) and all(m % l for l in (3, 7, 11, 19, 23))
def pell(N, Yp):
    """Lemma P, exact integer arithmetic.  p >= Yq = Yp + 1 >= 5."""
    Yq = Yp + 1; assert Yq >= 5
    M = (N * N + 1) // (Yq * Yq)
    if M < 1: return 0
    tot = Bd.adm_count(M)
    m = 1
    while m <= M:
        X2 = m * Yq * Yq - 1              # x_lo^2
        g2 = max(9, 4 * m)                 # growth factor squared (g = max(3, 2 sqrt m))
        if N * N < g2 * X2: break          # N / x_lo < g : no second solution, and same for larger m
        if adm(m):
            j = 0; t = X2 * g2              # count j >= 1 with g^j x_lo <= N
            while t <= N * N: j += 1; t *= g2
            tot += j
        m += 1
    return tot

def tail(N, pT, Yp):
    return u1_tail(N, pT, Yp) + pell(N, Yp)

def S_prefix_len(xb, z2):
    n = 0; prod = 1
    for p in P1:
        if p > z2: break
        if (prod * p) ** 2 > xb * xb + 1: break
        n += 1; prod *= p
    return n

def lemC(N, Leff, mult, xb, z1, z2, pc, pB, dC):
    nS = S_prefix_len(xb, z2)
    key = ('C', nS, z1, z2, pc, max(pB, z1), dC)
    if key not in _cache:
        a = c = F(0); pB2 = max(pB, z1)
        a += F(2 * 23, 25) * s2(z1, pB2, P1, SP1I); c += 2 * 23 * cnt(z1, pB2, P1)
        U = [p for p in P1 if p <= z1]; S = set(P1[:nS]); gains = []
        for p2 in PR[1:]:
            if p2 > z2: break
            main, err = ie([F(2, p * p) for p in U if p != p2], 2, dC)
            if p2 == 5:
                a += main / 25; c += err; continue
            a += F(23, 25 * p2 * p2) * main; c += 3 * err
            if p2 in S: gains.append((F(23, 25 * p2 * p2) * (1 - main), 3 - 3 * err))
        a += s2(z2, pc); c += cnt(z2, pc)
        _cache[key] = (a, c, gains)
    a, c, gains = _cache[key]
    return a * Leff + c * mult + sum(max(ga * Leff + gc * mult, 0) for ga, gc in gains)

# ---------------- shared sets ----------------
DISCX = {}
for line in open(os.path.join(Bd.HERE, Bd.DISC_FILE)):
    t = line.split(); e = int(t[0]); k = int(t[1]); Q = tuple(map(int, t[2:2 + k]))
    P = int(t[2 + k][2:]); phi = int(t[3 + k][4:]); bn = int(t[4 + k][9:])
    DISCX[(e, Q)] = (F(phi, P), F(bn, P))

def mid(N, pc, Y):
    r = isqrt(N)
    if Y <= r: return N * s2(pc, Y) + cnt(pc, Y)
    lo = max(pc, r)
    return N * s2(pc, lo) + cnt(pc, lo) + cnt(lo, Y)

def ex(N, Y, x, cons):
    M = (N * x + 1) // (Y * Y)
    if M < 1: return F(0)
    A = F(N + 1, Y) + M
    Af = float(A)
    # float pre-selection of the near-maximal structures (see module docstring)
    vals = []
    for (e, S, u, bm) in Bd.structures(x, cons):
        Bf = (isqrt(N * bm + 1) + 1) / bm + 1        # same upper bound as the exact Bup below
        vf = min(f * (a0 * Af + b0 * Bf) for (f, a0, b0) in Bd.best_avg_choices(e, S)) * 2 ** u
        vals.append((vf, e, S, u, bm))
    vmax = max(v[0] for v in vals)
    best = F(0)
    for (vf, e, S, u, bm) in vals:
        if vf < vmax * (1 - 1e-6): continue
        Bup = F(isqrt(N * bm + 1) + 1, bm) + 1          # >= sqrt(N/bm + 1/bm^2) + 1
        ch = [(F(Bd.C2[e] * 2 ** len(S)), F(1), F(0))]    # trivial: rho*(b) = C2 * 2^{|S|+u}
        for r in range(len(S) + 1):
            for Q in itertools.combinations(S, r):
                if (e, Q) in DISCX:
                    a0, b0 = DISCX[(e, Q)]
                    ch.append((F(2 ** (len(S) - r)), a0, b0))
        v = 2 ** u * min(f * (a0 * A + b0 * Bup) for (f, a0, b0) in ch)
        best = max(best, v)
    return best

def Sh(N, pc, x, cons, Y):
    return mid(N, pc, Y) + ex(N, Y, x, cons)

# ---------------- cases ----------------
def buckets(N): return C.buckets(N)

def evaluate(Nhi, prm_by_case, verbose=False):
    """exact bounds at N = Nhi (integer) for the five cases with the given parameters"""
    N = int(Nhi)
    C.set_opts(**BEST)
    out = {}
    for case, prm in prm_by_case.items():
        pc = C.pc_of(N, prm); z = prm['z']; dA = prm['dA']; zB = prm['zB']; dB = prm['dB']
        z1, z2, dC = prm['z1'], prm['z2'], prm['dC']
        Yb = {}
        def SH(x, cons):
            key = (x, cons)
            if key not in Yb:
                Y = max(pc + 1, int(round(Bd.shared(float(N), pc, x, cons)[1])))
                Yb[key] = Sh(N, pc, x, cons, Y)
            return Yb[key]
        def TL(pT):
            Yp = max(pT, 4, int(round(Bd.best_tail(float(N), pT)[1])))
            return tail(N, pT, Yp)
        def smax(cons, fn):
            return max(fn(N - xa + 1, xb) + SH(xb, cons) for xa, xb in buckets(N))
        if case == 'I.b':
            v = 2 * smax(C.ANY5, lambda L, xb: restricted(1, 25, {5}, z, pc, L, dA))
        elif case == 'II':
            pB = C.pB_of(N, 25, prm); tl = TL(max(pB, z1))
            base = restricted(2, 25, {2, 5}, z, pc, N, dA)
            v = max(base + SH(xb, C.EVEN) + tl +
                    min(lemC(N, N - F(xa - 1, 2), 2, xb, z1, z2, pc, pB, dC), lemC(N, N, 1, xb, z1, z2, pc, pB, dC))
                    for xa, xb in buckets(N))
        else:
            pT = max(C.pB_of(N, 100, prm), zB, z1)
            tl = TL(pT)
            def Ast(L, xb):
                return min(lemB_perclass(23, 100, zB, pT, L, dB), lemC(N, F(L, 4), 1, xb, z1, z2, pc, pT, dC))
            shb = smax(C.ODD, Ast) + tl
            if case == 'III.1':
                v = restricted(6, 100, {2, 5}, z, pc, N, dA) + restricted(2, 100, {2, 5}, z, pc, N, dA) + 2 * (shb - tl) + tl
            elif case == 'III.2.a':     # beta
                v = (F(N, 100) + 1) + restricted(4, 100, {2, 5}, z, pc, N, dA) + shb
            else:                       # alpha
                a3 = restricted(2, 100, {2, 5}, z, pc, N, dA) + shb + 2 * smax(C.ANY5, lambda L, xb: restricted(3, 100, {2, 5}, z, pc, L, dA))
                a2 = (F(N, 100) + 1) + restricted(6, 100, {2, 5}, z, pc, N, dA) + shb + smax(C.ANY5, lambda L, xb: restricted(1, 100, {2, 5}, z, pc, N, dA))
                v = min(a3, a2)
        out[case] = v
    return out

def check(Nlo, Nhi, prm_by_case):
    out = evaluate(Nhi, prm_by_case)
    tgt = F(Nlo - 6, 25)
    return {k: v / tgt for k, v in out.items()}
