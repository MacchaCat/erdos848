"""Improved explicit bounds for Erdos #848 (exploration version, floating point).

Every function returns an UPPER bound for a count; parameters may be chosen freely.
Improvements are switched on by the flags in OPT (see REPORT.md for the lemmas):

  cons   : witness constraints (coprime to 5 / odd / even) used in rho_max and the structures
  ex1    : Ex(b) <= rho*(b) * ((N+1)/Y + floor((Nb+1)/Y^2))     [Lemma E1]
           and Mid counts at most 1 per prime p > sqrt(N)
  exavg  : averaged root count over m (Lemma E2): rho*(b) replaced by
           2^u (alpha0 A + beta0 B) for the small-prime structure of b
  pell2  : Pell tail counted in the window x in [x_lo(m), N] with growth factor max(3, 2 sqrt m),
           only admissible m (m mod 8 in {1,2,5}, no prime factor = 3 mod 4 from a fixed list)  [Lemma P]
  u1half : a U1 prime p with p^2 > 2N contributes at most one n <= N to {n = +-r_p mod p^2}  [Lemma H]
  bonf   : Bonferroni truncation of the inclusion-exclusion at odd depth (parameters dA, dB, dC)
  minw   : witness = minimum of the part it belongs to (Lemma W); the bound is a max over b
  cases2 : refined case split of III.2 (sub-cases alpha / beta) [Lemma S]
  opt    : optimise all parameters per N (otherwise the parameters of code/n0_exact.py)
"""
import math, bisect, itertools, os, functools
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
PMAX = 2 * 10 ** 7
_sv = bytearray([1]) * (PMAX + 1); _sv[0] = _sv[1] = 0
for _i in range(2, int(PMAX ** 0.5) + 1):
    if _sv[_i]: _sv[_i * _i::_i] = bytearray(len(_sv[_i * _i::_i]))
PR = [i for i in range(PMAX + 1) if _sv[i]]
del _sv
P1 = [p for p in PR if p % 4 == 1 and p >= 13]
def _prefix(lst):
    s = [0.0]; acc = 0.0
    for p in lst: acc += 1.0 / (p * p); s.append(acc)
    return s
SP, SP1 = _prefix(PR), _prefix(P1)
TAIL = 1.0 / (PMAX - 1)

OPT = dict(w97=False, lcodd=False, cons=False, ex1=False, exavg=False, pell2=False, u1half=False, bonf=False, minw=False, cases2=False, opt=False)

def pi(x):
    if x < 2: return 0
    if x <= PMAX: return bisect.bisect_right(PR, int(x))
    return math.isqrt(int(x)) + 1 + 2 * 1.3863 * x / math.log(x)        # lean/Chebyshev bound
def cnt(lo, hi, lst=PR):
    if hi <= lo: return 0
    if hi <= PMAX: return bisect.bisect_right(lst, int(hi)) - bisect.bisect_right(lst, int(lo))
    return pi(hi) - (bisect.bisect_right(lst, int(lo)) if lo <= PMAX else 0) * 0   # crude (as in n0_exact)
def s2(lo, hi, lst=PR, S=SP):
    if hi <= lo: return 0.0
    a = bisect.bisect_right(lst, lo); b = bisect.bisect_right(lst, min(hi, PMAX))
    r = S[b] - S[a]
    if hi > PMAX: r += TAIL
    return r

# ---------------- inclusion-exclusion / Bonferroni ----------------
def esym(vals, d):
    """elementary symmetric sums e_0..e_d of vals"""
    e = [1.0] + [0.0] * d
    for v in vals:
        for j in range(d, 0, -1): e[j] += e[j - 1] * v
    return e
def ie(vals, ncls, depth=None):
    """union of k events, event p = ncls disjoint classes of relative density vals[p]/ncls ... :
    returns (main, err): count <= (L/q)*main + err  (per residue class mod q).
    vals[p] = ncls / p^2 (density of the event).  Full IE: main = 1 - prod(1 - v), err = (1+ncls)^k - 1.
    Bonferroni depth d (odd, < k): main = sum_{j<=d} (-1)^{j+1} e_j, err = sum_{j<=d} C(k,j) ncls^j."""
    k = len(vals)
    if depth is None or depth >= k:
        pr = 1.0
        for v in vals: pr *= 1 - v
        return 1 - pr, (1 + ncls) ** k - 1
    e = esym(vals, depth)
    main = sum((-1) ** (j + 1) * e[j] for j in range(1, depth + 1))
    err = sum(comb(k, j) * ncls ** j for j in range(1, depth + 1))
    return main, err

# ---------------- Lemma A' : restricted sieve ----------------
@functools.lru_cache(maxsize=None)
def _restricted_lin(T, q, excl, z, pc, dA, bonf):
    ps = [p for p in PR if p <= z and p not in excl]
    main, err = ie([1.0 / (p * p) for p in ps], 1, dA if bonf else None)
    return T * (main + s2(z, pc)) / q, T * (err + cnt(z, pc))
def restricted(T, q, excl, z, pc, L, dA=None):
    a, c = _restricted_lin(T, q, frozenset(excl), z, pc, dA, OPT['bonf'])
    return a * L + c
def restricted_density(q, excl, z, pc, dA=None):
    ps = [p for p in PR if p <= z and p not in excl]
    main, _ = ie([1.0 / (p * p) for p in ps], 1, dA if OPT['bonf'] else None)
    return (main + s2(z, pc)) / q

# ---------------- structures of the witness b (for rho and the averaged Ex) ----------------
DISC = {}
DISC_FILE = os.environ.get("DISC_FILE", os.path.join("..", "..", "certificates", "threshold", "disc_table_97.txt"))
for line in open(os.path.join(HERE, DISC_FILE)):
    t = line.split(); e = int(t[0]); k = int(t[1]); Q = tuple(map(int, t[2:2 + k]))
    P = int(t[2 + k][2:]); phi = int(t[3 + k][4:]); bn = int(t[4 + k][9:])
    DISC[(e, Q)] = (phi / P, bn / P)          # alpha0, beta0
W_SMALL = 47                     # switched to 97 by the flag w97 (see set_w)
SMALL = tuple(p for p in range(3, W_SMALL + 1) if all(p % d for d in range(2, p)))
def set_w(w):
    global W_SMALL, SMALL
    W_SMALL = w
    SMALL = tuple(p for p in range(3, W_SMALL + 1) if all(p % d for d in range(2, p)))
C2 = [1, 1, 2, 4]
M2 = [1, 2, 4, 8]

def big_primes_max(R, w=None):
    if w is None: w = W_SMALL
    """max number of distinct primes > w with product <= R; and the list of minimal products"""
    u = 0; prod = 1; prods = [1]
    for p in PR:
        if p <= w: continue
        if prod * p > R: break
        prod *= p; u += 1; prods.append(prod)
    return u, prods

@functools.lru_cache(maxsize=None)
def structures(x, cons):
    """all (e, S, u, bmin) for witnesses b <= x satisfying cons:
    e = min(v2(b),3), S = set of odd primes <= 23 dividing b, u = #odd prime factors > 23,
    bmin = smallest such b."""
    out = []
    par, cop5 = cons                       # par in {'any','odd','even'}, cop5: 5 does not divide b
    if not OPT['cons']: par, cop5 = 'any', False
    es = {'any': (0, 1, 2, 3), 'odd': (0,), 'even': (1, 2, 3)}[par]
    small = [p for p in SMALL if not (cop5 and p == 5)]
    assert all(p <= W_SMALL for p in small)
    def rec(i, base, S, e):
        if i == len(small):
            umax, prods = big_primes_max(x // base)
            for u in range(umax + 1):
                out.append((e, tuple(S), u, base * prods[u]))
            return
        rec(i + 1, base, S, e)
        if base * small[i] <= x: rec(i + 1, base * small[i], S + [small[i]], e)
    for e in es:
        if M2[e] <= x: rec(0, M2[e], [], e)
    return out

def rho_max(x, cons=('any', False)):
    return max(C2[e] * 2 ** (len(S) + u) for (e, S, u, bm) in structures(int(x), cons))

@functools.lru_cache(maxsize=None)
def best_avg_choices(e, S):
    """list of (factor, alpha0, beta0) over subsets Q of S present in DISC (with sieved 2-part),
    plus the trivial choice; factor = 2^{|S \\ Q|}"""
    ch = [(C2[e] * 2 ** len(S), 1.0, 0.0)]            # trivial: rho = C2*2^|S| (times 2^u)
    for r in range(len(S) + 1):
        for Q in itertools.combinations(S, r):
            if (e, Q) in DISC:
                a0, b0 = DISC[(e, Q)]
                ch.append((2 ** (len(S) - r), a0, b0))
    # keep only Pareto-useful choices
    return ch

@functools.lru_cache(maxsize=None)
def _ex_struct_list(x, cons, N):
    """per structure: list of (slope, intercept) choices; bound = 2^u min_c (slope*A + icpt)"""
    out = []
    for (e, S, u, bm) in structures(int(x), cons):
        B = math.sqrt(N / bm + 1.0 / bm ** 2) + 1
        ch = [(2 ** u * f * a0, 2 ** u * f * b0 * B) for (f, a0, b0) in best_avg_choices(e, S)]
        # drop choices dominated inside the structure (larger slope and larger intercept)
        ch = [c for c in ch if not any(d != c and d[0] <= c[0] and d[1] <= c[1] for d in ch)]
        out.append(tuple(sorted(set(ch))))
    # drop structures s whose envelope is pointwise <= that of another structure s2:
    # sufficient: every choice of s2 is >= (coordinatewise) some choice of s ... reversed:
    # env(s) <= env(s2) if for every choice c2 of s2 there is a choice c of s with c <= c2.
    out = sorted(set(out), key=lambda ch: -min(c[0] for c in ch))
    keep = []
    for s_ in out:
        if any(all(any(c[0] <= c2[0] and c[1] <= c2[1] for c in s_) for c2 in t) for t in keep):
            continue
        keep.append(s_)
    return keep

GRID_R = 1.0005
@functools.lru_cache(maxsize=None)
def _ex_avg(x, cons, N, Ak):
    A = GRID_R ** Ak                      # A rounded UP to the grid: h is nondecreasing in A
    return max(min(s * A + c for (s, c) in ch) for ch in _ex_struct_list(x, cons, N))

def ex_bound(N, Y, x, cons):
    """upper bound for |Ex(b)| valid for every witness b <= x satisfying cons"""
    M = math.floor((N * x + 1) / (Y * Y))
    if M < 1: return 0.0
    A = (N + 1) / Y + M if OPT['ex1'] else 2 * (N + 1) / Y + (N * x + 1) / (Y * Y)
    if not OPT['exavg']:
        return rho_max(x, cons) * A
    Ak = math.ceil(math.log(A) / math.log(GRID_R))
    return _ex_avg(int(x), cons, N, Ak)

def mid_bound(N, pc, Y):
    if not OPT['ex1']:
        return N * s2(pc, Y) + cnt(pc, Y)
    r = math.isqrt(int(N))
    if Y <= r: return N * s2(pc, Y) + cnt(pc, Y)
    lo = max(pc, r)
    return N * s2(pc, lo) + cnt(pc, lo) + cnt(lo, Y)

def shared(N, pc, x, cons, Yfix=None):
    """min over Y of |Mid(b)| + |Ex(b)| bound, witnesses b <= x; returns (value, Y)"""
    f = lambda Y: mid_bound(N, pc, Y) + ex_bound(N, Y, x, cons)
    if Yfix is not None:
        return f(Yfix), Yfix
    best = None; Y = max(pc * 1.0, 300.0)
    while Y < 4 * N:
        v = f(Y)
        if best is None or v < best[0]: best = (v, Y)
        Y *= 1.12
    Y0 = best[1]
    for t in [Y0 * (1 + 0.01 * i) for i in range(-12, 13)]:
        if t <= pc: continue
        v = f(t)
        if v < best[0]: best = (v, t)
    return best

# ---------------- Lemma B ----------------
ADM_L = (3, 7, 11, 19, 23)
_ADM_P = 8 * 3 * 7 * 11 * 19 * 23
_adm_prefix = None
def _adm_init():
    global _adm_prefix
    pre = [0] * (_ADM_P + 1); c = 0
    for m in range(1, _ADM_P + 1):
        if m % 8 in (1, 2, 5) and all(m % l for l in ADM_L): c += 1
        pre[m] = c
    _adm_prefix = pre
def adm(m):
    return m % 8 in (1, 2, 5) and all(m % l for l in ADM_L)
def adm_count(M):
    if _adm_prefix is None: _adm_init()
    return (M // _ADM_P) * _adm_prefix[_ADM_P] + _adm_prefix[M % _ADM_P]

def pell(N, Yp):
    """#{n <= N : p^2 | n^2+1 for some prime p > Yp}"""
    if not OPT['pell2']:
        return (math.floor((N * N + 1) / (Yp * Yp)) + 1) * (0.9103 * math.log(2 * N + 1) + 1)
    Yq = math.floor(Yp) + 1                       # p >= Yq
    M = (int(N) ** 2 + 1) // (Yq * Yq)
    if M < 1: return 0
    tot = adm_count(M)                            # one solution per admissible m ...
    m = 1                                         # ... plus extra chain elements
    while m <= M:
        xlo = math.sqrt(m * Yq * Yq - 1)
        g = max(3.0, 2 * math.sqrt(m))
        if N / xlo < g: break                     # N/xlo decreasing, g increasing
        if adm(m):
            tot += math.floor(math.log(N / xlo) / math.log(g) + 1e-12)
        m += 1
    return tot

def u1_tail(N, lo, hi):
    """sum over U1 primes lo < p <= hi of #{n <= N : n = +-r_p mod p^2}"""
    if hi <= lo: return 0.0
    if not OPT['u1half']:
        return 2 * (N * s2(lo, hi, P1, SP1) + cnt(lo, hi, P1))
    r1 = math.isqrt(int(N)); r2 = math.isqrt(int(2 * N))
    a = min(hi, r1)
    v = 2 * (N * s2(lo, a, P1, SP1) + cnt(lo, a, P1)) if a > lo else 0.0
    b = min(hi, r2); lo2 = max(lo, r1)
    if b > lo2: v += 2 * cnt(lo2, b, P1)
    lo3 = max(lo, r2)
    if hi > lo3: v += cnt(lo3, hi, P1)
    return v

@functools.lru_cache(maxsize=None)
def _lemB_lin(T, q, zB, pB, dB, bonf):
    ps = [p for p in P1 if p <= zB]
    main, err = ie([2.0 / (p * p) for p in ps], 2, dB if bonf else None)
    pB = max(pB, zB)
    return T * (main + 2 * s2(zB, pB, P1, SP1)) / q, T * (err + 2 * cnt(zB, pB, P1))
def lemB_perclass(T, q, zB, pB, L, dB=None):
    a, c = _lemB_lin(T, q, zB, pB, dB, OPT['bonf'])
    return a * L + c
def lemB_tail(N, pB, Yp):
    return u1_tail(N, pB, Yp) + pell(N, Yp)
def best_tail(N, pB):
    best = None; Yp = max(pB * 1.0, 300.0)
    while Yp < 2 * N:
        v = lemB_tail(N, pB, Yp)
        if best is None or v < best[0]: best = (v, Yp)
        Yp *= 1.05
    return best

# ---------------- Lemma C ----------------
def S_prefix(xb, z2):
    S = []; prod = 1
    for p in P1:
        if p > z2: break
        if (prod * p) ** 2 > xb * xb + 1: break
        S.append(p); prod *= p
    return S

@functools.lru_cache(maxsize=None)
def _lemC_lin(nS, z1, z2, pc, pB, dC, bonf):
    """lemC without the tail: a*Leff + c*mult + sum_g max(g_a*Leff + g_c*mult, 0)"""
    d = dC if bonf else None
    a = c = 0.0
    pB = max(pB, z1)
    a += 2 * 23 / 25 * s2(z1, pB, P1, SP1); c += 2 * 23 * cnt(z1, pB, P1)
    U = [p for p in P1 if p <= z1]
    S = set(P1[:nS])
    gains = []
    for p2 in PR[1:]:
        if p2 > z2: break
        others = [p for p in U if p != p2]
        main, err = ie([2.0 / (p * p) for p in others], 2, d)
        if p2 == 5:
            a += main / 25; c += err; continue
        a += 23 / 25 / p2 ** 2 * main; c += 3 * err
        if p2 in S:
            gains.append((23 / 25 / p2 ** 2 * (1 - main), 3 - 3 * err))
    a += s2(z2, pc); c += cnt(z2, pc)
    return a, c, tuple(gains)

def lemC(N, Leff, mult, xb, z1, z2, pc, pB, Yp, dC=None, tail=None):
    """bound for |A*| (minus the shared sets of b), even witness b <= xb.
    Counts are over a domain where each class count mod an odd Q is <= Leff/Q + mult."""
    nS = len(S_prefix(xb, z2))
    a, c, gains = _lemC_lin(nS, z1, z2, pc, max(pB, z1), dC, OPT['bonf'])
    v = a * Leff + c * mult + sum(max(ga * Leff + gc * mult, 0) for ga, gc in gains)
    v += lemB_tail(N, max(pB, z1), Yp) if tail is None else tail
    return v

# ---------------- Y chosen per witness structure (Lemma W': parameters may depend on b) ----------------
def shared_struct(N, pc, x, cons):
    """max over structures s of min over Y of Mid(Y) + Ex_s(Y)  (only with exavg)"""
    if not (OPT['ex1'] and OPT['exavg']):
        return shared(N, pc, x, cons)[0]
    Ys = []
    Y = max(pc * 1.0, 300.0)
    while Y < 4 * N:
        Ys.append(Y); Y *= 1.04
    mids = [mid_bound(N, pc, Y) for Y in Ys]
    As = []
    for Y in Ys:
        M = math.floor((N * x + 1) / (Y * Y))
        As.append((N + 1) / Y + M if M >= 1 else 0.0)
    worst = 0.0
    for ch in _ex_struct_list(int(x), cons, N):
        best = min(mids[i] + (min(s * As[i] + c for (s, c) in ch) if As[i] > 0 else 0.0) for i in range(len(Ys)))
        worst = max(worst, best)
    return worst
