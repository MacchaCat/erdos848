"""Case bounds (Section 5 of proof.en.md) with the improvements of bounds.py.

case_values(N, prm) -> {case: upper bound for |A|} for every case; the target is (N-6)/25.
Parameters may differ from case to case (each case is a separate inequality).
"""
import math, functools
import bounds as Bd
from bounds import OPT, restricted, shared, lemB_perclass, lemB_tail, best_tail, lemC

ANY5 = ('any', True)       # witness in A7 or A18: coprime to 5
ODD = ('odd', False)       # witness in A*, all of A* odd
EVEN = ('even', False)     # even witness in A*
EVEN5 = ('even', True)     # even witness in A7 or A18

def set_opts(**kw):
    for k in OPT: OPT[k] = False
    OPT.update(kw)
    Bd.set_w(97 if OPT['w97'] else 47)
    Bd.structures.cache_clear(); Bd.best_avg_choices.cache_clear(); Bd._ex_struct_list.cache_clear(); Bd._ex_avg.cache_clear(); Bd._restricted_lin.cache_clear(); Bd._lemB_lin.cache_clear(); Bd._lemC_lin.cache_clear()
    _sh.cache_clear(); _tail.cache_clear()

DEFAULT = dict(z=31, dA=None, zB=41, dB=None, z1=41, z2=1000, dC=None, pcA=None, pBf=1.0)

@functools.lru_cache(maxsize=None)
def _sh(N, pc, x, cons):
    return shared(N, pc, x, cons)[0]
@functools.lru_cache(maxsize=None)
def _tail(N, pB):
    return best_tail(N, pB)[0]

def buckets(N, ratio=1.3):
    """partition of [1, N] into [xa, xb]"""
    out = []; xa = 1
    while xa < N:
        xb = min(N, max(xa + 1, math.floor(xa * ratio)))
        out.append((xa, xb)); xa = xb
    return out

def pc_of(N, prm):
    return prm['pc'] if prm.get('pc') else max(2000, int(0.3 * math.sqrt(N)))
def pB_of(N, q, prm):
    return max(13, int(prm.get('pBf', 1.0) * math.sqrt(N * (1 - 23 / q) / 22)))

def sh_max(N, pc, cons, mainfun, ratio=1.3):
    """max over witnesses b in [1,N] of mainfun(L = N - b + 1) + Sh(b) (Lemma W),
    or mainfun(N) + Sh(N) without minw"""
    if not OPT['minw']:
        return mainfun(N) + _sh(N, pc, N, cons)
    best = 0.0
    for xa, xb in buckets(N, ratio):
        best = max(best, mainfun(N - xa + 1) + _sh(N, pc, xb, cons))
    return best

def case_Ib(N, prm):
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']
    f = lambda L: restricted(1, 25, {5}, z, pc, L, dA)
    return 2 * sh_max(N, pc, ANY5, f)

def case_II(N, prm):
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']
    pB = pB_of(N, 25, prm); tail = _tail(N, max(pB, prm['z1']))
    base = restricted(2, 25, {2, 5}, z, pc, N, dA)
    args = dict(z1=prm['z1'], z2=prm['z2'], pc=pc, pB=pB, Yp=None, dC=prm['dC'], tail=tail)
    if not OPT['minw']:
        return base + _sh(N, pc, N, EVEN) + lemC(N, N, 1, N, **args)
    best = 0.0
    for xa, xb in buckets(N):
        lc = min(lemC(N, N - (xa - 1) / 2, 2, xb, **args), lemC(N, N, 1, xb, **args))
        best = max(best, base + _sh(N, pc, xb, EVEN) + lc)
    return best

def pT_of(N, prm):
    """common start of the U1 tail for the A* parts (Lemma B and the odd-witness Lemma C)"""
    return max(pB_of(N, 100, prm), prm['zB'], prm['z1'] if OPT['lcodd'] else 0)

def sh_max2(N, pc, cons, partfun, ratio=1.3):
    """max over buckets [xa,xb] of partfun(L=N-xa+1, xb) + Sh(xb)"""
    if not OPT['minw']:
        return partfun(N, N) + _sh(N, pc, N, cons)
    best = 0.0
    for xa, xb in buckets(N, ratio):
        best = max(best, partfun(N - xa + 1, xb) + _sh(N, pc, xb, cons))
    return best

def Astar_part(N, prm, L, xb):
    """A* intersected with one class mod 4 and [b, N], b = minimal element (odd witness b <= xb):
    Lemma B per class, or Lemma C with the odd witness b (flag lcodd); the U1 tail is NOT included"""
    pT = pT_of(N, prm); pc = pc_of(N, prm)
    v = lemB_perclass(23, 100, prm['zB'], pT, L, prm['dB'])
    if OPT['lcodd']:
        v = min(v, lemC(N, L / 4, 1, xb, prm['z1'], prm['z2'], pc, pT, None, prm['dC'], tail=0.0))
    return v

def case_III1(N, prm):
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']; zB = prm['zB']; dB = prm['dB']
    base = restricted(6, 100, {2, 5}, z, pc, N, dA) + restricted(2, 100, {2, 5}, z, pc, N, dA)
    pB50 = pB_of(N, 50, prm)
    std = base + 2 * _sh(N, pc, N, ODD) + lemB_perclass(23, 50, zB, pB50, N, dB) + _tail(N, max(pB50, zB))
    if not OPT['minw']:
        return std
    split = base + 2 * sh_max2(N, pc, ODD, lambda L, xb: Astar_part(N, prm, L, xb)) + _tail(N, pT_of(N, prm))
    return min(std, split)

def LB100(N, prm, L=None):
    zB = prm['zB']; pB = pB_of(N, 100, prm)
    return lemB_perclass(23, 100, zB, pB, N if L is None else L, prm['dB'])

def shb_III2(N, prm, pc):
    """[Sh(b) + A* part] maximised over b, plus the U1 tail"""
    return sh_max2(N, pc, ODD, lambda L, xb: Astar_part(N, prm, L, xb)) + _tail(N, pT_of(N, prm))

def case_III2a(N, prm):
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']
    pB = pB_of(N, 100, prm); tail = _tail(N, max(pB, prm['zB']))
    base = 2 * (N / 100 + 1) + restricted(2, 100, {2, 5}, z, pc, N, dA) + tail
    return base + sh_max(N, pc, ODD, lambda L: LB100(N, prm, L))

def case_III2b(N, prm):
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']
    pB = pB_of(N, 100, prm); tail = _tail(N, max(pB, prm['zB']))
    base = (N / 100 + 1) + restricted(3, 100, {2, 5}, z, pc, N, dA) + restricted(4, 100, {2, 5}, z, pc, N, dA) + tail
    return base + _sh(N, pc, N, EVEN5) + sh_max(N, pc, ODD, lambda L: LB100(N, prm, L))

def case_III2_beta(N, prm):
    """A* in one class mod 4, b = min A*; F18 empty (or F7 empty): one witness"""
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']
    base = (N / 100 + 1) + restricted(4, 100, {2, 5}, z, pc, N, dA)
    return base + shb_III2(N, prm, pc)

def case_III2_alpha(N, prm):
    """F7, F18 both nonempty: witnesses b (A*), c (F7), c' (F18), or only b, c with one whole class"""
    pc = pc_of(N, prm); z = prm['z']; dA = prm['dA']
    shb = shb_III2(N, prm, pc)
    # three witnesses: classes 57,93 by b over [1,N]; {32,82 by b, 7 by c'} over [c,N]; {18,68 by b, 43 by c} over [c',N]
    a3 = restricted(2, 100, {2, 5}, z, pc, N, dA) + shb
    fc = lambda L: restricted(3, 100, {2, 5}, z, pc, L, dA)
    a3 += 2 * sh_max(N, pc, ANY5, fc)
    # two witnesses (b and c): class 7 whole, 43 by c
    a2 = (N / 100 + 1) + restricted(6, 100, {2, 5}, z, pc, N, dA) + shb
    a2 += sh_max(N, pc, ANY5, lambda L: restricted(1, 100, {2, 5}, z, pc, N, dA) + 0 * L)
    return min(a3, a2)

CASES = ['I.b', 'II', 'III.1', 'III.2.a', 'III.2.b']
def case_fun(name):
    if OPT['cases2']:
        return {'I.b': case_Ib, 'II': case_II, 'III.1': case_III1,
                'III.2.a': case_III2_beta, 'III.2.b': case_III2_alpha}[name]
    return {'I.b': case_Ib, 'II': case_II, 'III.1': case_III1,
            'III.2.a': case_III2a, 'III.2.b': case_III2b}[name]

# ---------------- parameter optimisation ----------------
GRID = dict(
    z=[7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 61],
    dA=[None, 1, 3, 5, 7],
    zB=[13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113],
    dB=[None, 1, 3, 5],
    z1=[13, 17, 29, 37, 41, 53, 61, 73, 89],
    z2=[13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 150, 200, 300, 500, 1000],
    dC=[None, 1, 3],
    pc=[None, 100, 150, 200, 300, 400, 600, 800, 1000, 1500, 2000, 3000, 5000, 8000, 12000, 20000],
    pBf=[0.25, 0.4, 0.6, 0.8, 1.0, 1.3, 1.7, 2.5, 4.0],
)
RELEVANT = {
    'I.b': ['z', 'dA', 'pc'],
    'II': ['z', 'dA', 'pc', 'z1', 'z2', 'dC', 'pBf'],
    'III.1': ['z', 'dA', 'pc', 'zB', 'dB', 'pBf', 'z1', 'z2', 'dC'],
    'III.2.a': ['z', 'dA', 'pc', 'zB', 'dB', 'pBf', 'z1', 'z2', 'dC'],
    'III.2.b': ['z', 'dA', 'pc', 'zB', 'dB', 'pBf', 'z1', 'z2', 'dC'],
}
STARTS = [dict(), dict(z=17, dA=3, z1=61, z2=73, dC=1, pc=300, zB=13), dict(z=13, dA=3, z1=41, z2=97, dC=1, pc=600, zB=13, pBf=0.6)]
def optimise(name, N, rounds=4, starts=None):
    f = case_fun(name)
    prm0 = dict(DEFAULT); prm0['pc'] = None
    if not OPT['opt']:
        return f(N, prm0), prm0
    keys = [k for k in RELEVANT[name] if OPT['bonf'] or k not in ('dA', 'dB', 'dC')]
    best_all = None
    for st in (starts if starts is not None else STARTS):
        prm = dict(prm0); prm.update({k: v for k, v in st.items() if OPT['bonf'] or k not in ('dA', 'dB', 'dC')})
        best = f(N, prm)
        for _ in range(rounds):
            improved = False
            for k in keys:
                for v in GRID[k]:
                    t = dict(prm); t[k] = v
                    try:
                        val = f(N, t)
                    except Exception:
                        continue
                    if val < best - 1e-9:
                        best, prm, improved = val, t, True
            if not improved: break
        if best_all is None or best < best_all[0]: best_all = (best, prm)
    return best_all

def table(Ns, flags, verbose=False):
    set_opts(**flags)
    res = {}
    for N in Ns:
        tgt = (N - 6) / 25
        row = {}
        for c in CASES:
            v, prm = optimise(c, N)
            row[c] = v / tgt
            if verbose: print("   %s N=%.3g ratio=%.4f prm=%s" % (c, N, v / tgt, prm), flush=True)
        res[N] = row
    return res
