# Tail argument: all N >= NT = 1e60, with N-independent parameters except Y = Y' = N^0.7.
#
# Every bound is  C*N + E(N)  where C is a constant (computed below with N-independent choices,
# worst case over everything N-dependent: the set S_b in Lemma C is taken to be ALL U1 primes <= z2),
# and E(N) is a finite sum of terms  a * N^alpha * (ln N)^gamma  with alpha <= 0.8 plus constants.
# Then E(N)/N is decreasing for N >= NT (each term: (alpha-1) + gamma/ln N < 0), so it suffices to
# check  25*C + 25*E(NT)/(NT-6) < 1  (with (N-6)/25 <= c7(N) and C < 1/25).
#
# rho*(b) <= 2^(omega(b)+1) and Robin (1983): omega(n) <= 1.3841 ln n / ln ln n for n >= 3.
# For N >= 1e60: ln ln N >= 4.9277..., so 2^omega(b) <= N^(1.3841*ln2/4.9277) <= N^0.1950.
import math
import n0_v2 as M

NT = 1e60
lnN = math.log(NT)
assert math.log(lnN) > 4.927
EXPO = 1.3841 * math.log(2) / 4.927
assert EXPO < 0.1950
def rho_bound(N): return 2 * N ** 0.1950

def bounds(N, Sfull=True):
    pc = 2000; Y = N ** 0.7; Yp = N ** 0.7; z = 31; zB = 41; z1 = 41; z2 = 1000
    rho = rho_bound(N)
    def SH(B):
        M.shared(B, pc, Y, N, rho)
    out = {}
    B = M.Bound(); M.restricted(B, 1, 25, {5}, z, pc, N); SH(B); M.restricted(B, 1, 25, {5}, z, pc, N); SH(B); out['I.b'] = B
    B = M.Bound(); M.restricted(B, 2, 25, {2, 5}, z, pc, N); SH(B)
    # Lemma C with S = all U1 primes <= z2 (worst case for any N): emulate by passing huge N to S-construction
    Bc = M.Bound()
    M.lemC(Bc, zB, pc, Yp, z1, z2, pc, N, Sall=True)
    B.add(C=Bc.C, E=Bc.E); out['II'] = B
    def LB(T, q):
        Bb = M.Bound(); M.lemB(Bb, T, q, zB, pc, Yp, N); return Bb
    B = M.Bound(); M.restricted(B, 6, 100, {2, 5}, z, pc, N); SH(B); M.restricted(B, 2, 100, {2, 5}, z, pc, N); SH(B)
    b = LB(23, 50); B.add(C=b.C, E=b.E); out['III.1'] = B
    B = M.Bound(); B.add(C=2 / 100, E=2); M.restricted(B, 2, 100, {2, 5}, z, pc, N); SH(B); b = LB(23, 100); B.add(C=b.C, E=b.E); out['III.2.a'] = B
    B = M.Bound(); B.add(C=1 / 100, E=1); M.restricted(B, 3, 100, {2, 5}, z, pc, N); SH(B); M.restricted(B, 4, 100, {2, 5}, z, pc, N); SH(B); b = LB(23, 100); B.add(C=b.C, E=b.E); out['III.2.b'] = B
    return out

# S_b in lemC is built from N via prod p <= sqrt(N^2+1); at N = 1e60 that already contains every
# U1 prime <= z2 = 1000? check, otherwise the constant C is not the worst case for larger N.
S = []; prod = 1
for p in M.P1:
    if prod * p > math.sqrt(NT * NT + 1): break
    S.append(p); prod *= p
print("S at NT has", len(S), "primes, largest", S[-1])

out = bounds(NT)
for k, B in out.items():
    assert 25 * B.C + 25 * B.E / (NT - 6) < 0.999, k
    print("%-8s 25*C = %.6f   25*E(NT)/(NT-6) = %.3e   total = %.6f" % (k, 25 * B.C, 25 * B.E / (NT - 6), 25 * B.C + 25 * B.E / (NT - 6)))
