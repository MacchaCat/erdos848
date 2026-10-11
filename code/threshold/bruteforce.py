"""Brute-force checks of the new inequalities for small N (adversarial: high-rho witnesses,
witnesses with many U1 primes in S_b, all parameter regimes).

    python3 bruteforce.py [quick]
Every check prints the worst ratio actual/bound (must be <= 1)."""
import sys, math, random, itertools
from math import gcd, isqrt
import bounds as Bd
import cases as C

random.seed(848)
QUICK = len(sys.argv) > 1 and sys.argv[1] == "quick"
LIM = 4 * 10 ** 6
_sv = bytearray([1]) * (LIM + 1); _sv[0] = _sv[1] = 0
for i in range(2, isqrt(LIM) + 1):
    if _sv[i]: _sv[i * i::i] = bytearray(len(_sv[i * i::i]))
PRS = [i for i in range(LIM + 1) if _sv[i]]

def factor(n):
    f = {}
    for p in PRS:
        if p * p > n: break
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def rho_star(b):
    f = factor(b); e = f.get(2, 0)
    return Bd.C2[min(e, 3)] * 2 ** len([p for p in f if p != 2])

def make_rb(b):
    """m -> #{s mod b : s^2 m == 1 mod b}, by CRT (local tables for each prime power)"""
    loc = []
    for p, k in factor(b).items():
        q = p ** k
        if p == 2:
            tab = [0] * q
            for s in range(1, q, 2): tab[pow(s * s, -1, q) if q > 1 else 0] += 1
            loc.append(('t', q, tab))
        else:
            loc.append(('l', p, None))      # odd prime power: Hensel => 2 or 0 according to (m/p)
    def r(m):
        if gcd(m, b) != 1: return 0
        out = 1
        for kind, q, tab in loc:
            if kind == 't': out *= tab[m % q]
            else: out *= 2 if pow(m % q, (q - 1) // 2, q) == 1 else 0
            if out == 0: return 0
        return out
    return r

def r_b(b, m):
    return make_rb(b)(m)

def ex_actual(N, b, Y):
    S = set()
    top = isqrt(N * b + 1)
    for p in PRS:
        if p <= Y: continue
        if p > top: break
        if b % p == 0: continue
        q = p * p
        a0 = (-pow(b, -1, q)) % q
        a = a0 if a0 else q
        while a <= N:
            S.add(a); a += q
    return len(S)

def ex_E2(N, b, Y, x=None):
    """averaged bound for this b (structure of b, bm = b, x = b)"""
    if x is None: x = b
    f = factor(b); e = min(f.get(2, 0), 3)
    S = tuple(p for p in Bd.SMALL if p in f)
    u = len([p for p in f if p != 2 and p > Bd.W_SMALL])
    M = (N * x + 1) // (Y * Y)
    if M < 1: return 0.0
    A = (N + 1) / Y + M
    B = math.sqrt(N / b + 1.0 / b ** 2) + 1
    best = min(fct * (a0 * A + b0 * B) for (fct, a0, b0) in Bd.best_avg_choices(e, S))
    return 2 ** u * best

def ex_sum_exact(N, b, Y):
    """sum_{m<=M} r_b(m) (floor((X_m - Y)/b) + 1)  (the intermediate bound of Lemma E)"""
    M = (N * b + 1) // (Y * Y); tot = 0
    rb = make_rb(b)
    for m in range(1, M + 1):
        r = rb(m)
        if r == 0: continue
        X = isqrt((N * b + 1) // m)            # p <= X_m  <=>  p <= isqrt(floor((Nb+1)/m))
        if X <= Y: continue
        tot += r * ((X - Y - 1) // b + 1) if X > Y else 0
    return tot

def check_ex():
    print("--- Lemma E1/E2 (Ex(b)) ---")
    worst = {}
    Ns = [20000, 100000] if QUICK else [20000, 100000, 400000]
    for N in Ns:
        wits = [N, N - 1, 8 * 3 * 5 * 7 * 11, 4 * 3 * 5 * 7 * 11, 3 * 5 * 7 * 11 * 13, 2 * 3 * 5 * 7 * 11 * 13]
        wits += [b for b in (17 * 19 * 23, 17 * 19 * 23 * 29, 8 * 17 * 19 * 23, 3 * 17 * 19 * 23 * 29) if b <= N]
        wits += [random.randint(1, N) for _ in range(12 if QUICK else 30)]
        wits += [random.randrange(7, N, 25) for _ in range(5)]
        wits = [b for b in wits if 1 <= b <= N]
        for b in wits:
            for Y in [int(math.sqrt(N) / 2), int(math.sqrt(N)), int(2 * math.sqrt(N)), int(N ** 0.66), int(N ** 0.8)]:
                if Y < 2: continue
                act = ex_actual(N, b, Y)
                rho = rho_star(b)
                M = (N * b + 1) // (Y * Y)
                old = rho * (2 * (N + 1) / Y + (N * b + 1) / Y ** 2)
                e1 = rho * ((N + 1) / Y + M)
                inter = ex_sum_exact(N, b, Y) if b <= 200000 or M < 3000 else None
                e2 = ex_E2(N, b, Y)
                for k, v in (("old", old), ("E1", e1), ("E2", e2), ("inter", inter)):
                    if v is None: continue
                    r = act / v if v > 0 else (0 if act == 0 else float('inf'))
                    worst[k] = max(worst.get(k, 0), r)
                if inter is not None:
                    worst['inter<=E2'] = max(worst.get('inter<=E2', 0), inter / e2 if e2 > 0 else (0 if inter == 0 else 9e9))
                    worst['inter<=E1'] = max(worst.get('inter<=E1', 0), inter / e1 if e1 > 0 else (0 if inter == 0 else 9e9))
    for k, v in worst.items(): print("   worst actual/bound %-10s %.4f" % (k, v))
    assert all(v <= 1 for v in worst.values())

def check_disc_claim():
    """R(m) = sum_{j<=m} g(j) <= alpha0 m + beta0 for every m (spot check over 3 periods)"""
    print("--- discrepancy table: G(r) <= alpha0 r + beta0 ---")
    bad = 0; n = 0
    for (e, Q), (a0, b0) in Bd.DISC.items():
        P = Bd.M2[e]
        for q in Q: P *= q
        if P > 3000: continue
        g = [0] * P
        for t in range(P):
            if gcd(t, P) == 1: g[pow(t * t, -1, P) % P if P > 1 else 0] += 1
        G = 0
        for m in range(1, 3 * P + 1):
            G += g[m % P]
            if G > a0 * m + b0 + 1e-9: bad += 1
        n += 1
    print("   tables checked %d, violations %d" % (n, bad)); assert bad == 0

def sqrt_m1_mod_p2(p):
    for g in range(2, p):
        if pow(g, (p - 1) // 2, p) == p - 1: break
    r = pow(g, (p - 1) // 4, p)
    # Hensel: r^2 + 1 = 0 mod p ; lift to p^2
    q = p * p
    t = ((r * r + 1) // p) * pow(2 * r, -1, p) % p
    r2 = (r - t * p) % q
    assert (r2 * r2 + 1) % q == 0
    return r2

def pell_actual(N, Yp):
    S = set()
    for p in PRS:
        if p <= Yp: continue
        if p * p > N * N + 1: break
        if p % 4 != 1: continue
        q = p * p; r = sqrt_m1_mod_p2(p)
        for c in (r, q - r):
            a = c
            while a <= N: S.add(a); a += q
    return len(S)

def check_pell():
    print("--- Lemma P (Pell tail) and Lemma H (one class for p^2 > 2N) ---")
    C.set_opts(pell2=True, u1half=True)
    worst = 0; worstH = 0
    for N in ([3000, 30000, 200000] if QUICK else [3000, 30000, 200000, 1000000]):
        for Yp in [int(N ** 0.55), int(N ** 0.6), int(N ** 0.7), int(N ** 0.8), int(N ** 0.9), N // 2]:
            act = pell_actual(N, Yp)
            bnd = Bd.pell(N, Yp)
            worst = max(worst, act / bnd if bnd else (0 if act == 0 else 9e9))
        # Lemma H: for U1 p with p^2 > 2N, #{n <= N: n = +-r_p mod p^2} <= 1
        for p in PRS:
            if p * p <= 2 * N or p % 4 != 1 or p < 13: continue
            if p * p > N * N + 1: break
            q = p * p; r = sqrt_m1_mod_p2(p)
            c = sum(1 for x in (r, q - r) if x <= N)
            worstH = max(worstH, c)
    print("   worst actual/bound pell2 %.4f ; max count per prime with p^2>2N: %d" % (worst, worstH))
    assert worst <= 1 and worstH <= 1

def check_restricted():
    print("--- Lemma A' small primes with Bonferroni, on an interval [x, N] ---")
    C.set_opts(bonf=True)
    worst = 0
    for N in [20000, 200000]:
        for _ in range(6 if QUICK else 25):
            b = random.randint(1, N)
            if random.random() < 0.3: b = random.choice([30030, 2 * 3 * 7 * 11 * 13, 9699690 % N + 1])
            q, excl, t = random.choice([(25, {5}, 18), (25, {5}, 7), (100, {2, 5}, 57), (100, {2, 5}, 32)])
            x = random.choice([1, N // 3, N // 2])
            for z in [7, 13, 23, 31]:
                ps = [p for p in PRS if p <= z and p not in excl and b % p]
                act = 0
                for a in range(x, N + 1):
                    if a % q != t: continue
                    v = a * b + 1
                    if any(v % (p * p) == 0 for p in ps): act += 1
                for dA in [None, 1, 3, 5]:
                    bnd = Bd.restricted(1, q, excl, z, z, N - x + 1, dA)
                    worst = max(worst, act / bnd)
    print("   worst actual/bound %.4f" % worst); assert worst <= 1

def check_lemB():
    print("--- Lemma B small/medium U1 primes with Bonferroni, per class, on [x, N] ---")
    C.set_opts(bonf=True)
    worst = 0
    for N in [30000, 120000]:
        U = [p for p in PRS if p % 4 == 1 and p >= 13 and p < 400]
        R = {p: sqrt_m1_mod_p2(p) for p in U}
        for (q, T) in [(50, [t for t in range(1, 50, 2) if t % 25 not in (7, 18)]),
                       (100, [t for t in range(1, 100, 4) if t % 25 not in (7, 18)])]:
            for x in [1, N // 4, N // 2]:
                for zB in [13, 17, 29, 41]:
                    for pB in [zB, 61, 113]:
                        ps = [p for p in U if p <= pB]
                        Ts = set(T); act = 0
                        for n in range(x, N + 1):
                            if n % q not in Ts: continue
                            v = n * n + 1
                            if any(v % (p * p) == 0 for p in ps): act += 1
                        for dB in [None, 1, 3]:
                            bnd = Bd.lemB_perclass(len(T), q, zB, pB, N - x + 1, dB)
                            worst = max(worst, act / bnd)
    print("   worst actual/bound %.4f" % worst); assert worst <= 1

def is_U1set(n, U, R):
    return any((n - R[p]) % (p * p) == 0 or (n + R[p]) % (p * p) == 0 for p in U)

def check_lemC():
    """actual #{x in D cap T25 : x in U1-set and (x == b or p2^2 | xb+1 for some odd p2 <= pc, p2 !| b)}
    vs lemC (D = odd x in [1,N] union even x in [b,N] with mult=2, or [1,N] with mult=1)."""
    print("--- Lemma C (even witness, S_b prefix with b <= x, split domain) ---")
    C.set_opts(bonf=True, u1half=True, pell2=True)
    worst = 0
    N = 60000 if QUICK else 150000
    U = [p for p in PRS if p % 4 == 1 and p >= 13 and p * p <= N * N + 1]
    R = {p: sqrt_m1_mod_p2(p) for p in U}
    U1 = bytearray(N + 1)
    for p in U:
        q = p * p
        for c in (R[p], q - R[p]):
            a = c
            while a <= N: U1[a] = 1; a += q
    # witnesses: random even, and even b with many U1 primes in S_b (b = r mod 169*289 ...)
    wits = [random.randrange(2, N, 2) for _ in range(4 if QUICK else 10)]
    for mods in [(13,), (13, 17), (13, 17, 29)]:
        # CRT: b = r_p mod p^2 for p in mods, b even
        M = 2; r = 0
        for p in mods:
            q = p * p
            # solve b == r (mod M), b == R[p] (mod q)
            t = ((R[p] - r) * pow(M, -1, q)) % q
            r = r + M * t; M *= q
        if r <= N: wits.append(r if r % 2 == 0 else r + M if r + M <= N else r)
    wits = [b for b in wits if b % 2 == 0 and b in range(2, N + 1)]
    for b in wits:
        for (z1, z2, pc, dC) in [(13, 13, 60, None), (41, 200, 300, None), (29, 97, 200, 1), (41, 1000, 1000, 3), (17, 61, 61, None)]:
            odd_ps = [p for p in PRS if 3 <= p <= pc and b % p]
            for split in (False, True):
                act = 0
                for x in range(1, N + 1):
                    if x % 25 in (7, 18) or not U1[x]: continue
                    if split and x % 2 == 0 and x < b: continue
                    if x == b or any((x * b + 1) % (p * p) == 0 for p in odd_ps): act += 1
                pB = max(13, int(math.sqrt(N * (2 / 25) / 22)))
                tail = Bd.lemB_tail(N, max(pB, z1), max(pB, z1, int(N ** 0.7)))
                Leff, mult = (N - (b - 1) / 2, 2) if split else (N, 1)
                bnd = Bd.lemC(N, Leff, mult, b, z1, z2, pc, pB, None, dC, tail=tail)
                worst = max(worst, act / bnd)
    print("   worst actual/bound %.4f" % worst); assert worst <= 1

def check_classes():
    """the sieving claims used in the case split (mod 100): for a in class r, witness in class s,
    neither 4 nor 25 divides ab+1 for any lifts, i.e. the pair is 'sieved' with excl {2,5}"""
    print("--- class bookkeeping of the case split ---")
    def sieved(r, s):    # r, s mod 100; True if 4 !| ab+1 and 25 !| ab+1 for all a=r, b=s mod 100
        return all((a * b + 1) % 4 and (a * b + 1) % 25 for a in (r, r + 100) for b in (s, s + 100))
    # III.2 with A* = 1 mod 4: b in A* odd, b = 1 mod 4, b not in {7,18} mod 25
    bs = [s for s in range(1, 100, 4) if s % 25 not in (7, 18)]
    A7 = [7, 32, 57, 82]; A18 = [18, 43, 68, 93]
    for cl in [57, 93, 32, 82, 18, 68]: assert all(sieved(cl, s) for s in bs), cl
    for cl in [7, 43]: assert not any(sieved(cl, s) for s in bs), cl
    F7 = [7, 32, 82]; F18 = [18, 68, 43]
    assert all(sieved(43, c) for c in F7) and all(sieved(7, c) for c in F18)
    assert not sieved(43, 57) and not sieved(7, 93)
    # III.1: b1 = 1 mod 4 sieves 57,93,32,82,18,68 ; b3 = 3 mod 4 sieves 7,43
    b3s = [s for s in range(3, 100, 4) if s % 25 not in (7, 18)]
    for cl in [7, 43]: assert all(sieved(cl, s) for s in b3s)
    print("   OK")

def check_lemC_odd():
    """odd witness b = 1 mod 4 in A*, domain x = 1 mod 4 in [x0, N] (Lemma C with Leff=(N-x0+1)/4, mult=1)"""
    print("--- Lemma C with an odd witness, domain one class mod 4 on [x0, N] ---")
    C.set_opts(bonf=True, u1half=True, pell2=True)
    worst = 0
    N = 60000 if QUICK else 150000
    U = [p for p in PRS if p % 4 == 1 and p >= 13 and p * p <= N * N + 1]
    R = {p: sqrt_m1_mod_p2(p) for p in U}
    U1 = bytearray(N + 1)
    for p in U:
        q = p * p
        for c in (R[p], q - R[p]):
            a = c
            while a <= N: U1[a] = 1; a += q
    cand = [b for b in range(1, N + 1, 4) if U1[b] and b % 25 not in (7, 18)]
    wits = random.sample(cand, 6 if QUICK else 15)
    # witnesses with b in R_13 and R_17 (S_b of size 2), b = 1 mod 4
    for b in cand:
        if (b * b + 1) % (169 * 289) == 0: wits.append(b); break
    for b in wits:
        for (z1, z2, pc, dC) in [(13, 13, 60, None), (41, 200, 300, None), (29, 97, 200, 1), (17, 61, 61, None)]:
            odd_ps = [p for p in PRS if 3 <= p <= pc and b % p]
            for x0 in (1, b):
                act = 0
                for x in range(x0 + (1 - x0) % 4, N + 1, 4):
                    if x % 25 in (7, 18) or not U1[x]: continue
                    if x == b or any((x * b + 1) % (p * p) == 0 for p in odd_ps): act += 1
                pB = max(13, z1, int(math.sqrt(N * (77 / 100) / 22)))
                tail = Bd.lemB_tail(N, pB, max(pB, int(N ** 0.7)))
                bnd = Bd.lemC(N, (N - x0 + 1) / 4, 1, b, z1, z2, pc, pB, None, dC, tail=tail)
                worst = max(worst, act / bnd)
    print("   worst actual/bound %.4f" % worst); assert worst <= 1

if __name__ == "__main__":
    check_classes()
    check_disc_claim()
    check_pell()
    check_ex()
    check_restricted()
    check_lemB()
    check_lemC()
    check_lemC_odd()
    print("ALL CHECKS PASSED")
