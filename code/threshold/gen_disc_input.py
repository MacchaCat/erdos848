# all (e, Q): Q subset of odd primes <= W, 2^e*prod(Q) <= PLIM (e in 0..3, e=3 means 8|b)
import itertools, sys
W = int(sys.argv[1]) if len(sys.argv) > 1 else 47
PLIM = int(float(sys.argv[2])) if len(sys.argv) > 2 else 2_000_000
ps = [p for p in range(3, W + 1) if all(p % d for d in range(2, p))]
def rec(i, P, Q, e):
    if i == len(ps):
        print(e, len(Q), *Q); return
    rec(i + 1, P, Q, e)
    if P * ps[i] <= PLIM: rec(i + 1, P * ps[i], Q + [ps[i]], e)
for e in range(4):
    rec(0, [1, 2, 4, 8][e], [], e)
