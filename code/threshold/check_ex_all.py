"""Uniform check of the Ex bounds of a witness bucket against brute force for ALL b <= N."""
import sys
import cases as C, bounds as B
fn = sys.argv[1]; N = int(sys.argv[2]); Ys = list(map(int, sys.argv[3:]))
rows = [list(map(int, l.split())) for l in open(fn)]
CONS = {C.ANY5: lambda b: b % 5 != 0, C.ODD: lambda b: b % 2 == 1, C.EVEN: lambda b: b % 2 == 0,
        C.EVEN5: lambda b: b % 2 == 0 and b % 5 != 0, ('any', False): lambda b: True}
for flags in [dict(cons=True), dict(cons=True, ex1=True), dict(cons=True, ex1=True, exavg=True),
              dict(cons=True, ex1=True, exavg=True, w97=True), dict(cons=True, exavg=True, w97=True)]:
    C.set_opts(**flags)
    worst = 0; tight = None
    for xa, xb in C.buckets(N, 1.3) + [(1, N)]:
        for cons, ok in CONS.items():
            for t, Y in enumerate(Ys):
                act = max((rows[b - 1][1 + t] for b in range(1, xb + 1) if ok(b)), default=0)
                bnd = B.ex_bound(float(N), Y, xb, cons)
                r = act / bnd if bnd > 0 else (0 if act == 0 else 9e9)
                if r > worst: worst, tight = r, (xb, cons, Y, act, bnd)
    print(flags, "worst max_b Ex(b) / bound = %.4f at %s" % (worst, tight))
    assert worst <= 1
