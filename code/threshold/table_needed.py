"""Which entries of the root-count discrepancy table (Lemma E2) are actually needed?

For every witness bucket [xa, xb] (as used by the minimal-witness bound), every witness constraint
and the cut-off Y chosen by the optimiser, the bound for |Ex| is V = max over structures of
min over table choices.  A structure only needs a table entry if its trivial bound rho*(b)*A
exceeds V; then the entry with the smallest period P that keeps it <= V is selected.
Prints the number of entries needed and sum of their periods (cost of verifying them, e.g. in Lean).

    python3 table_needed.py N1 N2 ...
"""
import sys, math
import cases as C, bounds as B
from exact import BEST

def needed(N, pc=600):
    C.set_opts(**BEST)
    need = {}
    for cons in (C.ANY5, C.ODD, C.EVEN):
        for xa, xb in C.buckets(N):
            v, Y = B.shared(N, pc, xb, cons)
            M = math.floor((N * xb + 1) / (Y * Y))
            if M < 1: continue
            A = (N + 1) / Y + M
            vals = []
            for (e, S, u, bm) in B.structures(xb, cons):
                Bv = math.sqrt(N / bm + 1.0 / bm ** 2) + 1
                vals.append((e, S, u, bm, Bv))
            V = max(min(f * (a0 * A + b0 * Bv) for (f, a0, b0) in B.best_avg_choices(e, S)) * 2 ** u
                    for (e, S, u, bm, Bv) in vals)
            for (e, S, u, bm, Bv) in vals:
                if B.C2[e] * 2 ** (len(S) + u) * A <= V: continue
                best = None
                import itertools
                for r in range(len(S) + 1):
                    for Q in itertools.combinations(S, r):
                        if (e, Q) not in B.DISC: continue
                        a0, b0 = B.DISC[(e, Q)]
                        if 2 ** u * 2 ** (len(S) - r) * (a0 * A + b0 * Bv) <= V * (1 + 1e-12):
                            P = B.M2[e]
                            for q in Q: P *= q
                            if best is None or P < best[0]: best = (P, (e, Q))
                assert best is not None
                need[best[1]] = best[0]
    return need

if __name__ == "__main__":
    tot = {}
    for a in sys.argv[1:]:
        n = needed(float(a))
        tot.update(n)
        print("N=%s: %d entries, sum of periods %.3g, largest %d" % (a, len(n), sum(n.values()), max(n.values())), flush=True)
    print("union: %d entries, sum of periods %.3g" % (len(tot), sum(tot.values())))
