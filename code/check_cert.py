"""Independent check of the scan certificates cert_1.csv, cert_2.csv.

Checks, using exact rational arithmetic on the recorded decimal values:
  * the intervals are contiguous: Nlo of each row equals Nhi of the previous row;
  * cert_1 starts at 1.6e8, cert_2 starts where cert_1 ends, cert_2 ends at >= 1e60;
  * for every row and every case:  C*Nlo + E < 0.999 * (Nlo - 6)/25  and  C < 1/25.
(The values C, E themselves are produced by n0_v2.py from the formulas of proof.md section 2-5;
 this script re-verifies the final inequality and the coverage, not the derivation of C and E.)
"""
import csv, sys
from fractions import Fraction as F

def load(path):
    with open(path) as f:
        return list(csv.DictReader(f))

def check(rows, start):
    names = ["I.b", "II", "III.1", "III.2.a", "III.2.b"]
    prev_hi = None
    worst = F(0)
    for i, r in enumerate(rows):
        lo, hi = F(r["Nlo"]), F(r["Nhi"])
        if i == 0:
            assert lo <= start, (lo, start)
        else:
            assert lo == prev_hi, ("gap", i, prev_hi, lo)
        assert hi > lo
        target = (lo - 6) / 25
        for k in names:
            C, E = F(r["C_" + k]), F(r["E_" + k])
            assert C < F(1, 25), (i, k)
            ratio = (C * lo + E) / target
            assert ratio < F(999, 1000), (i, k, float(ratio))
            worst = max(worst, ratio)
        prev_hi = hi
    return prev_hi, worst

if __name__ == "__main__" and sys.argv[1] == "--exact":
    pass
elif __name__ == "__main__":
    r1 = load(sys.argv[1]); r2 = load(sys.argv[2])
    end1, w1 = check(r1, F(160000000))
    end2, w2 = check(r2, end1)
    assert F(r2[0]["Nlo"]) == end1, "cert_2 must start where cert_1 ends"
    # tail.py covers all N >= NT where NT is the double 1e60 (slightly below 10^60)
    assert end2 >= F(1e60), float(end2)
    print("certificates OK: [1.6e8, %.3g] covered by %d + %d intervals; worst ratios %.5f, %.5f"
          % (float(end2), len(r1), len(r2), float(w1), float(w2)))


def check_exact(paths):
    """Coverage check for the exact certificates produced by n0_exact.py:
    integer endpoints, contiguous, from 1.6e8 to exactly 10^60, every recorded ratio bound < 1."""
    from fractions import Fraction as F
    names = ["I.b", "II", "III.1", "III.2.a", "III.2.b"]
    prev = None; n = 0; first = None
    for path in paths:
        for r in load(path):
            lo = F(int(r["Nlo_num"]), int(r["Nlo_den"])); hi = F(int(r["Nhi_num"]), int(r["Nhi_den"]))
            if first is None: first = lo
            if prev is not None: assert lo == prev, ("gap", float(prev), float(lo))
            assert hi > lo and lo.denominator == 1 and hi.denominator == 1
            for k in names: assert F(r["ratio_up_" + k]) < 1, (float(lo), k)
            prev = hi; n += 1
    assert first == 160000000 and prev == F(10) ** 60, (first, prev)
    print("exact certificates OK: [1.6e8, 10^60] covered by %d contiguous integer intervals" % n)


if __name__ == "__main__" and sys.argv[1] == "--exact":
    check_exact(sys.argv[2:])
