"""Interval certificate for the best combination, exact arithmetic (exact.py).

  python3 scan.py anchors N0 N1 ratio anchors.json      # optimise parameters at geometric anchors
  python3 scan.py cert    N0 N1 step  anchors.json out.csv

For each interval [Nlo, Nhi] (integers, Nhi = floor(Nlo*step), consecutive intervals share
endpoints) the parameters of the anchor nearest to Nhi (in log scale) are used, the bound is
evaluated exactly at Nhi (every bound is nondecreasing in N for fixed parameters) and compared with
(Nlo-6)/25 <= c7(N).  A failing interval is retried with smaller steps (down to step 1.0005)."""
import os, sys, json, math, time
from multiprocessing import Pool
from fractions import Fraction as F
import cases as C
import exact as X

def opt_job(arg):
    N, case = arg
    C.set_opts(**X.BEST)
    v, prm = C.optimise(case, N)
    return N, case, v / ((N - 6) / 25), prm

def anchors(N0, N1, ratio, path):
    Ns = []; N = N0
    while N < N1 * ratio:
        Ns.append(float(int(N))); N *= ratio
    jobs = [(N, c) for N in Ns for c in C.CASES]
    with Pool(int(os.environ.get("WORKERS", "4"))) as P:
        res = P.map(opt_job, jobs, chunksize=1)
    json.dump(res, open(path, "w"), indent=1)
    for N in Ns:
        print("anchor %.4g: " % N + " ".join("%s %.4f" % (c, r) for (n, c, r, p) in res if n == N), flush=True)

def load_anchors(path):
    res = json.load(open(path))
    A = {}
    for n, c, r, p in res: A.setdefault(n, {})[c] = p
    return sorted(A.items())

def pick(A, Nhi):
    return min(A, key=lambda t: abs(math.log(t[0] / Nhi)))[1]

def cert_job(arg):
    Nlo, Nhi, prm = arg
    r = X.check(Nlo, Nhi, prm)
    return Nlo, Nhi, {k: float(v) for k, v in r.items()}, max(r.values()) < 1, prm

def cert(N0, N1, step, apath, out):
    A = load_anchors(apath)
    ivs = []; Nlo = N0
    while Nlo < N1:
        Nhi = min(N1, math.floor(Nlo * step)); ivs.append((Nlo, Nhi)); Nlo = Nhi
    todo = [(lo, hi, pick(A, hi)) for lo, hi in ivs]
    done = []
    with Pool(int(os.environ.get("WORKERS", "4"))) as P:
        while todo:
            res = []
            for item in P.imap_unordered(cert_job, todo, chunksize=1):
                res.append(item)
                lo, hi, r, ok, prm = item
                print("[%d,%d] %s %.5f" % (lo, hi, "ok" if ok else "FAILED", max(r.values())), flush=True)
            todo = []
            for (lo, hi, r, ok, prm) in res:
                if ok: done.append((lo, hi, r, prm)); continue
                s = (hi / lo) ** 0.5
                if hi / lo < 1.0005:
                    print("FAIL [%d,%d] %s" % (lo, hi, r), flush=True); done.append((lo, hi, r, prm)); continue
                mid = math.floor(lo * s)
                todo += [(lo, mid, prm), (mid, hi, prm)]
                print("split [%d,%d] worst %.5f" % (lo, hi, max(r.values())), flush=True)
    done.sort()
    with open(out, "w") as f:
        f.write("Nlo,Nhi," + ",".join("ratio_" + c for c in C.CASES) + ",params\n")
        for lo, hi, r, prm in done:
            f.write("%d,%d," % (lo, hi) + ",".join("%.9f" % r[c] for c in C.CASES) + ",\"%s\"\n" % json.dumps(prm).replace('"', "'"))
    ok = all(max(r.values()) < 1 for lo, hi, r, p in done)
    contiguous = all(done[i][1] == done[i + 1][0] for i in range(len(done) - 1)) and done[0][0] == N0 and done[-1][1] == N1
    worst = max(max(r.values()) for lo, hi, r, p in done)
    print("CERT %s: %d intervals [%d, %d], contiguous=%s, worst ratio %.6f" % ("OK" if ok else "FAILED", len(done), N0, N1, contiguous, worst))

if __name__ == "__main__":
    if sys.argv[1] == "anchors":
        anchors(float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), sys.argv[5])
    else:
        cert(int(float(sys.argv[2])), int(float(sys.argv[3])), float(sys.argv[4]), sys.argv[5], sys.argv[6])
