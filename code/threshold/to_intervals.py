"""cert_best_*.csv -> intervals.txt for cert.c (None -> 0)."""
import csv, json, sys
CASES = ['I.b', 'II', 'III.1', 'III.2.a', 'III.2.b']
out = open(sys.argv[-1], 'w')
for path in sys.argv[1:-1]:
    for d in csv.DictReader(open(path)):
        prm = json.loads(d['params'].replace("'", '"'))
        f = [d['Nlo'], d['Nhi']]
        for c in CASES:
            p = prm[c]
            f += [str(p[k] or 0) for k in ('z', 'dA', 'zB', 'dB', 'z1', 'z2', 'dC', 'pc')] + [repr(float(p.get('pBf', 1.0)))]
        out.write(' '.join(f) + '\n')
