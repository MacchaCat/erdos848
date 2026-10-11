"""Generate the kernel-checked data for the analytic part N >= 1.6e8 (old checker).

Writes (relative to Erdos848/):
  ErdosComp/RowsK.lean      the 2913 certificate rows as literals (chunks rowsK0, rowsK1, ...)
  ErdosComp/TabK.lean       the prime table at all needed points (pieces tabP0, tabP1, ...),
                            including those of the §10 checker (ErdosComp/C2Points.txt)
  Erdos848/KTab/T*.lean     kernel checks `chainOK` of each table piece
  Erdos848/KRows/R*.lean    kernel checks of the rows, chunk by chunk
Usage: python3 gen_old_checker.py <path to Erdos848 project>
"""
import re, sys, os

ROOT = sys.argv[1]
PM = 20000000
K = 10 ** 30
PIECE = 250000          # numbers per table piece
PIECES_PER_MODULE = 4
ROWS_PER_CHUNK = 40
CHUNKS_PER_MODULE = 6

src = open(os.path.join(ROOT, 'ErdosComp/Rows.lean')).read()
m = re.search(r'def rowsStr : String := "(.*?)"\n', src, re.S)
rows = [list(map(int, l.split())) for l in m.group(1).split('\\n') if l.strip()]
assert len(rows) == 2913

pts = {31, 41, 1000, 2000, PM}
for r in rows:
    for v in r[2:]:
        if v <= PM:
            pts.add(v)
# points of the §10 checker (written by gen_check2.py)
extra = os.path.join(ROOT, 'ErdosComp/C2Points.txt')
if os.path.exists(extra):
    pts.update(int(l) for l in open(extra) if l.strip())
pts = sorted(pts)

# sieve and table values
sv = bytearray([1]) * (PM + 1); sv[0] = sv[1] = 0
for i in range(2, int(PM ** 0.5) + 1):
    if sv[i]:
        sv[i * i::i] = bytearray(len(sv[i * i::i]))
vals = {}
cp = cu = fp = fu = 0
j = 0
for n in range(PM + 1):
    if sv[n]:
        c = (K + n * n - 1) // (n * n)
        cp += 1; fp += c
        if n % 4 == 1 and n >= 13:
            cu += 1; fu += c
    while j < len(pts) and pts[j] == n:
        vals[n] = (cp, cu, fp, fu); j += 1
assert len(vals) == len(pts)

def st(v):
    return f"⟨{v[0]}, {v[1]}, {v[2]}, {v[3]}⟩"

# table pieces by numeric range
pieces = []
cur = []; start = 0
for x in pts:
    cur.append(x)
    if x - start >= PIECE:
        pieces.append(cur); start = x; cur = []
if cur:
    pieces.append(cur)
starts = [(0, (0, 0, 0, 0))]
for pc in pieces[:-1]:
    starts.append((pc[-1], vals[pc[-1]]))

with open(os.path.join(ROOT, 'ErdosComp/TabK.lean'), 'w') as f:
    f.write("import ErdosComp.KTable\n\n/-! # The prime table at the points needed by the analytic certificate (generated) -/\n\n")
    f.write("namespace ErdosComp\n\nset_option maxRecDepth 100000\n\n")
    for k, pc in enumerate(pieces):
        f.write(f"def tabP{k} : List (Nat × PSt) := [\n")
        f.write(",\n".join(f"  ({x}, {st(vals[x])})" for x in pc))
        f.write("]\n\n")
    for k, (x, v) in enumerate(starts):
        f.write(f"def tabS{k} : Nat × PSt := ({x}, {st(v)})\n")
    # right-nested, so that walking along the list is cheap for the kernel
    f.write("\ndef tabK : List (Nat × PSt) :=\n  " + " ++ (".join(f"tabP{k}" for k in range(len(pieces))) +
            ")" * (len(pieces) - 1) + "\n\n")
    # the search tree as a literal (balanced, in-order = `tabK`), subtrees at depth 6 as separate defs
    ents = [(x, vals[x]) for pc in pieces for x in pc]
    subs = []
    def tree(l, depth):
        if not l:
            return ".leaf"
        h = len(l) // 2
        t = f"(.node {tree(l[:h], depth + 1)} {l[h][0]} {st(l[h][1])} {tree(l[h + 1:], depth + 1)})"
        if depth == 6:
            subs.append(t)
            return f"treeK{len(subs) - 1}"
        return t
    top = tree(ents, 0)
    f.write("/-! The search tree of `tabK` (checked against `tabK` by `matchT`, `Erdos848/KAnalytic.lean`). -/\n\n")
    for i, t in enumerate(subs):
        f.write(f"def treeK{i} : PTree :=\n  {t}\n\n")
    f.write(f"def treeK : PTree :=\n  {top}\n\nend ErdosComp\n")

os.makedirs(os.path.join(ROOT, 'Erdos848/KTab'), exist_ok=True)
mods_t = []
for mi in range(0, len(pieces), PIECES_PER_MODULE):
    name = f"T{mi // PIECES_PER_MODULE:02d}"
    mods_t.append(name)
    with open(os.path.join(ROOT, f'Erdos848/KTab/{name}.lean'), 'w') as f:
        f.write("import ErdosComp.TabK\n\nnamespace ErdosComp\n\nset_option maxRecDepth 100000\n\n")
        for k in range(mi, min(mi + PIECES_PER_MODULE, len(pieces))):
            f.write(f"theorem tabP{k}_ok : chainOK tabS{k}.1 tabS{k}.2 tabP{k} = true := by decide +kernel\n\n")
        f.write("end ErdosComp\n")

# rows
chunks = [rows[i:i + ROWS_PER_CHUNK] for i in range(0, len(rows), ROWS_PER_CHUNK)]
with open(os.path.join(ROOT, 'ErdosComp/RowsK.lean'), 'w') as f:
    f.write("import ErdosComp.Check\n\n/-! # The analytic certificate rows as literals (generated from `Rows.lean`) -/\n\n")
    f.write("namespace ErdosComp\n\nset_option maxRecDepth 100000\n\n")
    for i, ch in enumerate(chunks):
        f.write(f"def rowsK{i} : List Row := [\n")
        f.write(",\n".join("  ⟨" + ", ".join(map(str, r)) + "⟩" for r in ch))
        f.write("]\n\n")
    f.write("def rowsK : List Row :=\n  " + " ++\n  ".join(f"rowsK{i}" for i in range(len(chunks))) + "\n\nend ErdosComp\n")

os.makedirs(os.path.join(ROOT, 'Erdos848/KRows'), exist_ok=True)
mods_r = []
for mi in range(0, len(chunks), CHUNKS_PER_MODULE):
    name = f"R{mi // CHUNKS_PER_MODULE:02d}"
    mods_r.append(name)
    with open(os.path.join(ROOT, f'Erdos848/KRows/{name}.lean'), 'w') as f:
        f.write("import ErdosComp.CheckK\n\nnamespace ErdosComp\n\nset_option maxRecDepth 100000\n\n")
        for i in range(mi, min(mi + CHUNKS_PER_MODULE, len(chunks))):
            f.write(f"theorem rowsK{i}_ok : rowsK{i}.all (fun r => checkRow (rowTab treeK r) r) = true := by\n  decide +kernel\n\n")
        f.write("end ErdosComp\n")

print("points", len(pts), "pieces", len(pieces), "table modules", len(mods_t),
      "row chunks", len(chunks), "row modules", len(mods_r))
print("piece sizes (range):", [p[-1] - (pieces[i - 1][-1] if i else 0) for i, p in enumerate(pieces)][:5], "...")
