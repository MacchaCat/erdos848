"""Windowed Lean data for the small-case checker (ErdosComp/Col.lean, `winCheck`).

Usage: python3 gen_colwin.py <ops.txt> <roots.txt> <X> <W> <path to Erdos848 project>
Replays the operations with the checker's semantics, cuts them into windows (X_{i-1}, X_i]
(X_i = i W, last window ending at X) and records the checkpoint classes after each window.
Writes Erdos848/ColW/*.lean, Erdos848/ColW.lean and Erdos848/KColW/*.lean.
"""
import os, sys

OPS, ROOTS, X, W, ROOT = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
roots = [tuple(map(int, l.split())) for l in open(ROOTS) if l.strip()]
roots = [(p, r) for (p, r) in roots if p <= X]
ops = [l.split() for l in open(OPS) if l.strip()]
bounds = list(range(W, X, W)) + [X]

# replay
cls = []          # Lean order: newest first
last = 0
win_ops = [[] for _ in bounds]
cks = []
wi = 0
pending = []      # moves before the next placement

def flush_ck():
    cks.append(([list(c) for c in cls], last))

for t in ops:
    if t[0] == 'M':
        pending.append(t); continue
    v = int(t[1])
    while v > bounds[wi]:
        flush_ck(); wi += 1
    for m in pending:
        w, c, d = int(m[1]), int(m[2]), int(m[3])
        cls[c].remove(w); cls[d].insert(0, w)
        win_ops[wi].append(f".mv {w} {c} {d}")
    pending = []
    if t[0] == 'N':
        cls.append([v]); win_ops[wi].append(f".nw {v}")
    else:
        j = int(t[2]); cls[j].insert(0, v); win_ops[wi].append(f".put {v} {j}")
    last = v
while len(cks) < len(bounds):
    flush_ck()
assert not pending

D = os.path.join(ROOT, 'Erdos848/ColW')
os.makedirs(D, exist_ok=True)
for f in os.listdir(D):
    os.remove(os.path.join(D, f))
hdr = "import ErdosComp.Col\n\nnamespace ErdosComp\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
with open(os.path.join(D, 'Roots.lean'), 'w') as f:
    f.write(hdr)
    f.write("/-- Empty trees. -/\ndef E0 : BT := .lf []\n" + "".join(f"def E{d} : BT := .nd E{d-1} E{d-1}\n" for d in range(1, 17)) + "\n")
    ch = [roots[i:i + 1000] for i in range(0, len(roots), 1000)]
    for i, c in enumerate(ch):
        f.write(f"def rootsW{i} : List (Nat × Nat) := [" + ", ".join(f"({p}, {r})" for p, r in c) + "]\n\n")
    f.write("def rootsW : List (Nat × Nat) :=\n  " + " ++ (".join(f"rootsW{i}" for i in range(len(ch))) +
            ")" * (len(ch) - 1) + "\n\nend ErdosComp\n")
def render(d, cl, out, prefix, counter):
    """Lean term for the depth-`d` tree holding `cl` (index bits read from the least one).
    Subtrees are emitted as auxiliary definitions so that no term is deep or long."""
    if all(len(c) == 0 for c in cl):
        return f"E{d}"
    if d == 0:
        c = cl[0] if cl else []
        return "(.lf [" + ", ".join(map(str, c)) + "])"
    ev, od = cl[0::2], cl[1::2]
    a = render(d - 1, ev, out, prefix, counter)
    b = render(d - 1, od, out, prefix, counter)
    term = f"(.nd {a} {b})"
    if d >= 6:   # name subtrees of depth >= 6
        counter[0] += 1
        name = f"{prefix}_{counter[0]}"
        out.append(f"def {name} : BT := {term}\n")
        return name
    return term

names = []
for i, b in enumerate(bounds):
    name = f"W{i:02d}"; names.append(name)
    cl, ls = cks[i]
    with open(os.path.join(D, name + ".lean"), 'w') as f:
        f.write(hdr.replace("import ErdosComp.Col\n", "import Erdos848.ColW.Roots\n"))
        f.write(f"def winX{i} : Nat := {b}\n\n")
        och = [win_ops[i][k:k + 1500] for k in range(0, len(win_ops[i]), 1500)] or [[]]
        for k, c in enumerate(och):
            f.write(f"def winOps{i}_{k} : List COp := [" + ", ".join(c) + "]\n\n")
        f.write(f"def winOps{i} : List COp :=\n  " + " ++ (".join(f"winOps{i}_{k}" for k in range(len(och))) +
                ")" * (len(och) - 1) + "\n\n")
        full = cl + [[] for _ in range(2 ** 16 - len(cl))]
        out = []
        top = render(16, full, out, f"ck{i}", [0])
        f.write("".join(out))
        f.write(f"\ndef ckT{i} : BT := {top}\n\n")
        f.write(f"def ckCnt{i} : Nat := {len(cl)}\n\n")
        f.write(f"def ckLast{i} : Nat := {ls}\n\nend ErdosComp\n")
with open(os.path.join(ROOT, 'Erdos848/ColW.lean'), 'w') as f:
    f.write("import Erdos848.ColW.Roots\n" + "".join(f"import Erdos848.ColW.{n}\n" for n in names))
    f.write(f"\nnamespace ErdosComp\n\ndef colWX : Nat := {X}\n\ndef colWN : Nat := {len(bounds)}\n\nend ErdosComp\n")
K = os.path.join(ROOT, 'Erdos848/KColW')
os.makedirs(K, exist_ok=True)
for f in os.listdir(K):
    os.remove(os.path.join(K, f))
khdr = "namespace ErdosComp\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
# roots: one kernel run per chunk on its own range, glued by `rootsGo_append`
nch = len(ch)
Mj = [c[-1][0] for c in ch[:-1]] + [X]
mj = [5] + [Mj[j] + 4 for j in range(nch - 1)]
fj = [(Mj[j] - mj[j]) // 4 + 2 for j in range(nch)]
kj = [(mj[j + 1] - mj[j]) // 4 for j in range(nch - 1)]
Fj = [0] * nch
Fj[-1] = X // 4 + 2 - (mj[-1] - 5) // 4
for j in range(nch - 2, -1, -1):
    Fj[j] = kj[j] + Fj[j + 1]
assert Fj[0] == X // 4 + 2 and Fj[-1] >= (X - mj[-1]) // 4 + 1
def tail(j):
    t = f"rootsW{nch - 1}"
    for i in range(nch - 2, j - 1, -1):
        t = f"rootsW{i} ++ ({t})"
    return t
with open(os.path.join(K, 'Roots.lean'), 'w') as f:
    f.write("import Erdos848.RootsAppend\nimport Erdos848.ColW.Roots\n\n" + khdr +
            "set_option linter.style.longLine false\n\n")
    for j in range(nch - 1):
        f.write(f"theorem rootsSeg{j} : rootsGo {Mj[j]} {fj[j]} {mj[j]} rootsW{j} = true := by decide +kernel\n\n")
    f.write(f"theorem rootsTail{nch - 1} : rootsGo {X} {Fj[-1]} {mj[-1]} rootsW{nch - 1} = true := by decide +kernel\n\n")
    for j in range(nch - 2, -1, -1):
        f.write(f"theorem rootsTail{j} : rootsGo {X} {Fj[j]} {mj[j]} ({tail(j)}) = true :=\n"
                f"  Erdos848.rootsGo_append {X} {Mj[j]} {mj[j + 1]} {Fj[j + 1]} _ rootsTail{j + 1} (by norm_num) (by norm_num)\n"
                f"    (by norm_num) {kj[j]} {mj[j]} {fj[j]} rootsW{j} (by norm_num) (by norm_num) rootsSeg{j}\n\n")
    f.write(f"theorem rootsW_ok : rootsOK {X} rootsW = true := by\n  unfold rootsOK\n  rw [Bool.and_eq_true]\n"
            f"  exact ⟨by decide, rootsTail0⟩\n\nend ErdosComp\n")
for i, b in enumerate(bounds):
    with open(os.path.join(K, f"K{i:02d}.lean"), 'w') as f:
        prev = f"Erdos848.ColW.W{i-1:02d}" if i > 0 else None
        f.write("import Erdos848.ColW.Roots\n" + f"import Erdos848.ColW.W{i:02d}\n" + (f"import {prev}\n" if prev else "") + "\n" + khdr)
        x0, t0, c0, l0 = (f"winX{i-1}", f"ckT{i-1}", f"ckCnt{i-1}", f"ckLast{i-1}") if i > 0 else ("0", "(mkBT 16)", "0", "0")
        f.write(f"theorem win{i}_ok : winCheck {x0} winX{i} rootsW {t0} {c0} {l0} winOps{i} ckT{i} ckCnt{i} ckLast{i} = true := by\n  decide +kernel\n\nend ErdosComp\n")
# assembly
with open(os.path.join(K, 'All.lean'), 'w') as f:
    f.write("import Erdos848.ColSound\nimport Erdos848.KColW.Roots\n" + "".join(f"import Erdos848.KColW.K{i:02d}\n" for i in range(len(bounds))))
    f.write(f"""
/-!
# The small cases `N ≤ {X}`, checked by the kernel (generated by `gen_colwin.py`)

{len(bounds)} windows of the colouring certificate (`Erdos848/KColW/K*.lean`), chained by
`winCheck_sound`.
-/

namespace Erdos848

open ErdosComp

theorem statement_small : ∀ N ≤ {X}, Statement N := by
  have hr := rootsW_ok
""")
    prev = "winOK_zero"
    for i, b in enumerate(bounds):
        f.write(f"  obtain ⟨s{i}, k{i}⟩ := winCheck_sound (X := {X}) (X0 := {'0' if i == 0 else f'winX{i-1}'}) hr (show winX{i} ≤ {X} by decide) {prev} win{i}_ok\n")
        prev = f"k{i}"
    f.write("  intro N hN\n")
    for i, b in enumerate(bounds):
        lo = "0" if i == 0 else f"ckLast{i-1}"
        f.write(f"  by_cases h{i} : N ≤ winX{i}\n")
        if i == 0:
            f.write(f"  · exact s{i} N (Nat.zero_le N) h{i}\n")
        else:
            f.write(f"  · exact s{i} N (by have := k{i-1}.2.2.1; omega) h{i}\n")
    f.write(f"  exact absurd hN (by have : winX{len(bounds)-1} = {X} := rfl; omega)\n\nend Erdos848\n")
print("windows", len(bounds), "ops per window", [len(w) for w in win_ops][:5], "...", "checkpoint sizes", [sum(len(c) for c in ck[0]) for ck in cks][-3:])
