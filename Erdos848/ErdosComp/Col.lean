import ErdosComp.KTable
import ErdosComp.SmallPrimes4

/-!
# The small cases `N ≤ N₀` (kernel-friendly)

A dynamic colouring is replayed and checked step by step.  Classes are stored in a complete
binary tree of depth `16` (`BT`), so that every update copies one path only.  The steps are

* `nw v`  — open a new class `{v}` (allowed while the number of classes stays `≤ c₇(v)`),
* `put v j` — add `v` to class `j` (`v` must be compatible with every member),
* `mv w c d` — move `w` from class `c` to class `d` (`w` must be compatible with `d`).

The placed vertices increase, and every *mark* (a `v ≤ X` with `p² ∣ v² + 1` for some prime
`p ≡ 1 (mod 4)`, from the roots of `-1` modulo `p²`) must be placed at its own step.  The
soundness proof is `Erdos848/ColSound.lean`.
-/

namespace ErdosComp

/-! ### Squarefreeness below `10007³` -/

def isSqK (m : Nat) : Bool := Nat.beq (Nat.sqrt m * Nat.sqrt m) m

/-- `n` is squarefree, for `0 < n < 10007³`: with `g = gcd(n, ∏_{p ≤ 10⁴} p)`, the parts `g` and
`n / g` are coprime and `n / g` (all of whose prime factors exceed `10⁴`) is not a square. -/
def sqfK (n : Nat) : Bool :=
  Nat.blt 0 n && Nat.blt n (10007 * 10007 * 10007) &&
    Nat.beq (Nat.gcd (Nat.gcd n PS4) (n / Nat.gcd n PS4)) 1 &&
    !(Nat.blt 1 (n / Nat.gcd n PS4) && isSqK (n / Nat.gcd n PS4))

/-! ### Binary trees of classes -/

inductive BT where
  | lf : List Nat → BT
  | nd : BT → BT → BT

def BT.get : BT → Nat → List Nat
  | .lf l, _ => l
  | .nd a b, i => cond (Nat.beq (i % 2) 0) (a.get (i / 2)) (b.get (i / 2))

def BT.set : BT → Nat → List Nat → BT
  | .lf _, _, x => .lf x
  | .nd a b, i, x => cond (Nat.beq (i % 2) 0) (.nd (a.set (i / 2) x) b) (.nd a (b.set (i / 2) x))

def mkBT : Nat → BT
  | 0 => .lf []
  | d + 1 => .nd (mkBT d) (mkBT d)

/-- Number of class slots. -/
def slots : Nat := 2 ^ 16

/-! ### The colouring steps -/

inductive COp where
  | nw (v : Nat)
  | put (v j : Nat)
  | mv (w c d : Nat)

structure CSt where
  cnt : Nat
  t : BT
  last : Nat
  marks : List Nat

def c7K (N : Nat) : Nat := (N + 18) / 25

def compatL (v : Nat) (l : List Nat) : Bool := l.all (fun u => sqfK (u * v + 1))

/-- Marks must be placed at their own step: the next mark is not below `v`. -/
def markOK (ms : List Nat) (v : Nat) : Bool :=
  match ms with
  | [] => true
  | m :: _ => Nat.ble v m

def popMark (ms : List Nat) (v : Nat) : List Nat :=
  match ms with
  | [] => []
  | m :: rest => cond (Nat.beq m v) rest (m :: rest)

def stepC (s : CSt) : COp → Option CSt
  | .nw v =>
    cond (Nat.blt s.last v && Nat.ble (s.cnt + 1) (c7K v) && Nat.blt s.cnt slots && markOK s.marks v)
      (some ⟨s.cnt + 1, s.t.set s.cnt [v], v, popMark s.marks v⟩) none
  | .put v j =>
    cond (Nat.blt s.last v && Nat.blt j s.cnt && markOK s.marks v && compatL v (s.t.get j))
      (some ⟨s.cnt, s.t.set j (v :: s.t.get j), v, popMark s.marks v⟩) none
  | .mv w c d =>
    cond (Nat.blt c s.cnt && Nat.blt d s.cnt && !Nat.beq c d && (s.t.get c).contains w &&
        compatL w (s.t.get d))
      (some ⟨s.cnt, (s.t.set c ((s.t.get c).erase w)).set d (w :: s.t.get d), s.last, s.marks⟩) none

def runC : CSt → List COp → Option CSt
  | s, [] => some s
  | s, op :: ops =>
    match stepC s op with
    | some s' => runC s' ops
    | none => none

/-! ### The marks -/

/-- `r, r + m, r + 2m, … ≤ X` (fuel `f`). -/
def progL (X m : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, r => cond (Nat.ble r X) (r :: progL X m f (r + m)) []

/-- Merge of two sorted lists (fuel `f ≥` total length). -/
def mergeF : Nat → List Nat → List Nat → List Nat
  | 0, l1, l2 => l1 ++ l2
  | _ + 1, [], l => l
  | _ + 1, l, [] => l
  | f + 1, a :: as, b :: bs =>
    cond (Nat.ble a b) (a :: mergeF f as (b :: bs)) (b :: mergeF f (a :: as) bs)

def mergeL (l1 l2 : List Nat) : List Nat := mergeF (l1.length + l2.length) l1 l2

/-- One round of pairwise merges. -/
def mergeRound : List (List Nat) → List (List Nat)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => mergeL a b :: mergeRound rest

def mergeAllF : Nat → List (List Nat) → List Nat
  | 0, ls => ls.flatten
  | f + 1, ls => match ls with
    | [] => []
    | [l] => l
    | _ :: _ :: _ => mergeAllF f (mergeRound ls)

/-- Strictly increasing, duplicates removed (from a sorted list). -/
def dedupS : List Nat → List Nat
  | [] => []
  | a :: l => match l with
    | [] => [a]
    | b :: _ => cond (Nat.beq a b) (dedupS l) (a :: dedupS l)

/-- The marks of one prime `p` with root `r`. -/
def marksP (X p r : Nat) : List Nat :=
  mergeL (progL X (p * p) (X / (p * p) + 2) r) (progL X (p * p) (X / (p * p) + 2) (p * p - r))

def marksOf (X : Nat) (roots : List (Nat × Nat)) : List Nat :=
  dedupS (mergeAllF 40 (roots.map (fun pr => marksP X pr.1 pr.2)))

/-- The roots are valid, and every `n ≡ 1 (mod 4)`, `5 ≤ n ≤ X`, either has a root or is not
prime (`fastP`, valid below `4473²`). -/
def rootsGo (X : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | 0, _, rs => rs.isEmpty
  | f + 1, n, rs =>
    cond (Nat.blt X n) rs.isEmpty
      (match rs with
       | (p, r) :: rest =>
         cond (Nat.beq p n)
           (Nat.blt r (p * p) && Nat.beq ((r * r + 1) % (p * p)) 0 && rootsGo X f (n + 4) rest)
           (!fastP n && rootsGo X f (n + 4) ((p, r) :: rest))
       | [] => !fastP n && rootsGo X f (n + 4) [])

def rootsOK (X : Nat) (roots : List (Nat × Nat)) : Bool :=
  Nat.blt X 20007729 && rootsGo X (X / 4 + 2) 5 roots

/-- Strictly increasing. -/
def strictInc : List Nat → Bool
  | [] => true
  | a :: l => match l with
    | [] => true
    | b :: _ => Nat.blt a b && strictInc l

/-! ### Windows `(X₀, X₁]` with checkpoints -/

/-- The progression `r + k m` restricted to `[lo, X]`. -/
def progFrom (lo X m r : Nat) : List Nat :=
  progL X m ((X - lo) / m + 2) (cond (Nat.ble lo r) r (r + (lo - r + m - 1) / m * m))

def marksWin (X0 X1 : Nat) (roots : List (Nat × Nat)) : List Nat :=
  dedupS (mergeAllF 40 (roots.map (fun pr =>
    mergeL (progFrom (X0 + 1) X1 (pr.1 * pr.1) pr.2)
      (progFrom (X0 + 1) X1 (pr.1 * pr.1) (pr.1 * pr.1 - pr.2)))))

def listEq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && listEq as bs
  | _, _ => false

def btEq : BT → BT → Bool
  | .lf a, .lf b => listEq a b
  | .nd a b, .nd c d => btEq a c && btEq b d
  | _, _ => false

/-- One window: from the checkpoint `(t0, cnt0, last0)` to `(t1, cnt1, last1)`. -/
def winCheck (X0 X1 : Nat) (roots : List (Nat × Nat)) (t0 : BT) (cnt0 last0 : Nat)
    (ops : List COp) (t1 : BT) (cnt1 last1 : Nat) : Bool :=
  strictInc (marksWin X0 X1 roots) && Nat.ble last0 X0 && Nat.ble last1 X1 &&
    Nat.ble cnt0 slots &&
    match runC ⟨cnt0, t0, last0, marksWin X0 X1 roots⟩ ops with
    | some s => s.marks.isEmpty && Nat.beq s.cnt cnt1 && btEq s.t t1 && Nat.beq s.last last1
    | none => false

/-- The whole check for `N ≤ X`. -/
def colCheck (X : Nat) (roots : List (Nat × Nat)) (ops : List COp) : Bool :=
  strictInc (marksOf X roots) &&
    match runC ⟨0, mkBT 16, 0, marksOf X roots⟩ ops with
    | some s => s.marks.isEmpty
    | none => false

end ErdosComp
