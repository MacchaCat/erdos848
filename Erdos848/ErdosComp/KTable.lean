import ErdosComp.Table
import ErdosComp.SmallPrimes

/-!
# A kernel-friendly prime table

`fastP n` decides primality for `n < 4473²` by `gcd(n, PSH) = 1` (`PSH` is the product of the
primes `≤ 4472`).  `segB` sums the contributions of `(lo, lo + len]` by binary splitting (depth
`log₂ len`, so the kernel never builds long chains of unevaluated terms); `chainOK` checks a
sorted table of `(x, stAt x)` segment by segment; `PTree` is a search tree for lookups.
Everything is written with `Nat.rec`/`cond` so that `decide +kernel` evaluates it efficiently.
-/

namespace ErdosComp

def fastP (n : Nat) : Bool := cond (Nat.blt n 4473) (isPrimeB n) (Nat.beq (Nat.gcd n PSH) 1)

def zeroSt : PSt := ⟨0, 0, 0, 0⟩

def addSt (a b : PSt) : PSt := ⟨a.cp + b.cp, a.cu + b.cu, a.fp + b.fp, a.fu + b.fu⟩

/-- The increment of `stAt` at `n` (for `n < 4473²`). -/
def contribF (n : Nat) : PSt :=
  cond (fastP n)
    (cond (n % 4 == 1 && decide (13 ≤ n)) ⟨1, 1, ceilK n, ceilK n⟩ ⟨1, 0, ceilK n, 0⟩)
    zeroSt

/-- The sum of `contribF` over `(lo, lo + len]`, by binary splitting (fuel `f`). -/
def segB (f : Nat) : Nat → Nat → PSt :=
  Nat.rec (motive := fun _ => Nat → Nat → PSt) (fun _ _ => zeroSt)
    (fun _ ih lo len => cond (Nat.beq len 0) zeroSt (cond (Nat.beq len 1) (contribF (lo + 1))
      (addSt (ih lo (len / 2)) (ih (lo + len / 2) (len - len / 2))))) f

def eqSt (a b : PSt) : Bool :=
  Nat.beq a.cp b.cp && Nat.beq a.cu b.cu && Nat.beq a.fp b.fp && Nat.beq a.fu b.fu

/-- Check a sorted table starting from the known value `v = stAt x`. -/
def chainOK : Nat → PSt → List (Nat × PSt) → Bool
  | _, _, [] => true
  | x, v, (y, w) :: rest =>
    Nat.ble x y && Nat.blt y 20007729 && eqSt w (addSt v (segB 64 x (y - x))) && chainOK y w rest

/-- Search trees of table entries. -/
inductive PTree where
  | leaf : PTree
  | node : PTree → Nat → PSt → PTree → PTree

def PTree.look : PTree → Nat → Option PSt
  | .leaf, _ => none
  | .node l k v r, x => cond (Nat.beq x k) (some v) (cond (Nat.blt x k) (l.look x) (r.look x))

/-- Walk the tree in order along the list `l`: the entries must be a prefix of `l`; returns
the rest of `l`. -/
def matchT : PTree → List (Nat × PSt) → Option (List (Nat × PSt))
  | .leaf, l => some l
  | .node a k v b, l =>
    match matchT a l with
    | some ((k₁, v₁) :: rest) => cond (Nat.beq k k₁ && eqSt v v₁) (matchT b rest) none
    | _ => none

/-- A balanced tree from a sorted list (fuel `f`). -/
def PTree.ofList : Nat → List (Nat × PSt) → PTree
  | 0, _ => .leaf
  | _ + 1, [] => .leaf
  | f + 1, l@(_ :: _) =>
    match l.drop (l.length / 2) with
    | [] => .leaf
    | (k, v) :: rest => .node (PTree.ofList f (l.take (l.length / 2))) k v (PTree.ofList f rest)

/-- Lookup, falling back to the specification. -/
def lookDT (t : PTree) (x : Nat) : PSt :=
  match t.look x with
  | some v => v
  | none => stAt x

end ErdosComp
