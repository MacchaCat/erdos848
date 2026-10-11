import ErdosComp.Table

/-!
# The computational part (executable)

* `sqfTest n` — a squarefreeness test whose `true` answers are proved correct
  (`Erdos848/CompSound.lean`): trial division by all primes `p` with `p³ ≤ n`, then a perfect
  square test for the cofactor.
* `buildMarks X cert` — marks every `w ≤ X` that could have `w² + 1` non-squarefree: for every
  `p ≡ 1 (mod 4)`, `5 ≤ p ≤ X`, the certificate gives either a root `r² ≡ -1 (mod p²)` (then the
  two classes `±r mod p²` are marked) or a proper factor of `p`.
* `runFrom` — the guarded colouring: an *untrusted* proposer suggests operations, each of which
  is checked (classes stay pairwise compatible, at most `c₇(N)` classes, every marked `N` is
  coloured).
-/

namespace ErdosComp

/-! ### Squarefreeness -/

/-- Bound for the trial division: `D³ ≥ (1.6·10⁸)² + 1`. -/
def DTr : Nat := 300000

/-- All primes `≤ DTr`, increasing. -/
def plist : List Nat := (List.range (DTr + 1)).filter isPrimeB

def isSq (m : Nat) : Bool := Nat.sqrt m * Nat.sqrt m == m

/-- Trial division of `rem` (initially `n`) by the primes `p` with `p³ ≤ n`. -/
def sqfGo (n : Nat) : Nat → List Nat → Bool
  | rem, [] => !(1 < rem && isSq rem)
  | rem, p :: ps =>
    if n < p * p * p then !(1 < rem && isSq rem)
    else if rem % p == 0 then (if rem / p % p == 0 then false else sqfGo n (rem / p) ps)
    else sqfGo n rem ps

def sqfTest (n : Nat) : Bool := decide (0 < n) && decide (n ≤ DTr * DTr * DTr) && sqfGo n n plist

/-! ### Marks for `V` -/

/-- Mark `r, r + m, r + 2m, … ≤ X`. -/
def markProg (X m : Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, a => a
  | f + 1, w, a => if X < w then a else markProg X m f (w + m) (a.set! w true)

/-- Process `p = 5, 9, 13, …` (`k` more values). `cert p = (0, r)` (a root) or `(1, d)` (a factor). -/
def markLoop (X : Nat) (cert : Nat → Nat × Nat) : Nat → Nat → Array Bool → Option (Array Bool)
  | 0, _, a => some a
  | k + 1, p, a =>
    let c := cert p
    if c.1 == 0 then
      let r := c.2
      if r < p * p && (r * r + 1) % (p * p) == 0 then
        let a := markProg X (p * p) (X / (p * p) + 2) r a
        let a := markProg X (p * p) (X / (p * p) + 2) (p * p - r) a
        markLoop X cert k (p + 4) a
      else none
    else if c.1 == 1 && 1 < c.2 && c.2 < p && p % c.2 == 0 then markLoop X cert k (p + 4) a
    else none

def buildMarks (X : Nat) (cert : Nat → Nat × Nat) : Option (Array Bool) :=
  markLoop X cert (X / 4 + 1) 5 (Array.replicate (X + 1) false)

/-! ### Untrusted certificates for `buildMarks` -/

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

/-- Smallest factor `≤ √p` (or `p`). -/
def smallFactor (p : Nat) : Nat := Id.run do
  if p % 2 == 0 then return 2
  let mut d := 3
  while d * d ≤ p do
    if p % d == 0 then return d
    d := d + 2
  return p

def certGen (p : Nat) : Nat × Nat := Id.run do
  let d := smallFactor p
  if d < p then return (1, d)
  -- p prime, p ≡ 1 (mod 4): a square root of -1 mod p, lifted to p²
  let mut g := 2
  let mut r0 := 0
  while g < p do
    let x := powMod g ((p - 1) / 4) p
    if x * x % p == p - 1 then r0 := x; break
    g := g + 1
  let c := ((r0 * r0 + 1) / p) % p
  let inv := powMod (2 * r0 % p) (p - 2) p
  let k := (p - c) % p * inv % p
  return (0, (r0 + p * k) % (p * p))

/-! ### Guarded colouring -/

inductive Op where
  | opn (v : Nat)
  | place (v c : Nat)
  | move (u c₁ c₂ : Nat)

def c7C (N : Nat) : Nat := (N + 18) / 25

def compatB (v : Nat) (arr : Array Nat) : Bool := arr.all (fun u => u == v || sqfTest (u * v + 1))

def applyOp (N : Nat) (cls : Array (Array Nat)) : Op → Option (Array (Array Nat))
  | .opn v => if cls.size + 1 ≤ c7C N then some (cls.push #[v]) else none
  | .place v c =>
    if h : c < cls.size then (if compatB v cls[c] then some (cls.modify c (·.push v)) else none)
    else none
  | .move u c₁ c₂ =>
    if h₁ : c₁ < cls.size then
      if h₂ : c₂ < cls.size then
        if c₁ != c₂ && cls[c₁].contains u && compatB u cls[c₂] then
          some ((cls.modify c₁ (·.erase u)).modify c₂ (·.push u))
        else none
      else none
    else none

def applyOps (N : Nat) : Array (Array Nat) → List Op → Option (Array (Array Nat))
  | cls, [] => some cls
  | cls, op :: ops => match applyOp N cls op with
    | some cls' => applyOps N cls' ops
    | none => none

/-- `prop aux cls v = (ops, c, aux')`: operations for step `v`, and the class that should then
contain `v`. -/
def runFrom {Aux : Type} (prop : Aux → Array (Array Nat) → Nat → List Op × Nat × Aux)
    (marks : Array Bool) : Nat → Nat → Aux → Array (Array Nat) → Bool
  | 0, _, _, _ => true
  | k + 1, v, aux, cls =>
    let r := prop aux cls v
    match applyOps v cls r.1 with
    | none => false
    | some cls' =>
      (if marks.getD v true then (if h : r.2.1 < cls'.size then cls'[r.2.1].contains v else false)
        else true) &&
      runFrom prop marks k (v + 1) r.2.2 cls'

end ErdosComp
