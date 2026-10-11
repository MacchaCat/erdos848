import ErdosComp.Bounds

/-!
# The interval checker (executable)

For an interval `[Nlo, Nhi]` with parameters `(pc, Y, Y'_q, p_{B,q})`, each case of the
case analysis is bounded by `C·N + E` (`proof.md` §6.1, Lemma D); the soundness of every
component is proved in `Erdos848/CheckSound.lean`.  Fixed parameters: `z = 31`, `z_B = z₁ = 41`,
`z₂ = 1000`.
-/

namespace ErdosComp

/-! ### Products, sums and counts over `[0, n)` -/

def prodF (cond : Nat → Bool) (f : Nat → Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => prodF cond f n * (if cond n then f n else 1)

def sumF (cond : Nat → Bool) (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumF cond f n + (if cond n then f n else 0)

def cntF (cond : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cntF cond n + (if cond n then 1 else 0)

/-! ### Constants of the small primes -/

def condP (excl : List Nat) (p : Nat) : Bool := isPrimeB p && !(excl.contains p)

/-- `∏_{p ≤ 31, p ∉ excl} (1 - 1/p²)`. -/
def prod1 (excl : List Nat) : Rat := prodF (condP excl) (fun p => 1 - 1 / ((p : Rat) * p)) 32
def k1 (excl : List Nat) : Nat := cntF (condP excl) 32

/-- `∏_{U1, p ≤ 41} (1 - 2/p²)`. -/
def prodU : Rat := prodF isU1B (fun p => 1 - 2 / ((p : Rat) * p)) 42
def kU : Nat := cntF isU1B 42

def condE (p q : Nat) : Bool := isU1B q && q != p
def prErase (p : Nat) : Rat := prodF (condE p) (fun q => 1 - 2 / ((q : Rat) * q)) 42
def kErase (p : Nat) : Nat := cntF (condE p) 42

def condOdd (p : Nat) : Bool := isPrimeB p && p != 2 && p != 5

/-- `∑_{p ≤ 1000, p ≠ 2, 5} nonB = cNon · N + eNon`. -/
def cNon : Rat :=
  sumF condOdd (fun p => 23 / 25 * (1 / ((p : Rat) * p)) * (1 - prErase p)) 1001
def eNon : Rat := sumF condOdd (fun p => 3 * ((3 : Rat) ^ kErase p - 1)) 1001

/-- The first 30 U1 primes. -/
def UL : List Nat := [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173,
  181, 193, 197, 229, 233, 241, 257, 269, 277, 281, 293, 313, 317]

/-- `g(p) = gA p · N + gE p`. -/
def gA (p : Nat) : Rat := 23 / 25 * prErase p / ((p : Rat) * p)
def gE (p : Nat) : Rat := 3 - 3 * ((3 : Rat) ^ kErase p - 1)

/-! ### `ρ` and the Pell factor -/

def OPc : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

def primeProdC (k : Nat) : Nat := (OPc.take k).prod

/-- `W(L) = #{k ∈ [1, 45] : primeProdC k ≤ L}`. -/
def Wc (L : Nat) : Nat := ((List.range 45).filter (fun k => primeProdC (k + 1) ≤ L)).length

def rhoMaxC (N : Nat) : Nat := max (2 ^ Wc N) (max (2 * 2 ^ Wc (N / 4)) (4 * 2 ^ Wc (N / 8)))

def log3Go (n : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if 3 ^ (k + 1) ≤ n then log3Go n f (k + 1) else k

def log3C (n : Nat) : Nat := log3Go n n 0

def pellC (N Y : Nat) : Nat := (N * N + 1) / ((Y + 1) * (Y + 1)) * (log3C N + 1)

/-! ### The components `(C, E)` -/

abbrev CE := Rat × Rat

def addCE (a b : CE) : CE := (a.1 + b.1, a.2 + b.2)

def resCE (tab : List (Nat × PSt)) (q T : Nat) (excl : List Nat) (pc : Nat) : CE :=
  ((T : Rat) / q * (1 - prod1 excl + s2P tab 31 pc),
   (T : Rat) * ((2 : Rat) ^ k1 excl - 1 + cP tab 31 pc))

def shCE (tab : List (Nat × PSt)) (Nhi pc Y : Nat) : CE :=
  (s2P tab pc Y,
   cP tab pc Y + (rhoMaxC Nhi : Rat) * (2 * ((Nhi : Rat) + 1) / Y + ((Nhi : Rat) * Nhi + 1) / ((Y : Rat) * Y)))

def lemBCE (tab : List (Nat × PSt)) (Nhi q T pB YB : Nat) : CE :=
  ((T : Rat) / q * (1 - prodU) + 2 * (T : Rat) / q * s2U tab 41 pB + 2 * s2U tab pB YB,
   (T : Rat) * ((3 : Rat) ^ kU - 1) + 2 * (T : Rat) * cU tab 41 pB + 2 * cU tab pB YB +
     (pellC Nhi YB : Rat))

def gSumC (L : Nat) : Rat := sumF (fun _ => true) (fun j => gA (UL.getD j 0)) L
def gSumE (Nlo L : Nat) : Rat :=
  sumF (fun _ => true) (fun j => max (gE (UL.getD j 0)) (-(gA (UL.getD j 0)) * Nlo)) L

/-- `q₀ q₁ ⋯ q_{l-1}`. -/
def ulProd : Nat → Nat
  | 0 => 1
  | l + 1 => ulProd l * UL.getD l 0

def lemCCE (tab : List (Nat × PSt)) (Nlo Nhi pB YB pc L : Nat) : CE :=
  (46 / 25 * s2U tab 41 pB + 2 * s2U tab pB YB + (1 - prodU) / 25 + cNon + gSumC L +
     s2P tab 1000 pc,
   46 * cU tab 41 pB + 2 * cU tab pB YB + (pellC Nhi YB : Rat) + ((3 : Rat) ^ kU - 1) + eNon +
     gSumE Nlo L + cP tab 1000 pc)

/-- `L = max {ℓ ≤ 29 : (q₀ ⋯ q_{ℓ-1})² ≤ N² + 1}`. -/
def Lval (Nhi : Nat) : Nat :=
  ((List.range 29).filter (fun l => ulProd (l + 1) * ulProd (l + 1) ≤ Nhi * Nhi + 1)).length

/-! ### One interval -/

structure Row where
  Nlo : Nat
  Nhi : Nat
  pc : Nat
  Y : Nat
  Y25 : Nat
  Y50 : Nat
  Y100 : Nat
  pB25 : Nat
  pB50 : Nat
  pB100 : Nat

def okCE (Nlo : Nat) (c : CE) : Bool :=
  decide (c.1 < 1 / 25) && decide (c.1 * Nlo + c.2 < ((Nlo : Rat) - 6) / 25)

def caseIb (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (resCE tab 25 1 [5] r.pc) (shCE tab r.Nhi r.pc r.Y))
    (addCE (resCE tab 25 1 [5] r.pc) (shCE tab r.Nhi r.pc r.Y))

def caseII (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (resCE tab 25 2 [2, 5] r.pc) (lemCCE tab r.Nlo r.Nhi r.pB25 r.Y25 r.pc (Lval r.Nhi)))
    (shCE tab r.Nhi r.pc r.Y)

def caseIII1 (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (addCE (resCE tab 100 6 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y))
    (addCE (resCE tab 100 2 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (lemBCE tab r.Nhi 50 23 r.pB50 r.Y50)

def caseIII2a (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (2 / 100, 2) (addCE (resCE tab 100 2 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (lemBCE tab r.Nhi 100 23 r.pB100 r.Y100)

def caseIII2b (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (addCE (1 / 100, 1) (addCE (resCE tab 100 3 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (addCE (resCE tab 25 1 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (lemBCE tab r.Nhi 100 23 r.pB100 r.Y100)

def checkRow (tab : List (Nat × PSt)) (r : Row) : Bool :=
  decide (1 ≤ r.Y) && decide (7 ≤ r.Nlo) && decide (r.Nlo ≤ r.Nhi) &&
  decide (r.Nhi < primeProdC 45) &&
  decide (Nat.succ (Lval r.Nhi) ≤ 30) &&
  decide (r.Nhi * r.Nhi + 1 < ulProd (Lval r.Nhi + 1) * ulProd (Lval r.Nhi + 1)) &&
  okCE r.Nlo (caseIb tab r) && okCE r.Nlo (caseII tab r) && okCE r.Nlo (caseIII1 tab r) &&
  okCE r.Nlo (caseIII2a tab r) && okCE r.Nlo (caseIII2b tab r)

/-- The rows are contiguous from `a` to `b`. -/
def chain : Nat → Nat → List Row → Bool
  | a, b, [] => a == b
  | a, b, r :: rs => r.Nlo == a && chain r.Nhi b rs

/-- Points at which the prime table is needed. -/
def needPts (rows : List Row) : List Nat :=
  let raw := [31, 41, 1000, PM] ++ rows.flatMap (fun r => [r.pc, r.Y, r.Y25, r.Y50, r.Y100,
    r.pB25, r.pB50, r.pB100])
  (raw.filter (· ≤ PM)).mergeSort (· ≤ ·) |>.eraseDups

def checkAll (a b : Nat) (rows : List Row) : Bool :=
  let tab := evalPts (needPts rows) 0 (stAt 0)
  chain a b rows && rows.all (checkRow tab)

end ErdosComp

/-! ### The tail `N > 10⁶⁰` (fixed `p_c = p_B = 2000`, `Y = Y' > PM`) -/

namespace ErdosComp

def PM1 : Nat := PM + 1

def shT (tab : List (Nat × PSt)) : CE := (s2P tab 2000 PM1, 0)

def lemBT (tab : List (Nat × PSt)) (q T : Nat) : CE :=
  ((T : Rat) / q * (1 - prodU) + 2 * (T : Rat) / q * s2U tab 41 2000 + 2 * s2U tab 2000 PM1,
   (T : Rat) * ((3 : Rat) ^ kU - 1) + 2 * (T : Rat) * cU tab 41 2000)

def gAllC : Rat := sumF isU1B gA 1001
def gAllE (Nt : Nat) : Rat := sumF isU1B (fun p => max (gE p) (-(gA p) * Nt)) 1001

def lemCT (tab : List (Nat × PSt)) (Nt : Nat) : CE :=
  (46 / 25 * s2U tab 41 2000 + 2 * s2U tab 2000 PM1 + (1 - prodU) / 25 + cNon + gAllC +
     s2P tab 1000 2000,
   46 * cU tab 41 2000 + ((3 : Rat) ^ kU - 1) + eNon + gAllE Nt + cP tab 1000 2000)

def caseIbT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (resCE tab 25 1 [5] 2000) (shT tab)) (addCE (resCE tab 25 1 [5] 2000) (shT tab))

def caseIIT (tab : List (Nat × PSt)) (Nt : Nat) : CE :=
  addCE (addCE (resCE tab 25 2 [2, 5] 2000) (lemCT tab Nt)) (shT tab)

def caseIII1T (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (addCE (resCE tab 100 6 [2, 5] 2000) (shT tab))
    (addCE (resCE tab 100 2 [2, 5] 2000) (shT tab))) (lemBT tab 50 23)

def caseIII2aT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (2 / 100, 2) (addCE (resCE tab 100 2 [2, 5] 2000) (shT tab))) (lemBT tab 100 23)

def caseIII2bT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (addCE (1 / 100, 1) (addCE (resCE tab 100 3 [2, 5] 2000) (shT tab)))
    (addCE (resCE tab 25 1 [2, 5] 2000) (shT tab))) (lemBT tab 100 23)

def okT (c : CE) : Bool := decide (c.1 ≤ 1 / 25 - 1 / 1000) && decide (c.2 ≤ 10 ^ 30)

def checkTailWith (tab : List (Nat × PSt)) (Nt : Nat) : Bool :=
  okT (caseIbT tab) && okT (caseIIT tab Nt) && okT (caseIII1T tab) && okT (caseIII2aT tab) &&
    okT (caseIII2bT tab)

def checkTail (Nt : Nat) : Bool := checkTailWith (evalPts [31, 41, 1000, 2000, PM] 0 (stAt 0)) Nt

end ErdosComp
