import ErdosComp.Check
import ErdosComp.KTable

/-!
# The §10 interval checker (kernel-friendly)

For an interval `[lo, hi]` of `N`, every case of `proof.md` §10.6 is bounded by a rational
computed at `N = hi` (each bound is monotone in `N`), and compared with `(lo - 6)/25`.
Witnesses are grouped into buckets `[xa, xb]`; for each bucket the certificate supplies the
split point `Y` of the shared set and a claimed bound `En / (Y · KE)` for `|Ex(b)|`, which is
verified against every witness structure (Lemma E2, `Erdos848/RootLocal.lean`).

The prime table is accessed through a lookup function `lk` (instantiated with a verified
search tree).  The soundness proof is `Erdos848/Check2Sound.lean`.
-/

namespace ErdosComp

/-- Lookups in the prime table. -/
abbrev Lk := Nat → PSt

def tab3 (lk : Lk) (lo hi : Nat) : List (Nat × PSt) := [(lo, lk lo), (hi, lk hi), (PM, lk PM)]

def S2Pk (lk : Lk) (lo hi : Nat) : Rat := s2P (tab3 lk lo hi) lo hi
def S2Uk (lk : Lk) (lo hi : Nat) : Rat := s2U (tab3 lk lo hi) lo hi
def CPk (lk : Lk) (lo hi : Nat) : Rat := cP (tab3 lk lo hi) lo hi
def CUk (lk : Lk) (lo hi : Nat) : Rat := cU (tab3 lk lo hi) lo hi

/-! ### Small primes and truncated inclusion–exclusion -/

def primesUpTo (z : Nat) : List Nat := (List.range (z + 1)).filter isPrimeB
def u1UpTo (z : Nat) : List Nat := (List.range (z + 1)).filter isU1B
def primesEx (z : Nat) (excl : List Nat) : List Nat :=
  (List.range (z + 1)).filter (fun p => isPrimeB p && !(excl.contains p))

/-- Elementary symmetric functions of `f` over a list. -/
def esym (f : Nat → Rat) : List Nat → Nat → Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | p :: l, j + 1 => esym f l (j + 1) + f p * esym f l j

/-- `∑_{j ≤ d} (-1)^j e_j` (`altE` of `Erdos848/Bonf.lean`). -/
def altL (f : Nat → Rat) (l : List Nat) : Nat → Rat
  | 0 => esym f l 0
  | d + 1 => altL f l d + (-1) ^ (d + 1) * esym f l (d + 1)

/-- `∑_{1 ≤ j ≤ d} C(k, j) c^j` (`truncErr` with constant weights). -/
def chooseN : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseN n k + chooseN n (k + 1)

def terrL (k : Nat) (c : Rat) : Nat → Rat
  | 0 => 0
  | d + 1 => terrL k c d + (chooseN k (d + 1) : Rat) * c ^ (d + 1)

def invSq (c : Nat) (p : Nat) : Rat := (c : Rat) / ((p : Rat) * p)

/-! ### Linear bounds `coef · L + const` -/

/-- Lemma A′(iii) with Bonferroni (`resR`): coefficient and constant. -/
def resLin (lk : Lk) (q z pc dA : Nat) (excl : List Nat) : Rat × Rat :=
  let l := primesEx z excl
  ((1 - altL (invSq 1) l dA) / q + S2Pk lk z pc / q, terrL l.length 1 dA + CPk lk z pc)

/-- Lemma B per class (`lemBR`). -/
def lemBLin (lk : Lk) (zB pT dB : Nat) : Rat × Rat :=
  let l := u1UpTo zB
  ((1 - altL (invSq 2) l dB) / 100 + 2 * S2Uk lk zB pT / 100, terrL l.length 2 dB + 2 * CUk lk zB pT)

def evalLin (c : Rat × Rat) (L : Rat) : Rat := c.1 * L + c.2

/-! ### Lemma C (`coreB`) -/

/-- Constants of Lemma C that do not depend on `L`. -/
structure CConst where
  mU : Rat                         -- mainU over the U1 primes `≤ z₁`
  eU : Rat                         -- errU
  non : List (Rat × Rat)           -- per odd `p₂ ≤ z₂`, `p₂ ≠ 5`: `(mainU, errU)` of `Uer z₁ p₂`, with `p₂`
  nonP : List Nat
  gainP : List Nat                 -- U1 primes `≤ z₂`
  gain : List (Rat × Rat)          -- their `(mainU, errU)` of `Uer`
  s1 : Rat                         -- `S2U (z₁, pB]`
  c1 : Rat                         -- `CU (z₁, pB]`
  s2 : Rat                         -- `S2P (z₂, pc]`
  c2 : Rat                         -- `CP (z₂, pc]`

def mainUL (l : List Nat) (d : Nat) : Rat := 1 - altL (invSq 2) l d
def errUL (l : List Nat) (d : Nat) : Rat := terrL l.length 2 d

def cConst (lk : Lk) (z₁ z₂ pB pc d : Nat) : CConst :=
  let U := u1UpTo z₁
  let me := fun p => (mainUL (U.erase p) d, errUL (U.erase p) d)
  let np := primesEx z₂ [2, 5]
  let gp := u1UpTo z₂
  { mU := mainUL U d, eU := errUL U d, non := np.map me, nonP := np, gainP := gp,
    gain := gp.map me, s1 := S2Uk lk z₁ pB, c1 := CUk lk z₁ pB, s2 := S2Pk lk z₂ pc,
    c2 := CPk lk z₂ pc }

def nonQ (L μ : Rat) (p : Nat) (m : Rat × Rat) : Rat :=
  min (L / ((p : Rat) * p) * m.1 + μ * m.2) (23 / 25 * (L / ((p : Rat) * p)) * m.1 + 23 * μ * m.2)

def wholeQ (L μ : Rat) (p : Nat) : Rat := 23 / 25 * (L / ((p : Rat) * p)) + 3 * μ

def gainQ (L μ : Rat) (p : Nat) (m : Rat × Rat) : Rat := max (wholeQ L μ p - nonQ L μ p m) 0

/-! ### Lemma C in fixed point

The sums over the primes `≤ z₂` are evaluated in fixed point with scale `SF`: the per-prime
constants are rounded once (up, or down where they are subtracted), and each bucket then only
needs `Nat` arithmetic.  Any threshold `τ ≥ 0` is allowed (`Erdos848/Check2Core.lean`); the
checker takes `τ = T / SF` with `T` the `nS`-th largest rounded gain. -/

/-- The fixed-point scale. -/
def SF : Nat := 2 ^ 40

def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-- `⌈SF · x⌉` and `⌊SF · x⌋`, clipped at `0`. -/
def ceilF (x : Rat) : Nat := (-(-(x * SF)).floor).toNat
def floorF (x : Rat) : Nat := (x * SF).floor.toNat

/-- Constants of one prime `p` with `(mainU, errU) = m`: `⌈SF m₁/p²⌉`, `⌈SF m₂⌉`, `⌊SF m₁/p²⌋`,
`⌊SF m₂⌋` and `⌈SF/p²⌉`. -/
structure PC where
  aU : Nat
  bU : Nat
  aL : Nat
  bL : Nat
  w : Nat

def mkPC (p : Nat) (m : Rat × Rat) : PC :=
  ⟨ceilF (m.1 / ((p : Rat) * p)), ceilF m.2, floorF (m.1 / ((p : Rat) * p)), floorF m.2,
    cdiv SF (p * p)⟩

/-- `SF · nonQ (L₄ / 4) μ p m`, rounded up. -/
def nonUp (L4 μ : Nat) (c : PC) : Nat :=
  min (cdiv (L4 * c.aU) 4 + μ * c.bU) (cdiv (23 * L4 * c.aU) 100 + 23 * μ * c.bU)

/-- `SF · nonQ (L₄ / 4) μ p m`, rounded down. -/
def nonLo (L4 μ : Nat) (c : PC) : Nat :=
  min (L4 * c.aL / 4 + μ * c.bL) (23 * L4 * c.aL / 100 + 23 * μ * c.bL)

/-- `SF · gainQ (L₄ / 4) μ p m`, rounded up. -/
def gainUp (L4 μ : Nat) (c : PC) : Nat := cdiv (23 * L4 * c.w) 100 + 3 * μ * SF - nonLo L4 μ c

def sumN : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumN xs

def maxN : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxN xs)

/-- The `(k + 1)`-th largest element (`0` if there are fewer). -/
def kthN : Nat → List Nat → Nat
  | 0, l => maxN l
  | k + 1, l => kthN k (l.erase (maxN l))

/-- The rounded constants of `cConst`. -/
structure CF where
  non : List PC
  gain : List PC

def mkCF (cc : CConst) : CF :=
  ⟨(cc.nonP.zip cc.non).map (fun pm => mkPC pm.1 pm.2),
    (cc.gainP.zip cc.gain).map (fun pm => mkPC pm.1 pm.2)⟩

/-- An upper bound for `coreB (L₄ / 4) μ … τ` with `τ = T / SF`. -/
def coreF (cc : CConst) (cf : CF) (L4 μ nS : Nat) : Rat :=
  let L : Rat := (L4 : Rat) / 4
  let gs := cf.gain.map (gainUp L4 μ)
  let T := kthN (nS - 1) gs
  23 * (2 * (L / 25) * cc.s1 + μ * 2 * cc.c1) + (L / 25 * cc.mU + μ * cc.eU) +
    ((sumN (cf.non.map (nonUp L4 μ)) + (nS * T + sumN (gs.map (· - T))) : Nat) : Rat) / SF +
    (L * cc.s2 + μ * cc.c2)

/-- `nS`: the number of `n ≥ 1` with `(q₀ ⋯ q_{n-1})² ≤ x² + 1`. -/
def nSOf (x : Nat) : Nat :=
  ((List.range 29).filter (fun l => ulProd (l + 1) * ulProd (l + 1) ≤ x * x + 1)).length

/-- `PrefixOK x (nSOf x)`. -/
def nSOK (x : Nat) : Bool :=
  decide (nSOf x + 1 ≤ 30) && decide (x * x + 1 < ulProd (nSOf x + 1) * ulProd (nSOf x + 1))

/-- Side conditions for the monotonicity of `coreB` in `L`. -/
def cConstOK (cc : CConst) : Bool :=
  decide (0 ≤ cc.mU) && cc.non.all (fun m => decide (0 ≤ m.1)) &&
    cc.gain.all (fun m => decide (0 ≤ m.1) && decide (m.1 ≤ 23 / 25))

/-! ### `Mid`, the U1 tail and the Pell tail -/

/-- Copies of `Erdos848.admB`, `chainCnt`, `pellTerm` (Lemma P). -/
def admBk (m : Nat) : Bool :=
  (m % 8 == 1 || m % 8 == 2 || m % 8 == 5) && m % 3 != 0 && m % 7 != 0 && m % 11 != 0 &&
    m % 19 != 0 && m % 23 != 0

def chainK (G X₂ : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, T => if T < X₂ then 0 else 1 + chainK G X₂ f (T / G)

def pellTermK (N Y m : Nat) : Nat :=
  if admBk m then chainK (max 9 (4 * m)) (m * (Y + 1) ^ 2 - 1) (N ^ 2 + 1) (N ^ 2) else 0

/-- `midB N pc Y = ∑_{pc < p ≤ Y} (⌊N/p²⌋ + 1)`. -/
def midQ (lk : Lk) (N pc Y : Nat) : Rat :=
  let h := max pc (min Y (Nat.sqrt N))
  N * S2Pk lk pc h + CPk lk pc Y

/-- `∑_{U1 p ∈ (pT, Y]} hcnt N p`. -/
def u1TailQ (lk : Lk) (N pT Y : Nat) : Rat :=
  let a := max pT (min Y (Nat.sqrt N))
  let b := max a (min Y (Nat.sqrt (2 * N)))
  2 * (N * S2Uk lk pT a + CUk lk pT a) + 2 * CUk lk a b + CUk lk b Y

/-- Admissible `m` in `[1, M]`, counted directly. -/
def admCnt (lo : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => admCnt lo k + cond (admBk (lo + k + 1)) 1 0

/-- Block length of the prefix table of admissible `m`. -/
def admBlock : Nat := 1000

/-- The prefix table: `pre[i] = admCnt 0 (1000 i)`. -/
def admPreOK : List Nat → Nat → Nat → Bool
  | [], _, _ => true
  | c :: cs, i, acc => Nat.beq c acc && admPreOK cs (i + 1) (acc + admCnt (i * admBlock) admBlock)

/-- `#{m ∈ [1, M] : admB m}` from a prefix table `pre` (`pre[i] = #{m ≤ 1000 i}`). -/
def admUpTo (pre : List Nat) (M : Nat) : Nat :=
  pre.getD (M / admBlock) 0 + admCnt (M / admBlock * admBlock) (M % admBlock)

/-- `∑_{m ≤ K} pellTerm N Y m`. -/
def pellSum (N Y : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => pellSum N Y k + pellTermK N Y (k + 1)

/-- The Pell tail: terms `m ≤ K` exactly, the rest count `1` each (checked: `m > K` gives a
chain of length `≤ 1`). -/
def pellQ (pre : List Nat) (N Y K : Nat) : Option Nat :=
  let M := (N ^ 2 + 1) / (Y + 1) ^ 2
  if K ≤ M ∧ M / admBlock < pre.length ∧
      (K = M ∨ N ^ 2 / max 9 (4 * (K + 1)) < (K + 1) * (Y + 1) ^ 2 - 1) then
    some (pellSum N Y K + (admUpTo pre M - admUpTo pre K))
  else none

def tailQ (lk : Lk) (pre : List Nat) (N pT Y K : Nat) : Option Rat :=
  (pellQ pre N Y K).map (fun s => u1TailQ lk N pT Y + s)

/-! ### `Ex(b)`: witness structures (Lemma E2) -/

/-- Odd primes `≤ 23` (the small primes of the structures). -/
def smallW : List Nat := [3, 5, 7, 11, 13, 17, 19, 23]

/-- Products of the first `u` primes `> 23`. -/
def bigProd : Nat → Nat
  | 0 => 1
  | 1 => 29
  | 2 => 29 * 31
  | 3 => 29 * 31 * 37
  | 4 => 29 * 31 * 37 * 41
  | 5 => 29 * 31 * 37 * 41 * 43
  | _ => 29 * 31 * 37 * 41 * 43 * 47

/-- All sublists of a list. -/
def subl : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => subl xs ++ (subl xs).map (x :: ·)

/-- A strictly increasing list. -/
def incr : List Nat → Bool
  | a :: b :: rest => Nat.blt a b && incr (b :: rest)
  | _ => true

/-- A table entry for Lemma E2: `(e, Q)` with period `P = 2^e ∏ Q`, `Ssum = ∑_{m ≤ P} g(m)` and
`bn ≥ max_{r < P} (P · G(r) - Ssum · r)`. -/
structure DiscE where
  e : Nat
  qs : List Nat
  P : Nat
  Ssum : Nat
  bn : Nat

/-- A witness structure `(e, S, u)` with its least possible value `bm` and its choices. -/
structure StrE where
  e : Nat
  qs : List Nat
  u : Nat
  bm : Nat
  ch : List DiscE

def twoC (e : Nat) : Nat := if e = 3 then 4 else if e = 2 then 2 else 1

def strBm (e : Nat) (qs : List Nat) (u : Nat) : Nat := 2 ^ e * qs.prod * bigProd u

/-- `|Ex(b)| ≤ En / (Y · KE)`. -/
def KE : Nat := 2 ^ 20

/-- One structure, given `aN = N + 1 + M Y` (`M = exM N xb Y`) and `bN = √(N bm + 1) + 1 + bm`. -/
def strOK (aN bN Y En : Nat) (s : StrE) : Bool :=
  let w := s.qs.length + s.u
  Nat.ble (twoC s.e * 2 ^ w * aN * KE) En ||
    s.ch.any (fun d =>
      Nat.beq d.e s.e && d.qs.all (fun q => s.qs.contains q) &&
      Nat.ble (2 ^ (w - d.qs.length) * (d.Ssum * aN * s.bm + d.bn * bN * Y) * KE)
        (En * d.P * s.bm))

/-- All structures with `bm ≤ xb` pass (the list is sorted by `bm`; `bNs` is aligned with it). -/
def exOK (strs : List StrE) (bNs : List Nat) (aN Y xb En : Nat) : Bool :=
  match strs, bNs with
  | s :: ss, bN :: bs => !Nat.ble s.bm xb || (strOK aN bN Y En s && exOK ss bs aN Y xb En)
  | [], _ => true
  | _ :: _, [] => false

def bNsOf (N : Nat) (strs : List StrE) : List Nat :=
  strs.map (fun s => Nat.sqrt (N * s.bm + 1) + 1 + s.bm)

def exAN (N xb Y : Nat) : Nat := N + 1 + (N * xb + 1) / ((Y + 1) * (Y + 1)) * Y

/-! ### Buckets -/

def bucketsGo (N : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | f + 1, xa =>
    if xa < N then
      let xb := min N (max (xa + 1) (xa * 13 / 10))
      (xa, xb) :: bucketsGo N f xb
    else []

def buckets (N : Nat) : List (Nat × Nat) := bucketsGo N N 1

/-- Certificate data for one bucket: the split point `Y` and the claimed `Ex` numerator. -/
structure BkD where
  Y : Nat
  En : Nat

/-- Shared set bound `midB + Ex` for one bucket, or `none` if the `Ex` claim fails. -/
def shQ (lk : Lk) (strs : List StrE) (bNs : List Nat) (N pc : Nat) (xb : Nat) (d : BkD) :
    Option Rat :=
  if 1 ≤ d.Y ∧ exOK strs bNs (exAN N xb d.Y) d.Y xb d.En then
    some (midQ lk N pc d.Y + (d.En : Rat) / ((d.Y : Rat) * KE))
  else none

/-- `max_i f(bucket_i, data_i)`, failing if any is `none` or the lengths differ. -/
def maxBk (f : Nat × Nat → BkD → Option Rat) : List (Nat × Nat) → List BkD → Option Rat
  | [], [] => some 0
  | b :: bs, d :: ds =>
    match f b d, maxBk f bs ds with
    | some x, some y => some (max x y)
    | _, _ => none
  | _, _ => none

/-! ### The cases -/

/-- Parameters of one case. `pB` is `p_B` (case II) or `p_T` (case III). -/
structure Prm2 where
  z : Nat
  dA : Nat
  zB : Nat
  dB : Nat
  z₁ : Nat
  z₂ : Nat
  dC : Nat
  pc : Nat
  pB : Nat
  Yt : Nat
  Kt : Nat

def prmOK (p : Prm2) : Bool :=
  p.dA % 2 == 1 && p.dB % 2 == 1 && p.dC % 2 == 1 && decide (5 ≤ p.z₂) && decide (1 ≤ p.Yt)

/-- Structure lists for the three witness constraints. -/
structure Strs where
  any5 : List StrE
  odd : List StrE
  even : List StrE

/-- I.b: `2 max_i [R({7}, 25; {5}; N + 1 - xa) + Sh]`. -/
def caseIbQ (lk : Lk) (S : Strs) (N : Nat) (p : Prm2) (ds : List BkD) : Option Rat :=
  let r := resLin lk 25 p.z p.pc p.dA [5]
  let bNs := bNsOf N S.any5
  if decide (0 ≤ r.1) then
    (maxBk (fun b d => (shQ lk S.any5 bNs N p.pc b.2 d).map
      (fun s => evalLin r ((N + 1 - b.1 : Nat) : Rat) + s)) (buckets N) ds).map (fun m => 2 * m)
  else none

/-- II. -/
def caseIIQ (lk : Lk) (pre : List Nat) (S : Strs) (N : Nat) (p : Prm2) (ds : List BkD) :
    Option Rat :=
  let r := resLin lk 25 p.z p.pc p.dA [2, 5]
  let cc := cConst lk p.z₁ p.z₂ p.pB p.pc p.dC
  let cf := mkCF cc
  let bNs := bNsOf N S.even
  if cConstOK cc && decide (0 ≤ r.1) then
    match tailQ lk pre N p.pB p.Yt p.Kt,
      maxBk (fun b d => if nSOK b.2 then (shQ lk S.even bNs N p.pc b.2 d).map (fun s =>
        min (coreF cc cf (2 * (2 * N + 1 - b.1)) 2 (nSOf b.2))
          (coreF cc cf (4 * N) 1 (nSOf b.2)) + s) else none) (buckets N) ds with
    | some t, some m => some (2 * evalLin r (N : Rat) + m + t)
    | _, _ => none
  else none

/-- `max_i [min(23 lemB, lemC′) + Sh]` over odd witnesses (case III). -/
def shbQ (lk : Lk) (S : Strs) (N : Nat) (p : Prm2) (ds : List BkD) : Option Rat :=
  let lb := lemBLin lk p.zB p.pB p.dB
  let cc := cConst lk p.z₁ p.z₂ p.pB p.pc p.dC
  let cf := mkCF cc
  let bNs := bNsOf N S.odd
  if cConstOK cc && decide (0 ≤ lb.1) then
    maxBk (fun b d => if nSOK b.2 then (shQ lk S.odd bNs N p.pc b.2 d).map (fun s =>
      min (23 * evalLin lb ((N + 1 - b.1 : Nat) : Rat))
        (coreF cc cf (N + 1 - b.1) 1 (nSOf b.2)) + s) else none) (buckets N) ds
  else none

def caseIII1Q (lk : Lk) (pre : List Nat) (S : Strs) (N : Nat) (p : Prm2) (ds : List BkD) :
    Option Rat :=
  let r := resLin lk 100 p.z p.pc p.dA [2, 5]
  if decide (0 ≤ r.1) then
    match shbQ lk S N p ds, tailQ lk pre N p.pB p.Yt p.Kt with
    | some s, some t => some (8 * evalLin r (N : Rat) + 2 * s + t)
    | _, _ => none
  else none

def caseIII2bQ (lk : Lk) (pre : List Nat) (S : Strs) (N : Nat) (p : Prm2) (ds : List BkD) :
    Option Rat :=
  let r := resLin lk 100 p.z p.pc p.dA [2, 5]
  if decide (0 ≤ r.1) then
    match shbQ lk S N p ds, tailQ lk pre N p.pB p.Yt p.Kt with
    | some s, some t => some (((N : Rat) / 100 + 1) + 4 * evalLin r (N : Rat) + s + t)
    | _, _ => none
  else none

/-- III.2 α: the smaller of the three-witness and two-witness bounds. -/
def caseIII2aQ (lk : Lk) (pre : List Nat) (S : Strs) (N : Nat) (p : Prm2) (ds ds' : List BkD) :
    Option Rat :=
  let r := resLin lk 100 p.z p.pc p.dA [2, 5]
  let bNs := bNsOf N S.any5
  if decide (0 ≤ r.1) then
  match shbQ lk S N p ds, tailQ lk pre N p.pB p.Yt p.Kt,
    maxBk (fun b d => (shQ lk S.any5 bNs N p.pc b.2 d).map
      (fun s => 3 * evalLin r ((N + 1 - b.1 : Nat) : Rat) + s)) (buckets N) ds',
    maxBk (fun b d => (shQ lk S.any5 bNs N p.pc b.2 d).map
      (fun s => evalLin r (N : Rat) + s)) (buckets N) ds' with
  | some s, some t, some m3, some m1 =>
    some (min (2 * evalLin r (N : Rat) + s + t + 2 * m3)
      (((N : Rat) / 100 + 1) + 6 * evalLin r (N : Rat) + s + t + m1))
  | _, _, _, _ => none
  else none

/-- One interval of the certificate. -/
structure Iv2 where
  lo : Nat
  hi : Nat
  p : List Prm2          -- five cases
  d : List (List BkD)    -- bucket data: I.b, II, III.1, III.2β, III.2α (odd), III.2α (any)

def below (lo : Nat) : Option Rat → Bool
  | some v => decide (v < ((lo : Rat) - 6) / 25)
  | none => false

def checkIv2 (lk : Lk) (pre : List Nat) (S : Strs) (iv : Iv2) : Bool :=
  match iv.p, iv.d with
  | [p0, p1, p2, p3, p4], [d0, d1, d2, d3, d4, d5] =>
    decide (7 ≤ iv.lo) && decide (iv.lo ≤ iv.hi) && decide (iv.hi ≤ 160000000) &&
    prmOK p0 && prmOK p1 && prmOK p2 && prmOK p3 && prmOK p4 &&
    below iv.lo (caseIbQ lk S iv.hi p0 d0) &&
    below iv.lo (caseIIQ lk pre S iv.hi p1 d1) &&
    below iv.lo (caseIII1Q lk pre S iv.hi p2 d2) &&
    below iv.lo (caseIII2bQ lk pre S iv.hi p3 d3) &&
    below iv.lo (caseIII2aQ lk pre S iv.hi p4 d4 d5)
  | _, _ => false

/-! ### Validation of the static data -/

/-- `|rootSet b m|`. -/
def rootCnt (b m : Nat) : Nat := ((List.range b).filter (fun s => s * s * m % b == 1 % b)).length

/-- `gLoc e Q m`. -/
def gLocL (e : Nat) (qs : List Nat) (m : Nat) : Nat :=
  rootCnt (2 ^ e) m * (qs.map (fun q => rootCnt q m)).prod

/-- `G(m) = ∑_{k ≤ m} g(k)`: checks `P G(r) ≤ Ssum r + bn` for `r < P` and `G(P) = Ssum`. -/
def discGo (e : Nat) (qs : List Nat) (P Ssum bn : Nat) : Nat → Nat → Nat → Bool
  | 0, _, G => Nat.beq G Ssum
  | f + 1, m, G =>
    (Nat.ble P m || Nat.ble (P * (G + gLocL e qs m)) (Ssum * m + bn)) &&
      discGo e qs P Ssum bn f (m + 1) (G + gLocL e qs m)

def discOK (d : DiscE) : Bool :=
  decide (d.e ≤ 3) && incr d.qs && Nat.blt 0 d.P && Nat.beq d.P (2 ^ d.e * d.qs.prod) &&
    discGo d.e d.qs d.P d.Ssum d.bn d.P 1 0

def discBEq (a b : DiscE) : Bool :=
  Nat.beq a.e b.e && decide (a.qs = b.qs) && Nat.beq a.P b.P && Nat.beq a.Ssum b.Ssum &&
    Nat.beq a.bn b.bn

/-- Witness constraints: `0` coprime to 5, `1` odd, `2` even. -/
def consOK (ci e : Nat) (qs : List Nat) : Bool :=
  if ci = 0 then !qs.contains 5 else if ci = 1 then Nat.beq e 0 else decide (1 ≤ e)

def strValid (disc : List DiscE) (s : StrE) : Bool :=
  decide (s.e ≤ 3) && Nat.beq s.bm (strBm s.e s.qs s.u) && s.ch.all (fun d => disc.any (discBEq d))

def sortedBm : List StrE → Bool
  | a :: b :: rest => Nat.ble a.bm b.bm && sortedBm (b :: rest)
  | _ => true

/-- The structures with `bm ≤ 1.6·10⁸` and constraint `ci`, for one `e`. -/
def keysOf (ci e : Nat) : List (List Nat × Nat) :=
  (subl smallW).flatMap (fun qs =>
    ((List.range 6).filter (fun u => consOK ci e qs && Nat.ble (strBm e qs u) 160000000)).map
      (fun u => (qs, u)))

def completeE (ci e : Nat) (strs : List StrE) : Bool :=
  (keysOf ci e).all (fun k => strs.any (fun s => Nat.beq s.e e && decide (s.qs = k.1) && Nat.beq s.u k.2))

end ErdosComp
