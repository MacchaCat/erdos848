import Erdos848.InclExcl
import Erdos848.SqrtCount
import Erdos848.ExBound
import Erdos848.Skeleton
import Erdos848.PellTail

/-!
# Phase 6 (part 1): root sets and single-class sieves

`witRoots b p` : residues `r < p²` with `p² ∣ r·b + 1` (at most one, `card_witRoots_le`);
`sqRoots p`    : residues `r < p²` with `p² ∣ r² + 1` (at most two for odd `p`, `card_sqRoots_le`).

`classSieve_le` is the generic single-class sieve of Lemma A′(iii) and Lemma B:
small primes by inclusion–exclusion (`card_union_le`), medium primes by a union bound.
-/

namespace Erdos848

open Finset

/-- Residues `r < p²` with `p² ∣ r b + 1`. -/
def witRoots (b p : ℕ) : Finset ℕ := (range (p * p)).filter (fun r => p * p ∣ r * b + 1)

/-- Residues `r < p²` with `p² ∣ r² + 1`. -/
def sqRoots (p : ℕ) : Finset ℕ := (range (p * p)).filter (fun r => p * p ∣ r * r + 1)

lemma witRoots_sub (b p : ℕ) : witRoots b p ⊆ range (p * p) := filter_subset _ _
lemma sqRoots_sub (p : ℕ) : sqRoots p ⊆ range (p * p) := filter_subset _ _

lemma mod_mem_witRoots {b p : ℕ} (hp : 0 < p) (a : ℕ) :
    a % (p * p) ∈ witRoots b p ↔ p * p ∣ a * b + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hmod : (a % (p * p)) * b + 1 ≡ a * b + 1 [MOD p * p] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul_right b (Nat.mod_modEq a _))
  simp only [witRoots, mem_filter, mem_range, Nat.mod_lt a hpp, true_and]
  exact (Nat.ModEq.dvd_iff hmod dvd_rfl)

lemma mod_mem_sqRoots {p : ℕ} (hp : 0 < p) (a : ℕ) :
    a % (p * p) ∈ sqRoots p ↔ p * p ∣ a * a + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hmod : (a % (p * p)) * (a % (p * p)) + 1 ≡ a * a + 1 [MOD p * p] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul (Nat.mod_modEq a _) (Nat.mod_modEq a _))
  simp only [sqRoots, mem_filter, mem_range, Nat.mod_lt a hpp, true_and]
  exact (Nat.ModEq.dvd_iff hmod dvd_rfl)

lemma card_witRoots_le {b p : ℕ} (hp : p.Prime) : (witRoots b p).card ≤ 1 := by
  by_cases hpb : p ∣ b
  · have : witRoots b p = ∅ := by
      rw [witRoots, filter_eq_empty_iff]
      intro r _; exact not_sq_dvd_of_dvd hp hpb
    rw [this]; simp
  · obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp hpb
    rw [card_le_one]
    intro r hr r' hr'
    simp only [witRoots, mem_filter, mem_range] at hr hr'
    have h1 := (hc r).mp hr.2
    have h2 := (hc r').mp hr'.2
    rw [Nat.mod_eq_of_lt hr.1] at h1
    rw [Nat.mod_eq_of_lt hr'.1] at h2
    omega

lemma card_sqRoots_le {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : (sqRoots p).card ≤ 2 := by
  have hpp : 1 ≤ p * p := Nat.mul_pos hp.pos hp.pos
  have hpc : ¬ p ∣ p * p - 1 := by
    intro h
    have h1 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub (dvd_mul_right p p) h
    rw [Nat.sub_sub_self hpp] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have := sqrtCount_oddPrimePow_le (e := 2) hp hodd hpc
  unfold sqrtCount at this
  rw [pow_two] at this
  refine le_trans (card_le_card ?_) this
  intro r hr
  simp only [sqRoots, mem_filter, mem_range] at hr ⊢
  refine ⟨hr.1, ?_⟩
  rw [Nat.mod_eq_of_lt (Nat.sub_lt hpp one_pos)]
  obtain ⟨k, hk⟩ := hr.2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0] at hk; omega
    · exact h
  have : r * r = (p * p) * (k - 1) + (p * p - 1) := by
    have : p * p * k = p * p * (k - 1) + p * p := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hk1)]
    omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.sub_lt hpp one_pos)]

/-- U1 primes: `p ≡ 1 (mod 4)`, `p ≥ 13`. -/
def IsU1 (p : ℕ) : Prop := p.Prime ∧ p % 4 = 1 ∧ 13 ≤ p

instance : DecidablePred IsU1 := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A prime whose square divides `x² + 1` is `≡ 1 (mod 4)`. -/
lemma prime_mod_four_of_sq_dvd {p x : ℕ} (hp : p.Prime) (h : p * p ∣ x * x + 1) : p % 4 = 1 := by
  have hdvd : p ∣ x * x + 1 := dvd_trans (dvd_mul_right p p) h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
      rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
    omega
  have h3 : p % 4 ≠ 3 := by
    have := Fact.mk hp
    apply ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := (x : ZMod p))
    have : ((x * x + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    linear_combination this
  rcases Nat.Prime.eq_two_or_odd hp with h2 | h2
  · exact absurd h2 hp2
  · omega

/-- For `x ≢ ±7 (mod 25)`, a prime square dividing `x² + 1` comes from a U1 prime. -/
lemma isU1_of_sq_dvd {p x : ℕ} (hp : p.Prime) (h : p * p ∣ x * x + 1)
    (hx : x % 25 ≠ 7 ∧ x % 25 ≠ 18) : IsU1 p := by
  have h4 := prime_mod_four_of_sq_dvd hp h
  refine ⟨hp, h4, ?_⟩
  by_contra hlt
  push Not at hlt
  have hp5 : p = 5 := by
    interval_cases p <;> first | rfl | omega | (exfalso; norm_num at hp)
  subst hp5
  have h25 : (x * x + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
  have hx25 : (x * x + 1) % 25 = ((x % 25) * (x % 25) + 1) % 25 := by
    rw [Nat.add_mod, Nat.mul_mod]; conv_rhs => rw [Nat.add_mod]
  have : x % 25 < 25 := Nat.mod_lt _ (by norm_num)
  rw [hx25] at h25
  interval_cases hr : x % 25 <;> omega

/-! ### The generic single-class sieve -/

/-- Primes `p ≤ z` with property `Q`. -/
def smallP (z : ℕ) (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (range (z + 1)).filter (fun p => p.Prime ∧ Q p)

/-- Primes `z < p ≤ w` with property `Q`. -/
def midP (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (Ioc z w).filter (fun p => p.Prime ∧ Q p)

lemma coprime_sq_of_primes {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : p ≠ p') :
    Nat.Coprime (p * p) (p' * p') := by
  have := (Nat.coprime_primes hp hp').mpr h
  have h2 : Nat.Coprime (p * p) p' := Nat.coprime_mul_iff_left.mpr ⟨this, this⟩
  exact Nat.Coprime.mul_right h2 h2

/-- One prime: `#{a ≤ N : a ≡ t (q), a mod p² ∈ R} ≤ |R| (N/q)/p² + |R|`. -/
lemma card_single_le (N q t p : ℕ) (R : Finset ℕ) (hq : 0 < q) (ht : t < q) (hp : 0 < p)
    (hR : R ⊆ range (p * p)) (hcop : Nat.Coprime q p) :
    (((Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ R)).card : ℝ) ≤
      (R.card : ℝ) * ((N : ℝ) / q / (p * p)) + R.card := by
  have h := card_union_le N q t (fun p => p * p) (fun _ => R) {p} hq ht
    (by simp [hp.ne']) (fun p' hp' r hr => by
      rw [mem_singleton] at hp'; subst hp'; exact mem_range.mp (hR hr))
    (fun p' hp' => by rw [mem_singleton] at hp'; subst hp'; exact Nat.Coprime.mul_right hcop hcop)
    (fun p₁ h₁ p₂ h₂ hne => by rw [mem_singleton] at h₁ h₂; exact absurd (h₁.trans h₂.symm) hne)
  have hset : (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p' ∈ ({p} : Finset ℕ), a % (p' * p') ∈ R) =
      (Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ R) := by
    apply filter_congr; intro a _; simp
  rw [hset] at h
  simp only [prod_singleton, Nat.cast_mul] at h
  have : (N : ℝ) / q * (1 - (1 - (R.card : ℝ) / (p * p))) + (1 + (R.card : ℝ) - 1) =
      (R.card : ℝ) * ((N : ℝ) / q / (p * p)) + R.card := by ring
  linarith

/-- **Single-class sieve.** Small primes (`p ≤ z`) by inclusion–exclusion, medium primes
(`z < p ≤ w`) by a union bound; `c` bounds the number of bad residues mod `p²`. -/
theorem classSieve_le (N q t z w c : ℕ) (Rs : ℕ → Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hq : 0 < q) (ht : t < q) (hc : c ≤ 4)
    (hRs : ∀ p, Rs p ⊆ range (p * p)) (hRc : ∀ p, p.Prime → Q p → (Rs p).card ≤ c)
    (hcop : ∀ p, p.Prime → Q p → Nat.Coprime q p) :
    (((Icc 1 N).filter (fun a => a % q = t ∧
        ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) +
        (((1 + c : ℕ) : ℝ) ^ (smallP z Q).card - 1) +
        ∑ p ∈ midP z w Q, ((c : ℝ) * ((N : ℝ) / q / (p * p)) + c) := by
  classical
  set A := (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ smallP z Q, a % (p * p) ∈ Rs p)
  set B : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ Rs p)
  have hsub : (Icc 1 N).filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p) ⊆ A ∪ (midP z w Q).biUnion B := by
    intro a ha
    simp only [mem_filter] at ha
    obtain ⟨ha1, hat, p, hpw, hp, hQ, hR⟩ := ha
    by_cases hpz : p ≤ z
    · apply mem_union_left
      simp only [A, mem_filter, smallP, mem_range]
      exact ⟨ha1, hat, p, ⟨by omega, hp, hQ⟩, hR⟩
    · apply mem_union_right
      simp only [mem_biUnion, B, mem_filter, midP, mem_Ioc]
      exact ⟨p, ⟨⟨by omega, hpw⟩, hp, hQ⟩, ha1, hat, hR⟩
  have hcard : (((Icc 1 N).filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (A.card : ℝ) + ∑ p ∈ midP z w Q, ((B p).card : ℝ) := by
    have h1 := (card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := card_biUnion_le (s := midP z w Q) (t := B)
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  -- small primes
  have hsmallP : ∀ p ∈ smallP z Q, p.Prime ∧ Q p := fun p hp => (mem_filter.mp hp).2
  have hA := card_union_le N q t (fun p => p * p) Rs (smallP z Q) hq ht
    (fun p hp => Nat.mul_pos (hsmallP p hp).1.pos (hsmallP p hp).1.pos)
    (fun p _ r hr => mem_range.mp (hRs p hr))
    (fun p hp => Nat.Coprime.mul_right (hcop p (hsmallP p hp).1 (hsmallP p hp).2)
      (hcop p (hsmallP p hp).1 (hsmallP p hp).2))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hsmallP p hp).1 (hsmallP p' hp').1 hne)
  have hNq : (0 : ℝ) ≤ (N : ℝ) / q := by positivity
  have hprod : ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p)) ≤
      ∏ p ∈ smallP z Q, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) := by
    apply prod_le_prod₀
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hsmallP p hp).1.two_le
      have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
      rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
      push_cast
      have : (0 : ℝ) < p * p := by have := (hsmallP p hp).1.pos; positivity
      gcongr
  have hprod2 : ∏ p ∈ smallP z Q, (1 + ((Rs p).card : ℝ)) ≤ ((1 + c : ℕ) : ℝ) ^ (smallP z Q).card := by
    rw [← prod_const]
    apply prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
      push_cast; linarith
  have hA' : (A.card : ℝ) ≤ (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) +
      (((1 + c : ℕ) : ℝ) ^ (smallP z Q).card - 1) := by
    have : (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
        (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) :=
      mul_le_mul_of_nonneg_left (by linarith) hNq
    linarith
  -- medium primes
  have hB : ∀ p ∈ midP z w Q, ((B p).card : ℝ) ≤ (c : ℝ) * ((N : ℝ) / q / (p * p)) + c := by
    intro p hp
    have hpQ := (mem_filter.mp hp).2
    have h := card_single_le N q t p (Rs p) hq ht hpQ.1.pos (hRs p) (hcop p hpQ.1 hpQ.2)
    have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hpQ.1 hpQ.2
    have : (0 : ℝ) ≤ (N : ℝ) / q / (p * p) := by positivity
    calc ((B p).card : ℝ) ≤ ((Rs p).card : ℝ) * ((N : ℝ) / q / (p * p)) + (Rs p).card := h
      _ ≤ _ := by gcongr
  have := sum_le_sum hB
  linarith

/-! ### Lemma A′: sieving by one witness -/

/-- `Mid(b)`: some prime `p ∈ (pc, Y]` has `p² ∣ ab + 1`. -/
def midSet (N b pc Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => ∃ p ≤ Y, p.Prime ∧ pc < p ∧ a % (p * p) ∈ witRoots b p)

/-- The restricted part of Lemma A′(iii) for one class `t`. -/
def resPart (N b q t pc : ℕ) (excl : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ≤ pc, p.Prime ∧ p ∉ excl ∧ a % (p * p) ∈ witRoots b p)

/-- Every `a` with `ab + 1` not squarefree and no excluded prime square lies in a restricted
part, in `Mid(b)` or in `Ex(b)`. -/
lemma witness_cover (N b q pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop) [DecidablePred Pa]
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (Icc 1 N).filter (fun a => Pa a ∧ ¬ Squarefree (a * b + 1)) ⊆
      (Tset.biUnion (fun t => resPart N b q t pc excl) ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro a ha
  simp only [mem_filter, mem_Icc] at ha
  obtain ⟨⟨ha1, haN⟩, hPa, hsq⟩ := ha
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hpe : p ∉ excl := fun h => hexcl a hPa p h hd
  have hR : a % (p * p) ∈ witRoots b p := (mod_mem_witRoots hp.pos a).mpr hd
  by_cases hpc : p ≤ pc
  · apply mem_union_left; apply mem_union_left
    simp only [mem_biUnion, resPart, mem_filter, mem_Icc]
    exact ⟨a % q, hT a hPa, ⟨ha1, haN⟩, rfl, p, hpc, hp, hpe, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [midSet, mem_filter, mem_Icc]
    exact ⟨⟨ha1, haN⟩, p, hpY, hp, by omega, hR⟩
  · apply mem_union_right
    simp only [exSet, mem_filter, mem_Icc]
    have h1 : p ≤ a * b + 1 :=
      le_trans (Nat.le_mul_self p) (Nat.le_of_dvd (Nat.succ_pos _) hd)
    have h2 : a * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b haN) 1
    exact ⟨⟨ha1, haN⟩, p, ⟨by omega, h1.trans h2⟩, hd⟩

/-- **Lemma A′(i).** -/
lemma card_midSet_le (N b pc Y : ℕ) :
    ((midSet N b pc Y).card : ℝ) ≤
      ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) := by
  have h := classSieve_le N 1 0 pc Y 1 (witRoots b) (fun p => pc < p) one_pos one_pos
    (by norm_num) (witRoots_sub b) (fun p hp _ => card_witRoots_le hp)
    (fun p _ _ => Nat.coprime_one_left p)
  have hsmall : smallP pc (fun p => pc < p) = ∅ := by
    rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
  rw [hsmall] at h
  simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_one,
    Nat.mod_one, true_and, div_one, one_mul] at h
  have hset : midSet N b pc Y = (Icc 1 N).filter
      (fun a => ∃ p ≤ Y, p.Prime ∧ pc < p ∧ a % (p * p) ∈ witRoots b p) := rfl
  rw [hset]
  simpa using h

/-- **Lemma A′(iii)** for one class `t`. -/
lemma card_resPart_le (N b q t z pc : ℕ) (excl : Finset ℕ) (hq : 0 < q) (ht : t < q)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p) :
    ((resPart N b q t pc excl).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1) := by
  have h := classSieve_le N q t z pc 1 (witRoots b) (· ∉ excl) hq ht (by norm_num)
    (witRoots_sub b) (fun p hp _ => card_witRoots_le hp) hcop
  simp only [Nat.cast_one, one_mul, Nat.reduceAdd, Nat.cast_ofNat] at h
  exact h

/-- **Lemma A′** for a part of `A` lying in the classes `Tset` mod `q`. -/
theorem badCount_le (N b q z pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop) [DecidablePred Pa]
    (hb : 1 ≤ b) (hY : 1 ≤ Y) (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p)
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (badCount N Pa b : ℝ) ≤
      Tset.card * ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1)) +
      ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) +
      rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  have hc := card_le_card (witness_cover N b q pc Y Tset excl Pa hT hexcl)
  have h1 := Finset.card_union_le (Tset.biUnion (fun t => resPart N b q t pc excl) ∪ midSet N b pc Y)
    (exSet N b Y)
  have h1' := Finset.card_union_le (Tset.biUnion (fun t => resPart N b q t pc excl)) (midSet N b pc Y)
  have h2 := card_biUnion_le (s := Tset) (t := fun t => resPart N b q t pc excl)
  have hcN : badCount N Pa b ≤ ∑ t ∈ Tset, (resPart N b q t pc excl).card +
      (midSet N b pc Y).card + (exSet N b Y).card := by
    unfold badCount; omega
  have hcR : (badCount N Pa b : ℝ) ≤ ∑ t ∈ Tset, ((resPart N b q t pc excl).card : ℝ) +
      ((midSet N b pc Y).card : ℝ) + ((exSet N b Y).card : ℝ) := by exact_mod_cast hcN
  have hres : ∑ t ∈ Tset, ((resPart N b q t pc excl).card : ℝ) ≤ ∑ _t ∈ Tset,
      ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1)) :=
    sum_le_sum (fun t ht => card_resPart_le N b q t z pc excl hq (hTq t ht) hcop)
  rw [sum_const, nsmul_eq_mul] at hres
  have := card_midSet_le N b pc Y
  have := card_exSet_le N b Y hb hY
  linarith

/-! ### Lemma B -/

lemma isU1_odd {p : ℕ} (h : IsU1 p) : p ≠ 2 := by have := h.2.1; omega

/-- The restricted part of Lemma B for one class `t`. -/
def vResPart (N q t pB : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => x % q = t ∧ ∃ p ≤ pB, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

/-- The medium part of Lemma B (no class restriction). -/
def vMidSet (N pB Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ Y, p.Prime ∧ (IsU1 p ∧ pB < p) ∧ x % (p * p) ∈ sqRoots p)

/-- The Pell part of Lemma B. -/
def vPellSet (N Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)

lemma v_cover (N q pB Y : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (Icc 1 N).filter (fun x => Px x ∧ ¬ Squarefree (x * x + 1)) ⊆
      (Tset.biUnion (fun t => vResPart N q t pB) ∪ vMidSet N pB Y) ∪ vPellSet N Y := by
  intro x hx
  simp only [mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hPx, hsq⟩ := hx
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hU := isU1_of_sq_dvd hp hd (hstar x hPx)
  have hR : x % (p * p) ∈ sqRoots p := (mod_mem_sqRoots hp.pos x).mpr hd
  by_cases hpB : p ≤ pB
  · apply mem_union_left; apply mem_union_left
    simp only [mem_biUnion, vResPart, mem_filter, mem_Icc]
    exact ⟨x % q, hT x hPx, ⟨hx1, hxN⟩, rfl, p, hpB, hp, hU, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [vMidSet, mem_filter, mem_Icc]
    exact ⟨⟨hx1, hxN⟩, p, hpY, hp, ⟨hU, by omega⟩, hR⟩
  · apply mem_union_right
    simp only [vPellSet, mem_filter, mem_Icc]
    have h1 : p * p ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    have h2 : x * x + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hxN hxN) 1
    have h3 : p ≤ N + 1 := by
      by_contra hc; push Not at hc
      have : (N + 2) * (N + 2) ≤ p * p := Nat.mul_le_mul hc hc
      nlinarith
    refine ⟨⟨hx1, hxN⟩, p, ⟨by omega, h3⟩, ?_⟩
    rw [sq]; exact hd

/-- **Lemma B.** -/
theorem vCount_le (N q zB pB Y : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hcop : ∀ p, p.Prime → IsU1 p → Nat.Coprime q p)
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (vCount N Px : ℝ) ≤
      Tset.card * ((N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
        ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2)) +
      ∑ p ∈ midP pB Y (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
      (((N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  have hc := card_le_card (v_cover N q pB Y Tset Px hT hstar)
  have h1 := Finset.card_union_le (Tset.biUnion (fun t => vResPart N q t pB) ∪ vMidSet N pB Y)
    (vPellSet N Y)
  have h1' := Finset.card_union_le (Tset.biUnion (fun t => vResPart N q t pB)) (vMidSet N pB Y)
  have h2 := card_biUnion_le (s := Tset) (t := fun t => vResPart N q t pB)
  have hcN : vCount N Px ≤ ∑ t ∈ Tset, (vResPart N q t pB).card +
      (vMidSet N pB Y).card + (vPellSet N Y).card := by
    unfold vCount; omega
  have hcR : (vCount N Px : ℝ) ≤ ∑ t ∈ Tset, ((vResPart N q t pB).card : ℝ) +
      ((vMidSet N pB Y).card : ℝ) + ((vPellSet N Y).card : ℝ) := by exact_mod_cast hcN
  have hres : ∀ t ∈ Tset, ((vResPart N q t pB).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
        ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2) := by
    intro t ht
    have h := classSieve_le N q t zB pB 2 (fun p => sqRoots p) IsU1 hq (hTq t ht) (by norm_num)
      sqRoots_sub (fun p hp hU => card_sqRoots_le hp (isU1_odd hU)) hcop
    simp only [Nat.cast_ofNat, Nat.reduceAdd] at h
    exact h
  have hres' := sum_le_sum hres
  rw [sum_const, nsmul_eq_mul] at hres'
  have hmid : ((vMidSet N pB Y).card : ℝ) ≤
      ∑ p ∈ midP pB Y (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) := by
    have h := classSieve_le N 1 0 pB Y 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ pB < p)
      one_pos one_pos (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1)) (fun p _ _ => Nat.coprime_one_left p)
    have hsmall : smallP pB (fun p => IsU1 p ∧ pB < p) = ∅ := by
      rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
    rw [hsmall] at h
    simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat,
      Nat.mod_one, true_and] at h
    simpa [vMidSet] using h
  have hpell : ((vPellSet N Y).card : ℝ) ≤
      (((N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast pellTail_le N Y
  linarith

end Erdos848
