import Erdos848.Sieve
import Erdos848.PrimeBound
import ErdosComp

/-!
# Phase 7 (part 1): a verified prime table

`stAt n` records, for the integers in `[1, n]`, the number of primes, the number of U1 primes,
and the sums `∑ ⌈K/p²⌉` over primes and over U1 primes (`K = 10³⁰`).  It is defined by the
obvious recursion, so its specification (`stAt_spec`) is proved by induction; the fast evaluation
`evalPts` (one pass, recording the state at requested points) is proved to agree with it.

From these we get explicit rational upper bounds for
`∑_{p ∈ (lo, hi]} 1/p²` and `#{p ∈ (lo, hi]}` (primes, or U1 primes); above `PM = 2·10⁷` they use
`∑_{n > PM} 1/n² ≤ 1/PM` and Chebyshev's bound `π(x) ≤ √x + 2 log 4 · x / log x`.
-/

namespace Erdos848

open Finset

open ErdosComp

/-! ### Primality test: every prime is accepted -/

lemma minFacAux_prime {n : ℕ} (hn : n.Prime) : ∀ f k, 2 ≤ k → ErdosComp.minFacAux n k f = n := by
  intro f
  induction f with
  | zero => intro k _; rfl
  | succ f ih =>
    intro k hk
    simp only [ErdosComp.minFacAux]
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : k ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h2)
      rcases hn.eq_one_or_self_of_dvd k hdvd with h | h
      · omega
      · subst h; push Not at h1; nlinarith
    · exact ih (k + 2) (by omega)

lemma isPrimeB_of_prime {n : ℕ} (hn : n.Prime) : isPrimeB n = true := by
  unfold isPrimeB
  have h2 := hn.two_le
  have hlt : ¬ n < 2 := by omega
  simp only [hlt, ↓reduceIte]
  split_ifs with he
  · have : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using he)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hn).mp this
    simp [this]
  · simp [minFacAux_prime hn n 3 (by norm_num)]

lemma isU1B_of_isU1 {n : ℕ} (hn : IsU1 n) : isU1B n = true := by
  unfold isU1B
  simp [isPrimeB_of_prime hn.1, hn.2.1, hn.2.2]

/-! ### The state -/

/-- Accepted numbers (a superset of the primes) in `(lo, hi]`. -/
def accP (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter (fun n => isPrimeB n = true)

/-- Accepted U1 numbers in `(lo, hi]`. -/
def accU (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter (fun n => isU1B n = true)

lemma Ioc_succ (n : ℕ) : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
  ext x; simp only [mem_Ioc, mem_insert]; omega

lemma isPrimeB_of_isU1B {n : ℕ} (h : isU1B n = true) : isPrimeB n = true := by
  unfold isU1B at h; simp only [Bool.and_eq_true] at h; exact h.1.1

theorem stAt_spec (n : ℕ) :
    (stAt n).cp = (accP 0 n).card ∧ (stAt n).cu = (accU 0 n).card ∧
    (stAt n).fp = ∑ p ∈ accP 0 n, ceilK p ∧ (stAt n).fu = ∑ p ∈ accU 0 n, ceilK p := by
  induction n with
  | zero => simp [stAt, accP, accU]
  | succ n ih =>
    have hnot : n + 1 ∉ Ioc 0 n := by simp
    have hP : accP 0 (n + 1) = if isPrimeB (n + 1) = true then insert (n + 1) (accP 0 n)
        else accP 0 n := by
      unfold accP; rw [Ioc_succ, filter_insert]
    have hU : accU 0 (n + 1) = if isU1B (n + 1) = true then insert (n + 1) (accU 0 n)
        else accU 0 n := by
      unfold accU; rw [Ioc_succ, filter_insert]
    have hnP : n + 1 ∉ accP 0 n := fun h => hnot (mem_filter.mp h).1
    have hnU : n + 1 ∉ accU 0 n := fun h => hnot (mem_filter.mp h).1
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [stAt, stepSt]
    cases hp : isPrimeB (n + 1) with
    | true =>
      cases hu : isU1B (n + 1) with
      | true =>
        simp only [ite_true, hP, hp, hU, hu, card_insert_of_notMem hnP,
          card_insert_of_notMem hnU, sum_insert hnP, sum_insert hnU]
        refine ⟨by rw [h1], by rw [h2], by rw [h3]; ring, by rw [h4]; ring⟩
      | false =>
        simp only [ite_true, Bool.false_eq_true, ite_false, hP, hp, hU, hu,
          card_insert_of_notMem hnP, sum_insert hnP]
        refine ⟨by rw [h1], h2, by rw [h3]; ring, h4⟩
    | false =>
      have hu : isU1B (n + 1) = false := by
        cases h : isU1B (n + 1)
        · rfl
        · rw [isPrimeB_of_isU1B h] at hp; exact absurd hp (by simp)
      simp only [Bool.false_eq_true, ite_false, hP, hp, hU, hu]
      exact ⟨h1, h2, h3, h4⟩

/-! ### Fast evaluation -/

lemma advance_stAt : ∀ k n, advance k n (stAt n) = stAt (n + k) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    show advance k (n + 1) (stepSt (n + 1) (stAt n)) = stAt (n + (k + 1))
    rw [show stepSt (n + 1) (stAt n) = stAt (n + 1) from rfl, ih, Nat.add_right_comm, add_assoc]

lemma evalPts_sound : ∀ xs n, ∀ e ∈ evalPts xs n (stAt n), e.2 = stAt e.1 := by
  intro xs
  induction xs with
  | nil => intro n e he; simp [evalPts] at he
  | cons x xs ih =>
    intro n e he
    simp only [evalPts, List.mem_cons] at he
    rw [advance_stAt] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ e he

lemma lookD_eq {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1) (x : ℕ) :
    lookD tab x = stAt x := by
  unfold lookD
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hx := List.find?_some he
    simp only [beq_iff_eq] at hx
    rw [htab e hmem, hx]
  · rfl

/-! ### Bounds from the table -/

/-- `∑_{p ∈ P} 1/p²`. -/
noncomputable def S2 (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1 / ((p : ℝ) * p)

/-- Primes in `(lo, hi]`. -/
def primesIn (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter Nat.Prime

/-- U1 primes in `(lo, hi]`. -/
def u1In (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter IsU1

lemma S2_nonneg (P : Finset ℕ) : 0 ≤ S2 P := sum_nonneg (fun p _ => by positivity)

lemma S2_mono {P Q : Finset ℕ} (h : P ⊆ Q) : S2 P ≤ S2 Q :=
  sum_le_sum_of_subset_of_nonneg h (fun p _ _ => by positivity)

lemma primesIn_sub_accP (lo hi : ℕ) : primesIn lo hi ⊆ accP lo hi := fun p hp => by
  simp only [primesIn, accP, mem_filter] at hp ⊢; exact ⟨hp.1, isPrimeB_of_prime hp.2⟩

lemma u1In_sub_accU (lo hi : ℕ) : u1In lo hi ⊆ accU lo hi := fun p hp => by
  simp only [u1In, accU, mem_filter] at hp ⊢; exact ⟨hp.1, isU1B_of_isU1 hp.2⟩

lemma Ioc_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Ioc a c = Ioc a b ∪ Ioc b c := by
  ext x; simp only [mem_Ioc, mem_union]; omega

lemma Ioc_disj (a b c : ℕ) : Disjoint (Ioc a b) (Ioc b c) := by
  rw [disjoint_left]; intro x h1 h2; simp only [mem_Ioc] at h1 h2; omega

lemma filter_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → Bool) :
    (Ioc a c).filter (fun n => f n = true) =
      (Ioc a b).filter (fun n => f n = true) ∪ (Ioc b c).filter (fun n => f n = true) := by
  rw [Ioc_split hab hbc, filter_union]

lemma filter_disj (a b c : ℕ) (f : ℕ → Bool) :
    Disjoint ((Ioc a b).filter (fun n => f n = true)) ((Ioc b c).filter (fun n => f n = true)) :=
  disjoint_filter_filter (Ioc_disj a b c)

lemma inv_sq_le_ceilK {p : ℕ} (hp : 1 ≤ p) : 1 / ((p : ℝ) * p) ≤ (ceilK p : ℝ) / KS := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have h : KS ≤ ceilK p * (p * p) := by
    unfold ceilK
    have h1 := Nat.lt_div_mul_add (a := KS + p * p - 1) hpp
    have hK : 1 ≤ KS := by unfold KS; norm_num
    generalize (KS + p * p - 1) / (p * p) * (p * p) = y at h1 ⊢
    omega
  have hR : (KS : ℝ) ≤ (ceilK p : ℝ) * ((p : ℝ) * p) := by exact_mod_cast h
  have hK : (0 : ℝ) < KS := by unfold KS; positivity
  have hp' : (0 : ℝ) < (p : ℝ) * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  rw [div_le_div_iff₀ hp' hK]; linarith

/-- The table part of the reciprocal-square sum. -/
lemma S2_accP_le (lo hi : ℕ) :
    S2 (accP lo hi) ≤ (((stAt hi).fp - (stAt lo).fp : ℕ) : ℝ) / KS := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isPrimeB
    have hdisj := filter_disj 0 lo hi isPrimeB
    have hfp : (stAt hi).fp = (stAt lo).fp + ∑ p ∈ accP lo hi, ceilK p := by
      rw [(stAt_spec hi).2.2.1, (stAt_spec lo).2.2.1]
      unfold accP; rw [hsplit, sum_union hdisj]
    rw [hfp, Nat.add_sub_cancel_left, Nat.cast_sum, sum_div]
    unfold S2
    apply sum_le_sum; intro p hp
    exact inv_sq_le_ceilK (by simp only [accP, mem_filter, mem_Ioc] at hp; omega)
  · have : accP lo hi = ∅ := by
      unfold accP; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; unfold S2; simp only [sum_empty]; positivity

lemma S2_accU_le (lo hi : ℕ) :
    S2 (accU lo hi) ≤ (((stAt hi).fu - (stAt lo).fu : ℕ) : ℝ) / KS := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isU1B
    have hdisj := filter_disj 0 lo hi isU1B
    have hfu : (stAt hi).fu = (stAt lo).fu + ∑ p ∈ accU lo hi, ceilK p := by
      rw [(stAt_spec hi).2.2.2, (stAt_spec lo).2.2.2]
      unfold accU; rw [hsplit, sum_union hdisj]
    rw [hfu, Nat.add_sub_cancel_left, Nat.cast_sum, sum_div]
    unfold S2
    apply sum_le_sum; intro p hp
    exact inv_sq_le_ceilK (by simp only [accU, mem_filter, mem_Ioc] at hp; omega)
  · have : accU lo hi = ∅ := by
      unfold accU; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; unfold S2; simp only [sum_empty]; positivity

lemma card_accP_le (lo hi : ℕ) : (accP lo hi).card ≤ (stAt hi).cp - (stAt lo).cp := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isPrimeB
    have hdisj := filter_disj 0 lo hi isPrimeB
    have : (stAt hi).cp = (stAt lo).cp + (accP lo hi).card := by
      rw [(stAt_spec hi).1, (stAt_spec lo).1]; unfold accP; rw [hsplit, card_union_of_disjoint hdisj]
    omega
  · have : accP lo hi = ∅ := by
      unfold accP; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; simp

lemma card_accU_le (lo hi : ℕ) : (accU lo hi).card ≤ (stAt hi).cu - (stAt lo).cu := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isU1B
    have hdisj := filter_disj 0 lo hi isU1B
    have : (stAt hi).cu = (stAt lo).cu + (accU lo hi).card := by
      rw [(stAt_spec hi).2.1, (stAt_spec lo).2.1]; unfold accU; rw [hsplit, card_union_of_disjoint hdisj]
    omega
  · have : accU lo hi = ∅ := by
      unfold accU; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; simp

/-- `∑_{n ∈ (a, b]} 1/n² ≤ 1/a`. -/
lemma sum_inv_sq_Ioc_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ n ∈ Ioc a b, 1 / ((n : ℝ) * n) ≤ 1 / a - 1 / max a b := by
  induction b with
  | zero => rw [show Ioc a 0 = ∅ by ext; simp]; simp
  | succ b ih =>
    by_cases hab : b < a
    · have : Ioc a (b + 1) = ∅ := by
        ext x; simp only [mem_Ioc, notMem_empty, iff_false]; omega
      rw [this, max_eq_left (by omega)]; simp
    · push Not at hab
      have hins : Ioc a (b + 1) = insert (b + 1) (Ioc a b) := by
        ext x; simp only [mem_Ioc, mem_insert]; omega
      rw [hins, sum_insert (by simp), max_eq_right (by omega)]
      rw [max_eq_right hab] at ih
      have hb : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      have key : 1 / (((b + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

lemma S2_tail_le {a : ℕ} (ha : 1 ≤ a) (P : Finset ℕ) (b : ℕ) (hP : P ⊆ Ioc a b) :
    S2 P ≤ 1 / a := by
  have h1 := sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => by positivity : ∀ p ∈ Ioc a b,
    p ∉ P → (0 : ℝ) ≤ 1 / ((p : ℝ) * p))
  have h2 := sum_inv_sq_Ioc_le ha b
  have : (0 : ℝ) ≤ 1 / max (a : ℝ) b := by positivity
  unfold S2; push_cast at h2; linarith

/-! ### Chebyshev above the table -/

lemma logLo_le_log (x : ℕ) (hx : 1 ≤ x) : ((logLo x : ℚ) : ℝ) ≤ Real.log x := by
  unfold logLo log2Lo
  set k := Nat.log2 x
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hsplit : Real.log x = k * Real.log 2 + Real.log (x / 2 ^ k) := by
    rw [Real.log_div hxR.ne' h2k.ne', Real.log_pow]; ring
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hxR h2k)
  have hl2 := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := by positivity
  push_cast
  rw [hsplit]
  rw [inv_div] at hlog
  nlinarith

lemma sqrt_le_sqrtUp (x : ℕ) : Real.sqrt x ≤ ((sqrtUp x : ℚ) : ℝ) := by
  unfold sqrtUp
  set s : ℕ := 2 ^ (Nat.log2 x / 2)
  have hs : (0 : ℝ) < s := by positivity
  push_cast
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity)
  have : (Real.sqrt x - s) ^ 2 ≥ 0 := sq_nonneg _
  rw [div_add' _ _ _ hs.ne', le_div_iff₀ (by norm_num), le_div_iff₀ hs]
  nlinarith

lemma card_primesIn_le_cheb (lo x : ℕ) (hx : 2 ≤ x) :
    ((primesIn lo x).card : ℝ) ≤ ((chebUp x : ℚ) : ℝ) := by
  have hsub : primesIn lo x ⊆ Nat.primesLE x := by
    intro p hp; simp only [primesIn, mem_filter, mem_Ioc] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.1.2, hp.2⟩
  have h1 : ((primesIn lo x).card : ℝ) ≤ (Nat.primesLE x).card := by
    exact_mod_cast card_le_card hsub
  unfold chebUp
  split_ifs with hpos
  · have hc := card_primesLE_le x hx
    have hlo := logLo_le_log x (by omega)
    have hposR : (0 : ℝ) < ((logLo x : ℚ) : ℝ) := by exact_mod_cast hpos
    have hsq := sqrt_le_sqrtUp x
    have hl4 : Real.log 4 ≤ 13863 / 10000 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    have hxR : (0 : ℝ) ≤ x := by positivity
    have hlogpos : 0 < Real.log x := lt_of_lt_of_le hposR hlo
    have h3 : 2 * Real.log 4 * x / Real.log x ≤ 2 * (13863 / 10000) * x / ((logLo x : ℚ) : ℝ) := by
      have hl4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      calc 2 * Real.log 4 * x / Real.log x ≤ 2 * (13863 / 10000) * x / Real.log x := by
            gcongr
        _ ≤ 2 * (13863 / 10000) * x / ((logLo x : ℚ) : ℝ) := by
            apply div_le_div_of_nonneg_left (by positivity) hposR hlo
    push_cast
    linarith
  · have : (Nat.primesLE x).card ≤ x := by
      calc (Nat.primesLE x).card ≤ (Ioc 0 x).card := by
            apply card_le_card; intro p hp
            have := Nat.mem_primesLE.mp hp
            simp only [mem_Ioc]; exact ⟨this.2.pos, this.1⟩
        _ = x := by simp
    push_cast
    exact h1.trans (by exact_mod_cast this)

/-! ### The four bounds used by the checker -/

lemma PM_pos : (1 : ℕ) ≤ PM := by unfold PM; norm_num

lemma S2_union_le (A B : Finset ℕ) : S2 (A ∪ B) ≤ S2 A + S2 B := by
  unfold S2
  have := sum_union_inter (s₁ := A) (s₂ := B) (f := fun p => 1 / ((p : ℝ) * p))
  have : 0 ≤ ∑ p ∈ A ∩ B, 1 / ((p : ℝ) * p) := sum_nonneg (fun p _ => by positivity)
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

theorem S2_primesIn_le (lo hi : ℕ) : S2 (primesIn lo hi) ≤ ((s2P tab lo hi : ℚ) : ℝ) := by
  unfold s2P
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact (S2_mono (primesIn_sub_accP lo hi)).trans (S2_accP_le lo hi)
  · push_cast
    have hsub : primesIn lo hi ⊆ accP lo PM ∪ primesIn PM hi := by
      intro p hp
      simp only [primesIn, accP, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isPrimeB_of_prime hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have e1 := S2_mono hsub
    have e2 : S2 (accP lo PM ∪ primesIn PM hi) ≤ S2 (accP lo PM) + S2 (primesIn PM hi) := by
      exact S2_union_le _ _
    have e3 := S2_accP_le lo PM
    have e4 := S2_tail_le PM_pos (primesIn PM hi) hi (filter_subset _ _)
    linarith
  · push_cast
    have := S2_tail_le (show 1 ≤ lo by have := PM_pos; unfold PM at *; omega) (primesIn lo hi) hi
      (filter_subset _ _)
    exact this

theorem S2_u1In_le (lo hi : ℕ) : S2 (u1In lo hi) ≤ ((s2U tab lo hi : ℚ) : ℝ) := by
  unfold s2U
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact (S2_mono (u1In_sub_accU lo hi)).trans (S2_accU_le lo hi)
  · push_cast
    have hsub : u1In lo hi ⊆ accU lo PM ∪ u1In PM hi := by
      intro p hp
      simp only [u1In, accU, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isU1B_of_isU1 hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have e1 := S2_mono hsub
    have e2 : S2 (accU lo PM ∪ u1In PM hi) ≤ S2 (accU lo PM) + S2 (u1In PM hi) := by
      exact S2_union_le _ _
    have e3 := S2_accU_le lo PM
    have e4 := S2_tail_le PM_pos (u1In PM hi) hi (filter_subset _ _)
    linarith
  · push_cast
    exact S2_tail_le (show 1 ≤ lo by have := PM_pos; unfold PM at *; omega) (u1In lo hi) hi (filter_subset _ _)

theorem card_primesIn_le (lo hi : ℕ) : ((primesIn lo hi).card : ℝ) ≤ ((cP tab lo hi : ℚ) : ℝ) := by
  unfold cP
  simp only [lookD_eq htab]
  split_ifs with h1
  · push_cast
    exact_mod_cast (card_le_card (primesIn_sub_accP lo hi)).trans (card_accP_le lo hi)
  · exact card_primesIn_le_cheb lo hi (by unfold PM at h1; omega)

theorem card_u1In_le (lo hi : ℕ) : ((u1In lo hi).card : ℝ) ≤ ((cU tab lo hi : ℚ) : ℝ) := by
  unfold cU
  simp only [lookD_eq htab]
  split_ifs with h1
  · push_cast
    exact_mod_cast (card_le_card (u1In_sub_accU lo hi)).trans (card_accU_le lo hi)
  · have hsub : u1In lo hi ⊆ primesIn lo hi := fun p hp => by
      simp only [u1In, primesIn, mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
    exact (by exact_mod_cast card_le_card hsub : ((u1In lo hi).card : ℝ) ≤ (primesIn lo hi).card).trans
      (card_primesIn_le_cheb lo hi (by unfold PM at h1; omega))

end

end Erdos848
