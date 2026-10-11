import Erdos848.Cases2
import Erdos848.CheckSound
import ErdosComp.Check2

/-!
# Soundness of the §10 checker, part 1: algebra and table lookups

* `altE_toFinset`: the truncated alternating sum `altE` over the primes of a list equals the
  checker's `altL` (elementary symmetric functions by recursion).
* `truncErr_const`: `truncErr` with constant weights is `terrL`.
* Bounds for the prime-range sums through a lookup function `lk` with `lk x = stAt x`.
-/

namespace Erdos848

open Finset ErdosComp

/-! ### Binomials and elementary symmetric functions -/

lemma chooseN_eq : ∀ n k, chooseN n k = n.choose k
  | _, 0 => by simp [chooseN]
  | 0, k + 1 => by simp [chooseN]
  | n + 1, k + 1 => by
    simp only [chooseN, chooseN_eq n k, chooseN_eq n (k + 1), Nat.choose_succ_succ]

lemma esym_eq (f : ℕ → ℚ) : ∀ (l : List ℕ), l.Nodup → ∀ j,
    ((esym f l j : ℚ) : ℝ) = ∑ T ∈ powersetCard j l.toFinset, ∏ p ∈ T, ((f p : ℚ) : ℝ)
  | [], _, 0 => by simp [esym]
  | [], _, j + 1 => by
    rw [List.toFinset_nil, powersetCard_eq_empty.mpr (by simp)]; simp [esym]
  | p :: l, _, 0 => by simp [esym]
  | p :: l, h, j + 1 => by
    have hnd := (List.nodup_cons.mp h)
    have hp : p ∉ l.toFinset := by simpa using hnd.1
    rw [List.toFinset_cons, powersetCard_succ_insert hp, sum_union, sum_image]
    · simp only [esym]
      push_cast
      rw [esym_eq f l hnd.2 (j + 1), esym_eq f l hnd.2 j, mul_sum]
      congr 1
      apply sum_congr rfl
      intro T hT
      have hpT : p ∉ T := fun hpT => hp ((mem_powersetCard.mp hT).1 hpT)
      rw [prod_insert hpT]
    · intro T₁ h₁ T₂ h₂ he
      have hp₁ : p ∉ T₁ := fun hpT => hp ((mem_powersetCard.mp h₁).1 hpT)
      have hp₂ : p ∉ T₂ := fun hpT => hp ((mem_powersetCard.mp h₂).1 hpT)
      rw [← erase_insert hp₁, ← erase_insert hp₂]
      exact congrArg (fun s => s.erase p) he
    · rw [disjoint_left]
      intro T h₁ h₂
      obtain ⟨T', _, rfl⟩ := mem_image.mp h₂
      exact hp ((mem_powersetCard.mp h₁).1 (mem_insert_self p T'))

lemma altL_eq (f : ℕ → ℚ) (l : List ℕ) : ∀ d,
    altL f l d = ∑ j ∈ range (d + 1), (-1) ^ j * esym f l j
  | 0 => by simp [altL]
  | d + 1 => by rw [altL, altL_eq f l d, sum_range_succ (n := d + 1)]

lemma altE_eq_sum (P : Finset ℕ) (v : ℕ → ℝ) (d : ℕ) :
    altE P v d = ∑ j ∈ range (d + 1), (-1) ^ j * ∑ T ∈ powersetCard j P, ∏ p ∈ T, v p := by
  unfold altE
  rw [← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (d + 1))
    (fun T hT => by simp only [mem_filter, mem_range] at hT ⊢; omega)]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  have hset : (P.powerset.filter (fun T => T.card ≤ d)).filter (fun T => T.card = j) =
      powersetCard j P := by
    ext T
    simp only [mem_filter, mem_powerset, mem_powersetCard, mem_range] at hj ⊢
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  rw [hset]
  apply sum_congr rfl
  intro T hT
  rw [(mem_powersetCard.mp hT).2]

/-- **`altE` is computed by `altL`.** -/
theorem altE_toFinset (f : ℕ → ℚ) (l : List ℕ) (hl : l.Nodup) (d : ℕ) :
    altE l.toFinset (fun p => ((f p : ℚ) : ℝ)) d = ((altL f l d : ℚ) : ℝ) := by
  rw [altE_eq_sum, altL_eq]
  push_cast
  apply sum_congr rfl
  intro j _
  rw [esym_eq f l hl j]

lemma terrL_eq (k : ℕ) (c : ℚ) : ∀ d,
    terrL k c d = ∑ j ∈ range d, (k.choose (j + 1) : ℚ) * c ^ (j + 1)
  | 0 => by simp [terrL]
  | d + 1 => by rw [terrL, terrL_eq k c d, sum_range_succ, chooseN_eq]

/-- **`truncErr` with constant weights is computed by `terrL`.** -/
theorem truncErr_const (P : Finset ℕ) (c : ℚ) (d : ℕ) :
    truncErr P (fun _ => ((c : ℚ) : ℝ)) d = ((terrL P.card c d : ℚ) : ℝ) := by
  unfold truncErr
  rw [← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (d + 1))
    (fun T hT => by simp only [mem_filter, mem_range] at hT ⊢; omega)]
  rw [terrL_eq, sum_range_succ']
  have h0 : ((P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d)).filter
      (fun T => T.card = 0)) = ∅ := by
    ext T
    simp only [mem_filter, mem_powerset, notMem_empty, iff_false, not_and]
    rintro ⟨_, hne, _⟩ h0
    exact hne.ne_empty (card_eq_zero.mp h0)
  rw [h0, sum_empty, add_zero]
  push_cast
  apply sum_congr rfl
  intro j hj
  have hset : (P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d)).filter
      (fun T => T.card = j + 1) = powersetCard (j + 1) P := by
    ext T
    simp only [mem_filter, mem_powerset, mem_powersetCard, mem_range] at hj ⊢
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_, by omega⟩, h3⟩
      exact card_pos.mp (by omega)
  rw [hset]
  have : ∀ T ∈ powersetCard (j + 1) P, ∏ _p ∈ T, ((c : ℚ) : ℝ) = ((c : ℚ) : ℝ) ^ (j + 1) := by
    intro T hT
    rw [prod_const, (mem_powersetCard.mp hT).2]
  rw [sum_congr rfl this, sum_const, card_powersetCard, nsmul_eq_mul]

/-! ### Lists of primes -/

lemma primesEx_toFinset (z : ℕ) (excl : Finset ℕ) (exclL : List ℕ) (hex : ∀ p, p ∈ excl ↔ p ∈ exclL) :
    (primesEx z exclL).toFinset = smallP z (· ∉ excl) := by
  ext p
  simp only [primesEx, List.mem_toFinset, List.mem_filter, List.mem_range, smallP, mem_filter,
    mem_range, Bool.and_eq_true, isPrimeB_iff, Bool.not_eq_true', List.contains_eq_any_beq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have := (hex p).mp h
    simp only [List.any_eq_false, beq_iff_eq] at h3
    exact h3 p this rfl
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    simp only [List.any_eq_false, beq_iff_eq]
    intro y hy hpy
    subst hpy
    exact h3 ((hex _).mpr hy)

lemma primesEx_nodup (z : ℕ) (exclL : List ℕ) : (primesEx z exclL).Nodup :=
  (List.nodup_range).filter _

lemma u1UpTo_toFinset (z : ℕ) : (u1UpTo z).toFinset = smallP z IsU1 := by
  ext p
  simp only [u1UpTo, List.mem_toFinset, List.mem_filter, List.mem_range, smallP, mem_filter,
    mem_range, isU1B_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.1, h2⟩
  · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩

lemma u1UpTo_nodup (z : ℕ) : (u1UpTo z).Nodup := (List.nodup_range).filter _

lemma u1UpTo_erase_toFinset (z p : ℕ) : ((u1UpTo z).erase p).toFinset = Uer z p := by
  rw [List.Nodup.erase_eq_filter (u1UpTo_nodup z), Uer, ← u1UpTo_toFinset]
  ext x
  simp only [List.mem_toFinset, List.mem_filter, mem_erase, bne_iff_ne, ne_eq]
  tauto

lemma u1UpTo_erase_nodup (z p : ℕ) : ((u1UpTo z).erase p).Nodup := (u1UpTo_nodup z).erase p

/-! ### Table lookups -/

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

lemma tab3_valid (lo hi : ℕ) : ∀ e ∈ tab3 lk lo hi, e.2 = stAt e.1 := by
  intro e he
  simp only [tab3, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact hlk _

lemma primeSumK (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((S2Pk lk z w : ℚ) : ℝ) + ((CPk lk z w : ℚ) : ℝ) :=
  primeSum_le (tab3_valid hlk z w) z w Q a ha

lemma u1SumK (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p)
    (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((S2Uk lk z w : ℚ) : ℝ) + ((CUk lk z w : ℚ) : ℝ) :=
  u1Sum_le (tab3_valid hlk z w) z w Q hQ a ha

lemma S2PK_le (lo hi : ℕ) : S2 (primesIn lo hi) ≤ ((S2Pk lk lo hi : ℚ) : ℝ) :=
  S2_primesIn_le (tab3_valid hlk lo hi) lo hi

lemma S2UK_le (lo hi : ℕ) : S2 (u1In lo hi) ≤ ((S2Uk lk lo hi : ℚ) : ℝ) :=
  S2_u1In_le (tab3_valid hlk lo hi) lo hi

lemma CPK_le (lo hi : ℕ) : ((primesIn lo hi).card : ℝ) ≤ ((CPk lk lo hi : ℚ) : ℝ) :=
  card_primesIn_le (tab3_valid hlk lo hi) lo hi

lemma CUK_le (lo hi : ℕ) : ((u1In lo hi).card : ℝ) ≤ ((CUk lk lo hi : ℚ) : ℝ) :=
  card_u1In_le (tab3_valid hlk lo hi) lo hi

lemma S2PK_nonneg (lo hi : ℕ) : (0 : ℝ) ≤ ((S2Pk lk lo hi : ℚ) : ℝ) :=
  (S2_nonneg _).trans (S2PK_le hlk lo hi)

lemma S2UK_nonneg (lo hi : ℕ) : (0 : ℝ) ≤ ((S2Uk lk lo hi : ℚ) : ℝ) :=
  (S2_nonneg _).trans (S2UK_le hlk lo hi)

lemma CPK_nonneg (lo hi : ℕ) : (0 : ℝ) ≤ ((CPk lk lo hi : ℚ) : ℝ) :=
  (Nat.cast_nonneg _).trans (CPK_le hlk lo hi)

lemma CUK_nonneg (lo hi : ℕ) : (0 : ℝ) ≤ ((CUk lk lo hi : ℚ) : ℝ) :=
  (Nat.cast_nonneg _).trans (CUK_le hlk lo hi)

end

end Erdos848
