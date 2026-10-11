import Mathlib

/-!
# Phase 5: an elementary bound for the Pell tail of Lemma B

`pell_growth`: if `x₁ < x₂` and `xᵢ² + 1 = m yᵢ²`, then `3 x₁ ≤ x₂`.
`card_pell_le`: for fixed `m`, at most `Nat.log 3 N + 1` integers `x ∈ [1,N]` satisfy
`x² + 1 = m y²` for some `y`.

Proof idea (integers only): with `a = m y₁ y₂ − x₁ x₂` and `c = x₂ y₁ − x₁ y₂` one has
`a² − m c² = 1` and `x₂ = a x₁ + m c y₁`; then `c ≥ 1`, `a ≥ 2` and `m y₁ ≥ x₁` give `x₂ ≥ 3 x₁`.
This replaces the unit-group argument of `proof.md` §3 (the certificates were re-checked with the
resulting weaker constant `1/ln 3`).
-/

namespace Erdos848

open Finset

theorem pell_growth {m x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ ^ 2 + 1 = m * y₁ ^ 2)
    (h₂ : x₂ ^ 2 + 1 = m * y₂ ^ 2) (hlt : x₁ < x₂) : 3 * x₁ ≤ x₂ := by
  have H₁ : (x₁ : ℤ) ^ 2 + 1 = m * (y₁ : ℤ) ^ 2 := by exact_mod_cast h₁
  have H₂ : (x₂ : ℤ) ^ 2 + 1 = m * (y₂ : ℤ) ^ 2 := by exact_mod_cast h₂
  have hlt' : (x₁ : ℤ) < x₂ := by exact_mod_cast hlt
  have hx₁ : (0 : ℤ) ≤ x₁ := by positivity
  have hx₂ : (0 : ℤ) ≤ x₂ := by positivity
  have hy₁ : (0 : ℤ) ≤ y₁ := by positivity
  have hy₂ : (0 : ℤ) ≤ y₂ := by positivity
  have hm : (0 : ℤ) ≤ m := by positivity
  set a : ℤ := m * y₁ * y₂ - x₁ * x₂ with ha
  set c : ℤ := x₂ * y₁ - x₁ * y₂ with hc
  have hnorm : a ^ 2 - m * c ^ 2 = 1 := by
    rw [ha, hc]; linear_combination ((x₂ : ℤ) ^ 2 - m * (y₂ : ℤ) ^ 2) * H₁ - H₂
  have hx₂eq : (x₂ : ℤ) = a * x₁ + m * c * y₁ := by
    rw [ha, hc]; linear_combination (x₂ : ℤ) * H₁
  -- c ≥ 1
  have hsq : ((x₁ : ℤ) * y₂) ^ 2 < ((x₂ : ℤ) * y₁) ^ 2 := by
    have hyy : (y₁ : ℤ) ^ 2 < (y₂ : ℤ) ^ 2 := by nlinarith
    have : ((x₂ : ℤ) * y₁) ^ 2 - ((x₁ : ℤ) * y₂) ^ 2 = (y₂ : ℤ) ^ 2 - (y₁ : ℤ) ^ 2 := by
      linear_combination (y₁ : ℤ) ^ 2 * H₂ - (y₂ : ℤ) ^ 2 * H₁
    linarith
  have hc1 : 1 ≤ c := by
    have : (x₁ : ℤ) * y₂ < x₂ * y₁ :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [hc]; linarith
  -- a ≥ 2
  have ha1 : 1 ≤ a := by
    have hsq' : ((x₁ : ℤ) * x₂) ^ 2 < ((m : ℤ) * y₁ * y₂) ^ 2 := by
      have : ((m : ℤ) * y₁ * y₂) ^ 2 = ((x₁ : ℤ) ^ 2 + 1) * ((x₂ : ℤ) ^ 2 + 1) := by
        rw [H₁, H₂]; ring
      rw [this]; nlinarith [sq_nonneg ((x₁ : ℤ)), sq_nonneg ((x₂ : ℤ))]
    have : (x₁ : ℤ) * x₂ < m * y₁ * y₂ := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq'
    rw [ha]; linarith
  have hm1 : (1 : ℤ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp at h₁
    · exact_mod_cast hpos
  have ha2 : 2 ≤ a := by
    by_contra hlt2
    have : a = 1 := by omega
    rw [this] at hnorm
    nlinarith
  -- m y₁ ≥ x₁
  have hmy : (x₁ : ℤ) ≤ m * y₁ := by
    have : ((x₁ : ℤ)) ^ 2 < ((m : ℤ) * y₁) ^ 2 := by
      have : (m : ℤ) * y₁ ^ 2 ≤ (m * y₁) ^ 2 := by nlinarith
      nlinarith
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) this).le
  have : (3 : ℤ) * x₁ ≤ x₂ := by
    rw [hx₂eq]; nlinarith
  exact_mod_cast this

/-- For fixed `m`, the integers `x ∈ [1,N]` with `x² + 1 = m y²` (some `y`). -/
def pellSet (m N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ y ∈ range (x + 1), x ^ 2 + 1 = m * y ^ 2)

lemma mem_pellSet {m N x : ℕ} :
    x ∈ pellSet m N ↔ 1 ≤ x ∧ x ≤ N ∧ ∃ y, x ^ 2 + 1 = m * y ^ 2 := by
  unfold pellSet
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, y, -, hy⟩; exact ⟨h1, h2, y, hy⟩
  · rintro ⟨h1, h2, y, hy⟩
    refine ⟨⟨h1, h2⟩, y, ?_, hy⟩
    -- y ≤ x since m ≥ 1 and m y² = x² + 1 ≤ (x+1)², so y ≤ x + 1 - 1
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; simp at hy
    · by_contra hge
      push Not at hge
      have : (x + 1) ^ 2 ≤ m * y ^ 2 := by
        calc (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hge 2
          _ ≤ m * y ^ 2 := Nat.le_mul_of_pos_left _ hm
      nlinarith

/-- At most one element of `pellSet m N` lies in `(N/3, N]`. -/
lemma card_pellSet_le (m : ℕ) : ∀ N, (pellSet m N).card ≤ Nat.log 3 N + 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 3 with hN | hN
    · -- N < 3: the set has at most N ≤ 2 ... use a direct bound: elements x ≤ 2 with growth
      -- any two elements x < x' satisfy 3x ≤ x', impossible below 3 unless the smaller is 0
      have : (pellSet m N).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_pellSet] at hx hx'
        obtain ⟨hx1, hxN, y, hy⟩ := hx
        obtain ⟨hx1', hxN', y', hy'⟩ := hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have := pell_growth hy hy' hlt; omega
        · have := pell_growth hy' hy hlt; omega
      omega
    · -- split off (N/3, N]
      have hsplit : pellSet m N ⊆ pellSet m (N / 3) ∪ (pellSet m N).filter (fun x => N / 3 < x) := by
        intro x hx
        by_cases h : N / 3 < x
        · exact mem_union_right _ (mem_filter.mpr ⟨hx, h⟩)
        · apply mem_union_left
          rw [mem_pellSet] at hx ⊢
          exact ⟨hx.1, by omega, hx.2.2⟩
      have hone : ((pellSet m N).filter (fun x => N / 3 < x)).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_filter, mem_pellSet] at hx hx'
        obtain ⟨⟨hx1, hxN, y, hy⟩, hxl⟩ := hx
        obtain ⟨⟨hx1', hxN', y', hy'⟩, hxl'⟩ := hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have := pell_growth hy hy' hlt; omega
        · have := pell_growth hy' hy hlt; omega
      have hih := ih (N / 3) (by omega)
      have hlog : Nat.log 3 (N / 3) + 1 = Nat.log 3 N := by
        rw [Nat.log_div_base]
        have : 1 ≤ Nat.log 3 N := Nat.log_pos (by norm_num) hN
        omega
      calc (pellSet m N).card ≤ (pellSet m (N / 3)).card + ((pellSet m N).filter (fun x => N / 3 < x)).card :=
            (card_le_card hsplit).trans (card_union_le _ _)
        _ ≤ Nat.log 3 (N / 3) + 1 + 1 := by omega
        _ = Nat.log 3 N + 1 := by omega

/-- **Pell tail of Lemma B.** The integers `n ∈ [1,N]` such that `n² + 1` is divisible by `p²`
for some `p > Y` number at most `⌊(N²+1)/(Y+1)²⌋ · (log₃ N + 1)`. -/
theorem pellTail_le (N Y : ℕ) :
    ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card ≤
      ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) := by
  set M := (N ^ 2 + 1) / (Y + 1) ^ 2
  calc ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card
      ≤ ((Icc 1 M).biUnion (fun m => pellSet m N)).card := by
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_Icc] at hn
        obtain ⟨⟨hn1, hnN⟩, p, ⟨hp1, -⟩, hd⟩ := hn
        obtain ⟨m, hm⟩ := hd
        have hp0 : 0 < p := by omega
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | h
          · subst h0; simp at hm
          · exact h
        have hmM : m ≤ M := by
          apply (Nat.le_div_iff_mul_le (by positivity)).mpr
          have h1 : (Y + 1) ^ 2 ≤ p * p := by nlinarith
          have h2 : n ^ 2 + 1 ≤ N ^ 2 + 1 := by nlinarith
          calc m * (Y + 1) ^ 2 ≤ m * (p * p) := Nat.mul_le_mul_left _ h1
            _ = n ^ 2 + 1 := by rw [hm]; ring
            _ ≤ N ^ 2 + 1 := h2
        simp only [mem_biUnion, mem_Icc]
        refine ⟨m, ⟨hm1, hmM⟩, mem_pellSet.mpr ⟨hn1, hnN, p, ?_⟩⟩
        rw [hm]; ring
    _ ≤ ∑ m ∈ Icc 1 M, (pellSet m N).card := card_biUnion_le
    _ ≤ ∑ _m ∈ Icc 1 M, (Nat.log 3 N + 1) := sum_le_sum (fun m _ => card_pellSet_le m N)
    _ = M * (Nat.log 3 N + 1) := by simp

end Erdos848
