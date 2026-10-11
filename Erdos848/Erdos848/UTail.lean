import Erdos848.PellTail
import Erdos848.Sieve

/-!
# Phase 9.5: the U1 tail (Lemmas H and P of `proof.md` §10.2)

* `pell_growth2`: consecutive solutions of `x² + 1 = m y²` satisfy `x₂² ≥ 4 m x₁²`.
* `card_chain_le`: a set whose squares grow by a factor `G ≥ 2` between consecutive elements,
  all squares in `[X₂, T]`, has at most `chainCnt G X₂ (T+1) T` elements.
* `pellWin_le` (Lemma P): `#{n ≤ N : ∃ p > Y, p² ∣ n² + 1}` is at most
  `∑_{m ≤ M, m admissible} chainCnt (max 9 (4m)) (m (Y+1)² - 1) …`.
* `card_sq_dvd_le_two`, `card_sq_dvd_le_one` (Lemma H).
-/

namespace Erdos848

open Finset

/-- Consecutive solutions: `x₂² ≥ 4 m x₁²`. -/
theorem pell_growth2 {m x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ ^ 2 + 1 = m * y₁ ^ 2)
    (h₂ : x₂ ^ 2 + 1 = m * y₂ ^ 2) (hlt : x₁ < x₂) : 4 * m * x₁ ^ 2 ≤ x₂ ^ 2 := by
  have H₁ : (x₁ : ℤ) ^ 2 + 1 = m * (y₁ : ℤ) ^ 2 := by exact_mod_cast h₁
  have H₂ : (x₂ : ℤ) ^ 2 + 1 = m * (y₂ : ℤ) ^ 2 := by exact_mod_cast h₂
  have hlt' : (x₁ : ℤ) < x₂ := by exact_mod_cast hlt
  have hx₁ : (0 : ℤ) ≤ x₁ := by positivity
  have hy₁ : (0 : ℤ) ≤ y₁ := by positivity
  have hy₂ : (0 : ℤ) ≤ y₂ := by positivity
  have hm : (0 : ℤ) ≤ m := by positivity
  set a : ℤ := m * y₁ * y₂ - x₁ * x₂ with ha
  set c : ℤ := x₂ * y₁ - x₁ * y₂ with hc
  have hnorm : a ^ 2 - m * c ^ 2 = 1 := by
    rw [ha, hc]; linear_combination ((x₂ : ℤ) ^ 2 - m * (y₂ : ℤ) ^ 2) * H₁ - H₂
  have hx₂eq : (x₂ : ℤ) = a * x₁ + m * c * y₁ := by
    rw [ha, hc]; linear_combination (x₂ : ℤ) * H₁
  -- c ≥ 1 (as in `pell_growth`)
  have hm0 : (0 : ℤ) < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at h₁
    · exact_mod_cast h0
  have hyy : (y₁ : ℤ) ^ 2 < (y₂ : ℤ) ^ 2 := by
    have : (m : ℤ) * y₁ ^ 2 < m * y₂ ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hm0.le
  have hsq : ((x₁ : ℤ) * y₂) ^ 2 < ((x₂ : ℤ) * y₁) ^ 2 := by
    have : ((x₂ : ℤ) * y₁) ^ 2 - ((x₁ : ℤ) * y₂) ^ 2 = (y₂ : ℤ) ^ 2 - (y₁ : ℤ) ^ 2 := by
      linear_combination (y₁ : ℤ) ^ 2 * H₂ - (y₂ : ℤ) ^ 2 * H₁
    linarith
  have hc1 : 1 ≤ c := by
    have hpos : (x₁ : ℤ) * y₂ < x₂ * y₁ :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [hc]; linarith
  -- a ≥ 1: a² = 1 + m c² > 0, and a > 0 since a x₁ = x₂ - m c y₁ ... use a y₁ > x₁ ≥ 0 below
  have ha2 : a ^ 2 = 1 + m * c ^ 2 := by linarith
  -- (a y₁)² ≥ (m + 1) y₁² > x₁²
  have hay : (x₁ : ℤ) ^ 2 < (a * y₁) ^ 2 := by
    have : (a * y₁) ^ 2 = (1 + m * c ^ 2) * y₁ ^ 2 := by rw [mul_pow, ha2]
    rw [this]
    have hc2 : (1 : ℤ) ≤ c ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 hm) (sq_nonneg (y₁ : ℤ))]
  have ha1 : 0 < a := by
    have hsq2 : ((m : ℤ) * y₁ * y₂) ^ 2 = ((x₁ : ℤ) ^ 2 + 1) * ((x₂ : ℤ) ^ 2 + 1) := by
      linear_combination (-(m : ℤ) * y₂ ^ 2) * H₁ - ((x₁ : ℤ) ^ 2 + 1) * H₂
    have hlt2 : ((x₁ : ℤ) * x₂) ^ 2 < ((m : ℤ) * y₁ * y₂) ^ 2 := by rw [hsq2]; nlinarith
    have h0 : (0 : ℤ) ≤ (m : ℤ) * y₁ * y₂ := by positivity
    have := lt_of_pow_lt_pow_left₀ 2 h0 hlt2
    rw [ha]; linarith
  have hx2 : (x₂ : ℤ) ^ 2 ≥ 4 * m * x₁ ^ 2 := by
    have hA : (0 : ℤ) ≤ a * x₁ := by positivity
    have hB : (0 : ℤ) ≤ m * c * y₁ := by positivity
    have hamgm : 4 * (a * x₁) * (m * c * y₁) ≤ (x₂ : ℤ) ^ 2 := by
      have hid : (a * x₁ + m * c * y₁) ^ 2 - 4 * (a * x₁) * (m * c * y₁) = (a * x₁ - m * c * y₁) ^ 2 := by
        ring
      rw [hx₂eq]; linarith [sq_nonneg (a * x₁ - m * c * y₁)]
    have hay0 : (0 : ℤ) ≤ a * y₁ := by positivity
    have hayx : (x₁ : ℤ) ≤ a * y₁ := (lt_of_pow_lt_pow_left₀ 2 hay0 hay).le
    have e1 : (x₁ : ℤ) * x₁ ≤ x₁ * (a * y₁) := mul_le_mul_of_nonneg_left hayx hx₁
    have e2 : (x₁ : ℤ) * (a * y₁) ≤ x₁ * (a * y₁) * c :=
      le_mul_of_one_le_right (mul_nonneg hx₁ hay0) hc1
    have e3 : 4 * (a * x₁) * (m * c * y₁) = 4 * m * (x₁ * (a * y₁) * c) := by ring
    have : 4 * (m : ℤ) * x₁ ^ 2 ≤ 4 * m * (x₁ * (a * y₁) * c) := by
      have h4m : (0 : ℤ) ≤ 4 * m := by positivity
      rw [sq]; exact mul_le_mul_of_nonneg_left (e1.trans e2) h4m
    linarith
  exact_mod_cast hx2

/-! ### Counting chains -/

/-- `chainCnt G X₂ f T`: the number of `j ≥ 0` with `G^j X₂ ≤ T` (fuel `f`). -/
def chainCnt (G X₂ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, T => if T < X₂ then 0 else 1 + chainCnt G X₂ f (T / G)

/-- A finite set whose squares lie in `[X₂, T]` and grow by `G ≥ 2` between any two elements has
at most `chainCnt G X₂ f T` elements, for any fuel `f > T`. -/
theorem card_chain_le (G X₂ : ℕ) (hG : 2 ≤ G) (hX : 1 ≤ X₂) :
    ∀ f T (S : Finset ℕ), T < f → (∀ x ∈ S, X₂ ≤ x ^ 2 ∧ x ^ 2 ≤ T) →
      (∀ x ∈ S, ∀ x' ∈ S, x < x' → G * x ^ 2 ≤ x' ^ 2) → S.card ≤ chainCnt G X₂ f T := by
  intro f
  induction f with
  | zero => intro T S hT; omega
  | succ f ih =>
    intro T S hT hS hgr
    unfold chainCnt
    split_ifs with hTX
    · -- no element fits
      apply Nat.le_of_eq
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx; have := hS x hx; omega
    · -- elements with x² ≤ T/G, and at most one above
      set S' := S.filter (fun x => x ^ 2 ≤ T / G)
      have hone : (S.filter (fun x => T / G < x ^ 2)).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_filter] at hx hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have h1 := hgr x hx.1 x' hx'.1 hlt
          have h2 := (hS x' hx'.1).2
          have : T < G * x ^ 2 := by
            have := Nat.lt_mul_of_div_lt hx.2 (by omega : 0 < G); linarith
          omega
        · have h1 := hgr x' hx'.1 x hx.1 hlt
          have h2 := (hS x hx.1).2
          have : T < G * x' ^ 2 := by
            have := Nat.lt_mul_of_div_lt hx'.2 (by omega : 0 < G); linarith
          omega
      have hS'b : S'.card ≤ chainCnt G X₂ f (T / G) := by
        apply ih (T / G) S'
        · have : T / G < T ∨ T = 0 := by
            rcases Nat.eq_zero_or_pos T with h | h
            · right; exact h
            · left; exact Nat.div_lt_self h (by omega)
          omega
        · intro x hx; rw [mem_filter] at hx; exact ⟨(hS x hx.1).1, hx.2⟩
        · intro x hx x' hx' hlt
          exact hgr x (mem_filter.mp hx).1 x' (mem_filter.mp hx').1 hlt
      have hsplit := card_filter_add_card_filter_not (s := S) (fun x => x ^ 2 ≤ T / G)
      have hneg : (S.filter (fun x => ¬ x ^ 2 ≤ T / G)).card ≤ 1 := by
        have : S.filter (fun x => ¬ x ^ 2 ≤ T / G) = S.filter (fun x => T / G < x ^ 2) := by
          apply filter_congr; intro x _; omega
        rw [this]; exact hone
      calc S.card = S'.card + (S.filter (fun x => ¬ x ^ 2 ≤ T / G)).card := hsplit.symm
        _ ≤ chainCnt G X₂ f (T / G) + 1 := Nat.add_le_add hS'b hneg
        _ = 1 + chainCnt G X₂ f (T / G) := by ring

/-! ### Lemma P -/

/-- Admissible `m`: `m ≡ 1, 2, 5 (mod 8)` and none of `3, 7, 11, 19, 23` divides `m`. -/
def admB (m : ℕ) : Bool :=
  (m % 8 == 1 || m % 8 == 2 || m % 8 == 5) && m % 3 != 0 && m % 7 != 0 && m % 11 != 0 &&
    m % 19 != 0 && m % 23 != 0

/-- `n² + 1` is never divisible by `4`, nor by `3, 7, 11, 19, 23`. -/
lemma sq_add_one_mod_k (n k : ℕ) (hk : 0 < k) : (n ^ 2 + 1) % k = ((n % k) ^ 2 + 1) % k := by
  rw [Nat.add_mod, Nat.pow_mod]; conv_rhs => rw [Nat.add_mod]

lemma sq_add_one_mod (n : ℕ) : (n ^ 2 + 1) % 4 ≠ 0 ∧ (n ^ 2 + 1) % 3 ≠ 0 ∧ (n ^ 2 + 1) % 7 ≠ 0 ∧
    (n ^ 2 + 1) % 11 ≠ 0 ∧ (n ^ 2 + 1) % 19 ≠ 0 ∧ (n ^ 2 + 1) % 23 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq_add_one_mod_k n 4 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 4 by norm_num); interval_cases (n % 4) <;> decide
  · rw [sq_add_one_mod_k n 3 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 3 by norm_num); interval_cases (n % 3) <;> decide
  · rw [sq_add_one_mod_k n 7 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 7 by norm_num); interval_cases (n % 7) <;> decide
  · rw [sq_add_one_mod_k n 11 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 11 by norm_num); interval_cases (n % 11) <;> decide
  · rw [sq_add_one_mod_k n 19 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 19 by norm_num); interval_cases (n % 19) <;> decide
  · rw [sq_add_one_mod_k n 23 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 23 by norm_num); interval_cases (n % 23) <;> decide

/-- If `n² + 1 = p² m` then `m` is admissible. -/
lemma admB_of_eq {n p m : ℕ} (h : n ^ 2 + 1 = m * p ^ 2) : admB m = true := by
  obtain ⟨h4, h3, h7, h11, h19, h23⟩ := sq_add_one_mod n
  -- p is odd, so p² ≡ 1 (mod 8)
  have hp : p % 2 = 1 := by
    by_contra hp
    have : p % 2 = 0 := by omega
    have h4' : 4 ∣ n ^ 2 + 1 := by
      rw [h]; obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
      exact ⟨m * k ^ 2, by rw [hk]; ring⟩
    exact h4 (Nat.mod_eq_zero_of_dvd h4')
  have hp8 : p ^ 2 % 8 = 1 := by
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h] <;> norm_num
  have hn8 : (n ^ 2 + 1) % 8 = 1 ∨ (n ^ 2 + 1) % 8 = 2 ∨ (n ^ 2 + 1) % 8 = 5 := by
    have hk : (n ^ 2 + 1) % 8 = ((n % 8) ^ 2 + 1) % 8 := by
      rw [Nat.add_mod, Nat.pow_mod]; conv_rhs => rw [Nat.add_mod]
    rw [hk]; have := Nat.mod_lt n (show 0 < 8 by norm_num)
    interval_cases (n % 8) <;> simp
  have hm8 : m % 8 = (n ^ 2 + 1) % 8 := by
    rw [h, Nat.mul_mod, hp8, mul_one, Nat.mod_mod]
  have hdiv : ∀ l, m % l = 0 → (n ^ 2 + 1) % l = 0 := by
    intro l hl; rw [h]; exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hl) _)
  unfold admB
  have e3 : m % 3 ≠ 0 := fun hz => h3 (hdiv 3 hz)
  have e7 : m % 7 ≠ 0 := fun hz => h7 (hdiv 7 hz)
  have e11 : m % 11 ≠ 0 := fun hz => h11 (hdiv 11 hz)
  have e19 : m % 19 ≠ 0 := fun hz => h19 (hdiv 19 hz)
  have e23 : m % 23 ≠ 0 := fun hz => h23 (hdiv 23 hz)
  rcases hn8 with h1 | h1 | h1 <;> rw [h1] at hm8 <;> simp [hm8, e3, e7, e11, e19, e23]

/-- The bound of Lemma P for one `m`. -/
def pellTerm (N Y m : ℕ) : ℕ :=
  if admB m then chainCnt (max 9 (4 * m)) (m * (Y + 1) ^ 2 - 1) (N ^ 2 + 1) (N ^ 2) else 0

/-- **Lemma P** (Pell tail counted in a window). -/
theorem pellWin_le (N Y : ℕ) (hY : 1 ≤ Y) :
    ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card ≤
      ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), pellTerm N Y m := by
  classical
  set M := (N ^ 2 + 1) / (Y + 1) ^ 2
  -- solutions for one `m`
  let Sm : ℕ → Finset ℕ := fun m =>
    (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), n ^ 2 + 1 = m * p ^ 2)
  have hcover : (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1) ⊆
      (Icc 1 M).biUnion Sm := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, p, ⟨hp1, hpN⟩, ⟨m, hm⟩⟩ := hn
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
    simp only [mem_biUnion, mem_Icc, Sm, mem_filter]
    exact ⟨m, ⟨hm1, hmM⟩, ⟨hn1, hnN⟩, p, ⟨hp1, hpN⟩, by rw [hm]; ring⟩
  refine (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum ?_))
  intro m hm
  rw [mem_Icc] at hm
  unfold pellTerm
  by_cases hadm : admB m = true
  · rw [if_pos hadm]
    apply card_chain_le (max 9 (4 * m)) (m * (Y + 1) ^ 2 - 1) (by omega)
    · -- X₂ ≥ 1
      have h4 : 4 ≤ (Y + 1) ^ 2 := by nlinarith
      have : 4 ≤ m * (Y + 1) ^ 2 := le_trans h4 (Nat.le_mul_of_pos_left _ (by omega))
      omega
    · omega
    · intro x hx
      simp only [Sm, mem_filter, mem_Icc] at hx
      obtain ⟨⟨hx1, hxN⟩, p, ⟨hp1, -⟩, hxp⟩ := hx
      refine ⟨?_, by nlinarith⟩
      have : m * (Y + 1) ^ 2 ≤ m * p ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp1 2)
      omega
    · intro x hx x' hx' hlt
      simp only [Sm, mem_filter, mem_Icc] at hx hx'
      obtain ⟨-, p, -, hxp⟩ := hx
      obtain ⟨-, p', -, hxp'⟩ := hx'
      have g1 := pell_growth hxp hxp' hlt
      have g2 := pell_growth2 hxp hxp' hlt
      rcases le_total 9 (4 * m) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
  · rw [if_neg hadm]
    apply Nat.le_of_eq
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Sm, mem_filter] at hx
    obtain ⟨-, p, -, hxp⟩ := hx
    exact hadm (admB_of_eq hxp)

/-! ### Lemma H -/

lemma sqRoots_neg {p r : ℕ} (hr : r ∈ sqRoots p) (h0 : 0 < r) : p * p - r ∈ sqRoots p := by
  simp only [sqRoots, mem_filter, mem_range] at hr ⊢
  refine ⟨by omega, ?_⟩
  have hz : (((p * p - r) * (p * p - r) + 1 : ℕ) : ZMod (p * p)) = ((r * r + 1 : ℕ) : ZMod (p * p)) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr.1.le, ZMod.natCast_self]; push_cast; ring
  rw [← ZMod.natCast_eq_zero_iff] at hr ⊢
  rw [hz]; exact hr.2

/-- **Lemma H.** For an odd prime `p` with `p² > N`, at most two `n ∈ [1,N]` have `p² ∣ n² + 1`;
if `p² > 2N`, at most one. -/
theorem card_sqRoots_Icc_le {p N : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hpN : N < p * p) :
    ((Icc 1 N).filter (fun n => n % (p * p) ∈ sqRoots p)).card ≤ 2 ∧
      (2 * N < p * p → ((Icc 1 N).filter (fun n => n % (p * p) ∈ sqRoots p)).card ≤ 1) := by
  have hsub : (Icc 1 N).filter (fun n => n % (p * p) ∈ sqRoots p) ⊆ sqRoots p := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hn.1.2 hpN)] at hn; exact hn.2
  refine ⟨(card_le_card hsub).trans (card_sqRoots_le hp h2), fun h2N => ?_⟩
  rw [card_le_one]
  intro x hx y hy
  have hx' := hsub hx
  have hy' := hsub hy
  simp only [mem_filter, mem_Icc] at hx hy
  by_contra hne
  -- {x, y, p² - x} ⊆ sqRoots p has at most two elements, so y = p² - x
  have hnx := sqRoots_neg hx' (by omega)
  have hxy : p * p - x ≠ x := by omega
  have h3 : ({x, y, p * p - x} : Finset ℕ).card ≤ 2 := by
    refine (card_le_card ?_).trans (card_sqRoots_le hp h2)
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with h | h | h <;> rw [h] <;> assumption
  have hy3 : y = p * p - x := by
    by_contra hy3
    have : ({x, y, p * p - x} : Finset ℕ).card = 3 := by
      rw [card_insert_of_notMem (by simp; omega), card_pair hy3]
    omega
  omega

end Erdos848
