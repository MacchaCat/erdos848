import Erdos848.ExBound
import Erdos848.Dom

/-!
# Phase 9.4 (part 1): sharper bounds for `Ex(b)` (Lemma E of `proof.md` §10.1)

* `card_exSet_le_E0`: `#Ex(b) ≤ ∑_{m ≤ M} |rootSet b m| · ((X_m - Y)/b + 1)`, where
  `K = Nb + 1`, `M = ⌊K/(Y+1)²⌋`, `X_m = ⌊√(K/m)⌋`: a prime `p > Y` with `p² m = ab + 1` lies in
  `(Y, X_m]`, in one of `|rootSet b m|` classes mod `b`.
* `sum_fE_le`: `∑_{m ≤ M} ((X_m - Y)/b + 1) ≤ (N+1)/Y + M` (Lemma E1).
* `abel_le`: Abel summation against a nonincreasing nonnegative weight.
* `card_exSet_le_E1`, `card_exSet_le_E2`: the resulting bounds.
-/

namespace Erdos848

open Finset Real

/-- The weight `f(m) = (X_m - Y)/b + 1`. -/
noncomputable def fE (N b Y m : ℕ) : ℝ := ((Nat.sqrt ((N * b + 1) / m) : ℝ) - Y) / b + 1

/-- `M = ⌊(Nb+1)/(Y+1)²⌋`. -/
def exM (N b Y : ℕ) : ℕ := (N * b + 1) / ((Y + 1) * (Y + 1))

lemma sqrt_ge_of_le_exM {N b Y m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ exM N b Y) :
    Y + 1 ≤ Nat.sqrt ((N * b + 1) / m) := by
  apply Nat.le_sqrt.mpr
  rw [Nat.le_div_iff_mul_le (by omega)]
  unfold exM at hmM
  have := (Nat.le_div_iff_mul_le (by positivity)).mp hmM
  nlinarith

/-- Integers of `(Y, X]` in a set `R` of classes mod `b`: at most `|R| ((X - Y)/b + 1)`. -/
lemma card_Icc_mod_mem_le (Y X b : ℕ) (hYX : Y + 1 ≤ X + 1) (hb : 0 < b) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r < b) :
    (((Icc (Y + 1) X).filter (fun p => p % b ∈ R)).card : ℝ) ≤ R.card * (((X : ℝ) - Y) / b + 1) := by
  have hD := goodDom_Icc (Y + 1) X (by omega) hYX
  have h := hD.mem_real hb trivial R hR
  rw [abs_le] at h
  have hL : (((X + 1 - (Y + 1) : ℕ) : ℝ)) = (X : ℝ) - Y := by
    rw [show X + 1 - (Y + 1) = X - Y by omega, Nat.cast_sub (by omega)]
  rw [hL] at h
  nlinarith [h.2]

/-- **Lemma E0.** -/
theorem card_exSet_le_E0 (N b Y : ℕ) (hb : 1 ≤ b) :
    ((exSet N b Y).card : ℝ) ≤ ∑ m ∈ Icc 1 (exM N b Y), ((rootSet b m).card : ℝ) * fE N b Y m := by
  classical
  set K := N * b + 1 with hK
  set M := exM N b Y with hM
  let Pm : ℕ → Finset ℕ := fun m =>
    (Icc (Y + 1) (Nat.sqrt (K / m))).filter (fun p => p % b ∈ rootSet b m)
  have hcard : (exSet N b Y).card ≤ ((Icc 1 M).sigma Pm).card := by
    calc (exSet N b Y).card
        ≤ (((Icc 1 M).sigma Pm).image (fun x => (x.2 * x.2 * x.1 - 1) / b)).card := by
          apply card_le_card
          intro a ha
          simp only [exSet, mem_filter, mem_Icc] at ha
          obtain ⟨⟨ha1, haN⟩, p, hpI, hdvd⟩ := ha
          have hp1 : Y + 1 ≤ p := hpI.1
          obtain ⟨m, hm⟩ := hdvd
          have hab : a * b + 1 ≤ K := by rw [hK]; nlinarith
          have hm1 : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · rw [h0] at hm; simp at hm
            · exact h0
          rw [mem_image]
          refine ⟨⟨m, p⟩, ?_, ?_⟩
          · simp only [mem_sigma, mem_Icc, Pm, mem_filter]
            refine ⟨⟨hm1, ?_⟩, ⟨hp1, ?_⟩, ?_⟩
            · rw [hM, exM, Nat.le_div_iff_mul_le (by positivity)]
              calc m * ((Y + 1) * (Y + 1)) ≤ m * (p * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hp1 hp1)
                _ = a * b + 1 := by rw [hm]; ring
                _ ≤ K := hab
            · apply Nat.le_sqrt.mpr
              rw [Nat.le_div_iff_mul_le (by omega)]
              rw [show p * p * m = a * b + 1 by rw [hm]]; exact hab
            · simp only [rootSet, mem_filter, mem_range]
              refine ⟨Nat.mod_lt _ (by omega), ?_⟩
              have h1 : p * p * m % b = 1 % b := by
                rw [← hm, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
              have h2 : p % b * (p % b) * m % b = p * p * m % b :=
                (((Nat.mod_modEq p b).mul (Nat.mod_modEq p b)).mul_right m)
              rw [h2, h1]
          · simp only
            rw [show p * p * m = a * b + 1 by rw [hm], Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]
      _ ≤ ((Icc 1 M).sigma Pm).card := card_image_le
  have hsig : (((Icc 1 M).sigma Pm).card : ℝ) ≤
      ∑ m ∈ Icc 1 M, ((rootSet b m).card : ℝ) * fE N b Y m := by
    rw [card_sigma]; push_cast
    apply sum_le_sum; intro m hm
    rw [mem_Icc] at hm
    have hX : Y + 1 ≤ Nat.sqrt (K / m) := sqrt_ge_of_le_exM hm.1 hm.2
    have := card_Icc_mod_mem_le Y (Nat.sqrt (K / m)) b (by omega) (by omega) (rootSet b m)
      (fun r hr => (mem_range.mp (mem_filter.mp hr).1))
    unfold fE; exact this
  calc ((exSet N b Y).card : ℝ) ≤ (((Icc 1 M).sigma Pm).card : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := hsig

lemma fE_nonneg {N b Y m : ℕ} (hb : 1 ≤ b) (hm : 1 ≤ m) (hmM : m ≤ exM N b Y) : 0 ≤ fE N b Y m := by
  have hX := sqrt_ge_of_le_exM hm hmM
  unfold fE
  have : (Y : ℝ) + 1 ≤ (Nat.sqrt ((N * b + 1) / m) : ℝ) := by exact_mod_cast hX
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have : (0 : ℝ) ≤ ((Nat.sqrt ((N * b + 1) / m) : ℝ) - Y) / b := div_nonneg (by linarith) hb'.le
  linarith

lemma fE_anti {N b Y m m' : ℕ} (hb : 1 ≤ b) (hm : 1 ≤ m) (hmm' : m ≤ m') : fE N b Y m' ≤ fE N b Y m := by
  unfold fE
  have h1 : (N * b + 1) / m' ≤ (N * b + 1) / m := Nat.div_le_div_left hmm' (by omega)
  have h2 : Nat.sqrt ((N * b + 1) / m') ≤ Nat.sqrt ((N * b + 1) / m) := Nat.sqrt_le_sqrt h1
  have h3 : (Nat.sqrt ((N * b + 1) / m') : ℝ) ≤ Nat.sqrt ((N * b + 1) / m) := by exact_mod_cast h2
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have := div_le_div_of_nonneg_right (sub_le_sub_right h3 (Y : ℝ)) hb'.le
  linarith

lemma fE_one_le (N b Y : ℕ) (hb : 1 ≤ b) : fE N b Y 1 ≤ ((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1 := by
  unfold fE
  rw [Nat.div_one]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have : ((Nat.sqrt (N * b + 1) : ℝ) - Y) / b ≤ (Nat.sqrt (N * b + 1) : ℝ) / b :=
    div_le_div_of_nonneg_right (by have h0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y; linarith) hb'.le
  linarith

/-- **Lemma E1** (the sum of the weights). -/
theorem sum_fE_le (N b Y : ℕ) (hb : 1 ≤ b) (hY : 1 ≤ Y) :
    ∑ m ∈ Icc 1 (exM N b Y), fE N b Y m ≤ ((N : ℝ) + 1) / Y + exM N b Y := by
  set K := N * b + 1 with hK
  set M := exM N b Y with hM
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hKpos : (0 : ℝ) < K := by positivity
  -- X_m ≤ √K · m^{-1/2}
  have hX : ∀ m ∈ Icc 1 M, (Nat.sqrt (K / m) : ℝ) ≤ √(K : ℝ) * (1 / √(m : ℝ)) := by
    intro m hm
    rw [mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    have h2 : (Nat.sqrt (K / m) : ℝ) ≤ √((K / m : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h3 : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have h4 : √((K / m : ℕ) : ℝ) ≤ √((K : ℝ) / m) := Real.sqrt_le_sqrt h3
    have h5 : √((K : ℝ) / m) = √(K : ℝ) * (1 / √(m : ℝ)) := by
      rw [Real.sqrt_div' _ hm0.le, div_eq_mul_one_div]
    linarith
  have hsum := sum_inv_sqrt_le M
  have hMreal : (M : ℝ) * ((Y : ℝ) + 1) ^ 2 ≤ K := by
    have : M * ((Y + 1) * (Y + 1)) ≤ K := by
      rw [hM, exM]; exact Nat.div_mul_le_self _ _
    have : ((M * ((Y + 1) * (Y + 1)) : ℕ) : ℝ) ≤ K := by exact_mod_cast this
    push_cast at this; nlinarith
  have hsqM : √(M : ℝ) * Y ≤ √(K : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ Y), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (Y : ℝ)]
  -- ∑ (X_m - Y) ≤ √K · 2√M - M Y ≤ K / Y
  have hXsum : ∑ m ∈ Icc 1 M, ((Nat.sqrt (K / m) : ℝ) - Y) ≤ (K : ℝ) / Y := by
    calc ∑ m ∈ Icc 1 M, ((Nat.sqrt (K / m) : ℝ) - Y)
        ≤ ∑ m ∈ Icc 1 M, (√(K : ℝ) * (1 / √(m : ℝ)) - Y) := sum_le_sum (fun m hm => by linarith [hX m hm])
      _ = √(K : ℝ) * ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) - M * Y := by
          rw [sum_sub_distrib, ← mul_sum]; simp
      _ ≤ √(K : ℝ) * (2 * √(M : ℝ)) - M * Y := by
          have := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg (K : ℝ)); linarith
      _ ≤ (K : ℝ) / Y := by
          rw [le_div_iff₀ (by linarith)]
          have hsK : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt hKpos.le
          have hsM : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt (by positivity)
          nlinarith [sq_nonneg (√(K : ℝ) - √(M : ℝ) * Y)]
  have hcalc : ∑ m ∈ Icc 1 M, fE N b Y m =
      (∑ m ∈ Icc 1 M, ((Nat.sqrt (K / m) : ℝ) - Y)) / b + M := by
    unfold fE; rw [sum_add_distrib, ← sum_div, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    simp [hK]
  rw [hcalc]
  have hKN : (K : ℝ) / Y / b ≤ ((N : ℝ) + 1) / Y := by
    rw [hK]; push_cast
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ N) (by linarith : (0:ℝ) ≤ b - 1)]
  have := div_le_div_of_nonneg_right hXsum (by linarith : (0:ℝ) ≤ b)
  linarith

/-- **Lemma E1.** `#Ex(b) ≤ ρ(b) ((N+1)/Y + M)`. -/
theorem card_exSet_le_E1 (N b Y : ℕ) (hb : 1 ≤ b) (hY : 1 ≤ Y) :
    ((exSet N b Y).card : ℝ) ≤ rhoBound b * (((N : ℝ) + 1) / Y + exM N b Y) := by
  have h0 := card_exSet_le_E0 N b Y hb
  have h1 : ∑ m ∈ Icc 1 (exM N b Y), ((rootSet b m).card : ℝ) * fE N b Y m ≤
      ∑ m ∈ Icc 1 (exM N b Y), (rhoBound b : ℝ) * fE N b Y m := by
    apply sum_le_sum; intro m hm
    rw [mem_Icc] at hm
    apply mul_le_mul_of_nonneg_right _ (fE_nonneg hb hm.1 hm.2)
    exact_mod_cast card_rootSet_le b m
  rw [← mul_sum] at h1
  have h2 := sum_fE_le N b Y hb hY
  have : (0 : ℝ) ≤ rhoBound b := by positivity
  nlinarith

/-! ### Abel summation -/

/-- If the partial sums of `g ≥ 0` satisfy `G(R) ≤ αR + β` for `R ≤ M`, and `f` is nonincreasing
and nonnegative on `[1, M]`, then `∑_{m ≤ M} g f ≤ α ∑_{m ≤ M} f + β f(1)`. -/
theorem abel_le (g f : ℕ → ℝ) (α β B : ℝ) (M : ℕ)
    (hG : ∀ R ≤ M, ∑ m ∈ Icc 1 R, g m ≤ α * R + β)
    (hf0 : ∀ m, 1 ≤ m → m ≤ M → 0 ≤ f m) (hfa : ∀ m, 1 ≤ m → m + 1 ≤ M → f (m + 1) ≤ f m)
    (hB : f 1 ≤ B) (hB0 : 0 ≤ B) :
    ∑ m ∈ Icc 1 M, g m * f m ≤ α * ∑ m ∈ Icc 1 M, f m + β * B := by
  have hβ : 0 ≤ β := by have := hG 0 (Nat.zero_le _); simpa using this
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp; positivity
  -- D(R) := α ∑ f + β f 1 - ∑ g f ≥ (α R + β - G R) f R, by induction on R ≥ 1
  have key : ∀ R, 1 ≤ R → R ≤ M →
      (α * R + β - ∑ m ∈ Icc 1 R, g m) * f R ≤
        α * ∑ m ∈ Icc 1 R, f m + β * f 1 - ∑ m ∈ Icc 1 R, g m * f m := by
    intro R hR1
    induction R, hR1 using Nat.le_induction with
    | base => intro _; simp only [Icc_self, sum_singleton, Nat.cast_one]; apply le_of_eq; ring
    | succ R hR1 ih =>
      intro hRM
      have ih' := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have hcoef : 0 ≤ α * R + β - ∑ m ∈ Icc 1 R, g m := by have := hG R (by omega); linarith
      have hmono : f (R + 1) ≤ f R := hfa R hR1 (by omega)
      have hf1 : 0 ≤ f (R + 1) := hf0 (R + 1) (by omega) hRM
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hmono hcoef]
  have := key M hM le_rfl
  have hcoef : 0 ≤ α * M + β - ∑ m ∈ Icc 1 M, g m := by have := hG M le_rfl; linarith
  have := mul_nonneg hcoef (hf0 M hM le_rfl)
  have := mul_le_mul_of_nonneg_left hB hβ
  linarith

end Erdos848
