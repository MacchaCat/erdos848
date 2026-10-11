import Erdos848.OmegaBound
import Erdos848.Counting

/-!
# Phase 4 (part 3): the bound for `Ex(b)` (Lemma A′(ii))

`exSet N b Y = {a ∈ [1,N] : ∃ p > Y, p² ∣ ab+1}` and

  `#exSet N b Y ≤ rhoBound b · (2(N+1)/Y + (Nb+1)/Y²)`   (`card_exSet_le`, for `1 ≤ b`, `1 ≤ Y`).

Proof: write `ab+1 = p² m`; `a ↦ (m, p)` is injective, `m ≤ (Nb+1)/(Y+1)²`, `p ≤ √((Nb+1)/m)`,
and for fixed `m` the residue `p mod b` lies in a set of at most `rhoBound b` square roots.
-/

namespace Erdos848

open Finset Real

/-! ### A real-analysis lemma: `∑_{m ≤ M} 1/√m ≤ 2√M` -/

lemma sum_inv_sqrt_le (M : ℕ) : ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) ≤ 2 * √(M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) ≤ M := by positivity
    have key : 1 / √((M + 1 : ℕ) : ℝ) ≤ 2 * √((M + 1 : ℕ) : ℝ) - 2 * √(M : ℝ) := by
      push_cast
      have h1 : 0 < √((M : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      rw [div_le_iff₀ h1]
      have hsq : √(M : ℝ) * √((M : ℝ) + 1) ≤ (M : ℝ) + 1 / 2 := by
        rw [← Real.sqrt_mul hM]
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      have e1 : √((M : ℝ) + 1) * √((M : ℝ) + 1) = (M : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
      nlinarith
    linarith

/-! ### The set `Ex(b)` and its bound -/

def exSet (N b Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => ∃ p ∈ Icc (Y + 1) (N * b + 1), p * p ∣ a * b + 1)

/-- Residues `s < b` with `s² m ≡ 1 (mod b)`. -/
def rootSet (b m : ℕ) : Finset ℕ := (range b).filter (fun s => s * s * m % b = 1 % b)

lemma card_rootSet_le (b m : ℕ) : (rootSet b m).card ≤ rhoBound b := by
  by_cases hR : rootSet b m = ∅
  · rw [hR]; simp
  obtain ⟨s₀, hs₀⟩ := nonempty_iff_ne_empty.mpr hR
  simp only [rootSet, mem_filter, mem_range] at hs₀
  -- gcd(m, b) = 1 and gcd(s₀², b) = 1
  have hcop : Nat.Coprime (s₀ * s₀ * m) b := by
    have : s₀ * s₀ * m ≡ 1 [MOD b] := hs₀.2
    have h := Nat.ModEq.gcd_eq this
    rw [Nat.gcd_one_left] at h
    exact h
  have hm : Nat.Coprime m b := Nat.Coprime.coprime_mul_left hcop
  have hs : Nat.Coprime (s₀ * s₀) b := Nat.Coprime.coprime_mul_right hcop
  calc (rootSet b m).card ≤ sqrtCount b (s₀ * s₀) := by
        apply card_le_card
        intro x hx
        simp only [rootSet, mem_filter, mem_range] at hx
        simp only [mem_filter, mem_range]
        refine ⟨hx.1, ?_⟩
        -- x² m ≡ s₀² m ≡ 1, cancel m
        have h1 : x * x * m ≡ s₀ * s₀ * m [MOD b] := by
          unfold Nat.ModEq; rw [hx.2, hs₀.2]
        have h2 : x * x ≡ s₀ * s₀ [MOD b] :=
          Nat.ModEq.cancel_right_of_coprime (Nat.coprime_comm.mp hm) h1
        exact h2
    _ ≤ rhoBound b := sqrtCount_le_rhoBound b _ hs

/-- Integers `p ∈ [1, X]` with `p mod b` in `R`: at most `|R| (X/b + 1)`. -/
lemma card_mod_mem_le (X b : ℕ) (R : Finset ℕ) :
    ((Icc 1 X).filter (fun p => p % b ∈ R)).card ≤ R.card * (X / b + 1) := by
  calc ((Icc 1 X).filter (fun p => p % b ∈ R)).card
      ≤ (R.biUnion (fun r => (Icc 1 X).filter (fun p => p % b = r))).card := by
        apply card_le_card; intro p hp
        simp only [mem_filter] at hp
        simp only [mem_biUnion, mem_filter]
        exact ⟨p % b, hp.2, hp.1, rfl⟩
    _ ≤ ∑ r ∈ R, ((Icc 1 X).filter (fun p => p % b = r)).card := card_biUnion_le
    _ ≤ ∑ _r ∈ R, (X / b + 1) := sum_le_sum (fun r _ => card_mod_eq_le X b r)
    _ = R.card * (X / b + 1) := by simp

/-- **Lemma A′(ii).** `#Ex(b) ≤ rhoBound b · (2(N+1)/Y + (Nb+1)/Y²)`. -/
theorem card_exSet_le (N b Y : ℕ) (hb : 1 ≤ b) (hY : 1 ≤ Y) :
    ((exSet N b Y).card : ℝ) ≤ rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  classical
  set K := N * b + 1 with hK
  set M := K / ((Y + 1) * (Y + 1)) with hM
  -- per-m sets of admissible p
  let Pm : ℕ → Finset ℕ := fun m => (Icc 1 (Nat.sqrt (K / m))).filter (fun p => p % b ∈ rootSet b m)
  -- every a ∈ Ex(b) is (p² m − 1)/b for some (m, p) in the sigma set
  have hcard : (exSet N b Y).card ≤ ((Icc 1 M).sigma Pm).card := by
    calc (exSet N b Y).card
        ≤ (((Icc 1 M).sigma Pm).image (fun x => (x.2 * x.2 * x.1 - 1) / b)).card := by
          apply card_le_card
          intro a ha
          simp only [exSet, mem_filter, mem_Icc] at ha
          obtain ⟨⟨ha1, haN⟩, p, hpI, hdvd⟩ := ha
          have hp1 : Y + 1 ≤ p := hpI.1
          obtain ⟨m, hm⟩ := hdvd
          have hp0 : 0 < p * p := Nat.mul_pos (by omega) (by omega)
          have hab : a * b + 1 ≤ K := by rw [hK]; nlinarith
          have hm1 : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · rw [h0] at hm; simp at hm
            · exact h0
          rw [mem_image]
          refine ⟨⟨m, p⟩, ?_, ?_⟩
          · simp only [mem_sigma, mem_Icc, Pm, mem_filter]
            refine ⟨⟨hm1, ?_⟩, ⟨by omega, ?_⟩, ?_⟩
            · rw [hM, Nat.le_div_iff_mul_le (by positivity)]
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
  -- count the sigma set
  have hsig : ((Icc 1 M).sigma Pm).card ≤ ∑ m ∈ Icc 1 M, rhoBound b * (Nat.sqrt (K / m) / b + 1) := by
    rw [card_sigma]
    apply sum_le_sum; intro m _
    calc (Pm m).card ≤ (rootSet b m).card * (Nat.sqrt (K / m) / b + 1) := card_mod_mem_le _ _ _
      _ ≤ rhoBound b * (Nat.sqrt (K / m) / b + 1) := Nat.mul_le_mul_right _ (card_rootSet_le b m)
  -- real estimate of the sum
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hKpos : (0 : ℝ) < K := by positivity
  have hterm : ∀ m ∈ Icc 1 M, ((Nat.sqrt (K / m) / b + 1 : ℕ) : ℝ) ≤ √(K : ℝ) / b * (1 / √(m : ℝ)) + 1 := by
    intro m hm
    simp only [mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    push_cast
    have h1 : ((Nat.sqrt (K / m) / b : ℕ) : ℝ) ≤ (Nat.sqrt (K / m) : ℝ) / b := Nat.cast_div_le
    have h2 : (Nat.sqrt (K / m) : ℝ) ≤ √((K / m : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h3 : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have h4 : √((K / m : ℕ) : ℝ) ≤ √((K : ℝ) / m) := Real.sqrt_le_sqrt h3
    have h5 : √((K : ℝ) / m) = √(K : ℝ) * (1 / √(m : ℝ)) := by
      rw [Real.sqrt_div' _ hm0.le, div_eq_mul_one_div]
    have hbpos : (0 : ℝ) < b := by linarith
    have : (Nat.sqrt (K / m) : ℝ) / b ≤ √(K : ℝ) / b * (1 / √(m : ℝ)) := by
      rw [div_mul_eq_mul_div, ← h5]
      exact div_le_div_of_nonneg_right (h2.trans h4) hbpos.le
    linarith
  have hsum := sum_inv_sqrt_le M
  have hMreal : (M : ℝ) ≤ (K : ℝ) / ((Y : ℝ) + 1) ^ 2 := by
    rw [hM]
    have := (Nat.cast_div_le (m := K) (n := (Y + 1) * (Y + 1)) : ((K / ((Y + 1) * (Y + 1)) : ℕ) : ℝ) ≤ _)
    push_cast at this; rw [sq]; exact this
  have hsqM : √(M : ℝ) ≤ √(K : ℝ) / ((Y : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Y : ℝ) + 1),
      ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc (M : ℝ) * ((Y : ℝ) + 1) ^ 2 ≤ (K : ℝ) / ((Y : ℝ) + 1) ^ 2 * ((Y : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hMreal (by positivity)
      _ = K := by field_simp
  calc ((exSet N b Y).card : ℝ) ≤ ((∑ m ∈ Icc 1 M, rhoBound b * (Nat.sqrt (K / m) / b + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard.trans hsig
    _ = rhoBound b * ∑ m ∈ Icc 1 M, ((Nat.sqrt (K / m) / b + 1 : ℕ) : ℝ) := by
        push_cast; rw [mul_sum]
    _ ≤ rhoBound b * ∑ m ∈ Icc 1 M, (√(K : ℝ) / b * (1 / √(m : ℝ)) + 1) := by
        apply mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = rhoBound b * (√(K : ℝ) / b * ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) + M) := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ rhoBound b * (√(K : ℝ) / b * (2 * √(M : ℝ)) + (K : ℝ) / ((Y : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) hMreal
    _ ≤ rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hKN : (K : ℝ) = N * b + 1 := by rw [hK]; push_cast; ring
        have hsK : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt hKpos.le
        have e1 : √(K : ℝ) / b * (2 * √(M : ℝ)) ≤ 2 * (N + 1) / Y := by
          calc √(K : ℝ) / b * (2 * √(M : ℝ)) ≤ √(K : ℝ) / b * (2 * (√(K : ℝ) / ((Y : ℝ) + 1))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
            _ = 2 * (√(K : ℝ) * √(K : ℝ)) / (b * ((Y : ℝ) + 1)) := by
                have : (b : ℝ) ≠ 0 := by linarith
                field_simp
            _ = 2 * K / (b * ((Y : ℝ) + 1)) := by rw [hsK]
            _ ≤ 2 * (N + 1) / Y := by
                rw [hKN, div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ N) (by linarith : (0:ℝ) ≤ b - 1)]
        have e2 : (K : ℝ) / ((Y : ℝ) + 1) ^ 2 ≤ (N * b + 1) / (Y : ℝ) ^ 2 := by
          rw [hKN]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
        linarith

end Erdos848
