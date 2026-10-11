import Mathlib

/-!
# Phase 6: an explicit prime-counting bound from Chebyshev's `θ(x) ≤ x log 4`

`card_primesLE_le : #{p ≤ n prime} ≤ √n + 2 log 4 · n / log n` for `n ≥ 2`.

This is the only prime-counting bound the analytic certificates need beyond exact prime counts
(`code/n0_exact.py --cheb`); it replaces the Rosser–Schoenfeld bound, which is not in Mathlib.
-/

namespace Erdos848

open Real Finset Chebyshev

theorem card_primesLE_le (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.primesLE n).card : ℝ) ≤ √(n : ℝ) + 2 * log 4 * n / log n := by
  set s := Nat.sqrt n with hs
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < log (n : ℝ) := log_pos hn1
  have hsplit := card_filter_add_card_filter_not (s := Nat.primesLE n) (fun p => p ≤ s)
  -- primes ≤ √n
  have h1 : (((Nat.primesLE n).filter (fun p => p ≤ s)).card : ℝ) ≤ √(n : ℝ) := by
    have hc : ((Nat.primesLE n).filter (fun p => p ≤ s)).card ≤ s := by
      calc ((Nat.primesLE n).filter (fun p => p ≤ s)).card ≤ (Icc 1 s).card := by
            apply card_le_card
            intro p hp
            simp only [mem_filter, Nat.mem_primesLE] at hp
            simp only [mem_Icc]
            exact ⟨hp.1.2.one_lt.le, hp.2⟩
        _ = s := by simp
    calc (((Nat.primesLE n).filter (fun p => p ≤ s)).card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hc
      _ ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
  -- primes > √n: each has log p ≥ (log n) / 2
  set L := (Nat.primesLE n).filter (fun p => ¬ p ≤ s) with hL
  have hlogp : ∀ p ∈ L, log (n : ℝ) / 2 ≤ log p := by
    intro p hp
    simp only [hL, mem_filter, Nat.mem_primesLE, not_le] at hp
    have hsp : s + 1 ≤ p := hp.2
    have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
    have hnp : (n : ℝ) ≤ (p : ℝ) ^ 2 := by
      have : n ≤ p * p := le_trans hlt.le (Nat.mul_le_mul hsp hsp)
      rw [sq]; exact_mod_cast this
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.2.pos
    have := Real.log_le_log (by positivity) hnp
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2 : (L.card : ℝ) * (log (n : ℝ) / 2) ≤ log 4 * n := by
    calc (L.card : ℝ) * (log (n : ℝ) / 2) = ∑ _p ∈ L, (log (n : ℝ) / 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ L, log (p : ℝ) := sum_le_sum hlogp
      _ ≤ ∑ p ∈ Nat.primesLE n, log (p : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p hp _
          exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)
      _ = θ n := (theta_eq_sum_primesLE_log n).symm
      _ ≤ log 4 * n := theta_le_log4_mul_x (by positivity)
  have h3 : (L.card : ℝ) ≤ 2 * log 4 * n / log n := by
    rw [le_div_iff₀ hlogn]
    linarith
  have hsplit' : ((Nat.primesLE n).card : ℝ) =
      (((Nat.primesLE n).filter (fun p => p ≤ s)).card : ℝ) + (L.card : ℝ) := by
    rw [← hsplit]; push_cast; ring
  rw [hsplit']
  linarith

end Erdos848
