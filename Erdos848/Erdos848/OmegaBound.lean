import Erdos848.SqrtCount

/-!
# Phase 4 (part 2): bounding the number of odd prime factors

`primeProd k` is the product of the first `k` odd primes.  We show that `k` distinct odd primes
have product at least `primeProd k` (`primeProd_le_prod`), and deduce the bound used by the
certificates (`code/n0_exact.py`, `rho_max`):

  for `1 ≤ b ≤ N < primeProd 45`:  `rhoBound b ≤ rhoMax N`,
  `rhoMax N = max (2^W(N)) (max (2·2^W(N/4)) (4·2^W(N/8)))`,  `W(L) = max {k ≤ 45 : primeProd k ≤ L}`.
-/

namespace Erdos848

open Finset

/-- The odd primes below 200. -/
def OP : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

lemma OP_length : OP.length = 45 := rfl

/-- Product of the first `k` odd primes. -/
def primeProd (k : ℕ) : ℕ := (OP.take k).prod

set_option maxRecDepth 20000 in
lemma OP_complete : ∀ p < 200, p.Prime → p ≠ 2 → p ∈ OP := by decide

set_option maxRecDepth 20000 in
lemma OP_count : ∀ a < 200, ∀ k < 45, a < OP[k]! → (OP.filter (· ≤ a)).length ≤ k := by decide

lemma OP_le_199 : ∀ k < 45, OP[k]! ≤ 199 := by decide

lemma primeProd_succ {k : ℕ} (hk : k < 45) : primeProd (k + 1) = primeProd k * OP[k]! := by
  unfold primeProd
  rw [List.prod_take_succ OP k (by rw [OP_length]; exact hk)]
  congr 1
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [OP_length]; exact hk)]

/-- `k` distinct odd primes have product at least `primeProd k`. -/
theorem primeProd_le_prod : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ 45 →
    primeProd S.card ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _ _; simp [primeProd]
  | insert a s hlt ih =>
    intro hS hcard
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, prod_insert has] at *
    have hk : s.card < 45 := by omega
    have ih' := ih (fun p hp => hS p (mem_insert_of_mem hp)) (by omega)
    rw [primeProd_succ hk]
    -- the (s.card)-th odd prime is at most a
    have hOa : OP[s.card]! ≤ a := by
      by_contra hcon
      push Not at hcon
      have ha200 : a < 200 := lt_of_lt_of_le hcon (by have := OP_le_199 s.card hk; omega)
      have hsub : insert a s ⊆ (OP.filter (· ≤ a)).toFinset := by
        intro x hx
        have hxp := hS x hx
        have hxa : x ≤ a := by
          rcases mem_insert.mp hx with rfl | hx'
          · exact le_refl _
          · exact (hlt x hx').le
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨OP_complete x (by omega) hxp.1 hxp.2, by simpa using hxa⟩
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem has] at h1
      have h2 := List.toFinset_card_le (OP.filter (· ≤ a))
      have h3 := OP_count a ha200 s.card hk hcon
      omega
    calc primeProd s.card * OP[s.card]! ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul ih' hOa
      _ = a * ∏ p ∈ s, p := mul_comm _ _

/-- Odd prime factors of `b`. -/
def oddPF (b : ℕ) : Finset ℕ := b.primeFactors.filter (· ≠ 2)

lemma oddOmega_eq (b : ℕ) : oddOmega b = (oddPF b).card := rfl

lemma oddPF_prime {b p : ℕ} (hp : p ∈ oddPF b) : p.Prime ∧ p ≠ 2 := by
  unfold oddPF at hp
  rw [mem_filter, Nat.mem_primeFactors] at hp
  exact ⟨hp.1.1, hp.2⟩

lemma prod_oddPF_dvd (b : ℕ) : (∏ p ∈ oddPF b, p) ∣ b :=
  dvd_trans (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)) (Nat.prod_primeFactors_dvd b)

lemma coprime_two_prod_oddPF (b : ℕ) (n : ℕ) : Nat.Coprime (2 ^ n) (∏ p ∈ oddPF b, p) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  have := oddPF_prime hp
  exact (Nat.coprime_primes Nat.prime_two this.1).mpr (Ne.symm this.2)

/-- `W L = max {k ≤ 45 : primeProd k ≤ L}`. -/
def W (L : ℕ) : ℕ := Nat.findGreatest (fun k => primeProd k ≤ L) 45

lemma le_W {k L : ℕ} (hk : k ≤ 45) (h : primeProd k ≤ L) : k ≤ W L := Nat.le_findGreatest hk h

/-- The ρ bound used by the certificates. -/
def rhoMax (N : ℕ) : ℕ := max (2 ^ W N) (max (2 * 2 ^ W (N / 4)) (4 * 2 ^ W (N / 8)))

lemma card_oddPF_le {b L : ℕ} (hprod : (∏ p ∈ oddPF b, p) ≤ L) (hL : L < primeProd 45) :
    (oddPF b).card ≤ W L := by
  by_cases h45 : (oddPF b).card ≤ 45
  · exact le_W h45 ((primeProd_le_prod _ (fun p hp => oddPF_prime hp) h45).trans hprod)
  · -- impossible: a 45-element subset already has product ≥ primeProd 45 > L
    exfalso
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (show 45 ≤ (oddPF b).card by omega)
    have h1 := primeProd_le_prod T (fun p hp => oddPF_prime (hT hp)) (by omega)
    rw [hTc] at h1
    have h2 : (∏ p ∈ T, p) ≤ ∏ p ∈ oddPF b, p :=
      prod_le_prod_of_subset_of_one_le hT (fun p hp _ => (oddPF_prime hp).1.one_lt.le)
    omega

/-- **The ρ bound.** For `1 ≤ b ≤ N < primeProd 45`, `rhoBound b ≤ rhoMax N`. -/
theorem rhoBound_le_rhoMax {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) (hN : N < primeProd 45) :
    rhoBound b ≤ rhoMax N := by
  unfold rhoBound twoFactor rhoMax
  rw [oddOmega_eq]
  set P := ∏ p ∈ oddPF b, p
  have hb0 : b ≠ 0 := by omega
  have hPb : P ∣ b := prod_oddPF_dvd b
  split_ifs with h8 h4
  · -- 8 ∣ b: 8·P ∣ b, so P ≤ N / 8
    have : 2 ^ 3 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 3) (by simpa using h8) hPb
    have hP : P ≤ N / 8 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_le hP (by have := Nat.div_le_self N 8; omega)
    calc 4 * 2 ^ (oddPF b).card ≤ 4 * 2 ^ W (N / 8) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
  · -- 4 ∣ b
    have : 2 ^ 2 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 2) (by simpa using h4) hPb
    have hP : P ≤ N / 4 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_le hP (by have := Nat.div_le_self N 4; omega)
    calc 2 * 2 ^ (oddPF b).card ≤ 2 * 2 ^ W (N / 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · have hP : P ≤ N := (Nat.le_of_dvd (by omega) hPb).trans hbN
    have := card_oddPF_le hP hN
    calc 1 * 2 ^ (oddPF b).card ≤ 2 ^ W N := by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) this
      _ ≤ _ := le_max_left _ _

end Erdos848
