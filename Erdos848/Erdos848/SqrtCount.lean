import Mathlib

/-!
# Phase 4 (part 1): counting square roots modulo `b`

`sqrtCount b c = #{x ∈ [0,b) : x² ≡ c (mod b)}`.

* `sqrtCount_mul_le`: for coprime `b₁, b₂`, `sqrtCount (b₁ b₂) c ≤ sqrtCount b₁ c · sqrtCount b₂ c`
  (reduction mod `b₁` and mod `b₂` is injective on `[0, b₁ b₂)`).
* `sqrtCount_oddPrimePow_le`: for an odd prime `p` with `p ∤ c`, `sqrtCount (p^e) c ≤ 2`
  (if `x² ≡ y²` then `p^e ∣ (x−y)(x+y)`, and `p` cannot divide both factors).
-/

namespace Erdos848

open Finset

def sqrtCount (b c : ℕ) : ℕ := ((range b).filter (fun x => x * x % b = c % b)).card

theorem sqrtCount_mul_le {b₁ b₂ : ℕ} (h : Nat.Coprime b₁ b₂) (c : ℕ) :
    sqrtCount (b₁ * b₂) c ≤ sqrtCount b₁ c * sqrtCount b₂ c := by
  unfold sqrtCount
  rw [← card_product]
  apply card_le_card_of_injOn (fun x => (x % b₁, x % b₂))
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hx
    have hb₁ : 0 < b₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
    have hb₂ : 0 < b₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
    have hmod := hx.2
    simp only [coe_product, coe_filter, Set.mem_prod, Set.mem_ofPred_eq, mem_range]
    refine ⟨⟨Nat.mod_lt _ hb₁, ?_⟩, ⟨Nat.mod_lt _ hb₂, ?_⟩⟩
    · have : x * x % b₁ = c % b₁ := by
        have := congrArg (· % b₁) hmod
        simpa [Nat.mod_mod_of_dvd _ (dvd_mul_right b₁ b₂)] using this
      rw [← Nat.mul_mod]; exact this
    · have : x * x % b₂ = c % b₂ := by
        have := congrArg (· % b₂) hmod
        simpa [Nat.mod_mod_of_dvd _ (dvd_mul_left b₂ b₁)] using this
      rw [← Nat.mul_mod]; exact this
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have h1 : x ≡ y [MOD b₁] := hxy.1
    have h2 : x ≡ y [MOD b₂] := hxy.2
    have h12 : x ≡ y [MOD b₁ * b₂] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1, h2⟩
    unfold Nat.ModEq at h12
    rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h12

theorem sqrtCount_oddPrimePow_le {p e c : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpc : ¬ p ∣ c) :
    sqrtCount (p ^ e) c ≤ 2 := by
  unfold sqrtCount
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [pow_zero]
    calc ((range 1).filter (fun x => x * x % 1 = c % 1)).card ≤ (range 1).card := card_filter_le _ _
      _ ≤ 2 := by simp
  set P := p ^ e with hP
  set S := (range P).filter (fun x => x * x % P = c % P)
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hS
  have hPpos : 0 < P := pow_pos hp.pos e
  have hpP : p ∣ P := dvd_pow_self p he.ne'
  -- solutions are not divisible by p
  have hnd : ∀ z, z * z % P = c % P → ¬ p ∣ z := by
    intro z hz hpz
    apply hpc
    have h2 : (z * z) % P % p = c % P % p := by rw [hz]
    rw [Nat.mod_mod_of_dvd _ hpP, Nat.mod_mod_of_dvd _ hpP] at h2
    exact Nat.dvd_of_mod_eq_zero (h2 ▸ Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpz z))
  simp only [S, mem_filter, mem_range] at hx₀
  have hx0 := hnd x₀ hx₀.2
  have key : ∀ y ∈ S, y = x₀ ∨ y = P - x₀ := by
    intro y hy
    simp only [S, mem_filter, mem_range] at hy
    -- (P : ℤ) ∣ (x₀ - y)(x₀ + y)
    have hmod : y * y ≡ x₀ * x₀ [MOD P] := by unfold Nat.ModEq; rw [hx₀.2, hy.2]
    have hdvd : (P : ℤ) ∣ ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      push_cast at this
      have e1 : ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) = (x₀ : ℤ) * x₀ - y * y := by ring
      rw [e1]; exact this
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    -- p cannot divide both factors
    have hnot : ¬ ((p : ℤ) ∣ (x₀ : ℤ) - y ∧ (p : ℤ) ∣ (x₀ : ℤ) + y) := by
      rintro ⟨h1, h2⟩
      have h3 : (p : ℤ) ∣ 2 * (x₀ : ℤ) := by
        have := dvd_add h1 h2; rw [show (x₀ : ℤ) - y + (x₀ + y) = 2 * x₀ by ring] at this; exact this
      rcases hpZ.dvd_or_dvd h3 with h4 | h4
      · have : p ∣ 2 := by exact_mod_cast h4
        exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact hx0 (by exact_mod_cast h4)
    have hPZ : (P : ℤ) = (p : ℤ) ^ e := by rw [hP]; push_cast; ring
    by_cases hu : (p : ℤ) ∣ (x₀ : ℤ) - y
    · -- then p ∤ x₀ + y, so P ∣ x₀ - y, hence y = x₀
      have hv : ¬ (p : ℤ) ∣ (x₀ : ℤ) + y := fun hv => hnot ⟨hu, hv⟩
      have hcop : IsCoprime ((p : ℤ) ^ e) ((x₀ : ℤ) + y) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hv)
      have : (P : ℤ) ∣ (x₀ : ℤ) - y := by
        rw [hPZ] at hdvd ⊢; exact hcop.dvd_of_dvd_mul_right hdvd
      left
      have hlt : |(x₀ : ℤ) - y| < (P : ℤ) := by
        rw [abs_lt]; constructor <;> push_cast <;> omega
      have := Int.eq_zero_of_abs_lt_dvd this hlt
      omega
    · -- P ∣ x₀ + y, and 0 < x₀ + y < 2P, so y = P - x₀
      have hcop : IsCoprime ((p : ℤ) ^ e) ((x₀ : ℤ) - y) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hu)
      have h1 : (P : ℤ) ∣ (x₀ : ℤ) + y := by
        rw [hPZ] at hdvd ⊢; exact hcop.dvd_of_dvd_mul_left hdvd
      have h2 : P ∣ x₀ + y := by exact_mod_cast h1
      right
      obtain ⟨k, hk⟩ := h2
      have hx0pos : 0 < x₀ := Nat.pos_of_ne_zero (fun h => hx0 (h ▸ dvd_zero p))
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
  calc S.card ≤ ({x₀, P - x₀} : Finset ℕ).card := by
        apply card_le_card; intro y hy
        rcases key y hy with h | h <;> simp [h]
    _ ≤ 2 := card_le_two


/-- Two odd numbers whose squares agree modulo `2^e` (`e ≥ 3`) agree up to sign modulo `2^(e-1)`. -/
lemma two_pow_sq_eq {e : ℕ} (he : 3 ≤ e) {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : (2 : ℤ) ^ e ∣ (x - y) * (x + y)) :
    (2 : ℤ) ^ (e - 1) ∣ x - y ∨ (2 : ℤ) ^ (e - 1) ∣ x + y := by
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ x - y := Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ x + y := Int.dvd_of_emod_eq_zero (by omega)
  have hsum : u + v = x := by linarith
  have h4 : (2 : ℤ) ^ e = 2 * 2 * 2 ^ (e - 2) := by
    conv_lhs => rw [show e = (e - 2) + 2 from by omega]
    rw [pow_add]; ring
  have hdvd : (2 : ℤ) ^ (e - 2) ∣ u * v := by
    rw [hu, hv, h4] at h
    have : (2 * 2 * 2 ^ (e - 2) : ℤ) ∣ 2 * 2 * (u * v) := by
      rw [show (2 : ℤ) * u * (2 * v) = 2 * 2 * (u * v) by ring] at h; exact h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 * 2 : ℤ) ≠ 0)).mp this
  have hodd2 : ∀ w : ℤ, w % 2 = 1 → IsCoprime ((2 : ℤ) ^ (e - 2)) w := by
    intro w hw
    apply IsCoprime.pow_left
    exact (Prime.coprime_iff_not_dvd Int.prime_two).mpr (by omega)
  have hpow : (2 : ℤ) ^ (e - 1) = 2 * 2 ^ (e - 2) := by
    rw [← pow_succ']; congr 1; omega
  rcases Int.emod_two_eq_zero_or_one u with hu0 | hu1
  · -- u even ⇒ v odd ⇒ 2^(e-2) ∣ u ⇒ 2^(e-1) ∣ 2u = x - y
    have hv1 : v % 2 = 1 := by omega
    have := (hodd2 v hv1).dvd_of_dvd_mul_right hdvd
    left; rw [hu, hpow]; exact mul_dvd_mul_left 2 this
  · -- u odd ⇒ 2^(e-2) ∣ v ⇒ 2^(e-1) ∣ 2v = x + y
    have := (hodd2 u hu1).dvd_of_dvd_mul_left hdvd
    right; rw [hv, hpow]; exact mul_dvd_mul_left 2 this

/-- Modulo `2^e`, an odd number has at most 4 square roots. -/
theorem sqrtCount_twoPow_le {e c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ e) c ≤ 4 := by
  unfold sqrtCount
  rcases Nat.lt_or_ge e 3 with he | he
  · calc ((range (2 ^ e)).filter (fun x => x * x % 2 ^ e = c % 2 ^ e)).card ≤ (range (2 ^ e)).card :=
          card_filter_le _ _
      _ = 2 ^ e := card_range _
      _ ≤ 4 := by interval_cases e <;> norm_num
  set P := 2 ^ e with hP
  set Q := 2 ^ (e - 1) with hQ
  have hPQ : P = 2 * Q := by rw [hP, hQ, ← pow_succ']; congr 1; omega
  have hQpos : 0 < Q := pow_pos (by norm_num) _
  set S := (range P).filter (fun x => x * x % P = c % P)
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hS
  have h2P : 2 ∣ P := by rw [hPQ]; exact dvd_mul_right 2 Q
  have hoddsol : ∀ z, z * z % P = c % P → z % 2 = 1 := by
    intro z hz
    have h2 : (z * z) % P % 2 = c % P % 2 := by rw [hz]
    rw [Nat.mod_mod_of_dvd _ h2P, Nat.mod_mod_of_dvd _ h2P, hc] at h2
    rcases Nat.mod_two_eq_zero_or_one z with h | h
    · rw [Nat.mul_mod, h] at h2; simp at h2
    · exact h
  simp only [S, mem_filter, mem_range] at hx₀
  have hx0o := hoddsol x₀ hx₀.2
  -- every solution y has y % Q ∈ {x₀ % Q, (Q - x₀ % Q) % Q}
  have key : ∀ y ∈ S, y % Q = x₀ % Q ∨ (y + x₀) % Q = 0 := by
    intro y hy
    simp only [S, mem_filter, mem_range] at hy
    have hyo := hoddsol y hy.2
    have hmod : y * y ≡ x₀ * x₀ [MOD P] := by unfold Nat.ModEq; rw [hx₀.2, hy.2]
    have hdvd : ((2 : ℤ) ^ e) ∣ ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      rw [hP] at this; push_cast at this
      have e1 : ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) = (x₀ : ℤ) * x₀ - y * y := by ring
      rw [e1]; exact this
    have hQZ : ((Q : ℕ) : ℤ) = (2 : ℤ) ^ (e - 1) := by rw [hQ]; push_cast; ring
    rcases two_pow_sq_eq he (by omega) (by omega) hdvd with h1 | h1
    · left
      have : ((Q : ℕ) : ℤ) ∣ (x₀ : ℤ) - y := by rw [hQZ]; exact h1
      exact (Nat.modEq_iff_dvd).mpr this
    · right
      have : ((Q : ℕ) : ℤ) ∣ (x₀ : ℤ) + y := by rw [hQZ]; exact h1
      have h2 : Q ∣ y + x₀ := by
        have : ((Q : ℕ) : ℤ) ∣ ((y + x₀ : ℕ) : ℤ) := by push_cast; rwa [add_comm]
        exact_mod_cast this
      exact Nat.mod_eq_zero_of_dvd h2
  -- so y lies in a set of size ≤ 4
  set r₁ := x₀ % Q
  set r₂ := (Q - x₀ % Q) % Q
  calc S.card ≤ ({r₁, r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card := by
        apply card_le_card
        intro y hy
        have hyP : y < P := by simp only [S, mem_filter, mem_range] at hy; exact hy.1
        have hr1 : r₁ < Q := Nat.mod_lt _ hQpos
        rcases key y hy with h | h
        · -- y ≡ r₁ (mod Q), y < 2Q
          have : y = r₁ ∨ y = r₁ + Q := by
            have := Nat.div_add_mod y Q
            have hq : y / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            interval_cases hyq : y / Q <;> omega
          rcases this with h' | h' <;> simp [h']
        · -- y + x₀ ≡ 0 (mod Q) ⇒ y ≡ r₂ (mod Q)
          have hy2 : y % Q = r₂ := by
            have ha : y % Q < Q := Nat.mod_lt _ hQpos
            have hb : x₀ % Q < Q := Nat.mod_lt _ hQpos
            rw [Nat.add_mod] at h
            have hdm := Nat.div_add_mod (y % Q + x₀ % Q) Q
            rw [h] at hdm
            have hq : (y % Q + x₀ % Q) / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            simp only [r₂]
            interval_cases hq' : (y % Q + x₀ % Q) / Q
            · -- both residues are 0
              have h0 : x₀ % Q = 0 := by omega
              have h0' : y % Q = 0 := by omega
              rw [h0, h0', Nat.sub_zero, Nat.mod_self]
            · -- residues sum to Q
              rcases Nat.eq_zero_or_pos (x₀ % Q) with h0 | h0
              · rw [h0, Nat.sub_zero, Nat.mod_self]; omega
              · rw [Nat.mod_eq_of_lt (show Q - x₀ % Q < Q by omega)]; omega
          have : y = r₂ ∨ y = r₂ + Q := by
            have := Nat.div_add_mod y Q
            have hq : y / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            interval_cases hyq : y / Q <;> omega
          rcases this with h' | h' <;> simp [h']
    _ ≤ 4 := by
        calc ({r₁, r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card
            ≤ ({r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card + 1 := card_insert_le _ _
          _ ≤ (({r₂, r₂ + Q} : Finset ℕ).card + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ ≤ ((({r₂ + Q} : Finset ℕ).card + 1) + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ = 4 := by simp

/-- Modulo `2`, an odd number has exactly one square root. -/
lemma sqrtCount_two_le {c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ 1) c ≤ 1 := by
  unfold sqrtCount; rw [pow_one, hc]; decide

/-- Modulo `4`, an odd number has at most two square roots. -/
lemma sqrtCount_four_le {c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ 2) c ≤ 2 := by
  unfold sqrtCount
  have : c % 4 = 1 ∨ c % 4 = 3 := by omega
  norm_num
  rcases this with h | h <;> rw [h] <;> decide

/-- Number of odd prime factors. -/
def oddOmega (b : ℕ) : ℕ := (b.primeFactors.filter (· ≠ 2)).card

/-- The 2-adic factor: `4` if `8 ∣ b`, `2` if `4 ∣ b` but `8 ∤ b`, otherwise `1`. -/
def twoFactor (b : ℕ) : ℕ := if 8 ∣ b then 4 else if 4 ∣ b then 2 else 1

/-- The bound `twoFactor b · 2^(number of odd prime factors)`. -/
def rhoBound (b : ℕ) : ℕ := twoFactor b * 2 ^ oddOmega b

lemma oddOmega_mul {a b : ℕ} (h : Nat.Coprime a b) : oddOmega (a * b) = oddOmega a + oddOmega b := by
  unfold oddOmega
  rw [Nat.Coprime.primeFactors_mul h, filter_union]
  exact card_union_of_disjoint (disjoint_filter_filter h.disjoint_primeFactors)

lemma twoFactor_mul {a b : ℕ} (h : Nat.Coprime a b) : twoFactor a * twoFactor b = twoFactor (a * b) := by
  -- at most one of a, b is even
  have h2 : ¬ (2 ∣ a ∧ 2 ∣ b) := by
    rintro ⟨ha, hb⟩
    have := Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.coprime_dvd_right hb h)
    norm_num at this
  have key : ∀ x y : ℕ, ¬ 2 ∣ x → twoFactor x * twoFactor y = twoFactor (x * y) := by
    intro x y hx
    have hx8 : ¬ 8 ∣ x := fun h8 => hx (dvd_trans (by norm_num) h8)
    have hx4 : ¬ 4 ∣ x := fun h4 => hx (dvd_trans (by norm_num) h4)
    have c8 : Nat.Coprime 8 x := Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
    have c4 : Nat.Coprime 4 x := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
    have e8 : 8 ∣ x * y ↔ 8 ∣ y := ⟨fun h => c8.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h x⟩
    have e4 : 4 ∣ x * y ↔ 4 ∣ y := ⟨fun h => c4.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h x⟩
    unfold twoFactor
    simp only [hx8, hx4, ite_false, one_mul, e8, e4]
  by_cases ha : 2 ∣ a
  · have hb : ¬ 2 ∣ b := fun hb => h2 ⟨ha, hb⟩
    rw [mul_comm, mul_comm a b]; exact key b a hb
  · exact key a b ha

lemma rhoBound_mul {a b : ℕ} (h : Nat.Coprime a b) : rhoBound a * rhoBound b = rhoBound (a * b) := by
  unfold rhoBound
  rw [oddOmega_mul h, pow_add, ← twoFactor_mul h]; ring

/-- **Square roots modulo `b`.** If `gcd(c, b) = 1`, then `x² ≡ c (mod b)` has at most
`rhoBound b` solutions in `[0, b)`. -/
theorem sqrtCount_le_rhoBound : ∀ b c, Nat.Coprime c b → sqrtCount b c ≤ rhoBound b := by
  intro b
  induction b using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro c hc
    rcases eq_or_ne p 2 with rfl | hp2
    · have hodd : c % 2 = 1 := by
        have : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 hn.ne') hc
        rcases Nat.mod_two_eq_zero_or_one c with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) (by
            intro h2; have := Nat.Coprime.coprime_dvd_left h2 this; norm_num at this)
        · exact h
      have hω : oddOmega (2 ^ n) = 0 := by
        unfold oddOmega; rw [Nat.primeFactors_prime_pow hn.ne' Nat.prime_two]; simp
      unfold rhoBound; rw [hω, pow_zero, mul_one]
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
      · subst h1; calc sqrtCount (2 ^ 1) c ≤ 1 := sqrtCount_two_le hodd
          _ = twoFactor (2 ^ 1) := by decide
      · subst h2; calc sqrtCount (2 ^ 2) c ≤ 2 := sqrtCount_four_le hodd
          _ = twoFactor (2 ^ 2) := by decide
      · calc sqrtCount (2 ^ n) c ≤ 4 := sqrtCount_twoPow_le hodd
          _ = twoFactor (2 ^ n) := by
            unfold twoFactor
            have : 8 ∣ 2 ^ n := by
              have : (8 : ℕ) = 2 ^ 3 := by norm_num
              rw [this]; exact Nat.pow_dvd_pow 2 h3
            simp [this]
    · have hpc : ¬ p ∣ c := by
        intro h
        have : p ∣ Nat.gcd c (p ^ n) := Nat.dvd_gcd h (dvd_pow_self p hn.ne')
        rw [hc] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      calc sqrtCount (p ^ n) c ≤ 2 := sqrtCount_oddPrimePow_le hp hp2 hpc
        _ = rhoBound (p ^ n) := by
          unfold rhoBound oddOmega
          rw [Nat.primeFactors_prime_pow hn.ne' hp]
          have h2 : ¬ 2 ∣ p ^ n := by
            intro h
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
            exact hp2 this.symm
          have h8 : ¬ 8 ∣ p ^ n := fun h8 => h2 (dvd_trans (by norm_num) h8)
          have h4 : ¬ 4 ∣ p ^ n := fun h4 => h2 (dvd_trans (by norm_num) h4)
          simp [twoFactor, h8, h4, Finset.filter_singleton, hp2]
  | zero => intro c _; simp [sqrtCount]
  | one =>
    intro c _
    unfold sqrtCount rhoBound oddOmega twoFactor
    calc ((range 1).filter (fun x => x * x % 1 = c % 1)).card ≤ (range 1).card := card_filter_le _ _
      _ = 1 := by simp
      _ ≤ _ := by simp
  | coprime a b ha hb hab iha ihb =>
    intro c hc
    calc sqrtCount (a * b) c ≤ sqrtCount a c * sqrtCount b c := sqrtCount_mul_le hab c
      _ ≤ rhoBound a * rhoBound b := Nat.mul_le_mul
          (iha c (Nat.Coprime.coprime_mul_right_right hc)) (ihb c (Nat.Coprime.coprime_mul_left_right hc))
      _ = rhoBound (a * b) := rhoBound_mul hab

end Erdos848
