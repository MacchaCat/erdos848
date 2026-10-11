import Erdos848.ExBound2

/-!
# Phase 9.4 (part 2): local root counts (Lemma E2 of `proof.md` §10.1)

`rootSet b m = {s < b : s² m ≡ 1 (mod b)}`.  With `e = min(v₂ b, 3)` and `Q` a set of odd primes
dividing `b`,

  `|rootSet b m| ≤ 2^{ω_odd(b) - |Q|} · gLoc e Q m`,   `gLoc e Q m = |rootSet 2^e m| ∏_{q ∈ Q} |rootSet q m|`

(`card_rootSet_le_gLoc`).  Ingredients: CRT (`card_rootSet_mul_le`), odd prime powers
(`card_rootSet_oddPow_le`) and powers of two (`card_rootSet_twoPow_le`).
-/

namespace Erdos848

open Finset

/-- The local product `|rootSet 2^e m| · ∏_{q ∈ Q} |rootSet q m|`. -/
def gLoc (e : ℕ) (Q : Finset ℕ) (m : ℕ) : ℕ := (rootSet (2 ^ e) m).card * ∏ q ∈ Q, (rootSet q m).card

lemma mem_rootSet {b m s : ℕ} : s ∈ rootSet b m ↔ s < b ∧ s * s * m % b = 1 % b := by
  simp [rootSet]

lemma card_rootSet_one (m : ℕ) : (rootSet 1 m).card = 1 := by
  rw [card_eq_one]; refine ⟨0, ?_⟩; ext s; simp [rootSet]; omega

/-- **CRT.** For coprime `b₁`, `b₂`: `|rootSet (b₁ b₂) m| ≤ |rootSet b₁ m| · |rootSet b₂ m|`. -/
theorem card_rootSet_mul_le {b₁ b₂ : ℕ} (h : Nat.Coprime b₁ b₂) (m : ℕ) :
    (rootSet (b₁ * b₂) m).card ≤ (rootSet b₁ m).card * (rootSet b₂ m).card := by
  rw [← card_product]
  apply card_le_card_of_injOn (fun s => (s % b₁, s % b₂))
  · intro s hs
    simp only [coe_product, Set.mem_prod, mem_coe, mem_rootSet] at hs ⊢
    obtain ⟨hs1, hs2⟩ := hs
    have hb : 0 < b₁ * b₂ := by omega
    have hb1 : 0 < b₁ := Nat.pos_of_mul_pos_right hb
    have hb2 : 0 < b₂ := Nat.pos_of_mul_pos_left hb
    have key : ∀ d, d ∣ b₁ * b₂ → s % d * (s % d) * m % d = 1 % d := by
      intro d hd
      have e1 : s % d * (s % d) * m % d = s * s * m % d :=
        (((Nat.mod_modEq s d).mul (Nat.mod_modEq s d)).mul_right m)
      rw [e1, ← Nat.mod_mod_of_dvd (s * s * m) hd, hs2, Nat.mod_mod_of_dvd 1 hd]
    exact ⟨⟨Nat.mod_lt _ hb1, key b₁ (dvd_mul_right _ _)⟩, ⟨Nat.mod_lt _ hb2, key b₂ (dvd_mul_left _ _)⟩⟩
  · intro s hs t ht hst
    simp only [Prod.mk.injEq] at hst
    simp only [coe_filter, mem_coe, mem_rootSet] at hs ht
    have := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hst.1, hst.2⟩
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hs.1, Nat.mod_eq_of_lt ht.1] at this

lemma rhoBound_oddPrimePow {p n : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hn : 1 ≤ n) :
    rhoBound (p ^ n) = 2 := by
  unfold rhoBound twoFactor oddOmega
  have hodd : ¬ 2 ∣ p ^ n := by
    intro h; exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have h8 : ¬ 8 ∣ p ^ n := fun h => hodd (dvd_trans (by norm_num) h)
  have h4 : ¬ 4 ∣ p ^ n := fun h => hodd (dvd_trans (by norm_num) h)
  rw [if_neg h8, if_neg h4, Nat.primeFactors_prime_pow (by omega) hp, filter_singleton, if_pos h2]
  simp

lemma rhoBound_twoPow {n : ℕ} (hn : 3 ≤ n) : rhoBound (2 ^ n) = 4 := by
  unfold rhoBound twoFactor oddOmega
  have h8 : 8 ∣ 2 ^ n := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.pow_dvd_pow 2 hn
  rw [if_pos h8, Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
  simp

/-- Odd prime powers: `|rootSet p^n m| ≤ |rootSet p m|`. -/
theorem card_rootSet_oddPow_le {p n : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hn : 1 ≤ n) (m : ℕ) :
    (rootSet (p ^ n) m).card ≤ (rootSet p m).card := by
  by_cases hE : rootSet (p ^ n) m = ∅
  · rw [hE]; simp
  obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.mpr hE
  rw [mem_rootSet] at hs
  have hp2 : 3 ≤ p := by have := hp.two_le; omega
  -- reduce mod p
  have hpd : p ∣ p ^ n := dvd_pow_self p (by omega)
  have hred : s * s * m % p = 1 % p := by
    rw [← Nat.mod_mod_of_dvd (s * s * m) hpd, hs.2, Nat.mod_mod_of_dvd 1 hpd]
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  set u := s % p with hu
  have hu0 : u ≠ 0 := by
    intro h0
    have : s * s * m % p = 0 := by
      rw [Nat.mul_mod, Nat.mul_mod s s, ← hu, h0]; simp
    omega
  have hup : u < p := Nat.mod_lt _ (by omega)
  have hred' : u * u * m % p = 1 := by
    rw [← h1p, ← hred]
    exact (((Nat.mod_modEq s p).mul (Nat.mod_modEq s p)).mul_right m)
  -- `u` and `p - u` are two distinct roots mod p
  have hneg : (p - u) * (p - u) * m % p = 1 := by
    have hz : (((p - u) * (p - u) * m : ℕ) : ZMod p) = ((u * u * m : ℕ) : ZMod p) := by
      push_cast [Nat.cast_sub hup.le, ZMod.natCast_self]; ring
    rw [ZMod.natCast_eq_natCast_iff'] at hz
    rw [hz, hred']
  have hdist : p - u ≠ u := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two h2
    intro h; omega
  have htwo : 2 ≤ (rootSet p m).card := by
    have hsub : ({u, p - u} : Finset ℕ) ⊆ rootSet p m := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rw [mem_rootSet, h1p]
      rcases hx with rfl | rfl
      · exact ⟨hup, hred'⟩
      · exact ⟨by omega, hneg⟩
    have := card_le_card hsub
    rwa [card_pair hdist.symm] at this
  have hle := card_rootSet_le (p ^ n) m
  rw [rhoBound_oddPrimePow hp h2 hn] at hle
  omega

/-- Powers of two: `|rootSet 2^n m| ≤ |rootSet 2^{min(n,3)} m|`. -/
theorem card_rootSet_twoPow_le (n m : ℕ) :
    (rootSet (2 ^ n) m).card ≤ (rootSet (2 ^ min n 3) m).card := by
  by_cases hn : n ≤ 3
  · rw [min_eq_left hn]
  rw [min_eq_right (by omega)]
  by_cases hE : rootSet (2 ^ n) m = ∅
  · rw [hE]; simp
  obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.mpr hE
  rw [mem_rootSet] at hs
  have h8d : 8 ∣ 2 ^ n := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
  have h1 : 1 % 2 ^ n = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hred : s * s * m % 8 = 1 := by
    rw [← Nat.mod_mod_of_dvd (s * s * m) h8d, hs.2, h1]
  -- hence `m ≡ 1 (mod 8)`, and all four odd residues are roots mod 8
  have hm8 : m % 8 = 1 := by
    have : s * s * m % 8 = ((s % 8) * (s % 8) % 8 * (m % 8)) % 8 := by
      rw [Nat.mul_mod, Nat.mul_mod s s]
    rw [this] at hred
    have := Nat.mod_lt s (show 0 < 8 by norm_num)
    have := Nat.mod_lt m (show 0 < 8 by norm_num)
    interval_cases (s % 8) <;> interval_cases (m % 8) <;> omega
  have h4 : (rootSet (2 ^ 3) m).card = 4 := by
    have : rootSet (2 ^ 3) m = {1, 3, 5, 7} := by
      ext x
      simp only [mem_rootSet, mem_insert, mem_singleton]
      have hmm : x * x * m % 8 = (x * x % 8 * (m % 8)) % 8 := by rw [Nat.mul_mod (x * x)]
      norm_num
      rw [hmm, hm8]
      constructor
      · rintro ⟨hx, h⟩; interval_cases x <;> simp_all
      · rintro (rfl | rfl | rfl | rfl) <;> norm_num
    rw [this]; rfl
  have hle := card_rootSet_le (2 ^ n) m
  rw [rhoBound_twoPow (by omega)] at hle
  omega

/-! ### The global bound, by induction over coprime factorizations -/

lemma oddPF_one : oddPF 1 = ∅ := by simp [oddPF]

lemma oddPF_twoPow (n : ℕ) : oddPF (2 ^ n) = ∅ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [oddPF]
  · simp [oddPF, Nat.primeFactors_prime_pow (k := n) (by omega) Nat.prime_two]

lemma oddPF_oddPow {p n : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hn : 1 ≤ n) : oddPF (p ^ n) = {p} := by
  rw [oddPF, Nat.primeFactors_prime_pow (k := n) (by omega) hp, filter_singleton, if_pos h2]

lemma oddPF_mul {a c : ℕ} (h : Nat.Coprime a c) : oddPF (a * c) = oddPF a ∪ oddPF c := by
  unfold oddPF; rw [Nat.Coprime.primeFactors_mul h, filter_union]

lemma oddPF_disj {a c : ℕ} (h : Nat.Coprime a c) : Disjoint (oddPF a) (oddPF c) :=
  disjoint_filter_filter h.disjoint_primeFactors

lemma card_rootSet_twoPow_mul {x y : ℕ} (h : x = 0 ∨ y = 0) (m : ℕ) :
    (rootSet (2 ^ (x + y)) m).card = (rootSet (2 ^ x) m).card * (rootSet (2 ^ y) m).card := by
  rcases h with rfl | rfl <;> simp [card_rootSet_one]

/-- **Lemma E2, local part.** `|rootSet b m| ≤ 2^{ω_odd(b) - |Q|} · gLoc (min(v₂ b, 3)) Q m`. -/
theorem card_rootSet_le_gLoc : ∀ b, 1 ≤ b → ∀ Q ⊆ oddPF b, ∀ m,
    (rootSet b m).card ≤ 2 ^ ((oddPF b).card - Q.card) * gLoc (min (b.factorization 2) 3) Q m := by
  intro b
  induction b using Nat.recOnPrimeCoprime with
  | zero => intro h; omega
  | prime_pow p n hp =>
    intro _ Q hQ m
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, oddPF_one, subset_empty] at *
      subst hQ
      simp [gLoc, card_rootSet_one]
    by_cases h2 : p = 2
    · subst h2
      rw [oddPF_twoPow, subset_empty] at hQ
      subst hQ
      have hf2 : (2 ^ n).factorization 2 = n := by
        rw [Nat.factorization_pow]; simp [Nat.prime_two.factorization_self]
      rw [oddPF_twoPow, hf2]
      simp only [card_empty, Nat.sub_zero, pow_zero, one_mul, gLoc, prod_empty, mul_one]
      exact card_rootSet_twoPow_le n m
    · rw [oddPF_oddPow hp h2 hn] at hQ ⊢
      have hf : (p ^ n).factorization 2 = 0 := by
        rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization hp]
        simp [Ne.symm h2]
      rw [hf]
      rcases subset_singleton_iff.mp hQ with rfl | rfl
      · have hle := card_rootSet_le (p ^ n) m
        rw [rhoBound_oddPrimePow hp h2 hn] at hle
        simpa [gLoc, card_rootSet_one] using hle
      · simpa [gLoc, card_rootSet_one] using card_rootSet_oddPow_le hp h2 hn m
  | coprime a c ha hc hac iha ihc =>
    intro _ Q hQ m
    classical
    set Qa := Q.filter (· ∈ oddPF a)
    set Qc := Q.filter (· ∈ oddPF c)
    have hQac : Q = Qa ∪ Qc := by
      ext q; simp only [Qa, Qc, mem_union, mem_filter]
      constructor
      · intro hq
        have := hQ hq; rw [oddPF_mul hac, mem_union] at this
        rcases this with h | h
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
      · rintro (⟨hq, -⟩ | ⟨hq, -⟩) <;> exact hq
    have hdQ : Disjoint Qa Qc := by
      rw [disjoint_left]; intro q hqa hqc
      exact disjoint_left.mp (oddPF_disj hac) (mem_filter.mp hqa).2 (mem_filter.mp hqc).2
    have hQa : Qa ⊆ oddPF a := fun q hq => (mem_filter.mp hq).2
    have hQc : Qc ⊆ oddPF c := fun q hq => (mem_filter.mp hq).2
    have h1 := iha (by omega) Qa hQa m
    have h2 := ihc (by omega) Qc hQc m
    have hmul := card_rootSet_mul_le hac m
    -- the 2-adic exponents: at most one of a, c is even
    have hfac : (a * c).factorization 2 = a.factorization 2 + c.factorization 2 :=
      Nat.factorization_mul_apply_of_coprime hac
    have hone : a.factorization 2 = 0 ∨ c.factorization 2 = 0 := by
      by_contra hcon; push Not at hcon
      have da : 2 ∣ a := Nat.dvd_of_factorization_pos hcon.1
      have dc : 2 ∣ c := Nat.dvd_of_factorization_pos hcon.2
      have := Nat.dvd_gcd da dc
      rw [Nat.Coprime.gcd_eq_one hac] at this
      norm_num at this
    have hmin : min (a.factorization 2 + c.factorization 2) 3 =
        min (a.factorization 2) 3 + min (c.factorization 2) 3 := by omega
    have hg : gLoc (min ((a * c).factorization 2) 3) Q m =
        gLoc (min (a.factorization 2) 3) Qa m * gLoc (min (c.factorization 2) 3) Qc m := by
      unfold gLoc
      rw [hfac, hmin, card_rootSet_twoPow_mul (by omega) m, hQac, prod_union hdQ]; ring
    have hcardQ : Q.card = Qa.card + Qc.card := by rw [hQac, card_union_of_disjoint hdQ]
    have hcardP : (oddPF (a * c)).card = (oddPF a).card + (oddPF c).card := by
      rw [oddPF_mul hac, card_union_of_disjoint (oddPF_disj hac)]
    have hQa' := card_le_card hQa
    have hQc' := card_le_card hQc
    have hexp : (oddPF (a * c)).card - Q.card =
        ((oddPF a).card - Qa.card) + ((oddPF c).card - Qc.card) := by omega
    rw [hg, hexp, pow_add]
    calc (rootSet (a * c) m).card ≤ (rootSet a m).card * (rootSet c m).card := hmul
      _ ≤ (2 ^ ((oddPF a).card - Qa.card) * gLoc (min (a.factorization 2) 3) Qa m) *
          (2 ^ ((oddPF c).card - Qc.card) * gLoc (min (c.factorization 2) 3) Qc m) :=
          Nat.mul_le_mul h1 h2
      _ = _ := by ring

/-! ### Lemma E2 -/

/-- **Lemma E2.** If the partial sums of `gLoc e Q` satisfy `G(R) ≤ αR + β` (`e = min(v₂ b, 3)`,
`Q` odd primes of `b`), then
`#Ex(b) ≤ 2^{ω_odd(b) - |Q|} (α((N+1)/Y + M) + β(⌊√(Nb+1)⌋/b + 1))`. -/
theorem card_exSet_le_E2 (N b Y : ℕ) (hb : 1 ≤ b) (hY : 1 ≤ Y) (Q : Finset ℕ) (hQ : Q ⊆ oddPF b)
    (α β : ℝ) (hα : 0 ≤ α)
    (hG : ∀ R, ∑ m ∈ Icc 1 R, (gLoc (min (b.factorization 2) 3) Q m : ℝ) ≤ α * R + β) :
    ((exSet N b Y).card : ℝ) ≤ (2 : ℝ) ^ ((oddPF b).card - Q.card) *
      (α * (((N : ℝ) + 1) / Y + exM N b Y) + β * (((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1)) := by
  set c : ℝ := (2 : ℝ) ^ ((oddPF b).card - Q.card)
  set g : ℕ → ℝ := fun m => (gLoc (min (b.factorization 2) 3) Q m : ℝ)
  have h0 := card_exSet_le_E0 N b Y hb
  have h1 : ∑ m ∈ Icc 1 (exM N b Y), ((rootSet b m).card : ℝ) * fE N b Y m ≤
      c * ∑ m ∈ Icc 1 (exM N b Y), g m * fE N b Y m := by
    rw [mul_sum]
    apply sum_le_sum; intro m hm
    rw [mem_Icc] at hm
    have hle : ((rootSet b m).card : ℝ) ≤ c * g m := by
      have := card_rootSet_le_gLoc b hb Q hQ m
      simp only [c, g]; exact_mod_cast this
    have := fE_nonneg (N := N) (Y := Y) hb hm.1 hm.2
    nlinarith
  have hB0 : (0 : ℝ) ≤ ((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1 := by positivity
  have h2 := abel_le g (fE N b Y) α β (((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1) (exM N b Y)
    (fun R _ => hG R) (fun m h1 h2 => fE_nonneg hb h1 h2)
    (fun m h1 _ => fE_anti hb h1 (Nat.le_succ m)) (fE_one_le N b Y hb) hB0
  have h3 := sum_fE_le N b Y hb hY
  have hc : 0 ≤ c := by positivity
  have h4 : α * ∑ m ∈ Icc 1 (exM N b Y), fE N b Y m ≤ α * (((N : ℝ) + 1) / Y + exM N b Y) :=
    mul_le_mul_of_nonneg_left h3 hα
  have h5 : ∑ m ∈ Icc 1 (exM N b Y), g m * fE N b Y m ≤
      α * (((N : ℝ) + 1) / Y + exM N b Y) + β * (((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1) := by
    linarith
  have := mul_le_mul_of_nonneg_left h5 hc
  linarith

end Erdos848
