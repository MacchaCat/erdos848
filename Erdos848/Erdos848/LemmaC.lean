import Erdos848.Sieve

/-!
# Phase 6 (part 2): Lemma C (sieving `A*` by an even witness)

For an odd prime `p₂ ≠ 5`, `xSet N b p₂ z₁` is the set of `x ≤ N`, `x ≢ ±7 (25)`, with
`p₂² ∣ x b + 1` and `p² ∣ x² + 1` for a U1 prime `p ≤ z₁`.  We prove (`card_xSet_le`)

  `#xSet ≤ (23/25)(N/p₂²) + 3`                                  if `p₂² ∣ b² + 1`,
  `#xSet ≤ (23/25)(N/p₂²)(1 - ∏_{U∖p₂}(1 - 2/p²)) + 3(3^{|U∖p₂|} - 1)`   otherwise,

where `U` is the set of U1 primes `≤ z₁` ("all classes minus the classes 7 and 18 mod 25").
-/

namespace Erdos848

open Finset

/-! ### Small tools -/

/-- CRT: the classes `a (mod m)` and `c (mod n)` combine into one class mod `m n`. -/
lemma crt_class {m n a c : ℕ} (h : Nat.Coprime m n) (ha : a < m) (hc : c < n) :
    ∃ t < m * n, ∀ x, x % (m * n) = t ↔ x % m = a ∧ x % n = c := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h a c
  have hmn : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  refine ⟨k % (m * n), Nat.mod_lt _ hmn, fun x => ?_⟩
  have e : x % (m * n) = k % (m * n) ↔ x ≡ k [MOD m] ∧ x ≡ k [MOD n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul h).symm
  rw [e]
  unfold Nat.ModEq at hk1 hk2 ⊢
  rw [hk1, hk2, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]

/-- If `X`, `B`, `C` are pairwise disjoint subsets of `A`, then `|X| + |B| + |C| ≤ |A|`. -/
lemma card_three_le {A X B C : Finset ℕ} (hX : X ⊆ A) (hB : B ⊆ A) (hC : C ⊆ A)
    (hXB : Disjoint X B) (hXC : Disjoint X C) (hBC : Disjoint B C) :
    X.card + B.card + C.card ≤ A.card := by
  rw [← card_union_of_disjoint hXB, ← card_union_of_disjoint (disjoint_union_left.mpr ⟨hXC, hBC⟩)]
  exact card_le_card (union_subset (union_subset hX hB) hC)

/-- If `p² ∣ c b + 1` and `p² ∣ c² + 1` then `p² ∣ b² + 1`. -/
lemma sq_dvd_of_roots {p b c : ℕ} (h1 : p * p ∣ c * b + 1) (h2 : p * p ∣ c * c + 1) :
    p * p ∣ b * b + 1 := by
  have e1 := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr h1
  have e2 := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr h2
  apply (ZMod.natCast_eq_zero_iff _ (p * p)).mp
  push_cast at e1 e2 ⊢
  linear_combination ((b : ZMod (p * p)) * b) * e2 - ((c : ZMod (p * p)) * b - 1) * e1

/-- Monotonicity of the inclusion–exclusion main and error terms in the root counts. -/
lemma ie_mono (P : Finset ℕ) (Rs : ℕ → Finset ℕ) (c : ℕ) (hc : c ≤ 4)
    (hP : ∀ p ∈ P, p.Prime) (hRc : ∀ p ∈ P, (Rs p).card ≤ c) :
    (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
        1 - ∏ p ∈ P, (1 - (c : ℝ) / (p * p)) ∧
      ∏ p ∈ P, (1 + ((Rs p).card : ℝ)) ≤ ((1 + c : ℕ) : ℝ) ^ P.card := by
  constructor
  · have : ∏ p ∈ P, (1 - (c : ℝ) / (p * p)) ≤
        ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) := by
      apply prod_le_prod₀
      · intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
        have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
        rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
      · intro p hp
        have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hp
        push_cast
        have : (0 : ℝ) < p * p := by have := (hP p hp).pos; positivity
        gcongr
    linarith
  · rw [← prod_const]
    apply prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hp
      push_cast; linarith

/-! ### The term of one prime `p₂` -/

/-- `x ≤ N`, `x ≢ ±7 (25)`, `p₂² ∣ x b + 1`, and `p² ∣ x² + 1` for a U1 prime `p ≤ z₁`. -/
def xSet (N b p₂ z₁ : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => IsStar x ∧ x % (p₂ * p₂) ∈ witRoots b p₂ ∧
    ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

/-- The bound for a prime `p₂ ∉ S_b` (sieve by the U1 primes `≤ z₁` other than `p₂`). -/
noncomputable def nonB (N p₂ z₁ : ℕ) : ℝ :=
  23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) *
      (1 - ∏ p ∈ (smallP z₁ IsU1).erase p₂, (1 - 2 / ((p : ℝ) * p))) +
    3 * ((3 : ℝ) ^ ((smallP z₁ IsU1).erase p₂).card - 1)

/-- The bound for a prime `p₂ ∈ S_b` (whole class). -/
noncomputable def wholeB (N p₂ : ℕ) : ℝ := 23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) + 3

lemma prod_one_sub_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, (1 - 2 / ((p : ℝ) * p)) ≤ 1 := by
  apply prod_le_one₀
  · intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  · intro p _; have : 0 ≤ 2 / ((p : ℝ) * p) := by positivity
    linarith

lemma nonB_nonneg (N p₂ z₁ : ℕ) : 0 ≤ nonB N p₂ z₁ := by
  unfold nonB
  have h1 := prod_one_sub_le_one ((smallP z₁ IsU1).erase p₂)
    (fun p hp => (mem_filter.mp (mem_of_mem_erase hp)).2.1)
  have h2 : (1 : ℝ) ≤ 3 ^ ((smallP z₁ IsU1).erase p₂).card := one_le_pow₀ (by norm_num)
  have : 0 ≤ (N : ℝ) / ((p₂ : ℝ) * p₂) := by positivity
  have : 0 ≤ 23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) * (1 - ∏ p ∈ (smallP z₁ IsU1).erase p₂,
      (1 - 2 / ((p : ℝ) * p))) := by
    apply mul_nonneg (by positivity); linarith
  linarith

lemma wholeB_nonneg (N p₂ : ℕ) : 0 ≤ wholeB N p₂ := by unfold wholeB; positivity

lemma coprime_25_sq {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 (p * p) :=
  coprime_sq_of_primes Nat.prime_five hp (Ne.symm h5)

/-- **The term of `p₂`** (odd prime `p₂ ≠ 5`). -/
theorem card_xSet_le (N b p₂ z₁ : ℕ) (hp₂ : p₂.Prime) (h5 : p₂ ≠ 5) :
    ((xSet N b p₂ z₁).card : ℝ) ≤
      if p₂ * p₂ ∣ b * b + 1 then wholeB N p₂ else nonB N p₂ z₁ := by
  classical
  by_cases hW : witRoots b p₂ = ∅
  · have : xSet N b p₂ z₁ = ∅ := by
      rw [xSet, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]
    split_ifs
    · exact wholeB_nonneg N p₂
    · exact nonB_nonneg N p₂ z₁
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hpp : 0 < p₂ * p₂ := Nat.mul_pos hp₂.pos hp₂.pos
  have hc_lt : c < p₂ * p₂ := mem_range.mp (witRoots_sub b p₂ hcW)
  have hcdvd : p₂ * p₂ ∣ c * b + 1 := (mem_filter.mp hcW).2
  have huniq : ∀ x, x % (p₂ * p₂) ∈ witRoots b p₂ → x % (p₂ * p₂) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le hp₂) _ hx _ hcW
  have hcop25 := coprime_25_sq hp₂ h5
  obtain ⟨t7, ht7, H7⟩ := crt_class hcop25 (a := 7) (by norm_num) hc_lt
  obtain ⟨t18, ht18, H18⟩ := crt_class hcop25 (a := 18) (by norm_num) hc_lt
  have hQ : ((25 * (p₂ * p₂) : ℕ) : ℝ) = 25 * ((p₂ : ℝ) * p₂) := by push_cast; ring
  have hQ' : ((p₂ * p₂ : ℕ) : ℝ) = (p₂ : ℝ) * p₂ := by push_cast; ring
  have hp2R : (0 : ℝ) < (p₂ : ℝ) * p₂ := by have := hp₂.pos; positivity
  have hNdiv : (N : ℝ) / (25 * ((p₂ : ℝ) * p₂)) = (N : ℝ) / ((p₂ : ℝ) * p₂) / 25 := by
    rw [div_div, mul_comm]
  split_ifs with hsq
  · -- whole class
    set A := (Icc 1 N).filter (fun x => x % (p₂ * p₂) = c)
    set B7 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t7)
    set B18 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t18)
    have h3 := card_three_le (A := A) (X := xSet N b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSet, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, huniq x hx.2.2.1⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2).2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2).2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2).1; have := ((H18 x).mp hb.2).1; omega)
    have hA := card_mod_eq_real N (p₂ * p₂) c hpp hc_lt
    have hB7 := card_mod_eq_real N (25 * (p₂ * p₂)) t7 (by omega) ht7
    have hB18 := card_mod_eq_real N (25 * (p₂ * p₂)) t18 (by omega) ht18
    rw [hQ'] at hA; rw [hQ, hNdiv] at hB7 hB18
    rw [abs_le] at hA hB7 hB18
    have h3R : ((xSet N b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    unfold wholeB
    linarith [hA.2, hB7.1, hB18.1]
  · -- sieve by U ∖ {p₂}
    set U' := (smallP z₁ IsU1).erase p₂
    have hU' : ∀ p ∈ U', p.Prime ∧ IsU1 p ∧ p ≠ p₂ := by
      intro p hp
      have := mem_erase.mp hp
      exact ⟨(mem_filter.mp this.2).2.1, (mem_filter.mp this.2).2.2, this.1⟩
    set A := (Icc 1 N).filter (fun x => x % (p₂ * p₂) = c ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    set B7 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t7 ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    set B18 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t18 ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    have h3 := card_three_le (A := A) (X := xSet N b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSet, mem_filter] at hx; simp only [A, mem_filter]
        obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
        have hxc := huniq x hxW
        refine ⟨hx1, hxc, p, ?_, hpR⟩
        have hne : p ≠ p₂ := by
          rintro rfl
          rw [hxc] at hpR
          exact hsq (sq_dvd_of_roots hcdvd (mem_filter.mp hpR).2)
        exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2.1).2, hx.2.2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2.1).2, hx.2.2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2.1).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2.1).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2.1).1; have := ((H18 x).mp hb.2.1).1; omega)
    have hm : ∀ p ∈ U', 0 < (fun p => p * p) p := fun p hp =>
      Nat.mul_pos (hU' p hp).1.pos (hU' p hp).1.pos
    have hR : ∀ p ∈ U', ∀ r ∈ (fun p => sqRoots p) p, r < (fun p => p * p) p :=
      fun p _ r hr => mem_range.mp (sqRoots_sub p hr)
    have hcp : ∀ p ∈ U', ∀ p' ∈ U', p ≠ p' →
        Nat.Coprime ((fun p => p * p) p) ((fun p => p * p) p') := fun p hp p' hp' hne =>
      coprime_sq_of_primes (hU' p hp).1 (hU' p' hp').1 hne
    have hcq1 : ∀ p ∈ U', Nat.Coprime (p₂ * p₂) ((fun p => p * p) p) := fun p hp =>
      coprime_sq_of_primes hp₂ (hU' p hp).1 (Ne.symm (hU' p hp).2.2)
    have hcq2 : ∀ p ∈ U', Nat.Coprime (25 * (p₂ * p₂)) ((fun p => p * p) p) := fun p hp =>
      Nat.coprime_mul_iff_left.mpr ⟨coprime_25_sq (hU' p hp).1
        (by have := (hU' p hp).2.1.2.2; omega), hcq1 p hp⟩
    have hA := card_union_le N (p₂ * p₂) c (fun p => p * p) (fun p => sqRoots p) U' hpp hc_lt
      hm hR hcq1 hcp
    have hB7 := card_union_ge N (25 * (p₂ * p₂)) t7 (fun p => p * p) (fun p => sqRoots p) U'
      (by omega) ht7 hm hR hcq2 hcp
    have hB18 := card_union_ge N (25 * (p₂ * p₂)) t18 (fun p => p * p) (fun p => sqRoots p) U'
      (by omega) ht18 hm hR hcq2 hcp
    rw [hQ'] at hA; rw [hQ, hNdiv] at hB7 hB18
    have h3R : ((xSet N b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    obtain ⟨hM, hE⟩ := ie_mono U' (fun p => sqRoots p) 2 (by norm_num) (fun p hp => (hU' p hp).1)
      (fun p hp => card_sqRoots_le (hU' p hp).1 (isU1_odd (hU' p hp).2.1))
    set M := 1 - ∏ p ∈ U', (1 - (((fun p => sqRoots p) p).card : ℝ) / (((fun p => p * p) p : ℕ) : ℝ))
    set E := ∏ p ∈ U', (1 + (((fun p => sqRoots p) p).card : ℝ))
    set X := (N : ℝ) / ((p₂ : ℝ) * p₂)
    have hX : 0 ≤ X := by positivity
    have hmain : ((xSet N b p₂ z₁).card : ℝ) ≤ 23 / 25 * X * M + 3 * (E - 1) := by
      linarith [hA, hB7, hB18]
    unfold nonB
    simp only [Nat.cast_ofNat, Nat.reduceAdd] at hM hE
    have : 23 / 25 * X * M ≤ 23 / 25 * X * (1 - ∏ p ∈ U', (1 - 2 / ((p : ℝ) * p))) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    linarith

/-- The term `p₂ = 5`: one whole class mod 25, sieved by all U1 primes `≤ z₁`. -/
theorem card_xSet5_le (N b z₁ : ℕ) :
    ((xSet N b 5 z₁).card : ℝ) ≤
      (N : ℝ) / 25 * (1 - ∏ p ∈ smallP z₁ IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1) := by
  classical
  set U := smallP z₁ IsU1
  have hU : ∀ p ∈ U, p.Prime ∧ IsU1 p := fun p hp => (mem_filter.mp hp).2
  have hRHS : 0 ≤ (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) +
      ((3 : ℝ) ^ U.card - 1) := by
    have h1 := prod_one_sub_le_one U (fun p hp => (hU p hp).1)
    have h2 : (1 : ℝ) ≤ 3 ^ U.card := one_le_pow₀ (by norm_num)
    have : 0 ≤ (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  by_cases hW : witRoots b 5 = ∅
  · have : xSet N b 5 z₁ = ∅ := by
      rw [xSet, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]; exact hRHS
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hc_lt : c < 5 * 5 := mem_range.mp (witRoots_sub b 5 hcW)
  have huniq : ∀ x, x % (5 * 5) ∈ witRoots b 5 → x % (5 * 5) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le Nat.prime_five) _ hx _ hcW
  have hsub : xSet N b 5 z₁ ⊆ (Icc 1 N).filter (fun x => x % 25 = c ∧
      ∃ p ∈ U, x % (fun p => p * p) p ∈ (fun p => sqRoots p) p) := by
    intro x hx
    simp only [xSet, mem_filter] at hx
    obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
    exact mem_filter.mpr ⟨hx1, huniq x hxW, p,
      mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩, hpR⟩
  have hA := card_union_le N 25 c (fun p => p * p) (fun p => sqRoots p) U (by norm_num) hc_lt
    (fun p hp => Nat.mul_pos (hU p hp).1.pos (hU p hp).1.pos)
    (fun p _ r hr => mem_range.mp (sqRoots_sub p hr))
    (fun p hp => coprime_25_sq (hU p hp).1 (by have := (hU p hp).2.2.2; omega))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hU p hp).1 (hU p' hp').1 hne)
  obtain ⟨hM, hE⟩ := ie_mono U (fun p => sqRoots p) 2 (by norm_num) (fun p hp => (hU p hp).1)
    (fun p hp => card_sqRoots_le (hU p hp).1 (isU1_odd (hU p hp).2))
  simp only [Nat.cast_ofNat, Nat.reduceAdd] at hM hE hA
  have hcard : ((xSet N b 5 z₁).card : ℝ) ≤ ((Icc 1 N).filter (fun x => x % 25 = c ∧
      ∃ p ∈ U, x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)).card := by
    exact_mod_cast card_le_card hsub
  have : (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - ((sqRoots p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
      (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  linarith

/-! ### The cover of the Lemma C set -/

/-- The 23 classes mod 25 other than 7 and 18. -/
def T25 : Finset ℕ := (range 25).filter (fun t => t ≠ 7 ∧ t ≠ 18)

/-- Large U1 primes `p ∈ (z₁, p_B]`, inside one class mod 25. -/
def lcRes (N t z₁ pB : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => x % 25 = t ∧
    ∃ p ≤ pB, p.Prime ∧ (IsU1 p ∧ z₁ < p) ∧ x % (p * p) ∈ sqRoots p)

/-- Witness primes `p₂ ∈ (z₂, p_c]`. -/
def lcMid (N b z₂ pc : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ pc, p.Prime ∧ z₂ < p ∧ x % (p * p) ∈ witRoots b p)

/-- The Lemma C set. -/
def lemCSet (N b : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))

/-- The part of the Lemma C bound not involving the shared sets. -/
def lemCPart (N b z₁ z₂ pB Y' pc : ℕ) : Finset ℕ :=
  ((T25.biUnion (fun t => lcRes N t z₁ pB) ∪ vMidSet N pB Y') ∪ vPellSet N Y') ∪
    ((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSet N b p₂ z₁) ∪ lcMid N b z₂ pc)

lemma lemC_cover (N b z₁ z₂ pB Y' pc Y : ℕ) (hbe : b % 2 = 0) :
    lemCSet N b ⊆ (lemCPart N b z₁ z₂ pB Y' pc ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro x hx
  simp only [lemCSet, mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hxs, hsq1, hsq2⟩ := hx
  obtain ⟨p₁, hp₁, hd₁⟩ := exists_prime_sq_dvd hsq1
  have hU₁ := isU1_of_sq_dvd hp₁ hd₁ hxs
  have hR₁ : x % (p₁ * p₁) ∈ sqRoots p₁ := (mod_mem_sqRoots hp₁.pos x).mpr hd₁
  by_cases hsmall : ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p
  · -- sieve by the witness b
    obtain ⟨p₂, hp₂, hd₂⟩ := exists_prime_sq_dvd hsq2
    have hR₂ : x % (p₂ * p₂) ∈ witRoots b p₂ := (mod_mem_witRoots hp₂.pos x).mpr hd₂
    have hp₂2 : p₂ ≠ 2 := by
      rintro rfl
      have : 2 ∣ x * b + 1 := dvd_trans ⟨2, rfl⟩ hd₂
      have : 2 ∣ x * b := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hbe) x
      omega
    by_cases hz₂ : p₂ ≤ z₂
    · apply mem_union_left; apply mem_union_left; apply mem_union_right; apply mem_union_left
      simp only [mem_biUnion, smallP, mem_filter, mem_range, xSet, mem_Icc]
      exact ⟨p₂, ⟨by omega, hp₂, hp₂2⟩, ⟨hx1, hxN⟩, hxs, hR₂, hsmall⟩
    by_cases hpc : p₂ ≤ pc
    · apply mem_union_left; apply mem_union_left; apply mem_union_right; apply mem_union_right
      simp only [lcMid, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₂, hpc, hp₂, by omega, hR₂⟩
    by_cases hpY : p₂ ≤ Y
    · apply mem_union_left; apply mem_union_right
      simp only [midSet, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₂, hpY, hp₂, by omega, hR₂⟩
    · apply mem_union_right
      simp only [exSet, mem_filter, mem_Icc]
      have h1 : p₂ ≤ x * b + 1 :=
        le_trans (Nat.le_mul_self p₂) (Nat.le_of_dvd (Nat.succ_pos _) hd₂)
      have h2 : x * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b hxN) 1
      exact ⟨⟨hx1, hxN⟩, p₂, ⟨by omega, h1.trans h2⟩, hd₂⟩
  · -- large U1 prime
    have hz₁ : z₁ < p₁ := by
      by_contra h; push Not at h; exact hsmall ⟨p₁, h, hp₁, hU₁, hR₁⟩
    apply mem_union_left; apply mem_union_left; apply mem_union_left
    by_cases hpB : p₁ ≤ pB
    · apply mem_union_left; apply mem_union_left
      simp only [mem_biUnion, T25, mem_filter, mem_range, lcRes, mem_Icc]
      exact ⟨x % 25, ⟨Nat.mod_lt _ (by norm_num), hxs⟩, ⟨hx1, hxN⟩, rfl, p₁, hpB, hp₁,
        ⟨hU₁, hz₁⟩, hR₁⟩
    by_cases hpY : p₁ ≤ Y'
    · apply mem_union_left; apply mem_union_right
      simp only [vMidSet, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₁, hpY, hp₁, ⟨hU₁, by omega⟩, hR₁⟩
    · apply mem_union_right
      simp only [vPellSet, mem_filter, mem_Icc]
      have h1 : p₁ * p₁ ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd₁
      have h2 : x * x + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hxN hxN) 1
      have h3 : p₁ ≤ N + 1 := by
        by_contra hc; push Not at hc
        have : (N + 2) * (N + 2) ≤ p₁ * p₁ := Nat.mul_le_mul hc hc
        nlinarith
      refine ⟨⟨hx1, hxN⟩, p₁, ⟨by omega, h3⟩, ?_⟩
      rw [sq]; exact hd₁

/-! ### Lemma C2: prefix domination -/

lemma isU1_infinite : (Set.ofPred IsU1).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hap, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (a + 13) (by norm_num)
  refine ⟨p, ?_, by omega⟩
  show IsU1 p
  unfold Nat.ModEq at hmod
  exact ⟨hp, by simpa using hmod, by omega⟩

/-- The `j`-th U1 prime (`q₀ = 13, q₁ = 17, q₂ = 29, …`). -/
noncomputable def u1 (j : ℕ) : ℕ := Nat.nth IsU1 j

lemma u1_isU1 (j : ℕ) : IsU1 (u1 j) := Nat.nth_mem_of_infinite isU1_infinite j

lemma u1_le_of_count {a k : ℕ} (ha : IsU1 a) (hk : k ≤ Nat.count IsU1 a) : u1 k ≤ a := by
  unfold u1
  calc Nat.nth IsU1 k ≤ Nat.nth IsU1 (Nat.count IsU1 a) := Nat.nth_monotone isU1_infinite hk
    _ = a := Nat.nth_count ha

/-- **Prefix domination** (Lemma C2): for `g` antitone on U1 primes and a set `S` of U1 primes,
`∑_S g ≤ ∑_{j < |S|} g(q_j)` and `∏_{j < |S|} q_j ≤ ∏_S p`. -/
theorem prefix_dom (g : ℕ → ℝ) (hg : ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → g p' ≤ g p) :
    ∀ S : Finset ℕ, (∀ p ∈ S, IsU1 p) →
      ∑ p ∈ S, g p ≤ ∑ j ∈ range S.card, g (u1 j) ∧
        ∏ j ∈ range S.card, u1 j ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro hS
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha : IsU1 a := hS a (mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have hcount : s.card ≤ Nat.count IsU1 a := by
      rw [Nat.count_eq_card_filter_range]
      apply card_le_card
      intro x hx
      simp only [mem_filter, mem_range]
      exact ⟨hlt x hx, hS x (mem_insert_of_mem hx)⟩
    have hua := u1_le_of_count ha hcount
    rw [card_insert_of_notMem has, sum_insert has, prod_insert has, sum_range_succ,
      prod_range_succ]
    refine ⟨?_, ?_⟩
    · have := hg (u1 s.card) a (u1_isU1 _) ha hua
      linarith
    · calc (∏ j ∈ range s.card, u1 j) * u1 s.card ≤ (∏ p ∈ s, p) * a :=
            Nat.mul_le_mul ih2 hua
        _ = a * ∏ p ∈ s, p := mul_comm _ _

/-- Consequence used by the certificates: if the product of the first `L + 1` U1 primes exceeds
`M ≥ ∏_S p`, then `∑_S g ≤ ∑_{j < L} max(g(q_j), 0)`. -/
theorem prefix_dom_max (g : ℕ → ℝ) (hg : ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → g p' ≤ g p)
    (S : Finset ℕ) (hS : ∀ p ∈ S, IsU1 p) (M L : ℕ) (hSM : ∏ p ∈ S, p ≤ M)
    (hL : M < ∏ j ∈ range (L + 1), u1 j) :
    ∑ p ∈ S, g p ≤ ∑ j ∈ range L, max (g (u1 j)) 0 := by
  obtain ⟨h1, h2⟩ := prefix_dom g hg S hS
  have hcard : S.card ≤ L := by
    by_contra hc
    push Not at hc
    have hmono : ∏ j ∈ range (L + 1), u1 j ≤ ∏ j ∈ range S.card, u1 j := by
      apply prod_le_prod_of_subset_of_one_le (range_subset_range.mpr hc)
      intro j _ _; exact (u1_isU1 j).1.one_lt.le
    omega
  calc ∑ p ∈ S, g p ≤ ∑ j ∈ range S.card, g (u1 j) := h1
    _ ≤ ∑ j ∈ range S.card, max (g (u1 j)) 0 := sum_le_sum (fun j _ => le_max_left _ _)
    _ ≤ ∑ j ∈ range L, max (g (u1 j)) 0 :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hcard)
          (fun j _ _ => le_max_right _ _)

/-! ### Lemma C1: the gain `g = whole − non` is decreasing -/

/-- `g(p) = wholeB − nonB`. -/
noncomputable def gC (N z₁ p : ℕ) : ℝ := wholeB N p - nonB N p z₁

/-- `P = ∏_{U} (1 − 2/q²)`, `U` = U1 primes `≤ z₁`. -/
noncomputable def PU (z₁ : ℕ) : ℝ := ∏ q ∈ smallP z₁ IsU1, (1 - 2 / ((q : ℝ) * q))

lemma factor_pos {q : ℕ} (hq : q.Prime) : 0 < 1 - 2 / ((q : ℝ) * q) := by
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  rw [sub_pos, div_lt_one (by positivity)]; nlinarith

lemma PU_pos (z₁ : ℕ) : 0 < PU z₁ :=
  prod_pos (fun _q hq => factor_pos (mem_filter.mp hq).2.1)

lemma mem_U_iff {z₁ p : ℕ} (hp : IsU1 p) : p ∈ smallP z₁ IsU1 ↔ p ≤ z₁ := by
  simp only [smallP, mem_filter, mem_range]
  constructor
  · intro h; omega
  · intro h; exact ⟨by omega, hp.1, hp⟩

lemma gC_in {N z₁ p : ℕ} (hpU : p ∈ smallP z₁ IsU1) :
    gC N z₁ p = 23 / 25 * N * PU z₁ / ((p : ℝ) * p - 2) + 3 -
      3 * ((3 : ℝ) ^ ((smallP z₁ IsU1).card - 1) - 1) := by
  have hp : p.Prime := (mem_filter.mp hpU).2.1
  have hf := factor_pos hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0 : ℝ) < p * p := by positivity
  have hpp2 : (0 : ℝ) < p * p - 2 := by nlinarith
  have hmul := mul_prod_erase (smallP z₁ IsU1) (fun q => (1 - 2 / ((q : ℝ) * q))) hpU
  have hpr : ∏ q ∈ (smallP z₁ IsU1).erase p, (1 - 2 / ((q : ℝ) * q)) =
      PU z₁ / (1 - 2 / ((p : ℝ) * p)) := by
    rw [PU, ← hmul, mul_div_cancel_left₀ _ hf.ne']
  unfold gC wholeB nonB
  rw [hpr, card_erase_of_mem hpU]
  have e : (1 : ℝ) - 2 / ((p : ℝ) * p) = ((p : ℝ) * p - 2) / ((p : ℝ) * p) := by
    field_simp
  rw [e]
  field_simp
  ring

lemma gC_out {N z₁ p : ℕ} (hpU : p ∉ smallP z₁ IsU1) :
    gC N z₁ p = 23 / 25 * N * PU z₁ / ((p : ℝ) * p) + 3 -
      3 * ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1) := by
  unfold gC wholeB nonB
  rw [erase_eq_of_notMem hpU]
  unfold PU
  ring

/-- **Lemma C1.** -/
theorem gC_anti (N z₁ : ℕ) :
    ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → gC N z₁ p' ≤ gC N z₁ p := by
  intro p p' hp hp' hle
  have hP := PU_pos z₁
  have hN : (0 : ℝ) ≤ N := by positivity
  have h13 : (13 : ℝ) ≤ p := by exact_mod_cast hp.2.2
  have hle' : (p : ℝ) ≤ p' := by exact_mod_cast hle
  have hsq : (p : ℝ) * p ≤ (p' : ℝ) * p' := by nlinarith
  have hNP : 0 ≤ 23 / 25 * (N : ℝ) * PU z₁ := by positivity
  by_cases hpU : p ≤ z₁
  · rw [gC_in ((mem_U_iff hp).mpr hpU)]
    by_cases hpU' : p' ≤ z₁
    · rw [gC_in ((mem_U_iff hp').mpr hpU')]
      have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p' - 2) ≤
          23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p - 2) :=
        div_le_div_of_nonneg_left hNP (by nlinarith) (by linarith)
      linarith
    · rw [gC_out (fun h => hpU' ((mem_U_iff hp').mp h))]
      have hcard : 1 ≤ (smallP z₁ IsU1).card :=
        card_pos.mpr ⟨p, (mem_U_iff hp).mpr hpU⟩
      have hpow : (3 : ℝ) ^ ((smallP z₁ IsU1).card - 1) ≤ 3 ^ (smallP z₁ IsU1).card :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p') ≤
          23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p - 2) :=
        div_le_div_of_nonneg_left hNP (by nlinarith) (by linarith)
      linarith
  · have hpU' : ¬ p' ≤ z₁ := by omega
    rw [gC_out (fun h => hpU ((mem_U_iff hp).mp h)),
      gC_out (fun h => hpU' ((mem_U_iff hp').mp h))]
    have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p') ≤
        23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p) :=
      div_le_div_of_nonneg_left hNP (by nlinarith) hsq
    linarith

/-! ### The explicit Lemma C bound -/

lemma prod_sq_dvd {n : ℕ} : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p * p ∣ n) →
    (∏ p ∈ S, p) * (∏ p ∈ S, p) ∣ n := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a s has ih =>
    intro hP hd
    rw [prod_insert has]
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right (fun q hq =>
      (Nat.coprime_primes (hP a (mem_insert_self a s)) (hP q (mem_insert_of_mem hq))).mpr
        (fun h => has (h ▸ hq)))
    have hcop2 : Nat.Coprime (a * a) ((∏ p ∈ s, p) * (∏ p ∈ s, p)) :=
      Nat.Coprime.mul_right (Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩)
        (Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩)
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 (hd a (mem_insert_self a s))
      (ih (fun p hp => hP p (mem_insert_of_mem hp)) (fun p hp => hd p (mem_insert_of_mem hp)))
    calc a * (∏ p ∈ s, p) * (a * ∏ p ∈ s, p) = a * a * ((∏ p ∈ s, p) * (∏ p ∈ s, p)) := by ring
      _ ∣ n := this

lemma smallP_odd_eq (z₂ : ℕ) (h5 : 5 ≤ z₂) :
    smallP z₂ (· ≠ 2) = insert 5 (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)) := by
  ext p
  simp only [smallP, mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases h : p = 5
    · left; exact h
    · right; exact ⟨h1, h2, h3, h⟩
  · rintro (rfl | ⟨h1, h2, h3, -⟩)
    · exact ⟨by omega, Nat.prime_five, by norm_num⟩
    · exact ⟨h1, h2, h3⟩

/-- **Lemma C**, explicit form (without the shared sets `Mid(b)`, `Ex(b)`). -/
theorem card_lemCPart_le (N b z₁ z₂ pB Y' pc : ℕ) (G : ℝ) (hbN : b ≤ N) (hbs : IsStar b)
    (h5 : 5 ≤ z₂)
    (hG : ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 → ∑ p ∈ S, gC N z₁ p ≤ G) :
    ((lemCPart N b z₁ z₂ pB Y' pc).card : ℝ) ≤
      23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) +
      ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
      (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) +
      ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
      G +
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1) := by
  classical
  -- card of the union
  set R1 := T25.biUnion (fun t => lcRes N t z₁ pB)
  set X := (smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSet N b p₂ z₁)
  have hU : (lemCPart N b z₁ z₂ pB Y' pc).card ≤ R1.card + (vMidSet N pB Y').card +
      (vPellSet N Y').card + (X.card + (lcMid N b z₂ pc).card) := by
    have hdef : lemCPart N b z₁ z₂ pB Y' pc =
        ((R1 ∪ vMidSet N pB Y') ∪ vPellSet N Y') ∪ (X ∪ lcMid N b z₂ pc) := rfl
    rw [hdef]
    have a1 := Finset.card_union_le ((R1 ∪ vMidSet N pB Y') ∪ vPellSet N Y') (X ∪ lcMid N b z₂ pc)
    have a2 := Finset.card_union_le (R1 ∪ vMidSet N pB Y') (vPellSet N Y')
    have a3 := Finset.card_union_le R1 (vMidSet N pB Y')
    have a4 := Finset.card_union_le X (lcMid N b z₂ pc)
    omega
  have hUR : ((lemCPart N b z₁ z₂ pB Y' pc).card : ℝ) ≤ (R1.card : ℝ) + (vMidSet N pB Y').card +
      (vPellSet N Y').card + ((X.card : ℝ) + (lcMid N b z₂ pc).card) := by exact_mod_cast hU
  -- R1
  have hR1 : (R1.card : ℝ) ≤ 23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p),
      (2 * ((N : ℝ) / 25 / (p * p)) + 2) := by
    have h1 : (R1.card : ℝ) ≤ ∑ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 : ∀ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) ≤
        ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) := by
      intro t ht
      have ht25 : t < 25 := mem_range.mp (mem_filter.mp ht).1
      have h := classSieve_le N 25 t z₁ pB 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ z₁ < p)
        (by norm_num) ht25 (by norm_num) sqRoots_sub
        (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1))
        (fun p hp hU => Nat.Coprime.symm (Nat.Coprime.pow_right 2
          ((Nat.coprime_primes hp Nat.prime_five).mpr (by have := hU.1.2.2; omega))))
      have hsmall : smallP z₁ (fun p => IsU1 p ∧ z₁ < p) = ∅ := by
        rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
      rw [hsmall] at h
      simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat]
        at h
      simpa [lcRes] using h
    have hT : T25.card = 23 := by decide
    calc (R1.card : ℝ) ≤ ∑ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) := h1
      _ ≤ ∑ _t ∈ T25, ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p),
          (2 * ((N : ℝ) / 25 / (p * p)) + 2) := sum_le_sum h2
      _ = _ := by rw [sum_const, hT, nsmul_eq_mul]; norm_num
  -- vMid, Pell
  have hmid : ((vMidSet N pB Y').card : ℝ) ≤
      ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) := by
    have h := classSieve_le N 1 0 pB Y' 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ pB < p)
      one_pos one_pos (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1)) (fun p _ _ => Nat.coprime_one_left p)
    have hsmall : smallP pB (fun p => IsU1 p ∧ pB < p) = ∅ := by
      rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
    rw [hsmall] at h
    simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat,
      Nat.mod_one, true_and] at h
    simpa [vMidSet] using h
  have hpell : ((vPellSet N Y').card : ℝ) ≤
      (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast pellTail_le N Y'
  -- lcMid
  have hlc : ((lcMid N b z₂ pc).card : ℝ) ≤
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1) := card_midSet_le N b z₂ pc
  -- the p₂ terms
  have hX1 : (X.card : ℝ) ≤ ∑ p ∈ smallP z₂ (· ≠ 2), ((xSet N b p z₁).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  have hX5 := card_xSet5_le N b z₁
  have hodd : ∀ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), ((xSet N b p z₁).card : ℝ) ≤
      nonB N p z₁ + if p * p ∣ b * b + 1 then gC N z₁ p else 0 := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have := card_xSet_le N b p z₁ hpp.1 hpp.2.2
    split_ifs at this ⊢ <;> unfold gC at * <;> linarith
  set S := (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)).filter (fun p => p * p ∣ b * b + 1)
  have hsplit : ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5),
      (nonB N p z₁ + if p * p ∣ b * b + 1 then gC N z₁ p else 0) =
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ + ∑ p ∈ S, gC N z₁ p := by
    rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero]
  have hSU1 : ∀ p ∈ S, IsU1 p := fun p hp =>
    isU1_of_sq_dvd (mem_filter.mp (mem_filter.mp hp).1).2.1 (mem_filter.mp hp).2 hbs
  have hSprod : (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 := by
    have hd := prod_sq_dvd S (fun p hp => (hSU1 p hp).1) (fun p hp => (mem_filter.mp hp).2)
    have h1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    have h2 : b * b + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hbN hbN) 1
    omega
  have hC2 := hG S (filter_subset _ _) hSU1 hSprod
  have hXsum : ∑ p ∈ smallP z₂ (· ≠ 2), ((xSet N b p z₁).card : ℝ) ≤
      ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
      (∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
        G) := by
    rw [smallP_odd_eq z₂ h5, sum_insert (by simp [smallP])]
    have := sum_le_sum hodd
    rw [hsplit] at this
    unfold PU
    linarith
  linarith

/-- The prefix bound (Lemma C2) as a `G` for `card_lemCPart_le`. -/
lemma gBound_prefix (N z₁ z₂ L : ℕ)
    (hL : N * N + 1 < (∏ j ∈ range (L + 1), u1 j) * (∏ j ∈ range (L + 1), u1 j)) :
    ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 →
        ∑ p ∈ S, gC N z₁ p ≤ ∑ j ∈ range L, max (gC N z₁ (u1 j)) 0 := by
  intro S _ hSU1 hSprod
  have : ∏ p ∈ S, p < ∏ j ∈ range (L + 1), u1 j :=
    Nat.mul_self_lt_mul_self_iff.mp (by omega)
  exact prefix_dom_max (gC N z₁) (gC_anti N z₁) S hSU1 (∏ p ∈ S, p) L le_rfl this

/-- All U1 primes `≤ z₂` (no prefix condition) as a `G`. -/
lemma gBound_all (N z₁ z₂ : ℕ) :
    ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 →
        ∑ p ∈ S, gC N z₁ p ≤ ∑ p ∈ smallP z₂ IsU1, max (gC N z₁ p) 0 := by
  intro S hS hSU1 _
  have hsub : S ⊆ smallP z₂ IsU1 := fun p hp => by
    have := hS hp
    simp only [smallP, mem_filter] at this ⊢
    exact ⟨this.1, this.2.1, hSU1 p hp⟩
  calc ∑ p ∈ S, gC N z₁ p ≤ ∑ p ∈ S, max (gC N z₁ p) 0 := sum_le_sum (fun p _ => le_max_left _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => le_max_right _ _)

end Erdos848
