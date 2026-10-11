import Erdos848.Dom
import Erdos848.UTail

/-!
# Phase 9.6: Lemma C on a good domain (`proof.md` §10.5)

Lemma C for `x` in a good domain `D` (class counts `L/Q ± μ` for odd `Q`):

* `card_xSetD_le`: the term of an odd prime `p₂ ≠ 5`: `wholeD` if `p₂² ∣ b² + 1`, otherwise
  `nonD = min((a), (c))` with Bonferroni depth `d`:
  (a) `(L/p₂²)(1 - E_d) + μ E`,   (c) `(23/25)(L/p₂²)(1 - E_d) + 23 μ E`;
* `card_xSet5D_le`: the term `p₂ = 5` (one whole class mod 25);
* `card_lcResD_le`, `card_lcMidD_le`: large U1 primes in `(z₁, p_B]` and witness primes in
  `(z₂, p_c]`;
* `sum_gain_le`: the gains of `S_b`, bounded by `n τ + ∑ max(g - τ, 0)` (Lemma C2′);
* `lemCD_cover`: the cover of the Lemma C set.
-/

namespace Erdos848

open Finset

variable {D : Finset ℕ} {L μ : ℝ}

/-- The U1 primes `≤ z₁` other than `p₂`. -/
def Uer (z₁ p₂ : ℕ) : Finset ℕ := (smallP z₁ IsU1).erase p₂

/-- The term of `p₂` on `D`. -/
def xSetD (D : Finset ℕ) (b p₂ z₁ : ℕ) : Finset ℕ :=
  D.filter (fun x => IsStar x ∧ x % (p₂ * p₂) ∈ witRoots b p₂ ∧
    ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

/-- Truncated main term `1 - E_d` and error count over a set `U` of U1 primes. -/
noncomputable def mainU (U : Finset ℕ) (d : ℕ) : ℝ := 1 - altE U (fun p => 2 / ((p : ℝ) * p)) d
noncomputable def errU (U : Finset ℕ) (d : ℕ) : ℝ := truncErr U (fun _ => (2 : ℝ)) d

/-- Option (a) and option (c) for `p₂ ∉ S_b`. -/
noncomputable def nonD (L μ : ℝ) (p₂ z₁ d : ℕ) : ℝ :=
  min (L / ((p₂ : ℝ) * p₂) * mainU (Uer z₁ p₂) d + μ * errU (Uer z₁ p₂) d)
    (23 / 25 * (L / ((p₂ : ℝ) * p₂)) * mainU (Uer z₁ p₂) d + 23 * μ * errU (Uer z₁ p₂) d)

/-- The whole class of `R_{p₂}` for `p₂ ∈ S_b`. -/
noncomputable def wholeD (L μ : ℝ) (p₂ : ℕ) : ℝ := 23 / 25 * (L / ((p₂ : ℝ) * p₂)) + 3 * μ

lemma u1_two_div_mem {p : ℕ} (hp : p.Prime) : 0 ≤ 2 / ((p : ℝ) * p) ∧ 2 / ((p : ℝ) * p) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]; nlinarith

lemma mainU_nonneg (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) {d : ℕ} (hd : Odd d) : 0 ≤ mainU U d := by
  unfold mainU
  have hs := (altE_sandwich (fun p => 2 / ((p : ℝ) * p)) U (fun p hp => u1_two_div_mem (hU p hp)) d).2 hd
  have hp : ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p)) ≤ 1 := prod_one_sub_le_one U hU
  linarith

lemma errU_nonneg (U : Finset ℕ) (d : ℕ) : 0 ≤ errU U d :=
  truncErr_nonneg U (fun _ _ => by norm_num) d

lemma Uer_prime {z₁ p₂ p : ℕ} (hp : p ∈ Uer z₁ p₂) : p.Prime ∧ IsU1 p ∧ p ≠ p₂ := by
  have := mem_erase.mp hp
  exact ⟨(mem_filter.mp this.2).2.1, (mem_filter.mp this.2).2.2, this.1⟩

lemma nonD_nonneg (hL : 0 ≤ L) (hμ : 0 ≤ μ) (p₂ z₁ : ℕ) {d : ℕ} (hd : Odd d) : 0 ≤ nonD L μ p₂ z₁ d := by
  have hm := mainU_nonneg (Uer z₁ p₂) (fun p hp => (Uer_prime hp).1) hd
  have he := errU_nonneg (Uer z₁ p₂) d
  unfold nonD
  apply le_min <;> positivity

/-- A Bonferroni sieve of one class `t` mod `q` of `D` by the U1 primes of `U`. -/
lemma dom_sieveU (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (q t : ℕ) (hq : 0 < q)
    (hqo : Odd q) (ht : t < q) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ IsU1 p)
    (hcop : ∀ p ∈ U, Nat.Coprime q (p * p)) {d : ℕ} (hd : Odd d) :
    ((D.filter (fun x => x % q = t ∧ ∃ p ∈ U, x % (p * p) ∈ sqRoots p)).card : ℝ) ≤
      L / q * mainU U d + μ * errU U d := by
  have hoddp : ∀ p ∈ U, Odd p := fun p hp => (hU p hp).1.odd_of_ne_two (isU1_odd (hU p hp).2)
  have h := dom_bonf_le hD q t (fun p => p * p) (fun p => sqRoots p) U d hd hq ht
    (fun p hp => Nat.mul_pos (hU p hp).1.pos (hU p hp).1.pos)
    (fun p _ r hr => mem_range.mp (sqRoots_sub p hr)) hcop
    (fun p hp p' hp' hne => coprime_sq_of_primes (hU p hp).1 (hU p' hp').1 hne)
    (fun T hT => by
      unfold bigMod
      apply Odd.mul hqo
      apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) (by decide)
      intro p hp; exact (hoddp p (hT hp)).mul (hoddp p (hT hp)))
  have hv : ∀ p ∈ U, (0 : ℝ) ≤ ((sqRoots p).card : ℝ) / ((p * p : ℕ) : ℝ) ∧
      ((sqRoots p).card : ℝ) / ((p * p : ℕ) : ℝ) ≤ 2 / ((p : ℝ) * p) := by
    intro p hp
    have hpp : (0 : ℝ) < p * p := by have := (hU p hp).1.pos; positivity
    have hR : ((sqRoots p).card : ℝ) ≤ 2 := by
      exact_mod_cast card_sqRoots_le (hU p hp).1 (isU1_odd (hU p hp).2)
    push_cast
    exact ⟨by positivity, div_le_div_of_nonneg_right hR hpp.le⟩
  have hanti := altE_odd_anti (P := U) (v := fun p => ((sqRoots p).card : ℝ) / ((p * p : ℕ) : ℝ))
    (w := fun p => 2 / ((p : ℝ) * p)) (fun p hp => (hv p hp).2)
    (fun p hp => ⟨(hv p hp).1, (hv p hp).2.trans (u1_two_div_mem (hU p hp).1).2⟩)
    (fun p hp => u1_two_div_mem (hU p hp).1) hd
  have herr := truncErr_mono U (x := fun p => ((sqRoots p).card : ℝ)) (y := fun _ => (2 : ℝ))
    (fun p _ => by positivity)
    (fun p hp => by exact_mod_cast card_sqRoots_le (hU p hp).1 (isU1_odd (hU p hp).2)) d
  have hLq : 0 ≤ L / q := by positivity
  have e1 := mul_le_mul_of_nonneg_left (show 1 - altE U (fun p => ((sqRoots p).card : ℝ) /
    ((p * p : ℕ) : ℝ)) d ≤ mainU U d by unfold mainU; linarith) hLq
  have e2 := mul_le_mul_of_nonneg_left herr hμ
  unfold errU
  linarith

/-- **The term of an odd prime `p₂ ≠ 5`** on a good domain. -/
theorem card_xSetD_le (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (b p₂ z₁ : ℕ)
    (hp₂ : p₂.Prime) (h2 : p₂ ≠ 2) (h5 : p₂ ≠ 5) {d : ℕ} (hd : Odd d) :
    ((xSetD D b p₂ z₁).card : ℝ) ≤
      if p₂ * p₂ ∣ b * b + 1 then wholeD L μ p₂ else nonD L μ p₂ z₁ d := by
  classical
  have hp₂o : Odd p₂ := hp₂.odd_of_ne_two h2
  by_cases hW : witRoots b p₂ = ∅
  · have : xSetD D b p₂ z₁ = ∅ := by
      rw [xSetD, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]
    split_ifs
    · unfold wholeD; positivity
    · exact nonD_nonneg hL hμ p₂ z₁ hd
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hpp : 0 < p₂ * p₂ := Nat.mul_pos hp₂.pos hp₂.pos
  have hppo : Odd (p₂ * p₂) := hp₂o.mul hp₂o
  have hc_lt : c < p₂ * p₂ := mem_range.mp (witRoots_sub b p₂ hcW)
  have hcdvd : p₂ * p₂ ∣ c * b + 1 := (mem_filter.mp hcW).2
  have huniq : ∀ x, x % (p₂ * p₂) ∈ witRoots b p₂ → x % (p₂ * p₂) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le hp₂) _ hx _ hcW
  have hcop25 := coprime_25_sq hp₂ h5
  have h25o : Odd (25 * (p₂ * p₂)) := (by decide : Odd 25).mul hppo
  have hQ' : ((p₂ * p₂ : ℕ) : ℝ) = (p₂ : ℝ) * p₂ := by push_cast; ring
  have hQ : ((25 * (p₂ * p₂) : ℕ) : ℝ) = 25 * ((p₂ : ℝ) * p₂) := by push_cast; ring
  split_ifs with hsq
  · -- whole class: X ⊆ A ∖ (B₇ ∪ B₁₈)
    obtain ⟨t7, ht7, H7⟩ := crt_class hcop25 (a := 7) (by norm_num) hc_lt
    obtain ⟨t18, ht18, H18⟩ := crt_class hcop25 (a := 18) (by norm_num) hc_lt
    set A := D.filter (fun x => x % (p₂ * p₂) = c)
    set B7 := D.filter (fun x => x % (25 * (p₂ * p₂)) = t7)
    set B18 := D.filter (fun x => x % (25 * (p₂ * p₂)) = t18)
    have h3 := card_three_le (A := A) (X := xSetD D b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSetD, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, huniq x hx.2.2.1⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2).2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2).2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSetD, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSetD, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2).1; have := ((H18 x).mp hb.2).1; omega)
    have hA := hD (p₂ * p₂) c hpp hppo hc_lt
    have hB7 := hD (25 * (p₂ * p₂)) t7 (by omega) h25o ht7
    have hB18 := hD (25 * (p₂ * p₂)) t18 (by omega) h25o ht18
    rw [hQ'] at hA; rw [hQ] at hB7 hB18
    rw [abs_le] at hA hB7 hB18
    have h3R : ((xSetD D b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    have hdiv : L / (25 * ((p₂ : ℝ) * p₂)) = L / ((p₂ : ℝ) * p₂) / 25 := by
      rw [div_div, mul_comm]
    rw [hdiv] at hB7 hB18
    unfold wholeD
    linarith [hA.2, hB7.1, hB18.1]
  · -- sieve by `U' = U ∖ {p₂}`
    have hU' : ∀ p ∈ Uer z₁ p₂, p.Prime ∧ IsU1 p := fun p hp => ⟨(Uer_prime hp).1, (Uer_prime hp).2.1⟩
    have hmem : ∀ x ∈ xSetD D b p₂ z₁, x % (p₂ * p₂) = c ∧
        ∃ p ∈ Uer z₁ p₂, x % (p * p) ∈ sqRoots p := by
      intro x hx
      simp only [xSetD, mem_filter] at hx
      obtain ⟨-, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
      have hxc := huniq x hxW
      refine ⟨hxc, p, ?_, hpR⟩
      have hne : p ≠ p₂ := by
        rintro rfl
        rw [hxc] at hpR
        exact hsq (sq_dvd_of_roots hcdvd (mem_filter.mp hpR).2)
      exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩⟩
    have hcopU : ∀ p ∈ Uer z₁ p₂, Nat.Coprime (p₂ * p₂) (p * p) := fun p hp =>
      coprime_sq_of_primes hp₂ (hU' p hp).1 (Ne.symm (Uer_prime hp).2.2)
    -- option (a)
    have ha : ((xSetD D b p₂ z₁).card : ℝ) ≤
        L / ((p₂ : ℝ) * p₂) * mainU (Uer z₁ p₂) d + μ * errU (Uer z₁ p₂) d := by
      have hsub : xSetD D b p₂ z₁ ⊆ D.filter (fun x => x % (p₂ * p₂) = c ∧
          ∃ p ∈ Uer z₁ p₂, x % (p * p) ∈ sqRoots p) := by
        intro x hx; exact mem_filter.mpr ⟨(mem_filter.mp hx).1, hmem x hx⟩
      have h := dom_sieveU hD hL hμ (p₂ * p₂) c hpp hppo hc_lt (Uer z₁ p₂) hU' hcopU hd
      rw [hQ'] at h
      have : ((xSetD D b p₂ z₁).card : ℝ) ≤ ((D.filter (fun x => x % (p₂ * p₂) = c ∧
          ∃ p ∈ Uer z₁ p₂, x % (p * p) ∈ sqRoots p)).card : ℝ) := by exact_mod_cast card_le_card hsub
      linarith
    -- option (c): split into the 23 classes mod 25
    have hc : ((xSetD D b p₂ z₁).card : ℝ) ≤
        23 / 25 * (L / ((p₂ : ℝ) * p₂)) * mainU (Uer z₁ p₂) d + 23 * μ * errU (Uer z₁ p₂) d := by
      have hcls : ∀ t ∈ T25, ∃ s < 25 * (p₂ * p₂), ∀ x, x % (25 * (p₂ * p₂)) = s ↔
          x % 25 = t ∧ x % (p₂ * p₂) = c := fun t ht =>
        crt_class hcop25 (mem_range.mp (mem_filter.mp ht).1) hc_lt
      choose! sOf hsOf hsOf' using hcls
      have hsub : xSetD D b p₂ z₁ ⊆ T25.biUnion (fun t => D.filter (fun x =>
          x % (25 * (p₂ * p₂)) = sOf t ∧ ∃ p ∈ Uer z₁ p₂, x % (p * p) ∈ sqRoots p)) := by
        intro x hx
        have hm := hmem x hx
        have hstar := (mem_filter.mp hx).2.1
        have ht : x % 25 ∈ T25 := by
          simp only [T25, mem_filter, mem_range]; unfold IsStar at hstar
          exact ⟨Nat.mod_lt _ (by norm_num), hstar⟩
        simp only [mem_biUnion, mem_filter]
        exact ⟨x % 25, ht, (mem_filter.mp hx).1, (hsOf' _ ht x).mpr ⟨rfl, hm.1⟩, hm.2⟩
      have hcopU' : ∀ p ∈ Uer z₁ p₂, Nat.Coprime (25 * (p₂ * p₂)) (p * p) := fun p hp =>
        Nat.coprime_mul_iff_left.mpr ⟨coprime_25_sq (hU' p hp).1
          (by have := (hU' p hp).2.2.2; omega), hcopU p hp⟩
      have hT : ∀ t ∈ T25, ((D.filter (fun x => x % (25 * (p₂ * p₂)) = sOf t ∧
          ∃ p ∈ Uer z₁ p₂, x % (p * p) ∈ sqRoots p)).card : ℝ) ≤
          L / (25 * ((p₂ : ℝ) * p₂)) * mainU (Uer z₁ p₂) d + μ * errU (Uer z₁ p₂) d := by
        intro t ht
        have h := dom_sieveU hD hL hμ (25 * (p₂ * p₂)) (sOf t) (by omega) h25o (hsOf t ht)
          (Uer z₁ p₂) hU' hcopU' hd
        rwa [hQ] at h
      have hbig : ((xSetD D b p₂ z₁).card : ℝ) ≤ ∑ t ∈ T25, ((D.filter (fun x =>
          x % (25 * (p₂ * p₂)) = sOf t ∧ ∃ p ∈ Uer z₁ p₂, x % (p * p) ∈ sqRoots p)).card : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      have hsum := sum_le_sum hT
      rw [sum_const, show T25.card = 23 by decide, nsmul_eq_mul] at hsum
      have : L / (25 * ((p₂ : ℝ) * p₂)) = L / ((p₂ : ℝ) * p₂) / 25 := by rw [div_div, mul_comm]
      rw [this] at hsum
      push_cast at hsum
      linarith
    unfold nonD
    exact le_min ha hc

/-- **The term `p₂ = 5`** on a good domain: one class mod 25. -/
theorem card_xSet5D_le (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (b z₁ : ℕ)
    {d : ℕ} (hd : Odd d) :
    ((xSetD D b 5 z₁).card : ℝ) ≤ L / 25 * mainU (smallP z₁ IsU1) d + μ * errU (smallP z₁ IsU1) d := by
  classical
  have hU : ∀ p ∈ smallP z₁ IsU1, p.Prime ∧ IsU1 p := fun p hp => (mem_filter.mp hp).2
  have hm0 := mainU_nonneg (smallP z₁ IsU1) (fun p hp => (hU p hp).1) hd
  have he0 := errU_nonneg (smallP z₁ IsU1) d
  by_cases hW : witRoots b 5 = ∅
  · have : xSetD D b 5 z₁ = ∅ := by
      rw [xSetD, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]; positivity
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hc_lt : c < 25 := mem_range.mp (witRoots_sub b 5 hcW)
  have huniq : ∀ x, x % (5 * 5) ∈ witRoots b 5 → x % (5 * 5) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le Nat.prime_five) _ hx _ hcW
  have hsub : xSetD D b 5 z₁ ⊆ D.filter (fun x => x % 25 = c ∧
      ∃ p ∈ smallP z₁ IsU1, x % (p * p) ∈ sqRoots p) := by
    intro x hx
    simp only [xSetD, mem_filter] at hx
    obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
    exact mem_filter.mpr ⟨hx1, huniq x hxW, p,
      mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩, hpR⟩
  have h := dom_sieveU hD hL hμ 25 c (by norm_num) (by decide) hc_lt (smallP z₁ IsU1) hU
    (fun p hp => coprime_25_sq (hU p hp).1 (by have := (hU p hp).2.2.2; omega)) hd
  have : ((xSetD D b 5 z₁).card : ℝ) ≤ ((D.filter (fun x => x % 25 = c ∧
      ∃ p ∈ smallP z₁ IsU1, x % (p * p) ∈ sqRoots p)).card : ℝ) := by exact_mod_cast card_le_card hsub
  push_cast at h
  linarith

/-! ### The other parts of Lemma C -/

/-- Large U1 primes `p ∈ (z₁, p_B]`, inside the class `t` mod 25. -/
def lcResD (D : Finset ℕ) (t z₁ pB : ℕ) : Finset ℕ :=
  D.filter (fun x => x % 25 = t ∧ ∃ p ≤ pB, p.Prime ∧ (IsU1 p ∧ z₁ < p) ∧ x % (p * p) ∈ sqRoots p)

/-- Witness primes `p₂ ∈ (z₂, p_c]`. -/
def lcMidD (D : Finset ℕ) (b z₂ pc : ℕ) : Finset ℕ :=
  D.filter (fun x => ∃ p ≤ pc, p.Prime ∧ z₂ < p ∧ x % (p * p) ∈ witRoots b p)

lemma smallP_empty_of (z : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (h : ∀ p, Q p → z < p) :
    smallP z Q = ∅ := by
  rw [smallP, filter_eq_empty_iff]; intro p hp hq; simp only [mem_range] at hp; have := h p hq.2; omega

lemma truncErr_empty (x : ℕ → ℝ) (d : ℕ) : truncErr ∅ x d = 0 := by
  unfold truncErr; rw [powerset_empty, filter_singleton, if_neg (by simp)]; simp

lemma coprime25_of_prime {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 p := by
  have := Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_five hp).mpr (Ne.symm h5))
  simpa using this

theorem card_lcResD_le (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (t z₁ pB : ℕ)
    (ht : t < 25) :
    ((lcResD D t z₁ pB).card : ℝ) ≤
      ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * (L / 25 / (p * p)) + μ * 2) := by
  have hE := smallP_empty_of z₁ (fun p => IsU1 p ∧ z₁ < p) (fun p h => h.2)
  have h := domSieve_le hD hL hμ 25 t z₁ pB 2 1 odd_one (fun p => sqRoots p) (fun p => IsU1 p ∧ z₁ < p)
    (by norm_num) ht (by norm_num) sqRoots_sub (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1))
    (fun p hp hU => coprime25_of_prime hp (by have := hU.1.2.2; omega))
    (fun T hT => by rw [hE, subset_empty] at hT; subst hT; simp [bigMod]; decide)
    (by decide)
    (fun p hp => by
      have hU := (mem_filter.mp hp).2
      have ho : Odd p := hU.1.odd_of_ne_two (isU1_odd hU.2.1)
      exact (by decide : Odd 25).mul (ho.mul ho))
  rw [hE, altE_empty, truncErr_empty] at h
  simp only [sub_self, mul_zero, zero_add, Nat.cast_ofNat] at h
  simpa [lcResD] using h

theorem card_lcMidD_le (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (b z₂ pc : ℕ)
    (hz : 2 ≤ z₂) :
    ((lcMidD D b z₂ pc).card : ℝ) ≤ ∑ p ∈ midP z₂ pc (fun p => z₂ < p), (L / (p * p) + μ) := by
  have hE := smallP_empty_of z₂ (fun p => z₂ < p) (fun p h => h)
  have h := domSieve_le hD hL hμ 1 0 z₂ pc 1 1 odd_one (witRoots b) (fun p => z₂ < p)
    one_pos one_pos (by norm_num) (witRoots_sub b) (fun p hp _ => card_witRoots_le hp)
    (fun p _ _ => Nat.coprime_one_left p)
    (fun T hT => by rw [hE, subset_empty] at hT; subst hT; simp [bigMod])
    (by decide)
    (fun p hp => by
      have hp' := (mem_filter.mp hp).2
      have hodd : Odd p := hp'.1.odd_of_ne_two (by have := (mem_Ioc.mp (mem_filter.mp hp).1).1; omega)
      simpa using hodd.mul hodd)
  rw [hE, altE_empty, truncErr_empty] at h
  simp only [sub_self, mul_zero, zero_add, Nat.cast_one, one_mul, div_one, mul_one,
    Nat.mod_one, true_and] at h
  simpa [lcMidD] using h

/-! ### The U1 tail (Lemmas H and P) -/

/-- `x ∈ [1,N]` with `p² ∣ x² + 1` for a U1 prime `p > p_T`. -/
def u1Tail (N pT : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ x * x + 1, IsU1 p ∧ pT < p ∧ p * p ∣ x * x + 1)

/-- Lemma H for one U1 prime. -/
noncomputable def hcnt (N p : ℕ) : ℝ :=
  if p * p ≤ N then 2 * ((N : ℝ) / (p * p) + 1) else if p * p ≤ 2 * N then 2 else 1

lemma card_root_class_le (N p : ℕ) (hp : IsU1 p) :
    (((Icc 1 N).filter (fun x => x % (p * p) ∈ sqRoots p)).card : ℝ) ≤ hcnt N p := by
  unfold hcnt
  have hpp : 0 < p * p := Nat.mul_pos hp.1.pos hp.1.pos
  split_ifs with h1 h2
  · have h := card_mod_mem_real N (p * p) hpp (sqRoots p) (fun r hr => mem_range.mp (sqRoots_sub p hr))
    rw [abs_le] at h
    have hR : ((sqRoots p).card : ℝ) ≤ 2 := by exact_mod_cast card_sqRoots_le hp.1 (isU1_odd hp)
    have : ((sqRoots p).card : ℝ) * ((N : ℝ) / ((p * p : ℕ) : ℝ)) ≤ 2 * ((N : ℝ) / ((p * p : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hR (by positivity)
    push_cast at h this ⊢
    linarith [h.2]
  · exact_mod_cast (card_sqRoots_Icc_le hp.1 (isU1_odd hp) (by omega)).1
  · exact_mod_cast (card_sqRoots_Icc_le hp.1 (isU1_odd hp) (by omega)).2 (by omega)

/-- **The U1 tail.** -/
theorem card_u1Tail_le (N pT Y : ℕ) (hY : 1 ≤ Y) :
    ((u1Tail N pT).card : ℝ) ≤ ∑ p ∈ midP pT Y (fun p => IsU1 p ∧ pT < p), hcnt N p +
      ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N Y m : ℝ) := by
  classical
  set B : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun x => x % (p * p) ∈ sqRoots p)
  have hsub : u1Tail N pT ⊆ (midP pT Y (fun p => IsU1 p ∧ pT < p)).biUnion B ∪
      (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1) := by
    intro x hx
    simp only [u1Tail, mem_filter, mem_Icc] at hx
    obtain ⟨⟨hx1, hxN⟩, p, -, hU, hpT, hd⟩ := hx
    by_cases hpY : p ≤ Y
    · apply mem_union_left
      simp only [mem_biUnion, midP, mem_filter, mem_Ioc, B, mem_Icc]
      exact ⟨p, ⟨⟨hpT, hpY⟩, hU.1, hU, hpT⟩, ⟨hx1, hxN⟩, (mod_mem_sqRoots hU.1.pos x).mpr hd⟩
    · apply mem_union_right
      simp only [mem_filter, mem_Icc]
      have h1 : p * p ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd
      have h3 : p ≤ N + 1 := by
        by_contra hc; push Not at hc
        have : (N + 2) * (N + 2) ≤ p * p := Nat.mul_le_mul hc hc
        nlinarith
      exact ⟨⟨hx1, hxN⟩, p, ⟨by omega, h3⟩, by rw [sq]; exact hd⟩
  have h1 : ((u1Tail N pT).card : ℝ) ≤ ∑ p ∈ midP pT Y (fun p => IsU1 p ∧ pT < p), ((B p).card : ℝ) +
      (((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card : ℝ) := by
    have := (card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right card_biUnion_le _))
    exact_mod_cast this
  have h2 := sum_le_sum (fun p hp => card_root_class_le N p ((mem_filter.mp hp).2.2.1) :
    ∀ p ∈ midP pT Y (fun p => IsU1 p ∧ pT < p), ((B p).card : ℝ) ≤ hcnt N p)
  have h3 : (((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card : ℝ) ≤
      ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N Y m : ℝ) := by
    exact_mod_cast pellWin_le N Y hY
  linarith

/-! ### The cover of the Lemma C set on `D` -/

/-- The Lemma C set on `D`. -/
def lemCSetD (D : Finset ℕ) (b : ℕ) : Finset ℕ :=
  D.filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))

/-- The part of the Lemma C cover not involving the U1 tail and the shared sets. -/
def lemCcore (D : Finset ℕ) (b z₁ z₂ pB pc : ℕ) : Finset ℕ :=
  T25.biUnion (fun t => lcResD D t z₁ pB) ∪
    ((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSetD D b p₂ z₁) ∪ lcMidD D b z₂ pc)

theorem lemCD_cover {N : ℕ} (hDN : D ⊆ Icc 1 N) (b z₁ z₂ pB pc Y : ℕ)
    (h4 : ∀ x ∈ D, ¬ 2 * 2 ∣ x * b + 1) :
    lemCSetD D b ⊆ ((lemCcore D b z₁ z₂ pB pc ∪ u1Tail N pB) ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro x hx
  simp only [lemCSetD, mem_filter] at hx
  obtain ⟨hxD, hxs, hsq1, hsq2⟩ := hx
  have hxI := mem_Icc.mp (hDN hxD)
  obtain ⟨p₁, hp₁, hd₁⟩ := exists_prime_sq_dvd hsq1
  have hU₁ := isU1_of_sq_dvd hp₁ hd₁ hxs
  have hR₁ : x % (p₁ * p₁) ∈ sqRoots p₁ := (mod_mem_sqRoots hp₁.pos x).mpr hd₁
  by_cases hsmall : ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p
  · obtain ⟨p₂, hp₂, hd₂⟩ := exists_prime_sq_dvd hsq2
    have hR₂ : x % (p₂ * p₂) ∈ witRoots b p₂ := (mod_mem_witRoots hp₂.pos x).mpr hd₂
    have hp₂2 : p₂ ≠ 2 := by rintro rfl; exact h4 x hxD hd₂
    by_cases hz₂ : p₂ ≤ z₂
    · apply mem_union_left; apply mem_union_left; apply mem_union_left
      apply mem_union_right; apply mem_union_left
      simp only [mem_biUnion, smallP, mem_filter, mem_range, xSetD]
      exact ⟨p₂, ⟨by omega, hp₂, hp₂2⟩, hxD, hxs, hR₂, hsmall⟩
    by_cases hpc : p₂ ≤ pc
    · apply mem_union_left; apply mem_union_left; apply mem_union_left
      apply mem_union_right; apply mem_union_right
      simp only [lcMidD, mem_filter]
      exact ⟨hxD, p₂, hpc, hp₂, by omega, hR₂⟩
    by_cases hpY : p₂ ≤ Y
    · apply mem_union_left; apply mem_union_right
      simp only [midSet, mem_filter, mem_Icc]
      exact ⟨hxI, p₂, hpY, hp₂, by omega, hR₂⟩
    · apply mem_union_right
      simp only [exSet, mem_filter, mem_Icc]
      have h1 : p₂ ≤ x * b + 1 :=
        le_trans (Nat.le_mul_self p₂) (Nat.le_of_dvd (Nat.succ_pos _) hd₂)
      have h2 : x * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b hxI.2) 1
      exact ⟨hxI, p₂, ⟨by omega, h1.trans h2⟩, hd₂⟩
  · have hz₁ : z₁ < p₁ := by
      by_contra h; push Not at h; exact hsmall ⟨p₁, h, hp₁, hU₁, hR₁⟩
    apply mem_union_left; apply mem_union_left
    by_cases hpB : p₁ ≤ pB
    · apply mem_union_left; apply mem_union_left
      simp only [mem_biUnion, T25, mem_filter, mem_range, lcResD]
      exact ⟨x % 25, ⟨Nat.mod_lt _ (by norm_num), hxs⟩, hxD, rfl, p₁, hpB, hp₁, ⟨hU₁, hz₁⟩, hR₁⟩
    · apply mem_union_right
      simp only [u1Tail, mem_filter]
      exact ⟨hDN hxD, p₁, le_trans (Nat.le_mul_self p₁) (Nat.le_of_dvd (Nat.succ_pos _) hd₁),
        hU₁, by omega, hd₁⟩

/-! ### Lemma C2′ and the sum over `p₂` -/

/-- At most `n` U1 primes whose product squared is at most `X² + 1`, if the first `n + 1`
U1 primes have a larger product. -/
lemma card_le_of_prefix (S : Finset ℕ) (hS : ∀ p ∈ S, IsU1 p) (X n : ℕ)
    (hSprod : (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ X * X + 1)
    (hpre : X * X + 1 < (∏ j ∈ range (n + 1), u1 j) * (∏ j ∈ range (n + 1), u1 j)) : S.card ≤ n := by
  obtain ⟨-, h2⟩ := prefix_dom (fun _ => 0) (fun _ _ _ _ _ => le_rfl) S hS
  by_contra hc; push Not at hc
  have hmono : ∏ j ∈ range (n + 1), u1 j ≤ ∏ j ∈ range S.card, u1 j := by
    apply prod_le_prod_of_subset_of_one_le (range_subset_range.mpr hc)
    intro j _ _; exact (u1_isU1 j).1.one_lt.le
  have := Nat.mul_le_mul (hmono.trans h2) (hmono.trans h2)
  omega

/-- The gain of `p₂ ∈ S_b`: `max(whole - non, 0)`. -/
noncomputable def gainD (L μ : ℝ) (p z₁ d : ℕ) : ℝ := max (wholeD L μ p - nonD L μ p z₁ d) 0

/-- **The sum over the odd primes `p₂ ≤ z₂`** (Lemma C2′ with a threshold `τ`). -/
theorem card_p2_le (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (b xb z₁ z₂ nS : ℕ) (τ : ℝ)
    {d : ℕ} (hd : Odd d) (hbs : IsStar b) (hbx : b ≤ xb) (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ)
    (hpre : xb * xb + 1 < (∏ j ∈ range (nS + 1), u1 j) * (∏ j ∈ range (nS + 1), u1 j)) :
    (((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSetD D b p₂ z₁)).card : ℝ) ≤
      (L / 25 * mainU (smallP z₁ IsU1) d + μ * errU (smallP z₁ IsU1) d) +
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD L μ p z₁ d +
      (nS * τ + ∑ p ∈ smallP z₂ IsU1, max (gainD L μ p z₁ d - τ) 0) := by
  classical
  have hX1 : (((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSetD D b p₂ z₁)).card : ℝ) ≤
      ∑ p ∈ smallP z₂ (· ≠ 2), ((xSetD D b p z₁).card : ℝ) := by exact_mod_cast card_biUnion_le
  have hX5 := card_xSet5D_le hD hL hμ b z₁ hd
  set S := (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)).filter (fun p => p * p ∣ b * b + 1)
  have hodd : ∀ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), ((xSetD D b p z₁).card : ℝ) ≤
      nonD L μ p z₁ d + if p * p ∣ b * b + 1 then gainD L μ p z₁ d else 0 := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have := card_xSetD_le hD hL hμ b p z₁ hpp.1 hpp.2.1 hpp.2.2 hd
    unfold gainD
    split_ifs at this ⊢
    · have := le_max_left (wholeD L μ p - nonD L μ p z₁ d) 0; linarith
    · linarith
  have hsplit : ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5),
      (nonD L μ p z₁ d + if p * p ∣ b * b + 1 then gainD L μ p z₁ d else 0) =
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD L μ p z₁ d + ∑ p ∈ S, gainD L μ p z₁ d := by
    rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero]
  have hSU1 : ∀ p ∈ S, IsU1 p := fun p hp =>
    isU1_of_sq_dvd (mem_filter.mp (mem_filter.mp hp).1).2.1 (mem_filter.mp hp).2 hbs
  have hScard : S.card ≤ nS := by
    apply card_le_of_prefix S hSU1 xb nS _ hpre
    have hd' := prod_sq_dvd S (fun p hp => (hSU1 p hp).1) (fun p hp => (mem_filter.mp hp).2)
    have h1 := Nat.le_of_dvd (Nat.succ_pos _) hd'
    have h2 : b * b + 1 ≤ xb * xb + 1 := Nat.add_le_add_right (Nat.mul_le_mul hbx hbx) 1
    omega
  -- ∑_S gain ≤ |S| τ + ∑_S (gain - τ)⁺ ≤ nS τ + ∑_{U1 ≤ z₂} (gain - τ)⁺
  have hgain : ∑ p ∈ S, gainD L μ p z₁ d ≤
      nS * τ + ∑ p ∈ smallP z₂ IsU1, max (gainD L μ p z₁ d - τ) 0 := by
    have e1 : ∑ p ∈ S, gainD L μ p z₁ d ≤ ∑ p ∈ S, (τ + max (gainD L μ p z₁ d - τ) 0) :=
      sum_le_sum (fun p _ => by have := le_max_left (gainD L μ p z₁ d - τ) 0; linarith)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at e1
    have e2 : (S.card : ℝ) * τ ≤ nS * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) hτ
    have hsub : S ⊆ smallP z₂ IsU1 := fun p hp => by
      have := mem_filter.mp (mem_filter.mp hp).1
      simp only [smallP, mem_filter] at this ⊢
      exact ⟨this.1, this.2.1, hSU1 p hp⟩
    have e3 : ∑ p ∈ S, max (gainD L μ p z₁ d - τ) 0 ≤ ∑ p ∈ smallP z₂ IsU1, max (gainD L μ p z₁ d - τ) 0 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => le_max_right _ _)
    linarith
  have hsum5 : ∑ p ∈ smallP z₂ (· ≠ 2), ((xSetD D b p z₁).card : ℝ) =
      ((xSetD D b 5 z₁).card : ℝ) + ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), ((xSetD D b p z₁).card : ℝ) := by
    rw [smallP_odd_eq z₂ hz₂, sum_insert (by simp [smallP])]
  have := sum_le_sum hodd
  rw [hsplit] at this
  linarith

/-- **Lemma C on a good domain**, the core (everything except the U1 tail and the shared sets). -/
theorem card_lemCcore_le (hD : GoodDom D L μ Odd) (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (b xb z₁ z₂ pB pc nS : ℕ) (τ : ℝ) {d : ℕ} (hd : Odd d) (hbs : IsStar b) (hbx : b ≤ xb)
    (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ)
    (hpre : xb * xb + 1 < (∏ j ∈ range (nS + 1), u1 j) * (∏ j ∈ range (nS + 1), u1 j)) :
    ((lemCcore D b z₁ z₂ pB pc).card : ℝ) ≤
      23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * (L / 25 / (p * p)) + μ * 2) +
      ((L / 25 * mainU (smallP z₁ IsU1) d + μ * errU (smallP z₁ IsU1) d) +
        ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD L μ p z₁ d +
        (nS * τ + ∑ p ∈ smallP z₂ IsU1, max (gainD L μ p z₁ d - τ) 0)) +
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), (L / (p * p) + μ) := by
  classical
  have hU : (lemCcore D b z₁ z₂ pB pc).card ≤ (T25.biUnion (fun t => lcResD D t z₁ pB)).card +
      (((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSetD D b p₂ z₁)).card + (lcMidD D b z₂ pc).card) := by
    unfold lemCcore
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
  have hUR : ((lemCcore D b z₁ z₂ pB pc).card : ℝ) ≤ ((T25.biUnion (fun t => lcResD D t z₁ pB)).card : ℝ) +
      ((((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSetD D b p₂ z₁)).card : ℝ) + (lcMidD D b z₂ pc).card) := by
    exact_mod_cast hU
  have hR1 : ((T25.biUnion (fun t => lcResD D t z₁ pB)).card : ℝ) ≤
      23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * (L / 25 / (p * p)) + μ * 2) := by
    have h1 : ((T25.biUnion (fun t => lcResD D t z₁ pB)).card : ℝ) ≤
        ∑ t ∈ T25, ((lcResD D t z₁ pB).card : ℝ) := by exact_mod_cast card_biUnion_le
    have h2 := sum_le_sum (fun t (ht : t ∈ T25) =>
      card_lcResD_le hD hL hμ t z₁ pB (mem_range.mp (mem_filter.mp ht).1))
    rw [sum_const, show T25.card = 23 by decide, nsmul_eq_mul] at h2
    push_cast at h2
    linarith
  have hX := card_p2_le hD hL hμ b xb z₁ z₂ nS τ hd hbs hbx hz₂ hτ hpre
  have hM := card_lcMidD_le hD hL hμ b z₂ pc (by omega)
  linarith

end Erdos848
