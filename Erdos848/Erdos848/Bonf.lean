import Mathlib

/-!
# Phase 9.2: Bonferroni truncation

For finite sets `S i` (`i ∈ P`) and odd `d`,

  `|⋃ S i| ≤ ∑_{∅ ≠ T ⊆ P, |T| ≤ d} (-1)^{|T|+1} |⋂_{i ∈ T} S i|`   (`bonferroni_odd`).

Proof by double counting: an element lying in exactly `k ≥ 1` of the sets contributes
`∑_{1 ≤ j ≤ min(k,d)} (-1)^{j+1} C(k,j)`, which is `1` if `d ≥ k` and `1 + C(k-1,d)` otherwise.
-/

namespace Erdos848

open Finset

/-- The contribution of one element lying in `k ≥ 1` sets is at least one. -/
lemma alt_trunc_ge_one (k d : ℕ) (hk : 1 ≤ k) (hd : Odd d) :
    1 ≤ ∑ m ∈ range (k + 1),
      (k.choose m : ℤ) * (if 0 < m ∧ m ≤ d then (-1 : ℤ) ^ (m + 1) else 0) := by
  -- rewrite as (the m = 0 term put back) minus a partial alternating sum
  have hsplit : ∑ m ∈ range (k + 1),
      (k.choose m : ℤ) * (if 0 < m ∧ m ≤ d then (-1 : ℤ) ^ (m + 1) else 0) =
      1 - ∑ m ∈ (range (k + 1)).filter (· ≤ d), (-1 : ℤ) ^ m * k.choose m := by
    rw [sum_filter]
    have h0 : ∀ m ∈ range (k + 1),
        (k.choose m : ℤ) * (if 0 < m ∧ m ≤ d then (-1 : ℤ) ^ (m + 1) else 0) =
        -(if m ≤ d then (-1 : ℤ) ^ m * k.choose m else 0) + (if m = 0 then 1 else 0) := by
      intro m _
      by_cases hm : m = 0
      · subst hm; simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        by_cases hmd : m ≤ d
        · simp [hm, hmd, hmpos, pow_succ]; ring
        · simp [hm, hmd]
    rw [sum_congr rfl h0, sum_add_distrib, sum_neg_distrib, sum_ite_eq' (range (k + 1)) 0]
    simp
    ring
  rw [hsplit]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  by_cases hdk : n + 1 ≤ d
  · -- the whole alternating sum, which vanishes
    have hf : (range (n + 1 + 1)).filter (· ≤ d) = range (n + 1 + 1) := by
      ext m; simp only [mem_filter, mem_range]; omega
    rw [hf, Int.alternating_sum_range_choose_of_ne (by omega)]
    norm_num
  · have hf : (range (n + 1 + 1)).filter (· ≤ d) = range (d + 1) := by
      ext m; simp only [mem_filter, mem_range]; omega
    rw [hf, Int.alternating_sum_range_choose_eq_choose, hd.neg_one_pow]
    have : (0 : ℤ) ≤ n.choose d := by positivity
    linarith

/-- The truncated alternating sum over the nonempty subsets of `K` of size at most `d`. -/
lemma trunc_sum_powerset {ι : Type*} (K : Finset ι) (d : ℕ) :
    ∑ T ∈ K.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d), (-1 : ℤ) ^ (T.card + 1) =
      ∑ m ∈ range (K.card + 1),
        (K.card.choose m : ℤ) * (if 0 < m ∧ m ≤ d then (-1 : ℤ) ^ (m + 1) else 0) := by
  rw [sum_filter]
  have : ∀ T ∈ K.powerset, (if T.Nonempty ∧ T.card ≤ d then (-1 : ℤ) ^ (T.card + 1) else 0) =
      (fun m => if 0 < m ∧ m ≤ d then (-1 : ℤ) ^ (m + 1) else 0) T.card := by
    intro T _
    simp only [card_pos]
  rw [sum_congr rfl this]
  exact (sum_powerset_apply_card
    (fun m => if 0 < m ∧ m ≤ d then (-1 : ℤ) ^ (m + 1) else 0)).trans (by simp only [nsmul_eq_mul])

/-- **Bonferroni inequality** at odd depth `d`, with the intersections taken inside the union. -/
theorem bonferroni_odd {ι α : Type*} [DecidableEq ι] [DecidableEq α] (P : Finset ι)
    (S : ι → Finset α) (d : ℕ) (hd : Odd d) :
    ((P.biUnion S).card : ℤ) ≤ ∑ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      (-1 : ℤ) ^ (T.card + 1) * ((P.biUnion S).filter (fun x => ∀ i ∈ T, x ∈ S i)).card := by
  set U := P.biUnion S
  -- the sets containing a given element
  let K : α → Finset ι := fun x => P.filter (fun i => x ∈ S i)
  -- swap the order of summation
  have hswap : ∑ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      (-1 : ℤ) ^ (T.card + 1) * (U.filter (fun x => ∀ i ∈ T, x ∈ S i)).card =
      ∑ x ∈ U, ∑ T ∈ (K x).powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
        (-1 : ℤ) ^ (T.card + 1) := by
    have h1 : ∀ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
        (-1 : ℤ) ^ (T.card + 1) * (U.filter (fun x => ∀ i ∈ T, x ∈ S i)).card =
        ∑ x ∈ U, if (∀ i ∈ T, x ∈ S i) then (-1 : ℤ) ^ (T.card + 1) else 0 := by
      intro T _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rw [sum_congr rfl h1, sum_comm]
    apply sum_congr rfl
    intro x _
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [mem_filter, mem_powerset, K]
    constructor
    · rintro ⟨⟨hTP, hne⟩, hx⟩
      exact ⟨fun i hi => mem_filter.mpr ⟨hTP hi, hx i hi⟩, hne⟩
    · rintro ⟨hTK, hne⟩
      exact ⟨⟨fun i hi => (mem_filter.mp (hTK hi)).1, hne⟩, fun i hi => (mem_filter.mp (hTK hi)).2⟩
  rw [hswap]
  have hcard : (U.card : ℤ) = ∑ x ∈ U, (1 : ℤ) := by simp
  rw [hcard]
  apply sum_le_sum
  intro x hx
  have hK : 1 ≤ (K x).card := by
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    exact card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hxi⟩⟩
  rw [trunc_sum_powerset]
  exact alt_trunc_ge_one _ d hK hd

/-! ### The truncated alternating sums of products -/

/-- `E_d(P) = ∑_{T ⊆ P, |T| ≤ d} (-1)^{|T|} ∏_{p ∈ T} v p`. -/
noncomputable def altE (P : Finset ℕ) (v : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ T ∈ P.powerset.filter (fun T => T.card ≤ d), (-1 : ℝ) ^ T.card * ∏ p ∈ T, v p

lemma altE_empty (v : ℕ → ℝ) (d : ℕ) : altE ∅ v d = 1 := by
  unfold altE; rw [powerset_empty, filter_singleton, if_pos (by simp)]; simp

lemma altE_insert {a : ℕ} {P : Finset ℕ} (ha : a ∉ P) (v : ℕ → ℝ) (d : ℕ) :
    altE (insert a P) v d = altE P v d - (if d = 0 then 0 else v a * altE P v (d - 1)) := by
  unfold altE
  rw [sum_filter, sum_powerset_insert ha, ← sum_filter]
  congr 1
  have h1 : ∀ T ∈ P.powerset, (if (insert a T).card ≤ d then
      (-1 : ℝ) ^ (insert a T).card * ∏ p ∈ insert a T, v p else 0) =
      -(if d = 0 then 0 else v a * (if T.card ≤ d - 1 then (-1 : ℝ) ^ T.card * ∏ p ∈ T, v p else 0)) := by
    intro T hT
    have haT : a ∉ T := fun h => ha (mem_powerset.mp hT h)
    rw [card_insert_of_notMem haT, prod_insert haT]
    by_cases hd : d = 0
    · simp [hd]
    · by_cases hc : T.card ≤ d - 1
      · rw [if_pos (by omega), if_neg hd, if_pos hc, pow_succ]; ring
      · rw [if_neg (by omega), if_neg hd, if_neg hc]; ring
  rw [sum_congr rfl h1, sum_neg_distrib]
  by_cases hd : d = 0
  · simp [hd]
  · simp only [hd, if_false, ← mul_sum, sum_filter]

/-- Bonferroni for products: even truncations bound `∏ (1 - v)` from above, odd ones from below. -/
theorem altE_sandwich (v : ℕ → ℝ) : ∀ (P : Finset ℕ), (∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1) →
    ∀ d, (Even d → ∏ p ∈ P, (1 - v p) ≤ altE P v d) ∧ (Odd d → altE P v d ≤ ∏ p ∈ P, (1 - v p)) := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ d
    simp only [altE_empty, prod_empty]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | insert a P ha ih =>
    intro hv d
    have hvP : ∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1 := fun p hp => hv p (mem_insert_of_mem hp)
    have hva := hv a (mem_insert_self a P)
    have hpos : 0 ≤ ∏ p ∈ P, (1 - v p) :=
      prod_nonneg (fun p hp => by linarith [(hvP p hp).2])
    rw [altE_insert ha, prod_insert ha]
    rcases Nat.even_or_odd d with he | ho
    · refine ⟨fun _ => ?_, fun h => absurd h (Nat.not_odd_iff_even.mpr he)⟩
      by_cases hd0 : d = 0
      · rw [if_pos hd0]
        have := (ih hvP d).1 he
        nlinarith [hva.1]
      · rw [if_neg hd0]
        have h1 := (ih hvP d).1 he
        have h2 := (ih hvP (d - 1)).2 (by rcases he with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩)
        nlinarith [hva.1]
    · refine ⟨fun h => absurd ho (Nat.not_odd_iff_even.mpr h), fun _ => ?_⟩
      have hd0 : d ≠ 0 := by rintro rfl; exact absurd ho (by decide)
      rw [if_neg hd0]
      have h1 := (ih hvP d).2 ho
      have h2 := (ih hvP (d - 1)).1 (by rcases ho with ⟨k, hk⟩; exact ⟨k, by omega⟩)
      nlinarith [hva.1]

lemma altE_congr {P : Finset ℕ} {v w : ℕ → ℝ} (h : ∀ p ∈ P, v p = w p) (d : ℕ) :
    altE P v d = altE P w d := by
  unfold altE
  apply sum_congr rfl
  intro T hT
  rw [prod_congr rfl (fun p hp => h p (mem_powerset.mp (mem_filter.mp hT).1 hp))]

/-- Odd truncations are antitone in one coordinate. -/
lemma altE_odd_anti_one {P : Finset ℕ} {a : ℕ} (haP : a ∈ P) {v w : ℕ → ℝ}
    (hvw : ∀ p ∈ P, p ≠ a → v p = w p) (hva : v a ≤ w a)
    (hv : ∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1) {d : ℕ} (hd : Odd d) :
    altE P w d ≤ altE P v d := by
  have hd0 : d ≠ 0 := by rintro rfl; exact absurd hd (by decide)
  set P' := P.erase a
  have hP : P = insert a P' := (insert_erase haP).symm
  have ha' : a ∉ P' := notMem_erase a P
  rw [hP, altE_insert ha', altE_insert ha', if_neg hd0, if_neg hd0]
  have hcong : ∀ e, altE P' v e = altE P' w e :=
    fun e => altE_congr (fun p hp => hvw p (mem_of_mem_erase hp) (ne_of_mem_erase hp)) e
  rw [← hcong d, ← hcong (d - 1)]
  have hv' : ∀ p ∈ P', 0 ≤ v p ∧ v p ≤ 1 := fun p hp => hv p (mem_of_mem_erase hp)
  have h2 := (altE_sandwich v P' hv' (d - 1)).1 (by rcases hd with ⟨k, hk⟩; exact ⟨k, by omega⟩)
  have hpos : 0 ≤ ∏ p ∈ P', (1 - v p) := prod_nonneg (fun p hp => by linarith [(hv' p hp).2])
  nlinarith

/-- Odd truncations are antitone: `v ≤ w` on `P` (values in `[0,1]`) gives `E_d(w) ≤ E_d(v)`. -/
theorem altE_odd_anti {P : Finset ℕ} {v w : ℕ → ℝ} (hvw : ∀ p ∈ P, v p ≤ w p)
    (hv : ∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) {d : ℕ} (hd : Odd d) :
    altE P w d ≤ altE P v d := by
  classical
  -- switch the coordinates of `Q` from `v` to `w`, one at a time
  let mix : Finset ℕ → ℕ → ℝ := fun Q p => if p ∈ Q then w p else v p
  have key : ∀ Q : Finset ℕ, Q ⊆ P → altE P (mix Q) d ≤ altE P v d := by
    intro Q
    induction Q using Finset.induction_on with
    | empty => intro _; exact le_of_eq (altE_congr (fun p _ => by simp [mix]) d)
    | insert b Q hb ih =>
      intro hQP
      have hbP : b ∈ P := hQP (mem_insert_self b Q)
      refine le_trans ?_ (ih (fun p hp => hQP (mem_insert_of_mem hp)))
      apply altE_odd_anti_one hbP
      · intro p _ hpb; simp [mix, hpb]
      · simp [mix, hb]; exact hvw b hbP
      · intro p hp; simp only [mix]; split_ifs
        · exact hw p hp
        · exact hv p hp
      · exact hd
  have := key P subset_rfl
  rw [altE_congr (v := mix P) (w := w) (fun p hp => by simp [mix, hp]) d] at this
  exact this

end Erdos848
