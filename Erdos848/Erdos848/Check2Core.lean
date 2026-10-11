import Erdos848.Check2Comp

/-!
# Soundness of the §10 checker, part 3: Lemma C (`coreB`)

`coreB_le`: for `0 ≤ L₀ ≤ L₄ / 4`, the threshold `τ = T / SF` chosen by the checker gives
`coreB L₀ μ … τ ≤ coreF (cConst …) (mkCF …) L₄ μ nS`, provided the checker's side conditions
`cConstOK` hold (they make `coreB` monotone in `L`).  `coreF` evaluates the sums over the primes
`≤ z₂` in fixed point; the rounding lemmas are in the section *Fixed point*.
-/

namespace Erdos848

open Finset ErdosComp

/-! ### List sums -/

lemma zip_map_self {α β γ : Type*} (g : α → β → γ) (me : α → β) :
    ∀ l : List α, (l.zip (l.map me)).map (fun pm => g pm.1 pm.2) = l.map (fun p => g p (me p))
  | [] => rfl
  | p :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self g me l]

lemma sumN_eq : ∀ l : List ℕ, sumN l = l.sum
  | [] => rfl
  | x :: l => by simp only [sumN, List.sum_cons, sumN_eq l]

/-! ### Fixed point -/

lemma SF_pos : (0 : ℚ) < SF := by unfold SF; positivity

lemma ceilF_ge (x : ℚ) : x * SF ≤ (ceilF x : ℚ) := by
  unfold ceilF
  have e : (-(-(x * SF)).floor : ℤ) = ⌈x * SF⌉ := by
    change -⌊-(x * SF)⌋ = _
    rw [Int.floor_neg, neg_neg]
  rw [e]
  have h1 := Int.le_ceil (x * SF)
  have h2 : ⌈x * SF⌉ ≤ (⌈x * SF⌉.toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((⌈x * SF⌉ : ℤ) : ℚ) ≤ ((⌈x * SF⌉.toNat : ℤ) : ℚ) := by exact_mod_cast h2
  push_cast at h3
  linarith

lemma floorF_le (x : ℚ) (hx : 0 ≤ x) : (floorF x : ℚ) ≤ x * SF := by
  unfold floorF
  change ((⌊x * SF⌋.toNat : ℕ) : ℚ) ≤ _
  have h0 : 0 ≤ ⌊x * SF⌋ := Int.floor_nonneg.mpr (mul_nonneg hx SF_pos.le)
  have h1 := Int.floor_le (x * SF)
  have h2 : ((⌊x * SF⌋.toNat : ℤ) : ℚ) = ((⌊x * SF⌋ : ℤ) : ℚ) := by rw [Int.toNat_of_nonneg h0]
  push_cast at h2
  linarith

lemma cdiv_ge (a b : ℕ) : (a : ℚ) / b ≤ (cdiv a b : ℚ) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  unfold cdiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ((a + b - 1) / b) := by
    set q := (a + b - 1) / b
    set r := (a + b - 1) % b
    omega
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have : (a : ℚ) ≤ b * ((a + b - 1) / b : ℕ) := by exact_mod_cast h3
  linarith

lemma div_floor_le (a b : ℕ) : (((a / b : ℕ) : ℚ)) ≤ (a : ℚ) / b := Nat.cast_div_le

lemma natSub_ge (a b : ℕ) : (a : ℚ) - b ≤ ((a - b : ℕ) : ℚ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℚ) ≤ b := by exact_mod_cast h
    push_cast; linarith

lemma nonUp_ge (L4 μ p : ℕ) (m : ℚ × ℚ) :
    nonQ ((L4 : ℚ) / 4) μ p m * SF ≤ (nonUp L4 μ (mkPC p m) : ℚ) := by
  unfold nonQ nonUp mkPC
  dsimp only
  have hA := ceilF_ge (m.1 / ((p : ℚ) * p))
  have hB := ceilF_ge m.2
  have hL : (0 : ℚ) ≤ L4 := Nat.cast_nonneg _
  have hμ : (0 : ℚ) ≤ μ := Nat.cast_nonneg _
  have c1 := cdiv_ge (L4 * ceilF (m.1 / ((p : ℚ) * p))) 4
  have c2 := cdiv_ge (23 * L4 * ceilF (m.1 / ((p : ℚ) * p))) 100
  push_cast at c1 c2 ⊢
  rw [min_mul_of_nonneg _ _ SF_pos.le]
  apply min_le_min
  · have e : ((L4 : ℚ) / 4 / ((p : ℚ) * p) * m.1 + μ * m.2) * SF =
        (L4 : ℚ) / 4 * (m.1 / ((p : ℚ) * p) * SF) + μ * (m.2 * SF) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℚ) ≤ (L4 : ℚ) / 4)
    have := mul_le_mul_of_nonneg_left hB hμ
    nlinarith
  · have e : (23 / 25 * ((L4 : ℚ) / 4 / ((p : ℚ) * p)) * m.1 + 23 * μ * m.2) * SF =
        23 * (L4 : ℚ) / 100 * (m.1 / ((p : ℚ) * p) * SF) + 23 * μ * (m.2 * SF) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℚ) ≤ 23 * (L4 : ℚ) / 100)
    have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℚ) ≤ 23 * μ)
    nlinarith

lemma nonLo_le (L4 μ p : ℕ) (m : ℚ × ℚ) (h1 : 0 ≤ m.1) (h2 : 0 ≤ m.2) :
    (nonLo L4 μ (mkPC p m) : ℚ) ≤ nonQ ((L4 : ℚ) / 4) μ p m * SF := by
  unfold nonQ nonLo mkPC
  dsimp only
  have hA := floorF_le (m.1 / ((p : ℚ) * p)) (by positivity)
  have hB := floorF_le m.2 h2
  have hL : (0 : ℚ) ≤ L4 := Nat.cast_nonneg _
  have hμ : (0 : ℚ) ≤ μ := Nat.cast_nonneg _
  have c1 := div_floor_le (L4 * floorF (m.1 / ((p : ℚ) * p))) 4
  have c2 := div_floor_le (23 * L4 * floorF (m.1 / ((p : ℚ) * p))) 100
  push_cast at c1 c2 ⊢
  rw [min_mul_of_nonneg _ _ SF_pos.le]
  apply min_le_min
  · have e : ((L4 : ℚ) / 4 / ((p : ℚ) * p) * m.1 + μ * m.2) * SF =
        (L4 : ℚ) / 4 * (m.1 / ((p : ℚ) * p) * SF) + μ * (m.2 * SF) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℚ) ≤ (L4 : ℚ) / 4)
    have := mul_le_mul_of_nonneg_left hB hμ
    nlinarith
  · have e : (23 / 25 * ((L4 : ℚ) / 4 / ((p : ℚ) * p)) * m.1 + 23 * μ * m.2) * SF =
        23 * (L4 : ℚ) / 100 * (m.1 / ((p : ℚ) * p) * SF) + 23 * μ * (m.2 * SF) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℚ) ≤ 23 * (L4 : ℚ) / 100)
    have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℚ) ≤ 23 * μ)
    nlinarith

lemma gainUp_ge (L4 μ p : ℕ) (m : ℚ × ℚ) (h1 : 0 ≤ m.1) (h2 : 0 ≤ m.2) :
    gainQ ((L4 : ℚ) / 4) μ p m * SF ≤ (gainUp L4 μ (mkPC p m) : ℚ) := by
  have hlo := nonLo_le L4 μ p m h1 h2
  unfold gainQ gainUp
  rw [max_mul_of_nonneg _ _ SF_pos.le, zero_mul]
  apply max_le _ (Nat.cast_nonneg _)
  refine le_trans ?_ (natSub_ge _ _)
  have hw := cdiv_ge SF (p * p)
  have c := cdiv_ge (23 * L4 * cdiv SF (p * p)) 100
  have hL : (0 : ℚ) ≤ L4 := Nat.cast_nonneg _
  unfold mkPC at hlo ⊢
  dsimp only at hlo ⊢
  push_cast at hw c hlo ⊢
  have e : (wholeQ ((L4 : ℚ) / 4) μ p - nonQ ((L4 : ℚ) / 4) μ p m) * SF =
      23 * (L4 : ℚ) / 100 * (SF / ((p : ℚ) * p)) + 3 * μ * SF -
        nonQ ((L4 : ℚ) / 4) μ p m * SF := by unfold wholeQ; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℚ) ≤ 23 * (L4 : ℚ) / 100)
  nlinarith

/-- `max (g - T/SF) 0 ≤ (G - T)/SF` when `g · SF ≤ G`. -/
lemma tauTerm_le (g : ℚ) (G T : ℕ) (h : g * SF ≤ G) :
    max (g - T / SF) 0 ≤ ((G - T : ℕ) : ℚ) / SF := by
  have hS := SF_pos
  apply max_le
  · rw [le_div_iff₀ hS]
    have := natSub_ge G T
    have e : (g - T / SF) * SF = g * SF - T := by field_simp
    rw [e]; linarith
  · positivity

/-! ### Casts of the pieces -/

lemma mainUL_cast (l : List ℕ) (hl : l.Nodup) (d : ℕ) :
    mainU l.toFinset d = ((mainUL l d : ℚ) : ℝ) := by
  unfold mainU mainUL
  push_cast
  rw [← altE_toFinset _ _ hl]
  congr 1
  apply altE_congr; intro p _; simp [invSq]

lemma errUL_cast (l : List ℕ) (hl : l.Nodup) (d : ℕ) :
    errU l.toFinset d = ((errUL l d : ℚ) : ℝ) := by
  unfold errU errUL
  rw [← List.toFinset_card_of_nodup hl, ← truncErr_const]
  simp

lemma mainU_U (z₁ d : ℕ) : mainU (smallP z₁ IsU1) d = ((mainUL (u1UpTo z₁) d : ℚ) : ℝ) := by
  rw [← u1UpTo_toFinset, mainUL_cast _ (u1UpTo_nodup z₁)]

lemma errU_U (z₁ d : ℕ) : errU (smallP z₁ IsU1) d = ((errUL (u1UpTo z₁) d : ℚ) : ℝ) := by
  rw [← u1UpTo_toFinset, errUL_cast _ (u1UpTo_nodup z₁)]

lemma mainU_Uer (z₁ p d : ℕ) : mainU (Uer z₁ p) d = ((mainUL ((u1UpTo z₁).erase p) d : ℚ) : ℝ) := by
  rw [← u1UpTo_erase_toFinset, mainUL_cast _ (u1UpTo_erase_nodup z₁ p)]

lemma errU_Uer (z₁ p d : ℕ) : errU (Uer z₁ p) d = ((errUL ((u1UpTo z₁).erase p) d : ℚ) : ℝ) := by
  rw [← u1UpTo_erase_toFinset, errUL_cast _ (u1UpTo_erase_nodup z₁ p)]

/-- The pair `(mainU, errU)` of `Uer z₁ p`. -/
def meU (z₁ d p : ℕ) : ℚ × ℚ := (mainUL ((u1UpTo z₁).erase p) d, errUL ((u1UpTo z₁).erase p) d)

lemma nonD_cast (L μ : ℚ) (p z₁ d : ℕ) :
    nonD (L : ℝ) (μ : ℝ) p z₁ d = ((nonQ L μ p (meU z₁ d p) : ℚ) : ℝ) := by
  unfold nonD nonQ meU
  rw [mainU_Uer, errU_Uer]
  push_cast
  rfl

lemma gainD_cast (L μ : ℚ) (p z₁ d : ℕ) :
    gainD (L : ℝ) (μ : ℝ) p z₁ d = ((gainQ L μ p (meU z₁ d p) : ℚ) : ℝ) := by
  unfold gainD gainQ wholeD wholeQ
  rw [nonD_cast]
  push_cast
  rfl

/-! ### Monotonicity in `L` -/

lemma nonD_mono {L₀ L μ : ℝ} (h0 : 0 ≤ L₀) (hL : L₀ ≤ L) (p z₁ d : ℕ) (hm : 0 ≤ mainU (Uer z₁ p) d) :
    nonD L₀ μ p z₁ d ≤ nonD L μ p z₁ d := by
  unfold nonD
  have hx : L₀ / ((p : ℝ) * p) ≤ L / ((p : ℝ) * p) := by gcongr
  apply min_le_min
  · nlinarith
  · nlinarith

lemma sub_min_le_sub_min {W₀ W a₀ a c₀ c : ℝ} (ha : W₀ - a₀ ≤ W - a) (hc : W₀ - c₀ ≤ W - c) :
    W₀ - min a₀ c₀ ≤ W - min a c := by
  rcases min_choice a c with e | e <;> rw [e] <;>
    rcases min_choice a₀ c₀ with e₀ | e₀ <;> rw [e₀]
  · exact ha
  · have := min_le_right a c; rw [e] at this; linarith
  · have := min_le_left a c; rw [e] at this; linarith
  · exact hc

lemma gainD_mono {L₀ L μ : ℝ} (h0 : 0 ≤ L₀) (hL : L₀ ≤ L) (p z₁ d : ℕ)
    (hm0 : 0 ≤ mainU (Uer z₁ p) d) (hm1 : mainU (Uer z₁ p) d ≤ 23 / 25) :
    gainD L₀ μ p z₁ d ≤ gainD L μ p z₁ d := by
  unfold gainD wholeD nonD
  apply max_le_max _ le_rfl
  have hx : L₀ / ((p : ℝ) * p) ≤ L / ((p : ℝ) * p) := by gcongr
  apply sub_min_le_sub_min <;> nlinarith

/-! ### `coreB` -/

lemma errUL_nonneg (l : List ℕ) (d : ℕ) : 0 ≤ errUL l d := by
  unfold errUL
  induction d with
  | zero => simp [terrL]
  | succ d ih => simp only [terrL]; positivity

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

omit hlk in
lemma cConstOK_eq (z₁ z₂ pB pc d : ℕ) : cConstOK (cConst lk z₁ z₂ pB pc d) =
    (decide (0 ≤ mainUL (u1UpTo z₁) d) &&
      ((primesEx z₂ [2, 5]).map (meU z₁ d)).all (fun m => decide (0 ≤ m.1)) &&
      ((u1UpTo z₂).map (meU z₁ d)).all (fun m => decide (0 ≤ m.1) && decide (m.1 ≤ 23 / 25))) := rfl

omit hlk in
lemma mkCF_non (z₁ z₂ pB pc d : ℕ) : (mkCF (cConst lk z₁ z₂ pB pc d)).non =
    (primesEx z₂ [2, 5]).map (fun p => mkPC p (meU z₁ d p)) :=
  zip_map_self (fun p m => mkPC p m) (meU z₁ d) _

omit hlk in
lemma mkCF_gain (z₁ z₂ pB pc d : ℕ) : (mkCF (cConst lk z₁ z₂ pB pc d)).gain =
    (u1UpTo z₂).map (fun p => mkPC p (meU z₁ d p)) :=
  zip_map_self (fun p m => mkPC p m) (meU z₁ d) _

omit hlk in
lemma smallP_odd25 (z₂ : ℕ) : smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5) = (primesEx z₂ [2, 5]).toFinset := by
  rw [primesEx_toFinset z₂ {2, 5} [2, 5] (by intro p; simp)]
  unfold smallP
  apply filter_congr
  intro p _
  simp

/-- **Lemma C as computed by the checker.** -/
theorem coreB_le (z₁ z₂ pB pc d nS L4 μ : ℕ) (L₀ : ℝ) (h0 : 0 ≤ L₀) (hL : L₀ ≤ (L4 : ℝ) / 4)
    (hok : cConstOK (cConst lk z₁ z₂ pB pc d) = true) :
    ∃ τ : ℝ, 0 ≤ τ ∧ coreB L₀ μ z₁ z₂ pB pc nS d τ ≤
      ((coreF (cConst lk z₁ z₂ pB pc d) (mkCF (cConst lk z₁ z₂ pB pc d)) L4 μ nS : ℚ) : ℝ) := by
  rw [cConstOK_eq] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map] at hok
  obtain ⟨⟨hmU, hnon⟩, hgain⟩ := hok
  set cc := cConst lk z₁ z₂ pB pc d with hcc
  set gs := (mkCF cc).gain.map (gainUp L4 μ) with hgs
  set T := kthN (nS - 1) gs
  have hS : (0 : ℚ) < SF := SF_pos
  refine ⟨((T : ℚ) / SF : ℚ), by positivity, ?_⟩
  set L : ℚ := (L4 : ℚ) / 4 with hLdef
  have hμR : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
  have hLR : (0 : ℝ) ≤ (L : ℝ) := by rw [hLdef]; positivity
  have hL' : L₀ ≤ (L : ℝ) := by rw [hLdef]; push_cast; exact hL
  -- facts about the pieces
  have hmUR : 0 ≤ mainU (smallP z₁ IsU1) d := by rw [mainU_U]; exact_mod_cast hmU
  have hnonR : ∀ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), 0 ≤ mainU (Uer z₁ p) d := by
    intro p hp
    rw [smallP_odd25, List.mem_toFinset] at hp
    have := hnon _ ⟨p, hp, rfl⟩
    simp only [meU] at this
    rw [mainU_Uer]; exact_mod_cast this
  have hgainR : ∀ p ∈ smallP z₂ IsU1, 0 ≤ mainU (Uer z₁ p) d ∧ mainU (Uer z₁ p) d ≤ 23 / 25 := by
    intro p hp
    rw [← u1UpTo_toFinset, List.mem_toFinset] at hp
    have := hgain _ ⟨p, hp, rfl⟩
    simp only [meU] at this
    rw [mainU_Uer]
    refine ⟨by exact_mod_cast this.1, ?_⟩
    have h2 := (Rat.cast_le (K := ℝ)).mpr this.2
    push_cast at h2
    exact h2
  -- step 1: monotonicity in `L`
  have hmono : coreB L₀ μ z₁ z₂ pB pc nS d ((T : ℚ) / SF : ℚ) ≤
      coreB (L : ℝ) μ z₁ z₂ pB pc nS d ((T : ℚ) / SF : ℚ) := by
    unfold coreB
    have s1 : ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * (L₀ / 25 / (p * p)) + (μ : ℝ) * 2) ≤
        ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((L : ℝ) / 25 / (p * p)) + (μ : ℝ) * 2) := by
      apply sum_le_sum; intro p _; gcongr
    have s2 : L₀ / 25 * mainU (smallP z₁ IsU1) d ≤ (L : ℝ) / 25 * mainU (smallP z₁ IsU1) d := by
      gcongr
    have s3 : ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD L₀ μ p z₁ d ≤
        ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD (L : ℝ) μ p z₁ d :=
      sum_le_sum (fun p hp => nonD_mono h0 hL' p z₁ d (hnonR p hp))
    have s4 : ∑ p ∈ smallP z₂ IsU1, max (gainD L₀ μ p z₁ d - ((T : ℚ) / SF : ℚ)) 0 ≤
        ∑ p ∈ smallP z₂ IsU1, max (gainD (L : ℝ) μ p z₁ d - ((T : ℚ) / SF : ℚ)) 0 := by
      apply sum_le_sum; intro p hp
      have := gainD_mono (μ := μ) h0 hL' p z₁ d (hgainR p hp).1 (hgainR p hp).2
      exact max_le_max (by linarith) le_rfl
    have s5 : ∑ p ∈ midP z₂ pc (fun p => z₂ < p), (L₀ / (p * p) + (μ : ℝ)) ≤
        ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((L : ℝ) / (p * p) + μ) := by
      apply sum_le_sum; intro p _; gcongr
    linarith
  refine hmono.trans ?_
  -- step 2: the value at `L`
  unfold coreB
  have e1 : ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((L : ℝ) / 25 / (p * p)) + (μ : ℝ) * 2) ≤
      2 * ((L : ℝ) / 25 * ((S2Uk lk z₁ pB : ℚ) : ℝ) + μ * ((CUk lk z₁ pB : ℚ) : ℝ)) := by
    have := u1SumK' hlk z₁ pB (fun p => IsU1 p ∧ z₁ < p) (fun _ h => h.1) ((L : ℝ) / 25) μ
      (by positivity) hμR
    have he : ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((L : ℝ) / 25 / (p * p)) + (μ : ℝ) * 2) =
        2 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), ((L : ℝ) / 25 / ((p : ℝ) * p) + μ) := by
      rw [mul_sum]; apply sum_congr rfl; intro p _; ring
    rw [he]; linarith
  -- the sum over the odd primes `≤ z₂`
  have e2 : ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD (L : ℝ) μ p z₁ d ≤
      ((sumN ((mkCF cc).non.map (nonUp L4 μ)) : ℚ) / SF : ℚ) := by
    rw [smallP_odd25, List.sum_toFinset _ (primesEx_nodup z₂ [2, 5])]
    have hq : ((primesEx z₂ [2, 5]).map (fun p => nonQ L μ p (meU z₁ d p))).sum * SF ≤
        (sumN ((mkCF cc).non.map (nonUp L4 μ)) : ℚ) := by
      rw [hcc, mkCF_non, sumN_eq, List.map_map, Nat.cast_list_sum, List.map_map,
        ← List.sum_map_mul_right]
      apply List.sum_le_sum
      intro p _
      simp only [Function.comp_apply]
      exact nonUp_ge L4 μ p (meU z₁ d p)
    have hq' : ((primesEx z₂ [2, 5]).map (fun p => nonQ L μ p (meU z₁ d p))).sum ≤
        (sumN ((mkCF cc).non.map (nonUp L4 μ)) : ℚ) / SF := by
      rw [le_div_iff₀ hS]; exact hq
    have hc : ((primesEx z₂ [2, 5]).map (fun p => nonD (L : ℝ) μ p z₁ d)).sum =
        ((((primesEx z₂ [2, 5]).map (fun p => nonQ L μ p (meU z₁ d p))).sum : ℚ) : ℝ) := by
      rw [Rat.cast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      have := nonD_cast L μ p z₁ d
      push_cast at this
      simp only [Function.comp_apply]
      exact this
    rw [hc]
    exact_mod_cast hq'
  -- the gains
  have e3 : (nS : ℝ) * (((T : ℚ) / SF : ℚ) : ℝ) +
      ∑ p ∈ smallP z₂ IsU1, max (gainD (L : ℝ) μ p z₁ d - ((T : ℚ) / SF : ℚ)) 0 ≤
      ((((nS * T + sumN (gs.map (· - T)) : ℕ) : ℚ) / SF : ℚ) : ℝ) := by
    rw [← u1UpTo_toFinset, List.sum_toFinset _ (u1UpTo_nodup z₂)]
    have hq0 : ((u1UpTo z₂).map (fun p => max (gainQ L μ p (meU z₁ d p) - (T : ℚ) / SF) 0)).sum * SF ≤
        (sumN (gs.map (· - T)) : ℚ) := by
      rw [hgs, hcc, mkCF_gain, sumN_eq, List.map_map, List.map_map, Nat.cast_list_sum, List.map_map,
        ← List.sum_map_mul_right]
      apply List.sum_le_sum
      intro p hp
      simp only [Function.comp_apply]
      have hm := hgain _ ⟨p, hp, rfl⟩
      have := tauTerm_le _ _ T (gainUp_ge L4 μ p (meU z₁ d p) hm.1 (errUL_nonneg _ _))
      rwa [le_div_iff₀ hS] at this
    have hq : ((u1UpTo z₂).map (fun p => max (gainQ L μ p (meU z₁ d p) - (T : ℚ) / SF) 0)).sum ≤
        (sumN (gs.map (· - T)) : ℚ) / SF := by
      rw [le_div_iff₀ hS]; exact hq0
    have hc : ((u1UpTo z₂).map (fun p => max (gainD (L : ℝ) μ p z₁ d - (((T : ℚ) / SF : ℚ) : ℝ)) 0)).sum =
        ((((u1UpTo z₂).map (fun p => max (gainQ L μ p (meU z₁ d p) - (T : ℚ) / SF) 0)).sum : ℚ) : ℝ) := by
      rw [Rat.cast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      have := gainD_cast L μ p z₁ d
      push_cast at this
      simp only [Function.comp_apply]
      rw [this]
      norm_cast
    rw [hc]
    have hq' := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hq' ⊢
    rw [add_div, mul_div_assoc]
    linarith
  have e4 : ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((L : ℝ) / (p * p) + μ) ≤
      (L : ℝ) * ((S2Pk lk z₂ pc : ℚ) : ℝ) + μ * ((CPk lk z₂ pc : ℚ) : ℝ) :=
    primeSumK' hlk z₂ pc (fun p => z₂ < p) L μ hLR hμR
  have hF : coreF cc (mkCF cc) L4 μ nS =
      23 * (2 * (L / 25) * S2Uk lk z₁ pB + μ * 2 * CUk lk z₁ pB) +
        (L / 25 * mainUL (u1UpTo z₁) d + μ * errUL (u1UpTo z₁) d) +
        ((sumN ((mkCF cc).non.map (nonUp L4 μ)) + (nS * T + sumN (gs.map (· - T))) : ℕ) : ℚ) / SF +
        (L * S2Pk lk z₂ pc + μ * CPk lk z₂ pc) := rfl
  rw [hF, mainU_U, errU_U]
  have e5 : ((((sumN ((mkCF cc).non.map (nonUp L4 μ)) + (nS * T + sumN (gs.map (· - T))) : ℕ) : ℚ) / SF :
      ℚ) : ℝ) = (((sumN ((mkCF cc).non.map (nonUp L4 μ)) : ℚ) / SF : ℚ) : ℝ) +
        ((((nS * T + sumN (gs.map (· - T)) : ℕ) : ℚ) / SF : ℚ) : ℝ) := by
    push_cast; ring
  push_cast at e1 e2 e3 e4 e5 ⊢
  nlinarith [e1, e2, e3, e4, e5]

end

end Erdos848
