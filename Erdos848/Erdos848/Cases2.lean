import Erdos848.LemmaC2
import Erdos848.Skeleton2
import Erdos848.Cases

/-!
# Phase 9.7 (part 1): building blocks for the case bounds of §10.6

* `rPartI`, `card_rPartI_le`: one class mod `q` of `[m, N]`, sieved by a witness (Lemma A′(iii)
  on an interval, with Bonferroni depth `dA`); the bound `resR`.
* `bad_part_cover`: a class part of `A₇ ∪ A₁₈` above `m` lies in `rPartI ∪ Mid(b) ∪ Ex(b)`.
* `card_midSet_le_floor` (Lemma M): `#Mid(b) ≤ ∑_{p_c < p ≤ Y} (⌊N/p²⌋ + 1)`.
* `lemBcoreI`, `card_lemBcoreI_le`, `star_cover_B`: the star part by Lemma B on `[m, N]`.
* `star_cover_C`: the star part by Lemma C′ on `[b, N] ∩ (r + 4ℤ)`.
-/

namespace Erdos848

open Finset

/-! ### Lemma A′(iii) on an interval -/

/-- One class `t` mod `q` of `[m, N]`, with a non-excluded prime `p ≤ p_c` and `p² ∣ ab + 1`. -/
def rPartI (N m b q t pc : ℕ) (excl : Finset ℕ) : Finset ℕ :=
  (Icc m N).filter (fun a => a % q = t ∧ ∃ p ≤ pc, p.Prime ∧ p ∉ excl ∧ a % (p * p) ∈ witRoots b p)

/-- The bound of `rPartI` (length `L`, error `1` per class). -/
noncomputable def resR (L : ℝ) (q z pc dA : ℕ) (excl : Finset ℕ) : ℝ :=
  L / q * (1 - altE (smallP z (· ∉ excl)) (fun p => ((1 : ℕ) : ℝ) / (p * p)) dA) +
    1 * truncErr (smallP z (· ∉ excl)) (fun _ => ((1 : ℕ) : ℝ)) dA +
    ∑ p ∈ midP z pc (· ∉ excl), (((1 : ℕ) : ℝ) * (L / q / (p * p)) + 1 * ((1 : ℕ) : ℝ))

theorem card_rPartI_le (N m b q t z pc dA : ℕ) (excl : Finset ℕ) (hm : 1 ≤ m) (hmN : m ≤ N + 1)
    (hq : 0 < q) (ht : t < q) (hdA : Odd dA) (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p) :
    ((rPartI N m b q t pc excl).card : ℝ) ≤ resR ((N + 1 - m : ℕ) : ℝ) q z pc dA excl := by
  have hD := goodDom_Icc m N hm hmN
  have h := domSieve_le hD (by positivity) zero_le_one q t z pc 1 dA hdA (witRoots b) (· ∉ excl) hq ht
    (by norm_num) (witRoots_sub b) (fun p hp _ => card_witRoots_le hp) hcop
    (fun _ _ => trivial) trivial (fun _ _ => trivial)
  unfold resR rPartI
  exact h

/-- A class part of `A₇ ∪ A₁₈` above `m`, sieved by `b`. -/
lemma bad_part_cover (N b q t m pc Y : ℕ) (excl : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P a → a % q = t ∧ m ≤ a) (hexcl : ∀ a, P a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1)) ⊆
      (rPartI N m b q t pc excl ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro a ha
  simp only [mem_filter, mem_Icc] at ha
  obtain ⟨⟨ha1, haN⟩, hPa, hsq⟩ := ha
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hpe : p ∉ excl := fun h => hexcl a hPa p h hd
  have hR : a % (p * p) ∈ witRoots b p := (mod_mem_witRoots hp.pos a).mpr hd
  have hqt := hP a hPa
  by_cases hpc : p ≤ pc
  · apply mem_union_left; apply mem_union_left
    simp only [rPartI, mem_filter, mem_Icc]
    exact ⟨⟨hqt.2, haN⟩, hqt.1, p, hpc, hp, hpe, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [midSet, mem_filter, mem_Icc]
    exact ⟨⟨ha1, haN⟩, p, hpY, hp, by omega, hR⟩
  · apply mem_union_right
    simp only [exSet, mem_filter, mem_Icc]
    have h1 : p ≤ a * b + 1 := le_trans (Nat.le_mul_self p) (Nat.le_of_dvd (Nat.succ_pos _) hd)
    have h2 : a * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b haN) 1
    exact ⟨⟨ha1, haN⟩, p, ⟨by omega, h1.trans h2⟩, hd⟩

/-! ### Lemma M -/

/-- `Mid(b) ≤ ∑_{p_c < p ≤ Y} (⌊N/p²⌋ + 1)`; the summand is `1` once `p² > N` (Lemma M). -/
theorem card_midSet_le_floor (N b pc Y : ℕ) :
    (midSet N b pc Y).card ≤ ∑ p ∈ midP pc Y (fun p => pc < p), (N / (p * p) + 1) := by
  classical
  have hsub : midSet N b pc Y ⊆ (midP pc Y (fun p => pc < p)).biUnion
      (fun p => (Icc 1 N).filter (fun a => a % (p * p) ∈ witRoots b p)) := by
    intro a ha
    simp only [midSet, mem_filter, mem_Icc] at ha
    obtain ⟨hai, p, hpY, hp, hpc, hR⟩ := ha
    simp only [mem_biUnion, midP, mem_filter, mem_Ioc, mem_Icc]
    exact ⟨p, ⟨⟨hpc, hpY⟩, hp, hpc⟩, hai, hR⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum ?_))
  intro p hp
  have hp' := (mem_filter.mp hp).2.1
  by_cases hpb : p ∣ b
  · have : witRoots b p = ∅ := by
      rw [witRoots, filter_eq_empty_iff]; intro r _; exact not_sq_dvd_of_dvd hp' hpb
    simp [this]
  · obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp' hpb
    calc ((Icc 1 N).filter (fun a => a % (p * p) ∈ witRoots b p)).card
        ≤ ((Icc 1 N).filter (fun a => a % (p * p) = c)).card := by
          apply card_le_card; intro a ha
          simp only [mem_filter] at ha ⊢
          exact ⟨ha.1, (hc a).mp ((mod_mem_witRoots hp'.pos a).mp ha.2)⟩
      _ ≤ N / (p * p) + 1 := card_mod_eq_le N (p * p) c

/-! ### The star part by Lemma B -/

/-- Star elements of `[m, N]` in the class `r` mod 4 with a U1 prime `p ≤ p_T`. -/
def lemBcoreI (N m r pT : ℕ) : Finset ℕ :=
  (Icc m N).filter (fun x => x % 100 ∈ T100 r ∧ ∃ p ≤ pT, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

/-- The bound of one class of `lemBcoreI`. -/
noncomputable def lemBR (L : ℝ) (zB pT dB : ℕ) : ℝ :=
  L / 100 * (1 - altE (smallP zB IsU1) (fun p => ((2 : ℕ) : ℝ) / (p * p)) dB) +
    1 * truncErr (smallP zB IsU1) (fun _ => ((2 : ℕ) : ℝ)) dB +
    ∑ p ∈ midP zB pT IsU1, (((2 : ℕ) : ℝ) * (L / 100 / (p * p)) + 1 * ((2 : ℕ) : ℝ))

theorem card_lemBcoreI_le (N m r zB pT dB : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N + 1) (hr : r = 1 ∨ r = 3)
    (hdB : Odd dB) :
    ((lemBcoreI N m r pT).card : ℝ) ≤ 23 * lemBR ((N + 1 - m : ℕ) : ℝ) zB pT dB := by
  classical
  have hD := goodDom_Icc m N hm hmN
  have hsub : lemBcoreI N m r pT ⊆ (T100 r).biUnion (fun t => (Icc m N).filter (fun x =>
      x % 100 = t ∧ ∃ p ≤ pT, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)) := by
    intro x hx
    simp only [lemBcoreI, mem_filter] at hx
    simp only [mem_biUnion, mem_filter]
    exact ⟨x % 100, hx.2.1, hx.1, rfl, hx.2.2⟩
  have hT : ∀ t ∈ T100 r, (((Icc m N).filter (fun x => x % 100 = t ∧
      ∃ p ≤ pT, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)).card : ℝ) ≤
      lemBR ((N + 1 - m : ℕ) : ℝ) zB pT dB := by
    intro t ht
    have ht100 : t < 100 := mem_range.mp (mem_filter.mp ht).1
    have h := domSieve_le hD (by positivity) zero_le_one 100 t zB pT 2 dB hdB (fun p => sqRoots p) IsU1
      (by norm_num) ht100 (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU)) (fun p _ hU => coprime_U1 hU)
      (fun _ _ => trivial) trivial (fun _ _ => trivial)
    unfold lemBR; exact h
  have h1 : ((lemBcoreI N m r pT).card : ℝ) ≤ ∑ t ∈ T100 r, (((Icc m N).filter (fun x =>
      x % 100 = t ∧ ∃ p ≤ pT, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have h2 := sum_le_sum hT
  rw [sum_const, T100_card hr, nsmul_eq_mul] at h2
  push_cast at h2
  linarith

/-- The star set of `starCount`. -/
def starSet (N b e : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => b ≤ x ∧ x % 4 = e ∧ IsStar x ∧ ¬ Squarefree (x * x + 1) ∧
    ¬ Squarefree (x * b + 1))

lemma starCount_eq (N b e : ℕ) : starCount N b e = (starSet N b e).card := rfl

lemma star_cover_B (N b r pT : ℕ) (hb : 1 ≤ b) :
    starSet N b r ⊆ lemBcoreI N b r pT ∪ u1Tail N pT := by
  intro x hx
  simp only [starSet, mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hbx, hr, hxs, hsq1, -⟩ := hx
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq1
  have hU := isU1_of_sq_dvd hp hd hxs
  have hR : x % (p * p) ∈ sqRoots p := (mod_mem_sqRoots hp.pos x).mpr hd
  by_cases hpT : p ≤ pT
  · apply mem_union_left
    have h1 : x % 100 % 25 = x % 25 := Nat.mod_mod_of_dvd x (by norm_num)
    have h2 : x % 100 % 4 = x % 4 := Nat.mod_mod_of_dvd x (by norm_num)
    have hT : x % 100 ∈ T100 r := by
      unfold IsStar at hxs
      simp only [T100, mem_filter, mem_range]
      exact ⟨Nat.mod_lt _ (by norm_num), by omega, by omega, by omega⟩
    simp only [lemBcoreI, mem_filter, mem_Icc]
    exact ⟨⟨hbx, hxN⟩, hT, p, hpT, hp, hU, hR⟩
  · apply mem_union_right
    simp only [u1Tail, mem_filter, mem_Icc]
    exact ⟨⟨hx1, hxN⟩, p, le_trans (Nat.le_mul_self p) (Nat.le_of_dvd (Nat.succ_pos _) hd), hU,
      by omega, hd⟩

/-! ### The star part by Lemma C′ -/

/-- The domain of Lemma C′: `[b, N] ∩ (r + 4ℤ)`. -/
def domC (N b r : ℕ) : Finset ℕ := (Icc b N).filter (fun x => x % 4 = r)

lemma star_sub_lemCSetD (N b r : ℕ) : starSet N b r ⊆ lemCSetD (domC N b r) b := by
  intro x hx
  simp only [starSet, mem_filter, mem_Icc] at hx
  simp only [lemCSetD, domC, mem_filter, mem_Icc]
  exact ⟨⟨⟨hx.2.1, hx.1.2⟩, hx.2.2.1⟩, hx.2.2.2⟩

lemma domC_sub (N b r : ℕ) (hb : 1 ≤ b) : domC N b r ⊆ Icc 1 N := by
  intro x hx; simp only [domC, mem_filter, mem_Icc] at hx ⊢; omega

lemma domC_not4 {N b r : ℕ} (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3) :
    ∀ x ∈ domC N b r, ¬ 2 * 2 ∣ x * b + 1 := by
  intro x hx
  have hx4 := (mem_filter.mp hx).2
  apply not4_same
  rcases hr with rfl | rfl
  · exact Or.inl ⟨hx4, hbr⟩
  · exact Or.inr ⟨hx4, hbr⟩

/-! ### Combining covers -/

lemma GoodDom.mono_ok {D : Finset ℕ} {L μ : ℝ} {P P' : ℕ → Prop} (hD : GoodDom D L μ P)
    (h : ∀ Q, P' Q → P Q) : GoodDom D L μ P' :=
  fun Q r hQ hok hr => hD Q r hQ (h Q hok) hr

/-- `Mid(b)` bound. -/
noncomputable def midB (N pc Y : ℕ) : ℝ := ((∑ p ∈ midP pc Y (fun p => pc < p), (N / (p * p) + 1) : ℕ) : ℝ)

lemma card_midSet_le_midB (N b pc Y : ℕ) : ((midSet N b pc Y).card : ℝ) ≤ midB N pc Y := by
  unfold midB; exact_mod_cast card_midSet_le_floor N b pc Y

/-- The U1 tail bound. -/
noncomputable def tailB (N pT Y : ℕ) : ℝ :=
  ∑ p ∈ midP pT Y (fun p => IsU1 p ∧ pT < p), hcnt N p +
    ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N Y m : ℝ)

/-- Lemma C core bound (`card_lemCcore_le`). -/
noncomputable def coreB (L μ : ℝ) (z₁ z₂ pB pc nS d : ℕ) (τ : ℝ) : ℝ :=
  23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * (L / 25 / (p * p)) + μ * 2) +
      ((L / 25 * mainU (smallP z₁ IsU1) d + μ * errU (smallP z₁ IsU1) d) +
        ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonD L μ p z₁ d +
        (nS * τ + ∑ p ∈ smallP z₂ IsU1, max (gainD L μ p z₁ d - τ) 0)) +
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), (L / (p * p) + μ)

/-- Parameters of Lemma C: the prefix condition for witnesses `b ≤ xb`. -/
def PrefixOK (xb nS : ℕ) : Prop :=
  xb * xb + 1 < (∏ j ∈ range (nS + 1), u1 j) * (∏ j ∈ range (nS + 1), u1 j)

/-- Three disjoint parts sieved by one witness share `Mid` and `Ex`. -/
lemma card_cover3 {X1 X2 X3 C1 C2 C3 T M E : Finset ℕ} (h1 : X1 ⊆ (C1 ∪ M) ∪ E)
    (h2 : X2 ⊆ (C2 ∪ M) ∪ E) (h3 : X3 ⊆ ((C3 ∪ T) ∪ M) ∪ E) (d12 : Disjoint X1 X2)
    (d3 : Disjoint (X1 ∪ X2) X3) :
    X1.card + X2.card + X3.card ≤ C1.card + C2.card + C3.card + T.card + M.card + E.card := by
  have hall : (X1 ∪ X2) ∪ X3 ⊆ ((((C1 ∪ C2) ∪ C3) ∪ T) ∪ M) ∪ E := by
    intro a ha
    simp only [mem_union] at ha ⊢
    rcases ha with (h | h) | h
    · have := h1 h; simp only [mem_union] at this; tauto
    · have := h2 h; simp only [mem_union] at this; tauto
    · have := h3 h; simp only [mem_union] at this; tauto
  rw [← card_union_of_disjoint d12, ← card_union_of_disjoint d3]
  refine (card_le_card hall).trans ?_
  have a1 := Finset.card_union_le ((((C1 ∪ C2) ∪ C3) ∪ T) ∪ M) E
  have a2 := Finset.card_union_le (((C1 ∪ C2) ∪ C3) ∪ T) M
  have a3 := Finset.card_union_le ((C1 ∪ C2) ∪ C3) T
  have a4 := Finset.card_union_le (C1 ∪ C2) C3
  have a5 := Finset.card_union_le C1 C2
  omega

/-! ### Case II -/

/-- **Case II.** `b` the least even element of `A*`, `b ≤ xb`; Lemma C on the split domain or on
`[1, N]`; U1 tail from `p_B`. -/
theorem caseII2 (N b xb z pc dA Y z₁ z₂ pB nS dC Y' : ℕ) (τ τ' E : ℝ)
    (hw : Witness N b) (hbs : IsStar b) (hbe : b % 2 = 0) (hbx : b ≤ xb)
    (hdA : Odd dA) (hdC : Odd dC) (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') (hY' : 1 ≤ Y')
    (hpre : PrefixOK xb nS) (hEx : ((exSet N b Y).card : ℝ) ≤ E) :
    ((badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount2 N b : ℕ) : ℝ) ≤
      2 * resR (N : ℝ) 25 z pc dA {2, 5} +
      min (coreB (((2 * N + 1 - b : ℕ) : ℝ) / 2) 2 z₁ z₂ pB pc nS dC τ)
          (coreB (N : ℝ) 1 z₁ z₂ pB pc nS dC τ') +
      tailB N pB Y' + midB N pc Y + E := by
  classical
  have hb1 := hw.1
  have hbN := hw.2.1
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 25 p := fun p hp hne => by
    simp at hne; exact coprime25 hp hne.2
  have hexcl : ∀ a, (a % 25 = 7 ∨ a % 25 = 18) → ∀ p ∈ ({2, 5} : Finset ℕ), ¬ p * p ∣ a * b + 1 := by
    intro a ha p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact not4_even (Or.inr hbe)
    · exact not25_star ha hbs
  have c7 := bad_part_cover N b 25 7 1 pc Y {2, 5} (fun a => a % 25 = 7)
    (fun a ha => ⟨ha, by omega⟩) (fun a ha => hexcl a (Or.inl ha))
  have c18 := bad_part_cover N b 25 18 1 pc Y {2, 5} (fun a => a % 25 = 18)
    (fun a ha => ⟨ha, by omega⟩) (fun a ha => hexcl a (Or.inr ha))
  have hDs : (Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a) ⊆ Icc 1 N := filter_subset _ _
  have cC := lemCD_cover hDs b z₁ z₂ pB pc Y (fun x _ => not4_even (Or.inr hbe))
  have hLC : lemCCount2 N b = (lemCSetD ((Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a)) b).card := by
    unfold lemCCount2 lemCSetD; rw [filter_filter]
  have hbad : badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b ≤
      ((Icc 1 N).filter (fun a => a % 25 = 7 ∧ ¬ Squarefree (a * b + 1))).card +
      ((Icc 1 N).filter (fun a => a % 25 = 18 ∧ ¬ Squarefree (a * b + 1))).card := by
    unfold badCount
    refine (card_le_card ?_).trans (Finset.card_union_le _ _)
    intro a ha
    simp only [mem_union, mem_filter] at ha ⊢
    rcases ha.2.1 with h | h
    · exact Or.inl ⟨ha.1, h, ha.2.2⟩
    · exact Or.inr ⟨ha.1, h, ha.2.2⟩
  have d12 : Disjoint ((Icc 1 N).filter (fun a => a % 25 = 7 ∧ ¬ Squarefree (a * b + 1)))
      ((Icc 1 N).filter (fun a => a % 25 = 18 ∧ ¬ Squarefree (a * b + 1))) := by
    rw [disjoint_left]; intro a ha hb'
    simp only [mem_filter] at ha hb'; omega
  have d3 : Disjoint ((Icc 1 N).filter (fun a => a % 25 = 7 ∧ ¬ Squarefree (a * b + 1)) ∪
      (Icc 1 N).filter (fun a => a % 25 = 18 ∧ ¬ Squarefree (a * b + 1)))
      (lemCSetD ((Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a)) b) := by
    rw [disjoint_left]; intro a ha hc
    simp only [mem_union, mem_filter, lemCSetD] at ha hc
    unfold IsStar at hc; omega
  have hcardS := card_cover3 c7 c18 cC d12 d3
  have cCF := lemCD_cover (subset_refl (Icc 1 N)) b z₁ z₂ pB pc Y (fun x _ => not4_even (Or.inr hbe))
  have hsubF : lemCSetD ((Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a)) b ⊆ lemCSetD (Icc 1 N) b := by
    intro x hx; simp only [lemCSetD, mem_filter] at hx ⊢; exact ⟨hx.1.1, hx.2⟩
  have hcardF := card_cover3 c7 c18 (hsubF.trans cCF) d12 d3
  -- real bounds of the pieces
  have hR7 := card_rPartI_le N 1 b 25 7 z pc dA {2, 5} le_rfl (by omega) (by norm_num) (by norm_num) hdA hcop
  have hR18 := card_rPartI_le N 1 b 25 18 z pc dA {2, 5} le_rfl (by omega) (by norm_num) (by norm_num) hdA hcop
  rw [show N + 1 - 1 = N by omega] at hR7 hR18
  have hDsG := goodDom_split N b hb1 (by omega)
  have hDf : GoodDom (Icc 1 N) (N : ℝ) 1 Odd := by
    have := goodDom_Icc 1 N le_rfl (by omega)
    rw [show N + 1 - 1 = N by omega] at this
    exact this.mono_ok (fun _ _ => trivial)
  have hCs := card_lemCcore_le hDsG (by positivity) (by norm_num) b xb z₁ z₂ pB pc nS τ hdC hbs hbx hz₂ hτ hpre
  have hCf := card_lemCcore_le hDf (by positivity) zero_le_one b xb z₁ z₂ pB pc nS τ' hdC hbs hbx hz₂ hτ' hpre
  have hT := card_u1Tail_le N pB Y' hY'
  have hM := card_midSet_le_midB N b pc Y
  have e1 : ((badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount2 N b : ℕ) : ℝ) ≤
      (((Icc 1 N).filter (fun a => a % 25 = 7 ∧ ¬ Squarefree (a * b + 1))).card : ℝ) +
      ((Icc 1 N).filter (fun a => a % 25 = 18 ∧ ¬ Squarefree (a * b + 1))).card +
      (lemCSetD ((Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a)) b).card := by
    rw [hLC]; exact_mod_cast (by omega)
  have eS := (Nat.cast_le (α := ℝ)).mpr hcardS
  have eF := (Nat.cast_le (α := ℝ)).mpr hcardF
  push_cast at eS eF
  unfold tailB coreB
  unfold tailB at hT
  rcases min_choice (coreB (((2 * N + 1 - b : ℕ) : ℝ) / 2) 2 z₁ z₂ pB pc nS dC τ)
      (coreB (N : ℝ) 1 z₁ z₂ pB pc nS dC τ') with hm | hm
  · unfold coreB at hm; rw [hm]; push_cast at e1 hCs ⊢; linarith
  · unfold coreB at hm; rw [hm]; push_cast at e1 hCf ⊢; linarith

/-! ### More building blocks -/

/-- Several classes `Tset` mod `q` above `m`, sieved by `b`. -/
lemma bad_parts_cover (N b q m pc Y : ℕ) (Tset excl : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P a → a % q ∈ Tset ∧ m ≤ a) (hexcl : ∀ a, P a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1)) ⊆
      (Tset.biUnion (fun t => rPartI N m b q t pc excl) ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro a ha
  have hPa := (mem_filter.mp ha).2.1
  have hc := bad_part_cover N b q (a % q) m pc Y excl (fun x => P x ∧ x % q = a % q)
    (fun x hx => ⟨hx.2, (hP x hx.1).2⟩) (fun x hx => hexcl x hx.1)
    (mem_filter.mpr ⟨(mem_filter.mp ha).1, ⟨hPa, rfl⟩, (mem_filter.mp ha).2.2⟩)
  simp only [mem_union] at hc ⊢
  rcases hc with (h | h) | h
  · exact Or.inl (Or.inl (mem_biUnion.mpr ⟨a % q, (hP a hPa).1, h⟩))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

lemma card_rParts_le (N m b q z pc dA : ℕ) (Tset excl : Finset ℕ) (hm : 1 ≤ m) (hmN : m ≤ N + 1)
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hdA : Odd dA)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p) :
    ((Tset.biUnion (fun t => rPartI N m b q t pc excl)).card : ℝ) ≤
      Tset.card * resR ((N + 1 - m : ℕ) : ℝ) q z pc dA excl := by
  have h1 : ((Tset.biUnion (fun t => rPartI N m b q t pc excl)).card : ℝ) ≤
      ∑ t ∈ Tset, ((rPartI N m b q t pc excl).card : ℝ) := by exact_mod_cast card_biUnion_le
  have h2 := sum_le_sum (fun t ht => card_rPartI_le N m b q t z pc dA excl hm hmN hq (hTq t ht) hdA hcop)
  rw [sum_const, nsmul_eq_mul] at h2
  linarith

/-- One whole class mod 100. -/
lemma classCount_one (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (t : ℕ) (hP : ∀ a, P a → a % 100 = t) :
    (classCount N P : ℝ) ≤ (N : ℝ) / 100 + 1 := by
  have h1 : classCount N P ≤ ((Icc 1 N).filter (fun a => a % 100 = t)).card := by
    unfold classCount; apply card_le_card; intro a ha
    simp only [mem_filter] at ha ⊢; exact ⟨ha.1, hP a ha.2⟩
  have h2 := card_mod_eq_le N 100 t
  have h3 : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
  have : (classCount N P : ℝ) ≤ ((N / 100 + 1 : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
  push_cast at this; linarith

/-- **The star part** `starSet N b r`, by Lemma B or by Lemma C′ (whichever bound is smaller). -/
theorem star_cover_min (N b r xb zB pT dB z₁ z₂ pc nS dC Y : ℕ) (τ : ℝ)
    (hw : Witness N b) (hbs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3) (hbx : b ≤ xb)
    (hdB : Odd dB) (hdC : Odd dC) (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ) (hpre : PrefixOK xb nS) :
    ∃ C : Finset ℕ, starSet N b r ⊆ ((C ∪ u1Tail N pT) ∪ midSet N b pc Y) ∪ exSet N b Y ∧
      (C.card : ℝ) ≤ min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) zB pT dB)
        (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS dC τ) := by
  have hb1 := hw.1
  have hbN := hw.2.1
  rcases le_total (23 * lemBR ((N + 1 - b : ℕ) : ℝ) zB pT dB)
      (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS dC τ) with hle | hle
  · refine ⟨lemBcoreI N b r pT, ?_, ?_⟩
    · intro x hx
      have := star_cover_B N b r pT hb1 hx
      simp only [mem_union] at this ⊢; tauto
    · rw [min_eq_left hle]; exact card_lemBcoreI_le N b r zB pT dB hb1 (by omega) hr hdB
  · refine ⟨lemCcore (domC N b r) b z₁ z₂ pT pc, ?_, ?_⟩
    · exact (star_sub_lemCSetD N b r).trans
        (lemCD_cover (domC_sub N b r hb1) b z₁ z₂ pT pc Y (domC_not4 hbr hr))
    · rw [min_eq_right hle]
      have hD := goodDom_mod4 N b r hb1 (by omega) (by omega)
      exact card_lemCcore_le hD (by positivity) zero_le_one b xb z₁ z₂ pT pc nS τ hdC hbs hbx hz₂ hτ hpre

/-! ### Set bookkeeping -/

lemma card_union4 (R C M E : Finset ℕ) : (((R ∪ C) ∪ M) ∪ E).card ≤ R.card + C.card + M.card + E.card := by
  have a1 := Finset.card_union_le ((R ∪ C) ∪ M) E
  have a2 := Finset.card_union_le (R ∪ C) M
  have a3 := Finset.card_union_le R C
  omega

/-- The part sieved by `b` and the star part, with the U1 tail kept apart. -/
lemma cover_bs {X S R C T M E : Finset ℕ} (hX : X ⊆ (R ∪ M) ∪ E) (hS : S ⊆ ((C ∪ T) ∪ M) ∪ E) :
    X ∪ S ⊆ (((R ∪ C) ∪ M) ∪ E) ∪ T := by
  intro a ha
  simp only [mem_union] at ha ⊢
  rcases ha with h | h
  · have := hX h; simp only [mem_union] at this; tauto
  · have := hS h; simp only [mem_union] at this; tauto

/-- Two halves sharing the U1 tail. -/
lemma card_halves {H1 H3 U1 U3 T : Finset ℕ} (h1 : H1 ⊆ U1 ∪ T) (h3 : H3 ⊆ U3 ∪ T)
    (hd : Disjoint H1 H3) : H1.card + H3.card ≤ U1.card + U3.card + T.card := by
  rw [← card_union_of_disjoint hd]
  have : H1 ∪ H3 ⊆ (U1 ∪ U3) ∪ T := by
    intro a ha; simp only [mem_union] at ha ⊢
    rcases ha with h | h
    · have := h1 h; simp only [mem_union] at this; tauto
    · have := h3 h; simp only [mem_union] at this; tauto
  refine (card_le_card this).trans ?_
  have a1 := Finset.card_union_le (U1 ∪ U3) T
  have a2 := Finset.card_union_le U1 U3
  omega

lemma badCount_eq (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    badCount N P b = ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card := rfl

/-- A badCount set and a star set are disjoint when the badCount predicate forces `A₇ ∪ A₁₈`. -/
lemma disj_bad_star (N b w e : ℕ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ a, P a → a % 25 = 7 ∨ a % 25 = 18) :
    Disjoint ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * w + 1))) (starSet N b e) := by
  rw [disjoint_left]; intro a ha hs
  have h1 := hP a (mem_filter.mp ha).2.1
  have h2 := (mem_filter.mp hs).2.2.2.1
  unfold IsStar at h2; omega

lemma mod100_25 (a : ℕ) : a % 100 % 25 = a % 25 := Nat.mod_mod_of_dvd a (by norm_num)
lemma mod100_4 (a : ℕ) : a % 100 % 4 = a % 4 := Nat.mod_mod_of_dvd a (by norm_num)
lemma mod100_2 (a : ℕ) : a % 100 % 2 = a % 2 := Nat.mod_mod_of_dvd a (by norm_num)

/-! ### Case I.b -/

theorem caseIb2 (N b b' z pc dA Y Y' : ℕ) (E E' : ℝ) (hw : Witness N b) (h7 : b % 25 = 7)
    (hw' : Witness N b') (h18 : b' % 25 = 18) (hdA : Odd dA)
    (hEx : ((exSet N b Y).card : ℝ) ≤ E) (hEx' : ((exSet N b' Y').card : ℝ) ≤ E') :
    ((badCount N (fun a => a % 25 = 18 ∧ b' ≤ a) b + badCount N (fun a => a % 25 = 7 ∧ b ≤ a) b' : ℕ) : ℝ) ≤
      (resR ((N + 1 - b' : ℕ) : ℝ) 25 z pc dA {5} + midB N pc Y + E) +
      (resR ((N + 1 - b : ℕ) : ℝ) 25 z pc dA {5} + midB N pc Y' + E') := by
  have hcop : ∀ p, p.Prime → p ∉ ({5} : Finset ℕ) → Nat.Coprime 25 p := fun p hp hne =>
    coprime25 hp (by simpa using hne)
  have c1 := bad_part_cover N b 25 18 b' pc Y {5} (fun a => a % 25 = 18 ∧ b' ≤ a) (fun a ha => ha)
    (fun a ha p hp => by rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inr ⟨ha.1, h7⟩))
  have c2 := bad_part_cover N b' 25 7 b pc Y' {5} (fun a => a % 25 = 7 ∧ b ≤ a) (fun a ha => ha)
    (fun a ha p hp => by rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inl ⟨ha.1, h18⟩))
  have k1 := (card_le_card c1).trans (by
    have := Finset.card_union_le (rPartI N b' b 25 18 pc {5} ∪ midSet N b pc Y) (exSet N b Y)
    have := Finset.card_union_le (rPartI N b' b 25 18 pc {5}) (midSet N b pc Y); omega :
    _ ≤ (rPartI N b' b 25 18 pc {5}).card + (midSet N b pc Y).card + (exSet N b Y).card)
  have k2 := (card_le_card c2).trans (by
    have := Finset.card_union_le (rPartI N b b' 25 7 pc {5} ∪ midSet N b' pc Y') (exSet N b' Y')
    have := Finset.card_union_le (rPartI N b b' 25 7 pc {5}) (midSet N b' pc Y'); omega :
    _ ≤ (rPartI N b b' 25 7 pc {5}).card + (midSet N b' pc Y').card + (exSet N b' Y').card)
  have r1 := card_rPartI_le N b' b 25 18 z pc dA {5} hw'.1 (by have := hw'.2.1; omega) (by norm_num)
    (by norm_num) hdA hcop
  have r2 := card_rPartI_le N b b' 25 7 z pc dA {5} hw.1 (by have := hw.2.1; omega) (by norm_num)
    (by norm_num) hdA hcop
  have m1 := card_midSet_le_midB N b pc Y
  have m2 := card_midSet_le_midB N b' pc Y'
  rw [← badCount_eq] at k1 k2
  have k1' := (Nat.cast_le (α := ℝ)).mpr k1
  have k2' := (Nat.cast_le (α := ℝ)).mpr k2
  push_cast at k1' k2' ⊢
  linarith

/-! ### The class sets mod 100 -/

/-- Classes of `A₇ ∪ A₁₈` mod 100 satisfying `Q`. -/
def cls100 (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ Q t)

lemma mem_cls100 {Q : ℕ → Prop} [DecidablePred Q] {a : ℕ} (h78 : a % 25 = 7 ∨ a % 25 = 18)
    (hQ : Q (a % 100)) : a % 100 ∈ cls100 Q := by
  simp only [cls100, mem_filter, mem_range, mod100_25]
  exact ⟨Nat.mod_lt _ (by norm_num), h78, hQ⟩

lemma cls100_lt {Q : ℕ → Prop} [DecidablePred Q] : ∀ t ∈ cls100 Q, t < 100 :=
  fun t ht => mem_range.mp (mem_filter.mp ht).1

/-- Exclusion of `2` and `5` for classes `≡ r (mod 4)` or even, sieved by an odd star `b ≡ r`. -/
lemma excl25_star {a b r : ℕ} (hbs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (h78 : a % 25 = 7 ∨ a % 25 = 18) (h4 : a % 4 = r ∨ a % 2 = 0) :
    ∀ p ∈ ({2, 5} : Finset ℕ), ¬ p * p ∣ a * b + 1 := by
  intro p hp
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl
  · rcases h4 with h | h
    · rcases hr with rfl | rfl
      · exact not4_same (Or.inl ⟨h, hbr⟩)
      · exact not4_same (Or.inr ⟨h, hbr⟩)
    · exact not4_even (Or.inl h)
  · exact not25_star h78 hbs

lemma coprime100' : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
  simp at hne; exact coprime100 hp hne.1 hne.2

/-! ### Case III.1 -/

/-- The half of case III.1 (or the `b`-part of III.2) belonging to one odd witness `b ≡ r`. -/
lemma half_cover (N b r xb pc Y zB pT dB z₁ z₂ nS dC : ℕ) (τ : ℝ) (Tset : Finset ℕ)
    (P : ℕ → Prop) [DecidablePred P]
    (hw : Witness N b) (hbs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3) (hbx : b ≤ xb)
    (hdB : Odd dB) (hdC : Odd dC) (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ) (hpre : PrefixOK xb nS)
    (hP : ∀ a, P a → a % 100 ∈ Tset ∧ 1 ≤ a) (hexcl : ∀ a, P a → ∀ p ∈ ({2, 5} : Finset ℕ), ¬ p * p ∣ a * b + 1)
    (h78 : ∀ a, P a → a % 25 = 7 ∨ a % 25 = 18) :
    ∃ C : Finset ℕ,
      (Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1)) ∪ starSet N b r ⊆
        (((Tset.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5}) ∪ C) ∪ midSet N b pc Y) ∪ exSet N b Y) ∪
          u1Tail N pT ∧
      (C.card : ℝ) ≤ min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) zB pT dB)
        (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS dC τ) := by
  obtain ⟨C, hC, hCc⟩ := star_cover_min N b r xb zB pT dB z₁ z₂ pc nS dC Y τ hw hbs hbr hr hbx hdB hdC hz₂ hτ hpre
  exact ⟨C, cover_bs (bad_parts_cover N b 100 1 pc Y Tset {2, 5} P hP hexcl) hC, hCc⟩

theorem caseIII1_2 (N b₁ b₃ xb₁ xb₃ z pc dA Y₁ Y₃ zB pT dB z₁ z₂ nS₁ nS₃ dC Y' : ℕ)
    (τ₁ τ₃ E₁ E₃ : ℝ)
    (hw₁ : Witness N b₁) (hs₁ : IsStar b₁) (hr₁ : b₁ % 4 = 1)
    (hw₃ : Witness N b₃) (hs₃ : IsStar b₃) (hr₃ : b₃ % 4 = 3)
    (hbx₁ : b₁ ≤ xb₁) (hbx₃ : b₃ ≤ xb₃) (hdA : Odd dA) (hdB : Odd dB) (hdC : Odd dC)
    (hz₂ : 5 ≤ z₂) (hτ₁ : 0 ≤ τ₁) (hτ₃ : 0 ≤ τ₃) (hY' : 1 ≤ Y')
    (hpre₁ : PrefixOK xb₁ nS₁) (hpre₃ : PrefixOK xb₃ nS₃)
    (hEx₁ : ((exSet N b₁ Y₁).card : ℝ) ≤ E₁) (hEx₃ : ((exSet N b₃ Y₃).card : ℝ) ≤ E₃) :
    ((badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
      starCount N b₁ 1 + starCount N b₃ 3 : ℕ) : ℝ) ≤
      (6 * resR (N : ℝ) 100 z pc dA {2, 5} + midB N pc Y₁ + E₁ +
        min (23 * lemBR ((N + 1 - b₁ : ℕ) : ℝ) zB pT dB)
          (coreB (((N + 1 - b₁ : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS₁ dC τ₁)) +
      (2 * resR (N : ℝ) 100 z pc dA {2, 5} + midB N pc Y₃ + E₃ +
        min (23 * lemBR ((N + 1 - b₃ : ℕ) : ℝ) zB pT dB)
          (coreB (((N + 1 - b₃ : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS₃ dC τ₃)) +
      tailB N pT Y' := by
  classical
  set T1 := cls100 (fun t => t % 4 = 1 ∨ t % 2 = 0)
  set T3 := cls100 (fun t => t % 4 = 3)
  have hT1 : T1.card = 6 := by decide
  have hT3 : T3.card = 2 := by decide
  obtain ⟨C1, h1, hC1⟩ := half_cover N b₁ 1 xb₁ pc Y₁ zB pT dB z₁ z₂ nS₁ dC τ₁ T1
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) hw₁ hs₁ hr₁ (Or.inl rfl) hbx₁
    hdB hdC hz₂ hτ₁ hpre₁
    (fun a ha => ⟨mem_cls100 ha.1 (by rw [mod100_4, mod100_2]; exact ha.2), by omega⟩)
    (fun a ha => excl25_star hs₁ hr₁ (Or.inl rfl) ha.1 ha.2) (fun a ha => ha.1)
  obtain ⟨C3, h3, hC3⟩ := half_cover N b₃ 3 xb₃ pc Y₃ zB pT dB z₁ z₂ nS₃ dC τ₃ T3
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) hw₃ hs₃ hr₃ (Or.inr rfl) hbx₃
    hdB hdC hz₂ hτ₃ hpre₃
    (fun a ha => ⟨mem_cls100 ha.1 (by rw [mod100_4]; exact ha.2), by omega⟩)
    (fun a ha => excl25_star hs₃ hr₃ (Or.inr rfl) ha.1 (Or.inl ha.2)) (fun a ha => ha.1)
  -- disjointness
  set X1 := (Icc 1 N).filter (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) ∧
    ¬ Squarefree (a * b₁ + 1))
  set X3 := (Icc 1 N).filter (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) ∧
    ¬ Squarefree (a * b₃ + 1))
  have dX1S1 := disj_bad_star N b₁ b₁ 1 (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0))
    (fun a ha => ha.1)
  have dX3S3 := disj_bad_star N b₃ b₃ 3 (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3)
    (fun a ha => ha.1)
  have dH : Disjoint (X1 ∪ starSet N b₁ 1) (X3 ∪ starSet N b₃ 3) := by
    rw [disjoint_left]; intro a ha hb
    simp only [X1, X3, starSet, mem_union, mem_filter] at ha hb
    unfold IsStar at ha hb
    omega
  have hcard := card_halves h1 h3 dH
  rw [card_union_of_disjoint dX1S1, card_union_of_disjoint dX3S3] at hcard
  have u1 := card_union4 (T1.biUnion (fun t => rPartI N 1 b₁ 100 t pc {2, 5}) ∪ C1) (midSet N b₁ pc Y₁)
    (exSet N b₁ Y₁) ∅
  have u1' := Finset.card_union_le (T1.biUnion (fun t => rPartI N 1 b₁ 100 t pc {2, 5})) C1
  have u3 := card_union4 (T3.biUnion (fun t => rPartI N 1 b₃ 100 t pc {2, 5}) ∪ C3) (midSet N b₃ pc Y₃)
    (exSet N b₃ Y₃) ∅
  have u3' := Finset.card_union_le (T3.biUnion (fun t => rPartI N 1 b₃ 100 t pc {2, 5})) C3
  simp only [union_empty, card_empty, add_zero] at u1 u3
  have r1 := card_rParts_le N 1 b₁ 100 z pc dA T1 {2, 5} le_rfl (by omega) (by norm_num) cls100_lt hdA coprime100'
  have r3 := card_rParts_le N 1 b₃ 100 z pc dA T3 {2, 5} le_rfl (by omega) (by norm_num) cls100_lt hdA coprime100'
  rw [hT1, show N + 1 - 1 = N by omega] at r1
  rw [hT3, show N + 1 - 1 = N by omega] at r3
  have m1 := card_midSet_le_midB N b₁ pc Y₁
  have m3 := card_midSet_le_midB N b₃ pc Y₃
  have ht := card_u1Tail_le N pT Y' hY'
  have hc := (Nat.cast_le (α := ℝ)).mpr hcard
  have hu1 := (Nat.cast_le (α := ℝ)).mpr (u1.trans (Nat.add_le_add_right (Nat.add_le_add_right u1' _) _))
  have hu3 := (Nat.cast_le (α := ℝ)).mpr (u3.trans (Nat.add_le_add_right (Nat.add_le_add_right u3' _) _))
  rw [← badCount_eq, ← badCount_eq, ← starCount_eq, ← starCount_eq] at hc
  push_cast at hc hu1 hu3 r1 r3 ⊢
  unfold tailB
  linarith

/-! ### Case III.2 -/

lemma card_cls100 (r s s' : ℕ) (hr : r = 1 ∨ r = 3) (hss : (s = 7 ∧ s' = 18) ∨ (s = 18 ∧ s' = 7)) :
    (cls100 (fun t => (t % 25 = s ∧ ¬ t % 4 = 4 - r) ∨ (t % 25 = s' ∧ t % 4 = r))).card = 4 := by
  rcases hr with rfl | rfl <;> rcases hss with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

lemma unsieved_class (s r : ℕ) (hr : r = 1 ∨ r = 3) (hs : s = 7 ∨ s = 18) :
    ∃ t, ∀ a, Unsieved s r a → a % 100 = t := by
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨7, fun a ha => by unfold Unsieved at ha; omega⟩
  · exact ⟨43, fun a ha => by unfold Unsieved at ha; omega⟩
  · exact ⟨57, fun a ha => by unfold Unsieved at ha; omega⟩
  · exact ⟨93, fun a ha => by unfold Unsieved at ha; omega⟩

/-- **Case III.2 β.** -/
theorem caseIII2beta2 (N b r s s' xb z pc dA Y zB pT dB z₁ z₂ nS dC Y' : ℕ) (τ E : ℝ)
    (hw : Witness N b) (hbs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hss : (s = 7 ∧ s' = 18) ∨ (s = 18 ∧ s' = 7)) (hbx : b ≤ xb)
    (hdA : Odd dA) (hdB : Odd dB) (hdC : Odd dC) (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ) (hY' : 1 ≤ Y')
    (hpre : PrefixOK xb nS) (hEx : ((exSet N b Y).card : ℝ) ≤ E) :
    ((classCount N (Unsieved s r) +
      badCount N (fun a => (a % 25 = s ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = s' ∧ a % 4 = r)) b +
      starCount N b r : ℕ) : ℝ) ≤
      ((N : ℝ) / 100 + 1) +
      (4 * resR (N : ℝ) 100 z pc dA {2, 5} + midB N pc Y + E +
        min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) zB pT dB)
          (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS dC τ)) +
      tailB N pT Y' := by
  classical
  have hs78 : ∀ a, ((a % 25 = s ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = s' ∧ a % 4 = r)) → a % 25 = 7 ∨ a % 25 = 18 := by
    intro a ha; rcases hss with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  set Tset := cls100 (fun t => (t % 25 = s ∧ ¬ t % 4 = 4 - r) ∨ (t % 25 = s' ∧ t % 4 = r))
  obtain ⟨C, hcov, hC⟩ := half_cover N b r xb pc Y zB pT dB z₁ z₂ nS dC τ Tset
    (fun a => (a % 25 = s ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = s' ∧ a % 4 = r)) hw hbs hbr hr hbx
    hdB hdC hz₂ hτ hpre
    (fun a ha => ⟨mem_cls100 (hs78 a ha) (by rw [mod100_25, mod100_4]; exact ha), by omega⟩)
    (fun a ha => excl25_star hbs hbr hr (hs78 a ha) (by rcases hr with rfl | rfl <;> omega))
    hs78
  have dXS := disj_bad_star N b b r _ hs78
  have hcard : ((Icc 1 N).filter (fun a => ((a % 25 = s ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = s' ∧ a % 4 = r)) ∧
      ¬ Squarefree (a * b + 1))).card + (starSet N b r).card ≤
      (Tset.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})).card + C.card + (midSet N b pc Y).card +
        (exSet N b Y).card + (u1Tail N pT).card := by
    rw [← card_union_of_disjoint dXS]
    refine (card_le_card hcov).trans ?_
    have a1 := Finset.card_union_le ((((Tset.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) ∪ C) ∪
      midSet N b pc Y) ∪ exSet N b Y) (u1Tail N pT)
    have a2 := card_union4 (Tset.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) C (midSet N b pc Y) (exSet N b Y)
    omega
  have r1 := card_rParts_le N 1 b 100 z pc dA Tset {2, 5} le_rfl (by omega) (by norm_num) cls100_lt hdA coprime100'
  rw [card_cls100 r s s' hr hss, show N + 1 - 1 = N by omega] at r1
  obtain ⟨t0, ht0⟩ := unsieved_class s r hr (by rcases hss with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
  have hcl := classCount_one N (Unsieved s r) t0 ht0
  have m1 := card_midSet_le_midB N b pc Y
  have ht := card_u1Tail_le N pT Y' hY'
  have hc := (Nat.cast_le (α := ℝ)).mpr hcard
  rw [← badCount_eq, ← starCount_eq] at hc
  push_cast at hc r1 ⊢
  unfold tailB
  linarith

/-- Three families of classes above `m₁, m₂, m₃`, sieved by `b`. -/
lemma bad_parts_cover3 (N b q pc Y m₁ m₂ m₃ : ℕ) (T₁ T₂ T₃ excl : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P a → (a % q ∈ T₁ ∧ m₁ ≤ a) ∨ (a % q ∈ T₂ ∧ m₂ ≤ a) ∨ (a % q ∈ T₃ ∧ m₃ ≤ a))
    (hexcl : ∀ a, P a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1)) ⊆
      ((((T₁.biUnion (fun t => rPartI N m₁ b q t pc excl) ∪ T₂.biUnion (fun t => rPartI N m₂ b q t pc excl)) ∪
        T₃.biUnion (fun t => rPartI N m₃ b q t pc excl)) ∪ midSet N b pc Y) ∪ exSet N b Y) := by
  intro a ha
  have hPa := (mem_filter.mp ha).2.1
  rcases hP a hPa with h | h | h
  · have hc := bad_parts_cover N b q m₁ pc Y T₁ excl (fun x => P x ∧ x % q ∈ T₁ ∧ m₁ ≤ x)
      (fun x hx => hx.2) (fun x hx => hexcl x hx.1)
      (mem_filter.mpr ⟨(mem_filter.mp ha).1, ⟨hPa, h⟩, (mem_filter.mp ha).2.2⟩)
    simp only [mem_union] at hc ⊢; tauto
  · have hc := bad_parts_cover N b q m₂ pc Y T₂ excl (fun x => P x ∧ x % q ∈ T₂ ∧ m₂ ≤ x)
      (fun x hx => hx.2) (fun x hx => hexcl x hx.1)
      (mem_filter.mpr ⟨(mem_filter.mp ha).1, ⟨hPa, h⟩, (mem_filter.mp ha).2.2⟩)
    simp only [mem_union] at hc ⊢; tauto
  · have hc := bad_parts_cover N b q m₃ pc Y T₃ excl (fun x => P x ∧ x % q ∈ T₃ ∧ m₃ ≤ x)
      (fun x hx => hx.2) (fun x hx => hexcl x hx.1)
      (mem_filter.mpr ⟨(mem_filter.mp ha).1, ⟨hPa, h⟩, (mem_filter.mp ha).2.2⟩)
    simp only [mem_union] at hc ⊢; tauto

/-- A single witness part: `|X| ≤ |R| + |Mid| + |Ex|`. -/
lemma card_cover1 {X R M E : Finset ℕ} (h : X ⊆ (R ∪ M) ∪ E) : X.card ≤ R.card + M.card + E.card := by
  refine (card_le_card h).trans ?_
  have := Finset.card_union_le (R ∪ M) E
  have := Finset.card_union_le R M
  omega

/-- Exclusion of `2, 5` for the unsieved class of `A_s`, sieved by `w ∈ A_{s'}` with `w ≢ r (mod 4)`. -/
lemma excl25_cross {a w r : ℕ} (hr : r = 1 ∨ r = 3) (hw4 : ¬ w % 4 = r) (ha4 : a % 4 = 4 - r)
    (h25 : (a % 25 = 7 ∧ w % 25 = 18) ∨ (a % 25 = 18 ∧ w % 25 = 7)) :
    ∀ p ∈ ({2, 5} : Finset ℕ), ¬ p * p ∣ a * w + 1 := by
  intro p hp
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl
  · by_cases he : w % 2 = 0
    · exact not4_even (Or.inr he)
    · rcases hr with rfl | rfl
      · exact not4_same (Or.inr ⟨by omega, by omega⟩)
      · exact not4_same (Or.inl ⟨by omega, by omega⟩)
  · exact not25_7_18 h25

/-- **Case III.2 α**: the bound with three witnesses (`a3`) and with two witnesses (`a2`). -/
theorem caseIII2alpha2 (N b r c c' xb z pc dA Y Yc Yc' zB pT dB z₁ z₂ nS dC Y' : ℕ)
    (τ E Ec Ec' : ℝ)
    (hw : Witness N b) (hbs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hwc : Witness N c) (hc7 : c % 25 = 7) (hcr : ¬ c % 4 = r)
    (hwc' : Witness N c') (hc18 : c' % 25 = 18) (hcr' : ¬ c' % 4 = r) (hbx : b ≤ xb)
    (hdA : Odd dA) (hdB : Odd dB) (hdC : Odd dC) (hz₂ : 5 ≤ z₂) (hτ : 0 ≤ τ) (hY' : 1 ≤ Y')
    (hpre : PrefixOK xb nS) (hEx : ((exSet N b Y).card : ℝ) ≤ E)
    (hExc : ((exSet N c Yc).card : ℝ) ≤ Ec) (hExc' : ((exSet N c' Yc').card : ℝ) ≤ Ec') :
    ((badCount N (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
        (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a)) b +
      badCount N (fun a => Unsieved 7 r a ∧ c ≤ a) c' +
      badCount N (fun a => Unsieved 18 r a ∧ c' ≤ a) c +
      starCount N b r : ℕ) : ℝ) ≤
      (2 * resR (N : ℝ) 100 z pc dA {2, 5} + 2 * resR ((N + 1 - c : ℕ) : ℝ) 100 z pc dA {2, 5} +
        2 * resR ((N + 1 - c' : ℕ) : ℝ) 100 z pc dA {2, 5} + midB N pc Y + E +
        min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) zB pT dB)
          (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS dC τ)) +
      tailB N pT Y' +
      (resR ((N + 1 - c : ℕ) : ℝ) 100 z pc dA {2, 5} + midB N pc Yc' + Ec') +
      (resR ((N + 1 - c' : ℕ) : ℝ) 100 z pc dA {2, 5} + midB N pc Yc + Ec) ∧
    ((classCount N (Unsieved 7 r) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a) b +
      badCount N (Unsieved 18 r) c +
      starCount N b r : ℕ) : ℝ) ≤
      ((N : ℝ) / 100 + 1) +
      (6 * resR (N : ℝ) 100 z pc dA {2, 5} + midB N pc Y + E +
        min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) zB pT dB)
          (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 z₁ z₂ pT pc nS dC τ)) +
      tailB N pT Y' +
      (resR (N : ℝ) 100 z pc dA {2, 5} + midB N pc Yc + Ec) := by
  classical
  have hcN := hwc.2.1
  have hcN' := hwc'.2.1
  have hc1 := hwc.1
  have hc1' := hwc'.1
  have hbN := hw.2.1
  set TA := cls100 (fun t => t % 4 = r)
  set TB := cls100 (fun t => t % 25 = 7 ∧ t % 2 = 0)
  set TC := cls100 (fun t => t % 25 = 18 ∧ t % 2 = 0)
  set T7 := cls100 (fun t => Unsieved 7 r t)
  set T18 := cls100 (fun t => Unsieved 18 r t)
  set T6 := cls100 (fun t => ¬ Unsieved 7 r t ∧ ¬ Unsieved 18 r t)
  have hTA : TA.card = 2 := by rcases hr with rfl | rfl <;> decide
  have hTB : TB.card = 2 := by decide
  have hTC : TC.card = 2 := by decide
  have hT7 : T7.card = 1 := by rcases hr with rfl | rfl <;> decide
  have hT18 : T18.card = 1 := by rcases hr with rfl | rfl <;> decide
  have hT6 : T6.card = 6 := by rcases hr with rfl | rfl <;> decide
  have hm := card_midSet_le_midB N b pc Y
  have hmc := card_midSet_le_midB N c pc Yc
  have hmc' := card_midSet_le_midB N c' pc Yc'
  have ht := card_u1Tail_le N pT Y' hY'
  have hu7 : ∀ a, Unsieved 7 r a → a % 100 ∈ T7 := fun a ha =>
    mem_cls100 (Or.inl ha.1) (by unfold Unsieved at ha ⊢; rw [mod100_25, mod100_4]; exact ha)
  have hu18 : ∀ a, Unsieved 18 r a → a % 100 ∈ T18 := fun a ha =>
    mem_cls100 (Or.inr ha.1) (by unfold Unsieved at ha ⊢; rw [mod100_25, mod100_4]; exact ha)
  -- the star part of b
  obtain ⟨C, hC, hCc⟩ := star_cover_min N b r xb zB pT dB z₁ z₂ pc nS dC Y τ hw hbs hbr hr hbx hdB hdC hz₂ hτ hpre
  constructor
  · -- three witnesses
    have hPb78 : ∀ a, (((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
        (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a)) →
        a % 25 = 7 ∨ a % 25 = 18 := by intro a ha; omega
    have cb := bad_parts_cover3 N b 100 pc Y 1 c c' TA TB TC {2, 5}
      (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
        (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a))
      (fun a ha => by
        rcases ha with ⟨h78, h4⟩ | ⟨h7, h2, hca⟩ | ⟨h18, h2, hca⟩
        · exact Or.inl ⟨mem_cls100 h78 (by rw [mod100_4]; exact h4), by omega⟩
        · exact Or.inr (Or.inl ⟨mem_cls100 (Or.inl h7) (by rw [mod100_25, mod100_2]; exact ⟨h7, h2⟩), hca⟩)
        · exact Or.inr (Or.inr ⟨mem_cls100 (Or.inr h18) (by rw [mod100_25, mod100_2]; exact ⟨h18, h2⟩), hca⟩))
      (fun a ha => excl25_star hbs hbr hr (hPb78 a ha) (by omega))
    have hcovb := cover_bs cb hC
    have dXS := disj_bad_star N b b r _ hPb78
    have hcardb := (card_le_card hcovb)
    rw [card_union_of_disjoint dXS] at hcardb
    have k1 := Finset.card_union_le ((((((TA.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) ∪
      TB.biUnion (fun t => rPartI N c b 100 t pc {2, 5})) ∪ TC.biUnion (fun t => rPartI N c' b 100 t pc {2, 5})) ∪ C) ∪
      midSet N b pc Y) ∪ exSet N b Y) (u1Tail N pT)
    have k2 := card_union4 (((TA.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) ∪
      TB.biUnion (fun t => rPartI N c b 100 t pc {2, 5})) ∪ TC.biUnion (fun t => rPartI N c' b 100 t pc {2, 5}))
      C (midSet N b pc Y) (exSet N b Y)
    have k3 := Finset.card_union_le ((TA.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) ∪
      TB.biUnion (fun t => rPartI N c b 100 t pc {2, 5})) (TC.biUnion (fun t => rPartI N c' b 100 t pc {2, 5}))
    have k4 := Finset.card_union_le (TA.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5}))
      (TB.biUnion (fun t => rPartI N c b 100 t pc {2, 5}))
    -- the parts sieved by c' and by c
    have cc' := card_cover1 (bad_parts_cover N c' 100 c pc Yc' T7 {2, 5} (fun a => Unsieved 7 r a ∧ c ≤ a)
      (fun a ha => ⟨hu7 a ha.1, ha.2⟩)
      (fun a ha => excl25_cross hr hcr' ha.1.2 (Or.inl ⟨ha.1.1, hc18⟩)))
    have cc := card_cover1 (bad_parts_cover N c 100 c' pc Yc T18 {2, 5} (fun a => Unsieved 18 r a ∧ c' ≤ a)
      (fun a ha => ⟨hu18 a ha.1, ha.2⟩)
      (fun a ha => excl25_cross hr hcr ha.1.2 (Or.inr ⟨ha.1.1, hc7⟩)))
    have rA := card_rParts_le N 1 b 100 z pc dA TA {2, 5} le_rfl (by omega) (by norm_num) cls100_lt hdA coprime100'
    have rB := card_rParts_le N c b 100 z pc dA TB {2, 5} hc1 (by omega) (by norm_num) cls100_lt hdA coprime100'
    have rC := card_rParts_le N c' b 100 z pc dA TC {2, 5} hc1' (by omega) (by norm_num) cls100_lt hdA coprime100'
    have r7 := card_rParts_le N c c' 100 z pc dA T7 {2, 5} hc1 (by omega) (by norm_num) cls100_lt hdA coprime100'
    have r18 := card_rParts_le N c' c 100 z pc dA T18 {2, 5} hc1' (by omega) (by norm_num) cls100_lt hdA coprime100'
    rw [hTA, show N + 1 - 1 = N by omega] at rA
    rw [hTB] at rB; rw [hTC] at rC; rw [hT7] at r7; rw [hT18] at r18
    rw [← badCount_eq] at cc cc'
    have e1 := (Nat.cast_le (α := ℝ)).mpr (hcardb.trans (k1.trans (Nat.add_le_add_right
      (k2.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
        (k3.trans (Nat.add_le_add_right k4 _)) _) _) _)) _)))
    have e2 := (Nat.cast_le (α := ℝ)).mpr cc
    have e3 := (Nat.cast_le (α := ℝ)).mpr cc'
    rw [← badCount_eq, ← starCount_eq] at e1
    push_cast at e1 e2 e3 rA rB rC r7 r18 ⊢
    unfold tailB
    linarith
  · -- two witnesses and the whole class `Unsieved 7 r`
    have hQ78 : ∀ a, ((a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a) →
        a % 25 = 7 ∨ a % 25 = 18 := fun a ha => ha.1
    have cb := bad_parts_cover N b 100 1 pc Y T6 {2, 5}
      (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a)
      (fun a ha => ⟨mem_cls100 ha.1 (by
          unfold Unsieved at ha ⊢; rw [mod100_25, mod100_4]; exact ha.2), by omega⟩)
      (fun a ha => excl25_star hbs hbr hr ha.1 (by
          unfold Unsieved at ha; rcases hr with rfl | rfl <;> omega))
    have hcovb := cover_bs cb hC
    have dXS := disj_bad_star N b b r _ hQ78
    have hcardb := (card_le_card hcovb)
    rw [card_union_of_disjoint dXS] at hcardb
    have k1 := Finset.card_union_le (((((T6.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) ∪ C) ∪
      midSet N b pc Y) ∪ exSet N b Y)) (u1Tail N pT)
    have k2 := card_union4 (T6.biUnion (fun t => rPartI N 1 b 100 t pc {2, 5})) C (midSet N b pc Y) (exSet N b Y)
    have cc := card_cover1 (bad_parts_cover N c 100 1 pc Yc T18 {2, 5} (Unsieved 18 r)
      (fun a ha => ⟨hu18 a ha, by unfold Unsieved at ha; omega⟩)
      (fun a ha => excl25_cross hr hcr ha.2 (Or.inr ⟨ha.1, hc7⟩)))
    have r6 := card_rParts_le N 1 b 100 z pc dA T6 {2, 5} le_rfl (by omega) (by norm_num) cls100_lt hdA coprime100'
    have r18 := card_rParts_le N 1 c 100 z pc dA T18 {2, 5} le_rfl (by omega) (by norm_num) cls100_lt hdA coprime100'
    rw [hT6, show N + 1 - 1 = N by omega] at r6
    rw [hT18, show N + 1 - 1 = N by omega] at r18
    obtain ⟨t0, ht0⟩ := unsieved_class 7 r hr (Or.inl rfl)
    have hcl := classCount_one N (Unsieved 7 r) t0 ht0
    rw [← badCount_eq] at cc
    have e1 := (Nat.cast_le (α := ℝ)).mpr (hcardb.trans (k1.trans (Nat.add_le_add_right k2 _)))
    have e2 := (Nat.cast_le (α := ℝ)).mpr cc
    rw [← badCount_eq, ← starCount_eq] at e1
    push_cast at e1 e2 r6 r18 ⊢
    unfold tailB
    linarith

end Erdos848
