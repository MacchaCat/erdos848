import Erdos848.LemmaC

/-!
# Phase 6 (part 3): explicit real bounds for each case of `CountBounds`

`resB`, `shB`, `lemBB`, `lemCB` are the explicit bounds of Lemma A′(iii) (restricted part),
Lemma A′(i)+(ii) (the shared sets of a witness), Lemma B and Lemma C.  For every case of
`CountBounds N` we bound the left-hand side by a sum of these (`caseIb_real`, …).
-/

namespace Erdos848

open Finset

/-! ### The explicit bounds -/

/-- Lemma A′(iii): `T` classes mod `q`, primes in `excl` excluded. -/
noncomputable def resB (N q T z pc : ℕ) (excl : Finset ℕ) : ℝ :=
  T * ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
    ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
    ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1))

/-- Lemma A′(i)+(ii): the shared sets `Mid(b) ∪ Ex(b)` of a witness. -/
noncomputable def shB (N b pc Y : ℕ) : ℝ :=
  ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) +
    rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2)

/-- Lemma B: `T` classes mod `q`. -/
noncomputable def lemBB (N q T zB pB Y' : ℕ) : ℝ :=
  T * ((N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
    ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
    ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2)) +
  ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
  (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ)

/-- Lemma C (without the shared sets). -/
noncomputable def lemCB (N z₁ z₂ pB Y' pc : ℕ) (G : ℝ) : ℝ :=
  23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) +
  ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
  (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) +
  ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
  ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
  G +
  ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1)

/-! ### Residue facts -/

/-- (F2) -/
lemma not25_star {a b : ℕ} (ha : a % 25 = 7 ∨ a % 25 = 18) (hb : IsStar b) :
    ¬ 5 * 5 ∣ a * b + 1 := by
  intro h
  have h0 : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
  rw [mod_mul_add_one] at h0
  have := Nat.mod_lt b (show 0 < 25 by norm_num)
  unfold IsStar at hb
  rcases ha with ha | ha <;> rw [ha] at h0 <;> interval_cases hr : b % 25 <;> omega

/-- (F3) -/
lemma not25_7_18 {a b : ℕ} (h : (a % 25 = 7 ∧ b % 25 = 18) ∨ (a % 25 = 18 ∧ b % 25 = 7)) :
    ¬ 5 * 5 ∣ a * b + 1 := by
  intro hd
  have h0 : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hd)
  rw [mod_mul_add_one] at h0
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h0 <;> norm_num at h0

/-- (F4), even case. -/
lemma not4_even {a b : ℕ} (h : a % 2 = 0 ∨ b % 2 = 0) : ¬ 2 * 2 ∣ a * b + 1 := by
  intro hd
  have h2 : 2 ∣ a * b + 1 := dvd_trans ⟨2, rfl⟩ hd
  have : 2 ∣ a * b := by
    rcases h with h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) b
    · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) a
  omega

/-- (F4), odd case: `a ≡ b ≡ r (mod 4)` with `r` odd. -/
lemma not4_same {a b : ℕ} (h : (a % 4 = 1 ∧ b % 4 = 1) ∨ (a % 4 = 3 ∧ b % 4 = 3)) :
    ¬ 2 * 2 ∣ a * b + 1 := by
  intro hd
  have h0 : (a * b + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hd)
  rw [mod_mul_add_one] at h0
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h0 <;> norm_num at h0

lemma coprime100 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) : Nat.Coprime 100 p := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have : p ∣ 2 ^ 2 * 5 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h'))

lemma coprime25 {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 p := by
  have := (Nat.coprime_primes Nat.prime_five hp).mpr (Ne.symm h5)
  exact Nat.Coprime.pow_left 2 this

lemma coprime_U1 {p : ℕ} (hU : IsU1 p) : Nat.Coprime 100 p :=
  coprime100 hU.1 (by have := hU.2.2; omega) (by have := hU.2.2; omega)

/-! ### Assembling one witness -/

lemma badCount_resB (N b q T z pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop)
    [DecidablePred Pa] (hb : 1 ≤ b) (hY : 1 ≤ Y) (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q)
    (hTc : Tset.card = T) (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p)
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (badCount N Pa b : ℝ) ≤ resB N q T z pc excl + shB N b pc Y := by
  have := badCount_le N b q z pc Y Tset excl Pa hb hY hq hTq hcop hT hexcl
  unfold resB shB; rw [← hTc]; linarith

lemma vCount_lemBB (N q T zB pB Y' : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hTc : Tset.card = T)
    (hcop : ∀ p, p.Prime → IsU1 p → Nat.Coprime q p)
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (vCount N Px : ℝ) ≤ lemBB N q T zB pB Y' := by
  have := vCount_le N q zB pB Y' Tset Px hq hTq hcop hT hstar
  unfold lemBB; rw [← hTc]; linarith

/-- A whole set of classes mod 100. -/
lemma classCount_le (N : ℕ) (D : Finset ℕ) (hD : ∀ t ∈ D, t < 100) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ a, P a → a % 100 ∈ D) :
    (classCount N P : ℝ) ≤ D.card * ((N : ℝ) / 100) + D.card := by
  have h := card_mod_mem_real N 100 (by norm_num) D hD
  rw [abs_le] at h
  have hsub : classCount N P ≤ ((Icc 1 N).filter (fun a => a % 100 ∈ D)).card := by
    unfold classCount; apply card_le_card; intro a ha
    rw [mem_filter] at ha ⊢; exact ⟨ha.1, hP a ha.2⟩
  have : (classCount N P : ℝ) ≤ ((Icc 1 N).filter (fun a => a % 100 ∈ D)).card := by
    exact_mod_cast hsub
  push_cast at h
  linarith

/-! ### The cases -/

theorem caseIb_real (N b b' z pc Y : ℕ) (hY : 1 ≤ Y) (hw : Witness N b) (h7 : b % 25 = 7)
    (hw' : Witness N b') (h18 : b' % 25 = 18) :
    (badCount N (fun a => a % 25 = 18) b : ℝ) + badCount N (fun a => a % 25 = 7) b' ≤
      (resB N 25 1 z pc {5} + shB N b pc Y) + (resB N 25 1 z pc {5} + shB N b' pc Y) := by
  have e1 := badCount_resB N b 25 1 z pc Y {18} {5} (fun a => a % 25 = 18) hw.1 hY (by norm_num)
    (by simp) (by simp) (fun p hp hne => coprime25 hp (by simpa using hne)) (by simp)
    (fun a ha p hp => by
      rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inr ⟨ha, h7⟩))
  have e2 := badCount_resB N b' 25 1 z pc Y {7} {5} (fun a => a % 25 = 7) hw'.1 hY (by norm_num)
    (by simp) (by simp) (fun p hp hne => coprime25 hp (by simpa using hne)) (by simp)
    (fun a ha p hp => by
      rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inl ⟨ha, h18⟩))
  linarith

theorem caseII_real (N b z pc Y z₁ z₂ pB Y' : ℕ) (G : ℝ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hbs : IsStar b) (hbe : b % 2 = 0) (h5 : 5 ≤ z₂)
    (hG : ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 → ∑ p ∈ S, gC N z₁ p ≤ G) :
    (badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b : ℝ) + lemCCount N b ≤
      resB N 25 2 z pc {2, 5} + lemCB N z₁ z₂ pB Y' pc G + shB N b pc Y := by
  classical
  set Tset : Finset ℕ := {7, 18}
  set Bset := (Icc 1 N).filter (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Squarefree (a * b + 1))
  set R := Tset.biUnion (fun t => resPart N b 25 t pc {2, 5})
  have hB := witness_cover N b 25 pc Y Tset {2, 5} (fun a => a % 25 = 7 ∨ a % 25 = 18)
    (fun a ha => by simp only [Tset, mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr hbe)
      · exact not25_star ha hbs)
  have hC := lemC_cover N b z₁ z₂ pB Y' pc Y hbe
  have hdisj : Disjoint Bset (lemCSet N b) := by
    rw [disjoint_left]; intro a ha hc
    simp only [Bset, lemCSet, mem_filter] at ha hc
    unfold IsStar at hc; omega
  have hsub : Bset ∪ lemCSet N b ⊆ ((R ∪ lemCPart N b z₁ z₂ pB Y' pc) ∪ midSet N b pc Y) ∪
      exSet N b Y := by
    intro a ha
    rcases mem_union.mp ha with h | h
    · have := hB h
      simp only [mem_union] at this ⊢; tauto
    · have := hC h
      simp only [mem_union] at this ⊢; tauto
  have hcard : Bset.card + (lemCSet N b).card ≤ R.card + (lemCPart N b z₁ z₂ pB Y' pc).card +
      (midSet N b pc Y).card + (exSet N b Y).card := by
    rw [← card_union_of_disjoint hdisj]
    have a0 := card_le_card hsub
    have a1 := Finset.card_union_le ((R ∪ lemCPart N b z₁ z₂ pB Y' pc) ∪ midSet N b pc Y)
      (exSet N b Y)
    have a2 := Finset.card_union_le (R ∪ lemCPart N b z₁ z₂ pB Y' pc) (midSet N b pc Y)
    have a3 := Finset.card_union_le R (lemCPart N b z₁ z₂ pB Y' pc)
    omega
  have hcardR : (badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b : ℝ) + lemCCount N b ≤
      (R.card : ℝ) + (lemCPart N b z₁ z₂ pB Y' pc).card + (midSet N b pc Y).card +
        (exSet N b Y).card := by
    have : badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount N b ≤ R.card +
        (lemCPart N b z₁ z₂ pB Y' pc).card + (midSet N b pc Y).card + (exSet N b Y).card :=
      hcard
    exact_mod_cast this
  have hR : (R.card : ℝ) ≤ resB N 25 2 z pc {2, 5} := by
    have h1 : (R.card : ℝ) ≤ ∑ t ∈ Tset, ((resPart N b 25 t pc {2, 5}).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 := sum_le_sum (fun t (ht : t ∈ Tset) => card_resPart_le N b 25 t z pc {2, 5}
      (by norm_num) (by simp only [Tset, mem_insert, mem_singleton] at ht; omega)
      (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)))
    rw [sum_const, show Tset.card = 2 by decide, nsmul_eq_mul] at h2
    unfold resB; push_cast at h2 ⊢; linarith
  have hCP := card_lemCPart_le N b z₁ z₂ pB Y' pc G hw.2.1 hbs h5 hG
  have hmid := card_midSet_le N b pc Y
  have hex := card_exSet_le N b Y hw.1 hY
  unfold lemCB shB
  linarith

/-- The 23 odd classes mod 50 of `A*`. -/
def T50 : Finset ℕ := (range 50).filter (fun t => t % 2 = 1 ∧ t % 25 ≠ 7 ∧ t % 25 ≠ 18)

/-- The 23 classes mod 100 of `A*` in the class `r` mod 4. -/
def T100 (r : ℕ) : Finset ℕ := (range 100).filter (fun t => t % 25 ≠ 7 ∧ t % 25 ≠ 18 ∧ t % 4 = r)

lemma T100_card {r : ℕ} (hr : r = 1 ∨ r = 3) : (T100 r).card = 23 := by
  rcases hr with rfl | rfl <;> decide

lemma vCount_III2 (N zB pB Y' r : ℕ) (hr : r = 1 ∨ r = 3) :
    (vCount N (fun x => IsStar x ∧ x % 4 = r) : ℝ) ≤ lemBB N 100 23 zB pB Y' :=
  vCount_lemBB N 100 23 zB pB Y' (T100 r) _ (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) (T100_card hr)
    (fun p _ hU => coprime_U1 hU)
    (fun x hx => by
      unfold IsStar at hx
      simp only [T100, mem_filter, mem_range]; omega)
    (fun x hx => hx.1)

theorem caseIII1_real (N b₁ b₃ z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y)
    (hw₁ : Witness N b₁) (hs₁ : IsStar b₁) (hr₁ : b₁ % 4 = 1)
    (hw₃ : Witness N b₃) (hs₃ : IsStar b₃) (hr₃ : b₃ % 4 = 3) :
    (badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ : ℝ) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
      vCount N (fun x => IsStar x ∧ x % 2 = 1) ≤
      (resB N 100 6 z pc {2, 5} + shB N b₁ pc Y) + (resB N 100 2 z pc {2, 5} + shB N b₃ pc Y) +
        lemBB N 50 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  have e1 := badCount_resB N b₁ 100 6 z pc Y {32, 57, 82, 18, 68, 93} {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) hw₁.1 hY
    (by norm_num) (by simp) (by decide) hcop
    (fun a ha => by simp only [mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · exact not4_same (Or.inl ⟨h, hr₁⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star ha.1 hs₁)
  have e3 := badCount_resB N b₃ 100 2 z pc Y {7, 43} {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) hw₃.1 hY
    (by norm_num) (by simp) (by decide) hcop
    (fun a ha => by simp only [mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_same (Or.inr ⟨ha.2, hr₃⟩)
      · exact not25_star ha.1 hs₃)
  have ev := vCount_lemBB N 50 23 zB pB Y' T50 (fun x => IsStar x ∧ x % 2 = 1) (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) (by decide)
    (fun p _ hU => Nat.Coprime.coprime_dvd_left (by norm_num) (coprime_U1 hU))
    (fun x hx => by
      have := hx.1; unfold IsStar at this
      simp only [T50, mem_filter, mem_range]; omega)
    (fun x hx => hx.1)
  linarith

theorem caseIII2a_real (N b r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3) :
    (classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      (2 * ((N : ℝ) / 100) + 2) + (resB N 100 2 z pc {2, 5} + shB N b pc Y) +
        lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ t % 4 = 4 - r)
  have hD : D.card = 2 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ t % 4 = r)
  have hTs : Ts.card = 2 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 2 z pc Y Ts {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases hr with rfl | rfl
        · exact not4_same (Or.inl ⟨ha.2, hbr⟩)
        · exact not4_same (Or.inr ⟨ha.2, hbr⟩)
      · exact not25_star ha.1 hs)
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

theorem caseIII2b7_real (N b b' r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hw' : Witness N b') (h7 : b' % 25 = 7) (he : b' % 2 = 0) :
    (classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 18) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      ((N : ℝ) / 100 + 1) + (resB N 100 3 z pc {2, 5} + shB N b pc Y) +
        (resB N 25 1 z pc {2, 5} + shB N b' pc Y) + lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => t % 25 = 7 ∧ t % 4 = 4 - r)
  have hD : D.card = 1 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => a % 25 = 7 ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => t % 25 = 7 ∧ (t % 4 = r ∨ t % 2 = 0))
  have hTs : Ts.card = 3 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 3 z pc Y Ts {2, 5}
    (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · rcases hr with rfl | rfl
          · exact not4_same (Or.inl ⟨h, hbr⟩)
          · exact not4_same (Or.inr ⟨h, hbr⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star (Or.inl ha.1) hs)
  have eb' := badCount_resB N b' 25 1 z pc Y {18} {2, 5} (fun a => a % 25 = 18) hw'.1 hY
    (by norm_num) (by simp) (by simp)
    (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)) (by simp)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr he)
      · exact not25_7_18 (Or.inr ⟨ha, h7⟩))
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

theorem caseIII2b18_real (N b b' r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hw' : Witness N b') (h18 : b' % 25 = 18) (he : b' % 2 = 0) :
    (classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 7) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      ((N : ℝ) / 100 + 1) + (resB N 100 3 z pc {2, 5} + shB N b pc Y) +
        (resB N 25 1 z pc {2, 5} + shB N b' pc Y) + lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => t % 25 = 18 ∧ t % 4 = 4 - r)
  have hD : D.card = 1 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => a % 25 = 18 ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => t % 25 = 18 ∧ (t % 4 = r ∨ t % 2 = 0))
  have hTs : Ts.card = 3 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 3 z pc Y Ts {2, 5}
    (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · rcases hr with rfl | rfl
          · exact not4_same (Or.inl ⟨h, hbr⟩)
          · exact not4_same (Or.inr ⟨h, hbr⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star (Or.inr ha.1) hs)
  have eb' := badCount_resB N b' 25 1 z pc Y {7} {2, 5} (fun a => a % 25 = 7) hw'.1 hY
    (by norm_num) (by simp) (by simp)
    (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)) (by simp)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr he)
      · exact not25_7_18 (Or.inl ⟨ha, h18⟩))
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

end Erdos848
