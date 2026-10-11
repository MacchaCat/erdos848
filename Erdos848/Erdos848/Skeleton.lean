import Erdos848.Basic

/-!
# The combinatorial skeleton of the analytic part

For an admissible `A ⊆ [1,N]` we split `A = A₇ ∪ A₁₈ ∪ A*` and run the case analysis of
`proof.md` §5.  Every part of `A` is bounded by a *count* of integers in `[1,N]` — either a whole
residue class, or the integers `a` with `a·b+1` not squarefree for a witness `b ∈ A`, or the
integers `x` with `x²+1` not squarefree.  The theorem `statement_of_bounds` shows:

  if these explicit counts satisfy the inequalities collected in `CountBounds N`,
  then `Statement N` holds.

So the analytic part reduces to purely number-theoretic counting inequalities (`CountBounds N`),
with all combinatorial reasoning formalised here.
-/

namespace Erdos848

open Finset

/-- `a ∈ A*`-type residue: `a ≢ 7, 18 (mod 25)`. -/
def IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18

instance : DecidablePred IsStar := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Integers `a ∈ [1,N]` with property `P` and `a·b+1` not squarefree. -/
def badCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card

/-- Integers `a ∈ [1,N]` with property `P`. -/
def classCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ := ((Icc 1 N).filter P).card

/-- Integers `x ∈ [1,N]` with property `P` and `x²+1` not squarefree. -/
def vCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  ((Icc 1 N).filter (fun x => P x ∧ ¬ Squarefree (x * x + 1))).card

/-- Lemma C set: `x ∈ [1,N]`, `x ≢ ±7 (25)`, `x²+1` and `x·b+1` both not squarefree. -/
def lemCCount (N b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))).card

/-- A witness: an element of `[1,N]` lying in `V` (its square plus one is not squarefree). -/
def Witness (N b : ℕ) : Prop := 1 ≤ b ∧ b ≤ N ∧ ¬ Squarefree (b * b + 1)

/-- The counting inequalities of the case analysis (`proof.md` §5), one per case. -/
structure CountBounds (N : ℕ) : Prop where
  /-- I.b: witnesses `b ∈ A₇` (sieves `A₁₈`) and `b' ∈ A₁₈` (sieves `A₇`). -/
  caseIb : ∀ b b', Witness N b → b % 25 = 7 → Witness N b' → b' % 25 = 18 →
    badCount N (fun a => a % 25 = 18) b + badCount N (fun a => a % 25 = 7) b' ≤ c7 N
  /-- II: an even witness `b ∈ A*` sieves `A₇ ∪ A₁₈`; Lemma C bounds `A*`. -/
  caseII : ∀ b, Witness N b → IsStar b → b % 2 = 0 →
    badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount N b ≤ c7 N
  /-- III.1: odd witnesses `b₁ ≡ 1`, `b₃ ≡ 3 (mod 4)` in `A*`; `A*` odd. -/
  caseIII1 : ∀ b₁ b₃, Witness N b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness N b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount N (fun x => IsStar x ∧ x % 2 = 1) ≤ c7 N
  /-- III.2.a: `A* ⊆ {≡ r (mod 4)}` (r = 1 or 3, s = 4 - r), `A₇ ∪ A₁₈` odd. -/
  caseIII2a : ∀ b r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N
  /-- III.2.b (even witness in `A₇`): `A* ⊆ {≡ r (mod 4)}`, even `b' ∈ A₇`. -/
  caseIII2b7 : ∀ b b' r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount N (fun a => a % 25 = 18) b' +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N
  /-- III.2.b (even witness in `A₁₈`). -/
  caseIII2b18 : ∀ b b' r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount N (fun a => a % 25 = 7) b' +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N

/-! ### Basic counting tools -/

lemma card_le_two {A : Finset ℕ} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a ∈ A, P a ∨ Q a) : A.card ≤ (A.filter P).card + (A.filter Q).card := by
  calc A.card ≤ (A.filter P ∪ A.filter Q).card := by
        apply card_le_card; intro a ha
        rcases h a ha with hp | hq
        · exact mem_union_left _ (mem_filter.mpr ⟨ha, hp⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨ha, hq⟩)
    _ ≤ _ := card_union_le _ _

variable {N : ℕ} {A : Finset ℕ}

lemma filter_le_bad (hA : Admissible A) (hsub : A ⊆ Icc 1 N) {b : ℕ} (hb : b ∈ A)
    (P : ℕ → Prop) [DecidablePred P] : (A.filter P).card ≤ badCount N P b := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ha.2, hA a ha.1 b hb⟩

lemma filter_le_class (hsub : A ⊆ Icc 1 N) (P : ℕ → Prop) [DecidablePred P] :
    (A.filter P).card ≤ classCount N P := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ha.2⟩

lemma filter_le_v (hA : Admissible A) (hsub : A ⊆ Icc 1 N) (P : ℕ → Prop) [DecidablePred P] :
    (A.filter P).card ≤ vCount N P := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ha.2, hA a ha.1 a ha.1⟩

lemma witness_of_mem (hA : Admissible A) (hsub : A ⊆ Icc 1 N) {b : ℕ} (hb : b ∈ A) :
    Witness N b := by
  have := mem_Icc.mp (hsub hb)
  exact ⟨this.1, this.2, hA b hb b hb⟩

/-- The class `18 mod 25` is never larger than the class `7 mod 25` in `[1,N]`. -/
lemma class18_le_c7 : classCount N (fun a => a % 25 = 18) ≤ c7 N := by
  rw [← C7set_card]
  unfold classCount C7set
  apply card_le_card_of_injOn (fun a => a - 11)
  · intro a ha
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · intro a ha a' ha' h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ha'
    simp only at h
    omega

lemma class7_eq_c7 : classCount N (fun a => a % 25 = 7) = c7 N := C7set_card N

/-! ### The case analysis -/

theorem statement_of_bounds (h : CountBounds N) : Statement N := by
  classical
  intro A hsub hA
  -- the three parts
  have hsplit : A.card ≤ (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card +
      (A.filter IsStar).card :=
    card_le_two _ _ (fun a _ => by unfold IsStar; omega)
  by_cases hII : ∃ b ∈ A, IsStar b ∧ b % 2 = 0
  · -- Case II
    obtain ⟨b, hb, hbs, hbe⟩ := hII
    have h1 := filter_le_bad hA hsub hb (fun a => a % 25 = 7 ∨ a % 25 = 18)
    have h2 : (A.filter IsStar).card ≤ lemCCount N b := by
      apply card_le_card; intro x hx
      rw [mem_filter] at hx
      exact mem_filter.mpr ⟨hsub hx.1, hx.2, hA x hx.1 x hx.1, hA x hx.1 b hb⟩
    have := h.caseII b (witness_of_mem hA hsub hb) hbs hbe
    omega
  push Not at hII
  -- from here on every element of A* is odd
  have hodd : ∀ x ∈ A, IsStar x → x % 2 = 1 := fun x hx hs => by
    have := hII x hx hs; omega
  by_cases hIII1 : ∃ b₁ ∈ A, ∃ b₃ ∈ A, IsStar b₁ ∧ b₁ % 4 = 1 ∧ IsStar b₃ ∧ b₃ % 4 = 3
  · -- Case III.1
    obtain ⟨b₁, hb₁, b₃, hb₃, hs₁, hr₁, hs₃, hr₃⟩ := hIII1
    have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ := by
      have := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 4 = 1 ∨ a % 2 = 0) (fun a => a % 4 = 3) (fun a _ => by omega)
      rw [filter_filter, filter_filter] at this
      have e1 := filter_le_bad hA hsub hb₁ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0))
      have e2 := filter_le_bad hA hsub hb₃ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3)
      omega
    have hS : (A.filter IsStar).card ≤ vCount N (fun x => IsStar x ∧ x % 2 = 1) := by
      calc (A.filter IsStar).card = (A.filter (fun x => IsStar x ∧ x % 2 = 1)).card := by
            congr 1; apply filter_congr; intro x hx
            exact ⟨fun hs => ⟨hs, hodd x hx hs⟩, fun h => h.1⟩
        _ ≤ _ := filter_le_v hA hsub _
    have := h.caseIII1 b₁ b₃ (witness_of_mem hA hsub hb₁) hs₁ hr₁ (witness_of_mem hA hsub hb₃) hs₃ hr₃
    omega
  push Not at hIII1
  by_cases hStar : ∃ b ∈ A, IsStar b
  · -- Case III.2: all of A* lies in the residue class r = b mod 4
    obtain ⟨b, hb, hbs⟩ := hStar
    set r := b % 4 with hr
    have hr13 : r = 1 ∨ r = 3 := by have := hodd b hb hbs; omega
    have hAllr : ∀ x ∈ A, IsStar x → x % 4 = r := by
      intro x hx hxs
      have hxo := hodd x hx hxs
      rcases hr13 with h1 | h3
      · by_contra hne
        exact hIII1 b hb x hx hbs (by omega) hxs (by omega)
      · by_contra hne
        exact hIII1 x hx b hb hxs (by omega) hbs (by omega)
    have hS : (A.filter IsStar).card ≤ vCount N (fun x => IsStar x ∧ x % 4 = r) := by
      calc (A.filter IsStar).card = (A.filter (fun x => IsStar x ∧ x % 4 = r)).card := by
            congr 1; apply filter_congr; intro x hx
            exact ⟨fun hs => ⟨hs, hAllr x hx hs⟩, fun h => h.1⟩
        _ ≤ _ := filter_le_v hA hsub _
    have hwb := witness_of_mem hA hsub hb
    by_cases hEven : ∃ b' ∈ A, (b' % 25 = 7 ∨ b' % 25 = 18) ∧ b' % 2 = 0
    · obtain ⟨b', hb', h78, hbe'⟩ := hEven
      have hwb' := witness_of_mem hA hsub hb'
      rcases h78 with h7 | h18
      · -- III.2.b, even witness in A₇
        have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
            classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
            badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
            badCount N (fun a => a % 25 = 18) b' := by
          have c1 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
            (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
          have c2 := card_le_two (A := (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter (fun a => a % 25 = 7))
            (fun a => a % 4 = 4 - r) (fun a => a % 4 = r ∨ a % 2 = 0) (fun a _ => by omega)
          simp only [filter_filter] at c1 c2
          have e1 := filter_le_class hsub (fun a => a % 25 = 7 ∧ a % 4 = 4 - r)
          have e2 := filter_le_bad hA hsub hb (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0))
          have e3 := filter_le_bad hA hsub hb' (fun a => a % 25 = 18)
          have s1 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7) ∧ a % 4 = 4 - r)).card ≤
              (A.filter fun a => a % 25 = 7 ∧ a % 4 = 4 - r).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s2 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7) ∧ (a % 4 = r ∨ a % 2 = 0))).card ≤
              (A.filter fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s3 : ((A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18)).card ≤
              (A.filter fun a => a % 25 = 18).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
          omega
        have := h.caseIII2b7 b b' r hwb hbs rfl hr13 hwb' h7 hbe'
        omega
      · -- III.2.b, even witness in A₁₈
        have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
            classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
            badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
            badCount N (fun a => a % 25 = 7) b' := by
          have c1 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
            (fun a => a % 25 = 18) (fun a => a % 25 = 7) (fun a ha => (mem_filter.mp ha).2.symm)
          have c2 := card_le_two (A := (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter (fun a => a % 25 = 18))
            (fun a => a % 4 = 4 - r) (fun a => a % 4 = r ∨ a % 2 = 0) (fun a _ => by omega)
          simp only [filter_filter] at c1 c2
          have e1 := filter_le_class hsub (fun a => a % 25 = 18 ∧ a % 4 = 4 - r)
          have e2 := filter_le_bad hA hsub hb (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0))
          have e3 := filter_le_bad hA hsub hb' (fun a => a % 25 = 7)
          have s1 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18) ∧ a % 4 = 4 - r)).card ≤
              (A.filter fun a => a % 25 = 18 ∧ a % 4 = 4 - r).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s2 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18) ∧ (a % 4 = r ∨ a % 2 = 0))).card ≤
              (A.filter fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s3 : ((A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7)).card ≤
              (A.filter fun a => a % 25 = 7).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
          omega
        have := h.caseIII2b18 b b' r hwb hbs rfl hr13 hwb' h18 hbe'
        omega
    · -- III.2.a: A₇ ∪ A₁₈ all odd
      push Not at hEven
      have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
          classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
          badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b := by
        have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
          (fun a => a % 4 = 4 - r) (fun a => a % 4 = r) (fun a ha => by
            have ha' := mem_filter.mp ha
            have := hEven a ha'.1 ha'.2
            omega)
        simp only [filter_filter] at c
        have e1 := filter_le_class hsub (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r)
        have e2 := filter_le_bad hA hsub hb (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r)
        omega
      have := h.caseIII2a b r hwb hbs rfl hr13
      omega
  · -- Case I: A* = ∅
    push Not at hStar
    have hS0 : (A.filter IsStar).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => hStar x hx
    have h78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        (A.filter (fun a => a % 25 = 7)).card + (A.filter (fun a => a % 25 = 18)).card := by
      have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
      simp only [filter_filter] at c
      have s1 : (A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7).card ≤ (A.filter fun a => a % 25 = 7).card :=
        card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
      have s2 : (A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18).card ≤ (A.filter fun a => a % 25 = 18).card :=
        card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
      omega
    by_cases h7 : ∃ b ∈ A, b % 25 = 7
    · by_cases h18 : ∃ b' ∈ A, b' % 25 = 18
      · -- I.b
        obtain ⟨b, hb, hb7⟩ := h7
        obtain ⟨b', hb', hb18⟩ := h18
        have e1 := filter_le_bad hA hsub hb (fun a => a % 25 = 18)
        have e2 := filter_le_bad hA hsub hb' (fun a => a % 25 = 7)
        have := h.caseIb b b' (witness_of_mem hA hsub hb) hb7 (witness_of_mem hA hsub hb') hb18
        omega
      · -- I.a with A₁₈ = ∅
        push Not at h18
        have h0 : (A.filter (fun a => a % 25 = 18)).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h18 x hx
        have e := filter_le_class hsub (fun a => a % 25 = 7)
        rw [class7_eq_c7] at e
        omega
    · -- I.a with A₇ = ∅
      push Not at h7
      have h0 : (A.filter (fun a => a % 25 = 7)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h7 x hx
      have e := filter_le_class hsub (fun a => a % 25 = 18)
      have := class18_le_c7 (N := N)
      omega

end Erdos848
