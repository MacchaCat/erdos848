import Erdos848.Skeleton

/-!
# Phase 9.3: the combinatorial skeleton of Section 10 (minimal witnesses)

As `Skeleton.lean`, but every witness is the least element of its part, so that the part it
belongs to lies in `[b, N]`, and case III.2 is split as in `proof.md` §10.6:

* `r` is the class mod 4 of `A*` (`r = 1` or `3`); in `A₇ ∪ A₁₈` the witness `b ∈ A*` sieves every
  class except the two classes `≡ 4 - r (mod 4)`;
* `F₇ = {a ∈ A₇ : a ≢ r (mod 4)}`, `F₁₈ = {a ∈ A₁₈ : a ≢ r (mod 4)}`; an element of `F₁₈` sieves the
  unsieved class of `A₇`, an element of `F₇` the unsieved class of `A₁₈`;
* β: `F₁₈ = ∅` (or `F₇ = ∅`); α: both are nonempty.

`statement_of_bounds2 : CountBounds2 N → Statement N`.
-/

namespace Erdos848

open Finset

/-- `x ∈ [1,N]` with `b ≤ x`, `x ≡ e (mod 4)`, `x ∈ A*`-type, `x²+1` and `xb+1` not squarefree. -/
def starCount (N b e : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun x => b ≤ x ∧ x % 4 = e ∧ IsStar x ∧ ¬ Squarefree (x * x + 1) ∧
    ¬ Squarefree (x * b + 1))).card

/-- Lemma C set on the split domain: `x` odd or `b ≤ x`. -/
def lemCCount2 (N b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun x => (x % 2 = 1 ∨ b ≤ x) ∧ IsStar x ∧ ¬ Squarefree (x * x + 1) ∧
    ¬ Squarefree (x * b + 1))).card

/-- The class of `A₇` (`s = 7`) or `A₁₈` (`s = 18`) that a witness `≡ r (mod 4)` cannot sieve. -/
def Unsieved (s r a : ℕ) : Prop := a % 25 = s ∧ a % 4 = 4 - r

instance (s r : ℕ) : DecidablePred (Unsieved s r) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The counting inequalities of `proof.md` §10.6. -/
structure CountBounds2 (N : ℕ) : Prop where
  /-- I.b: `b = min A₇` sieves `A₁₈ ⊆ [b', N]`, `b' = min A₁₈` sieves `A₇ ⊆ [b, N]`. -/
  caseIb : ∀ b b', Witness N b → b % 25 = 7 → Witness N b' → b' % 25 = 18 →
    badCount N (fun a => a % 25 = 18 ∧ b' ≤ a) b + badCount N (fun a => a % 25 = 7 ∧ b ≤ a) b' ≤ c7 N
  /-- II: `b` the least even element of `A*`. -/
  caseII : ∀ b, Witness N b → IsStar b → b % 2 = 0 →
    badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount2 N b ≤ c7 N
  /-- III.1: `b₁ = min (A* ∩ (1 + 4ℤ))`, `b₃ = min (A* ∩ (3 + 4ℤ))`. -/
  caseIII1 : ∀ b₁ b₃, Witness N b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness N b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    starCount N b₁ 1 + starCount N b₃ 3 ≤ c7 N
  /-- III.2 β: `b = min A*`, `A* ⊆ r + 4ℤ`, and the part of `A_{s'}` sieving `Unsieved s r` is
  empty (`(s, s') = (7, 18)` or `(18, 7)`). -/
  caseIII2beta : ∀ b r s s', Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    ((s = 7 ∧ s' = 18) ∨ (s = 18 ∧ s' = 7)) →
    classCount N (Unsieved s r) +
    badCount N (fun a => (a % 25 = s ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = s' ∧ a % 4 = r)) b +
    starCount N b r ≤ c7 N
  /-- III.2 α: `b = min A*`, `c = min F₇`, `c' = min F₁₈`: three witnesses, or two witnesses and
  one whole class. -/
  caseIII2alpha : ∀ b r c c', Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N c → c % 25 = 7 → ¬ c % 4 = r → Witness N c' → c' % 25 = 18 → ¬ c' % 4 = r →
    (badCount N (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
        (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a)) b +
      badCount N (fun a => Unsieved 7 r a ∧ c ≤ a) c' +
      badCount N (fun a => Unsieved 18 r a ∧ c' ≤ a) c +
      starCount N b r ≤ c7 N) ∨
    (classCount N (Unsieved 7 r) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a) b +
      badCount N (Unsieved 18 r) c +
      starCount N b r ≤ c7 N)

/-! ### Tools -/

variable {N : ℕ} {A : Finset ℕ}

/-- Splitting a filter into three. -/
lemma card_le_three (B : Finset ℕ) (P Q R : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (h : ∀ a ∈ B, P a ∨ Q a ∨ R a) :
    B.card ≤ (B.filter P).card + (B.filter Q).card + (B.filter R).card := by
  have h1 := card_le_two (A := B) P (fun a => Q a ∨ R a) h
  have h2 := card_le_two (A := B.filter (fun a => Q a ∨ R a)) Q R (fun a ha => (mem_filter.mp ha).2)
  rw [filter_filter, filter_filter] at h2
  have s1 : (B.filter (fun a => (Q a ∨ R a) ∧ Q a)).card ≤ (B.filter Q).card :=
    card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
  have s2 : (B.filter (fun a => (Q a ∨ R a) ∧ R a)).card ≤ (B.filter R).card :=
    card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
  omega

lemma filter_le_star (hA : Admissible A) (hsub : A ⊆ Icc 1 N) {b : ℕ} (hb : b ∈ A) (e : ℕ)
    (hmin : ∀ x ∈ A, IsStar x → x % 4 = e → b ≤ x) :
    (A.filter (fun x => IsStar x ∧ x % 4 = e)).card ≤ starCount N b e := by
  apply card_le_card; intro x hx
  rw [mem_filter] at hx
  exact mem_filter.mpr ⟨hsub hx.1, hmin x hx.1 hx.2.1 hx.2.2, hx.2.2, hx.2.1,
    hA x hx.1 x hx.1, hA x hx.1 b hb⟩

/-- Monotonicity of `badCount` in the predicate. -/
lemma badCount_mono (N b : ℕ) {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P a → Q a) : badCount N P b ≤ badCount N Q b := by
  unfold badCount; apply card_le_card; intro a ha
  simp only [mem_filter] at ha ⊢; exact ⟨ha.1, h a ha.2.1, ha.2.2⟩

/-- A filter of `A` whose elements are all `≥ b` (and in `A`) is bounded by a `badCount` with the
interval condition built in. -/
lemma filter_le_bad_ge (hA : Admissible A) (hsub : A ⊆ Icc 1 N) {b w : ℕ} (hw : w ∈ A)
    (P : ℕ → Prop) [DecidablePred P] (hge : ∀ a ∈ A, P a → b ≤ a) :
    (A.filter P).card ≤ badCount N (fun a => P a ∧ b ≤ a) w := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ⟨ha.2, hge a ha.1 ha.2⟩, hA a ha.1 w hw⟩

/-- The least element of a nonempty filter. -/
lemma exists_min_filter (A : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (h : ∃ a ∈ A, P a) :
    ∃ m ∈ A, P m ∧ ∀ a ∈ A, P a → m ≤ a := by
  have hne : (A.filter P).Nonempty := by
    obtain ⟨a, ha, hp⟩ := h; exact ⟨a, mem_filter.mpr ⟨ha, hp⟩⟩
  refine ⟨(A.filter P).min' hne, (mem_filter.mp (min'_mem _ hne)).1,
    (mem_filter.mp (min'_mem _ hne)).2, fun a ha hp => min'_le _ _ (mem_filter.mpr ⟨ha, hp⟩)⟩

/-! ### The case analysis of §10.6 -/

/-- The covering of `A₇ ∪ A₁₈` in case III.2 α with three witnesses. -/
lemma alpha3_cover {A : Finset ℕ} {r c c' : ℕ} (hr13 : r = 1 ∨ r = 3)
    (hcmin : ∀ a ∈ A, a % 25 = 7 ∧ ¬ a % 4 = r → c ≤ a)
    (hcmin' : ∀ a ∈ A, a % 25 = 18 ∧ ¬ a % 4 = r → c' ≤ a) :
    ∀ a ∈ A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18),
      (((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
        (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a)) ∨
      Unsieved 7 r a ∨ Unsieved 18 r a := by
  intro a ha
  obtain ⟨haA, h78⟩ := mem_filter.mp ha
  have hm4 := Nat.mod_lt a (show 0 < 4 by norm_num)
  have h24 : a % 2 = a % 4 % 2 := (Nat.mod_mod_of_dvd a (by norm_num : 2 ∣ 4)).symm
  by_cases har : a % 4 = r
  · exact Or.inl (Or.inl ⟨h78, har⟩)
  · rcases h78 with h7 | h18
    · by_cases he : a % 2 = 0
      · exact Or.inl (Or.inr (Or.inl ⟨h7, he, hcmin a haA ⟨h7, har⟩⟩))
      · refine Or.inr (Or.inl ⟨h7, ?_⟩)
        rcases hr13 with rfl | rfl <;> omega
    · by_cases he : a % 2 = 0
      · exact Or.inl (Or.inr (Or.inr ⟨h18, he, hcmin' a haA ⟨h18, har⟩⟩))
      · refine Or.inr (Or.inr ⟨h18, ?_⟩)
        rcases hr13 with rfl | rfl <;> omega

/-- Case III.2, given `b = min A*` and `A* ⊆ r + 4ℤ`. -/
lemma caseIII2_bound (h : CountBounds2 N) (hsub : A ⊆ Icc 1 N) (hA : Admissible A)
    {b r : ℕ} (hb : b ∈ A) (hbs : IsStar b) (hbr : b % 4 = r) (hr13 : r = 1 ∨ r = 3)
    (hS : (A.filter IsStar).card ≤ starCount N b r) :
    (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card + (A.filter IsStar).card ≤ c7 N := by
  classical
  have hsubF : ∀ (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q], (∀ a, P a → Q a) →
      (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter P ⊆ A.filter Q := by
    intro P Q _ _ hPQ a ha
    simp only [mem_filter] at ha ⊢; exact ⟨ha.1.1, hPQ a ha.2⟩
  have hwb := witness_of_mem hA hsub hb
  by_cases hF18 : ∃ c' ∈ A, c' % 25 = 18 ∧ ¬ c' % 4 = r
  · by_cases hF7 : ∃ c ∈ A, c % 25 = 7 ∧ ¬ c % 4 = r
    · -- α
      obtain ⟨c, hc, ⟨hc7, hcr⟩, hcmin⟩ := exists_min_filter A (fun a => a % 25 = 7 ∧ ¬ a % 4 = r) hF7
      obtain ⟨c', hc', ⟨hc18, hcr'⟩, hcmin'⟩ :=
        exists_min_filter A (fun a => a % 25 = 18 ∧ ¬ a % 4 = r) hF18
      rcases h.caseIII2alpha b r c c' hwb hbs hbr hr13 (witness_of_mem hA hsub hc) hc7 hcr
          (witness_of_mem hA hsub hc') hc18 hcr' with h3 | h2
      · have c3 := card_le_three (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
          (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
            (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a))
          (Unsieved 7 r) (Unsieved 18 r) (alpha3_cover hr13 hcmin hcmin')
        have e1 := (card_le_card (hsubF _ _ (fun _ h => h))).trans (filter_le_bad hA hsub hb
          (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
            (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a)))
        have e2 := (card_le_card (hsubF (Unsieved 7 r) (Unsieved 7 r) (fun _ h => h))).trans
          (filter_le_bad_ge hA hsub hc' (Unsieved 7 r) (fun a ha hu => hcmin a ha ⟨hu.1, by
            unfold Unsieved at hu; rcases hr13 with rfl | rfl <;> omega⟩))
        have e3 := (card_le_card (hsubF (Unsieved 18 r) (Unsieved 18 r) (fun _ h => h))).trans
          (filter_le_bad_ge hA hsub hc (Unsieved 18 r) (fun a ha hu => hcmin' a ha ⟨hu.1, by
            unfold Unsieved at hu; rcases hr13 with rfl | rfl <;> omega⟩))
        omega
      · have c3 := card_le_three (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)) (Unsieved 7 r)
          (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a)
          (Unsieved 18 r) (fun a ha => by
            have h78 := (mem_filter.mp ha).2
            by_cases h7 : Unsieved 7 r a
            · exact Or.inl h7
            · by_cases h18 : Unsieved 18 r a
              · exact Or.inr (Or.inr h18)
              · exact Or.inr (Or.inl ⟨h78, h7, h18⟩))
        have e1 := (card_le_card (hsubF (Unsieved 7 r) (Unsieved 7 r) (fun _ h => h))).trans
          (filter_le_class hsub (Unsieved 7 r))
        have e2 := (card_le_card (hsubF _ _ (fun _ h => h))).trans (filter_le_bad hA hsub hb
          (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a))
        have e3 := (card_le_card (hsubF (Unsieved 18 r) (Unsieved 18 r) (fun _ h => h))).trans
          (filter_le_bad hA hsub hc (Unsieved 18 r))
        omega
    · -- β with F₇ = ∅
      push Not at hF7
      have c2 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (Unsieved 18 r) (fun a => (a % 25 = 18 ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = 7 ∧ a % 4 = r))
        (fun a ha => by
          obtain ⟨haA, h78⟩ := mem_filter.mp ha
          rcases h78 with h7 | h18
          · exact Or.inr (Or.inr ⟨h7, hF7 a haA h7⟩)
          · by_cases hu : a % 4 = 4 - r
            · exact Or.inl ⟨h18, hu⟩
            · exact Or.inr (Or.inl ⟨h18, hu⟩))
      have e1 := (card_le_card (hsubF (Unsieved 18 r) (Unsieved 18 r) (fun _ h => h))).trans
        (filter_le_class hsub (Unsieved 18 r))
      have e2 := (card_le_card (hsubF _ _ (fun _ h => h))).trans (filter_le_bad hA hsub hb
        (fun a => (a % 25 = 18 ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = 7 ∧ a % 4 = r)))
      have := h.caseIII2beta b r 18 7 hwb hbs hbr hr13 (Or.inr ⟨rfl, rfl⟩)
      omega
  · -- β with F₁₈ = ∅
    push Not at hF18
    have c2 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
      (Unsieved 7 r) (fun a => (a % 25 = 7 ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = 18 ∧ a % 4 = r))
      (fun a ha => by
        obtain ⟨haA, h78⟩ := mem_filter.mp ha
        rcases h78 with h7 | h18
        · by_cases hu : a % 4 = 4 - r
          · exact Or.inl ⟨h7, hu⟩
          · exact Or.inr (Or.inl ⟨h7, hu⟩)
        · exact Or.inr (Or.inr ⟨h18, hF18 a haA h18⟩))
    have e1 := (card_le_card (hsubF (Unsieved 7 r) (Unsieved 7 r) (fun _ h => h))).trans
      (filter_le_class hsub (Unsieved 7 r))
    have e2 := (card_le_card (hsubF _ _ (fun _ h => h))).trans (filter_le_bad hA hsub hb
      (fun a => (a % 25 = 7 ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = 18 ∧ a % 4 = r)))
    have := h.caseIII2beta b r 7 18 hwb hbs hbr hr13 (Or.inl ⟨rfl, rfl⟩)
    omega

theorem statement_of_bounds2 (h : CountBounds2 N) : Statement N := by
  classical
  intro A hsub hA
  have hsplit : A.card ≤ (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card +
      (A.filter IsStar).card :=
    card_le_two _ _ (fun a _ => by unfold IsStar; omega)
  have hsubF : ∀ (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q], (∀ a, P a → Q a) →
      (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter P ⊆ A.filter Q := by
    intro P Q _ _ hPQ a ha
    simp only [mem_filter] at ha ⊢; exact ⟨ha.1.1, hPQ a ha.2⟩
  by_cases hII : ∃ b ∈ A, IsStar b ∧ b % 2 = 0
  · -- Case II: b the least even element of A*
    obtain ⟨b, hb, ⟨hbs, hbe⟩, hbmin⟩ := exists_min_filter A (fun x => IsStar x ∧ x % 2 = 0) hII
    have h1 := filter_le_bad hA hsub hb (fun a => a % 25 = 7 ∨ a % 25 = 18)
    have h2 : (A.filter IsStar).card ≤ lemCCount2 N b := by
      apply card_le_card; intro x hx
      rw [mem_filter] at hx
      refine mem_filter.mpr ⟨hsub hx.1, ?_, hx.2, hA x hx.1 x hx.1, hA x hx.1 b hb⟩
      rcases Nat.mod_two_eq_zero_or_one x with he | ho
      · exact Or.inr (hbmin x hx.1 ⟨hx.2, he⟩)
      · exact Or.inl ho
    have := h.caseII b (witness_of_mem hA hsub hb) hbs hbe
    omega
  push Not at hII
  have hodd : ∀ x ∈ A, IsStar x → x % 2 = 1 := fun x hx hs => by
    have := hII x hx hs; omega
  by_cases hIII1 : (∃ b ∈ A, IsStar b ∧ b % 4 = 1) ∧ (∃ b ∈ A, IsStar b ∧ b % 4 = 3)
  · -- Case III.1
    obtain ⟨b₁, hb₁, ⟨hs₁, hr₁⟩, hmin₁⟩ := exists_min_filter A (fun x => IsStar x ∧ x % 4 = 1) hIII1.1
    obtain ⟨b₃, hb₃, ⟨hs₃, hr₃⟩, hmin₃⟩ := exists_min_filter A (fun x => IsStar x ∧ x % 4 = 3) hIII1.2
    have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ := by
      have := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 4 = 1 ∨ a % 2 = 0) (fun a => a % 4 = 3) (fun a _ => by omega)
      rw [filter_filter, filter_filter] at this
      have e1 := filter_le_bad hA hsub hb₁ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0))
      have e2 := filter_le_bad hA hsub hb₃ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3)
      omega
    have hS : (A.filter IsStar).card ≤ starCount N b₁ 1 + starCount N b₃ 3 := by
      have c := card_le_two (A := A.filter IsStar) (fun x => x % 4 = 1) (fun x => x % 4 = 3)
        (fun x hx => by have := hodd x (mem_filter.mp hx).1 (mem_filter.mp hx).2; omega)
      rw [filter_filter, filter_filter] at c
      have e1 := filter_le_star hA hsub hb₁ 1 (fun x hx hs he => hmin₁ x hx ⟨hs, he⟩)
      have e3 := filter_le_star hA hsub hb₃ 3 (fun x hx hs he => hmin₃ x hx ⟨hs, he⟩)
      omega
    have := h.caseIII1 b₁ b₃ (witness_of_mem hA hsub hb₁) hs₁ hr₁ (witness_of_mem hA hsub hb₃) hs₃ hr₃
    omega
  by_cases hStar : ∃ b ∈ A, IsStar b
  · -- Case III.2: A* lies in one class r mod 4; b = min A*
    obtain ⟨b, hb, hbs, hbmin⟩ := exists_min_filter A IsStar hStar
    obtain ⟨r, hbr⟩ : ∃ r, b % 4 = r := ⟨_, rfl⟩
    have hr13 : r = 1 ∨ r = 3 := by have := hodd b hb hbs; omega
    have hAllr : ∀ x ∈ A, IsStar x → x % 4 = r := by
      intro x hx hxs
      have hxo := hodd x hx hxs
      by_contra hne
      apply hIII1
      rcases hr13 with h1 | h3
      · exact ⟨⟨b, hb, hbs, by omega⟩, ⟨x, hx, hxs, by omega⟩⟩
      · exact ⟨⟨x, hx, hxs, by omega⟩, ⟨b, hb, hbs, by omega⟩⟩
    have hS : (A.filter IsStar).card ≤ starCount N b r := by
      have : A.filter IsStar = A.filter (fun x => IsStar x ∧ x % 4 = r) := by
        apply filter_congr; intro x hx
        exact ⟨fun hs => ⟨hs, hAllr x hx hs⟩, fun h => h.1⟩
      rw [this]
      exact filter_le_star hA hsub hb r (fun x hx hs _ => hbmin x hx hs)
    have := caseIII2_bound h hsub hA hb hbs hbr hr13 hS
    omega
  · -- Case I: A* = ∅
    push Not at hStar
    have hS0 : (A.filter IsStar).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => hStar x hx
    have h78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        (A.filter (fun a => a % 25 = 7)).card + (A.filter (fun a => a % 25 = 18)).card := by
      have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
      have s1 := card_le_card (hsubF (fun a => a % 25 = 7) (fun a => a % 25 = 7) (fun _ h => h))
      have s2 := card_le_card (hsubF (fun a => a % 25 = 18) (fun a => a % 25 = 18) (fun _ h => h))
      omega
    by_cases h7 : ∃ b ∈ A, b % 25 = 7
    · by_cases h18 : ∃ b' ∈ A, b' % 25 = 18
      · -- I.b with minimal witnesses
        obtain ⟨b, hb, hb7, hbmin⟩ := exists_min_filter A (fun a => a % 25 = 7) h7
        obtain ⟨b', hb', hb18, hbmin'⟩ := exists_min_filter A (fun a => a % 25 = 18) h18
        have e1 := filter_le_bad_ge hA hsub hb (fun a => a % 25 = 18) hbmin'
        have e2 := filter_le_bad_ge hA hsub hb' (fun a => a % 25 = 7) hbmin
        have := h.caseIb b b' (witness_of_mem hA hsub hb) hb7 (witness_of_mem hA hsub hb') hb18
        omega
      · push Not at h18
        have h0 : (A.filter (fun a => a % 25 = 18)).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h18 x hx
        have e := filter_le_class hsub (fun a => a % 25 = 7)
        rw [class7_eq_c7] at e
        omega
    · push Not at h7
      have h0 : (A.filter (fun a => a % 25 = 7)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h7 x hx
      have e := filter_le_class hsub (fun a => a % 25 = 18)
      have := class18_le_c7 (N := N)
      omega

end Erdos848
