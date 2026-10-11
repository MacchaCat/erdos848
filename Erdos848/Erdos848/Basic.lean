import Mathlib

/-!
# Erdős Problem #848 — basic definitions and elementary facts

Problem (Erdős–Sárközy): if `A ⊆ {1,…,N}` and `a*b+1` is never squarefree for `a, b ∈ A`
(`a = b` allowed), is `|A|` at most the number of `n ≤ N` with `n ≡ 7 (mod 25)`?
-/

namespace Erdos848

/-- `A` is *admissible*: `a*b+1` is not squarefree for all `a, b ∈ A` (including `a = b`). -/
def Admissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

/-- `c7 N = #{n ∈ [1,N] : n ≡ 7 (mod 25)}` in closed form (see `c7_eq_card`). -/
def c7 (N : ℕ) : ℕ := (N + 18) / 25

/-- The extremal example `{n ∈ [1,N] : n ≡ 7 (mod 25)}`. -/
def C7set (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => n % 25 = 7)

/-- The statement of Erdős #848 for a given `N`. -/
def Statement (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible A → A.card ≤ c7 N

lemma not_squarefree_of_mul_self_dvd {n p : ℕ} (hp : 2 ≤ p) (h : p * p ∣ n) :
    ¬ Squarefree n := by
  intro hs
  have hu := hs p h
  rw [Nat.isUnit_iff] at hu
  omega

lemma C7set_card (N : ℕ) : (C7set N).card = c7 N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    unfold C7set at ih ⊢
    rw [hIcc, Finset.filter_insert]
    unfold c7 at ih ⊢
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

/-- The class `7 mod 25` is admissible: `25 ∣ a*b+1`. -/
theorem C7set_admissible (N : ℕ) : Admissible (C7set N) := by
  intro a ha b hb
  simp only [C7set, Finset.mem_filter] at ha hb
  apply not_squarefree_of_mul_self_dvd (p := 5) (by norm_num)
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mul_mod, ha.2, hb.2]

/-- Lower bound: the answer is at least `c7 N`. -/
theorem lower_bound (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Admissible A ∧ A.card = c7 N :=
  ⟨C7set N, Finset.filter_subset _ _, C7set_admissible N, C7set_card N⟩

/-- A proper colouring with `k` colours of the "compatibility graph" bounds admissible sets. -/
theorem card_le_of_coloring {A : Finset ℕ} {k : ℕ} (f : ℕ → ℕ) (hA : Admissible A)
    (hf : ∀ a ∈ A, f a < k)
    (hcol : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → f a = f b → Squarefree (a * b + 1)) :
    A.card ≤ k := by
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    by_contra hne
    exact hA a ha b hb (hcol a ha b hb hne hab)
  calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simpa using hf a ha
    _ = k := Finset.card_range k

/-! ### Elementary congruence facts (F1–F4 of the written proof) -/

lemma mod_mul_add_one (a b m : ℕ) : (a * b + 1) % m = ((a % m) * (b % m) + 1) % m := by
  rw [Nat.add_mod, Nat.mul_mod]; conv_rhs => rw [Nat.add_mod]

/-- (F1) `25 ∣ x² + 1 ↔ x ≡ ±7 (mod 25)`. -/
lemma F1 (x : ℕ) : 25 ∣ x * x + 1 ↔ x % 25 = 7 ∨ x % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  have h := Nat.mod_lt x (by norm_num : 25 > 0)
  interval_cases (x % 25) <;> simp

/-- (F2, first half) if `a ≡ 7` then `25 ∣ ab+1 ↔ b ≡ 7 (mod 25)`. -/
lemma F2_seven (a b : ℕ) (ha : a % 25 = 7) : 25 ∣ a * b + 1 ↔ b % 25 = 7 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one, ha]
  have h := Nat.mod_lt b (by norm_num : 25 > 0)
  interval_cases (b % 25) <;> simp

/-- (F2, second half) if `a ≡ 18` then `25 ∣ ab+1 ↔ b ≡ 18 (mod 25)`. -/
lemma F2_eighteen (a b : ℕ) (ha : a % 25 = 18) : 25 ∣ a * b + 1 ↔ b % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one, ha]
  have h := Nat.mod_lt b (by norm_num : 25 > 0)
  interval_cases (b % 25) <;> simp

/-- (F3) `a ≡ 7`, `b ≡ 18 (mod 25)` ⟹ `25 ∤ ab+1`. -/
lemma F3 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) : ¬ 25 ∣ a * b + 1 := by
  rw [F2_seven a b ha, hb]; norm_num

/-- (F4) for odd `a, b`: `4 ∣ ab+1 ↔ a ≢ b (mod 4)`. -/
lemma F4 (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) : 4 ∣ a * b + 1 ↔ a % 4 ≠ b % 4 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases ha4 with h1 | h1 <;> rcases hb4 with h2 | h2 <;> simp [h1, h2]

/-- (F4') if `a` or `b` is even then `ab+1` is odd, so `2 ∤ ab+1`. -/
lemma F4_even (a b : ℕ) (h : a % 2 = 0 ∨ b % 2 = 0) : ¬ 2 ∣ a * b + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  rcases h with h | h <;> simp [h]

/-- Every element of an admissible set lies in `V = {n : n² + 1 not squarefree}`. -/
lemma mem_V_of_admissible {A : Finset ℕ} (hA : Admissible A) {a : ℕ} (ha : a ∈ A) :
    ¬ Squarefree (a * a + 1) := hA a ha a ha

end Erdos848
