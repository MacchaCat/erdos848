import Erdos848.SmallN
import Erdos848.Skeleton

/-!
# Erdős #848 — assembly of the proof

The proof has two large parts, stated here as propositions:

* `ComputationalPart`: `Statement N` for all `N ≤ 4·10⁸`.  In Lean the range `N ≤ 1.6·10⁸` is proved
  in `CompSound.lean`/`Final.lean` (guarded colouring, `computational`); the C++ programs
  `incr.cpp`/`replay.cpp` independently cover `N ≤ 4·10⁸`.
* `AnalyticPart`: `Statement N` for all `N ≥ 1.6·10⁸`, proved in `Analytic.lean` (`analyticPart`).

This file contains the lower bound, the reduction from colourings, the combination of the two
parts, and the equivalence with the `formal-conjectures` statement.  The unconditional theorem is
`Erdos848.erdos848` in `Final.lean`.
-/

namespace Erdos848

/-- Computer verification range (the C++ programs; Lean proves `N ≤ 1.6·10⁸`, see `Final.lean`). -/
def ComputationalPart : Prop := ∀ N, N ≤ 400000000 → Statement N

/-- Explicit analytic range (proved in `Analytic.lean`). -/
def AnalyticPart : Prop := ∀ N, 160000000 ≤ N → Statement N

/-- The purely number-theoretic counting inequalities: for every `N ≥ 1.6·10⁸`, the counts of
`Skeleton.lean` satisfy `CountBounds N` (proved in `Analytic.lean`). -/
def AnalyticCounting : Prop := ∀ N, 160000000 ≤ N → CountBounds N

/-- The combinatorial skeleton is fully formalised: the counting inequalities imply the
analytic part. -/
theorem analyticPart_of_counting (h : AnalyticCounting) : AnalyticPart :=
  fun N hN => statement_of_bounds (h N hN)

/-- Final form with the analytic hypothesis reduced to counting inequalities. -/
theorem erdos848_of_counting (hC : ComputationalPart) (h : AnalyticCounting) :
    ∀ N, Statement N := by
  intro N
  by_cases hN : N ≤ 400000000
  · exact hC N hN
  · exact analyticPart_of_counting h N (by omega)

/-- The two parts overlap on `[1.6·10⁸, 4·10⁸]`, so together they give every `N`. -/
theorem erdos848_of_parts (hC : ComputationalPart) (hA : AnalyticPart) : ∀ N, Statement N := by
  intro N
  by_cases h : N ≤ 400000000
  · exact hC N h
  · exact hA N (by omega)

/-- Final form: the maximum size of an admissible `A ⊆ [1,N]` is exactly `c7 N`. -/
theorem erdos848_max (hC : ComputationalPart) (hA : AnalyticPart) (N : ℕ) :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Admissible A ∧ A.card = c7 N) ∧
    (∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible A → A.card ≤ c7 N) :=
  ⟨lower_bound N, erdos848_of_parts hC hA N⟩

/-! ### Equivalence with the `formal-conjectures` formulation

There the sets live in `Finset.range N = {0, …, N-1}` and the bound is
`#{n < N : n ≡ 7 (mod 25)}`.  Since `0·0+1 = 1` is squarefree, `0` never lies in an admissible set. -/

lemma zero_not_mem {A : Finset ℕ} (hA : Admissible A) : 0 ∉ A := by
  intro h0
  exact hA 0 h0 0 h0 (by simp)

lemma range_filter_eq (N : ℕ) :
    (Finset.range N).filter (fun n => n % 25 = 7) = C7set (N - 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, C7set, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨⟨?_, ?_⟩, h2⟩ <;> omega
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩

/-- `Statement` for all `N` implies the `formal-conjectures` form of Erdős #848. -/
theorem formalConjectures_form (h : ∀ N, Statement N) (N : ℕ) (A : Finset ℕ)
    (hsub : A ⊆ Finset.range N) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)) :
    A.card ≤ ((Finset.range N).filter (fun n => n % 25 = 7)).card := by
  rw [range_filter_eq, C7set_card]
  apply h (N - 1) A _ hA
  intro x hx
  have hx0 : x ≠ 0 := fun e => zero_not_mem hA (e ▸ hx)
  have := hsub hx
  simp only [Finset.mem_range] at this
  simp only [Finset.mem_Icc]
  omega

end Erdos848
