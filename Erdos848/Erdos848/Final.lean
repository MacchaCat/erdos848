import Erdos848.Analytic
import Erdos848.AnalyticLow
import Erdos848.KColW.All

/-!
# Erdős #848 — the complete theorem

* `statement_small`: every `N ≤ 986746` — a dynamic colouring, replayed and checked by the kernel
  in 20 windows (`KColW/All.lean`, soundness `ColSound.lean`).
* `statement_low`: every `N ∈ [986747, 1.6·10⁸]` — the analytic argument of `proof.md` §10,
  346 intervals checked by the kernel (`AnalyticLow.lean`, soundness `Check2*.lean`).
* `analyticPart`: every `N ≥ 1.6·10⁸` — `proof.md` §6 (`Analytic.lean`, `KAnalytic.lean`).

Every computation is evaluated by the Lean kernel (`decide +kernel`); there is no
`native_decide`.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos848

/-- **Erdős #848.** For every `N`, an admissible `A ⊆ [1,N]` has at most `c₇(N)` elements. -/
theorem erdos848 : ∀ N, Statement N := by
  intro N
  by_cases h1 : N ≤ 986746
  · exact statement_small N h1
  · by_cases h2 : N ≤ 160000000
    · exact statement_low N (by omega) h2
    · exact analyticPart N (by omega)

/-- The maximum is exactly `c₇(N) = #{n ≤ N : n ≡ 7 (mod 25)}`. -/
theorem erdos848_max' (N : ℕ) :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Admissible A ∧ A.card = c7 N) ∧
    (∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible A → A.card ≤ c7 N) :=
  ⟨lower_bound N, erdos848 N⟩

/-- The `formal-conjectures` formulation. -/
theorem erdos848_formalConjectures (N : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.range N)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)) :
    A.card ≤ ((Finset.range N).filter (fun n => n % 25 = 7)).card :=
  formalConjectures_form erdos848 N A hsub hA

end Erdos848
