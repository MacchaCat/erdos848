import Erdos848.Main
import Erdos848.KAnalytic

/-!
# The analytic part, fully formalised

`analyticCounting : AnalyticCounting` combines the interval checker on `[1.6·10⁸, 10⁶⁰]`
(`countBounds_mid`) with the tail `N ≥ 10⁶⁰` (`countBounds_tail`).  Hence the only remaining
hypothesis of the main theorem is `ComputationalPart`.
-/

namespace Erdos848

theorem analyticCounting : AnalyticCounting := by
  intro N hN
  by_cases h : N ≤ 10 ^ 60
  · exact countBounds_mid N hN h
  · exact countBounds_tail N (by omega)

theorem analyticPart : AnalyticPart := analyticPart_of_counting analyticCounting

/-- Erdős #848, conditional only on the finite computation for `N ≤ 4·10⁸`. -/
theorem erdos848_of_computational (hC : ComputationalPart) : ∀ N, Statement N :=
  erdos848_of_parts hC analyticPart

end Erdos848
