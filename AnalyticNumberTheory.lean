import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# AnalyticNumberTheory

A thematic library for analytic number theory in Lean 4 and Mathlib `v4.36.0`.
-/

namespace AnalyticNumberTheory

/-- Placeholder smoke-test alias for Riemann's zeta function $\zeta(s)$ from Mathlib. -/
noncomputable def zetaFn (s : ℂ) : ℂ := riemannZeta s

end AnalyticNumberTheory
