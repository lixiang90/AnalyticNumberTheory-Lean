import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-! # A real-axis majorant for a Dirichlet series with nonnegative coefficients -/

open Complex
open scoped ComplexOrder

namespace AnalyticNumberTheory.DirichletSeries

/-- In a closed half-plane of absolute convergence, a Dirichlet series with
nonnegative real coefficients is bounded in norm by its value at the real boundary point. -/
theorem norm_LSeries_le_re_of_nonnegative {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    {σ : ℝ} (hsum : LSeriesSummable a (σ : ℂ)) {s : ℂ} (hs : σ ≤ s.re) :
    ‖LSeries a s‖ ≤ (LSeries a (σ : ℂ)).re := by
  apply (norm_LSeries_le_tsum_norm_of_re_ge hsum hs).trans_eq
  rw [LSeries, Complex.re_tsum hsum]
  apply tsum_congr
  intro n
  exact (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg (ha n) σ))).symm

end AnalyticNumberTheory.DirichletSeries
