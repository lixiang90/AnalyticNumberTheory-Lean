import AnalyticNumberTheory.RiemannZeta.HadamardProduct
import AnalyticNumberTheory.DirichletSeries.PositiveMajorant

/-! # Uniform bounds for the logarithm defined by the Euler product -/

noncomputable section

open Complex
open scoped ComplexOrder

namespace AnalyticNumberTheory.RiemannZeta

/-- The coefficients of the Euler logarithm are nonnegative real numbers. -/
theorem logZetaCoeff_nonneg (n : ℕ) : 0 ≤ logZetaCoeff n := by
  rw [logZetaCoeff, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), one_mul,
    ← Complex.ofReal_div, Complex.zero_le_real]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- Absolute convergence of the logarithmic Dirichlet series to the right of one. -/
theorem lSeriesSummable_logZetaCoeff {s : ℂ} (hs : 1 < s.re) : LSeriesSummable logZetaCoeff s := by
  apply Summable.of_norm
  apply (LSeriesSummable_one_iff.mpr hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  exact LSeries.norm_term_le s (by simpa using norm_logZetaCoeff_le_one n)

/-- On Re s ≥ a > 1 the sharp uniform majorant is the real Euler logarithm at a. -/
theorem norm_logZeta_le_log_norm_riemannZeta {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖logZeta s‖ ≤ Real.log ‖riemannZeta (a : ℂ)‖ := by
  have ha' : 1 < (a : ℂ).re := ha
  have hsum := lSeriesSummable_logZetaCoeff ha'
  rw [logZeta_eq_LSeries (ha.trans_le hs), ← logZeta_re_eq_log_norm ha',
    logZeta_eq_LSeries ha']
  exact AnalyticNumberTheory.DirichletSeries.norm_LSeries_le_re_of_nonnegative logZetaCoeff_nonneg hsum hs

end AnalyticNumberTheory.RiemannZeta
