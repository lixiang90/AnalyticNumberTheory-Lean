import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! # Logarithmic differentiation of the real archimedean gamma factor -/

noncomputable section

namespace AnalyticNumberTheory.AnalyticTools.Gamma

/-- The real archimedean factor has no zero when its half-argument avoids the gamma poles. -/
theorem gammaReal_ne_zero {s : ℂ} (hs : s/2 ∈ nonPoleSet) : Complex.Gammaℝ s ≠ 0 :=
  mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero hs)

/-- The derivative of Γℝ expressed as the factor times its digamma logarithmic derivative. -/
theorem hasDerivAt_gammaReal {s : ℂ} (hs : s/2 ∈ nonPoleSet) :
    HasDerivAt Complex.Gammaℝ (Complex.Gammaℝ s * ((digamma (s/2)-(Real.log Real.pi : ℂ))/2)) s := by
  have hπ := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg := ((Complex.differentiableAt_Gamma _ hs).hasDerivAt).comp s ((hasDerivAt_id s).div_const (2 : ℂ))
  have hpow := (((hasDerivAt_id s).neg.div_const (2 : ℂ)).mul_const (Complex.log (Real.pi : ℂ))).cexp
  have H := hpow.mul hg
  simp only [Pi.neg_apply, id_eq, Function.comp_def] at H
  change HasDerivAt (fun z : ℂ => (Real.pi : ℂ)^(-z/2)*Complex.Gamma (z/2)) _ s
  convert H using 1
  · funext z
    rw [Complex.cpow_def_of_ne_zero hπ, mul_comm (Complex.log (Real.pi : ℂ))]
    rfl
  · rw [Complex.Gammaℝ, Complex.cpow_def_of_ne_zero hπ, Complex.ofReal_log Real.pi_pos.le,
      digamma_def]
    field_simp [Complex.Gamma_ne_zero hs]
    ring

/-- The logarithmic derivative of Γℝ is half the digamma at half the argument minus
half the logarithm of π. -/
theorem logDeriv_gammaReal {s : ℂ} (hs : s/2 ∈ nonPoleSet) :
    logDeriv Complex.Gammaℝ s = (digamma (s/2)-(Real.log Real.pi : ℂ))/2 := by
  rw [logDeriv_apply, (hasDerivAt_gammaReal hs).deriv, mul_div_cancel_left₀ _ (gammaReal_ne_zero hs)]

end AnalyticNumberTheory.AnalyticTools.Gamma
