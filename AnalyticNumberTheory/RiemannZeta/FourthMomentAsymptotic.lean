import AnalyticNumberTheory.RiemannZeta.FourthMomentDyadicAsymptotic
import AnalyticNumberTheory.DivisorProblems.DivisorSquareAsymptotic
import AnalyticNumberTheory.AnalyticTools.DyadicAsymptotics

/-!
# Ingham's leading asymptotic for the fourth zeta moment

The two divisor polynomials each contribute `T (log T)^4/(4π²)` on a dyadic interval.
Passing to the full interval gives the leading coefficient `1/(2π²)`.
-/

open Complex Real Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DivisorProblems

namespace AnalyticNumberTheory.RiemannZeta

/-- The normalized fourth moment on the dyadic interval tends to `1/(2π²)`. -/
theorem fourthMoment_riemannZeta_dyadic_tendsto :
    Tendsto (fun T : ℝ => (∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) /
      (T*(Real.log T)^4)) atTop (𝓝 (1/(2*π^2))) := by
  have H := fourthMoment_dyadic_tendsto_of_diagonal (κ := 1/(4*π^2)) (by positivity) tendsto_divisor_square_harmonic
  convert H using 2
  ring

/-- Ingham's leading coefficient for the fourth moment on `[1,T]`. -/
theorem fourthMoment_riemannZeta_tendsto :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) /
      (T*(Real.log T)^4)) atTop (𝓝 (1/(2*π^2))) :=
  integral_from_one_of_dyadic_asymptotic (f := fun t : ℝ => ‖riemannZeta ((1/2:ℂ)+t*I)‖^4)
    (continuous_riemannZeta_half.norm.pow 4) 4 fourthMoment_riemannZeta_dyadic_tendsto

/-- Ingham's fourth-moment asymptotic for the Riemann zeta function on the critical line. -/
theorem fourthMoment_riemannZeta_equivalent :
    Asymptotics.IsEquivalent atTop (fun T : ℝ => ∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4)
      (fun T : ℝ => T*(Real.log T)^4/(2*π^2)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := fourthMoment_riemannZeta_tendsto.mul_const (2*π^2)
  rw [one_div_mul_cancel (show 2*π^2 ≠ 0 by positivity)] at h
  exact h.congr (fun T => by simp only [Pi.div_apply,div_eq_mul_inv,mul_inv_rev,inv_inv]; ring)

end AnalyticNumberTheory.RiemannZeta
