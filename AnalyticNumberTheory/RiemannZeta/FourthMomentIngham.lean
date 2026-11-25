import AnalyticNumberTheory.RiemannZeta.FourthMomentCrossTerm
import AnalyticNumberTheory.RiemannZeta.FourthMomentSharpRemainder

/-!
# Ingham's fourth-moment formula with a cubic logarithmic remainder

The reflected analytic cross integral contributes at most cubic logarithmic
order. The two arithmetic diagonals give the common leading coefficient on
a dyadic interval and on the full interval from zero.
-/

open Real Complex MeasureTheory Filter
open scoped Interval
namespace AnalyticNumberTheory.RiemannZeta

/-- The dyadic fourth zeta moment, including its cubic logarithmic remainder. -/
theorem fourthMoment_riemannZeta_dyadic_sharp :
    ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
      |(∫t in T..2*T,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)-
        (1/(2*π^2))*T*(Real.log T)^4|≤C*T*(1+Real.log T)^3 :=
  fourthMoment_dyadic_sharp_of_crossTerm fourthMomentCrossTerm_integral_bound

/-- Ingham's fourth-moment estimate on the critical line, uniform for T ≥ 2. -/
theorem fourthMoment_riemannZeta_sharp_remainder :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ}, 2≤T →
      |(∫t in (0:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)-
        T*(Real.log T)^4/(2*π^2)|≤C*T*(Real.log T)^3 := by
  obtain ⟨C,hC,H⟩ := fourthMoment_sharp_of_crossTerm fourthMomentCrossTerm_integral_bound
  refine ⟨C,hC,fun {T} hT => ?_⟩
  rw [show T*(Real.log T)^4/(2*π^2)=(1/(2*π^2))*T*(Real.log T)^4 by ring]
  exact H hT

end AnalyticNumberTheory.RiemannZeta
