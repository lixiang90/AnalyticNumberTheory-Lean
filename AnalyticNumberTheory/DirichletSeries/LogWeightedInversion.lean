import AnalyticNumberTheory.DirichletSeries.LogPerronContours
import AnalyticNumberTheory.AnalyticTools.LaplaceInversion

/-! # Identification of logarithmic means by Laplace inversion -/

noncomputable section

open Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletSeries

/-- A continuous function whose exponentially damped transform on a right line
equals F(s)/s² recovers the first logarithmic mean of the coefficients of F. -/
theorem logWeightedSum_eq_of_laplaceTransform {a : ℕ → ℂ} {G : ℝ → ℂ} {σ x : ℝ}
    (hσ : 0 < σ) (ha : LSeriesSummable a (σ:ℂ)) (hx : 1 < x)
    (hc : ContinuousAt G (Real.log x))
    (hi : IntegrableOn (fun u : ℝ => Complex.exp (-(σ:ℂ)*u)*G u) (Ioi 0))
    (H : ∀ t : ℝ, laplaceTransform G ((σ:ℂ)+t*I) = LSeries a ((σ:ℂ)+t*I)/((σ:ℂ)+t*I)^2) :
    logWeightedSum a x = G (Real.log x) := by
  have hx₀ := zero_lt_one.trans hx
  have htrace : Integrable fun t : ℝ => laplaceTransform G ((σ:ℂ)+t*I) := by
    apply (integrable_logPerronTrace_LSeries hσ ha 1).congr
    apply ae_of_all _ fun t => ?_
    dsimp only
    rw [logPerronTrace_eq_cpow _ _ zero_lt_one,H]
    simp
  have h := laplace_inversion (σ := σ) (Real.log_pos hx) hc hi htrace
  rw [←h,logWeightedSum_eq_perron hx₀ hσ ha,bromwichIntegral]
  congr 1
  apply integral_congr_ae
  apply ae_of_all _ fun t => ?_
  dsimp only
  rw [H,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx₀.ne'),
    ←Complex.ofReal_log hx₀.le,mul_comm ((σ:ℂ)+t*I)]
  ring

end AnalyticNumberTheory.DirichletSeries
