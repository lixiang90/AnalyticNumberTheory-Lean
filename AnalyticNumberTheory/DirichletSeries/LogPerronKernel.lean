import AnalyticNumberTheory.AnalyticTools.GammaLaplace
import AnalyticNumberTheory.AnalyticTools.LaplaceInversion
import AnalyticNumberTheory.DirichletSeries.Perron

/-! # The logarithmically smoothed Perron kernel -/

noncomputable section

open Complex MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletSeries

/-- The inverse Laplace integrand for the positive part of a real argument.
Its squared denominator makes the vertical integral absolutely convergent. -/
def logPerronKernel (σ u t : ℝ) : ℂ :=
  Complex.exp (((σ : ℂ)+t*I)*u) / (((σ : ℂ)+t*I)^2)

private lemma norm_sq_line (σ t : ℝ) : ‖(σ : ℂ)+t*I‖^2 = σ^2+t^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

/-- The modulus of the smoothed kernel is a constant times a Cauchy density in height. -/
theorem norm_logPerronKernel (σ u t : ℝ) :
    ‖logPerronKernel σ u t‖ = Real.exp (σ*u) * (σ^2+t^2)⁻¹ := by
  rw [logPerronKernel, norm_div, norm_exp, norm_pow, norm_sq_line, div_eq_mul_inv]
  simp [Complex.mul_re]

theorem continuous_logPerronKernel {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    Continuous (logPerronKernel σ u) := by
  have hn (t : ℝ) : (σ : ℂ)+t*I ≠ 0 := fun h => hσ.ne' (by simpa using congrArg Complex.re h)
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*u))).div
    (by fun_prop) (fun t => pow_ne_zero 2 (hn t))

theorem integrable_logPerronKernel {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    Integrable (logPerronKernel σ u) := by
  apply ((integrable_inv_sq_add hσ).const_mul (Real.exp (σ*u))).mono'
  · exact (continuous_logPerronKernel hσ u).aestronglyMeasurable
  · exact ae_of_all _ fun t => (norm_logPerronKernel σ u t).le

private lemma laplace_id {z : ℂ} (hz : 0 < z.re) :
    laplaceTransform (fun u : ℝ => (u : ℂ)) z = (z^2)⁻¹ := by
  have H := integral_gammaLaplaceKernel_rightHalfPlane (s := 2) (by norm_num) hz
  have hΓ : Complex.Gamma 2 = 1 := by simp
  simpa only [laplaceTransform, show (2 : ℂ)-1 = 1 by norm_num, Complex.cpow_one,
    Complex.cpow_neg, Complex.cpow_ofNat, hΓ, mul_one] using H

/-- Absolute vertical inversion of the squared Perron denominator. At zero
the weight vanishes, so the same formula holds at a cutoff lying on an exponent. -/
theorem integral_logPerronKernel {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    (∫ t : ℝ, logPerronKernel σ u t)/(2*Real.pi) = ((max u 0 : ℝ) : ℂ) := by
  have hf : IntegrableOn (fun v : ℝ => Complex.exp (-(σ : ℂ)*v)*(v : ℂ)) (Ioi 0) := by
    have h := integrable_gammaLaplaceKernel (s := 2) (z := (σ : ℂ)) (by norm_num) hσ
    change IntegrableOn (fun v : ℝ => Complex.exp (-(σ : ℂ)*v)*(v : ℂ)^((2 : ℂ)-1)) _ at h
    simpa only [show (2 : ℂ)-1 = 1 by norm_num, Complex.cpow_one] using h
  have hline (t : ℝ) : laplaceTransform (fun v : ℝ => (v : ℂ)) ((σ : ℂ)+t*I) =
      (((σ : ℂ)+t*I)^2)⁻¹ := laplace_id (by simpa using hσ)
  have hF : Integrable (fun t : ℝ => laplaceTransform (fun v : ℝ => (v : ℂ)) ((σ : ℂ)+t*I)) := by
    have h := integrable_logPerronKernel hσ 0
    change Integrable (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*(0 : ℝ))/(((σ : ℂ)+t*I)^2)) at h
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div, hline] using h
  have hd (v : ℝ) : laplaceDamped σ (fun y : ℝ => (y : ℂ)) v =
      Complex.exp (-(σ : ℂ)*v) * ((max v 0 : ℝ) : ℂ) := by
    by_cases hv : 0 < v
    · simp [laplaceDamped, hv, max_eq_left hv.le]
    · simp [laplaceDamped, hv, max_eq_right (le_of_not_gt hv)]
  have hc : Continuous (laplaceDamped σ (fun v : ℝ => (v : ℂ))) := by
    rw [funext hd]
    fun_prop
  have H := bromwichIntegral_eq_damped hf hF (hc.continuousAt (x := u))
  rw [hd, ← mul_assoc, ← Complex.exp_add, show (σ : ℂ)*u+ -(σ : ℂ)*u = 0 by ring, Complex.exp_zero,
    one_mul] at H
  simpa only [bromwichIntegral, hline, logPerronKernel, div_eq_mul_inv] using H

end AnalyticNumberTheory.DirichletSeries
