import AnalyticNumberTheory.DirichletSeries.LogPerronKernel

/-! # Logarithmic Perron kernels of arbitrary positive integral order -/

noncomputable section

open Complex MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletSeries

/-- The height integrand with denominator `s^(k+1)`, in the logarithmic
cutoff variable `u`. For positive order it is absolutely integrable. -/
def powerLogPerronKernel (k : ℕ) (σ u t : ℝ) : ℂ :=
  Complex.exp (((σ : ℂ)+t*I)*u) / (((σ : ℂ)+t*I)^(k+1))

@[simp] theorem powerLogPerronKernel_one (σ u : ℝ) :
    powerLogPerronKernel 1 σ u = logPerronKernel σ u := rfl

theorem continuous_powerLogPerronKernel (k : ℕ) {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    Continuous (powerLogPerronKernel k σ u) := by
  have hn (t : ℝ) : (σ : ℂ)+t*I ≠ 0 := fun h => hσ.ne' (by simpa using congrArg Complex.re h)
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*u))).div
    (by fun_prop) (fun t => pow_ne_zero _ (hn t))

/-- Every positive order admits absolute vertical integration, also when
the cutoff is an exponent of the series. -/
theorem integrable_powerLogPerronKernel {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    Integrable (powerLogPerronKernel k σ u) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  apply ((integrable_logPerronKernel hσ u).norm.div_const (σ^m)).mono'
    (continuous_powerLogPerronKernel _ hσ u).aestronglyMeasurable
  refine ae_of_all _ fun t => ?_
  let z := (σ : ℂ)+t*I
  have hz : σ ≤ ‖z‖ := by simpa [z, abs_of_pos hσ] using Complex.abs_re_le_norm z
  have he : powerLogPerronKernel (m+1) σ u t = logPerronKernel σ u t / z^m := by
    simp only [powerLogPerronKernel, logPerronKernel, z, div_div, show m+1+1=2+m by omega, pow_add]
  rw [he, norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hσ _) (pow_le_pow_left₀ hσ.le hz _)

private lemma laplace_divided_power (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    laplaceTransform (fun v : ℝ => (v : ℂ)^k / k.factorial) z = (z^(k+1))⁻¹ := by
  have hs : 0 < ((k : ℂ)+1).re := by simp; positivity
  have H := integral_gammaLaplaceKernel_rightHalfPlane (s := (k : ℂ)+1) hs hz
  have hcast : (k : ℂ)+1 = ((k+1 : ℕ) : ℂ) := by simp
  simp only [add_sub_cancel_right, Complex.cpow_natCast, Complex.cpow_neg,
    Complex.Gamma_nat_eq_factorial] at H
  rw [hcast, Complex.cpow_natCast] at H
  unfold laplaceTransform
  simp_rw [← mul_div_assoc]
  rw [integral_div, H]
  have hn : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- Vertical inversion of the repeated Perron denominator. It gives the
divided power of the positive part, including value zero at the cutoff. -/
theorem integral_powerLogPerronKernel {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    (∫ t : ℝ, powerLogPerronKernel k σ u t)/(2*Real.pi) =
      ((max u 0 : ℝ) : ℂ)^k / k.factorial := by
  let f := fun v : ℝ => (v : ℂ)^k / k.factorial
  have hf : IntegrableOn (fun v : ℝ => Complex.exp (-(σ : ℂ)*v)*f v) (Ioi 0) := by
    have H := integrable_gammaLaplaceKernel (s := (k : ℂ)+1) (z := (σ : ℂ)) (by simp; positivity) hσ
    change IntegrableOn (fun v : ℝ => Complex.exp (-(σ : ℂ)*v)*(v : ℂ)^(((k : ℂ)+1)-1)) _ at H
    simp only [add_sub_cancel_right, Complex.cpow_natCast] at H
    change Integrable (fun v : ℝ => Complex.exp (-(σ : ℂ)*v)*((v : ℂ)^k / k.factorial)) (volume.restrict (Ioi 0))
    simpa only [mul_div_assoc] using H.div_const (k.factorial : ℂ)
  have hline (t : ℝ) : laplaceTransform f ((σ : ℂ)+t*I) =
      (((σ : ℂ)+t*I)^(k+1))⁻¹ := laplace_divided_power k (by simpa using hσ)
  have hF : Integrable (fun t : ℝ => laplaceTransform f ((σ : ℂ)+t*I)) := by
    have H := integrable_powerLogPerronKernel hk hσ 0
    change Integrable (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*(0 : ℝ))/(((σ : ℂ)+t*I)^(k+1))) at H
    simpa only [hline, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div] using H
  have hd (v : ℝ) : laplaceDamped σ f v =
      Complex.exp (-(σ : ℂ)*v) * (((max v 0 : ℝ) : ℂ)^k / k.factorial) := by
    by_cases hv : 0 < v
    · simp [laplaceDamped, f, hv, max_eq_left hv.le]
    · simp [laplaceDamped, hv, max_eq_right (le_of_not_gt hv), zero_pow hk.ne']
  have hc : Continuous (laplaceDamped σ f) := by rw [funext hd]; fun_prop
  have H := bromwichIntegral_eq_damped hf hF (hc.continuousAt (x := u))
  rw [hd, ← mul_assoc, ← Complex.exp_add, show (σ : ℂ)*u+ -(σ : ℂ)*u = 0 by ring,
    Complex.exp_zero, one_mul] at H
  simpa only [bromwichIntegral, hline, powerLogPerronKernel, div_eq_mul_inv] using H

end AnalyticNumberTheory.DirichletSeries
