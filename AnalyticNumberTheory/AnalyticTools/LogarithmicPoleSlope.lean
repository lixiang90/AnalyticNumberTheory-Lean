import AnalyticNumberTheory.AnalyticTools.IntegratedPoleTransform
import AnalyticNumberTheory.AnalyticTools.QuadraticPowerApproximation

/-! # Comparing a logarithmic pole slope with the sharp residue -/

noncomputable section

open Complex

namespace AnalyticNumberTheory.AnalyticTools

/-- The slope of an integrated pole over one signed logarithmic step. -/
def logarithmicPoleSlope (ω : ℂ) (u h : ℝ) : ℂ :=
  Complex.exp (ω*u)*(Complex.exp (ω*h)-1)/((h:ℂ)*ω^2)

/-- A logarithmic slope is a finite difference of the integrated pole when both
endpoints belong to its positive half-line. -/
theorem logarithmicPoleSlope_eq_difference (ω : ℂ) {u h : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ u+h) :
    logarithmicPoleSlope ω u h = (integratedPole ω (u+h)-integratedPole ω u)/(h:ℂ) := by
  simp only [logarithmicPoleSlope,integratedPole,max_eq_left hu,max_eq_left hv,Complex.ofReal_add,
    mul_add,Complex.exp_add,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Absolute convergence and termwise differencing for any family with bounded
real parts and square-summable reciprocal norms. -/
theorem hasSum_logarithmicPoleSlope {a : ℕ → ℂ} {b : ℝ} (hb : ∀ n, (a n).re ≤ b)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) {u h : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ u+h) :
    HasSum (fun n => logarithmicPoleSlope (a n) u h)
      (((∑' n, integratedPole (a n) (u+h))-(∑' n, integratedPole (a n) u))/(h:ℂ)) := by
  have H (v : ℝ) := (summable_integratedPole hb hS v).hasSum
  apply (((H (u+h)).sub (H u)).div_const (h:ℂ)).congr_fun
  intro n
  exact logarithmicPoleSlope_eq_difference _ hu hv

/-- Below the inverse step size, replacing a slope by the sharp residue costs
at most exp(Re(ω) u) |h|. This holds for left and right steps. -/
theorem norm_logarithmicPoleSlope_sub_residue_le {ω : ℂ} (hω : ω ≠ 0) (u : ℝ) {h : ℝ}
    (hh : h ≠ 0) (hsmall : ‖ω*(h:ℂ)‖ ≤ 1) :
    ‖logarithmicPoleSlope ω u h - Complex.exp (ω*u)/ω‖ ≤ Real.exp (ω.re*u)*|h| := by
  have hc := Complex.ofReal_ne_zero.mpr hh
  have he : logarithmicPoleSlope ω u h - Complex.exp (ω*u)/ω =
      Complex.exp (ω*u)*(Complex.exp (ω*h)-1-ω*h)/((h:ℂ)*ω^2) := by
    dsimp only [logarithmicPoleSlope]
    field_simp
  rw [he,norm_div,norm_mul,Complex.norm_exp,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have H := Complex.norm_exp_sub_one_sub_id_le hsmall
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow] at H
  rw [div_le_iff₀ (mul_pos (abs_pos.mpr hh) (sq_pos_of_pos (norm_pos_iff.mpr hω)))]
  exact (mul_le_mul_of_nonneg_left H (Real.exp_pos _).le).trans_eq (by ring)

/-- Slopes at nonreal poles have a reciprocal-square bound in the ordinate,
with the signed step appearing only through its absolute value in the denominator. -/
theorem norm_logarithmicPoleSlope_le_height {ω : ℂ} (him : ω.im ≠ 0) (u : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ‖logarithmicPoleSlope ω u h‖ ≤ Real.exp (ω.re*u)*(Real.exp (ω.re*h)+1)/(|h| * ω.im^2) := by
  have he : ‖Complex.exp (ω*h)-1‖ ≤ Real.exp (ω.re*h)+1 := by
    simpa only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
      sub_zero,norm_one] using norm_sub_le (Complex.exp (ω*h)) 1
  simp only [logarithmicPoleSlope,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
    (mul_pos (abs_pos.mpr hh) (sq_pos_of_ne_zero him))
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg ω.im) (Complex.abs_im_le_norm ω) 2

/-- A bound uniform down to step zero compares the slope to the two endpoint
exponentials divided by the norm of the pole. -/
theorem norm_logarithmicPoleSlope_le_endpoints {ω : ℂ} (hω : ω ≠ 0) (u : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ‖logarithmicPoleSlope ω u h‖ ≤ (Real.exp (ω.re*(u+h))+Real.exp (ω.re*u))/‖ω‖ := by
  have he := norm_cexp_sub_cexp_le (ω*(h:ℂ)) 0
  simp only [Complex.exp_zero,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,norm_one] at he
  simp only [logarithmicPoleSlope,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [div_le_div_iff₀ (mul_pos (abs_pos.mpr hh) (sq_pos_of_pos (norm_pos_iff.mpr hω))) (norm_pos_iff.mpr hω),
    mul_add ω.re u h,Real.exp_add]
  calc
    _ ≤ (Real.exp (ω.re*u)*(‖ω‖*|h| * (Real.exp (ω.re*h)+1)))*‖ω‖ := by gcongr
    _ = _ := by ring

end AnalyticNumberTheory.AnalyticTools
