import AnalyticNumberTheory.AnalyticTools.LogarithmicPoleSlope

/-! # Reciprocal-square estimates for the kernel of Selberg's formula -/

noncomputable section

open Complex

namespace AnalyticNumberTheory.AnalyticTools

/-- The slope kernel is bounded by an exponential factor times the full squared
reciprocal distance. This retains the horizontal distance when ordinates coincide. -/
theorem norm_logarithmicPoleSlope_le_inv_sq (ω : ℂ) (u h : ℝ) :
    ‖logarithmicPoleSlope ω u h‖ ≤
      (Real.exp (ω.re*u) * (Real.exp (ω.re*h)+1) / |h|) * (‖ω‖^2)⁻¹ := by
  have he := norm_sub_le (Complex.exp (ω*(h : ℂ))) 1
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, norm_one] at he
  rw [logarithmicPoleSlope, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp (ω.re*u) * (Real.exp (ω.re*h)+1) / (|h| * ‖ω‖^2) := by gcongr
    _ = _ := by ring

/-- At horizontal displacement δ with δu ≥ 2 the diagonal kernel is at most
exp(−δu) times the single-zero Poisson weight δ/|ω|². -/
theorem norm_selbergKernel_le_poisson {ω : ℂ} {δ u : ℝ}
    (hω : ω.re = -δ) (hu : 0 < u) (hδu : 2 ≤ δ*u) :
    ‖logarithmicPoleSlope ω u u‖ ≤ Real.exp (-(δ*u)) * δ * (‖ω‖^2)⁻¹ := by
  refine (norm_logarithmicPoleSlope_le_inv_sq ω u u).trans ?_
  rw [hω, neg_mul, abs_of_pos hu]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg _))
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (div_le_iff₀ hu).mpr
  linarith [Real.exp_le_one_iff.mpr (show -(δ*u) ≤ 0 by linarith)]

end AnalyticNumberTheory.AnalyticTools
