import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Convex

/-!
# Quadratic approximation to a large imaginary power

The exponential difference is estimated using the two actual endpoint
moduli. This preserves Gaussian decay on a steepest descent contour even
when the error in the logarithmic phase is larger than one.
-/
noncomputable section
open Real Complex Set
namespace AnalyticNumberTheory.AnalyticTools

/-- A difference of exponentials controlled by the endpoint values. -/
theorem norm_cexp_sub_cexp_le (z w : ℂ) :
    ‖Complex.exp z-Complex.exp w‖≤‖z-w‖*(‖Complex.exp z‖+‖Complex.exp w‖) := by
  let M := max z.re w.re
  have h := (convex_halfSpace_re_le M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Complex.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => by rw [Complex.norm_exp];exact Real.exp_le_exp.mpr hu)
    (show w.re≤M from le_max_right _ _) (show z.re≤M from le_max_left _ _)
  rw [mul_comm] at h
  apply h.trans
  gcongr
  simp only [Complex.norm_exp]
  rcases le_total z.re w.re with h|h
  · dsimp only [M];rw [max_eq_right h];linarith [Real.exp_pos z.re]
  · dsimp only [M];rw [max_eq_left h];linarith [Real.exp_pos w.re]

private theorem norm_log_quadratic {u : ℂ} (hu : ‖u‖≤1/2) :
    ‖Complex.log (1+u)-(u-u^2/2)‖≤‖u‖^3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2 (by linarith : ‖u‖<1)
  have he : Complex.logTaylor (2+1) u=u-u^2/2 := by norm_num [Complex.logTaylor_succ,Complex.logTaylor_zero];ring
  rw [he] at h
  apply h.trans
  norm_num
  have hinv : (1-‖u‖)⁻¹≤2 := (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by norm_num;linarith)
  nlinarith [mul_le_mul_of_nonneg_left hinv (show 0≤‖u‖^3 by positivity),show 0≤‖u‖^3 by positivity]

/-- Second-order phase approximation to a Dirichlet power near a positive
real base. It is uniform in the imaginary part. -/
theorem norm_cpow_sub_quadratic_le {x : ℝ} (hx : 0<x) {s : ℂ} (hσ : 0≤s.re)
    {u : ℂ} (hu : ‖u‖≤1/2) :
    let z := (x:ℂ)*(1+u)
    let G := (x:ℂ)^(-s)*Complex.exp (-(s.im:ℂ)*I*(u-u^2/2))
    ‖z^(-s)-G‖≤(2*s.re*‖u‖+|s.im| *‖u‖^3)*(‖z^(-s)‖+‖G‖) := by
  intro z G
  let L := Complex.log (1+u)
  let V := u-u^2/2
  have hone : 1+u≠0 := by
    intro he
    have h : u= -1 := by linear_combination he
    rw [h,norm_neg,norm_one] at hu;norm_num at hu
  have hz : z≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne') hone
  let A := Complex.log z*(-s)
  let B := Complex.log x*(-s) - (s.im:ℂ)*I*V
  have he : Complex.exp A=z^(-s) := (Complex.cpow_def_of_ne_zero hz _).symm
  have he' : Complex.exp B=G := by
    dsimp only [B,G,V];rw [sub_eq_add_neg,Complex.exp_add,←Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 2;ring
  have HD : A-B= -(s.re:ℂ)*L-(s.im:ℂ)*I*(L-V) := by
    dsimp only [A,B,z,L];rw [Complex.log_ofReal_mul hx hone,Complex.ofReal_log hx.le]
    linear_combination Complex.log (1+u)*(Complex.re_add_im s)
  have hL : ‖L‖≤2*‖u‖ := (Complex.norm_log_one_add_half_le_self hu).trans (by linarith [norm_nonneg u])
  have hV := norm_log_quadratic hu
  have hD : ‖A-B‖≤2*s.re*‖u‖+|s.im| *‖u‖^3 := by
    rw [HD];apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_neg,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ]
    nlinarith [mul_le_mul_of_nonneg_left hL hσ,mul_le_mul_of_nonneg_left hV (abs_nonneg s.im)]
  rw [←he,←he']
  exact (norm_cexp_sub_cexp_le A B).trans (mul_le_mul_of_nonneg_right hD (by positivity))

end AnalyticNumberTheory.AnalyticTools
