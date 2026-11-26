import AnalyticNumberTheory.AdditiveNumberTheory.CircleMethod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import AnalyticNumberTheory.AnalyticTools.Summation.WeightedIntegrals

/-! # Fourier integrals of decreasing real powers with a linear phase -/

noncomputable section

open Real Complex MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Derivative of the standard additive character on the real line. -/
theorem hasDerivAt_e (u : ℝ) :
    HasDerivAt e ((2 * Real.pi * Complex.I) * e u) u := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul ((2 : ℂ) * Real.pi)).mul_const Complex.I
  exact h.cexp.congr_deriv (by simp [e]; ring)

/-- Derivative with respect to the integration variable at any real frequency. -/
theorem hasDerivAt_e_linear (z t : ℝ) :
    HasDerivAt (fun v : ℝ => e (z*v)) (((2*Real.pi*z*Complex.I) : ℂ)*e (z*t)) t := by
  have h := (hasDerivAt_e (z*t)).scomp t ((hasDerivAt_id t).const_mul z)
  apply h.congr_deriv
  simp only [mul_one, Algebra.smul_def]
  change (z : ℂ) * ((2*Real.pi*Complex.I)*e (z*t)) = _
  ring

private theorem norm_linearPhaseDerivative (z : ℝ) :
    ‖((2*Real.pi*z*Complex.I) : ℂ)‖ = 2*Real.pi*|z| := by
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]

/-- The derivative of a linear additive phase has constant modulus. -/
theorem norm_deriv_e_linear (z t : ℝ) :
    ‖deriv (fun v : ℝ => e (z*v)) t‖ = 2*Real.pi*|z| := by
  rw [(hasDerivAt_e_linear z t).deriv, norm_mul, norm_e, mul_one, norm_linearPhaseDerivative]

/-- On any interval of length at most X, the linear exponential integral is
bounded by 2X/(1+X|z|), including the frequency zero. -/
theorem norm_integral_e_linear {a b X : ℝ} (hab : a ≤ b) (hX : b-a ≤ X) (z : ℝ) :
    ‖∫ t in a..b, e (z*t)‖ ≤ 2*X/(1+X*|z|) := by
  let I₀ := ∫ t in a..b, e (z*t)
  let c : ℂ := 2*Real.pi*z*Complex.I
  have hX₀ := (sub_nonneg.mpr hab).trans hX
  have hn : ‖I₀‖ ≤ X := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=a) (b:=b) (f:=fun t => e (z*t)) (C:=1) (fun t _ => (norm_e _).le)
    rw [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] at h
    exact h.trans hX
  have hc : Continuous (fun t : ℝ => e (z*t)) := continuous_e.comp (continuous_const.mul continuous_id)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=a) (b:=b) (fun t _ => hasDerivAt_e_linear z t) ((continuous_const.mul hc).intervalIntegrable a b)
  rw [intervalIntegral.integral_const_mul] at h
  have hcancel : 2*Real.pi*|z| * ‖I₀‖ ≤ 2 := by
    change c*I₀ = _ at h
    have h' := norm_sub_le (e (z*b)) (e (z*a))
    rw [← h, norm_mul, norm_e, norm_e] at h'
    norm_num only [c, norm_linearPhaseDerivative] at h'
    linarith only [h']
  have hzI : |z| * ‖I₀‖ ≤ 1 := by
    nlinarith only [hcancel, mul_nonneg (show 0 ≤ Real.pi-1 by linarith [Real.two_le_pi])
      (mul_nonneg (abs_nonneg z) (norm_nonneg I₀))]
  apply (le_div_iff₀ (by positivity : 0 < 1+X*|z|)).mpr
  change ‖I₀‖*(1+X*|z|) ≤ _
  nlinarith only [hn, mul_le_mul_of_nonneg_left hzI hX₀]

/-- Fourier integral of the density t^(β−1) on [1,x], with the phase e(zt).
At β = 1 this includes the principal main term. -/
def powerWeightFourierIntegral (β x z : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..x, ((t^(β-1) : ℝ) : ℂ)*e (z*t)

/-- Every decreasing real power on [1,x] satisfies the same first-derivative
bound as the constant amplitude, uniformly in β ≤ 1 and all frequencies. -/
theorem norm_powerWeightFourierIntegral_le {β x : ℝ} (hβ : β ≤ 1) (hx : 1 ≤ x) (z : ℝ) :
    ‖powerWeightFourierIntegral β x z‖ ≤ 2*x/(1+x*|z|) := by
  let w (t : ℝ) := t^(β-1)
  let w' (t : ℝ) := (β-1)*t^(β-1-1)
  have hp {t : ℝ} (ht : t ∈ Icc 1 x) : 0 < t := zero_lt_one.trans_le ht.1
  have hc : Continuous (fun t : ℝ => e (z*t)) := continuous_e.comp (continuous_const.mul continuous_id)
  have h := norm_integral_decreasing_weight hx (fun t => e (z*t)) w w'
    (fun _ _ => hc.continuousAt) hc.stronglyMeasurable
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (hp ht).ne'))
    (continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (hp ht).ne')))
    (fun t ht => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hβ) (Real.rpow_nonneg (hp ht).le _))
    (Real.rpow_nonneg (zero_le_one.trans hx) _)
    (fun t ht => norm_integral_e_linear ht.1 (by linarith only [ht.2] : t-1 ≤ x) z)
  simpa only [powerWeightFourierIntegral, w, Real.one_rpow, one_mul] using h

end AnalyticNumberTheory.AdditiveNumberTheory
