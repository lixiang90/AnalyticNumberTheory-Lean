import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The first asymptotic term of Ei off the real axis

Moving horizontally from the negative end of the plane isolates the upper/lower
boundary phase. After subtracting exp(z)/z, the horizontal derivative is exp(z)/z²,
which gives a uniform bound in terms of the ordinate.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- The exponential integral continued through the negative real ray, using log(−z). -/
def leftExponentialIntegral (z : ℂ) : ℂ :=
  (Real.eulerMascheroniConstant : ℂ) + Complex.log (-z) + exponentialIntegralRemainder z

/-- The imaginary boundary term of Ei in the upper and lower half-planes. -/
def exponentialIntegralPhase (y : ℝ) : ℂ :=
  if 0 < y then (Real.pi : ℂ)*I else if y < 0 then -((Real.pi : ℂ)*I) else 0

/-- Complex conjugation of the argument reverses the phase. -/
theorem exponentialIntegralPhase_neg (y : ℝ) : exponentialIntegralPhase (-y) = -exponentialIntegralPhase y := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · simp [exponentialIntegralPhase,h,h.not_gt]
  · simp [exponentialIntegralPhase]
  · simp [exponentialIntegralPhase,h,h.not_gt]

theorem hasDerivAt_leftExponentialIntegral {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    HasDerivAt leftExponentialIntegral (Complex.exp z/z) z := by
  have hn : z ≠ 0 := neg_ne_zero.mp (Complex.slitPlane_ne_zero hz)
  apply ((((Complex.hasDerivAt_log hz).comp z (hasDerivAt_id z).neg).const_add
    (Real.eulerMascheroniConstant : ℂ)).add (hasDerivAt_exponentialIntegralRemainder_of_ne_zero hn)).congr_deriv
  field_simp
  ring

/-- Away from the real axis the two continuations differ by +πi above and −πi below. -/
theorem principalExponentialIntegral_eq_left_add_phase {z : ℂ} (hy : z.im ≠ 0) :
    principalExponentialIntegral z = leftExponentialIntegral z + exponentialIntegralPhase z.im := by
  have hl : Complex.log z = Complex.log (-z) + exponentialIntegralPhase z.im := by
    rcases lt_or_gt_of_ne hy with h | h
    · apply Complex.ext
      · simp [exponentialIntegralPhase,h,h.not_gt,Complex.log_re]
      · simp [exponentialIntegralPhase,h,h.not_gt,Complex.log_im,Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
    · apply Complex.ext
      · simp [exponentialIntegralPhase,h,Complex.log_re]
      · simp [exponentialIntegralPhase,h,Complex.log_im,Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
  rw [principalExponentialIntegral,leftExponentialIntegral,hl]
  ring

private theorem left_neg_real {R : ℝ} (hR : 0 < R) :
    leftExponentialIntegral (-(R:ℂ)) = -(realEOne R : ℂ) := by
  rw [leftExponentialIntegral,neg_neg,←Complex.ofReal_log hR.le,realEOne_eq_log_remainder hR]
  ring

private theorem vertical_left_edge {R : ℝ} (hR : 0 < R) (y : ℝ) :
    ‖leftExponentialIntegral (-(R:ℂ)+(y:ℂ)*I) - leftExponentialIntegral (-(R:ℂ))‖ ≤
      (Real.exp (-R)/R)*|y| := by
  let z (v : ℝ) : ℂ := -(R:ℂ)+(v:ℂ)*I
  let D (v : ℝ) := I*(Complex.exp (z v)/z v)
  have hre (v : ℝ) : (z v).re = -R := by simp [z]
  have hz (v : ℝ) : z v ≠ 0 := fun he => by have h := hre v; rw [he] at h; simp at h; linarith
  have hd (v : ℝ) : HasDerivAt (fun v => leftExponentialIntegral (z v)) (D v) v := by
    have hm : -(z v) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa [hre] using hR))
    have h := (hasDerivAt_leftExponentialIntegral hm).scomp v
      (((Complex.ofRealCLM.hasDerivAt (x := v)).mul_const I).const_add (-(R:ℂ)))
    simpa [z,D,smul_eq_mul,Function.comp_def] using h
  have hc : Continuous z := by unfold z; fun_prop
  have hD : Continuous D := continuous_const.mul ((Complex.continuous_exp.comp hc).div hc hz)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := y) (fun v _ => hd v) (hD.intervalIntegrable ..)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y) (f := D)
    (C := Real.exp (-R)/R) (by
      intro v _
      change ‖I*(Complex.exp (z v)/z v)‖ ≤ _
      rw [norm_mul,Complex.norm_I,one_mul,norm_div,Complex.norm_exp,hre]
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le hR
      simpa only [hre,abs_neg,abs_of_pos hR] using Complex.abs_re_le_norm (z v))
  rw [h] at hb
  simpa [z] using hb

/-- Along any fixed horizontal line the continuation through the negative axis tends to zero at the left end. -/
theorem tendsto_leftExponentialIntegral_neg_add_im (y : ℝ) :
    Tendsto (fun R : ℝ => leftExponentialIntegral (-(R:ℂ)+(y:ℂ)*I)) atTop (𝓝 0) := by
  have ha : Tendsto (fun R : ℝ => leftExponentialIntegral (-(R:ℂ))) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_realEOne_atTop).neg
    apply (by simpa using h : Tendsto _ atTop (𝓝 (0:ℂ))).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR using (left_neg_real hR).symm
  have he : Tendsto (fun R : ℝ => Real.exp (-R)/R*|y|) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (Real.tendsto_exp_neg_atTop_nhds_zero.mul tendsto_inv_atTop_zero).mul_const |y|
  have hd : Tendsto (fun R : ℝ => leftExponentialIntegral (-(R:ℂ)+(y:ℂ)*I) - leftExponentialIntegral (-(R:ℂ))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_gt_atTop (0:ℝ)).mono fun R hR => vertical_left_edge hR y) he
  simpa only [Pi.add_apply,sub_add_cancel,add_zero] using hd.add ha

private theorem left_exponential_remainder_deriv {z : ℂ} (h : -z ∈ Complex.slitPlane) :
    HasDerivAt (fun z => leftExponentialIntegral z - Complex.exp z/z) (Complex.exp z/z^2) z := by
  have hz : z ≠ 0 := neg_ne_zero.mp (Complex.slitPlane_ne_zero h)
  apply ((hasDerivAt_leftExponentialIntegral h).sub ((Complex.hasDerivAt_exp z).div (hasDerivAt_id z) hz)).congr_deriv
  simp only [id_eq]
  field_simp
  ring

/-- For every nonreal argument, Ei consists of its half-plane phase, exp(z)/z, and
a remainder of norm at most exp(Re z)/(Im z)², uniformly in both coordinates. -/
theorem norm_principalExponentialIntegral_sub_phase_sub_le {w : ℂ} (hy : w.im ≠ 0) :
    ‖principalExponentialIntegral w - exponentialIntegralPhase w.im - Complex.exp w/w‖ ≤
      Real.exp w.re/w.im^2 := by
  let z (r : ℝ) : ℂ := (r:ℂ)+(w.im:ℂ)*I
  let F (r : ℝ) := leftExponentialIntegral (z r) - Complex.exp (z r)/z r
  let D (r : ℝ) := Complex.exp (z r)/(z r)^2
  have hr (r : ℝ) : (z r).re=r := by simp [z]
  have hi (r : ℝ) : (z r).im=w.im := by simp [z]
  have hz (r : ℝ) : z r ≠ 0 := fun he => hy (by simpa [he] using (hi r).symm)
  have hc : Continuous z := by unfold z; fun_prop
  have hD : Continuous D := (Complex.continuous_exp.comp hc).div (hc.pow 2) (fun r => pow_ne_zero 2 (hz r))
  have hd (r : ℝ) : HasDerivAt F (D r) r := by
    have hm : -(z r) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa [hi] using hy))
    have h := (left_exponential_remainder_deriv hm).scomp r
      ((Complex.ofRealCLM.hasDerivAt (x := r)).add_const ((w.im:ℂ)*I))
    simpa [F,D,z,smul_eq_mul,Function.comp_def] using h
  have hden (t : ℝ) : |w.im| ≤ ‖z t‖ := by simpa only [hi] using Complex.abs_im_le_norm (z t)
  have hband {a b : ℝ} (hab : a ≤ b) : ‖F b-F a‖ ≤ Real.exp b/w.im^2 := by
    rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hD.intervalIntegrable ..)]
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    calc
      _ ≤ ∫ r in a..b, Real.exp r/w.im^2 := by
        apply intervalIntegral.integral_mono_on hab (hD.norm.intervalIntegrable ..) (Real.continuous_exp.div_const _ |>.intervalIntegrable ..)
        intro r _
        change ‖Complex.exp (z r)/(z r)^2‖ ≤ _
        rw [norm_div,Complex.norm_exp,hr,norm_pow]
        apply div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_ne_zero hy)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hden r) 2
      _ = (Real.exp b-Real.exp a)/w.im^2 := by rw [intervalIntegral.integral_div,integral_exp]
      _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (sq_nonneg _)
  have he : Tendsto (fun R : ℝ => Complex.exp (z (-R))/z (-R)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.div_const |w.im|)
    exact Eventually.of_forall (fun R => by
      rw [norm_div,Complex.norm_exp,hr]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr hy) (hden _))
  have hF : Tendsto (fun R : ℝ => F (-R)) atTop (𝓝 0) := by
    simpa only [F,z,Complex.ofReal_neg,sub_zero] using (tendsto_leftExponentialIntegral_neg_add_im w.im).sub he
  have hlim : Tendsto (fun R : ℝ => ‖F w.re-F (-R)‖) atTop (𝓝 ‖F w.re‖) := by
    simpa only [sub_zero] using ((tendsto_const_nhds (x := F w.re)).sub hF).norm
  have hb := le_of_tendsto hlim ((eventually_ge_atTop (-w.re)).mono fun R hR => hband (by linarith : -R ≤ w.re))
  have hz₀ : z w.re = w := Complex.re_add_im w
  rw [principalExponentialIntegral_eq_left_add_phase hy,add_sub_cancel_right]
  simpa only [F,hz₀] using hb

end AnalyticNumberTheory.AnalyticTools
