import AnalyticNumberTheory.ExponentialSums.VanDerCorput
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.AnalyticTools.Summation.WeightedIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fresnel integrals with explicit endpoint errors

The additive-character normalization is `e(x)=exp(2πix)`. A Gaussian
regularization evaluates the oscillatory half-line integral, and partial
summation bounds the tail uniformly as the damping tends to zero.
-/

open Real Complex MeasureTheory Filter Set
open scoped Topology
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.AnalyticTools

set_option maxHeartbeats 1000000 in
/-- The tail of a Fresnel integral on a finite positive interval. -/
theorem norm_integral_fresnel_tail_le {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ‖∫ x in a..b,e (x^2)‖ ≤ 1/(Real.pi*a) := by
  have hD (t : ℝ) : HasDerivAt (fun x : ℝ => 2*Real.pi*x^2) (4*Real.pi*t) t := by
    have H := (hasDerivAt_pow 2 t).const_mul (2*Real.pi)
    convert H using 1; ring
  have hD' (t : ℝ) : HasDerivAt (fun x : ℝ => 4*Real.pi*x) (4*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4*Real.pi)
  have H := vanDerCorput_integral_first_deriv (F:=fun x => 2*Real.pi*x^2)
    (F':=fun x => 4*Real.pi*x) (F'':=fun _ => 4*Real.pi) hab
    (show 0<4*Real.pi*a by positivity)
    (fun t _ => hD t) (fun t _ => hD' t)
    continuousOn_const (Or.inl (fun _ _ => by positivity))
    (fun t ht => by
      have ht0 : 0≤t := ha.le.trans ht.1
      rw [abs_of_nonneg (mul_nonneg (by positivity) ht0)]
      exact mul_le_mul_of_nonneg_left ht.1 (by positivity))
  have hcancel : 4/(4*Real.pi*a)=1/(Real.pi*a) := by ring
  simpa only [e,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow,hcancel] using H

private noncomputable def gaussianRay (u x : ℝ) : ℂ :=
  Complex.exp (-((u:ℂ)-2*Real.pi*Complex.I)*(x:ℂ)^2)

private theorem gaussianRay_factor (u x : ℝ) :
    gaussianRay u x = (Real.exp (-u*x^2):ℂ)*e (x^2) := by
  rw [gaussianRay,e,Complex.ofReal_exp,←Complex.exp_add]
  congr 1; push_cast; ring

/-- Gaussian damping preserves the Fresnel tail estimate uniformly in its
nonnegative damping parameter. -/
theorem norm_integral_damped_fresnel_tail_le {a b u : ℝ} (ha : 0<a) (hab : a≤b) (hu : 0≤u) :
    ‖∫ x in a..b,(Real.exp (-u*x^2):ℂ)*e (x^2)‖ ≤ 1/(Real.pi*a) := by
  let w (x : ℝ) := Real.exp (-u*x^2)
  let w' (x : ℝ) := (-2*u*x)*w x
  have hw (x : ℝ) : HasDerivAt w (w' x) x := by
    convert (((hasDerivAt_pow 2 x).const_mul (-u)).exp) using 1; dsimp [w',w]; ring
  have he : Continuous (fun x : ℝ => e (x^2)) := by unfold e; fun_prop
  have hw' : Continuous w' := by dsimp [w',w]; fun_prop
  have H := Summation.norm_integral_decreasing_weight hab (fun x => e (x^2)) w w'
    (fun x _ => he.continuousAt) he.stronglyMeasurable (fun x _ => hw x)
    hw'.continuousOn (fun x hx => by
      have hx0 := ha.trans_le hx.1
      dsimp only [w',w]; exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [mul_nonneg hu hx0.le]) (Real.exp_pos _).le)
    (Real.exp_pos _).le (fun x hx => norm_integral_fresnel_tail_le ha hx.1)
  apply H.trans
  apply mul_le_of_le_one_left (by positivity)
  apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

private theorem gaussianRay_tail {u R : ℝ} (hu : 0<u) (hR : 0<R) :
    ‖(∫ x in (0:ℝ)..R,gaussianRay u x) -
      ((Real.pi:ℂ)/((u:ℂ)-2*Real.pi*Complex.I))^(1/2:ℂ)/2‖ ≤ 1/(Real.pi*R) := by
  let b := ((u:ℂ)-2*Real.pi*Complex.I)
  have hb : 0<b.re := by simpa [b] using hu
  have hint := (integrable_cexp_neg_mul_sq hb).integrableOn (s:=Ioi (0:ℝ))
  have H := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hint (show Tendsto id atTop (atTop:Filter ℝ) from tendsto_id)
  rw [integral_gaussian_complex_Ioi hb] at H
  change Tendsto (fun v : ℝ => ∫ x in (0:ℝ)..v,gaussianRay u x) atTop (𝓝 (((Real.pi:ℂ)/b)^(1/2:ℂ)/2)) at H
  have hf : Continuous (gaussianRay u) := by unfold gaussianRay; fun_prop
  apply le_of_tendsto ((tendsto_const_nhds (x:=∫ x in (0:ℝ)..R,gaussianRay u x)).sub H).norm
  filter_upwards [eventually_ge_atTop R] with v hv
  rw [←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (a:=0) (b:=R))
    (hf.intervalIntegrable (a:=R) (b:=v)),sub_add_cancel_left,norm_neg]
  simpa only [gaussianRay_factor] using norm_integral_damped_fresnel_tail_le hR hv hu.le

set_option maxHeartbeats 1500000 in
/-- Fresnel's half-line integral in additive-character normalization, with an
explicit error at every positive truncation point. -/
theorem norm_fresnel_half_sub_le {R : ℝ} (hR : 0<R) :
    ‖(∫ x in (0:ℝ)..R, e (x^2)) - (1+Complex.I)/4‖ ≤ 1/(Real.pi*R) := by
  let q (u : ℝ) := (Real.pi:ℂ)/((u:ℂ)-2*Real.pi*Complex.I)
  have hden : ((0:ℝ):ℂ)-2*Real.pi*Complex.I ≠ 0 := by simp [Real.pi_ne_zero]
  have hq : q 0=Complex.I/2 := by
    apply (div_eq_iff hden).mpr
    push_cast; ring_nf; simp [Complex.I_sq]
  have hcq : ContinuousAt q 0 := ContinuousAt.div continuousAt_const (by fun_prop) hden
  have hsl : q 0∈Complex.slitPlane := by rw [hq]; apply Or.inr; norm_num [Complex.div_im]
  have hpow := (continuousAt_cpow_const (b:=(1/2:ℂ)) hsl).comp hcq
  have hi : Continuous (fun u : ℝ => ∫ x in (0:ℝ)..R,gaussianRay u x) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f:=gaussianRay) (μ:=volume) _ 0 R
    change Continuous (fun p : ℝ × ℝ => Complex.exp (-((p.1:ℂ)-2*Real.pi*Complex.I)*(p.2:ℂ)^2))
    fun_prop
  have hh := (hi.continuousAt.sub (hpow.div_const 2)).norm.continuousWithinAt (s:=Ioi 0)
  have H := le_of_tendsto hh (Filter.eventually_of_mem self_mem_nhdsWithin (fun u hu => gaussianRay_tail hu hR))
  have hroot : (Complex.I/2)^(1/2:ℂ)=(1+Complex.I)/2 := by
    have hs : ((1+Complex.I)/2)^2=Complex.I/2 := by ring_nf; simp [Complex.I_sq]
    rw [←hs,one_div]
    apply Complex.sq_cpow_two_inv; norm_num [Complex.div_re]
  change ‖(∫ x in (0:ℝ)..R,gaussianRay 0 x) - (q 0)^(1/2:ℂ)/2‖≤_ at H
  simp only [hq,hroot,gaussianRay_factor,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul] at H
  convert H using 2; ring

/-- Fresnel's half-line integral as an ordinary improper integral. -/
theorem tendsto_integral_fresnel_half :
    Tendsto (fun R : ℝ => ∫ x in (0:ℝ)..R, e (x^2)) atTop (𝓝 ((1+Complex.I)/4)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hz : Tendsto (fun R : ℝ => 1/(Real.pi*R)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop Real.pi_pos)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR using norm_fresnel_half_sub_le hR

/-- A bound valid also when the endpoint coincides with the saddle. -/
theorem norm_fresnel_half_sub_le_uniform {R : ℝ} (hR : 0≤R) :
    ‖(∫ x in (0:ℝ)..R, e (x^2)) - (1+Complex.I)/4‖ ≤ 3/(1+R) := by
  by_cases h : R≤1
  · have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=R)
      (f:=fun x : ℝ => e (x^2)) (C:=1) (fun x _ => (norm_e _).le)
    simp only [sub_zero,abs_of_nonneg hR,one_mul] at H
    have hc : ‖(1+Complex.I)/4‖ ≤ 1/2 := by
      rw [norm_div]; norm_num
      have h' := norm_add_le (1:ℂ) Complex.I
      simp only [norm_one,Complex.norm_I] at h'; linarith
    apply (norm_sub_le _ _).trans
    apply (add_le_add H hc).trans; apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [sq_nonneg R,mul_nonneg hR (sub_nonneg.mpr h),h]
  · apply (norm_fresnel_half_sub_le (by linarith : 0<R)).trans
    have hR' : 0<R := by linarith
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos hR') (by positivity)).mpr
    nlinarith only [h, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hR]

/-- A quadratic oscillatory integral with a saddle between its endpoints,
including an endpoint saddle. Both endpoint errors decay independently. -/
theorem norm_scaled_fresnel_sub_le {a b v : ℝ} (ha : a≤0) (hb : 0≤b) (hv : 0<v) :
    ‖(∫ x in a..b, e (v*x^2)) - ((Real.sqrt v)⁻¹:ℝ)*((1+Complex.I)/2)‖ ≤
      (Real.sqrt v)⁻¹ * (3/(1-Real.sqrt v*a) + 3/(1+Real.sqrt v*b)) := by
  let d := Real.sqrt v
  have hd : 0<d := Real.sqrt_pos.mpr hv
  let f (x : ℝ) := e (x^2)
  have hf : Continuous f := by unfold f e; fun_prop
  have hchange : (∫ x in a..b,e (v*x^2)) = (d⁻¹:ℝ)*(∫ x in d*a..d*b,f x) := by
    rw [←Complex.real_smul,←intervalIntegral.integral_comp_mul_left f hd.ne']
    apply intervalIntegral.integral_congr; intro x _
    change e (v*x^2) = e ((Real.sqrt v*x)^2)
    rw [mul_pow,Real.sq_sqrt hv.le]
  have hneg : (∫ x in d*a..0,f x) = ∫ x in (0:ℝ)..(-(d*a)),f x := by
    simpa [f] using (intervalIntegral.integral_comp_neg f (a:=d*a) (b:=0))
  have hL := norm_fresnel_half_sub_le_uniform (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hd.le ha))
  have hR := norm_fresnel_half_sub_le_uniform (mul_nonneg hd.le hb)
  rw [hchange,←mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hd.le)
  rw [←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (a:=d*a) (b:=0)) (hf.intervalIntegrable (a:=0) (b:=d*b)),hneg]
  let L := ∫ x in (0:ℝ)..(-(d*a)),f x
  let R := ∫ x in (0:ℝ)..(d*b),f x
  change ‖L+R-(1+Complex.I)/2‖≤_
  rw [show L+R-(1+Complex.I)/2=(L-(1+Complex.I)/4)+(R-(1+Complex.I)/4) by ring]
  exact (norm_add_le _ _).trans (add_le_add (by simpa only [sub_eq_add_neg] using hL) hR)

end AnalyticNumberTheory.AnalyticTools
