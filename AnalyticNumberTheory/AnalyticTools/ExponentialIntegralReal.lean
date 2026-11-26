import AnalyticNumberTheory.AnalyticTools.ExponentialIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-! # The real exponential integral and its Euler normalization -/

noncomputable section
open Filter Set MeasureTheory Real
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private theorem log_exp_integrable : IntegrableOn (fun t : ℝ => log t*exp (-t)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  intro hz
  have he := Real.eulerMascheroniConstant_eq_neg_integral_log
  rw [hz] at he
  linarith [Real.one_half_lt_eulerMascheroniConstant]

private theorem log_tail_parts {s : ℝ} (hs : 0<s) :
    log s+(∫t in Ioi s,exp (-t)/t)=
      (∫t in Ioi s,log t*exp (-t))+(1-exp (-s))*log s := by
  let U := Real.log
  let V := fun t : ℝ => exp (-t)
  have hU (t : ℝ) (ht : t∈Ioi s) : HasDerivAt U t⁻¹ t := Real.hasDerivAt_log (hs.trans ht).ne'
  have hV (t : ℝ) : HasDerivAt V (-exp (-t)) t := by simpa [V] using! (hasDerivAt_id' t).neg.exp
  have h₁ : IntegrableOn (U*(fun t => -exp (-t))) (Ioi s) := by
    simpa only [U,Pi.mul_def,mul_neg] using! (log_exp_integrable.mono_set (Ioi_subset_Ioi hs.le)).neg
  have h₂ : IntegrableOn ((fun t : ℝ => t⁻¹)*V) (Ioi s) := by
    apply ((integrableOn_exp_neg_Ioi s).const_mul s⁻¹).mono' (by dsimp [V,Pi.mul_def]; fun_prop)
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    change ‖t⁻¹*exp (-t)‖≤s⁻¹*exp (-t)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity [hs.trans ht])]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hs ht.le) (exp_pos _).le
  have hzero : Tendsto (U*V) (𝓝[>] s) (𝓝 (log s*exp (-s))) :=
    ((Real.continuousAt_log hs.ne').mul (by fun_prop : ContinuousAt V s)).tendsto.mono_left nhdsWithin_le_nhds
  have htop : Tendsto (U*V) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 zero_lt_one)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      exact mul_nonneg (Real.log_nonneg ht) (exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      change log t*exp (-t)≤t^(1:ℝ)*exp (-1*t)
      rw [Real.rpow_one,neg_one_mul]; gcongr; linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le ht)]
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul hU (fun t _ => hV t) h₁ h₂ hzero htop
  dsimp [U,V] at hip
  simp only [mul_neg,integral_neg,←div_eq_inv_mul] at hip
  linarith only [hip]

/-- The constant term of the exponential integral at zero is −γ. -/
theorem tendsto_log_add_eOne :
    Tendsto (fun s : ℝ => log s+∫t in Ioi s,exp (-t)/t) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  let f := fun t : ℝ => log t*exp (-t)
  have hcover : AECover (volume.restrict (Ioi (0:ℝ))) (𝓝[>] 0) (fun s : ℝ => Ioi s) :=
    aecover_Ioi_of_Ioi (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hlim : Tendsto (fun s : ℝ => ∫t in Ioi s,f t) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
    have h := hcover.integral_tendsto_of_countably_generated log_exp_integrable
    rw [Real.eulerMascheroniConstant_eq_neg_integral_log,neg_neg]
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi (mem_Ioi.mp hs).le)]
  have hr : Tendsto (fun s : ℝ => (1-exp (-s))*log s) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_log_mul_rpow_nhdsGT_zero (r:=1) zero_lt_one).norm)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0<s)
    simp only [Real.norm_eq_abs,abs_mul,Real.rpow_one]
    have hnon : 0≤1-exp (-s) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    rw [abs_of_nonneg hnon,abs_of_pos hs,mul_comm]
    gcongr; linarith [Real.add_one_le_exp (-s)]
  have hh := hlim.add hr
  apply (show Tendsto (fun s : ℝ => (∫t in Ioi s,f t)+(1-exp (-s))*log s) (𝓝[>] 0)
    (𝓝 (-eulerMascheroniConstant)) by simpa using! hh).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs using (log_tail_parts hs).symm


/-- The positive decaying real exponential integral E₁(x). -/
def realEOne (x : ℝ) : ℝ := ∫ u in Ioi x, Real.exp (-u)/u

theorem integrableOn_eOneKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)/t) (Ioi x) := by
  apply ((integrableOn_exp_neg_Ioi x).mul_const x⁻¹).mono' ((Real.continuous_exp.measurable.comp measurable_id.neg).div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  have ht₀ := hx.trans ht
  change ‖Real.exp (-t)/t‖ ≤ Real.exp (-t)*x⁻¹
  rw [Real.norm_eq_abs,abs_of_pos (div_pos (Real.exp_pos _) ht₀),div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hx ht.le) (Real.exp_pos _).le

private theorem deriv_log_remainder_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (Real.log y : ℂ)+exponentialIntegralRemainder (-(y : ℂ)))
      ((Real.exp (-t)/t : ℝ) : ℂ) t := by
  have hc := Complex.ofReal_ne_zero.mpr ht.ne'
  have h := ((Real.hasDerivAt_log ht.ne').ofReal_comp).add
    ((hasDerivAt_exponentialIntegralRemainder_of_ne_zero (neg_ne_zero.mpr hc)).scomp t (Complex.ofRealCLM.hasDerivAt.neg))
  apply h.congr_deriv
  simp only [smul_eq_mul,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_exp,Complex.ofReal_neg]
  change (t⁻¹ : ℂ) + (-(1:ℂ))*((Complex.exp (-(t:ℂ))-1)/(-(t:ℂ))) = Complex.exp (-(t:ℂ))/(t:ℂ)
  field_simp
  ring

/-- The real exponential integral is the Euler-normalized, convergent series
on the negative real ray. This identity also fixes the real part of the boundary values of Ei. -/
theorem realEOne_eq_log_remainder {x : ℝ} (hx : 0 < x) :
    (realEOne x : ℂ) = -(Real.eulerMascheroniConstant : ℂ) - (Real.log x : ℂ) -
      exponentialIntegralRemainder (-(x : ℂ)) := by
  let F (s : ℝ) : ℂ := ((Real.log s + realEOne s : ℝ) : ℂ) +
    (Real.eulerMascheroniConstant : ℂ) + exponentialIntegralRemainder (-(s : ℂ))
  have hconst {s : ℝ} (hs : 0 < s) : F s = F x := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := x)
      (fun t ht => deriv_log_remainder_neg ((lt_min hs hx).trans_le ht.1))
      (show IntervalIntegrable (fun t : ℝ => ((Real.exp (-t)/t : ℝ) : ℂ)) volume s x from
        ContinuousOn.intervalIntegrable (fun t ht => (Complex.continuous_ofReal.continuousAt.comp
          ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).div continuousAt_id
            ((lt_min hs hx).trans_le ht.1).ne')).continuousWithinAt))
    rw [intervalIntegral.integral_ofReal, ←intervalIntegral.integral_Ioi_sub_Ioi'
      (integrableOn_eOneKernel hs) (integrableOn_eOneKernel hx),Complex.ofReal_sub] at hi
    dsimp only [F,realEOne]
    simp only [Complex.ofReal_add]
    linear_combination hi
  have hR : Tendsto (fun s : ℝ => exponentialIntegralRemainder (-(s : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    have he := (hasDerivAt_exponentialIntegralRemainder 0).continuousAt
    have ht : Tendsto (fun s : ℝ => -(s : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Pi.neg_def,Complex.ofReal_zero,neg_zero] using (Complex.continuous_ofReal.continuousAt (x := (0:ℝ))).neg.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def,exponentialIntegralRemainder_zero] using he.tendsto.comp ht
  have hF : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have he := (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_log_add_eOne).add_const
      (Real.eulerMascheroniConstant : ℂ)
    simpa [F,realEOne,Function.comp_def] using he.add hR
  have he : Tendsto F (𝓝[>] 0) (𝓝 (F x)) :=
    tendsto_const_nhds.congr' ((show ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s from self_mem_nhdsWithin).mono fun s hs => (hconst hs).symm)
  have hf := tendsto_nhds_unique he hF
  dsimp only [F] at hf
  rw [Complex.ofReal_add] at hf
  linear_combination hf

/-- E₁ tends to zero at positive infinity. -/
theorem tendsto_realEOne_atTop : Tendsto realEOne atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero (μ := volume) tendsto_id

/-- With the principal argument π at negative reals, the value selected on the cut
has real part −E₁(x) and imaginary part π. -/
theorem principalExponentialIntegral_neg_real {x : ℝ} (hx : 0 < x) :
    principalExponentialIntegral (-(x : ℂ)) = -(realEOne x : ℂ) + (Real.pi : ℂ)*Complex.I := by
  have hl := Complex.log_ofReal_mul hx (x := (-1:ℂ)) (by norm_num)
  rw [mul_neg_one, Complex.log_neg_one] at hl
  rw [principalExponentialIntegral,hl,realEOne_eq_log_remainder hx]
  ring

/-- The boundary value selected by the principal argument approaches πi at the far
negative end of the real axis. -/
theorem tendsto_principalExponentialIntegral_neg_real :
    Tendsto (fun x : ℝ => principalExponentialIntegral (-(x : ℂ))) atTop (𝓝 ((Real.pi : ℂ)*Complex.I)) := by
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_realEOne_atTop).neg.add_const ((Real.pi : ℂ)*Complex.I)
  apply (by simpa using h : Tendsto _ atTop (𝓝 ((Real.pi : ℂ)*Complex.I))).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact (principalExponentialIntegral_neg_real hx).symm

end AnalyticNumberTheory.AnalyticTools
