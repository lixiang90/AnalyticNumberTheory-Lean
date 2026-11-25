import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Symmetric means of absolutely summable exponential expansions -/

noncomputable section

open Complex Real Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- An exponential series with real frequencies, normalized as `exp(iωt)`. -/
def exponentialSeries {ι : Type*} (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑' j, c j * Complex.exp ((ω j*t : ℝ) * I)

/-- The mean of a complex function over the symmetric interval of height `T`. -/
def symmetricMean (f : ℝ → ℂ) (T : ℝ) : ℂ :=
  (∫ t : ℝ in -T..T, f t) / (2 * (T : ℂ))

/-- The mean of an individual real frequency on a nonzero symmetric interval. -/
theorem symmetricMean_exp {T : ℝ} (hT : T ≠ 0) (r : ℝ) :
    symmetricMean (fun t : ℝ => Complex.exp ((r*t : ℝ) * I)) T = (Real.sinc (r*T) : ℂ) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  by_cases hr : r = 0
  · simp [hr,symmetricMean,Complex.real_smul]
    field_simp [hTc]
    ring
  · unfold symmetricMean
    have h := intervalIntegral.integral_comp_mul_left (fun t : ℝ => Complex.exp (t * I))
      (a := -T) (b := T) hr
    rw [mul_neg, integral_exp_mul_I_eq_sinc] at h
    rw [h,Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr,hTc]

private lemma sinc_frequency_limit (r : ℝ) :
    Tendsto (fun T : ℝ => (Real.sinc (r*T) : ℂ)) atTop (𝓝 (if r=0 then 1 else 0)) := by
  split_ifs with hr
  · simp [hr]
  · have hmajor : Tendsto (fun T : ℝ => |r|⁻¹ * T⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul |r|⁻¹
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Complex.norm_real, Real.norm_eq_abs, Real.sinc_of_ne_zero (mul_ne_zero hr hT.ne'),
      abs_div, abs_mul, abs_of_pos hT]
    simpa [div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right (Real.abs_sin_le_one (r*T)) (mul_pos (abs_pos.mpr hr) hT).le

/-- A symmetric mean retains precisely the total coefficient at frequency
zero. The index can be any countable type, and equal frequencies may occur. -/
theorem tendsto_symmetricMean_expansion {ι : Type*} [Countable ι] (c : ι → ℂ) (ω : ι → ℝ)
    (hc : Summable (fun j => ‖c j‖)) :
    Tendsto (symmetricMean (exponentialSeries c ω)) atTop
      (𝓝 (∑' j, if ω j = 0 then c j else 0)) := by
  have hlim (j : ι) : Tendsto (fun T : ℝ => c j * (Real.sinc (ω j*T) : ℂ)) atTop
      (𝓝 (if ω j=0 then c j else 0)) := by
    simpa only [mul_ite, mul_one, mul_zero] using (sinc_frequency_limit (ω j)).const_mul (c j)
  have hsum := tendsto_tsum_of_dominated_convergence hc hlim (.of_forall fun T j => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sinc_le_one _))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  let f (j : ι) (t : ℝ) := c j * Complex.exp ((ω j*t : ℝ) * I)
  have hnorm (j : ι) (t : ℝ) : ‖f j t‖ = ‖c j‖ := by
    dsimp only [f]
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
  have H : HasSum (fun j => ∫ t : ℝ in -T..T, f j t) (∫ t : ℝ in -T..T, ∑' j, f j t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun j _ => ‖c j‖)
    · intro j
      exact (by dsimp [f]; fun_prop : Continuous (f j)).aestronglyMeasurable
    · intro j
      exact .of_forall fun t _ => (hnorm j t).le
    · exact .of_forall fun _ _ => hc
    · exact intervalIntegrable_const
    · exact .of_forall fun t _ => (hc.of_norm_bounded fun j => (hnorm j t).le).hasSum
  change (∑' j, c j * (Real.sinc (ω j*T) : ℂ)) = _
  unfold symmetricMean
  change _ = (∫ t : ℝ in -T..T, ∑' j, f j t) / (2*(T : ℂ))
  rw [← H.tsum_eq, ← tsum_div_const]
  apply tsum_congr
  intro j
  unfold f
  rw [intervalIntegral.integral_const_mul, mul_div_assoc, ← symmetricMean, symmetricMean_exp hT.ne']

end AnalyticNumberTheory.AnalyticTools
