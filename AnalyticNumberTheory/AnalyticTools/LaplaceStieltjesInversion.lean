import AnalyticNumberTheory.AnalyticTools.BromwichKernel
import AnalyticNumberTheory.DirichletSeries.PerronKernelUniform
import Mathlib.MeasureTheory.Integral.Prod

/-! # Laplace–Stieltjes inversion

On a finite vertical segment the inverse integral of the transform divided by
the complex variable is a superposition of Perron kernels. Passing to the limit
recovers all the mass strictly to the left of the inversion point and half the
atom at the point.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Interval Topology
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.AnalyticTools

/-- The bilateral Laplace transform of a positive measure. For a measure
supported on the nonnegative half-line this is the one-sided transform. -/
def laplaceStieltjesTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-z * u) ∂μ

private def linePoint (σ t : ℝ) : ℂ := (σ : ℂ) + t * I

private lemma linePoint_re (σ t : ℝ) : (linePoint σ t).re = σ := by
  simp [linePoint]

private lemma linePoint_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : linePoint σ t ≠ 0 := by
  intro he
  have hzero := congrArg Complex.re he
  exact hσ.ne' (by simpa only [linePoint_re, Complex.zero_re] using hzero)

private def stepIntegrand (σ x t u : ℝ) : ℂ :=
  Complex.exp (linePoint σ t * (x - u : ℝ)) / linePoint σ t

private lemma stepIntegrand_factor (σ x t u : ℝ) :
    stepIntegrand σ x t u =
      Complex.exp (linePoint σ t * x) * (Complex.exp (-linePoint σ t * u) / linePoint σ t) := by
  unfold stepIntegrand
  rw [← mul_div_assoc, ← Complex.exp_add]
  push_cast
  congr 2
  ring

private lemma stepIntegrand_continuous {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => stepIntegrand σ x p.1 p.2) := by
  have hline : Continuous (fun p : ℝ × ℝ => linePoint σ p.1) := by
    unfold linePoint
    fun_prop
  exact (Complex.continuous_exp.comp (hline.mul
    (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)))).div hline
    (fun p => linePoint_ne_zero hσ p.1)

private lemma exp_sub_weight (σ x u : ℝ) :
    Real.exp (σ * (x - u)) = Real.exp (σ * x) * Real.exp (-σ * u) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma norm_stepIntegrand_le {σ : ℝ} (hσ : 0 < σ) (x t u : ℝ) :
    ‖stepIntegrand σ x t u‖ ≤ (Real.exp (σ * x) / σ) * Real.exp (-σ * u) := by
  have hz : σ ≤ ‖linePoint σ t‖ := by
    simpa only [linePoint_re] using (linePoint σ t).re_le_norm
  rw [stepIntegrand, norm_div, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, linePoint_re]
  refine (div_le_div_of_nonneg_left (Real.exp_pos _).le hσ hz).trans_eq ?_
  rw [exp_sub_weight]
  ring

private lemma perronKernel_exp_integral (σ x u T : ℝ) :
    perronKernel (Real.exp (x-u)) σ T =
      (1 / (2 * Real.pi : ℂ)) * ∫ t in -T..T, stepIntegrand σ x t u := by
  rw [← truncatedBromwich_step_eq_perron u x σ T]
  unfold truncatedBromwich
  apply congrArg (fun w : ℂ => (1 / (2 * Real.pi : ℂ)) * w)
  apply intervalIntegral.integral_congr
  intro t _
  exact (stepIntegrand_factor σ x t u).symm

/-- Exchanging the height and measure integrals expresses every finite
Bromwich integral as an average of truncated Perron kernels. -/
theorem truncatedBromwich_laplaceStieltjes {μ : Measure ℝ} [SFinite μ]
    {σ : ℝ} (hσ : 0 < σ) (hw : Integrable (fun u : ℝ => Real.exp (-σ * u)) μ) (x T : ℝ) :
    truncatedBromwich (fun z => laplaceStieltjesTransform μ z / z) σ x T =
      ∫ u : ℝ, perronKernel (Real.exp (x-u)) σ T ∂μ := by
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (σ*x) / σ) (uIoc (-T) T) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hp : Integrable (Function.uncurry (stepIntegrand σ x))
      ((volume.restrict (uIoc (-T) T)).prod μ) :=
    (hc.mul_prod hw).mono' (stepIntegrand_continuous hσ x).aestronglyMeasurable
      (ae_of_all _ fun p => norm_stepIntegrand_le hσ x p.1 p.2)
  have ht (t : ℝ) : Complex.exp (linePoint σ t * x) *
      (laplaceStieltjesTransform μ (linePoint σ t) / linePoint σ t) =
      ∫ u : ℝ, stepIntegrand σ x t u ∂μ := by
    simp_rw [stepIntegrand_factor]
    rw [integral_const_mul, integral_div]
    rfl
  unfold truncatedBromwich
  change (1 / (2 * Real.pi : ℂ)) * (∫ t in -T..T, Complex.exp (linePoint σ t * x) *
    (laplaceStieltjesTransform μ (linePoint σ t) / linePoint σ t)) = _
  simp_rw [ht]
  rw [intervalIntegral_integral_swap hp, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun u => (perronKernel_exp_integral σ x u T).symm)

private lemma perron_exp_measurable {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (x : ℝ) :
    StronglyMeasurable (fun u : ℝ => perronKernel (Real.exp (x-u)) σ T) := by
  simp_rw [perronKernel_exp_integral, intervalIntegral.integral_of_le (neg_le_self hT.le)]
  exact stronglyMeasurable_const.mul
    ((stepIntegrand_continuous hσ x).stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Ioc (-T) T)))

private lemma perronLimit_exp_eq (x u : ℝ) :
    (perronLimit (Real.exp (x-u)) : ℂ) =
      (Iio x).indicator (fun _ : ℝ => (1 : ℂ)) u +
      ({x} : Set ℝ).indicator (fun _ : ℝ => (1 / 2 : ℂ)) u := by
  rcases lt_trichotomy u x with hu | rfl | hu
  · simp [perronLimit, Real.one_lt_exp_iff.mpr (sub_pos.mpr hu), hu, hu.ne]
  · norm_num [perronLimit]
  · have he := Real.exp_lt_one_iff.mpr (sub_neg.mpr hu)
    simp [perronLimit, he.not_gt, he.ne, hu.not_gt, hu.ne']

/-- At every real point, Laplace–Stieltjes inversion recovers the mass of
the open left half-line plus half the mass of the singleton. The measure
only needs a finite exponential moment on the line of integration. -/
theorem laplaceStieltjes_inversion {μ : Measure ℝ} [SFinite μ] {σ : ℝ} (hσ : 0 < σ)
    (hw : Integrable (fun u : ℝ => Real.exp (-σ * u)) μ) (x : ℝ) :
    Tendsto (truncatedBromwich (fun z => laplaceStieltjesTransform μ z / z) σ x)
      atTop (𝓝 ((μ.real (Iio x) : ℂ) + (μ.real {x} : ℂ) / 2)) := by
  have hi (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ Iic x) (c : ℂ) (hc : ‖c‖ ≤ 1) :
      Integrable (s.indicator (fun _ : ℝ => c)) μ := by
    apply (hw.const_mul (Real.exp (σ*x))).mono' (measurable_const.indicator hs).aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    by_cases hu : u ∈ s
    · rw [indicator_of_mem hu, ← exp_sub_weight]
      exact hc.trans (Real.one_le_exp (mul_nonneg hσ.le (sub_nonneg.mpr (hsub hu))))
    · rw [indicator_of_notMem hu, norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hm : (∫ u : ℝ, (perronLimit (Real.exp (x-u)) : ℂ) ∂μ) =
      (μ.real (Iio x) : ℂ) + (μ.real {x} : ℂ) / 2 := by
    simp_rw [perronLimit_exp_eq]
    rw [integral_add (hi _ measurableSet_Iio Iio_subset_Iic_self 1 (by simp))
        (hi _ (measurableSet_singleton x) (by simp) (1/2) (by norm_num)),
      integral_indicator_const _ measurableSet_Iio, integral_indicator_const _ (measurableSet_singleton x)]
    simp [Complex.real_smul, div_eq_mul_inv]
  rw [← hm]
  apply (tendsto_integral_filter_of_dominated_convergence
    (F := fun T u : ℝ => perronKernel (Real.exp (x-u)) σ T)
    (fun u : ℝ => (2 * Real.exp (σ*x)) * Real.exp (-σ*u)) ?_ ?_
    (hw.const_mul _) (ae_of_all _ fun u => tendsto_perronKernel (Real.exp_pos _) hσ)).congr
  · exact fun T => (truncatedBromwich_laplaceStieltjes hσ hw x T).symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (perron_exp_measurable hσ hT x).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    refine ae_of_all _ fun u => (norm_perronKernel_le_two_mul_rpow (Real.exp_pos (x-u)) hσ hT).trans_eq ?_
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm (x-u), exp_sub_weight, mul_assoc]

end AnalyticNumberTheory.AnalyticTools
