import AnalyticNumberTheory.AnalyticTools.LaplaceStieltjesInversion

/-! # Bromwich inversion of cumulative distribution functions -/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- The one-sided Laplace transform of the cumulative mass of a finite
positive measure on the nonnegative half-line, expressed using its
Laplace–Stieltjes transform. -/
theorem laplaceTransform_cumulative {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : ∀ᵐ u ∂μ, 0 ≤ u) {z : ℂ} (hz : 0 < z.re) :
    laplaceTransform (fun t : ℝ => (μ.real (Iio t) : ℂ)) z = laplaceStieltjesTransform μ z / z := by
  let F (t u : ℝ) : ℂ := if u < t then Complex.exp (-z * t) else 0
  have hmeas : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    · exact Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp measurable_fst))
    · exact measurable_const
  have ht : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) 0
  have hpair : Integrable (Function.uncurry F) ((volume.restrict (Ioi 0)).prod μ) := by
    apply (ht.comp_fst μ).mono' hmeas.aestronglyMeasurable
    refine ae_of_all _ fun p => ?_
    change ‖if p.2 < p.1 then Complex.exp (-z * p.1) else 0‖ ≤ _
    split_ifs
    · simp [Complex.norm_exp, Complex.mul_re]
    · simpa using (Real.exp_pos (-z.re * p.1)).le
  have hleft (t : ℝ) : (∫ u : ℝ, F t u ∂μ) = Complex.exp (-z*t) * (μ.real (Iio t) : ℂ) := by
    change (∫ u : ℝ, (Iio t).indicator (fun _ => Complex.exp (-z*t)) u ∂μ) = _
    rw [integral_indicator_const _ measurableSet_Iio, Complex.real_smul, mul_comm]
  have hright (u : ℝ) (hu : 0 ≤ u) :
      (∫ t in Ioi (0 : ℝ), F t u) = Complex.exp (-z*u) / z := by
    change (∫ t in Ioi (0 : ℝ), (Ioi u).indicator (fun v => Complex.exp (-z*v)) t) = _
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hu)]
    simpa only [neg_div_neg_eq] using integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) u
  unfold laplaceTransform laplaceStieltjesTransform
  simp_rw [← hleft]
  rw [integral_integral_swap hpair, ← integral_div]
  exact integral_congr_ae (hs.mono fun u hu => hright u hu)

/-- The symmetric cutoff inverts a cumulative distribution function at
all real arguments and assigns half weight to every atom. -/
theorem laplace_cumulative_inversion {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : ∀ᵐ u ∂μ, 0 ≤ u) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (μ.real (Iio t) : ℂ))) σ x)
      atTop (𝓝 ((μ.real (Iio x) : ℂ) + (μ.real {x} : ℂ) / 2)) := by
  have hw : Integrable (fun u : ℝ => Real.exp (-σ*u)) μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hs] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) hu)
  apply (laplaceStieltjes_inversion hσ hw x).congr
  intro T
  unfold truncatedBromwich
  apply congrArg (fun w : ℂ => (1 / (2 * Real.pi : ℂ)) * w)
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [laplaceTransform_cumulative hs (by simpa using hσ)]

end AnalyticNumberTheory.AnalyticTools
