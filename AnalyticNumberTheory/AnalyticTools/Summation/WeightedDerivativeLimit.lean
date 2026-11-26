import AnalyticNumberTheory.AnalyticTools.Summation.WeightedDiscrepancy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integration by parts for bounded, pointwise-convergent primitives -/

open Filter Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- For primitives that are bounded together on a compact interval and converge pointwise,
integration against a continuously differentiable weight transfers the limit to their
derivatives. The limiting primitive may jump at either endpoint or inside the interval. -/
theorem tendsto_weighted_derivatives_of_bounded_primitives {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {a b : ℝ} (hab : a ≤ b) {F g : ι → ℝ → ℂ} {P w D : ℝ → ℂ}
    (hF : ∀ i t, t ∈ Icc a b → HasDerivAt (F i) (g i t) t)
    (hg : ∀ i, ContinuousOn (g i) (Icc a b))
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (D t) t) (hD : ContinuousOn D (Icc a b))
    (hlim : ∀ t ∈ Icc a b, Tendsto (F · t) l (𝓝 (P t)))
    (hbound : ∃ B : ℝ, ∀ᶠ i in l, ∀ t ∈ Icc a b, ‖F i t‖ ≤ B) :
    Tendsto (fun i => ∫ t in a..b, g i t * w t) l
      (𝓝 (P b * w b - P a * w a - ∫ t in a..b, P t * D t)) := by
  obtain ⟨B,hB⟩ := hbound
  have hmem {t : ℝ} (h : t ∈ uIoc a b) : t ∈ Icc a b :=
    Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using h)
  have hf (i : ι) : ContinuousOn (F i) (Icc a b) :=
    fun t ht => (hF i t ht).continuousAt.continuousWithinAt
  have hint : Tendsto (fun i => ∫ t in a..b, F i t * D t) l (𝓝 (∫ t in a..b, P t * D t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => B*‖D t‖)
    · exact Eventually.of_forall fun i => (((hf i).mul hD).mono (fun _ ht => hmem ht)).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hB] with i hi
      exact ae_of_all _ fun t ht => (norm_mul ..).le.trans (mul_le_mul_of_nonneg_right (hi t (hmem ht)) (norm_nonneg _))
    · exact (continuousOn_const.mul hD.norm).intervalIntegrable_of_Icc hab
    · exact ae_of_all _ fun t ht => (hlim t (hmem ht)).mul_const _
  apply (((hlim b ⟨hab,le_rfl⟩).mul_const _).sub ((hlim a ⟨le_rfl,hab⟩).mul_const _)
    |>.sub hint).congr
  intro i
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hF i t (by simpa only [uIcc_of_le hab] using ht))
    (fun t ht => hw t (by simpa only [uIcc_of_le hab] using ht))
    ((hg i).intervalIntegrable_of_Icc hab) (hD.intervalIntegrable_of_Icc hab)
  linear_combination -h

end AnalyticNumberTheory.AnalyticTools.Summation
