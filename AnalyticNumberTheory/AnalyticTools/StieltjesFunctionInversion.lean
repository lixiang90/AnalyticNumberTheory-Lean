import AnalyticNumberTheory.AnalyticTools.CumulativeLaplace
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # Bromwich inversion for a bounded nondecreasing distribution function -/

noncomputable section
open MeasureTheory Filter Set Function
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- Changing a function on a null subset of the positive half-line does
not affect its one-sided Laplace transform. -/
theorem laplaceTransform_congr_ae {f g : ℝ → ℂ}
    (he : f =ᵐ[volume.restrict (Ioi 0)] g) : laplaceTransform f = laplaceTransform g := by
  funext z
  exact integral_congr_ae (he.mono fun u hu => congrArg (Complex.exp (-z*u) * ·) hu)

/-- The symmetric inverse of a bounded right-continuous nondecreasing cumulative
function on the half-line equals the midpoint of its left and right limits.
The upper limit may be any finite total mass. -/
theorem laplace_stieltjesFunction_inversion (F : StieltjesFunction ℝ)
    (hneg : ∀ t : ℝ, t < 0 → F t = 0) {M : ℝ} (htop : Tendsto F atTop (𝓝 M))
    {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (F t : ℂ))) σ x)
      atTop (𝓝 ((((leftLim F x : ℝ) : ℂ) + (F x : ℂ)) / 2)) := by
  have hbot : Tendsto F atBot (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_lt_atBot (0 : ℝ)).mono fun t ht => (hneg t ht).symm)
  letI : IsFiniteMeasure F.measure := ⟨by rw [F.measure_univ hbot htop]; exact ENNReal.ofReal_lt_top⟩
  have hleft0 : leftLim F 0 = 0 := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht using (hneg t ht).symm
  have hsupport : ∀ᵐ u ∂F.measure, 0 ≤ u := by
    apply ae_iff.mpr
    simp only [not_le]
    change F.measure (Iio (0 : ℝ)) = 0
    rw [F.measure_Iio hbot, hleft0, sub_zero, ENNReal.ofReal_zero]
  have hleft (t : ℝ) : F.measure.real (Iio t) = leftLim F t := by
    rw [measureReal_def, F.measure_Iio hbot, sub_zero, ENNReal.toReal_ofReal]
    let a := min t 0 - 1
    have hat : a < t := by dsimp [a]; linarith [min_le_left t 0]
    have ha0 : a < 0 := by dsimp [a]; linarith [min_le_right t 0]
    simpa only [hneg a ha0] using F.mono.le_leftLim hat
  have hatom (t : ℝ) : F.measure.real {t} = F t - leftLim F t := by
    rw [measureReal_def, F.measure_singleton, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono.leftLim_le le_rfl))]
  have hae : ∀ᵐ t : ℝ, leftLim F t = F t :=
    ae_iff.mpr (F.countable_leftLim_ne.measure_zero volume)
  have htransform : laplaceTransform (fun t : ℝ => (F t : ℂ)) =
      laplaceTransform (fun t : ℝ => (F.measure.real (Iio t) : ℂ)) := by
    apply laplaceTransform_congr_ae
    filter_upwards [ae_restrict_of_ae (s := Ioi (0 : ℝ)) hae] with t ht
    rw [hleft, ht]
  have hm : (F.measure.real (Iio x) : ℂ) + (F.measure.real {x} : ℂ) / 2 =
      (((leftLim F x : ℝ) : ℂ) + (F x : ℂ)) / 2 := by
    rw [hleft, hatom]
    push_cast
    ring
  rw [htransform, ← hm]
  exact laplace_cumulative_inversion hsupport hσ x

/-- A monotone function may take any intermediate value at its discontinuities.
Its symmetric inverse depends only on the two one-sided limits. -/
theorem laplace_monotone_inversion {f : ℝ → ℝ} (hf : Monotone f)
    (hneg : ∀ t : ℝ, t < 0 → f t = 0) {M : ℝ} (htop : Tendsto f atTop (𝓝 M))
    {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (f t : ℂ))) σ x)
      atTop (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  let F := hf.stieltjesFunction
  have hnegF (t : ℝ) (ht : t < 0) : F t = 0 := by
    change rightLim f t = 0
    apply rightLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [(gt_mem_nhds ht).filter_mono (nhdsWithin_le_nhds : 𝓝[>] t ≤ 𝓝 t)]
      with u hu using (hneg u hu).symm
  have hac : ∀ᵐ t : ℝ, ContinuousAt f t := ae_iff.mpr (hf.countable_not_continuousAt.measure_zero volume)
  have he : laplaceTransform (fun t : ℝ => (f t : ℂ)) = laplaceTransform (fun t : ℝ => (F t : ℂ)) := by
    apply laplaceTransform_congr_ae
    filter_upwards [ae_restrict_of_ae (s := Ioi (0 : ℝ)) hac] with t ht
    exact congrArg Complex.ofReal (hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 ht.continuousWithinAt).symm
  rw [he]
  have H := laplace_stieltjesFunction_inversion F hnegF (tendsto_rightLim_atTop_of_tendsto htop) hσ x
  change Tendsto _ _ (𝓝 ((((leftLim (rightLim f) x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) at H
  rwa [leftLim_rightLim (hf.tendsto_leftLim x)] at H

end AnalyticNumberTheory.AnalyticTools
