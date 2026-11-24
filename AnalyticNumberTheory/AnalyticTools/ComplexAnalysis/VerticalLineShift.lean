import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalCauchy

/-!
# Shifting absolutely convergent vertical integrals

A holomorphic function with a quadratic majorant throughout a closed
vertical strip has equal integrals along its two vertical boundary lines.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Horizontal displacement of a full vertical contour. -/
theorem integral_verticalLine_eq_of_strip {F : ℂ → ℂ} {a b D : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ F {z : ℂ | z.re ∈ Icc a b}) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖F ((x:ℂ)+t*I)‖ ≤ D/(1+t^2)) :
    (∫ t : ℝ, F ((a:ℂ)+t*I)) = ∫ t : ℝ, F ((b:ℂ)+t*I) := by
  let V (x t : ℝ) := F ((x:ℂ)+t*I)
  let E (y : ℝ) := ∫ x in a..b, V x y
  have hi (x : ℝ) (hx : x ∈ Icc a b) : Integrable (V x) := by
    have hcont : Continuous (V x) := by
      rw [← continuousOn_univ]
      apply hf.continuousOn.comp (by fun_prop)
      intro t _
      simpa using hx
    apply (integrable_inv_one_add_sq.const_mul D).mono' hcont.aestronglyMeasurable
    filter_upwards with t
    exact (hbound x hx t).trans_eq (by ring)
  have he (t : ℝ) : ‖E t‖ ≤ ((b-a)*D)/(1+t^2) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := fun x => V x t)
      (C := D/(1+t^2)) (fun x hx => hbound x (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hx)) t)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hh
    exact hh.trans_eq (by ring)
  have ht : Tendsto (fun t : ℝ => ((b-a)*D)/(1+t^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by decide : 2 ≠ 0)))
  have hEu : Tendsto E atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall he) ht)
  have hEl : Tendsto (fun t => E (-t)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall fun t => by simpa only [neg_sq] using he (-t)) ht)
  have ha := intervalIntegral_tendsto_integral (hi a ⟨le_rfl,hab⟩) tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have hb := intervalIntegral_tendsto_integral (hi b ⟨hab,le_rfl⟩) tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have hI : Tendsto (fun _ : ℝ => I) atTop (𝓝 I) := tendsto_const_nhds
  have H := (((hEl.sub hEu).add (hI.mul hb)).sub (hI.mul ha))
  change Tendsto (fun t : ℝ => E (-t)-E t + I*(∫ y in (-t)..t, V b y)-I*(∫ y in (-t)..t, V a y))
    atTop (𝓝 (0-0 + I*(∫ y, V b y)-I*(∫ y, V a y))) at H
  have H' : ∀ t : ℝ, E (-t)-E t+I*(∫ y in (-t)..t, V b y)-I*(∫ y in (-t)..t, V a y)=0 := by
    intro t
    have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (⟨a,-t⟩:ℂ) (⟨b,t⟩:ℂ)
      (hf.mono (fun z hz => by
        change z.re ∈ Icc a b
        have hr : z.re ∈ uIcc a b := hz.1
        rwa [uIcc_of_le hab] at hr))
    simpa only [E,V,Complex.ofReal_neg,smul_eq_mul] using hh
  have heq := tendsto_nhds_unique H (tendsto_const_nhds.congr' (Eventually.of_forall fun t => (H' t).symm))
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -heq

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
