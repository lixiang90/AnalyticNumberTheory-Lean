import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleInterpolation
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalLineShift

/-! # Shifting a contour with integrable boundary traces

Only the two vertical traces need be integrable. A uniform majorant on
the two horizontal edges need only tend to zero at large height.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- For an integral along a closed vertical strip, it suffices to control
the horizontal edges uniformly along symmetric rectangles. -/
theorem integral_verticalLine_eq_of_boundary_decay {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ F {z : ℂ | z.re ∈ Icc a b})
    (ha : Integrable (fun t : ℝ => F ((a : ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => F ((b : ℂ)+t*I)))
    {w : ℝ → ℝ} (hw : Tendsto w atTop (𝓝 0))
    (hbound : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b, ∀ y ∈ ({-T,T} : Set ℝ),
      ‖F ((x : ℂ)+y*I)‖ ≤ w T) :
    (∫ t : ℝ, F ((a : ℂ)+t*I)) = ∫ t : ℝ, F ((b : ℂ)+t*I) := by
  have A := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have B := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have H := (A.sub B).norm
  have W : Tendsto (fun T => 2*w T*(b-a)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hw.const_mul 2).mul_const (b-a)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  exact le_antisymm (le_of_tendsto_of_tendsto H W (by
    filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with T hT hT₀
    exact norm_vertical_integral_sub_le_horizontal (l := -T) (u := T) hab (by linarith) (hf.mono fun z hz => hz.1) hT)) (norm_nonneg _)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
