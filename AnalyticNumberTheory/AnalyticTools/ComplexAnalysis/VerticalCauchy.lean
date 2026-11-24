import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleIntegrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Cauchy inversion on a pair of vertical lines

A quadratic bound on an entire function along a strip permits the two
horizontal edges of a rectangle to tend to infinity. Reflection in the
origin then puts both vertical integrals on the same line.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Integration on the vertical line with real part `c`, including the Cauchy denominator. -/
noncomputable def verticalCauchyIntegral (F : ℂ → ℂ) (c : ℝ) : ℂ :=
  ∫ t : ℝ, F ((c:ℂ)+t*I)/((c:ℂ)+t*I)

/-- Cauchy inversion for a function holomorphic on a neighborhood of the strip between the two lines. -/
theorem verticalCauchyIntegral_sub_neg {F : ℂ → ℂ} {c D : ℝ}
    (hF : ∀ z : ℂ, z.re ∈ Icc (-c) c → AnalyticAt ℂ F z)
    (hc : 0 < c) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Icc (-c) c, ∀ t : ℝ, ‖F ((x:ℂ)+t*I)‖ ≤ D/(1+t^2)) :
    verticalCauchyIntegral F c - verticalCauchyIntegral F (-c) = 2*π*F 0 := by
  let K (w : ℂ) := F w/w
  let L (t : ℝ) := K (-(c:ℂ)+t*I)
  let R (t : ℝ) := K ((c:ℂ)+t*I)
  let E (t : ℝ) := ∫ x in (-c)..c, K ((x:ℂ)+t*I)
  have hcc : -c ≤ c := by linarith
  have hi (a : ℝ) (ha : |a|=c) : Integrable (fun t : ℝ => K ((a:ℂ)+t*I)) := by
    have hc' (t : ℝ) : c ≤ ‖(a:ℂ)+t*I‖ := by simpa [ha] using Complex.abs_re_le_norm ((a:ℂ)+t*I)
    have hn (t : ℝ) : (a:ℂ)+t*I ≠ 0 := norm_pos_iff.mp (hc.trans_le (hc' t))
    have ham := abs_le.mp (le_of_eq ha)
    have hcomp : Continuous (fun t : ℝ => F ((a:ℂ)+t*I)) := by
      exact continuous_iff_continuousAt.mpr fun t => (hF _ (by simpa using ham)).continuousAt.comp ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const) : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt)
    have hcont : Continuous (fun t : ℝ => K ((a:ℂ)+t*I)) :=
      hcomp.div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) hn
    apply (integrable_inv_one_add_sq.const_mul (D/c)).mono' hcont.aestronglyMeasurable
    filter_upwards with t
    dsimp only [K]; rw [norm_div]
    calc _ ≤ (D/(1+t^2))/c := div_le_div₀ (by positivity) (hbound a ham t) hc (hc' t)
         _ = _ := by ring
  have il : Integrable L := by simpa only [Complex.ofReal_neg] using hi (-c) (abs_neg c ▸ abs_of_pos hc)
  have ir : Integrable R := hi c (abs_of_pos hc)
  have hE {t : ℝ} (ht : 1 ≤ |t|) : ‖E t‖ ≤ (2*c*D)/(1+t^2) := by
    have hp (x : ℝ) (hx : x ∈ Icc (-c) c) : ‖K ((x:ℂ)+t*I)‖ ≤ D/(1+t^2) := by
      have h1 : 1 ≤ ‖(x:ℂ)+t*I‖ := ht.trans (by simpa using Complex.abs_im_le_norm ((x:ℂ)+t*I))
      dsimp only [K]
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) h1).trans (hbound x hx t)
    have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := -c) (b := c)
      (f := fun x : ℝ => K ((x:ℂ)+t*I)) (C := D/(1+t^2))
      (fun x hx => hp x (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hcc] using hx)))
    change ‖E t‖ ≤ _ at he
    rw [abs_of_nonneg (sub_nonneg.mpr hcc)] at he
    exact he.trans_eq (by ring)
  have htail : Tendsto (fun t : ℝ => (2*c*D)/(1+t^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by decide : 2 ≠ 0)))
  have hEu : Tendsto E atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (by filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht; exact hE (ht.trans (le_abs_self t))) htail)
  have hEl : Tendsto (fun t => E (-t)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (by filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht; simpa only [abs_neg, neg_sq] using hE (t := -t) (by rw [abs_neg]; exact ht.trans (le_abs_self t))) htail)
  have hL := intervalIntegral_tendsto_integral il tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have hR := intervalIntegral_tendsto_integral ir tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have hI : Tendsto (fun _ : ℝ => I) atTop (𝓝 I) := tendsto_const_nhds
  have H := (((hEl.sub hEu).add (hI.mul hR)).sub (hI.mul hL))
  change Tendsto (fun t : ℝ => E (-t)-E t + I*(∫ y in (-t)..t, R y) - I*(∫ y in (-t)..t, L y))
      atTop (𝓝 (0-0 + I*(∫ y, R y)-I*(∫ y, L y))) at H
  have H' : ∀ᶠ t : ℝ in atTop, E (-t)-E t + I*(∫ y in (-t)..t, R y) - I*(∫ y in (-t)..t, L y) = 2*π*I*F 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have he := rectangleBoundary_cauchy_on_strip (p := 0) (z := ⟨-c,-t⟩) (w := ⟨c,t⟩) hF
      (by simpa using hc) (by simpa using hc) (by simpa using ht) (by simpa using ht)
    simpa only [rectangleBoundary,sub_zero,Complex.ofReal_neg,E,R,L,K] using he
  have he := tendsto_nhds_unique H (tendsto_const_nhds.congr' (H'.mono fun _ hh => hh.symm))
  have hs : (∫ t, R t) - (∫ t, L t) = 2*π*F 0 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination he
  simpa only [verticalCauchyIntegral,Complex.ofReal_neg,R,L,K] using hs

/-- Cauchy inversion on two vertical lines for an entire function decaying quadratically
on the intervening strip. Reflection puts both terms on the right vertical line. -/
theorem verticalCauchyIntegral_add_reflect {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c D : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Icc (-c) c, ∀ t : ℝ, ‖F ((x:ℂ)+t*I)‖ ≤ D/(1+t^2)) :
    verticalCauchyIntegral F c + verticalCauchyIntegral (fun z => F (-z)) c = 2*π*F 0 := by
  let K (w : ℂ) := F w/w
  let L (t : ℝ) := K (-(c:ℂ)+t*I)
  have hs := verticalCauchyIntegral_sub_neg (fun z _ => hF.analyticAt z) hc hD hbound
  have hl : (∫ t, L t) = -verticalCauchyIntegral (fun z => F (-z)) c := by
    rw [← integral_neg_eq_self (f := L)]
    unfold verticalCauchyIntegral
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [L,K]
    rw [Complex.ofReal_neg,show -(c:ℂ)+ -(t:ℂ)*I = -((c:ℂ)+t*I) by ring, div_neg]
  have hleft : verticalCauchyIntegral F (-c) = ∫ t, L t := by simp only [verticalCauchyIntegral,Complex.ofReal_neg,L,K]
  rw [hleft,hl,sub_neg_eq_add] at hs
  exact hs

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
