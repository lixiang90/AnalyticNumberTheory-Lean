import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Real

/-!
# Partial summation for oscillatory integrals

A nonnegative decreasing amplitude costs at most its left endpoint value
when the underlying integral has a uniform primitive bound.
-/
open Real Complex MeasureTheory Set
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- Partial summation for a decreasing weight and a variable bound on the primitive. -/
theorem norm_integral_decreasing_weight_variable {a b : ℝ} (H : ℝ → ℝ) (hab : a≤b)
    (f : ℝ → ℂ) (w w' : ℝ → ℝ) (hf : ∀ x∈Icc a b,ContinuousAt f x)
    (hfmeas : StronglyMeasurable f)
    (hw : ∀ x∈Icc a b,HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Icc a b)) (hwneg : ∀ x∈Icc a b,w' x≤0) (hwb : 0≤w b)
    (hH : ContinuousOn H (Icc a b)) (hF : ∀ x∈Icc a b, ‖∫ u in a..x,f u‖≤H x) :
    ‖∫ u in a..b,(w u:ℂ)*f u‖≤w b*H b+∫ u in a..b,(-w' u)*H u := by
  let F (x : ℝ) := ∫ u in a..x,f u
  have hc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousWithinAt
  have hd (x : ℝ) (hx : x∈Icc a b) : HasDerivAt F (f x) x :=
    intervalIntegral.integral_hasDerivAt_right ((hc.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1)
      hfmeas.stronglyMeasurableAtFilter (hf x hx)
  have hFc : ContinuousOn F (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hwc : ContinuousOn (fun x => (w' x:ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hw'
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u:=fun x => (w x:ℂ)) (v:=F) (u':=fun x => (w' x:ℂ)) (v':=f)
    (fun x hx => (hw x (by simpa only [uIcc_of_le hab] using hx)).ofReal_comp)
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx))
    (hwc.intervalIntegrable_of_Icc hab) (hc.intervalIntegrable_of_Icc hab)
  have hprim : F a=0 := intervalIntegral.integral_same
  rw [hparts,hprim,mul_zero,sub_zero]
  apply (norm_sub_le ..).trans
  have hlast : ‖(w b:ℂ)*F b‖ ≤ w b*H b := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hwb]
    exact mul_le_mul_of_nonneg_left (hF b (right_mem_Icc.mpr hab)) hwb
  have hnorm : ‖∫ u in a..b,(w' u:ℂ)*F u‖ ≤ ∫ u in a..b,(-w' u)*H u := by
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    apply intervalIntegral.integral_mono_on hab
      ((hwc.mul hFc).norm.intervalIntegrable_of_Icc hab) ((hw'.neg.mul hH).intervalIntegrable_of_Icc hab)
    intro u hu
    change ‖(w' u:ℂ)*F u‖≤(-w' u)*H u
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (hwneg u hu)]
    exact mul_le_mul_of_nonneg_left (hF u hu) (neg_nonneg.mpr (hwneg u hu))
  exact add_le_add hlast hnorm

/-- Continuous partial summation with a nonnegative decreasing weight. -/
theorem norm_integral_decreasing_weight {a b H : ℝ} (hab : a≤b)
    (f : ℝ → ℂ) (w w' : ℝ → ℝ) (hf : ∀ x∈Icc a b,ContinuousAt f x)
    (hfmeas : StronglyMeasurable f)
    (hw : ∀ x∈Icc a b,HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Icc a b)) (hwneg : ∀ x∈Icc a b,w' x≤0) (hwb : 0≤w b)
    (hF : ∀ x∈Icc a b, ‖∫ u in a..x,f u‖≤H) :
    ‖∫ u in a..b,(w u:ℂ)*f u‖≤w a*H := by
  apply (norm_integral_decreasing_weight_variable (fun _ => H) hab f w w' hf hfmeas hw hw' hwneg hwb continuousOn_const hF).trans_eq
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hw x (by simpa [uIcc_of_le hab] using hx))
      (hw'.intervalIntegrable_of_Icc hab)]
  ring

end AnalyticNumberTheory.AnalyticTools.Summation
