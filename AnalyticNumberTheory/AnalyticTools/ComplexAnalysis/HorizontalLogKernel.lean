import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# A logarithmic singularity on a horizontal segment

The integral of the logarithm of the distance to a fixed complex point
varies continuously as the horizontal segment passes through that point.
-/

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped Topology Interval
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Real logarithmic kernel for a zero at `u` on a segment of height `t`. -/
noncomputable def horizontalLogKernel (u : ℂ) (t x : ℝ) : ℝ :=
  Real.log ‖(x:ℂ)+(t:ℂ)*I-u‖

private theorem horizontal_norm_pos {u : ℂ} {x : ℝ} (hx : x≠u.re) (t : ℝ) :
    0<‖(x:ℂ)+(t:ℂ)*I-u‖ := by
  apply (abs_pos.mpr (sub_ne_zero.mpr hx)).trans_le
  simpa using Complex.abs_re_le_norm ((x:ℂ)+(t:ℂ)*I-u)

private theorem abs_kernel_bound {u : ℂ} {x : ℝ} (hx : x≠u.re) (t : ℝ) :
    |horizontalLogKernel u t x| ≤ |x|+|t|+‖u‖+|Real.log (x-u.re)| := by
  let z := (x:ℂ)+(t:ℂ)*I-u
  have hr : |x-u.re|≤‖z‖ := by simpa [z] using Complex.abs_re_le_norm z
  have hh : ‖z‖≤|x|+|t|+‖u‖ := by
    calc ‖z‖ ≤ ‖(x:ℂ)+(t:ℂ)*I‖+‖u‖ := norm_sub_le ..
         _ ≤ (‖(x:ℂ)‖+‖(t:ℂ)*I‖)+‖u‖ := by gcongr; exact norm_add_le ..
         _ = _ := by simp [norm_mul,Real.norm_eq_abs]
  have hlow := Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hx)) hr
  rw [Real.log_abs] at hlow
  change |Real.log ‖z‖|≤_
  exact abs_le.mpr ⟨by linarith only [hlow,neg_abs_le (Real.log (x-u.re)),norm_nonneg z,hh],
    by linarith only [Real.log_le_self (norm_nonneg z),hh,abs_nonneg (Real.log (x-u.re))]⟩

private theorem kernel_majorant (u : ℂ) (a b t₀ : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x|+(|t₀|+1)+‖u‖+|Real.log (x-u.re)|) volume a b := by
  have hi := (intervalIntegrable_log' (a:=a-u.re) (b:=b-u.re)).comp_sub_right u.re
  simp only [sub_add_cancel] at hi
  have hc : Continuous (fun x : ℝ => |x|+(|t₀|+1)+‖u‖) := by fun_prop
  exact (hc.intervalIntegrable a b).add hi.abs

private theorem measurable_kernel (u : ℂ) (t : ℝ) : Measurable (horizontalLogKernel u t) := by
  unfold horizontalLogKernel
  fun_prop

/-- The horizontal logarithmic kernel is integrable even on a segment through its zero. -/
theorem intervalIntegrable_horizontalLogKernel (u : ℂ) (t a b : ℝ) :
    IntervalIntegrable (horizontalLogKernel u t) volume a b := by
  rw [intervalIntegrable_iff]
  apply (intervalIntegrable_iff.mp (kernel_majorant u a b t)).mono'
    (measurable_kernel u t).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae (volume.ae_ne u.re)] with x hx
  rw [Real.norm_eq_abs]
  linarith only [abs_kernel_bound hx t]

/-- Moving a horizontal segment through a zero preserves continuity of its
integrated logarithm of distance. -/
theorem continuous_integral_horizontalLogKernel (u : ℂ) (a b : ℝ) :
    Continuous (fun t => ∫ x in a..b, horizontalLogKernel u t x) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  apply intervalIntegral.continuousAt_of_dominated_interval (bound:=fun x => |x|+(|t₀|+1)+‖u‖+|Real.log (x-u.re)|)
  · exact Eventually.of_forall fun t => (measurable_kernel u t).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t₀ (by norm_num : (0:ℝ)<1)] with t ht
    filter_upwards [volume.ae_ne u.re] with x hx
    intro _
    rw [Real.norm_eq_abs]
    have hh : |t-t₀|<1 := by simpa [Real.dist_eq] using ht
    linarith only [abs_kernel_bound hx t,abs_sub_abs_le_abs_sub t t₀,hh]
  · exact kernel_majorant u a b t₀
  · filter_upwards [volume.ae_ne u.re] with x hx
    intro _
    unfold horizontalLogKernel
    have h : ContinuousAt (fun t : ℝ => ‖(x:ℂ)+(t:ℂ)*I-u‖) t₀ := by fun_prop
    exact h.log (horizontal_norm_pos hx t₀).ne'

/-- Uniform L¹ bound as the location of the zero ranges over a bounded set
relative to the height of the segment. -/
theorem horizontalLogKernel_integral_abs_bound {a b K : ℝ} (hab : a≤b) (hK : 0≤K) :
    ∃ C : ℝ, 0≤C ∧ ∀ (u : ℂ) (t : ℝ), ‖u-(t:ℂ)*I‖≤K →
      (∫ x in a..b, |horizontalLogKernel u t x|)≤C := by
  let V := ∫ x in a..b, |x|+K
  let J := ∫ x in (a-K)..(b+K), |Real.log x|
  refine ⟨V+J,add_nonneg (intervalIntegral.integral_nonneg hab (fun _ _ => add_nonneg (abs_nonneg _) hK))
    (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)),?_⟩
  intro u t hu
  let v := u-(t:ℂ)*I
  have hre := (Complex.abs_re_le_norm v).trans hu
  have hlog := (intervalIntegrable_log' (a:=a-v.re) (b:=b-v.re)).comp_sub_right v.re
  simp only [sub_add_cancel] at hlog
  have hc : Continuous (fun x : ℝ => |x|+K) := by fun_prop
  have hb : (∫ x in a..b, |horizontalLogKernel u t x|)≤
      ∫ x in a..b, (|x|+K)+|Real.log (x-v.re)| := by
    apply intervalIntegral.integral_mono_ae hab (intervalIntegrable_horizontalLogKernel u t a b).abs
      ((hc.intervalIntegrable ..).add hlog.abs)
    filter_upwards [volume.ae_ne v.re] with x hx
    have he : horizontalLogKernel u t x=horizontalLogKernel v 0 x := by
      unfold horizontalLogKernel v
      simp only [Complex.ofReal_zero,zero_mul,add_zero]
      congr 2
      ring
    rw [he]
    have hh := abs_kernel_bound hx 0
    rw [abs_zero,add_zero] at hh
    linarith only [hh,hu]
  rw [intervalIntegral.integral_add (hc.intervalIntegrable ..) hlog.abs,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => |Real.log x|)] at hb
  apply hb.trans
  apply add_le_add le_rfl
  exact intervalIntegral.integral_mono_interval (by linarith [(abs_le.mp hre).2]) (by linarith)
    (by linarith [(abs_le.mp hre).1]) (Eventually.of_forall (fun x => abs_nonneg _)) intervalIntegrable_log'.abs

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
