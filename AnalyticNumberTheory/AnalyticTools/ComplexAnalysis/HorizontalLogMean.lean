import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalLogIntegral

/-!
# Horizontal logarithmic means inside an analytic disk

These estimates use the segment from one half to two, centered at its
right endpoint. The disk stays inside the positive half-plane when translated
vertically, as needed for the logarithmic mean of the zeta function.
-/

open Complex Real Set Filter Metric Finset MeasureTheory
open scoped Topology Interval
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Integral of the log modulus along the segment from one half to two. -/
noncomputable def horizontalLogMean (f : ℂ→ℂ) (t : ℝ) : ℝ :=
  ∫ x in (1/2:ℝ)..2, Real.log ‖f ((x:ℂ)+(t:ℂ)*I)‖

private theorem segment_distance {x t T : ℝ} (hx : x∈Set.Icc (1/2:ℝ) 2) :
    ‖((x:ℂ)+(t:ℂ)*I)-(2+(T:ℂ)*I)‖ ≤ 3/2+|t-T| := by
  rw [show ((x:ℂ)+(t:ℂ)*I)-(2+(T:ℂ)*I) = ((x-2:ℝ):ℂ)+((t-T:ℝ):ℂ)*I by push_cast;ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hx.2)]
  linarith [hx.1]

/-- Continuity in height of the horizontal logarithmic mean. Zeros may lie
on the central segment or on neighboring segments. -/
theorem continuousAt_horizontalLogMean {f : ℂ→ℂ} {T M : ℝ} (hM : 0<M)
    (hf : AnalyticOnNhd ℂ f (closedBall (2+(T:ℂ)*I) (7/4)))
    (hc : f (2+(T:ℂ)*I)≠0) (hb : ∀ z∈sphere (2+(T:ℂ)*I) (7/4), ‖f z/f (2+(T:ℂ)*I)‖≤M) :
    ContinuousAt (horizontalLogMean f) T := by
  let c : ℂ := 2+(T:ℂ)*I
  let U := closedBall c (13/8)
  let J := Set.Icc (T-1/16) (T+1/16)
  have hsub : U⊆closedBall c (7/4) := closedBall_subset_closedBall (by norm_num)
  have hrect (x : ℝ) (hx : x∈Set.Icc (1/2:ℝ) 2) (t : ℝ) (ht : t∈J) : (x:ℂ)+(t:ℂ)*I∈U := by
    rw [show U=closedBall c (13/8) by rfl,mem_closedBall,dist_eq_norm]
    apply (segment_distance hx).trans
    have ht' : |t-T|≤1/16 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    linarith only [ht']
  obtain ⟨Z,g,_,_,hg,hn,_,H⟩ := disk_log_norm_factorization (r:=13/8) (by norm_num) (by norm_num) hM hf hc hb
  let m := analyticOrderNatAt f
  have hgc : ContinuousOn g U := (hg.mono hsub).continuousOn
  have hlog := hgc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))
  have hJ : J∈𝓝 T := Icc_mem_nhds (by linarith) (by linarith)
  have hreg := (continuousOn_horizontalIntegral (by norm_num : (1/2:ℝ)≤2)
    (by linarith : T-1/16≤T+1/16) hlog hrect).continuousAt hJ
  have hsing : Continuous (fun t : ℝ => ∑ u∈Z,(m u:ℝ)*(∫ x in (1/2:ℝ)..2,horizontalLogKernel u t x)) :=
    continuous_finsetSum _ (fun u _ => continuous_const.mul (continuous_integral_horizontalLogKernel u _ _))
  apply (hsing.continuousAt.add hreg).congr_of_eventuallyEq
  filter_upwards [hJ] with t ht
  exact (integral_log_norm_of_factors Z m hgc hn H (by norm_num) (fun x hx => hrect x hx t ht)).2

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
