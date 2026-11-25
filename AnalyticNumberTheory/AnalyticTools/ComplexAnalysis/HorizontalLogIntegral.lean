import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.DiskLogFactors
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalLogKernel
import Mathlib.Topology.Order.ProjIcc

/-!
# Integrating logarithms across zeros

On a compact rectangle inside a disk, finitely many logarithmic kernels
account for all zeros. Their integrals and that of the regular part are
continuous functions of the height.
-/

open Complex Real Set Filter Metric Finset MeasureTheory
open scoped Topology Interval
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- A continuous integrand on a rectangle has a horizontal integral continuous
in height throughout that rectangle. -/
theorem continuousOn_horizontalIntegral {g : ℂ→ℝ} {a b v w : ℝ} (hab : a≤b) (hvw : v≤w)
    {U : Set ℂ} (hg : ContinuousOn g U)
    (hr : ∀ x∈Icc a b, ∀ t∈Icc v w, (x:ℂ)+(t:ℂ)*I∈U) :
    ContinuousOn (fun t : ℝ => ∫ x in a..b, g ((x:ℂ)+(t:ℂ)*I)) (Icc v w) := by
  let X (x : ℝ) : ℝ := (projIcc a b hab x:ℝ)
  let T (t : ℝ) : ℝ := (projIcc v w hvw t:ℝ)
  let F (t x : ℝ) := g ((X x:ℂ)+(T t:ℂ)*I)
  have hX : Continuous X := continuous_subtype_val.comp continuous_projIcc
  have hT : Continuous T := continuous_subtype_val.comp continuous_projIcc
  have hF : Continuous F.uncurry := by
    apply hg.comp_continuous (f:=fun p : ℝ×ℝ => (X p.2:ℂ)+(T p.1:ℂ)*I) (by fun_prop)
    intro p
    exact hr _ (projIcc a b hab p.2).2 _ (projIcc v w hvw p.1).2
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=volume) hF a b).continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  simp [F,X,T,projIcc_of_mem hab hx,projIcc_of_mem hvw ht]

set_option maxHeartbeats 800000 in
/-- Integrate a finite logarithmic factorization over a horizontal slice.
The identity may fail pointwise at any of the finitely many zeros. -/
theorem integral_log_norm_of_factors {f g : ℂ→ℂ} {U : Set ℂ} (Z : Finset ℂ) (m : ℂ→ℕ)
    (hg : ContinuousOn g U) (hn : ∀ z∈U, g z≠0)
    (hfac : ∀ z∈U, z∉Z → Real.log ‖f z‖=(∑ u∈Z,(m u:ℝ)*Real.log ‖z-u‖)+Real.log ‖g z‖)
    {a b t : ℝ} (hab : a≤b) (hr : ∀ x∈Icc a b, (x:ℂ)+(t:ℂ)*I∈U) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖f ((x:ℂ)+(t:ℂ)*I)‖) volume a b ∧
    (∫ x in a..b, Real.log ‖f ((x:ℂ)+(t:ℂ)*I)‖) =
      (∑ u∈Z, (m u:ℝ)*(∫ x in a..b,horizontalLogKernel u t x))+
      ∫ x in a..b, Real.log ‖g ((x:ℂ)+(t:ℂ)*I)‖ := by
  classical
  let p (x : ℝ) := (x:ℂ)+(t:ℂ)*I
  let L (u : ℂ) (x : ℝ) := (m u:ℝ)*horizontalLogKernel u t x
  have hg' : ContinuousOn (fun z => Real.log ‖g z‖) U := hg.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))
  have hgi : IntervalIntegrable (fun x => Real.log ‖g (p x)‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hg'.comp (by dsimp [p];fun_prop) hr
  have hLi (u : ℂ) : IntervalIntegrable (L u) volume a b :=
    (intervalIntegrable_horizontalLogKernel u t a b).const_mul _
  have hsum : IntervalIntegrable (fun x => ∑ u∈Z,L u x) volume a b := by
    rw [show (fun x => ∑ u∈Z,L u x) = (∑ u∈Z,L u) from funext (fun x => (Finset.sum_apply x Z L).symm)]
    exact IntervalIntegrable.sum Z (fun u _ => hLi u)
  have hi := hsum.add hgi
  have hne : ∀ᵐ x : ℝ, ∀ u∈Z, x≠u.re := (Finset.eventually_all Z).mpr (fun u _ => volume.ae_ne _)
  have he : ∀ᵐ x : ℝ, x∈Ι a b → Real.log ‖f (p x)‖=(∑ u∈Z,L u x)+Real.log ‖g (p x)‖ := by
    filter_upwards [hne] with x hx
    intro hmem
    rw [uIoc_of_le hab] at hmem
    apply hfac _ (hr x (Ioc_subset_Icc_self hmem))
    intro hp
    exact hx (p x) hp (by simp [p])
  refine ⟨(intervalIntegrable_congr_ae (ae_restrict_iff' measurableSet_uIoc |>.mpr he)).mpr hi,?_⟩
  rw [intervalIntegral.integral_congr_ae he,
    intervalIntegral.integral_add hsum hgi,
    intervalIntegral.integral_finsetSum (fun u _ => hLi u)]
  simp [L,p,intervalIntegral.integral_const_mul]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
