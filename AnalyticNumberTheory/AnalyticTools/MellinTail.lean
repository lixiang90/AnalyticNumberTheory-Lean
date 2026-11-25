import Mathlib.Analysis.MellinTransform

/-!
# Holomorphic Mellin integrals on a positive tail

Removing a neighborhood of the origin makes the Mellin transform of
an exponentially decaying function entire.
-/

open Complex Real Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- The Mellin integral on `(r,∞)` is entire when `r>0` and its
kernel is continuous there and decays exponentially. -/
theorem differentiable_mellinTail {f : ℝ→ℂ} {a r : ℝ} (ha : 0<a) (hr : 0<r)
    (hc : ContinuousOn f (Ici r)) (hd : f =O[atTop] fun t => Real.exp (-a*t)) :
    Differentiable ℂ (fun s : ℂ => ∫ t : ℝ in Ioi r,f t*(t:ℂ)^(s-1)) := by
  let g := (Ioi r).indicator f
  have hg : LocallyIntegrableOn g (Ioi 0) := by
    have hc' : Continuous (fun t : ℝ => f (max r t)) :=
      hc.comp_continuous (continuous_const.max continuous_id) (fun t => (le_max_left r t : r≤max r t))
    have he : g=(Ioi r).indicator (fun t : ℝ => f (max r t)) := by
      funext t; by_cases ht : r<t
      · simp [g,ht,max_eq_right ht.le]
      · simp [g,ht]
    rw [he]; exact (hc'.locallyIntegrable.indicator measurableSet_Ioi).locallyIntegrableOn _
  have hd' : g =O[atTop] fun t => Real.exp (-a*t) := by
    apply hd.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop r] with t ht; simp [g,ht]
  have he (s : ℂ) : mellin g s=∫ t : ℝ in Ioi r,f t*(t:ℂ)^(s-1) := by
    unfold mellin
    have hh (t : ℝ) : (t:ℂ)^(s-1) • g t=(Ioi r).indicator (fun u : ℝ => f u*(u:ℂ)^(s-1)) t := by
      by_cases ht : r<t <;> simp [g,ht,mul_comm,smul_eq_mul]
    simp_rw [hh]
    rw [setIntegral_indicator measurableSet_Ioi,inter_eq_right.mpr (Ioi_subset_Ioi hr.le)]
  rw [←funext he]
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow_exp ha hg hd' (b:=s.re-1) _ (by linarith)
  refine isBigO_iff.mpr ⟨0,?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hr)] with t (ht : t<r)
  simp [g,ht.not_gt]

end AnalyticNumberTheory.AnalyticTools
