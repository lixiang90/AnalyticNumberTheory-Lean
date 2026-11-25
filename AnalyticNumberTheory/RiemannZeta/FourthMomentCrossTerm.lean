import AnalyticNumberTheory.RiemannZeta.FourthMomentRightBoundary
import AnalyticNumberTheory.RiemannZeta.FourthMomentRightCross
import AnalyticNumberTheory.RiemannZeta.FourthMomentCrossEdges

/-! # Contour shift for the mixed term of the zeta fourth moment -/
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

set_option maxHeartbeats 700000 in
/-- The signed cross term between the short polynomial and the analytic remainder
has a third power of the logarithm on a dyadic interval. Moving the contour to
real part two retains cancellation that is lost in a critical-line absolute bound. -/
theorem fourthMomentCrossTerm_integral_bound :
    ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
      ‖∫ t in T..2*T, fourthMomentCrossTerm ⌊T/(4*Real.pi)⌋₊ ((1/2:ℂ)+(t:ℂ)*I)‖ ≤
        C*T*(1+Real.log T)^3 := by
  obtain ⟨B,hB,HB⟩ := fourthMoment_right_boundary_pointwise
  obtain ⟨M,hM,HM⟩ := fourthMomentCrossTerm_right_of_pointwise hB
  have he : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (T/2) (3*T),
      ‖fourthMomentCrossTerm ⌊T/(4*Real.pi)⌋₊ (2+(t:ℂ)*I)‖ ≤ M*T*(1+Real.log T)^3 := by
    filter_upwards [eventually_ge_atTop (16*Real.pi)] with T hT
    intro t ht
    obtain ⟨hP,hE⟩ := HB hT t
    exact HM (by linarith [Real.pi_gt_three] : 4≤T) ht.1 hP hE
  obtain ⟨K,hK,HK⟩ := eventually_fourthMomentCrossTerm_horizontal_edges hM.le he
  obtain ⟨D,hD,HD⟩ := fourthMoment_right_boundary_means
  obtain ⟨J,hJ,HJ⟩ := fourthMomentCrossTerm_right_integral_of_means hD
  refine ⟨3*K+J,by positivity,?_⟩
  filter_upwards [HK,eventually_ge_atTop (16*Real.pi)] with T hedges hT
  have hT' : 4≤T := by linarith [Real.pi_gt_three]
  have hT₀ : 0<T := by linarith
  let N := ⌊T/(4*Real.pi)⌋₊
  obtain ⟨hP,hE⟩ := HD hT
  have hr := HJ (T:=T) (N:=N) hT' hP (hE.trans_eq (by norm_num [zpow_neg,div_eq_mul_inv]))
  have hd : DifferentiableOn ℂ (fourthMomentCrossTerm N) (Icc (1/2:ℝ) 2 ×ℂ Icc T (2*T)) := by
    intro z hz
    exact (differentiableAt_fourthMomentCrossTerm N (by linarith [hz.2.1])).differentiableWithinAt
  have hs := norm_vertical_integral_sub_le_horizontal (f:=fourthMomentCrossTerm N)
    (M:=K*T*(1+Real.log T)^3) (by norm_num : (1/2:ℝ)≤2)
    (by linarith : T≤2*T) hd hedges
  push_cast at hs
  apply (norm_le_norm_sub_add _ (∫ t in T..2*T, fourthMomentCrossTerm N (2+(t:ℂ)*I))).trans
  exact (add_le_add hs hr).trans_eq (by ring)

end AnalyticNumberTheory.RiemannZeta
