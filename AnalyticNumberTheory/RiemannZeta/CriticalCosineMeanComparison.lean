import AnalyticNumberTheory.RiemannZeta.CriticalCosineExpansion
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelElementaryPhase
import AnalyticNumberTheory.AnalyticTools.FourthRootMeanComparison

/-!
# Comparing the Hardy and cosine second moments

Young's inequality with a height-dependent parameter balances the known
Hardy square mean against the integral of the pointwise squared error.
This costs T^(3/4) times the square root of a logarithm.
-/
open Real Complex MeasureTheory Set
open scoped Interval
namespace AnalyticNumberTheory.RiemannZeta

/-- The integrated error made by replacing Hardy's function squared by
the square of the elementary sharp cosine sum. -/
theorem hardyZ_square_cosine_mean_error : ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},8*Real.pi≤T →
    |(∫t in (8*Real.pi)..T,hardyZ t^2)-(∫t in (8*Real.pi)..T,hardyCosineMain t^2)|≤
      C*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)) := by
  obtain ⟨D,hD,Hd⟩ := hardyZ_elementary_cosine_error
  obtain ⟨K,hK,Hk⟩ := mean_sq_hardyZ_upper_bound
  let a := 8*Real.pi
  have ha : 1≤a := by dsimp [a];linarith [Real.pi_gt_three]
  have ha' : 0<a := by linarith
  refine ⟨K+4*D^2,by positivity,?_⟩
  intro T hT
  change a≤T at hT
  have hzz := Hk (ha.trans hT)
  have hiz {x y : ℝ} : IntervalIntegrable (fun t => hardyZ t^2) volume x y :=
    (continuous_hardyZ.pow 2).intervalIntegrable ..
  have hza : 0≤∫t in (1:ℝ)..a,hardyZ t^2 := intervalIntegral.integral_nonneg ha (fun _ _ => sq_nonneg _)
  rw [←intervalIntegral.integral_add_adjacent_intervals (hiz (x:=1) (y:=a)) (hiz (y:=T))] at hzz
  have ht₀ := ha'.trans_le hT
  have hz : (∫t in a..T,hardyZ t^2)≤K*T*Real.log (T+2) := by field_simp at hzz;linarith
  rw [←intervalIntegral.integral_sub (f:=fun t=>hardyZ t^2) (g:=fun t=>hardyCosineMain t^2)
    hiz (hardyCosineMain_sq_intervalIntegrable ha'.le hT)]
  exact AnalyticTools.fourth_root_mean_square_comparison (a:=a) le_rfl hT continuous_hardyZ hK hD hz
    (fun t ht => Hd ht.1)

end AnalyticNumberTheory.RiemannZeta
