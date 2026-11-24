import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.DirichletSeries.CriticalMeanValues

/-!
# The second moment of the zeta function on the critical line

The diagonal consists of the harmonic sum. The critical-line mean-square
criterion and the long Dirichlet approximation give leading coefficient one.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-- On the critical line the second moment has leading term `T log T`. -/
theorem mean_sq_riemannZeta_half_asymptotic :
    (fun T : ℝ => ∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^2) ~[atTop]
      (fun T : ℝ => T*Real.log T) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · apply criticalMeanSquare_of_approx continuous_riemannZeta_half (fun _ => 1)
      (fun _ => by simp) (zero_le_one) _ (fun T => ⌊T⌋₊+1) _ _
    · exact ⟨0,fun M => by simp only [harmonicMass,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
        Rat.cast_natCast,norm_one,one_pow,one_div,one_mul,sub_self,abs_zero,le_refl]⟩
    · refine ⟨2,by norm_num,?_⟩
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      refine ⟨le_rfl,?_⟩
      push_cast; linarith [Nat.floor_le (by linarith : 0 ≤ T)]
    · obtain ⟨C,_,H⟩ := mean_sq_zeta_sub_long_dirichletPoly_half
      exact ⟨C,(eventually_ge_atTop (1:ℝ)).mono (fun T h => H h)⟩
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T h
    exact mul_ne_zero (by linarith) (Real.log_pos h).ne'

end AnalyticNumberTheory.RiemannZeta
