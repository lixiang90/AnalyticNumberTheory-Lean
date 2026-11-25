import AnalyticNumberTheory.DivisorProblems.CircleOctantDiscrepancy
import AnalyticNumberTheory.DivisorProblems.CircleArcExponentialSums

/-!
# The cube-root bound for Gauss's circle problem

Counting the eight octants reduces the discrepancy to one arc where the
curvature is comparable to the reciprocal radius. The second derivative
estimate and a smoothed Fourier approximation give the classical cube-root
bound in the squared radius.
-/

noncomputable section
open Finset Filter Asymptotics
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DivisorProblems

/-- For squared radius `x≥2`, the number of lattice points in the closed
disk differs from `πx` by at most a constant times `x^(1/3)`. -/
theorem abs_gaussCircleError_le_cubeRoot :
    ∃ C > 0, ∀ {x : ℝ}, 2≤x → |gaussCircleError x| ≤ C*x^(1/3:ℝ) := by
  obtain ⟨C,hC,H⟩ := abs_circleArc_sawtooth_le_cubeRoot
  refine ⟨8+8*C,by positivity,?_⟩
  intro x hx
  let S := ∑ n ∈ Icc 1 ⌊Real.sqrt (x/2)⌋₊, sawtooth (circleArc x n)
  have he : |gaussCircleError x+8*S|≤8 := abs_gaussCircleError_add_octant_sawtooth_le (by linarith)
  have hs : |S|≤C*x^(1/3:ℝ) := H hx
  have hr : 1≤x^(1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp he).1,(abs_le.mp hs).2,hr],
    by linarith only [(abs_le.mp he).2,(abs_le.mp hs).1,hr]⟩

/-- The classical `O(x^(1/3))` estimate for the circle discrepancy. -/
theorem gaussCircleError_isBigO_cubeRoot :
    gaussCircleError =O[atTop] (fun x : ℝ => x^(1/3:ℝ)) := by
  obtain ⟨C,_,H⟩ := abs_gaussCircleError_le_cubeRoot
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact H hx

/-- The summatory two-squares representation function has the same
cube-root discrepancy, counting the origin at `n=0`. -/
theorem sum_repTwoSquares_sub_pi_isBigO_cubeRoot :
    (fun x : ℝ => (∑ n ∈ Icc 0 ⌊x⌋₊,(repTwoSquares n:ℝ))-Real.pi*x) =O[atTop]
      (fun x : ℝ => x^(1/3:ℝ)) := by
  apply gaussCircleError_isBigO_cubeRoot.congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  rw [gaussCircleError,gaussCircleCount_eq_sum_repTwoSquares hx]

end AnalyticNumberTheory.DivisorProblems
