import AnalyticNumberTheory.RiemannZeta.HurwitzDiagonalMean
import AnalyticNumberTheory.AnalyticTools.VerticalApproximationMean

/-!
# The square mean of Hurwitz zeta in the right half of the critical strip

For each real shift `0 < a ≤ 1` and each `1/2 < σ ≤ 1`, the mean square
on `[1,T]` tends to the absolutely convergent diagonal
`∑ (n+a)^(-2σ)`. Starting the integral at one includes the boundary `σ=1`.
-/

open Real Complex Finset MeasureTheory Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem verticalLine_continuousOn (a σ T : ℝ) : ContinuousOn
    (fun t : ℝ => HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((σ:ℂ)+t*I)) (Set.Icc 1 T) := by
  intro t ht
  have hs : (σ:ℂ)+t*I ≠ 1 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    linarith [ht.1]
  exact ((HurwitzZeta.differentiableAt_hurwitzZeta _ hs).continuousAt.comp
    (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop)).continuousWithinAt

/-- The square mean of the error in the length-`⌊T⌋+1` approximation tends to zero. -/
theorem tendsto_hurwitzZeta_long_error_squareMean {a σ : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1)
    (hσ : 1/2 < σ) (hσ' : σ ≤ 1) : Tendsto (fun T : ℝ => intervalSquareMean 1 T T
      (hurwitzVerticalPolynomial a σ (Icc 0 (⌊T⌋₊+1)) -
        fun t : ℝ => HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((σ:ℂ)+t*I))) atTop (𝓝 0) := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_dirichletPoly_error zero_lt_one (by linarith [Real.two_le_pi] : (1:ℝ)<2*π)
  let P (n : ℕ) := hurwitzVerticalPolynomial a σ (Icc 0 n)
  let Z (t : ℝ) := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((σ:ℂ)+t*I)
  apply tendsto_squareMean_of_vertical_error (fun n => P n-Z) (A:=1) (B:=K) hσ hσ'
    (fun n T => (continuous_hurwitzVerticalPolynomial ha.1 σ _).continuousOn.sub (verticalLine_continuousOn a σ T))
  intro n hn t ht ht'
  have ht0 : 0<t := by linarith
  change ‖P n t-Z t‖≤_
  rw [norm_sub_rev,one_mul]
  simpa only [P,Z,hurwitzVerticalPolynomial,abs_of_pos ht0] using H (σ:=σ) (t:=t) ha hn (by linarith) hσ'
    (by rwa [abs_of_pos ht0]) (by simpa [abs_of_pos ht0] using ht')

/-- The complete mean-square main term for every real shift and every `1/2 < σ ≤ 1`. -/
theorem mean_sq_hurwitzZeta_of_half_lt {a σ : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1)
    (hσ : 1/2 < σ) (hσ' : σ ≤ 1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle)
      ((σ:ℂ)+t*I)‖^2)/T) atTop (𝓝 (∑' n : ℕ, ((n:ℝ)+a)^(-2*σ))) :=
  tendsto_squareMean_of_difference (eventually_ge_atTop (1:ℝ)) (eventually_gt_atTop 0)
    (Eventually.of_forall fun _T => (continuous_hurwitzVerticalPolynomial ha.1 σ _).continuousOn)
    (Eventually.of_forall (verticalLine_continuousOn a σ))
    (tendsto_long_hurwitzPolynomial_squareMean ha hσ) (tendsto_hurwitzZeta_long_error_squareMean ha hσ hσ')

/-- The real diagonal constant is the value of Hurwitz zeta at `2σ`. -/
theorem hurwitzZeta_re_eq_square_diagonal {a σ : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1) (hσ : 1/2 < σ) :
    (HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((2*σ:ℝ):ℂ)).re =
      ∑' n : ℕ, ((n:ℝ)+a)^(-2*σ) := by
  have h := Complex.hasSum_re (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨ha.1.le,ha.2⟩
    (s := ((2*σ:ℝ):ℂ)) (by change 1<2*σ; linarith))
  symm
  apply (h.congr_fun fun n => ?_).tsum_eq
  have hp := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha.1
  rw [←Complex.ofReal_natCast,←Complex.ofReal_add,←Complex.ofReal_cpow hp.le,
    ←Complex.ofReal_one,←Complex.ofReal_div,Complex.ofReal_re,
    show -2*σ= -(2*σ) by ring,Real.rpow_neg hp.le,one_div]

end AnalyticNumberTheory.RiemannZeta
