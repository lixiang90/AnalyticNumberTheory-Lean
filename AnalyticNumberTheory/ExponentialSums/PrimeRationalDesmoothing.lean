import AnalyticNumberTheory.ExponentialSums.PrimeSumDesmoothing
import AnalyticNumberTheory.ExponentialSums.SmoothedRationalPrimeSums
import AnalyticNumberTheory.ExponentialSums.PrimeContourScales

/-! # Sharp prime exponential sums from the two-contour formula -/

noncomputable section
open Complex Real
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- At a reduced rational phase with q ≤ x the sharp von Mangoldt sum is
bounded by an absolute constant times x q^(−1/4)(1+log x)³
+ x^(7/8) q^(1/8)(1+log x)^(5/2). -/
theorem primeExpSum_rational_contour :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x : ℝ},
      a.natAbs.Coprime q → (q : ℝ) ≤ x →
      ‖primeExpSum x ((a : ℝ)/q)‖ ≤ C * primeContourRationalScale x q := by
  obtain ⟨K,hK,smoothed⟩ := logSmoothedPrimeExpSum_rational_contour
  let D := 1+64*K
  have hD₁ : 1 ≤ D := by dsimp only [D]; linarith only [hK]
  have hD := zero_lt_one.trans_le hD₁
  refine ⟨8*Real.sqrt D, by positivity, ?_⟩
  intro q _ a x ha hqx
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  have hx := hq.trans hqx
  let T := primeContourSmoothedScale x q
  have hL : 1+Real.log x ≤ T := log_le_primeContourSmoothedScale hq hqx
  have hT : 0 ≤ T := (by linarith only [Real.log_nonneg hx] : 0 ≤ 1+Real.log x).trans hL
  have hM : 1+Real.log x ≤ D*T := hL.trans (le_mul_of_one_le_left hT hD₁)
  have hbound (y : ℝ) (hy : y ∈ Set.Icc x (2*x)) : ‖logSmoothedPrimeExpSum y ((a : ℝ)/q)‖ ≤ D*T := by
    apply (smoothed ha (hqx.trans hy.1)).trans
    have h := primeContourSmoothedScale_le_double hx hy.1 hy.2 hq₀.le
    calc
      _ ≤ K*(64*T) := mul_le_mul_of_nonneg_left h hK.le
      _ ≤ D*T := by dsimp only [D]; linarith only [hT]
  have H := norm_primeExpSum_le_of_logSmoothed_bound hx hM hbound
  have hroot : Real.sqrt (x*(1+Real.log x)*(D*T)) = Real.sqrt D * Real.sqrt (x*(1+Real.log x)*T) := by
    rw [← Real.sqrt_mul hD.le]
    congr 1
    ring
  rw [hroot] at H
  apply H.trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left (sqrt_primeContourSmoothedScale_le hx hq₀) (by positivity)

end AnalyticNumberTheory.ExponentialSums
