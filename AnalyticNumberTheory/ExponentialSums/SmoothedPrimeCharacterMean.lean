import AnalyticNumberTheory.ExponentialSums.PrimeContourRegularMean
import AnalyticNumberTheory.ExponentialSums.PrimeContourTailScale
import AnalyticNumberTheory.ExponentialSums.PrimeContourCutoff

/-! # A fixed-modulus mean for the logarithmically smoothed prime sum -/

noncomputable section
open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.ExponentialSums

set_option maxHeartbeats 600000 in
/-- Summing the logarithmically smoothed prime sum over nonprincipal characters
costs at most x (1+log x)⁴ + (xq)^(3/4) (1+log x)³, up to an absolute constant. -/
theorem logSmoothedPsiChar_nonprincipal_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {x : ℝ}, 2 ≤ q → (q : ℝ) ≤ x →
      (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖logSmoothedPsiChar χ x‖) ≤
        C * (x*(1+Real.log x)^4 + (x*q)^(3/4 : ℝ)*(1+Real.log x)^3) := by
  obtain ⟨K,hK,mean⟩ := primeContourRegular_integral_mean
  refine ⟨2*K+4, by positivity, ?_⟩
  intro q _ x hq hqx
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hx := hq₁.trans hqx
  have hx₀ := zero_lt_one.trans_le hx
  obtain ⟨A,hA,hAx,hs,ht⟩ := exists_primeContour_cutoff hq₁ hqx
  have hAx' : (A : ℝ) ≤ x :=
    (show (A : ℝ) ≤ ((A*A : ℕ) : ℝ) by exact_mod_cast Nat.le_mul_of_pos_right A hA).trans hAx
  let L := 1+Real.log x
  let P := (x*q)^(3/4 : ℝ)
  let S := (univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1)
  let E (χ : DirichletCharacter ℂ q) := logPerronIntegral (primeContourRegularPart χ A A) (1/2) x
  let B (χ : DirichletCharacter ℂ q) := logPerronIntegral (primeContourTailPart χ A A ⌊x⌋₊) 1 x
  have hL : 0 ≤ L := by dsimp [L]; linarith only [Real.log_nonneg hx]
  have hP : 0 ≤ P := Real.rpow_nonneg (mul_nonneg hx₀.le (Nat.cast_nonneg q)) _
  have htri : (∑ χ ∈ S, ‖logSmoothedPsiChar χ x‖) ≤ (∑ χ ∈ S, ‖E χ‖) + ∑ χ, ‖B χ‖ := by
    calc
      _ ≤ ∑ χ ∈ S, (‖E χ‖ + ‖B χ‖) := by
        apply sum_le_sum
        intro χ hm
        rw [(logSmoothedPsiChar_two_contours hq (mem_filter.mp hm).2 (U := A) hA hx₀).2.2]
        exact norm_add_le _ _
      _ ≤ _ := by
        rw [sum_add_distrib]
        apply add_le_add le_rfl
        exact sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun χ _ _ => norm_nonneg (B χ))
  have hreg : (∑ χ ∈ S, ‖E χ‖) ≤ (2*K)*P*L^3 := by
    apply (mean hq hA hqx hAx).trans
    calc
      _ = K*(Real.sqrt x*Real.sqrt q*(Real.sqrt q+A))*L^3 := by dsimp only [L]; ring
      _ ≤ K*(2*P)*L^3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hK.le) (by positivity)
      _ = _ := by ring
  have htail : (∑ χ, ‖B χ‖) ≤ 4*P*L^3 + 2*x*L^4 := by
    apply (primeContourTail_balanced (q := q) hA hAx').trans
    calc
      _ = 2*(x*((q : ℝ)/A))*L^3 + 2*x*L^4 := by dsimp only [L]; ring
      _ ≤ 2*(2*P)*L^3 + 2*x*L^4 := add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)) (by positivity)) le_rfl
      _ = _ := by ring
  apply htri.trans ((add_le_add hreg htail).trans ?_)
  change _ ≤ (2*K+4)*(x*L^4 + P*L^3)
  nlinarith only [mul_nonneg (show 0 ≤ 2*K+2 by positivity) (show 0 ≤ x*L^4 by positivity)]

end AnalyticNumberTheory.ExponentialSums
