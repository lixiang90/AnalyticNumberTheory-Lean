import AnalyticNumberTheory.ExponentialSums.PrimeContourShortScale
import AnalyticNumberTheory.ExponentialSums.PrimeContourDecomposition

/-! # The absolute character mean of the regular prime contour numerator -/

noncomputable section
open Complex Real Finset
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.ExponentialSums

private theorem subset_energy_product {ι : Type*} [Fintype ι] (S : Finset ι) (a b : ι → ℂ)
    {C : ℝ} (hC : 0≤C) (h : (∑ i, ‖a i‖^2) ≤ C^2) :
    (∑ i ∈ S, ‖a i‖*‖b i‖) ≤ C*Real.sqrt (∑ i ∈ S, ‖b i‖^2) := by
  have hs : (∑ i ∈ S, ‖a i‖^2) ≤ ∑ i, ‖a i‖^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  apply (Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans
  exact mul_le_mul_of_nonneg_right ((Real.sqrt_le_sqrt (hs.trans h)).trans_eq (Real.sqrt_sq hC)) (Real.sqrt_nonneg _)

/-- The three terms of the regular numerator have pointwise character
means controlled by the Euclidean norms of the L and L′ families. -/
theorem primeContourRegular_pointwise {q A : ℕ} [NeZero q] (hA : 1≤A)
    {x : ℝ} (hAx : ((A*A : ℕ) : ℝ)≤x) (t : ℝ) :
    let s := (1/2 : ℂ)+t*I
    let R := Real.sqrt q + A
    let L := 1+Real.log x
    let V := nonprincipalCriticalNorm (q := q) (fun χ => χ.LFunction) t
    let D := nonprincipalCriticalNorm (q := q) (fun χ => deriv χ.LFunction) t
    (∑ χ : DirichletCharacter ℂ q with χ≠1, ‖primeContourRegularPart χ A A s‖) ≤
      (4*R*L)*Real.sqrt q + (R*L)*D + (R*L^2)*V := by
  intro s R L V D
  let S := (univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1)
  let P (χ : DirichletCharacter ℂ q) := intervalCharacterPolynomial χ (fun n => (Λ n : ℂ)) 0 A s
  let M (χ : DirichletCharacter ℂ q) := intervalCharacterPolynomial χ (fun n => (μ n : ℂ)) 0 A s
  let J (χ : DirichletCharacter ℂ q) := intervalCharacterPolynomial χ (fun n => (vaughanTypeICoeff A A n : ℂ)) 0 (A*A) s
  have sqs := primeContour_short_scale (q := q) hA hAx (s := s) (by simp [s])
  have hx : 1≤x := (show (1 : ℝ)≤((A*A : ℕ) : ℝ) by exact_mod_cast Nat.mul_pos hA hA).trans hAx
  have hL : 0≤L := by dsimp [L]; positivity [Real.log_nonneg hx]
  have hR : 0≤R := by dsimp [R]; positivity
  have hcard : (S.card : ℝ) ≤ q := by
    exact_mod_cast (card_le_univ S).trans ((card_dirichletCharacter_eq_totient (q := q)).le.trans (Nat.totient_le q))
  have hp : (∑ χ ∈ S, ‖P χ‖) ≤ (4*R*L)*Real.sqrt q := by
    have H := subset_energy_product S P (fun _ => 1) (by positivity : 0≤4*R*L) sqs.1
    simp only [norm_one, mul_one, one_pow, sum_const, nsmul_eq_mul] at H
    simpa only [mul_one] using H.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard) (by positivity))
  have hm : (∑ χ ∈ S, ‖M χ‖*‖deriv χ.LFunction s‖) ≤ (R*L)*D :=
    subset_energy_product S M _ (by positivity) sqs.2.1
  have hj : (∑ χ ∈ S, ‖J χ‖*‖χ.LFunction s‖) ≤ (R*L^2)*V :=
    subset_energy_product S J _ (by positivity) sqs.2.2
  calc
    _ ≤ ∑ χ ∈ S, (‖P χ‖+‖M χ‖*‖deriv χ.LFunction s‖+‖J χ‖*‖χ.LFunction s‖) := by
      apply sum_le_sum
      intro χ _
      calc
        ‖P χ + M χ*(-deriv χ.LFunction s) - J χ*χ.LFunction s‖ ≤
            ‖P χ+M χ*(-deriv χ.LFunction s)‖ + ‖J χ*χ.LFunction s‖ := norm_sub_le ..
        _ ≤ (‖P χ‖+‖M χ*(-deriv χ.LFunction s)‖) + ‖J χ*χ.LFunction s‖ := add_le_add (norm_add_le ..) le_rfl
        _ = _ := by simp only [norm_mul, norm_neg]
    _ ≤ _ := by rw [sum_add_distrib, sum_add_distrib]; exact add_le_add (add_le_add hp hm) hj

end AnalyticNumberTheory.ExponentialSums
