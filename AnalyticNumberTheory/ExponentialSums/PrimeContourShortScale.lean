import AnalyticNumberTheory.ExponentialSums.PrimeContourPolynomialMeans

/-! # A common length scale for the three short prime contour polynomials -/

open Complex Real Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

/-- For equal truncations with A² ≤ x, one uses the common length scale
√q+A. The square roots of the three critical-line energies then cost one,
one and two logarithms, respectively. -/
theorem primeContour_short_scale {q A : ℕ} [NeZero q] (hA : 1≤A) {x : ℝ} (hAx : ((A*A : ℕ) : ℝ) ≤ x)
    {s : ℂ} (hs : s.re=1/2) :
    let L := 1+Real.log x
    let R := Real.sqrt q + A
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ (fun n => (Λ n : ℂ)) 0 A s‖^2) ≤ (4*R*L)^2 ∧
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ (fun n => (μ n : ℂ)) 0 A s‖^2) ≤ (R*L)^2 ∧
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ
      (fun n => (vaughanTypeICoeff A A n : ℂ)) 0 (A*A) s‖^2) ≤ (R*L^2)^2 := by
  intro L R
  have hA₁ : (1 : ℝ)≤A := by exact_mod_cast hA
  have hAA : (A : ℝ)≤((A*A : ℕ) : ℝ) := by push_cast; exact le_mul_of_one_le_right (Nat.cast_nonneg _) hA₁
  have hx := hA₁.trans (hAA.trans hAx)
  have hL : 1≤L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL₀ := zero_le_one.trans hL
  have hLsq : L≤L^2 := by rw [sq]; exact le_mul_of_one_le_right hL₀ hL
  have hlogA : Real.log A ≤ Real.log x := Real.log_le_log (zero_lt_one.trans_le hA₁) (hAA.trans hAx)
  have hlogAA : Real.log ((A*A : ℕ) : ℝ) ≤ Real.log x :=
    Real.log_le_log ((zero_lt_one.trans_le hA₁).trans_le hAA) hAx
  have hcost : (q : ℝ)+((A*A : ℕ) : ℝ) ≤ R^2 := by
    dsimp only [R]
    push_cast
    nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) q), mul_nonneg (Real.sqrt_nonneg (q : ℝ)) (Nat.cast_nonneg (α := ℝ) A)]
  have hcost₁ : (q : ℝ)+A ≤ R^2 := (add_le_add_right hAA _).trans hcost
  have hΛ := (fixed_modulus_vonMangoldt_polynomial_moments (q := q) hA hs).1
  have hμ := (fixed_modulus_mobius_polynomial_moments (q := q) A hs).1
  have hI := typeI_critical_polynomial_energy (q := q) A A hs
  have hfour : Real.log 4≤3 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)]
  have hΛlog : Real.log A*(Real.log A+Real.log 4+8) ≤ (4*L)^2 := by
    calc
      _ ≤ L*(16*L) := mul_le_mul (by dsimp [L]; linarith) (by dsimp only [L] at *; linarith only [hlogA,hfour,hL])
        (by positivity [Real.log_natCast_nonneg A, Real.log_nonneg (show (1 : ℝ)≤4 by norm_num)]) hL₀
      _ = _ := by ring
  have hIlog : (Real.log ((A*A : ℕ) : ℝ))^2 * (1+Real.log ((A*A : ℕ) : ℝ)) ≤ (L^2)^2 := by
    rw [sq (L^2)]
    exact mul_le_mul (pow_le_pow_left₀ (Real.log_natCast_nonneg _) (by dsimp [L]; linarith) 2)
      ((add_le_add_right hlogAA 1).trans hLsq) (by positivity) (sq_nonneg _)
  refine ⟨?_,?_,?_⟩
  · rw [show (4*R*L)^2=R^2*(4*L)^2 by ring]
    simp_rw [intervalCharacterPolynomial_zero]
    exact hΛ.trans (mul_le_mul hcost₁ hΛlog (by positivity [Real.log_nonneg (show (1 : ℝ)≤4 by norm_num)]) (sq_nonneg _))
  · rw [mul_pow]
    simp_rw [intervalCharacterPolynomial_zero]
    exact hμ.trans (mul_le_mul hcost₁ ((add_le_add_right hlogA 1).trans hLsq) (by positivity) (sq_nonneg _))
  · rw [mul_pow]
    exact hI.trans (mul_le_mul hcost hIlog (by positivity) (sq_nonneg _))

end AnalyticNumberTheory.ExponentialSums
