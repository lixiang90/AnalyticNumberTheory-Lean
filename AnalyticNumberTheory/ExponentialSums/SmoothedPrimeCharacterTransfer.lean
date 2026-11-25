import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeSums

/-! # Chebyshev and Gauss-sum bounds under logarithmic smoothing -/

noncomputable section
open Complex Finset Real MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.PrimeDistribution
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- Chebyshev's elementary bound integrates to (log 4 + 4)(x−1),
uniformly in the modulus and the character, including the principal one. -/
theorem norm_logSmoothedPsiChar_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖logSmoothedPsiChar χ x‖ ≤ (Real.log 4+4)*(x-1) := by
  rw [logSmoothedPsiChar, logWeightedSum_eq_integral hx]
  calc
    _ ≤ ∫ _t : ℝ in 1..x, (Real.log 4+4) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hx _ intervalIntegrable_const
      apply ae_of_all _
      intro t ht
      have ht₀ := zero_lt_one.trans ht.1
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht₀.le, div_le_iff₀ ht₀]
      exact norm_psiChar_le_const_mul_self ht₀.le χ
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

/-- Replacing the phase by its negative conjugates the logarithmically
weighted prime sum. The cutoff may be any real number. -/
theorem star_logSmoothedPrimeExpSum (x α : ℝ) :
    star (logSmoothedPrimeExpSum x α) = logSmoothedPrimeExpSum x (-α) := by
  simp only [logSmoothedPrimeExpSum, logWeightedSum, star_sum, star_mul', AdditiveNumberTheory.star_e,
    neg_mul, Complex.star_def, Complex.conj_ofReal]

/-- Transfer the full character mean to a reduced rational phase, allowing
either sign of the numerator. The error counts powers of primes dividing q. -/
theorem norm_logSmoothedPrimeExpSum_le_character_mean {q : ℕ} [NeZero q] {a : ℤ}
    (ha : a.natAbs.Coprime q) {x : ℝ} (hx : 1 ≤ x) :
    ‖logSmoothedPrimeExpSum x ((a : ℝ)/q)‖ ≤ (Real.log q/Real.log 2)*(Real.log x)^2/2 +
      (Real.sqrt q/q.totient) * ∑ χ : DirichletCharacter ℂ q, ‖logSmoothedPsiChar χ x‖ := by
  let S := ∑ χ : DirichletCharacter ℂ q, rationalCharacterCoefficient χ a.natAbs * logSmoothedPsiChar χ x
  have hS : ‖S‖ ≤ (Real.sqrt q/q.totient) * ∑ χ : DirichletCharacter ℂ q, ‖logSmoothedPsiChar χ x‖ := by
    rw [mul_sum]
    apply (norm_sum_le ..).trans (sum_le_sum ?_)
    intro χ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_rationalCharacterCoefficient_le_conductor χ ha).trans
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (Nat.cast_le.mpr
      (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level))) (Nat.cast_nonneg _)
  have h := (norm_le_norm_sub_add (logSmoothedPrimeExpSum x ((a.natAbs : ℝ)/q)) S).trans
    (add_le_add (norm_logSmoothedPrimeExpSum_sub_characters a.natAbs hx) hS)
  have habs : (a.natAbs : ℝ)/q = |(a : ℝ)/q| := by
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) by positivity)]
    apply congrArg (fun t : ℝ => t/q)
    simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun n : ℤ => (n : ℝ)) (Int.natCast_natAbs a)
  rw [habs] at h
  rcases le_or_gt 0 ((a : ℝ)/q) with hpos | hneg
  · rwa [abs_of_nonneg hpos] at h
  · rwa [abs_of_neg hneg, ← star_logSmoothedPrimeExpSum, norm_star] at h

end AnalyticNumberTheory.ExponentialSums
