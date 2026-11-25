import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary
import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterExpansion
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-! # Logarithmic smoothing and the character expansion of rational prime sums -/

noncomputable section

open Complex Finset MeasureTheory Set
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.ExponentialSums

/-- The first logarithmic mean of a von Mangoldt sum twisted by a Dirichlet character. -/
def logSmoothedPsiChar {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  logWeightedSum (fun n => χ n * (Λ n : ℂ)) x

/-- The first logarithmic mean of the linear prime exponential sum. -/
def logSmoothedPrimeExpSum (x α : ℝ) : ℂ :=
  logWeightedSum (fun n => (Λ n : ℂ) * AdditiveNumberTheory.e (α*n)) x

/-- At every positive cutoff the logarithmically weighted character sum equals
the absolutely convergent Perron integral of the negative logarithmic derivative. -/
theorem logSmoothedPsiChar_eq_logDeriv_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    logSmoothedPsiChar χ x =
      (∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ)+t*I) /
        DirichletCharacter.LFunction χ ((σ : ℂ)+t*I)) *
        (x : ℂ)^((σ : ℂ)+t*I) / (((σ : ℂ)+t*I)^2))/(2*Real.pi) := by
  rw [logSmoothedPsiChar, logWeightedSum_eq_perron hx (zero_lt_one.trans hσ)
    (neg_logDeriv_LFunction_eq_LSeries χ (s := (σ : ℂ)) hσ).1]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  dsimp only
  rw [← (neg_logDeriv_LFunction_eq_LSeries χ (s := (σ : ℂ)+t*I) (by simpa using hσ)).2]

private lemma log_weight_bound {x C : ℝ} (hx : 1 ≤ x) {b : ℕ → ℂ}
    (hb : ∀ t ∈ Set.Icc 1 x, ‖coeffPartialSum b ⌊t⌋₊‖ ≤ C*Real.log t) :
    ‖logWeightedSum b x‖ ≤ C*(Real.log x)^2/2 := by
  have hp {t : ℝ} (ht : t ∈ uIcc 1 x) : 0 < t := by
    rw [uIcc_of_le hx] at ht
    exact zero_lt_one.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => Real.log t / t) (uIcc 1 x) :=
    (Real.continuousOn_log.mono fun _ ht => (hp ht).ne').div continuousOn_id (fun _ ht => (hp ht).ne')
  have hdiff (t : ℝ) (ht : t ∈ uIcc 1 x) :
      HasDerivAt (fun v : ℝ => (Real.log v)^2/2) (Real.log t/t) t := by
    convert ((Real.hasDerivAt_log (hp ht).ne').pow 2).div_const 2 using 1
    ring
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff hc.intervalIntegrable
  rw [logWeightedSum_eq_integral hx]
  calc
    _ ≤ ∫ t : ℝ in 1..x, C*(Real.log t/t) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hx _ (hc.intervalIntegrable.const_mul C)
      apply ae_of_all _
      intro t ht
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans ht.1.le), ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hb t ⟨ht.1.le,ht.2⟩) (zero_le_one.trans ht.1.le)
    _ = _ := by rw [intervalIntegral.integral_const_mul, hI, Real.log_one]; ring

/-- The Gauss-weighted character expansion of the logarithmically smoothed
prime sum. Prime powers whose base divides the modulus contribute at most
`log q · (log x)²/(2 log 2)`. The numerator need not be reduced. -/
theorem norm_logSmoothedPrimeExpSum_sub_characters {q : ℕ} [NeZero q] (a : ℕ)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖logSmoothedPrimeExpSum x ((a : ℝ)/q) -
      ∑ χ : DirichletCharacter ℂ q, rationalCharacterCoefficient χ a * logSmoothedPsiChar χ x‖ ≤
      (Real.log q/Real.log 2)*(Real.log x)^2/2 := by
  let c := fun n : ℕ => (Λ n : ℂ) * AdditiveNumberTheory.e (((a : ℝ)/q)*n)
  let d := fun (χ : DirichletCharacter ℂ q) (n : ℕ) => χ n*(Λ n : ℂ)
  let w := fun χ : DirichletCharacter ℂ q => rationalCharacterCoefficient χ a
  let b := fun n : ℕ => c n - ∑ χ : DirichletCharacter ℂ q, w χ * d χ n
  have sum_b (S : Finset ℕ) (v : ℕ → ℂ) :
      ∑ n ∈ S, b n*v n = ∑ n ∈ S, c n*v n - ∑ χ, w χ * ∑ n ∈ S, d χ n*v n := by
    simp only [b, sub_mul, sum_sub_distrib, sum_mul, mul_assoc]
    rw [sum_comm (s := S)]
    simp only [mul_sum]
  have hb (t : ℝ) (ht : 1 ≤ t) : ‖coeffPartialSum b ⌊t⌋₊‖ ≤ (Real.log q/Real.log 2)*Real.log t := by
    have he := sum_b (Icc 1 ⌊t⌋₊) (fun _ => 1)
    simp only [mul_one] at he
    rw [coeffPartialSum, he]
    exact norm_primeExpSum_sub_character_expansion ht a
  have H := log_weight_bound hx (b := b) (fun t ht => hb t ht.1)
  rw [logWeightedSum, sum_b] at H
  exact H

/-- Finite differences of the smoothed exponential sums recover the sharp
prime sum up to the von Mangoldt mass of the short interval. -/
theorem norm_logSmoothedPrimeExpSum_difference {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (α : ℝ) :
    ‖logSmoothedPrimeExpSum y α - logSmoothedPrimeExpSum x α -
      primeExpSum x α * (Real.log (y/x) : ℂ)‖ ≤
      (Chebyshev.psi y - Chebyshev.psi x) * Real.log (y/x) := by
  let a := fun n : ℕ => (Λ n : ℂ) * AdditiveNumberTheory.e (α*n)
  have hmass (t : ℝ) : (∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n) = Chebyshev.psi t := by
    rw [psi_eq_sum_Icc, ← Icc_add_one_left_eq_Ioc, zero_add]
  have hsplit := sum_Ioc_consecutive (fun n : ℕ => Λ n) (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxy)
  rw [hmass, hmass] at hsplit
  have hw (n : ℕ) : ‖a n‖ = Λ n := by
    simp [a, AdditiveNumberTheory.norm_e, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have H := norm_logWeightedSum_sub_sub_le a hx hxy
  have hcoeff : coeffPartialSum a ⌊x⌋₊ = primeExpSum x α := rfl
  simpa only [hw, hcoeff, eq_sub_of_add_eq' hsplit, logSmoothedPrimeExpSum, a] using H

end AnalyticNumberTheory.ExponentialSums
