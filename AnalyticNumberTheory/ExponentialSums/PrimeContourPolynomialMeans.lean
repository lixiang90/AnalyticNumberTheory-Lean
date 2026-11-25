import AnalyticNumberTheory.ExponentialSums.VaughanIdentity
import AnalyticNumberTheory.DirichletLFunctions.TailPolynomialEnergy
import AnalyticNumberTheory.PrimeDistribution.FixedModulusPolynomialMoments

/-! # Fixed-modulus polynomial bounds for the two prime contours -/

open Complex Real Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DivisorProblems

namespace AnalyticNumberTheory.ExponentialSums

/-- The short convolution μ≤U * Λ≤V has modulus at most log n. At every
point of the critical line its second moment costs q+UV and three logs. -/
theorem typeI_critical_polynomial_energy {q : ℕ} [NeZero q] (U V : ℕ) {s : ℂ} (hs : s.re=1/2) :
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ
      (fun n => (vaughanTypeICoeff U V n : ℂ)) 0 (U*V) s‖^2) ≤
      ((q : ℝ)+((U*V : ℕ) : ℝ))*((Real.log ((U*V : ℕ) : ℝ))^2*(1+Real.log ((U*V : ℕ) : ℝ))) := by
  let N := U*V
  have coeff (n : ℕ) (hn : n ∈ Icc 1 N) : ‖(vaughanTypeICoeff U V n : ℂ)‖ ≤ Real.log N := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_vaughanTypeICoeff_le_log U V n).trans
      (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ)<n) (Nat.cast_le.mpr (mem_Icc.mp hn).2))
  simp_rw [intervalCharacterPolynomial_zero]
  apply (critical_polynomial_energy_of_bound (q := q) _ coeff hs).trans
  exact mul_le_mul_of_nonneg_right (fixed_modulus_length_cost_le _) (by positivity)

/-- On real part one the long Vaughan factor is supported past U. The
divisor bound supplies a fourth logarithmic power in the coefficient energy. -/
theorem typeII_tail_polynomial_energy {q U : ℕ} [NeZero q] (hU : 1≤U) (Y : ℕ)
    {s : ℂ} (hs : s.re=1) :
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ
      (fun n => (vaughanTypeIICoeff U n : ℂ)) U Y s‖^2) ≤
      ((q : ℝ)/U+ (1+Real.log Y))*(1+Real.log Y)^4 := by
  apply (fixed_modulus_tail_energy hU Y _ hs).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ n ∈ Ioc U Y, (n.divisors.card : ℝ)^2/n := by
      apply sum_le_sum
      intro n _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_vaughanTypeIICoeff_le_divisors U n) 2
    _ ≤ ∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)^2/n :=
      sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.mpr ⟨(Nat.zero_le U).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)
        fun _ _ _ => by positivity
    _ ≤ _ := sum_card_divisors_pow_div_le 2 Y

/-- The von Mangoldt tail on real part one retains Mertens' two-logarithm
bound for its harmonic diagonal. -/
theorem vonMangoldt_tail_polynomial_energy {q V X : ℕ} [NeZero q] (hV : 1≤V) (hX : 1≤X)
    {s : ℂ} (hs : s.re=1) :
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ
      (fun n => (Λ n : ℂ)) V X s‖^2) ≤
      ((q : ℝ)/V+(1+Real.log X))*(Real.log X*(Real.log X+Real.log 4+8)) := by
  apply (fixed_modulus_tail_energy hV X _ hs).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ (vonMangoldt_harmonic_energy hX)
  exact sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.mpr ⟨(Nat.zero_le V).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)
    fun _ _ _ => by positivity

end AnalyticNumberTheory.ExponentialSums
