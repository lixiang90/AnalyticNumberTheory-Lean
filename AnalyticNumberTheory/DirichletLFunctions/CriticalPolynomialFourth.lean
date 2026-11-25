import AnalyticNumberTheory.DirichletLFunctions.CriticalPolynomialEnergy
import AnalyticNumberTheory.DirichletLFunctions.CharacterPolynomialSquares
import AnalyticNumberTheory.DivisorProblems.DivisorPowerMeans

/-! # Fourth moments of short character polynomials at a fixed height -/

noncomputable section
open Complex Finset
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DivisorProblems

namespace AnalyticNumberTheory.DirichletLFunctions

/-- The exact fixed-modulus length factor is at most `q+N`. -/
theorem fixed_modulus_length_cost_le {q : ℕ} [NeZero q] (N : ℕ) :
    (q.totient : ℝ)*(1+(N : ℝ)/q) ≤ q+N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    _ ≤ (q : ℝ)*(1+(N : ℝ)/q) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le q)) (by positivity)
    _ = _ := by field_simp

/-- Squaring the polynomial on any subset of `[1,N]` replaces its coefficients
by their restricted Dirichlet convolution. The resulting critical-line
energy is uniform in the ordinate and uses all characters of one modulus. -/
theorem critical_polynomial_fourth_energy {q N : ℕ} [NeZero q] (a : ℕ → ℂ)
    {S : Finset ℕ} (hS : S ⊆ Icc 1 N) {s : ℂ} (hs : s.re = 1/2) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n*χ n*(n : ℂ)^(-s)‖^4) ≤
      q.totient*(1+((N^2 : ℕ) : ℝ)/q)*∑ n ∈ Icc 1 (N^2), ‖factorPairWeight S a n‖^2/(n : ℝ) := by
  have he (χ : DirichletCharacter ℂ q) :
      ‖∑ n ∈ S, a n*χ n*(n : ℂ)^(-s)‖^4 =
      ‖dirichletPoly (fun n => factorPairWeight S a n * χ n) (N^2) s‖^2 := by
    rw [show (4 : ℕ)=2*2 by decide, pow_mul, ← norm_pow, weighted_characterPolynomial_square χ a S hS]
    rfl
  simp_rw [he]
  exact critical_polynomial_energy _ _ hs

/-- For coefficients of modulus at most one, the fourth moment at each
height is bounded by the fourth power of the harmonic logarithm. -/
theorem bounded_critical_polynomial_fourth {q N : ℕ} [NeZero q] (a : ℕ → ℂ)
    {S : Finset ℕ} (hS : S ⊆ Icc 1 N) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {s : ℂ} (hs : s.re = 1/2) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n*χ n*(n : ℂ)^(-s)‖^4) ≤
      ((q : ℝ)+((N^2 : ℕ) : ℝ))*(1+Real.log ((N^2 : ℕ) : ℝ))^4 := by
  apply (critical_polynomial_fourth_energy a hS hs).trans
  apply mul_le_mul (fixed_modulus_length_cost_le _) _ (sum_nonneg fun _ _ => by positivity) (by positivity)
  apply le_trans _ (sum_card_divisors_pow_div_le 2 (N^2))
  apply sum_le_sum
  intro n hn
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_factorPairWeight_le ha (mem_Icc.mp hn).1) 2)
    (Nat.cast_nonneg _)

end AnalyticNumberTheory.DirichletLFunctions
