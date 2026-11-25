import AnalyticNumberTheory.DirichletLFunctions.CriticalPolynomialFourth
import AnalyticNumberTheory.PrimeDistribution.MangoldtPolynomialEnergy
import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector

/-! # Short Möbius and von Mangoldt polynomials on the critical line

The modulus is fixed and the height is arbitrary. The second moments
have length cost q+N, and the fourth moments have length cost q+N².
-/

noncomputable section
open Complex Real Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- Simultaneous second and fourth moments of a finite Möbius mollifier,
uniformly at a single critical-line point. -/
theorem fixed_modulus_mobius_polynomial_moments {q : ℕ} [NeZero q] (N : ℕ)
    {s : ℂ} (hs : s.re = 1/2) :
    let M := fun χ : DirichletCharacter ℂ q => dirichletPoly (fun n => (μ n : ℂ)*χ n) N s
    (∑ χ, ‖M χ‖^2) ≤ ((q : ℝ)+N)*(1+Real.log N) ∧
      (∑ χ, ‖M χ‖^4) ≤ ((q : ℝ)+((N^2 : ℕ) : ℝ))*(1+Real.log ((N^2 : ℕ) : ℝ))^4 := by
  intro M
  have ha (n : ℕ) (_hn : n ∈ Icc 1 N) : ‖(μ n : ℂ)‖ ≤ 1 := norm_moebius_complex_le n
  constructor
  · have h := critical_polynomial_energy_of_bound (q := q) _ ha hs
    simp only [one_pow, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (fixed_modulus_length_cost_le N) (by positivity))
  · exact bounded_critical_polynomial_fourth _ (Subset.refl _) ha hs

/-- Mertens' first sum bounds both moments of the short von Mangoldt
polynomial. They cost two and four powers of the logarithm, respectively. -/
theorem fixed_modulus_vonMangoldt_polynomial_moments {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    {s : ℂ} (hs : s.re = 1/2) :
    let P := fun χ : DirichletCharacter ℂ q => dirichletPoly (fun n => (Λ n : ℂ)*χ n) N s
    let H := Real.log N+Real.log 4+8
    (∑ χ, ‖P χ‖^2) ≤ ((q : ℝ)+N)*(Real.log N*H) ∧
      (∑ χ, ‖P χ‖^4) ≤ ((q : ℝ)+((N^2 : ℕ) : ℝ))*
        ((Real.log N*Real.log ((N^2 : ℕ) : ℝ))*H^2) := by
  intro P H
  constructor
  · apply (critical_polynomial_energy _ _ hs).trans
    exact mul_le_mul (fixed_modulus_length_cost_le _) (vonMangoldt_harmonic_energy hN)
      (sum_nonneg fun _ _ => by positivity) (by positivity)
  · apply (critical_polynomial_fourth_energy _ (Subset.refl _) hs).trans
    exact mul_le_mul (fixed_modulus_length_cost_le _) (vonMangoldt_square_harmonic_energy hN)
      (sum_nonneg fun _ _ => by positivity) (by positivity)

end AnalyticNumberTheory.PrimeDistribution
