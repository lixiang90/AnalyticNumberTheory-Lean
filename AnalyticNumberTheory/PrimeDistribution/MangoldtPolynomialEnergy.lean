import AnalyticNumberTheory.DirichletLFunctions.FactorPairEnergy
import AnalyticNumberTheory.PrimeDistribution.Chebyshev

/-! # Coefficient energy of the von Mangoldt polynomial and its square -/

open Finset Complex Real
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

private lemma mangoldt_le_log_cutoff {N n : ℕ} (hn : n ∈ Icc 1 N) : Λ n ≤ Real.log N :=
  ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ)<n) (Nat.cast_le.mpr (mem_Icc.mp hn).2))

private lemma mangoldt_harmonic_mass {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, ‖(Λ n : ℂ)‖/(n : ℝ)) ≤ Real.log N+Real.log 4+8 := by
  have hm := (abs_le.mp (abs_sum_vonMangoldt_div_sub_log_le (by exact_mod_cast hN : (1 : ℝ)≤N))).2
  rw [Nat.floor_natCast] at hm
  simp only [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  linarith only [hm]

/-- Mertens' first sum gives a two-logarithm bound for the harmonic
second moment of the von Mangoldt coefficients. -/
theorem vonMangoldt_harmonic_energy {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, ‖(Λ n : ℂ)‖^2/(n : ℝ)) ≤
      Real.log N*(Real.log N+Real.log 4+8) := by
  apply le_trans _ (mul_le_mul_of_nonneg_left (mangoldt_harmonic_mass hN) (Real.log_natCast_nonneg _))
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  simp only [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, sq, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mangoldt_le_log_cutoff hn)
    ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg _)

/-- A single coefficient in the squared von Mangoldt polynomial is bounded
by `log N log k`, using the exact divisor identity for Λ. -/
theorem norm_factorPairWeight_vonMangoldt_le {N k : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N)
    (hk : 0 < k) : ‖factorPairWeight S (fun n => (Λ n : ℂ)) k‖ ≤ Real.log N * Real.log k := by
  let T := (S ×ˢ S).filter (fun p => p.1*p.2=k)
  have hsub : T ⊆ k.divisorsAntidiagonal := fun p hp =>
    Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hp).2, hk.ne'⟩
  calc
    _ ≤ ∑ p ∈ T, ‖(Λ p.1 : ℂ)*(Λ p.2 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ T, Real.log N * Λ p.1 := by
      apply sum_le_sum
      intro p hp
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (mangoldt_le_log_cutoff (hS (mem_product.mp (mem_filter.mp hp).1).2))
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ p ∈ k.divisorsAntidiagonal, Real.log N * Λ p.1 :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => mul_nonneg (Real.log_natCast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by rw [← mul_sum, Nat.sum_divisorsAntidiagonal (f := fun i _ => Λ i), ArithmeticFunction.vonMangoldt_sum]

/-- The squared polynomial has harmonic coefficient energy of order
`(1+log N)^4`. One factor uses the pointwise divisor identity and the
other uses the first, rather than the second, harmonic moment of Λ. -/
theorem vonMangoldt_square_harmonic_energy {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Icc 1 (N^2), ‖factorPairWeight (Icc 1 N) (fun n => (Λ n : ℂ)) k‖^2/(k : ℝ)) ≤
      (Real.log N * Real.log ((N^2 : ℕ) : ℝ))*(Real.log N+Real.log 4+8)^2 := by
  have hc (k : ℕ) (hk : k ∈ Icc 1 (N^2)) :
      ‖factorPairWeight (Icc 1 N) (fun n => (Λ n : ℂ)) k‖ ≤ Real.log N * Real.log ((N^2 : ℕ) : ℝ) :=
    (norm_factorPairWeight_vonMangoldt_le (Subset.refl _) (mem_Icc.mp hk).1).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hk).1 : (0 : ℝ)<k)
        (Nat.cast_le.mpr (mem_Icc.mp hk).2)) (Real.log_natCast_nonneg _))
  apply (factorPairWeight_harmonic_energy (Subset.refl _) _ (by positivity) hc).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity)
    (mangoldt_harmonic_mass hN) 2) (by positivity)

end AnalyticNumberTheory.PrimeDistribution
