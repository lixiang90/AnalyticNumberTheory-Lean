import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # The reciprocal totient and the number of distinct prime factors -/

open Finset Real

namespace AnalyticNumberTheory.PrimeDistribution

/-- Real form of Euler's product for the inverse totient ratio, including n=1. -/
theorem div_totient_eq_reciprocal_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (1-(p : ℝ)⁻¹)⁻¹ := by
  have hφ : (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1-(p : ℝ)⁻¹) := by
    simpa only [map_mul, map_prod, map_sub, map_one, map_inv₀, map_natCast] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors n)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hφ, prod_inv_distrib, div_mul_eq_div_div, div_self hn', one_div]

/-- Each distinct prime divisor costs at least log 2 in log n. -/
theorem primeFactors_card_mul_log_two_le {n : ℕ} (hn : 0 < n) :
    (n.primeFactors.card : ℝ)*Real.log 2 ≤ Real.log n := by
  have hpow : 2^n.primeFactors.card ≤ n := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        rw [← Finset.prod_const (2 : ℕ)]
        exact Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ _ := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)

end AnalyticNumberTheory.PrimeDistribution
