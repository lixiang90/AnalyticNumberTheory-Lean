import AnalyticNumberTheory.DivisorProblems.OrderedDivisorCounts
import AnalyticNumberTheory.DirichletSeries.DivisorConvolutionMeans
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Ordinary and harmonic moments of the divisor function

Truncating a divisor convolution on a hyperbola increases the harmonic
bound by at most one harmonic sum. For the ordinary sum its final
factor counts multiples and saves one power of the logarithm.
-/

open Finset Real ArithmeticFunction
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DivisorProblems

private lemma sum_divisor_transform_harmonic_le (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (∑ d ∈ n.divisors, f d)/(n : ℝ)) ≤
      (∑ d ∈ Icc 1 N, f d/d)*(1+Real.log N) := by
  rw [sum_divisor_sum_div_eq_tsum_harmonic, tsum_eq_sum (s := Icc 1 N) ?_, sum_mul]
  · apply sum_le_sum
    intro d hd
    have hd₁ := (mem_Icc.mp hd).1
    have hdN := (mem_Icc.mp hd).2
    have hpos : 0 < N/d := Nat.div_pos hdN hd₁
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (hf d) (Nat.cast_nonneg _))
    exact (harmonic_le_one_add_log (N/d)).trans (add_le_add_right
      (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.div_le_self N d)) 1)
  · intro d hd
    by_cases hz : d=0
    · simp [hz]
    have h : N<d := by simp only [mem_Icc, not_and_or, not_le] at hd; omega
    simp [Nat.div_eq_of_lt h]

/-- Harmonic mass of r-fold ordered factorizations, including order zero
and the empty interval. -/
theorem sum_orderedDivisorCount_div_le (r N : ℕ) :
    (∑ n ∈ Icc 1 N, (orderedDivisorCount r n : ℝ)/n) ≤ (1+Real.log N)^r := by
  induction r with
  | zero =>
    by_cases h : 1 ≤ N
    · simp [orderedDivisorCount, ArithmeticFunction.one_apply, apply_ite, ite_div, h]
    · have : N=0 := by omega
      simp [this]
  | succ r ih =>
    simp_rw [orderedDivisorCount_succ, Nat.cast_sum]
    exact (sum_divisor_transform_harmonic_le _ (fun _ => Nat.cast_nonneg _) N).trans
      ((mul_le_mul_of_nonneg_right ih (by positivity)).trans_eq (pow_succ _ _).symm)

/-- Ordinary mass of ordered factorizations into r+1 factors. -/
theorem sum_orderedDivisorCount_succ_le (r N : ℕ) :
    (∑ n ∈ Icc 1 N, (orderedDivisorCount (r+1) n : ℝ)) ≤ (N : ℝ)*(1+Real.log N)^r := by
  simp_rw [orderedDivisorCount_succ, Nat.cast_sum]
  rw [sum_divisor_sum_eq_weighted_floor]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ)*((orderedDivisorCount r d : ℝ)/d) := by
      apply sum_le_sum
      intro d hd
      have hpos : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have h : ((N/d : ℕ) : ℝ) ≤ (N : ℝ)/d := (le_div_iff₀ hpos).mpr (by exact_mod_cast Nat.div_mul_le_self N d)
      exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (by ring)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_orderedDivisorCount_div_le r N) (Nat.cast_nonneg _)

/-- The harmonic k-th moment of the ordinary divisor count is at most
`(1+log N)^(2^k)`, with constant one for every nonnegative integer k. -/
theorem sum_card_divisors_pow_div_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)^k/n) ≤ (1+Real.log N)^(2^k) := by
  apply le_trans _ (sum_orderedDivisorCount_div_le (2^k) N)
  apply sum_le_sum
  intro n hn
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_divisors_pow_le_ordered k (mem_Icc.mp hn).1) (Nat.cast_nonneg _)

/-- The ordinary k-th moment saves one log compared with its harmonic counterpart. -/
theorem sum_card_divisors_pow_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)^k) ≤ (N : ℝ)*(1+Real.log N)^(2^k-1) := by
  have hs : 2^k-1+1 = 2^k := Nat.sub_add_cancel (Nat.one_le_pow k 2 (by decide))
  apply le_trans _ (sum_orderedDivisorCount_succ_le (2^k-1) N)
  rw [hs]
  exact sum_le_sum fun n hn => by exact_mod_cast card_divisors_pow_le_ordered k (mem_Icc.mp hn).1

end AnalyticNumberTheory.DivisorProblems
