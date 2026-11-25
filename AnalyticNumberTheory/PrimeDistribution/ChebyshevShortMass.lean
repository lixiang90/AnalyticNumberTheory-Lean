import AnalyticNumberTheory.PrimeDistribution.Chebyshev

/-! # Elementary Chebyshev mass of a finite real interval -/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.PrimeDistribution

/-- Each integer in (x,y] has von Mangoldt weight at most log y.
The extra 1 in the length handles arbitrary real endpoints. -/
theorem psi_sub_le_length_mul_log {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    Chebyshev.psi y - Chebyshev.psi x ≤ (y-x+1)*Real.log y := by
  have hy := hx.trans hxy
  have hx₀ := zero_le_one.trans hx
  have hy₀ := zero_le_one.trans hy
  have hs (z : ℝ) : (∑ n ∈ Ioc 0 ⌊z⌋₊, Λ n) = Chebyshev.psi z := by
    rw [psi_eq_sum_Icc, ← Icc_add_one_left_eq_Ioc, zero_add]
  have hsplit := sum_Ioc_consecutive (fun n : ℕ => Λ n) (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxy)
  rw [hs,hs] at hsplit
  rw [← eq_sub_of_add_eq' hsplit]
  calc
    _ ≤ ∑ _n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, Real.log y := by
      apply sum_le_sum
      intro n hn
      have hn₁ : x < n := (Nat.floor_lt hx₀).mp (mem_Ioc.mp hn).1
      have hn₂ : (n : ℝ) ≤ y := (Nat.le_floor_iff hy₀).mp (mem_Ioc.mp hn).2
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (hx₀.trans_lt hn₁) hn₂)
    _ ≤ _ := by
      simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub (Nat.floor_mono hxy)]
      exact mul_le_mul_of_nonneg_right (by linarith only [Nat.floor_le hy₀, Nat.lt_floor_add_one x]) (Real.log_nonneg hy)

end AnalyticNumberTheory.PrimeDistribution
