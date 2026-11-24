import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Dyadic decomposition and reciprocal-square-root sums
-/

open Finset
namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- The integer points in `(2^j, 2^(j+1)]` up to the cutoff `N`. -/
def dyadicBlock (N j : ℕ) : Finset ℕ :=
  Ioc (2 ^ j) (min N (2 ^ (j + 1)))

/-- Split a sum over positive integers into the first summand and half-open dyadic blocks.
The last block can be incomplete, and blocks above the cutoff are empty. -/
theorem sum_Icc_eq_dyadic_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {N K : ℕ} (hN : 1 ≤ N) (hK : N ≤ 2 ^ K) :
    ∑ n ∈ Icc 1 N, f n = f 1 + ∑ j ∈ range K, ∑ n ∈ dyadicBlock N j, f n := by
  have hsplit (k : ℕ) :
      ∑ n ∈ Ioc 0 (min N (2 ^ k)), f n =
        f 1 + ∑ j ∈ range k, ∑ n ∈ dyadicBlock N j, f n := by
    induction k with
    | zero => simp [min_eq_right hN, Nat.Ioc_succ_singleton]
    | succ k ih =>
      rw [sum_range_succ, ← add_assoc, ← ih]
      by_cases hk : 2 ^ k ≤ N
      · rw [dyadicBlock, min_eq_right hk]
        exact (sum_Ioc_consecutive f (Nat.zero_le _)
          (le_min hk (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ k)))).symm
      · have hle : N ≤ 2 ^ k := by omega
        have hle' : N ≤ 2 ^ (k + 1) := hle.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))
        simp [dyadicBlock, min_eq_left hle, min_eq_left hle', Ioc_eq_empty_of_le hle]
  simpa only [min_eq_left hK, ← Icc_add_one_left_eq_Ioc, zero_add] using hsplit K

/-- Summing reciprocal square roots up to a finite cutoff. -/
theorem sum_Icc_inv_sqrt_le (K : ℕ) :
    ∑ n ∈ Icc 1 K, (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * Real.sqrt K := by
  rw [show Icc 1 K = Ioc 0 K by rw [← Icc_add_one_left_eq_Ioc, zero_add]]
  induction K with
  | zero => simp
  | succ k ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _)]
    have hs : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hstep : (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt k) := by
      rw [← one_div, div_le_iff₀ hs]
      have hnew := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))
      have hold := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      push_cast at *
      nlinarith only [hnew, hold, sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k)]
    linarith only [ih, hstep]

end AnalyticNumberTheory.AnalyticTools.Summation
