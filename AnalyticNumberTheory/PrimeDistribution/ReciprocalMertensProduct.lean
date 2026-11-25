import AnalyticNumberTheory.PrimeDistribution.Chebyshev

/-! # A uniform upper bound for the reciprocal Mertens product -/

noncomputable section
open Finset Real

namespace AnalyticNumberTheory.PrimeDistribution

/-- The reciprocal Mertens product over p ≤ y is at most C log y for every
real y ≥ 2. An admissible C follows from the logarithmic form of Mertens' theorem. -/
theorem reciprocal_mertens_product_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {y : ℝ}, 2 ≤ y →
      (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1-(p : ℝ)⁻¹)⁻¹) ≤ C*Real.log y := by
  let B := (2*mertensOneBound+1)/Real.log 2
  refine ⟨Real.exp (Real.eulerMascheroniConstant+B), Real.exp_pos _, ?_⟩
  intro y hy
  let P := ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1-(p : ℝ)⁻¹)
  have hp : 0 < P := prod_pos fun p hp => sub_pos.mpr (inv_lt_one_of_one_lt₀
    (show (1 : ℝ) < p by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt))
  have hylog := Real.log_pos (one_lt_two.trans_le hy)
  have hB : (2*mertensOneBound+1)/Real.log y ≤ B := div_le_div_of_nonneg_left
    (by positivity [mertensOneBound_pos]) (Real.log_pos one_lt_two) (Real.log_le_log (by norm_num) hy)
  have h := (abs_le.mp (abs_log_mertens_three_sub_le hy)).1
  change -((2*mertensOneBound+1)/Real.log y) ≤ Real.log P-(-Real.log (Real.log y)-Real.eulerMascheroniConstant) at h
  have he : -Real.log P ≤ Real.eulerMascheroniConstant+B+Real.log (Real.log y) := by linarith only [h,hB]
  rw [prod_inv_distrib]
  change P⁻¹ ≤ _
  simpa only [Real.exp_neg, Real.exp_log hp, Real.exp_add (Real.eulerMascheroniConstant+B),
    Real.exp_log hylog] using Real.exp_le_exp.mpr he

end AnalyticNumberTheory.PrimeDistribution
