import AnalyticNumberTheory.RiemannZeta.CenteredPartialFractions

/-! # Elementary bounds for the negative even zeros -/

noncomputable section

namespace AnalyticNumberTheory.RiemannZeta

/-- The real part of the nth trivial zero, starting with −2. -/
theorem re_trivialZetaZero (n : ℕ) : (trivialZetaZero n).re = -2*((n:ℝ)+1) := by
  simp [trivialZetaZero,Complex.mul_re]

/-- Every negative even zero is at least one unit from the origin. -/
theorem one_le_norm_trivialZetaZero (n : ℕ) : 1 ≤ ‖trivialZetaZero n‖ := by
  have H := Complex.abs_re_le_norm (trivialZetaZero n)
  rw [re_trivialZetaZero,abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) n])] at H
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Past logarithmic argument one the exponential from the nth trivial zero
is at most 2 to the power −(n+1). -/
theorem exp_re_trivialZetaZero_le_half_pow (n : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    Real.exp ((trivialZetaZero n).re*v) ≤ (1/2:ℝ)^(n+1) := by
  have he : Real.exp (-2*v) ≤ 1/2 := by
    rw [show -2*v = -(2*v) by ring,Real.exp_neg,inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos (by linarith [Real.add_one_le_exp (2*v)])
  rw [re_trivialZetaZero,show -2*((n:ℝ)+1)*v = ((n+1:ℕ):ℝ)*(-2*v) by push_cast; ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he _

end AnalyticNumberTheory.RiemannZeta
