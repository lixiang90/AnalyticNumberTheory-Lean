import AnalyticNumberTheory.AnalyticTools.Gamma.StirlingExpansion

/-! # Sectorial errors in the all-order Stirling expansions -/

noncomputable section

open Complex Finset
open scoped Nat
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AnalyticTools.Gamma

private lemma even_kernel_bound (m : ℕ) (u : ℝ) :
    |bernoulliKernel (2*m+2) u| ≤ |bernoulliKernel (2*m+2) 0| := by
  simpa only [Nat.mul_succ] using abs_bernoulliKernel_even_le (Nat.succ_pos m) u

/-- After the first `m` nonzero terms, the error in log gamma is bounded by
the modulus of the next term times an explicit factor depending on the argument. -/
theorem norm_stirlingRemainder_sub_expansion_le (m : ℕ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    ‖stirlingRemainder s - ∑ n ∈ range (2*m), (stirlingCoefficient n : ℂ)/s^(n+1)‖ ≤
      |stirlingCoefficient (2*m)| / ‖s‖^(2*m+1) * (1 + (Real.cos (s.arg/2)^(2*m+2))⁻¹) := by
  let n := 2*m
  let c := Real.cos (s.arg/2)
  let b := |bernoulliKernel (n+2) 0|
  have hc : 0 < c := cos_half_arg_pos_of_mem_slitPlane hs
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  have hI := norm_stirlingBernoulliIntegral_le (j := n+2) (Nat.succ_pos n) hs
    (abs_nonneg (bernoulliKernel (n+2) 0)) (even_kernel_bound m)
  have H := stirlingRemainder_expansion n hs
  rw [sum_range_succ] at H
  have hre : stirlingRemainder s - ∑ i ∈ range n, (stirlingCoefficient i : ℂ)/s^(i+1) =
      (stirlingCoefficient n : ℂ)/s^(n+1) - ((n+1)! : ℂ)*stirlingBernoulliIntegral (n+2) (n+2) s := by
    rw [H]; abel
  rw [hre]
  calc
    _ ≤ ‖(stirlingCoefficient n : ℂ)/s^(n+1)‖ + ‖((n+1)! : ℂ)*stirlingBernoulliIntegral (n+2) (n+2) s‖ :=
      norm_sub_le ..
    _ ≤ |stirlingCoefficient n|/‖s‖^(n+1) + ((n+1)! : ℝ) * (b/(c^(n+2)*(n+1 : ℕ)*‖s‖^(n+1))) := by
      simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_natCast]
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg (n+1)!)
    _ = _ := by
      change _ = |stirlingCoefficient n| / ‖s‖^(n+1) * (1+(c^(n+2))⁻¹)
      simp only [stirlingCoefficient, abs_mul, abs_of_nonneg (show 0 ≤ (n.factorial : ℝ) by positivity), Nat.factorial_succ n, Nat.cast_mul, b]
      push_cast
      field_simp [hc.ne', hr.ne']

/-- The parallel sectorial error in the logarithmic derivative has one
extra inverse power and the differentiated Bernoulli coefficient. -/
theorem norm_digamma_sub_expansion_le (m : ℕ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    ‖digamma s - (Complex.log s - 1/(2*s) -
      ∑ n ∈ range (2*m), (n+1 : ℂ)*(stirlingCoefficient n : ℂ)/s^(n+2))‖ ≤
      (2*m+1 : ℕ) * |stirlingCoefficient (2*m)| / ‖s‖^(2*m+2) *
        (1+(Real.cos (s.arg/2)^(2*m+3))⁻¹) := by
  let n := 2*m
  let c := Real.cos (s.arg/2)
  let b := |bernoulliKernel (n+2) 0|
  have hc : 0 < c := cos_half_arg_pos_of_mem_slitPlane hs
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  have hI := norm_stirlingBernoulliIntegral_le (j := n+2) (Nat.succ_pos (n+1)) hs
    (abs_nonneg (bernoulliKernel (n+2) 0)) (even_kernel_bound m)
  have H := digamma_stirling_expansion n hs
  rw [sum_range_succ] at H
  have hre : digamma s - (Complex.log s - 1/(2*s) -
      ∑ i ∈ range n, (i+1 : ℂ)*(stirlingCoefficient i : ℂ)/s^(i+2)) =
      ((n+2)! : ℂ)*stirlingBernoulliIntegral (n+2) (n+3) s -
        (n+1 : ℂ)*(stirlingCoefficient n : ℂ)/s^(n+2) := by rw [H]; abel
  rw [hre, norm_sub_rev]
  calc
    _ ≤ ‖(n+1 : ℂ)*(stirlingCoefficient n : ℂ)/s^(n+2)‖ +
        ‖((n+2)! : ℂ)*stirlingBernoulliIntegral (n+2) (n+3) s‖ := norm_sub_le ..
    _ ≤ (n+1 : ℕ) * |stirlingCoefficient n|/‖s‖^(n+2) +
        ((n+2)! : ℝ) * (b/(c^(n+3)*(n+2 : ℕ)*‖s‖^(n+2))) := by
      rw [← Nat.cast_succ (R := ℂ)]
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg (n+2)!)
    _ = _ := by
      change _ = (n+1 : ℕ) * |stirlingCoefficient n| / ‖s‖^(n+2) * (1+(c^(n+3))⁻¹)
      simp only [stirlingCoefficient, abs_mul, abs_of_nonneg (show 0 ≤ (n.factorial : ℝ) by positivity), Nat.factorial_succ (n+1),
        Nat.factorial_succ n, Nat.cast_mul, b]
      push_cast
      field_simp [hc.ne', hr.ne']
      ring

end AnalyticNumberTheory.AnalyticTools.Gamma
