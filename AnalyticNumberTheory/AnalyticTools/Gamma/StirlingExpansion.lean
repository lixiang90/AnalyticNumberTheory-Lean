import AnalyticNumberTheory.AnalyticTools.Gamma.StirlingRecurrence

/-! # The Stirling expansions of gamma and its logarithmic derivative -/

noncomputable section

open Complex Finset
open scoped Nat
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AnalyticTools.Gamma

/-- Coefficient of `s^(-(n+1))` in the Stirling expansion of log gamma. -/
def stirlingCoefficient (n : ℕ) : ℝ :=
  n.factorial * bernoulliKernel (n+2) 0

/-- The coefficients are Bernoulli numbers divided by two consecutive integers. -/
theorem stirlingCoefficient_eq_bernoulli (n : ℕ) :
    stirlingCoefficient n = (_root_.bernoulli (n+2) : ℝ) / ((n+1 : ℝ)*(n+2)) := by
  have h := bernoulliKernel_intCast (n+2) 0
  simp only [Int.cast_zero] at h
  rw [stirlingCoefficient, h]
  rw [Nat.factorial_succ (n+1), Nat.factorial_succ n]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- The zero coefficients explain why only odd inverse powers enter log gamma. -/
theorem stirlingCoefficient_odd (n : ℕ) : stirlingCoefficient (2*n+1) = 0 := by
  rw [stirlingCoefficient_eq_bernoulli, bernoulli_eq_zero_of_odd
    (show Odd (2*n+1+2) from ⟨n+1, by omega⟩) (by omega)]
  simp

/-- Exact expansion on the slit plane through degree `N+1`, retaining the
absolutely convergent periodic Bernoulli integral as the remainder. -/
theorem stirlingRemainder_expansion (N : ℕ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    stirlingRemainder s =
      (∑ n ∈ range (N+1), (stirlingCoefficient n : ℂ)/s^(n+1)) -
        ((N+1)! : ℂ) * stirlingBernoulliIntegral (N+2) (N+2) s := by
  induction N with
  | zero =>
    have h : bernoulliKernel 2 0 = 1/12 := by simpa using bernoulliKernel_two_natCast 0
    simp [stirlingRemainder, stirlingBernoulliIntegral, stirlingCoefficient, h]
    ring
  | succ N ih =>
    rw [sum_range_succ (n := N+1), ih,
      stirlingBernoulliIntegral_step (j := N+2) (p := N+1) (by omega) (by omega) hs,
      Nat.factorial_succ (N+1)]
    simp only [stirlingCoefficient, Complex.ofReal_mul, Complex.ofReal_natCast]
    push_cast
    ring

/-- The differentiated Stirling remainder has its own exact expansion. It
follows by integration by parts, without differentiating an asymptotic error. -/
theorem deriv_stirlingRemainder_expansion (N : ℕ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    deriv stirlingRemainder s =
      -(∑ n ∈ range (N+1), (n+1 : ℂ) * (stirlingCoefficient n : ℂ)/s^(n+2)) +
        ((N+2)! : ℂ) * stirlingBernoulliIntegral (N+2) (N+3) s := by
  induction N with
  | zero =>
    have h : bernoulliKernel 2 0 = 1/12 := by simpa using bernoulliKernel_two_natCast 0
    rw [(hasDerivAt_stirlingRemainder hs).deriv]
    simp [stirlingBernoulliIntegral, stirlingCoefficient, h]
    ring
  | succ N ih =>
    rw [sum_range_succ (n := N+1), ih,
      stirlingBernoulliIntegral_step (j := N+2) (p := N+2) (by omega) (by omega) hs,
      Nat.factorial_succ (N+2), Nat.factorial_succ (N+1)]
    simp only [stirlingCoefficient, Complex.ofReal_mul, Complex.ofReal_natCast]
    push_cast
    ring

/-- Arbitrary-order Stirling formula for the complex gamma function, with
the holomorphic logarithm in the principal slit plane encoded by the power. -/
theorem complex_gamma_stirling_expansion (N : ℕ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    Complex.Gamma s = (Real.sqrt (2*Real.pi) : ℂ) * s^(s-1/2) *
      Complex.exp (-s + ((∑ n ∈ range (N+1), (stirlingCoefficient n : ℂ)/s^(n+1)) -
        ((N+1)! : ℂ) * stirlingBernoulliIntegral (N+2) (N+2) s)) := by
  rw [complex_gamma_eq_stirling hs, stirlingRemainder_expansion N hs]

/-- Arbitrary-order expansion for the logarithmic derivative of gamma,
including the full Bernoulli integral on the slit plane. -/
theorem digamma_stirling_expansion (N : ℕ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    digamma s = Complex.log s - 1/(2*s) -
      (∑ n ∈ range (N+1), (n+1 : ℂ)*(stirlingCoefficient n : ℂ)/s^(n+2)) +
        ((N+2)! : ℂ) * stirlingBernoulliIntegral (N+2) (N+3) s := by
  rw [digamma_eq_stirling hs, deriv_stirlingRemainder_expansion N hs]
  ring

end AnalyticNumberTheory.AnalyticTools.Gamma
