import AnalyticNumberTheory.ExponentialSums.SmoothedRationalPrimeSums
import AnalyticNumberTheory.PrimeDistribution.ReciprocalTotient

/-! # The modulus logarithm in the smoothed prime contour bound -/

open Real
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

/-- Keeping the totient ratio until the last step leaves just log log(10q)
outside the contour scales with four and three powers of 1+log x. -/
theorem logSmoothedPrimeExpSum_rational_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x : ℝ},
      a.natAbs.Coprime q → (q : ℝ) ≤ x →
      ‖logSmoothedPrimeExpSum x ((a : ℝ)/q)‖ ≤ C*Real.log (Real.log (10*q))*
        (x/Real.sqrt q*(1+Real.log x)^4+x^(3/4 : ℝ)*(q : ℝ)^(1/4 : ℝ)*(1+Real.log x)^3) := by
  obtain ⟨A,hA,H⟩ := logSmoothedPrimeExpSum_rational_totient
  obtain ⟨B,hB,F⟩ := div_totient_le_loglog
  refine ⟨A*B, by positivity,?_⟩
  intro q _ a x ha hqx
  have hx : 1 ≤ x := (show (1 : ℝ) ≤ q by exact_mod_cast NeZero.pos q).trans hqx
  have hx₀ := zero_le_one.trans hx
  have hL : 0 ≤ 1+Real.log x := by linarith only [Real.log_nonneg hx]
  apply (H ha hqx).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (mul_le_mul_of_nonneg_left (F (NeZero.pos q)) hA.le).trans_eq (by ring)

end AnalyticNumberTheory.ExponentialSums
