import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The principal exponential integral

We use the analytic continuation of the real positive-axis normalization
Ei(x) = γ + log x + ∑ xⁿ/(n n!). The power-series remainder is entire.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- The entire remainder of the principal exponential integral after subtracting γ and log z. -/
def exponentialIntegralRemainder (z : ℂ) : ℂ :=
  ∑' n : ℕ, z^(n+1) / ((n+1 : ℂ)*((n+1).factorial : ℂ))

/-- The principal exponential integral. Its domain of holomorphy is the slit plane. -/
def principalExponentialIntegral (z : ℂ) : ℂ :=
  (Real.eulerMascheroniConstant : ℂ) + Complex.log z + exponentialIntegralRemainder z

/-- The defining series of the entire remainder converges absolutely at every complex argument. -/
theorem summable_exponentialIntegralRemainder (z : ℂ) :
    Summable (fun n : ℕ => z^(n+1)/((n+1 : ℂ)*((n+1).factorial : ℂ))) := by
  have he : Summable (fun n : ℕ => ‖z‖^n/(n.factorial : ℝ)) := (NormedSpace.expSeries_div_hasSum_exp ‖z‖).summable
  have hs := (summable_nat_add_iff 1).mpr he
  apply Summable.of_norm_bounded hs
  intro n
  rw [norm_div,norm_pow,norm_mul,←Nat.cast_add_one,Complex.norm_natCast,Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (show (1:ℝ) ≤ ((n+1 : ℕ):ℝ) by exact_mod_cast Nat.succ_pos n) (Nat.cast_nonneg (n+1).factorial)

/-- Termwise derivative of the entire remainder, including at the origin. -/
theorem hasDerivAt_exponentialIntegralRemainder (z : ℂ) :
    HasDerivAt exponentialIntegralRemainder (∑' n : ℕ, z^n/((n+1).factorial : ℂ)) z := by
  let R := ‖z‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : Summable (fun n : ℕ => R^n/(n.factorial : ℝ)) := (NormedSpace.expSeries_div_hasSum_exp R).summable
  apply hasDerivAt_tsum_of_isPreconnected hs (Metric.isOpen_ball (x := (0:ℂ)) (ε := R))
    (convex_ball (0:ℂ) R).isPreconnected
    (g := fun (n : ℕ) (y : ℂ) => y^(n+1)/((n+1 : ℂ)*((n+1).factorial : ℂ)))
    (g' := fun (n : ℕ) (y : ℂ) => y^n/((n+1).factorial : ℂ)) _ _ (Metric.mem_ball_self hR)
    (summable_exponentialIntegralRemainder 0) (by simp [R])
  · intro n y _
    apply (((hasDerivAt_id y).pow (n+1)).div_const _).congr_deriv
    simp only [id_eq,Nat.add_one_sub_one,Nat.cast_add_one,mul_one]
    field_simp [show (n:ℂ)+1 ≠ 0 by exact_mod_cast (Nat.succ_ne_zero n)]
  · intro n y hy
    rw [norm_div,norm_pow,Complex.norm_natCast]
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Metric.mem_ball,dist_zero_right] using (Metric.mem_ball.mp hy).le) n) (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)

private theorem mul_tsum_exp_tail (z : ℂ) :
    z*(∑' n : ℕ, z^n/((n+1).factorial : ℂ)) = Complex.exp z - 1 := by
  have hs : HasSum (fun n : ℕ => z^n/(n.factorial : ℂ)) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have h := hs.summable.sum_add_tsum_nat_add 1
  rw [hs.tsum_eq] at h
  simp only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at h
  rw [←tsum_mul_left]
  have he (n : ℕ) : z*(z^n/((n+1).factorial : ℂ)) = z^(n+1)/((n+1).factorial : ℂ) := by rw [pow_succ]; ring
  simp_rw [he]
  linear_combination h

/-- The entire remainder vanishes at the origin. -/
@[simp]
theorem exponentialIntegralRemainder_zero : exponentialIntegralRemainder 0 = 0 := by simp [exponentialIntegralRemainder]

/-- Away from zero the derivative series sums to the divided exponential difference. -/
theorem hasDerivAt_exponentialIntegralRemainder_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt exponentialIntegralRemainder ((Complex.exp z-1)/z) z := by
  apply (hasDerivAt_exponentialIntegralRemainder z).congr_deriv
  apply (eq_div_iff hz).mpr
  rw [mul_comm, mul_tsum_exp_tail]

/-- The derivative of the principal exponential integral is exp(z)/z throughout the slit plane. -/
theorem hasDerivAt_principalExponentialIntegral {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt principalExponentialIntegral (Complex.exp z/z) z := by
  have h := (((Complex.hasDerivAt_log hz).const_add (Real.eulerMascheroniConstant : ℂ))).add
    (hasDerivAt_exponentialIntegralRemainder z)
  apply h.congr_deriv
  have hz₀ := Complex.slitPlane_ne_zero hz
  apply (eq_div_iff hz₀).mpr
  rw [add_mul,inv_mul_cancel₀ hz₀,mul_comm _ z,mul_tsum_exp_tail]
  ring

end AnalyticNumberTheory.AnalyticTools
