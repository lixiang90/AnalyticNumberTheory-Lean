import AnalyticNumberTheory.PrimeDistribution.ConsecutivePrimeGaps
import AnalyticNumberTheory.PrimeDistribution.TriangularExplicitFormula
import Mathlib.NumberTheory.LSeries.WeakPNT

/-!
# Cramér's bound for prime gaps under the Riemann hypothesis

Taking a logarithmic step of order log x / √x in the triangular explicit formula
gives positive prime mass in intervals of length O(√x log x). The contribution
of proper prime powers costs only O(√x).
-/

noncomputable section

open Filter Asymptotics Real
open scoped Topology
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem exp_double_step_le {h : ℝ} (hh : 0 ≤ h) (hsmall : h ≤ 1/2) :
    exp (2*h) ≤ 1+2*exp 1*h := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(2*h))) (Real.exp_pos (2*h)).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at H
  have he := Real.exp_le_exp.mpr (by linarith : 2*h ≤ 1)
  nlinarith only [H,mul_le_mul_of_nonneg_right he hh]

/-- Under RH, a sufficiently large absolute multiple of √x log x as interval
length guarantees at least √x log x of prime logarithmic mass. -/
theorem exists_theta_shortInterval_lower_sqrt_log_of_rh (hRH : RiemannHypothesisProp) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, √x*log x ≤
      Chebyshev.theta (x+K*√x*log x)-Chebyshev.theta x := by
  obtain ⟨C,hC,HC⟩ := exists_lower_bound_triangular_psi_of_rh hRH
  let D := C+3
  let K := 2*exp 1*D
  let A := (log 4+4)*3
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  have hlim : Tendsto (fun u : ℝ => D*u/exp (u/2)) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x := D)).mul
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/2) (by norm_num))
    rw [mul_zero] at H
    apply H.congr'
    filter_upwards with u
    rw [Real.rpow_one,show -(1/2)*u = -(u/2) by ring,Real.exp_neg]
    ring
  have hlogScale : ∀ᶠ u : ℝ in atTop, exp (u/2)*u ≤
      Chebyshev.theta (exp u+K*exp (u/2)*u)-Chebyshev.theta (exp u) := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      eventually_ge_atTop (1:ℝ),eventually_ge_atTop (A*exp 1+4)] with u hsmall hu hlarge
    let E := exp (u/2)
    let h := D*u/E
    let y := exp (u+2*h)
    have hE : 0 < E := Real.exp_pos _
    have hE₁ : 1 ≤ E := Real.one_le_exp_iff.mpr (by linarith)
    have hu₀ : 0 < u := by linarith
    have hh : 0 < h := div_pos (mul_pos hD₀ hu₀) hE
    have hhalf : h ≤ 1/2 := hsmall.le
    have heq : exp u = E*E := by dsimp only [E]; rw [←Real.exp_add]; congr 1; ring
    have hxstep : exp u*h = D*u*E := by rw [heq]; dsimp only [h]; field_simp
    have hlog : log (1/h) ≤ u := by
      apply (Real.log_le_iff_le_exp (by positivity : 0 < 1/h)).mpr
      calc
        _ = E/(D*u) := by dsimp only [h]; rw [one_div,inv_div]
        _ ≤ E := div_le_self hE.le (one_le_mul_of_one_le_of_one_le hD hu)
        _ ≤ exp u := Real.exp_le_exp.mpr (by linarith)
    have hψ : exp u*h ≤ (Chebyshev.psi y-Chebyshev.psi (exp u)) + C*E*log (1/h) + 4*h := by
      apply (mul_le_mul_iff_right₀ hh).mp
      calc
        _ = exp u*h^2 := by ring
        _ ≤ _ := HC hu hh hhalf
        _ = _ := by dsimp only [y,E]; ring
    have hroot : √y ≤ E*exp 1 := by
      rw [show y = exp (u+2*h) from rfl,←Real.exp_half,show (u+2*h)/2 = u/2+h by ring,Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hE.le
    have hpow : Chebyshev.psi y-Chebyshev.theta y ≤ A*(E*exp 1) :=
      (le_abs_self _).trans ((abs_psi_sub_theta_le_mul_sqrt y).trans (mul_le_mul_of_nonneg_left hroot hA))
    have hmass : E*u ≤ Chebyshev.theta y-Chebyshev.theta (exp u) := by
      rw [hxstep] at hψ
      dsimp only [D] at hψ
      nlinarith only [hψ,hpow,Chebyshev.theta_le_psi (exp u),
        mul_le_mul_of_nonneg_left hlog (mul_pos hC hE).le,
        mul_le_mul_of_nonneg_right hlarge hE.le,hE₁,hhalf,
        mul_nonneg hu₀.le hE.le]
    have hy : y ≤ exp u+K*E*u := calc
      y = exp u*exp (2*h) := Real.exp_add ..
      _ ≤ exp u*(1+2*exp 1*h) := mul_le_mul_of_nonneg_left (exp_double_step_le hh.le hhalf) (Real.exp_pos _).le
      _ = exp u + (2*exp 1)*(exp u*h) := by ring
      _ = _ := by rw [hxstep]; dsimp only [K]; ring
    exact hmass.trans (sub_le_sub_right (Chebyshev.theta_mono hy) _)
  filter_upwards [Real.tendsto_log_atTop.eventually hlogScale,eventually_gt_atTop (0:ℝ)] with x hx hx₀
  simpa only [Real.exp_half,Real.exp_log hx₀] using hx

/-- Cramér's conditional short-interval theorem. For every sufficiently large
real x there is a prime strictly above x and at most x + K √x log x. -/
theorem eventually_exists_prime_sqrt_log_of_rh (hRH : RiemannHypothesisProp) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧
      (p:ℝ) ≤ x+K*√x*log x := by
  obtain ⟨K,hK,H⟩ := exists_theta_shortInterval_lower_sqrt_log_of_rh hRH
  refine ⟨K,hK,?_⟩
  filter_upwards [H,eventually_gt_atTop (1:ℝ)] with x hx hx₁
  have hpos := mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx₁)) (Real.log_pos hx₁)
  exact Chebyshev.exists_prime_of_theta_lt (sub_pos.mp (hpos.trans_le hx))

/-- Under RH the gap between consecutive primes is O(√p log p), where p is
the smaller prime. Here the prime indexed by zero is two. -/
theorem cramer_prime_gap_of_rh (hRH : RiemannHypothesisProp) :
    consecutivePrimeGap =O[atTop] fun n : ℕ => √(Nat.nth Nat.Prime n : ℝ)*log (Nat.nth Nat.Prime n : ℝ) := by
  obtain ⟨K,_,H⟩ := eventually_exists_prime_sqrt_log_of_rh hRH
  have h := consecutivePrimeGap_le_of_interval (h := fun x => K*√x*log x) H
  refine IsBigO.of_bound K ?_
  filter_upwards [h,tendsto_nth_prime_real.eventually (eventually_ge_atTop (1:ℝ))] with n hn hp
  rw [Real.norm_of_nonneg (consecutivePrimeGap_pos n).le,
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hp)),←mul_assoc]
  exact hn

end AnalyticNumberTheory.PrimeDistribution
