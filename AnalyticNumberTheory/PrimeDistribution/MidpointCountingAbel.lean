import AnalyticNumberTheory.PrimeDistribution.SharpExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.RiemannCountingZeroSum

/-! # Abel summation for the midpoint prime-power count -/

noncomputable section

open Filter Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.PrimeDistribution

/-- Changing the prime-power count to half weight changes only the endpoint, by the
Chebyshev endpoint correction divided by its logarithm. -/
theorem riemannPrimeCounting_half_sub_one (x : ℝ) :
    riemannPrimeCounting (1/2) x - riemannPrimeCounting 1 x =
      (midpointPsi x - Chebyshev.psi x)/Real.log x := by
  have hI : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  rw [riemannPrimeCounting_one, riemannPrimeCounting, hI, midpointPsi, psi_eq_sum_Icc,
    ←sum_sub_distrib, ←sum_sub_distrib, sum_div]
  refine sum_congr rfl fun n _ => ?_
  by_cases h : (n : ℝ) = x
  · simp [endpointWeight,h]
    ring
  · simp [endpointWeight,h]

/-- Lebesgue almost everywhere, the midpoint and inclusive Chebyshev functions agree. -/
theorem midpointPsi_ae_eq_psi : midpointPsi =ᵐ[volume] Chebyshev.psi := by
  have h : ∀ᵐ x : ℝ, ∀ n : ℕ, x ≠ (n : ℝ) := ae_all_iff.mpr fun n => volume.ae_ne (n : ℝ)
  exact h.mono fun x hx => midpointPsi_eq_psi_of_not_primePower (fun n _ => (hx n).symm)

/-- Abel summation for Riemann's midpoint count, with half weight at both boundary
values. The integrand may use the inclusive Chebyshev function. -/
theorem riemannPrimeCounting_midpoint_abel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    riemannPrimeCounting (1/2) b - riemannPrimeCounting (1/2) a =
      midpointPsi b * (Real.log b)⁻¹ - midpointPsi a * (Real.log a)⁻¹ -
        ∫ t in a..b, Chebyshev.psi t * (-t⁻¹ / (Real.log t)^2) := by
  let w (t : ℝ) := (Real.log t)⁻¹
  let D (t : ℝ) := -t⁻¹ / (Real.log t)^2
  have hw (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt w (D t) t :=
    Real.hasDerivAt_inv_log (zero_lt_one.trans (ha.trans_le ht.1)).ne' (ha.trans_le ht.1).ne'
      (by linarith [ht.1])
  have hD : ContinuousOn D (Set.Icc a b) := by
    intro t ht
    have h := (zero_lt_one.trans (ha.trans_le ht.1)).ne'
    exact (((continuousAt_id.inv₀ h).neg).div ((Real.continuousAt_log h).pow 2)
      (pow_ne_zero 2 (Real.log_pos (ha.trans_le ht.1)).ne')).continuousWithinAt
  have H := abel_summation_Ioc_one (fun n => Λ n) (zero_lt_one.trans ha).le hab
    (fun t ht => (hw t ht).differentiableAt) (hD.congr fun t ht => (hw t ht).deriv)
  simp_rw [←psi_eq_sum_Icc] at H
  have hi : (∫ t in a..b, Chebyshev.psi t * deriv w t) =
      ∫ t in a..b, Chebyshev.psi t * D t :=
    intervalIntegral.integral_congr fun t ht => congrArg (Chebyshev.psi t * ·)
      (hw t (by simpa only [Set.uIcc_of_le hab] using ht)).deriv
  rw [hi] at H
  have hJ := riemannPrimeCounting_sub_eq_sum_Ioc hab
  simp only [div_eq_mul_inv] at hJ
  change riemannPrimeCounting 1 b - riemannPrimeCounting 1 a = _ at hJ
  rw [H] at hJ
  have hb := riemannPrimeCounting_half_sub_one b
  have hₐ := riemannPrimeCounting_half_sub_one a
  simp only [div_eq_mul_inv, sub_mul] at hb hₐ
  dsimp only [D,w] at hJ
  linarith

end AnalyticNumberTheory.PrimeDistribution
