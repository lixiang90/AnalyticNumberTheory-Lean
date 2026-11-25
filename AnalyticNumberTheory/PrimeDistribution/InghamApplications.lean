import AnalyticNumberTheory.PrimeDistribution.InghamBalance
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalEstimates
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalPrimeCounts

/-!
# Prime intervals from Ingham's density exponent

The exponent `3(1−σ)/(2−σ)` supplies the linear density constant three.
Combined with a super-logarithmic zero-free region, it gives the prime
number theorem in intervals of length `x^θ` for each fixed `2/3 < θ < 1`.
-/

open Filter Asymptotics
open scoped Topology

namespace AnalyticNumberTheory.PrimeDistribution

/-- The global Ingham counting inequality for ordinates in `(0,T]`. -/
def InghamDensityEstimate : Prop :=
  ∃ D > (0:ℝ), ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
    (zeroDensityN σ T : ℝ) ≤ D*T^(inghamExponent σ)*(Real.log T)^11

theorem inghamExponent_le_linear {σ : ℝ} (hσ : σ ≤ 1) :
    inghamExponent σ ≤ 3*(1-σ) :=
  div_le_self (by linarith) (by linarith)

/-- Ingham's refined exponent gives the linear density hypothesis with constant three. -/
theorem zeroDensityHypothesis_of_ingham_bound (h : InghamDensityEstimate) :
    ZeroDensityHypothesis 3 11 := by
  obtain ⟨D,hD,H⟩ := h
  refine ⟨D,hD,fun σ hσ T hT => (H σ hσ T hT).trans ?_⟩
  rw [show (Real.log T)^(11:ℝ)=(Real.log T)^11 by norm_cast]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (inghamExponent_le_linear hσ.2)) hD.le)
    (pow_nonneg (Real.log_nonneg (by linarith)) _)

/-- Short-interval asymptotic for the von Mangoldt function at each exponent exceeding two thirds. -/
theorem ingham_psi_shortInterval_of_superLogZeroFree (h : InghamDensityEstimate)
    (hZF : SuperLogZeroFreeHypothesis) {θ : ℝ} (hθ : 2/3 < θ) (hθ' : θ < 1) :
    (fun x : ℝ => Chebyshev.psi (x+x^θ)-Chebyshev.psi x) ~[atTop] fun x => x^θ :=
  psi_shortInterval_isEquivalent_of_zeroDensity (zeroDensityHypothesis_of_ingham_bound h)
    truncatedExplicitFormula hZF (by linarith) hθ' (by linarith)

/-- The prime-counting asymptotic on the same polynomial intervals. -/
theorem ingham_primePi_shortInterval_of_superLogZeroFree (h : InghamDensityEstimate)
    (hZF : SuperLogZeroFreeHypothesis) {θ : ℝ} (hθ : 2/3 < θ) (hθ' : θ < 1) :
    (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] fun x => x^θ/Real.log x :=
  primePi_shortInterval_of_theta_equivalent hθ'.le (theta_shortInterval_of_psi_equivalent
    (by linarith) hθ'.le (ingham_psi_shortInterval_of_superLogZeroFree h hZF hθ hθ'))

/-- Every sufficiently large interval of the stated length contains a prime. -/
theorem ingham_eventually_exists_prime_of_superLogZeroFree (h : InghamDensityEstimate)
    (hZF : SuperLogZeroFreeHypothesis) {θ : ℝ} (hθ : 2/3 < θ) (hθ' : θ < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+x^θ :=
  eventually_exists_prime_shortInterval (zeroDensityHypothesis_of_ingham_bound h)
    truncatedExplicitFormula hZF (by linarith) hθ' (by linarith)

end AnalyticNumberTheory.PrimeDistribution
