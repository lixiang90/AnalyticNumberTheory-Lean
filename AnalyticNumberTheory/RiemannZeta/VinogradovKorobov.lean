import AnalyticNumberTheory.ExponentialSums.VinogradovLogarithmicSums
import AnalyticNumberTheory.RiemannZeta.VinogradovKorobovZeroFree

/-!
# The Vinogradov–Korobov theorems for zeta

Vinogradov's mean-value estimate supplies cubic cancellation in logarithmic
exponential sums. Its analytic consequences are the three-halves growth
bound near one and the classical zero-free region.
-/
open Real Complex Filter
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.RiemannZeta

/-- The three-halves growth estimate for the Riemann zeta function. -/
theorem vinogradovKorobov_strip_growth : VinogradovKorobovStripGrowth :=
  vinogradovKorobov_growth_of_blocks vinogradov_logarithmic_block

/-- The classical Vinogradov–Korobov zero-free region, uniformly in height
and real part. -/
theorem vinogradovKorobov_zero_free :
    ∃ d>(0:ℝ), ∀ᶠ T : ℝ in atTop, ∀ σ t : ℝ, T≤|t| →
      1-d/vinogradovKorobovDenom |t|≤σ → riemannZeta ((σ:ℂ)+t*I)≠0 :=
  vinogradovKorobov_zero_free_of_stripGrowth vinogradovKorobov_strip_growth

/-- Pointwise form at the nontrivial zeros in the open critical strip. -/
theorem vinogradovKorobov_zero_gap : VinogradovKorobovZeroFreeHypothesis :=
  vinogradovKorobov_zero_free_of_blocks vinogradov_logarithmic_block

/-- The super-logarithmic zero-free hypothesis used in density applications. -/
theorem superLogZeroFree : SuperLogZeroFreeHypothesis :=
  superLogZeroFree_of_vinogradovKorobov vinogradovKorobov_zero_gap

end AnalyticNumberTheory.RiemannZeta
