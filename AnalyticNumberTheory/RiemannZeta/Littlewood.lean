import AnalyticNumberTheory.RiemannZeta.LittlewoodStripGrowth
import AnalyticNumberTheory.ExponentialSums.HigherLogarithmicBlocks

/-!
# Littlewood's improvement of the logarithmic zero-free region

Every fixed multiple of the classical logarithmic width is eventually
zero-free. The height threshold can depend on the chosen multiple.
-/

open Filter Complex
namespace AnalyticNumberTheory.RiemannZeta

/-- Uniform strip growth with an arbitrarily small ratio of height exponent
to strip width. -/
theorem littlewood_strip_growth : LittlewoodStripGrowth :=
  littlewood_strip_growth_of_logarithmic_blocks ExponentialSums.logarithmic_block_power_saving

/-- For each fixed positive `B`, the half-plane to the right of
`1 − B / log |t|` is eventually free of zeta zeros. -/
theorem littlewood_zero_free {B : ℝ} (hB : 0<B) :
    ∀ᶠ T : ℝ in atTop, ∀ σ t : ℝ, T ≤ |t| → 1-B/Real.log |t| ≤ σ →
      riemannZeta ((σ:ℂ)+t*I) ≠ 0 :=
  littlewood_zero_free_of_stripGrowth littlewood_strip_growth hB

end AnalyticNumberTheory.RiemannZeta
