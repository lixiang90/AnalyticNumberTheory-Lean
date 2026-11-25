import AnalyticNumberTheory.PrimeDistribution.Hoheisel
import AnalyticNumberTheory.RiemannZeta.Littlewood

/-!
# The short-interval prime number theorem from Littlewood strip growth
-/

noncomputable section
open Filter Asymptotics
open scoped Topology
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- Littlewood's strip growth implies the prime number theorem on intervals
of length `x^θ` for all fixed exponents sufficiently close to one. -/
theorem hoheisel_prime_asymptotic_of_strip_growth (h : LittlewoodStripGrowth) :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] (fun x : ℝ => x^θ/Real.log x) :=
  hoheisel_prime_asymptotic_of_growing_gap (growingZetaScaledGap_of_arbitrary_width
    (fun _ hB => littlewood_zero_free_of_stripGrowth h hB))

/-- The short-interval prime number theorem on a fixed power scale.
The exponent threshold is absolute and all larger fixed exponents below one
are admissible. -/
theorem hoheisel_prime_asymptotic :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] (fun x : ℝ => x^θ/Real.log x) :=
  hoheisel_prime_asymptotic_of_strip_growth littlewood_strip_growth

/-- The von Mangoldt and prime-logarithm weighted counts have the same
unit leading coefficient on the corresponding power intervals. -/
theorem hoheisel_chebyshev_asymptotic :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      ((fun x : ℝ => Chebyshev.psi (x+x^θ)-Chebyshev.psi x) ~[atTop] (fun x : ℝ => x^θ)) ∧
      ((fun x : ℝ => Chebyshev.theta (x+x^θ)-Chebyshev.theta x) ~[atTop] (fun x : ℝ => x^θ)) := by
  obtain ⟨θ₀,hθ₀,H⟩ := hoheisel_power_intervals
  refine ⟨θ₀,hθ₀,fun θ hθ => ?_⟩
  have hψ := (H θ hθ).2 (growingZetaScaledGap_of_arbitrary_width (fun _ hB => littlewood_zero_free hB))
  exact ⟨hψ,theta_shortInterval_of_psi_equivalent (hθ₀.1.trans_le hθ.1) hθ.2.le hψ⟩

end AnalyticNumberTheory.PrimeDistribution
