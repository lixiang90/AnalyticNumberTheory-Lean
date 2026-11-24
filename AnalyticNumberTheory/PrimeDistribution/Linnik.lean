import AnalyticNumberTheory.PrimeDistribution.LeastPrimeZeroSum
import AnalyticNumberTheory.PrimeDistribution.LinnikReduction

/-!
# Linnik's theorem on the least prime in an arithmetic progression

The unconditional log-free zero density estimate and Deuring–Heilbronn
repulsion control the high moments of the whole primitive character family.
The arithmetic progression moment inequality then gives a prime below a
fixed power of the modulus, uniformly in the reduced residue class.
-/
noncomputable section
namespace AnalyticNumberTheory.PrimeDistribution

/-- The least prime in a reduced residue class modulo q is at most C q^L
with absolute positive constants C and L. -/
theorem linnik_least_prime :
    ∃ C L : ℝ, 0<C ∧ 0<L ∧ ∀ {q a : ℕ} (hq : q≠0) (ha : a.Coprime q),
      (leastPrimeAP hq ha:ℝ) ≤ C*(q:ℝ)^L :=
  leastPrimeAP_polynomial_of_high_moment_zero_sum linnik_zero_sum_le

/-- For every modulus at least two, a fixed power of the modulus suffices
without a leading constant. -/
theorem linnik_least_prime_power :
    ∃ L : ℝ, 0<L ∧ ∀ {q a : ℕ} (hq : 2≤q) (ha : a.Coprime q),
      (leastPrimeAP (by omega : q≠0) ha:ℝ) ≤ (q:ℝ)^L :=
  leastPrimeAP_power_of_polynomial linnik_least_prime

/-- Linnik's theorem in the prime existence formulation. -/
theorem exists_prime_modEq_le_pow :
    ∃ L : ℝ, 0<L ∧ ∀ {q a : ℕ}, 2≤q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p:ℝ)≤(q:ℝ)^L := by
  obtain ⟨L,hL,hbound⟩ := linnik_least_prime_power
  refine ⟨L,hL,fun {q a} hq ha => ?_⟩
  have hq' : q≠0 := by omega
  exact ⟨leastPrimeAP hq' ha,(leastPrimeAP_spec hq' ha).1,
    (leastPrimeAP_spec hq' ha).2,hbound hq ha⟩

end AnalyticNumberTheory.PrimeDistribution
