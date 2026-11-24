import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachAsymptotic
import AnalyticNumberTheory.PrimeDistribution.SiegelWalfisz

/-!
# Vinogradov's three-primes theorem

The uniform prime number theorem for polylogarithmic moduli supplies the major
arc input to the ternary Goldbach asymptotic.
-/

open Filter
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- The weighted ternary Goldbach asymptotic with a logarithmic saving
of every fixed natural order. -/
theorem goldbachTernaryWeighted_asymptotic (A : ℕ) :
    (fun N : ℕ => goldbachTernaryWeighted N -
      goldbachTernarySingularSeries N * (N : ℝ) ^ 2 / 2) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ 2 / (Real.log N) ^ A) :=
  ternaryGoldbach_asymptotic siegelWalfisz A

/-- **Vinogradov's three-primes theorem.** Every sufficiently large odd
integer is the sum of three odd primes. The primes may repeat. -/
theorem vinogradov_three_primes :
    ∀ᶠ N : ℕ in atTop, Odd N → ∃ p q r : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      r.Prime ∧ Odd r ∧ p + q + r = N :=
  eventually_odd_sum_three_odd_primes_of_siegelWalfisz siegelWalfisz

end AnalyticNumberTheory.AdditiveNumberTheory
