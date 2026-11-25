import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachDeweighting
import AnalyticNumberTheory.AdditiveNumberTheory.VinogradovThreePrimes

/-!
# The unweighted ternary Goldbach asymptotic

The von Mangoldt asymptotic and the binary sieve give the full leading
term for the actual number of ordered triples, with a fourth logarithm in
the error. Allowing the prime two does not affect that estimate.
-/

open Finset Real Filter Asymptotics
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem primeTripleAsymptotic (T : ℕ→ℕ)
    (ho : ∀N,goldbachTernaryOddCount N≤T N) (ha : ∀N,T N≤goldbachTernaryCount N) :
    (fun N : ℕ => (T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^4) := by
  have H := goldbachTernary_deweight T ho ha (η:=1) le_rfl
    (by simpa using goldbachTernaryWeighted_asymptotic 1)
  norm_num at H
  exact H

/-- The number of ordered representations by three odd primes differs from
the singular-series main term by O(N²/log⁴ N). Repeated primes are allowed. -/
theorem goldbachTernaryOddCount_asymptotic :
    (fun N : ℕ => (goldbachTernaryOddCount N:ℝ)-
      goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^4) :=
  primeTripleAsymptotic _ (fun _ => le_rfl) goldbachTernaryOddCount_le_count

/-- The same ternary Goldbach asymptotic with all primes allowed. -/
theorem goldbachTernaryCount_asymptotic :
    (fun N : ℕ => (goldbachTernaryCount N:ℝ)-
      goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^4) :=
  primeTripleAsymptotic _ goldbachTernaryOddCount_le_count (fun _ => le_rfl)

end AnalyticNumberTheory.AdditiveNumberTheory
