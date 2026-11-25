import AnalyticNumberTheory.SieveMethods.CombinatorialSieve

/-! # The local correction in the binary Goldbach upper-bound sieve -/
noncomputable section
open Real Finset
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Product of the correction factors over the odd prime divisors of n. -/
def goldbachSieveFactor (n : ℕ) : ℝ :=
  ∏ p∈n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2))

theorem one_le_goldbachSieveFactor (n : ℕ) : 1≤goldbachSieveFactor n := by
  apply Finset.one_le_prod₀
  intro p hp
  have h : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
  linarith only [div_nonneg zero_le_one (sub_nonneg.mpr h.le)]

end AnalyticNumberTheory.AdditiveNumberTheory
