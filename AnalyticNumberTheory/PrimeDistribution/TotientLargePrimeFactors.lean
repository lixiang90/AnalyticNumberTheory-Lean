import AnalyticNumberTheory.PrimeDistribution.TotientPrimeFactors

/-! # The large prime factors in the reciprocal totient -/

noncomputable section
open Finset Real

namespace AnalyticNumberTheory.PrimeDistribution

/-- The factors from primes dividing n larger than y cost at most
exp(2 log n/(y log 2)), uniformly for real y ≥ 2. -/
theorem reciprocal_totient_large_primes_le {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 2 ≤ y) :
    (∏ p ∈ n.primeFactors.filter (fun p : ℕ => y < (p : ℝ)), (1-(p : ℝ)⁻¹)⁻¹) ≤
      Real.exp (2*Real.log n/(y*Real.log 2)) := by
  let T := n.primeFactors.filter (fun p : ℕ => y < (p : ℝ))
  let f (p : ℕ) : ℝ := (1-(p : ℝ)⁻¹)⁻¹
  have hy₀ : 0 < y := by linarith only [hy]
  have htwo := Real.log_pos one_lt_two
  have local_bound (p : ℕ) (hp : p ∈ T) : 0 ≤ f p ∧ f p ≤ Real.exp (2/y) := by
    have hpy := (mem_filter.mp hp).2
    have hp₁ : (1 : ℝ) < p := by linarith only [hpy,hy]
    have hp₀ := zero_lt_one.trans hp₁
    have hpos := sub_pos.mpr hp₁
    have heq : f p = 1+1/((p : ℝ)-1) := by
      dsimp only [f]
      have hz : 1-(p : ℝ)⁻¹ = ((p : ℝ)-1)/p := by field_simp [hp₀.ne'] <;> ring
      rw [hz,inv_div]
      field_simp [hpos.ne'] <;> ring
    rw [heq]
    refine ⟨by positivity, ?_⟩
    have hfrac : 1/((p : ℝ)-1) ≤ 2/y := (div_le_div_iff₀ hpos hy₀).mpr (by linarith only [hpy,hy])
    have he := Real.add_one_le_exp (2/y)
    linarith only [hfrac,he]
  have hcard : (T.card : ℝ)*Real.log 2 ≤ Real.log n :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (filter_subset _ _))) htwo.le).trans
      (primeFactors_card_mul_log_two_le hn)
  have hprod : (∏ p ∈ T, f p) ≤ ∏ _p ∈ T, Real.exp (2/y) :=
    prod_le_prod₀ (fun p hp => (local_bound p hp).1) (fun p hp => (local_bound p hp).2)
  apply hprod.trans
  rw [prod_const, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (mul_pos hy₀ htwo)).mpr
  calc
    _ = 2*((T.card : ℝ)*Real.log 2) := by field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by norm_num)

end AnalyticNumberTheory.PrimeDistribution
