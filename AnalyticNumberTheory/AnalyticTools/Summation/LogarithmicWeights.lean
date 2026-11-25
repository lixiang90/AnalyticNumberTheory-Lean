import AnalyticNumberTheory.AnalyticTools.Summation.Abel

/-!
# A logarithmically weighted sum from a counting estimate

A uniform linear majorant for partial sums gives a bound with the same
coefficient for the sum weighted by log(x/n).
-/

open Finset Real MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- A partial-sum estimate C t on [1,x] bounds the logarithmic weight by C(x−1). -/
theorem sum_log_deficit_le {x C : ℝ} (hx : 1≤x) (a : ℕ→ℝ)
    (H : ∀ t ∈ Set.Icc (1:ℝ) x, ∑n∈Icc 1 ⌊t⌋₊,a n ≤ C*t) :
    (∑ n∈Icc 1 ⌊x⌋₊,a n*(log x-log n)) ≤ C*(x-1) := by
  let P (t:ℝ) := ∑n∈Icc 1 ⌊t⌋₊,a n
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
    continuousOn_id.inv₀ (fun t ht => (zero_lt_one.trans_le ht.1).ne')
  have hd (t : ℝ) (ht : t∈Set.Icc (1:ℝ) x) :
      HasDerivAt (fun v => log x-log v) (-t⁻¹) t := by
    simpa only [zero_sub] using (hasDerivAt_const t (log x)).fun_sub (hasDerivAt_log (zero_lt_one.trans_le ht.1).ne')
  have hab := abel_summation_Icc_one_hasDerivAt a hx hd hcont.neg
  rw [sub_self,mul_zero] at hab
  simp_rw [mul_neg,intervalIntegral.integral_neg,zero_sub,neg_neg] at hab
  rw [hab]
  change (∫t in (1:ℝ)..x,P t*t⁻¹)≤_
  have hint : IntervalIntegrable (fun t => P t*t⁻¹) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    simpa only [P,mul_comm] using integrableOn_mul_sum_Icc a (m:=1) zero_le_one hcont.integrableOn_Icc
  calc
    _ ≤ ∫_t in (1:ℝ)..x,C := by
      apply intervalIntegral.integral_mono_on hx hint intervalIntegrable_const
      intro t ht
      have hpos := zero_lt_one.trans_le ht.1
      rw [←div_eq_mul_inv, div_le_iff₀ hpos]
      exact H t ht
    _ = _ := by rw [intervalIntegral.integral_const];simp [mul_comm]

end AnalyticNumberTheory.AnalyticTools.Summation
