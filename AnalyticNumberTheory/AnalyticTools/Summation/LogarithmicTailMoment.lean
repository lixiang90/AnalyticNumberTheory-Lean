import AnalyticNumberTheory.AnalyticTools.LogPowerTailIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A logarithmic moment from a reciprocal tail bound -/

noncomputable section

open Finset Set MeasureTheory Real
open scoped Classical

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- If the tail mass above u is at most K log(u)/u for u ≥ 2, then the
logarithmic moment above 2 has a uniform finite integral bound. -/
theorem sum_log_ratio_of_tail_bound {ι : Type*} (S : Finset ι) (v w : ι → ℝ) {K : ℝ}
    (hv : ∀ i ∈ S, 2 ≤ v i) (hw : ∀ i ∈ S, 0 ≤ w i)
    (H : ∀ u ≥ 2, (∑ i ∈ S with u ≤ v i, w i) ≤ K*(Real.log u/u)) :
    (∑ i ∈ S, w i*Real.log (v i/2)) ≤ K*((Real.log 2+1)/2) := by
  let F (i : ι) := (Set.Ioc 2 (v i)).indicator (fun t : ℝ => w i*t⁻¹)
  have hj (i : ι) (hi : i ∈ S) : Integrable (F i) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    have hi' : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 2 (v i) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (hv i hi)]
      exact continuousOn_id.inv₀ (fun t ht => (two_pos.trans_le ht.1).ne')
    exact hi'.1.const_mul _
  have hrow (i : ι) (hi : i ∈ S) : (∫ t in Ioi (2:ℝ), F i t) = w i*Real.log (v i/2) := by
    dsimp only [F]
    rw [setIntegral_indicator measurableSet_Ioc,Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self,
      integral_const_mul,← intervalIntegral.integral_of_le (hv i hi),
      integral_inv_of_pos two_pos (two_pos.trans_le (hv i hi))]
  have hlog := integral_log_mul_rpow_tail (by norm_num : (1:ℝ) ≤ 2) (p := 1) one_pos
  have h := calc
    (∫ t in Ioi (2:ℝ), ∑ i ∈ S, F i t) ≤ ∫ t in Ioi (2:ℝ), K*(Real.log t*t^(-(1:ℝ)-1)) := by
      apply setIntegral_mono_on (integrable_finsetSum _ (fun i hi => (hj i hi).integrableOn))
        (hlog.1.const_mul _) measurableSet_Ioi
      intro t ht
      have ht₂ : 2 < t := ht
      have ht₀ := two_pos.trans ht₂
      have he : (∑ i ∈ S,F i t) = (∑ i ∈ S with t ≤ v i,w i)*t⁻¹ := by
        rw [Finset.sum_filter,Finset.sum_mul]
        apply sum_congr rfl
        intro i _
        by_cases hi : t ≤ v i
        · simp [F,ht₂,hi]
        · simp [F,hi]
      rw [he]
      apply (mul_le_mul_of_nonneg_right (H t ht₂.le) (inv_nonneg.mpr ht₀.le)).trans_eq
      norm_num [Real.rpow_neg ht₀.le]
      ring
    _ = K*((Real.log 2+1)/2) := by
      rw [integral_const_mul,hlog.2,Real.rpow_neg_one]
      ring
  rw [integral_finsetSum _ (fun i hi => (hj i hi).integrableOn),sum_congr rfl hrow] at h
  exact h

end AnalyticNumberTheory.AnalyticTools.Summation
