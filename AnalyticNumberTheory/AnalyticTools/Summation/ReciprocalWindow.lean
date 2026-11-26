import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Reciprocal summation over a finite height window -/

noncomputable section

open Finset Set MeasureTheory
open scoped Classical

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- A linear upper bound for cumulative mass on [U,T] gives a logarithm
of T/U for the reciprocal-weighted sum over that window. -/
theorem sum_div_height_window_le {ι : Type*} (S : Finset ι) (v w : ι → ℝ)
    {U T D : ℝ} (hU : 0 < U) (hUT : U ≤ T)
    (hv : ∀ i ∈ S, U ≤ v i ∧ v i ≤ T) (hw : ∀ i ∈ S, 0 ≤ w i)
    (H : ∀ u ∈ Icc U T, (∑ i ∈ S with v i ≤ u, w i) ≤ D*u) :
    (∑ i ∈ S,w i/v i) ≤ D*(1+Real.log (T/U)) := by
  let f (i : ι) := (Ioi (v i)).indicator (fun t : ℝ => w i*t^(-2:ℝ))
  have hT := hU.trans_le hUT
  have hi (i : ι) (h : i ∈ S) : Integrable (f i) := (integrable_indicator_iff measurableSet_Ioi).mpr
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) (hU.trans_le (hv i h).1)).const_mul _)
  have hbase (x : ℝ) (hx : 0 < x) : (∫ t in Ioi x, t^(-2:ℝ)) = x⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hx]; norm_num [Real.rpow_neg_one]
  have hrow (i : ι) (h : i ∈ S) : (∫ t in Ioc U T, f i t) = w i/v i - w i/T := by
    obtain ⟨hl,hr⟩ := hv i h
    have hp := hU.trans_le hl
    have he : Ioc U T ∩ Ioi (v i) = Ioc (v i) T := by
      ext t
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hl.trans_lt h.1,h.2⟩,h.1⟩⟩
    dsimp only [f]
    rw [setIntegral_indicator measurableSet_Ioi,he,integral_const_mul,← intervalIntegral.integral_of_le hr]
    have hi₀ := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hp
    have hi₁ := hi₀.mono_set (Ioi_subset_Ioi hr)
    have hsum := intervalIntegral.integral_interval_add_Ioi hi₀ hi₁
    rw [hbase (v i) hp,hbase T hT] at hsum
    have hdiff := eq_sub_of_add_eq hsum
    rw [hdiff]
    ring
  have hint : (∫ t in Ioc U T, ∑ i ∈ S, f i t) ≤ D*Real.log (T/U) := by
    have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc U T) := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hUT).mp
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hUT]
      exact continuousOn_id.inv₀ (fun t ht => (hU.trans_le ht.1).ne')
    calc
      _ ≤ ∫ t in Ioc U T, D*t⁻¹ := by
        apply setIntegral_mono_on (integrable_finsetSum _ (fun i h => (hi i h).integrableOn))
          (hinv.const_mul _) measurableSet_Ioc
        intro t ht
        have ht0 := hU.trans ht.1
        have hle : (∑ i ∈ S, f i t) ≤ (∑ i ∈ S with v i ≤ t,w i)*t^(-2:ℝ) := by
          rw [Finset.sum_filter,Finset.sum_mul]
          apply sum_le_sum
          intro i hi
          dsimp only [f]
          by_cases ht' : v i < t
          · simp [Set.indicator_of_mem (show t ∈ Ioi (v i) from ht'),ht'.le]
          rw [Set.indicator_of_notMem (show t ∉ Ioi (v i) from ht')]
          split_ifs <;> positivity [hw i hi]
        apply hle.trans ((mul_le_mul_of_nonneg_right (H t ⟨ht.1.le,ht.2⟩) (Real.rpow_nonneg ht0.le _)).trans_eq _)
        rw [Real.rpow_neg ht0.le,Real.rpow_two]
        field_simp [ht0.ne']
      _ = _ := by
        rw [integral_const_mul,← intervalIntegral.integral_of_le hUT,integral_inv_of_pos hU hT]
  rw [integral_finsetSum _ (fun i h => (hi i h).integrableOn)] at hint
  have heq := sum_congr rfl hrow
  rw [heq,sum_sub_distrib,←sum_div] at hint
  have hav := H T ⟨hUT,le_rfl⟩
  rw [filter_eq_self.mpr (fun i hi => (hv i hi).2)] at hav
  have hend := (div_le_iff₀ hT).mpr hav
  linarith

end AnalyticNumberTheory.AnalyticTools.Summation
