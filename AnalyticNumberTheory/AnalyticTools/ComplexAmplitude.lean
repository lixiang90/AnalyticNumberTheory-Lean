import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Integration by parts for a complex amplitude

A bounded real derivative is enough to integrate a complex amplitude
against an oscillation with bounded partial integrals.
-/
open Set MeasureTheory
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

theorem norm_integral_mul_of_partial_integrals {f g : ℝ→ℂ} {a b K J D : ℝ}
    (hab : a≤b) (hf : Continuous f) (hg : ∀ t∈Icc a b,DifferentiableAt ℝ g t)
    (hF : ∀ t∈Icc a b, ‖∫u in a..t,f u‖≤K)
    (hJ : ‖g b‖≤J) (hD : ∀t∈Icc a b, ‖deriv g t‖≤D) :
    ‖∫t in a..b,f t*g t‖≤K*(J+(b-a)*D) := by
  let F := fun t : ℝ => ∫u in a..t,f u
  have hK : 0≤K := by simpa using hF a ⟨le_rfl,hab⟩
  have hh (t : ℝ) : HasDerivAt F (f t) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hh t).continuousAt
  have hgc : ContinuousOn g (uIcc a b) := by
    rw [uIcc_of_le hab];exact fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hd : IntervalIntegrable (deriv g) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    apply IntegrableOn.of_bound measure_Ioc_lt_top (aestronglyMeasurable_deriv _ _) D
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hD t ⟨ht.1.le,ht.2⟩)
  have H := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hFc.continuousOn hgc
    (fun t _ => hh t) (fun t ht => (hg t (by rw [min_eq_left hab,max_eq_right hab] at ht;exact ⟨ht.1.le,ht.2.le⟩)).hasDerivAt)
    (hf.intervalIntegrable ..) hd
  rw [intervalIntegral.integral_add (f:=fun t=>f t*g t) (g:=fun t=>F t*deriv g t)
    ((hf.continuousOn.mul hgc).intervalIntegrable) (hd.continuousOn_mul hFc.continuousOn),
    show F a=0 by simp [F],zero_mul,sub_zero] at H
  have Hi := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t=>F t*deriv g t) (a:=a) (b:=b) (C:=K*D) (fun t ht => by
    rw [uIoc_of_le hab] at ht
    rw [norm_mul]
    exact mul_le_mul (hF t ⟨ht.1.le,ht.2⟩) (hD t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) hK)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at Hi
  have hb : ‖F b*g b‖≤K*J := by rw [norm_mul];exact mul_le_mul (hF b ⟨hab,le_rfl⟩) hJ (norm_nonneg _) hK
  rw [eq_sub_of_add_eq H]
  exact (norm_sub_le ..).trans ((add_le_add hb Hi).trans_eq (by ring))

end AnalyticNumberTheory.AnalyticTools
