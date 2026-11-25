import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Oscillatory integrals with a differentiable amplitude

A uniform bound for partial integrals of the oscillation is multiplied
by the endpoint amplitude and a bound for its total variation.
-/
open Set MeasureTheory
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- Partial integration with uniform derivative and partial-integral
bounds, keeping the interval length explicit. -/
theorem abs_integral_mul_of_partial_integrals {f g g' : ℝ→ℝ} {a b K J D : ℝ}
    (hab : a≤b) (hf : Continuous f) (hg : ∀ t∈Icc a b,HasDerivAt g (g' t) t)
    (hgc : ContinuousOn g' (Icc a b)) (hF : ∀ t∈Icc a b, |∫u in a..t,f u|≤K)
    (hJ : |g b|≤J) (hD : ∀t∈Icc a b, |g' t|≤D) :
    |∫t in a..b,f t*g t|≤K*(J+(b-a)*D) := by
  let F := fun t : ℝ => ∫u in a..t,f u
  have hK : 0≤K := by simpa using hF a ⟨le_rfl,hab⟩
  have hh (t : ℝ) : HasDerivAt F (f t) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hh t).continuousAt
  have hgc' : ContinuousOn g (uIcc a b) := by
    rw [uIcc_of_le hab];exact fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hd : ContinuousOn g' (uIcc a b) := by rwa [uIcc_of_le hab]
  have H := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hFc.continuousOn hgc'
    (fun t _ => hh t) (fun t ht => hg t (by rw [min_eq_left hab,max_eq_right hab] at ht;exact ⟨ht.1.le,ht.2.le⟩))
    (hf.intervalIntegrable ..) hd.intervalIntegrable
  rw [intervalIntegral.integral_add (f:=fun t=>f t*g t) (g:=fun t=>F t*g' t) ((hf.continuousOn.mul hgc').intervalIntegrable)
    ((hFc.continuousOn.mul hd).intervalIntegrable),show F a=0 by simp [F],zero_mul,sub_zero] at H
  have Hi := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t=>F t*g' t) (a:=a) (b:=b) (C:=K*D) (fun t ht => by
    rw [uIoc_of_le hab] at ht
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hF t ⟨ht.1.le,ht.2⟩) (hD t ⟨ht.1.le,ht.2⟩) (abs_nonneg _) hK)
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at Hi
  have hb : |F b*g b|≤K*J := by rw [abs_mul];exact mul_le_mul (hF b ⟨hab,le_rfl⟩) hJ (abs_nonneg _) hK
  rw [show (∫t in a..b,f t*g t)=F b*g b-(∫t in a..b,F t*g' t) by linarith only [H] ]
  linarith only [abs_sub (F b*g b) (∫t in a..b,F t*g' t),hb,Hi]

end AnalyticNumberTheory.AnalyticTools
