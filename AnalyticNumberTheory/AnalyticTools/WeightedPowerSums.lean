import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Partial summation for positive exponential weights -/
noncomputable section
open Finset Real Set MeasureTheory
open scoped Classical
namespace AnalyticNumberTheory.AnalyticTools

/-- A tail count on [a,b] controls the exponential sum. The term at a
also covers points below a, whose weights are at most x^a. -/
theorem weighted_rpow_sum_le_of_tail {ι : Type*} (S : Finset ι) (w β : ι→ℝ)
    {a b x B : ℝ} (hx : 1≤x) (hab : a≤b) (hw : ∀ i∈S,0≤w i) (hβ : ∀ i∈S,β i≤b)
    (htail : ∀ t∈Icc a b,x^t*(∑ i∈S,w i*(if t≤β i then 1 else 0))≤B) :
    (∑ i∈S,w i*x^(β i)) ≤ x^a*(∑ i∈S,w i)+(b-a)*Real.log x*B := by
  have hx₀ := zero_lt_one.trans_le hx
  let f (t : ℝ) := Real.log x*x^t
  have hf : Continuous f := (continuous_const_rpow hx₀.ne').const_mul _
  let g (i : ι) := (Set.Iic (β i)).indicator f
  have hg (i : ι) : IntervalIntegrable (g i) volume a b :=
    intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp (hf.intervalIntegrable a b)).indicator measurableSet_Iic)
  have hi (i) (hi : i∈S) : x^(β i)≤x^a+∫ t in a..b,g i t := by
    by_cases hh : a≤β i
    · have h := intervalIntegral.integral_indicator (f:=f) (μ:=volume) (show β i∈Set.Icc a b from ⟨hh,hβ i hi⟩)
      change (∫ t in a..b,g i t)=_ at h
      have hd (t : ℝ) : HasDerivAt (fun u : ℝ => x^u) (f t) t := by
        simpa only [f,mul_one,id_eq] using (hasDerivAt_id t).const_rpow hx₀
      rw [h,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hf.intervalIntegrable ..)]
      linarith
    · have hnn := intervalIntegral.integral_nonneg (μ:=volume) hab (f:=g i) (fun t _ => by
        dsimp only [g];apply Set.indicator_nonneg;intro t _;exact mul_nonneg (Real.log_nonneg hx) (Real.rpow_nonneg hx₀.le _))
      linarith only [hnn,Real.rpow_le_rpow_of_exponent_le hx (le_of_not_ge hh)]
  calc
    _ ≤ ∑ i∈S,w i*(x^a+∫ t in a..b,g i t) :=
      sum_le_sum (fun i h => mul_le_mul_of_nonneg_left (hi i h) (hw i h))
    _ = x^a*(∑ i∈S,w i)+∫ t in a..b,∑ i∈S,w i*g i t := by
      simp only [mul_add,sum_add_distrib,intervalIntegral.integral_finsetSum (fun i _ => (hg i).const_mul (w i)),
        intervalIntegral.integral_const_mul,←sum_mul];ring
    _ ≤ x^a*(∑ i∈S,w i)+∫ _ in a..b,Real.log x*B := by
      apply add_le_add_right
      apply intervalIntegral.integral_mono_on hab (by
        have he : (fun t => ∑ i∈S,w i*g i t)=∑ i∈S,(fun t => w i*g i t) := by ext t;simp
        rw [he];exact IntervalIntegrable.sum S (fun i _ => (hg i).const_mul (w i)))
        (intervalIntegrable_const)
      intro t ht
      have he (i : ι) : w i*g i t=Real.log x*x^t*(w i*(if t≤β i then 1 else 0)) := by
        by_cases h : t≤β i <;> simp [g,Set.indicator,f,h] <;> ring
      simp only [he,←mul_sum,mul_assoc]
      exact mul_le_mul_of_nonneg_left (htail t ht) (Real.log_nonneg hx)
    _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul];ring

end AnalyticNumberTheory.AnalyticTools
