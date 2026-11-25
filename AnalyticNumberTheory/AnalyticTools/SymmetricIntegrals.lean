import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-! # Integration over symmetric real intervals -/

open MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools

/-- An odd real function integrates to zero on every symmetric interval. -/
theorem integral_odd_real_zero {f : ℝ → ℝ} (hodd : ∀ t : ℝ, f (-t) = -f t) (T : ℝ) :
    ∫ t in (-T)..T, f t = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg f (a := -T) (b := T)
  have h1 : ∫ t in (-T)..T, f (-t) = ∫ t in (-T)..T, f t := by
    simp only [neg_neg] at hcomp
    exact hcomp
  have h2 : ∫ t in (-T)..T, f (-t) = -∫ t in (-T)..T, f t := by
    simp only [hodd, intervalIntegral.integral_neg]
  linarith

/-- The integral of a continuous even function on a symmetric interval is twice its positive half. -/
theorem integral_even_real_eq_two_mul {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ t : ℝ, f (-t) = f t) (T : ℝ) :
    ∫ t in (-T)..T, f t = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have hsplit :
      (∫ t in (-T)..0, f t) + (∫ t in (0 : ℝ)..T, f t) = ∫ t in (-T)..T, f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)
  have hleft : ∫ t in (-T)..0, f t = ∫ t in (0 : ℝ)..T, f t := by
    have hcomp := intervalIntegral.integral_comp_neg f (a := (0 : ℝ)) (b := T)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    exact intervalIntegral.integral_congr fun t _ ↦ heven t
  linarith

end AnalyticNumberTheory.AnalyticTools
