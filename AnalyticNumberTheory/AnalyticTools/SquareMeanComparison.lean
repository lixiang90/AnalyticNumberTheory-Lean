import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Comparing square means under perturbation

An adjustable Young inequality bounds the change in energy in terms of the
original square mean and the square mean of the perturbation.
-/

open Set MeasureTheory

namespace AnalyticNumberTheory.AnalyticTools

set_option maxHeartbeats 700000 in
/-- Comparison of square means on a compact interval, with a free positive parameter. -/
theorem abs_integral_norm_sq_sub_le {E : Type*} [NormedAddCommGroup E] {a b η : ℝ}
    (hab : a ≤ b) (hη : 0 < η) {f g : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) :
    |(∫ t in a..b, ‖f t‖^2) - (∫ t in a..b, ‖g t‖^2)| ≤
      η*(∫ t in a..b, ‖f t‖^2) + (1+1/η)*(∫ t in a..b, ‖f t-g t‖^2) := by
  have hp (x y : E) : |‖x‖^2-‖y‖^2| ≤ η*‖x‖^2+(1+1/η)*‖x-y‖^2 := by
    let d := ‖x-y‖
    have hd : 0 ≤ d := norm_nonneg _
    have hdiff : |‖x‖-‖y‖| ≤ d := abs_norm_sub_norm_le x y
    have hy : ‖y‖ ≤ ‖x‖+d := by linarith [(abs_le.mp hdiff).1]
    have hmul := mul_le_mul hdiff (show ‖x‖+‖y‖ ≤ 2*‖x‖+d by linarith)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) hd
    have hY : 2*‖x‖*d ≤ η*‖x‖^2+d^2/η := by
      have hh : 2*‖x‖*d ≤ (η^2*‖x‖^2+d^2)/η := (le_div_iff₀ hη).mpr (by nlinarith [sq_nonneg (η*‖x‖-d)])
      exact hh.trans_eq (by field_simp)
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [mul_comm (‖x‖+‖y‖)]
    apply hmul.trans
    calc d*(2*‖x‖+d) = 2*‖x‖*d+d^2 := by ring
         _ ≤ (η*‖x‖^2+d^2/η)+d^2 := add_le_add hY (le_refl _)
         _ = _ := by change _ = η*‖x‖^2+(1+1/η)*d^2; ring
  have h₁ : ContinuousOn (fun t => ‖f t‖^2) (Icc a b) := hf.norm.pow 2
  have h₂ : ContinuousOn (fun t => ‖g t‖^2) (Icc a b) := hg.norm.pow 2
  have h₃ : ContinuousOn (fun t => ‖f t-g t‖^2) (Icc a b) := (hf.sub hg).norm.pow 2
  have hR : ContinuousOn (fun t => η*‖f t‖^2+(1+1/η)*‖f t-g t‖^2) (Icc a b) :=
    (continuousOn_const.mul h₁).add (continuousOn_const.mul h₃)
  have hL : ContinuousOn (fun t => |‖f t‖^2-‖g t‖^2|) (Icc a b) := (h₁.sub h₂).abs
  rw [← intervalIntegral.integral_sub (f := fun t => ‖f t‖^2) (g := fun t => ‖g t‖^2)
    (h₁.intervalIntegrable_of_Icc hab) (h₂.intervalIntegrable_of_Icc hab)]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => ‖f t‖^2-‖g t‖^2) hab
  simp only [Real.norm_eq_abs] at hnorm
  calc
    _ ≤ ∫ t in a..b, |‖f t‖^2-‖g t‖^2| := hnorm
    _ ≤ ∫ t in a..b, η*‖f t‖^2+(1+1/η)*‖f t-g t‖^2 :=
      intervalIntegral.integral_mono_on hab (hL.intervalIntegrable_of_Icc hab) (hR.intervalIntegrable_of_Icc hab) (fun t _ => hp _ _)
    _ = _ := by
      rw [intervalIntegral.integral_add (f := fun t => η*‖f t‖^2) (g := fun t => (1+1/η)*‖f t-g t‖^2)
        ((h₁.intervalIntegrable_of_Icc hab).const_mul _) ((h₃.intervalIntegrable_of_Icc hab).const_mul _),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

end AnalyticNumberTheory.AnalyticTools
