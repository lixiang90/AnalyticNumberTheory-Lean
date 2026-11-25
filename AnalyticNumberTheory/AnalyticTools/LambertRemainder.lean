import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# The remainder of the Lambert kernel at the origin

Removing the pole of the geometric kernel gives a bounded decreasing
weight. This allows Abel summation against coefficients with bounded partial sums.
-/

open Real Set
namespace AnalyticNumberTheory.AnalyticTools

/-- Difference between the polar part and the geometric kernel on the positive real axis. -/
noncomputable def lambertRemainder (x : ℝ) : ℝ := 1 / x - 1 / (exp x - 1)

theorem lambertRemainder_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ lambertRemainder x := by
  have h : x ≤ exp x - 1 := by linarith [Real.add_one_le_exp x]
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hx h)

theorem lambertRemainder_le_one {x : ℝ} (hx : 0 < x) : lambertRemainder x ≤ 1 := by
  have he : 0 < exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  unfold lambertRemainder
  apply (le_of_sub_nonneg ?_)
  field_simp [hx.ne', he.ne'] <;> nlinarith

private theorem lambertRemainder_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt lambertRemainder (-1 / x^2 + exp x / (exp x - 1)^2) x := by
  have he : exp x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  convert ((hasDerivAt_const x (1:ℝ)).div (hasDerivAt_id x) hx.ne').sub
    ((hasDerivAt_const x (1:ℝ)).div ((Real.hasDerivAt_exp x).sub_const 1) he) using 1 <;>
    first | rfl | dsimp <;> ring

/-- The regular part of the Lambert kernel decreases for positive arguments. -/
theorem antitoneOn_lambertRemainder : AntitoneOn lambertRemainder (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun x hx => (lambertRemainder_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => (lambertRemainder_hasDerivAt (interior_subset hx)).hasDerivWithinAt)
  intro x hx'
  have hx : 0 < x := interior_subset hx'
  have he : 0 < exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ x/2 by positivity)
  rw [Real.sinh_eq] at hs
  have hhalf := Real.exp_pos (x/2)
  have heq : exp (x/2) * exp (x/2) = exp x := by rw [← Real.exp_add]; congr 1 <;> ring
  have hneg : exp (-(x/2)) * exp (x/2) = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h : x * exp (x/2) ≤ exp x - 1 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs hhalf.le, heq, hneg]
  have hh := pow_le_pow_left₀ (mul_nonneg hx.le hhalf.le) h 2
  rw [mul_pow, sq (exp (x/2)), heq] at hh
  have hdiv : exp x / (exp x - 1)^2 ≤ 1 / x^2 :=
    (div_le_div_iff₀ (sq_pos_of_pos he) (sq_pos_of_pos hx)).mpr (by linarith only [hh])
  rw [neg_div]
  linarith only [hdiv]

end AnalyticNumberTheory.AnalyticTools
