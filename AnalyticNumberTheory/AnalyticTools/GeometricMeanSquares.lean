import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Summing geometrically decreasing mean-square bounds

A weighted Cauchy–Schwarz inequality keeps the bound for a finite sum independent
of the number of blocks.
-/

open MeasureTheory Set Finset

namespace AnalyticNumberTheory.AnalyticTools

/-- If the square means of successive blocks are at most `B/4^j`, the square mean of
their sum is at most `4B`, independently of the number of blocks. -/
theorem integral_norm_sum_sq_le_geometric {E : Type*} [NormedAddCommGroup E]
    {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B) (J : ℕ) (f : ℕ → ℝ → E)
    (hc : ∀ j ∈ range J, ContinuousOn (f j) (Icc a b))
    (h : ∀ j ∈ range J, (∫ t in a..b, ‖f j t‖^2) ≤ B*(1/4:ℝ)^j) :
    (∫ t in a..b, ‖∑ j ∈ range J, f j t‖^2) ≤ 4*B := by
  have hgeom : (∑ j ∈ range J, (1/2:ℝ)^j) ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1/2:ℝ) ≠ 1)]
    norm_num
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) J]
  let W (j : ℕ) (t : ℝ) := (2:ℝ)^j*‖f j t‖^2
  have hW (j : ℕ) (hj : j ∈ range J) : ContinuousOn (W j) (Icc a b) := continuousOn_const.mul ((hc j hj).norm.pow 2)
  have hpoint (t : ℝ) : ‖∑ j ∈ range J, f j t‖^2 ≤ 2*∑ j ∈ range J, W j t := by
    have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul (range J) (r := fun j => ‖f j t‖)
      (f := fun j => (1/2:ℝ)^j) (g := fun j => W j t)
      (fun _ _ => by positivity) (fun _ _ => by dsimp [W]; positivity) (fun j _ => by
        dsimp [W]; rw [← mul_assoc,← mul_pow]; norm_num)
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
      (hh.trans (mul_le_mul_of_nonneg_right hgeom (Finset.sum_nonneg fun j _ => by dsimp [W]; positivity)))
  have hsum := continuousOn_finsetSum (range J) hc
  have hsumW := continuousOn_finsetSum (range J) hW
  have hr : ContinuousOn (fun t => (2:ℝ)*∑ j ∈ range J, W j t) (Icc a b) := continuousOn_const.mul hsumW
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab ((hsum.norm.pow 2).intervalIntegrable_of_Icc hab)
    (hr.intervalIntegrable_of_Icc hab) (fun t _ => hpoint t)
  apply hi.trans
  change (∫ t in a..b, 2 * ∑ j ∈ range J, W j t) ≤ _
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun j hj => (hW j hj).intervalIntegrable_of_Icc hab)]
  have hj (j : ℕ) (hj : j ∈ range J) : (∫ t in a..b, W j t) ≤ B*(1/2:ℝ)^j := by
    dsimp [W]; rw [intervalIntegral.integral_const_mul]
    apply (mul_le_mul_of_nonneg_left (h j hj) (by positivity : 0 ≤ (2:ℝ)^j)).trans_eq
    rw [mul_left_comm,← mul_pow]; norm_num
  have htot := Finset.sum_le_sum hj
  rw [← Finset.mul_sum] at htot
  nlinarith [mul_le_mul_of_nonneg_left hgeom hB]

set_option maxHeartbeats 600000 in
/-- The square mean of a sum is at most twice the sum of the individual square means. -/
theorem integral_norm_add_sq_le {E : Type*} [NormedAddCommGroup E]
    {a b A B : ℝ} (hab : a ≤ b) {f g : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (h₁ : (∫ t in a..b, ‖f t‖^2) ≤ A) (h₂ : (∫ t in a..b, ‖g t‖^2) ≤ B) :
    (∫ t in a..b, ‖f t+g t‖^2) ≤ 2*(A+B) := by
  have hp (t : ℝ) (_ : t ∈ Icc a b) : ‖f t+g t‖^2 ≤ 2*(‖f t‖^2+‖g t‖^2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f t) (g t)) 2).trans (by nlinarith [sq_nonneg (‖f t‖-‖g t‖)])
  have hi := intervalIntegral.integral_mono_on (μ := volume) (f := fun t => ‖f t+g t‖^2)
    (g := fun t => 2*(‖f t‖^2+‖g t‖^2)) hab ((hf.add hg).norm.pow 2 |>.intervalIntegrable_of_Icc hab)
    ((continuousOn_const.mul ((hf.norm.pow 2).add (hg.norm.pow 2)) :
      ContinuousOn (fun t => (2:ℝ)*(‖f t‖^2+‖g t‖^2)) (Icc a b)).intervalIntegrable_of_Icc hab)
    hp
  change (∫ t in a..b, ‖f t+g t‖^2) ≤ ∫ t in a..b, 2*(‖f t‖^2+‖g t‖^2) at hi
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f := fun t => ‖f t‖^2) (g := fun t => ‖g t‖^2) ((hf.norm.pow 2).intervalIntegrable_of_Icc hab)
    ((hg.norm.pow 2).intervalIntegrable_of_Icc hab)] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num))

end AnalyticNumberTheory.AnalyticTools
