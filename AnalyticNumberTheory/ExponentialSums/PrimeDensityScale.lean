import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # The powers of the denominator in the zero-density method -/

noncomputable section

namespace AnalyticNumberTheory.ExponentialSums

/-- The four powers in the fixed-modulus density estimate after passing from
a rational frequency to a real frequency within `1/q²`. -/
def densityPrimeScale (x q : ℝ) : ℝ :=
  x / Real.sqrt q + x ^ (4/5 : ℝ) * q ^ (1/10 : ℝ) + Real.sqrt (x*q) +
    x ^ (9/10 : ℝ) / q ^ (1/10 : ℝ)

theorem sqrt_mul_le_densityPrimeScale {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) :
    Real.sqrt (x*q) ≤ densityPrimeScale x q := by
  unfold densityPrimeScale
  linarith only [div_nonneg hx (Real.sqrt_nonneg q),
    mul_nonneg (Real.rpow_nonneg hx (4/5)) (Real.rpow_nonneg hq (1/10)),
    div_nonneg (Real.rpow_nonneg hx (9/10)) (Real.rpow_nonneg hq (1/10))]

private lemma middle_le_of_product {x q r : ℝ} (hx : 0 < x) (hq : 0 < q) (hr : 0 ≤ r)
    (hrq : r*q ≤ x) :
    x ^ (4/5 : ℝ) * r ^ (1/10 : ℝ) ≤ x ^ (9/10 : ℝ) / q ^ (1/10 : ℝ) := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mpr
  rw [mul_assoc, ← Real.mul_rpow hr hq.le]
  calc
    _ ≤ x ^ (4/5 : ℝ) * x ^ (1/10 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr hq.le) hrq (by norm_num)) (Real.rpow_nonneg hx.le _)
    _ = _ := by rw [← Real.rpow_add hx]; norm_num

/-- For a refined denominator between `q/2` and `x/q`, the three rational
terms are controlled by the two decreasing powers of the original denominator. -/
theorem rational_density_scale_of_refinement {x q r : ℝ} (hx : 0 < x) (hq : 0 < q)
    (hlo : q/2 ≤ r) (hhi : r*q ≤ x) :
    x / Real.sqrt r + x ^ (4/5 : ℝ) * r ^ (1/10 : ℝ) + Real.sqrt (x*r) ≤
      3 * x / Real.sqrt q + x ^ (9/10 : ℝ) / q ^ (1/10 : ℝ) := by
  have hr : 0 < r := by linarith
  have hs := Real.sqrt_pos.mpr hq
  have ht := Real.sqrt_pos.mpr hr
  have hcomp : Real.sqrt q ≤ 2 * Real.sqrt r := Real.sqrt_le_iff.mpr
    ⟨by positivity, by nlinarith only [Real.sq_sqrt hr.le, hlo, hr.le]⟩
  have hhead : x / Real.sqrt r ≤ 2 * x / Real.sqrt q := (div_le_div_iff₀ ht hs).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hcomp hx.le])
  have hlast : Real.sqrt (x*r) ≤ x / Real.sqrt q := by
    apply (le_div_iff₀ hs).mpr
    rw [← Real.sqrt_mul (mul_nonneg hx.le hr.le)]
    exact Real.sqrt_le_iff.mpr ⟨hx.le, by nlinarith only [mul_le_mul_of_nonneg_left hhi hx.le]⟩
  exact (add_le_add (add_le_add hhead (middle_le_of_product hx hq hr.le hhi)) hlast).trans_eq (by ring)

/-- In the balanced range `Q ≤ q ≤ x/Q`, the four density terms are each
at most `x/√Q` as soon as `Q ≤ x^(1/4)`. -/
theorem densityPrimeScale_le_of_denominator_range {x q Q : ℝ} (hx : 0 < x) (hQ : 0 < Q)
    (hQx : Q ≤ x ^ (1/4 : ℝ)) (hlo : Q ≤ q) (hhi : q*Q ≤ x) :
    densityPrimeScale x q ≤ 4 * x / Real.sqrt Q := by
  have hq := hQ.trans_le hlo
  have hs := Real.sqrt_pos.mpr hQ
  have hfirst := div_le_div_of_nonneg_left hx.le hs (Real.sqrt_le_sqrt hlo)
  have hlast : Real.sqrt (x*q) ≤ x / Real.sqrt Q := by
    apply (le_div_iff₀ hs).mpr
    rw [← Real.sqrt_mul (mul_nonneg hx.le hq.le)]
    exact Real.sqrt_le_iff.mpr ⟨hx.le, by nlinarith only [mul_le_mul_of_nonneg_left hhi hx.le]⟩
  have hden : Q ^ (2/5 : ℝ) ≤ x ^ (1/10 : ℝ) := by
    calc
      _ ≤ (x ^ (1/4 : ℝ)) ^ (2/5 : ℝ) := Real.rpow_le_rpow hQ.le hQx (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hx.le]; norm_num
  have hmid : x ^ (9/10 : ℝ) / Q ^ (1/10 : ℝ) ≤ x / Real.sqrt Q := by
    have hhalf : Real.sqrt Q = Q ^ (2/5 : ℝ) * Q ^ (1/10 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ]; norm_num
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hQ _) hs).mpr
    rw [hhalf, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
    calc
      _ ≤ x ^ (9/10 : ℝ) * x ^ (1/10 : ℝ) :=
        mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hx.le _)
      _ = _ := by rw [← Real.rpow_add hx]; norm_num
  have hmid₁ := (middle_le_of_product hx hQ hq.le hhi).trans hmid
  have hmid₂ := (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le (9/10))
    (Real.rpow_pos_of_pos hQ (1/10)) (Real.rpow_le_rpow hQ.le hlo (by norm_num : (0 : ℝ) ≤ 1/10))).trans hmid
  unfold densityPrimeScale
  exact (add_le_add (add_le_add (add_le_add hfirst hmid₁) hlast) hmid₂).trans_eq (by ring)

end AnalyticNumberTheory.ExponentialSums
