import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Size estimates for rational-frequency prime contours -/

noncomputable section
open Real

namespace AnalyticNumberTheory.ExponentialSums

/-- The two terms in the logarithmically smoothed, rational-frequency bound. -/
def primeContourSmoothedScale (x q : ℝ) : ℝ :=
  x/Real.sqrt q*(1+Real.log x)^5 + x^(3/4 : ℝ)*q^(1/4 : ℝ)*(1+Real.log x)^4

/-- The corresponding scale for a sharp rational-frequency cutoff after desmoothing. -/
def primeContourRationalScale (x q : ℝ) : ℝ :=
  x/q^(1/4 : ℝ)*(1+Real.log x)^3 + x^(7/8 : ℝ)*q^(1/8 : ℝ)*(1+Real.log x)^(5/2 : ℝ)

/-- The smoothed contour scale controls the rounding error of a real cutoff. -/
theorem log_le_primeContourSmoothedScale {x q : ℝ} (hq : 1 ≤ q) (hqx : q ≤ x) :
    1+Real.log x ≤ primeContourSmoothedScale x q := by
  let L := 1+Real.log x
  have hx := hq.trans hqx
  have hx₀ := zero_le_one.trans hx
  have hq₀ := zero_lt_one.trans_le hq
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hU : 1 ≤ x/Real.sqrt q := (one_le_div (Real.sqrt_pos.mpr hq₀)).mpr
    ((Real.sqrt_le_iff.mpr ⟨hq₀.le, by nlinarith only [mul_nonneg hq₀.le (sub_nonneg.mpr hq)]⟩).trans hqx)
  have h5 : L ≤ L^5 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 5)
  change L ≤ _ + x^(3/4 : ℝ)*q^(1/4 : ℝ)*L^4
  exact (h5.trans (le_mul_of_one_le_left (by positivity) hU)).trans (le_add_of_nonneg_right (by positivity))

/-- Moving the real endpoint anywhere in [x,2x] costs an absolute factor 64. -/
theorem primeContourSmoothedScale_le_double {x q y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hy₂ : y ≤ 2*x) (hq : 0 ≤ q) : primeContourSmoothedScale y q ≤ 64*primeContourSmoothedScale x q := by
  let L := 1+Real.log x
  let J := 1+Real.log y
  have hx₀ := zero_lt_one.trans_le hx
  have hy₀ := hx₀.trans_le hxy
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hJ : 0 ≤ J := by dsimp only [J]; linarith only [Real.log_nonneg (hx.trans hxy)]
  have hl : J ≤ 2*L := by
    have h := Real.log_le_log hy₀ hy₂
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx₀.ne'] at h
    dsimp only [J,L]
    linarith only [h,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2),Real.log_nonneg hx]
  have hp : y^(3/4 : ℝ) ≤ 2*x^(3/4 : ℝ) := by
    apply (Real.rpow_le_rpow hy₀.le hy₂ (by norm_num : (0 : ℝ) ≤ 3/4)).trans
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx₀.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx₀.le _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3/4 : ℝ) ≤ 1)
  have hfirst := mul_le_mul (div_le_div_of_nonneg_right hy₂ (Real.sqrt_nonneg q))
    (pow_le_pow_left₀ hJ hl 5) (pow_nonneg hJ 5) (show 0 ≤ 2*x/Real.sqrt q by positivity)
  have hsecond := mul_le_mul (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hq (1/4)))
    (pow_le_pow_left₀ hJ hl 4) (pow_nonneg hJ 4) (show 0 ≤ 2*x^(3/4 : ℝ)*q^(1/4 : ℝ) by positivity)
  apply (add_le_add hfirst hsecond).trans
  change _ ≤ 64*(x/Real.sqrt q*L^5+x^(3/4 : ℝ)*q^(1/4 : ℝ)*L^4)
  calc
    _ = 64*(x/Real.sqrt q*L^5) + 32*(x^(3/4 : ℝ)*q^(1/4 : ℝ)*L^4) := by ring
    _ ≤ 64*(x/Real.sqrt q*L^5) + 64*(x^(3/4 : ℝ)*q^(1/4 : ℝ)*L^4) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
    _ = _ := by ring

/-- Taking the square root of x(1+log x) times the smoothed scale gives
the denominator powers −1/4 and 1/8, and the logarithm powers 3 and 5/2. -/
theorem sqrt_primeContourSmoothedScale_le {x q : ℝ} (hx : 1 ≤ x) (hq : 0 < q) :
    Real.sqrt (x*(1+Real.log x)*primeContourSmoothedScale x q) ≤ primeContourRationalScale x q := by
  let L := 1+Real.log x
  let A := x/q^(1/4 : ℝ)*L^3
  let B := x^(7/8 : ℝ)*q^(1/8 : ℝ)*L^(5/2 : ℝ)
  have hx₀ := zero_lt_one.trans_le hx
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq4 : (q^(1/4 : ℝ))^2 = Real.sqrt q := by
    rw [← Real.rpow_mul_natCast hq.le, Real.sqrt_eq_rpow]
    norm_num
  have hx8 : (x^(7/8 : ℝ))^2 = x*x^(3/4 : ℝ) := by
    calc
      _ = x^(1+3/4 : ℝ) := by rw [← Real.rpow_mul_natCast hx₀.le]; norm_num
      _ = _ := by rw [Real.rpow_add hx₀, Real.rpow_one]
  have hq8 : (q^(1/8 : ℝ))^2 = q^(1/4 : ℝ) := by rw [← Real.rpow_mul_natCast hq.le]; norm_num
  have hL2 : (L^(5/2 : ℝ))^2 = L^5 := by rw [← Real.rpow_mul_natCast hL]; norm_num
  have ha : A^2 = x*L*(x/Real.sqrt q*L^5) := by
    dsimp only [A]
    rw [mul_pow, div_pow, hq4]
    ring
  have hb : B^2 = x*L*(x^(3/4 : ℝ)*q^(1/4 : ℝ)*L^4) := by
    dsimp only [B]
    rw [mul_pow, mul_pow, hx8, hq8, hL2]
    ring
  change Real.sqrt (x*L*(x/Real.sqrt q*L^5+x^(3/4 : ℝ)*q^(1/4 : ℝ)*L^4)) ≤ A+B
  apply Real.sqrt_le_iff.mpr ⟨add_nonneg hA hB, ?_⟩
  rw [mul_add, ← ha, ← hb]
  nlinarith only [mul_nonneg hA hB]

end AnalyticNumberTheory.ExponentialSums
