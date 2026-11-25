import AnalyticNumberTheory.ExponentialSums.PrimeContourDenominators

/-! # Denominator estimates for the contour method at nearby real frequencies -/

noncomputable section
open Real

namespace AnalyticNumberTheory.ExponentialSums

/-- The two terms in the sharp contour bound within q⁻² of a reduced rational,
before multiplication by the common logarithm power. -/
def primeContourFrequencyScale (x q : ℝ) : ℝ :=
  x/q^(1/8 : ℝ) + x^(7/8 : ℝ)*q^(1/8 : ℝ)

/-- For all intermediate endpoints one may take the same logarithm and the
same rational denominator terms. -/
theorem primeContourRationalScale_le_at_larger_cutoff {x y q : ℝ}
    (hy : 1 ≤ y) (hyx : y ≤ x) (hq : 0 < q) :
    primeContourRationalScale y q ≤
      (x/q^(1/4 : ℝ)+x^(7/8 : ℝ)*q^(1/8 : ℝ))*(1+Real.log x)^3 := by
  let L := 1+Real.log x
  let J := 1+Real.log y
  have hy₀ := zero_lt_one.trans_le hy
  have hJ : 1 ≤ J := by dsimp only [J]; linarith only [Real.log_nonneg hy]
  have hL : J ≤ L := add_le_add_right (Real.log_le_log hy₀ hyx) 1
  have hl : J^(5/2 : ℝ) ≤ L^3 := by
    apply (Real.rpow_le_rpow_of_exponent_le hJ (by norm_num : (5/2 : ℝ) ≤ (3 : ℕ))).trans
    simpa only [Real.rpow_natCast] using pow_le_pow_left₀ (zero_le_one.trans hJ) hL 3
  rw [add_mul]
  exact add_le_add (mul_le_mul (div_le_div_of_nonneg_right hyx (by positivity))
    (pow_le_pow_left₀ (zero_le_one.trans hJ) hL 3) (by positivity) (by positivity [hy₀.trans_le hyx]))
    (mul_le_mul (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy₀.le hyx (by norm_num : (0 : ℝ) ≤ 7/8))
      (Real.rpow_nonneg hq.le (1/8))) hl (Real.rpow_nonneg (zero_le_one.trans hJ) _) (by positivity [hy₀.trans_le hyx]))

/-- The upper denominator term controls the sharp sum trivially when its
endpoint lies below both x and the modulus. -/
theorem le_contour_denominator_term {y x q : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hyq : y ≤ q) :
    y ≤ x^(7/8 : ℝ)*q^(1/8 : ℝ) := by
  calc
    _ = y^(7/8 : ℝ)*y^(1/8 : ℝ) := by
      rw [← Real.rpow_add' hy (by norm_num : (7/8 : ℝ)+1/8 ≠ 0), show (7/8 : ℝ)+1/8=1 by norm_num, Real.rpow_one]
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hy hyx (by norm_num)) (Real.rpow_le_rpow hy hyq (by norm_num))
      (Real.rpow_nonneg hy _) (Real.rpow_nonneg (hy.trans hyx) _)

/-- In the narrow rational refinement, q/2 ≤ r and rq ≤ x control both
terms by three times x/q^(1/8). -/
theorem primeContour_scale_of_refinement {x q r : ℝ} (hx : 0 < x) (hq : 1 ≤ q)
    (hlo : q/2 ≤ r) (hhi : r*q ≤ x) :
    x/r^(1/4 : ℝ)+x^(7/8 : ℝ)*r^(1/8 : ℝ) ≤ 3*(x/q^(1/8 : ℝ)) := by
  have hq₀ := zero_lt_one.trans_le hq
  have hr : 0 < r := by linarith only [hq₀,hlo]
  have hpow : q^(1/8 : ℝ) ≤ 2*r^(1/4 : ℝ) := by
    calc
      _ ≤ q^(1/4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
      _ ≤ (2*r)^(1/4 : ℝ) := Real.rpow_le_rpow hq₀.le (by linarith only [hlo]) (by norm_num)
      _ ≤ _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1/4 : ℝ) ≤ 1)
  have hu : x/r^(1/4 : ℝ) ≤ (2*x)/q^(1/8 : ℝ) :=
    (div_le_div_iff₀ (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hq₀ _)).mpr
      ((mul_le_mul_of_nonneg_left hpow hx.le).trans_eq (by ring))
  have hv : x^(7/8 : ℝ)*r^(1/8 : ℝ) ≤ x/q^(1/8 : ℝ) := by
    simpa only [show (1:ℝ)-1/8=7/8 by norm_num] using
      complementary_powers_le_of_mul_le hx hr.le hq₀ (by norm_num : (0 : ℝ) ≤ 1/8) hhi
  exact (add_le_add hu hv).trans_eq (by ring)

/-- On Q ≤ q and qQ ≤ x, both real-frequency denominator terms are at most x/Q^(1/8). -/
theorem primeContourFrequencyScale_le_of_denominator_range {x q Q : ℝ} (hx : 0 < x) (hQ : 0 < Q)
    (hlo : Q ≤ q) (hhi : q*Q ≤ x) : primeContourFrequencyScale x q ≤ 2*(x/Q^(1/8 : ℝ)) := by
  have hq := hQ.trans_le hlo
  have hu := div_le_div_of_nonneg_left hx.le (Real.rpow_pos_of_pos hQ (1/8)) (Real.rpow_le_rpow hQ.le hlo (by norm_num))
  have hv : x^(7/8 : ℝ)*q^(1/8 : ℝ) ≤ x/Q^(1/8 : ℝ) := by
    simpa only [show (1:ℝ)-1/8=7/8 by norm_num] using
      complementary_powers_le_of_mul_le hx hq.le hQ (by norm_num : (0 : ℝ) ≤ 1/8) hhi
  exact (add_le_add hu hv).trans_eq (by ring)

end AnalyticNumberTheory.ExponentialSums
