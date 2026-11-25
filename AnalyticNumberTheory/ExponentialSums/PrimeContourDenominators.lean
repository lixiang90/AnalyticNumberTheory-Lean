import AnalyticNumberTheory.ExponentialSums.PrimeRationalDesmoothing

/-! # Balanced denominator ranges for the rational prime contours -/

open Real
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- The complementary powers x^(1−a) q^a are at most x/Q^a when qQ ≤ x.
This comparison applies to the exponents on both prime contours. -/
theorem complementary_powers_le_of_mul_le {x q Q a : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (hQ : 0 < Q) (ha : 0 ≤ a) (hprod : q*Q ≤ x) : x^(1-a)*q^a ≤ x/Q^a := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ a)).mpr
  rw [mul_assoc, ← Real.mul_rpow hq hQ.le]
  calc
    _ ≤ x^(1-a)*x^a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hq hQ.le) hprod ha)
      (Real.rpow_nonneg hx.le _)
    _ = _ := by rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]

/-- Both rational-frequency scales save a power of Q if Q ≤ q² and qQ ≤ x.
The smoothed saving is a fourth root, and the sharp saving is an eighth root. -/
theorem primeContourScales_le_of_denominator_range {x q Q : ℝ} (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hlo : Q ≤ q^2) (hhi : q*Q ≤ x) :
    primeContourSmoothedScale x q ≤ 2*(x/Q^(1/4 : ℝ))*(1+Real.log x)^5 ∧
    primeContourRationalScale x q ≤ 2*(x/Q^(1/8 : ℝ))*(1+Real.log x)^3 := by
  let L := 1+Real.log x
  have hq₀ := zero_lt_one.trans_le hq
  have hQ₀ := zero_lt_one.trans_le hQ
  have hx := (one_le_mul_of_one_le_of_one_le hq hQ).trans hhi
  have hx₀ := zero_lt_one.trans_le hx
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL₀ := zero_le_one.trans hL
  have low {a : ℝ} (ha : 0 ≤ a) : x/q^(2*a) ≤ x/Q^a := by
    apply div_le_div_of_nonneg_left hx₀.le (Real.rpow_pos_of_pos hQ₀ _)
    exact (Real.rpow_le_rpow hQ₀.le hlo ha).trans_eq (Real.rpow_natCast_mul hq₀.le 2 a).symm
  have f₁ : x/Real.sqrt q ≤ x/Q^(1/4 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow, show (2:ℝ)*(1/4)=1/2 by norm_num] using low (by norm_num : (0 : ℝ) ≤ 1/4)
  have f₂ : x/q^(1/4 : ℝ) ≤ x/Q^(1/8 : ℝ) := by
    simpa only [show (2:ℝ)*(1/8)=1/4 by norm_num] using low (by norm_num : (0 : ℝ) ≤ 1/8)
  have g₁ : x^(3/4 : ℝ)*q^(1/4 : ℝ) ≤ x/Q^(1/4 : ℝ) := by
    simpa only [show (1:ℝ)-1/4=3/4 by norm_num] using
      complementary_powers_le_of_mul_le hx₀ hq₀.le hQ₀ (by norm_num : (0 : ℝ) ≤ 1/4) hhi
  have g₂ : x^(7/8 : ℝ)*q^(1/8 : ℝ) ≤ x/Q^(1/8 : ℝ) := by
    simpa only [show (1:ℝ)-1/8=7/8 by norm_num] using
      complementary_powers_le_of_mul_le hx₀ hq₀.le hQ₀ (by norm_num : (0 : ℝ) ≤ 1/8) hhi
  constructor
  · exact (add_le_add (mul_le_mul_of_nonneg_right f₁ (pow_nonneg hL₀ 5))
      (mul_le_mul g₁ (pow_le_pow_right₀ hL (by decide : 4 ≤ 5)) (pow_nonneg hL₀ 4) (by positivity))).trans_eq
        (by change _ = 2*(x/Q^(1/4 : ℝ))*L^5; ring)
  · have hl : L^(5/2 : ℝ) ≤ L^3 := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (5/2 : ℝ) ≤ (3 : ℕ))
    exact (add_le_add (mul_le_mul_of_nonneg_right f₂ (pow_nonneg hL₀ 3))
      (mul_le_mul g₂ hl (Real.rpow_nonneg hL₀ _) (by positivity))).trans_eq
        (by change _ = 2*(x/Q^(1/8 : ℝ))*L^3; ring)

/-- The rational smoothed and sharp prime sums on the common denominator range,
with a single absolute constant and all real cutoffs. -/
theorem primeExpSums_rational_contour_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x Q : ℝ}, a.natAbs.Coprime q →
      1 ≤ Q → Q ≤ (q : ℝ)^2 → (q : ℝ)*Q ≤ x →
      ‖logSmoothedPrimeExpSum x ((a : ℝ)/q)‖ ≤ C*(x/Q^(1/4 : ℝ))*(1+Real.log x)^5 ∧
      ‖primeExpSum x ((a : ℝ)/q)‖ ≤ C*(x/Q^(1/8 : ℝ))*(1+Real.log x)^3 := by
  obtain ⟨A,hA,F⟩ := logSmoothedPrimeExpSum_rational_contour
  obtain ⟨B,hB,G⟩ := primeExpSum_rational_contour
  refine ⟨2*(A+B), by positivity, ?_⟩
  intro q _ a x Q ha hQ hlo hhi
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqx := (le_mul_of_one_le_right (Nat.cast_nonneg q) hQ).trans hhi
  have hx₀ := zero_le_one.trans (hq.trans hqx)
  have hQ₀ := zero_lt_one.trans_le hQ
  have hL : 0 ≤ 1+Real.log x := by linarith only [Real.log_nonneg (hq.trans hqx)]
  obtain ⟨h₁,h₂⟩ := primeContourScales_le_of_denominator_range hq hQ hlo hhi
  have bound {S A' b c : ℝ} (hA' : 0 ≤ A') (hC : A' ≤ A+B) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (h : S ≤ 2*b*c) : A'*S ≤ (2*(A+B))*b*c := by
    apply (mul_le_mul_of_nonneg_left h hA').trans
    exact (mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ 2*b*c)).trans_eq (by ring)
  exact ⟨(F ha hqx).trans (bound hA.le (by linarith) (by positivity) (by positivity) h₁),
    (G ha hqx).trans (bound hB.le (by linarith) (by positivity) (by positivity) h₂)⟩

end AnalyticNumberTheory.ExponentialSums
