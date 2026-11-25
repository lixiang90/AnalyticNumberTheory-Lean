import AnalyticNumberTheory.ExponentialSums.VinogradovBilinearSums
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bilinear Taylor approximation for a logarithmic phase

A shift by a product `xy` turns the logarithmic phase into a bilinear
polynomial in the powers `x^j y^j`. The truncation error is uniform across
the square of shifts, including both endpoints.
-/

open Finset Real Complex
namespace AnalyticNumberTheory.ExponentialSums

/-- Lipschitz bound for the standard additive character. -/
theorem norm_e_sub_e_le (u v : ℝ) : ‖e u-e v‖ ≤ 2*Real.pi*|u-v| := by
  have he : e u-e v = e v*(e (u-v)-1) := by
    rw [mul_sub,←e_add,show v+(u-v)=u by ring,mul_one]
  rw [he,norm_mul,norm_e,one_mul,norm_sub_rev,norm_one_sub_e]
  have h := Real.sin_le (x:=Real.pi*distToInt (u-v)) (mul_nonneg Real.pi_pos.le (distToInt_nonneg _))
  have hd := distToInt_le_abs_sub_int (u-v) 0
  simp only [Int.cast_zero,sub_zero] at hd
  nlinarith only [h,mul_le_mul_of_nonneg_left hd Real.pi_pos.le]

private theorem e_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    e (∑ i∈S,f i) = ∏ i∈S,e (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [sum_insert hi,prod_insert hi,e_add,ih]

/-- Explicit scalar form of the polynomial phase in the bilinear sum. -/
theorem diagonalBilinearChar_curve {k : ℕ} (α : Fin k → ℝ) (x y : ℤ) :
    diagonalBilinearChar α (vinogradovCurve k x) (vinogradovCurve k y) =
      e (∑ j, α j * ((x:ℝ)*y)^(j.val+1)) := by
  rw [e_sum]
  change (∏ j, e ((α j * ((vinogradovCurve k y j:ℤ):ℝ)) * ((vinogradovCurve k x j:ℤ):ℝ))) = _
  apply prod_congr rfl; intro j _; congr 1
  simp [vinogradovCurve,mul_pow]; ring

/-- Degree-`k` Taylor coefficients of `t log(n+h)/(2π)`, omitting the constant. -/
noncomputable def logTaylorCoefficients (k : ℕ) (t n : ℝ) (j : Fin k) : ℝ :=
  -(t/(2*Real.pi)) * (-(1/n))^(j.val+1) / (j.val+1)

/-- Error in the polynomial approximation for any shift between `0` and `n/2`. -/
theorem logTaylor_phase_error (k : ℕ) (t : ℝ) {n h : ℝ} (hn : 0<n) (hh : 0≤h)
    (hsmall : h/n ≤ 1/2) :
    |(t/(2*Real.pi))*Real.log (1+h/n) -
      ∑ j, logTaylorCoefficients k t n j * h^(j.val+1)| ≤
      |t/(2*Real.pi)| * (2*(h/n)^(k+1)) := by
  have hz : 0≤h/n := div_nonneg hh hn.le
  have ha : |-(h/n)| = h/n := by rw [abs_neg,abs_of_nonneg hz]
  have H := Real.abs_log_sub_add_sum_range_le (x:=-(h/n)) (ha.trans_lt (by linarith)) k
  rw [ha,sub_neg_eq_add] at H
  have hs : (∑ j, logTaylorCoefficients k t n j * h^(j.val+1)) =
      -(t/(2*Real.pi)) * ∑ i∈range k, (-(h/n))^(i+1)/(i+1) := by
    rw [mul_sum,←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl; intro j _
    unfold logTaylorCoefficients
    rw [show -(h/n)=(-(1/n))*h by ring,mul_pow]; ring
  rw [hs,show ∀ a b c : ℝ, a*b-(-a)*c=a*(c+b) by intros; ring,abs_mul]
  apply mul_le_mul_of_nonneg_left (H.trans _) (abs_nonneg _)
  rw [div_le_iff₀ (by linarith : 0<1-h/n)]
  nlinarith only [mul_le_mul_of_nonneg_left hsmall (pow_nonneg hz (k+1))]

/-- The error after passing from the logarithm to its additive character. -/
theorem logTaylor_character_error (k : ℕ) (t : ℝ) {n : ℝ} (hn : 0<n)
    {x y : ℤ} (hxy : 0≤(x:ℝ)*y) (hsmall : (x:ℝ)*y/n ≤ 1/2) :
    ‖e ((t/(2*Real.pi))*Real.log (1+(x:ℝ)*y/n)) -
      diagonalBilinearChar (logTaylorCoefficients k t n) (vinogradovCurve k x) (vinogradovCurve k y)‖ ≤
      2*|t| * (((x:ℝ)*y)/n)^(k+1) := by
  rw [diagonalBilinearChar_curve]
  apply (norm_e_sub_e_le ..).trans
  have H := logTaylor_phase_error k t hn hxy hsmall
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0≤2*Real.pi)).trans_eq
  rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
  field_simp

end AnalyticNumberTheory.ExponentialSums
