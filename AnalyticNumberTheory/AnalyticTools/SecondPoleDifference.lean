import AnalyticNumberTheory.AnalyticTools.IntegratedPoleTransform
import AnalyticNumberTheory.AnalyticTools.QuadraticPowerApproximation

/-! # Second differences of the integrated explicit-formula kernel -/

noncomputable section

open Complex

namespace AnalyticNumberTheory.AnalyticTools

/-- The second forward difference of the integrated pole, in factored form. -/
def secondPoleDifference (ω : ℂ) (u h : ℝ) : ℂ :=
  Complex.exp (ω*u) * ((Complex.exp (ω*h)-1)/ω)^2

/-- Taking the second difference a logarithmic distance h apart eliminates the
constant in the integrated kernel and gives the square of an exponential difference. -/
theorem integratedPole_second_difference (ω : ℂ) {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    integratedPole ω (u+2*h) - 2*integratedPole ω (u+h) + integratedPole ω u =
      secondPoleDifference ω u h := by
  simp only [integratedPole, max_eq_left hu, max_eq_left (add_nonneg hu hh),
    max_eq_left (add_nonneg hu (mul_nonneg zero_le_two hh)), secondPoleDifference,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_add, Complex.exp_add]
  rw [show ω*(2*(h:ℂ)) = ω*h+ω*h by ring,Complex.exp_add]
  ring

/-- The second difference is O(h²), with the exponential dependence on the real
part of the pole explicit. The bound is uniform in its imaginary part. -/
theorem norm_secondPoleDifference_le_step {ω : ℂ} (hω : ω ≠ 0) (u : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖secondPoleDifference ω u h‖ ≤ Real.exp (ω.re*u)*(h*(Real.exp (ω.re*h)+1))^2 := by
  have he := norm_cexp_sub_cexp_le (ω*(h:ℂ)) 0
  simp only [Complex.exp_zero,sub_zero,norm_mul,Complex.norm_of_nonneg hh,Complex.norm_exp,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,norm_one] at he
  have hquot : ‖(Complex.exp (ω*h)-1)/ω‖ ≤ h*(Real.exp (ω.re*h)+1) := by
    rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr hω)]
    exact he.trans_eq (by ring)
  rw [secondPoleDifference,norm_mul,norm_pow,Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hquot 2) (Real.exp_pos _).le

/-- At large ordinates the same second difference gains a squared denominator. -/
theorem norm_secondPoleDifference_le_height {ω : ℂ} (him : ω.im ≠ 0) (u h : ℝ) :
    ‖secondPoleDifference ω u h‖ ≤ Real.exp (ω.re*u)*(Real.exp (ω.re*h)+1)^2/ω.im^2 := by
  have h0 : 0 < |ω.im| := abs_pos.mpr him
  have he : ‖Complex.exp (ω*h)-1‖ ≤ Real.exp (ω.re*h)+1 := by
    simpa only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
      sub_zero,norm_one] using norm_sub_le (Complex.exp (ω*h)) 1
  have hquot : ‖(Complex.exp (ω*h)-1)/ω‖ ≤ (Real.exp (ω.re*h)+1)/|ω.im| := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) he h0 (Complex.abs_im_le_norm _)
  simp only [secondPoleDifference,norm_mul,norm_pow,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (ω.re*u)*((Real.exp (ω.re*h)+1)/|ω.im|)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hquot 2) (Real.exp_pos _).le
    _ = _ := by rw [div_pow,sq_abs,mul_div_assoc']

/-- For a pole sequence with bounded real parts and square-summable reciprocals,
the second-difference series sums to the second difference of the three series. -/
theorem hasSum_secondPoleDifference {a : ℕ → ℂ} {b : ℝ} (hb : ∀ n, (a n).re ≤ b)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    HasSum (fun n => secondPoleDifference (a n) u h)
      ((∑' n, integratedPole (a n) (u+2*h)) - 2*(∑' n, integratedPole (a n) (u+h)) +
        ∑' n, integratedPole (a n) u) := by
  have H (v : ℝ) := (summable_integratedPole hb hS v).hasSum
  apply (((H (u+2*h)).sub ((H (u+h)).mul_left 2)).add (H u)).congr_fun
  intro n
  exact (integratedPole_second_difference _ hu hh).symm

end AnalyticNumberTheory.AnalyticTools
