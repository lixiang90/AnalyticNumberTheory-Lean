import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Interval moments of a decaying real exponential -/

noncomputable section

open Set MeasureTheory

namespace AnalyticNumberTheory.AnalyticTools

/-- The zeroth and first shifted moments of a decaying exponential on any interval
to the right of its center cost at most 1/u and 1/u², respectively. -/
theorem integral_shifted_exp_neg_moments {c a b u : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hu : 0 < u) :
    (∫ x in a..b, Real.exp (-((x-c)*u))) ≤ 1/u ∧
      (∫ x in a..b, (x-c)*Real.exp (-((x-c)*u))) ≤ 1/u^2 := by
  let E (x : ℝ) := Real.exp (-((x-c)*u))
  have hE (x : ℝ) : HasDerivAt E (-u*E x) x := by
    have h := ((((hasDerivAt_id x).sub_const c).mul_const u).neg).exp
    exact h.congr_deriv (by dsimp [E]; ring)
  have hcont : Continuous E := continuous_iff_continuousAt.mpr fun x => (hE x).continuousAt
  have h₀ (x : ℝ) : HasDerivAt (fun v => -E v/u) (E x) x :=
    ((hE x).neg.div_const u).congr_deriv (by field_simp)
  have h₁ (x : ℝ) : HasDerivAt (fun v => -((v-c)*u+1)*E v/u^2) ((x-c)*E x) x := by
    have hlin := ((((hasDerivAt_id x).sub_const c).mul_const u).add_const 1).neg
    exact ((hlin.mul (hE x)).div_const (u^2)).congr_deriv (by dsimp only [Pi.neg_apply, id_eq]; field_simp; ring)
  have hEa : E a ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hca) hu.le))
  have hEb : 0 ≤ E b := (Real.exp_pos _).le
  have hl : ((a-c)*u+1)*E a ≤ 1 := by
    dsimp only [E]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith [Real.add_one_le_exp ((a-c)*u)]
  have hb : 0 ≤ ((b-c)*u+1)*E b :=
    mul_nonneg (by linarith [mul_nonneg (sub_nonneg.mpr (hca.trans hab)) hu.le]) hEb
  constructor
  · change (∫ x in a..b, E x) ≤ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h₀ x) (hcont.intervalIntegrable a b)]
    rw [← sub_div, div_le_div_iff_of_pos_right hu]
    linarith
  · change (∫ x in a..b, (x-c)*E x) ≤ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h₁ x)
      (((continuous_id.sub continuous_const).mul hcont).intervalIntegrable a b)]
    rw [← sub_div, div_le_div_iff_of_pos_right (sq_pos_of_pos hu)]
    linarith

private theorem abs_integral_le_majorant {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : Continuous g) (h : ∀ x ∈ Icc a b, |f x| ≤ g x) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, g x :=
  (intervalIntegral.abs_integral_le_integral_abs hab).trans
    (intervalIntegral.integral_mono_on hab (hf.abs.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable a b) h)

private theorem integral_scaled_add {a b B L : ℝ} (K : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in a..b, B*(K+g x*L)) = B*(K*(b-a)+(∫ x in a..b, g x)*L) := by
  have hi : IntervalIntegrable (fun x => g x*L) volume a b := (hg.mul continuous_const).intervalIntegrable a b
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (f := fun _ => K) intervalIntegrable_const
    hi, intervalIntegral.integral_const,
    intervalIntegral.integral_mul_const, smul_eq_mul, mul_comm (b-a) K]

/-- The integral of the norm of a function with a horizontal exponential
majorant is bounded uniformly in the endpoints of a segment of length at most two. -/
theorem horizontal_exp_majorant_norm_integral {F : Type*} [NormedAddCommGroup F]
    {c a b u X L B : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hlen : b-a ≤ 2)
    (hu : 0 < u) (hX : 0 ≤ X) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (f : ℝ → F) (hf : ContinuousOn f (Icc a b))
    (H : ∀ x ∈ Icc a b, ‖f x‖ ≤ B*(X + Real.exp (-((x-c)*u))*L)) :
    (∫ x in a..b, ‖f x‖) ≤ B*(2*X+L/u) := by
  let E (x : ℝ) := Real.exp (-((x-c)*u))
  have he : Continuous E := by unfold E; fun_prop
  have hg : Continuous (fun x => B*(X+E x*L)) := by fun_prop
  apply (intervalIntegral.integral_mono_on hab (hf.norm.intervalIntegrable_of_Icc hab)
    (hg.intervalIntegrable a b) H).trans
  rw [integral_scaled_add X E he]
  have h₀ := (integral_shifted_exp_neg_moments hca hab hu).1
  apply mul_le_mul_of_nonneg_left _ hB
  calc
    _ ≤ X*2+(1/u)*L := add_le_add (mul_le_mul_of_nonneg_left hlen hX) (mul_le_mul_of_nonneg_right h₀ hL)
    _ = _ := by ring

/-- Integrating a complex function with an exponential majorant gives one inverse
power of u for its imaginary part and two for its displacement-weighted real part. -/
theorem horizontal_exp_majorant_integrals {c a b u X L B : ℝ} (hca : c ≤ a) (hab : a ≤ b)
    (hb : b ≤ c+2) (hu : 0 < u) (hX : 0 ≤ X) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b))
    (H : ∀ x ∈ Icc a b, ‖f x‖ ≤ B*(X + Real.exp (-((x-c)*u))*L)) :
    |∫ x in a..b, (f x).im| ≤ B*(2*X+L/u) ∧
      |∫ x in a..b, (x-c)*(f x).re| ≤ B*(4*X+L/u^2) := by
  let E (x : ℝ) := Real.exp (-((x-c)*u))
  have he : Continuous E := by unfold E; fun_prop
  have hw : Continuous (fun x : ℝ => (x-c)*E x) := (continuous_id.sub continuous_const).mul he
  have h := integral_shifted_exp_neg_moments hca hab hu
  have hlen : b-a ≤ 2 := by linarith
  constructor
  · have hi := Complex.continuous_im.comp_continuousOn hf
    exact (intervalIntegral.abs_integral_le_integral_abs hab).trans
      ((intervalIntegral.integral_mono_on hab (hi.abs.intervalIntegrable_of_Icc hab)
        (hf.norm.intervalIntegrable_of_Icc hab) (fun x _ => Complex.abs_im_le_norm (f x))).trans
          (horizontal_exp_majorant_norm_integral hca hab hlen hu hX hL hB f hf H))
  · have hnear : ∀ x ∈ Icc a b, |(x-c)*(f x).re| ≤ B*(2*X+((x-c)*E x)*L) := by
      intro x hx
      have hx₀ := sub_nonneg.mpr (hca.trans hx.1)
      rw [abs_mul, abs_of_nonneg hx₀]
      calc
        _ ≤ (x-c)*(B*(X+E x*L)) := mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (H x hx)) hx₀
        _ = B*((x-c)*X+((x-c)*E x)*L) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hB
          exact add_le_add (mul_le_mul_of_nonneg_right (by linarith [hx.2]) hX) le_rfl
    apply (abs_integral_le_majorant hab ((continuous_id.sub continuous_const).continuousOn.mul
        (Complex.continuous_re.comp_continuousOn hf)) (g := fun x => B*(2*X+((x-c)*E x)*L))
        (by fun_prop) hnear).trans
    rw [integral_scaled_add _ _ hw]
    have h₁ : (∫ x in a..b, (x-c)*E x) ≤ 1/u^2 := h.2
    apply mul_le_mul_of_nonneg_left _ hB
    calc
      _ ≤ (2*X)*2+(1/u^2)*L := add_le_add (mul_le_mul_of_nonneg_left hlen (by positivity))
        (mul_le_mul_of_nonneg_right h₁ hL)
      _ = _ := by ring

end AnalyticNumberTheory.AnalyticTools
