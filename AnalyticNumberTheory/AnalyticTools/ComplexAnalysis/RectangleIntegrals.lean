import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The Cauchy kernel on a rectangle

Integration of the real and imaginary parts along the four edges computes
the winding number of a positively oriented axis-aligned rectangle.
-/

open MeasureTheory Set Filter
open Complex (I reProdIm)
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private lemma horiz_inv_eq (α x : ℝ) (hα : α ≠ 0) :
    ((x : ℂ) + (α : ℂ) * I)⁻¹ =
      ((x / (α ^ 2 + x ^ 2) : ℝ) : ℂ) - ((α / (α ^ 2 + x ^ 2) : ℝ) : ℂ) * I := by
  have hden : α ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hne : (x : ℂ) + (α : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hα him
  have hmul : ((x : ℂ) + (α : ℂ) * I) *
      (((x / (α ^ 2 + x ^ 2) : ℝ) : ℂ) - ((α / (α ^ 2 + x ^ 2) : ℝ) : ℂ) * I) = 1 := by
    push_cast
    have hdenC : (α : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden
    rw [show (x : ℂ) / ((α : ℂ) ^ 2 + (x : ℂ) ^ 2) - (α : ℂ) / ((α : ℂ) ^ 2 + (x : ℂ) ^ 2) * I =
        ((x : ℂ) - (α : ℂ) * I) / ((α : ℂ) ^ 2 + (x : ℂ) ^ 2) by ring]
    rw [← mul_div_assoc, div_eq_one_iff_eq hdenC]
    linear_combination -(α : ℂ) ^ 2 * Complex.I_sq
  rw [inv_eq_one_div]
  exact (eq_div_of_mul_eq hne (by rw [mul_comm]; exact hmul)).symm

private lemma I_mul_vert_inv_eq (β y : ℝ) (hβ : β ≠ 0) :
    I * ((β : ℂ) + (y : ℂ) * I)⁻¹ =
      ((y / (β ^ 2 + y ^ 2) : ℝ) : ℂ) + ((β / (β ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
  have hden : β ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hne : (β : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hβ hre
  have hmul : ((β : ℂ) + (y : ℂ) * I) *
      (((y / (β ^ 2 + y ^ 2) : ℝ) : ℂ) + ((β / (β ^ 2 + y ^ 2) : ℝ) : ℂ) * I) = I := by
    push_cast
    have hdenC : (β : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden
    rw [show (y : ℂ) / ((β : ℂ) ^ 2 + (y : ℂ) ^ 2) + (β : ℂ) / ((β : ℂ) ^ 2 + (y : ℂ) ^ 2) * I =
        ((y : ℂ) + (β : ℂ) * I) / ((β : ℂ) ^ 2 + (y : ℂ) ^ 2) by ring]
    rw [← mul_div_assoc, div_eq_iff hdenC]
    linear_combination (β : ℂ) * (y : ℂ) * Complex.I_sq
  rw [mul_comm, inv_mul_eq_div]
  exact (eq_div_of_mul_eq hne (by rw [mul_comm]; exact hmul)).symm

private lemma intervalIntegral_id_div_sq_add_sq {α x₁ x₂ : ℝ} (hα : α ≠ 0) :
    ∫ x : ℝ in x₁..x₂, x / (α ^ 2 + x ^ 2) =
      (Real.log (α ^ 2 + x₂ ^ 2) - Real.log (α ^ 2 + x₁ ^ 2)) / 2 := by
  have hne_all : ∀ x : ℝ, α ^ 2 + x ^ 2 ≠ 0 := fun x ↦
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hα) (sq_nonneg x)).ne'
  have hderiv : ∀ x ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun t : ℝ ↦ Real.log (α ^ 2 + t ^ 2) / 2) (x / (α ^ 2 + x ^ 2)) x := by
    intro x _
    have hne := hne_all x
    have h1 : HasDerivAt (fun t : ℝ ↦ α ^ 2 + t ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (α ^ 2))
    have h2 := (h1.log hne).div_const 2
    have hEq : (2 * x / (α ^ 2 + x ^ 2)) / 2 = x / (α ^ 2 + x ^ 2) := by ring
    simpa only [hEq] using h2
  have hcont : Continuous (fun x : ℝ ↦ x / (α ^ 2 + x ^ 2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2)) hne_all
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable x₁ x₂)]
  ring

private lemma intervalIntegral_const_div_sq_add_sq {α x₁ x₂ : ℝ} (hα : α ≠ 0) :
    ∫ x : ℝ in x₁..x₂, α / (α ^ 2 + x ^ 2) =
      Real.arctan (x₂ / α) - Real.arctan (x₁ / α) := by
  have hne_all : ∀ x : ℝ, α ^ 2 + x ^ 2 ≠ 0 := fun x ↦
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hα) (sq_nonneg x)).ne'
  have hderiv : ∀ x ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun t : ℝ ↦ Real.arctan (t / α)) (α / (α ^ 2 + x ^ 2)) x := by
    intro x _
    have hne := hne_all x
    have hlin : HasDerivAt (fun t : ℝ ↦ t / α) (1 / α) x := (hasDerivAt_id x).div_const α
    have h2 := hlin.arctan
    have hEq : 1 / (1 + (x / α) ^ 2) * (1 / α) = α / (α ^ 2 + x ^ 2) := by
      field_simp [hα, hne]
    exact h2.congr_deriv hEq
  have hcont : Continuous (fun x : ℝ ↦ α / (α ^ 2 + x ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) hne_all
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable x₁ x₂)

private lemma horiz_inv_integral (x₁ x₂ α : ℝ) (hα : α ≠ 0) :
    ∫ x : ℝ in x₁..x₂, ((x : ℂ) + (α : ℂ) * I)⁻¹ =
      (((Real.log (α ^ 2 + x₂ ^ 2) - Real.log (α ^ 2 + x₁ ^ 2)) / 2 : ℝ) : ℂ) -
        ((Real.arctan (x₂ / α) - Real.arctan (x₁ / α) : ℝ) : ℂ) * I := by
  have hne_all : ∀ x : ℝ, α ^ 2 + x ^ 2 ≠ 0 := fun x ↦
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hα) (sq_nonneg x)).ne'
  have hcont_re : Continuous (fun x : ℝ ↦ x / (α ^ 2 + x ^ 2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2)) hne_all
  have hcont_im : Continuous (fun x : ℝ ↦ α / (α ^ 2 + x ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) hne_all
  have hi1 : IntervalIntegrable (fun x : ℝ ↦ ((x / (α ^ 2 + x ^ 2) : ℝ) : ℂ)) volume x₁ x₂ :=
    (Complex.continuous_ofReal.comp hcont_re).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun x : ℝ ↦ ((α / (α ^ 2 + x ^ 2) : ℝ) : ℂ) * I) volume x₁ x₂ :=
    ((Complex.continuous_ofReal.comp hcont_im).mul continuous_const).intervalIntegrable _ _
  have hf_eq : (fun x : ℝ ↦ ((x : ℂ) + (α : ℂ) * I)⁻¹) =
      fun x : ℝ ↦ ((x / (α ^ 2 + x ^ 2) : ℝ) : ℂ) - ((α / (α ^ 2 + x ^ 2) : ℝ) : ℂ) * I :=
    funext fun x ↦ horiz_inv_eq α x hα
  rw [hf_eq, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    intervalIntegral_id_div_sq_add_sq hα, intervalIntegral_const_div_sq_add_sq hα]

private lemma I_mul_vert_inv_integral (y₁ y₂ β : ℝ) (hβ : β ≠ 0) :
    I * ∫ y : ℝ in y₁..y₂, ((β : ℂ) + (y : ℂ) * I)⁻¹ =
      (((Real.log (β ^ 2 + y₂ ^ 2) - Real.log (β ^ 2 + y₁ ^ 2)) / 2 : ℝ) : ℂ) +
        ((Real.arctan (y₂ / β) - Real.arctan (y₁ / β) : ℝ) : ℂ) * I := by
  have hne_all : ∀ y : ℝ, β ^ 2 + y ^ 2 ≠ 0 := fun y ↦
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hβ) (sq_nonneg y)).ne'
  have hcont_re : Continuous (fun y : ℝ ↦ y / (β ^ 2 + y ^ 2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2)) hne_all
  have hcont_im : Continuous (fun y : ℝ ↦ β / (β ^ 2 + y ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) hne_all
  have hi1 : IntervalIntegrable (fun y : ℝ ↦ ((y / (β ^ 2 + y ^ 2) : ℝ) : ℂ)) volume y₁ y₂ :=
    (Complex.continuous_ofReal.comp hcont_re).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun y : ℝ ↦ ((β / (β ^ 2 + y ^ 2) : ℝ) : ℂ) * I) volume y₁ y₂ :=
    ((Complex.continuous_ofReal.comp hcont_im).mul continuous_const).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul]
  have hf_eq : (fun y : ℝ ↦ I * ((β : ℂ) + (y : ℂ) * I)⁻¹) =
      fun y : ℝ ↦ ((y / (β ^ 2 + y ^ 2) : ℝ) : ℂ) + ((β / (β ^ 2 + y ^ 2) : ℝ) : ℂ) * I :=
    funext fun y ↦ I_mul_vert_inv_eq β y hβ
  rw [hf_eq, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    intervalIntegral_id_div_sq_add_sq hβ, intervalIntegral_const_div_sq_add_sq hβ]

private lemma arctan_div_add_arctan_div_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.arctan (u / v) + Real.arctan (v / u) = Real.pi / 2 := by
  have hinv : v / u = (u / v)⁻¹ := by field_simp
  rw [hinv, Real.arctan_inv_of_pos (div_pos hu hv)]
  ring

private lemma contour_rect_inv_eq_one {a b c d : ℝ}
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    (1 / (2 * Real.pi * I)) *
        ((∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * I)⁻¹) -
          (∫ x : ℝ in a..b, ((x : ℂ) + (d : ℂ) * I)⁻¹) +
          I * (∫ y : ℝ in c..d, ((b : ℂ) + (y : ℂ) * I)⁻¹) -
          I * (∫ y : ℝ in c..d, ((a : ℂ) + (y : ℂ) * I)⁻¹)) = 1 := by
  rw [horiz_inv_integral a b c hc.ne, horiz_inv_integral a b d hd.ne',
    I_mul_vert_inv_integral c d b hb.ne', I_mul_vert_inv_integral c d a ha.ne]
  have hlog_swap : ∀ u v : ℝ, Real.log (u ^ 2 + v ^ 2) = Real.log (v ^ 2 + u ^ 2) := by
    intro u v
    ring_nf
  have hna : 0 < -a := neg_pos.mpr ha
  have hnc : 0 < -c := neg_pos.mpr hc
  have hc1 : Real.arctan (b / d) + Real.arctan (d / b) = Real.pi / 2 :=
    arctan_div_add_arctan_div_pos hb hd
  have hc2 : Real.arctan (-a / d) + Real.arctan (d / -a) = Real.pi / 2 :=
    arctan_div_add_arctan_div_pos hna hd
  have hc3 : Real.arctan (-a / -c) + Real.arctan (-c / -a) = Real.pi / 2 :=
    arctan_div_add_arctan_div_pos hna hnc
  have hc4 : Real.arctan (b / -c) + Real.arctan (-c / b) = Real.pi / 2 :=
    arctan_div_add_arctan_div_pos hb hnc
  have h_re_zero :
      (Real.log (c ^ 2 + b ^ 2) - Real.log (c ^ 2 + a ^ 2)) / 2 -
        (Real.log (d ^ 2 + b ^ 2) - Real.log (d ^ 2 + a ^ 2)) / 2 +
        (Real.log (b ^ 2 + d ^ 2) - Real.log (b ^ 2 + c ^ 2)) / 2 -
        (Real.log (a ^ 2 + d ^ 2) - Real.log (a ^ 2 + c ^ 2)) / 2 = 0 := by
    rw [hlog_swap c b, hlog_swap c a, hlog_swap d b, hlog_swap d a]
    ring
  have ha_d : Real.arctan (a / d) = -Real.arctan (-a / d) := by
    rw [show a / d = -(-a / d) by ring, Real.arctan_neg]
  have hd_a : Real.arctan (d / a) = -Real.arctan (d / -a) := by
    rw [show d / a = -(d / -a) by ring, Real.arctan_neg]
  have hb_c : Real.arctan (b / c) = -Real.arctan (b / -c) := by
    rw [show b / c = -(b / -c) by ring, Real.arctan_neg]
  have hc_b : Real.arctan (c / b) = -Real.arctan (-c / b) := by
    rw [show c / b = -(-c / b) by ring, Real.arctan_neg]
  have ha_c : Real.arctan (a / c) = Real.arctan (-a / -c) := by rw [neg_div_neg_eq]
  have hc_a : Real.arctan (c / a) = Real.arctan (-c / -a) := by rw [neg_div_neg_eq]
  have h_im_two_pi :
      -(Real.arctan (b / c) - Real.arctan (a / c)) +
        (Real.arctan (b / d) - Real.arctan (a / d)) +
        (Real.arctan (d / b) - Real.arctan (c / b)) -
        (Real.arctan (d / a) - Real.arctan (c / a)) = 2 * Real.pi := by
    rw [ha_d, hd_a, hb_c, hc_b, ha_c, hc_a]
    linarith [hc1, hc2, hc3, hc4]
  have hsum :
      ((((Real.log (c ^ 2 + b ^ 2) - Real.log (c ^ 2 + a ^ 2)) / 2 : ℝ) : ℂ) -
          ((Real.arctan (b / c) - Real.arctan (a / c) : ℝ) : ℂ) * I) -
        ((((Real.log (d ^ 2 + b ^ 2) - Real.log (d ^ 2 + a ^ 2)) / 2 : ℝ) : ℂ) -
          ((Real.arctan (b / d) - Real.arctan (a / d) : ℝ) : ℂ) * I) +
        ((((Real.log (b ^ 2 + d ^ 2) - Real.log (b ^ 2 + c ^ 2)) / 2 : ℝ) : ℂ) +
          ((Real.arctan (d / b) - Real.arctan (c / b) : ℝ) : ℂ) * I) -
        ((((Real.log (a ^ 2 + d ^ 2) - Real.log (a ^ 2 + c ^ 2)) / 2 : ℝ) : ℂ) +
          ((Real.arctan (d / a) - Real.arctan (c / a) : ℝ) : ℂ) * I) =
        ((2 * Real.pi : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [h_re_zero]
    · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero]
      linear_combination h_im_two_pi
  rw [hsum]
  push_cast
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Cauchy integral of `(s - p)⁻¹` around any axis-aligned rectangle strictly enclosing `p`
equals `1`. -/
theorem rectangle_cauchyKernel_eq_one {p z w : ℂ}
    (hzre : z.re < p.re) (hpre : p.re < w.re) (hzim : z.im < p.im) (hpim : p.im < w.im) :
    (1 / (2 * Real.pi * I)) *
        ((∫ x : ℝ in z.re..w.re, ((x : ℂ) + (z.im : ℂ) * I - p)⁻¹) -
          (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (w.im : ℂ) * I - p)⁻¹) +
          I * (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * I - p)⁻¹) -
          I * (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * I - p)⁻¹)) = 1 := by
  have hhoriz : ∀ (α : ℝ),
      ∫ x : ℝ in z.re..w.re, ((x : ℂ) + (α : ℂ) * I - p)⁻¹ =
        ∫ u : ℝ in (z.re - p.re)..(w.re - p.re), ((u : ℂ) + ((α - p.im : ℝ) : ℂ) * I)⁻¹ := by
    intro α
    have hfun : (fun x : ℝ ↦ ((x : ℂ) + (α : ℂ) * I - p)⁻¹) =
        fun x : ℝ ↦ (((x - p.re : ℝ) : ℂ) + ((α - p.im : ℝ) : ℂ) * I)⁻¹ := by
      ext x
      apply congrArg Inv.inv
      apply Complex.ext <;> simp
    rw [hfun]
    exact intervalIntegral.integral_comp_sub_right
      (fun u : ℝ ↦ ((u : ℂ) + ((α - p.im : ℝ) : ℂ) * I)⁻¹) p.re
  have hvert : ∀ (β : ℝ),
      ∫ y : ℝ in z.im..w.im, ((β : ℂ) + (y : ℂ) * I - p)⁻¹ =
        ∫ v : ℝ in (z.im - p.im)..(w.im - p.im), (((β - p.re : ℝ) : ℂ) + (v : ℂ) * I)⁻¹ := by
    intro β
    have hfun : (fun y : ℝ ↦ ((β : ℂ) + (y : ℂ) * I - p)⁻¹) =
        fun y : ℝ ↦ (((β - p.re : ℝ) : ℂ) + ((y - p.im : ℝ) : ℂ) * I)⁻¹ := by
      ext y
      apply congrArg Inv.inv
      apply Complex.ext <;> simp
    rw [hfun]
    exact intervalIntegral.integral_comp_sub_right
      (fun v : ℝ ↦ (((β - p.re : ℝ) : ℂ) + (v : ℂ) * I)⁻¹) p.im
  rw [hhoriz z.im, hhoriz w.im, hvert w.re, hvert z.re]
  exact contour_rect_inv_eq_one
    (sub_lt_zero.mpr hzre) (sub_pos.mpr hpre) (sub_lt_zero.mpr hzim) (sub_pos.mpr hpim)

open Complex Real

set_option maxHeartbeats 600000 in
/-- Counterclockwise contour integral on an axis-aligned rectangle with opposite corners
`z` (bottom left) and `w` (top right). -/
noncomputable def rectangleBoundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x+z.im*I)) - (∫ x : ℝ in z.re..w.re, f (x+w.im*I)) +
    I*(∫ y : ℝ in z.im..w.im, f (w.re+y*I)) - I*(∫ y : ℝ in z.im..w.im, f (z.re+y*I))

set_option maxHeartbeats 600000 in
/-- Cauchy's integral formula for an entire function on a rectangular contour. -/
theorem rectangleBoundary_cauchy {f : ℂ → ℂ} (hf : Differentiable ℂ f) {p z w : ℂ}
    (hzre : z.re < p.re) (hpre : p.re < w.re) (hzim : z.im < p.im) (hpim : p.im < w.im) :
    rectangleBoundary (fun u => f u/(u-p)) z w = 2*π*I*f p := by
  let S := dslope f p
  have hS : Differentiable ℂ S := fun v => ((hf.analyticAt v).dslope p).differentiableAt
  have hline (P : ℝ → ℂ) (hP : Continuous P) (h : ∀ x : ℝ, P x ≠ p) (a b : ℝ) :
      (∫ x in a..b, f (P x)/(P x-p)) = (∫ x in a..b, S (P x)) +
        (f p)*(∫ x in a..b, (P x-p)⁻¹) := by
    have he (x : ℝ) : f (P x)/(P x-p) = S (P x) + f p*(P x-p)⁻¹ := by
      rw [show S (P x) = (f (P x)-f p)/(P x-p) by dsimp only [S]; rw [dslope_of_ne _ (h x),slope_def_field]]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
    · exact (hS.continuous.comp hP).intervalIntegrable ..
    · exact (continuous_const.mul ((hP.sub continuous_const).inv₀ (fun x => sub_ne_zero.mpr (h x)))).intervalIntegrable ..
  have hH (a b v : ℝ) (hv : v ≠ p.im) := hline (fun x : ℝ => (x:ℂ)+v*I) (by fun_prop)
    (fun x h => hv (by simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using congrArg Complex.im h)) a b
  have hV (a b v : ℝ) (hv : v ≠ p.re) := hline (fun x : ℝ => (v:ℂ)+x*I) (by fun_prop)
    (fun x h => hv (by simpa using congrArg Complex.re h)) a b
  have hz : rectangleBoundary S z w = 0 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn S z w hS.differentiableOn
  have hi := rectangle_cauchyKernel_eq_one hzre hpre hzim hpim
  change 1/(2*(π:ℂ)*I)*rectangleBoundary (fun u => (u-p)⁻¹) z w = 1 at hi
  have hi' : rectangleBoundary (fun u => (u-p)⁻¹) z w = 2*π*I := by
    have hπ : (2*(π:ℂ)*I) ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    rw [one_div, ← div_eq_inv_mul] at hi
    simpa only [one_mul] using (div_eq_iff hπ).mp hi
  unfold rectangleBoundary at hz hi' ⊢
  rw [hH _ _ _ hzim.ne,hH _ _ _ hpim.ne',hV _ _ _ hpre.ne',hV _ _ _ hzre.ne]
  linear_combination hz + (f p)*hi'

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
