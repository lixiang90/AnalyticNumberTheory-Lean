import AnalyticNumberTheory.AnalyticTools.IntegratedPoleTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real shifts of integrated pole terms

If F is a primitive vanishing at zero, integration by parts expresses
y ∫₀ᵘ exp(−yt)F'(t) dt in terms of F itself. In this form the operation commutes
with a pole series having summable inverse squared radii.
-/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.AnalyticTools

/-- Integration by parts for the real shift on a primitive vanishing at zero. -/
def exponentialShiftOfPrimitive (y u : ℝ) (F : ℝ → ℂ) : ℂ :=
  (y:ℂ)*Complex.exp (-(y:ℂ)*u)*F u +
    (y:ℂ)^2 * ∫ t in (0:ℝ)..u, Complex.exp (-(y:ℂ)*t)*F t

/-- Subtraction of two continuous primitives commutes with the shift. -/
theorem exponentialShiftOfPrimitive_sub (y u : ℝ) {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) :
    exponentialShiftOfPrimitive y u (fun t => F t-G t) =
      exponentialShiftOfPrimitive y u F - exponentialShiftOfPrimitive y u G := by
  unfold exponentialShiftOfPrimitive
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
    ((show Continuous (fun t : ℝ => Complex.exp (-(y:ℂ)*t)*F t) by fun_prop).intervalIntegrable ..)
    ((show Continuous (fun t : ℝ => Complex.exp (-(y:ℂ)*t)*G t) by fun_prop).intervalIntegrable ..)]
  ring

/-- A primitive that vanishes on the entire integration segment has zero shift. -/
theorem exponentialShiftOfPrimitive_eq_zero {u : ℝ} (hu : 0 ≤ u) (y : ℝ) {F : ℝ → ℂ}
    (hF : ∀ t ∈ Icc 0 u, F t = 0) : exponentialShiftOfPrimitive y u F = 0 := by
  have hi : (∫ t in (0:ℝ)..u, Complex.exp (-(y:ℂ)*t)*F t) = 0 := by
    convert intervalIntegral.integral_congr (f := fun t : ℝ => Complex.exp (-(y:ℂ)*t)*F t)
      (g := fun _ => (0:ℂ)) (a := 0) (b := u) (fun t ht => by simp only [hF t (uIcc_of_le hu ▸ ht), mul_zero]) using 1
    simp
  rw [exponentialShiftOfPrimitive, hF u ⟨hu,le_rfl⟩, hi, mul_zero, mul_zero, zero_add]

/-- The shift applied to the linear primitive of a constant. -/
theorem exponentialShiftOfPrimitive_linear {y : ℝ} (hy : 0 < y) (u : ℝ) (c : ℂ) :
    exponentialShiftOfPrimitive y u (fun t => c*(t:ℂ)) =
      c*(1-Complex.exp (-(y:ℂ)*u)) := by
  have hy₀ := Complex.ofReal_ne_zero.mpr hy.ne'
  let E (t : ℝ) := Complex.exp (-(y:ℂ)*t)
  let A (z : ℂ) := Complex.exp (-(y:ℂ)*z)*(z/(-(y:ℂ)) - 1/(y:ℂ)^2)
  have hA (t : ℝ) : HasDerivAt (fun v : ℝ => A v) (E t*(t:ℂ)) t := by
    have h := (((hasDerivAt_id' (t:ℂ)).const_mul (-(y:ℂ))).cexp).mul
      (((hasDerivAt_id' (t:ℂ)).div_const (-(y:ℂ))).sub_const (1/(y:ℂ)^2))
    apply h.comp_ofReal.congr_deriv
    dsimp [E]
    field_simp [hy₀]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := u) (fun t _ => hA t)
    ((show Continuous (fun t : ℝ => E t*(t:ℂ)) by dsimp [E]; fun_prop).intervalIntegrable ..)
  change (y:ℂ)*E u*(c*(u:ℂ))+(y:ℂ)^2*(∫ t in (0:ℝ)..u, E t*(c*(t:ℂ))) = _
  simp_rw [show ∀ t : ℝ, E t*(c*(t:ℂ)) = c*(E t*(t:ℂ)) by intro t; ring]
  rw [intervalIntegral.integral_const_mul,hint]
  simp only [A,E,Complex.ofReal_zero,mul_zero,Complex.exp_zero,zero_div,zero_sub,one_mul]
  field_simp [hy₀]
  ring

/-- For one pole the shift of the integrated kernel is an exponential increment with
denominator ω(ω−y). The additional denominator makes the zero series absolutely summable. -/
theorem exponentialShiftOfPrimitive_integratedPole {ω : ℂ} {u y : ℝ} (hω : ω ≠ 0)
    (hωy : ω ≠ y) (hu : 0 ≤ u) (hy : 0 < y) :
    exponentialShiftOfPrimitive y u (integratedPole ω) =
      (y:ℂ)*(Complex.exp ((ω-y)*u)-1)/(ω*(ω-y)) := by
  have hy₀ := Complex.ofReal_ne_zero.mpr hy.ne'
  have hd := sub_ne_zero.mpr hωy
  let E (c : ℂ) (t : ℝ) := Complex.exp (c*t)
  have hc (c : ℂ) : Continuous (E c) := by dsimp [E]; fun_prop
  have hmul (t : ℝ) : E (-(y:ℂ)) t * E ω t = E (ω-y) t := by
    dsimp only [E]
    rw [←Complex.exp_add]
    congr 1; ring
  have hsplit : (∫ t in (0:ℝ)..u, E (-(y:ℂ)) t * integratedPole ω t) =
      ((∫ t in (0:ℝ)..u, E (ω-y) t) - ∫ t in (0:ℝ)..u, E (-(y:ℂ)) t)/ω^2 := by
    rw [←intervalIntegral.integral_sub ((hc _).intervalIntegrable ..) ((hc _).intervalIntegrable ..),
      ←intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [integratedPole,max_eq_left ((uIcc_of_le hu ▸ ht).1),←hmul]
    change _ * ((E ω t-1)/_) = _
    ring
  unfold exponentialShiftOfPrimitive
  change (y:ℂ)*E (-(y:ℂ)) u*integratedPole ω u + (y:ℂ)^2*(∫ t in (0:ℝ)..u, E (-(y:ℂ)) t*integratedPole ω t) = _
  rw [hsplit,integratedPole,max_eq_left hu]
  simp only [E, integral_exp_mul_complex hd,integral_exp_mul_complex (neg_ne_zero.mpr hy₀),
    Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  rw [← show E (-(y:ℂ)) u * E ω u = Complex.exp ((ω-y)*u) from hmul u]
  dsimp [E]
  field_simp [hy₀,hω,hd]
  ring


/-- The shift commutes with a series of integrated poles bounded to the right and
with summable squared inverse radii. This holds on each finite segment beginning at zero. -/
theorem hasSum_exponentialShiftOfPrimitive_integratedPole {a : ℕ → ℂ} {b u y : ℝ}
    (hb₀ : 0 ≤ b) (hb : ∀ n, (a n).re ≤ b) (hS : Summable fun n => (‖a n‖^2)⁻¹)
    (hu : 0 ≤ u) (hy : 0 ≤ y) :
    HasSum (fun n => exponentialShiftOfPrimitive y u (integratedPole (a n)))
      (exponentialShiftOfPrimitive y u (fun t => ∑' n, integratedPole (a n) t)) := by
  let f (n : ℕ) (t : ℝ) := Complex.exp (-(y:ℂ)*t)*integratedPole (a n) t
  let B (n : ℕ) := (Real.exp (b*u)+1)*(‖a n‖^2)⁻¹
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ Ioc 0 u) : ‖f n t‖ ≤ B n := by
    have hE : ‖Complex.exp (-(y:ℂ)*t)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp [Complex.mul_re, mul_nonneg hy ht.1.le]
    change ‖_ * _‖ ≤ _
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right hE (norm_nonneg _)).trans
    rw [one_mul]
    apply (norm_integratedPole_le (hb n) t).trans
    unfold B
    rw [max_eq_left ht.1.le]
    gcongr
    exact ht.2
  have hi (n : ℕ) : IntegrableOn (f n) (Ioc 0 u) :=
    ((show Continuous (f n) by unfold f integratedPole; fun_prop).intervalIntegrable 0 u).1
  have hsum : Summable fun n => ∫ t in Ioc 0 u, ‖f n t‖ := by
    apply (hS.mul_left ((Real.exp (b*u)+1)*u)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => ‖f n t‖) (a := 0) (b := u)
      (C := B n) (fun t ht => by simpa using hbound n t (uIoc_of_le hu ▸ ht))
    rw [intervalIntegral.integral_of_le hu, Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg _)),
      sub_zero,abs_of_nonneg hu] at H
    exact H.trans_eq (by dsimp [B]; ring)
  have hI := hasSum_integral_of_summable_integral_norm hi hsum
  have h := ((summable_integratedPole hb hS u).hasSum.mul_left
    ((y:ℂ)*Complex.exp (-(y:ℂ)*u))).add (hI.mul_left ((y:ℂ)^2))
  unfold exponentialShiftOfPrimitive
  simp_rw [intervalIntegral.integral_of_le hu]
  rw [show (fun t : ℝ => Complex.exp (-(y:ℂ)*t)*(∑' n, integratedPole (a n) t)) =
    (fun t : ℝ => ∑' n, f n t) from funext fun _ => tsum_mul_left.symm]
  exact h


/-- The Perron residue of a pole after shifting its position from ω to ω−y. -/
def shiftedPoleResidue (ω : ℂ) (y u : ℝ) : ℂ :=
  Complex.exp ((ω-y)*u)/(ω-y)

/-- Remainder after removing the damped unshifted residue. -/
def shiftedPoleCorrection (ω : ℂ) (y u : ℝ) : ℂ :=
  (y:ℂ)*Complex.exp ((ω-y)*u)/(ω*(ω-y))

/-- Subtracting the original residue with the common damping gives a second denominator. -/
theorem shiftedPoleResidue_eq_damped_add {ω : ℂ} {y : ℝ} (u : ℝ) (hω : ω ≠ 0) (hωy : ω ≠ y) :
    shiftedPoleResidue ω y u =
      Complex.exp (-(y:ℂ)*u)*(Complex.exp (ω*u)/ω) + shiftedPoleCorrection ω y u := by
  have h : Complex.exp ((ω-y)*u) = Complex.exp (-(y:ℂ)*u)*Complex.exp (ω*u) := by
    rw [← Complex.exp_add]
    congr 1; ring
  rw [shiftedPoleResidue,shiftedPoleCorrection,h]
  field_simp [hω,sub_ne_zero.mpr hωy]
  ring

/-- Shifting the integrated pole gives the residue correction plus its centered partial fraction. -/
theorem exponentialShiftOfPrimitive_integratedPole_eq_centered {ω : ℂ} {y u : ℝ}
    (hω : ω ≠ 0) (hωy : ω ≠ y) (hu : 0 ≤ u) (hy : 0 < y) :
    exponentialShiftOfPrimitive y u (integratedPole ω) = shiftedPoleCorrection ω y u + centeredPole ω y := by
  rw [exponentialShiftOfPrimitive_integratedPole hω hωy hu hy, shiftedPoleCorrection, centeredPole]
  field_simp [hω,sub_ne_zero.mpr hωy,sub_ne_zero.mpr hωy.symm]
  ring

/-- For a summable family of centered fractions, the exponential corrections also
sum and their total is determined by the shift of the integrated family. -/
theorem hasSum_shiftedPoleCorrection {a : ℕ → ℂ} {b u y : ℝ}
    (hb₀ : 0 ≤ b) (hb : ∀ n, (a n).re ≤ b) (hS : Summable fun n => (‖a n‖^2)⁻¹)
    (ha : ∀ n, a n ≠ 0) (hay : ∀ n, a n ≠ y) (hC : Summable fun n => centeredPole (a n) y)
    (hu : 0 ≤ u) (hy : 0 < y) :
    HasSum (fun n => shiftedPoleCorrection (a n) y u)
      (exponentialShiftOfPrimitive y u (fun t => ∑' n, integratedPole (a n) t) -
        ∑' n, centeredPole (a n) y) := by
  apply ((hasSum_exponentialShiftOfPrimitive_integratedPole hb₀ hb hS hu hy.le).sub hC.hasSum).congr_fun
  intro n
  simp only [exponentialShiftOfPrimitive_integratedPole_eq_centered (ha n) (hay n) hu hy,add_sub_cancel_right]

end AnalyticNumberTheory.AnalyticTools
