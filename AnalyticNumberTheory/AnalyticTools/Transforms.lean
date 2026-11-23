import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Analytic Integral Transforms

This file collects foundational identities and bridges for the Mellin, Fourier, and Laplace
transforms used across analytic number theory:

- Scaling, shift, reflection, differentiation, and inversion identities for `mellin` and `mellinInv`.
- The Mellin transform of `exp (-a * t)` and `exp (-a * t ^ 2)` in terms of `Complex.Gamma` and
  `Complex.Gammaℝ`, plus the Laplace transform bridge.
- 1D Fourier transform scaling, translation, modulation, inversion, and Gaussian identities.
- Mellin–Dirichlet series bridges wrapping `Mathlib.NumberTheory.LSeries.MellinEqDirichlet`,
  including the classical integral representations of `Gamma s * riemannZeta s` and
  `Gammaℝ s * riemannZeta s`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

namespace AnalyticNumberTheory.AnalyticTools

section MellinAlgebra

/-- Linearity of the Mellin transform under addition when both transforms converge. -/
theorem mellin_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℝ → E} {s : ℂ} (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (fun t => f t + g t) s = mellin f s + mellin g s :=
  (hasMellin_add hf hg).2

/-- Linearity of the Mellin transform under subtraction when both transforms converge. -/
theorem mellin_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℝ → E} {s : ℂ} (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (fun t => f t - g t) s = mellin f s - mellin g s :=
  (hasMellin_sub hf hg).2

/-- Scalar homogeneity of the Mellin transform. -/
theorem mellin_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) (c : ℂ) :
    mellin (fun t => c • f t) s = c • mellin f s :=
  mellin_const_smul f s c

/-- Shift property of the Mellin transform: multiplying by `t ^ a` shifts `s` to `s + a`. -/
theorem mellin_shift (f : ℝ → ℂ) (s a : ℂ) :
    mellin (fun t : ℝ => (t : ℂ) ^ a * f t) s = mellin f (s + a) := by
  simpa only [smul_eq_mul] using mellin_cpow_smul f s a

/-- `HasMellin` version of the power-shift identity. -/
theorem hasMellin_shift {f : ℝ → ℂ} {s a m : ℂ} (h : HasMellin f (s + a) m) :
    HasMellin (fun t : ℝ => (t : ℂ) ^ a * f t) s m := by
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using MellinConvergent.cpow_smul.mpr h.1
  · simpa only [mellin_shift] using h.2

/-- Left-scaling identity for the complex-valued Mellin transform (`0 < a`). -/
theorem mellin_scale_left (f : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun t => f (a * t)) s = (a : ℂ) ^ (-s) * mellin f s := by
  simpa only [smul_eq_mul] using mellin_comp_mul_left f s ha

/-- Right-scaling identity for the complex-valued Mellin transform (`0 < a`). -/
theorem mellin_scale_right (f : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun t => f (t * a)) s = (a : ℂ) ^ (-s) * mellin f s := by
  simpa only [smul_eq_mul] using mellin_comp_mul_right f s ha

/-- `HasMellin` version of the left-scaling identity (`0 < a`). -/
theorem hasMellin_scale_left {f : ℝ → ℂ} {s m : ℂ} {a : ℝ} (ha : 0 < a)
    (h : HasMellin f s m) :
    HasMellin (fun t => f (a * t)) s ((a : ℂ) ^ (-s) * m) := by
  refine ⟨(MellinConvergent.comp_mul_left ha).mpr h.1, ?_⟩
  rw [mellin_scale_left f s ha, h.2]

/-- Reflection identity for the Mellin transform under `t ↦ t⁻¹`. -/
theorem mellin_inv_arg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) :
    mellin (fun t => f t⁻¹) s = mellin f (-s) :=
  mellin_comp_inv f s

/-- Convergence equivalence for the Mellin transform under `t ↦ t⁻¹`. -/
theorem mellinConvergent_inv_arg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {s : ℂ} :
    MellinConvergent (fun t => f t⁻¹) s ↔ MellinConvergent f (-s) := by
  have h := MellinConvergent.comp_rpow (f := f) (s := s) (a := (-1 : ℝ)) (by norm_num)
  simpa only [Real.rpow_neg_one, Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using h

/-- `HasMellin` version of the reflection identity `t ↦ t⁻¹`. -/
theorem hasMellin_inv_arg {f : ℝ → ℂ} {s m : ℂ} (h : HasMellin f (-s) m) :
    HasMellin (fun t => f t⁻¹) s m :=
  ⟨mellinConvergent_inv_arg.mpr h.1, (mellin_inv_arg f s).trans h.2⟩

/-- Power-substitution identity for the complex-valued Mellin transform (`a ≠ 0`). -/
theorem mellin_rpow_arg (f : ℝ → ℂ) (s : ℂ) (a : ℝ) :
    mellin (fun t => f (t ^ a)) s = (|a|⁻¹ : ℝ) • mellin f (s / a) :=
  mellin_comp_rpow f s a

/-- `HasMellin` version of the power-substitution identity (`a ≠ 0`). -/
theorem hasMellin_rpow_arg {f : ℝ → ℂ} {s m : ℂ} {a : ℝ} (ha : a ≠ 0)
    (h : HasMellin f (s / a) m) :
    HasMellin (fun t => f (t ^ a)) s (((|a|⁻¹ : ℝ) : ℂ) * m) := by
  refine ⟨(MellinConvergent.comp_rpow ha).mpr h.1, ?_⟩
  rw [mellin_rpow_arg, h.2, Complex.real_smul]

end MellinAlgebra

section MellinAnalyticityAndInversion

/-- On any strip `b < s.re < a` dictated by asymptotics at `0` and `∞`, `mellin f` is complex
differentiable and its derivative is the Mellin transform of `t ↦ Real.log t • f t`. -/
theorem mellin_hasDerivAt_strip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℝ} {f : ℝ → E} {s : ℂ}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf_top : f =O[atTop] (· ^ (-a))) (hs_top : s.re < a)
    (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    MellinConvergent (fun t => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t => Real.log t • f t) s) s :=
  mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot

/-- Holomorphicity of `mellin f` on the open vertical strip `{s : ℂ | b < s.re ∧ s.re < a}`. -/
theorem mellin_differentiableOn_strip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℝ} {f : ℝ → E}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf_top : f =O[atTop] (· ^ (-a))) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) :
    DifferentiableOn ℂ (mellin f) {s : ℂ | b < s.re ∧ s.re < a} :=
  fun _ hs => (mellin_differentiableAt_of_isBigO_rpow hfc hf_top hs.2 hf_bot hs.1).differentiableWithinAt

/-- Holomorphicity of `mellin f` on the open right half-plane `{s : ℂ | b < s.re}` under
exponential decay at infinity. -/
theorem mellin_differentiableOn_halfPlane {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℝ} (ha : 0 < a) {f : ℝ → E}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf_top : f =O[atTop] fun t => Real.exp (-a * t)) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) :
    DifferentiableOn ℂ (mellin f) {s : ℂ | b < s.re} :=
  fun _ hs => (mellin_differentiableAt_of_isBigO_rpow_exp ha hfc hf_top hf_bot hs).differentiableWithinAt

/-- Mellin–Fourier bridge: `mellin f s` expressed as a 1D Fourier transform of an exponentially
rescaled pullback. -/
theorem mellin_eq_fourier_bridge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) :
    mellin f s = 𝓕 (fun u : ℝ => Real.exp (-s.re * u) • f (Real.exp (-u))) (s.im / (2 * Real.pi)) :=
  mellin_eq_fourier f

/-- Mellin inversion theorem on the vertical line `Re z = σ` for continuous functions whose Mellin
transform is vertically integrable. -/
theorem mellin_inversion_bridge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x)
    (hf : MellinConvergent f σ) (hFf : Complex.VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x :=
  mellinInv_mellin_eq σ f hx hf hFf hfx

end MellinAnalyticityAndInversion

section GammaAndLaplace

/-- Convergence of the Mellin transform of `t ↦ Real.exp (-a * t)` for `0 < a` and `0 < s.re`. -/
theorem mellinConvergent_exp_neg_mul {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => (Real.exp (-a * t) : ℂ)) s := by
  refine mellinConvergent_of_isBigO_rpow_exp ha (b := 0) ?_ ?_ ?_ hs
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun t => ?_⟩
    simp only [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul, le_refl]
  · refine isBigO_iff.mpr ⟨1, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
    have ht0 : 0 < t := ht
    have hexp : Real.exp (-a * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul, neg_zero,
      Real.rpow_zero, norm_one]
    exact hexp

/-- The Mellin transform of `t ↦ Real.exp (-a * t)` for `0 < a` and `0 < s.re` equals
`(a : ℂ) ^ (-s) * Complex.Gamma s`. -/
theorem mellin_exp_neg_mul {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-a * t) : ℂ)) s = (a : ℂ) ^ (-s) * Complex.Gamma s := by
  have h1 : mellin (fun t : ℝ => (Real.exp (-a * t) : ℂ)) s =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-((a : ℂ) * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only
    rw [smul_eq_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [h1, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha, one_div, Complex.cpow_neg,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne)]

/-- `HasMellin` form of the Mellin transform of `t ↦ Real.exp (-a * t)`. -/
theorem hasMellin_exp_neg_mul {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (Real.exp (-a * t) : ℂ)) s ((a : ℂ) ^ (-s) * Complex.Gamma s) :=
  ⟨mellinConvergent_exp_neg_mul ha hs, mellin_exp_neg_mul ha hs⟩

/-- The Mellin transform of `t ↦ Real.exp (-t)` equals `Complex.Gamma s` for `0 < s.re`. -/
theorem mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) s = Complex.Gamma s := by
  simpa only [neg_one_mul, Complex.ofReal_one, Complex.one_cpow, one_mul] using
    mellin_exp_neg_mul zero_lt_one hs

/-- Complex-exponential variant of `mellin_exp_neg_mul` for `0 < a` and `0 < s.re`. -/
theorem mellin_cexp_neg_mul {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => Complex.exp (-(a : ℂ) * t)) s = (a : ℂ) ^ (-s) * Complex.Gamma s := by
  have hcongr : (fun t : ℝ => Complex.exp (-(a : ℂ) * t)) =
      fun t : ℝ => (Real.exp (-a * t) : ℂ) := by
    ext t
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcongr, mellin_exp_neg_mul ha hs]

/-- Mellin transform of the Gaussian `t ↦ Real.exp (-a * t ^ 2)` for `0 < a` and `0 < s.re`. -/
theorem mellin_gaussian {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-a * t ^ 2) : ℂ)) s =
      (1 / 2 : ℂ) * (a : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2) := by
  have heq : mellin (fun t : ℝ => (Real.exp (-a * t ^ 2) : ℂ)) s =
      mellin (fun t : ℝ => (Real.exp (-a * (t ^ (2 : ℝ))) : ℂ)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only
    rw [Real.rpow_two]
  have hs2 : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    exact half_pos hs
  rw [heq, mellin_comp_rpow (fun u : ℝ => (Real.exp (-a * u) : ℂ)) s 2]
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [h2, mellin_exp_neg_mul ha hs2, Complex.real_smul]
  norm_num [mul_assoc]

/-- Twice the Mellin transform of `t ↦ Real.exp (-π * t ^ 2)` equals `Complex.Gammaℝ s`. -/
theorem two_mul_mellin_gaussian_pi {s : ℂ} (hs : 0 < s.re) :
    2 * mellin (fun t : ℝ => (Real.exp (-Real.pi * t ^ 2) : ℂ)) s = Complex.Gammaℝ s := by
  rw [mellin_gaussian Real.pi_pos hs, Complex.Gammaℝ_def]
  have h : (2 : ℂ) * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)) =
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    ring_nf
  exact h

/-- The Laplace transform of `f : ℝ → ℂ` at `z : ℂ`, defined over `Ioi 0`. -/
def laplaceTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-z * t) * f t

/-- The Laplace transform of `t ↦ (t : ℂ) ^ (s - 1)` at a positive real parameter `a` equals
`(a : ℂ) ^ (-s) * Complex.Gamma s` for `0 < s.re`. -/
theorem laplaceTransform_cpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t : ℝ => (t : ℂ) ^ (s - 1)) a = (a : ℂ) ^ (-s) * Complex.Gamma s := by
  have hcongr : laplaceTransform (fun t : ℝ => (t : ℂ) ^ (s - 1)) a =
      mellin (fun t : ℝ => Complex.exp (-(a : ℂ) * t)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hcongr, mellin_cexp_neg_mul ha hs]

end GammaAndLaplace

section FourierBridges

/-- Scaling identity for the 1D Fourier transform on `ℝ` (`a ≠ 0`). -/
theorem fourier_scale (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (w : ℝ) :
    𝓕 (fun x : ℝ => f (a * x)) w = ((|a|⁻¹ : ℝ) : ℂ) * 𝓕 f (w / a) := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have h : ∀ x : ℝ, Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) * f (a * x) =
      (fun u : ℝ => Complex.exp ((-2 * Real.pi * u * (w / a) : ℝ) * Complex.I) * f u) (a * x) := by
    intro x
    congr 3
    field_simp [ha]
  simp_rw [h]
  rw [Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp ((-2 * Real.pi * u * (w / a) : ℝ) * Complex.I) * f u) a,
    Complex.real_smul, abs_inv]

/-- Translation identity for the 1D Fourier transform on `ℝ`. -/
theorem fourier_translate (f : ℝ → ℂ) (x₀ w : ℝ) :
    𝓕 (fun x : ℝ => f (x + x₀)) w = (Real.fourierChar (x₀ * w) : ℂ) * 𝓕 f w := by
  have h := Fourier.fourierIntegral_comp_add_right Real.fourierChar volume f x₀
  have hw := congr_fun h w
  simpa [Fourier.fourierIntegral, VectorFourier.fourierIntegral, Real.fourier_real_eq,
    Circle.smul_def, smul_eq_mul] using hw

/-- Modulation identity for the 1D Fourier transform on `ℝ`. -/
theorem fourier_modulate (f : ℝ → ℂ) (ξ₀ w : ℝ) :
    𝓕 (fun x : ℝ => (Real.fourierChar (x * ξ₀) : ℂ) * f x) w = 𝓕 f (w - ξ₀) := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, Real.fourierChar_apply]
  congr 1 with x
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Complex-parameter Gaussian Fourier transform identity (`0 < b.re`), wrapping
`fourier_gaussian_pi`. -/
theorem fourier_gaussian_pi_bridge {b : ℂ} (hb : 0 < b.re) (w : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) w =
      1 / b ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / b * (w : ℂ) ^ 2) :=
  congr_fun (fourier_gaussian_pi hb) w

/-- Real-parameter Gaussian Fourier transform identity (`0 < a`). -/
theorem fourier_gaussian_real {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (fun x : ℝ => (Real.exp (-a * x ^ 2) : ℂ)) w =
      (((Real.pi / a) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-(Real.pi ^ 2 * (w : ℂ) ^ 2 / a)) := by
  let b : ℂ := (a / Real.pi : ℝ)
  have hb : 0 < b.re := by
    simp only [b, Complex.ofReal_re]
    positivity
  have hfun : (fun x : ℝ => (Real.exp (-a * x ^ 2) : ℂ)) =
      fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2) := by
    ext x
    rw [Complex.ofReal_exp]
    congr 1
    simp only [b, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp [Real.pi_ne_zero]
  rw [hfun, fourier_gaussian_pi_bridge hb w]
  have hb_nonneg : 0 ≤ (a / Real.pi) := by positivity
  have hpow : (1 : ℂ) / b ^ (1 / 2 : ℂ) = (((Real.pi / a) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    have hpi : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by norm_num
    simp only [b]
    rw [hpi, ← Complex.ofReal_cpow hb_nonneg, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Complex.ofReal_inj, one_div, ← Real.inv_rpow hb_nonneg, inv_div]
  rw [hpow]
  congr 2
  simp only [b, Complex.ofReal_div]
  field_simp [Real.pi_ne_zero, ha.ne']

/-- The standard Gaussian `x ↦ exp (-π * x ^ 2)` is an eigenfunction of the 1D Fourier transform
with eigenvalue `1`. -/
theorem fourier_gaussian_selfReciprocal :
    𝓕 (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) =
      fun w : ℝ => (Real.exp (-Real.pi * w ^ 2) : ℂ) := by
  ext w
  have hb : (0 : ℝ) < (1 : ℂ).re := by simp
  have h := congr_fun (fourier_gaussian_pi hb) w
  simpa [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow] using h

/-- 1D Fourier inversion formula for integrable functions with integrable Fourier transform. -/
theorem fourier_inversion {f : ℝ → ℂ} (hf : Integrable f) (hFf : Integrable (𝓕 f))
    {x : ℝ} (hx : ContinuousAt f x) :
    𝓕⁻ (𝓕 f) x = f x :=
  hf.fourierInv_fourier_eq hFf hx

/-- Iterated 1D Fourier transform identity `𝓕 (𝓕 f) x = f (-x)`. -/
theorem fourier_fourier_eq_neg {f : ℝ → ℂ} (hf : Integrable f) (hFf : Integrable (𝓕 f))
    {x : ℝ} (hx : ContinuousAt f (-x)) :
    𝓕 (𝓕 f) x = f (-x) := by
  rw [← neg_neg x, ← Real.fourierInv_eq_fourier_neg (𝓕 f) (-x), neg_neg]
  exact hf.fourierInv_fourier_eq hFf hx

end FourierBridges

section MellinDirichlet

/-- General Mellin–Dirichlet series bridge: for `0 < s.re`, the Mellin transform of a Dirichlet
exponential series equals `Complex.Gamma s` times the corresponding Dirichlet series. -/
theorem mellin_tsum_exp_neg_mul {ι : Type*} [Countable ι]
    {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i => a i * Real.exp (-p i * t)) (F t))
    (h_sum : Summable fun i => ‖a i‖ / (p i) ^ s.re) :
    HasSum (fun i => Complex.Gamma s * a i / (p i : ℂ) ^ s) (mellin F s) :=
  hasSum_mellin hp hs hF h_sum

/-- Evaluated `tsum` form of the Mellin–Dirichlet bridge. -/
theorem mellin_tsum_exp_neg_mul_eq {ι : Type*} [Countable ι]
    {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i => a i * Real.exp (-p i * t)) (F t))
    (h_sum : Summable fun i => ‖a i‖ / (p i) ^ s.re) :
    mellin F s = Complex.Gamma s * ∑' i, a i / (p i : ℂ) ^ s := by
  rw [← (mellin_tsum_exp_neg_mul hp hs hF h_sum).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  ring

/-- Mellin transform of an even quadratic theta series equals `Complex.Gammaℝ s` times the
corresponding Dirichlet series. -/
theorem mellin_tsum_pi_mul_sq_eq {ι : Type*} [Countable ι]
    {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i => if r i = 0 then 0 else a i * Real.exp (-Real.pi * r i ^ 2 * t)) (F t))
    (h_sum : Summable fun i => ‖a i‖ / |r i| ^ s.re) :
    mellin F (s / 2) = Complex.Gammaℝ s * ∑' i, a i / ((|r i| : ℝ) : ℂ) ^ s := by
  have h := hasSum_mellin_pi_mul_sq hs hF h_sum
  rw [← h.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  ring

/-- Classical Mellin integral representation of `Complex.Gamma s * riemannZeta s` for
`1 < s.re`: `mellin (fun t => (1 / (Real.exp t - 1) : ℂ)) s = Complex.Gamma s * riemannZeta s`. -/
theorem mellin_inv_exp_sub_one_eq_gamma_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => (1 / (Real.exp t - 1) : ℂ)) s = Complex.Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (1 : ℂ) * Real.exp (-(n + 1 : ℝ) * t))
        ((1 / (Real.exp t - 1) : ℂ)) := by
    intro t ht
    have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
    have hnonneg : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hgeom : HasSum (fun n : ℕ => Real.exp (-t) ^ n * Real.exp (-t))
        ((1 - Real.exp (-t))⁻¹ * Real.exp (-t)) :=
      (hasSum_geometric_of_lt_one hnonneg hlt).mul_right (Real.exp (-t))
    have hval : ((1 - Real.exp (-t))⁻¹ * Real.exp (-t) : ℝ) = 1 / (Real.exp t - 1) := by
      have hpos : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
      rw [Real.exp_neg]
      field_simp [hpos.ne', (Real.exp_pos t).ne']
    have hgeomC := Complex.ofRealCLM.hasSum hgeom
    simp only [Complex.ofRealCLM_apply] at hgeomC
    rw [hval] at hgeomC
    have hcast : ((1 / (Real.exp t - 1) : ℝ) : ℂ) = 1 / ((Real.exp t : ℂ) - 1) := by
      push_cast; rfl
    rw [hcast] at hgeomC
    refine hgeomC.congr_fun fun n => ?_
    rw [one_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    ring
  have hsum : Summable fun n : ℕ => ‖(1 : ℂ)‖ / (n + 1 : ℝ) ^ s.re := by
    have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
    refine h.congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [norm_one, abs_of_pos hpos]
  have hM := mellin_tsum_exp_neg_mul_eq (a := fun _ : ℕ => (1 : ℂ))
    (p := fun n : ℕ => (n + 1 : ℝ)) (F := fun t : ℝ => (1 / (Real.exp t - 1) : ℂ))
    (fun n => Or.inr (by positivity)) hs0 hF hsum
  rw [hM, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  congr 2 with n
  norm_cast

/-- Classical Mellin representation of the completed zeta factor `Gammaℝ s * riemannZeta s` via
the theta tail `∑' n : ℕ, Real.exp (-π * (n + 1)^2 * t)` for `1 < s.re`. -/
theorem mellin_theta_tail_eq_gammaR_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => ∑' n : ℕ, (Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t) : ℂ)) (s / 2) =
      Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hsum_nat : Summable fun n : ℕ => ‖(1 : ℂ)‖ / |((n : ℝ) + 1)| ^ s.re := by
    simpa only [norm_one] using (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => if (n + 1 : ℝ) = 0 then (0 : ℂ)
        else (1 : ℂ) * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t))
        (∑' n : ℕ, (Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t) : ℂ)) := by
    intro t ht
    have hsumm : Summable fun n : ℕ => (Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t) : ℂ) := by
      refine Summable.of_norm ?_
      have hdom : Summable fun n : ℕ => Real.exp (-Real.pi * t) ^ (n + 1) := by
        have hpos : 0 ≤ Real.exp (-Real.pi * t) := (Real.exp_pos _).le
        have hlt : Real.exp (-Real.pi * t) < 1 :=
          Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, show 0 < t from ht])
        exact (hasSum_geometric_of_lt_one hpos hlt).summable.comp_injective Nat.succ_injective
      refine hdom.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have hn : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
        nlinarith [show (0 : ℝ) ≤ n by positivity]
      have hpi : 0 < Real.pi * t := mul_pos Real.pi_pos ht
      calc
        -Real.pi * ((n : ℝ) + 1) ^ 2 * t
            = -(Real.pi * t) * ((n : ℝ) + 1) ^ 2 := by ring
        _ ≤ -(Real.pi * t) * ((n : ℝ) + 1) := by
            exact mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr hpi.le)
        _ = ((n + 1 : ℕ) : ℝ) * (-Real.pi * t) := by push_cast; ring
    refine hsumm.hasSum.congr_fun fun n => ?_
    have hne : (n + 1 : ℝ) ≠ 0 := by positivity
    simp [hne]
  have hM := mellin_tsum_pi_mul_sq_eq (a := fun _ : ℕ => (1 : ℂ))
    (r := fun n : ℕ => (n + 1 : ℝ))
    (F := fun t : ℝ => ∑' n : ℕ, (Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t) : ℂ))
    hs0 hF hsum_nat
  rw [hM, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  congr 2 with n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_of_pos hpos]
  norm_cast

end MellinDirichlet

end AnalyticNumberTheory.AnalyticTools
