/-
Copyright (c) 2026 AnalyticNumberTheory-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AnalyticNumberTheory.ModularAndPartitions.DedekindSums
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.Tactic

/-!
# Dedekind Eta Function and Modular Discriminant

This file develops the theory of the Dedekind eta function `η(τ)` and the modular
discriminant `Δ(τ) = η(τ) ^ 24` on the upper half-plane `ℍ`:

- Infinite product representation `η(τ) = exp(π i τ / 12) ∏' n, (1 - exp(2 π i (n + 1) τ))`,
  non-vanishing, holomorphicity / `MDifferentiable`, and decay at `i∞`.
- Translation laws `η(τ + 1) = exp(π i / 12) η(τ)` and `η(τ + k) = exp(k π i / 12) η(τ)`.
- Inversion law `η(-1 / τ) = (-i τ) ^ (1 / 2) * η(τ)` using the principal branch of the
  square root, and the cocycle identity for `(-i (c τ + d)) ^ (1 / 2)`.
- Logarithmic derivative `logDeriv η(τ) = (π i / 12) E₂(τ)` and its q-series / value at `i`.
- Complete `SL(2, ℤ)` transformation law for `η` involving the Dedekind sums `dedekindSum`
  (covering `c = 0`, `c > 0`, and `c < 0`, plus the Rademacher multiplier integrality).
- Weight-12 modular invariance of `Δ(τ) = η(τ) ^ 24` under `SL(2, ℤ)` and bridge to
  `ModularForm.discriminant` and `CuspForm.discriminant`.
-/

noncomputable section

open Complex Filter Function Set Topology
open UpperHalfPlane hiding I
open ModularForm ModularGroup SlashInvariantForm
open scoped BigOperators Manifold MatrixGroups Real ArithmeticFunction.sigma

namespace AnalyticNumberTheory.ModularAndPartitions

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

section DefinitionAndProduct

/-- The Dedekind eta function restricted to the upper half-plane `ℍ`. -/
def dedekindEta (τ : ℍ) : ℂ :=
  ModularForm.eta (τ : ℂ)

/-- Unfolding lemma equating `dedekindEta τ` with `ModularForm.eta (τ : ℂ)`. -/
@[simp]
lemma dedekindEta_eq (τ : ℍ) : dedekindEta τ = ModularForm.eta (τ : ℂ) :=
  rfl

/-- Explicit exponential and infinite product representation of `ModularForm.eta` on `ℂ`. -/
theorem eta_eq_cexp_mul_tprod (z : ℂ) :
    ModularForm.eta z =
      Complex.exp (π * Complex.I * z / 12) *
        ∏' n : ℕ, (1 - Complex.exp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) := by
  have h1 : 𝕢 24 z = Complex.exp (π * Complex.I * z / 12) := by
    simp only [Periodic.qParam]
    congr 1
    push_cast
    ring
  have h2 :
      (∏' n : ℕ, (1 - ModularForm.eta_q n z)) =
        ∏' n : ℕ, (1 - Complex.exp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) := by
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_cexp]
  rw [ModularForm.eta, h1, h2]

/-- Explicit exponential and infinite product representation of `dedekindEta` on `ℍ`. -/
theorem dedekindEta_eq_cexp_mul_tprod (τ : ℍ) :
    dedekindEta τ =
      Complex.exp (π * Complex.I * (τ : ℂ) / 12) *
        ∏' n : ℕ, (1 - Complex.exp (2 * π * Complex.I * ((n : ℂ) + 1) * (τ : ℂ))) :=
  eta_eq_cexp_mul_tprod (τ : ℂ)

/-- Q-parameter infinite product representation of `dedekindEta` on `ℍ`. -/
theorem dedekindEta_eq_qParam (τ : ℍ) :
    dedekindEta τ =
      Complex.exp (π * Complex.I * (τ : ℂ) / 12) *
        ∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1)) := by
  have h1 : 𝕢 24 (τ : ℂ) = Complex.exp (π * Complex.I * (τ : ℂ) / 12) := by
    simp only [Periodic.qParam]
    congr 1
    push_cast
    ring
  have h2 :
      (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) =
        ∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1)) :=
    tprod_congr fun n => by rw [ModularForm.eta_q]
  rw [dedekindEta_eq, ModularForm.eta, h1, h2]

/-- The infinite product factors defining `ModularForm.eta` are multipliable on `ℍₒ`. -/
theorem eta_multipliable {z : ℂ} (hz : z ∈ ℍₒ) :
    Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n z) :=
  ModularForm.multipliableLocallyUniformlyOn_eta.multipliable hz

/-- The q-product factors `1 - 𝕢 1 τ ^ (n + 1)` are multipliable for every `τ : ℍ`. -/
theorem dedekindEta_multipliable (τ : ℍ) :
    Multipliable (fun n : ℕ => 1 - 𝕢 1 (τ : ℂ) ^ (n + 1)) := by
  simpa only [ModularForm.eta_q] using eta_multipliable τ.2

/-- Each factor `1 - 𝕢 1 τ ^ (n + 1)` in the Dedekind eta product is nonzero on `ℍ`. -/
theorem one_sub_qParam_pow_ne_zero (τ : ℍ) (n : ℕ) :
    1 - 𝕢 1 (τ : ℂ) ^ (n + 1) ≠ 0 := by
  simpa only [ModularForm.eta_q] using ModularForm.one_sub_eta_q_ne_zero n τ.2

/-- `ModularForm.eta` is non-vanishing on the upper half-plane set `ℍₒ`. -/
theorem eta_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : ModularForm.eta z ≠ 0 :=
  ModularForm.eta_ne_zero hz

/-- `dedekindEta τ` never vanishes for `τ : ℍ`. -/
theorem dedekindEta_ne_zero (τ : ℍ) : dedekindEta τ ≠ 0 :=
  ModularForm.eta_ne_zero τ.2

/-- `ModularForm.eta` is complex differentiable at every point with positive imaginary part. -/
theorem differentiableAt_eta_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ ModularForm.eta z :=
  ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz

/-- `ModularForm.eta` is holomorphic (`DifferentiableOn`) on the open upper half-plane `ℍₒ`. -/
theorem differentiableOn_eta : DifferentiableOn ℂ ModularForm.eta ℍₒ :=
  fun _ hz => (differentiableAt_eta_of_im_pos hz).differentiableWithinAt

/-- `ModularForm.eta` is complex analytic at every point with positive imaginary part. -/
theorem analyticAt_eta_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ ModularForm.eta z :=
  differentiableOn_eta.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)

/-- `dedekindEta` is manifold-holomorphic (`MDifferentiable`) on `ℍ`. -/
theorem mdifferentiable_dedekindEta : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) dedekindEta := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr differentiableOn_eta fun z hz => ?_
  simp only [Function.comp_apply, dedekindEta_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- `dedekindEta` is continuous on `ℍ`. -/
theorem continuous_dedekindEta : Continuous dedekindEta :=
  mdifferentiable_dedekindEta.continuous

/-- The infinite product `∏' n, (1 - 𝕢 1 τ ^ (n + 1))` tends to `1` as `im τ → ∞`. -/
theorem tendsto_dedekindEta_tprod_atImInfty :
    Tendsto (fun τ : ℍ => ∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) atImInfty (𝓝 1) := by
  have htprod : Tendsto (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have hdom := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 (0 : ℂ)) (g := 0)
      (f := fun (q : ℂ) (n : ℕ) => -q ^ (n + 1)) (bound := fun n => (1 / 2 : ℝ) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at hdom
    simp_rw [sub_eq_add_neg]
    refine hdom
      (by simpa only [pow_succ'] using
        (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _)
      (fun k => by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  simpa only [Function.comp_def] using
    htprod.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)

/-- `dedekindEta τ` tends to `0` as `im τ → ∞`. -/
theorem tendsto_dedekindEta_atImInfty : Tendsto dedekindEta atImInfty (𝓝 0) := by
  have hpref :
      Tendsto (fun τ : ℍ => Complex.exp (π * Complex.I * (τ : ℂ) / 12)) atImInfty (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm :
        (fun τ : ℍ => ‖Complex.exp (π * Complex.I * (τ : ℂ) / 12)‖) =
          fun τ : ℍ => Real.exp (-(π / 12 * τ.im)) := by
      ext τ
      rw [Complex.norm_exp]
      congr 1
      have hre : (π * Complex.I * (τ : ℂ) / 12).re = -(π / 12 * τ.im) := by
        rw [div_eq_mul_inv]
        norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_im]
        ring
      exact hre
    rw [hnorm]
    have hmul :
        Tendsto (fun τ : ℍ => -(π / 12 * τ.im)) atImInfty atBot := by
      have hid : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
      have hpos : 0 < π / 12 := by positivity
      exact Filter.tendsto_neg_atTop_atBot.comp (hid.const_mul_atTop hpos)
    exact Real.tendsto_exp_atBot.comp hmul
  simpa using (hpref.mul tendsto_dedekindEta_tprod_atImInfty).congr fun τ =>
    (dedekindEta_eq_qParam τ).symm

end DefinitionAndProduct

section Translation

private lemma eta_q_add_one (n : ℕ) (z : ℂ) :
    ModularForm.eta_q n (z + 1) = ModularForm.eta_q n z := by
  have hq : Complex.exp (2 * π * Complex.I * (z + 1)) = Complex.exp (2 * π * Complex.I * z) := by
    rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [ModularForm.eta_q_eq_pow, ModularForm.eta_q_eq_pow, hq]

private lemma eta_q_add_int (n : ℕ) (z : ℂ) (k : ℤ) :
    ModularForm.eta_q n (z + (k : ℂ)) = ModularForm.eta_q n z := by
  have hq :
      Complex.exp (2 * π * Complex.I * (z + (k : ℂ))) = Complex.exp (2 * π * Complex.I * z) := by
    rw [mul_add, Complex.exp_add]
    have hper : Complex.exp (2 * π * Complex.I * (k : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * π * Complex.I) by ring,
        Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    rw [hper, mul_one]
  rw [ModularForm.eta_q_eq_pow, ModularForm.eta_q_eq_pow, hq]

/-- Translation identity for `ModularForm.eta`: `η(z + 1) = exp(π i / 12) * η(z)`. -/
theorem eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) = Complex.exp (π * Complex.I / 12) * ModularForm.eta z := by
  have hpref : 𝕢 24 (z + 1) = Complex.exp (π * Complex.I / 12) * 𝕢 24 z := by
    simp only [Periodic.qParam]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hprod :
      (∏' n : ℕ, (1 - ModularForm.eta_q n (z + 1))) =
        ∏' n : ℕ, (1 - ModularForm.eta_q n z) :=
    tprod_congr fun n => by rw [eta_q_add_one n z]
  rw [ModularForm.eta, ModularForm.eta, hpref, hprod, mul_assoc]

/-- Integer translation identity: `η(z + k) = exp(k π i / 12) * η(z)`. -/
theorem eta_add_int (z : ℂ) (k : ℤ) :
    ModularForm.eta (z + (k : ℂ)) =
      Complex.exp ((k : ℂ) * π * Complex.I / 12) * ModularForm.eta z := by
  have hpref : 𝕢 24 (z + (k : ℂ)) =
      Complex.exp ((k : ℂ) * π * Complex.I / 12) * 𝕢 24 z := by
    simp only [Periodic.qParam]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hprod :
      (∏' n : ℕ, (1 - ModularForm.eta_q n (z + (k : ℂ)))) =
        ∏' n : ℕ, (1 - ModularForm.eta_q n z) :=
    tprod_congr fun n => by rw [eta_q_add_int n z k]
  rw [ModularForm.eta, ModularForm.eta, hpref, hprod, mul_assoc]

/-- Natural-number translation identity: `η(z + k) = exp(k π i / 12) * η(z)`. -/
theorem eta_add_nat (z : ℂ) (k : ℕ) :
    ModularForm.eta (z + (k : ℂ)) =
      Complex.exp ((k : ℂ) * π * Complex.I / 12) * ModularForm.eta z := by
  simpa using eta_add_int z (k : ℤ)

/-- Translation identity on `ℍ`: `η((k : ℝ) +ᵥ τ) = exp(k π i / 12) * η(τ)`. -/
theorem dedekindEta_vadd_int (k : ℤ) (τ : ℍ) :
    dedekindEta ((k : ℝ) +ᵥ τ) =
      Complex.exp ((k : ℂ) * π * Complex.I / 12) * dedekindEta τ := by
  rw [dedekindEta_eq, dedekindEta_eq, UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, add_comm]
  exact eta_add_int (τ : ℂ) k

/-- Transformation of `dedekindEta` under `ModularGroup.T`:
`η(T • τ) = exp(π i / 12) * η(τ)`. -/
theorem dedekindEta_T_smul (τ : ℍ) :
    dedekindEta (ModularGroup.T • τ) = Complex.exp (π * Complex.I / 12) * dedekindEta τ := by
  rw [UpperHalfPlane.modular_T_smul, dedekindEta_eq, dedekindEta_eq, UpperHalfPlane.coe_vadd,
    Complex.ofReal_one, add_comm]
  exact eta_add_one (τ : ℂ)

/-- Transformation of `dedekindEta` under integer powers `T ^ k` (`k : ℤ`):
`η(T ^ k • τ) = exp(k π i / 12) * η(τ)`. -/
theorem dedekindEta_T_zpow_smul (k : ℤ) (τ : ℍ) :
    dedekindEta ((ModularGroup.T ^ k) • τ) =
      Complex.exp ((k : ℂ) * π * Complex.I / 12) * dedekindEta τ := by
  rw [UpperHalfPlane.modular_T_zpow_smul]
  exact dedekindEta_vadd_int k τ

end Translation

section InversionAndBranch

/-- For every `τ : ℍ`, `-I * τ` has positive real part and lies in the right half-plane. -/
theorem neg_I_mul_re_pos (τ : ℍ) : 0 < (-Complex.I * (τ : ℂ)).re := by
  have hre : (-Complex.I * (τ : ℂ)).re = τ.im := by
    simp [Complex.mul_re, UpperHalfPlane.coe_im]
  rw [hre]
  exact τ.im_pos

/-- Principal-branch bridge connecting `(-I * τ) ^ (1 / 2)` with Mathlib's
`(Complex.sqrt I)⁻¹ * Complex.sqrt τ` on `ℍ`. -/
theorem cpow_half_neg_I_mul_eq (τ : ℍ) :
    (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) = (Complex.sqrt Complex.I)⁻¹ * Complex.sqrt (τ : ℂ) := by
  have hargτ_pos : 0 < (τ : ℂ).arg := by
    have hnonneg : 0 ≤ (τ : ℂ).arg := Complex.arg_nonneg_iff.mpr τ.im_pos.le
    have hne : (τ : ℂ).arg ≠ 0 := by
      intro h0
      have him := (Complex.arg_eq_zero_iff.mp h0).2
      exact τ.im_pos.ne' him
    exact lt_of_le_of_ne hnonneg hne.symm
  have hargτ_lt : (τ : ℂ).arg < π := by
    have hle : (τ : ℂ).arg ≤ π := Complex.arg_le_pi _
    have hne : (τ : ℂ).arg ≠ π := by
      intro hpi
      have him := (Complex.arg_eq_pi_iff.mp hpi).2
      exact τ.im_pos.ne' him
    exact lt_of_le_of_ne hle hne
  have hsum_mem : (-Complex.I).arg + (τ : ℂ).arg ∈ Set.Ioc (-π) π := by
    rw [Complex.arg_neg_I]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmul := Complex.mul_cpow hsum_mem (1 / 2 : ℂ)
  have hhalf : (1 / 2 : ℂ) = (2⁻¹ : ℂ) := by norm_num
  rw [hhalf] at hmul ⊢
  rw [hmul]
  have hI_arg : Complex.I.arg ≠ π := by
    rw [Complex.arg_I]
    linarith [Real.pi_pos]
  have hnegI : (-Complex.I) ^ (2⁻¹ : ℂ) = (Complex.sqrt Complex.I)⁻¹ := by
    rw [← Complex.inv_I, Complex.inv_cpow Complex.I (2⁻¹ : ℂ) hI_arg]
    rfl
  rw [hnegI]
  rfl

/-- At `τ = UpperHalfPlane.I`, the automorphy factor `(-I * I) ^ (1 / 2)` equals `1`. -/
theorem cpow_half_neg_I_mul_at_I :
    (-Complex.I * (UpperHalfPlane.I : ℂ)) ^ (1 / 2 : ℂ) = 1 := by
  have hmul : -Complex.I * (UpperHalfPlane.I : ℂ) = 1 := by
    simp [UpperHalfPlane.coe_I]
  rw [hmul, Complex.one_cpow]

/-- Inversion law for `ModularForm.eta`: `η(-τ⁻¹) = (-i τ) ^ (1 / 2) * η(τ)`. -/
theorem eta_inv (τ : ℍ) :
    ModularForm.eta (-(τ : ℂ)⁻¹) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  have he :
      ModularForm.eta (-1 / (τ : ℂ)) =
        (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt (τ : ℂ) * ModularForm.eta (τ : ℂ)) := by
    simpa only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using
      ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [show -(τ : ℂ)⁻¹ = -1 / (τ : ℂ) by ring, he, ← mul_assoc, cpow_half_neg_I_mul_eq τ]

/-- Inversion law in fraction form: `η(-1 / τ) = (-i τ) ^ (1 / 2) * η(τ)`. -/
theorem eta_neg_one_div (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  simpa only [neg_div, one_div] using eta_inv τ

/-- Transformation of `dedekindEta` under `ModularGroup.S`:
`η(S • τ) = (-i τ) ^ (1 / 2) * η(τ)`. -/
theorem dedekindEta_S_smul (τ : ℍ) :
    dedekindEta (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * dedekindEta τ := by
  rw [dedekindEta_eq, dedekindEta_eq, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  exact eta_inv τ

/-- Right half-plane square-root cocycle: if `w₁, w₂, w₃ : ℂ` satisfy `0 < w₁.re`, `0 < w₂.re`,
`0 < w₃.re`, and `w₁ * w₂ = I * w₃`, then `w₁ ^ (1 / 2) * w₂ ^ (1 / 2) = exp(π i / 4) * w₃ ^ (1 / 2)`. -/
theorem cpow_half_mul_eq_exp_pi_div_four_mul {w₁ w₂ w₃ : ℂ}
    (hw₁ : 0 < w₁.re) (hw₂ : 0 < w₂.re) (hw₃ : 0 < w₃.re) (heq : w₁ * w₂ = Complex.I * w₃) :
    w₁ ^ (1 / 2 : ℂ) * w₂ ^ (1 / 2 : ℂ) =
      Complex.exp (π * Complex.I / 4) * w₃ ^ (1 / 2 : ℂ) := by
  have h1 : |w₁.arg| < π / 2 := (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hw₁)
  have h2 : |w₂.arg| < π / 2 := (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hw₂)
  have h3 : |w₃.arg| < π / 2 := (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hw₃)
  have hsum12 : w₁.arg + w₂.arg ∈ Set.Ioc (-π) π := by
    rw [abs_lt] at h1 h2
    exact ⟨by linarith, by linarith⟩
  have hsumI3 : Complex.I.arg + w₃.arg ∈ Set.Ioc (-π) π := by
    rw [abs_lt] at h3
    rw [Complex.arg_I]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hIhalf : Complex.I ^ (1 / 2 : ℂ) = Complex.exp (π * Complex.I / 4) := by
    rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.log_I]
    congr 1
    ring
  calc
    w₁ ^ (1 / 2 : ℂ) * w₂ ^ (1 / 2 : ℂ)
        = (w₁ * w₂) ^ (1 / 2 : ℂ) := (Complex.mul_cpow hsum12 (1 / 2 : ℂ)).symm
    _ = (Complex.I * w₃) ^ (1 / 2 : ℂ) := by rw [heq]
    _ = Complex.I ^ (1 / 2 : ℂ) * w₃ ^ (1 / 2 : ℂ) := Complex.mul_cpow hsumI3 (1 / 2 : ℂ)
    _ = Complex.exp (π * Complex.I / 4) * w₃ ^ (1 / 2 : ℂ) := by rw [hIhalf]

/-- Half-plane cocycle for `(-i (c τ + r)) ^ (1 / 2)` under the inversion step `S • τ'`:
for positive integers `c, r` and `τ' : ℍ`,
`(-i (r * (S • τ') - c)) ^ (1 / 2) * (-i τ') ^ (1 / 2) = exp(π i / 4) * (-i (c τ' + r)) ^ (1 / 2)`. -/
theorem cpow_half_neg_I_mul_cocycle {c r : ℤ} (hc : 0 < c) (hr : 0 < r) (τ' : ℍ) :
    (-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-c : ℂ))) ^ (1 / 2 : ℂ) *
        (-Complex.I * (τ' : ℂ)) ^ (1 / 2 : ℂ) =
      Complex.exp (π * Complex.I / 4) *
        (-Complex.I * ((c : ℂ) * (τ' : ℂ) + (r : ℂ))) ^ (1 / 2 : ℂ) := by
  have hS_coe : ((ModularGroup.S • τ' : ℍ) : ℂ) = -(τ' : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hw₁ : 0 < (-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-c : ℂ))).re := by
    have hre :
        (-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-c : ℂ))).re =
          (r : ℝ) * (ModularGroup.S • τ').im := by
      simp [Complex.mul_re, UpperHalfPlane.coe_im]
    rw [hre]
    exact mul_pos (Int.cast_pos.mpr hr) (ModularGroup.S • τ').im_pos
  have hw₂ : 0 < (-Complex.I * (τ' : ℂ)).re := neg_I_mul_re_pos τ'
  have hw₃ : 0 < (-Complex.I * ((c : ℂ) * (τ' : ℂ) + (r : ℂ))).re := by
    have hre : (-Complex.I * ((c : ℂ) * (τ' : ℂ) + (r : ℂ))).re = (c : ℝ) * τ'.im := by
      simp [Complex.mul_re, UpperHalfPlane.coe_im]
    rw [hre]
    exact mul_pos (Int.cast_pos.mpr hc) τ'.im_pos
  have heq :
      (-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-c : ℂ))) *
          (-Complex.I * (τ' : ℂ)) =
        Complex.I * (-Complex.I * ((c : ℂ) * (τ' : ℂ) + (r : ℂ))) := by
    rw [hS_coe]
    have hτ : (τ' : ℂ) ≠ 0 := τ'.ne_zero
    field_simp [hτ]
    ring_nf
  exact cpow_half_mul_eq_exp_pi_div_four_mul hw₁ hw₂ hw₃ heq

end InversionAndBranch

section LogDerivAndE2

/-- The logarithmic derivative of `ModularForm.eta` on `ℍ` equals `(π i / 12) * E₂(τ)`. -/
theorem logDeriv_eta_eq_E2 (τ : ℍ) :
    logDeriv ModularForm.eta (τ : ℂ) = (π * Complex.I / 12) * EisensteinSeries.E2 τ :=
  ModularForm.logDeriv_eta_eq_E2 τ

/-- The complex derivative of `ModularForm.eta` at `τ : ℍ` equals
`(π i / 12) * E₂(τ) * η(τ)`. -/
theorem deriv_eta_eq_E2_mul_eta (τ : ℍ) :
    deriv ModularForm.eta (τ : ℂ) =
      (π * Complex.I / 12) * EisensteinSeries.E2 τ * ModularForm.eta (τ : ℂ) :=
  ModularForm.deriv_eta_eq_E2_mul_eta τ

/-- Derivative of `dedekindEta ∘ UpperHalfPlane.ofComplex` at `τ : ℍ`. -/
theorem deriv_dedekindEta_comp_ofComplex (τ : ℍ) :
    deriv (dedekindEta ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
      (π * Complex.I / 12) * EisensteinSeries.E2 τ * dedekindEta τ := by
  have heq : dedekindEta ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 (τ : ℂ)] ModularForm.eta := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    simp [dedekindEta_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rw [heq.deriv_eq, deriv_eta_eq_E2_mul_eta τ, dedekindEta_eq]

/-- Q-expansion of the logarithmic derivative of `eta` via the divisor-sum function `σ₁`. -/
theorem logDeriv_eta_eq_tsum_sigma (τ : ℍ) :
    logDeriv ModularForm.eta (τ : ℂ) =
      (π * Complex.I / 12) *
        (1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) * 𝕢 1 (τ : ℂ) ^ (n : ℕ)) := by
  rw [logDeriv_eta_eq_E2 τ, EisensteinSeries.E2_eq_tsum_cexp]
  have hq : Complex.exp (2 * π * Complex.I * (τ : ℂ)) = 𝕢 1 (τ : ℂ) := by
    simp [Periodic.qParam]
  rw [hq]

/-- Lambert-series form of the logarithmic derivative of `eta`:
`logDeriv η(τ) = (π i / 12) * (1 - 24 * ∑' n : ℕ+, n * q ^ n / (1 - q ^ n))`. -/
theorem logDeriv_eta_eq_tsum_div (τ : ℍ) :
    logDeriv ModularForm.eta (τ : ℂ) =
      (π * Complex.I / 12) *
        (1 - 24 * ∑' n : ℕ+, (n : ℂ) * 𝕢 1 (τ : ℂ) ^ (n : ℕ) / (1 - 𝕢 1 (τ : ℂ) ^ (n : ℕ))) := by
  rw [logDeriv_eta_eq_tsum_sigma τ]
  have hnorm : ‖𝕢 1 (τ : ℂ)‖ < 1 := τ.norm_qParam_lt_one 1
  have hlam :
      (∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) * 𝕢 1 (τ : ℂ) ^ (n : ℕ)) =
        ∑' n : ℕ+, (n : ℂ) * 𝕢 1 (τ : ℂ) ^ (n : ℕ) / (1 - 𝕢 1 (τ : ℂ) ^ (n : ℕ)) := by
    simpa only [pow_one] using (tsum_pow_div_one_sub_eq_tsum_sigma hnorm 1).symm
  rw [hlam]

/-- Inversion transformation law of the logarithmic derivative of `eta`:
`logDeriv η(-τ⁻¹) = τ² * logDeriv η(τ) + τ / 2`. -/
theorem logDeriv_eta_inv (τ : ℍ) :
    logDeriv ModularForm.eta (-(τ : ℂ)⁻¹) =
      (τ : ℂ) ^ 2 * logDeriv ModularForm.eta (τ : ℂ) + (τ : ℂ) / 2 := by
  let f : ℂ → ℂ := ModularForm.eta ∘ (fun z : ℂ => -1 / z)
  let c : ℂ := (Complex.sqrt Complex.I)⁻¹
  let g : ℂ → ℂ := fun z : ℂ => c * (Complex.sqrt z * ModularForm.eta z)
  have hfg : f =ᶠ[𝓝 (τ : ℂ)] g := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    have he := ModularForm.eta_comp_eq_csqrt_I_inv hz
    simpa only [f, g, c, Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using he
  have hlog_eq : logDeriv f (τ : ℂ) = logDeriv g (τ : ℂ) := by
    simp only [logDeriv_apply, hfg.deriv_eq, hfg.eq_of_nhds]
  have hcomp : logDeriv f (τ : ℂ) =
      ((τ : ℂ) ^ 2)⁻¹ * logDeriv ModularForm.eta (-(τ : ℂ)⁻¹) := by
    have him' : 0 < (-1 / (τ : ℂ)).im := by
      simpa [neg_div, one_div, inv_neg] using τ.im_inv_neg_coe_pos
    have hdiff_eta : DifferentiableAt ℂ ModularForm.eta (-1 / (τ : ℂ)) :=
      differentiableAt_eta_of_im_pos him'
    have hderiv_inv : HasDerivAt (fun z : ℂ => -1 / z) (((τ : ℂ) ^ 2)⁻¹) (τ : ℂ) := by
      have h1 :
          HasDerivAt (fun z : ℂ => (-1 : ℂ) / z)
            ((0 * (τ : ℂ) - (-1 : ℂ) * 1) / (τ : ℂ) ^ 2) (τ : ℂ) :=
        (hasDerivAt_const (τ : ℂ) (-1 : ℂ)).fun_div (hasDerivAt_id (τ : ℂ)) τ.ne_zero
      have h2 : (0 * (τ : ℂ) - (-1 : ℂ) * 1) / (τ : ℂ) ^ 2 = ((τ : ℂ) ^ 2)⁻¹ := by ring
      rw [h2] at h1
      exact h1
    have hf : logDeriv f (τ : ℂ) =
        logDeriv ModularForm.eta (-1 / (τ : ℂ)) * (((τ : ℂ) ^ 2)⁻¹) := by
      rw [show f = ModularForm.eta ∘ (fun z : ℂ => -1 / z) from rfl,
        logDeriv_comp hdiff_eta hderiv_inv.differentiableAt, hderiv_inv.deriv]
    rw [hf, show (-1 / (τ : ℂ)) = -(τ : ℂ)⁻¹ by ring, mul_comm]
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    exact inv_ne_zero (by simp [Complex.sqrt, Complex.I_ne_zero])
  have hsqrt_ne : Complex.sqrt (τ : ℂ) ≠ 0 := by
    simp [Complex.sqrt, τ.ne_zero]
  have heta_ne : ModularForm.eta (τ : ℂ) ≠ 0 := eta_ne_zero_of_im_pos τ.2
  have hdiff_sqrt : DifferentiableAt ℂ Complex.sqrt (τ : ℂ) :=
    Complex.differentiableAt_sqrt (UpperHalfPlane.mem_slitPlane τ)
  have hdiff_eta : DifferentiableAt ℂ ModularForm.eta (τ : ℂ) :=
    differentiableAt_eta_of_im_pos τ.2
  have hsqrt_eval :
      logDeriv g (τ : ℂ) = (2 * (τ : ℂ))⁻¹ + logDeriv ModularForm.eta (τ : ℂ) := by
    have hconst : logDeriv g (τ : ℂ) =
        logDeriv (Complex.sqrt * ModularForm.eta) (τ : ℂ) := by
      have hgfun : g = fun y => c * (Complex.sqrt * ModularForm.eta) y := rfl
      rw [logDeriv_apply, logDeriv_apply, hgfun, deriv_const_mul c (hdiff_sqrt.mul hdiff_eta),
        mul_div_mul_left _ _ hc_ne]
    rw [hconst, logDeriv_mul _ hsqrt_ne heta_ne hdiff_sqrt hdiff_eta,
      logDeriv_apply Complex.sqrt, Complex.deriv_sqrt (UpperHalfPlane.mem_slitPlane τ)]
    congr 1
    have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
    simp only [Complex.sqrt]
    rw [div_div, mul_comm (2 : ℂ), ← div_div]
    have hsub : (τ : ℂ) ^ (-1 / 2 : ℂ) / (τ : ℂ) ^ (2⁻¹ : ℂ) = (τ : ℂ)⁻¹ := by
      rw [← Complex.cpow_sub _ _ hτ, show (-1 / 2 : ℂ) - 2⁻¹ = -1 by norm_num, Complex.cpow_neg_one]
    rw [hsub, div_eq_mul_inv, mul_inv, mul_comm (2 : ℂ)⁻¹]
  have hcombine :
      ((τ : ℂ) ^ 2)⁻¹ * logDeriv ModularForm.eta (-(τ : ℂ)⁻¹) =
        (2 * (τ : ℂ))⁻¹ + logDeriv ModularForm.eta (τ : ℂ) :=
    hcomp.symm.trans (hlog_eq.trans hsqrt_eval)
  have hτ2 : (τ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 τ.ne_zero
  calc
    logDeriv ModularForm.eta (-(τ : ℂ)⁻¹)
        = (τ : ℂ) ^ 2 * (((τ : ℂ) ^ 2)⁻¹ * logDeriv ModularForm.eta (-(τ : ℂ)⁻¹)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hτ2, one_mul]
    _ = (τ : ℂ) ^ 2 * ((2 * (τ : ℂ))⁻¹ + logDeriv ModularForm.eta (τ : ℂ)) := by
          rw [hcombine]
    _ = (τ : ℂ) ^ 2 * logDeriv ModularForm.eta (τ : ℂ) + (τ : ℂ) / 2 := by
          have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
          field_simp [hτ]
          ring

/-- Inversion transformation of the quasi-modular Eisenstein series `E₂`:
`E₂(S • τ) = τ² * E₂(τ) + 6 * τ / (π i)`. -/
theorem E2_S_smul (τ : ℍ) :
    EisensteinSeries.E2 (ModularGroup.S • τ) =
      (τ : ℂ) ^ 2 * EisensteinSeries.E2 τ + 6 * (τ : ℂ) / (π * Complex.I) := by
  have hlog := logDeriv_eta_inv τ
  have hS : (-(τ : ℂ)⁻¹ : ℂ) = ((ModularGroup.S • τ : ℍ) : ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  rw [hS, logDeriv_eta_eq_E2 (ModularGroup.S • τ), logDeriv_eta_eq_E2 τ] at hlog
  have hpi : (π * Complex.I / 12 : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ hpi
  rw [hlog, mul_add]
  have hpi0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi0, Complex.I_ne_zero]
  ring

/-- Special value `logDeriv η(i) = i / 4` at `τ = UpperHalfPlane.I`. -/
theorem logDeriv_eta_at_I :
    logDeriv ModularForm.eta (UpperHalfPlane.I : ℂ) = Complex.I / 4 := by
  have h := logDeriv_eta_inv UpperHalfPlane.I
  have hIval : (UpperHalfPlane.I : ℂ) = Complex.I := rfl
  have hinv : -((UpperHalfPlane.I : ℂ))⁻¹ = (UpperHalfPlane.I : ℂ) := by
    rw [hIval, Complex.inv_I, neg_neg]
  rw [hinv, hIval, Complex.I_sq] at h
  have h2 : 2 * logDeriv ModularForm.eta Complex.I = Complex.I / 2 := by
    calc
      2 * logDeriv ModularForm.eta Complex.I
          = logDeriv ModularForm.eta Complex.I + logDeriv ModularForm.eta Complex.I := by ring
      _ = (-1 * logDeriv ModularForm.eta Complex.I + Complex.I / 2) +
            logDeriv ModularForm.eta Complex.I := by nth_rw 1 [h]
      _ = Complex.I / 2 := by ring
  rw [hIval]
  calc
    logDeriv ModularForm.eta Complex.I
        = (2 * logDeriv ModularForm.eta Complex.I) / 2 := by ring
    _ = (Complex.I / 2) / 2 := by rw [h2]
    _ = Complex.I / 4 := by ring

/-- Special value `E₂(i) = 3 / π` of the quasi-modular Eisenstein series at `τ = i`. -/
theorem E2_at_I : EisensteinSeries.E2 UpperHalfPlane.I = 3 / (π : ℂ) := by
  have h := logDeriv_eta_eq_E2 UpperHalfPlane.I
  rw [logDeriv_eta_at_I] at h
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hmul :
      (π * Complex.I / 12) * EisensteinSeries.E2 UpperHalfPlane.I =
        (π * Complex.I / 12) * (3 / (π : ℂ)) := by
    rw [← h]
    field_simp [hpi]
    ring
  exact mul_left_cancel₀ (by simp [hpi, hI]) hmul

end LogDerivAndE2

section SL2ZTransformation

private lemma mul_T_zpow_entry_00 (γ : SL(2, ℤ)) (q : ℤ) :
    (γ * ModularGroup.T ^ (-q)) 0 0 = γ 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ModularGroup.coe_T_zpow]
  simp

private lemma mul_T_zpow_entry_01 (γ : SL(2, ℤ)) (q : ℤ) :
    (γ * ModularGroup.T ^ (-q)) 0 1 = γ 0 1 - γ 0 0 * q := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ModularGroup.coe_T_zpow]
  simp
  ring

private lemma mul_T_zpow_entry_10 (γ : SL(2, ℤ)) (q : ℤ) :
    (γ * ModularGroup.T ^ (-q)) 1 0 = γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ModularGroup.coe_T_zpow]
  simp

private lemma mul_T_zpow_entry_11 (γ : SL(2, ℤ)) (q : ℤ) :
    (γ * ModularGroup.T ^ (-q)) 1 1 = γ 1 1 - γ 1 0 * q := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ModularGroup.coe_T_zpow]
  simp
  ring

private lemma mul_S_entry_00 (γ : SL(2, ℤ)) : (γ * ModularGroup.S) 0 0 = γ 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]
  simp

private lemma mul_S_entry_01 (γ : SL(2, ℤ)) : (γ * ModularGroup.S) 0 1 = -γ 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]
  simp

private lemma mul_S_entry_10 (γ : SL(2, ℤ)) : (γ * ModularGroup.S) 1 0 = γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]
  simp

private lemma mul_S_entry_11 (γ : SL(2, ℤ)) : (γ * ModularGroup.S) 1 1 = -γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]
  simp

private lemma sl2z_det_eq (γ : SL(2, ℤ)) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  rw [← Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)]
  exact γ.2

private lemma sl2z_coprime_bottom (γ : SL(2, ℤ)) :
    Nat.Coprime (γ 1 0).natAbs (γ 1 1).natAbs := by
  refine Nat.coprime_of_dvd fun p hp hpc hpd => ?_
  have hpc' : (p : ℤ) ∣ γ 1 0 := Int.natCast_dvd.mpr hpc
  have hpd' : (p : ℤ) ∣ γ 1 1 := Int.natCast_dvd.mpr hpd
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := sl2z_det_eq γ
  have hdvd1 : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_right hpd' _) (dvd_mul_of_dvd_right hpc' _)
  have hp1 : p = 1 := Nat.dvd_one.mp (Int.natCast_dvd.mp hdvd1)
  exact hp.ne_one hp1

private lemma dedekindEta_SL2Z_of_pos_aux :
    ∀ k : ℕ, 1 ≤ k →
      ∀ (γ : SL(2, ℤ)), γ 1 0 = (k : ℤ) → ∀ τ : ℍ,
        dedekindEta (γ • τ) =
          Complex.exp (π * Complex.I *
            ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
              dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ)) *
          (-Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) ^ (1 / 2 : ℂ) *
          dedekindEta τ := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk γ hγc τ
    have hc_pos : 0 < γ 1 0 := by omega
    let q : ℤ := γ 1 1 / γ 1 0
    let r : ℤ := γ 1 1 % γ 1 0
    let γ₁ : SL(2, ℤ) := γ * ModularGroup.T ^ (-q)
    let τ' : ℍ := (ModularGroup.T ^ q) • τ
    have hr_nonneg : 0 ≤ r := Int.emod_nonneg (γ 1 1) hc_pos.ne'
    have hr_lt : r < γ 1 0 := Int.emod_lt_of_pos (γ 1 1) hc_pos
    have hdiv_mod : γ 1 0 * q + r = γ 1 1 := Int.mul_ediv_add_emod (γ 1 1) (γ 1 0)
    have hγ₁_00 : γ₁ 0 0 = γ 0 0 := mul_T_zpow_entry_00 γ q
    have hγ₁_01 : γ₁ 0 1 = γ 0 1 - γ 0 0 * q := mul_T_zpow_entry_01 γ q
    have hγ₁_10 : γ₁ 1 0 = γ 1 0 := mul_T_zpow_entry_10 γ q
    have hγ₁_11 : γ₁ 1 1 = r := by
      rw [mul_T_zpow_entry_11]
      linarith
    have hsmul1 : γ • τ = γ₁ • τ' := by
      change γ • τ = γ₁ • ((ModularGroup.T ^ q) • τ)
      rw [← mul_smul γ₁ (ModularGroup.T ^ q) τ]
      have hprod : γ₁ * ModularGroup.T ^ q = γ := by
        dsimp [γ₁]
        rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      rw [hprod]
    have hτ'_coe : (τ' : ℂ) = (τ : ℂ) + (q : ℂ) := by
      change (((ModularGroup.T ^ q) • τ : ℍ) : ℂ) = (τ : ℂ) + (q : ℂ)
      rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, Complex.ofReal_intCast,
        add_comm]
    have hdenom_eq : (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) =
        (γ 1 0 : ℂ) * (τ' : ℂ) + (r : ℂ) := by
      rw [hτ'_coe]
      have hdivC : (γ 1 1 : ℂ) = (γ 1 0 : ℂ) * (q : ℂ) + (r : ℂ) := by
        exact_mod_cast hdiv_mod.symm
      rw [hdivC]
      ring
    have hdedekind_mod : dedekindSum (γ 1 1) (γ 1 0).natAbs = dedekindSum r (γ 1 0).natAbs := by
      have hc_nat_coe : ((γ 1 0).natAbs : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc_pos.le
      have hsplit : γ 1 1 = r + q * ((γ 1 0).natAbs : ℤ) := by
        rw [hc_nat_coe]
        linarith
      rw [hsplit]
      exact dedekindSum_add_int r q (γ 1 0).natAbs
    have hexp_shift :
        (((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
            dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) =
          (((γ₁ 0 0 + r : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
            dedekindSum r (γ 1 0).natAbs) + (q : ℝ) / 12 := by
      rw [hγ₁_00, hdedekind_mod]
      have hdivR : (γ 1 1 : ℝ) = (γ 1 0 : ℝ) * (q : ℝ) + (r : ℝ) := by
        exact_mod_cast hdiv_mod.symm
      have hcR : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc_pos.ne'
      rw [Int.cast_add, Int.cast_add, hdivR]
      field_simp [hcR]
      ring
    have heta_shift : dedekindEta τ' =
        Complex.exp (π * Complex.I * ((q : ℝ) / 12 : ℝ)) * dedekindEta τ := by
      change dedekindEta ((ModularGroup.T ^ q) • τ) = _
      rw [dedekindEta_T_zpow_smul q τ]
      congr 2
      rw [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
      ring
    rcases eq_or_lt_of_le hr_nonneg with hr0 | hr_pos
    · have hr_zero : r = 0 := hr0.symm
      have hγ₁_det : γ₁ 0 0 * γ₁ 1 1 - γ₁ 0 1 * γ₁ 1 0 = 1 := sl2z_det_eq γ₁
      rw [hγ₁_10, hγ₁_11, hr_zero, mul_zero, zero_sub] at hγ₁_det
      have hc1 : γ 1 0 = 1 := by
        have hdvd : γ 1 0 ∣ 1 := ⟨-γ₁ 0 1, by linarith⟩
        have hle := Int.le_of_dvd one_pos hdvd
        omega
      have hb' : γ₁ 0 1 = -1 := by
        rw [hc1, mul_one] at hγ₁_det
        linarith
      have hγ₁_eq : γ₁ = (ModularGroup.T ^ (γ₁ 0 0)) * ModularGroup.S := by
        ext i j
        have hM :
            ((ModularGroup.T ^ (γ₁ 0 0) * ModularGroup.S : SL(2, ℤ)) :
                Matrix (Fin 2) (Fin 2) ℤ) i j =
              (ModularGroup.T ^ (γ₁ 0 0) : SL(2, ℤ)) i 0 * (ModularGroup.S : SL(2, ℤ)) 0 j +
                (ModularGroup.T ^ (γ₁ 0 0) : SL(2, ℤ)) i 1 * (ModularGroup.S : SL(2, ℤ)) 1 j := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
        change (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) i j = _
        rw [hM, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
        fin_cases i <;> fin_cases j
        · simp
        · simpa [hγ₁_01] using hb'
        · simp [hγ₁_10, hc1]
        · simp [hγ₁_11, hr_zero]
      rw [hsmul1, hγ₁_eq, mul_smul, dedekindEta_T_zpow_smul, dedekindEta_S_smul, heta_shift]
      have hded_zero : dedekindSum r (γ 1 0).natAbs = 0 := by
        rw [hr_zero, hc1]
        simp [dedekindSum_one_right]
      rw [hdenom_eq, hexp_shift, hded_zero, hr_zero, hc1, hγ₁_00]
      have hsimp_r0 :
          ((γ 0 0 + 0 : ℤ) : ℝ) / (12 * ((1 : ℤ) : ℝ)) - 0 + (q : ℝ) / 12 =
            ((γ 0 0 : ℤ) : ℝ) / 12 + (q : ℝ) / 12 := by
        norm_num
      rw [hsimp_r0]
      have hdenom_1 :
          -Complex.I * (((1 : ℤ) : ℂ) * (τ' : ℂ) + ((0 : ℤ) : ℂ)) = -Complex.I * (τ' : ℂ) := by
        simp
      rw [hdenom_1]
      have hexp_comb :
          Complex.exp (π * Complex.I * ((((γ 0 0 : ℤ) : ℝ) / 12 + (q : ℝ) / 12 : ℝ) : ℂ)) =
            Complex.exp ((γ 0 0 : ℂ) * π * Complex.I / 12) *
              Complex.exp (π * Complex.I * ((q : ℝ) / 12 : ℝ)) := by
        rw [← Complex.exp_add]
        congr 1
        rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_intCast,
          Complex.ofReal_ofNat]
        ring
      rw [hexp_comb]
      ring
    · let γ₂ : SL(2, ℤ) := γ₁ * ModularGroup.S
      have hγ₂_00 : γ₂ 0 0 = γ₁ 0 1 := mul_S_entry_00 γ₁
      have hγ₂_10 : γ₂ 1 0 = r := by rw [mul_S_entry_10, hγ₁_11]
      have hγ₂_11 : γ₂ 1 1 = -γ 1 0 := by rw [mul_S_entry_11, hγ₁_10]
      have hr_nat_lt : r.natAbs < k := by omega
      have hr_nat_pos : 1 ≤ r.natAbs := by omega
      have hγ₂_c : γ₂ 1 0 = (r.natAbs : ℤ) := by
        rw [hγ₂_10, Int.natAbs_of_nonneg hr_pos.le]
      have hih := ih r.natAbs hr_nat_lt hr_nat_pos γ₂ hγ₂_c (ModularGroup.S • τ')
      have hsmul2 : γ₁ • τ' = γ₂ • (ModularGroup.S • τ') := by
        rw [← mul_smul γ₂ ModularGroup.S τ']
        have hprod : γ₂ * ModularGroup.S = -γ₁ := by
          dsimp [γ₂]
          rw [mul_assoc, ModularGroup.S_mul_S_eq, mul_neg_one]
        rw [hprod, ModularGroup.SL_neg_smul]
      rw [hsmul1, hsmul2, hih, dedekindEta_S_smul τ', heta_shift]
      have hcocycle := cpow_half_neg_I_mul_cocycle hc_pos hr_pos τ'
      have hγ₂_denom :
          (-Complex.I * ((γ₂ 1 0 : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (γ₂ 1 1 : ℂ))) =
            (-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-γ 1 0 : ℂ))) := by
        rw [hγ₂_10, hγ₂_11, Int.cast_neg]
      have hcop : Nat.Coprime (γ 1 0).natAbs r.natAbs := by
        have hcop₁ := sl2z_coprime_bottom γ₁
        rwa [hγ₁_10, hγ₁_11] at hcop₁
      have hrec := dedekind_reciprocity_div (show 1 ≤ (γ 1 0).natAbs by omega) hr_nat_pos hcop
      have hneg_ded : dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs =
          -dedekindSum (γ 1 0) r.natAbs := by
        rw [hγ₂_11, hγ₂_10, dedekindSum_neg]
      have hγ₁_det : γ₁ 0 0 * r - γ₁ 0 1 * γ 1 0 = 1 := by
        have hdet := sl2z_det_eq γ₁
        rwa [hγ₁_10, hγ₁_11] at hdet
      have hc_coeR : ((γ 1 0).natAbs : ℝ) = (γ 1 0 : ℝ) := by
        rw [← Int.cast_natCast (γ 1 0).natAbs, Int.natAbs_of_nonneg hc_pos.le]
      have hr_coeR : (r.natAbs : ℝ) = (r : ℝ) := by
        rw [← Int.cast_natCast r.natAbs, Int.natAbs_of_nonneg hr_pos.le]
      have hcR_ne : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc_pos.ne'
      have hrR_ne : (r : ℝ) ≠ 0 := by exact_mod_cast hr_pos.ne'
      have hdetR : (γ₁ 0 0 : ℝ) * (r : ℝ) - (γ₁ 0 1 : ℝ) * (γ 1 0 : ℝ) = 1 := by
        exact_mod_cast hγ₁_det
      have hrecR :
          dedekindSum (γ 1 0) r.natAbs + dedekindSum r (γ 1 0).natAbs =
            -1 / 4 + ((γ 1 0 : ℝ) / (r : ℝ) + (r : ℝ) / (γ 1 0 : ℝ) +
              1 / ((γ 1 0 : ℝ) * (r : ℝ))) / 12 := by
        have h1 : (((γ 1 0).natAbs : ℕ) : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc_pos.le
        have h2 : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hr_pos.le
        rw [hc_coeR, hr_coeR] at hrec
        rwa [h1, h2] at hrec
      have harg_real :
          (((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
              dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs) + 1 / 4 =
            (((γ₁ 0 0 + r : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
              dedekindSum r (γ 1 0).natAbs) := by
        rw [hneg_ded, hγ₂_00, hγ₂_11, hγ₂_10, Int.cast_add, Int.cast_neg, Int.cast_add]
        have hsub : dedekindSum (γ 1 0) r.natAbs =
            -dedekindSum r (γ 1 0).natAbs - 1 / 4 +
              ((γ 1 0 : ℝ) / (r : ℝ) + (r : ℝ) / (γ 1 0 : ℝ) +
                1 / ((γ 1 0 : ℝ) * (r : ℝ))) / 12 := by
          linarith [hrecR]
        rw [hsub]
        have halg :
            ((γ₁ 0 1 : ℝ) + -(γ 1 0 : ℝ)) / (12 * (r : ℝ)) +
                ((γ 1 0 : ℝ) / (r : ℝ) + (r : ℝ) / (γ 1 0 : ℝ) +
                  1 / ((γ 1 0 : ℝ) * (r : ℝ))) / 12 =
              ((γ₁ 0 0 : ℝ) + (r : ℝ)) / (12 * (γ 1 0 : ℝ)) := by
          have hb1 : (γ₁ 0 1 : ℝ) * (γ 1 0 : ℝ) = (γ₁ 0 0 : ℝ) * (r : ℝ) - 1 := by linarith
          field_simp [hcR_ne, hrR_ne]
          rw [mul_add, mul_comm (γ 1 0 : ℝ) (γ₁ 0 1 : ℝ), hb1]
          ring
        linarith [halg]
      rw [hγ₂_denom]
      calc
        Complex.exp (π * Complex.I *
              ((((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
                dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs : ℝ) : ℂ)) *
            (-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-γ 1 0 : ℂ))) ^
              (1 / 2 : ℂ) *
            ((-Complex.I * (τ' : ℂ)) ^ (1 / 2 : ℂ) *
              (Complex.exp (π * Complex.I * ((q : ℝ) / 12 : ℝ)) * dedekindEta τ))
            = Complex.exp (π * Complex.I *
                  ((((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
                    dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs : ℝ) : ℂ)) *
                (((-Complex.I * ((r : ℂ) * ((ModularGroup.S • τ' : ℍ) : ℂ) + (-γ 1 0 : ℂ))) ^
                    (1 / 2 : ℂ) *
                  (-Complex.I * (τ' : ℂ)) ^ (1 / 2 : ℂ)) *
                  Complex.exp (π * Complex.I * ((q : ℝ) / 12 : ℝ)) * dedekindEta τ) := by
              ring
        _ = Complex.exp (π * Complex.I *
                  ((((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
                    dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs : ℝ) : ℂ)) *
                ((Complex.exp (π * Complex.I / 4) *
                  (-Complex.I * ((γ 1 0 : ℂ) * (τ' : ℂ) + (r : ℂ))) ^ (1 / 2 : ℂ)) *
                  Complex.exp (π * Complex.I * ((q : ℝ) / 12 : ℝ)) * dedekindEta τ) := by
              rw [hcocycle]
        _ = (Complex.exp (π * Complex.I *
                  ((((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
                    dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs : ℝ) : ℂ)) *
                Complex.exp (π * Complex.I / 4) *
                Complex.exp (π * Complex.I * ((q : ℝ) / 12 : ℝ))) *
              (-Complex.I * ((γ 1 0 : ℂ) * (τ' : ℂ) + (r : ℂ))) ^ (1 / 2 : ℂ) *
              dedekindEta τ := by
              ring
        _ = Complex.exp (π * Complex.I *
                ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
                  dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ)) *
              (-Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) ^ (1 / 2 : ℂ) *
              dedekindEta τ := by
              rw [← hdenom_eq]
              congr 2
              rw [← Complex.exp_add, ← Complex.exp_add]
              congr 1
              have harg_sum :
                  ((((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
                      dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs : ℝ) + (1 / 4 : ℝ)) + (q : ℝ) / 12 =
                    (((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
                      dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) := by
                rw [harg_real, hexp_shift]
              have harg_sumC :
                  π * Complex.I *
                        ((((γ₂ 0 0 + γ₂ 1 1 : ℤ) : ℝ) / (12 * (γ₂ 1 0 : ℝ)) -
                          dedekindSum (γ₂ 1 1) (γ₂ 1 0).natAbs : ℝ) : ℂ) +
                      π * Complex.I / 4 +
                    π * Complex.I * ((q : ℝ) / 12 : ℝ) =
                    π * Complex.I *
                      ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
                        dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ) := by
                have h := congrArg (fun x : ℝ => (π : ℂ) * Complex.I * (x : ℂ)) harg_sum
                simp only [Complex.ofReal_add] at h
                have hpiI4 : (π : ℂ) * Complex.I * ((1 / 4 : ℝ) : ℂ) = π * Complex.I / 4 := by
                  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
                  ring
                linear_combination h - hpiI4
              exact harg_sumC

/-- Upper-triangular `SL(2, ℤ)` transformation law for `dedekindEta` (`γ 1 0 = 0`). -/
theorem dedekindEta_SL2Z_of_zero (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (τ : ℍ) :
    dedekindEta (γ • τ) =
      Complex.exp (π * Complex.I * ((γ 0 0 * γ 0 1 : ℤ) : ℂ) / 12) * dedekindEta τ := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := sl2z_det_eq γ
    rwa [hc, mul_zero, sub_zero] at h
  have hpm : γ 0 0 = 1 ∧ γ 1 1 = 1 ∨ γ 0 0 = -1 ∧ γ 1 1 = -1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hpm with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · have hγ : γ = ModularGroup.T ^ (γ 0 1) := by
      ext i j
      rw [ModularGroup.coe_T_zpow]
      fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
    conv_lhs => rw [hγ]
    rw [dedekindEta_T_zpow_smul, ha, one_mul]
    congr 2
    ring
  · have hγ : -γ = ModularGroup.T ^ (-γ 0 1) := by
      ext i j
      rw [ModularGroup.coe_T_zpow]
      fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
    rw [← ModularGroup.SL_neg_smul, hγ, dedekindEta_T_zpow_smul, ha]
    congr 2
    rw [Int.cast_mul, Int.cast_neg, Int.cast_neg, Int.cast_one]
    ring

/-- General `SL(2, ℤ)` transformation law of `dedekindEta` when `γ 1 0 > 0`:
`η(γ • τ) = exp(π i * ((a + d) / (12 c) - s(d, c))) * (-i (c τ + d)) ^ (1 / 2) * η(τ)`. -/
theorem dedekindEta_SL2Z_of_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    dedekindEta (γ • τ) =
      Complex.exp (π * Complex.I *
        ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
          dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ)) *
      (-Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) ^ (1 / 2 : ℂ) *
      dedekindEta τ := by
  have hk1 : 1 ≤ (γ 1 0).natAbs := by omega
  have hk : γ 1 0 = ((γ 1 0).natAbs : ℤ) := (Int.natAbs_of_nonneg hc.le).symm
  exact dedekindEta_SL2Z_of_pos_aux (γ 1 0).natAbs hk1 γ hk τ

/-- General `SL(2, ℤ)` transformation law of `dedekindEta` when `γ 1 0 < 0`:
obtained by passing to `-γ` (which satisfies `(-γ) 1 0 > 0`). -/
theorem dedekindEta_SL2Z_of_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) (τ : ℍ) :
    dedekindEta (γ • τ) =
      Complex.exp (π * Complex.I *
        ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) +
          dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ)) *
      (Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) ^ (1 / 2 : ℂ) *
      dedekindEta τ := by
  have hc' : 0 < (-γ) 1 0 := by
    change 0 < -(γ 1 0)
    linarith
  have h := dedekindEta_SL2Z_of_pos (-γ) hc' τ
  rw [ModularGroup.SL_neg_smul] at h
  have h00 : (-γ) 0 0 = -γ 0 0 := rfl
  have h10 : (-γ) 1 0 = -γ 1 0 := rfl
  have h11 : (-γ) 1 1 = -γ 1 1 := rfl
  have hrat :
      (((((-γ) 0 0 + (-γ) 1 1 : ℤ) : ℝ) / (12 * (((-γ) 1 0 : ℤ) : ℝ)) -
          dedekindSum ((-γ) 1 1) ((-γ) 1 0).natAbs : ℝ)) =
        ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) +
          dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ)) := by
    rw [h00, h10, h11, Int.natAbs_neg, dedekindSum_neg, Int.cast_add, Int.cast_neg, Int.cast_neg,
      Int.cast_neg, Int.cast_add]
    ring
  have hfac :
      -Complex.I * ((((-γ) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((-γ) 1 1 : ℤ) : ℂ)) =
        Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) := by
    rw [h10, h11, Int.cast_neg, Int.cast_neg]
    ring
  rw [hrat, hfac] at h
  exact h

/-- Explicit Möbius-fraction form of Dedekind's transformation law for `ModularForm.eta`:
for integers `a, b, c, d` with `a * d - b * c = 1` and `c > 0`,
`η((a τ + b) / (c τ + d)) = exp(π i ((a + d) / (12 c) - s(d, c))) * (-i (c τ + d)) ^ (1 / 2) * η(τ)`. -/
theorem eta_moebius_of_pos {a b c d : ℤ} (hdet : a * d - b * c = 1) (hc : 0 < c) (τ : ℍ) :
    ModularForm.eta (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ))) =
      Complex.exp (π * Complex.I *
        (((a + d : ℤ) : ℝ) / (12 * (c : ℝ)) - dedekindSum d c.natAbs : ℝ)) *
      (-Complex.I * ((c : ℂ) * (τ : ℂ) + (d : ℂ))) ^ (1 / 2 : ℂ) *
      ModularForm.eta (τ : ℂ) := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using hdet⟩
  have hcoe :
      ((γ • τ : ℍ) : ℂ) =
        ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [γ]
  have h := dedekindEta_SL2Z_of_pos γ hc τ
  rw [dedekindEta_eq, dedekindEta_eq, hcoe] at h
  simpa [γ] using h

/-- The 24th-root-of-unity multiplier `ε(γ)` in the transformation law of `dedekindEta`. -/
def etaMultiplier (γ : SL(2, ℤ)) : ℂ :=
  if γ 1 0 = 0 then
    Complex.exp (π * Complex.I * ((γ 0 0 * γ 0 1 : ℤ) : ℂ) / 12)
  else if 0 < γ 1 0 then
    Complex.exp (π * Complex.I *
      ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
        dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ))
  else
    Complex.exp (π * Complex.I *
      ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) +
        dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ))

/-- The square-root automorphy factor `j_half(γ, τ)` accompanying `etaMultiplier γ`. -/
def etaAutomorphyFactor (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  if γ 1 0 = 0 then
    1
  else if 0 < γ 1 0 then
    (-Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) ^ (1 / 2 : ℂ)
  else
    (Complex.I * ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) ^ (1 / 2 : ℂ)

/-- Unified `SL(2, ℤ)` transformation law for `dedekindEta` in terms of `etaMultiplier`
and `etaAutomorphyFactor`. -/
theorem dedekindEta_SL2Z_factor (γ : SL(2, ℤ)) (τ : ℍ) :
    dedekindEta (γ • τ) = etaMultiplier γ * etaAutomorphyFactor γ τ * dedekindEta τ := by
  unfold etaMultiplier etaAutomorphyFactor
  rcases lt_trichotomy (γ 1 0) 0 with hc_neg | hc_zero | hc_pos
  · have hne : γ 1 0 ≠ 0 := hc_neg.ne
    have hnpos : ¬ 0 < γ 1 0 := not_lt_of_gt hc_neg
    simp only [hne, ↓reduceIte, hnpos]
    exact dedekindEta_SL2Z_of_neg γ hc_neg τ
  · simp only [hc_zero, ↓reduceIte, mul_one]
    exact dedekindEta_SL2Z_of_zero γ hc_zero τ
  · have hne : γ 1 0 ≠ 0 := hc_pos.ne'
    simp only [hne, ↓reduceIte, hc_pos]
    exact dedekindEta_SL2Z_of_pos γ hc_pos τ

/-- Value of `etaMultiplier ModularGroup.T`. -/
theorem etaMultiplier_T :
    etaMultiplier ModularGroup.T = Complex.exp (π * Complex.I / 12) := by
  have hc : ModularGroup.T 1 0 = 0 := rfl
  have ha : ModularGroup.T 0 0 = 1 := rfl
  have hb : ModularGroup.T 0 1 = 1 := rfl
  simp [etaMultiplier, hc, ha, hb]

/-- Value of `etaMultiplier ModularGroup.S`. -/
theorem etaMultiplier_S : etaMultiplier ModularGroup.S = 1 := by
  have hc : ModularGroup.S 1 0 = 1 := rfl
  have ha : ModularGroup.S 0 0 = 0 := rfl
  have hd : ModularGroup.S 1 1 = 0 := rfl
  simp [etaMultiplier, hc, ha, hd, dedekindSum_one_right]

end SL2ZTransformation

section Discriminant

/-- The modular discriminant `Δ(τ) = η(τ) ^ 24` on `ℍ` (bridging `ModularForm.discriminant`). -/
def modularDiscriminant (τ : ℍ) : ℂ :=
  ModularForm.discriminant τ

/-- Definition identity `modularDiscriminant τ = dedekindEta τ ^ 24`. -/
theorem modularDiscriminant_eq_eta_pow (τ : ℍ) :
    modularDiscriminant τ = dedekindEta τ ^ 24 :=
  rfl

/-- Bridge between `modularDiscriminant` and Mathlib's `ModularForm.discriminant`. -/
@[simp]
theorem modularDiscriminant_eq_discriminant (τ : ℍ) :
    modularDiscriminant τ = ModularForm.discriminant τ :=
  rfl

/-- Bridge between `modularDiscriminant` and Mathlib's cusp form `CuspForm.discriminant`. -/
theorem modularDiscriminant_eq_cuspForm (τ : ℍ) :
    modularDiscriminant τ = CuspForm.discriminant τ :=
  rfl

/-- Q-expansion infinite product formula `Δ(τ) = q * ∏' n, (1 - q ^ (n + 1)) ^ 24`. -/
theorem modularDiscriminant_eq_q_prod (τ : ℍ) :
    modularDiscriminant τ =
      𝕢 1 (τ : ℂ) * ∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1)) ^ 24 := by
  simpa only [modularDiscriminant_eq_discriminant, ModularForm.eta_q] using
    ModularForm.discriminant_eq_q_prod τ

/-- `modularDiscriminant` is non-vanishing on `ℍ`. -/
theorem modularDiscriminant_ne_zero (τ : ℍ) : modularDiscriminant τ ≠ 0 :=
  ModularForm.discriminant_ne_zero τ

/-- `ModularForm.discriminant` is invariant under the weight-12 slash action of `T`. -/
theorem modularDiscriminant_T_invariant :
    (ModularForm.discriminant ∣[(12 : ℤ)] ModularGroup.T) = ModularForm.discriminant :=
  ModularForm.discriminant_T_invariant

/-- `ModularForm.discriminant` is invariant under the weight-12 slash action of `S`. -/
theorem modularDiscriminant_S_invariant :
    (ModularForm.discriminant ∣[(12 : ℤ)] ModularGroup.S) = ModularForm.discriminant :=
  ModularForm.discriminant_S_invariant

/-- `ModularForm.discriminant` is invariant under the weight-12 slash action of every `γ : SL(2, ℤ)`. -/
theorem modularDiscriminant_slash_invariant (γ : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] γ) = ModularForm.discriminant :=
  SlashInvariantForm.slash_action_generators_SL2Z
    ModularForm.discriminant_S_invariant ModularForm.discriminant_T_invariant γ

/-- Explicit weight-12 transformation law of `modularDiscriminant` for every `γ : SL(2, ℤ)`:
`Δ(γ • τ) = (c τ + d) ^ 12 * Δ(τ)`. -/
theorem modularDiscriminant_SL2Z_apply (γ : SL(2, ℤ)) (τ : ℍ) :
    modularDiscriminant (γ • τ) =
      ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) ^ 12 * modularDiscriminant τ := by
  have hslash := congrFun (modularDiscriminant_slash_invariant γ) τ
  have hiff := (ModularForm.slash_action_eq'_iff (12 : ℤ) ModularForm.discriminant γ τ).mp hslash
  simpa only [modularDiscriminant_eq_discriminant, zpow_ofNat] using hiff

/-- Explicit Möbius transformation law for `ModularForm.eta ^ 24`:
for `a d - b c = 1`, `η((a τ + b) / (c τ + d)) ^ 24 = (c τ + d) ^ 12 * η(τ) ^ 24`. -/
theorem modularDiscriminant_moebius {a b c d : ℤ} (hdet : a * d - b * c = 1) (τ : ℍ) :
    ModularForm.eta (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ))) ^ 24 =
      ((c : ℂ) * (τ : ℂ) + (d : ℂ)) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24 := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using hdet⟩
  have hcoe :
      ((γ • τ : ℍ) : ℂ) =
        ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [γ]
  have h := modularDiscriminant_SL2Z_apply γ τ
  rw [modularDiscriminant_eq_eta_pow, modularDiscriminant_eq_eta_pow, dedekindEta_eq,
    dedekindEta_eq, hcoe] at h
  simpa [γ] using h

/-- The Dedekind eta multiplier `etaMultiplier γ` is always a 24th root of unity. -/
theorem etaMultiplier_pow_24 (γ : SL(2, ℤ)) : etaMultiplier γ ^ 24 = 1 := by
  have hη : dedekindEta (γ • UpperHalfPlane.I) ^ 24 =
      (etaMultiplier γ * etaAutomorphyFactor γ UpperHalfPlane.I *
        dedekindEta UpperHalfPlane.I) ^ 24 := by
    rw [dedekindEta_SL2Z_factor γ UpperHalfPlane.I]
  have hΔ := modularDiscriminant_SL2Z_apply γ UpperHalfPlane.I
  rw [modularDiscriminant_eq_eta_pow, modularDiscriminant_eq_eta_pow, hη] at hΔ
  have hfactor24 :
      etaAutomorphyFactor γ UpperHalfPlane.I ^ 24 =
        ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) ^ 12 := by
    unfold etaAutomorphyFactor
    rcases lt_trichotomy (γ 1 0) 0 with hc_neg | hc_zero | hc_pos
    · have hne : γ 1 0 ≠ 0 := hc_neg.ne
      have hnpos : ¬ 0 < γ 1 0 := not_lt_of_gt hc_neg
      simp only [hne, ↓reduceIte, hnpos]
      have hsq :
          ((Complex.I * ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ))) ^
              (1 / 2 : ℂ)) ^ 2 =
            Complex.I * ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) := by
        rw [show (1 / 2 : ℂ) = ((2 : ℕ)⁻¹ : ℂ) by norm_num, Complex.cpow_nat_inv_pow _ (by decide)]
      rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, hsq, mul_pow]
      have hI12 : (Complex.I : ℂ) ^ 12 = 1 := by
        rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
      rw [hI12, one_mul]
    · have hdet : γ 0 0 * γ 1 1 = 1 := by
        have h := sl2z_det_eq γ
        rwa [hc_zero, mul_zero, sub_zero] at h
      have hd12 : (γ 1 1 : ℂ) ^ 12 = 1 := by
        rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, hd⟩ | ⟨_, hd⟩
        · simp [hd]
        · simp [hd]
          norm_num
      simp only [hc_zero, ↓reduceIte, one_pow, Int.cast_zero, zero_mul, zero_add]
      exact hd12.symm
    · have hne : γ 1 0 ≠ 0 := hc_pos.ne'
      simp only [hne, ↓reduceIte, hc_pos]
      have hsq :
          ((-Complex.I * ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ))) ^
              (1 / 2 : ℂ)) ^ 2 =
            -Complex.I * ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) := by
        rw [show (1 / 2 : ℂ) = ((2 : ℕ)⁻¹ : ℂ) by norm_num, Complex.cpow_nat_inv_pow _ (by decide)]
      rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, hsq, mul_pow]
      have hnegI12 : (-Complex.I : ℂ) ^ 12 = 1 := by
        rw [neg_pow, show (-1 : ℂ) ^ 12 = 1 by norm_num, one_mul,
          show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
      rw [hnegI12, one_mul]
  rw [mul_pow, mul_pow, hfactor24] at hΔ
  have hdenom_ne : ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) ^ 12 ≠ 0 :=
    pow_ne_zero 12 (UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) UpperHalfPlane.I)
  have heta_ne : dedekindEta UpperHalfPlane.I ^ 24 ≠ 0 :=
    pow_ne_zero 24 (dedekindEta_ne_zero UpperHalfPlane.I)
  have hmul :
      etaMultiplier γ ^ 24 *
          (((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) ^ 12 *
            dedekindEta UpperHalfPlane.I ^ 24) =
        1 * (((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) ^ 12 *
          dedekindEta UpperHalfPlane.I ^ 24) := by
    linear_combination hΔ
  exact mul_right_cancel₀ (mul_ne_zero hdenom_ne heta_ne) hmul

/-- Rademacher's congruence identity: for any `γ : SL(2, ℤ)` with `0 < γ 1 0`,
`(γ 0 0 + γ 1 1) / γ 1 0 - 12 * dedekindSum (γ 1 1) (γ 1 0).natAbs` is an integer. -/
theorem dedekindSum_rademacher_int (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    ∃ m : ℤ,
      ((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (γ 1 0 : ℝ) -
        12 * dedekindSum (γ 1 1) (γ 1 0).natAbs = (m : ℝ) := by
  have hpow := etaMultiplier_pow_24 γ
  have hne : γ 1 0 ≠ 0 := hc.ne'
  simp only [etaMultiplier, hne, ↓reduceIte, hc, ← Complex.exp_nat_mul] at hpow
  rw [Complex.exp_eq_one_iff] at hpow
  rcases hpow with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  let val : ℝ :=
    ((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (γ 1 0 : ℝ) - 12 * dedekindSum (γ 1 1) (γ 1 0).natAbs
  have h24 :
      ((24 : ℕ) : ℂ) * (π * Complex.I *
          ((((γ 0 0 + γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℝ)) -
            dedekindSum (γ 1 1) (γ 1 0).natAbs : ℝ) : ℂ)) =
        (val : ℂ) * (2 * π * Complex.I) := by
    dsimp [val]
    rw [Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_mul]
    norm_num
    ring
  rw [h24] at hm
  have hmC : (val : ℂ) = (m : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hm
  have hmR : val = (m : ℝ) := by exact_mod_cast hmC
  exact hmR

/-- `modularDiscriminant` vanishes at the cusp `i∞`. -/
theorem modularDiscriminant_isZeroAtImInfty : IsZeroAtImInfty modularDiscriminant :=
  ModularForm.discriminant_isZeroAtImInfty

/-- The first Fourier (`q`-expansion) coefficient of `Δ` equals `1`. -/
theorem modularDiscriminant_qExpansion_coeff_one :
    (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 :=
  ModularForm.discriminant_qExpansion_coeff_one

/-- Ramanujan-type derivative identity `d/dτ Δ(τ) = 2 π i E₂(τ) Δ(τ)` on `ℍ`. -/
theorem deriv_modularDiscriminant_comp_ofComplex (τ : ℍ) :
    deriv (modularDiscriminant ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
      2 * π * Complex.I * EisensteinSeries.E2 τ * modularDiscriminant τ := by
  have hD := congrFun ModularForm.normalizedDerivOfComplex_discriminant τ
  simp only [Derivative.normalizedDerivOfComplex, Pi.mul_apply] at hD
  have hmod : modularDiscriminant = ModularForm.discriminant := rfl
  rw [hmod]
  have h2piI : (2 * π * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [mul_assoc (2 * π * Complex.I), ← hD]
  field_simp [h2piI]

end Discriminant

end AnalyticNumberTheory.ModularAndPartitions
