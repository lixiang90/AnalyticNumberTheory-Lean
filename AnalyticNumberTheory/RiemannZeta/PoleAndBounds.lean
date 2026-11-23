import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Meromorphic.Order
import AnalyticNumberTheory.AnalyticTools.Transforms
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PhragmenLindelof
import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-!
# Pole at `s = 1`, Trivial Zeros, and Strip/Vertical-Line Bounds for `riemannZeta`

This file collects the local behavior of `riemannZeta` around `s = 1` (simple pole of residue `1`,
Laurent constant term `γ`, holomorphicity of `ζ(s) - 1/(s-1)`, derivative and log-derivative
expansions), establishes simplicity of the trivial zeros `s = -2 * (k + 1)` together with
non-vanishing on `1 ≤ Re s`, proves logarithmic bounds on `ζ(1 + it)` and `ζ'(1 + it)`, and
derives the Phragmén–Lindelöf convexity bounds and vertical-order upper bound `μ(σ) ≤ (1 - σ) / 2`
in the critical strip `0 ≤ σ ≤ 1`.
-/

open Complex Real Filter MeasureTheory Set Asymptotics
open scoped Topology Nat ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

section PoleAtOne

/-- Simple pole of `riemannZeta` at `s = 1` with residue `1`:
`(s - 1) * riemannZeta s → 1` along `𝓝[≠] 1`. -/
theorem tendsto_sub_one_mul_riemannZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

/-- Explicit Laurent constant term at `s = 1`:
`riemannZeta s - 1 / (s - 1) → Real.eulerMascheroniConstant` along `𝓝[≠] 1`. -/
theorem tendsto_riemannZeta_sub_one_div_eulerMascheroni :
    Tendsto (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) (𝓝[≠] 1)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
  tendsto_riemannZeta_sub_one_div

/-- `riemannZeta s - 1 / (s - 1)` is complex differentiable on `{1}ᶜ`. -/
theorem differentiableOn_riemannZeta_sub_one_div :
    DifferentiableOn ℂ (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) ({1}ᶜ : Set ℂ) := by
  intro s hs
  have hne : s ≠ 1 := Set.mem_compl_singleton_iff.mp hs
  have h1 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hne
  have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ 1 / (z - 1)) s := by
    have hinv : DifferentiableAt ℂ (fun z : ℂ ↦ (z - 1)⁻¹) s :=
      (differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hne)
    simpa only [one_div] using hinv
  exact (h1.sub h2).differentiableWithinAt

/-- Away from `s = 1`, `riemannZeta s - 1 / (s - 1)` agrees with the entire function
`riemannZeta₀ s`. -/
theorem riemannZeta_sub_one_div_eq_riemannZeta₀ {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s - 1 / (s - 1) = riemannZeta₀ s := by
  rw [riemannZeta_eq_inv_sub_add hs, one_div]
  ring

/-- The entire completion `riemannZeta₀` of `ζ(s) - 1/(s-1)` is differentiable everywhere. -/
theorem differentiable_riemannZeta₀_bridge : Differentiable ℂ riemannZeta₀ :=
  differentiable_riemannZeta₀

/-- The entire completion `riemannZeta₁` of `(s - 1) * ζ(s)` is differentiable everywhere. -/
theorem differentiable_riemannZeta₁_bridge : Differentiable ℂ riemannZeta₁ :=
  differentiable_riemannZeta₁

/-- `riemannZeta` has a simple pole at `s = 1`, i.e., `meromorphicOrderAt riemannZeta 1 = -1`. -/
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = (-1 : ℤ) := by
  have hev : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] fun s : ℂ ↦ (s - 1)⁻¹ * riemannZeta₁ s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact riemannZeta_eq_inv_sub_mul hs
  rw [meromorphicOrderAt_congr hev]
  have hf_an : AnalyticAt ℂ (fun s : ℂ ↦ s - 1) 1 :=
    (differentiable_id.sub_const 1).analyticAt 1
  have hg_an : AnalyticAt ℂ riemannZeta₁ 1 :=
    differentiable_riemannZeta₁.analyticAt 1
  have hord_f : analyticOrderAt (fun s : ℂ ↦ s - 1) 1 = 1 :=
    hf_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) (by simp)
  have hm_f : meromorphicOrderAt (fun s : ℂ ↦ s - 1) 1 = (1 : ℤ) := by
    rw [hf_an.meromorphicOrderAt_eq, hord_f]
    rfl
  have hm_inv : meromorphicOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) 1 = (-1 : ℤ) := by
    change meromorphicOrderAt ((fun s : ℂ ↦ s - 1)⁻¹) 1 = (-1 : ℤ)
    rw [meromorphicOrderAt_inv, hm_f]
    rfl
  have hord_g : analyticOrderAt riemannZeta₁ 1 = 0 :=
    hg_an.analyticOrderAt_eq_zero.mpr (by simp)
  have hm_g : meromorphicOrderAt riemannZeta₁ 1 = (0 : ℤ) := by
    rw [hg_an.meromorphicOrderAt_eq, hord_g]
    rfl
  have hm_inv_mer : MeromorphicAt (fun s : ℂ ↦ (s - 1)⁻¹) 1 :=
    hf_an.meromorphicAt.inv
  change meromorphicOrderAt ((fun s : ℂ ↦ (s - 1)⁻¹) * riemannZeta₁) 1 = (-1 : ℤ)
  rw [meromorphicOrderAt_mul hm_inv_mer hg_an.meromorphicAt, hm_inv, hm_g]
  norm_num

/-- Derivative pole behavior at `s = 1`: `(s - 1) ^ 2 * deriv riemannZeta s → -1` along
`𝓝[≠] 1`. -/
theorem tendsto_sq_sub_one_mul_deriv_riemannZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) ^ 2 * deriv riemannZeta s) (𝓝[≠] 1) (𝓝 (-1)) := by
  have hev : (fun s : ℂ ↦ (s - 1) ^ 2 * deriv riemannZeta s) =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s : ℂ ↦ -1 + (s - 1) ^ 2 * deriv riemannZeta₀ s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add hs]
    have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp [hs']
  refine Tendsto.congr' hev.symm ?_
  have hd : Continuous (deriv riemannZeta₀) :=
    continuousOn_univ.mp (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd
      isOpen_univ).deriv.continuousOn
  have hcont : Continuous fun s : ℂ ↦ -1 + (s - 1) ^ 2 * deriv riemannZeta₀ s := by fun_prop
  have hlim : Tendsto (fun s : ℂ ↦ -1 + (s - 1) ^ 2 * deriv riemannZeta₀ s) (𝓝 (1 : ℂ))
      (𝓝 (-1 + ((1 : ℂ) - 1) ^ 2 * deriv riemannZeta₀ 1)) :=
    hcont.tendsto (1 : ℂ)
  rw [sub_self, zero_pow two_ne_zero, zero_mul, add_zero] at hlim
  exact hlim.mono_left nhdsWithin_le_nhds

/-- Regularized derivative limit at `s = 1`:
`deriv riemannZeta s + (s - 1)⁻¹ ^ 2 → deriv riemannZeta₀ 1` along `𝓝[≠] 1`. -/
theorem tendsto_deriv_riemannZeta_add_sq_inv :
    Tendsto (fun s : ℂ ↦ deriv riemannZeta s + (s - 1)⁻¹ ^ 2) (𝓝[≠] 1)
      (𝓝 (deriv riemannZeta₀ 1)) := by
  have hev : (fun s : ℂ ↦ deriv riemannZeta s + (s - 1)⁻¹ ^ 2) =ᶠ[𝓝[≠] (1 : ℂ)]
      deriv riemannZeta₀ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add hs]
    ring
  refine Tendsto.congr' hev.symm ?_
  have hd : Continuous (deriv riemannZeta₀) :=
    continuousOn_univ.mp (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd
      isOpen_univ).deriv.continuousOn
  exact hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- Logarithmic derivative expansion at `s = 1`:
`logDeriv riemannZeta s + (s - 1)⁻¹ → Real.eulerMascheroniConstant` along `𝓝[≠] 1`. -/
theorem tendsto_logDeriv_riemannZeta_add_inv :
    Tendsto (fun s : ℂ ↦ logDeriv riemannZeta s + (s - 1)⁻¹) (𝓝[≠] 1)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have h0 : Tendsto (fun s : ℂ ↦
      deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ - (Real.eulerMascheroniConstant : ℂ))
      (𝓝[≠] 1) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.bound (half_pos hε)] with s hs
    rw [dist_zero_right]
    exact lt_of_le_of_lt (by simpa using hs) (half_lt_self hε)
  have hlim : Tendsto (fun s : ℂ ↦ (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ -
      (Real.eulerMascheroniConstant : ℂ)) + (Real.eulerMascheroniConstant : ℂ))
      (𝓝[≠] 1) (𝓝 (0 + (Real.eulerMascheroniConstant : ℂ))) :=
    h0.add tendsto_const_nhds
  simpa [logDeriv_apply] using hlim

end PoleAtOne

section TrivialZerosAndNonvanishing

/-- Trivial zeros of `riemannZeta`: `riemannZeta (-2 * (k + 1)) = 0` for all `k : ℕ`. -/
theorem riemannZeta_trivial_zero (k : ℕ) :
    riemannZeta (-2 * ((k : ℂ) + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one k

/-- Trivial zeros indexed by positive natural numbers `k ≥ 1`: `riemannZeta (-2 * k) = 0`. -/
theorem riemannZeta_trivial_zero_of_pos {k : ℕ} (hk : 1 ≤ k) :
    riemannZeta (-2 * (k : ℂ)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  simpa [Nat.cast_add, Nat.cast_one] using riemannZeta_trivial_zero m

/-- Exact derivative formula for `riemannZeta` at each trivial zero `-2 * (k + 1)`:
`deriv riemannZeta (-2 * (k + 1)) = (-1)^(k+1) * π * (2π)^(-2*(k+1)-1) * (2k+2)! * ζ(2k+3)`. -/
theorem deriv_riemannZeta_neg_two_mul_nat_add_one (k : ℕ) :
    deriv riemannZeta (-2 * ((k : ℂ) + 1)) =
      (-1 : ℂ) ^ (k + 1) * (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (-2 * ((k : ℂ) + 1) - 1) *
        (((2 * k + 2)! : ℕ) : ℂ) * riemannZeta (2 * (k : ℂ) + 3) := by
  let s₀ : ℂ := -2 * ((k : ℂ) + 1)
  let g : ℂ → ℂ := fun s ↦ 2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s) *
    riemannZeta (1 - s)
  let h : ℂ → ℂ := fun s ↦ Complex.sin ((Real.pi : ℂ) * s / 2)
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hre_s0 : s₀.re < 0 := by
    simp only [s₀, neg_mul, neg_re, mul_re, re_ofNat, add_re, natCast_re, one_re, im_ofNat,
      add_im, natCast_im, one_im, add_zero, mul_zero, sub_zero]
    linarith
  have hev : riemannZeta =ᶠ[𝓝 s₀] fun s ↦ g s * h s := by
    have hopen : IsOpen {s : ℂ | s.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds hre_s0] with s hs
    have hs_re : s.re < 0 := hs
    have h1 : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp only [sub_re, one_re, neg_re, natCast_re] at hre
      linarith
    have h2 : 1 - s ≠ 1 := by
      intro hEq
      have hre := congrArg Complex.re hEq
      simp only [sub_re, one_re] at hre
      linarith
    have hfe := riemannZeta_one_sub h1 h2
    rw [sub_sub_cancel] at hfe
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = h s := by
      simp only [h]
      rw [show (Real.pi : ℂ) * (1 - s) / 2 = Real.pi / 2 - Real.pi * s / 2 by ring,
        Complex.cos_pi_div_two_sub]
    have hexp : -(1 - s) = s - 1 := by ring
    rw [hfe, hcos, hexp]
    dsimp only [g, h]
    ring
  have hg_diff : DifferentiableAt ℂ g s₀ := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ 2 * (2 * (Real.pi : ℂ)) ^ (s - 1)) s₀ :=
      ((differentiableAt_id.sub_const 1).const_cpow (Or.inl h2pi)).const_mul 2
    have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ Complex.Gamma (1 - s)) s₀ := by
      refine (Complex.differentiableAt_Gamma _ fun m hm ↦ ?_).comp s₀
        ((differentiableAt_const 1).sub differentiableAt_id)
      have hre := congrArg Complex.re hm
      simp only [s₀, sub_re, one_re, neg_mul, neg_re, mul_re, re_ofNat, add_re, natCast_re,
        im_ofNat, add_im, natCast_im, one_im, add_zero, mul_zero, sub_zero] at hre
      linarith
    have h3 : DifferentiableAt ℂ (fun s : ℂ ↦ riemannZeta (1 - s)) s₀ := by
      refine (differentiableAt_riemannZeta ?_).comp s₀
        ((differentiableAt_const 1).sub differentiableAt_id)
      intro hEq
      have hre := congrArg Complex.re hEq
      simp only [s₀, sub_re, one_re, neg_mul, neg_re, mul_re, re_ofNat, add_re, natCast_re,
        im_ofNat, add_im, natCast_im, one_im, add_zero, mul_zero, sub_zero] at hre
      linarith
    exact (h1.mul h2).mul h3
  have hh_deriv : HasDerivAt h ((Real.pi : ℂ) / 2 * Complex.cos ((Real.pi : ℂ) * s₀ / 2)) s₀ := by
    have hlin : HasDerivAt (fun s : ℂ ↦ (Real.pi : ℂ) * s / 2) ((Real.pi : ℂ) / 2) s₀ := by
      have h1 := ((hasDerivAt_id s₀).const_mul (Real.pi : ℂ)).div_const 2
      simpa using h1
    convert hlin.csin using 1
    ring
  have hprod := hg_diff.hasDerivAt.mul hh_deriv
  have hs0_eq : h s₀ = 0 := by
    have harg : (Real.pi : ℂ) * s₀ / 2 = -(((k + 1 : ℕ) : ℂ) * Real.pi) := by
      dsimp only [s₀]; push_cast; ring
    dsimp only [h]
    rw [harg, Complex.sin_neg, neg_eq_zero]
    exact Complex.sin_nat_mul_pi (k + 1)
  have hcos_nat (n : ℕ) : Complex.cos ((n : ℂ) * Real.pi) = (-1 : ℂ) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Complex.cos_add_pi, ih, pow_succ]
      ring
  have hcos_eq : Complex.cos ((Real.pi : ℂ) * s₀ / 2) = (-1 : ℂ) ^ (k + 1) := by
    have harg : (Real.pi : ℂ) * s₀ / 2 = -(((k + 1 : ℕ) : ℂ) * Real.pi) := by
      dsimp only [s₀]; push_cast; ring
    rw [harg, Complex.cos_neg, hcos_nat]
  have h1_sub_s0 : 1 - s₀ = 2 * (k : ℂ) + 3 := by
    dsimp only [s₀]; ring
  have hG_eq : Complex.Gamma (1 - s₀) = (((2 * k + 2)! : ℕ) : ℂ) := by
    rw [h1_sub_s0, show 2 * (k : ℂ) + 3 = ((2 * k + 2 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hgh : (fun s ↦ g s * h s) = g * h := rfl
  rw [hev.deriv_eq, hgh, hprod.deriv, hs0_eq, mul_zero, zero_add, hcos_eq]
  dsimp only [g]
  rw [hG_eq, h1_sub_s0]
  change (2 * (2 * (Real.pi : ℂ)) ^ (s₀ - 1) * (((2 * k + 2)! : ℕ) : ℂ) *
      riemannZeta (2 * (k : ℂ) + 3)) * ((Real.pi : ℂ) / 2 * (-1 : ℂ) ^ (k + 1)) = _
  ring

/-- Every trivial zero `s = -2 * (k + 1)` has nonzero derivative `ζ'(-2 * (k + 1)) ≠ 0`. -/
theorem deriv_riemannZeta_neg_two_mul_nat_add_one_ne_zero (k : ℕ) :
    deriv riemannZeta (-2 * ((k : ℂ) + 1)) ≠ 0 := by
  rw [deriv_riemannZeta_neg_two_mul_nat_add_one k]
  have h1 : (-1 : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h2 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h3 : (2 * (Real.pi : ℂ)) ^ (-2 * ((k : ℂ) + 1) - 1) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero h2))
  have h4 : (((2 * k + 2)! : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h5 : riemannZeta (2 * (k : ℂ) + 3) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5

/-- Every trivial zero `-2 * (k + 1)` is a simple zero (`analyticOrderAt riemannZeta (-2*(k+1)) = 1`). -/
theorem analyticOrderAt_riemannZeta_neg_two_mul_nat_add_one (k : ℕ) :
    analyticOrderAt riemannZeta (-2 * ((k : ℂ) + 1)) = 1 := by
  have han : AnalyticAt ℂ riemannZeta (-2 * ((k : ℂ) + 1)) := by
    refine analyticOn_riemannZeta _ ?_
    intro h
    have hre := congrArg Complex.re h
    simp only [neg_mul, neg_re, mul_re, re_ofNat, add_re, natCast_re, one_re, im_ofNat,
      add_im, natCast_im, one_im, add_zero, mul_zero, sub_zero] at hre
    linarith
  exact han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (riemannZeta_trivial_zero k) (deriv_riemannZeta_neg_two_mul_nat_add_one_ne_zero k)

/-- Every trivial zero `-2 * k` (`k ≥ 1`) is a simple zero (`analyticOrderAt = 1`). -/
theorem analyticOrderAt_riemannZeta_neg_two_mul {k : ℕ} (hk : 1 ≤ k) :
    analyticOrderAt riemannZeta (-2 * (k : ℂ)) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  simpa [Nat.cast_add, Nat.cast_one] using analyticOrderAt_riemannZeta_neg_two_mul_nat_add_one m

/-- Non-vanishing of `riemannZeta` on `1 < s.re`. -/
theorem riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  _root_.riemannZeta_ne_zero_of_one_le_re hs.le

/-- Non-vanishing of `riemannZeta` on `1 ≤ s.re`. -/
theorem riemannZeta_ne_zero_of_one_le_re_bridge {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  _root_.riemannZeta_ne_zero_of_one_le_re hs

/-- Characterization of zeros of `riemannZeta` in `s.re ≤ 0`: only the trivial zeros
`s = -2 * (n + 1)`. -/
theorem riemannZeta_eq_zero_iff_of_re_nonpos_bridge {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * (n + 1) :=
  _root_.riemannZeta_eq_zero_iff_of_re_nonpos hs

/-- Every non-trivial zero of `riemannZeta` lies strictly inside the open critical strip
`0 < s.re < 1`. -/
theorem nontrivial_zero_re_mem_Ioo {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    push Not at hle
    exact htriv ((riemannZeta_eq_zero_iff_of_re_nonpos hle).mp hz)
  · by_contra hge
    push Not at hge
    exact _root_.riemannZeta_ne_zero_of_one_le_re hge hz

end TrivialZerosAndNonvanishing

section HalfPlaneAndVerticalLineBounds

private lemma isPathConnected_re_gt_pos_sdiff_one :
    IsPathConnected {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}
  refine ⟨(2 : ℂ), ⟨by norm_num, by norm_num⟩, fun {z} hz ↦ ?_⟩
  by_cases him : z.im ≠ 0
  · let γ : unitInterval → ℂ := fun t ↦ ((1 - (t : ℝ) : ℝ) : ℂ) * 2 + ((t : ℝ) : ℂ) * z
    refine ⟨⟨⟨γ, by fun_prop⟩, by simp [γ], by simp [γ]⟩, fun t ↦ ?_⟩
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    refine ⟨?_, ?_⟩
    · change 0 < (γ t).re
      simp only [γ, add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, mul_zero, sub_zero,
        zero_mul]
      rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
      · rw [← ht_zero]
        norm_num
      · have hmul1 : 0 ≤ (1 - (t : ℝ)) * 2 := by positivity
        have hmul2 : 0 < (t : ℝ) * z.re := mul_pos ht_pos hz.1
        linarith
    · intro hEq
      have hEq' : γ t = 1 := hEq
      have hIm : (γ t).im = (1 : ℂ).im := congrArg Complex.im hEq'
      simp only [γ, add_im, mul_im, ofReal_re, ofReal_im, im_ofNat, mul_zero, zero_mul, add_zero,
        one_im, zero_add, mul_eq_zero] at hIm
      rcases hIm with ht_zero | him_zero
      · have h21 : (2 : ℂ) = 1 := calc
          (2 : ℂ) = γ t := by simp [γ, ht_zero]
          _ = 1 := hEq'
        exact absurd h21 (by norm_num)
      · exact him him_zero
  · push Not at him
    let mid : ℂ := (2 : ℂ) + I
    have hpath1 : JoinedIn U (2 : ℂ) mid := by
      refine ⟨⟨⟨fun t : unitInterval ↦ (2 : ℂ) + ((t : ℝ) : ℂ) * I, by fun_prop⟩,
        by simp, by simp [mid]⟩, fun t ↦ ?_⟩
      refine ⟨by simp, ?_⟩
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp at hRe
    have hpath2 : JoinedIn U mid z := by
      let γ : unitInterval → ℂ := fun t ↦ ((1 - (t : ℝ) : ℝ) : ℂ) * mid + ((t : ℝ) : ℂ) * z
      refine ⟨⟨⟨γ, by fun_prop⟩, by simp [γ], by simp [γ]⟩, fun t ↦ ?_⟩
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      refine ⟨?_, ?_⟩
      · change 0 < (γ t).re
        simp only [γ, mid, add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, I_re, add_zero,
          zero_mul, sub_zero]
        rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
        · rw [← ht_zero]
          norm_num
        · have hmul1 : 0 ≤ (1 - (t : ℝ)) * 2 := by positivity
          have hmul2 : 0 < (t : ℝ) * z.re := mul_pos ht_pos hz.1
          linarith
      · intro hEq
        have hEq' : γ t = 1 := hEq
        rcases eq_or_lt_of_le ht1 with ht_one | ht_lt
        · have hEnd : γ t = z := by simp [γ, ht_one]
          exact hz.2 (hEnd ▸ hEq')
        · have hIm : (γ t).im = (1 : ℂ).im := congrArg Complex.im hEq'
          simp [γ, mid, him] at hIm
          linarith
    exact hpath1.trans hpath2

private lemma cpow_ofReal_hasDerivAt' {t : ℝ} (ht : 0 < t) (c : ℂ) :
    HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hmem : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
  simpa using ((hasDerivAt_id (t : ℂ)).cpow_const hmem).comp_ofReal

private lemma integral_cpow_ofReal_eq' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : s ≠ 1) :
    ∫ u in a..b, (u : ℂ) ^ (-s) = ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  have hderiv : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ (x : ℂ) ^ (1 - s) / (1 - s)) ((u : ℂ) ^ (-s)) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu_pos : 0 < u := lt_of_lt_of_le ha hu.1
    have hd := (cpow_ofReal_hasDerivAt' hu_pos (1 - s)).div_const (1 - s)
    convert hd using 1
    have hexp : (1 - s) - 1 = -s := by ring
    rw [hexp, mul_div_cancel_left₀ _ hne]
  have hint : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ) ^ (-s)) volume a b := by
    have hcont : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (-s)) (Set.Icc a b) :=
      continuousOn_of_forall_continuousAt fun u hu ↦
        (cpow_ofReal_hasDerivAt' (lt_of_lt_of_le ha hu.1) (-s)).continuousAt
    exact hcont.intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

private lemma euler_maclaurin_Ioc_complex {M N : ℕ} (hMN : M ≤ N)
    {f f' : ℝ → ℂ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Ioc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f N - f M) / 2 +
        ∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t := by
  have hle : (M : ℝ) ≤ N := Nat.cast_le.mpr hMN
  have hre_em := euler_maclaurin_first_order_Ioc hMN
    (fun t ht ↦ Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht))
    (Complex.continuous_re.comp_continuousOn hf')
  have him_em := euler_maclaurin_first_order_Ioc hMN
    (fun t ht ↦ Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht))
    (Complex.continuous_im.comp_continuousOn hf')
  have hf_cont : ContinuousOn f (Set.Icc (M : ℝ) N) :=
    fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hf_int : IntervalIntegrable f volume (M : ℝ) N := hf_cont.intervalIntegrable_of_Icc hle
  have hsaw_int : IntervalIntegrable (fun t ↦ (sawtooth t : ℂ) * f' t) volume (M : ℝ) N := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    refine Integrable.mono' (hf'.norm.integrableOn_Icc.const_mul (1 / 2)) ?_ ?_
    · exact ((Complex.continuous_ofReal.aestronglyMeasurable.comp_measurable
        (measurable_fract.sub_const _)).mul (hf'.aestronglyMeasurable measurableSet_Icc))
    · filter_upwards with t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (sawtooth_abs_le t) (norm_nonneg _)
  have hint_re1 := Complex.reCLM.intervalIntegral_comp_comm hf_int
  have hint_im1 := Complex.imCLM.intervalIntegral_comp_comm hf_int
  have hint_re2 := Complex.reCLM.intervalIntegral_comp_comm hsaw_int
  have hint_im2 := Complex.imCLM.intervalIntegral_comp_comm hsaw_int
  apply Complex.ext
  · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.re_sum]
    change ∑ n ∈ Finset.Ioc M N, (f n).re =
      (Complex.reCLM (∫ t in (M : ℝ)..N, f t)) + ((f N).re - (f M).re) / 2 +
        Complex.reCLM (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t)
    rw [← hint_re1, ← hint_re2]
    simpa [Complex.reCLM_apply] using hre_em
  · simp only [Complex.add_im, Complex.div_ofNat_im, Complex.sub_im, Complex.im_sum]
    change ∑ n ∈ Finset.Ioc M N, (f n).im =
      (Complex.imCLM (∫ t in (M : ℝ)..N, f t)) + ((f N).im - (f M).im) / 2 +
        Complex.imCLM (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t)
    rw [← hint_im1, ← hint_im2]
    simpa [Complex.imCLM_apply] using him_em

private lemma mellin_sawtooth_hasDerivAt {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt
      (fun z : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))
      (-∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)) s := by
  let f : ℝ → ℂ := Set.indicator (Set.Ioi (N : ℝ)) (fun u : ℝ ↦ (sawtooth u : ℂ))
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf_loc : LocallyIntegrableOn f (Set.Ioi 0) := by
    have hm : Measurable f :=
      Measurable.indicator (Complex.continuous_ofReal.measurable.comp
        (measurable_fract.sub_const _)) measurableSet_Ioi
    have hloc : LocallyIntegrable f volume := by
      refine (locallyIntegrable_const (1 / 2 : ℝ)).mono hm.aestronglyMeasurable
        (Eventually.of_forall fun u ↦ ?_)
      rw [Real.norm_of_nonneg (by norm_num)]
      by_cases hu : (N : ℝ) < u
      · simpa [f, hu, Complex.norm_real, Real.norm_eq_abs] using sawtooth_abs_le u
      · simp [f, hu]
    exact hloc.locallyIntegrableOn _
  have hf_top : f =O[atTop] (fun u : ℝ ↦ u ^ (0 : ℝ)) := by
    refine IsBigO.of_bound (1 / 2) ?_
    filter_upwards [eventually_gt_atTop (N : ℝ)] with u hu
    simpa [f, hu, Complex.norm_real, Real.norm_eq_abs] using sawtooth_abs_le u
  let b : ℝ := -(s.re + 1)
  have hf_bot : f =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-b)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT hN_pos] with u hu
    have huN : ¬ (N : ℝ) < u := not_lt.mpr hu.2.le
    simp [f, huN]
  have hmel := (mellin_hasDerivAt_strip (a := 0) (b := b) hf_loc hf_top
    (by simp [neg_re, hs] : (-s).re < 0) hf_bot (by simp [b])).2
  have hcomp : HasDerivAt (fun z : ℂ ↦ mellin f (-z))
      (mellin (fun u ↦ Real.log u • f u) (-s) * (-1)) s :=
    hmel.comp s (hasDerivAt_neg s)
  have heq1 : (fun z : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1)) =
      fun z : ℂ ↦ mellin f (-z) := by
    ext z
    rw [mellin]
    have hcongr : Set.EqOn
        (fun u : ℝ ↦ (u : ℂ) ^ (-z - 1) • f u)
        (Set.indicator (Set.Ioi (N : ℝ)) (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1)))
        (Set.Ioi (0 : ℝ)) := by
      intro u _
      by_cases huN : (N : ℝ) < u
      · simp [f, Set.mem_Ioi, huN, smul_eq_mul, mul_comm]
      · simp [f, Set.mem_Ioi, huN]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (fun _ hu ↦ lt_trans hN_pos hu)]
  have heq2 : mellin (fun u ↦ Real.log u • f u) (-s) * (-1) =
      -∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [mul_neg_one, mellin]
    have hcongr : Set.EqOn
        (fun u : ℝ ↦ (u : ℂ) ^ (-s - 1) • (Real.log u • f u))
        (Set.indicator (Set.Ioi (N : ℝ))
          (fun u : ℝ ↦ (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)))
        (Set.Ioi (0 : ℝ)) := by
      intro u _
      by_cases huN : (N : ℝ) < u
      · simp only [f, Set.indicator_of_mem (Set.mem_Ioi.mpr huN), smul_eq_mul, Complex.real_smul]
        ring
      · simp [f, Set.mem_Ioi, huN]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (fun _ hu ↦ lt_trans hN_pos hu)]
  rw [heq1, ← heq2]
  exact hcomp

private lemma integrableOn_sawtooth_cpow_Ioi' {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi a) := by
  have hpow_int : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-s.re - 1)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul (1 / 2)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hmeas_saw : Measurable fun u : ℝ ↦ (sawtooth u : ℂ) :=
      Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const _)
    have hcont_pow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (-s - 1)) (Set.Ioi a) :=
      continuousOn_of_forall_continuousAt fun u hu ↦
        (cpow_ofReal_hasDerivAt' (lt_trans ha hu) (-s - 1)).continuousAt
    exact (hmeas_saw.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
      (hcont_pow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := lt_trans ha hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)

private lemma riemannZeta_eulerMaclaurin_N {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) -
      (N : ℂ) ^ (1 - s) / (1 - s) - (1 / 2 : ℂ) * (N : ℂ) ^ (-s) -
      s * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  let L : ℂ → ℂ := riemannZeta
  let R : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z) -
    (N : ℂ) ^ (1 - z) / (1 - z) - (1 / 2 : ℂ) * (N : ℂ) ^ (-z) -
    z * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1)
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL_an : AnalyticOnNhd ℂ L U := analyticOn_riemannZeta.mono (fun _ hz ↦ hz.2)
  have hR_diff : DifferentiableOn ℂ R U := by
    intro z hz
    have hsum : DifferentiableAt ℂ (fun w : ℂ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-w)) z := by
      refine DifferentiableAt.fun_sum fun n hn ↦ ?_
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp only [Finset.mem_Icc] at hn; omega)
      exact (differentiableAt_id.neg).const_cpow (Or.inl hn0)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ (N : ℂ) ^ (1 - w) / (1 - w)) z := by
      have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.2.symm
      fun_prop (disch := first | exact hne | exact Or.inl hN_ne)
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 2 : ℂ) * (N : ℂ) ^ (-w)) z :=
      (differentiableAt_id.neg.const_cpow (Or.inl hN_ne)).const_mul _
    have h3 : DifferentiableAt ℂ
        (fun w : ℂ ↦ w * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-w - 1)) z :=
      differentiableAt_id.mul (mellin_sawtooth_hasDerivAt hN hz.1).differentiableAt
    exact (((hsum.sub h1).sub h2).sub h3).differentiableWithinAt
  have hU_open : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (0 : ℝ) < z.re}).inter
      (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})
  have hR_an : AnalyticOnNhd ℂ R U := hR_diff.analyticOnNhd hU_open
  have h_gt_one : ∀ {z : ℂ}, 1 < z.re → L z = R z := by
    intro z hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hz0 : 0 < z.re := lt_trans zero_lt_one hz
    have hem (M : ℕ) (hNM : N ≤ M) :
        ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-z) =
          ((M : ℂ) ^ (1 - z) - (N : ℂ) ^ (1 - z)) / (1 - z) +
            ((M : ℂ) ^ (-z) - (N : ℂ) ^ (-z)) / 2 -
            z * ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) := by
      have hf : ∀ t ∈ Set.Icc (N : ℝ) M,
          HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-z)) (-z * (t : ℂ) ^ (-z - 1)) t :=
        fun t ht ↦ cpow_ofReal_hasDerivAt' (lt_of_lt_of_le hN_pos ht.1) (-z)
      have hf' : ContinuousOn (fun u : ℝ ↦ -z * (u : ℂ) ^ (-z - 1)) (Set.Icc (N : ℝ) M) :=
        continuousOn_const.mul (continuousOn_of_forall_continuousAt fun u hu ↦
          (cpow_ofReal_hasDerivAt' (lt_of_lt_of_le hN_pos hu.1) (-z - 1)).continuousAt)
      have h_em := euler_maclaurin_Ioc_complex hNM hf hf'
      rw [integral_cpow_ofReal_eq' hN_pos (Nat.cast_le.mpr hNM) hz1] at h_em
      have hpull : ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (-z * (t : ℂ) ^ (-z - 1)) =
          -z * ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) := by
        have hcongr : (fun t : ℝ ↦ (sawtooth t : ℂ) * (-z * (t : ℂ) ^ (-z - 1))) =
            fun t : ℝ ↦ (-z) * ((sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
          ext t; ring
        rw [hcongr, intervalIntegral.integral_const_mul]
      rw [hpull] at h_em
      linear_combination h_em
    have hsum_full : Tendsto (fun M : ℕ ↦ ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-z))
        atTop (𝓝 (riemannZeta z)) := by
      have hsumm : Summable fun n : ℕ ↦ 1 / (n + 1 : ℂ) ^ z := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hz)
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
      refine hsumm.hasSum.tendsto_sum_nat.congr fun M ↦ ?_
      refine Finset.sum_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
      · intro a _ b _ h; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb; exact ⟨b - 1, by simp; omega, by omega⟩
      · intro n _; rw [Nat.cast_add, Nat.cast_one, one_div, cpow_neg]
    have hsum_tail : Tendsto (fun M : ℕ ↦ ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-z))
        atTop (𝓝 (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))) := by
      have hlim := hsum_full.sub_const (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop N] with M hNM
      have hsplit : ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-z) =
          (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) + ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-z) := by
        rw [← Finset.sum_union]
        · congr 1; ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
        · rw [Finset.disjoint_left]; intro n hn1 hn2
          simp only [Finset.mem_Icc] at hn1; simp only [Finset.mem_Ioc] at hn2; omega
      rw [hsplit, add_sub_cancel_left]
    have hpow1 : Tendsto (fun M : ℕ ↦ (M : ℂ) ^ (1 - z)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hreal : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (1 - z.re)) atTop (𝓝 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < z.re - 1)).comp tendsto_natCast_atTop_atTop).congr
          fun M ↦ by dsimp; rw [show -(z.re - 1) = 1 - z.re by ring]
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      rw [Complex.norm_natCast_cpow_of_pos hM, sub_re, one_re]
    have hpow2 : Tendsto (fun M : ℕ ↦ (M : ℂ) ^ (-z)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hreal : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hz0).comp tendsto_natCast_atTop_atTop
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      rw [Complex.norm_natCast_cpow_of_pos hM, neg_re]
    have hint_lim : Tendsto
        (fun M : ℕ ↦ ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))) :=
      (intervalIntegral_tendsto_integral_Ioi N (integrableOn_sawtooth_cpow_Ioi' hN_pos hz0)
        tendsto_id).comp tendsto_natCast_atTop_atTop
    have hrhs_lim : Tendsto (fun M : ℕ ↦
        ((M : ℂ) ^ (1 - z) - (N : ℂ) ^ (1 - z)) / (1 - z) +
          ((M : ℂ) ^ (-z) - (N : ℂ) ^ (-z)) / 2 -
          z * ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (-(N : ℂ) ^ (1 - z) / (1 - z) - (1 / 2 : ℂ) * (N : ℂ) ^ (-z) -
          z * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))) := by
      have h1 := ((hpow1.sub_const ((N : ℂ) ^ (1 - z))).div_const (1 - z)).add
        ((hpow2.sub_const ((N : ℂ) ^ (-z))).div_const 2)
      have h2 := h1.sub (hint_lim.const_mul z)
      refine h2.trans_eq (congrArg 𝓝 ?_)
      ring
    have heq_tail := tendsto_nhds_unique hsum_tail (hrhs_lim.congr' (by
      filter_upwards [eventually_ge_atTop N] with M hNM; exact (hem M hNM).symm))
    dsimp only [L, R]
    linear_combination heq_tail
  have hev : L =ᶠ[𝓝 (2 : ℂ)] R := by
    have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with z hz
    exact h_gt_one hz
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an
    isPathConnected_re_gt_pos_sdiff_one.isConnected.isPreconnected ⟨by norm_num, by norm_num⟩ hev ⟨hs, hs1⟩

private lemma summable_one_div_nat_add_one_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-σ) := by
  have h := Real.summable_one_div_nat_rpow.mpr hσ
  refine (summable_nat_add_iff 1).mpr h |>.congr fun n ↦ ?_
  rw [one_div, Real.rpow_neg (by positivity), Nat.cast_add, Nat.cast_one]

private lemma tsum_nat_add_one_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) ≤ σ / (σ - 1) := by
  have hsumm := summable_one_div_nat_add_one_rpow hσ
  have hint : IntegrableOn (fun u : ℝ ↦ u ^ (-σ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hint_eval : ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ) = 1 / (σ - 1) := by
    have htend : Tendsto (fun R : ℝ ↦ ∫ u in (1 : ℝ)..R, u ^ (-σ)) atTop
        (𝓝 (∫ u in Set.Ioi (1 : ℝ), u ^ (-σ))) :=
      intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
    have hcalc : ∀ R : ℝ, 1 ≤ R →
        ∫ u in (1 : ℝ)..R, u ^ (-σ) = (1 - R ^ (1 - σ)) / (σ - 1) := by
      intro R hR
      rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
        rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
      simp only [Real.one_rpow]
      have hexp : -σ + 1 = 1 - σ := by ring
      rw [hexp]
      field_simp [show 1 - σ ≠ 0 by linarith]
      ring
    have hlim : Tendsto (fun R : ℝ ↦ (1 - R ^ (1 - σ)) / (σ - 1)) atTop (𝓝 (1 / (σ - 1))) := by
      have hr : Tendsto (fun R : ℝ ↦ R ^ (1 - σ)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)).congr fun R ↦ by
          rw [show -(σ - 1) = 1 - σ by ring]
      simpa using (tendsto_const_nhds (x := (1 : ℝ)).sub hr).div_const (σ - 1)
    exact tendsto_nhds_unique htend (hlim.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR; exact (hcalc R hR).symm))
  have hpart (N : ℕ) :
      ∑ n ∈ Finset.range (N + 1), ((n : ℝ) + 1) ^ (-σ) ≤
        1 + ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ) := by
    have hsplit : ∑ n ∈ Finset.range (N + 1), ((n : ℝ) + 1) ^ (-σ) =
        1 + ∑ n ∈ Finset.range N, ((n + 1 : ℝ) + 1) ^ (-σ) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      push_cast; ring_nf
    rw [hsplit]
    gcongr
    have hterm_le (n : ℕ) : ((n + 1 : ℝ) + 1) ^ (-σ) ≤
        ∫ u in ((n : ℝ) + 1)..((n : ℝ) + 2), u ^ (-σ) := by
      have hconst : ((n + 1 : ℝ) + 1) ^ (-σ) =
          ∫ _ in ((n : ℝ) + 1)..((n : ℝ) + 2), ((n + 1 : ℝ) + 1) ^ (-σ) := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hconst]
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const ?_ ?_
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
        exact hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (by linarith)))
      · intro u hu
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hu.1]) (by linarith [hu.2]) (by linarith)
    have hsum_int : ∑ n ∈ Finset.range N, ((n + 1 : ℝ) + 1) ^ (-σ) ≤
        ∫ u in (1 : ℝ)..((N : ℝ) + 1), u ^ (-σ) := by
      calc
        ∑ n ∈ Finset.range N, ((n + 1 : ℝ) + 1) ^ (-σ)
            ≤ ∑ n ∈ Finset.range N, ∫ u in ((n : ℝ) + 1)..((n : ℝ) + 2), u ^ (-σ) :=
          Finset.sum_le_sum fun n _ ↦ hterm_le n
        _ = ∫ u in (1 : ℝ)..((N : ℝ) + 1), u ^ (-σ) := by
          clear hterm_le hsplit
          induction N with
          | zero => simp
          | succ N ih =>
            rw [Finset.sum_range_succ, ih,
              show ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 by push_cast; ring]
            exact intervalIntegral.integral_add_adjacent_intervals
              ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
                (hint.mono_set Set.Ioc_subset_Ioi_self))
              ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
                (hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (by linarith)))))
    refine hsum_int.trans ?_
    rw [intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ N + 1)]
    exact setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 1 < u) ↦
        Real.rpow_nonneg (by linarith) _)
      (Filter.Eventually.of_forall fun _ hu ↦ hu.1)
  have hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), ((n : ℝ) + 1) ^ (-σ))
      atTop (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ))) :=
    hsumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hle : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) ≤ 1 + ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ) :=
    le_of_tendsto hlim (Eventually.of_forall hpart)
  rw [hint_eval] at hle
  have heq : 1 + 1 / (σ - 1) = σ / (σ - 1) := by
    field_simp [show σ - 1 ≠ 0 by linarith]
    ring
  linarith [hle, heq]

/-- Upper bound for `riemannZeta` in the half-plane `1 < σ`:
`‖riemannZeta (σ + t * I)‖ ≤ σ / (σ - 1)`. -/
theorem norm_riemannZeta_le_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ σ / (σ - 1) := by
  have hs : 1 < ((σ : ℂ) + (t : ℂ) * I).re := by simp [hσ]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hsumm_c : Summable fun n : ℕ ↦ ‖1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + (t : ℂ) * I)‖ := by
    refine summable_norm_iff.mpr ?_
    refine (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs) |>.congr
      fun n ↦ ?_
    simp [Nat.cast_add, Nat.cast_one]
  have hterm (n : ℕ) :
      ‖1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + (t : ℂ) * I)‖ = ((n : ℝ) + 1) ^ (-σ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [one_div, norm_inv, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
      Real.rpow_neg hn_pos.le]
    simp
  have h1 : ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + (t : ℂ) * I)‖ :=
    norm_tsum_le_tsum_norm hsumm_c
  have h2 : ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + (t : ℂ) * I)‖ =
      ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) :=
    tsum_congr hterm
  exact h1.trans (h2 ▸ tsum_nat_add_one_rpow_le hσ)

/-- Upper bound for `(riemannZeta (σ + t * I))⁻¹` in the half-plane `1 < σ`:
`‖riemannZeta (σ + t * I)‖⁻¹ ≤ σ / (σ - 1)`. -/
theorem inv_norm_riemannZeta_le_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖⁻¹ ≤ σ / (σ - 1) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s, hσ]
  have hmul := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hmul
  have hinv_eq := (eq_inv_of_mul_eq_one_right hmul).symm
  rw [← norm_inv, hinv_eq, LSeries]
  have hsumm_m : Summable fun n : ℕ ↦
      ‖LSeries.term (fun k : ℕ ↦ ((ArithmeticFunction.moebius k : ℤ) : ℂ)) s n‖ := by
    refine summable_norm_iff.mpr ?_
    exact (ArithmeticFunction.LSeriesSummable_moebius_iff (s := s)).mpr hs
  have hsumm_r : Summable fun n : ℕ ↦ if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
    have h := Real.summable_one_div_nat_rpow.mpr hσ
    refine h.congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : σ ≠ 0)]
    · simp [hn, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  have htsum_r : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) =
      ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) := by
    rw [Summable.tsum_eq_zero_add hsumm_r]
    simp only [↓reduceIte, zero_add]
    refine tsum_congr fun n ↦ ?_
    simp [Nat.cast_add, Nat.cast_one]
  calc
    ‖∑' n : ℕ, LSeries.term (fun k : ℕ ↦ ((ArithmeticFunction.moebius k : ℤ) : ℂ)) s n‖
        ≤ ∑' n : ℕ, ‖LSeries.term (fun k : ℕ ↦ ((ArithmeticFunction.moebius k : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsumm_m
    _ ≤ ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
      refine hsumm_m.tsum_le_tsum (fun n ↦ ?_) hsumm_r
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp only [LSeries.term_of_ne_zero hn, hn, ↓reduceIte, norm_div,
          Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
        have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
          have h1 : |ArithmeticFunction.moebius n| ≤ 1 := by
            simpa using ArithmeticFunction.abs_moebius_le_one (n := n)
          rw [Complex.norm_intCast]
          exact_mod_cast h1
        rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
        simpa [s] using mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hmu
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) := htsum_r
    _ ≤ σ / (σ - 1) := tsum_nat_add_one_rpow_le hσ

/-- Lower bound for `riemannZeta` in the half-plane `1 < σ`:
`(σ - 1) / σ ≤ ‖riemannZeta (σ + t * I)‖`. -/
theorem norm_riemannZeta_ge_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (σ - 1) / σ ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := by
  have hne : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp [hσ])
  have hpos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := norm_pos_iff.mpr hne
  have hinv := inv_norm_riemannZeta_le_of_one_lt_re hσ t
  have hinv_pos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖⁻¹ := inv_pos.mpr hpos
  calc
    (σ - 1) / σ = (σ / (σ - 1))⁻¹ := by
      field_simp [show σ ≠ 0 by linarith, show σ - 1 ≠ 0 by linarith]
    _ ≤ (‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖⁻¹)⁻¹ := inv_anti₀ hinv_pos hinv
    _ = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := inv_inv _

/-- Upper bound for `deriv riemannZeta` in the half-plane `1 < σ`:
`‖deriv riemannZeta (σ + t * I)‖ ≤ 2 * (σ + 1) / (σ - 1) ^ 2`. -/
theorem norm_deriv_riemannZeta_le_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2 * (σ + 1) / (σ - 1) ^ 2 := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s, hσ]
  have hev : riemannZeta =ᶠ[𝓝 s] LSeries 1 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have habs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact EReal.coe_lt_coe_iff.mpr hs
  rw [hev.deriv_eq, LSeries_deriv habs, norm_neg, LSeries]
  have hsumm_l : Summable fun n : ℕ ↦ ‖LSeries.term (LSeries.logMul 1) s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_logMul_of_lt_re habs)
  let σ' : ℝ := (σ + 1) / 2
  have hσ' : 1 < σ' := by dsimp only [σ']; linarith
  have hsumm_r : Summable fun n : ℕ ↦
      if n = 0 then (0 : ℝ) else (2 / (σ - 1)) * (n : ℝ) ^ (-σ') := by
    have h := (Real.summable_one_div_nat_rpow.mpr hσ').mul_left (2 / (σ - 1))
    refine h.congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : σ' ≠ 0)]
    · simp [hn, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  have htsum_r : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (2 / (σ - 1)) * (n : ℝ) ^ (-σ')) =
      (2 / (σ - 1)) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ') := by
    rw [Summable.tsum_eq_zero_add hsumm_r]
    simp only [↓reduceIte, zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, tsum_mul_left]
    congr 1
    refine tsum_congr fun n ↦ ?_
    simp [Nat.cast_add, Nat.cast_one]
  calc
    ‖∑' n : ℕ, LSeries.term (LSeries.logMul 1) s n‖
        ≤ ∑' n : ℕ, ‖LSeries.term (LSeries.logMul 1) s n‖ :=
      norm_tsum_le_tsum_norm hsumm_l
    _ ≤ ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (2 / (σ - 1)) * (n : ℝ) ^ (-σ')) := by
      refine hsumm_l.tsum_le_tsum (fun n ↦ ?_) hsumm_r
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
        simp only [LSeries.term_of_ne_zero hn, LSeries.logMul, Pi.one_apply, mul_one, hn,
          ↓reduceIte, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
        have hlog_eq : ‖Complex.log (n : ℂ)‖ = Real.log n := by
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le, Complex.norm_real,
            Real.norm_of_nonneg (Real.log_nonneg hn1)]
        have hlog_bd : Real.log n ≤ (2 / (σ - 1)) * (n : ℝ) ^ ((σ - 1) / 2) := by
          have h1 : Real.log ((n : ℝ) ^ ((σ - 1) / 2)) ≤ (n : ℝ) ^ ((σ - 1) / 2) - 1 :=
            Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos _)
          rw [Real.log_rpow hn_pos] at h1
          have h2 : ((σ - 1) / 2) * Real.log n ≤ (n : ℝ) ^ ((σ - 1) / 2) := by linarith
          calc
            Real.log n = (2 / (σ - 1)) * (((σ - 1) / 2) * Real.log n) := by
              field_simp [show σ - 1 ≠ 0 by linarith]
            _ ≤ (2 / (σ - 1)) * (n : ℝ) ^ ((σ - 1) / 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        have hexp : ((σ - 1) / 2) - σ = -σ' := by dsimp only [σ']; ring
        rw [hlog_eq, show s.re = σ by simp [s], div_eq_mul_inv,
          ← Real.rpow_neg hn_pos.le]
        calc
          Real.log n * (n : ℝ) ^ (-σ)
              ≤ ((2 / (σ - 1)) * (n : ℝ) ^ ((σ - 1) / 2)) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hlog_bd (Real.rpow_nonneg hn_pos.le _)
          _ = (2 / (σ - 1)) * ((n : ℝ) ^ ((σ - 1) / 2) * (n : ℝ) ^ (-σ)) := by ring
          _ = (2 / (σ - 1)) * (n : ℝ) ^ (((σ - 1) / 2) + -σ) := by
            rw [← Real.rpow_add hn_pos]
          _ = (2 / (σ - 1)) * (n : ℝ) ^ (-σ') := by rw [← sub_eq_add_neg, hexp]
    _ = (2 / (σ - 1)) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ') := htsum_r
    _ ≤ (2 / (σ - 1)) * (σ' / (σ' - 1)) := by
      gcongr
      exact tsum_nat_add_one_rpow_le hσ'
    _ = 2 * (σ + 1) / (σ - 1) ^ 2 := by
      dsimp only [σ']
      rw [div_mul_div_comm,
        div_eq_div_iff (mul_ne_zero (by linarith) (by linarith)) (pow_ne_zero 2 (by linarith))]
      ring

private lemma harmonic_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    (harmonic N : ℝ) ≤ 1 + Real.log N := by
  have hsplit (M : ℕ) (hM : 1 ≤ M) :
      (harmonic M : ℝ) = 1 + ∑ n ∈ Finset.Icc 2 M, (1 / (n : ℝ)) := by
    induction M with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hM with hk1 | hk_gt
      · have hk0 : k = 0 := by omega
        subst hk0; simp
      · have hk1' : 1 ≤ k := by omega
        rw [harmonic_succ, Rat.cast_add, ih hk1']
        have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        push_cast
        simp only [one_div]
        ring
  rw [hsplit N hN]
  gcongr
  have hterm (n : ℕ) (hn : 2 ≤ n) : 1 / (n : ℝ) ≤ ∫ u in ((n : ℝ) - 1)..(n : ℝ), 1 / u := by
    have hn_pos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hconst : 1 / (n : ℝ) = ∫ _ in ((n : ℝ) - 1)..(n : ℝ), 1 / (n : ℝ) := by
      simp [intervalIntegral.integral_const]
    rw [hconst]
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const ?_ ?_
    · exact intervalIntegral.intervalIntegrable_one_div (fun u hu ↦ by
        rw [Set.uIcc_of_le (by linarith)] at hu; linarith [hu.1]) (by fun_prop)
    · intro u hu
      exact one_div_le_one_div_of_le (lt_of_lt_of_le hn_pos hu.1) hu.2
  have hsum_le : ∑ n ∈ Finset.Icc 2 N, (1 / (n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 2 N, ∫ u in ((n : ℝ) - 1)..(n : ℝ), 1 / u :=
    Finset.sum_le_sum fun n hn ↦ hterm n (Finset.mem_Icc.mp hn).1
  have htele (M : ℕ) (hM : 1 ≤ M) : ∑ n ∈ Finset.Icc 2 M, ∫ u in ((n : ℝ) - 1)..(n : ℝ), 1 / u =
      ∫ u in (1 : ℝ)..(M : ℝ), 1 / u := by
    induction M with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hM with hk1 | hk_gt
      · have hk0 : k = 0 := by omega
        subst hk0; simp
      · have hk1' : 1 ≤ k := by omega
        have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih hk1', Nat.cast_add, Nat.cast_one,
          show ((k : ℝ) + 1) - 1 = k by ring, add_comm]
        exact intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegral.intervalIntegrable_one_div (fun u hu ↦ by
            rw [Set.uIcc_of_le (Nat.one_le_cast.mpr hk1')] at hu; linarith [hu.1]) (by fun_prop))
          (intervalIntegral.intervalIntegrable_one_div (fun u hu ↦ by
            rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ k + 1)] at hu
            have hk1r : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk1'
            linarith [hu.1]) (by fun_prop))
  have hint_log : ∫ u in (1 : ℝ)..(N : ℝ), 1 / u = Real.log N := by
    rw [integral_one_div_of_pos zero_lt_one (Nat.cast_pos.mpr hN), div_one]
  exact hsum_le.trans_eq ((htele N hN).trans hint_log)

/-- Logarithmic upper bound on `riemannZeta` for `1 ≤ σ` and `2 ≤ |t|`:
`‖riemannZeta (σ + t * I)‖ ≤ C * Real.log (|t| + 2)`. -/
theorem norm_riemannZeta_re_ge_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, 1 ≤ σ → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + 2) := by
  refine ⟨6, by norm_num, fun σ t hσ ht ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  rcases le_or_gt σ 2 with hσ2 | hσ2
  · let N : ℕ := Nat.floor |t|
    have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast ht)
    have hN1 : 1 ≤ N := by omega
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
    have hN_le : (N : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    have ht_lt : |t| < (N : ℝ) + 1 := Nat.lt_floor_add_one |t|
    have hN_half : |t| / 2 ≤ N := by
      have hN_ge2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      linarith
    have hs0 : 0 < s.re := by simp [s]; linarith
    have hs1 : s ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp [s] at him
      rw [him, abs_zero] at ht
      linarith
    rw [show (σ : ℂ) + (t : ℂ) * I = s from rfl, riemannZeta_eulerMaclaurin_N hN1 hs0 hs1]
    have hsum_bd : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + Real.log |t| := by
      calc
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
            ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := by
          refine Finset.sum_congr rfl fun n hn ↦ ?_
          have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
          rw [Complex.norm_natCast_cpow_of_pos hn0]
          simp [s]
        _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          rw [one_div, ← Real.rpow_neg_one (n : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (harmonic N : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          simp only [one_div]
        _ ≤ 1 + Real.log N := harmonic_le_one_add_log N hN1
        _ ≤ 1 + Real.log |t| := by gcongr
    have h1s_norm : |t| ≤ ‖1 - s‖ := by
      have him : (1 - s).im = -t := by simp [s]
      calc
        |t| = |(-t)| := (abs_neg t).symm
        _ = |(1 - s).im| := by rw [him]
        _ ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
    have hterm2_bd : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_natCast_cpow_of_pos hN1]
      have hre : (1 - s).re = 1 - σ := by simp [s]
      have hpow : (N : ℝ) ^ (1 - s).re ≤ 1 := by
        rw [hre]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
      calc
        (N : ℝ) ^ (1 - s).re / ‖1 - s‖ ≤ 1 / |t| := div_le_div₀ zero_le_one hpow (by linarith) h1s_norm
        _ ≤ 1 / 2 := div_le_div_of_nonneg_left zero_le_one two_pos ht
    have hterm3_bd : ‖(1 / 2 : ℂ) * (N : ℂ) ^ (-s)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN1]
      have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      have hpow : (N : ℝ) ^ (-s).re ≤ 1 / 2 := by
        have hre : (-s).re = -σ := by simp [s]
        rw [hre]
        have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
        rw [Real.rpow_neg_one] at h1
        have hN_ge2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
        have hinv2 : (N : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ two_pos hN_ge2
        exact h1.trans (by simpa [one_div] using hinv2)
      rw [hhalf]
      linarith
    have hint_bd : ‖s * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ 2 := by
      have hs_norm : ‖s‖ ≤ 2 * |t| := by
        calc
          ‖s‖ = ‖(σ : ℂ) + (t : ℂ) * I‖ := rfl
          _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = σ + |t| := by simp [abs_of_nonneg (by linarith : 0 ≤ σ)]
          _ ≤ 2 * |t| := by linarith
      have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-σ - 1)) (Set.Ioi (N : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (1 / 2)
      have hint_rpow : ∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) =
          1 / (2 * σ * (N : ℝ) ^ σ) := by
        rw [integral_const_mul]
        have htend : Tendsto (fun R : ℝ ↦ ∫ u in (N : ℝ)..R, u ^ (-σ - 1)) atTop
            (𝓝 (∫ u in Set.Ioi (N : ℝ), u ^ (-σ - 1))) :=
          intervalIntegral_tendsto_integral_Ioi N
            (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos) tendsto_id
        have hcalc : ∀ R : ℝ, (N : ℝ) ≤ R →
            ∫ u in (N : ℝ)..R, u ^ (-σ - 1) =
              ((N : ℝ) ^ (-σ) - R ^ (-σ)) / σ := by
          intro R hR
          rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
            rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
          have hexp : -σ - 1 + 1 = -σ := by ring
          rw [hexp]
          field_simp [show σ ≠ 0 by linarith]
          ring
        have hlim : Tendsto (fun R : ℝ ↦ ((N : ℝ) ^ (-σ) - R ^ (-σ)) / σ)
            atTop (𝓝 ((N : ℝ) ^ (-σ) / σ)) := by
          have hr : Tendsto (fun R : ℝ ↦ R ^ (-σ)) atTop (𝓝 0) :=
            tendsto_rpow_neg_atTop (by linarith)
          simpa using (tendsto_const_nhds.sub hr).div_const σ
        have heq := tendsto_nhds_unique htend (hlim.congr' (by
          filter_upwards [eventually_ge_atTop (N : ℝ)] with R hR; exact (hcalc R hR).symm))
        rw [heq, Real.rpow_neg hN_pos.le]
        ring
      have h_int := integrableOn_sawtooth_cpow_Ioi' hN_pos hs0
      have hre_exp : (-s - 1).re = -σ - 1 := by simp [s]
      have hint_norm : ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤
          1 / (2 * σ * (N : ℝ) ^ σ) := by
        calc
          ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖
              ≤ ∫ u in Set.Ioi (N : ℝ), ‖(sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
            norm_integral_le_integral_norm _
          _ ≤ ∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) := by
            refine setIntegral_mono_on h_int.norm hdom measurableSet_Ioi fun u hu ↦ ?_
            have hu_pos : 0 < u := lt_trans hN_pos hu
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, hre_exp]
            exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)
          _ = 1 / (2 * σ * (N : ℝ) ^ σ) := hint_rpow
      have hden_ge : |t| / 2 ≤ σ * (N : ℝ) ^ σ := by
        have hpow_ge : (N : ℝ) ≤ (N : ℝ) ^ σ := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1 : (1 : ℝ) ≤ N) hσ
        calc
          |t| / 2 ≤ N := hN_half
          _ = 1 * N := (one_mul _).symm
          _ ≤ σ * (N : ℝ) ^ σ := mul_le_mul hσ hpow_ge hN_pos.le (by linarith)
      rw [norm_mul]
      calc
        ‖s‖ * ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖
            ≤ (2 * |t|) * (1 / (2 * (|t| / 2))) := by
          refine mul_le_mul hs_norm ?_ (norm_nonneg _) (by positivity)
          refine hint_norm.trans (one_div_le_one_div_of_le (by linarith [ht]) ?_)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hden_ge zero_le_two
        _ = 2 := by
          have ht_ne : |t| ≠ 0 := by linarith
          field_simp [ht_ne]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have htri1 := norm_sub_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) -
      (1 / 2 : ℂ) * (N : ℂ) ^ (-s))
      (s * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1))
    have htri2 := norm_sub_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s))
      ((1 / 2 : ℂ) * (N : ℂ) ^ (-s))
    have htri3 := norm_sub_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
      ((N : ℂ) ^ (1 - s) / (1 - s))
    calc
      ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) -
          (1 / 2 : ℂ) * (N : ℂ) ^ (-s) -
          s * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖
          ≤ (1 + Real.log |t|) + 1 / 2 + 1 / 4 + 2 := by linarith
      _ ≤ Real.log (|t| + 2) + 4 := by linarith
      _ ≤ Real.log (|t| + 2) + 4 * Real.log (|t| + 2) := by
        have h4 : (4 : ℝ) ≤ 4 * Real.log (|t| + 2) := by linarith
        linarith
      _ ≤ 6 * Real.log (|t| + 2) := by linarith
  · have hbd := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < σ) t
    have h2 : σ / (σ - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2 := hbd.trans h2
      _ ≤ 6 * 1 := by norm_num
      _ ≤ 6 * Real.log (|t| + 2) := by gcongr

/-- Logarithmic upper bound on the vertical line `Re s = 1`:
`‖riemannZeta (1 + t * I)‖ ≤ C * Real.log (|t| + 2)` for `2 ≤ |t|`. -/
theorem norm_riemannZeta_one_add_mul_I_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃t : ℝ⦄, 2 ≤ |t| →
      ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, hbd⟩ := norm_riemannZeta_re_ge_one_le
  exact ⟨C, hC, fun t ht ↦ by simpa using hbd le_rfl ht⟩

private lemma integral_log_div_sq_Ioi {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun u : ℝ ↦ Real.log u / u ^ 2) (Set.Ioi a) ∧
      ∫ u in Set.Ioi a, Real.log u / u ^ 2 = (Real.log a + 1) / a := by
  have ha_pos : 0 < a := by linarith
  let g : ℝ → ℝ := fun u ↦ -(Real.log u + 1) / u
  have hderiv : ∀ u ∈ Set.Ici a, HasDerivAt g (Real.log u / u ^ 2) u := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le ha_pos hu
    have hnum : HasDerivAt (fun x : ℝ ↦ -(Real.log x + 1)) (-u⁻¹) u := by
      exact ((Real.hasDerivAt_log hu_pos.ne').add_const 1).neg
    have hdiv := hnum.fun_div (hasDerivAt_id u) hu_pos.ne'
    convert hdiv using 1
    dsimp
    simp only [id_eq]
    field_simp [hu_pos.ne']
    ring
  have hg_pos : ∀ u ∈ Set.Ioi a, 0 ≤ Real.log u / u ^ 2 := by
    intro u hu
    have hu1 : 1 ≤ u := le_trans ha (le_of_lt hu)
    exact div_nonneg (Real.log_nonneg hu1) (sq_nonneg u)
  have htend : Tendsto g atTop (𝓝 0) := by
    have hlim0 : Tendsto (fun u : ℝ ↦ 3 / Real.sqrt u) atTop (𝓝 0) := by
      have hsq : Tendsto Real.sqrt atTop atTop := tendsto_atTop_atTop.mpr fun b ↦
        ⟨(max b 0) ^ 2, fun x hx ↦ by
          have := Real.sqrt_le_sqrt hx
          rw [Real.sqrt_sq (le_max_right _ _)] at this
          exact (le_max_left b 0).trans this⟩
      simpa [div_eq_mul_inv] using hsq.inv_tendsto_atTop.const_mul (3 : ℝ)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim0
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu_pos : 0 < u := by linarith
    have hlog : Real.log u ≤ 2 * Real.sqrt u := by
      have h1 : Real.log (u ^ (1 / 2 : ℝ)) ≤ u ^ (1 / 2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu_pos _)
      rw [Real.log_rpow hu_pos, ← Real.sqrt_eq_rpow] at h1
      linarith
    have h1 : 1 ≤ Real.sqrt u := by simpa using Real.sqrt_le_sqrt hu
    rw [Real.norm_eq_abs, show g u = -(Real.log u + 1) / u from rfl, abs_div, abs_neg,
      abs_of_nonneg (by linarith [Real.log_nonneg hu]), abs_of_pos hu_pos]
    calc
      (Real.log u + 1) / u ≤ (2 * Real.sqrt u + Real.sqrt u) / u := by gcongr
      _ = 3 / Real.sqrt u := by
        rw [div_eq_div_iff hu_pos.ne' (Real.sqrt_pos.mpr hu_pos).ne']
        linear_combination 3 * (Real.mul_self_sqrt hu_pos.le)
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hg_pos htend
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  simp [g]
  ring

/-- Logarithmic derivative-squared bound on `deriv riemannZeta` for `1 ≤ σ` and `2 ≤ |t|`:
`‖deriv riemannZeta (σ + t * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2`. -/
theorem norm_deriv_riemannZeta_re_ge_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, 1 ≤ σ → 2 ≤ |t| →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  refine ⟨16, by norm_num, fun σ t hσ ht ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  rcases le_or_gt σ 2 with hσ2 | hσ2
  · let N : ℕ := Nat.floor |t|
    have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast ht)
    have hN1 : 1 ≤ N := by omega
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
    have hN_ge1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN1
    have hN_le : (N : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    have ht_lt : |t| < (N : ℝ) + 1 := Nat.lt_floor_add_one |t|
    have hN_half : |t| / 2 ≤ N := by
      have hN_ge2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      linarith
    have hs0 : 0 < s.re := by simp [s]; linarith
    have hs1 : s ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp [s] at him
      rw [him, abs_zero] at ht
      linarith
    let R : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z) -
      (N : ℂ) ^ (1 - z) / (1 - z) - (1 / 2 : ℂ) * (N : ℂ) ^ (-z) -
      z * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1)
    have hev : riemannZeta =ᶠ[𝓝 s] R := by
      have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
        (isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (0 : ℝ) < z.re}).inter
          (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})
      filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
      exact riemannZeta_eulerMaclaurin_N hN1 hz.1 hz.2
    have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd_sum : HasDerivAt (fun z : ℂ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
        (∑ n ∈ Finset.Icc 1 N, -(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)) s := by
      have hterm : ∀ n ∈ Finset.Icc 1 N, HasDerivAt (fun z : ℂ ↦ (n : ℂ) ^ (-z))
          (-(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)) s := by
        intro n hn
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp only [Finset.mem_Icc] at hn; omega)
        have hd := (hasDerivAt_neg s).const_cpow (Or.inl hn0)
        convert hd using 1
        ring
      exact HasDerivAt.fun_sum hterm
    have hd_term2 : HasDerivAt (fun z : ℂ ↦ (N : ℂ) ^ (1 - z) / (1 - z))
        ((-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) * (1 - s) -
          (N : ℂ) ^ (1 - s) * (-1)) / (1 - s) ^ 2) s := by
      have h1sub : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1 : ℂ) s := by
        simpa using (hasDerivAt_const s (1 : ℂ)).fun_sub (hasDerivAt_id s)
      have hnum : HasDerivAt (fun z : ℂ ↦ (N : ℂ) ^ (1 - z))
          (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s)) s := by
        have hd := h1sub.const_cpow (Or.inl hN_ne)
        convert hd using 1
        ring
      exact hnum.div h1sub (sub_ne_zero.mpr hs1.symm)
    have hd_term3 : HasDerivAt (fun z : ℂ ↦ (1 / 2 : ℂ) * (N : ℂ) ^ (-z))
        ((1 / 2 : ℂ) * (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (-s))) s := by
      have hd := (hasDerivAt_neg s).const_cpow (Or.inl hN_ne)
      exact (hd.congr_deriv (by ring)).const_mul _
    have hd_term4 : HasDerivAt
        (fun z : ℂ ↦ z * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))
        (1 * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)) +
          s * (-∫ u in Set.Ioi (N : ℝ),
            (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1))) s :=
      (hasDerivAt_id s).mul (mellin_sawtooth_hasDerivAt hN1 hs0)
    have hdR : HasDerivAt R _ s := ((hd_sum.sub hd_term2).sub hd_term3).sub hd_term4
    rw [show (σ : ℂ) + (t : ℂ) * I = s from rfl, hev.deriv_eq, hdR.deriv]
    have hlogN : Real.log N ≤ Real.log |t| := Real.log_le_log hN_pos (by linarith)
    have h1_bd : ‖∑ n ∈ Finset.Icc 1 N, -(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)‖ ≤
        Real.log |t| * (1 + Real.log |t|) := by
      calc
        ‖∑ n ∈ Finset.Icc 1 N, -(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)‖
            ≤ ∑ n ∈ Finset.Icc 1 N, ‖-(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log N * (1 / (n : ℝ)) := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn1r : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn1
          have hn_pos : (0 : ℝ) < n := by linarith
          rw [norm_mul, norm_neg, Complex.norm_natCast_cpow_of_pos hn1,
            ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le, Complex.norm_real,
            Real.norm_of_nonneg (Real.log_nonneg hn1r)]
          have hlog_le : Real.log n ≤ Real.log N := Real.log_le_log hn_pos (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
          have hpow_le : (n : ℝ) ^ (-s).re ≤ 1 / (n : ℝ) := by
            have hre : (-s).re = -σ := by simp [s]
            rw [hre, one_div, ← Real.rpow_neg_one (n : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le hn1r (by linarith)
          exact mul_le_mul hlog_le hpow_le (by positivity) (Real.log_nonneg hN_ge1)
        _ = Real.log N * (harmonic N : ℝ) := by
          rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
          push_cast
          simp only [one_div]
        _ ≤ Real.log |t| * (1 + Real.log N) := by
          have hharm_nn : 0 ≤ (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            push_cast
            positivity
          exact mul_le_mul hlogN (harmonic_le_one_add_log N hN1) hharm_nn
            (Real.log_nonneg (by linarith))
        _ ≤ Real.log |t| * (1 + Real.log |t|) := by
          gcongr
          exact Real.log_nonneg (by linarith)
    have h1s_norm : |t| ≤ ‖1 - s‖ := by
      have him : (1 - s).im = -t := by simp [s]
      calc |t| = |(-t)| := (abs_neg t).symm
        _ = |(1 - s).im| := by rw [him]
        _ ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
    have hlogN_norm : ‖Complex.log (N : ℂ)‖ = Real.log N := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hN_pos.le, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg hN_ge1)]
    have h2_bd : ‖(-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) * (1 - s) -
        (N : ℂ) ^ (1 - s) * (-1)) / (1 - s) ^ 2‖ ≤ 2 * Real.log (|t| + 2) := by
      have hpow1 : ‖(N : ℂ) ^ (1 - s)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hN1]
        have hre : (1 - s).re = 1 - σ := by simp [s]
        rw [hre]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN_ge1 (by linarith)
      have heq_split : (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) * (1 - s) -
          (N : ℂ) ^ (1 - s) * (-1)) / (1 - s) ^ 2 =
          -(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) / (1 - s) +
            (N : ℂ) ^ (1 - s) / (1 - s) ^ 2 := by
        field_simp [sub_ne_zero.mpr hs1.symm]
        ring
      rw [heq_split]
      have hA : ‖-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ Real.log |t| := by
        rw [norm_div, norm_mul, norm_neg, hlogN_norm]
        calc
          Real.log N * ‖(N : ℂ) ^ (1 - s)‖ / ‖1 - s‖ ≤ Real.log |t| * 1 / |t| := by
            refine div_le_div₀ (mul_nonneg (Real.log_nonneg (by linarith)) zero_le_one)
              (mul_le_mul hlogN hpow1 (norm_nonneg _) (Real.log_nonneg (by linarith)))
              (by linarith [ht]) h1s_norm
          _ ≤ Real.log |t| := by
            rw [mul_one]
            exact div_le_self (Real.log_nonneg (by linarith)) (by linarith)
      have hB : ‖(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ ≤ 1 := by
        rw [norm_div, norm_pow]
        have hsq : 4 ≤ ‖1 - s‖ ^ 2 := by nlinarith
        calc
          ‖(N : ℂ) ^ (1 - s)‖ / ‖1 - s‖ ^ 2 ≤ 1 / 4 :=
            div_le_div₀ zero_le_one hpow1 (by norm_num) hsq
          _ ≤ 1 := by norm_num
      have hlog_le : Real.log |t| ≤ Real.log (|t| + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      calc
        ‖-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) / (1 - s) + (N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖
            ≤ ‖-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
                ‖(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ := norm_add_le _ _
        _ ≤ Real.log |t| + 1 := add_le_add hA hB
        _ ≤ Real.log (|t| + 2) + Real.log (|t| + 2) := add_le_add hlog_le hlog_ge_one
        _ = 2 * Real.log (|t| + 2) := by ring
    have h3_bd : ‖(1 / 2 : ℂ) * (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (-s))‖ ≤ Real.log (|t| + 2) := by
      have hpow0 : ‖(N : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hN1]
        have hre : (-s).re = -σ := by simp [s]
        rw [hre]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN_ge1 (by linarith)
      rw [norm_mul, norm_mul, norm_neg, hlogN_norm]
      have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [hhalf]
      have hlog_le : Real.log N ≤ Real.log (|t| + 2) := Real.log_le_log hN_pos (by linarith)
      calc
        1 / 2 * (Real.log N * ‖(N : ℂ) ^ (-s)‖) ≤ 1 / 2 * (Real.log (|t| + 2) * 1) := by
          gcongr
        _ ≤ Real.log (|t| + 2) := by linarith
    have hre_exp : (-s - 1).re = -σ - 1 := by simp [s]
    have h4a_bd : ‖1 * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ 1 := by
      rw [one_mul]
      have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-2 : ℝ)) (Set.Ioi (N : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hN_pos).const_mul (1 / 2)
      have hint_rpow : ∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℝ) * u ^ (-2 : ℝ) = 1 / (2 * N) := by
        rw [integral_const_mul]
        have htend : Tendsto (fun R : ℝ ↦ ∫ u in (N : ℝ)..R, u ^ (-2 : ℝ)) atTop
            (𝓝 (∫ u in Set.Ioi (N : ℝ), u ^ (-2 : ℝ))) :=
          intervalIntegral_tendsto_integral_Ioi N
            (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hN_pos) tendsto_id
        have hcalc : ∀ R : ℝ, (N : ℝ) ≤ R →
            ∫ u in (N : ℝ)..R, u ^ (-2 : ℝ) = (N : ℝ)⁻¹ - R⁻¹ := by
          intro R hR
          rw [integral_rpow (Or.inr ⟨by norm_num, fun h ↦ by
            rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
          simp only [show (-2 : ℝ) + 1 = -1 by norm_num, div_neg, div_one, Real.rpow_neg_one]
          ring
        have hlim : Tendsto (fun R : ℝ ↦ (N : ℝ)⁻¹ - R⁻¹) atTop (𝓝 (N : ℝ)⁻¹) := by
          simpa using (tendsto_const_nhds (x := (N : ℝ)⁻¹)).sub tendsto_inv_atTop_zero
        rw [tendsto_nhds_unique htend (hlim.congr' (by
          filter_upwards [eventually_ge_atTop (N : ℝ)] with R hR; exact (hcalc R hR).symm))]
        ring
      have h_int := integrableOn_sawtooth_cpow_Ioi' hN_pos hs0
      calc
        ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖
            ≤ ∫ u in Set.Ioi (N : ℝ), ‖(sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℝ) * u ^ (-2 : ℝ) := by
          refine setIntegral_mono_on h_int.norm hdom measurableSet_Ioi fun u hu ↦ ?_
          have hu_pos : 0 < u := lt_trans hN_pos hu
          have hu1 : 1 ≤ u := hN_ge1.trans hu.le
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, hre_exp]
          exact mul_le_mul (sawtooth_abs_le u)
            (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)) (by positivity) (by positivity)
        _ = 1 / (2 * N) := hint_rpow
        _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
    have h4b_bd :
        ‖s * (-∫ u in Set.Ioi (N : ℝ),
          (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1))‖ ≤
          4 * Real.log (|t| + 2) := by
      have hs_norm : ‖s‖ ≤ 2 * |t| := by
        calc
          ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = σ + |t| := by simp [abs_of_nonneg (by linarith : 0 ≤ σ)]
          _ ≤ 2 * |t| := by linarith
      obtain ⟨hint_log, heval_log⟩ := integral_log_div_sq_Ioi hN_ge1
      have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * (Real.log u / u ^ 2)) (Set.Ioi (N : ℝ)) :=
        hint_log.const_mul (1 / 2)
      have h_int : IntegrableOn
          (fun u : ℝ ↦ (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1))
          (Set.Ioi (N : ℝ)) := by
        refine Integrable.mono' hdom ?_ ?_
        · have h1 : AEStronglyMeasurable (fun u : ℝ ↦ (sawtooth u : ℂ))
              (volume.restrict (Set.Ioi (N : ℝ))) :=
            (Complex.continuous_ofReal.measurable.comp
              (measurable_fract.sub_const _)).aestronglyMeasurable.mono_measure
              Measure.restrict_le_self
          have h2 : ContinuousOn (fun u : ℝ ↦ (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1))
              (Set.Ioi (N : ℝ)) := by
            refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
            have hu_pos : 0 < u := lt_trans hN_pos hu
            exact ((Complex.continuous_ofReal.continuousAt.comp
              (Real.continuousAt_log hu_pos.ne')).mul
              (cpow_ofReal_hasDerivAt' hu_pos (-s - 1)).continuousAt)
          have heq : (fun u : ℝ ↦ (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)) =
              fun u : ℝ ↦ (sawtooth u : ℂ) * ((Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
            ext u; ring
          rw [heq]
          exact h1.mul (h2.aestronglyMeasurable measurableSet_Ioi)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          have hu_pos : 0 < u := lt_trans hN_pos hu
          have hu1 : 1 ≤ u := hN_ge1.trans hu.le
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hu1),
            Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, hre_exp]
          have hpow : u ^ (-σ - 1) ≤ (u ^ 2)⁻¹ := by
            rw [← Real.rpow_natCast u 2, ← Real.rpow_neg hu_pos.le]
            exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num; linarith)
          rw [div_eq_mul_inv]
          calc
            |sawtooth u| * Real.log u * u ^ (-σ - 1)
                ≤ (1 / 2) * Real.log u * (u ^ 2)⁻¹ :=
              mul_le_mul (mul_le_mul_of_nonneg_right (sawtooth_abs_le u) (Real.log_nonneg hu1))
                hpow (Real.rpow_nonneg hu_pos.le _) (mul_nonneg (by norm_num) (Real.log_nonneg hu1))
            _ = 1 / 2 * (Real.log u * (u ^ 2)⁻¹) := by ring
      have hint_norm :
          ‖-∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤
            (Real.log N + 1) / (2 * N) := by
        rw [norm_neg]
        calc
          ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)‖
              ≤ ∫ u in Set.Ioi (N : ℝ), ‖(sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
            norm_integral_le_integral_norm _
          _ ≤ ∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℝ) * (Real.log u / u ^ 2) := by
            refine setIntegral_mono_on h_int.norm hdom measurableSet_Ioi fun u hu ↦ ?_
            have hu_pos : 0 < u := lt_trans hN_pos hu
            have hu1 : 1 ≤ u := hN_ge1.trans hu.le
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hu1),
              Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, hre_exp]
            have hpow : u ^ (-σ - 1) ≤ (u ^ 2)⁻¹ := by
              rw [← Real.rpow_natCast u 2, ← Real.rpow_neg hu_pos.le]
              exact Real.rpow_le_rpow_of_exponent_le hu1 (by push_cast; linarith)
            rw [div_eq_mul_inv]
            calc
              |sawtooth u| * Real.log u * u ^ (-σ - 1)
                  ≤ (1 / 2) * Real.log u * (u ^ 2)⁻¹ :=
                mul_le_mul (mul_le_mul_of_nonneg_right (sawtooth_abs_le u) (Real.log_nonneg hu1))
                  hpow (Real.rpow_nonneg hu_pos.le _) (mul_nonneg (by norm_num) (Real.log_nonneg hu1))
              _ = 1 / 2 * (Real.log u * (u ^ 2)⁻¹) := by ring
          _ = (Real.log N + 1) / (2 * N) := by
            rw [integral_const_mul, heval_log]
            ring
      rw [norm_mul]
      calc
        ‖s‖ * ‖-∫ u in Set.Ioi (N : ℝ),
            (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)‖
            ≤ (2 * |t|) * ((Real.log N + 1) / (2 * (|t| / 2))) := by
          refine mul_le_mul hs_norm ?_ (norm_nonneg _) (by positivity)
          exact hint_norm.trans (div_le_div_of_nonneg_left
            (add_nonneg (Real.log_nonneg hN_ge1) zero_le_one) (by linarith [ht])
            (by linarith [hN_half]))
        _ = 2 * (Real.log N + 1) := by
          have ht_ne : |t| ≠ 0 := by linarith
          field_simp [ht_ne]
        _ ≤ 2 * (Real.log (|t| + 2) + Real.log (|t| + 2)) := by
          have hlog_N : Real.log N ≤ Real.log (|t| + 2) := Real.log_le_log hN_pos (by linarith)
          linarith
        _ = 4 * Real.log (|t| + 2) := by ring
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h1_bd' : Real.log |t| * (1 + Real.log |t|) ≤ 2 * (Real.log (|t| + 2)) ^ 2 := by
      calc
        Real.log |t| * (1 + Real.log |t|)
            ≤ Real.log (|t| + 2) * (Real.log (|t| + 2) + Real.log (|t| + 2)) :=
          mul_le_mul hlog_le (by linarith)
            (add_nonneg zero_le_one (Real.log_nonneg (by linarith)))
            (Real.log_nonneg (by linarith))
        _ = 2 * (Real.log (|t| + 2)) ^ 2 := by ring
    have hlog_sq : Real.log (|t| + 2) ≤ (Real.log (|t| + 2)) ^ 2 := by
      simpa [sq] using mul_le_mul_of_nonneg_left hlog_ge_one (by linarith : 0 ≤ Real.log (|t| + 2))
    have h1_sq : (1 : ℝ) ≤ (Real.log (|t| + 2)) ^ 2 := by nlinarith
    have htri1 := norm_sub_le ((∑ n ∈ Finset.Icc 1 N, -(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)) -
      (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) * (1 - s) - (N : ℂ) ^ (1 - s) * (-1)) / (1 - s) ^ 2 -
      (1 / 2 : ℂ) * (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (-s)))
      (1 * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)) +
        s * (-∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)))
    have htri2 := norm_sub_le ((∑ n ∈ Finset.Icc 1 N, -(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s)) -
      (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) * (1 - s) - (N : ℂ) ^ (1 - s) * (-1)) / (1 - s) ^ 2)
      ((1 / 2 : ℂ) * (-(Complex.log (N : ℂ)) * (N : ℂ) ^ (-s)))
    have htri3 := norm_sub_le (∑ n ∈ Finset.Icc 1 N, -(Complex.log (n : ℂ)) * (n : ℂ) ^ (-s))
      ((-(Complex.log (N : ℂ)) * (N : ℂ) ^ (1 - s) * (1 - s) - (N : ℂ) ^ (1 - s) * (-1)) / (1 - s) ^ 2)
    have htri4 := norm_add_le
      (1 * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1))
      (s * (-∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (Real.log u : ℂ) * (u : ℂ) ^ (-s - 1)))
    linarith
  · have hbd := norm_deriv_riemannZeta_le_of_one_lt_re (by linarith : 1 < σ) t
    have h6 : 2 * (σ + 1) / (σ - 1) ^ 2 ≤ 6 := by
      rw [div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < σ - 1))]
      nlinarith
    have h1_sq : (1 : ℝ) ≤ (Real.log (|t| + 2)) ^ 2 := by nlinarith
    calc
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 6 := hbd.trans h6
      _ ≤ 16 * 1 := by norm_num
      _ ≤ 16 * (Real.log (|t| + 2)) ^ 2 := by gcongr

/-- Logarithmic squared upper bound on `deriv riemannZeta` on the vertical line `Re s = 1`:
`‖deriv riemannZeta (1 + t * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2` for `2 ≤ |t|`. -/
theorem norm_deriv_riemannZeta_one_add_mul_I_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃t : ℝ⦄, 2 ≤ |t| →
      ‖deriv riemannZeta (1 + (t : ℂ) * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨C, hC, hbd⟩ := norm_deriv_riemannZeta_re_ge_one_le
  exact ⟨C, hC, fun t ht ↦ by simpa using hbd le_rfl ht⟩

/-- Growth bound on the vertical line `Re s = 0` via the functional equation and Stirling's formula:
`‖riemannZeta (t * I)‖ ≤ C * |t| ^ (1 / 2) * Real.log (|t| + 2)` for `2 ≤ |t|`. -/
theorem norm_riemannZeta_zero_add_mul_I_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃t : ℝ⦄, 2 ≤ |t| →
      ‖riemannZeta ((t : ℂ) * I)‖ ≤ C * |t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨c_g, C_G, hcg_pos, hCG_ge, hG_bd⟩ := norm_complex_gamma_strip_bounds 1 1
  have hCG_pos : 0 < C_G := lt_of_lt_of_le hcg_pos hCG_ge
  obtain ⟨C₁, hC₁_pos, hZ_bd⟩ := norm_riemannZeta_one_add_mul_I_le
  let C : ℝ := (1 / Real.pi) * C_G * C₁
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun t ht ↦ ?_⟩
  let w : ℂ := 1 - (t : ℂ) * I
  have hw_ne : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have him := congrArg Complex.im h
    simp only [w, sub_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_sub, neg_im, natCast_im, neg_zero] at him
    have : t = 0 := by linarith
    rw [this, abs_zero] at ht
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [w] at him
    rw [him, abs_zero] at ht
    linarith
  have hfe := riemannZeta_one_sub hw_ne hw1
  have h1sub : 1 - w = (t : ℂ) * I := by simp [w]
  rw [h1sub] at hfe
  have h2pi_norm : ‖2 * (2 * (Real.pi : ℂ)) ^ (-w)‖ = 1 / Real.pi := by
    have hpos : 0 < 2 * Real.pi := by positivity
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have hre : (-w).re = -1 := by simp [w]
    rw [hre, Real.rpow_neg_one]
    field_simp [Real.pi_ne_zero]
  have hG_norm : ‖Complex.Gamma w‖ ≤
      C_G * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (1 / 2 : ℝ) := by
    have heq : w = (1 : ℂ) + ((-t : ℝ) : ℂ) * I := by
      dsimp only [w]; push_cast; ring
    rw [heq]
    have hmem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 1 := Set.left_mem_Icc.mpr le_rfl
    have habs : 1 ≤ |-t| := by rw [abs_neg]; linarith
    have hres := (hG_bd hmem habs).2
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, abs_neg] at hres
    simpa [mul_assoc] using hres
  have hcos_norm : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
    have harg : (Real.pi : ℂ) * w / 2 = (Real.pi : ℂ) / 2 - (Real.pi * t / 2 : ℝ) * I := by
      dsimp only [w]; push_cast; ring
    rw [harg, Complex.cos_pi_div_two_sub, Complex.sin]
    have hi1 : -(((Real.pi * t / 2 : ℝ) : ℂ) * I) * I = ((Real.pi * t / 2 : ℝ) : ℂ) := by
      calc -(((Real.pi * t / 2 : ℝ) : ℂ) * I) * I = -((Real.pi * t / 2 : ℝ) : ℂ) * (I * I) := by ring
        _ = -((Real.pi * t / 2 : ℝ) : ℂ) * (-1) := by rw [I_mul_I]
        _ = _ := by ring
    have hi2 : (((Real.pi * t / 2 : ℝ) : ℂ) * I) * I = -((Real.pi * t / 2 : ℝ) : ℂ) := by
      calc (((Real.pi * t / 2 : ℝ) : ℂ) * I) * I = ((Real.pi * t / 2 : ℝ) : ℂ) * (I * I) := by ring
        _ = ((Real.pi * t / 2 : ℝ) : ℂ) * (-1) := by rw [I_mul_I]
        _ = _ := by ring
    rw [hi1, hi2]
    have he1 : ‖Complex.exp ((Real.pi * t / 2 : ℝ) : ℂ)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
      rw [Complex.norm_exp, Complex.ofReal_re]
      refine Real.exp_le_exp.mpr ?_
      rw [show Real.pi * t / 2 = (Real.pi / 2) * t by ring]
      exact mul_le_mul_of_nonneg_left (le_abs_self t) (by positivity)
    have he2 : ‖Complex.exp (-((Real.pi * t / 2 : ℝ) : ℂ))‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
      refine Real.exp_le_exp.mpr ?_
      rw [show -(Real.pi * t / 2) = (Real.pi / 2) * (-t) by ring]
      exact mul_le_mul_of_nonneg_left (neg_le_abs t) (by positivity)
    calc
      ‖(Complex.exp ((Real.pi * t / 2 : ℝ) : ℂ) - Complex.exp (-((Real.pi * t / 2 : ℝ) : ℂ))) * I / 2‖
          = ‖Complex.exp ((Real.pi * t / 2 : ℝ) : ℂ) -
              Complex.exp (-((Real.pi * t / 2 : ℝ) : ℂ))‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, show ‖(2 : ℂ)‖ = 2 by norm_num]
      _ ≤ (‖Complex.exp ((Real.pi * t / 2 : ℝ) : ℂ)‖ +
            ‖Complex.exp (-((Real.pi * t / 2 : ℝ) : ℂ))‖) / 2 := by
        gcongr; exact norm_sub_le _ _
      _ ≤ (Real.exp ((Real.pi / 2) * |t|) + Real.exp ((Real.pi / 2) * |t|)) / 2 := by gcongr
      _ = Real.exp ((Real.pi / 2) * |t|) := by ring
  have hzeta_norm : ‖riemannZeta w‖ ≤ C₁ * Real.log (|t| + 2) := by
    have heq : w = 1 + ((-t : ℝ) : ℂ) * I := by
      dsimp only [w]; push_cast; ring
    rw [heq]
    have habs : 2 ≤ |-t| := by rw [abs_neg]; exact ht
    simpa [abs_neg] using hZ_bd habs
  rw [hfe, norm_mul, norm_mul, norm_mul]
  calc
    ‖2 * (2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ *
        ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ * ‖riemannZeta w‖
        ≤ (1 / Real.pi) * (C_G * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (1 / 2 : ℝ)) *
            Real.exp ((Real.pi / 2) * |t|) * (C₁ * Real.log (|t| + 2)) := by
      rw [h2pi_norm]
      gcongr
    _ = ((1 / Real.pi) * C_G * C₁) *
          (Real.exp (-(Real.pi / 2) * |t|) * Real.exp ((Real.pi / 2) * |t|)) *
          |t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2) := by ring
    _ = C * |t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2) := by
      rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one]

end HalfPlaneAndVerticalLineBounds

section CriticalStripConvexityBounds

private lemma differentiableOn_integral_b2 :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-s - 2))
      {s : ℂ | -1 < s.re} := by
  let f : ℝ → ℂ := Set.indicator (Set.Ioi (1 : ℝ)) (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ))
  have hf_loc : LocallyIntegrableOn f (Set.Ioi 0) := by
    have hcont : Continuous (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))
    have hloc : LocallyIntegrable f volume := by
      refine (locallyIntegrable_const (1 / 12 : ℝ)).mono
        (hcont.measurable.indicator measurableSet_Ioi).aestronglyMeasurable
        (Eventually.of_forall fun u ↦ ?_)
      rw [Real.norm_of_nonneg (by norm_num)]
      by_cases hu : (1 : ℝ) < u
      · simpa [f, hu, Complex.norm_real, Real.norm_eq_abs] using bernoulliKernel_two_abs_le u
      · simp [f, hu]
    exact hloc.locallyIntegrableOn _
  have hf_top : f =O[atTop] (fun u : ℝ ↦ u ^ (0 : ℝ)) := by
    refine IsBigO.of_bound (1 / 12) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    simpa [f, hu, Complex.norm_real, Real.norm_eq_abs] using bernoulliKernel_two_abs_le u
  intro s hs
  have hs_gt : -1 < s.re := hs
  let b : ℝ := -(s.re + 2)
  have hf_bot : f =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-b)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    have hu1 : ¬ (1 : ℝ) < u := not_lt.mpr hu.2.le
    simp [f, hu1]
  have hmel := mellin_differentiableOn_strip (a := 0) (b := b) hf_loc hf_top hf_bot
  have hstrip : -s - 1 ∈ {z : ℂ | b < z.re ∧ z.re < 0} := by
    simp only [Set.mem_ofPred_eq, sub_re, neg_re, one_re, b]
    exact ⟨by linarith, by linarith⟩
  have hdiff := (hmel (-s - 1) hstrip).differentiableAt (by
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hstrip)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ ↦ mellin f (-z - 1)) s :=
    DifferentiableAt.comp (g := mellin f) (f := fun z : ℂ ↦ -z - 1) s hdiff
      ((hasDerivAt_neg s).differentiableAt.sub_const 1)
  have heq : (fun z : ℂ ↦ ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)) =
      fun z : ℂ ↦ mellin f (-z - 1) := by
    ext z
    rw [mellin]
    have hcongr : Set.EqOn
        (fun u : ℝ ↦ (u : ℂ) ^ ((-z - 1) - 1) • f u)
        (Set.indicator (Set.Ioi (1 : ℝ))
          (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)))
        (Set.Ioi (0 : ℝ)) := by
      intro u _
      have hexp : (-z - 1) - 1 = -z - 2 := by ring
      by_cases hu1 : (1 : ℝ) < u
      · simp [f, Set.mem_Ioi, hu1, smul_eq_mul, mul_comm, hexp]
      · simp [f, Set.mem_Ioi, hu1]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  rw [heq]
  exact hcomp.differentiableWithinAt

private lemma integral_bernoulliKernel_one_mul_eq_sub_complex' {M N : ℕ} (hMN : M ≤ N)
    {g g' : ℝ → ℂ}
    (hg : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Set.Icc (M : ℝ) N)) :
    ∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * g t =
      ((1 / 12 : ℂ) * g N - (1 / 12 : ℂ) * g M) -
        ∫ t in (M : ℝ)..N, (bernoulliKernel 2 t : ℂ) * g' t := by
  have hle : (M : ℝ) ≤ N := Nat.cast_le.mpr hMN
  have hre_deriv : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt (fun x ↦ (g x).re) (g' t).re t :=
    fun t ht ↦ Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hg t ht)
  have him_deriv : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt (fun x ↦ (g x).im) (g' t).im t :=
    fun t ht ↦ Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hg t ht)
  have hre_cont : ContinuousOn (fun x ↦ (g' x).re) (Set.Icc (M : ℝ) N) :=
    Complex.continuous_re.comp_continuousOn hg'
  have him_cont : ContinuousOn (fun x ↦ (g' x).im) (Set.Icc (M : ℝ) N) :=
    Complex.continuous_im.comp_continuousOn hg'
  have hre_ibp := integral_bernoulliKernel_mul_eq_sub (j := 1) le_rfl hle hre_deriv hre_cont
  have him_ibp := integral_bernoulliKernel_mul_eq_sub (j := 1) le_rfl hle him_deriv him_cont
  simp only [bernoulliKernel_one] at hre_ibp him_ibp
  have hg_cont : ContinuousOn g (Set.Icc (M : ℝ) N) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have h_int1 : IntervalIntegrable (fun t ↦ (sawtooth t : ℂ) * g t) volume (M : ℝ) N := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    refine Integrable.mono' (hg_cont.norm.integrableOn_Icc.const_mul (1 / 2)) ?_ ?_
    · exact ((Complex.continuous_ofReal.aestronglyMeasurable.comp_measurable
        (measurable_fract.sub_const _)).mul (hg_cont.aestronglyMeasurable measurableSet_Icc))
    · filter_upwards with t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (sawtooth_abs_le t) (norm_nonneg _)
  have h_int2 : IntervalIntegrable (fun t ↦ (bernoulliKernel 2 t : ℂ) * g' t) volume (M : ℝ) N := by
    refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
    exact (Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))).continuousOn.mul hg'
  have hint_re1 := Complex.reCLM.intervalIntegral_comp_comm h_int1
  have hint_im1 := Complex.imCLM.intervalIntegral_comp_comm h_int1
  have hint_re2 := Complex.reCLM.intervalIntegral_comp_comm h_int2
  have hint_im2 := Complex.imCLM.intervalIntegral_comp_comm h_int2
  apply Complex.ext
  · have h1 : (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * g t).re =
        Complex.reCLM (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * g t) := rfl
    have h2 : (∫ t in (M : ℝ)..N, (bernoulliKernel 2 t : ℂ) * g' t).re =
        Complex.reCLM (∫ t in (M : ℝ)..N, (bernoulliKernel 2 t : ℂ) * g' t) := rfl
    rw [h1, ← hint_re1]
    simp only [Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.div_ofNat_im, Complex.one_im, zero_div, zero_mul, sub_zero]
    rw [h2, ← hint_re2]
    simpa [Complex.reCLM_apply] using hre_ibp
  · have h1 : (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * g t).im =
        Complex.imCLM (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * g t) := rfl
    have h2 : (∫ t in (M : ℝ)..N, (bernoulliKernel 2 t : ℂ) * g' t).im =
        Complex.imCLM (∫ t in (M : ℝ)..N, (bernoulliKernel 2 t : ℂ) * g' t) := rfl
    rw [h1, ← hint_im1]
    simp only [Complex.sub_im, Complex.mul_im, Complex.div_ofNat_re, Complex.one_re,
      Complex.div_ofNat_im, Complex.one_im, zero_div, zero_mul, add_zero]
    rw [h2, ← hint_im2]
    simpa [Complex.imCLM_apply] using him_ibp

private lemma integrableOn_bernoulliKernel_two_cpow_Ioi' {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : -1 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-s - 2)) (Set.Ioi a) := by
  have hpow_int : IntegrableOn (fun u : ℝ ↦ (1 / 12 : ℝ) * u ^ (-s.re - 2)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul (1 / 12)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hcont_b2 : Continuous (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))
    have hcont_pow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (-s - 2)) (Set.Ioi a) :=
      continuousOn_of_forall_continuousAt fun u hu ↦
        (cpow_ofReal_hasDerivAt' (lt_trans ha hu) (-s - 2)).continuousAt
    exact (hcont_b2.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
      (hcont_pow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := lt_trans ha hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re]
    exact mul_le_mul (bernoulliKernel_two_abs_le u) le_rfl (by positivity) (by positivity)

private lemma isPathConnected_re_gt_neg_one_sdiff_one :
    IsPathConnected {s : ℂ | -1 < s.re ∧ s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | -1 < s.re ∧ s ≠ 1}
  refine ⟨(2 : ℂ), ⟨by norm_num, by norm_num⟩, fun {z} hz ↦ ?_⟩
  by_cases him : z.im ≠ 0
  · let γ : unitInterval → ℂ := fun t ↦ ((1 - (t : ℝ) : ℝ) : ℂ) * 2 + ((t : ℝ) : ℂ) * z
    refine ⟨⟨⟨γ, by fun_prop⟩, by simp [γ], by simp [γ]⟩, fun t ↦ ?_⟩
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    refine ⟨?_, ?_⟩
    · change -1 < (γ t).re
      simp only [γ, add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, mul_zero, sub_zero,
        zero_mul]
      rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
      · rw [← ht_zero]
        norm_num
      · have hmul1 : (1 - (t : ℝ)) * (-1) ≤ (1 - (t : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
        have hmul2 : (t : ℝ) * (-1) < (t : ℝ) * z.re :=
          mul_lt_mul_of_pos_left hz.1 ht_pos
        linarith
    · intro hEq
      have hEq' : γ t = 1 := hEq
      have hIm : (γ t).im = (1 : ℂ).im := congrArg Complex.im hEq'
      simp only [γ, add_im, mul_im, ofReal_re, ofReal_im, im_ofNat, mul_zero, zero_mul, add_zero,
        one_im, zero_add, mul_eq_zero] at hIm
      rcases hIm with ht_zero | him_zero
      · have h21 : (2 : ℂ) = 1 := calc
          (2 : ℂ) = γ t := by simp [γ, ht_zero]
          _ = 1 := hEq'
        exact absurd h21 (by norm_num)
      · exact him him_zero
  · push Not at him
    let mid : ℂ := (2 : ℂ) + I
    have hpath1 : JoinedIn U (2 : ℂ) mid := by
      refine ⟨⟨⟨fun t : unitInterval ↦ (2 : ℂ) + ((t : ℝ) : ℂ) * I, by fun_prop⟩,
        by simp, by simp [mid]⟩, fun t ↦ ?_⟩
      refine ⟨by simp; norm_num, ?_⟩
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp at hRe
    have hpath2 : JoinedIn U mid z := by
      let γ : unitInterval → ℂ := fun t ↦ ((1 - (t : ℝ) : ℝ) : ℂ) * mid + ((t : ℝ) : ℂ) * z
      refine ⟨⟨⟨γ, by fun_prop⟩, by simp [γ], by simp [γ]⟩, fun t ↦ ?_⟩
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      refine ⟨?_, ?_⟩
      · change -1 < (γ t).re
        simp only [γ, mid, add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, I_re, add_zero,
          zero_mul, sub_zero]
        rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
        · rw [← ht_zero]
          norm_num
        · have hmul1 : (1 - (t : ℝ)) * (-1) ≤ (1 - (t : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
          have hmul2 : (t : ℝ) * (-1) < (t : ℝ) * z.re :=
            mul_lt_mul_of_pos_left hz.1 ht_pos
          linarith
      · intro hEq
        have hEq' : γ t = 1 := hEq
        rcases eq_or_lt_of_le ht1 with ht_one | ht_lt
        · have hEnd : γ t = z := by simp [γ, ht_one]
          exact hz.2 (hEnd ▸ hEq')
        · have hIm : (γ t).im = (1 : ℂ).im := congrArg Complex.im hEq'
          simp [γ, mid, him] at hIm
          linarith
    exact hpath1.trans hpath2

private lemma riemannZeta_second_order_base {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 + (1 / 12 : ℂ) * s -
      s * (s + 1) * ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-s - 2) := by
  let U : Set ℂ := {z : ℂ | -1 < z.re ∧ z ≠ 1}
  let L : ℂ → ℂ := riemannZeta
  let R : ℂ → ℂ := fun z ↦ 1 / (z - 1) + 1 / 2 + (1 / 12 : ℂ) * z -
    z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)
  have hL_an : AnalyticOnNhd ℂ L U := analyticOn_riemannZeta.mono (fun _ hz ↦ hz.2)
  have hR_diff : DifferentiableOn ℂ R U := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / (w - 1) + 1 / 2 + (1 / 12 : ℂ) * w) z := by
      have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz.2
      fun_prop (disch := exact hne)
    have hint : DifferentiableAt ℂ
        (fun w : ℂ ↦ ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-w - 2)) z :=
      (differentiableOn_integral_b2 z hz.1).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1)
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦
        w * (w + 1) * ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-w - 2)) z :=
      (differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul hint
    exact (h1.sub h2).differentiableWithinAt
  have hU_open : IsOpen {z : ℂ | -1 < z.re ∧ z ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (-1 : ℝ) < z.re}).inter
      (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})
  have hR_an : AnalyticOnNhd ℂ R U := hR_diff.analyticOnNhd hU_open
  have h_pos : ∀ {z : ℂ}, 0 < z.re → z ≠ 1 → L z = R z := by
    intro z hz hz1
    have h1 := riemannZeta_eulerMaclaurin_N (N := 1) le_rfl hz hz1
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow] at h1
    have hrecip : 1 - 1 / (1 - z) - (1 / 2 : ℂ) = 1 / (z - 1) + 1 / 2 := by
      have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
      have hne' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      field_simp [hne, hne']
      ring
    have hibp (M : ℕ) (hM : 1 ≤ M) :
        ∫ t in (1 : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) =
          ((1 / 12 : ℂ) * (M : ℂ) ^ (-z - 1) - (1 / 12 : ℂ)) +
            (z + 1) * ∫ t in (1 : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2) := by
      have hg : ∀ t ∈ Set.Icc ((1 : ℕ) : ℝ) M,
          HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-z - 1)) ((-z - 1) * (t : ℂ) ^ (-z - 2)) t := by
        intro t ht
        simp only [Nat.cast_one] at ht
        have hd := cpow_ofReal_hasDerivAt' (lt_of_lt_of_le zero_lt_one ht.1) (-z - 1)
        convert hd using 1
        ring_nf
      have hg' : ContinuousOn (fun u : ℝ ↦ (-z - 1) * (u : ℂ) ^ (-z - 2))
          (Set.Icc ((1 : ℕ) : ℝ) M) := by
        simp only [Nat.cast_one]
        exact continuousOn_const.mul (continuousOn_of_forall_continuousAt fun u hu ↦
          (cpow_ofReal_hasDerivAt' (lt_of_lt_of_le zero_lt_one hu.1) (-z - 2)).continuousAt)
      have hres := integral_bernoulliKernel_one_mul_eq_sub_complex' hM hg hg'
      simp only [Nat.cast_one, Complex.ofReal_one, one_cpow, mul_one] at hres
      have hpull : ∫ t in (1 : ℝ)..M, (bernoulliKernel 2 t : ℂ) * ((-z - 1) * (t : ℂ) ^ (-z - 2)) =
          (-z - 1) * ∫ t in (1 : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2) := by
        have hcongr : (fun t : ℝ ↦ (bernoulliKernel 2 t : ℂ) * ((-z - 1) * (t : ℂ) ^ (-z - 2))) =
            fun t : ℝ ↦ (-z - 1) * ((bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2)) := by
          ext t; ring
        rw [hcongr, intervalIntegral.integral_const_mul]
      rw [hpull] at hres
      linear_combination hres
    have hint1 : Tendsto (fun M : ℕ ↦ ∫ t in (1 : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))) :=
      (intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_sawtooth_cpow_Ioi' zero_lt_one hz)
        tendsto_id).comp tendsto_natCast_atTop_atTop
    have hint2 : Tendsto
        (fun M : ℕ ↦ ∫ t in (1 : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2))
        atTop (𝓝 (∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))) :=
      (intervalIntegral_tendsto_integral_Ioi 1
        (integrableOn_bernoulliKernel_two_cpow_Ioi' zero_lt_one (by linarith))
        tendsto_id).comp tendsto_natCast_atTop_atTop
    have hpowM : Tendsto (fun M : ℕ ↦ (M : ℂ) ^ (-z - 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hreal : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (-z.re - 1)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < z.re + 1)).comp tendsto_natCast_atTop_atTop
          |>.congr fun M ↦ by rw [Function.comp_apply, show -(z.re + 1) = -z.re - 1 by ring]
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      rw [Complex.norm_natCast_cpow_of_pos hM, sub_re, neg_re, one_re]
    have hlim_rhs : Tendsto (fun M : ℕ ↦
        ((1 / 12 : ℂ) * (M : ℂ) ^ (-z - 1) - (1 / 12 : ℂ)) +
          (z + 1) * ∫ t in (1 : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2))
        atTop (𝓝 (-(1 / 12 : ℂ) +
          (z + 1) * ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))) := by
      have hsub : Tendsto (fun M : ℕ ↦ (1 / 12 : ℂ) * (M : ℂ) ^ (-z - 1) - (1 / 12 : ℂ))
          atTop (𝓝 (0 - (1 / 12 : ℂ))) := by
        simpa using (hpowM.const_mul (1 / 12 : ℂ)).sub_const (1 / 12 : ℂ)
      have hres := hsub.add (hint2.const_mul (z + 1))
      refine hres.trans_eq (congrArg 𝓝 ?_)
      ring
    have heq_tail :
        ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1) =
          -(1 / 12 : ℂ) +
            (z + 1) * ∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2) :=
      tendsto_nhds_unique hint1 (hlim_rhs.congr' (by
        filter_upwards [eventually_ge_atTop 1] with M hM; exact (hibp M hM).symm))
    dsimp only [L, R]
    rw [h1, heq_tail]
    linear_combination hrecip
  have h2mem : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : L =ᶠ[𝓝 (2 : ℂ)] R := by
    have hopen_set : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (0 : ℝ) < z.re}).inter
        (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})
    filter_upwards [hopen_set.mem_nhds ⟨by norm_num, by norm_num⟩] with z hz
    exact h_pos hz.1 hz.2
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an
    isPathConnected_re_gt_neg_one_sdiff_one.isConnected.isPreconnected
    h2mem hev ⟨hs, hs1⟩

private lemma integral_rpow_neg_two_Ioi :
    ∫ u in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ) = 1 := by
  have hint : IntegrableOn (fun u : ℝ ↦ u ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have htend : Tendsto (fun R : ℝ ↦ ∫ u in (1 : ℝ)..R, u ^ (-2 : ℝ)) atTop
      (𝓝 (∫ u in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
  have hcalc : ∀ R : ℝ, 1 ≤ R → ∫ u in (1 : ℝ)..R, u ^ (-2 : ℝ) = 1 - R ^ (-1 : ℝ) := by
    intro R hR
    rw [integral_rpow (Or.inr ⟨by norm_num, fun h ↦ by
      rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
    simp only [Real.one_rpow]
    have hexp : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [hexp]
    ring
  have hlim : Tendsto (fun R : ℝ ↦ 1 - R ^ (-1 : ℝ)) atTop (𝓝 1) := by
    have hr : Tendsto (fun R : ℝ ↦ R ^ (-1 : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop zero_lt_one
    simpa using tendsto_const_nhds.sub hr
  exact tendsto_nhds_unique htend (hlim.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR; exact (hcalc R hR).symm))

private noncomputable def zetaStripAux (s : ℂ) : ℂ :=
  riemannZeta₁ s / (s + 2)

private lemma log_le_inv_eps_mul_rpow {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 ≤ u) :
    Real.log u ≤ (1 / ε) * u ^ ε := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h1 : Real.log (u ^ ε) ≤ u ^ ε - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu_pos ε)
  rw [Real.log_rpow hu_pos] at h1
  have h2 : ε * Real.log u ≤ u ^ ε := by linarith
  have h3 : Real.log u ≤ u ^ ε / ε := (le_div_iff₀ hε).mpr (by linarith)
  simpa [div_eq_mul_inv, mul_comm] using h3

private lemma differentiableOn_zetaStripAux :
    DifferentiableOn ℂ zetaStripAux {z : ℂ | -1 < z.re} := by
  intro z hz
  have hz_gt : -1 < z.re := hz
  have hne : z + 2 ≠ 0 := fun h ↦ by
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  exact (differentiable_riemannZeta₁.differentiableAt.div
    (differentiableAt_id.add_const 2) hne).differentiableWithinAt

private lemma norm_zetaStripAux_verticalStrip_bound :
    ∀ z ∈ verticalStripOpen 0 1, ‖zetaStripAux z‖ ≤ 20 * (|z.im| + 2) ^ (3 : ℝ) := by
  intro z hz
  have hz_gt : -1 < z.re := by linarith [hz.1]
  have hz_ne1 : z ≠ 1 := fun h ↦ absurd (h ▸ hz).2 (by simp)
  have h_add2 : 2 ≤ ‖z + 2‖ := by
    have hre : 2 ≤ (z + 2).re := by simp; linarith [hz.1]
    exact hre.trans (Complex.re_le_norm _)
  have hz_norm : ‖z‖ ≤ |z.im| + 2 := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |z.im| := by gcongr; rw [abs_of_nonneg hz.1.le]; exact hz.2.le
      _ ≤ |z.im| + 2 := by linarith
  have hz_sub1 : ‖z - 1‖ ≤ 2 * (|z.im| + 2) := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
      _ ≤ (|z.im| + 2) + 1 := by simp only [norm_one]; linarith
      _ ≤ 2 * (|z.im| + 2) := by linarith [abs_nonneg z.im]
  have hz_add1 : ‖z + 1‖ ≤ 2 * (|z.im| + 2) := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le z 1
      _ ≤ (|z.im| + 2) + 1 := by simp only [norm_one]; linarith
      _ ≤ 2 * (|z.im| + 2) := by linarith [abs_nonneg z.im]
  have hint_le : ‖∫ u in Set.Ioi (1 : ℝ),
      (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)‖ ≤ 1 / 12 := by
    have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 12 : ℝ) * u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul (1 / 12)
    calc
      ‖∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)‖
          ≤ ∫ u in Set.Ioi (1 : ℝ), ‖(bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (1 : ℝ), (1 / 12 : ℝ) * u ^ (-2 : ℝ) := by
        refine setIntegral_mono_on
          (integrableOn_bernoulliKernel_two_cpow_Ioi' zero_lt_one hz_gt).norm hdom
          measurableSet_Ioi fun u hu ↦ ?_
        have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
        have hu_pos : 0 < u := by linarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
        simp only [sub_re, neg_re, re_ofNat]
        refine mul_le_mul (bernoulliKernel_two_abs_le u)
          (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith [hz.1]))
          (by positivity) (by positivity)
      _ = (1 / 12 : ℝ) * ∫ u in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ) := integral_const_mul _ _
      _ = 1 / 12 := by rw [integral_rpow_neg_two_Ioi, mul_one]
  have hzeta1_eq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr hz_ne1), one_mul]
  have hbase := riemannZeta_second_order_base hz_gt hz_ne1
  have hexp_eq : (z - 1) * riemannZeta z =
      1 + (z - 1) * (1 / 2 + (1 / 12 : ℂ) * z -
        z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ),
          (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)) := by
    rw [hbase]
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
    field_simp [hne]
    ring
  have hz2_ge1 : (1 : ℝ) ≤ |z.im| + 2 := by linarith [abs_nonneg z.im]
  have hpow1 : |z.im| + 2 ≤ (|z.im| + 2) ^ (3 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hz2_ge1 (by norm_num : (1 : ℝ) ≤ 3)
  have hpow2 : (|z.im| + 2) ^ (2 : ℝ) ≤ (|z.im| + 2) ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hz2_ge1 (by norm_num : (2 : ℝ) ≤ 3)
  have h1_le : (1 : ℝ) ≤ (|z.im| + 2) ^ (3 : ℝ) := Real.one_le_rpow hz2_ge1 (by norm_num)
  have hnorm_z1 : ‖riemannZeta₁ z‖ ≤ 20 * (|z.im| + 2) ^ (3 : ℝ) := by
    rw [hzeta1_eq, hexp_eq]
    have hterm1 : ‖(1 / 2 : ℂ) + (1 / 12 : ℂ) * z -
        z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ),
          (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)‖ ≤
        1 + (1 / 12 : ℝ) * (|z.im| + 2) +
          (|z.im| + 2) * (2 * (|z.im| + 2)) * (1 / 12 : ℝ) := by
      have htri := norm_sub_le ((1 / 2 : ℂ) + (1 / 12 : ℂ) * z)
        (z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ),
          (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))
      have hadd := norm_add_le (1 / 2 : ℂ) ((1 / 12 : ℂ) * z)
      have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      have h12 : ‖(1 / 12 : ℂ)‖ = 1 / 12 := by norm_num
      rw [norm_mul, h12] at hadd
      rw [norm_mul, norm_mul] at htri
      have hmul_int : ‖z‖ * ‖z + 1‖ *
          ‖∫ u in Set.Ioi (1 : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)‖ ≤
          (|z.im| + 2) * (2 * (|z.im| + 2)) * (1 / 12 : ℝ) := by gcongr
      linarith
    calc
      ‖1 + (z - 1) * (1 / 2 + (1 / 12 : ℂ) * z -
          z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ),
            (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))‖
          ≤ ‖(1 : ℂ)‖ + ‖(z - 1) * (1 / 2 + (1 / 12 : ℂ) * z -
              z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ),
                (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))‖ := norm_add_le _ _
      _ = 1 + ‖z - 1‖ * ‖1 / 2 + (1 / 12 : ℂ) * z -
            z * (z + 1) * ∫ u in Set.Ioi (1 : ℝ),
              (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + (2 * (|z.im| + 2)) * (1 + (1 / 12 : ℝ) * (|z.im| + 2) +
            (|z.im| + 2) * (2 * (|z.im| + 2)) * (1 / 12 : ℝ)) := by gcongr
      _ = 1 + 2 * (|z.im| + 2) + (1 / 6 : ℝ) * (|z.im| + 2) ^ (2 : ℝ) +
            (1 / 3 : ℝ) * (|z.im| + 2) ^ (3 : ℝ) := by
        rw [show (|z.im| + 2) ^ (2 : ℝ) = (|z.im| + 2) ^ (2 : ℕ) by norm_cast,
          show (|z.im| + 2) ^ (3 : ℝ) = (|z.im| + 2) ^ (3 : ℕ) by norm_cast]
        ring
      _ ≤ 1 * (|z.im| + 2) ^ (3 : ℝ) + 2 * (|z.im| + 2) ^ (3 : ℝ) +
            (1 / 6 : ℝ) * (|z.im| + 2) ^ (3 : ℝ) + (1 / 3 : ℝ) * (|z.im| + 2) ^ (3 : ℝ) := by
        have h1_le' : (1 : ℝ) ≤ 1 * (|z.im| + 2) ^ (3 : ℝ) := by simpa using h1_le
        gcongr
      _ ≤ 20 * (|z.im| + 2) ^ (3 : ℝ) := by
        linarith [Real.rpow_pos_of_pos (by linarith : 0 < |z.im| + 2) 3]
  calc
    ‖zetaStripAux z‖ = ‖riemannZeta₁ z‖ / ‖z + 2‖ := norm_div _ _
    _ ≤ ‖riemannZeta₁ z‖ / 1 := div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one (by linarith)
    _ = ‖riemannZeta₁ z‖ := div_one _
    _ ≤ 20 * (|z.im| + 2) ^ (3 : ℝ) := hnorm_z1

private lemma norm_zetaStripAux_left_edge_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ t : ℝ,
      ‖zetaStripAux ((0 : ℂ) + (t : ℂ) * I)‖ ≤ K₀ * (|t| + 2) ^ (1 / 2 + ε) := by
  obtain ⟨C₀, _, hZ₀⟩ := norm_riemannZeta_zero_add_mul_I_le
  have hcont_left : Continuous fun t : ℝ ↦ zetaStripAux ((0 : ℂ) + (t : ℂ) * I) :=
    differentiableOn_zetaStripAux.continuousOn.comp_continuous
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t ↦ by simp
  obtain ⟨B₀, hB₀⟩ :=
    ((isCompact_Icc (a := (-2 : ℝ)) (b := 2)).image_of_continuousOn
      hcont_left.norm.continuousOn).bddAbove
  let M₀ : ℝ := max B₀ 0
  have hM₀ : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (-2 : ℝ) 2 →
      ‖zetaStripAux ((0 : ℂ) + (t : ℂ) * I)‖ ≤ M₀ := fun t ht ↦
    (hB₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  let K₀ : ℝ := max (C₀ / ε) M₀
  refine ⟨K₀, le_trans (le_max_right _ _) (le_max_right _ _), fun t ↦ ?_⟩
  have ht2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  rcases le_or_gt 2 |t| with ht_ge | ht_lt
  · have hne1 : ((t : ℂ) * I) ≠ 1 := fun h ↦ by
      have := congrArg Complex.re h
      simp at this
    have hratio : ‖((t : ℂ) * I - 1) / ((t : ℂ) * I + 2)‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ ?_ (norm_nonneg _)
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_zero, one_re, add_re, re_ofNat, sub_im, mul_im, one_im, add_im,
        im_ofNat, add_zero, zero_sub]
      linarith
    have hzeta_eq : zetaStripAux ((0 : ℂ) + (t : ℂ) * I) =
        (((t : ℂ) * I - 1) / ((t : ℂ) * I + 2)) * riemannZeta ((t : ℂ) * I) := by
      simp only [zero_add, zetaStripAux]
      rw [riemannZeta_eq_inv_sub_mul hne1]
      have hsub : (t : ℂ) * I - 1 ≠ 0 := sub_ne_zero.mpr hne1
      field_simp [hsub]
    have hlog : Real.log (|t| + 2) ≤ (1 / ε) * (|t| + 2) ^ ε :=
      log_le_inv_eps_mul_rpow hε ht2
    have hlog_nn : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg ht2
    have hsqrt : |t| ^ (1 / 2 : ℝ) ≤ (|t| + 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) (by norm_num)
    calc
      ‖zetaStripAux ((0 : ℂ) + (t : ℂ) * I)‖
          = ‖((t : ℂ) * I - 1) / ((t : ℂ) * I + 2)‖ * ‖riemannZeta ((t : ℂ) * I)‖ := by
        rw [hzeta_eq, norm_mul]
      _ ≤ 1 * (C₀ * |t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2)) := by
        gcongr; exact hZ₀ ht_ge
      _ ≤ C₀ * (|t| + 2) ^ (1 / 2 : ℝ) * ((1 / ε) * (|t| + 2) ^ ε) := by
        rw [one_mul]; gcongr
      _ = (C₀ / ε) * ((|t| + 2) ^ (1 / 2 : ℝ) * (|t| + 2) ^ ε) := by ring
      _ = (C₀ / ε) * (|t| + 2) ^ (1 / 2 + ε) := by
        rw [← Real.rpow_add (by linarith : 0 < |t| + 2)]
      _ ≤ K₀ * (|t| + 2) ^ (1 / 2 + ε) := by
        gcongr; exact le_max_left _ _
  · have hpow_ge : 1 ≤ (|t| + 2) ^ (1 / 2 + ε) := Real.one_le_rpow ht2 (by linarith)
    have ht_mem : t ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp ht_lt.le
    calc
      ‖zetaStripAux ((0 : ℂ) + (t : ℂ) * I)‖ ≤ M₀ := hM₀ ht_mem
      _ = M₀ * 1 := (mul_one _).symm
      _ ≤ K₀ * (|t| + 2) ^ (1 / 2 + ε) := by
        gcongr; exact le_max_right _ _

private lemma norm_zetaStripAux_right_edge_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ t : ℝ,
      ‖zetaStripAux ((1 : ℂ) + (t : ℂ) * I)‖ ≤ K₁ * (|t| + 2) ^ ε := by
  obtain ⟨C₁, _, hZ₁⟩ := norm_riemannZeta_one_add_mul_I_le
  have hcont_right : Continuous fun t : ℝ ↦ zetaStripAux ((1 : ℂ) + (t : ℂ) * I) :=
    differentiableOn_zetaStripAux.continuousOn.comp_continuous
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t ↦ by simp
  obtain ⟨B₁, hB₁⟩ :=
    ((isCompact_Icc (a := (-2 : ℝ)) (b := 2)).image_of_continuousOn
      hcont_right.norm.continuousOn).bddAbove
  let M₁ : ℝ := max B₁ 0
  have hM₁ : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (-2 : ℝ) 2 →
      ‖zetaStripAux ((1 : ℂ) + (t : ℂ) * I)‖ ≤ M₁ := fun t ht ↦
    (hB₁ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  let K₁ : ℝ := max (C₁ / ε) M₁
  refine ⟨K₁, le_trans (le_max_right _ _) (le_max_right _ _), fun t ↦ ?_⟩
  have ht2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  rcases le_or_gt 2 |t| with ht_ge | ht_lt
  · have hne1 : ((1 : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
      have := congrArg Complex.im h
      simp at this
      rw [this, abs_zero] at ht_ge
      linarith
    have hratio : ‖((1 : ℂ) + (t : ℂ) * I - 1) / ((1 : ℂ) + (t : ℂ) * I + 2)‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ ?_ (norm_nonneg _)
      have him_le : |t| ≤ ‖(1 : ℂ) + (t : ℂ) * I + 2‖ := by
        simpa using Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * I + 2)
      have hnum_eq : ‖(1 : ℂ) + (t : ℂ) * I - 1‖ = |t| := by
        have : (1 : ℂ) + (t : ℂ) * I - 1 = (t : ℂ) * I := by ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [hnum_eq]
      exact him_le
    have hzeta_eq : zetaStripAux ((1 : ℂ) + (t : ℂ) * I) =
        (((1 : ℂ) + (t : ℂ) * I - 1) / ((1 : ℂ) + (t : ℂ) * I + 2)) *
          riemannZeta ((1 : ℂ) + (t : ℂ) * I) := by
      simp only [zetaStripAux]
      rw [riemannZeta_eq_inv_sub_mul hne1]
      have hsub : (1 : ℂ) + (t : ℂ) * I - 1 ≠ 0 := sub_ne_zero.mpr hne1
      field_simp [hsub]
    have hlog : Real.log (|t| + 2) ≤ (1 / ε) * (|t| + 2) ^ ε :=
      log_le_inv_eps_mul_rpow hε ht2
    calc
      ‖zetaStripAux ((1 : ℂ) + (t : ℂ) * I)‖
          = ‖((1 : ℂ) + (t : ℂ) * I - 1) / ((1 : ℂ) + (t : ℂ) * I + 2)‖ *
              ‖riemannZeta ((1 : ℂ) + (t : ℂ) * I)‖ := by rw [hzeta_eq, norm_mul]
      _ ≤ 1 * (C₁ * Real.log (|t| + 2)) := by gcongr; exact hZ₁ ht_ge
      _ ≤ C₁ * ((1 / ε) * (|t| + 2) ^ ε) := by rw [one_mul]; gcongr
      _ = (C₁ / ε) * (|t| + 2) ^ ε := by ring
      _ ≤ K₁ * (|t| + 2) ^ ε := by gcongr; exact le_max_left _ _
  · have hpow_ge : 1 ≤ (|t| + 2) ^ ε := Real.one_le_rpow ht2 hε.le
    have ht_mem : t ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp ht_lt.le
    calc
      ‖zetaStripAux ((1 : ℂ) + (t : ℂ) * I)‖ ≤ M₁ := hM₁ ht_mem
      _ = M₁ * 1 := (mul_one _).symm
      _ ≤ K₁ * (|t| + 2) ^ ε := by gcongr; exact le_max_right _ _

private lemma norm_zetaStripAux_critical_strip_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃σ t : ℝ⦄, σ ∈ Set.Icc (0 : ℝ) 1 →
      ‖zetaStripAux ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ ((1 - σ) / 2 + ε) := by
  have hf_diff : DiffContOnCl ℂ zetaStripAux (verticalStripOpen 0 1) := by
    refine ⟨differentiableOn_zetaStripAux.mono (fun z hz ↦ ?_), ?_⟩
    · change (-1 : ℝ) < z.re
      exact lt_trans (by norm_num : (-1 : ℝ) < 0) hz.1
    · have hsub : closure (verticalStripOpen 0 1) ⊆ {z : ℂ | 0 ≤ z.re} :=
        (isClosed_le continuous_const Complex.continuous_re).closure_subset_iff.mpr
          fun _ hz ↦ hz.1.le
      refine differentiableOn_zetaStripAux.continuousOn.mono (hsub.trans fun z hz ↦ ?_)
      change (-1 : ℝ) < z.re
      have hz0 : 0 ≤ z.re := hz
      linarith
  obtain ⟨K₀, _, hleft⟩ := norm_zetaStripAux_left_edge_le hε
  obtain ⟨K₁, _, hright⟩ := norm_zetaStripAux_right_edge_le hε
  obtain ⟨C, hC_nn, hpl⟩ := phragmen_lindelof_poly_interp_of_poly_le
    (σ₁ := 0) (σ₂ := 1) (A := 20) (γ := 3) (C₁ := K₀) (C₂ := K₁) (α₁ := 1 / 2 + ε) (α₂ := ε)
    zero_lt_one hf_diff (by norm_num) norm_zetaStripAux_verticalStrip_bound hleft hright
  refine ⟨C, hC_nn, fun σ t hσ ↦ ?_⟩
  have hlin : linearInterp 0 1 (1 / 2 + ε) ε σ = (1 - σ) / 2 + ε := by
    simp only [linearInterp]
    ring
  have hres := hpl σ hσ t
  rw [hlin] at hres
  exact hres

/-- **Critical-strip Phragmén–Lindelöf convexity bound** for `riemannZeta`:
for every `ε > 0`, there exists `C > 0` such that
`‖riemannZeta (σ + t * I)‖ ≤ C * (|t| + 2) ^ ((1 - σ) / 2 + ε)`
uniformly for `σ ∈ [0, 1]` and `1 ≤ |t|`. -/
theorem norm_riemannZeta_critical_strip_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, σ ∈ Set.Icc (0 : ℝ) 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ ((1 - σ) / 2 + ε) := by
  obtain ⟨C₀, hC₀_nn, haux⟩ := norm_zetaStripAux_critical_strip_le hε
  let C : ℝ := 4 * max C₀ 1
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun σ t hσ ht ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := fun h ↦ by
    have him := congrArg Complex.im h
    simp [s] at him
    rw [him, abs_zero] at ht
    linarith
  have hs_sub1 : 1 ≤ ‖s - 1‖ := by
    have him : |t| ≤ ‖s - 1‖ := by
      simpa [s] using Complex.abs_im_le_norm (s - 1)
    linarith
  have hratio : ‖(s + 2) / (s - 1)‖ ≤ 4 := by
    have heq : (s + 2) / (s - 1) = 1 + 3 / (s - 1) := by
      have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp [hne]
      ring
    rw [heq]
    calc
      ‖1 + 3 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖3 / (s - 1)‖ := norm_add_le _ _
      _ = 1 + 3 / ‖s - 1‖ := by
        rw [norm_one, norm_div, show ‖(3 : ℂ)‖ = 3 by norm_num]
      _ ≤ 1 + 3 / 1 := by gcongr
      _ = 4 := by norm_num
  have hzeta_eq : riemannZeta s = ((s + 2) / (s - 1)) * zetaStripAux s := by
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hne2 : s + 2 ≠ 0 := fun h ↦ by
      have hre := congrArg Complex.re h
      simp [s] at hre
      linarith [hσ.1]
    simp only [zetaStripAux]
    rw [riemannZeta_eq_inv_sub_mul hs1]
    field_simp [hne, hne2]
  have hpow_nn : 0 ≤ (|t| + 2) ^ ((1 - σ) / 2 + ε) := Real.rpow_nonneg (by positivity) _
  calc
    ‖riemannZeta s‖ = ‖(s + 2) / (s - 1)‖ * ‖zetaStripAux s‖ := by rw [hzeta_eq, norm_mul]
    _ ≤ 4 * (C₀ * (|t| + 2) ^ ((1 - σ) / 2 + ε)) := by
      gcongr; exact haux hσ
    _ ≤ C * (|t| + 2) ^ ((1 - σ) / 2 + ε) := by
      have hC_ge : 4 * C₀ ≤ C := by dsimp [C]; gcongr; exact le_max_left _ _
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hC_ge hpow_nn

/-- Critical-strip Phragmén–Lindelöf convexity bound in pure `|t|` form for `2 ≤ |t|`:
`‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ((1 - σ) / 2 + ε)` uniformly for `σ ∈ [0, 1]`. -/
theorem norm_riemannZeta_critical_strip_le_of_two_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, σ ∈ Set.Icc (0 : ℝ) 1 → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ ((1 - σ) / 2 + ε) := by
  obtain ⟨C₀, hC₀_pos, hbd⟩ := norm_riemannZeta_critical_strip_le hε
  let M : ℝ := (2 : ℝ) ^ (1 / 2 + ε)
  refine ⟨C₀ * M, mul_pos hC₀_pos (by positivity), fun σ t hσ ht ↦ ?_⟩
  have ht1 : 1 ≤ |t| := by linarith
  have hpow_le : (|t| + 2) ^ ((1 - σ) / 2 + ε) ≤ M * |t| ^ ((1 - σ) / 2 + ε) := by
    have hexp_nn : 0 ≤ (1 - σ) / 2 + ε := by linarith [hσ.2]
    have h2 : |t| + 2 ≤ 2 * |t| := by linarith
    calc
      (|t| + 2) ^ ((1 - σ) / 2 + ε)
          ≤ (2 * |t|) ^ ((1 - σ) / 2 + ε) := Real.rpow_le_rpow (by positivity) h2 hexp_nn
      _ = (2 : ℝ) ^ ((1 - σ) / 2 + ε) * |t| ^ ((1 - σ) / 2 + ε) :=
          Real.mul_rpow zero_le_two (abs_nonneg t)
      _ ≤ M * |t| ^ ((1 - σ) / 2 + ε) := by
          gcongr
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hσ.1])
  calc
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C₀ * (|t| + 2) ^ ((1 - σ) / 2 + ε) := hbd hσ ht1
    _ ≤ C₀ * (M * |t| ^ ((1 - σ) / 2 + ε)) := by gcongr
    _ = (C₀ * M) * |t| ^ ((1 - σ) / 2 + ε) := by ring

/-- `riemannZeta` has vertical order at most `(1 - σ) / 2 + ε` on every vertical line `σ ∈ [0, 1]`. -/
theorem hasVerticalOrder_riemannZeta_of_mem_Icc {σ ε : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hε : 0 < ε) : HasVerticalOrder riemannZeta σ ((1 - σ) / 2 + ε) := by
  obtain ⟨C, _, hbd⟩ := norm_riemannZeta_critical_strip_le hε
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [Filter.eventually_comap.mpr
    ((eventually_ge_atTop (1 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t ht
  have hpow_nn : 0 ≤ (|t| + 2) ^ ((1 - σ) / 2 + ε) := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg hpow_nn]
  exact hbd hσ ht

/-- Vertical order convexity bound in the critical strip:
`verticalOrder riemannZeta σ ≤ (1 - σ) / 2` for all `σ ∈ [0, 1]`. -/
theorem verticalOrder_riemannZeta_le {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    verticalOrder riemannZeta σ ≤ (1 - σ) / 2 := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hexp_nn : 0 ≤ (1 - σ) / 2 + ε := by linarith [hσ.2]
  exact verticalOrder_le_of_hasVerticalOrder hexp_nn (hasVerticalOrder_riemannZeta_of_mem_Icc hσ hε)

/-- Vanishing of the vertical order of `riemannZeta` for `1 ≤ σ`:
`verticalOrder riemannZeta σ = 0`. -/
theorem verticalOrder_riemannZeta_eq_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) :
    verticalOrder riemannZeta σ = 0 := by
  refine le_antisymm ?_ (verticalOrder_nonneg riemannZeta σ)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  obtain ⟨C, hC_pos, hbd⟩ := norm_riemannZeta_re_ge_one_le
  have hvo : HasVerticalOrder riemannZeta σ ε := by
    refine Asymptotics.isBigO_iff.mpr ⟨C / ε, ?_⟩
    filter_upwards [Filter.eventually_comap.mpr
      ((eventually_ge_atTop (2 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t ht
    have ht2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have hpow_nn : 0 ≤ (|t| + 2) ^ ε := Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg hpow_nn]
    calc
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + 2) := hbd hσ ht
      _ ≤ C * ((1 / ε) * (|t| + 2) ^ ε) := by gcongr; exact log_le_inv_eps_mul_rpow hε ht2
      _ = (C / ε) * (|t| + 2) ^ ε := by ring
  exact verticalOrder_le_of_hasVerticalOrder hε.le hvo

end CriticalStripConvexityBounds

end AnalyticNumberTheory.RiemannZeta
