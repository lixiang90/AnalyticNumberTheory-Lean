import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-!
# Zero-Free Region and Vertical Bounds for the Riemann Zeta Function

This file develops the classical de la Vallée Poussin zero-free region and effective upper
bounds for `deriv riemannZeta / riemannZeta` and `(riemannZeta)⁻¹` inside it:

- Trigonometric positivity `3 + 4 cos θ + cos (2θ) = 2 (1 + cos θ)^2 ≥ 0` and the resulting
  positivity `0 ≤ 3 Re(-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ + it)) + Re(-ζ'/ζ(σ + 2it))` for `1 < σ`.
- Non-vanishing of `riemannZeta` on the closed half-plane `1 ≤ Re s`.
- The de la Vallée Poussin zero-free region: there exists `c ∈ (0, 1/4)` such that
  `riemannZeta (σ + t * I) ≠ 0` whenever `1 - c / log (|t| + 2) ≤ σ` (and the standard `2 ≤ |t|`
  variant `1 - c / log |t| ≤ σ`).
- Effective logarithmic-squared bounds on `‖deriv riemannZeta / riemannZeta‖` and
  `‖(riemannZeta)⁻¹‖` throughout a zero-free region `1 - c' / log (|t| + 2) ≤ σ` via
  Borel–Carathéodory and Landau's lemma.
-/

open Complex Filter Topology Metric Set Real
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-! ### Trigonometric Positivity and the 3-4-1 Inequality -/

/-- Trigonometric identity `3 + 4 * cos θ + cos (2 * θ) = 2 * (1 + cos θ)^2`. -/
theorem three_add_four_cos_add_cos_two_mul_eq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- Non-negativity of the classical trigonometric polynomial `3 + 4 * cos θ + cos (2 * θ)`. -/
theorem three_add_four_cos_add_cos_two_mul_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [three_add_four_cos_add_cos_two_mul_eq]
  positivity

private lemma lseriesTerm_vonMangoldt_re {σ y : ℝ} (n : ℕ) :
    (LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ))
      ((σ : ℂ) + (y : ℂ) * I) n).re =
      if n = 0 then 0 else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (y * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn, ite_eq_right hn, div_eq_mul_inv, ← cpow_neg]
  have hcpow : (n : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) =
      ((n : ℝ) ^ (-σ) : ℝ) * Complex.exp (-(y * Real.log n : ℝ) * I) := by
    rw [cpow_def_of_ne_zero hn_ne, Real.rpow_def_of_pos hn_pos, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
    push_cast
    ring
  rw [hcpow, ← mul_assoc, ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hexp_re : (Complex.exp (-(y * Real.log n : ℝ) * I)).re = Real.cos (y * Real.log n) := by
    have him : -(y * Real.log n : ℝ) * I = (((-(y * Real.log n) : ℝ) : ℂ)) * I := by
      push_cast; rfl
    rw [him, Complex.exp_mul_I, Complex.add_re, ← Complex.ofReal_cos, Complex.ofReal_re,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, Real.cos_neg]
  rw [hexp_re]

private lemma re_neg_logDeriv_riemannZeta_eq_tsum {σ y : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta ((σ : ℂ) + (y : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (y : ℂ) * I)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (y * Real.log n) := by
  let s : ℂ := (σ : ℂ) + (y : ℂ) * I
  let fΛ : ℕ → ℂ := fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)
  have hs : 1 < s.re := by simp [s, hσ]
  have heq : -deriv riemannZeta s / riemannZeta s = LSeries fΛ s :=
    (AnalyticNumberTheory.DirichletSeries.LSeries_vonMangoldt_eq hs).symm
  have hsum : LSeriesSummable fΛ s :=
    AnalyticNumberTheory.DirichletSeries.LSeriesSummable_vonMangoldt_iff.mpr hs
  have hre : (∑' n : ℕ, LSeries.term fΛ s n).re = ∑' n : ℕ, (LSeries.term fΛ s n).re :=
    ((Complex.reCLM.hasSum hsum.hasSum).tsum_eq).symm
  rw [heq, LSeries, hre]
  refine tsum_congr fun n ↦ ?_
  exact lseriesTerm_vonMangoldt_re (σ := σ) (y := y) n

private lemma summable_vonMangoldt_re {σ y : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ ↦
      if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (y * Real.log n) := by
  let s : ℂ := (σ : ℂ) + (y : ℂ) * I
  let fΛ : ℕ → ℂ := fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)
  have hs : 1 < s.re := by simp [s, hσ]
  have hsum : LSeriesSummable fΛ s :=
    AnalyticNumberTheory.DirichletSeries.LSeriesSummable_vonMangoldt_iff.mpr hs
  have hre := Complex.reCLM.summable hsum
  refine hre.congr fun n ↦ ?_
  exact lseriesTerm_vonMangoldt_re (σ := σ) (y := y) n

/-- The `3-4-1` logarithmic-derivative positivity inequality: for `1 < σ` and `t : ℝ`,
`0 ≤ 3 Re(-ζ'(σ)/ζ(σ)) + 4 Re(-ζ'(σ+it)/ζ(σ+it)) + Re(-ζ'(σ+2it)/ζ(σ+2it))`. -/
theorem three_neg_logDeriv_add_four_add_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re +
      (-deriv riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * I) /
        riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * I)).re := by
  have h0 : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (0 * Real.log n) := by
    simpa using re_neg_logDeriv_riemannZeta_eq_tsum (y := 0) hσ
  have h1 : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
      riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) :=
    re_neg_logDeriv_riemannZeta_eq_tsum (y := t) hσ
  have h2 : (-deriv riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * I) /
      riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * I)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos ((2 * t) * Real.log n) := by
    simpa [mul_assoc] using re_neg_logDeriv_riemannZeta_eq_tsum (y := 2 * t) hσ
  have hs0 := summable_vonMangoldt_re (y := 0) hσ
  have hs1 := summable_vonMangoldt_re (y := t) hσ
  have hs2 := summable_vonMangoldt_re (y := 2 * t) hσ
  rw [h0, h1, h2, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add (hs0.mul_left 3) (hs1.mul_left 4),
    ← Summable.tsum_add ((hs0.mul_left 3).add (hs1.mul_left 4)) hs2]
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, ↓reduceIte, zero_mul, Real.cos_zero, mul_one]
  have hfac : 3 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) +
      4 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)) +
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (2 * t * Real.log n) =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) *
        (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n))) := by
    ring_nf
  rw [hfac]
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _))
    (three_add_four_cos_add_cos_two_mul_nonneg _)

/-! ### Non-vanishing on `Re s = 1` and Real-axis Pole Control -/

/-- Non-vanishing of `riemannZeta` on the boundary line `Re s = 1`. -/
theorem riemannZeta_ne_zero_of_one_add_mul_I (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by simp)

/-- Non-vanishing of `riemannZeta` on the closed half-plane `1 ≤ Re s`. -/
theorem riemannZeta_ne_zero_of_one_le_re' {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- Upper bound for the norm of `deriv riemannZeta / riemannZeta` on `1 < Re s` by its value on
the real axis: `‖ζ'(σ + it) / ζ(σ + it)‖ ≤ Re (-ζ'(σ) / ζ(σ))`. -/
theorem norm_logDeriv_riemannZeta_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) / riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let fΛ : ℕ → ℂ := fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)
  have hs : 1 < s.re := by simp [s, hσ]
  have hneg : ‖deriv riemannZeta s / riemannZeta s‖ = ‖-deriv riemannZeta s / riemannZeta s‖ := by
    rw [neg_div, norm_neg]
  have hs_sum : LSeriesSummable fΛ s :=
    AnalyticNumberTheory.DirichletSeries.LSeriesSummable_vonMangoldt_iff.mpr hs
  have hσ_eq : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
    simpa using re_neg_logDeriv_riemannZeta_eq_tsum (y := 0) hσ
  have hs_abs : Summable fun n : ℕ ↦ ‖LSeries.term fΛ s n‖ := summable_norm_iff.mpr hs_sum
  have hσ_abs : Summable fun n : ℕ ↦
      if n = 0 then (0 : ℝ) else ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
    simpa using summable_vonMangoldt_re (σ := σ) (y := 0) hσ
  rw [hneg, ← AnalyticNumberTheory.DirichletSeries.LSeries_vonMangoldt_eq hs, LSeries, hσ_eq]
  refine (norm_tsum_le_tsum_norm hs_abs).trans ?_
  refine hs_abs.tsum_le_tsum (fun n ↦ ?_) hσ_abs
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  rw [ite_eq_right hn, LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos hn_pos,
    Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    show s.re = σ by simp [s], div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]

/-- Explicit bound on `(-deriv riemannZeta / riemannZeta) (1 + η)` for `0 < η ≤ 1`:
there exists `C₀ > 0` such that `(-deriv riemannZeta (1 + η) / riemannZeta (1 + η)).re ≤ 1 / η + C₀`. -/
theorem neg_logDeriv_riemannZeta_one_add_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ⦃η : ℝ⦄, 0 < η → η ≤ 1 →
      (-deriv riemannZeta ((1 + η : ℝ) : ℂ) / riemannZeta ((1 + η : ℝ) : ℂ)).re ≤ 1 / η + C₀ := by
  let g : ℂ → ℂ := fun z ↦ 1 + (z - 1) * riemannZeta₀ z
  have hg_diff : Differentiable ℂ g :=
    (differentiable_const 1).add ((differentiable_id.sub_const 1).mul differentiable_riemannZeta₀_bridge)
  have hg_eq : ∀ {z : ℂ}, z ≠ 1 → g z = (z - 1) * riemannZeta z := by
    intro z hz
    dsimp only [g]
    rw [← riemannZeta_sub_one_div_eq_riemannZeta₀ hz]
    field_simp [sub_ne_zero.mpr hz]
    ring
  have hg_ne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g ((1 + u : ℝ) : ℂ) ≠ 0 := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hu0
    · simp [g]
    have hu_pos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    have hz1 : ((1 + u : ℝ) : ℂ) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    rw [hg_eq hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re (by simp [hu_pos]))
  have hg_cont : ContinuousOn (fun u : ℝ ↦ ‖logDeriv g ((1 + u : ℝ) : ℂ)‖) (Set.Icc (0 : ℝ) 1) := by
    have hg_eq_ld : ∀ w : ℂ, logDeriv g w = deriv g w / g w := fun w ↦ logDeriv_apply g w
    simp_rw [hg_eq_ld]
    have hderiv_cont : Continuous (deriv g) :=
      continuous_iff_continuousAt.mpr fun w ↦
        (hg_diff.differentiableOn.analyticOnNhd isOpen_univ w (Set.mem_univ w)).deriv.continuousAt
    have hlin : Continuous (fun x : ℝ ↦ ((1 + x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
    have hd_all : Continuous (fun x : ℝ ↦ deriv g ((1 + x : ℝ) : ℂ)) := hderiv_cont.comp hlin
    have hg_all : Continuous (fun x : ℝ ↦ g ((1 + x : ℝ) : ℂ)) := hg_diff.continuous.comp hlin
    refine ContinuousOn.norm fun u hu ↦ ?_
    exact (hd_all.continuousAt.div hg_all.continuousAt (hg_ne u hu)).continuousWithinAt
  obtain ⟨u₀, _, hu₀⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩ hg_cont
  let C₀ : ℝ := max (‖logDeriv g ((1 + u₀ : ℝ) : ℂ)‖) 1
  refine ⟨C₀, by positivity, fun η hη0 hη1 ↦ ?_⟩
  let z : ℂ := ((1 + η : ℝ) : ℂ)
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hev : riemannZeta =ᶠ[𝓝 z] fun w ↦ (w - 1)⁻¹ * g w := by
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    rw [hg_eq hw, inv_mul_cancel_left₀ (sub_ne_zero.mpr hw)]
  have hinv_d : HasDerivAt (fun w : ℂ ↦ (w - 1)⁻¹) (-1 / (z - 1) ^ 2) z :=
    ((hasDerivAt_id' z).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hz1)
  have hmul_d : HasDerivAt (fun w : ℂ ↦ (w - 1)⁻¹ * g w)
      ((-1 / (z - 1) ^ 2) * g z + (z - 1)⁻¹ * deriv g z) z :=
    hinv_d.mul (hg_diff z).hasDerivAt
  have hld_eq : logDeriv riemannZeta z = -(z - 1)⁻¹ + logDeriv g z := by
    rw [logDeriv_apply, hev.deriv_eq, hmul_d.deriv, hev.eq_of_nhds, logDeriv_apply]
    have h1z : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hgz : g z ≠ 0 := hg_ne η ⟨hη0.le, hη1⟩
    field_simp [h1z, hgz]
  have hsub_eq : z - 1 = (η : ℂ) := by simp [z]
  have hneg_eq : -deriv riemannZeta z / riemannZeta z = 1 / (η : ℂ) - logDeriv g z := by
    rw [show -deriv riemannZeta z / riemannZeta z = -(logDeriv riemannZeta z) by
      rw [logDeriv_apply]; ring]
    rw [hld_eq, hsub_eq, one_div]
    ring
  rw [hneg_eq, Complex.sub_re, show (1 / (η : ℂ)).re = 1 / η by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]]
  have hbd : -(logDeriv g z).re ≤ C₀ := by
    calc
      -(logDeriv g z).re = (-logDeriv g z).re := (Complex.neg_re _).symm
      _ ≤ ‖-logDeriv g z‖ := Complex.re_le_norm _
      _ = ‖logDeriv g z‖ := norm_neg _
      _ ≤ ‖logDeriv g ((1 + u₀ : ℝ) : ℂ)‖ := hu₀ ⟨hη0.le, hη1⟩
      _ ≤ C₀ := le_max_left _ _
  linarith

private lemma neg_logDeriv_riemannZeta_re_bound_of_ge_two {σ : ℝ} (hσ : 2 ≤ σ) (t : ℝ) :
    ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) / riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re := by
  refine (norm_logDeriv_riemannZeta_of_one_lt_re (by linarith) t).trans ?_
  have hre₁ : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (0 * Real.log n) := by
    simpa using re_neg_logDeriv_riemannZeta_eq_tsum (σ := σ) (y := 0) (by linarith)
  have hre₂ : (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-2 : ℝ) * Real.cos (0 * Real.log n) := by
    simpa using re_neg_logDeriv_riemannZeta_eq_tsum (σ := 2) (y := 0) (by norm_num)
  rw [hre₁, hre₂]
  refine (summable_vonMangoldt_re (y := 0) (by linarith)).tsum_le_tsum (fun n ↦ ?_)
    (summable_vonMangoldt_re (y := 0) (by norm_num))
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, ↓reduceIte, zero_mul, Real.cos_zero, mul_one]
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) ArithmeticFunction.vonMangoldt_nonneg

/-! ### Thin-Strip Bounds and Compact Neighborhood of `[1 - c₀, 1] × [-T₀, T₀]` -/

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  rw [← Real.exp_lt_exp, Real.exp_log two_pos]
  have hexp1 : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
  have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  nlinarith

private lemma one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

private lemma norm_riemannZeta_thin_strip_le {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hc₀_le : c₀ ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, 2 ≤ |t| → 1 - c₀ / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨Kap, hKap_pos, h_ap⟩ :=
    riemannZeta_approx_dirichletPoly_sub_bound (c := 1) zero_lt_one (by linarith [Real.two_le_pi])
  let E : ℝ := Real.exp (1 / 4 : ℝ)
  have hE_ge1 : 1 ≤ E := by simp [E]
  refine ⟨3 * E + Kap, by positivity, fun σ t ht hσ_low hσ_high ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let N : ℕ := Nat.ceil |t|
  have hN_ge_t : |t| ≤ N := Nat.le_ceil |t|
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  have hN1 : 1 ≤ N := by omega
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
  have hN_ge1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN1
  have ht_le_N : |t| ≤ N := hN_ge_t
  have hN_lt : (N : ℝ) < |t| + 1 := Nat.ceil_lt_add_one (abs_nonneg t)
  have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hlog_pos : 0 < Real.log (|t| + 2) := zero_lt_one.trans_le hlog_ge_one
  have hσ_ge_half : (1 / 2 : ℝ) ≤ σ := by
    have : c₀ / Real.log (|t| + 2) ≤ 1 / 4 := (div_le_self hc₀ hlog_ge_one).trans hc₀_le
    linarith
  have hN_rpow_le : (N : ℝ) ^ (1 - σ) ≤ E := by
    rcases le_or_gt 1 σ with hσ1 | hσ1
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hN_ge1 (by linarith)).trans hE_ge1
    · have hlogN_le : Real.log N ≤ Real.log (|t| + 2) :=
        Real.log_le_log hN_pos (by linarith)
      have hexp_le : (1 - σ) * Real.log N ≤ 1 / 4 := by
        have h1 : 1 - σ ≤ c₀ / Real.log (|t| + 2) := by linarith
        calc
          (1 - σ) * Real.log N ≤ (c₀ / Real.log (|t| + 2)) * Real.log (|t| + 2) :=
            mul_le_mul h1 hlogN_le (Real.log_nonneg hN_ge1) (by positivity)
          _ = c₀ := div_mul_cancel₀ _ hlog_pos.ne'
          _ ≤ 1 / 4 := hc₀_le
      rw [Real.rpow_def_of_pos hN_pos, mul_comm]
      exact Real.exp_le_exp.mpr hexp_le
  have hdir_bd : ‖dirichletPoly (fun _ ↦ 1) N s‖ ≤ E * (1 + Real.log (|t| + 2)) := by
    rw [dirichletPoly]
    calc
      ‖∑ n ∈ Finset.Icc 1 N, (1 : ℂ) * (n : ℂ) ^ (-s)‖
          ≤ ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := by
        refine Finset.sum_congr rfl fun n hn ↦ ?_
        have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
        rw [one_mul, Complex.norm_natCast_cpow_of_pos hn0]
        simp [s]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, E * ((1 : ℝ) / n) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Finset.mem_Icc.mp hn).1
        have hn_pos : (0 : ℝ) < n := by linarith
        have hn_le_N : (n : ℝ) ≤ N := Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2
        have hfac : (n : ℝ) ^ (1 - σ) ≤ E := by
          rcases le_or_gt 1 σ with hσ1 | hσ1
          · exact (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)).trans hE_ge1
          · exact (Real.rpow_le_rpow hn_pos.le hn_le_N (by linarith)).trans hN_rpow_le
        have hmul : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 - σ) * ((1 : ℝ) / n) := by
          rw [one_div, ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn_pos]
          congr 1; ring
        rw [hmul]
        exact mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = E * ∑ n ∈ Finset.Icc 1 N, ((1 : ℝ) / n) := by rw [← Finset.mul_sum]
      _ ≤ E * (1 + Real.log N) := by
        gcongr
        have hha := sum_inv_le_one_add_log (x := (N : ℝ)) hN_ge1
        have hfl : ∑ n ∈ Finset.Icc 1 ⌊(N : ℝ)⌋₊, (n : ℝ)⁻¹ =
            ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
          rw [Nat.floor_natCast]
          refine Finset.sum_congr rfl fun n _ ↦ (one_div (n : ℝ)).symm
        linarith
      _ ≤ E * (1 + Real.log (|t| + 2)) := by
        have hlogN_le_t : Real.log (N : ℝ) ≤ Real.log (|t| + 2) :=
          Real.log_le_log hN_pos (by linarith)
        exact mul_le_mul_of_nonneg_left
          (by linarith : 1 + Real.log (N : ℝ) ≤ 1 + Real.log (|t| + 2)) (by positivity)
  have hap := h_ap hN1 (σ := σ) (t := t) (by linarith) (by linarith : 1 ≤ |t|)
    (by simpa using ht_le_N)
  have hrem_bd : (N : ℝ) ^ (1 - σ) / |t| + Kap * (N : ℝ) ^ (-σ) ≤ E / 2 + Kap := by
    have h1 : (N : ℝ) ^ (1 - σ) / |t| ≤ E / 2 := div_le_div₀ (by positivity) hN_rpow_le two_pos ht
    have h2 : (N : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN_ge1 (by linarith)
    nlinarith [hKap_pos]
  have htri : ‖riemannZeta s‖ ≤
      ‖riemannZeta s - dirichletPoly (fun _ ↦ 1) N s‖ + ‖dirichletPoly (fun _ ↦ 1) N s‖ := by
    calc
      ‖riemannZeta s‖ = ‖(riemannZeta s - dirichletPoly (fun _ ↦ 1) N s) +
          dirichletPoly (fun _ ↦ 1) N s‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  calc
    ‖riemannZeta s‖ ≤ (E / 2 + Kap) + E * (1 + Real.log (|t| + 2)) := by linarith
    _ = E * Real.log (|t| + 2) + (3 / 2 * E + Kap) := by ring
    _ ≤ E * Real.log (|t| + 2) + (2 * E + Kap) * Real.log (|t| + 2) := by
      have hbd1 : 3 / 2 * E + Kap ≤ (2 * E + Kap) * 1 := by linarith
      have hbd2 : (2 * E + Kap) * 1 ≤ (2 * E + Kap) * Real.log (|t| + 2) :=
        mul_le_mul_of_nonneg_left hlog_ge_one (by positivity)
      linarith
    _ = (3 * E + Kap) * Real.log (|t| + 2) := by ring

private lemma exists_riemannZeta_ne_zero_of_abs_im_le (T₀ : ℝ) (hT₀ : 0 ≤ T₀) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ ∀ ⦃σ t : ℝ⦄, |t| ≤ T₀ → 1 - c₀ ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let Rbox : ℝ := T₀ + 2
  have hRbox_pos : 0 < Rbox := by linarith
  have hcont_xi : Continuous (fun t : ℝ ↦ ‖xi ((1 : ℂ) + (t : ℂ) * I)‖) :=
    (differentiable_xi.continuous.comp (by fun_prop)).norm
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    (⟨0, neg_nonpos.mpr hT₀, hT₀⟩ : (Set.Icc (-T₀) T₀).Nonempty) hcont_xi.continuousOn
  let m : ℝ := ‖xi ((1 : ℂ) + (t₀ : ℂ) * I)‖
  have hm_pos : 0 < m := norm_pos_iff.mpr (xi_ne_zero_of_one_le_re (by simp))
  have hd_cont : Continuous (fun z : ℂ ↦ ‖deriv xi z‖) := by
    have hca : ∀ z : ℂ, ContinuousAt (deriv xi) z := fun z ↦
      (analyticOnNhd_xi z (Set.mem_univ z)).deriv.continuousAt
    exact (continuous_iff_continuousAt.mpr hca).norm
  obtain ⟨zD, _, hzD_max⟩ := (isCompact_closedBall (0 : ℂ) Rbox).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hRbox_pos.le) hd_cont.continuousOn
  let D : ℝ := max ‖deriv xi zD‖ 1
  have hD_pos : 0 < D := by positivity
  let c₀ : ℝ := min (1 / 4) (m / (2 * D))
  refine ⟨c₀, by positivity, min_le_left _ _, fun σ t ht hσ ↦ ?_⟩
  rcases le_or_gt 1 σ with hσ1 | hσ1
  · exact riemannZeta_ne_zero_of_one_le_re (by simp [hσ1])
  have hc₀_le : c₀ ≤ m / (2 * D) := min_le_right _ _
  have hc₀_quarter : c₀ ≤ 1 / 4 := min_le_left _ _
  have hσ_pos : 0 < σ := by linarith
  have hmem_t : t ∈ Set.Icc (-T₀) T₀ := abs_le.mp ht
  have hm_le : m ≤ ‖xi ((1 : ℂ) + (t : ℂ) * I)‖ := ht₀_min hmem_t
  have hderiv_bd : ∀ u ∈ Set.Icc σ 1, ‖deriv xi ((u : ℂ) + (t : ℂ) * I)‖ ≤ D := by
    intro u hu
    have hu_mem : (u : ℂ) + (t : ℂ) * I ∈ Metric.closedBall (0 : ℂ) Rbox := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖(u : ℂ) + (t : ℂ) * I‖ ≤ ‖(u : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |u| + |t| := by simp
        _ ≤ 1 + T₀ := add_le_add (abs_le.mpr ⟨by linarith [hu.1], hu.2⟩) ht
        _ ≤ Rbox := by linarith
    exact (hzD_max hu_mem).trans (le_max_left _ _)
  have hhasDeriv : ∀ u ∈ Set.uIcc σ 1,
      HasDerivAt (fun x : ℝ ↦ xi ((x : ℂ) + (t : ℂ) * I))
        (deriv xi ((u : ℂ) + (t : ℂ) * I)) u := by
    intro u _
    have hxi : HasDerivAt xi (deriv xi ((u : ℂ) + (t : ℂ) * I)) ((u : ℂ) + (t : ℂ) * I) :=
      (differentiable_xi _).hasDerivAt
    have htr : HasDerivAt (fun z : ℂ ↦ z + (t : ℂ) * I) 1 (u : ℂ) :=
      (hasDerivAt_id' (u : ℂ)).add_const ((t : ℂ) * I)
    have hcomp : HasDerivAt (xi ∘ fun z : ℂ ↦ z + (t : ℂ) * I)
        (deriv xi ((u : ℂ) + (t : ℂ) * I) * 1) (u : ℂ) := hxi.comp (u : ℂ) htr
    rw [mul_one] at hcomp
    exact hcomp.comp_ofReal
  have hint_eq :
      ∫ u in σ..1, deriv xi ((u : ℂ) + (t : ℂ) * I) =
        xi ((1 : ℂ) + (t : ℂ) * I) - xi ((σ : ℂ) + (t : ℂ) * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt hhasDeriv
    refine ContinuousOn.intervalIntegrable ?_
    have hc_deriv : Continuous (deriv xi) :=
      continuous_iff_continuousAt.mpr fun z ↦
        (analyticOnNhd_xi z (Set.mem_univ z)).deriv.continuousAt
    have hc : Continuous (fun u : ℝ ↦ deriv xi ((u : ℂ) + (t : ℂ) * I)) :=
      hc_deriv.comp (Complex.continuous_ofReal.add continuous_const)
    exact hc.continuousOn
  have hdiff_le : ‖xi ((1 : ℂ) + (t : ℂ) * I) - xi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ m / 2 := by
    rw [← hint_eq]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := 1) (C := D)
      fun u hu ↦ by
        rw [Set.uIoc_of_le hσ1.le] at hu
        exact hderiv_bd u ⟨hu.1.le, hu.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hσ1.le)] at hbd
    calc
      ‖∫ u in σ..1, deriv xi ((u : ℂ) + (t : ℂ) * I)‖ ≤ D * (1 - σ) := hbd
      _ ≤ D * (m / (2 * D)) := mul_le_mul_of_nonneg_left (by linarith) hD_pos.le
      _ = m / 2 := by field_simp [hD_pos.ne']
  have hxi_ne : xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h0
    rw [h0, sub_zero] at hdiff_le
    linarith
  intro hz0
  exact hxi_ne (xi_eq_zero_iff.mpr ⟨hz0, by simp [hσ_pos], by simp [hσ1]⟩)

/-! ### Classical de la Vallée Poussin Zero-Free Region -/

private lemma de_la_vallee_poussin_ratio_const :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ⦃η t : ℝ⦄, 0 < η → η ≤ 1 / 4 → 4 ≤ |t| → ∀ ⦃k : ℕ⦄, k = 1 ∨ k = 2 →
      let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I
      AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ 1) ∧
        riemannZeta z₀ ≠ 0 ∧
        ∀ w ∈ Metric.sphere z₀ 1,
          ‖riemannZeta w / riemannZeta z₀‖ ≤ Real.exp (K * Real.log |t|) / η := by
  obtain ⟨Cs, hCs_pos, hCs_bd⟩ := norm_riemannZeta_critical_strip_le (ε := 1 / 2) (by norm_num)
  obtain ⟨C₁, hC₁_pos, hbd₁⟩ := norm_riemannZeta_re_ge_one_le
  let Cw : ℝ := max (4 * max Cs C₁) 1
  have hCw_pos : 0 < Cw := by positivity
  let B : ℝ := max (2 * Cw) 1
  let K : ℝ := max (Real.log B + 1) 1
  refine ⟨K, le_max_right _ _, fun η t hη_pos hη_le ht k hk ↦ ?_⟩
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I
  change AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ 1) ∧
    riemannZeta z₀ ≠ 0 ∧
    ∀ w ∈ Metric.sphere z₀ 1,
      ‖riemannZeta w / riemannZeta z₀‖ ≤ Real.exp (K * Real.log |t|) / η
  have h_im_lb : ∀ w ∈ Metric.closedBall z₀ 1, 2 ≤ |w.im| := by
    intro w hw
    have hw_im : |w.im - z₀.im| ≤ 1 := by
      have hdist : ‖w - z₀‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      exact (Complex.abs_im_le_norm (w - z₀)).trans hdist
    have hz₀_im : |z₀.im| = (k : ℝ) * |t| := by
      simp only [z₀, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
    have hk1 : (1 : ℝ) ≤ k := by rcases hk with rfl | rfl <;> norm_num
    have hkz : |t| ≤ |z₀.im| := by
      rw [hz₀_im]
      nlinarith [abs_nonneg t]
    have him_ge : |z₀.im| - 1 ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub z₀.im w.im
      rw [abs_sub_comm] at this
      linarith
    linarith
  have han : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ 1) := by
    have hdiff_compl : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    have han_compl : AnalyticOnNhd ℂ riemannZeta {w : ℂ | w ≠ 1} :=
      hdiff_compl.analyticOnNhd isOpen_ne
    refine han_compl.mono fun w hw ↦ ?_
    intro h
    have h2 := h_im_lb w hw
    rw [h, Complex.one_im, abs_zero] at h2
    linarith
  have hz₀_re : 1 < z₀.re := by simp [z₀, hη_pos]
  have hz₀_ne : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz₀_re
  refine ⟨han, hz₀_ne, fun w hw ↦ ?_⟩
  have hw_cb : w ∈ Metric.closedBall z₀ 1 := Metric.sphere_subset_closedBall hw
  have hw_im2 : 2 ≤ |w.im| := h_im_lb w hw_cb
  have hw_im_ub : |w.im| + 2 ≤ 2 * (|t| + 2) := by
    have hw_im : |w.im - z₀.im| ≤ 1 := by
      have hdist : ‖w - z₀‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw_cb
      exact (Complex.abs_im_le_norm (w - z₀)).trans hdist
    have hz₀_im : |z₀.im| ≤ 2 * |t| := by
      simp only [z₀, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
      rcases hk with rfl | rfl <;> push_cast <;> linarith [abs_nonneg t]
    have : |w.im| ≤ |z₀.im| + 1 := by
      have := abs_sub_abs_le_abs_sub w.im z₀.im
      linarith
    linarith
  have hw_re_nonneg : 0 ≤ w.re := by
    have hre : |w.re - z₀.re| ≤ 1 := by
      have hdist : ‖w - z₀‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw_cb
      exact (Complex.abs_re_le_norm (w - z₀)).trans hdist
    have hzre : z₀.re = 1 + η := by simp [z₀]
    linarith [(abs_le.mp hre).1]
  have hw_norm_bd : ‖riemannZeta w‖ ≤ Cw * |t| := by
    have h2t : 2 * (|t| + 2) ≤ 4 * |t| := by linarith
    have hw_eq : riemannZeta w = riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I) := by
      congr 1; exact (Complex.re_add_im w).symm
    rcases le_or_gt w.re 1 with hw1 | hw1
    · rw [hw_eq]
      have hstrip := hCs_bd ⟨hw_re_nonneg, hw1⟩ (by linarith : 1 ≤ |w.im|)
      have hexp_le : (1 - w.re) / 2 + 1 / 2 ≤ 1 := by linarith
      have hpow_le : (|w.im| + 2) ^ ((1 - w.re) / 2 + 1 / 2) ≤ |w.im| + 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ |w.im| + 2) hexp_le
      calc
        ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
            ≤ Cs * (|w.im| + 2) ^ ((1 - w.re) / 2 + 1 / 2) := hstrip
        _ ≤ Cs * (|w.im| + 2) := mul_le_mul_of_nonneg_left hpow_le hCs_pos.le
        _ ≤ (max Cs C₁) * (4 * |t|) := mul_le_mul (le_max_left _ _) (hw_im_ub.trans h2t)
          (by positivity) (by positivity)
        _ = (4 * max Cs C₁) * |t| := by ring
        _ ≤ Cw * |t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t)
    · rw [hw_eq]
      have hge := hbd₁ hw1.le hw_im2
      have hlog_le : Real.log (|w.im| + 2) ≤ |w.im| + 2 := by
        have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < |w.im| + 2)
        linarith
      calc
        ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
            ≤ C₁ * Real.log (|w.im| + 2) := hge
        _ ≤ C₁ * (|w.im| + 2) := mul_le_mul_of_nonneg_left hlog_le hC₁_pos.le
        _ ≤ (max Cs C₁) * (4 * |t|) := mul_le_mul (le_max_right _ _) (hw_im_ub.trans h2t)
          (by positivity) (by positivity)
        _ = (4 * max Cs C₁) * |t| := by ring
        _ ≤ Cw * |t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t)
  have hz₀_lb : η / 2 ≤ ‖riemannZeta z₀‖ := by
    have hge := norm_riemannZeta_ge_of_one_lt_re (σ := 1 + η) (by linarith) ((k : ℝ) * t)
    have hz₀_eq : ((1 + η : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I = z₀ := rfl
    rw [hz₀_eq] at hge
    have hfrac : η / 2 ≤ (1 + η - 1) / (1 + η) := by
      rw [show 1 + η - 1 = η by ring]
      exact div_le_div_of_nonneg_left hη_pos.le (by linarith) (by linarith)
    exact hfrac.trans hge
  have hlog_lt : 1 < Real.log |t| :=
    lt_of_lt_of_le one_lt_log_four (Real.log_le_log (by norm_num) ht)
  have hB_ge1 : 1 ≤ B := le_max_right _ _
  have hexp_ge : 2 * Cw * |t| ≤ Real.exp (K * Real.log |t|) := by
    rw [← Real.log_le_iff_le_exp (by positivity)]
    calc
      Real.log (2 * Cw * |t|) ≤ Real.log (B * |t|) :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t))
      _ = Real.log B + Real.log |t| := Real.log_mul (by positivity) (by linarith)
      _ ≤ Real.log B * Real.log |t| + Real.log |t| := by
        nlinarith [Real.log_nonneg hB_ge1]
      _ = (Real.log B + 1) * Real.log |t| := by ring
      _ ≤ K * Real.log |t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  rw [norm_div]
  calc
    ‖riemannZeta w‖ / ‖riemannZeta z₀‖ ≤ (Cw * |t|) / (η / 2) :=
      div_le_div₀ (by positivity) hw_norm_bd (by positivity) hz₀_lb
    _ = (2 * Cw * |t|) / η := by ring
    _ ≤ Real.exp (K * Real.log |t|) / η := div_le_div_of_nonneg_right hexp_ge hη_pos.le

private lemma mul_log_inv_le_two_sqrt {u : ℝ} (hu : 0 < u) :
    u * Real.log (1 / u) ≤ 2 * Real.sqrt u := by
  have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsq : 1 / u = (1 / Real.sqrt u) ^ 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt hu.le]
  have hlog : Real.log (1 / u) ≤ 2 / Real.sqrt u := by
    rw [hsq, Real.log_pow, Nat.cast_ofNat]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / Real.sqrt u)
    linarith [show 2 * (1 / Real.sqrt u) = 2 / Real.sqrt u by ring]
  calc
    u * Real.log (1 / u) ≤ u * (2 / Real.sqrt u) := mul_le_mul_of_nonneg_left hlog hu.le
    _ = 2 * Real.sqrt u := by
      have hmul : u = Real.sqrt u * Real.sqrt u := (Real.mul_self_sqrt hu.le).symm
      nth_rw 1 [hmul]
      field_simp [hsqrt_pos.ne']

/-- **de la Vallée Poussin Zero-Free Region** (`2 ≤ |t|` logarithmic form):
there exists `c ∈ (0, 1/4)` such that `riemannZeta (σ + t * I) ≠ 0` whenever
`2 ≤ |t|` and `1 - c / Real.log |t| ≤ σ`. -/
theorem de_la_vallee_poussin_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 4 ∧ ∀ ⦃σ t : ℝ⦄, 2 ≤ |t| → 1 - c / Real.log |t| ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  obtain ⟨c₀, hc₀_pos, _, hc₀_bd⟩ := exists_riemannZeta_ne_zero_of_abs_im_le 4 (by norm_num)
  obtain ⟨C₀, hC₀_pos, hC₀_bd⟩ := neg_logDeriv_riemannZeta_one_add_le
  obtain ⟨K, hK_ge1, hK_bd⟩ := de_la_vallee_poussin_ratio_const
  let Ktot : ℝ := 20 * (K + 1) + 3 * C₀
  have hKtot_pos : 0 < Ktot := by positivity
  let cη : ℝ := min (1 / 4) (min (1 / (8 * Ktot)) (1 / (320 * 320 : ℝ)))
  have hcη_pos : 0 < cη := by positivity
  have hcη_le_quarter : cη ≤ 1 / 4 := min_le_left _ _
  have hcη_le_K : cη ≤ 1 / (8 * Ktot) := (min_le_right _ _).trans (min_le_left _ _)
  have hcη_le_sq : cη ≤ 1 / (320 * 320 : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  let c : ℝ := min (cη / 10) (min (c₀ * Real.log 2) ((1 / 5) * Real.log 4))
  have hc_pos : 0 < c := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hc_lt_quarter : c < 1 / 4 := by
    have h1 : c ≤ cη / 10 := min_le_left _ _
    linarith
  have hc_lt_313 : c < 3 * cη / 13 := by
    have h1 : c ≤ cη / 10 := min_le_left _ _
    linarith
  refine ⟨c, hc_pos, hc_lt_quarter, fun σ t ht hσ_low ↦ ?_⟩
  rcases le_or_gt 1 σ with hσ1 | hσ1
  · exact riemannZeta_ne_zero_of_one_le_re (by simp [hσ1])
  rcases le_or_gt |t| 4 with ht4 | ht4
  · have hlog_le : Real.log 2 ≤ Real.log |t| := Real.log_le_log two_pos ht
    have hc_le : c ≤ c₀ * Real.log 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hlow : 1 - c₀ ≤ σ := by
      have : c / Real.log |t| ≤ c₀ := by
        calc
          c / Real.log |t| ≤ (c₀ * Real.log 2) / Real.log 2 :=
            div_le_div₀ (by positivity) hc_le (Real.log_pos one_lt_two) hlog_le
          _ = c₀ := mul_div_cancel_right₀ _ (Real.log_pos one_lt_two).ne'
      linarith
    exact hc₀_bd ht4 hlow
  have hlogt_gt1 : 1 < Real.log |t| :=
    lt_of_lt_of_le one_lt_log_four (Real.log_le_log (by norm_num) ht4.le)
  have hlogt_pos : 0 < Real.log |t| := zero_lt_one.trans hlogt_gt1
  have hσ_ge : 3 / 4 ≤ σ := by
    have hc_log4 : c ≤ (1 / 5) * Real.log 4 := (min_le_right _ _).trans (min_le_right _ _)
    have hlog_le : Real.log 4 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht4.le
    have : c / Real.log |t| ≤ 1 / 5 := by
      calc
        c / Real.log |t| ≤ ((1 / 5) * Real.log 4) / Real.log 4 :=
          div_le_div₀ (by positivity) hc_log4 (by positivity) hlog_le
        _ = 1 / 5 := mul_div_cancel_right₀ _ (by positivity)
    linarith
  intro hzero
  let η : ℝ := cη / Real.log |t|
  have hη_pos : 0 < η := div_pos hcη_pos hlogt_pos
  have hη_le : η ≤ 1 / 4 := (div_le_self hcη_pos.le hlogt_gt1.le).trans hcη_le_quarter
  let ρ : ℂ := (σ : ℂ) + (t : ℂ) * I
  let z₁ : ℂ := ((1 + η : ℝ) : ℂ) + (t : ℂ) * I
  let z₂ : ℂ := ((1 + η : ℝ) : ℂ) + (((2 : ℝ) * t : ℝ) : ℂ) * I
  obtain ⟨han₁, hz₁_ne, hM₁_bd⟩ := hK_bd hη_pos hη_le ht4.le (k := 1) (Or.inl rfl)
  obtain ⟨han₂, hz₂_ne, hM₂_bd⟩ := hK_bd hη_pos hη_le ht4.le (k := 2) (Or.inr rfl)
  simp only [Nat.cast_one, one_mul] at han₁ hz₁_ne hM₁_bd
  simp only [Nat.cast_ofNat] at han₂ hz₂_ne hM₂_bd
  let M : ℝ := Real.exp (K * Real.log |t|) / η
  have hM_pos : 0 < M := by positivity
  have hz_re_le : ∀ (z₀ : ℂ), 1 < z₀.re →
      ∀ w ∈ Metric.closedBall z₀ (1 / 2 : ℝ), riemannZeta w = 0 → w.re ≤ z₀.re := by
    intro z₀ hz₀ w _ hw0
    by_contra! hgt
    have hw1 : 1 ≤ w.re := by linarith
    exact riemannZeta_ne_zero_of_one_le_re hw1 hw0
  have hρ_mem : ρ ∈ Metric.closedBall z₁ (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : ρ - z₁ = (((σ - (1 + η) : ℝ) : ℂ)) := by
      simp only [ρ, z₁]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hre₁ := landau_neg_re_logDeriv_center_le_sub_zero (R := 1) zero_lt_one han₁ hz₁_ne
    hM₁_bd (hz_re_le z₁ (by simp [z₁, hη_pos])) hρ_mem hzero
  have hre₂ := landau_neg_re_logDeriv_center_le (R := 1) zero_lt_one han₂ hz₂_ne
    hM₂_bd (hz_re_le z₂ (by simp [z₂, hη_pos]))
  have hre₀ := hC₀_bd hη_pos (by linarith)
  have h341 := three_neg_logDeriv_add_four_add_nonneg (σ := 1 + η) (by linarith) t
  have hinv_eq : ((z₁ - ρ)⁻¹).re = 1 / (1 + η - σ) := by
    have hdiff : z₁ - ρ = (((1 + η - σ : ℝ) : ℂ)) := by
      simp only [ρ, z₁]; push_cast; ring
    rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hneg_ld_eq : ∀ z : ℂ, -(logDeriv riemannZeta z).re =
      (-deriv riemannZeta z / riemannZeta z).re := fun z ↦ by
    rw [logDeriv_apply, neg_div, Complex.neg_re]
  rw [hneg_ld_eq, hinv_eq] at hre₁
  rw [hneg_ld_eq] at hre₂
  have hz₂_eq : (((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
      (((1 + η : ℝ) : ℂ) + 2 * (t : ℂ) * I) := by
    push_cast; ring
  rw [hz₂_eq] at hre₂
  have hlogM_le : Real.log M ≤ (K + 1) * Real.log |t| + Real.log (1 / cη) := by
    dsimp only [M, η]
    have hdiv_eq : Real.exp (K * Real.log |t|) / (cη / Real.log |t|) =
        Real.exp (K * Real.log |t|) * Real.log |t| * (1 / cη) := by
      field_simp [hcη_pos.ne', hlogt_pos.ne']
    rw [hdiv_eq, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hlogt_pos.ne', Real.log_exp]
    have hloglog : Real.log (Real.log |t|) ≤ Real.log |t| := by
      have h := Real.log_le_sub_one_of_pos hlogt_pos
      linarith
    linarith
  have hcomb : 4 / (1 + η - σ) ≤ 3 / η + (Ktot + 20 * Real.log (1 / cη)) * Real.log |t| := by
    have hM_eq : M = Real.exp (K * Real.log |t|) / η := rfl
    have h1 : 3 * (-deriv riemannZeta ((1 + η : ℝ) : ℂ) /
        riemannZeta ((1 + η : ℝ) : ℂ)).re ≤ 3 / η + 3 * C₀ := by
      calc
        3 * (-deriv riemannZeta ((1 + η : ℝ) : ℂ) /
            riemannZeta ((1 + η : ℝ) : ℂ)).re ≤ 3 * (1 / η + C₀) :=
          mul_le_mul_of_nonneg_left hre₀ (by norm_num)
        _ = 3 / η + 3 * C₀ := by ring
    have h2 : 4 * (-deriv riemannZeta (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)).re ≤
        16 * Real.log M - 4 / (1 + η - σ) := by
      have hre₁' : (-deriv riemannZeta (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) /
          riemannZeta (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)).re ≤
          4 * Real.log M - 1 / (1 + η - σ) := by
        simpa only [← hM_eq, div_one] using hre₁
      calc
        4 * (-deriv riemannZeta (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) /
            riemannZeta (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)).re
            ≤ 4 * (4 * Real.log M - 1 / (1 + η - σ)) :=
          mul_le_mul_of_nonneg_left hre₁' (by norm_num)
        _ = 16 * Real.log M - 4 / (1 + η - σ) := by ring
    have h3 : (-deriv riemannZeta (((1 + η : ℝ) : ℂ) + 2 * (t : ℂ) * I) /
        riemannZeta (((1 + η : ℝ) : ℂ) + 2 * (t : ℂ) * I)).re ≤ 4 * Real.log M := by
      simpa only [← hM_eq, div_one] using hre₂
    have h20M : 20 * Real.log M ≤
        20 * (K + 1) * Real.log |t| + 20 * Real.log (1 / cη) * Real.log |t| := by
      have hcη_lt1 : cη ≤ 1 := hcη_le_quarter.trans (by norm_num)
      have hlog_inv_nn : 0 ≤ Real.log (1 / cη) := Real.log_nonneg (one_le_one_div hcη_pos hcη_lt1)
      have hmul_log : 20 * Real.log (1 / cη) ≤ 20 * Real.log (1 / cη) * Real.log |t| := by
        nlinarith [hlogt_gt1]
      linarith
    have hC0_le : 3 * C₀ ≤ 3 * C₀ * Real.log |t| := by nlinarith [hlogt_gt1]
    have hsum_all : 4 / (1 + η - σ) ≤ 3 / η + 3 * C₀ + 20 * Real.log M := by linarith
    calc
      4 / (1 + η - σ) ≤ 3 / η + 3 * C₀ + 20 * Real.log M := hsum_all
      _ ≤ 3 / η + 3 * C₀ * Real.log |t| +
          (20 * (K + 1) * Real.log |t| + 20 * Real.log (1 / cη) * Real.log |t|) := by linarith
      _ = 3 / η + (Ktot + 20 * Real.log (1 / cη)) * Real.log |t| := by
        simp only [Ktot]; ring
  have hcη_small : (Ktot + 20 * Real.log (1 / cη)) * cη ≤ 1 / 4 := by
    have hK_part : Ktot * cη ≤ 1 / 8 := by
      calc
        Ktot * cη ≤ Ktot * (1 / (8 * Ktot)) := mul_le_mul_of_nonneg_left hcη_le_K hKtot_pos.le
        _ = 1 / 8 := by field_simp [hKtot_pos.ne']
    have hsqrt_le : Real.sqrt cη ≤ 1 / 320 := by
      have hsq : (1 / 320 : ℝ) ^ 2 = 1 / (320 * 320 : ℝ) := by norm_num
      rw [← hsq] at hcη_le_sq
      simpa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / 320)] using Real.sqrt_le_sqrt hcη_le_sq
    have hlog_part : 20 * (cη * Real.log (1 / cη)) ≤ 1 / 8 := by
      calc
        20 * (cη * Real.log (1 / cη)) ≤ 20 * (2 * Real.sqrt cη) :=
          mul_le_mul_of_nonneg_left (mul_log_inv_le_two_sqrt hcη_pos) (by norm_num)
        _ = 40 * Real.sqrt cη := by ring
        _ ≤ 40 * (1 / 320) := by linarith
        _ = 1 / 8 := by norm_num
    linarith
  have hcomb2 : 4 / (1 + η - σ) ≤ (13 / 4) / η := by
    have hlog_eq : Real.log |t| = cη / η := by
      dsimp only [η]
      field_simp [hcη_pos.ne', hlogt_pos.ne']
    have hmul_eq : (Ktot + 20 * Real.log (1 / cη)) * Real.log |t| =
        ((Ktot + 20 * Real.log (1 / cη)) * cη) / η := by
      rw [hlog_eq]; ring
    have hfrac : ((Ktot + 20 * Real.log (1 / cη)) * cη) / η ≤ (1 / 4) / η :=
      div_le_div_of_nonneg_right hcη_small hη_pos.le
    have h314 : 3 / η + (1 / 4) / η = (13 / 4) / η := by ring
    linarith
  have hden_pos : 0 < 1 + η - σ := by linarith
  have hinv_ineq : (16 : ℝ) / 13 * η ≤ 1 + η - σ := by
    rw [div_le_div_iff₀ hden_pos hη_pos] at hcomb2
    linarith
  have h1sub : (3 * cη / 13) / Real.log |t| ≤ 1 - σ := by
    have heq : (3 * cη / 13) / Real.log |t| = (3 / 13 : ℝ) * η := by
      dsimp only [η]; ring
    rw [heq]
    linarith [hinv_ineq]
  have hc_lt : c / Real.log |t| < 1 - σ := by
    have h1 : c / Real.log |t| < (3 * cη / 13) / Real.log |t| :=
      div_lt_div_of_pos_right hc_lt_313 hlogt_pos
    exact h1.trans_le h1sub
  linarith

/-- **Zero-Free Region** in global `Real.log (|t| + 2)` form:
there exists `c ∈ (0, 1/4)` such that `riemannZeta (σ + t * I) ≠ 0` whenever
`1 - c / Real.log (|t| + 2) ≤ σ`. -/
theorem riemannZeta_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 4 ∧ ∀ ⦃σ t : ℝ⦄, 1 - c / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  obtain ⟨c₁, hc₁_pos, hc₁_lt, hc₁_bd⟩ := de_la_vallee_poussin_zero_free_region
  obtain ⟨c₀, hc₀_pos, _, hc₀_bd⟩ := exists_riemannZeta_ne_zero_of_abs_im_le 2 (by norm_num)
  let c : ℝ := min c₁ (c₀ * Real.log 2)
  refine ⟨c, by positivity, lt_of_le_of_lt (min_le_left _ _) hc₁_lt, fun σ t hσ ↦ ?_⟩
  rcases le_or_gt |t| 2 with ht2 | ht2
  · have hlog2_le : Real.log 2 ≤ Real.log (|t| + 2) :=
      Real.log_le_log two_pos (by linarith [abs_nonneg t])
    have hc_le : c ≤ c₀ * Real.log 2 := min_le_right _ _
    have hlow : 1 - c₀ ≤ σ := by
      have : c / Real.log (|t| + 2) ≤ c₀ := by
        calc
          c / Real.log (|t| + 2) ≤ (c₀ * Real.log 2) / Real.log 2 :=
            div_le_div₀ (by positivity) hc_le (Real.log_pos one_lt_two) hlog2_le
          _ = c₀ := mul_div_cancel_right₀ _ (Real.log_pos one_lt_two).ne'
      linarith
    exact hc₀_bd ht2 hlow
  · have hc_le : c ≤ c₁ := min_le_left _ _
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlow : 1 - c₁ / Real.log |t| ≤ σ := by
      have : c / Real.log (|t| + 2) ≤ c₁ / Real.log |t| :=
        div_le_div₀ (by positivity) hc_le (Real.log_pos (by linarith)) hlog_le
      linarith
    exact hc₁_bd ht2.le hlow

/-! ### Effective Bounds on `deriv riemannZeta / riemannZeta` and `(riemannZeta)⁻¹` -/

private lemma thin_strip_disk_bounds {c_zfr : ℝ} (hc_pos : 0 < c_zfr) (hc_lt : c_zfr < 1 / 4)
    (hzfr : ∀ ⦃σ t : ℝ⦄, 1 - c_zfr / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, 4 ≤ |t| →
      1 - (c_zfr / 20) / Real.log (|t| + 2) ≤ σ →
      σ ≤ 1 + (c_zfr / 20) / Real.log (|t| + 2) →
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2 ∧
        ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨Cem, hCem_pos, hCem_bd⟩ := norm_riemannZeta_thin_strip_le (c₀ := 1 / 4) (by norm_num) le_rfl
  let c₂ : ℝ := c_zfr / 20
  let c₁ : ℝ := c_zfr / 2
  have hc₂_pos : 0 < c₂ := by positivity
  have hc₁_pos : 0 < c₁ := by positivity
  let K : ℝ := max (4 * Cem / c₂) 1
  let B_ld : ℝ := (26 / (81 * c₂)) * (Real.log K + 2)
  let B_inv : ℝ := (2 / c₂) * Real.sqrt K
  let C : ℝ := max B_ld B_inv + 1
  refine ⟨C, by positivity, fun σ t ht hσ_low hσ_high ↦ ?_⟩
  let logT : ℝ := Real.log (|t| + 2)
  have hL_gt1 : 1 < logT := lt_trans one_lt_log_four (Real.log_lt_log (by norm_num) (by linarith))
  have hL_pos : 0 < logT := zero_lt_one.trans hL_gt1
  let η : ℝ := c₂ / logT
  let R : ℝ := (c₁ + c₂) / logT
  let r : ℝ := 2 * c₂ / logT
  have hη_pos : 0 < η := div_pos hc₂_pos hL_pos
  have hR_pos : 0 < R := div_pos (by positivity) hL_pos
  have hr_pos : 0 < r := div_pos (by positivity) hL_pos
  have hR_lt1 : R < 1 := by
    have hnum : c₁ + c₂ < 1 / 4 := by dsimp [c₁, c₂]; linarith
    calc
      R = (c₁ + c₂) / logT := rfl
      _ < (1 / 4) / 1 := div_lt_div₀ hnum hL_gt1.le (by norm_num) zero_lt_one
      _ = 1 / 4 := by norm_num
      _ < 1 := by norm_num
  have hrR : r < R := by
    dsimp [r, R, c₁, c₂]
    exact div_lt_div_of_pos_right (by linarith) hL_pos
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (t : ℂ) * I
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs_mem : s ∈ Metric.closedBall z₀ r := by
    change 1 - c₂ / logT ≤ σ at hσ_low
    change σ ≤ 1 + c₂ / logT at hσ_high
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : s - z₀ = (((σ - (1 + η) : ℝ) : ℂ)) := by
      simp only [s, z₀]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hr_eq : r = 2 * (c₂ / logT) := by dsimp [r]; ring
    rw [hr_eq]
    constructor <;> · dsimp [η]; linarith
  have hw_prop : ∀ w ∈ Metric.ball z₀ R,
      w ≠ 1 ∧ 2 ≤ |w.im| ∧ |w.im| + 2 ≤ (|t| + 2) ^ 2 ∧
      1 - (1 / 4) / Real.log (|w.im| + 2) ≤ w.re ∧ w.re ≤ 2 ∧
      1 - c_zfr / Real.log (|w.im| + 2) ≤ w.re := by
    intro w hw
    have hw_dist : ‖w - z₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw_im_diff : |w.im - t| < 1 := by
      have him : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have hz₀_im : z₀.im = t := by simp [z₀]
      rw [hz₀_im] at him
      linarith
    have hw_im2 : 2 ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub t w.im
      rw [abs_sub_comm] at this
      linarith
    have hw_im_sq : |w.im| + 2 ≤ (|t| + 2) ^ 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have hub : |w.im| + 2 ≤ |t| + 3 := by linarith
      nlinarith
    have hw_log_le : Real.log (|w.im| + 2) ≤ 2 * logT := by
      have h1 := Real.log_le_log (by positivity : 0 < |w.im| + 2) hw_im_sq
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hw_re_diff : |w.re - z₀.re| < R := by
      have hre : |w.re - z₀.re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
      linarith
    have hz₀_re : z₀.re = 1 + η := by simp [z₀]
    have hw_re_lb : 1 - c₁ / logT ≤ w.re := by
      have h1 : z₀.re - R < w.re := by linarith [(abs_lt.mp hw_re_diff).1]
      have heq : 1 + η - R = 1 - c₁ / logT := by dsimp [η, R]; ring
      linarith
    have hw_re_ub : w.re ≤ 2 := by
      have h1 : w.re < z₀.re + R := by linarith [(abs_lt.mp hw_re_diff).2]
      have hR1 : η + R < 1 := by
        have hnum : c₂ + (c₁ + c₂) < 1 := by dsimp [c₁, c₂]; linarith
        dsimp [η, R]
        calc
          c₂ / logT + (c₁ + c₂) / logT = (c₂ + (c₁ + c₂)) / logT := by ring
          _ < 1 / 1 := div_lt_div₀ hnum hL_gt1.le zero_le_one zero_lt_one
          _ = 1 := by norm_num
      linarith
    have hw_zfr : 1 - c_zfr / Real.log (|w.im| + 2) ≤ w.re := by
      have hfrac : c₁ / logT ≤ c_zfr / Real.log (|w.im| + 2) := by
        have heq : c₁ / logT = c_zfr / (2 * logT) := by dsimp [c₁]; ring
        rw [heq]
        exact div_le_div_of_nonneg_left hc_pos.le (Real.log_pos (by linarith)) hw_log_le
      linarith
    have hw_quarter : 1 - (1 / 4) / Real.log (|w.im| + 2) ≤ w.re := by
      have hfrac : c_zfr / Real.log (|w.im| + 2) ≤ (1 / 4) / Real.log (|w.im| + 2) :=
        div_le_div_of_nonneg_right hc_lt.le (Real.log_nonneg (by linarith))
      linarith
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, Complex.one_im, abs_zero] at hw_im2
      linarith
    exact ⟨hw1, hw_im2, hw_im_sq, hw_quarter, hw_re_ub, hw_zfr⟩
  have hf_diff : DifferentiableOn ℂ riemannZeta (Metric.ball z₀ R) := fun w hw ↦
    (differentiableAt_riemannZeta (hw_prop w hw).1).differentiableWithinAt
  have hf_ne : ∀ w ∈ Metric.ball z₀ R, riemannZeta w ≠ 0 := by
    intro w hw
    have hw_eq : riemannZeta w = riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I) := by
      congr 1; exact (Complex.re_add_im w).symm
    rw [hw_eq]
    exact hzfr (hw_prop w hw).2.2.2.2.2
  let M : ℝ := K * logT ^ 2
  have hM_ge1 : 1 ≤ M := by
    have hK1 : 1 ≤ K := le_max_right _ _
    have hL1 : 1 ≤ logT ^ 2 := by nlinarith [hL_gt1]
    exact one_le_mul_of_one_le_of_one_le hK1 hL1
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_ge1
  have hz₀_lb : η / 2 ≤ ‖riemannZeta z₀‖ := by
    have hη_lt1 : η < 1 := by
      have : c₂ < 1 := by dsimp [c₂]; linarith
      calc
        η = c₂ / logT := rfl
        _ < 1 / 1 := div_lt_div₀ this hL_gt1.le zero_le_one zero_lt_one
        _ = 1 := by norm_num
    have hge := norm_riemannZeta_ge_of_one_lt_re (σ := 1 + η) (by linarith) t
    have hz₀_eq : ((1 + η : ℝ) : ℂ) + (t : ℂ) * I = z₀ := rfl
    rw [hz₀_eq] at hge
    have hfrac : η / 2 ≤ (1 + η - 1) / (1 + η) := by
      rw [show 1 + η - 1 = η by ring]
      exact div_le_div_of_nonneg_left hη_pos.le (by linarith) (by linarith)
    exact hfrac.trans hge
  have hf_bound : ∀ w ∈ Metric.ball z₀ R, ‖riemannZeta w / riemannZeta z₀‖ ≤ M := by
    intro w hw
    obtain ⟨_, hw_im2, hw_im_sq, hw_q, hw_ub, _⟩ := hw_prop w hw
    have hw_eq : riemannZeta w = riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I) := by
      congr 1; exact (Complex.re_add_im w).symm
    have hlog_le : Real.log (|w.im| + 2) ≤ 2 * logT := by
      have h1 := Real.log_le_log (by positivity : 0 < |w.im| + 2) hw_im_sq
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hw_bd : ‖riemannZeta w‖ ≤ 2 * Cem * logT := by
      rw [hw_eq]
      calc
        ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
            ≤ Cem * Real.log (|w.im| + 2) := hCem_bd hw_im2 hw_q hw_ub
        _ ≤ Cem * (2 * logT) := mul_le_mul_of_nonneg_left hlog_le hCem_pos.le
        _ = 2 * Cem * logT := by ring
    rw [norm_div]
    calc
      ‖riemannZeta w‖ / ‖riemannZeta z₀‖ ≤ (2 * Cem * logT) / (η / 2) :=
        div_le_div₀ (by positivity) hw_bd (by positivity) hz₀_lb
      _ = (4 * Cem / c₂) * logT ^ 2 := by
        dsimp only [η]
        field_simp [hc₂_pos.ne', hL_pos.ne']
        ring
      _ ≤ K * logT ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg logT)
  have hlogM_le : Real.log M ≤ (Real.log K + 2) * logT := by
    have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hK_ge1 : 1 ≤ K := le_max_right _ _
    dsimp only [M]
    rw [Real.log_mul hK_pos.ne' (pow_ne_zero 2 hL_pos.ne'), Real.log_pow, Nat.cast_ofNat]
    have hlogK_le : Real.log K ≤ Real.log K * logT := by nlinarith [Real.log_nonneg hK_ge1, hL_gt1]
    have hlogL_le : Real.log logT ≤ logT := by
      have h1 := Real.log_le_sub_one_of_pos hL_pos
      linarith
    linarith
  have hld := landau_logDeriv_le_of_ne_zero hr_pos.le hrR hf_diff hf_ne hf_bound hs_mem
  have hld_bound : ‖logDeriv riemannZeta s‖ ≤ C * logT ^ 2 := by
    have hcoeff : 2 * (R + r) / (R - r) ^ 2 = (26 / (81 * c₂)) * logT := by
      dsimp only [R, r, c₁, c₂]
      have hL_ne : logT ≠ 0 := hL_pos.ne'
      have hz_ne : c_zfr ≠ 0 := hc_pos.ne'
      field_simp [hL_ne, hz_ne]
      ring
    have h1 : 2 * (R + r) / (R - r) ^ 2 * Real.log M ≤ B_ld * logT ^ 2 := by
      rw [hcoeff]
      calc
        (26 / (81 * c₂)) * logT * Real.log M
            ≤ (26 / (81 * c₂)) * logT * ((Real.log K + 2) * logT) :=
          mul_le_mul_of_nonneg_left hlogM_le (by positivity)
        _ = B_ld * logT ^ 2 := by dsimp [B_ld]; ring
    have hBC : B_ld ≤ C := (le_max_left _ _).trans (by linarith)
    exact hld.trans (h1.trans (mul_le_mul_of_nonneg_right hBC (sq_nonneg logT)))
  obtain ⟨h, hh_diff, hh₀, hh_exp, _⟩ := exists_holomorphic_log_on_ball hR_pos hf_diff hf_ne
  have hh_re : ∀ w ∈ Metric.ball z₀ R, (h w).re ≤ Real.log M := by
    intro w hw
    have hexp := hh_exp w hw
    have hnorm : Real.exp (h w).re = ‖riemannZeta w / riemannZeta z₀‖ := by
      rw [← Complex.norm_exp, hexp]
    rw [← Real.exp_le_exp, hnorm, Real.exp_log hM_pos]
    exact hf_bound w hw
  have hbc := borel_caratheodory_sub_on_closedBall hr_pos.le hrR hh_diff hh_re hs_mem
  rw [hh₀, sub_zero, Complex.zero_re, sub_zero] at hbc
  have hratio_r : 2 * r / (R - r) ≤ 1 / 2 := by
    dsimp only [R, r, c₁, c₂]
    have hL_ne : logT ≠ 0 := hL_pos.ne'
    have hsimp :
        2 * (2 * (c_zfr / 20) / logT) /
          ((c_zfr / 2 + c_zfr / 20) / logT - 2 * (c_zfr / 20) / logT) = 4 / 9 := by
      field_simp [hL_ne, hc_pos.ne']
      ring
    rw [hsimp]
    norm_num
  have hhs_norm : ‖h s‖ ≤ (1 / 2) * Real.log M :=
    hbc.trans (mul_le_mul_of_nonneg_right hratio_r (Real.log_nonneg hM_ge1))
  have hhs_neg_re : -(h s).re ≤ (1 / 2) * Real.log M := by
    calc
      -(h s).re ≤ |-(h s).re| := le_abs_self _
      _ = |(h s).re| := abs_neg _
      _ ≤ ‖h s‖ := Complex.abs_re_le_norm _
      _ ≤ (1 / 2) * Real.log M := hhs_norm
  have hinv_eq : ‖(riemannZeta s)⁻¹‖ = ‖(riemannZeta z₀)⁻¹‖ * Real.exp (-(h s).re) := by
    have hs_ball : s ∈ Metric.ball z₀ R := Metric.closedBall_subset_ball hrR hs_mem
    have hexp_s := hh_exp s hs_ball
    have hs_ne : riemannZeta s ≠ 0 := hf_ne s hs_ball
    have hz₀_ne : riemannZeta z₀ ≠ 0 := hf_ne z₀ (Metric.mem_ball_self hR_pos)
    have hinv : (riemannZeta s)⁻¹ = (riemannZeta z₀)⁻¹ * Complex.exp (-h s) := by
      rw [Complex.exp_neg, hexp_s]
      field_simp [hs_ne, hz₀_ne]
    rw [hinv, norm_mul, Complex.norm_exp, Complex.neg_re]
  have hinv_bound : ‖(riemannZeta s)⁻¹‖ ≤ C * logT ^ 2 := by
    have hsqrt_M : Real.exp (-(h s).re) ≤ Real.sqrt K * logT := by
      have h1 : Real.exp (-(h s).re) ≤ Real.exp ((1 / 2) * Real.log M) := Real.exp_le_exp.mpr hhs_neg_re
      have h2 : Real.exp ((1 / 2) * Real.log M) = Real.sqrt M := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hM_pos, mul_comm]
      have h3 : Real.sqrt M = Real.sqrt K * logT := by
        dsimp only [M]
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ K), Real.sqrt_sq hL_pos.le]
      linarith
    have hz₀_inv_bd : ‖(riemannZeta z₀)⁻¹‖ ≤ (2 / c₂) * logT := by
      rw [norm_inv]
      calc
        (‖riemannZeta z₀‖)⁻¹ ≤ (η / 2)⁻¹ := inv_anti₀ (by positivity) hz₀_lb
        _ = (2 / c₂) * logT := by dsimp only [η]; field_simp [hc₂_pos.ne', hL_pos.ne']
    have hBC : B_inv ≤ C := (le_max_right _ _).trans (by linarith)
    calc
      ‖(riemannZeta s)⁻¹‖ = ‖(riemannZeta z₀)⁻¹‖ * Real.exp (-(h s).re) := hinv_eq
      _ ≤ ((2 / c₂) * logT) * (Real.sqrt K * logT) :=
        mul_le_mul hz₀_inv_bd hsqrt_M (Real.exp_pos _).le (by positivity)
      _ = B_inv * logT ^ 2 := by dsimp [B_inv]; ring
      _ ≤ C * logT ^ 2 := mul_le_mul_of_nonneg_right hBC (sq_nonneg logT)
  exact ⟨hld_bound, hinv_bound⟩

private lemma compact_box_zero_free_bounds {c_zfr c₂ : ℝ} (hc_pos : 0 < c_zfr)
    (hc_lt : c_zfr < 1 / 4) (hc₂_pos : 0 < c₂) (hc₂_le : c₂ ≤ c_zfr / 20)
    (hzfr : ∀ ⦃σ t : ℝ⦄, 1 - c_zfr / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, |t| ≤ 4 →
      1 - c₂ / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      (((σ : ℂ) + (t : ℂ) * I ≠ 1 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) +
          1 / ((σ : ℂ) + (t : ℂ) * I - 1)‖ ≤ C) ∧
        ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C) := by
  let g : ℂ → ℂ := fun z ↦ 1 + (z - 1) * riemannZeta₀ z
  have hg_diff : Differentiable ℂ g :=
    (differentiable_const 1).add ((differentiable_id.sub_const 1).mul differentiable_riemannZeta₀_bridge)
  have hg_eq : ∀ {z : ℂ}, z ≠ 1 → g z = (z - 1) * riemannZeta z := by
    intro z hz
    dsimp only [g]
    rw [← riemannZeta_sub_one_div_eq_riemannZeta₀ hz]
    field_simp [sub_ne_zero.mpr hz]
    ring
  let a : ℝ := 1 - c₂ / Real.log 2
  let K : Set ℂ := {z : ℂ | z.re ∈ Set.Icc a 2 ∧ z.im ∈ Set.Icc (-4 : ℝ) 4}
  have hK_eq : K = Complex.equivRealProdCLM.symm '' (Set.Icc a 2 ×ˢ Set.Icc (-4 : ℝ) 4) := by
    ext z
    simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
    constructor
    · intro hz
      refine ⟨(z.re, z.im), hz, ?_⟩
      change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) = z
      exact Complex.equivRealProdCLM.symm_apply_apply z
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
  have hK_comp : IsCompact K := by
    rw [hK_eq]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have ha_le1 : a ≤ 1 := by
    dsimp only [a]
    have := div_nonneg hc₂_pos.le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  have h1_mem : (1 : ℂ) ∈ K := by
    simp only [K, Set.mem_ofPred_eq, Complex.one_re, Complex.one_im, Set.mem_Icc]
    exact ⟨⟨ha_le1, by norm_num⟩, by norm_num, by norm_num⟩
  have hg_ne_K : ∀ z ∈ K, g z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z 1 with rfl | hz1
    · simp [g]
    rw [hg_eq hz1]
    refine mul_ne_zero (sub_ne_zero.mpr hz1) ?_
    have hz_eq : riemannZeta z = riemannZeta ((z.re : ℂ) + (z.im : ℂ) * I) := by
      congr 1; exact (Complex.re_add_im z).symm
    rw [hz_eq]
    refine hzfr ?_
    have him4 : |z.im| ≤ 4 := abs_le.mpr hz.2
    have hlog6_lt : Real.log 6 < 4 * Real.log 2 := by
      rw [show (4 : ℝ) * Real.log 2 = ((4 : ℕ) : ℝ) * Real.log 2 by norm_num, ← Real.log_pow]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog6_pos : 0 < Real.log 6 := Real.log_pos (by norm_num)
    have hfrac : c₂ / Real.log 2 ≤ c_zfr / Real.log (|z.im| + 2) := by
      calc
        c₂ / Real.log 2 ≤ (c_zfr / 20) / Real.log 2 :=
          div_le_div_of_nonneg_right hc₂_le hlog2_pos.le
        _ ≤ (c_zfr / 5) / Real.log 6 := by
          rw [div_le_div_iff₀ hlog2_pos hlog6_pos]
          nlinarith
        _ ≤ c_zfr / Real.log 6 :=
          div_le_div_of_nonneg_right (by linarith) hlog6_pos.le
        _ ≤ c_zfr / Real.log (|z.im| + 2) :=
          div_le_div_of_nonneg_left hc_pos.le (Real.log_pos (by linarith [abs_nonneg z.im]))
            (Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith))
    have hz_re : a ≤ z.re := hz.1.1
    dsimp only [a] at hz_re
    linarith
  have hld_cont : ContinuousOn (fun z : ℂ ↦ ‖logDeriv g z‖) K := by
    have hg_eq_ld : ∀ w : ℂ, logDeriv g w = deriv g w / g w := fun w ↦ logDeriv_apply g w
    simp_rw [hg_eq_ld]
    refine ContinuousOn.norm fun z hz ↦ ?_
    have hg_an : AnalyticAt ℂ g z :=
      (hg_diff.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
    exact (hg_an.deriv.continuousAt.div hg_diff.continuous.continuousAt (hg_ne_K z hz)).continuousWithinAt
  have hginv_cont : ContinuousOn (fun z : ℂ ↦ ‖(g z)⁻¹‖) K := by
    refine ContinuousOn.norm fun z hz ↦ ?_
    exact (hg_diff.continuous.continuousAt.inv₀ (hg_ne_K z hz)).continuousWithinAt
  obtain ⟨z₁, _, hz₁_max⟩ := hK_comp.exists_isMaxOn ⟨1, h1_mem⟩ hld_cont
  obtain ⟨z₂, _, hz₂_max⟩ := hK_comp.exists_isMaxOn ⟨1, h1_mem⟩ hginv_cont
  let C : ℝ := max ‖logDeriv g z₁‖ (max (6 * ‖(g z₂)⁻¹‖) ‖(riemannZeta 1)⁻¹‖) + 1
  refine ⟨C, by positivity, fun σ t ht hσ_low hσ_high ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hlog_ge2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have ha_le_σ : a ≤ σ := by
    have hfrac : c₂ / Real.log (|t| + 2) ≤ c₂ / Real.log 2 :=
      div_le_div_of_nonneg_left hc₂_pos.le (Real.log_pos one_lt_two) hlog_ge2
    dsimp only [a]
    linarith
  have hs_mem : s ∈ K := by
    simp only [K, Set.mem_ofPred_eq, s, add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add,
      Set.mem_Icc]
    exact ⟨⟨ha_le_σ, hσ_high⟩, abs_le.mp ht⟩
  refine ⟨fun hs1 ↦ ?_, ?_⟩
  · have hev : riemannZeta =ᶠ[𝓝 s] fun w ↦ (w - 1)⁻¹ * g w := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
      rw [hg_eq hw, inv_mul_cancel_left₀ (sub_ne_zero.mpr hw)]
    have hinv_d : HasDerivAt (fun w : ℂ ↦ (w - 1)⁻¹) (-1 / (s - 1) ^ 2) s :=
      ((hasDerivAt_id' s).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs1)
    have hmul_d : HasDerivAt (fun w : ℂ ↦ (w - 1)⁻¹ * g w)
        ((-1 / (s - 1) ^ 2) * g s + (s - 1)⁻¹ * deriv g s) s :=
      hinv_d.mul (hg_diff s).hasDerivAt
    have hld_eq : logDeriv riemannZeta s = -(s - 1)⁻¹ + logDeriv g s := by
      rw [logDeriv_apply, hev.deriv_eq, hmul_d.deriv, hev.eq_of_nhds, logDeriv_apply]
      have h1s : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hgs : g s ≠ 0 := hg_ne_K s hs_mem
      field_simp [h1s, hgs]
    rw [hld_eq, one_div, add_comm, ← add_assoc, add_neg_cancel, zero_add]
    have hmax1 : ‖logDeriv g z₁‖ ≤ C := by
      dsimp only [C]
      have hle := le_max_left ‖logDeriv g z₁‖ (max (6 * ‖(g z₂)⁻¹‖) ‖(riemannZeta 1)⁻¹‖)
      linarith
    exact (hz₁_max hs_mem).trans hmax1
  · rcases eq_or_ne s 1 with hs1 | hs1
    · change ‖(riemannZeta s)⁻¹‖ ≤ C
      rw [hs1]
      dsimp only [C]
      have hle := le_trans (le_max_right (6 * ‖(g z₂)⁻¹‖) ‖(riemannZeta 1)⁻¹‖)
        (le_max_right ‖logDeriv g z₁‖ (max (6 * ‖(g z₂)⁻¹‖) ‖(riemannZeta 1)⁻¹‖))
      linarith
    · have hinv_eq : (riemannZeta s)⁻¹ = (s - 1) * (g s)⁻¹ := by
        calc
          (riemannZeta s)⁻¹ = (s - 1) * ((s - 1)⁻¹ * (riemannZeta s)⁻¹) := by
            field_simp [sub_ne_zero.mpr hs1]
          _ = (s - 1) * (g s)⁻¹ := by
            rw [← mul_inv, hg_eq hs1]
      have hnorm_s1 : ‖s - 1‖ ≤ 6 := by
        have hs1_eq : s - 1 = ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I := by
          simp only [s]; push_cast; ring
        have hσ_sub : |σ - 1| ≤ 2 := by
          have ha0 : 0 ≤ a := by
            dsimp only [a]
            have hc2_small : c₂ ≤ 1 / 80 := by linarith
            have : c₂ / Real.log 2 ≤ 1 / 40 := by
              calc
                c₂ / Real.log 2 ≤ (1 / 80) / (1 / 2) :=
                  div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1 / 80) hc2_small (by norm_num)
                    half_lt_log_two.le
                _ = 1 / 40 := by norm_num
            linarith
          rw [abs_le]; constructor <;> linarith
        rw [hs1_eq]
        calc
          ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = |σ - 1| + |t| := by
            simp only [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
              Real.norm_eq_abs]
          _ ≤ 2 + 4 := add_le_add hσ_sub ht
          _ = 6 := by norm_num
      change ‖(riemannZeta s)⁻¹‖ ≤ C
      rw [hinv_eq, norm_mul]
      have hmax : 6 * ‖(g s)⁻¹‖ ≤ C := by
        have h1 : ‖(g s)⁻¹‖ ≤ ‖(g z₂)⁻¹‖ := hz₂_max hs_mem
        have h2 : 6 * ‖(g z₂)⁻¹‖ ≤ C := by
          dsimp only [C]
          have hle := le_trans (le_max_left (6 * ‖(g z₂)⁻¹‖) ‖(riemannZeta 1)⁻¹‖)
            (le_max_right ‖logDeriv g z₁‖ (max (6 * ‖(g z₂)⁻¹‖) ‖(riemannZeta 1)⁻¹‖))
          linarith
        linarith
      exact (mul_le_mul_of_nonneg_right hnorm_s1 (norm_nonneg _)).trans hmax

/-- **Unified zero-free region and effective vertical bounds**:
there exist `c ∈ (0, 1/4)` and `C > 0` such that on the zero-free region
`1 - c / Real.log (|t| + 2) ≤ σ`:
1. `riemannZeta (σ + t * I) ≠ 0`,
2. `‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I) + 1 / (σ + t * I - 1)‖ ≤ C * (Real.log (|t| + 2)) ^ 2`
   whenever `σ + t * I ≠ 1`,
3. `‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2`
   whenever `1 ≤ |t|`,
4. `‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * (Real.log (|t| + 2)) ^ 2`. -/
theorem riemannZeta_zero_free_region_with_bounds :
    ∃ c C : ℝ, 0 < c ∧ c < 1 / 4 ∧ 0 < C ∧
      ∀ ⦃σ t : ℝ⦄, 1 - c / Real.log (|t| + 2) ≤ σ →
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧
        ((σ : ℂ) + (t : ℂ) * I ≠ 1 →
          ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * I) +
            1 / ((σ : ℂ) + (t : ℂ) * I - 1)‖ ≤ C * (Real.log (|t| + 2)) ^ 2) ∧
        (1 ≤ |t| →
          ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (Real.log (|t| + 2)) ^ 2) ∧
        ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨c_zfr, hc_pos, hc_lt, hzfr⟩ := riemannZeta_zero_free_region
  let c : ℝ := c_zfr / 20
  obtain ⟨C₀, hC₀_pos, hC₀_bd⟩ := neg_logDeriv_riemannZeta_one_add_le
  obtain ⟨C_thin, hC_thin_pos, h_thin⟩ := thin_strip_disk_bounds hc_pos hc_lt hzfr
  obtain ⟨C_box, hC_box_pos, h_box⟩ :=
    compact_box_zero_free_bounds hc_pos hc_lt (by positivity : 0 < c) le_rfl hzfr
  let C_two : ℝ := max (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re 2 + 1
  have hlog2_sq_pos : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos (Real.log_pos one_lt_two)
  let C_base : ℝ := max C_thin (max ((C_box + 2) / (Real.log 2) ^ 2)
    (max (2 / c + (C₀ + 2) / (Real.log 2) ^ 2) (C_two / (Real.log 2) ^ 2))) + 2
  refine ⟨c, C_base, by positivity, by dsimp [c]; linarith, by positivity, fun σ t hσ ↦ ?_⟩
  have hc_lt_zfr : c < c_zfr := by dsimp [c]; linarith
  have hlog_ge_log2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hlog_pos : 0 < Real.log (|t| + 2) := (Real.log_pos one_lt_two).trans_le hlog_ge_log2
  have hlog_sq_ge : (Real.log 2) ^ 2 ≤ (Real.log (|t| + 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg one_le_two) hlog_ge_log2 2
  have hne : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    refine hzfr ?_
    have hfrac : c / Real.log (|t| + 2) ≤ c_zfr / Real.log (|t| + 2) :=
      div_le_div_of_nonneg_right hc_lt_zfr.le hlog_pos.le
    linarith
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let logT : ℝ := Real.log (|t| + 2)
  have hconst_le : ∀ M : ℝ, M ≤ C_two → M ≤ C_base * logT ^ 2 := fun M hM ↦ by
    have h1 : C_two / (Real.log 2) ^ 2 ≤ C_base := by
      dsimp only [C_base]
      have ha := le_max_right (2 / c + (C₀ + 2) / (Real.log 2) ^ 2) (C_two / (Real.log 2) ^ 2)
      have hb := le_trans ha (le_max_right ((C_box + 2) / (Real.log 2) ^ 2) _)
      have hc := le_trans hb (le_max_right C_thin _)
      linarith
    calc
      M ≤ C_two := hM
      _ = (C_two / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := by
        field_simp [hlog2_sq_pos.ne']
      _ ≤ C_base * logT ^ 2 := mul_le_mul h1 hlog_sq_ge hlog2_sq_pos.le (by positivity)
  have hbox_le : C_box + 2 ≤ C_base * logT ^ 2 := by
    have h1 : (C_box + 2) / (Real.log 2) ^ 2 ≤ C_base := by
      dsimp only [C_base]
      have ha := le_max_left ((C_box + 2) / (Real.log 2) ^ 2)
        (max (2 / c + (C₀ + 2) / (Real.log 2) ^ 2) (C_two / (Real.log 2) ^ 2))
      have hb := le_trans ha (le_max_right C_thin _)
      linarith
    calc
      C_box + 2 = ((C_box + 2) / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := by
        field_simp [hlog2_sq_pos.ne']
      _ ≤ C_base * logT ^ 2 := mul_le_mul h1 hlog_sq_ge hlog2_sq_pos.le (by positivity)
  have h_inv_and_ld : (s ≠ 1 → ‖logDeriv riemannZeta s + 1 / (s - 1)‖ ≤ C_base * logT ^ 2) ∧
      (1 ≤ |t| → ‖logDeriv riemannZeta s‖ ≤ C_base * logT ^ 2) ∧
      ‖(riemannZeta s)⁻¹‖ ≤ C_base * logT ^ 2 := by
    rcases le_or_gt 2 σ with hσ2 | hσ2
    · have hs1 : s ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        simp [s] at hre
        linarith
      have hld_ge2 := neg_logDeriv_riemannZeta_re_bound_of_ge_two hσ2 t
      have hld_norm : ‖logDeriv riemannZeta s‖ ≤
          (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re := by
        simpa [logDeriv_apply] using hld_ge2
      have h1s_norm : 1 ≤ ‖s - 1‖ := by
        have hre : 1 ≤ (s - 1).re := by simp [s]; linarith
        exact hre.trans (Complex.re_le_norm _)
      have hinv_s1 : ‖1 / (s - 1)‖ ≤ 1 := by
        rw [norm_div, norm_one, div_le_one (by positivity)]
        exact h1s_norm
      have hinv_ge2 : ‖(riemannZeta s)⁻¹‖ ≤ 2 := by
        rw [norm_inv]
        have := inv_norm_riemannZeta_le_of_one_lt_re (σ := σ) (by linarith) t
        have hfrac : σ / (σ - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        exact this.trans hfrac
      have hC2_1 : (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re + 1 ≤ C_two := by
        dsimp only [C_two]
        linarith [le_max_left (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re 2]
      have h2_le : (2 : ℝ) ≤ C_two := by
        dsimp only [C_two]
        linarith [le_max_right (-deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)).re 2]
      refine ⟨fun _ ↦ ?_, fun _ ↦ ?_, ?_⟩
      · exact (norm_add_le _ _).trans ((add_le_add hld_norm hinv_s1).trans (hconst_le _ hC2_1))
      · exact hld_norm.trans (hconst_le _ (by linarith))
      · exact hinv_ge2.trans (hconst_le 2 h2_le)
    · rcases le_or_gt |t| 4 with ht4 | ht4
      · obtain ⟨hld_b, hinv_b⟩ := h_box ht4 hσ hσ2.le
        refine ⟨fun hs1 ↦ (hld_b hs1).trans (by linarith [hbox_le]), fun ht1 ↦ ?_,
          hinv_b.trans (by linarith [hbox_le])⟩
        have hs1 : s ≠ 1 := by
          intro h
          have him := congrArg Complex.im h
          simp [s] at him
          rw [him, abs_zero] at ht1
          linarith
        have h_abs_s1 : |t| ≤ ‖s - 1‖ := by
          have := Complex.abs_im_le_norm (s - 1)
          simpa [s] using this
        have hinv_s1 : ‖1 / (s - 1)‖ ≤ 1 := by
          rw [norm_div, norm_one, div_le_one (by linarith)]
          exact ht1.trans h_abs_s1
        have htri : ‖logDeriv riemannZeta s‖ ≤
            ‖logDeriv riemannZeta s + 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := by
          calc
            ‖logDeriv riemannZeta s‖ =
                ‖(logDeriv riemannZeta s + 1 / (s - 1)) - 1 / (s - 1)‖ := by
              congr 1; ring
            _ ≤ ‖logDeriv riemannZeta s + 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
        exact htri.trans (by linarith [hld_b hs1, hbox_le])
      · have hL_gt1 : 1 < logT :=
          lt_of_lt_of_le one_lt_log_four (Real.log_le_log (by norm_num) (by linarith))
        have hs1 : s ≠ 1 := by
          intro h
          have him := congrArg Complex.im h
          simp [s] at him
          rw [him, abs_zero] at ht4
          linarith
        have hinv_s1 : ‖1 / (s - 1)‖ ≤ 1 := by
          have him_le : 1 ≤ ‖s - 1‖ := by
            have := Complex.abs_im_le_norm (s - 1)
            simp [s] at this
            linarith
          rw [norm_div, norm_one, div_le_one (by positivity)]
          exact him_le
        rcases le_or_gt σ (1 + c / logT) with hσ_strip | hσ_right
        · obtain ⟨hld_th, hinv_th⟩ := h_thin ht4.le hσ hσ_strip
          have hthin_le : C_thin + 2 ≤ C_base := by
            dsimp only [C_base]
            linarith [le_max_left C_thin (max ((C_box + 2) / (Real.log 2) ^ 2)
              (max (2 / c + (C₀ + 2) / (Real.log 2) ^ 2) (C_two / (Real.log 2) ^ 2)))]
          have hL1 : 1 ≤ logT ^ 2 := by nlinarith [hL_gt1]
          refine ⟨fun _ ↦ ?_, fun _ ↦ ?_, ?_⟩
          · have htri := norm_add_le (logDeriv riemannZeta s) (1 / (s - 1))
            calc
              ‖logDeriv riemannZeta s + 1 / (s - 1)‖ ≤ C_thin * logT ^ 2 + 1 := by linarith
              _ ≤ C_thin * logT ^ 2 + 2 * logT ^ 2 := by nlinarith
              _ = (C_thin + 2) * logT ^ 2 := by ring
              _ ≤ C_base * logT ^ 2 := mul_le_mul_of_nonneg_right hthin_le (sq_nonneg logT)
          · exact hld_th.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg logT))
          · exact hinv_th.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg logT))
        · have hη_ge : c / logT < σ - 1 := by linarith
          have hσ1 : 1 < σ := by
            have : 0 < c / logT := div_pos (by positivity) hlog_pos
            linarith
          have hσ_sub_le : σ - 1 ≤ 1 := by linarith
          have hld_r : ‖logDeriv riemannZeta s‖ ≤ 1 / (σ - 1) + C₀ := by
            have hnorm := norm_logDeriv_riemannZeta_of_one_lt_re hσ1 t
            have hb := hC₀_bd (sub_pos.mpr hσ1) hσ_sub_le
            have heq1 : ((1 + (σ - 1) : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
            rw [heq1] at hb
            simpa [logDeriv_apply, s] using hnorm.trans hb
          have hld_L : ‖logDeriv riemannZeta s‖ ≤ (1 / c) * logT + C₀ := by
            have hinv_le : 1 / (σ - 1) ≤ (1 / c) * logT := by
              calc
                1 / (σ - 1) ≤ 1 / (c / logT) := one_div_le_one_div_of_le (by positivity) hη_ge.le
                _ = (1 / c) * logT := by field_simp [(by positivity : 0 < c).ne', hlog_pos.ne']
            linarith
          have hinv_r : ‖(riemannZeta s)⁻¹‖ ≤ (2 / c) * logT := by
            rw [norm_inv]
            have h1 := inv_norm_riemannZeta_le_of_one_lt_re hσ1 t
            have h2 : σ / (σ - 1) ≤ 2 / (c / logT) :=
              div_le_div₀ (by linarith) hσ2.le (by positivity) hη_ge.le
            have h3 : 2 / (c / logT) = (2 / c) * logT := by
              field_simp [(by positivity : 0 < c).ne', hlog_pos.ne']
            exact h1.trans (h2.trans_eq h3)
          have hC_comb_le : 2 / c + (C₀ + 2) / (Real.log 2) ^ 2 ≤ C_base := by
            dsimp only [C_base]
            have ha := le_max_left (2 / c + (C₀ + 2) / (Real.log 2) ^ 2) (C_two / (Real.log 2) ^ 2)
            have hb := le_trans ha (le_max_right ((C_box + 2) / (Real.log 2) ^ 2) _)
            have hc := le_trans hb (le_max_right C_thin _)
            linarith
          have hL_le_sq : logT ≤ logT ^ 2 := by nlinarith [hL_gt1]
          have hC0_bd : C₀ + 1 ≤ (C₀ + 2) / (Real.log 2) ^ 2 * logT ^ 2 := by
            have h := mul_le_mul_of_nonneg_left hlog_sq_ge
              (by positivity : 0 ≤ (C₀ + 2) / (Real.log 2) ^ 2)
            rw [show (C₀ + 2) / (Real.log 2) ^ 2 * (Real.log 2) ^ 2 = C₀ + 2 by
              field_simp [hlog2_sq_pos.ne']] at h
            linarith
          have h1c_le : (1 / c) * logT + C₀ + 1 ≤ C_base * logT ^ 2 := by
            calc
              (1 / c) * logT + C₀ + 1
                  ≤ (2 / c) * logT ^ 2 + ((C₀ + 2) / (Real.log 2) ^ 2) * logT ^ 2 := by
                have hc12 : 1 / c ≤ 2 / c :=
                  div_le_div_of_nonneg_right (by norm_num) (by positivity)
                have hmul1 : (1 / c) * logT ≤ (2 / c) * logT ^ 2 :=
                  mul_le_mul hc12 hL_le_sq (by positivity) (by positivity)
                linarith
              _ = (2 / c + (C₀ + 2) / (Real.log 2) ^ 2) * logT ^ 2 := by ring
              _ ≤ C_base * logT ^ 2 := mul_le_mul_of_nonneg_right hC_comb_le (sq_nonneg logT)
          refine ⟨fun _ ↦ ?_, fun _ ↦ ?_, ?_⟩
          · exact (norm_add_le _ _).trans (by linarith)
          · exact hld_L.trans (by linarith)
          · calc
              ‖(riemannZeta s)⁻¹‖ ≤ (2 / c) * logT := hinv_r
              _ ≤ (2 / c) * logT ^ 2 := mul_le_mul_of_nonneg_left hL_le_sq (by positivity)
              _ ≤ C_base * logT ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg logT)
                linarith [show 0 ≤ (C₀ + 2) / (Real.log 2) ^ 2 by positivity]
  refine ⟨hne, fun hs1 ↦ ?_, fun ht1 ↦ ?_, h_inv_and_ld.2.2⟩
  · simpa only [logDeriv_apply] using h_inv_and_ld.1 hs1
  · simpa only [logDeriv_apply] using h_inv_and_ld.2.1 ht1

/-- Effective logarithmic-squared bound for `deriv riemannZeta s / riemannZeta s + 1 / (s - 1)`
throughout the zero-free region (valid up to `s = 1`). -/
theorem norm_logDeriv_riemannZeta_add_sub_one_le :
    ∃ c C : ℝ, 0 < c ∧ c < 1 / 4 ∧ 0 < C ∧
      ∀ ⦃σ t : ℝ⦄, (σ : ℂ) + (t : ℂ) * I ≠ 1 → 1 - c / Real.log (|t| + 2) ≤ σ →
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) / riemannZeta ((σ : ℂ) + (t : ℂ) * I) +
          1 / ((σ : ℂ) + (t : ℂ) * I - 1)‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨c, C, hc, hlt, hC, h⟩ := riemannZeta_zero_free_region_with_bounds
  exact ⟨c, C, hc, hlt, hC, fun σ t hs1 hσ ↦ (h hσ).2.1 hs1⟩

/-- Effective logarithmic-squared bound for `deriv riemannZeta / riemannZeta` inside the
zero-free region for `1 ≤ |t|`. -/
theorem norm_logDeriv_riemannZeta_zero_free_le :
    ∃ c C : ℝ, 0 < c ∧ c < 1 / 4 ∧ 0 < C ∧
      ∀ ⦃σ t : ℝ⦄, 1 ≤ |t| → 1 - c / Real.log (|t| + 2) ≤ σ →
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) / riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨c, C, hc, hlt, hC, h⟩ := riemannZeta_zero_free_region_with_bounds
  exact ⟨c, C, hc, hlt, hC, fun σ t ht hσ ↦ (h hσ).2.2.1 ht⟩

/-- Effective logarithmic-squared bound for `(riemannZeta s)⁻¹` throughout the zero-free
region `1 - c / Real.log (|t| + 2) ≤ σ`. -/
theorem norm_inv_riemannZeta_zero_free_le :
    ∃ c C : ℝ, 0 < c ∧ c < 1 / 4 ∧ 0 < C ∧
      ∀ ⦃σ t : ℝ⦄, 1 - c / Real.log (|t| + 2) ≤ σ →
        ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨c, C, hc, hlt, hC, h⟩ := riemannZeta_zero_free_region_with_bounds
  exact ⟨c, C, hc, hlt, hC, fun σ t hσ ↦ (h hσ).2.2.2⟩

end AnalyticNumberTheory.RiemannZeta
