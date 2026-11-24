import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleIntegrals
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.HadamardFactorization
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv

/-!
# Truncated von Mangoldt Explicit Formula

This file establishes the unconditional truncated von Mangoldt explicit formula relating
`Chebyshev.psi x` to `x`, a finite sum over nontrivial zeros `ρ` of `riemannZeta` with
`0 < ρ.re < 1` and `|ρ.im| ≤ T`, and an explicit error term `O((x * (log x)^2) / T + log x)`:

1. **Uniform Perron kernel bound and Perron truncation for `Λ`**:
   We prove the unconditional uniform bound `‖perronKernel y c T‖ ≤ 2 * y ^ c` (for all
   `y > 0`, `c > 0`, `T > 0`) via trigonometric expansion and integration by parts, eliminating
   the `log T` loss near `y = 1`. Using this uniform bound for integers within distance `1` of
   `x` and `perronKernel` tail estimates away from `x`, we prove the general truncated Perron
   formula `perron_truncated_vonMangoldt` for all `x ≥ 2`, along with its half-integer
   specialization `perron_truncated_half_integer_vonMangoldt`.
2. **Local zero counting, good horizontal contours, and `-ζ'/ζ` estimates**:
   Applying Jensen's formula to `xi` on balls `closedBall (2 + τ * I) 6` yields `O(log (|τ| + 2))`
   zeros in every unit horizontal strip, finite zero sets `nontrivialZerosUpTo T`, a pigeonhole
   choice `T' ∈ (T, T + 1)` staying at distance `≫ 1 / log T` from every nontrivial zero
   ordinate, and vertical/horizontal bounds for `-deriv riemannZeta s / riemannZeta s` via
   Hadamard factorization of `xi` and the functional equation.
3. **Rectangular Cauchy contour shift**:
   Subtracting the poles at `s = 1`, `s = 0`, and nontrivial zeros `ρ` inside `[-1/2, c] × [-T', T']`
   produces a holomorphic integrand whose rectangular boundary integral vanishes, yielding the
   shifted explicit representation.
4. **Main truncated explicit formula theorems**:
   Combining the Perron formula, contour shift, and `T → T'` zero-tail adjustment gives
   `explicit_formula_psi` (valid for all `2 ≤ x` and `2 ≤ T ≤ x`) and `explicit_formula_psi_half_integer`.
-/

noncomputable section

open Finset MeasureTheory Set Filter Asymptotics
open Complex (I reProdIm)
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.RiemannZeta
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.EntireFunctions
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.PrimeDistribution

/-! ### Section 1: Uniform Perron Kernel Bound and Perron Truncation for `Λ` -/

private lemma integral_odd_real_zero {f : ℝ → ℝ} (hodd : ∀ t : ℝ, f (-t) = -f t) (T : ℝ) :
    ∫ t in (-T)..T, f t = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg f (a := -T) (b := T)
  have h1 : ∫ t in (-T)..T, f (-t) = ∫ t in (-T)..T, f t := by
    simp only [neg_neg] at hcomp
    exact hcomp
  have h2 : ∫ t in (-T)..T, f (-t) = -∫ t in (-T)..T, f t := by
    simp only [hodd, intervalIntegral.integral_neg]
  linarith

private lemma integral_even_real_eq_two_mul {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ t : ℝ, f (-t) = f t) (T : ℝ) :
    ∫ t in (-T)..T, f t = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have hsplit :
      (∫ t in (-T)..0, f t) + (∫ t in (0 : ℝ)..T, f t) = ∫ t in (-T)..T, f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)
  have hleft : ∫ t in (-T)..0, f t = ∫ t in (0 : ℝ)..T, f t := by
    have hcomp := intervalIntegral.integral_comp_neg f (a := (0 : ℝ)) (b := T)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    exact intervalIntegral.integral_congr fun t _ ↦ heven t
  linarith

private lemma continuous_trig_div_sq {c a b α : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ ↦
      (a * Real.cos (α * t) + b * t * Real.sin (α * t)) / (c ^ 2 + t ^ 2) := by
  have hcos : Continuous fun t : ℝ ↦ Real.cos (α * t) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin : Continuous fun t : ℝ ↦ Real.sin (α * t) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hnum : Continuous fun t : ℝ ↦ a * Real.cos (α * t) + b * t * Real.sin (α * t) :=
    (continuous_const.mul hcos).add ((continuous_const.mul continuous_id).mul hsin)
  have hden : Continuous fun t : ℝ ↦ c ^ 2 + t ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  exact hnum.div hden fun t ↦ by positivity

private lemma continuous_trig_div_sq' {c a b α : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ ↦
      (a * Real.sin (α * t) + b * t * Real.cos (α * t)) / (c ^ 2 + t ^ 2) := by
  have hcos : Continuous fun t : ℝ ↦ Real.cos (α * t) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin : Continuous fun t : ℝ ↦ Real.sin (α * t) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hnum : Continuous fun t : ℝ ↦ a * Real.sin (α * t) + b * t * Real.cos (α * t) :=
    (continuous_const.mul hsin).add ((continuous_const.mul continuous_id).mul hcos)
  have hden : Continuous fun t : ℝ ↦ c ^ 2 + t ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  exact hnum.div hden fun t ↦ by positivity

private lemma perronKernel_eq_real_cos_sin {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) :
    perronKernel y c T =
      (((y ^ c / Real.pi) *
        ∫ t in (0 : ℝ)..T,
          (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) / (c ^ 2 + t ^ 2) :
          ℝ) : ℂ) := by
  let α : ℝ := Real.log y
  let f : ℝ → ℝ := fun t ↦ (c * Real.cos (α * t) + t * Real.sin (α * t)) / (c ^ 2 + t ^ 2)
  let g : ℝ → ℝ := fun t ↦ (c * Real.sin (α * t) - t * Real.cos (α * t)) / (c ^ 2 + t ^ 2)
  have hden_pos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t ↦ by positivity
  have hf_cont : Continuous f := by
    simpa [f] using (continuous_trig_div_sq (a := c) (b := 1) (α := α) hc)
  have hg_cont : Continuous g := by
    have h := continuous_trig_div_sq' (a := c) (b := -1) (α := α) hc
    refine h.congr fun t ↦ ?_
    dsimp [g]
    ring
  have hf_even : ∀ t : ℝ, f (-t) = f t := fun t ↦ by
    dsimp [f]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg, neg_sq]
    ring
  have hg_odd : ∀ t : ℝ, g (-t) = -g t := fun t ↦ by
    dsimp [g]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg, neg_sq]
    ring
  have hpt : ∀ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) =
        ((y ^ c : ℝ) : ℂ) * (((f t : ℝ) : ℂ) + ((g t : ℝ) : ℂ) * I) := by
    intro t
    have hyc0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hpow : (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) =
        ((y ^ c : ℝ) : ℂ) * ((Real.cos (α * t) : ℂ) + (Real.sin (α * t) : ℂ) * I) := by
      rw [Complex.cpow_add _ _ hyc0, Complex.ofReal_cpow hy.le c]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hyc0, ← Complex.ofReal_log hy.le]
      have harg : (Real.log y : ℂ) * ((t : ℂ) * I) = (((α * t : ℝ) : ℂ) * I) := by
        dsimp [α]; push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hct0 : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hinv : ((c : ℂ) + (t : ℂ) * I)⁻¹ =
        ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) + ((-t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
      rw [inv_eq_one_div, div_eq_iff hct0]
      symm
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
          Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
        have hd0 : c ^ 2 + t ^ 2 ≠ 0 := (hden_pos t).ne'
        field_simp [hd0]
        ring
      · simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
          Complex.add_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im]
        ring
    rw [div_eq_mul_inv, hpow, hinv]
    apply Complex.ext
    · simp only [f, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_im, Complex.add_im]
      ring
    · simp only [g, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_re, Complex.add_re]
      ring
  have hint_eq :
      (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
        ((y ^ c : ℝ) : ℂ) *
          (((∫ t in (-T)..T, f t : ℝ) : ℂ) + ((∫ t in (-T)..T, g t : ℝ) : ℂ) * I) := by
    have hcongr :
        (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
          ((y ^ c : ℝ) : ℂ) * ∫ t in (-T)..T, (((f t : ℝ) : ℂ) + ((g t : ℝ) : ℂ) * I) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ ↦ hpt t
    rw [hcongr]
    congr 1
    have hf_c : IntervalIntegrable (fun t : ℝ ↦ (f t : ℂ)) volume (-T) T :=
      (Complex.continuous_ofReal.comp hf_cont).intervalIntegrable (-T) T
    have hg_c : IntervalIntegrable (fun t : ℝ ↦ ((g t : ℂ) * I)) volume (-T) T :=
      ((Complex.continuous_ofReal.comp hg_cont).mul continuous_const).intervalIntegrable (-T) T
    rw [intervalIntegral.integral_add hf_c hg_c]
    congr 1
    · exact intervalIntegral.integral_ofReal
    · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  rw [perronKernel, hint_eq, integral_odd_real_zero hg_odd T, integral_even_real_eq_two_mul hf_cont
    hf_even T]
  dsimp [f, α]
  push_cast
  rw [zero_mul, add_zero]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi0]

private lemma integral_cos_div_le_pi_div_two {α c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    |∫ t in (0 : ℝ)..T, c * Real.cos (α * t) / (c ^ 2 + t ^ 2)| ≤ Real.pi / 2 := by
  have hden_pos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t ↦ by positivity
  have hcont1 : Continuous fun t : ℝ ↦ c * Real.cos (α * t) / (c ^ 2 + t ^ 2) := by
    have h := continuous_trig_div_sq (a := c) (b := 0) (α := α) hc
    refine h.congr fun t ↦ ?_
    ring
  have hcont2 : Continuous fun t : ℝ ↦ c / (c ^ 2 + t ^ 2) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) fun t ↦ (hden_pos t).ne'
  have hnorm_le :
      |∫ t in (0 : ℝ)..T, c * Real.cos (α * t) / (c ^ 2 + t ^ 2)| ≤
        ∫ t in (0 : ℝ)..T, |c * Real.cos (α * t) / (c ^ 2 + t ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hT.le
  have hmono :
      (∫ t in (0 : ℝ)..T, |c * Real.cos (α * t) / (c ^ 2 + t ^ 2)|) ≤
        ∫ t in (0 : ℝ)..T, c / (c ^ 2 + t ^ 2) := by
    refine intervalIntegral.integral_mono_on hT.le
      (hcont1.abs.intervalIntegrable 0 T) (hcont2.intervalIntegrable 0 T) fun t _ ↦ ?_
    rw [abs_div, abs_mul, abs_of_pos hc, abs_of_pos (hden_pos t)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hc.le (Real.abs_cos_le_one _)) (hden_pos t).le
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ ↦ Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    intro t _
    have hsub : HasDerivAt (fun u : ℝ ↦ u / c) (1 / c) t := by
      simpa using (hasDerivAt_id' t).div_const c
    have hcomp := (Real.hasDerivAt_arctan (t / c)).comp t hsub
    refine hcomp.congr_deriv ?_
    have hden_sub : 1 + (t / c) ^ 2 ≠ 0 := by positivity
    field_simp [hc.ne', hden_sub]
  have hint_eq : ∫ t in (0 : ℝ)..T, c / (c ^ 2 + t ^ 2) = Real.arctan (T / c) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont2.intervalIntegrable 0 T)
    simpa [zero_div, Real.arctan_zero] using h
  have harctan : Real.arctan (T / c) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two (T / c)).le
  exact (hnorm_le.trans hmono).trans (hint_eq.le.trans harctan)

private lemma integral_sin_div_pos_le_four {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    |∫ t in (0 : ℝ)..T, t * Real.sin (a * t) / (c ^ 2 + t ^ 2)| ≤ 4 := by
  have hden_pos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t ↦ by positivity
  let f : ℝ → ℝ := fun t ↦ t * Real.sin (a * t) / (c ^ 2 + t ^ 2)
  have hf_cont : Continuous f := by
    have h := continuous_trig_div_sq (a := 0) (b := 1) (α := a) hc
    refine h.congr fun t ↦ ?_
    dsimp [f]
    ring
  let u : ℝ := min T (1 / a)
  have hu_pos : 0 < u := lt_min hT (one_div_pos.mpr ha)
  have hu_le_T : u ≤ T := min_le_left T (1 / a)
  have hu_le_inv : u ≤ 1 / a := min_le_right T (1 / a)
  have hsplit :
      ∫ t in (0 : ℝ)..T, f t = (∫ t in (0 : ℝ)..u, f t) + ∫ t in u..T, f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable 0 u) (hf_cont.intervalIntegrable u T)).symm
  have hpart1 : |∫ t in (0 : ℝ)..u, f t| ≤ 1 := by
    have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f) hu_pos.le
    have h2 : (∫ t in (0 : ℝ)..u, |f t|) ≤ ∫ _ in (0 : ℝ)..u, a := by
      refine intervalIntegral.integral_mono_on hu_pos.le
        (hf_cont.abs.intervalIntegrable 0 u) intervalIntegrable_const fun t ht ↦ ?_
      dsimp [f]
      rw [abs_div, abs_mul, abs_of_nonneg ht.1, abs_of_pos (hden_pos t)]
      have hsin : |Real.sin (a * t)| ≤ a * t := by
        calc
          |Real.sin (a * t)| ≤ |a * t| := Real.abs_sin_le_abs
          _ = a * t := abs_of_nonneg (mul_nonneg ha.le ht.1)
      have hsq : t ^ 2 ≤ c ^ 2 + t ^ 2 := le_add_of_nonneg_left (sq_nonneg c)
      calc
        t * |Real.sin (a * t)| / (c ^ 2 + t ^ 2)
            ≤ t * (a * t) / (c ^ 2 + t ^ 2) := by
          have ht0 : 0 ≤ t := ht.1
          gcongr
        _ = a * (t ^ 2 / (c ^ 2 + t ^ 2)) := by ring
        _ ≤ a * 1 := by gcongr; exact (div_le_one (hden_pos t)).mpr hsq
        _ = a := mul_one a
    have hconst : (∫ _ in (0 : ℝ)..u, a) = u * a := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    have hua : u * a ≤ 1 := by
      calc
        u * a ≤ (1 / a) * a := mul_le_mul_of_nonneg_right hu_le_inv ha.le
        _ = 1 := one_div_mul_cancel ha.ne'
    exact (h1.trans h2).trans (hconst.le.trans hua)
  have hpart2 : |∫ t in u..T, f t| ≤ 3 := by
    by_cases hTu : T ≤ 1 / a
    · have hu_eq : u = T := min_eq_left hTu
      rw [hu_eq, intervalIntegral.integral_same, abs_zero]
      norm_num
    · have hinv_lt : 1 / a < T := lt_of_not_ge hTu
      have hu_eq : u = 1 / a := min_eq_right hinv_lt.le
      have huT : u ≤ T := hu_le_T
      let φ : ℝ → ℝ := fun t ↦ t / (c ^ 2 + t ^ 2)
      let φ' : ℝ → ℝ := fun t ↦ (c ^ 2 - t ^ 2) / (c ^ 2 + t ^ 2) ^ 2
      let ψ : ℝ → ℝ := fun t ↦ -Real.cos (a * t) / a
      let ψ' : ℝ → ℝ := fun t ↦ Real.sin (a * t)
      have hφ : ∀ t ∈ Set.uIcc u T, HasDerivAt φ (φ' t) t := by
        intro t _
        have hden_deriv : HasDerivAt (fun s : ℝ ↦ c ^ 2 + s ^ 2) (2 * t) t := by
          have h := (hasDerivAt_pow 2 t).const_add (c ^ 2)
          refine h.congr_deriv ?_
          ring
        have hdiv := (hasDerivAt_id' t).div hden_deriv (hden_pos t).ne'
        refine hdiv.congr_deriv ?_
        dsimp [φ']
        ring
      have hψ : ∀ t ∈ Set.uIcc u T, HasDerivAt ψ (ψ' t) t := by
        intro t _
        have hlin : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
          simpa using (hasDerivAt_id' t).const_mul a
        have hcos : HasDerivAt (fun s : ℝ ↦ Real.cos (a * s)) (-Real.sin (a * t) * a) t :=
          (Real.hasDerivAt_cos (a * t)).comp t hlin
        have hscaled := (hcos.neg).div_const a
        refine hscaled.congr_deriv ?_
        dsimp [ψ']
        field_simp [ha.ne']
      have hφ'_cont : Continuous φ' :=
        (continuous_const.sub (continuous_id.pow 2)).div
          ((continuous_const.add (continuous_id.pow 2)).pow 2) fun t ↦
            pow_ne_zero 2 (hden_pos t).ne'
      have hψ'_cont : Continuous ψ' :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      have hψ_cont : Continuous ψ :=
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).neg).div_const a
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ hψ
        (hφ'_cont.intervalIntegrable u T) (hψ'_cont.intervalIntegrable u T)
      have hf_eq : ∫ t in u..T, f t = ∫ t in u..T, φ t * ψ' t := by
        refine intervalIntegral.integral_congr fun t _ ↦ ?_
        dsimp [f, φ, ψ']
        ring
      rw [hf_eq, hibp]
      have hbd_val : ∀ t : ℝ, u ≤ t → |φ t * ψ t| ≤ 1 := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hu_pos ht
        have hφ_le : |φ t| ≤ a := by
          dsimp [φ]
          rw [abs_of_nonneg (div_nonneg ht_pos.le (hden_pos t).le)]
          have h1 : t / (c ^ 2 + t ^ 2) ≤ t / t ^ 2 :=
            div_le_div_of_nonneg_left ht_pos.le (sq_pos_of_pos ht_pos)
              (le_add_of_nonneg_left (sq_nonneg c))
          have h2 : t / t ^ 2 = 1 / t := by
            field_simp [ht_pos.ne']
          have h3 : 1 / t ≤ 1 / u := one_div_le_one_div_of_le hu_pos ht
          have h4 : 1 / u = a := by rw [hu_eq, one_div_one_div]
          exact h1.trans (h2 ▸ h3.trans_eq h4)
        have hψ_le : |ψ t| ≤ 1 / a := by
          dsimp [ψ]
          rw [abs_div, abs_neg, abs_of_pos ha]
          exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ha.le
        rw [abs_mul]
        calc
          |φ t| * |ψ t| ≤ a * (1 / a) := mul_le_mul hφ_le hψ_le (abs_nonneg _) ha.le
          _ = 1 := mul_one_div_cancel ha.ne'
      have hrem : |∫ t in u..T, φ' t * ψ t| ≤ 1 := by
        have hcont_rem : Continuous fun t : ℝ ↦ φ' t * ψ t := hφ'_cont.mul hψ_cont
        have hcont_invsq : ContinuousOn (fun t : ℝ ↦ (1 / a) * (t ^ 2)⁻¹) (Set.Icc u T) := by
          refine ContinuousOn.mul continuousOn_const
            (ContinuousOn.inv₀ (continuous_id.pow 2).continuousOn fun t ht ↦ ?_)
          exact pow_ne_zero 2 (lt_of_lt_of_le hu_pos ht.1).ne'
        have hint_invsq : IntervalIntegrable (fun t : ℝ ↦ (1 / a) * (t ^ 2)⁻¹) volume u T :=
          hcont_invsq.intervalIntegrable_of_Icc huT
        have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun t ↦ φ' t * ψ t) huT
        have h2 : (∫ t in u..T, |φ' t * ψ t|) ≤ ∫ t in u..T, (1 / a) * (t ^ 2)⁻¹ := by
          refine intervalIntegral.integral_mono_on huT
            (hcont_rem.abs.intervalIntegrable u T) hint_invsq fun t ht ↦ ?_
          have ht_pos : 0 < t := lt_of_lt_of_le hu_pos ht.1
          have hφ'_le : |φ' t| ≤ (t ^ 2)⁻¹ := by
            dsimp [φ']
            rw [abs_div, abs_of_pos (pow_pos (hden_pos t) 2)]
            have hnum : |c ^ 2 - t ^ 2| ≤ c ^ 2 + t ^ 2 := by
              rw [abs_sub_le_iff]
              constructor <;> linarith [sq_nonneg c, sq_nonneg t]
            calc
              |c ^ 2 - t ^ 2| / (c ^ 2 + t ^ 2) ^ 2
                  ≤ (c ^ 2 + t ^ 2) / (c ^ 2 + t ^ 2) ^ 2 := by gcongr
              _ = (c ^ 2 + t ^ 2)⁻¹ := by
                  have hd0 : c ^ 2 + t ^ 2 ≠ 0 := (hden_pos t).ne'
                  field_simp [hd0]
              _ ≤ (t ^ 2)⁻¹ :=
                  inv_anti₀ (sq_pos_of_pos ht_pos) (le_add_of_nonneg_left (sq_nonneg c))
          have hψ_le : |ψ t| ≤ 1 / a := by
            dsimp [ψ]
            rw [abs_div, abs_neg, abs_of_pos ha]
            exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ha.le
          rw [abs_mul]
          calc
            |φ' t| * |ψ t| ≤ (t ^ 2)⁻¹ * (1 / a) := mul_le_mul hφ'_le hψ_le (abs_nonneg _)
              (inv_nonneg.mpr (sq_nonneg t))
            _ = (1 / a) * (t ^ 2)⁻¹ := mul_comm _ _
        have hderiv_inv : ∀ t ∈ Set.uIcc u T,
            HasDerivAt (fun s : ℝ ↦ (1 / a) * (-s⁻¹)) ((1 / a) * (t ^ 2)⁻¹) t := by
          intro t ht
          rw [Set.uIcc_of_le huT] at ht
          have ht0 : t ≠ 0 := (lt_of_lt_of_le hu_pos ht.1).ne'
          have hinv := (hasDerivAt_inv ht0).neg.const_mul (1 / a)
          refine hinv.congr_deriv ?_
          ring
        have hint_val :
            ∫ t in u..T, (1 / a) * (t ^ 2)⁻¹ = (1 / a) * (-T⁻¹) - (1 / a) * (-u⁻¹) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_inv hint_invsq
        have hle_one : (1 / a) * (-T⁻¹) - (1 / a) * (-u⁻¹) ≤ 1 := by
          have hT_neg : 0 < T⁻¹ := inv_pos.mpr hT
          have hu_inv : u⁻¹ = a := by rw [hu_eq, one_div, inv_inv]
          calc
            (1 / a) * (-T⁻¹) - (1 / a) * (-u⁻¹)
                = (1 / a) * (u⁻¹ - T⁻¹) := by ring
            _ ≤ (1 / a) * u⁻¹ := by gcongr; linarith
            _ = 1 := by rw [hu_inv]; exact one_div_mul_cancel ha.ne'
        exact (h1.trans h2).trans (hint_val.le.trans hle_one)
      have htri : |φ T * ψ T - φ u * ψ u - ∫ t in u..T, φ' t * ψ t| ≤
          |φ T * ψ T| + |φ u * ψ u| + |∫ t in u..T, φ' t * ψ t| := by
        calc
          |φ T * ψ T - φ u * ψ u - ∫ t in u..T, φ' t * ψ t|
              ≤ |φ T * ψ T - φ u * ψ u| + |∫ t in u..T, φ' t * ψ t| := abs_sub _ _
          _ ≤ (|φ T * ψ T| + |φ u * ψ u|) + |∫ t in u..T, φ' t * ψ t| :=
              add_le_add (abs_sub _ _) le_rfl
          _ = |φ T * ψ T| + |φ u * ψ u| + |∫ t in u..T, φ' t * ψ t| := rfl
      linarith [htri, hbd_val T huT, hbd_val u le_rfl, hrem]
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith [hpart1, hpart2])

private lemma integral_sin_div_le_four {α c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    |∫ t in (0 : ℝ)..T, t * Real.sin (α * t) / (c ^ 2 + t ^ 2)| ≤ 4 := by
  rcases lt_trichotomy α 0 with hneg | rfl | hpos
  · have hpos : 0 < -α := neg_pos.mpr hneg
    have heq :
        (∫ t in (0 : ℝ)..T, t * Real.sin (α * t) / (c ^ 2 + t ^ 2)) =
          -∫ t in (0 : ℝ)..T, t * Real.sin ((-α) * t) / (c ^ 2 + t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      rw [show α * t = -((-α) * t) by ring, Real.sin_neg]
      ring
    rw [heq, abs_neg]
    exact integral_sin_div_pos_le_four hpos hc hT
  · simp
  · exact integral_sin_div_pos_le_four hpos hc hT

/-- Uniform Perron kernel upper bound `‖perronKernel y c T‖ ≤ 2 * y ^ c`, valid for all `y > 0`,
`c > 0`, and `T > 0`, with no dependence on `T` or `y = 1` proximity. -/
theorem norm_perronKernel_le_const_mul_rpow {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T‖ ≤ 2 * y ^ c := by
  rw [perronKernel_eq_real_cos_sin hy hc]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (div_pos (Real.rpow_pos_of_pos hy c) Real.pi_pos)]
  let f₁ : ℝ → ℝ := fun t ↦ c * Real.cos (Real.log y * t) / (c ^ 2 + t ^ 2)
  let f₂ : ℝ → ℝ := fun t ↦ t * Real.sin (Real.log y * t) / (c ^ 2 + t ^ 2)
  have hf₁ : Continuous f₁ := by
    have h := continuous_trig_div_sq (a := c) (b := 0) (α := Real.log y) hc
    refine h.congr fun t ↦ ?_
    dsimp [f₁]; ring
  have hf₂ : Continuous f₂ := by
    have h := continuous_trig_div_sq (a := 0) (b := 1) (α := Real.log y) hc
    refine h.congr fun t ↦ ?_
    dsimp [f₂]; ring
  have heq_sum :
      (∫ t in (0 : ℝ)..T, (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) /
          (c ^ 2 + t ^ 2)) =
        (∫ t in (0 : ℝ)..T, f₁ t) + ∫ t in (0 : ℝ)..T, f₂ t := by
    rw [← intervalIntegral.integral_add (hf₁.intervalIntegrable 0 T) (hf₂.intervalIntegrable 0 T)]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    dsimp [f₁, f₂]
    ring
  have hint_le :
      |∫ t in (0 : ℝ)..T, (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) /
          (c ^ 2 + t ^ 2)| ≤
        Real.pi / 2 + 4 := by
    rw [heq_sum]
    exact (abs_add_le _ _).trans (add_le_add (integral_cos_div_le_pi_div_two hc hT)
      (integral_sin_div_le_four hc hT))
  have hpi_le : (Real.pi / 2 + 4) / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  calc
    y ^ c / Real.pi *
        |∫ t in (0 : ℝ)..T, (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) /
          (c ^ 2 + t ^ 2)|
        ≤ y ^ c / Real.pi * (Real.pi / 2 + 4) :=
      mul_le_mul_of_nonneg_left hint_le (div_nonneg (Real.rpow_pos_of_pos hy c).le Real.pi_pos.le)
    _ = ((Real.pi / 2 + 4) / Real.pi) * y ^ c := by ring
    _ ≤ 2 * y ^ c := mul_le_mul_of_nonneg_right hpi_le (Real.rpow_pos_of_pos hy c).le

private lemma harmonic_Icc_le_one_add_log (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ ≤ 1 + Real.log (max M 1 : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hmax_m : (max (m : ℝ) 1) = (m : ℝ) := max_eq_left (by exact_mod_cast hm_pos)
      have hmax_ms : (max ((m + 1 : ℕ) : ℝ) 1) = ((m + 1 : ℕ) : ℝ) :=
        max_eq_left (by exact_mod_cast (by omega : 1 ≤ m + 1))
      have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hstep : (((m + 1 : ℕ) : ℝ)⁻¹) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hm_r : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
        have hm1_r : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        have hdiv : (m : ℝ) / ((m + 1 : ℕ) : ℝ) > 0 := div_pos hm_r hm1_r
        have hlog := Real.log_le_sub_one_of_pos hdiv
        rw [Real.log_div hm_r.ne' hm1_r.ne'] at hlog
        have heq : 1 - (m : ℝ) / ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ)⁻¹ := by
          push_cast
          field_simp [hm1_r.ne']
          ring
        linarith
      rw [hsplit, Finset.sum_insert (by simp), hmax_ms]
      rw [hmax_m] at ih
      linarith

private lemma abs_log_div_ge_band {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (_hy_lo : x / 2 ≤ y) (hy_hi : y ≤ 2 * x) :
    |x - y| / (2 * x) ≤ |Real.log (x / y)| := by
  rcases le_total y x with hyx | hxy
  · have hratio : 0 < y / x := div_pos hy hx
    have hlog := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div hy.ne' hx.ne'] at hlog
    have hlog_xy : (x - y) / x ≤ Real.log (x / y) := by
      rw [Real.log_div hx.ne' hy.ne']
      have : (x - y) / x = 1 - y / x := by field_simp [hx.ne']
      linarith
    have h1 : |x - y| / (2 * x) ≤ (x - y) / x := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hx (by linarith)
    exact h1.trans (hlog_xy.trans (le_abs_self _))
  · have hratio : 0 < x / y := div_pos hx hy
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hlog_yx : (y - x) / y ≤ -Real.log (x / y) := by
      have : (y - x) / y = 1 - x / y := by field_simp [hy.ne']
      linarith
    have h1 : |x - y| / (2 * x) ≤ (y - x) / y := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hy_hi
    exact h1.trans (hlog_yx.trans (neg_le_abs _))

private lemma perron_harmonic_near_band_sum {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0) ≤
      12 * Real.log x := by
  let N : ℕ := ⌊x⌋₊
  let M : ℕ := ⌊2 * x⌋₊
  have hNM : N ≤ M := Nat.floor_mono (by linarith)
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  have hx_ge0 : 0 ≤ x := by linarith
  have hfl_le : (N : ℝ) ≤ x := Nat.floor_le hx_ge0
  have hx_lt_fl : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hIcc_split :
      Finset.Icc 1 M = Finset.Icc 1 N ∪ Finset.Icc (N + 1) M := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) M) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  rw [hIcc_split, Finset.sum_union hdisj]
  have hleft :
      (∑ n ∈ Finset.Icc 1 N, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
        1 + (1 + Real.log (max M 1 : ℝ)) := by
    let S1 : Finset ℕ := (Finset.Icc 1 N).filter (fun n ↦ n = N)
    let S2 : Finset ℕ := (Finset.Icc 1 N).filter (fun n ↦ n < N)
    have hS_eq : Finset.Icc 1 N = S1 ∪ S2 := by
      ext n
      simp only [S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      omega
    have hS_disj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [S1, S2, Finset.mem_filter] at hn1 hn2
      omega
    rw [hS_eq, Finset.sum_union hS_disj]
    have hS1_le : (∑ n ∈ S1, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤ 1 := by
      have hcard : S1.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦ by
        simp only [S1, Finset.mem_filter] at ha hb; omega
      have h1 : (∑ n ∈ S1, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
          S1.card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul S1 _ 1 fun n _ ↦ by
          split_ifs with h1
          · exact inv_le_one_of_one_le₀ h1
          · exact zero_le_one
      have h2 : (S1.card • (1 : ℝ)) ≤ 1 := by
        simpa [nsmul_eq_mul] using (Nat.cast_le (α := ℝ)).mpr hcard
      exact h1.trans h2
    have hS2_le :
        (∑ n ∈ S2, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
          ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ := by
      have h1 :
          (∑ n ∈ S2, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
            ∑ n ∈ S2, (((N - n : ℕ) : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        simp only [S2, Finset.mem_filter, Finset.mem_Icc] at hn
        split_ifs with h1
        · have hk_pos : (0 : ℝ) < ((N - n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - n)
          have hle : ((N - n : ℕ) : ℝ) ≤ |x - (n : ℝ)| := by
            have hn_le : (n : ℝ) ≤ N := by exact_mod_cast hn.2.le
            have heq_sub : ((N - n : ℕ) : ℝ) = (N : ℝ) - n := Nat.cast_sub hn.2.le
            rw [heq_sub, abs_of_nonneg (by linarith)]
            linarith
          exact inv_anti₀ hk_pos hle
        · positivity
      have h2 :
          (∑ n ∈ S2, (((N - n : ℕ) : ℝ)⁻¹)) = ∑ k ∈ S2.image (fun n ↦ N - n), (k : ℝ)⁻¹ := by
        refine (Finset.sum_image (f := fun k : ℕ ↦ (k : ℝ)⁻¹) fun a ha b hb hab ↦ ?_).symm
        dsimp only [S2] at ha hb
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
        omega
      have hsub : S2.image (fun n ↦ N - n) ⊆ Finset.Icc 1 M := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
        simp only [S2, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        omega
      have h3 : (∑ k ∈ S2.image (fun n ↦ N - n), (k : ℝ)⁻¹) ≤ ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
      exact h1.trans (h2 ▸ h3)
    exact add_le_add hS1_le (hS2_le.trans (harmonic_Icc_le_one_add_log M))
  have hright :
      (∑ n ∈ Finset.Icc (N + 1) M, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
        1 + (1 + Real.log (max M 1 : ℝ)) := by
    let T1 : Finset ℕ := (Finset.Icc (N + 1) M).filter (fun n ↦ n = N + 1)
    let T2 : Finset ℕ := (Finset.Icc (N + 1) M).filter (fun n ↦ N + 1 < n)
    have hT_eq : Finset.Icc (N + 1) M = T1 ∪ T2 := by
      ext n
      simp only [T1, T2, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      omega
    have hT_disj : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [T1, T2, Finset.mem_filter] at hn1 hn2
      omega
    rw [hT_eq, Finset.sum_union hT_disj]
    have hT1_le : (∑ n ∈ T1, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤ 1 := by
      have hcard : T1.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦ by
        simp only [T1, Finset.mem_filter] at ha hb; omega
      have h1 : (∑ n ∈ T1, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
          T1.card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul T1 _ 1 fun n _ ↦ by
          split_ifs with h1
          · exact inv_le_one_of_one_le₀ h1
          · exact zero_le_one
      have h2 : (T1.card • (1 : ℝ)) ≤ 1 := by
        simpa [nsmul_eq_mul] using (Nat.cast_le (α := ℝ)).mpr hcard
      exact h1.trans h2
    have hT2_le :
        (∑ n ∈ T2, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
          ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ := by
      have h1 :
          (∑ n ∈ T2, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0)) ≤
            ∑ n ∈ T2, (((n - (N + 1) : ℕ) : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        simp only [T2, Finset.mem_filter, Finset.mem_Icc] at hn
        split_ifs with h1
        · have hk_pos : (0 : ℝ) < ((n - (N + 1) : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 0 < n - (N + 1))
          have hle : ((n - (N + 1) : ℕ) : ℝ) ≤ |x - (n : ℝ)| := by
            have heq_sub : ((n - (N + 1) : ℕ) : ℝ) = (n : ℝ) - ((N : ℝ) + 1) := by
              rw [Nat.cast_sub hn.2.le]
              push_cast
              ring
            rw [heq_sub, abs_sub_comm, abs_of_nonneg (by
              have hleN1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn.2.le
              linarith)]
            linarith
          exact inv_anti₀ hk_pos hle
        · positivity
      have h2 :
          (∑ n ∈ T2, (((n - (N + 1) : ℕ) : ℝ)⁻¹)) =
            ∑ k ∈ T2.image (fun n ↦ n - (N + 1)), (k : ℝ)⁻¹ := by
        refine (Finset.sum_image (f := fun k : ℕ ↦ (k : ℝ)⁻¹) fun a ha b hb hab ↦ ?_).symm
        dsimp only [T2] at ha hb
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
        omega
      have hsub : T2.image (fun n ↦ n - (N + 1)) ⊆ Finset.Icc 1 M := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
        simp only [T2, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        omega
      have h3 : (∑ k ∈ T2.image (fun n ↦ n - (N + 1)), (k : ℝ)⁻¹) ≤
          ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
      exact h1.trans (h2 ▸ h3)
    exact add_le_add hT1_le (hT2_le.trans (harmonic_Icc_le_one_add_log M))
  have hlogM : Real.log (max M 1 : ℝ) ≤ Real.log 2 + Real.log x := by
    have hmax_le : (max M 1 : ℝ) ≤ 2 * x := by
      have hM_le : (M : ℝ) ≤ 2 * x := Nat.floor_le (by positivity)
      exact max_le hM_le (by linarith)
    calc
      Real.log (max M 1 : ℝ) ≤ Real.log (2 * x) :=
        Real.log_le_log (by positivity) hmax_le
      _ = Real.log 2 + Real.log x := Real.log_mul two_ne_zero (by linarith)
  have h1_le : (1 : ℝ) ≤ 2 * Real.log x := by linarith
  linarith [hleft, hright, hlogM, hlogx, h1_le]

/-- General truncated Perron formula for `Λ` at arbitrary `x ≥ 2`, `1 < c`, and `0 < T`,
combining the uniform Perron kernel bound for `|x - n| < 1` with `|x - n| ≥ 1` near-band sums
and tail `L`-series convergence. -/
theorem perron_truncated_vonMangoldt_of_abscissa {x c T : ℝ}
    (hx : 2 ≤ x) (hc : 1 < c) (hT : 0 < T) :
    ‖dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T - (Chebyshev.psi x : ℂ)‖ ≤
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) +
        (96 / Real.pi) * (2 ^ c * x * (Real.log x) ^ 2 / T) +
        12 * 2 ^ c * Real.log x := by
  have hx_pos : 0 < x := by linarith
  have hc_pos : 0 < c := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le hlog2_pos hlogx_ge
  have ha : LSeriesSummable (fun n : ℕ ↦ (Λ n : ℂ)) (c : ℂ) := by
    rw [AnalyticNumberTheory.DirichletSeries.LSeriesSummable_vonMangoldt_iff]
    simpa using hc
  have htsum_int := dirichletContourIntegral_eq_tsum hx_pos hc_pos hT.le ha
  have hpsi_eq : (Chebyshev.psi x : ℂ) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) := by
    rw [psi_eq_sum_Icc]
    push_cast
    rfl
  let target : ℕ → ℂ := fun n ↦ if 1 ≤ n ∧ n ≤ ⌊x⌋₊ then (Λ n : ℂ) else 0
  have hpsi_tsum : (Chebyshev.psi x : ℂ) = ∑' n : ℕ, target n := by
    rw [hpsi_eq, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
    · refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn' := Finset.mem_Icc.mp hn
      simp [target, hn'.1, hn'.2]
    · intro n hn
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      by_cases h1 : 1 ≤ n
      · simp [target, h1, (hn h1).not_ge]
      · simp [target, h1]
  have hsumm_target : Summable target :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) fun n hn ↦ by
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      by_cases h1 : 1 ≤ n
      · simp [target, h1, (hn h1).not_ge]
      · simp [target, h1]
  let kernTerm : ℕ → ℂ := fun n ↦
    if n = 0 then 0 else (Λ n : ℂ) * perronKernel (x / n) c T
  have hkern_norm_le : ∀ n : ℕ,
      ⌊2 * x⌋₊ < n → ‖kernTerm n‖ ≤ (x ^ c / (Real.pi * T * Real.log 2)) *
        ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have h2x_lt : 2 * x < n := (Nat.floor_lt (by positivity)).mp hn
    have hy_pos : 0 < x / n := div_pos hx_pos hn_pos
    have hy_lt : x / n < 1 / 2 := (div_lt_iff₀ hn_pos).mpr (by linarith)
    have hy_lt1 : x / n < 1 := by linarith
    have hk_le := norm_perronKernel_lt_one_le hy_pos hy_lt1 hc_pos hT
    have hlog_ge : Real.log 2 ≤ |Real.log (x / n)| := by
      have hlog_neg : Real.log (x / n) ≤ Real.log (1 / 2) := Real.log_le_log hy_pos hy_lt.le
      rw [one_div, Real.log_inv] at hlog_neg
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hpk_le : ‖perronKernel (x / n) c T‖ ≤ (x / n) ^ c / (Real.pi * T * Real.log 2) := by
      refine hk_le.trans ?_
      gcongr
    have hpow : (x / n) ^ c = x ^ c / (n : ℝ) ^ c := Real.div_rpow hx_pos.le hn_pos.le c
    have hterm_norm : ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ = |Λ n| / (n : ℝ) ^ c := by
      rw [LSeries.term_of_ne_zero hn0, norm_div, Complex.norm_real,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0)]
      simp
    dsimp [kernTerm]
    rw [ite_eq_right_iff.mpr (fun h ↦ False.elim (hn0 h)), norm_mul, Complex.norm_real, hterm_norm]
    calc
      |Λ n| * ‖perronKernel (x / n) c T‖
          ≤ |Λ n| * ((x / n) ^ c / (Real.pi * T * Real.log 2)) :=
        mul_le_mul_of_nonneg_left hpk_le (abs_nonneg _)
      _ = (x ^ c / (Real.pi * T * Real.log 2)) * (|Λ n| / (n : ℝ) ^ c) := by
          rw [hpow]; ring
  have hsumm_kern_norm : Summable (fun n ↦ ‖kernTerm n‖) := by
    have hdom : Summable fun n ↦
        (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ :=
      ha.norm.mul_left _
    have hhead : Summable fun n : ℕ ↦ if n ≤ ⌊2 * x⌋₊ then ‖kernTerm n‖ else 0 :=
      summable_of_ne_finset_zero (s := Finset.Icc 0 ⌊2 * x⌋₊) fun n hn ↦ by
        simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le] at hn
        simp [hn.not_ge]
    have htail : Summable fun n : ℕ ↦ if ⌊2 * x⌋₊ < n then ‖kernTerm n‖ else 0 :=
      hdom.of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity) fun n ↦ by
        split_ifs with hgt
        · exact hkern_norm_le n hgt
        · positivity
    refine (hhead.add htail).congr fun n ↦ ?_
    by_cases hle : n ≤ ⌊2 * x⌋₊
    · simp [hle, hle.not_gt]
    · have hgt : ⌊2 * x⌋₊ < n := lt_of_not_ge hle
      simp [hle, hgt]
  have hsumm_kern : Summable kernTerm := hsumm_kern_norm.of_norm
  let errTerm : ℕ → ℂ := fun n ↦ kernTerm n - target n
  have hsumm_err_norm : Summable (fun n ↦ ‖errTerm n‖) :=
    (hsumm_kern_norm.add hsumm_target.norm).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ norm_sub_le _ _
  have hdiff_eq :
      dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T - (Chebyshev.psi x : ℂ) =
        ∑' n : ℕ, errTerm n := by
    rw [htsum_int, hpsi_tsum, ← hsumm_kern.tsum_sub hsumm_target]
  have hnorm_tsum : ‖∑' n : ℕ, errTerm n‖ ≤ ∑' n : ℕ, ‖errTerm n‖ :=
    norm_tsum_le_tsum_norm hsumm_err_norm
  rw [hdiff_eq]
  refine hnorm_tsum.trans ?_
  let B : Finset ℕ := Finset.Icc 1 ⌊2 * x⌋₊
  let tailB : ℕ → ℝ := fun n ↦
    if n ∉ B ∨ (n : ℝ) < x / 2 then ‖errTerm n‖ else 0
  let closeB : ℕ → ℝ := fun n ↦
    if n ∈ B ∧ x / 2 ≤ n ∧ |x - (n : ℝ)| < 1 then ‖errTerm n‖ else 0
  let farB : ℕ → ℝ := fun n ↦
    if n ∈ B ∧ x / 2 ≤ n ∧ 1 ≤ |x - (n : ℝ)| then ‖errTerm n‖ else 0
  have hpoint : ∀ n : ℕ, ‖errTerm n‖ = tailB n + closeB n + farB n := by
    intro n
    dsimp [tailB, closeB, farB]
    by_cases hnB : n ∈ B
    · by_cases hhalf : x / 2 ≤ (n : ℝ)
      · by_cases hclose : |x - (n : ℝ)| < 1
        · simp [hnB, hhalf, hhalf.not_gt, hclose, hclose.not_ge]
        · have hge1 : 1 ≤ |x - (n : ℝ)| := le_of_not_gt hclose
          simp [hnB, hhalf, hhalf.not_gt, hclose, hge1]
      · have hlt : (n : ℝ) < x / 2 := lt_of_not_ge hhalf
        simp [hnB, hhalf, hlt]
    · simp [hnB]
  have hsumm_tail : Summable tailB :=
    hsumm_err_norm.of_nonneg_of_le (fun n ↦ by dsimp [tailB]; split_ifs <;> positivity)
      fun n ↦ by dsimp [tailB]; split_ifs <;> simp [norm_nonneg]
  have hsumm_close : Summable closeB :=
    summable_of_ne_finset_zero (s := B) fun n hn ↦ by simp [closeB, hn]
  have hsumm_far : Summable farB :=
    summable_of_ne_finset_zero (s := B) fun n hn ↦ by simp [farB, hn]
  have htsum_split : ∑' n : ℕ, ‖errTerm n‖ = (∑' n, tailB n) + (∑' n, closeB n) + (∑' n, farB n) := by
    rw [tsum_congr hpoint, (hsumm_tail.add hsumm_close).tsum_add hsumm_far, hsumm_tail.tsum_add hsumm_close]
  rw [htsum_split]
  have htail_le : ∑' n : ℕ, tailB n ≤ (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) := by
    let trivTerm : ℕ → ℂ := fun n ↦
      LSeries.term (fun k : ℕ ↦ (1 : DirichletCharacter ℂ 1) k * (Λ k : ℂ)) (c : ℂ) n
    have htriv_norm : ∀ n : ℕ, ‖trivTerm n‖ = ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ := by
      intro n
      dsimp [trivTerm]
      congr 2
      ext k
      have hk1 : (1 : DirichletCharacter ℂ 1) k = 1 := by
        simp [Subsingleton.elim ((k : ZMod 1)) 1]
      rw [hk1, one_mul]
    have htriv_bound := tsum_norm_LSeries_term_twist_le (1 : DirichletCharacter ℂ 1) hc
    have hL_tsum : ∑' n : ℕ, ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ ≤ 4 / (c - 1) ^ 2 := by
      simpa only [← htriv_norm] using htriv_bound
    have hdom_summ : Summable fun n : ℕ ↦
        (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ :=
      ha.norm.mul_left _
    have hpoint_tail : ∀ n : ℕ,
        tailB n ≤ (x ^ c / (Real.pi * T * Real.log 2)) *
          ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ := by
      intro n
      dsimp [tailB]
      split_ifs with hcond
      · rcases eq_or_ne n 0 with rfl | hn0
        · simp [errTerm, kernTerm, target]
        · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have h1n : 1 ≤ n := Nat.pos_of_ne_zero hn0
          have hn_out : (n : ℝ) < x / 2 ∨ 2 * x < n := by
            rcases hcond with hnotB | hlt
            · simp only [B, Finset.mem_Icc, not_and, not_le] at hnotB
              right
              exact (Nat.floor_lt (by positivity)).mp (hnotB h1n)
            · left; exact hlt
          rcases hn_out with hlt | hgt
          · have hy_pos : 0 < x / n := div_pos hx_pos hn_pos
            have hy_gt2 : 2 < x / n := (lt_div_iff₀ hn_pos).mpr (by linarith)
            have hy_gt1 : 1 < x / n := by linarith
            have hn_le_fl : n ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx_pos.le).mpr (by linarith)
            have hk_le := norm_perronKernel_gt_one_sub_one_le hy_gt1 hc_pos hT
            have hlog_ge : Real.log 2 ≤ Real.log (x / n) := Real.log_le_log zero_lt_two hy_gt2.le
            have herr_eq : errTerm n = (Λ n : ℂ) * (perronKernel (x / n) c T - 1) := by
              dsimp [errTerm, kernTerm, target]
              simp only [hn0, ↓reduceIte, h1n, hn_le_fl, and_self]
              ring
            have hpow : (x / n) ^ c = x ^ c / (n : ℝ) ^ c := Real.div_rpow hx_pos.le hn_pos.le c
            have hterm_norm : ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ = |Λ n| / (n : ℝ) ^ c := by
              rw [LSeries.term_of_ne_zero hn0, norm_div, Complex.norm_real,
                Complex.norm_natCast_cpow_of_pos h1n]
              simp
            rw [herr_eq, norm_mul, Complex.norm_real, hterm_norm]
            calc
              |Λ n| * ‖perronKernel (x / n) c T - 1‖
                  ≤ |Λ n| * ((x / n) ^ c / (Real.pi * T * Real.log (x / n))) :=
                mul_le_mul_of_nonneg_left hk_le (abs_nonneg _)
              _ ≤ |Λ n| * ((x / n) ^ c / (Real.pi * T * Real.log 2)) := by
                  gcongr
              _ = (x ^ c / (Real.pi * T * Real.log 2)) * (|Λ n| / (n : ℝ) ^ c) := by
                  rw [hpow]; ring
          · have hfl_gt : ⌊2 * x⌋₊ < n := (Nat.floor_lt (by positivity)).mpr hgt
            have hnot_fl : ¬ (n ≤ ⌊x⌋₊) := by
              have : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_pos.le
              intro hle
              have : (n : ℝ) ≤ x := (Nat.cast_le.mpr hle).trans this
              linarith
            have herr_eq : errTerm n = kernTerm n := by
              dsimp [errTerm, target]
              simp [hnot_fl]
            rw [herr_eq]
            exact hkern_norm_le n hfl_gt
      · positivity
    calc
      ∑' n : ℕ, tailB n
          ≤ ∑' n : ℕ, (x ^ c / (Real.pi * T * Real.log 2)) *
              ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ :=
        hsumm_tail.tsum_le_tsum hpoint_tail hdom_summ
      _ = (x ^ c / (Real.pi * T * Real.log 2)) *
            ∑' n : ℕ, ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ := tsum_mul_left
      _ ≤ (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hL_tsum (by positivity)
      _ = (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) := by
          field_simp [Real.pi_ne_zero, hlog2_pos.ne', hT.ne', (sub_pos.mpr hc).ne']
  have hclose_le : ∑' n : ℕ, closeB n ≤ 12 * 2 ^ c * Real.log x := by
    let Cset : Finset ℕ := {⌊x⌋₊, ⌊x⌋₊ + 1}
    have htsum_eq : ∑' n : ℕ, closeB n = ∑ n ∈ Cset, closeB n := by
      refine tsum_eq_sum fun n hn ↦ ?_
      dsimp [closeB]
      split_ifs with hcond
      · exfalso
        have hlt := abs_sub_lt_iff.mp hcond.2.2
        have hx1 : x - 1 < (n : ℝ) := by linarith [hlt.1]
        have hx2 : (n : ℝ) < x + 1 := by linarith [hlt.2]
        have h1 : ⌊x⌋₊ ≤ n := by
          by_contra hlt_fl
          have hle : n + 1 ≤ ⌊x⌋₊ := by omega
          have h2 : (n : ℝ) + 1 ≤ x := by
            have : ((n + 1 : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_le.mpr hle
            push_cast at this
            exact this.trans (Nat.floor_le hx_pos.le)
          linarith
        have h2 : n ≤ ⌊x⌋₊ + 1 := by
          by_contra hgt_fl
          have hge : ⌊x⌋₊ + 2 ≤ n := by omega
          have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
          have h3 : (⌊x⌋₊ : ℝ) + 2 ≤ (n : ℝ) := by
            have := Nat.cast_le (α := ℝ).mpr hge
            push_cast at this
            exact this
          linarith
        have hmem : n ∈ Cset := by
          simp only [Cset, Finset.mem_insert, Finset.mem_singleton]
          omega
        exact hn hmem
      · rfl
    rw [htsum_eq]
    have hcard : Cset.card ≤ 2 := Finset.card_le_two
    have hterm_le : ∀ n ∈ Cset, closeB n ≤ 6 * 2 ^ c * Real.log x := by
      intro n _
      dsimp [closeB]
      split_ifs with hcond
      · have hn_pos : (0 : ℝ) < n := by
          have := (Finset.mem_Icc.mp hcond.1).1
          exact_mod_cast this
        have hn_le_2x : (n : ℝ) ≤ 2 * x :=
          (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hcond.1).2
        have hΛ_le : |Λ n| ≤ 2 * Real.log x := by
          rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          have h1 := ArithmeticFunction.vonMangoldt_le_log (n := n)
          have h2 : Real.log n ≤ Real.log (2 * x) := Real.log_le_log hn_pos hn_le_2x
          have h3 : Real.log (2 * x) = Real.log 2 + Real.log x :=
            Real.log_mul two_ne_zero hx_pos.ne'
          linarith [h1, h2, h3, hlogx_ge]
        have hy_pos : 0 < x / n := div_pos hx_pos hn_pos
        have hy_le_2 : x / n ≤ 2 := (div_le_iff₀ hn_pos).mpr (by linarith [hcond.2.1])
        have hpow_le : (x / n) ^ c ≤ 2 ^ c := Real.rpow_le_rpow hy_pos.le hy_le_2 hc_pos.le
        have h2c_ge1 : (1 : ℝ) ≤ 2 ^ c := Real.one_le_rpow one_le_two hc_pos.le
        have hpk_unif : ‖perronKernel (x / n) c T‖ ≤ 2 * 2 ^ c :=
          (norm_perronKernel_le_const_mul_rpow hy_pos hc_pos hT).trans (by gcongr)
        have herr_le : ‖errTerm n‖ ≤ |Λ n| * (2 * 2 ^ c + 1) := by
          dsimp [errTerm, kernTerm, target]
          have hn0 : n ≠ 0 := by
            have := (Finset.mem_Icc.mp hcond.1).1; omega
          simp only [hn0, ↓reduceIte]
          split_ifs
          · rw [← mul_sub_one, norm_mul, Complex.norm_real]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact (norm_sub_le _ _).trans (by simpa [norm_one] using add_le_add hpk_unif (le_refl (1 : ℝ)))
          · rw [sub_zero, norm_mul, Complex.norm_real]
            refine mul_le_mul_of_nonneg_left (hpk_unif.trans (by linarith)) (abs_nonneg _)
        have h3c : (2 : ℝ) * 2 ^ c + 1 ≤ 3 * 2 ^ c := by linarith
        calc
          ‖errTerm n‖ ≤ |Λ n| * (2 * 2 ^ c + 1) := herr_le
          _ ≤ (2 * Real.log x) * (3 * 2 ^ c) :=
            mul_le_mul hΛ_le h3c (by positivity) (by positivity)
          _ = 6 * 2 ^ c * Real.log x := by ring
      · positivity
    have h1 : ∑ n ∈ Cset, closeB n ≤ Cset.card • (6 * 2 ^ c * Real.log x) :=
      Finset.sum_le_card_nsmul Cset _ _ hterm_le
    have h2 : (Cset.card • (6 * 2 ^ c * Real.log x)) = (Cset.card : ℝ) * (6 * 2 ^ c * Real.log x) := by
      simp [nsmul_eq_mul]
    have h3 : (Cset.card : ℝ) * (6 * 2 ^ c * Real.log x) ≤ 2 * (6 * 2 ^ c * Real.log x) := by
      have hcard_r : (Cset.card : ℝ) ≤ 2 := Nat.cast_le.mpr hcard
      exact mul_le_mul_of_nonneg_right hcard_r (by positivity)
    exact (h1.trans_eq h2).trans (h3.trans_eq (by ring))
  have hfar_le : ∑' n : ℕ, farB n ≤ (96 / Real.pi) * (2 ^ c * x * (Real.log x) ^ 2 / T) := by
    have htsum_eq : ∑' n : ℕ, farB n = ∑ n ∈ B, farB n := by
      refine tsum_eq_sum fun n hn ↦ ?_
      simp [farB, hn]
    rw [htsum_eq]
    have hpoint_far : ∀ n ∈ B, farB n ≤
        ((8 * 2 ^ c * x * Real.log x) / (Real.pi * T)) *
          (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0) := by
      intro n hn
      dsimp [farB]
      split_ifs with hcond h1
      · have hn_pos : (0 : ℝ) < n := by
          exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hn_le_2x : (n : ℝ) ≤ 2 * x :=
          (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
        have hΛ_le : |Λ n| ≤ 2 * Real.log x := by
          rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          have h1' := ArithmeticFunction.vonMangoldt_le_log (n := n)
          have h2' : Real.log n ≤ Real.log (2 * x) := Real.log_le_log hn_pos hn_le_2x
          have h3' : Real.log (2 * x) = Real.log 2 + Real.log x :=
            Real.log_mul two_ne_zero hx_pos.ne'
          linarith [h1', h2', h3', hlogx_ge]
        have hy_pos : 0 < x / n := div_pos hx_pos hn_pos
        have hy_le_2 : x / n ≤ 2 := (div_le_iff₀ hn_pos).mpr (by linarith [hcond.2.1])
        have hpow_le : (x / n) ^ c ≤ 2 ^ c := Real.rpow_le_rpow hy_pos.le hy_le_2 hc_pos.le
        have hband := abs_log_div_ge_band hx_pos hn_pos hcond.2.1 hn_le_2x
        have hxn_pos : 0 < |x - (n : ℝ)| := lt_of_lt_of_le zero_lt_one h1
        have hlog_pos : 0 < |Real.log (x / n)| := lt_of_lt_of_le (by positivity) hband
        have hpk_le : ‖errTerm n‖ ≤ |Λ n| * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) := by
          dsimp [errTerm, kernTerm, target]
          have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          simp only [hn0, ↓reduceIte]
          rcases lt_or_gt_of_ne (sub_ne_zero.mp (abs_pos.mp hxn_pos)) with hlt | hgt
          · -- `x < n`
            have hy1 : x / n < 1 := (div_lt_one hn_pos).mpr hlt
            have hnot_fl : ¬ (n ≤ ⌊x⌋₊) := by
              intro hle
              have : (n : ℝ) ≤ x := (Nat.cast_le.mpr hle).trans (Nat.floor_le hx_pos.le)
              linarith
            have hcond_fl : ¬ (1 ≤ n ∧ n ≤ ⌊x⌋₊) := fun h ↦ hnot_fl h.2
            simp only [hcond_fl, ↓reduceIte, sub_zero, norm_mul, Complex.norm_real]
            exact mul_le_mul_of_nonneg_left (norm_perronKernel_lt_one_le hy_pos hy1 hc_pos hT)
              (abs_nonneg _)
          · -- `n < x`
            have hy1 : 1 < x / n := (one_lt_div hn_pos).mpr hgt
            have hn_le_fl : n ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx_pos.le).mpr hgt.le
            have hcond_fl : 1 ≤ n ∧ n ≤ ⌊x⌋₊ := ⟨(Finset.mem_Icc.mp hn).1, hn_le_fl⟩
            simp only [hcond_fl, and_self, ↓reduceIte]
            rw [← mul_sub_one, norm_mul, Complex.norm_real]
            have hpk := norm_perronKernel_gt_one_sub_one_le hy1 hc_pos hT
            rw [abs_of_pos (Real.log_pos hy1)]
            exact mul_le_mul_of_nonneg_left hpk (abs_nonneg _)
        have hquot_le :
            (x / n) ^ c / (Real.pi * T * |Real.log (x / n)|) ≤
              2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|) := by
          calc
            (x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)
                ≤ 2 ^ c / (Real.pi * T * (|x - (n : ℝ)| / (2 * x))) := by
                  refine div_le_div₀ (by positivity) hpow_le
                    (mul_pos (mul_pos Real.pi_pos hT) (by positivity)) (by gcongr)
            _ = 2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|) := by
                  field_simp [Real.pi_ne_zero, hT.ne', hx_pos.ne', hxn_pos.ne']
        have hscale :
            (2 * Real.log x) * (2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|)) =
              4 * (2 ^ c * x * Real.log x / (Real.pi * T) * |x - (n : ℝ)|⁻¹) := by
          field_simp [Real.pi_ne_zero, hT.ne', hxn_pos.ne']
          ring
        have hscale8 :
            ((8 * 2 ^ c * x * Real.log x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹ =
              8 * (2 ^ c * x * Real.log x / (Real.pi * T) * |x - (n : ℝ)|⁻¹) := by
          ring
        calc
          ‖errTerm n‖ ≤ |Λ n| * (2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|)) :=
            hpk_le.trans (mul_le_mul_of_nonneg_left hquot_le (abs_nonneg _))
          _ ≤ (2 * Real.log x) * (2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|)) := by gcongr
          _ = 4 * (2 ^ c * x * Real.log x / (Real.pi * T) * |x - (n : ℝ)|⁻¹) := hscale
          _ ≤ 8 * (2 ^ c * x * Real.log x / (Real.pi * T) * |x - (n : ℝ)|⁻¹) := by
              have hnn : 0 ≤ 2 ^ c * x * Real.log x / (Real.pi * T) * |x - (n : ℝ)|⁻¹ := by
                positivity
              linarith
          _ = ((8 * 2 ^ c * x * Real.log x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹ := hscale8.symm
      · exfalso; exact h1 hcond.2.2
      · positivity
      · positivity
    calc
      ∑ n ∈ B, farB n
          ≤ ∑ n ∈ B, ((8 * 2 ^ c * x * Real.log x) / (Real.pi * T)) *
              (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0) :=
        Finset.sum_le_sum hpoint_far
      _ = ((8 * 2 ^ c * x * Real.log x) / (Real.pi * T)) *
            ∑ n ∈ B, (if 1 ≤ |x - (n : ℝ)| then |x - (n : ℝ)|⁻¹ else 0) := by
          rw [← Finset.mul_sum]
      _ ≤ ((8 * 2 ^ c * x * Real.log x) / (Real.pi * T)) * (12 * Real.log x) :=
          mul_le_mul_of_nonneg_left (perron_harmonic_near_band_sum hx) (by positivity)
      _ = (96 / Real.pi) * (2 ^ c * x * (Real.log x) ^ 2 / T) := by ring
  linarith [htail_le, hclose_le, hfar_le]

/-- Canonical truncated Perron formula for `Λ` at `c = 1 + 1 / Real.log x` for all `x ≥ 2` and
`T > 0`, giving the bound `C * (x * (log x)^2 / T + log x)`. -/
theorem perron_truncated_vonMangoldt {x T : ℝ} (hx : 2 ≤ x) (hT : 0 < T) :
    let c : ℝ := 1 + 1 / Real.log x
    ‖dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T - (Chebyshev.psi x : ℂ)‖ ≤
      900 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  intro c
  have hx_pos : 0 < x := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le hlog2_pos hlogx_ge
  have hc_gt : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlogx_pos]
  have hc_le : c ≤ 3 := by
    dsimp [c]
    have hinv_le : 1 / Real.log x ≤ 2 := by
      rw [div_le_iff₀ hlogx_pos]
      linarith
    linarith
  have hpow_2 : (2 : ℝ) ^ c ≤ 8 := by
    calc
      (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hc_le
      _ = 8 := by norm_num
  have hpow_x : x ^ c = x * Real.exp 1 := by
    dsimp [c]
    rw [Real.rpow_add hx_pos, Real.rpow_one]
    congr 1
    rw [Real.rpow_def_of_pos hx_pos, mul_one_div_cancel hlogx_pos.ne']
  have hexp_le : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hcm1 : 1 / (c - 1) ^ 2 = (Real.log x) ^ 2 := by
    dsimp [c]
    have h1 : 1 + 1 / Real.log x - 1 = 1 / Real.log x := by ring
    rw [h1]
    field_simp [hlogx_pos.ne']
  have hmain := perron_truncated_vonMangoldt_of_abscissa hx hc_gt hT
  have hterm1 :
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) ≤
        20 * (x * (Real.log x) ^ 2 / T) := by
    have hcoef : 4 / (Real.pi * Real.log 2) ≤ 4 / (3 * (1 / 2 : ℝ)) := by
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      exact mul_le_mul Real.pi_gt_three.le hlog2_gt.le (by norm_num) (by positivity)
    have hval : x ^ c / (T * (c - 1) ^ 2) ≤ 3 * (x * (Real.log x) ^ 2 / T) := by
      have heq : x ^ c / (T * (c - 1) ^ 2) = Real.exp 1 * (x * (Real.log x) ^ 2 / T) := by
        rw [hpow_x]
        have heq_inv : ((c - 1) ^ 2)⁻¹ = (Real.log x) ^ 2 := by simpa [one_div] using hcm1
        field_simp [hT.ne', (sub_pos.mpr hc_gt).ne']
        have hcm1' : (c - 1) ^ 2 = ((Real.log x) ^ 2)⁻¹ := by
          have : (c - 1) ^ 2 * (Real.log x) ^ 2 = 1 := by
            have := congrArg (fun z ↦ (c - 1) ^ 2 * z) hcm1
            have hne : (c - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_pos.mpr hc_gt).ne'
            field_simp [hne] at this
            linarith
          exact eq_inv_of_mul_eq_one_left this
        rw [hcm1']
        field_simp [hlogx_pos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_right hexp_le (by positivity)
    calc
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2))
          ≤ (4 / (3 * (1 / 2 : ℝ))) * (3 * (x * (Real.log x) ^ 2 / T)) :=
        mul_le_mul hcoef hval (by positivity) (by positivity)
      _ ≤ 20 * (x * (Real.log x) ^ 2 / T) := by
          have hnn : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
          linarith
  have hterm2 :
      (96 / Real.pi) * (2 ^ c * x * (Real.log x) ^ 2 / T) ≤
        260 * (x * (Real.log x) ^ 2 / T) := by
    have hcoef : 96 / Real.pi ≤ 96 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
    calc
      (96 / Real.pi) * (2 ^ c * x * (Real.log x) ^ 2 / T)
          ≤ (96 / 3) * (8 * x * (Real.log x) ^ 2 / T) := by gcongr
      _ = 256 * (x * (Real.log x) ^ 2 / T) := by ring
      _ ≤ 260 * (x * (Real.log x) ^ 2 / T) := by
          have : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
          linarith
  have hterm3 : 12 * 2 ^ c * Real.log x ≤ 96 * Real.log x := by
    nlinarith [hpow_2, hlogx_pos]
  linarith [hmain, hterm1, hterm2, hterm3,
    show 0 ≤ x * (Real.log x) ^ 2 / T by positivity, hlogx_pos]

/-- Half-integer specialization `x = N + 1 / 2` (`N ≥ 2`) of the truncated Perron formula for
`Λ`, avoiding the `|x - n| < 1` close-hit log term and yielding pure `O(x * (log x)^2 / T)`
truncation error. -/
theorem perron_truncated_half_integer_vonMangoldt {N : ℕ} {c T : ℝ}
    (_hN : 2 ≤ N) (hc : 1 < c) (hT : 0 < T) :
    let x : ℝ := N + 1 / 2
    ‖dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T - (Chebyshev.psi x : ℂ)‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) +
        (2 ^ c * (4 * x) / (Real.pi * T)) * ((Real.log 4 + 4) * (2 * N + 1 : ℕ)) := by
  intro x
  have ha : LSeriesSummable (fun n : ℕ ↦ (Λ n : ℂ)) (c : ℂ) := by
    rw [AnalyticNumberTheory.DirichletSeries.LSeriesSummable_vonMangoldt_iff]
    simpa using hc
  have hhalf := perron_truncated_half_integer (N := N) (by linarith : 0 < c) hT ha
  dsimp only at hhalf
  have hx_ge0 : 0 ≤ x := by dsimp [x]; positivity
  have hfloor : ⌊x⌋₊ = N := by
    rw [Nat.floor_eq_iff hx_ge0]
    dsimp [x]
    constructor <;> linarith
  have hpsi_eq : (Chebyshev.psi x : ℂ) = ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) := by
    rw [psi_eq_sum_Icc, hfloor]
    push_cast
    rfl
  rw [hpsi_eq]
  refine hhalf.trans ?_
  have htriv_bound :
      ∑' n : ℕ, ‖LSeries.term (fun k : ℕ ↦ (Λ k : ℂ)) (c : ℂ) n‖ ≤ 4 / (c - 1) ^ 2 := by
    have htriv_norm : ∀ n : ℕ,
        ‖LSeries.term (fun k : ℕ ↦ (1 : DirichletCharacter ℂ 1) k * (Λ k : ℂ)) (c : ℂ) n‖ =
          ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ := by
      intro n
      congr 2
      ext k
      have hk1 : (1 : DirichletCharacter ℂ 1) k = 1 := by
        simp [Subsingleton.elim ((k : ZMod 1)) 1]
      rw [hk1, one_mul]
    simpa only [htriv_norm] using tsum_norm_LSeries_term_twist_le (1 : DirichletCharacter ℂ 1) hc
  have hsum_lam :
      ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖(Λ n : ℂ)‖ ≤ (Real.log 4 + 4) * ((2 * N + 1 : ℕ) : ℝ) := by
    have heq_psi : ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖(Λ n : ℂ)‖ =
        Chebyshev.psi ((2 * N + 1 : ℕ) : ℝ) := by
      rw [psi_eq_sum_Icc, Nat.floor_natCast]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [heq_psi]
    exact psi_le_const_mul_self (Nat.cast_nonneg _)
  have h1 : (x ^ c / (Real.pi * T * Real.log 2)) *
        ∑' n : ℕ, ‖LSeries.term (fun k ↦ (Λ k : ℂ)) (c : ℂ) n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) := by
    have hpos : 0 ≤ x ^ c / (Real.pi * T * Real.log 2) := by
      have : 0 < Real.log 2 := Real.log_pos one_lt_two
      positivity
    exact mul_le_mul_of_nonneg_left htriv_bound hpos
  have h2 :
      (2 ^ c * (4 * x) / (Real.pi * T)) * ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖(Λ n : ℂ)‖ ≤
        (2 ^ c * (4 * x) / (Real.pi * T)) * ((Real.log 4 + 4) * (2 * N + 1 : ℕ)) := by
    have hpos : 0 ≤ 2 ^ c * (4 * x) / (Real.pi * T) := by positivity
    exact mul_le_mul_of_nonneg_left hsum_lam hpos
  exact add_le_add h1 h2

/-! ### Section 2a: Local Zero Counting, Nontrivial Zero Sets, and Horizontal Contour Selection -/

/-- The multiplicity of `ρ` as a zero of `riemannZeta` (computed via `analyticOrderNatAt`). -/
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ

private lemma analyticAt_xi_prefactor {ρ : ℂ} (hre0 : 0 < ρ.re) :
    AnalyticAt ℂ (fun s : ℂ ↦ (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) *
      Complex.Gamma (s / 2)) ρ := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) Set.univ := by
    have heq : (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) =
        fun s : ℂ ↦ Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2)) := by
      ext s
      exact Complex.cpow_def_of_ne_zero hpi0 _
    have hdiff : Differentiable ℂ fun s : ℂ ↦ Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2)) :=
      fun s ↦ DifferentiableAt.cexp (by fun_prop)
    rw [heq]
    exact hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hgam : AnalyticOnNhd ℂ (fun s : ℂ ↦ Complex.Gamma (s / 2)) {s : ℂ | 0 < s.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    change 0 < s.re at hs
    have hs2 : 0 < (s / 2).re := by
      have hre : (s / 2).re = s.re / 2 := by simp
      rw [hre]; linarith
    have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m h
      have hre := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hdiff := (Complex.differentiableAt_Gamma (s / 2) hne).comp s
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ w / 2) s)
    exact hdiff.differentiableWithinAt
  have hgam_at : AnalyticAt ℂ (fun s : ℂ ↦ Complex.Gamma (s / 2)) ρ := hgam ρ hre0
  have hpow_at : AnalyticAt ℂ (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) ρ := hpow ρ (Set.mem_univ _)
  have hpoly : AnalyticAt ℂ (fun s : ℂ ↦ (1 / 2 : ℂ) * s * (s - 1)) ρ :=
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.sub analyticAt_const))
  exact (hpoly.mul hpow_at).mul hgam_at

private lemma xi_prefactor_ne_zero {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    (1 / 2 : ℂ) * ρ * (ρ - 1) * (Real.pi : ℂ) ^ (-ρ / 2) * Complex.Gamma (ρ / 2) ≠ 0 := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hρ0 : ρ ≠ 0 := fun h ↦ by simp [h] at hre0
  have hρ1 : ρ - 1 ≠ 0 := fun h ↦ by
    have hre := congrArg Complex.re (sub_eq_zero.mp h)
    simp at hre
    linarith
  have hpow : (Real.pi : ℂ) ^ (-ρ / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi0]
    exact Complex.exp_ne_zero _
  have hgam : Complex.Gamma (ρ / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    have : (ρ / 2).re = ρ.re / 2 := by simp
    rw [this]; linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hρ0) hρ1) hpow) hgam

/-- Inside the critical strip `0 < ρ.re < 1`, `zeroMultiplicity ρ` equals `analyticOrderNatAt xi ρ`. -/
theorem zeroMultiplicity_eq_xi {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    zeroMultiplicity ρ = analyticOrderNatAt xi ρ := by
  let pref : ℂ → ℂ := fun s ↦
    (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
  have hU : {s : ℂ | (0 : ℝ) < s.re} ∩ {s : ℂ | s.re < (1 : ℝ)} ∈ 𝓝 ρ :=
    (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hre0, hre1⟩
  have hev : xi =ᶠ[𝓝 ρ] (fun s ↦ pref s * riemannZeta s) := by
    refine eventually_of_mem hU fun s hs ↦ ?_
    have hs_lo : (0 : ℝ) < s.re := hs.1
    have hs_hi : s.re < (1 : ℝ) := hs.2
    have hs_m : ∀ m : ℕ, s ≠ -2 * (m : ℂ) := by
      intro m h
      have hre : s.re = (-2 * (m : ℂ)).re := congrArg Complex.re h
      have hmr : (-2 * (m : ℂ)).re = -2 * (m : ℝ) := by simp
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hs1 : s ≠ 1 := fun h ↦ by
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    simpa [pref, mul_assoc] using xi_eq_formula hs_m hs1
  have hpref_an : AnalyticAt ℂ pref ρ := analyticAt_xi_prefactor hre0
  have hzeta_an : AnalyticAt ℂ riemannZeta ρ := by
    have hdiff : DifferentiableOn ℂ riemannZeta {1}ᶜ := by
      intro s hs
      exact (differentiableAt_riemannZeta hs).differentiableWithinAt
    have han := hdiff.analyticOnNhd (isOpen_compl_singleton)
    exact han ρ fun h ↦ by
      have hre := congrArg Complex.re (Set.mem_singleton_iff.mp h)
      simp at hre
      linarith
  have hxi_an : AnalyticAt ℂ xi ρ := analyticOnNhd_xi ρ (Set.mem_univ _)
  have hpref_ord0 : analyticOrderAt pref ρ = 0 :=
    hpref_an.analyticOrderAt_eq_zero.mpr (xi_prefactor_ne_zero hre0 hre1)
  have hord : analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_congr hev]
    change analyticOrderAt (pref * riemannZeta) ρ = analyticOrderAt riemannZeta ρ
    rw [analyticOrderAt_mul hpref_an hzeta_an, hpref_ord0, zero_add]
  simp only [zeroMultiplicity, analyticOrderNatAt, hord]

/-- Inside `0 < ρ.re < 1`, `0 < zeroMultiplicity ρ` holds if and only if `riemannZeta ρ = 0`. -/
theorem zeroMultiplicity_pos_iff {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    0 < zeroMultiplicity ρ ↔ riemannZeta ρ = 0 := by
  rw [zeroMultiplicity_eq_xi hre0 hre1]
  have hxi_an : AnalyticAt ℂ xi ρ := analyticOnNhd_xi ρ (Set.mem_univ _)
  have hxi_ntop : analyticOrderAt xi ρ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_differentiable_ne_zero differentiable_xi
      (fun h ↦ xi_ne_zero_of_re_nonpos (s := 0) (by simp) (by simpa using congrFun h 0)) ρ
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro hne
    exact (xi_eq_zero_iff.mp (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)).1
  · intro hz
    have hxi0 : xi ρ = 0 := xi_eq_zero_iff.mpr ⟨hz, hre0, hre1⟩
    have hord_ne : analyticOrderAt xi ρ ≠ 0 := hxi_an.analyticOrderAt_ne_zero.mpr hxi0
    intro hnat0
    have hcast : (analyticOrderNatAt xi ρ : ℕ∞) = analyticOrderAt xi ρ :=
      Nat.cast_analyticOrderNatAt hxi_ntop
    rw [hnat0, ENat.natCast_zero] at hcast
    exact hord_ne hcast.symm

private lemma xi_center_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ τ : ℝ,
      c₀ * Real.exp (-(Real.pi / 4) * |τ|) ≤ ‖xi ((2 : ℂ) + (τ : ℂ) * I)‖ := by
  let φ : ℝ → ℝ := fun t ↦ ‖Complex.Gamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖
  have hφ_cont : Continuous φ := by
    refine Continuous.norm ?_
    rw [continuous_iff_continuousAt]
    intro t
    have hne : ∀ m : ℕ, (1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I ≠ -(m : ℂ) := by
      intro m h
      have hre : ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I).re = (-(m : ℂ)).re := congrArg Complex.re h
      have h1re : ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I).re = 1 := by simp
      have hmre : (-(m : ℂ)).re = -(m : ℝ) := by simp
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hlin : Continuous fun s : ℝ ↦ (1 : ℂ) + ((s / 2 : ℝ) : ℂ) * I :=
      continuous_const.add ((Complex.continuous_ofReal.comp (continuous_id.div_const 2)).mul
        continuous_const)
    exact ContinuousAt.comp (f := fun s : ℝ ↦ (1 : ℂ) + ((s / 2 : ℝ) : ℂ) * I)
      (g := Complex.Gamma) (Complex.differentiableAt_Gamma _ hne).continuousAt
      (hlin.continuousAt (x := t))
  obtain ⟨t₀, _, ht₀_min⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num : (-2 : ℝ) ≤ 2))
    hφ_cont.continuousOn
  let γ₀ : ℝ := φ t₀
  have hγ₀_pos : 0 < γ₀ := by
    dsimp [γ₀, φ]
    refine norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp
  obtain ⟨c₁, _, hc₁_pos, _, hstrip⟩ := norm_complex_gamma_strip_bounds 1 1
  let cγ : ℝ := min γ₀ c₁
  have hcγ_pos : 0 < cγ := lt_min hγ₀_pos hc₁_pos
  have hgam_lb : ∀ τ : ℝ,
      cγ * Real.exp (-(Real.pi / 4) * |τ|) ≤ ‖Complex.Gamma ((1 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ := by
    intro τ
    by_cases hτ : |τ| ≤ 2
    · have hmem : τ ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp hτ
      have hφ_ge : γ₀ ≤ φ τ := ht₀_min hmem
      have hexp_le : Real.exp (-(Real.pi / 4) * |τ|) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have : 0 ≤ (Real.pi / 4) * |τ| := mul_nonneg (by positivity) (abs_nonneg τ)
        linarith
      calc
        cγ * Real.exp (-(Real.pi / 4) * |τ|) ≤ γ₀ * 1 :=
          mul_le_mul (min_le_left _ _) hexp_le (by positivity) hγ₀_pos.le
        _ = γ₀ := mul_one γ₀
        _ ≤ φ τ := hφ_ge
    · have hτ2 : 2 < |τ| := lt_of_not_ge hτ
      have h1 : 1 ≤ |τ / 2| := by
        rw [abs_div, abs_two]
        linarith
      have hst := (hstrip (σ := 1) (t := τ / 2) ⟨le_rfl, le_rfl⟩ h1).1
      have hpow1 : (1 : ℝ) ≤ |τ / 2| ^ ((1 : ℝ) - 1 / 2) :=
        Real.one_le_rpow h1 (by norm_num)
      have hexp_eq : -(Real.pi / 2) * |τ / 2| = -(Real.pi / 4) * |τ| := by
        rw [abs_div, abs_two]
        ring
      calc
        cγ * Real.exp (-(Real.pi / 4) * |τ|) ≤ c₁ * Real.exp (-(Real.pi / 4) * |τ|) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
        _ ≤ c₁ * Real.exp (-(Real.pi / 2) * |τ / 2|) * |τ / 2| ^ ((1 : ℝ) - 1 / 2) := by
            rw [← hexp_eq]
            calc
              c₁ * Real.exp (-(Real.pi / 2) * |τ / 2|)
                  = (c₁ * Real.exp (-(Real.pi / 2) * |τ / 2|)) * 1 := (mul_one _).symm
              _ ≤ (c₁ * Real.exp (-(Real.pi / 2) * |τ / 2|)) * |τ / 2| ^ ((1 : ℝ) - 1 / 2) :=
                  mul_le_mul_of_nonneg_left hpow1 (by positivity)
        _ ≤ ‖Complex.Gamma ((1 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ := hst
  refine ⟨cγ / (2 * Real.pi), by positivity, fun τ ↦ ?_⟩
  let z₀ : ℂ := (2 : ℂ) + (τ : ℂ) * I
  have hz₀_m : ∀ m : ℕ, z₀ ≠ -2 * (m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp [z₀] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hz₀_1 : z₀ ≠ 1 := fun h ↦ by
    have hre := congrArg Complex.re h
    simp [z₀] at hre
  rw [xi_eq_formula hz₀_m hz₀_1]
  have hz₀_half : z₀ / 2 = (1 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [z₀]
  have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hnz₀ : 2 ≤ ‖z₀‖ := by
    have hre : |z₀.re| ≤ ‖z₀‖ := Complex.abs_re_le_norm z₀
    simpa [z₀] using hre
  have hnz₀1 : 1 ≤ ‖z₀ - 1‖ := by
    have hre : |(z₀ - 1).re| ≤ ‖z₀ - 1‖ := Complex.abs_re_le_norm (z₀ - 1)
    have h1 : (1 : ℝ) ≤ |(z₀ - 1).re| := by
      simp [z₀]
      norm_num
    exact h1.trans hre
  have hnpi : ‖(Real.pi : ℂ) ^ (-z₀ / 2)‖ = Real.pi⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-z₀ / 2).re = -1 := by simp [z₀]
    rw [hre, Real.rpow_neg_one]
  have hnz : 1 / 2 ≤ ‖riemannZeta z₀‖ := by
    have h := norm_riemannZeta_ge_of_one_lt_re (σ := 2) one_lt_two τ
    norm_num at h
    exact h
  have hng : cγ * Real.exp (-(Real.pi / 4) * |τ|) ≤ ‖Complex.Gamma (z₀ / 2)‖ := by
    rw [hz₀_half]
    exact hgam_lb τ
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hn12, hnpi]
  have hprod :
      (1 / 2 : ℝ) * 2 * 1 * Real.pi⁻¹ * (cγ * Real.exp (-(Real.pi / 4) * |τ|)) * (1 / 2) ≤
        (1 / 2 : ℝ) * ‖z₀‖ * ‖z₀ - 1‖ * Real.pi⁻¹ * ‖Complex.Gamma (z₀ / 2)‖ * ‖riemannZeta z₀‖ := by
    gcongr
  calc
    cγ / (2 * Real.pi) * Real.exp (-(Real.pi / 4) * |τ|)
        = (1 / 2 : ℝ) * 2 * 1 * Real.pi⁻¹ * (cγ * Real.exp (-(Real.pi / 4) * |τ|)) * (1 / 2) := by
          ring
    _ ≤ (1 / 2 : ℝ) * ‖z₀‖ * ‖z₀ - 1‖ * Real.pi⁻¹ * ‖Complex.Gamma (z₀ / 2)‖ * ‖riemannZeta z₀‖ :=
          hprod

private lemma xi_sphere_upper_bound :
    ∃ C_sph : ℝ, 0 < C_sph ∧ ∀ (τ : ℝ) (w : ℂ),
      w ∈ Metric.sphere ((2 : ℂ) + (τ : ℂ) * I) 6 →
        ‖xi w‖ ≤ C_sph * (|τ| + 14) ^ 7 * Real.exp (-(Real.pi / 4) * |τ|) := by
  let Scomp : Set (ℝ × ℝ) := Set.Icc (1 / 2 : ℝ) 8 ×ˢ Set.Icc (-2 : ℝ) 2
  have hS_comp : IsCompact Scomp := isCompact_Icc.prod isCompact_Icc
  have hS_ne : Scomp.Nonempty := ⟨(1, 0), by norm_num, by norm_num⟩
  let gcomp : ℝ × ℝ → ℝ := fun p ↦ ‖xi ((p.1 : ℂ) + (p.2 : ℂ) * I)‖
  have hgcomp : Continuous gcomp := by
    refine Continuous.norm ?_
    exact differentiable_xi.continuous.comp
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  obtain ⟨p₀, _, hp₀_max⟩ := hS_comp.exists_isMaxOn hS_ne hgcomp.continuousOn
  let M₀ : ℝ := max (gcomp p₀) 1
  have hM₀_pos : 0 < M₀ := by positivity
  obtain ⟨_, C₁, hc₁_pos, hc₁C₁, hstrip⟩ := norm_complex_gamma_strip_bounds (1 / 4) 4
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hc₁_pos hc₁C₁
  let C_strip : ℝ := max (M₀ * Real.exp (Real.pi / 2)) C₁
  have hC_strip_pos : 0 < C_strip := by positivity
  have hhalf_strip : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 8 →
      ‖xi s‖ ≤ C_strip * (|s.im| + 8) ^ 7 * Real.exp (-(Real.pi / 4) * |s.im|) := by
    intro s hs_lo hs_hi
    by_cases him : |s.im| ≤ 2
    · have hp_mem : (s.re, s.im) ∈ Scomp := ⟨⟨hs_lo, hs_hi⟩, abs_le.mp him⟩
      have hmax : ‖xi s‖ ≤ gcomp p₀ := by
        have hs_eq : (s.re : ℂ) + (s.im : ℂ) * I = s := Complex.re_add_im s
        simpa [gcomp, hs_eq] using hp₀_max hp_mem
      have hM : ‖xi s‖ ≤ M₀ := hmax.trans (le_max_left _ _)
      have hpow1 : (1 : ℝ) ≤ (|s.im| + 8) ^ 7 :=
        one_le_pow₀ (by linarith [abs_nonneg s.im])
      have hexp_ge : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi / 4) * |s.im|) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [Real.pi_pos, him]
      have h1 : M₀ ≤ (M₀ * Real.exp (Real.pi / 2)) * Real.exp (-(Real.pi / 4) * |s.im|) := by
        calc
          M₀ = (M₀ * Real.exp (Real.pi / 2)) * Real.exp (-(Real.pi / 2)) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
          _ ≤ (M₀ * Real.exp (Real.pi / 2)) * Real.exp (-(Real.pi / 4) * |s.im|) :=
            mul_le_mul_of_nonneg_left hexp_ge (by positivity)
      have hC_ge : M₀ * Real.exp (Real.pi / 2) ≤ C_strip := le_max_left _ _
      have h2 : (M₀ * Real.exp (Real.pi / 2)) * Real.exp (-(Real.pi / 4) * |s.im|) ≤
          C_strip * 1 * Real.exp (-(Real.pi / 4) * |s.im|) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right hC_ge (Real.exp_pos _).le
      calc
        ‖xi s‖ ≤ M₀ := hM
        _ ≤ (M₀ * Real.exp (Real.pi / 2)) * Real.exp (-(Real.pi / 4) * |s.im|) := h1
        _ ≤ C_strip * 1 * Real.exp (-(Real.pi / 4) * |s.im|) := h2
        _ ≤ C_strip * (|s.im| + 8) ^ 7 * Real.exp (-(Real.pi / 4) * |s.im|) := by gcongr
    · have him2 : 2 ≤ |s.im| := le_of_not_ge him
      have hs_m : ∀ m : ℕ, s ≠ -2 * (m : ℂ) := by
        intro m h
        have hre : s.re = (-2 * (m : ℂ)).re := congrArg Complex.re h
        have hmr : (-2 * (m : ℂ)).re = -2 * (m : ℝ) := by simp
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hs1 : s ≠ 1 := fun h ↦ by
        have him0 := congrArg Complex.im h
        simp only [Complex.one_im] at him0
        rw [him0, abs_zero] at him2
        linarith
      rw [xi_eq_formula hs_m hs1]
      have hsnorm_le : ‖s‖ ≤ |s.im| + 8 := by
        calc
          ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
          _ ≤ 8 + |s.im| := by rw [abs_of_nonneg (by linarith)]; linarith
          _ = |s.im| + 8 := add_comm _ _
      have hs1norm_le : ‖s - 1‖ ≤ |s.im| + 8 := by
        calc
          ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| := Complex.norm_le_abs_re_add_abs_im (s - 1)
          _ = |s.re - 1| + |s.im| := by simp
          _ ≤ 8 + |s.im| := by
              have hre1 : |s.re - 1| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
              linarith
          _ = |s.im| + 8 := add_comm _ _
      have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      have hpow_pi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        have hre_neg : (-s / 2).re ≤ 0 := by
          have : (-s / 2).re = -s.re / 2 := by simp
          rw [this]; linarith
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) hre_neg
      have hnorm_ge2 : 2 ≤ ‖s‖ := him2.trans (Complex.abs_im_le_norm s)
      have hzeta_le : ‖riemannZeta s‖ ≤ 2 * (|s.im| + 8) :=
        (norm_riemannZeta_re_ge_half_le hs_lo hnorm_ge2).trans (by gcongr)
      have hgam_le : ‖Complex.Gamma (s / 2)‖ ≤
          C₁ * (|s.im| + 8) ^ 4 * Real.exp (-(Real.pi / 4) * |s.im|) := by
        have hs2_eq : s / 2 = ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * I := by
          apply Complex.ext <;> simp
        have hs2_re : s.re / 2 ∈ Set.Icc (1 / 4 : ℝ) 4 := ⟨by linarith, by linarith⟩
        have hs2_im : 1 ≤ |s.im / 2| := by
          rw [abs_div, abs_two]; linarith
        have hst := (hstrip hs2_re hs2_im).2
        have hrpow_le : |s.im / 2| ^ (s.re / 2 - 1 / 2) ≤ (|s.im| + 8) ^ 4 := by
          have h1 : |s.im / 2| ^ (s.re / 2 - 1 / 2) ≤ |s.im / 2| ^ (4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hs2_im (by linarith)
          have h2 : |s.im / 2| ^ (4 : ℝ) = |s.im / 2| ^ (4 : ℕ) := Real.rpow_natCast _ 4
          have h3 : |s.im / 2| ≤ |s.im| + 8 := by
            rw [abs_div, abs_two]; linarith [abs_nonneg s.im]
          calc
            |s.im / 2| ^ (s.re / 2 - 1 / 2) ≤ |s.im / 2| ^ (4 : ℕ) := h1.trans_eq h2
            _ ≤ (|s.im| + 8) ^ (4 : ℕ) := by gcongr
        have hexp_eq : -(Real.pi / 2) * |s.im / 2| = -(Real.pi / 4) * |s.im| := by
          rw [abs_div, abs_two]; ring
        rw [hs2_eq]
        calc
          ‖Complex.Gamma (((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * I)‖
              ≤ C₁ * Real.exp (-(Real.pi / 2) * |s.im / 2|) * |s.im / 2| ^ (s.re / 2 - 1 / 2) := hst
          _ ≤ C₁ * Real.exp (-(Real.pi / 4) * |s.im|) * (|s.im| + 8) ^ 4 := by
              rw [hexp_eq]
              gcongr
          _ = C₁ * (|s.im| + 8) ^ 4 * Real.exp (-(Real.pi / 4) * |s.im|) := by ring
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hn12]
      calc
        (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ * ‖(Real.pi : ℂ) ^ (-s / 2)‖ *
            ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖
            ≤ (1 / 2 : ℝ) * (|s.im| + 8) * (|s.im| + 8) * 1 *
                (C₁ * (|s.im| + 8) ^ 4 * Real.exp (-(Real.pi / 4) * |s.im|)) *
                (2 * (|s.im| + 8)) := by gcongr
        _ = C₁ * (|s.im| + 8) ^ 7 * Real.exp (-(Real.pi / 4) * |s.im|) := by ring
        _ ≤ C_strip * (|s.im| + 8) ^ 7 * Real.exp (-(Real.pi / 4) * |s.im|) := by
            have : C₁ ≤ C_strip := le_max_right _ _
            gcongr
  refine ⟨C_strip * Real.exp (3 * Real.pi / 2), by positivity, fun τ w hw ↦ ?_⟩
  have hdist : ‖w - ((2 : ℂ) + (τ : ℂ) * I)‖ = 6 := by
    simpa [Complex.dist_eq] using Metric.mem_sphere.mp hw
  have hre_diff : |w.re - 2| ≤ 6 := by
    have h := Complex.abs_re_le_norm (w - ((2 : ℂ) + (τ : ℂ) * I))
    simpa [hdist] using h
  have him_diff : |w.im - τ| ≤ 6 := by
    have h := Complex.abs_im_le_norm (w - ((2 : ℂ) + (τ : ℂ) * I))
    simpa [hdist] using h
  let s : ℂ := if (1 / 2 : ℝ) ≤ w.re then w else 1 - w
  have hxi_eq : xi w = xi s := by
    dsimp [s]
    split_ifs
    · rfl
    · exact (xi_one_sub w).symm
  have hs_lo : 1 / 2 ≤ s.re := by
    dsimp [s]
    split_ifs with h
    · exact h
    · simp only [Complex.sub_re, Complex.one_re]; linarith
  have hs_hi : s.re ≤ 8 := by
    have hw_bounds := abs_le.mp hre_diff
    dsimp [s]
    split_ifs with h
    · linarith
    · simp only [Complex.sub_re, Complex.one_re]; linarith
  have hsim_eq : |s.im| = |w.im| := by
    dsimp [s]
    split_ifs <;> simp
  have him_hi : |s.im| + 8 ≤ |τ| + 14 := by
    have h1 : |w.im| - |τ| ≤ |w.im - τ| := abs_sub_abs_le_abs_sub w.im τ
    rw [hsim_eq]
    linarith
  have him_lo : |τ| - 6 ≤ |s.im| := by
    have h1 : |τ| - |w.im| ≤ |τ - w.im| := abs_sub_abs_le_abs_sub τ w.im
    rw [abs_sub_comm] at h1
    rw [hsim_eq]
    linarith
  have hexp_le : Real.exp (-(Real.pi / 4) * |s.im|) ≤
      Real.exp (3 * Real.pi / 2) * Real.exp (-(Real.pi / 4) * |τ|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [Real.pi_pos, him_lo]
  calc
    ‖xi w‖ = ‖xi s‖ := by rw [hxi_eq]
    _ ≤ C_strip * (|s.im| + 8) ^ 7 * Real.exp (-(Real.pi / 4) * |s.im|) := hhalf_strip s hs_lo hs_hi
    _ ≤ C_strip * (|τ| + 14) ^ 7 * (Real.exp (3 * Real.pi / 2) * Real.exp (-(Real.pi / 4) * |τ|)) := by
        gcongr
    _ = (C_strip * Real.exp (3 * Real.pi / 2)) * (|τ| + 14) ^ 7 * Real.exp (-(Real.pi / 4) * |τ|) := by
        ring

/-- Local zero-counting bound for `xi`: on every disk `closedBall (2 + τ * I) 3`, the total
zero multiplicity of `xi` is `O(log (|τ| + 2))` uniformly in `τ : ℝ`. -/
theorem zeroCount_xi_local_le :
    ∃ C > 0, ∀ τ : ℝ,
      (zeroCount xi ((2 : ℂ) + (τ : ℂ) * I) 3 : ℝ) ≤ C * Real.log (|τ| + 2) := by
  obtain ⟨c₀, hc₀, hlb⟩ := xi_center_lower_bound
  obtain ⟨C_sph, hCsph, hub⟩ := xi_sphere_upper_bound
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let A : ℝ := max (C_sph / c₀) 1
  have hA_pos : 1 ≤ A := le_max_right _ _
  have hA_ge : C_sph / c₀ ≤ A := le_max_left _ _
  let C : ℝ := (Real.log A + 7 * Real.log 7) / (Real.log 2) ^ 2 + 7 / Real.log 2
  have hC_pos : 0 < C := by
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA_pos
    have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
    positivity
  refine ⟨C, hC_pos, fun τ ↦ ?_⟩
  let z₀ : ℂ := (2 : ℂ) + (τ : ℂ) * I
  let M : ℝ := C_sph * (|τ| + 14) ^ 7 * Real.exp (-(Real.pi / 4) * |τ|)
  have hM_pos : 0 < M := by positivity
  have hxi_an : AnalyticOnNhd ℂ xi (Metric.closedBall z₀ 6) :=
    analyticOnNhd_xi.mono (Set.subset_univ _)
  have hz₀_ne : xi z₀ ≠ 0 := xi_ne_zero_of_one_le_re (by simp [z₀])
  have hjen := zeroCount_le_sub_log_div_log (r := 3) (R := 6) (M := M) (by norm_num) (by norm_num)
    hM_pos hxi_an hz₀_ne (fun w hw ↦ hub τ w hw)
  have h63 : (6 : ℝ) / 3 = 2 := by norm_num
  rw [h63] at hjen
  have hnorm_pos : 0 < ‖xi z₀‖ := norm_pos_iff.mpr hz₀_ne
  have hquot_le : M / ‖xi z₀‖ ≤ A * (7 * (|τ| + 2)) ^ 7 := by
    have h1 : M / ‖xi z₀‖ ≤ M / (c₀ * Real.exp (-(Real.pi / 4) * |τ|)) :=
      div_le_div_of_nonneg_left hM_pos.le (by positivity) (hlb τ)
    have h2 : M / (c₀ * Real.exp (-(Real.pi / 4) * |τ|)) = (C_sph / c₀) * (|τ| + 14) ^ 7 := by
      dsimp [M]
      have hexp0 : Real.exp (-(Real.pi / 4) * |τ|) ≠ 0 := (Real.exp_pos _).ne'
      field_simp [hc₀.ne', hexp0]
    have h3 : (C_sph / c₀) * (|τ| + 14) ^ 7 ≤ A * (7 * (|τ| + 2)) ^ 7 := by
      have hlin : |τ| + 14 ≤ 7 * (|τ| + 2) := by linarith [abs_nonneg τ]
      gcongr
    exact h1.trans (h2 ▸ h3)
  have hlog_τ : Real.log 2 ≤ Real.log (|τ| + 2) := Real.log_le_log zero_lt_two (by linarith [abs_nonneg τ])
  have hlog_τ_pos : 0 < Real.log (|τ| + 2) := lt_of_lt_of_le hlog2_pos hlog_τ
  have hnum_le : Real.log M - Real.log ‖xi z₀‖ ≤
      ((Real.log A + 7 * Real.log 7) / Real.log 2 + 7) * Real.log (|τ| + 2) := by
    rw [← Real.log_div hM_pos.ne' hnorm_pos.ne']
    have hq_pos : 0 < M / ‖xi z₀‖ := div_pos hM_pos hnorm_pos
    calc
      Real.log (M / ‖xi z₀‖) ≤ Real.log (A * (7 * (|τ| + 2)) ^ 7) :=
        Real.log_le_log hq_pos hquot_le
      _ = Real.log A + 7 * (Real.log 7 + Real.log (|τ| + 2)) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
            Real.log_mul (by norm_num) (by positivity)]
          push_cast
          ring
      _ = (Real.log A + 7 * Real.log 7) * 1 + 7 * Real.log (|τ| + 2) := by ring
      _ ≤ (Real.log A + 7 * Real.log 7) * (Real.log (|τ| + 2) / Real.log 2) +
            7 * Real.log (|τ| + 2) := by
          have h1_le : 1 ≤ Real.log (|τ| + 2) / Real.log 2 := (one_le_div hlog2_pos).mpr hlog_τ
          have hnn : 0 ≤ Real.log A + 7 * Real.log 7 := by
            have := Real.log_nonneg hA_pos
            have := Real.log_pos (by norm_num : (1 : ℝ) < 7)
            positivity
          gcongr
      _ = ((Real.log A + 7 * Real.log 7) / Real.log 2 + 7) * Real.log (|τ| + 2) := by ring
  calc
    (zeroCount xi z₀ 3 : ℝ) ≤ (Real.log M - Real.log ‖xi z₀‖) / Real.log 2 := hjen
    _ ≤ (((Real.log A + 7 * Real.log 7) / Real.log 2 + 7) * Real.log (|τ| + 2)) / Real.log 2 :=
        div_le_div_of_nonneg_right hnum_le hlog2_pos.le
    _ = C * Real.log (|τ| + 2) := by dsimp [C]; ring

/-- The set of nontrivial zeros `ρ` of `riemannZeta` with `0 < ρ.re < 1` and `|ρ.im| ≤ T`. -/
def nontrivialZeroSetUpTo (T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Finiteness of the set of nontrivial zeros of `riemannZeta` up to height `T`. -/
theorem nontrivialZeroSetUpTo_finite (T : ℝ) : (nontrivialZeroSetUpTo T).Finite := by
  have hsub : nontrivialZeroSetUpTo T ⊆ zeroSet xi 2 (3 + |T|) := by
    intro ρ hρ
    refine ⟨?_, xi_eq_zero_iff.mpr ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩⟩
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have h1 : ‖ρ - 2‖ ≤ |(ρ - 2).re| + |(ρ - 2).im| := Complex.norm_le_abs_re_add_abs_im (ρ - 2)
    have hre : |(ρ - 2).re| ≤ 2 := abs_le.mpr ⟨by simp; linarith [hρ.2.1], by simp; linarith [hρ.2.2.1]⟩
    have him : |(ρ - 2).im| ≤ |T| := by
      have him_eq : (ρ - 2).im = ρ.im := by simp
      rw [him_eq]
      exact hρ.2.2.2.trans (le_abs_self T)
    linarith
  refine (zeroSet_finite (by positivity : (0 : ℝ) ≤ 3 + |T|)
    (analyticOnNhd_xi.mono (Set.subset_univ _)) (xi_ne_zero_of_one_le_re (by norm_num))).subset hsub

/-- Finite set (`Finset ℂ`) of all nontrivial zeros `ρ` of `riemannZeta` with `0 < ρ.re < 1` and
`|ρ.im| ≤ T`. -/
noncomputable def nontrivialZerosUpTo (T : ℝ) : Finset ℂ :=
  (nontrivialZeroSetUpTo_finite T).toFinset

/-- Membership characterization for `nontrivialZerosUpTo T`. -/
@[simp]
theorem mem_nontrivialZerosUpTo {T : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZerosUpTo T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
  simp [nontrivialZerosUpTo, nontrivialZeroSetUpTo]

/-- Sum of `zeroMultiplicity` over any finite set of nontrivial zeros in the horizontal strip
`|ρ.im - τ| ≤ 2` is bounded uniformly by `O(log (|τ| + 2))`. -/
theorem sum_zeroMultiplicity_strip_le :
    ∃ C > 0, ∀ (τ : ℝ) (S : Finset ℂ),
      (∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - τ| ≤ 2) →
        (∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)) ≤ C * Real.log (|τ| + 2) := by
  obtain ⟨C, hC_pos, hloc⟩ := zeroCount_xi_local_le
  refine ⟨C, hC_pos, fun τ S hS ↦ ?_⟩
  let z₀ : ℂ := (2 : ℂ) + (τ : ℂ) * I
  have hxi_an : AnalyticOnNhd ℂ xi (Metric.closedBall z₀ 3) :=
    analyticOnNhd_xi.mono (Set.subset_univ _)
  have hz₀_ne : xi z₀ ≠ 0 := xi_ne_zero_of_one_le_re (by simp [z₀])
  have hfin := zeroSet_finite (r := 3) (by norm_num) hxi_an hz₀_ne
  let Z : Finset ℂ := hfin.toFinset
  have hZ_eq : (zeroCount xi z₀ 3 : ℝ) = ∑ u ∈ Z, (analyticOrderNatAt xi u : ℝ) := by
    have hnat : zeroCount xi z₀ 3 = ∑ u ∈ Z, analyticOrderNatAt xi u :=
      zeroCount_eq_sum_analyticOrderNatAt (by norm_num) hxi_an hz₀_ne (Set.Finite.coe_toFinset hfin)
    exact_mod_cast hnat
  have hS_sub : S ⊆ Z := by
    intro ρ hρ
    have hρ_spec := hS ρ hρ
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, xi_eq_zero_iff.mpr ⟨hρ_spec.1, hρ_spec.2.1, hρ_spec.2.2.1⟩⟩
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have hsq : ‖ρ - z₀‖ ^ 2 < 3 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre : (ρ - z₀).re = ρ.re - 2 := by simp [z₀]
      have him : (ρ - z₀).im = ρ.im - τ := by simp [z₀]
      rw [hre, him]
      have h1 : (ρ.re - 2) * (ρ.re - 2) ≤ 4 := by nlinarith [hρ_spec.2.1, hρ_spec.2.2.1]
      have h2 : (ρ.im - τ) * (ρ.im - τ) ≤ 4 := by
        have := sq_le_sq' (by linarith [abs_le.mp hρ_spec.2.2.2]) (abs_le.mp hρ_spec.2.2.2).2
        nlinarith
      linarith
    have hnorm : ‖ρ - z₀‖ ≤ 3 := by
      have : ‖ρ - z₀‖ ^ 2 ≤ (3 : ℝ) ^ 2 := hsq.le
      nlinarith [norm_nonneg (ρ - z₀)]
    exact hnorm
  have hsum_eq :
      (∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)) = ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ_spec := hS ρ hρ
    rw [zeroMultiplicity_eq_xi hρ_spec.2.1 hρ_spec.2.2.1]
  have hsum_sub :
      (∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ)) ≤ ∑ u ∈ Z, (analyticOrderNatAt xi u : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun _ _ _ ↦ Nat.cast_nonneg _
  rw [hsum_eq]
  exact hsum_sub.trans (hZ_eq.symm ▸ hloc τ)

private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (g : β → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ y ∈ s.biUnion t, g y ≤ ∑ a ∈ s, ∑ y ∈ t a, g y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hsplit : t a ∪ s.biUnion t = (t a \ s.biUnion t) ∪ s.biUnion t := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    have hdisj : Disjoint (t a \ s.biUnion t) (s.biUnion t) := disjoint_sdiff_self_left
    have hs1 : ∑ y ∈ t a \ s.biUnion t, g y ≤ ∑ y ∈ t a, g y :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ ↦ hg _
    rw [hsplit, Finset.sum_union hdisj]
    linarith [hs1, ih]

/-- Total multiplicity (and count) of nontrivial zeros `ρ` with `|ρ.im| ≤ T` is `O(T * log T)` for
all `2 ≤ T`. -/
theorem sum_zeroMultiplicity_nontrivialZerosUpTo_le :
    ∃ C > 0, ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℝ)) ≤ C * T * Real.log T := by
  obtain ⟨C₀, hC₀_pos, hstrip⟩ := sum_zeroMultiplicity_strip_le
  refine ⟨15 * C₀, by positivity, fun T hT ↦ ?_⟩
  let K : ℤ := ⌊T⌋ + 1
  have hK_pos : 0 ≤ K := by
    dsimp [K]
    have : (0 : ℤ) ≤ ⌊T⌋ := Int.floor_nonneg.mpr (by linarith)
    omega
  let centers : Finset ℤ := Finset.Icc (-K) K
  let strip : ℤ → Finset ℂ := fun k ↦
    (nontrivialZerosUpTo T).filter (fun ρ ↦ |ρ.im - (k : ℝ)| ≤ 2)
  have hcover : nontrivialZerosUpTo T ⊆ centers.biUnion strip := by
    intro ρ hρ
    rw [Finset.mem_biUnion]
    let k : ℤ := ⌊ρ.im⌋
    have hmem_c : k ∈ centers := by
      simp only [centers, Finset.mem_Icc]
      have hρ_im := (mem_nontrivialZerosUpTo.mp hρ).2.2.2
      have habs := abs_le.mp hρ_im
      have hk_hi : k ≤ K := by
        have h1 : ⌊ρ.im⌋ ≤ ⌊T⌋ := Int.floor_mono habs.2
        dsimp [K]; omega
      have hk_lo : -K ≤ k := by
        have h1 : (-T : ℝ) < (k : ℝ) + 1 := lt_of_le_of_lt habs.1 (Int.lt_floor_add_one ρ.im)
        have h2 : (-K : ℤ) ≤ ⌊-T⌋ := by
          dsimp [K]
          have hfl : (⌊-T⌋ : ℝ) ≤ -T := Int.floor_le (-T)
          have : -(⌊T⌋ : ℝ) - 1 < -T := by linarith [Int.lt_floor_add_one T]
          have h3 : -(⌊T⌋ + 1 : ℤ) < ⌊-T⌋ + 1 := by
            have : (-(⌊T⌋ + 1 : ℤ) : ℝ) < (⌊-T⌋ + 1 : ℝ) := by
              push_cast
              linarith [Int.lt_floor_add_one (-T)]
            exact_mod_cast this
          omega
        exact h2.trans (Int.floor_mono habs.1)
      exact ⟨hk_lo, hk_hi⟩
    refine ⟨k, hmem_c, ?_⟩
    simp only [strip, Finset.mem_filter]
    refine ⟨hρ, ?_⟩
    have hfl1 : (k : ℝ) ≤ ρ.im := Int.floor_le ρ.im
    have hfl2 : ρ.im < (k : ℝ) + 1 := Int.lt_floor_add_one ρ.im
    rw [abs_le]
    constructor <;> linarith
  have h1 :
      (∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℝ)) ≤
        ∑ ρ ∈ centers.biUnion strip, (zeroMultiplicity ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ ↦ Nat.cast_nonneg _
  have h2 :
      (∑ ρ ∈ centers.biUnion strip, (zeroMultiplicity ρ : ℝ)) ≤
        ∑ k ∈ centers, ∑ ρ ∈ strip k, (zeroMultiplicity ρ : ℝ) :=
    sum_biUnion_le_of_nonneg centers strip _ fun _ ↦ Nat.cast_nonneg _
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hterm_le : ∀ k ∈ centers,
      (∑ ρ ∈ strip k, (zeroMultiplicity ρ : ℝ)) ≤ 3 * C₀ * Real.log T := by
    intro k hk
    have hstrip_k := hstrip (k : ℝ) (strip k) fun ρ hρ ↦ by
      have hf := Finset.mem_filter.mp hρ
      have hz := mem_nontrivialZerosUpTo.mp hf.1
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hf.2⟩
    have hk_abs : |(k : ℝ)| ≤ T + 1 := by
      simp only [centers, Finset.mem_Icc] at hk
      have hK_le : (K : ℝ) ≤ T + 1 := by
        dsimp [K]; push_cast; linarith [Int.floor_le T]
      rw [abs_le]
      constructor
      · have : (-K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        linarith
      · have : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk.2
        linarith
    have hlog_k : Real.log (|(k : ℝ)| + 2) ≤ 3 * Real.log T := by
      have hT3 : |(k : ℝ)| + 2 ≤ T ^ 3 := by
        have hT2 : 4 ≤ T ^ 2 := by nlinarith
        nlinarith [hT, hk_abs]
      calc
        Real.log (|(k : ℝ)| + 2) ≤ Real.log (T ^ 3) := Real.log_le_log (by positivity) hT3
        _ = 3 * Real.log T := by rw [Real.log_pow]; norm_cast
    exact hstrip_k.trans (by
      have := mul_le_mul_of_nonneg_left hlog_k hC₀_pos.le
      linarith)
  have h3 :
      (∑ k ∈ centers, ∑ ρ ∈ strip k, (zeroMultiplicity ρ : ℝ)) ≤
        (centers.card : ℝ) * (3 * C₀ * Real.log T) := by
    have h := Finset.sum_le_card_nsmul centers _ (3 * C₀ * Real.log T) hterm_le
    simpa [nsmul_eq_mul] using h
  have hcard_c : (centers.card : ℝ) ≤ 5 * T := by
    have hcard_int : (centers.card : ℤ) = 2 * K + 1 := by
      dsimp [centers]
      rw [Int.card_Icc]
      omega
    have hK_le : (K : ℝ) ≤ T + 1 := by
      dsimp [K]; push_cast; linarith [Int.floor_le T]
    have hcard_r : (centers.card : ℝ) = 2 * (K : ℝ) + 1 := by exact_mod_cast hcard_int
    linarith
  calc
    (∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℝ))
        ≤ (centers.card : ℝ) * (3 * C₀ * Real.log T) := (h1.trans h2).trans h3
    _ ≤ (5 * T) * (3 * C₀ * Real.log T) := by
        exact mul_le_mul_of_nonneg_right hcard_c (by positivity)
    _ = (15 * C₀) * T * Real.log T := by ring

/-- Number of distinct nontrivial zeros `ρ` with `|ρ.im| ≤ T` is `O(T * log T)` for `2 ≤ T`. -/
theorem card_nontrivialZerosUpTo_le :
    ∃ C > 0, ∀ T : ℝ, 2 ≤ T →
      ((nontrivialZerosUpTo T).card : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨C, hC_pos, hsum⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  have h1 : ((nontrivialZerosUpTo T).card : ℝ) ≤ ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℝ) := by
    calc
      ((nontrivialZerosUpTo T).card : ℝ) = ∑ _ρ ∈ nontrivialZerosUpTo T, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ ↦ ?_
          have hmem := mem_nontrivialZerosUpTo.mp hρ
          have hpos := (zeroMultiplicity_pos_iff hmem.2.1 hmem.2.2.1).mpr hmem.1
          exact_mod_cast hpos
  exact h1.trans (hsum T hT)

/-- Number of nontrivial zeros `ρ` (counted with multiplicity) in the unit height band
`T ≤ |ρ.im| ≤ T + 1` is `O(log T)` uniformly for `2 ≤ T`. -/
theorem sum_zeroMultiplicity_unit_band_le :
    ∃ C > 0, ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ (nontrivialZerosUpTo (T + 1)).filter (fun ρ ↦ T ≤ |ρ.im|),
          (zeroMultiplicity ρ : ℝ)) ≤ C * Real.log T := by
  obtain ⟨C₀, hC₀_pos, hstrip⟩ := sum_zeroMultiplicity_strip_le
  refine ⟨8 * C₀, by positivity, fun T hT ↦ ?_⟩
  let B := (nontrivialZerosUpTo (T + 1)).filter (fun ρ ↦ T ≤ |ρ.im|)
  let Bpos := B.filter (fun ρ ↦ 0 ≤ ρ.im)
  let Bneg := B.filter (fun ρ ↦ ρ.im < 0)
  have hB_eq : B = Bpos ∪ Bneg := by
    ext ρ
    simp only [Bpos, Bneg, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases le_or_gt 0 ρ.im with h0 | h0
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h0⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint Bpos Bneg := by
    rw [Finset.disjoint_left]
    intro ρ hp hn
    simp only [Bpos, Bneg, Finset.mem_filter] at hp hn
    linarith
  change ∑ ρ ∈ B, (zeroMultiplicity ρ : ℝ) ≤ 8 * C₀ * Real.log T
  rw [hB_eq, Finset.sum_union hdisj]
  have hpos_le :
      (∑ ρ ∈ Bpos, (zeroMultiplicity ρ : ℝ)) ≤ C₀ * Real.log (|T + 1 / 2| + 2) := by
    refine hstrip (T + 1 / 2) Bpos fun ρ hρ ↦ ?_
    have hpf := Finset.mem_filter.mp hρ
    have hbf := Finset.mem_filter.mp hpf.1
    have hm := mem_nontrivialZerosUpTo.mp hbf.1
    refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
    have him0 : 0 ≤ ρ.im := hpf.2
    rw [abs_of_nonneg him0] at hm hbf
    rw [abs_le]
    constructor <;> linarith [hm.2.2.2, hbf.2]
  have hneg_le :
      (∑ ρ ∈ Bneg, (zeroMultiplicity ρ : ℝ)) ≤ C₀ * Real.log (|-(T + 1 / 2)| + 2) := by
    refine hstrip (-(T + 1 / 2)) Bneg fun ρ hρ ↦ ?_
    have hpf := Finset.mem_filter.mp hρ
    have hbf := Finset.mem_filter.mp hpf.1
    have hm := mem_nontrivialZerosUpTo.mp hbf.1
    refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
    have him0 : ρ.im < 0 := hpf.2
    rw [abs_of_neg him0] at hm hbf
    rw [abs_le]
    constructor <;> linarith [hm.2.2.2, hbf.2]
  have hlog_le : Real.log (|T + 1 / 2| + 2) ≤ 4 * Real.log T := by
    have hpos_abs : |T + 1 / 2| + 2 = T + 5 / 2 := by
      rw [abs_of_nonneg (by linarith)]
      ring
    have hpow : T + 5 / 2 ≤ T ^ 4 := by
      have hsq : 4 ≤ T ^ 2 := by nlinarith
      nlinarith
    rw [hpos_abs]
    calc
      Real.log (T + 5 / 2) ≤ Real.log (T ^ 4) := Real.log_le_log (by linarith) hpow
      _ = 4 * Real.log T := by rw [Real.log_pow]; norm_cast
  have hlog_eq : |-(T + 1 / 2)| + 2 = |T + 1 / 2| + 2 := by rw [abs_neg]
  rw [hlog_eq] at hneg_le
  have hC := mul_le_mul_of_nonneg_left hlog_le hC₀_pos.le
  linarith

/-- **Horizontal contour avoidance (`T'` selection)**: for every `T ≥ 2`, there exists
`T' ∈ (T, T + 1)` whose distance to the ordinate `|ρ.im|` of every nontrivial zero `ρ` of
`riemannZeta` (`0 < ρ.re < 1`) is at least `c / Real.log T`, for an absolute constant `c > 0`. -/
theorem exists_good_T_avoiding_zeros :
    ∃ c > 0, ∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ, T < T' ∧ T' < T + 1 ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        c / Real.log T ≤ abs (|ρ.im| - T') := by
  obtain ⟨C₀, hC₀_pos, hband⟩ := sum_zeroMultiplicity_unit_band_le
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  let c : ℝ := 1 / (2 * (C₀ + 2))
  refine ⟨c, by positivity, fun T hT ↦ ?_⟩
  have hlogT_ge : 1 / 2 < Real.log T := lt_of_lt_of_le hlog2_gt (Real.log_le_log zero_lt_two hT)
  have hlogT_pos : 0 < Real.log T := by linarith
  let F : Finset ℂ := (nontrivialZerosUpTo (T + 1)).filter (fun ρ ↦ T ≤ |ρ.im|)
  have hF_card : (F.card : ℝ) ≤ C₀ * Real.log T := by
    have h1 : (F.card : ℝ) ≤ ∑ ρ ∈ F, (zeroMultiplicity ρ : ℝ) := by
      calc
        (F.card : ℝ) = ∑ _ρ ∈ F, (1 : ℝ) := by simp
        _ ≤ ∑ ρ ∈ F, (zeroMultiplicity ρ : ℝ) := by
            refine Finset.sum_le_sum fun ρ hρ ↦ ?_
            have hm := mem_nontrivialZerosUpTo.mp (Finset.mem_filter.mp hρ).1
            exact_mod_cast (zeroMultiplicity_pos_iff hm.2.1 hm.2.2.1).mpr hm.1
    exact h1.trans (hband T hT)
  let K : ℕ := F.card + 1
  have hK_pos : 0 < K := Nat.succ_pos _
  have hKr_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK_pos
  let grid : ℕ → ℝ := fun j ↦ T + (2 * (j : ℝ) + 1) / (2 * (K : ℝ))
  let bad : Finset ℕ := F.biUnion fun ρ ↦
    (Finset.range K).filter fun j ↦ abs (|ρ.im| - grid j) < 1 / (2 * (K : ℝ))
  have hbad_card : bad.card ≤ F.card := by
    have hfiber : ∀ ρ ∈ F,
        ((Finset.range K).filter fun j ↦ abs (|ρ.im| - grid j) < 1 / (2 * (K : ℝ))).card ≤ 1 := by
      intro ρ _
      refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ ↦ ?_
      have hj₁' := (Finset.mem_filter.mp hj₁).2
      have hj₂' := (Finset.mem_filter.mp hj₂).2
      have hdiff : |grid j₁ - grid j₂| < 1 / (K : ℝ) := by
        calc
          |grid j₁ - grid j₂| = abs ((|ρ.im| - grid j₂) - (|ρ.im| - grid j₁)) := by ring_nf
          _ ≤ abs (|ρ.im| - grid j₂) + abs (|ρ.im| - grid j₁) := abs_sub _ _
          _ < 1 / (2 * (K : ℝ)) + 1 / (2 * (K : ℝ)) := add_lt_add hj₂' hj₁'
          _ = 1 / (K : ℝ) := by ring
      rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
      · exfalso
        have hj_ge : (j₁ : ℝ) + 1 ≤ j₂ := by exact_mod_cast hlt
        have hstep : 1 / (K : ℝ) ≤ grid j₂ - grid j₁ := by
          dsimp [grid]
          have h1 : (1 : ℝ) / (K : ℝ) = ((2 * ((j₁ : ℝ) + 1) + 1) - (2 * (j₁ : ℝ) + 1)) / (2 * (K : ℝ)) := by
            field_simp [hKr_pos.ne']
            ring
          have h2 : (2 * ((j₁ : ℝ) + 1) + 1) - (2 * (j₁ : ℝ) + 1) ≤
              (2 * (j₂ : ℝ) + 1) - (2 * (j₁ : ℝ) + 1) := by linarith
          have h3 := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * (K : ℝ))
          linarith [h1, h3, div_sub_div_same (2 * (j₂ : ℝ) + 1) (2 * (j₁ : ℝ) + 1) (2 * (K : ℝ))]
        linarith [neg_abs_le (grid j₁ - grid j₂)]
      · rfl
      · exfalso
        have hj_ge : (j₂ : ℝ) + 1 ≤ j₁ := by exact_mod_cast hgt
        have hstep : 1 / (K : ℝ) ≤ grid j₁ - grid j₂ := by
          dsimp [grid]
          have h1 : (1 : ℝ) / (K : ℝ) = ((2 * ((j₂ : ℝ) + 1) + 1) - (2 * (j₂ : ℝ) + 1)) / (2 * (K : ℝ)) := by
            field_simp [hKr_pos.ne']
            ring
          have h2 : (2 * ((j₂ : ℝ) + 1) + 1) - (2 * (j₂ : ℝ) + 1) ≤
              (2 * (j₁ : ℝ) + 1) - (2 * (j₂ : ℝ) + 1) := by linarith
          have h3 := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * (K : ℝ))
          linarith [h1, h3, div_sub_div_same (2 * (j₁ : ℝ) + 1) (2 * (j₂ : ℝ) + 1) (2 * (K : ℝ))]
        linarith [le_abs_self (grid j₁ - grid j₂)]
    calc
      bad.card ≤ ∑ ρ ∈ F,
          ((Finset.range K).filter fun j ↦ abs (|ρ.im| - grid j) < 1 / (2 * (K : ℝ))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ρ ∈ F, 1 := Finset.sum_le_sum hfiber
      _ = F.card := by simp
  have hsdiff_ne : (Finset.range K \ bad).Nonempty := by
    rw [← Finset.card_pos]
    have hle : (bad ∩ Finset.range K).card ≤ F.card :=
      (Finset.card_le_card Finset.inter_subset_left).trans hbad_card
    have hcard_sdiff : (Finset.range K \ bad).card + (Finset.range K ∩ bad).card =
        (Finset.range K).card := Finset.card_sdiff_add_card_inter _ _
    rw [Finset.card_range, Finset.inter_comm] at hcard_sdiff
    omega
  obtain ⟨j, hj_mem⟩ := hsdiff_ne
  rw [Finset.mem_sdiff, Finset.mem_range] at hj_mem
  have hj_lt : j < K := hj_mem.1
  have hj_not_bad : j ∉ bad := hj_mem.2
  let T' : ℝ := grid j
  have hT_lt : T + 1 / (2 * (K : ℝ)) ≤ T' := by
    dsimp [T', grid]
    have h1 : (1 : ℝ) ≤ 2 * (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have := div_le_div_of_nonneg_right h1 (by positivity : 0 ≤ 2 * (K : ℝ))
    linarith
  have hT_hi : T' ≤ T + 1 - 1 / (2 * (K : ℝ)) := by
    dsimp [T', grid]
    have hj_succ : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj_lt
    have h1 : 2 * (j : ℝ) + 1 ≤ 2 * (K : ℝ) - 1 := by linarith
    have h2 : (2 * (j : ℝ) + 1) / (2 * (K : ℝ)) ≤ (2 * (K : ℝ) - 1) / (2 * (K : ℝ)) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : (2 * (K : ℝ) - 1) / (2 * (K : ℝ)) = 1 - 1 / (2 * (K : ℝ)) := by
      field_simp [hKr_pos.ne']
    linarith
  have hT_gt : T < T' := lt_of_lt_of_le (by linarith [one_div_pos.mpr (by positivity : 0 < 2 * (K : ℝ))]) hT_lt
  have hT_lt1 : T' < T + 1 := lt_of_le_of_lt hT_hi (by linarith [one_div_pos.mpr (by positivity : 0 < 2 * (K : ℝ))])
  refine ⟨T', hT_gt, hT_lt1, fun ρ hζ hre0 hre1 ↦ ?_⟩
  have hK_le : (K : ℝ) ≤ (C₀ + 2) * Real.log T := by
    dsimp [K]
    push_cast
    linarith [hF_card, hlogT_ge]
  have hc_le_K : c / Real.log T ≤ 1 / (2 * (K : ℝ)) := by
    dsimp [c]
    rw [div_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith [hK_le]
  refine hc_le_K.trans ?_
  by_cases him_lo : |ρ.im| < T
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · by_cases him_hi : T + 1 < |ρ.im|
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · have hρF : ρ ∈ F := by
        simp only [F, Finset.mem_filter, mem_nontrivialZerosUpTo]
        exact ⟨⟨hζ, hre0, hre1, le_of_not_gt him_hi⟩, le_of_not_gt him_lo⟩
      have hj_nfilt : j ∉ (Finset.range K).filter fun i ↦ abs (|ρ.im| - grid i) < 1 / (2 * (K : ℝ)) := by
        intro hmem
        exact hj_not_bad (Finset.mem_biUnion.mpr ⟨ρ, hρF, hmem⟩)
      simp only [Finset.mem_filter, Finset.mem_range, hj_lt, true_and, not_lt] at hj_nfilt
      exact hj_nfilt

/-! ### Section 2b: Logarithmic Derivative Bounds for `riemannZeta` -/

private lemma riemannZeta_ne_zero_of_im_ne_zero_and_outside {s : ℂ}
    (hs_im : s.im ≠ 0) (hxi : xi s ≠ 0) : riemannZeta s ≠ 0 := by
  have hs_m : ∀ m : ℕ, s ≠ -2 * (m : ℂ) := by
    intro m h
    have him := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.neg_im, Complex.im_ofNat, Complex.natCast_im,
      mul_zero, zero_mul, neg_zero] at him
    exact hs_im (by simpa using him)
  have hs1 : s ≠ 1 := fun h ↦ by
    have him := congrArg Complex.im h
    simp only [Complex.one_im] at him
    exact hs_im him
  intro hz
  have h := xi_eq_formula hs_m hs1
  rw [hz, mul_zero] at h
  exact hxi h

private lemma logDeriv_xi_eq_logDeriv_zeta_add {s : ℂ} (hs_im : s.im ≠ 0)
    (hζ_ne : riemannZeta s ≠ 0) :
    deriv xi s / xi s =
      1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
        (1 / 2 : ℂ) * digamma (s / 2) + deriv riemannZeta s / riemannZeta s := by
  let f₁ : ℂ → ℂ := fun w ↦ (1 / 2 : ℂ) * w * (w - 1)
  let f₂ : ℂ → ℂ := fun w ↦ (Real.pi : ℂ) ^ (-w / 2)
  let f₃ : ℂ → ℂ := fun w ↦ Complex.Gamma (w / 2)
  let f₄ : ℂ → ℂ := fun w ↦ riemannZeta w
  have hs0 : s ≠ 0 := fun h ↦ hs_im (by simp [h])
  have hs1 : s ≠ 1 := fun h ↦ hs_im (by simp [h])
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hf₁_ne : f₁ s ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hs0) hsm1
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf₂_eq : f₂ = fun w : ℂ ↦ Complex.exp (Complex.log (Real.pi : ℂ) * (-w / 2)) := by
    ext w
    exact Complex.cpow_def_of_ne_zero hpi0 _
  have hf₂_ne : f₂ s ≠ 0 := by
    rw [hf₂_eq]
    exact Complex.exp_ne_zero _
  have hs2_m : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have him := congrArg Complex.im h
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im] at him
    exact hs_im (by linarith)
  have hf₃_ne : f₃ s ≠ 0 := Complex.Gamma_ne_zero hs2_m
  have hf₄_ne : f₄ s ≠ 0 := hζ_ne
  have hf₁_der : HasDerivAt f₁ ((1 / 2 : ℂ) * ((s - 1) + s)) s := by
    have hmul := ((hasDerivAt_id s).const_mul (1 / 2 : ℂ)).mul
      ((hasDerivAt_id s).sub (hasDerivAt_const s 1))
    refine hmul.congr_deriv ?_
    simp only [Pi.sub_apply, id_eq]
    ring
  have hf₂_der : HasDerivAt f₂ (f₂ s * (-((Real.log Real.pi : ℂ) / 2))) s := by
    rw [hf₂_eq]
    have hlog_pi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
      (Complex.ofReal_log Real.pi_pos.le).symm
    have hlin : HasDerivAt (fun w : ℂ ↦ Complex.log (Real.pi : ℂ) * (-w / 2))
        (-((Real.log Real.pi : ℂ) / 2)) s := by
      have hsub : HasDerivAt (fun w : ℂ ↦ -w / 2) (-1 / 2 : ℂ) s := by
        simpa using (hasDerivAt_id s).neg.div_const (2 : ℂ)
      have hmul := hsub.const_mul (Complex.log (Real.pi : ℂ))
      refine hmul.congr_deriv ?_
      rw [hlog_pi]
      ring
    exact hlin.cexp
  have hf₃_der : HasDerivAt f₃ (deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ)) s := by
    have hgam := (Complex.differentiableAt_Gamma (s / 2) hs2_m).hasDerivAt
    have hdiv : HasDerivAt (fun w : ℂ ↦ w / 2) (1 / 2 : ℂ) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℂ)
    exact hgam.comp s hdiv
  have hf₄_diff : DifferentiableAt ℂ f₄ s := differentiableAt_riemannZeta hs1
  have hev_xi : xi =ᶠ[𝓝 s] fun w ↦ ((f₁ w * f₂ w) * f₃ w) * f₄ w := by
    have hU : {w : ℂ | w.im ≠ 0} ∈ 𝓝 s :=
      (isOpen_ne.preimage Complex.continuous_im).mem_nhds hs_im
    refine eventually_of_mem hU fun w hw ↦ ?_
    change w.im ≠ 0 at hw
    have hw_m : ∀ m : ℕ, w ≠ -2 * (m : ℂ) := fun m h ↦ hw (by
      have him := congrArg Complex.im h
      simp only [Complex.mul_im, Complex.neg_im, Complex.im_ofNat, Complex.natCast_im,
        mul_zero, zero_mul, neg_zero] at him
      simpa using him)
    have hw1 : w ≠ 1 := fun h ↦ hw (by simp [h])
    simpa [f₁, f₂, f₃, f₄, mul_assoc] using xi_eq_formula hw_m hw1
  have hxi_eq : xi s = ((f₁ s * f₂ s) * f₃ s) * f₄ s := hev_xi.eq_of_nhds
  have hder_eq : deriv xi s = deriv (fun w ↦ ((f₁ w * f₂ w) * f₃ w) * f₄ w) s :=
    hev_xi.deriv_eq
  have hld_xi : logDeriv xi s = logDeriv (fun w ↦ ((f₁ w * f₂ w) * f₃ w) * f₄ w) s := by
    simp only [logDeriv_apply, hxi_eq, hder_eq]
  have hf₁₂_ne : (f₁ s * f₂ s) ≠ 0 := mul_ne_zero hf₁_ne hf₂_ne
  have hf₁₂₃_ne : (f₁ s * f₂ s * f₃ s) ≠ 0 := mul_ne_zero hf₁₂_ne hf₃_ne
  have hf₁₂_diff : DifferentiableAt ℂ (fun w ↦ f₁ w * f₂ w) s :=
    hf₁_der.differentiableAt.mul hf₂_der.differentiableAt
  have hf₁₂₃_diff : DifferentiableAt ℂ (fun w ↦ f₁ w * f₂ w * f₃ w) s :=
    hf₁₂_diff.mul hf₃_der.differentiableAt
  rw [← logDeriv_apply, hld_xi]
  rw [show (fun w ↦ ((f₁ w * f₂ w) * f₃ w) * f₄ w) = (fun w ↦ f₁ w * f₂ w * f₃ w) * f₄ from rfl,
    logDeriv_mul s hf₁₂₃_ne hf₄_ne hf₁₂₃_diff hf₄_diff]
  rw [show (fun w ↦ f₁ w * f₂ w * f₃ w) = (fun w ↦ f₁ w * f₂ w) * f₃ from rfl,
    logDeriv_mul s hf₁₂_ne hf₃_ne hf₁₂_diff hf₃_der.differentiableAt]
  rw [show (fun w ↦ f₁ w * f₂ w) = f₁ * f₂ from rfl,
    logDeriv_mul s hf₁_ne hf₂_ne hf₁_der.differentiableAt hf₂_der.differentiableAt]
  have hld₁ : logDeriv f₁ s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_apply, hf₁_der.deriv]
    dsimp [f₁]
    field_simp [hs0, hsm1]
  have hld₂ : logDeriv f₂ s = -((Real.log Real.pi : ℂ) / 2) := by
    rw [logDeriv_apply, hf₂_der.deriv]
    field_simp [hf₂_ne]
  have hld₃ : logDeriv f₃ s = (1 / 2 : ℂ) * digamma (s / 2) := by
    rw [logDeriv_apply, hf₃_der.deriv, digamma_def (s / 2)]
    dsimp [f₃]
    ring
  have hld₄ : logDeriv f₄ s = deriv riemannZeta s / riemannZeta s := rfl
  rw [hld₁, hld₂, hld₃, hld₄]
  ring

private lemma norm_inv_sub_inv_le_of_re_band {s ρ : ℂ}
    (hs_lo : -1 / 2 ≤ s.re) (hs_hi : s.re ≤ 4)
    (hρ_lo : 0 < ρ.re) (hρ_hi : ρ.re < 1) (him : s.im ≠ ρ.im) :
    let s₀ : ℂ := (2 : ℂ) + (s.im : ℂ) * I
    ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖ ≤ 1 / |s.im - ρ.im| + 1 ∧
      ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖ ≤ 3 / (s.im - ρ.im) ^ 2 := by
  intro s₀
  have him_pos : 0 < |s.im - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr him)
  have hnorm_sρ : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
    have h := Complex.abs_im_le_norm (s - ρ)
    simpa using h
  have hnorm_s₀ρ_im : |s.im - ρ.im| ≤ ‖s₀ - ρ‖ := by
    have h := Complex.abs_im_le_norm (s₀ - ρ)
    simpa [s₀] using h
  have hnorm_s₀ρ_re : 1 ≤ ‖s₀ - ρ‖ := by
    have h := Complex.abs_re_le_norm (s₀ - ρ)
    have h1 : 1 ≤ |(s₀ - ρ).re| := by
      have : (s₀ - ρ).re = 2 - ρ.re := by simp [s₀]
      rw [this, abs_of_pos (by linarith)]
      linarith
    exact h1.trans h
  have hsρ_ne : s - ρ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le him_pos hnorm_sρ)
  have hs₀ρ_ne : s₀ - ρ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hnorm_s₀ρ_re)
  constructor
  · have h1 : ‖1 / (s - ρ)‖ ≤ 1 / |s.im - ρ.im| := by
      rw [norm_div, norm_one]
      exact div_le_div_of_nonneg_left zero_le_one him_pos hnorm_sρ
    have h2 : ‖1 / (s₀ - ρ)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact div_le_one_of_le₀ hnorm_s₀ρ_re (norm_nonneg _)
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  · have heq : 1 / (s - ρ) - 1 / (s₀ - ρ) = (s₀ - s) / ((s - ρ) * (s₀ - ρ)) := by
      field_simp [hsρ_ne, hs₀ρ_ne]
      ring
    have hs₀s_norm : ‖s₀ - s‖ ≤ 3 := by
      have heq_re : s₀ - s = ((2 - s.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [s₀]
      rw [heq_re, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hden_ge : (s.im - ρ.im) ^ 2 ≤ ‖(s - ρ) * (s₀ - ρ)‖ := by
      rw [norm_mul, ← sq_abs (s.im - ρ.im), sq]
      exact mul_le_mul hnorm_sρ hnorm_s₀ρ_im (abs_nonneg _) (norm_nonneg _)
    have hden_pos : 0 < (s.im - ρ.im) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr him)
    rw [heq, norm_div]
    exact div_le_div₀ (by positivity) hs₀s_norm hden_pos hden_ge

private lemma summable_log_add_two_div_sq :
    Summable fun k : ℕ ↦ if k = 0 then (0 : ℝ) else Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2 := by
  have hsum : Summable fun k : ℕ ↦ (2 * Real.sqrt 3) * (k : ℝ) ^ (-3 / 2 : ℝ) := by
    have h1 : Summable fun k : ℕ ↦ ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
      Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)
    have h2 : Summable fun k : ℕ ↦ (k : ℝ) ^ (-3 / 2 : ℝ) := by
      refine h1.congr fun k ↦ ?_
      rw [← Real.rpow_neg (Nat.cast_nonneg k)]
      congr 1
      norm_num
    exact h2.mul_left (2 * Real.sqrt 3)
  refine hsum.of_nonneg_of_le (fun k ↦ by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg _)) fun k ↦ ?_
  split_ifs with hk0
  · positivity
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkr_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
    have hkr_ge1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk1
    have hlog := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)
      (by norm_num : (0 : ℝ) < 1 / 2)
    have hdiv : ((k : ℝ) + 2) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
        2 * ((k : ℝ) + 2) ^ (1 / 2 : ℝ) := by ring
    have hle_3k : (k : ℝ) + 2 ≤ 3 * k := by linarith
    have hrpow_le : ((k : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 * (k : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        ((k : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (3 * (k : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle_3k (by norm_num)
        _ = (3 : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (by norm_num) hkr_pos.le
        _ = Real.sqrt 3 * (k : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]
    have hnum : Real.log ((k : ℝ) + 2) ≤ (2 * Real.sqrt 3) * (k : ℝ) ^ (1 / 2 : ℝ) := by
      linarith [hlog, hdiv, hrpow_le]
    have hpow_eq : (k : ℝ) ^ (1 / 2 : ℝ) / (k : ℝ) ^ 2 = (k : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_sub hkr_pos]
      congr 1
      norm_num
    calc
      Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2
          ≤ ((2 * Real.sqrt 3) * (k : ℝ) ^ (1 / 2 : ℝ)) / (k : ℝ) ^ 2 := by gcongr
      _ = (2 * Real.sqrt 3) * ((k : ℝ) ^ (1 / 2 : ℝ) / (k : ℝ) ^ 2) := by ring
      _ = (2 * Real.sqrt 3) * (k : ℝ) ^ (-3 / 2 : ℝ) := by rw [hpow_eq]

private lemma sum_zeroMultiplicity_logDeriv_diff_le :
    ∃ C > 0, ∀ (s : ℂ) (δ : ℝ) (S : Finset ℂ),
      -1 / 2 ≤ s.re → s.re ≤ 4 → 0 < δ → δ ≤ 1 →
      (∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ δ ≤ |s.im - ρ.im|) →
        ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) *
            ‖1 / (s - ρ) - 1 / ((2 : ℂ) + (s.im : ℂ) * I - ρ)‖ ≤
          C * (1 / δ) * Real.log (|s.im| + 2) := by
  obtain ⟨C_str, hCstr_pos, hstrip⟩ := sum_zeroMultiplicity_strip_le
  have hsum_inv_sq : Summable fun k : ℕ ↦ ((k : ℝ) ^ 2)⁻¹ := by
    simp
  let C_sq : ℝ := ∑' k : ℕ, ((k : ℝ) ^ 2)⁻¹
  let C_log : ℝ := ∑' k : ℕ, if k = 0 then (0 : ℝ) else Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2
  have hCsq_nn : 0 ≤ C_sq := tsum_nonneg fun _ ↦ by positivity
  have hClog_nn : 0 ≤ C_log := tsum_nonneg fun k ↦ by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg _)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let C : ℝ := 2 * C_str + 6 * C_str * (C_sq + C_log / Real.log 2) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    have hnn1 : 0 ≤ 6 * C_str * (C_sq + C_log / Real.log 2) :=
      mul_nonneg (by positivity) (add_nonneg hCsq_nn (div_nonneg hClog_nn hlog2_pos.le))
    linarith
  refine ⟨C, hC_pos, fun s δ S hs_lo hs_hi hδ_pos hδ_le1 hS ↦ ?_⟩
  let s₀ : ℂ := (2 : ℂ) + (s.im : ℂ) * I
  let term : ℂ → ℝ := fun ρ ↦ (zeroMultiplicity ρ : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖
  have hterm_nn : ∀ ρ, 0 ≤ term ρ := fun ρ ↦ by positivity
  let K : ℕ := S.sup fun ρ ↦ ⌊|s.im - ρ.im|⌋₊
  let band : ℕ → Finset ℂ := fun k ↦ S.filter fun ρ ↦ ⌊|s.im - ρ.im|⌋₊ = k
  have hS_part :
      ∑ ρ ∈ S, term ρ = ∑ k ∈ Finset.range (K + 1), ∑ ρ ∈ band k, term ρ := by
    have hS_eq : S = (Finset.range (K + 1)).biUnion band := by
      ext ρ
      simp only [Finset.mem_biUnion, Finset.mem_range, band, Finset.mem_filter]
      constructor
      · intro hρS
        exact ⟨⌊|s.im - ρ.im|⌋₊,
          Nat.lt_succ_of_le (Finset.le_sup (f := fun ρ : ℂ ↦ ⌊|s.im - ρ.im|⌋₊) hρS), hρS, rfl⟩
      · rintro ⟨k, _, hρS, _⟩
        exact hρS
    rw [hS_eq, Finset.sum_biUnion]
    intro k₁ _ k₂ _ hne
    change Disjoint (band k₁) (band k₂)
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    simp only [band, Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  have hband0 :
      ∑ ρ ∈ band 0, term ρ ≤ (2 * C_str) * (1 / δ) * Real.log (|s.im| + 2) := by
    have hpt : ∀ ρ ∈ band 0, term ρ ≤ 2 / δ * (zeroMultiplicity ρ : ℝ) := by
      intro ρ hρ
      have hρS := (Finset.mem_filter.mp hρ).1
      have hρ_spec := hS ρ hρS
      have him : s.im ≠ ρ.im := fun h ↦ by
        have hgap := hρ_spec.2.2.2
        rw [h, sub_self, abs_zero] at hgap
        linarith
      have h1 := (norm_inv_sub_inv_le_of_re_band hs_lo hs_hi hρ_spec.2.1 hρ_spec.2.2.1 him).1
      have hinv : 1 / |s.im - ρ.im| + 1 ≤ 2 / δ := by
        have hinv1 : 1 / |s.im - ρ.im| ≤ 1 / δ := one_div_le_one_div_of_le hδ_pos hρ_spec.2.2.2
        have hinv2 : (1 : ℝ) ≤ 1 / δ := (one_le_div hδ_pos).mpr hδ_le1
        have hinv_eq : 2 / δ = 1 / δ + 1 / δ := by ring
        linarith
      dsimp [term]
      calc
        (zeroMultiplicity ρ : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖
            ≤ (zeroMultiplicity ρ : ℝ) * (2 / δ) :=
          mul_le_mul_of_nonneg_left (h1.trans hinv) (Nat.cast_nonneg _)
        _ = 2 / δ * (zeroMultiplicity ρ : ℝ) := by ring
    have hsum_le : ∑ ρ ∈ band 0, term ρ ≤ (2 / δ) * ∑ ρ ∈ band 0, (zeroMultiplicity ρ : ℝ) := by
      calc
        ∑ ρ ∈ band 0, term ρ ≤ ∑ ρ ∈ band 0, 2 / δ * (zeroMultiplicity ρ : ℝ) :=
          Finset.sum_le_sum hpt
        _ = (2 / δ) * ∑ ρ ∈ band 0, (zeroMultiplicity ρ : ℝ) := by rw [← Finset.mul_sum]
    have hstrip0 : ∑ ρ ∈ band 0, (zeroMultiplicity ρ : ℝ) ≤ C_str * Real.log (|s.im| + 2) := by
      refine hstrip s.im (band 0) fun ρ hρ ↦ ?_
      have hf := Finset.mem_filter.mp hρ
      have hρ_spec := hS ρ hf.1
      refine ⟨hρ_spec.1, hρ_spec.2.1, hρ_spec.2.2.1, ?_⟩
      have hlt1 : |s.im - ρ.im| < 1 := (Nat.floor_eq_zero.mp hf.2).trans_le le_rfl
      rw [abs_sub_comm]
      linarith
    calc
      ∑ ρ ∈ band 0, term ρ ≤ (2 / δ) * (C_str * Real.log (|s.im| + 2)) :=
        hsum_le.trans (mul_le_mul_of_nonneg_left hstrip0 (by positivity))
      _ = (2 * C_str) * (1 / δ) * Real.log (|s.im| + 2) := by ring
  have hbandk : ∀ k : ℕ, 1 ≤ k →
      ∑ ρ ∈ band k, term ρ ≤
        (6 * C_str * (Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2))) / (k : ℝ) ^ 2 := by
    intro k hk1
    have hkr_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
    let bPos := (band k).filter fun ρ ↦ s.im ≤ ρ.im
    let bNeg := (band k).filter fun ρ ↦ ρ.im < s.im
    have hsplit : band k = bPos ∪ bNeg := by
      ext ρ
      simp only [bPos, bNeg, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h
        rcases le_or_gt s.im ρ.im with hle | hlt
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, hlt⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdisj : Disjoint bPos bNeg := by
      rw [Finset.disjoint_left]
      intro ρ hp hn
      simp only [bPos, bNeg, Finset.mem_filter] at hp hn
      linarith
    have hpt : ∀ ρ ∈ band k, term ρ ≤ (3 / (k : ℝ) ^ 2) * (zeroMultiplicity ρ : ℝ) := by
      intro ρ hρ
      have hf := Finset.mem_filter.mp hρ
      have hρ_spec := hS ρ hf.1
      have hfl_ge : (k : ℝ) ≤ |s.im - ρ.im| := by
        rw [← hf.2]
        exact Nat.floor_le (abs_nonneg _)
      have him : s.im ≠ ρ.im := fun h ↦ by
        rw [h, sub_self, abs_zero] at hfl_ge
        linarith
      have h2 := (norm_inv_sub_inv_le_of_re_band hs_lo hs_hi hρ_spec.2.1 hρ_spec.2.2.1 him).2
      have hinv_le : 3 / (s.im - ρ.im) ^ 2 ≤ 3 / (k : ℝ) ^ 2 := by
        have hsq : (k : ℝ) ^ 2 ≤ (s.im - ρ.im) ^ 2 := by
          rw [← sq_abs (s.im - ρ.im)]
          exact pow_le_pow_left₀ hkr_pos.le hfl_ge 2
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hkr_pos) hsq
      dsimp [term]
      calc
        (zeroMultiplicity ρ : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖
            ≤ (zeroMultiplicity ρ : ℝ) * (3 / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (h2.trans hinv_le) (Nat.cast_nonneg _)
        _ = (3 / (k : ℝ) ^ 2) * (zeroMultiplicity ρ : ℝ) := by ring
    have hlog_prod : ∀ τ : ℝ, |τ| ≤ |s.im| + k + 1 →
        Real.log (|τ| + 2) ≤ Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2) := by
      intro τ hτ
      have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hmul_ge : |τ| + 2 ≤ (|s.im| + 2) * ((k : ℝ) + 2) := by
        nlinarith [abs_nonneg s.im, hk_ge1]
      calc
        Real.log (|τ| + 2) ≤ Real.log ((|s.im| + 2) * ((k : ℝ) + 2)) :=
          Real.log_le_log (by positivity) hmul_ge
        _ = Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2) :=
          Real.log_mul (by positivity) (by positivity)
    have hpos_strip : ∑ ρ ∈ bPos, (zeroMultiplicity ρ : ℝ) ≤
        C_str * (Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2)) := by
      have h1 : ∑ ρ ∈ bPos, (zeroMultiplicity ρ : ℝ) ≤
          C_str * Real.log (|s.im + ((k : ℝ) + 1 / 2)| + 2) := by
        refine hstrip (s.im + ((k : ℝ) + 1 / 2)) bPos fun ρ hρ ↦ ?_
        have hpf := Finset.mem_filter.mp hρ
        have hbf := Finset.mem_filter.mp hpf.1
        have hρ_spec := hS ρ hbf.1
        refine ⟨hρ_spec.1, hρ_spec.2.1, hρ_spec.2.2.1, ?_⟩
        have hlo : (k : ℝ) ≤ ρ.im - s.im := by
          have := Nat.floor_le (abs_nonneg (s.im - ρ.im))
          rw [hbf.2, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hpf.2)] at this
          exact this
        have hhi : ρ.im - s.im < (k : ℝ) + 1 := by
          have := Nat.lt_floor_add_one |s.im - ρ.im|
          rw [hbf.2, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hpf.2)] at this
          exact this
        rw [abs_le]
        constructor <;> linarith
      have hτ_le : |s.im + ((k : ℝ) + 1 / 2)| ≤ |s.im| + k + 1 := by
        have hk_pos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
        exact (abs_add_le _ _).trans (by rw [abs_of_pos hk_pos]; linarith)
      exact h1.trans (mul_le_mul_of_nonneg_left (hlog_prod _ hτ_le) hCstr_pos.le)
    have hneg_strip : ∑ ρ ∈ bNeg, (zeroMultiplicity ρ : ℝ) ≤
        C_str * (Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2)) := by
      have h1 : ∑ ρ ∈ bNeg, (zeroMultiplicity ρ : ℝ) ≤
          C_str * Real.log (|s.im - ((k : ℝ) + 1 / 2)| + 2) := by
        refine hstrip (s.im - ((k : ℝ) + 1 / 2)) bNeg fun ρ hρ ↦ ?_
        have hpf := Finset.mem_filter.mp hρ
        have hbf := Finset.mem_filter.mp hpf.1
        have hρ_spec := hS ρ hbf.1
        refine ⟨hρ_spec.1, hρ_spec.2.1, hρ_spec.2.2.1, ?_⟩
        have hlo : (k : ℝ) ≤ s.im - ρ.im := by
          have := Nat.floor_le (abs_nonneg (s.im - ρ.im))
          rw [hbf.2, abs_of_pos (sub_pos.mpr hpf.2)] at this
          exact this
        have hhi : s.im - ρ.im < (k : ℝ) + 1 := by
          have := Nat.lt_floor_add_one |s.im - ρ.im|
          rw [hbf.2, abs_of_pos (sub_pos.mpr hpf.2)] at this
          exact this
        rw [abs_le]
        constructor <;> linarith
      have hτ_le : |s.im - ((k : ℝ) + 1 / 2)| ≤ |s.im| + k + 1 := by
        have hk_pos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
        exact (abs_sub _ _).trans (by rw [abs_of_pos hk_pos]; linarith)
      exact h1.trans (mul_le_mul_of_nonneg_left (hlog_prod _ hτ_le) hCstr_pos.le)
    have hsum_mult :
        ∑ ρ ∈ band k, (zeroMultiplicity ρ : ℝ) ≤
          2 * C_str * (Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2)) := by
      rw [hsplit, Finset.sum_union hdisj]
      linarith
    calc
      ∑ ρ ∈ band k, term ρ
          ≤ ∑ ρ ∈ band k, (3 / (k : ℝ) ^ 2) * (zeroMultiplicity ρ : ℝ) := Finset.sum_le_sum hpt
      _ = (3 / (k : ℝ) ^ 2) * ∑ ρ ∈ band k, (zeroMultiplicity ρ : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ (3 / (k : ℝ) ^ 2) * (2 * C_str * (Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left hsum_mult (by positivity)
      _ = (6 * C_str * (Real.log (|s.im| + 2) + Real.log ((k : ℝ) + 2))) / (k : ℝ) ^ 2 := by
          ring
  have hlog_s_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log zero_lt_two (by linarith [abs_nonneg s.im])
  have h1_le_log : 1 ≤ Real.log (|s.im| + 2) / Real.log 2 := (one_le_div hlog2_pos).mpr hlog_s_ge
  have h1_le_invδ : 1 ≤ 1 / δ := (one_le_div hδ_pos).mpr hδ_le1
  have htail_sum :
      ∑ k ∈ Finset.Icc 1 K, ∑ ρ ∈ band k, term ρ ≤
        6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2) := by
    have h1 :
        ∑ k ∈ Finset.Icc 1 K, ∑ ρ ∈ band k, term ρ ≤
          ∑ k ∈ Finset.Icc 1 K,
            (6 * C_str * Real.log (|s.im| + 2) * ((k : ℝ) ^ 2)⁻¹ +
              6 * C_str * (if k = 0 then (0 : ℝ) else Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2)) := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk1
      refine (hbandk k hk1).trans_eq ?_
      simp only [hk0, ↓reduceIte]
      ring
    have h2 :
        ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ ≤ C_sq :=
      hsum_inv_sq.sum_le_tsum (Finset.Icc 1 K) fun _ _ ↦ by positivity
    have h3 :
        ∑ k ∈ Finset.Icc 1 K, (if k = 0 then (0 : ℝ) else Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2) ≤
          C_log :=
      summable_log_add_two_div_sq.sum_le_tsum (Finset.Icc 1 K) fun _ _ ↦ by
        split_ifs
        · exact le_rfl
        · exact div_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg _)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have hlog_nn : 0 ≤ Real.log (|s.im| + 2) := by linarith
    have h4 : 6 * C_str * Real.log (|s.im| + 2) * C_sq + 6 * C_str * C_log ≤
        6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2) := by
      have hcle : C_log ≤ (C_log / Real.log 2) * Real.log (|s.im| + 2) := by
        calc
          C_log = C_log * 1 := (mul_one _).symm
          _ ≤ C_log * (Real.log (|s.im| + 2) / Real.log 2) :=
              mul_le_mul_of_nonneg_left h1_le_log hClog_nn
          _ = (C_log / Real.log 2) * Real.log (|s.im| + 2) := by ring
      nlinarith [hCstr_pos, hcle]
    calc
      ∑ k ∈ Finset.Icc 1 K, ∑ ρ ∈ band k, term ρ
          ≤ 6 * C_str * Real.log (|s.im| + 2) * C_sq + 6 * C_str * C_log :=
        h1.trans (add_le_add
          (mul_le_mul_of_nonneg_left h2 (by positivity))
          (mul_le_mul_of_nonneg_left h3 (by positivity)))
      _ ≤ 6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2) := h4
  have hrange_split :
      ∑ k ∈ Finset.range (K + 1), ∑ ρ ∈ band k, term ρ =
        (∑ ρ ∈ band 0, term ρ) + ∑ k ∈ Finset.Icc 1 K, ∑ ρ ∈ band k, term ρ := by
    have hsplit : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
  rw [hS_part, hrange_split]
  have htail_scaled :
      6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2) ≤
        6 * C_str * (C_sq + C_log / Real.log 2) * (1 / δ) * Real.log (|s.im| + 2) := by
    have hlog_nn : 0 ≤ Real.log (|s.im| + 2) := by linarith
    have hnn : 0 ≤ 6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2) :=
      mul_nonneg (mul_nonneg (by positivity) (add_nonneg hCsq_nn (div_nonneg hClog_nn hlog2_pos.le)))
        hlog_nn
    calc
      6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2)
          = (6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2)) * 1 := (mul_one _).symm
      _ ≤ (6 * C_str * (C_sq + C_log / Real.log 2) * Real.log (|s.im| + 2)) * (1 / δ) :=
          mul_le_mul_of_nonneg_left h1_le_invδ hnn
      _ = 6 * C_str * (C_sq + C_log / Real.log 2) * (1 / δ) * Real.log (|s.im| + 2) := by ring
  calc
    (∑ ρ ∈ band 0, term ρ) + ∑ k ∈ Finset.Icc 1 K, ∑ ρ ∈ band k, term ρ
        ≤ (2 * C_str) * (1 / δ) * Real.log (|s.im| + 2) +
            6 * C_str * (C_sq + C_log / Real.log 2) * (1 / δ) * Real.log (|s.im| + 2) :=
        add_le_add hband0 (htail_sum.trans htail_scaled)
    _ ≤ C * (1 / δ) * Real.log (|s.im| + 2) := by
        have hlog_nn : 0 ≤ Real.log (|s.im| + 2) := by linarith
        have hpos : 0 ≤ (1 / δ) * Real.log (|s.im| + 2) :=
          mul_nonneg (one_div_nonneg.mpr hδ_pos.le) hlog_nn
        have hC_ge : 2 * C_str + 6 * C_str * (C_sq + C_log / Real.log 2) ≤ C := by
          dsimp [C]; linarith
        calc
          (2 * C_str) * (1 / δ) * Real.log (|s.im| + 2) +
              6 * C_str * (C_sq + C_log / Real.log 2) * (1 / δ) * Real.log (|s.im| + 2)
              = (2 * C_str + 6 * C_str * (C_sq + C_log / Real.log 2)) *
                  ((1 / δ) * Real.log (|s.im| + 2)) := by ring
          _ ≤ C * ((1 / δ) * Real.log (|s.im| + 2)) :=
              mul_le_mul_of_nonneg_right hC_ge hpos
          _ = C * (1 / δ) * Real.log (|s.im| + 2) := by ring

private lemma list_norm_sum_le_toFinset_count (zs : List ℂ) (f : ℂ → ℂ) :
    ‖(zs.map f).sum‖ ≤ ∑ z ∈ zs.toFinset, (zs.count z : ℝ) * ‖f z‖ := by
  induction zs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have htri : ‖f x + (xs.map f).sum‖ ≤ ‖f x‖ + ‖(xs.map f).sum‖ := norm_add_le _ _
    have hto : (x :: xs).toFinset = insert x xs.toFinset := List.toFinset_cons
    rw [hto]
    by_cases hx : x ∈ xs.toFinset
    · rw [Finset.insert_eq_of_mem hx]
      have hsum :
          ∑ z ∈ xs.toFinset, (((x :: xs).count z : ℕ) : ℝ) * ‖f z‖ =
            ‖f x‖ + ∑ z ∈ xs.toFinset, (xs.count z : ℝ) * ‖f z‖ := by
        have hpt : ∀ z ∈ xs.toFinset,
            (((x :: xs).count z : ℕ) : ℝ) * ‖f z‖ =
              (if z = x then ‖f x‖ else 0) + (xs.count z : ℝ) * ‖f z‖ := by
          intro z _
          by_cases hzx : z = x
          · subst hzx
            have hif : (if z = z then ‖f z‖ else 0) = ‖f z‖ := by simp
            rw [List.count_cons_self, hif]
            push_cast
            ring
          · rw [List.count_cons_of_ne (Ne.symm hzx)]
            simp [hzx]
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp [hx]
      linarith [htri, ih, hsum]
    · rw [Finset.sum_insert hx]
      have hx_not_xs : x ∉ xs := by simpa [List.mem_toFinset] using hx
      have hcount_x : (x :: xs).count x = 1 := by
        rw [List.count_cons_self, List.count_eq_zero.mpr hx_not_xs]
      have hrest :
          ∑ z ∈ xs.toFinset, (((x :: xs).count z : ℕ) : ℝ) * ‖f z‖ =
            ∑ z ∈ xs.toFinset, (xs.count z : ℝ) * ‖f z‖ := by
        refine Finset.sum_congr rfl fun z hz ↦ ?_
        have hzx : z ≠ x := fun h ↦ hx (h ▸ hz)
        rw [List.count_cons_of_ne (Ne.symm hzx)]
      rw [hcount_x, Nat.cast_one, one_mul, hrest]
      linarith

private lemma finset_sum_fiberwise_card_mul (s : Finset ℕ) (a : ℕ → ℂ) (g : ℂ → ℝ) :
    ∑ n ∈ s, g (a n) =
      ∑ z ∈ s.image a, ((s.filter fun n ↦ a n = z).card : ℝ) * g z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, ih, Finset.image_insert]
    by_cases him : a n ∈ s.image a
    · rw [Finset.insert_eq_of_mem him]
      have hpt : ∀ z ∈ s.image a,
          (((insert n s).filter (fun k ↦ a k = z)).card : ℝ) * g z =
            (if z = a n then g (a n) else 0) + ((s.filter fun k ↦ a k = z).card : ℝ) * g z := by
        intro z _
        by_cases hza : z = a n
        · subst hza
          have hflt : (insert n s).filter (fun k ↦ a k = a n) =
              insert n (s.filter (fun k ↦ a k = a n)) := by
            simp [Finset.filter_insert]
          have hnotin : n ∉ s.filter (fun k ↦ a k = a n) := by
            simp [Finset.mem_filter, hn]
          have hif : (if a n = a n then g (a n) else 0) = g (a n) := by simp
          rw [hflt, Finset.card_insert_of_notMem hnotin, hif]
          push_cast
          ring
        · have hflt : (insert n s).filter (fun k ↦ a k = z) = s.filter (fun k ↦ a k = z) := by
            simp [Finset.filter_insert, Ne.symm hza]
          rw [hflt]
          simp [hza]
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [him]
    · rw [Finset.sum_insert him]
      have hflt_an : (insert n s).filter (fun k ↦ a k = a n) = {n} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hks, hak⟩
          · rfl
          · exfalso; exact him (Finset.mem_image.mpr ⟨k, hks, hak⟩)
        · rintro rfl
          exact ⟨Or.inl rfl, rfl⟩
      have hrest :
          ∑ z ∈ s.image a, (((insert n s).filter (fun k ↦ a k = z)).card : ℝ) * g z =
            ∑ z ∈ s.image a, ((s.filter fun k ↦ a k = z).card : ℝ) * g z := by
        refine Finset.sum_congr rfl fun z hz ↦ ?_
        have hza : z ≠ a n := fun h ↦ him (h ▸ hz)
        simp [Finset.filter_insert, Ne.symm hza]
      rw [hflt_an, Finset.card_singleton, Nat.cast_one, one_mul, hrest]

private lemma summable_logDeriv_genus_one_tail {a : ℕ → ℂ} {z : ℂ}
    (ha_ne : ∀ n, a n ≠ 0) (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (hsum : Summable fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) (hz : ∀ n, z ≠ a n) :
    Summable fun n : ℕ ↦ 1 / (z - a n) + 1 / a n := by
  have hnorm_sum : Summable fun n : ℕ ↦ ‖1 / (z - a n) + 1 / a n‖ := by
    let R : ℝ := 2 * ‖z‖ + 1
    have hfin := ha_fin R
    let F : Finset ℕ := hfin.toFinset
    have hdom : Summable fun n : ℕ ↦ (2 * ‖z‖) * ‖a n‖ ^ (-2 : ℝ) := hsum.mul_left _
    have hhead : Summable fun n : ℕ ↦ if n ∈ F then ‖1 / (z - a n) + 1 / a n‖ else 0 :=
      summable_of_ne_finset_zero (s := F) fun n hn ↦ by simp [hn]
    have htail : Summable fun n : ℕ ↦ if n ∉ F then ‖1 / (z - a n) + 1 / a n‖ else 0 := by
      refine hdom.of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity) fun n ↦ ?_
      by_cases hnF : n ∈ F
      · simp only [hnF, not_true_eq_false, ↓reduceIte]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
      · simp only [hnF, not_false_eq_true, ↓reduceIte]
        have hgt : R < ‖a n‖ := by
          by_contra hle
          have hmem : n ∈ F := (Set.Finite.mem_toFinset hfin).mpr (le_of_not_gt hle)
          exact hnF hmem
        have hane : a n ≠ 0 := ha_ne n
        have hzne : z - a n ≠ 0 := sub_ne_zero.mpr (hz n)
        have heq : 1 / (z - a n) + 1 / a n = z / (a n * (z - a n)) := by
          field_simp [hzne, hane]
          ring
        have hlow : ‖a n‖ / 2 ≤ ‖z - a n‖ := by
          have hrev := norm_sub_norm_le (a n) z
          rw [norm_sub_rev] at hrev
          have : 2 * ‖z‖ < ‖a n‖ := by dsimp [R] at hgt; linarith
          linarith
        have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr hane
        have hden_ge : ‖a n‖ ^ 2 / 2 ≤ ‖a n * (z - a n)‖ := by
          rw [norm_mul, sq]
          calc
            ‖a n‖ * ‖a n‖ / 2 = ‖a n‖ * (‖a n‖ / 2) := by ring
            _ ≤ ‖a n‖ * ‖z - a n‖ := mul_le_mul_of_nonneg_left hlow han_pos.le
        have hden_pos : 0 < ‖a n‖ ^ 2 / 2 := by positivity
        rw [heq, norm_div]
        calc
          ‖z‖ / ‖a n * (z - a n)‖ ≤ ‖z‖ / (‖a n‖ ^ 2 / 2) :=
            div_le_div_of_nonneg_left (norm_nonneg _) hden_pos hden_ge
          _ = (2 * ‖z‖) * (‖a n‖ ^ (2 : ℕ))⁻¹ := by ring
          _ = (2 * ‖z‖) * ‖a n‖ ^ (-2 : ℝ) := by
              rw [← Real.rpow_natCast ‖a n‖ 2, ← Real.rpow_neg han_pos.le]
              congr 1
    refine (hhead.add htail).congr fun n ↦ ?_
    by_cases hnF : n ∈ F <;> simp [hnF]
  exact hnorm_sum.of_norm

private lemma list_sub_map_sum (zs : List ℂ) (s s₀ : ℂ) :
    (zs.map fun w ↦ 1 / (s - w) + 1 / w).sum - (zs.map fun w ↦ 1 / (s₀ - w) + 1 / w).sum =
      (zs.map fun w ↦ 1 / (s - w) - 1 / (s₀ - w)).sum := by
  induction zs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [show (1 / (s - x) + 1 / x + (List.map (fun w ↦ 1 / (s - w) + 1 / w) xs).sum) -
        (1 / (s₀ - x) + 1 / x + (List.map (fun w ↦ 1 / (s₀ - w) + 1 / w) xs).sum) =
        (1 / (s - x) - 1 / (s₀ - x)) +
        ((List.map (fun w ↦ 1 / (s - w) + 1 / w) xs).sum -
          (List.map (fun w ↦ 1 / (s₀ - w) + 1 / w) xs).sum) by ring, ih]

private lemma norm_logDeriv_xi_sub_center_le :
    ∃ C > 0, ∀ (s : ℂ) (δ : ℝ),
      -1 / 2 ≤ s.re → s.re ≤ 4 → 0 < δ → δ ≤ 1 → s.im ≠ 0 → xi s ≠ 0 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → δ ≤ |s.im - ρ.im|) →
        ‖deriv xi s / xi s - deriv xi ((2 : ℂ) + (s.im : ℂ) * I) / xi ((2 : ℂ) + (s.im : ℂ) * I)‖ ≤
          C * (1 / δ) * Real.log (|s.im| + 2) := by
  obtain ⟨C₀, hC₀_pos, hmaster⟩ := sum_zeroMultiplicity_logDeriv_diff_le
  have hxi_ne : xi ≠ 0 := fun h ↦ xi_ne_zero_of_re_nonpos (s := 0) (by simp) (by simpa using congrFun h 0)
  have hord0 : analyticOrderNatAt xi 0 = 0 := by
    have h0 : xi 0 ≠ 0 := by rw [xi_zero]; norm_num
    have hord : analyticOrderAt xi 0 = 0 :=
      (analyticOnNhd_xi 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr h0
    simp [analyticOrderNatAt, hord]
  refine ⟨C₀, hC₀_pos, fun s δ hs_lo hs_hi hδ_pos hδ_le1 hs_im hxi_s hgap ↦ ?_⟩
  let s₀ : ℂ := (2 : ℂ) + (s.im : ℂ) * I
  have hs_ne0 : s ≠ 0 := fun h ↦ hs_im (by simp [h])
  have hs₀_ne0 : s₀ ≠ 0 := fun h ↦ hs_im (by
    have him := congrArg Complex.im h
    simpa [s₀] using him)
  have hxi_s₀ : xi s₀ ≠ 0 := xi_ne_zero_of_one_le_re (by simp [s₀])
  rcases hadamard_logDeriv_genus_one differentiable_xi hxi_ne zero_le_one entireOrderLe_xi_one
      one_lt_two with
    ⟨zs, A, B, hzs_ne, hzs_count, _, hzs_ld⟩ |
    ⟨a, A, B, ha_ne, ha_fin, ha_card, ha_sum, _, ha_ld⟩
  · have hld_s := hzs_ld s hs_ne0 hxi_s
    have hld_s₀ := hzs_ld s₀ hs₀_ne0 hxi_s₀
    rw [hord0, Nat.cast_zero, zero_div, zero_add] at hld_s hld_s₀
    have hdiff_eq :
        deriv xi s / xi s - deriv xi s₀ / xi s₀ =
          (zs.map fun w ↦ 1 / (s - w) - 1 / (s₀ - w)).sum := by
      rw [hld_s, hld_s₀]
      have hsub_map := list_sub_map_sum zs s s₀
      linear_combination hsub_map
    rw [hdiff_eq]
    refine (list_norm_sum_le_toFinset_count zs fun w ↦ 1 / (s - w) - 1 / (s₀ - w)).trans ?_
    have hS : ∀ ρ ∈ zs.toFinset,
        riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ δ ≤ |s.im - ρ.im| := by
      intro ρ hρ
      have hρ_mem : ρ ∈ zs := List.mem_toFinset.mp hρ
      have hρ_ne : ρ ≠ 0 := hzs_ne ρ hρ_mem
      have hcnt : 0 < zs.count ρ := List.count_pos_iff.mpr hρ_mem
      rw [hzs_count ρ hρ_ne] at hcnt
      have hxi0 : xi ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hcnt.ne'
      have hζ0 := xi_eq_zero_iff.mp hxi0
      exact ⟨hζ0.1, hζ0.2.1, hζ0.2.2, hgap ρ hζ0.1 hζ0.2.1 hζ0.2.2⟩
    have hcnt_eq : ∀ ρ ∈ zs.toFinset, (zs.count ρ : ℝ) = (zeroMultiplicity ρ : ℝ) := by
      intro ρ hρ
      have hρ_mem : ρ ∈ zs := List.mem_toFinset.mp hρ
      have hρ_spec := hS ρ hρ
      rw [hzs_count ρ (hzs_ne ρ hρ_mem), ← zeroMultiplicity_eq_xi hρ_spec.2.1 hρ_spec.2.2.1]
    have hsum_eq :
        ∑ ρ ∈ zs.toFinset, (zs.count ρ : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖ =
          ∑ ρ ∈ zs.toFinset, (zeroMultiplicity ρ : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖ :=
      Finset.sum_congr rfl fun ρ hρ ↦ by rw [hcnt_eq ρ hρ]
    rw [hsum_eq]
    exact hmaster s δ zs.toFinset hs_lo hs_hi hδ_pos hδ_le1 hS
  · have hld_s := ha_ld s hs_ne0 hxi_s
    have hld_s₀ := ha_ld s₀ hs₀_ne0 hxi_s₀
    rw [hord0, Nat.cast_zero, zero_div, zero_add] at hld_s hld_s₀
    have ha_zero_prop : ∀ n : ℕ, riemannZeta (a n) = 0 ∧ 0 < (a n).re ∧ (a n).re < 1 := by
      intro n
      have hfin_fib : ({k : ℕ | a k = a n}).Finite :=
        (ha_fin ‖a n‖).subset fun k hk ↦ by simp only [Set.mem_ofPred_eq] at hk ⊢; rw [hk]
      have hpos : 0 < ({k : ℕ | a k = a n}).ncard := (Set.ncard_pos hfin_fib).mpr ⟨n, rfl⟩
      rw [ha_card (a n) (ha_ne n)] at hpos
      have hxi0 : xi (a n) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne'
      exact xi_eq_zero_iff.mp hxi0
    have hs_not : ∀ n : ℕ, s ≠ a n := by
      intro n h
      have hprop := ha_zero_prop n
      have hg := hgap (a n) hprop.1 hprop.2.1 hprop.2.2
      rw [← h, sub_self, abs_zero] at hg
      linarith
    have hs₀_not : ∀ n : ℕ, s₀ ≠ a n := by
      intro n h
      have hprop := ha_zero_prop n
      have hre : s₀.re = (a n).re := congrArg Complex.re h
      have hs₀re : s₀.re = 2 := by simp [s₀]
      linarith [hprop.2.2]
    have hsum_s := summable_logDeriv_genus_one_tail ha_ne ha_fin ha_sum hs_not
    have hsum_s₀ := summable_logDeriv_genus_one_tail ha_ne ha_fin ha_sum hs₀_not
    have hdiff_eq :
        deriv xi s / xi s - deriv xi s₀ / xi s₀ =
          ∑' n : ℕ, (1 / (s - a n) - 1 / (s₀ - a n)) := by
      rw [hld_s, hld_s₀, show (B + ∑' n : ℕ, (1 / (s - a n) + 1 / a n)) -
          (B + ∑' n : ℕ, (1 / (s₀ - a n) + 1 / a n)) =
          (∑' n : ℕ, (1 / (s - a n) + 1 / a n)) - ∑' n : ℕ, (1 / (s₀ - a n) + 1 / a n) by ring,
        ← hsum_s.tsum_sub hsum_s₀]
      refine tsum_congr fun n ↦ by ring
    have hsum_diff : Summable fun n : ℕ ↦ 1 / (s - a n) - 1 / (s₀ - a n) := by
      refine (hsum_s.sub hsum_s₀).congr fun n ↦ by ring
    have hsum_diff_norm : Summable fun n : ℕ ↦ ‖1 / (s - a n) - 1 / (s₀ - a n)‖ := by
      refine (hsum_s.norm.add hsum_s₀.norm).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
      have h := norm_sub_le (1 / (s - a n) + 1 / a n) (1 / (s₀ - a n) + 1 / a n)
      simpa only [show (1 / (s - a n) + 1 / a n) - (1 / (s₀ - a n) + 1 / a n) =
        1 / (s - a n) - 1 / (s₀ - a n) by ring] using h
    rw [hdiff_eq]
    refine (norm_tsum_le_tsum_norm hsum_diff_norm).trans ?_
    refine hsum_diff_norm.tsum_le_of_sum_range_le fun N ↦ ?_
    let S : Finset ℕ := Finset.range N
    rw [finset_sum_fiberwise_card_mul S a fun w ↦ ‖1 / (s - w) - 1 / (s₀ - w)‖]
    have hS_im : ∀ ρ ∈ S.image a,
        riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ δ ≤ |s.im - ρ.im| := by
      intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨n, _, rfl⟩
      have hprop := ha_zero_prop n
      exact ⟨hprop.1, hprop.2.1, hprop.2.2, hgap (a n) hprop.1 hprop.2.1 hprop.2.2⟩
    have hcard_le : ∀ ρ ∈ S.image a,
        ((S.filter fun n ↦ a n = ρ).card : ℝ) ≤ (zeroMultiplicity ρ : ℝ) := by
      intro ρ hρ
      have hρ_spec := hS_im ρ hρ
      have hρ_ne : ρ ≠ 0 := fun h ↦ by simp [h] at hρ_spec
      have hfin_fib : ({k : ℕ | a k = ρ}).Finite :=
        (ha_fin ‖ρ‖).subset fun k hk ↦ by simp only [Set.mem_ofPred_eq] at hk ⊢; rw [hk]
      have hsub_fib : ((S.filter fun n ↦ a n = ρ) : Set ℕ) ⊆ {k : ℕ | a k = ρ} := by
        intro k hk
        exact (Finset.mem_filter.mp hk).2
      have hnc : (S.filter fun n ↦ a n = ρ).card ≤ ({k : ℕ | a k = ρ}).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub_fib hfin_fib
      rw [ha_card ρ hρ_ne, ← zeroMultiplicity_eq_xi hρ_spec.2.1 hρ_spec.2.2.1] at hnc
      exact_mod_cast hnc
    have hsum_le :
        ∑ ρ ∈ S.image a, ((S.filter fun n ↦ a n = ρ).card : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖ ≤
          ∑ ρ ∈ S.image a, (zeroMultiplicity ρ : ℝ) * ‖1 / (s - ρ) - 1 / (s₀ - ρ)‖ :=
      Finset.sum_le_sum fun ρ hρ ↦ mul_le_mul_of_nonneg_right (hcard_le ρ hρ) (norm_nonneg _)
    exact hsum_le.trans (hmaster s δ (S.image a) hs_lo hs_hi hδ_pos hδ_le1 hS_im)

/-- Horizontal strip bound for `-deriv riemannZeta s / riemannZeta s` away from zeros:
for `-1/2 ≤ σ ≤ 4`, `2 ≤ |t|`, `0 < δ ≤ 1`, and zero-gap `δ ≤ |t - ρ.im|` for all nontrivial
zeros `ρ`, we have `riemannZeta (σ + t * I) ≠ 0` and
`‖-deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * (1 / δ) * log (|t| + 2)`. -/
theorem norm_neg_logDeriv_zeta_avoiding_le :
    ∃ C > 0, ∀ (σ t δ : ℝ), -1 / 2 ≤ σ → σ ≤ 4 → 2 ≤ |t| → 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → δ ≤ |t - ρ.im|) →
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧
          ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
              riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
            C * (1 / δ) * Real.log (|t| + 2) := by
  obtain ⟨C_diff, hCdiff_pos, hdiff_xi⟩ := norm_logDeriv_xi_sub_center_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let C_dig : ℝ := (1 / 2 + (1 + 8 * ((max |(-1 / 4 : ℝ)| |(2 : ℝ)|) ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12)
  let C : ℝ := C_diff + 1 + (6 + C_dig + Real.pi) / Real.log 2 + 1
  refine ⟨C, by positivity, fun σ t δ hσ_lo hσ_hi ht2 hδ_pos hδ_le1 hgap ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let s₀ : ℂ := (2 : ℂ) + (t : ℂ) * I
  have ht0 : t ≠ 0 := fun h ↦ by rw [h, abs_zero] at ht2; linarith
  have hs_im : s.im ≠ 0 := by simpa [s] using ht0
  have hs₀_im : s₀.im ≠ 0 := by simpa [s₀] using ht0
  have hζ_s : riemannZeta s ≠ 0 := by
    by_cases hre0 : s.re ≤ 0
    · exact riemannZeta_ne_zero_of_im_ne_zero_and_outside hs_im (xi_ne_zero_of_re_nonpos hre0)
    · by_cases hre1 : 1 ≤ s.re
      · exact riemannZeta_ne_zero_of_im_ne_zero_and_outside hs_im (xi_ne_zero_of_one_le_re hre1)
      · intro hz
        have hg := hgap s hz (lt_of_not_ge hre0) (lt_of_not_ge hre1)
        have : s.im = t := by simp [s]
        rw [this, sub_self, abs_zero] at hg
        linarith
  refine ⟨hζ_s, ?_⟩
  have hζ_s₀ : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_im_ne_zero_and_outside hs₀_im (xi_ne_zero_of_one_le_re (by simp [s₀]))
  have hxi_s : xi s ≠ 0 := by
    have hs_m : ∀ m : ℕ, s ≠ -2 * (m : ℂ) := fun m h ↦ hs_im (by
      have him := congrArg Complex.im h
      simp only [Complex.mul_im, Complex.neg_im, Complex.im_ofNat, Complex.natCast_im,
        mul_zero, zero_mul, neg_zero] at him
      simpa using him)
    have hs1 : s ≠ 1 := fun h ↦ hs_im (by simp [h])
    rw [xi_eq_formula hs_m hs1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (fun h ↦ hs_im (by simp [h]))) (sub_ne_zero.mpr hs1))
      (by rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
          exact Complex.exp_ne_zero _))
      (Complex.Gamma_ne_zero fun m h ↦ hs_im (by
        have him := congrArg Complex.im h
        simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im] at him
        linarith)))
      hζ_s
  have hld_s := logDeriv_xi_eq_logDeriv_zeta_add hs_im hζ_s
  have hld_s₀ := logDeriv_xi_eq_logDeriv_zeta_add hs₀_im hζ_s₀
  have hξ_diff :
      ‖deriv xi s / xi s - deriv xi s₀ / xi s₀‖ ≤ C_diff * (1 / δ) * Real.log (|t| + 2) := by
    have h := hdiff_xi s δ (by simpa [s] using hσ_lo) (by simpa [s] using hσ_hi) hδ_pos hδ_le1
      hs_im hxi_s (by simpa [s] using hgap)
    simpa [s, s₀] using h
  have hs₀_re : 1 < s₀.re := by simp [s₀]
  have hL_s₀ : ‖deriv riemannZeta s₀ / riemannZeta s₀‖ ≤ 4 := by
    have heq := LSeries_vonMangoldt_eq hs₀_re
    have hL : ‖LSeries (fun n ↦ (Λ n : ℂ)) s₀‖ ≤ 4 := by
      have hsumm : LSeriesSummable (fun n ↦ (Λ n : ℂ)) s₀ :=
        LSeriesSummable_vonMangoldt_iff.mpr hs₀_re
      have h1 : ‖LSeries (fun n ↦ (Λ n : ℂ)) s₀‖ ≤
          ∑' n : ℕ, ‖LSeries.term (fun k ↦ (Λ k : ℂ)) s₀ n‖ :=
        norm_tsum_le_tsum_norm hsumm.norm
      have htriv_lam : (fun k : ℕ ↦ (1 : DirichletCharacter ℂ 1) k * (Λ k : ℂ)) =
          fun k ↦ (Λ k : ℂ) := by
        ext k
        simp [Subsingleton.elim ((k : ZMod 1)) 1]
      have htriv_norm : ∀ n : ℕ,
          ‖LSeries.term (fun k ↦ (Λ k : ℂ)) s₀ n‖ =
            ‖LSeries.term (fun k : ℕ ↦ (Λ k : ℂ)) ((2 : ℝ) : ℂ) n‖ := by
        intro n
        rcases eq_or_ne n 0 with rfl | hn0
        · simp [LSeries.term_zero]
        · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
          rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
            norm_div, norm_div, Complex.norm_natCast_cpow_of_pos hn_pos,
            Complex.norm_natCast_cpow_of_pos hn_pos]
          simp [s₀]
      have h2 := tsum_norm_LSeries_term_twist_le (1 : DirichletCharacter ℂ 1) one_lt_two
      rw [htriv_lam] at h2
      have h2' : ∑' n : ℕ, ‖LSeries.term (fun k : ℕ ↦ (Λ k : ℂ)) ((2 : ℝ) : ℂ) n‖ ≤ 4 := by
        refine h2.trans_eq (by norm_num)
      refine h1.trans ?_
      rw [tsum_congr htriv_norm]
      exact h2'
    have hneg : deriv riemannZeta s₀ / riemannZeta s₀ = -LSeries (fun n ↦ (Λ n : ℂ)) s₀ := by
      rw [heq, neg_div, neg_neg]
    rw [hneg, norm_neg]
    exact hL
  have hnorm_inv : ∀ w : ℂ, 2 ≤ |w.im| → ‖1 / w‖ ≤ 1 / 2 := fun w hw ↦ by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left zero_le_one zero_lt_two (hw.trans (Complex.abs_im_le_norm w))
  have h1s : ‖1 / s‖ ≤ 1 / 2 := hnorm_inv s (by simpa [s] using ht2)
  have h1s1 : ‖1 / (s - 1)‖ ≤ 1 / 2 := hnorm_inv (s - 1) (by simpa [s] using ht2)
  have h1s₀ : ‖1 / s₀‖ ≤ 1 / 2 := hnorm_inv s₀ (by simpa [s₀] using ht2)
  have h1s₀1 : ‖1 / (s₀ - 1)‖ ≤ 1 / 2 := hnorm_inv (s₀ - 1) (by simpa [s₀] using ht2)
  have hdig_bound : ∀ u : ℝ, -1 / 2 ≤ u → u ≤ 4 →
      ‖digamma (((u : ℂ) + (t : ℂ) * I) / 2)‖ ≤ Real.log (|t| + 2) + C_dig + Real.pi := by
    intro u hu_lo hu_hi
    let w : ℂ := ((u / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I
    have hw_eq : ((u : ℂ) + (t : ℂ) * I) / 2 = w := by apply Complex.ext <;> simp [w]
    have hstrip := norm_digamma_sub_log_strip_le (σ₁ := -1 / 4) (σ₂ := 2) (σ := u / 2)
      (t := t / 2) ⟨by linarith, by linarith⟩ (by rw [abs_div, abs_two]; linarith)
    have hsub_le : ‖digamma w - Complex.log w‖ ≤ C_dig := by
      refine hstrip.trans ?_
      have hdiv1 : 1 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
      exact div_le_self (by positivity) hdiv1
    have hlog_le : ‖Complex.log w‖ ≤ Real.log (|t| + 2) + Real.pi := by
      have hnorm : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have harg : |(Complex.log w).im| ≤ Real.pi := by
        rw [Complex.log_im]
        exact Complex.abs_arg_le_pi w
      have hwn_ge : 1 ≤ ‖w‖ := by
        have him : |t / 2| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
        rw [abs_div, abs_two] at him
        linarith
      have hwn_le : ‖w‖ ≤ |t| + 2 := by
        have htri := Complex.norm_le_abs_re_add_abs_im w
        have hw_re : w.re = u / 2 := by simp [w]
        have hw_im : w.im = t / 2 := by simp [w]
        have hre : |w.re| ≤ 2 := by
          rw [hw_re]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        have him : |w.im| ≤ |t| := by
          rw [hw_im, abs_div, abs_two]
          linarith [abs_nonneg t]
        linarith
      have hre_log : |(Complex.log w).re| ≤ Real.log (|t| + 2) := by
        rw [Complex.log_re, abs_of_nonneg (Real.log_nonneg hwn_ge)]
        exact Real.log_le_log (by linarith) hwn_le
      linarith
    rw [hw_eq]
    calc
      ‖digamma w‖ = ‖(digamma w - Complex.log w) + Complex.log w‖ := by ring_nf
      _ ≤ ‖digamma w - Complex.log w‖ + ‖Complex.log w‖ := norm_add_le _ _
      _ ≤ C_dig + (Real.log (|t| + 2) + Real.pi) := add_le_add hsub_le hlog_le
      _ = Real.log (|t| + 2) + C_dig + Real.pi := by ring
  have hdig_s := hdig_bound σ hσ_lo hσ_hi
  have hdig_s₀ : ‖digamma (s₀ / 2)‖ ≤ Real.log (|t| + 2) + C_dig + Real.pi := by
    have h := hdig_bound 2 (by norm_num) (by norm_num)
    simpa only [s₀, Complex.ofReal_ofNat] using h
  have hident :
      -deriv riemannZeta s / riemannZeta s =
        -(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀ +
          (1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)) +
          (1 / 2 : ℂ) * digamma (s / 2) - (1 / 2 : ℂ) * digamma (s₀ / 2) := by
    rw [neg_div, hld_s, hld_s₀]
    ring
  have htri :
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤
        ‖deriv xi s / xi s - deriv xi s₀ / xi s₀‖ + ‖deriv riemannZeta s₀ / riemannZeta s₀‖ +
          (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / s₀‖ + ‖1 / (s₀ - 1)‖) +
          (1 / 2 : ℝ) * ‖digamma (s / 2)‖ + (1 / 2 : ℝ) * ‖digamma (s₀ / 2)‖ := by
    rw [hident]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have hA : ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀‖ ≤
        ‖deriv xi s / xi s - deriv xi s₀ / xi s₀‖ + ‖deriv riemannZeta s₀ / riemannZeta s₀‖ := by
      rw [← norm_neg (deriv xi s / xi s - deriv xi s₀ / xi s₀)]
      exact norm_sub_le _ _
    have hB : ‖1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)‖ ≤
        ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / s₀‖ + ‖1 / (s₀ - 1)‖ := by
      have hB1 : ‖1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)‖ ≤
          ‖1 / s + 1 / (s - 1) - 1 / s₀‖ + ‖1 / (s₀ - 1)‖ := norm_sub_le _ _
      have hB2 : ‖1 / s + 1 / (s - 1) - 1 / s₀‖ ≤ ‖1 / s + 1 / (s - 1)‖ + ‖1 / s₀‖ := norm_sub_le _ _
      have hB3 : ‖1 / s + 1 / (s - 1)‖ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      linarith
    have hC1 : ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀ +
          (1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)) +
          (1 / 2 : ℂ) * digamma (s / 2) - (1 / 2 : ℂ) * digamma (s₀ / 2)‖ ≤
        ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀ +
          (1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)) +
          (1 / 2 : ℂ) * digamma (s / 2)‖ + ‖(1 / 2 : ℂ) * digamma (s₀ / 2)‖ := norm_sub_le _ _
    have hC2 : ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀ +
          (1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)) +
          (1 / 2 : ℂ) * digamma (s / 2)‖ ≤
        ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀ +
          (1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1))‖ + ‖(1 / 2 : ℂ) * digamma (s / 2)‖ :=
      norm_add_le _ _
    have hC3 : ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀ +
          (1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1))‖ ≤
        ‖-(deriv xi s / xi s - deriv xi s₀ / xi s₀) - deriv riemannZeta s₀ / riemannZeta s₀‖ +
          ‖1 / s + 1 / (s - 1) - 1 / s₀ - 1 / (s₀ - 1)‖ := norm_add_le _ _
    have hD1 : ‖(1 / 2 : ℂ) * digamma (s / 2)‖ = (1 / 2 : ℝ) * ‖digamma (s / 2)‖ := by
      rw [norm_mul, h12]
    have hD2 : ‖(1 / 2 : ℂ) * digamma (s₀ / 2)‖ = (1 / 2 : ℝ) * ‖digamma (s₀ / 2)‖ := by
      rw [norm_mul, h12]
    linarith
  have hlog_t_ge : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log zero_lt_two (by linarith [abs_nonneg t])
  have h1_le_log : 1 ≤ Real.log (|t| + 2) / Real.log 2 := (one_le_div hlog2_pos).mpr hlog_t_ge
  have h1_le_invδ : 1 ≤ 1 / δ := (one_le_div hδ_pos).mpr hδ_le1
  have hrest_le : ‖deriv riemannZeta s₀ / riemannZeta s₀‖ +
      (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / s₀‖ + ‖1 / (s₀ - 1)‖) +
      (1 / 2 : ℝ) * ‖digamma (s / 2)‖ + (1 / 2 : ℝ) * ‖digamma (s₀ / 2)‖ ≤
        Real.log (|t| + 2) + (6 + C_dig + Real.pi) := by
    have hs' : s = (σ : ℂ) + (t : ℂ) * I := rfl
    rw [← hs'] at hdig_s
    linarith [hL_s₀, h1s, h1s1, h1s₀, h1s₀1, hdig_s, hdig_s₀]
  have hrest_scaled : Real.log (|t| + 2) + (6 + C_dig + Real.pi) ≤
      (1 + (6 + C_dig + Real.pi) / Real.log 2) * (1 / δ) * Real.log (|t| + 2) := by
    have hconst_nn : 0 ≤ 6 + C_dig + Real.pi := by positivity
    have hconst_le : 6 + C_dig + Real.pi ≤ ((6 + C_dig + Real.pi) / Real.log 2) * Real.log (|t| + 2) := by
      calc
        6 + C_dig + Real.pi = (6 + C_dig + Real.pi) * 1 := (mul_one _).symm
        _ ≤ (6 + C_dig + Real.pi) * (Real.log (|t| + 2) / Real.log 2) :=
            mul_le_mul_of_nonneg_left h1_le_log hconst_nn
        _ = ((6 + C_dig + Real.pi) / Real.log 2) * Real.log (|t| + 2) := by ring
    have hlog_nn : 0 ≤ Real.log (|t| + 2) := by linarith
    have hcomb : Real.log (|t| + 2) + (6 + C_dig + Real.pi) ≤
        (1 + (6 + C_dig + Real.pi) / Real.log 2) * Real.log (|t| + 2) := by linarith
    calc
      Real.log (|t| + 2) + (6 + C_dig + Real.pi)
          ≤ ((1 + (6 + C_dig + Real.pi) / Real.log 2) * Real.log (|t| + 2)) * 1 := by linarith
      _ ≤ ((1 + (6 + C_dig + Real.pi) / Real.log 2) * Real.log (|t| + 2)) * (1 / δ) :=
          mul_le_mul_of_nonneg_left h1_le_invδ (by positivity)
      _ = (1 + (6 + C_dig + Real.pi) / Real.log 2) * (1 / δ) * Real.log (|t| + 2) := by ring
  have htri' :
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤
        ‖deriv xi s / xi s - deriv xi s₀ / xi s₀‖ +
          (‖deriv riemannZeta s₀ / riemannZeta s₀‖ +
            (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / s₀‖ + ‖1 / (s₀ - 1)‖) +
            (1 / 2 : ℝ) * ‖digamma (s / 2)‖ + (1 / 2 : ℝ) * ‖digamma (s₀ / 2)‖) := by
    linarith [htri]
  calc
    ‖-deriv riemannZeta s / riemannZeta s‖
        ≤ C_diff * (1 / δ) * Real.log (|t| + 2) +
            (1 + (6 + C_dig + Real.pi) / Real.log 2) * (1 / δ) * Real.log (|t| + 2) :=
        htri'.trans (add_le_add hξ_diff (hrest_le.trans hrest_scaled))
    _ ≤ C * (1 / δ) * Real.log (|t| + 2) := by
        have hlog_nn : 0 ≤ Real.log (|t| + 2) := by linarith
        have hnn : 0 ≤ (1 / δ) * Real.log (|t| + 2) :=
          mul_nonneg (one_div_nonneg.mpr hδ_pos.le) hlog_nn
        have hC_ge : C_diff + (1 + (6 + C_dig + Real.pi) / Real.log 2) ≤ C := by
          dsimp [C]; linarith
        calc
          C_diff * (1 / δ) * Real.log (|t| + 2) +
              (1 + (6 + C_dig + Real.pi) / Real.log 2) * (1 / δ) * Real.log (|t| + 2)
              = (C_diff + (1 + (6 + C_dig + Real.pi) / Real.log 2)) *
                  ((1 / δ) * Real.log (|t| + 2)) := by ring
          _ ≤ C * ((1 / δ) * Real.log (|t| + 2)) :=
              mul_le_mul_of_nonneg_right hC_ge hnn
          _ = C * (1 / δ) * Real.log (|t| + 2) := by ring

private lemma tan_eq_exp_div (z : ℂ) (hp1 : Complex.exp (2 * I * z) + 1 ≠ 0) :
    Complex.tan z = (Complex.exp (2 * I * z) - 1) / (I * (Complex.exp (2 * I * z) + 1)) := by
  rw [Complex.tan_eq_sin_div_cos, Complex.sin, Complex.cos]
  have he_ne : Complex.exp (z * I) ≠ 0 := Complex.exp_ne_zero _
  have hee : Complex.exp (z * I) * Complex.exp (z * I) = Complex.exp (2 * I * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hinv : Complex.exp (-z * I) = (Complex.exp (z * I))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  rw [hinv]
  generalize he : Complex.exp (z * I) = e at he_ne hee
  have hp1' : e * e + 1 ≠ 0 := by rw [hee]; exact hp1
  rw [← hee]
  field_simp [he_ne, Complex.I_ne_zero, hp1']
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma norm_tan_neg_quarter_pi_add_I_eq_one (t : ℝ) :
    ‖Complex.tan (Real.pi * ((-1 / 2 : ℂ) + (t : ℂ) * I) / 2)‖ = 1 := by
  let w : ℂ := Real.pi * ((-1 / 2 : ℂ) + (t : ℂ) * I) / 2
  let r : ℝ := Real.exp (-Real.pi * t)
  have hr_pos : 0 < r := Real.exp_pos _
  have h2iw : 2 * I * w = ((-(Real.pi * t) : ℝ) : ℂ) + ((-(Real.pi / 2) : ℝ) : ℂ) * I := by
    dsimp [w]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hexp_2iw : Complex.exp (2 * I * w) = -((r : ℂ) * I) := by
    rw [h2iw, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
    dsimp [r]
    push_cast
    ring
  have hp1 : Complex.exp (2 * I * w) + 1 ≠ 0 := by
    rw [hexp_2iw]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have htan_eq := tan_eq_exp_div w hp1
  change ‖Complex.tan w‖ = 1
  rw [htan_eq, norm_div, norm_mul, Complex.norm_I, one_mul, hexp_2iw]
  have hnum_sq : ‖-((r : ℂ) * I) - 1‖ ^ 2 = 1 + r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hden_sq : ‖-((r : ℂ) * I) + 1‖ ^ 2 = 1 + r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hnorm_eq : ‖-((r : ℂ) * I) - 1‖ = ‖-((r : ℂ) * I) + 1‖ := by
    have hsq : ‖-((r : ℂ) * I) - 1‖ ^ 2 = ‖-((r : ℂ) * I) + 1‖ ^ 2 := by
      rw [hnum_sq, hden_sq]
    nlinarith [norm_nonneg (-((r : ℂ) * I) - 1), norm_nonneg (-((r : ℂ) * I) + 1)]
  have hden_pos : 0 < ‖-((r : ℂ) * I) + 1‖ := by
    refine norm_pos_iff.mpr fun h ↦ ?_
    have hre := congrArg Complex.re h
    simp at hre
  rw [hnorm_eq, div_self hden_pos.ne']

private noncomputable def negHalfDigammaConst : ℝ :=
  Real.log (1 + (max |(-1 / 2 : ℝ)| |(-1 / 2 : ℝ)|) ^ 2) / 2 + Real.pi +
    (1 / 2 + (1 + 8 * ((max |(-1 / 2 : ℝ)| |(-1 / 2 : ℝ)|) ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12)

private lemma negHalfDigammaConst_nonneg : 0 ≤ negHalfDigammaConst := by
  dsimp [negHalfDigammaConst]
  have hlog : 0 ≤ Real.log (1 + (max |(-1 / 2 : ℝ)| |(-1 / 2 : ℝ)|) ^ 2) :=
    Real.log_nonneg (by linarith [sq_nonneg (max |(-1 / 2 : ℝ)| |(-1 / 2 : ℝ)|)])
  exact add_nonneg (add_nonneg (div_nonneg hlog (by norm_num)) Real.pi_pos.le) (by positivity)

private lemma norm_digamma_neg_half_strip_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.digamma ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log |t| + negHalfDigammaConst := by
  rw [← digamma_eq_complex_digamma]
  have h := norm_digamma_strip_le (σ₁ := -1 / 2) (σ₂ := -1 / 2) (σ := -1 / 2) ⟨le_rfl, le_rfl⟩ ht
  have hcast : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by norm_num
  rw [hcast] at h
  refine h.trans_eq ?_
  dsimp [negHalfDigammaConst]
  ring

private lemma norm_LSeries_vonMangoldt_re_three_halves_le {z : ℂ} (hz : z.re = 3 / 2) :
    ‖LSeries (fun n ↦ (Λ n : ℂ)) z‖ ≤ 16 := by
  have hz1 : 1 < z.re := by linarith
  have hsumm : LSeriesSummable (fun n ↦ (Λ n : ℂ)) z := LSeriesSummable_vonMangoldt_iff.mpr hz1
  have h1 : ‖LSeries (fun n ↦ (Λ n : ℂ)) z‖ ≤ ∑' n : ℕ, ‖LSeries.term (fun k ↦ (Λ k : ℂ)) z n‖ :=
    norm_tsum_le_tsum_norm hsumm.norm
  have htriv_lam : (fun k : ℕ ↦ (1 : DirichletCharacter ℂ 1) k * (Λ k : ℂ)) = fun k ↦ (Λ k : ℂ) := by
    ext k
    simp [Subsingleton.elim ((k : ZMod 1)) 1]
  have htriv_norm : ∀ n : ℕ,
      ‖LSeries.term (fun k ↦ (Λ k : ℂ)) z n‖ =
        ‖LSeries.term (fun k : ℕ ↦ (Λ k : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
        norm_div, norm_div, Complex.norm_natCast_cpow_of_pos hn_pos,
        Complex.norm_natCast_cpow_of_pos hn_pos]
      simp [hz]
  have h2 := tsum_norm_LSeries_term_twist_le (1 : DirichletCharacter ℂ 1) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [htriv_lam] at h2
  have h2' : ∑' n : ℕ, ‖LSeries.term (fun k : ℕ ↦ (Λ k : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ ≤ 16 :=
    h2.trans_eq (by norm_num)
  refine h1.trans ?_
  rw [tsum_congr htriv_norm]
  exact h2'

/-- Vertical line bound on `Re s = -1 / 2`: for every `t : ℝ`, `riemannZeta (-1/2 + t * I) ≠ 0`
and `‖-deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖ ≤ C * log (|t| + 2)`. -/
theorem norm_neg_logDeriv_zeta_neg_half_le :
    ∃ C > 0, ∀ t : ℝ,
      riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 ∧
        ‖-deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) /
            riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
          C * Real.log (|t| + 2) := by
  have hne_all : ∀ t : ℝ, riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t hz
    let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
    have hs_re : s.re = -1 / 2 := by simp [s]
    have hs_m : ∀ m : ℕ, s ≠ -2 * (m : ℂ) := fun m h ↦ by
      have hre := congrArg Complex.re h
      have hmr : (-2 * (m : ℂ)).re = -2 * (m : ℝ) := by simp
      rw [hs_re, hmr] at hre
      have : (2 : ℝ) * (m : ℝ) = 1 / 2 := by linarith
      have hm1 : (4 : ℤ) * (m : ℤ) = 1 := by
        exact_mod_cast (by linarith : (4 : ℝ) * (m : ℝ) = 1)
      omega
    have hs1 : s ≠ 1 := fun h ↦ by
      have hre := congrArg Complex.re h
      simp [hs_re] at hre
      linarith
    have hxi0 : xi s = 0 := by
      rw [xi_eq_formula hs_m hs1]
      change _ * riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) = 0
      rw [hz, mul_zero]
    exact xi_ne_zero_of_re_nonpos (by linarith : s.re ≤ 0) hxi0
  have hζ_an : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro w hw
    exact (differentiableAt_riemannZeta hw).differentiableWithinAt
  let φ : ℝ → ℝ := fun t ↦
    ‖-deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) / riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
  have hφ_cont : Continuous φ := by
    refine Continuous.norm ?_
    have hder_an : AnalyticOnNhd ℂ (deriv riemannZeta) ({(1 : ℂ)}ᶜ) := hζ_an.deriv
    have hline_mem : ∀ t : ℝ, (-1 / 2 : ℂ) + (t : ℂ) * I ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := fun t h ↦ by
      have hre := congrArg Complex.re (Set.mem_singleton_iff.mp h)
      simp at hre
      linarith
    have hcont_num : Continuous fun t : ℝ ↦ -deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hline : Continuous fun u : ℝ ↦ (-1 / 2 : ℂ) + (u : ℂ) * I :=
        continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
      exact ContinuousAt.comp (f := fun u : ℝ ↦ (-1 / 2 : ℂ) + (u : ℂ) * I)
        (g := fun z ↦ -deriv riemannZeta z)
        (hder_an _ (hline_mem t)).continuousAt.neg (hline.continuousAt (x := t))
    have hcont_den : Continuous fun t : ℝ ↦ riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hline : Continuous fun u : ℝ ↦ (-1 / 2 : ℂ) + (u : ℂ) * I :=
        continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
      exact ContinuousAt.comp (f := fun u : ℝ ↦ (-1 / 2 : ℂ) + (u : ℂ) * I)
        (g := riemannZeta) (hζ_an _ (hline_mem t)).continuousAt (hline.continuousAt (x := t))
    exact hcont_num.div hcont_den hne_all
  obtain ⟨t₀, _, ht₀_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-2 : ℝ) ≤ 2)) hφ_cont.continuousOn
  let M₀ : ℝ := max (φ t₀) 1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let C_dig : ℝ := negHalfDigammaConst
  let C_tail : ℝ := 16 + |Real.log (2 * Real.pi)| + C_dig + Real.pi / 2
  let C : ℝ := max (M₀ / Real.log 2) (1 + C_tail / Real.log 2)
  have hCdig_nn : 0 ≤ C_dig := negHalfDigammaConst_nonneg
  have hCtail_nn : 0 ≤ C_tail := by dsimp [C_tail]; positivity
  refine ⟨C, by positivity, fun t ↦ ⟨hne_all t, ?_⟩⟩
  have hlog_ge : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log zero_lt_two (by linarith [abs_nonneg t])
  by_cases ht2 : |t| ≤ 2
  · have hmem : t ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp ht2
    have hle : φ t ≤ M₀ := (ht₀_max hmem).trans (le_max_left _ _)
    calc
      φ t ≤ M₀ := hle
      _ = (M₀ / Real.log 2) * Real.log 2 := by field_simp [hlog2_pos.ne']
      _ ≤ C * Real.log (|t| + 2) := mul_le_mul (le_max_left _ _) hlog_ge hlog2_pos.le (by positivity)
  · have ht_ge2 : 2 ≤ |t| := le_of_not_ge ht2
    let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
    have hs_int : ∀ n : ℤ, s ≠ (n : ℂ) := fun n h ↦ by
      have hre := congrArg Complex.re h
      have hsn : s.re = -1 / 2 := by simp [s]
      have hnre : ((n : ℂ)).re = (n : ℝ) := by simp
      rw [hsn, hnre] at hre
      have : (2 : ℤ) * n = -1 := by exact_mod_cast (by linarith : (2 : ℝ) * (n : ℝ) = -1)
      omega
    have hfe := logDeriv_riemannZeta_one_sub hs_int (hne_all t)
    have h1ms_re_eq : (1 - s).re = 3 / 2 := by simp [s]; norm_num
    have h1ms_re : 1 < (1 - s).re := by linarith
    have hL_le : ‖logDeriv riemannZeta (1 - s)‖ ≤ 16 := by
      have heq := LSeries_vonMangoldt_eq h1ms_re
      have hneg : logDeriv riemannZeta (1 - s) = -LSeries (fun n ↦ (Λ n : ℂ)) (1 - s) := by
        rw [logDeriv_apply, heq, neg_div, neg_neg]
      rw [hneg, norm_neg]
      exact norm_LSeries_vonMangoldt_re_three_halves_le h1ms_re_eq
    have hdig_le : ‖Complex.digamma s‖ ≤ Real.log |t| + C_dig :=
      norm_digamma_neg_half_strip_le ht_ge2
    have htan_le : ‖(Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)‖ = Real.pi / 2 := by
      rw [norm_mul, norm_tan_neg_quarter_pi_add_I_eq_one t, mul_one,
        show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlog2pi : ‖(Real.log (2 * Real.pi) : ℂ)‖ = |Real.log (2 * Real.pi)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hld_norm : ‖logDeriv riemannZeta s‖ ≤ Real.log (|t| + 2) + C_tail := by
      have hlog_t_le : Real.log |t| ≤ Real.log (|t| + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlog_pi_eq : Complex.log (2 * (Real.pi : ℂ)) = (Real.log (2 * Real.pi) : ℂ) := by
        rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.ofReal_log (by positivity)]
      have htri : ‖logDeriv riemannZeta s‖ ≤
          ‖-logDeriv riemannZeta (1 - s)‖ + ‖(Real.log (2 * Real.pi) : ℂ)‖ +
            ‖Complex.digamma s‖ + ‖(Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)‖ := by
        rw [hfe, hlog_pi_eq]
        have h1 : ‖-logDeriv riemannZeta (1 - s) + (Real.log (2 * Real.pi) : ℂ) - Complex.digamma s +
            Real.pi / 2 * Complex.tan (Real.pi * s / 2)‖ ≤
            ‖-logDeriv riemannZeta (1 - s) + (Real.log (2 * Real.pi) : ℂ) - Complex.digamma s‖ +
              ‖Real.pi / 2 * Complex.tan (Real.pi * s / 2)‖ := norm_add_le _ _
        have h2 : ‖-logDeriv riemannZeta (1 - s) + (Real.log (2 * Real.pi) : ℂ) - Complex.digamma s‖ ≤
            ‖-logDeriv riemannZeta (1 - s) + (Real.log (2 * Real.pi) : ℂ)‖ + ‖Complex.digamma s‖ :=
          norm_sub_le _ _
        have h3 : ‖-logDeriv riemannZeta (1 - s) + (Real.log (2 * Real.pi) : ℂ)‖ ≤
            ‖-logDeriv riemannZeta (1 - s)‖ + ‖(Real.log (2 * Real.pi) : ℂ)‖ := norm_add_le _ _
        linarith
      rw [norm_neg] at htri
      have hnorm_2pi : ‖(Real.log (2 * Real.pi) : ℂ)‖ = |Real.log (2 * Real.pi)| := hlog2pi
      rw [hnorm_2pi, htan_le] at htri
      dsimp [C_tail]
      linarith
    have hφ_eq : φ t = ‖logDeriv riemannZeta s‖ := by
      dsimp [φ, s]
      rw [logDeriv_apply, show -deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) =
          -(deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)) by ring, norm_neg]
    have h1_le_log : 1 ≤ Real.log (|t| + 2) / Real.log 2 := (one_le_div hlog2_pos).mpr hlog_ge
    have htail_le : C_tail ≤ (C_tail / Real.log 2) * Real.log (|t| + 2) := by
      calc
        C_tail = C_tail * 1 := (mul_one _).symm
        _ ≤ C_tail * (Real.log (|t| + 2) / Real.log 2) := mul_le_mul_of_nonneg_left h1_le_log hCtail_nn
        _ = (C_tail / Real.log 2) * Real.log (|t| + 2) := by ring
    have hC_ge : 1 + C_tail / Real.log 2 ≤ C := le_max_right _ _
    change φ t ≤ C * Real.log (|t| + 2)
    rw [hφ_eq]
    calc
      ‖logDeriv riemannZeta s‖ ≤ Real.log (|t| + 2) + C_tail := hld_norm
      _ ≤ (1 + C_tail / Real.log 2) * Real.log (|t| + 2) := by linarith
      _ ≤ C * Real.log (|t| + 2) := mul_le_mul_of_nonneg_right hC_ge (by linarith)

/-! ### Section 3: Rectangular Cauchy Contour Shift -/

/-- The normalized Cauchy integral of the kernel around an enclosing rectangle is one. -/
theorem contour_rect_inv_sub_eq_one {p z w : ℂ}
    (hzre : z.re < p.re) (hpre : p.re < w.re) (hzim : z.im < p.im) (hpim : p.im < w.im) :
    (1 / (2 * Real.pi * I)) *
        ((∫ x : ℝ in z.re..w.re, ((x : ℂ) + (z.im : ℂ) * I - p)⁻¹) -
          (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (w.im : ℂ) * I - p)⁻¹) +
          I * (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * I - p)⁻¹) -
          I * (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * I - p)⁻¹)) = 1 :=
  rectangle_cauchyKernel_eq_one hzre hpre hzim hpim

private lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  have hdiff : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun w hw ↦
    (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_compl_singleton s hs

private noncomputable def explicitIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s)

private noncomputable def explicitPoleSum (x : ℝ) (Z : Finset ℂ) (s : ℂ) : ℂ :=
  (x : ℂ) * (s - 1)⁻¹ + (-deriv riemannZeta 0 / riemannZeta 0) * s⁻¹ -
    ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * (s - ρ)⁻¹

private noncomputable def explicitHolomorphicRaw (x : ℝ) (Z : Finset ℂ) (s : ℂ) : ℂ :=
  explicitIntegrand x s - explicitPoleSum x Z s

private noncomputable def explicitHolomorphic (x : ℝ) (Z : Finset ℂ) (s : ℂ) : ℂ :=
  if s ∈ insert (1 : ℂ) (insert (0 : ℂ) Z) then
    Filter.limUnder (𝓝[≠] s) (explicitHolomorphicRaw x Z)
  else explicitHolomorphicRaw x Z s

private lemma tendsto_explicitHolomorphicRaw_one {x : ℝ} {Z : Finset ℂ}
    (hx : 2 ≤ x) (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1) :
    ∃ L : ℂ, Tendsto (explicitHolomorphicRaw x Z) (𝓝[≠] 1) (𝓝 L) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  let φ : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / s
  have hφ_diff : DifferentiableAt ℂ φ 1 := by
    have hpow : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 1 :=
      differentiableAt_id.const_cpow (Or.inl hx_ne)
    exact hpow.div differentiableAt_id one_ne_zero
  have hφ_one : φ 1 = (x : ℂ) := by simp [φ]
  have hld_tend : Tendsto (fun s : ℂ ↦ -(logDeriv riemannZeta s + (s - 1)⁻¹)) (𝓝[≠] 1)
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) :=
    tendsto_logDeriv_riemannZeta_add_inv.neg
  have hφ_tend : Tendsto φ (𝓝[≠] 1) (𝓝 (φ 1)) :=
    hφ_diff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope_tend : Tendsto (slope φ 1) (𝓝[≠] 1) (𝓝 (deriv φ 1)) :=
    hasDerivAt_iff_tendsto_slope.mp hφ_diff.hasDerivAt
  have hmain_tend :
      Tendsto (fun s : ℂ ↦ explicitIntegrand x s - (x : ℂ) * (s - 1)⁻¹) (𝓝[≠] 1)
        (𝓝 (-(Real.eulerMascheroniConstant : ℂ) * φ 1 + deriv φ 1)) := by
    refine ((hld_tend.mul hφ_tend).add hslope_tend).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    simp only [explicitIntegrand, φ, logDeriv_apply, slope_def_field, hφ_one]
    field_simp [hs1]
    ring
  let rest : ℂ → ℂ := fun s ↦
    (-deriv riemannZeta 0 / riemannZeta 0) * s⁻¹ -
      ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * (s - ρ)⁻¹
  have hrest_cont : ContinuousAt rest 1 := by
    refine ContinuousAt.sub ?_ ?_
    · exact continuousAt_const.mul (continuousAt_id.inv₀ one_ne_zero)
    · refine tendsto_finsetSum Z fun ρ hρ ↦ ?_
      have hρ1 : (1 : ℂ) - ρ ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
        linarith [(hZ ρ hρ).2]
      exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hρ1)).tendsto
  have hrest_tend : Tendsto rest (𝓝[≠] 1) (𝓝 (rest 1)) :=
    hrest_cont.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨(-(Real.eulerMascheroniConstant : ℂ) * φ 1 + deriv φ 1) - rest 1, ?_⟩
  refine (hmain_tend.sub hrest_tend).congr fun s ↦ ?_
  simp only [explicitHolomorphicRaw, explicitPoleSum, rest]
  ring

private lemma tendsto_explicitHolomorphicRaw_zero {x : ℝ} {Z : Finset ℂ}
    (hx : 2 ≤ x) (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1) :
    ∃ L : ℂ, Tendsto (explicitHolomorphicRaw x Z) (𝓝[≠] 0) (𝓝 L) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hzeta0_ne : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  have hzeta_an0 : AnalyticAt ℂ riemannZeta 0 := analyticAt_riemannZeta_of_ne_one zero_ne_one
  let ψ : ℂ → ℂ := fun s ↦ (-deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s
  have hψ_diff : DifferentiableAt ℂ ψ 0 := by
    have hd : DifferentiableAt ℂ (fun s : ℂ ↦ -deriv riemannZeta s / riemannZeta s) 0 :=
      (hzeta_an0.deriv.differentiableAt.neg).div hzeta_an0.differentiableAt hzeta0_ne
    have hpow : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 0 :=
      differentiableAt_id.const_cpow (Or.inl hx_ne)
    exact hd.mul hpow
  have hψ_zero : ψ 0 = -deriv riemannZeta 0 / riemannZeta 0 := by simp [ψ]
  have hslope_tend : Tendsto (slope ψ 0) (𝓝[≠] 0) (𝓝 (deriv ψ 0)) :=
    hasDerivAt_iff_tendsto_slope.mp hψ_diff.hasDerivAt
  have hmain_tend :
      Tendsto (fun s : ℂ ↦ explicitIntegrand x s - (-deriv riemannZeta 0 / riemannZeta 0) * s⁻¹)
        (𝓝[≠] 0) (𝓝 (deriv ψ 0)) := by
    refine hslope_tend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [explicitIntegrand, ψ, slope_def_field, sub_zero, hψ_zero]
    field_simp [hs]
  let rest : ℂ → ℂ := fun s ↦
    (x : ℂ) * (s - 1)⁻¹ -
      ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * (s - ρ)⁻¹
  have hrest_cont : ContinuousAt rest 0 := by
    refine ContinuousAt.sub ?_ ?_
    · exact continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
        (by norm_num : (0 : ℂ) - 1 ≠ 0))
    · refine tendsto_finsetSum Z fun ρ hρ ↦ ?_
      have hρ0 : (0 : ℂ) - ρ ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.zero_re] at hre
        linarith [(hZ ρ hρ).1]
      exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hρ0)).tendsto
  have hrest_tend : Tendsto rest (𝓝[≠] 0) (𝓝 (rest 0)) :=
    hrest_cont.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨deriv ψ 0 - rest 0, ?_⟩
  refine (hmain_tend.sub hrest_tend).congr fun s ↦ ?_
  simp only [explicitHolomorphicRaw, explicitPoleSum, rest]
  ring

private lemma local_zeta_factorization {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ w in 𝓝 ρ, riemannZeta w = (w - ρ) ^ zeroMultiplicity ρ * g w := by
  have hρ1 : ρ ≠ 1 := fun h ↦ by
    have hre := congrArg Complex.re h
    simp only [Complex.one_re] at hre
    linarith
  have hzeta_an : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta_of_ne_one hρ1
  have hxi_ntop : analyticOrderAt xi ρ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_differentiable_ne_zero differentiable_xi
      (fun h ↦ xi_ne_zero_of_re_nonpos (s := 0) (by simp) (by simpa using congrFun h 0)) ρ
  have hzeta_ntop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    let pref : ℂ → ℂ := fun s ↦
      (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
    have hU : {s : ℂ | (0 : ℝ) < s.re} ∩ {s : ℂ | s.re < (1 : ℝ)} ∈ 𝓝 ρ :=
      (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hre0, hre1⟩
    have hev : xi =ᶠ[𝓝 ρ] (fun s ↦ pref s * riemannZeta s) := by
      refine eventually_of_mem hU fun s hs ↦ ?_
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hs
      have hs_m : ∀ m : ℕ, s ≠ -2 * (m : ℂ) := fun m h ↦ by
        have hre := congrArg Complex.re h
        have hmr : (-2 * (m : ℂ)).re = -2 * (m : ℝ) := by simp
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith [hs.1, hre, hmr, hm0]
      have hs1 : s ≠ 1 := fun h ↦ by
        have hre := congrArg Complex.re h
        simp only [Complex.one_re] at hre
        linarith [hs.2, hre]
      simpa [pref, mul_assoc] using xi_eq_formula hs_m hs1
    have hpref_an : AnalyticAt ℂ pref ρ := analyticAt_xi_prefactor hre0
    have hpref_ord0 : analyticOrderAt pref ρ = 0 :=
      hpref_an.analyticOrderAt_eq_zero.mpr (xi_prefactor_ne_zero hre0 hre1)
    have hord : analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ := by
      rw [analyticOrderAt_congr hev]
      change analyticOrderAt (pref * riemannZeta) ρ = analyticOrderAt riemannZeta ρ
      rw [analyticOrderAt_mul hpref_an hzeta_an, hpref_ord0, zero_add]
    simpa [hord] using hxi_ntop
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hzeta_an.analyticOrderAt_ne_top.mp hzeta_ntop
  refine ⟨g, hg_an, hg_ne, hfg.mono fun w hw ↦ ?_⟩
  simpa only [smul_eq_mul, zeroMultiplicity] using hw

private lemma tendsto_explicitHolomorphicRaw_zero_point {x : ℝ} {Z : Finset ℂ} {ρ : ℂ}
    (hx : 2 ≤ x) (hρ : ρ ∈ Z) (hZ : ∀ ρ' ∈ Z, 0 < ρ'.re ∧ ρ'.re < 1) :
    ∃ L : ℂ, Tendsto (explicitHolomorphicRaw x Z) (𝓝[≠] ρ) (𝓝 L) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hre0 : 0 < ρ.re := (hZ ρ hρ).1
  have hre1 : ρ.re < 1 := (hZ ρ hρ).2
  have hρ0 : ρ ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hre0; linarith
  have hρ1 : ρ ≠ 1 := fun h ↦ by rw [h, Complex.one_re] at hre1; linarith
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := local_zeta_factorization hre0 hre1
  let m : ℕ := zeroMultiplicity ρ
  have hderiv_ev : deriv riemannZeta =ᶠ[𝓝 ρ] deriv (fun w : ℂ ↦ (w - ρ) ^ m * g w) :=
    Filter.EventuallyEq.deriv hfg
  have hg_an_ev : ∀ᶠ w in 𝓝 ρ, AnalyticAt ℂ g w := hg_an.eventually_analyticAt
  have hg_ne_ev : ∀ᶠ w in 𝓝 ρ, g w ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
  have hld_tend :
      Tendsto (fun w : ℂ ↦ -deriv riemannZeta w / riemannZeta w + (m : ℂ) * (w - ρ)⁻¹)
        (𝓝[≠] ρ) (𝓝 (-deriv g ρ / g ρ)) := by
    have hg_ld_tend : Tendsto (fun w : ℂ ↦ -deriv g w / g w) (𝓝[≠] ρ) (𝓝 (-deriv g ρ / g ρ)) :=
      ((hg_an.deriv.continuousAt.neg).div hg_an.continuousAt hg_ne).tendsto.mono_left
        nhdsWithin_le_nhds
    refine hg_ld_tend.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hfg.filter_mono nhdsWithin_le_nhds,
      hderiv_ev.filter_mono nhdsWithin_le_nhds, hg_an_ev.filter_mono nhdsWithin_le_nhds,
      hg_ne_ev.filter_mono nhdsWithin_le_nhds] with w hw_ne hζw hdζw hgw_an hgw_ne
    have hpow_d : HasDerivAt (fun u : ℂ ↦ (u - ρ) ^ m * g u)
        (((m : ℂ) * (w - ρ) ^ (m - 1) * 1) * g w + (w - ρ) ^ m * deriv g w) w :=
      (((hasDerivAt_id w).sub_const ρ).pow m).mul hgw_an.differentiableAt.hasDerivAt
    have hw_sub : w - ρ ≠ 0 := sub_ne_zero.mpr hw_ne
    by_cases hm0 : m = 0
    · have hm0' : zeroMultiplicity ρ = 0 := hm0
      rw [hm0'] at hζw
      rw [hm0] at hpow_d hdζw ⊢
      rw [hζw, hdζw, hpow_d.deriv]
      simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul, zero_add, mul_one]
      field_simp [hgw_ne]
      ring
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      rw [Nat.succ_eq_add_one] at hk
      have hk' : zeroMultiplicity ρ = k + 1 := hk
      rw [hk'] at hζw
      rw [hk] at hpow_d hdζw ⊢
      rw [hζw, hdζw, hpow_d.deriv]
      simp only [Nat.add_sub_cancel, mul_one]
      have hpow_eq : (w - ρ) ^ (k + 1) = (w - ρ) ^ k * (w - ρ) := pow_succ (w - ρ) k
      have hpow_k_ne : (w - ρ) ^ k ≠ 0 := pow_ne_zero k hw_sub
      rw [hpow_eq]
      field_simp [hpow_k_ne, hw_sub, hgw_ne]
      ring
  let φ : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / s
  have hφ_diff : DifferentiableAt ℂ φ ρ :=
    (differentiableAt_id.const_cpow (Or.inl hx_ne)).div differentiableAt_id hρ0
  have hφ_tend : Tendsto φ (𝓝[≠] ρ) (𝓝 (φ ρ)) :=
    hφ_diff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope_tend : Tendsto (slope φ ρ) (𝓝[≠] ρ) (𝓝 (deriv φ ρ)) :=
    hasDerivAt_iff_tendsto_slope.mp hφ_diff.hasDerivAt
  have hmain_tend :
      Tendsto (fun s : ℂ ↦ explicitIntegrand x s + ((m : ℂ) * φ ρ) * (s - ρ)⁻¹)
        (𝓝[≠] ρ) (𝓝 ((-deriv g ρ / g ρ) * φ ρ - (m : ℂ) * deriv φ ρ)) := by
    refine ((hld_tend.mul hφ_tend).sub (tendsto_const_nhds.mul hslope_tend)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
    simp only [explicitIntegrand, φ, slope_def_field]
    field_simp [hsρ]
    ring
  let rest : ℂ → ℂ := fun s ↦
    (x : ℂ) * (s - 1)⁻¹ + (-deriv riemannZeta 0 / riemannZeta 0) * s⁻¹ -
      ∑ ρ' ∈ Z.erase ρ, ((zeroMultiplicity ρ' : ℂ) * ((x : ℂ) ^ ρ' / ρ')) * (s - ρ')⁻¹
  have hrest_cont : ContinuousAt rest ρ := by
    refine ContinuousAt.sub ?_ ?_
    · exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr hρ1))).add (continuousAt_const.mul (continuousAt_id.inv₀ hρ0))
    · refine tendsto_finsetSum (Z.erase ρ) fun ρ' hρ' ↦ ?_
      have hne : ρ - ρ' ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm
      exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hne)).tendsto
  have hrest_tend : Tendsto rest (𝓝[≠] ρ) (𝓝 (rest ρ)) :=
    hrest_cont.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨(-deriv g ρ / g ρ) * φ ρ - (m : ℂ) * deriv φ ρ - rest ρ, ?_⟩
  refine (hmain_tend.sub hrest_tend).congr fun s ↦ ?_
  have hsum_split :
      (∑ ρ' ∈ Z, ((zeroMultiplicity ρ' : ℂ) * ((x : ℂ) ^ ρ' / ρ')) * (s - ρ')⁻¹) =
        ((m : ℂ) * φ ρ) * (s - ρ)⁻¹ +
          ∑ ρ' ∈ Z.erase ρ, ((zeroMultiplicity ρ' : ℂ) * ((x : ℂ) ^ ρ' / ρ')) * (s - ρ')⁻¹ :=
    (Finset.add_sum_erase Z (fun ρ' ↦ ((zeroMultiplicity ρ' : ℂ) * ((x : ℂ) ^ ρ' / ρ')) * (s - ρ')⁻¹)
      hρ).symm
  simp only [explicitHolomorphicRaw, explicitPoleSum, rest, hsum_split]
  ring

private lemma differentiableAt_explicitHolomorphicRaw_of_notMem {x : ℝ} {Z : Finset ℂ}
    (hx : 2 ≤ x) {s : ℂ} (hsP : s ∉ insert (1 : ℂ) (insert (0 : ℂ) Z)) (hζs_ne : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (explicitHolomorphicRaw x Z) s := by
  let P : Finset ℂ := insert (1 : ℂ) (insert (0 : ℂ) Z)
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hs1 : s ≠ 1 := fun h ↦ hsP (by simp [h])
  have hs0 : s ≠ 0 := fun h ↦ hsP (by simp [h])
  have hsZ : ∀ ρ ∈ Z, s - ρ ≠ 0 := fun ρ hρ h ↦
    hsP (by simp [sub_eq_zero.mp h, hρ])
  have hζ_an : AnalyticAt ℂ riemannZeta s := analyticAt_riemannZeta_of_ne_one hs1
  have hd_ld : DifferentiableAt ℂ (fun w : ℂ ↦ -deriv riemannZeta w / riemannZeta w) s :=
    (hζ_an.deriv.differentiableAt.neg).div hζ_an.differentiableAt hζs_ne
  have hd_φ : DifferentiableAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ w / w) s :=
    (differentiableAt_id.const_cpow (Or.inl hx_ne)).div differentiableAt_id hs0
  have hd_int : DifferentiableAt ℂ (explicitIntegrand x) s := hd_ld.mul hd_φ
  have hd_pole : DifferentiableAt ℂ (explicitPoleSum x Z) s := by
    unfold explicitPoleSum
    refine DifferentiableAt.sub ?_ ?_
    · have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ (x : ℂ) * (w - 1)⁻¹) s :=
        (differentiableAt_const (x : ℂ)).mul
          ((differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).inv (sub_ne_zero.mpr hs1))
      have h0 : DifferentiableAt ℂ (fun w : ℂ ↦ (-deriv riemannZeta 0 / riemannZeta 0) * w⁻¹) s :=
        (differentiableAt_const (-deriv riemannZeta 0 / riemannZeta 0)).mul
          (differentiableAt_id.inv hs0)
      exact h1.add h0
    · refine DifferentiableAt.fun_sum fun ρ hρ ↦ ?_
      exact (differentiableAt_const ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ))).mul
        ((differentiableAt_id.sub (differentiableAt_const ρ)).inv (hsZ ρ hρ))
  exact hd_int.sub hd_pole

private lemma differentiableAt_explicitHolomorphic_of_notMem {x : ℝ} {Z : Finset ℂ}
    (hx : 2 ≤ x) {s : ℂ} (hsP : s ∉ insert (1 : ℂ) (insert (0 : ℂ) Z)) (hζs_ne : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (explicitHolomorphic x Z) s := by
  let P : Finset ℂ := insert (1 : ℂ) (insert (0 : ℂ) Z)
  have hopen : IsOpen (P : Set ℂ)ᶜ := P.finite_toSet.isClosed.isOpen_compl
  have hev : explicitHolomorphic x Z =ᶠ[𝓝 s] explicitHolomorphicRaw x Z := by
    refine eventually_of_mem (hopen.mem_nhds hsP) fun w (hw : w ∉ (P : Set ℂ)) ↦ ?_
    have hw' : w ∉ P := hw
    dsimp [explicitHolomorphic]
    split_ifs with h
    · exact False.elim (hw' h)
    · rfl
  exact (differentiableAt_explicitHolomorphicRaw_of_notMem hx hsP hζs_ne).congr_of_eventuallyEq hev

private lemma differentiableAt_explicitHolomorphic_pole {x : ℝ} {Z : Finset ℂ}
    (hx : 2 ≤ x) (hZ_strip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    {p : ℂ} (hpP : p ∈ insert (1 : ℂ) (insert (0 : ℂ) Z)) :
    DifferentiableAt ℂ (explicitHolomorphic x Z) p := by
  let P : Finset ℂ := insert (1 : ℂ) (insert (0 : ℂ) Z)
  have hlim : ∃ L : ℂ, Tendsto (explicitHolomorphicRaw x Z) (𝓝[≠] p) (𝓝 L) := by
    simp only [Finset.mem_insert] at hpP
    rcases hpP with rfl | rfl | hpZ
    · exact tendsto_explicitHolomorphicRaw_one hx hZ_strip
    · exact tendsto_explicitHolomorphicRaw_zero hx hZ_strip
    · exact tendsto_explicitHolomorphicRaw_zero_point hx hpZ hZ_strip
  obtain ⟨L, hL⟩ := hlim
  have havoidP : ∀ᶠ w in 𝓝[≠] p, w ∉ P := by
    have hopen : IsOpen ((P.erase p : Finset ℂ) : Set ℂ)ᶜ :=
      (P.erase p).finite_toSet.isClosed.isOpen_compl
    have hp_not_erase : p ∉ ((P.erase p : Finset ℂ) : Set ℂ) := by simp
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hopen.mem_nhds hp_not_erase)] with w hw_ne hw_erase hwP
    exact hw_erase (Finset.mem_erase.mpr ⟨hw_ne, hwP⟩)
  have hHp_eq : explicitHolomorphic x Z p = L := by
    dsimp [explicitHolomorphic]
    split_ifs
    exact hL.limUnder_eq
  have hH_tend : Tendsto (explicitHolomorphic x Z) (𝓝[≠] p) (𝓝 (explicitHolomorphic x Z p)) := by
    rw [hHp_eq]
    refine hL.congr' ?_
    filter_upwards [havoidP] with w hw
    dsimp [explicitHolomorphic]
    split_ifs with h
    · exact False.elim (hw h)
    · rfl
  have hcont : ContinuousAt (explicitHolomorphic x Z) p := by
    rw [← Function.update_eq_self p (explicitHolomorphic x Z)]
    exact continuousAt_update_same.mpr hH_tend
  have hζ_ne_ev : ∀ᶠ w in 𝓝[≠] p, riemannZeta w ≠ 0 := by
    simp only [Finset.mem_insert] at hpP
    rcases hpP with rfl | rfl | hpZ
    · have hxi1 : xi 1 ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
      have hxi_ev : ∀ᶠ w in 𝓝 (1 : ℂ), xi w ≠ 0 := differentiable_xi.continuous.continuousAt.eventually_ne hxi1
      have hre_ev : ∀ᶠ w in 𝓝 (1 : ℂ), (0 : ℝ) < w.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, hxi_ev.filter_mono nhdsWithin_le_nhds,
        hre_ev.filter_mono nhdsWithin_le_nhds] with w hw1 hxiw hrew hw0
      have hm : ∀ m : ℕ, w ≠ -2 * (m : ℂ) := fun m h ↦ by
        have hre := congrArg Complex.re h
        have hmr : (-2 * (m : ℂ)).re = -2 * (m : ℝ) := by simp
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hxi_eq := xi_eq_formula hm hw1
      rw [hw0, mul_zero] at hxi_eq
      exact hxiw hxi_eq
    · have hzeta0 : riemannZeta 0 ≠ 0 := by
        rw [riemannZeta_zero]
        norm_num
      exact ((analyticAt_riemannZeta_of_ne_one zero_ne_one).continuousAt.eventually_ne
        hzeta0).filter_mono nhdsWithin_le_nhds
    · obtain ⟨g, hg_an, hg_ne, hfg⟩ :=
        local_zeta_factorization (hZ_strip p hpZ).1 (hZ_strip p hpZ).2
      filter_upwards [self_mem_nhdsWithin, hfg.filter_mono nhdsWithin_le_nhds,
        (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds] with w hw_ne hζw hgw
      rw [hζw]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hw_ne)) hgw
  have hdiff_ev : ∀ᶠ w in 𝓝[≠] p, DifferentiableAt ℂ (explicitHolomorphic x Z) w := by
    filter_upwards [havoidP, hζ_ne_ev] with w hwP hwζ
    exact differentiableAt_explicitHolomorphic_of_notMem hx hwP hwζ
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff_ev hcont).differentiableAt

private lemma differentiableOn_explicitHolomorphic {x c T' : ℝ}
    (hx : 2 ≤ x) (_hc : 1 < c) (_hT' : 2 ≤ T')
    (_havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T') :
    DifferentiableOn ℂ (explicitHolomorphic x (nontrivialZerosUpTo T'))
      (Set.Icc (-1 / 2 : ℝ) c ×ℂ Set.Icc (-T') T') := by
  let Z : Finset ℂ := nontrivialZerosUpTo T'
  let P : Finset ℂ := insert (1 : ℂ) (insert (0 : ℂ) Z)
  have hZ_strip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 := fun ρ hρ ↦ by
    have hm := mem_nontrivialZerosUpTo.mp hρ
    exact ⟨hm.2.1, hm.2.2.1⟩
  intro s hsR
  by_cases hsP : s ∈ P
  · exact (differentiableAt_explicitHolomorphic_pole hx hZ_strip hsP).differentiableWithinAt
  · have hζs_ne : riemannZeta s ≠ 0 := by
      intro hz
      have hntriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := fun ⟨n, hn⟩ ↦ by
        have hre := congrArg Complex.re hn
        have hmr : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
        have hsre_lo : -1 / 2 ≤ s.re := hsR.1.1
        linarith
      obtain ⟨hre0, hre1⟩ := nontrivial_zero_re_mem_Ioo hz hntriv
      have him : |s.im| ≤ T' := abs_le.mpr ⟨hsR.2.1, hsR.2.2⟩
      have hsZ : s ∈ Z := mem_nontrivialZerosUpTo.mpr ⟨hz, hre0, hre1, him⟩
      exact hsP (by simp [P, hsZ])
    exact (differentiableAt_explicitHolomorphic_of_notMem hx hsP hζs_ne).differentiableWithinAt

private lemma explicit_contour_shift_identity {x c T' : ℝ}
    (hx : 2 ≤ x) (hc : 1 < c) (hT' : 2 ≤ T')
    (havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T') :
    dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' -
        ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
          ∑ ρ ∈ nontrivialZerosUpTo T', (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) =
      -(1 / (2 * Real.pi * I)) *
        ((∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I)) -
          (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I)) -
          I * (∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I))) := by
  let Z : Finset ℂ := nontrivialZerosUpTo T'
  let P : Finset ℂ := insert (1 : ℂ) (insert (0 : ℂ) Z)
  let H := explicitHolomorphic x Z
  let z₀ : ℂ := (-1 / 2 : ℂ) + (-T' : ℂ) * I
  let w₀ : ℂ := (c : ℂ) + (T' : ℂ) * I
  have hz_re : z₀.re = -1 / 2 := by simp [z₀]
  have hw_re : w₀.re = c := by simp [w₀]
  have hz_im : z₀.im = -T' := by simp [z₀]
  have hw_im : w₀.im = T' := by simp [w₀]
  have hre_le : (-1 / 2 : ℝ) ≤ c := by linarith
  have him_le : -T' ≤ T' := by linarith
  have hrect_eq : Set.uIcc z₀.re w₀.re ×ℂ Set.uIcc z₀.im w₀.im =
      Set.Icc (-1 / 2 : ℝ) c ×ℂ Set.Icc (-T') T' := by
    rw [hz_re, hw_re, hz_im, hw_im, Set.uIcc_of_le hre_le, Set.uIcc_of_le him_le]
  have hH_diff : DifferentiableOn ℂ H (Set.uIcc z₀.re w₀.re ×ℂ Set.uIcc z₀.im w₀.im) := by
    rw [hrect_eq]
    exact differentiableOn_explicitHolomorphic hx hc hT' havoid
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H z₀ w₀ hH_diff
  rw [hz_re, hw_re, hz_im, hw_im] at hcauchy
  simp only [smul_eq_mul] at hcauchy
  have hp_in_rect : ∀ p ∈ P, (-1 / 2 : ℝ) < p.re ∧ p.re < c ∧ -T' < p.im ∧ p.im < T' := by
    intro p hp
    simp only [P, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hpZ
    · exact ⟨by simp; norm_num, hc, by simp; linarith, by simp; linarith⟩
    · exact ⟨by simp; norm_num, by simp; linarith, by simp; linarith, by simp; linarith⟩
    · have hm := mem_nontrivialZerosUpTo.mp hpZ
      have hne_T : |p.im| ≠ T' := havoid p hm.1 hm.2.1 hm.2.2.1
      have hlt_T : |p.im| < T' := lt_of_le_of_ne hm.2.2.2 hne_T
      exact ⟨by linarith [hm.2.1], by linarith [hm.2.2.1], (abs_lt.mp hlt_T).1, (abs_lt.mp hlt_T).2⟩
  have hH_bot : ∀ u : ℝ, H ((u : ℂ) + (-T' : ℂ) * I) = explicitHolomorphicRaw x Z ((u : ℂ) + (-T' : ℂ) * I) := by
    intro u
    have hnot : (u : ℂ) + (-T' : ℂ) * I ∉ P := fun h ↦ by
      have him := (hp_in_rect _ h).2.2.1
      have him' : ((u : ℂ) + (-T' : ℂ) * I).im = -T' := by simp
      linarith [him, him']
    dsimp [H, explicitHolomorphic]; split_ifs with h; exact False.elim (hnot h); rfl
  have hH_top : ∀ u : ℝ, H ((u : ℂ) + (T' : ℂ) * I) = explicitHolomorphicRaw x Z ((u : ℂ) + (T' : ℂ) * I) := by
    intro u
    have hnot : (u : ℂ) + (T' : ℂ) * I ∉ P := fun h ↦ by
      have him := (hp_in_rect _ h).2.2.2
      have him' : ((u : ℂ) + (T' : ℂ) * I).im = T' := by simp
      linarith [him, him']
    dsimp [H, explicitHolomorphic]; split_ifs with h; exact False.elim (hnot h); rfl
  have hH_right : ∀ t : ℝ, H ((c : ℂ) + (t : ℂ) * I) = explicitHolomorphicRaw x Z ((c : ℂ) + (t : ℂ) * I) := by
    intro t
    have hnot : (c : ℂ) + (t : ℂ) * I ∉ P := fun h ↦ by
      have hre := (hp_in_rect _ h).2.1
      have hre' : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
      linarith [hre, hre']
    dsimp [H, explicitHolomorphic]; split_ifs with h; exact False.elim (hnot h); rfl
  have hH_left : ∀ t : ℝ, H ((-1 / 2 : ℂ) + (t : ℂ) * I) = explicitHolomorphicRaw x Z ((-1 / 2 : ℂ) + (t : ℂ) * I) := by
    intro t
    have hnot : (-1 / 2 : ℂ) + (t : ℂ) * I ∉ P := fun h ↦ by
      have hre := (hp_in_rect _ h).1
      have hre_val : ((-1 / 2 : ℂ) + (t : ℂ) * I).re = -1 / 2 := by simp
      linarith [hre, hre_val]
    dsimp [H, explicitHolomorphic]; split_ifs with h; exact False.elim (hnot h); rfl
  have hH_int_bot : IntervalIntegrable (fun u : ℝ ↦ H ((u : ℂ) + (-T' : ℂ) * I)) volume (-1 / 2) c := by
    refine ContinuousOn.intervalIntegrable ?_
    refine hH_diff.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun u hu ↦ ?_
    rw [hrect_eq]
    rw [Set.uIcc_of_le hre_le] at hu
    have hre' : ((u : ℂ) + (-T' : ℂ) * I).re = u := by simp
    have him' : ((u : ℂ) + (-T' : ℂ) * I).im = -T' := by simp
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, hre']; exact hu
    · rw [Set.mem_preimage, him']; exact ⟨le_rfl, by linarith⟩
  have hH_int_top : IntervalIntegrable (fun u : ℝ ↦ H ((u : ℂ) + (T' : ℂ) * I)) volume (-1 / 2) c := by
    refine ContinuousOn.intervalIntegrable ?_
    refine hH_diff.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun u hu ↦ ?_
    rw [hrect_eq]
    rw [Set.uIcc_of_le hre_le] at hu
    have hre' : ((u : ℂ) + (T' : ℂ) * I).re = u := by simp
    have him' : ((u : ℂ) + (T' : ℂ) * I).im = T' := by simp
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, hre']; exact hu
    · rw [Set.mem_preimage, him']; exact ⟨by linarith, le_rfl⟩
  have hH_int_right : IntervalIntegrable (fun t : ℝ ↦ H ((c : ℂ) + (t : ℂ) * I)) volume (-T') T' := by
    refine ContinuousOn.intervalIntegrable ?_
    refine hH_diff.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun t ht ↦ ?_
    rw [hrect_eq]
    rw [Set.uIcc_of_le him_le] at ht
    have hre' : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    have him' : ((c : ℂ) + (t : ℂ) * I).im = t := by simp
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, hre']; exact ⟨hre_le, le_rfl⟩
    · rw [Set.mem_preimage, him']; exact ht
  have hH_int_left : IntervalIntegrable (fun t : ℝ ↦ H ((-1 / 2 : ℂ) + (t : ℂ) * I)) volume (-T') T' := by
    refine ContinuousOn.intervalIntegrable ?_
    refine hH_diff.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun t ht ↦ ?_
    rw [hrect_eq]
    rw [Set.uIcc_of_le him_le] at ht
    have hre' : ((-1 / 2 : ℂ) + (t : ℂ) * I).re = -1 / 2 := by simp
    have him' : ((-1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, hre']; exact ⟨le_rfl, hre_le⟩
    · rw [Set.mem_preimage, him']; exact ht
  have hp_horiz_cont : ∀ (p : ℂ) (y : ℝ), p ∈ P → (y = -T' ∨ y = T') →
      Continuous (fun u : ℝ ↦ ((u : ℂ) + (y : ℂ) * I - p)⁻¹) := by
    intro p y hp hy
    refine Continuous.inv₀ (by fun_prop) fun u h ↦ ?_
    have him_eq : ((u : ℂ) + (y : ℂ) * I - p).im = 0 := by rw [h]; simp
    have him' : y - p.im = 0 := by simpa using him_eq
    rcases hy with rfl | rfl
    · linarith [(hp_in_rect p hp).2.2.1]
    · linarith [(hp_in_rect p hp).2.2.2]
  have hp_vert_cont : ∀ (p : ℂ) (β : ℝ), p ∈ P → (β = -1 / 2 ∨ β = c) →
      Continuous (fun t : ℝ ↦ ((β : ℂ) + (t : ℂ) * I - p)⁻¹) := by
    intro p β hp hβ
    refine Continuous.inv₀ (by fun_prop) fun t h ↦ ?_
    have hre_eq : ((β : ℂ) + (t : ℂ) * I - p).re = 0 := by rw [h]; simp
    have hre' : β - p.re = 0 := by simpa using hre_eq
    rcases hβ with rfl | rfl
    · linarith [(hp_in_rect p hp).1]
    · linarith [(hp_in_rect p hp).2.1]
  have hpole_horiz_cont : ∀ y : ℝ, (y = -T' ∨ y = T') →
      Continuous (fun u : ℝ ↦ explicitPoleSum x Z ((u : ℂ) + (y : ℂ) * I)) := by
    intro y hy
    refine Continuous.sub ?_ ?_
    · exact (continuous_const.mul (hp_horiz_cont 1 y (by simp [P]) hy)).add
        (continuous_const.mul (by simpa using hp_horiz_cont 0 y (by simp [P]) hy))
    · refine continuous_finsetSum Z fun ρ hρ ↦ ?_
      exact continuous_const.mul (hp_horiz_cont ρ y (by simp [P, hρ]) hy)
  have hpole_vert_cont : ∀ β : ℝ, (β = -1 / 2 ∨ β = c) →
      Continuous (fun t : ℝ ↦ explicitPoleSum x Z ((β : ℂ) + (t : ℂ) * I)) := by
    intro β hβ
    refine Continuous.sub ?_ ?_
    · exact (continuous_const.mul (hp_vert_cont 1 β (by simp [P]) hβ)).add
        (continuous_const.mul (by simpa using hp_vert_cont 0 β (by simp [P]) hβ))
    · refine continuous_finsetSum Z fun ρ hρ ↦ ?_
      exact continuous_const.mul (hp_vert_cont ρ β (by simp [P, hρ]) hβ)
  have hraw_bot : (fun u : ℝ ↦ H ((u : ℂ) + (-T' : ℂ) * I)) =
      fun u : ℝ ↦ explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I) -
        explicitPoleSum x Z ((u : ℂ) + (-T' : ℂ) * I) :=
    funext fun u ↦ hH_bot u
  have hraw_top : (fun u : ℝ ↦ H ((u : ℂ) + (T' : ℂ) * I)) =
      fun u : ℝ ↦ explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I) -
        explicitPoleSum x Z ((u : ℂ) + (T' : ℂ) * I) :=
    funext fun u ↦ hH_top u
  have hraw_right : (fun t : ℝ ↦ H ((c : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ ↦ explicitIntegrand x ((c : ℂ) + (t : ℂ) * I) -
        explicitPoleSum x Z ((c : ℂ) + (t : ℂ) * I) :=
    funext fun t ↦ hH_right t
  have hraw_left : (fun t : ℝ ↦ H ((-1 / 2 : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ ↦ explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I) -
        explicitPoleSum x Z ((-1 / 2 : ℂ) + (t : ℂ) * I) :=
    funext fun t ↦ hH_left t
  have hF_bot : IntervalIntegrable (fun u : ℝ ↦ explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I))
      volume (-1 / 2) c := by
    have hsum := hH_int_bot.add ((hpole_horiz_cont (-T') (Or.inl rfl)).intervalIntegrable _ _)
    refine hsum.congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    dsimp only
    rw [hH_bot u, explicitHolomorphicRaw, Complex.ofReal_neg, sub_add_cancel]
  have hF_top : IntervalIntegrable (fun u : ℝ ↦ explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I))
      volume (-1 / 2) c := by
    have hsum := hH_int_top.add ((hpole_horiz_cont T' (Or.inr rfl)).intervalIntegrable _ _)
    refine hsum.congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    dsimp only
    rw [hH_top u, explicitHolomorphicRaw, sub_add_cancel]
  have hF_right : IntervalIntegrable (fun t : ℝ ↦ explicitIntegrand x ((c : ℂ) + (t : ℂ) * I))
      volume (-T') T' := by
    have hsum := hH_int_right.add ((hpole_vert_cont c (Or.inr rfl)).intervalIntegrable _ _)
    refine hsum.congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [hH_right t, explicitHolomorphicRaw, sub_add_cancel]
  have hF_left : IntervalIntegrable (fun t : ℝ ↦ explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I))
      volume (-T') T' := by
    have hsum := hH_int_left.add ((hpole_vert_cont (-1 / 2) (Or.inl rfl)).intervalIntegrable _ _)
    refine hsum.congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    dsimp only
    have hhalf : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by push_cast; ring
    rw [hH_left t, explicitHolomorphicRaw, hhalf, sub_add_cancel]
  have hG_bot := (hpole_horiz_cont (-T') (Or.inl rfl)).intervalIntegrable (μ := volume) (-1 / 2) c
  have hG_top := (hpole_horiz_cont T' (Or.inr rfl)).intervalIntegrable (μ := volume) (-1 / 2) c
  have hG_right := (hpole_vert_cont c (Or.inr rfl)).intervalIntegrable (μ := volume) (-T') T'
  have hG_left := (hpole_vert_cont (-1 / 2) (Or.inl rfl)).intervalIntegrable (μ := volume) (-T') T'
  have hhalf_c : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by push_cast; ring
  rw [hhalf_c, Complex.ofReal_neg] at hcauchy
  rw [Complex.ofReal_neg] at hG_bot
  rw [hhalf_c] at hG_left
  rw [hraw_bot, hraw_top, hraw_right, hraw_left] at hcauchy
  rw [intervalIntegral.integral_sub hF_bot hG_bot,
    intervalIntegral.integral_sub hF_top hG_top,
    intervalIntegral.integral_sub hF_right hG_right,
    intervalIntegral.integral_sub hF_left hG_left] at hcauchy
  have hB_F_eq_G :
      (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I)) -
        (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I)) +
        I * (∫ t : ℝ in (-T')..T', explicitIntegrand x ((c : ℂ) + (t : ℂ) * I)) -
        I * (∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I)) =
      (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitPoleSum x Z ((u : ℂ) + (-T' : ℂ) * I)) -
        (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitPoleSum x Z ((u : ℂ) + (T' : ℂ) * I)) +
        I * (∫ t : ℝ in (-T')..T', explicitPoleSum x Z ((c : ℂ) + (t : ℂ) * I)) -
        I * (∫ t : ℝ in (-T')..T', explicitPoleSum x Z ((-1 / 2 : ℂ) + (t : ℂ) * I)) :=
    sub_eq_zero.mp (by linear_combination hcauchy)
  have hpole_rect_eval : ∀ (p : ℂ) (hp : p ∈ P),
      (1 / (2 * Real.pi * I)) *
        ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - p)⁻¹) -
          (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - p)⁻¹) +
          I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - p)⁻¹) -
          I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - p)⁻¹)) = 1 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp_in_rect p hp
    convert contour_rect_inv_sub_eq_one (p := p) (z := (-1 / 2 : ℂ) + (-T' : ℂ) * I)
      (w := (c : ℂ) + (T' : ℂ) * I) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4) using 3 <;> simp
  have hB_G_val :
      (1 / (2 * Real.pi * I)) *
        ((∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitPoleSum x Z ((u : ℂ) + (-T' : ℂ) * I)) -
          (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitPoleSum x Z ((u : ℂ) + (T' : ℂ) * I)) +
          I * (∫ t : ℝ in (-T')..T', explicitPoleSum x Z ((c : ℂ) + (t : ℂ) * I)) -
          I * (∫ t : ℝ in (-T')..T', explicitPoleSum x Z ((-1 / 2 : ℂ) + (t : ℂ) * I))) =
        (x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
          ∑ ρ ∈ Z, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ) := by
    have hsplit_horiz : ∀ y : ℝ, (y = -T' ∨ y = T') →
        ∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitPoleSum x Z ((u : ℂ) + (y : ℂ) * I) =
          (x : ℂ) * (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (y : ℂ) * I - 1)⁻¹) +
            (-deriv riemannZeta 0 / riemannZeta 0) *
              (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (y : ℂ) * I - 0)⁻¹) -
            ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
              (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (y : ℂ) * I - ρ)⁻¹) := by
      intro y hy
      have hi1 : IntervalIntegrable
          (fun u : ℝ ↦ (x : ℂ) * ((u : ℂ) + (y : ℂ) * I - 1)⁻¹) volume (-1 / 2) c :=
        (continuous_const.mul (hp_horiz_cont 1 y (by simp [P]) hy)).intervalIntegrable _ _
      have hi0 : IntervalIntegrable
          (fun u : ℝ ↦ (-deriv riemannZeta 0 / riemannZeta 0) * ((u : ℂ) + (y : ℂ) * I)⁻¹)
          volume (-1 / 2) c :=
        (continuous_const.mul (by simpa using hp_horiz_cont 0 y (by simp [P]) hy)).intervalIntegrable _ _
      have hiZ : ∀ ρ ∈ Z, IntervalIntegrable
          (fun u : ℝ ↦ ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * ((u : ℂ) + (y : ℂ) * I - ρ)⁻¹)
          volume (-1 / 2) c := fun ρ hρ ↦
        (continuous_const.mul (hp_horiz_cont ρ y (by simp [P, hρ]) hy)).intervalIntegrable _ _
      have hiZ_sum : IntervalIntegrable
          (fun u : ℝ ↦ ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
            ((u : ℂ) + (y : ℂ) * I - ρ)⁻¹) volume (-1 / 2) c := by
        convert IntervalIntegrable.sum Z hiZ using 1
        ext u
        simp only [Finset.sum_apply]
      simp only [explicitPoleSum]
      rw [intervalIntegral.integral_sub (hi1.add hi0) hiZ_sum,
        intervalIntegral.integral_add hi1 hi0,
        intervalIntegral.integral_finsetSum hiZ,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [sub_zero]
      congr 1
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      exact intervalIntegral.integral_const_mul _ _
    have hsplit_vert : ∀ β : ℝ, (β = -1 / 2 ∨ β = c) →
        ∫ t : ℝ in (-T')..T', explicitPoleSum x Z ((β : ℂ) + (t : ℂ) * I) =
          (x : ℂ) * (∫ t : ℝ in (-T')..T', ((β : ℂ) + (t : ℂ) * I - 1)⁻¹) +
            (-deriv riemannZeta 0 / riemannZeta 0) *
              (∫ t : ℝ in (-T')..T', ((β : ℂ) + (t : ℂ) * I - 0)⁻¹) -
            ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
              (∫ t : ℝ in (-T')..T', ((β : ℂ) + (t : ℂ) * I - ρ)⁻¹) := by
      intro β hβ
      have hi1 : IntervalIntegrable
          (fun t : ℝ ↦ (x : ℂ) * ((β : ℂ) + (t : ℂ) * I - 1)⁻¹) volume (-T') T' :=
        (continuous_const.mul (hp_vert_cont 1 β (by simp [P]) hβ)).intervalIntegrable _ _
      have hi0 : IntervalIntegrable
          (fun t : ℝ ↦ (-deriv riemannZeta 0 / riemannZeta 0) * ((β : ℂ) + (t : ℂ) * I)⁻¹)
          volume (-T') T' :=
        (continuous_const.mul (by simpa using hp_vert_cont 0 β (by simp [P]) hβ)).intervalIntegrable _ _
      have hiZ : ∀ ρ ∈ Z, IntervalIntegrable
          (fun t : ℝ ↦ ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * ((β : ℂ) + (t : ℂ) * I - ρ)⁻¹)
          volume (-T') T' := fun ρ hρ ↦
        (continuous_const.mul (hp_vert_cont ρ β (by simp [P, hρ]) hβ)).intervalIntegrable _ _
      have hiZ_sum : IntervalIntegrable
          (fun t : ℝ ↦ ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
            ((β : ℂ) + (t : ℂ) * I - ρ)⁻¹) volume (-T') T' := by
        convert IntervalIntegrable.sum Z hiZ using 1
        ext t
        simp only [Finset.sum_apply]
      simp only [explicitPoleSum]
      rw [intervalIntegral.integral_sub (hi1.add hi0) hiZ_sum,
        intervalIntegral.integral_add hi1 hi0,
        intervalIntegral.integral_finsetSum hiZ,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [sub_zero]
      congr 1
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      exact intervalIntegral.integral_const_mul _ _
    have hb1 := hsplit_horiz (-T') (Or.inl rfl)
    rw [Complex.ofReal_neg] at hb1
    have hl1 := hsplit_vert (-1 / 2) (Or.inl rfl)
    rw [hhalf_c] at hl1
    rw [hb1, hsplit_horiz T' (Or.inr rfl), hsplit_vert c (Or.inr rfl), hl1]
    let K : ℂ := 1 / (2 * Real.pi * I)
    change K * _ = _
    have hrearr :
        K *
          (((x : ℂ) * (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 1)⁻¹) +
              (-deriv riemannZeta 0 / riemannZeta 0) *
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 0)⁻¹) -
              ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - ρ)⁻¹)) -
            ((x : ℂ) * (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 1)⁻¹) +
              (-deriv riemannZeta 0 / riemannZeta 0) *
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 0)⁻¹) -
              ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - ρ)⁻¹)) +
            I * ((x : ℂ) * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) +
              (-deriv riemannZeta 0 / riemannZeta 0) *
                (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 0)⁻¹) -
              ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
                (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - ρ)⁻¹)) -
            I * ((x : ℂ) * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 1)⁻¹) +
              (-deriv riemannZeta 0 / riemannZeta 0) *
                (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 0)⁻¹) -
              ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
                (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - ρ)⁻¹))) =
          (x : ℂ) * (K *
            ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 1)⁻¹) -
              (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 1)⁻¹) +
              I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
              I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 1)⁻¹))) +
            (-deriv riemannZeta 0 / riemannZeta 0) * (K *
              ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 0)⁻¹) -
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 0)⁻¹) +
                I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 0)⁻¹) -
                I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 0)⁻¹))) -
            ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * (K *
              ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - ρ)⁻¹) -
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - ρ)⁻¹) +
                I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - ρ)⁻¹) -
                I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - ρ)⁻¹))) := by
      let S₁ : ℂ := ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
        (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - ρ)⁻¹)
      let S₂ : ℂ := ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
        (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - ρ)⁻¹)
      let S₃ : ℂ := ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
        (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - ρ)⁻¹)
      let S₄ : ℂ := ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) *
        (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - ρ)⁻¹)
      have hS : K * S₁ - K * S₂ + K * (I * S₃) - K * (I * S₄) =
          ∑ ρ ∈ Z, ((zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) * (K *
            ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - ρ)⁻¹) -
              (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - ρ)⁻¹) +
              I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - ρ)⁻¹) -
              I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - ρ)⁻¹))) := by
        dsimp [S₁, S₂, S₃, S₄]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ρ _ ↦ by ring
      have h_id :
          K *
            (((x : ℂ) * (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 1)⁻¹) +
                (-deriv riemannZeta 0 / riemannZeta 0) *
                  (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 0)⁻¹) - S₁) -
              ((x : ℂ) * (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 1)⁻¹) +
                (-deriv riemannZeta 0 / riemannZeta 0) *
                  (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 0)⁻¹) - S₂) +
              I * ((x : ℂ) * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) +
                (-deriv riemannZeta 0 / riemannZeta 0) *
                  (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 0)⁻¹) - S₃) -
              I * ((x : ℂ) * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 1)⁻¹) +
                (-deriv riemannZeta 0 / riemannZeta 0) *
                  (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 0)⁻¹) - S₄)) =
            (x : ℂ) * (K *
              ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 1)⁻¹) -
                (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 1)⁻¹) +
                I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
                I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 1)⁻¹))) +
              (-deriv riemannZeta 0 / riemannZeta 0) * (K *
                ((∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (-T' : ℂ) * I - 0)⁻¹) -
                  (∫ u : ℝ in (-1 / 2 : ℝ)..c, ((u : ℂ) + (T' : ℂ) * I - 0)⁻¹) +
                  I * (∫ t : ℝ in (-T')..T', ((c : ℂ) + (t : ℂ) * I - 0)⁻¹) -
                  I * (∫ t : ℝ in (-T')..T', ((-1 / 2 : ℂ) + (t : ℂ) * I - 0)⁻¹))) -
              (K * S₁ - K * S₂ + K * (I * S₃) - K * (I * S₄)) := by
        ring
      exact h_id.trans (congrArg (_ - ·) hS)
    rw [hrearr, hpole_rect_eval 1 (by simp [P]), hpole_rect_eval 0 (by simp [P]),
      mul_one, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [hpole_rect_eval ρ (by simp [P, hρ]), mul_one]
  have hright_eq_dirichlet :
      (1 / (2 * Real.pi * I)) *
          (I * ∫ t : ℝ in (-T')..T', explicitIntegrand x ((c : ℂ) + (t : ℂ) * I)) =
        dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' := by
    rw [← dirichletContourIntegral_eq_div_two_pi_mul_I]
    congr 2
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have hre_gt1 : 1 < ((c : ℂ) + (t : ℂ) * I).re := by simpa using hc
    have hL : LSeries (fun n : ℕ ↦ (Λ n : ℂ)) ((c : ℂ) + (t : ℂ) * I) =
        -deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I) :=
      LSeries_vonMangoldt_eq hre_gt1
    simp only [explicitIntegrand, ← hL]
    ring
  have hB_F_scaled := congrArg ((1 / (2 * Real.pi * I)) * ·) hB_F_eq_G
  rw [hB_G_val] at hB_F_scaled
  have hsplit_F :
      (1 / (2 * Real.pi * I)) *
          ((∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I)) -
            (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I)) +
            I * (∫ t : ℝ in (-T')..T', explicitIntegrand x ((c : ℂ) + (t : ℂ) * I)) -
            I * (∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I))) =
        dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' +
          (1 / (2 * Real.pi * I)) *
            ((∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I)) -
              (∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I)) -
              I * (∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I))) := by
    rw [← hright_eq_dirichlet]
    ring
  rw [hsplit_F] at hB_F_scaled
  linear_combination hB_F_scaled

/-! ### Section 4: Main Truncated Explicit Formula Theorems -/

private lemma log_abs_add_two_le_three_mul_log {x y : ℝ} (hx : 2 ≤ x) (hy_hi : |y| ≤ x + 1) :
    Real.log (|y| + 2) ≤ 3 * Real.log x := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx3 : |y| + 2 ≤ x ^ 3 := by
    have h4x : x + 3 ≤ 4 * x := by linarith
    have hxx : 4 * x ≤ x ^ 3 := by
      have hsq : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    linarith
  calc
    Real.log (|y| + 2) ≤ Real.log (x ^ 3) := Real.log_le_log (by positivity) hx3
    _ = ((3 : ℕ) : ℝ) * Real.log x := Real.log_pow x 3
    _ = 3 * Real.log x := by norm_num

private lemma norm_explicitHorizontalIntegral_le (c_gap : ℝ) (hcgap : 0 < c_gap) :
    ∃ C > 0, ∀ (x T T' y : ℝ),
      2 ≤ x → 2 ≤ T → T ≤ x → T < T' → T' < T + 1 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        c_gap / Real.log T ≤ abs (|ρ.im| - T')) →
      |y| = T' →
      let c : ℝ := 1 + 1 / Real.log x
      ‖∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (y : ℂ) * I)‖ ≤
        C * (x * (Real.log x) ^ 2 / T) := by
  obtain ⟨C_av, hCav_pos, hav⟩ := norm_neg_logDeriv_zeta_avoiding_le
  let C : ℝ := 12 * Real.exp 1 * C_av * (1 / c_gap + 2)
  refine ⟨C, by positivity, fun x T T' y hx hT2 hTx hT_lt hT_hi hgap hy ↦ ?_⟩
  intro c
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ge1 : (1 : ℝ) ≤ x := by linarith
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT_ge : Real.log 2 ≤ Real.log T := Real.log_le_log zero_lt_two hT2
  have hlogT_le : Real.log T ≤ Real.log x := Real.log_le_log hT_pos hTx
  have hlogT_gt : (1 / 2 : ℝ) < Real.log T := lt_of_lt_of_le hlog2_gt hlogT_ge
  have hlogx_gt : (1 / 2 : ℝ) < Real.log x := lt_of_lt_of_le hlogT_gt hlogT_le
  have hlogT_pos : 0 < Real.log T := by linarith
  have hlogx_pos : 0 < Real.log x := by linarith
  have hinv_logx_le : 1 / Real.log x ≤ 2 := (div_le_iff₀ hlogx_pos).mpr (by linarith)
  have hc_le3 : c ≤ 3 := by dsimp [c]; linarith
  have hc_ge_half : (-1 / 2 : ℝ) ≤ c := by dsimp [c]; have : 0 < 1 / Real.log x := one_div_pos.mpr hlogx_pos; linarith
  have hlen_le : |c - (-1 / 2 : ℝ)| ≤ 4 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hy2 : 2 ≤ |y| := by rw [hy]; linarith
  have hy_hi : |y| ≤ x + 1 := by rw [hy]; linarith
  have hy_log : Real.log (|y| + 2) ≤ 3 * Real.log x := log_abs_add_two_le_three_mul_log hx hy_hi
  let δ : ℝ := min (c_gap / Real.log T) 1
  have hδ_pos : 0 < δ := lt_min (div_pos hcgap hlogT_pos) zero_lt_one
  have hδ_le1 : δ ≤ 1 := min_le_right _ _
  have hinv_δ_le : 1 / δ ≤ (1 / c_gap + 2) * Real.log x := by
    by_cases hmin : c_gap / Real.log T ≤ 1
    · have hδ_eq : δ = c_gap / Real.log T := min_eq_left hmin
      have h1 : 1 / δ = (1 / c_gap) * Real.log T := by
        rw [hδ_eq]
        field_simp [hcgap.ne', hlogT_pos.ne']
      calc
        1 / δ = (1 / c_gap) * Real.log T := h1
        _ ≤ (1 / c_gap) * Real.log x := mul_le_mul_of_nonneg_left hlogT_le (by positivity)
        _ ≤ (1 / c_gap + 2) * Real.log x := by nlinarith [hlogx_pos]
    · have hδ_eq : δ = 1 := min_eq_right (le_of_not_ge hmin)
      calc
        1 / δ = 1 := by rw [hδ_eq, div_one]
        _ ≤ 2 * Real.log x := by linarith
        _ ≤ (1 / c_gap + 2) * Real.log x := by nlinarith [hlogx_pos, one_div_pos.mpr hcgap]
  have hgap_y : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → δ ≤ |y - ρ.im| := by
    intro ρ hρz hre0 hre1
    have h1 : δ ≤ c_gap / Real.log T := min_le_left _ _
    have h2 : c_gap / Real.log T ≤ abs (|ρ.im| - T') := hgap ρ hρz hre0 hre1
    have h3 : abs (|ρ.im| - T') = abs (|ρ.im| - |y|) := by rw [hy]
    have h4 : abs (|ρ.im| - |y|) ≤ |ρ.im - y| := abs_abs_sub_abs_le_abs_sub ρ.im y
    rw [abs_sub_comm ρ.im y] at h4
    exact h1.trans (h2.trans (h3 ▸ h4))
  have hpow_x : x ^ c = x * Real.exp 1 := by
    dsimp [c]
    rw [Real.rpow_add hx_pos, Real.rpow_one]
    congr 1
    rw [Real.rpow_def_of_pos hx_pos, mul_one_div_cancel hlogx_pos.ne']
  have hpt : ∀ u ∈ Set.uIoc (-1 / 2 : ℝ) c,
      ‖explicitIntegrand x ((u : ℂ) + (y : ℂ) * I)‖ ≤
        (3 * Real.exp 1 * C_av * (1 / c_gap + 2)) * (x * (Real.log x) ^ 2 / T) := by
    intro u hu
    rw [Set.uIoc_of_le hc_ge_half] at hu
    have hu_lo : -1 / 2 ≤ u := hu.1.le
    have hu_hi : u ≤ 4 := hu.2.trans (hc_le3.trans (by norm_num))
    have hav_u := (hav u y δ hu_lo hu_hi hy2 hδ_pos hδ_le1 hgap_y).2
    have hld_le : ‖-deriv riemannZeta ((u : ℂ) + (y : ℂ) * I) /
        riemannZeta ((u : ℂ) + (y : ℂ) * I)‖ ≤
        3 * C_av * (1 / c_gap + 2) * (Real.log x) ^ 2 := by
      calc
        ‖-deriv riemannZeta ((u : ℂ) + (y : ℂ) * I) /
            riemannZeta ((u : ℂ) + (y : ℂ) * I)‖
            ≤ C_av * (1 / δ) * Real.log (|y| + 2) := hav_u
        _ ≤ C_av * ((1 / c_gap + 2) * Real.log x) * (3 * Real.log x) := by
              gcongr
              exact Real.log_nonneg (by linarith)
        _ = 3 * C_av * (1 / c_gap + 2) * (Real.log x) ^ 2 := by ring
    have hre_u : ((u : ℂ) + (y : ℂ) * I).re = u := by simp
    have him_y : ((u : ℂ) + (y : ℂ) * I).im = y := by simp
    have hnum_le : ‖(x : ℂ) ^ ((u : ℂ) + (y : ℂ) * I)‖ ≤ x * Real.exp 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, hre_u]
      exact (Real.rpow_le_rpow_of_exponent_le hx_ge1 hu.2).trans hpow_x.le
    have hden_ge : T ≤ ‖(u : ℂ) + (y : ℂ) * I‖ := by
      calc
        T ≤ T' := hT_lt.le
        _ = |y| := hy.symm
        _ = |((u : ℂ) + (y : ℂ) * I).im| := by rw [him_y]
        _ ≤ ‖(u : ℂ) + (y : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hφ_le : ‖(x : ℂ) ^ ((u : ℂ) + (y : ℂ) * I) / ((u : ℂ) + (y : ℂ) * I)‖ ≤
        Real.exp 1 * x / T := by
      rw [norm_div]
      calc
        ‖(x : ℂ) ^ ((u : ℂ) + (y : ℂ) * I)‖ / ‖(u : ℂ) + (y : ℂ) * I‖
            ≤ (x * Real.exp 1) / T := div_le_div₀ (by positivity) hnum_le hT_pos hden_ge
        _ = Real.exp 1 * x / T := by ring
    dsimp [explicitIntegrand]
    rw [norm_mul]
    calc
      ‖-deriv riemannZeta ((u : ℂ) + (y : ℂ) * I) / riemannZeta ((u : ℂ) + (y : ℂ) * I)‖ *
          ‖(x : ℂ) ^ ((u : ℂ) + (y : ℂ) * I) / ((u : ℂ) + (y : ℂ) * I)‖
          ≤ (3 * C_av * (1 / c_gap + 2) * (Real.log x) ^ 2) * (Real.exp 1 * x / T) :=
        mul_le_mul hld_le hφ_le (norm_nonneg _) (by positivity)
      _ = (3 * Real.exp 1 * C_av * (1 / c_gap + 2)) * (x * (Real.log x) ^ 2 / T) := by ring
  calc
    ‖∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (y : ℂ) * I)‖
        ≤ (3 * Real.exp 1 * C_av * (1 / c_gap + 2)) * (x * (Real.log x) ^ 2 / T) *
            |c - (-1 / 2 : ℝ)| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ ≤ (3 * Real.exp 1 * C_av * (1 / c_gap + 2)) * (x * (Real.log x) ^ 2 / T) * 4 := by
          gcongr
    _ = C * (x * (Real.log x) ^ 2 / T) := by dsimp [C]; ring

private lemma norm_explicitVerticalLeftIntegral_le :
    ∃ C > 0, ∀ (x T T' : ℝ),
      2 ≤ x → 2 ≤ T → T ≤ x → T < T' → T' < T + 1 →
      ‖∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        C * (x * (Real.log x) ^ 2 / T) := by
  obtain ⟨C_v, hCv_pos, hneg⟩ := norm_neg_logDeriv_zeta_neg_half_le
  refine ⟨54 * C_v, by positivity, fun x T T' hx hT2 hTx hT_lt hT_hi ↦ ?_⟩
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ge1 : (1 : ℝ) ≤ x := by linarith
  have hT_pos : (0 : ℝ) < T := by linarith
  have hT'_pos : 0 < T' := by linarith
  let M : ℝ := 3 * C_v * Real.log (T' + 2) * x ^ (-1 / 2 : ℝ)
  have hM_nonneg : 0 ≤ M := by
    have hlog_nn : 0 ≤ Real.log (T' + 2) := Real.log_nonneg (by linarith)
    positivity
  let g : ℝ → ℝ := fun t ↦ M * (1 / (1 + |t|))
  have hne_abs : ∀ t : ℝ, 1 + |t| ≠ 0 := fun t ↦ by linarith [abs_nonneg t]
  have hg_cont : Continuous g :=
    continuous_const.mul (continuous_const.div (continuous_const.add continuous_abs) hne_abs)
  have hint_abs : ∫ t : ℝ in (-T')..T', (1 : ℝ) / (1 + |t|) = 2 * Real.log (1 + T') := by
    have hcont0 : Continuous (fun t : ℝ ↦ (1 : ℝ) / (1 + |t|)) :=
      continuous_const.div (continuous_const.add continuous_abs) hne_abs
    have heven : ∀ t : ℝ, (1 : ℝ) / (1 + |-t|) = 1 / (1 + |t|) := fun t ↦ by simp [abs_neg]
    rw [integral_even_real_eq_two_mul hcont0 heven T']
    congr 1
    have hcongr : ∫ t : ℝ in (0 : ℝ)..T', (1 : ℝ) / (1 + |t|) =
        ∫ t : ℝ in (0 : ℝ)..T', (1 : ℝ) / (1 + t) := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le hT'_pos.le] at ht
      rw [abs_of_nonneg ht.1]
    rw [hcongr]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T',
        HasDerivAt (fun u : ℝ ↦ Real.log (1 + u)) ((1 : ℝ) / (1 + t)) t := by
      intro t ht
      rw [Set.uIcc_of_le hT'_pos.le] at ht
      have hne : 1 + t ≠ 0 := by linarith [ht.1]
      have h1 : HasDerivAt (fun u : ℝ ↦ 1 + u) 1 t := by simpa using (hasDerivAt_id t).const_add 1
      simpa [one_div] using h1.log hne
    have hcont_pos : ContinuousOn (fun t : ℝ ↦ (1 : ℝ) / (1 + t)) (Set.uIcc 0 T') := by
      refine ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id) fun t ht ↦ ?_
      change (1 + t : ℝ) ≠ 0
      rw [Set.uIcc_of_le hT'_pos.le] at ht
      linarith [ht.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont_pos.intervalIntegrable]
    simp
  have hpt : ∀ᵐ (t : ℝ) ∂((volume : Measure ℝ).restrict (Set.uIoc (-T') T')),
      ‖explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ g t := by
    refine (ae_restrict_mem measurableSet_uIoc).mono fun t ht ↦ ?_
    rw [Set.uIoc_of_le (by linarith : -T' ≤ T')] at ht
    have ht_abs : |t| ≤ T' := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hlog_t : Real.log (|t| + 2) ≤ Real.log (T' + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hld_le : ‖-deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) /
        riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C_v * Real.log (T' + 2) :=
      (hneg t).2.trans (mul_le_mul_of_nonneg_left hlog_t hCv_pos.le)
    have hre_val : ((-1 / 2 : ℂ) + (t : ℂ) * I).re = -1 / 2 := by simp
    have him_val : ((-1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
    have hnorm_half : (1 / 2 : ℝ) ≤ ‖(-1 / 2 : ℂ) + (t : ℂ) * I‖ := by
      have h := Complex.abs_re_le_norm ((-1 / 2 : ℂ) + (t : ℂ) * I)
      have hhalf_abs : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [hre_val, hhalf_abs] at h
      exact h
    have hnorm_t : |t| ≤ ‖(-1 / 2 : ℂ) + (t : ℂ) * I‖ := by
      have h := Complex.abs_im_le_norm ((-1 / 2 : ℂ) + (t : ℂ) * I)
      rwa [him_val] at h
    have hden_pos : 0 < ‖(-1 / 2 : ℂ) + (t : ℂ) * I‖ := by linarith
    have hden_ge : 1 + |t| ≤ 3 * ‖(-1 / 2 : ℂ) + (t : ℂ) * I‖ := by linarith
    have hinv_le : 1 / ‖(-1 / 2 : ℂ) + (t : ℂ) * I‖ ≤ 3 / (1 + |t|) := by
      rw [div_le_div_iff₀ hden_pos (by positivity)]
      linarith
    have hpow_norm : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ = x ^ (-1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, hre_val]
    have hφ_le : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + (t : ℂ) * I) / ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        x ^ (-1 / 2 : ℝ) * (3 / (1 + |t|)) := by
      rw [norm_div, hpow_norm, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinv_le (Real.rpow_pos_of_pos hx_pos _).le
    dsimp [explicitIntegrand, g, M]
    rw [norm_mul]
    calc
      ‖-deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ *
          ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + (t : ℂ) * I) / ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
          ≤ (C_v * Real.log (T' + 2)) * (x ^ (-1 / 2 : ℝ) * (3 / (1 + |t|))) :=
        mul_le_mul hld_le hφ_le (norm_nonneg _) (mul_nonneg hCv_pos.le (Real.log_nonneg (by linarith)))
      _ = (3 * C_v * Real.log (T' + 2) * x ^ (-1 / 2 : ℝ)) * (1 / (1 + |t|)) := by ring
  have hnorm_le := intervalIntegral.norm_integral_le_abs_of_norm_le hpt (hg_cont.intervalIntegrable _ _)
  have hint_g : ∫ t : ℝ in (-T')..T', g t = M * (2 * Real.log (1 + T')) := by
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, hint_abs]
  have hlog_T' : Real.log (T' + 2) ≤ 3 * Real.log x := by
    have h_abs : |T'| ≤ x + 1 := by rw [abs_of_pos hT'_pos]; linarith
    simpa [abs_of_pos hT'_pos] using log_abs_add_two_le_three_mul_log hx h_abs
  have hlog_1T' : Real.log (1 + T') ≤ 3 * Real.log x :=
    (Real.log_le_log (by linarith) (by linarith)).trans hlog_T'
  have hrpow_le : x ^ (-1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx_ge1 (by norm_num)
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx_ge1
  have h1_le_xT : 1 ≤ x / T := (one_le_div hT_pos).mpr hTx
  have hint_nonneg : 0 ≤ M * (2 * Real.log (1 + T')) :=
    mul_nonneg hM_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
  calc
    ‖∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
        ≤ |∫ t : ℝ in (-T')..T', g t| := hnorm_le
    _ = M * (2 * Real.log (1 + T')) := by rw [hint_g, abs_of_nonneg hint_nonneg]
    _ = 6 * C_v * Real.log (T' + 2) * Real.log (1 + T') * x ^ (-1 / 2 : ℝ) := by dsimp [M]; ring
    _ ≤ 6 * C_v * (3 * Real.log x) * (3 * Real.log x) * 1 := by
          gcongr
          exact Real.log_nonneg (by linarith)
    _ = 54 * C_v * ((Real.log x) ^ 2 * 1) := by ring
    _ ≤ 54 * C_v * ((Real.log x) ^ 2 * (x / T)) := by gcongr
    _ = (54 * C_v) * (x * (Real.log x) ^ 2 / T) := by ring

private lemma sum_zero_tail_T_to_T'_le :
    ∃ C > 0, ∀ (x T T' : ℝ),
      2 ≤ x → 2 ≤ T → T ≤ x → T < T' → T' < T + 1 →
      ‖∑ ρ ∈ nontrivialZerosUpTo T', (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ ≤
        C * (x * (Real.log x) ^ 2 / T) := by
  obtain ⟨C_b, hCb_pos, hband⟩ := sum_zeroMultiplicity_unit_band_le
  refine ⟨2 * C_b, by positivity, fun x T T' hx hT2 hTx hT_lt hT_hi ↦ ?_⟩
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ge1 : (1 : ℝ) ≤ x := by linarith
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx_gt : (1 / 2 : ℝ) < Real.log x := lt_of_lt_of_le hlog2_gt (Real.log_le_log zero_lt_two hx)
  have hlogT_le : Real.log T ≤ Real.log x := Real.log_le_log hT_pos hTx
  have hsub : nontrivialZerosUpTo T ⊆ nontrivialZerosUpTo T' := fun ρ hρ ↦ by
    simp only [mem_nontrivialZerosUpTo] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans hT_lt.le⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hterm : ∀ ρ ∈ nontrivialZerosUpTo T' \ nontrivialZerosUpTo T,
      ‖(zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ ≤ (zeroMultiplicity ρ : ℝ) * (x / T) := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_nontrivialZerosUpTo, mem_nontrivialZerosUpTo] at hρ
    have hρ_im_ge : T ≤ |ρ.im| := by
      by_contra hlt
      push Not at hlt
      exact hρ.2 ⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.1, hlt.le⟩
    have hnorm_rho : T ≤ ‖ρ‖ := hρ_im_ge.trans (Complex.abs_im_le_norm ρ)
    have hrho_pos : 0 < ‖ρ‖ := lt_of_lt_of_le hT_pos hnorm_rho
    have hpow_le : ‖(x : ℂ) ^ ρ‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      calc
        x ^ ρ.re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx_ge1 hρ.1.2.2.1.le
        _ = x := Real.rpow_one x
    have hdiv_le : ‖(x : ℂ) ^ ρ / ρ‖ ≤ x / T := by
      rw [norm_div]
      exact div_le_div₀ hx_pos.le hpow_le hT_pos hnorm_rho
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hdiv_le (Nat.cast_nonneg _)
  have hsub_band : nontrivialZerosUpTo T' \ nontrivialZerosUpTo T ⊆
      (nontrivialZerosUpTo (T + 1)).filter (fun ρ ↦ T ≤ |ρ.im|) := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_nontrivialZerosUpTo, mem_nontrivialZerosUpTo] at hρ
    rw [Finset.mem_filter, mem_nontrivialZerosUpTo]
    refine ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.1, hρ.1.2.2.2.trans hT_hi.le⟩, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hρ.2 ⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.1, hlt.le⟩
  calc
    ‖∑ ρ ∈ nontrivialZerosUpTo T' \ nontrivialZerosUpTo T,
        (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖
        ≤ ∑ ρ ∈ nontrivialZerosUpTo T' \ nontrivialZerosUpTo T,
            ‖(zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ nontrivialZerosUpTo T' \ nontrivialZerosUpTo T,
            (zeroMultiplicity ρ : ℝ) * (x / T) := Finset.sum_le_sum hterm
    _ ≤ ∑ ρ ∈ (nontrivialZerosUpTo (T + 1)).filter (fun ρ ↦ T ≤ |ρ.im|),
            (zeroMultiplicity ρ : ℝ) * (x / T) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_band fun _ _ _ ↦ by positivity
    _ = (∑ ρ ∈ (nontrivialZerosUpTo (T + 1)).filter (fun ρ ↦ T ≤ |ρ.im|),
            (zeroMultiplicity ρ : ℝ)) * (x / T) := (Finset.sum_mul _ _ _).symm
    _ ≤ (C_b * Real.log T) * (x / T) := mul_le_mul_of_nonneg_right (hband T hT2) (by positivity)
    _ ≤ (C_b * Real.log x) * (x / T) := by gcongr
    _ ≤ (C_b * (Real.log x * (2 * Real.log x))) * (x / T) := by
          gcongr
          nlinarith
    _ = (2 * C_b) * (x * (Real.log x) ^ 2 / T) := by ring

private lemma norm_contour_shift_remainder_le (c_gap : ℝ) (hcgap : 0 < c_gap) :
    ∃ C > 0, ∀ (x T T' : ℝ),
      2 ≤ x → 2 ≤ T → T ≤ x → T < T' → T' < T + 1 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        c_gap / Real.log T ≤ abs (|ρ.im| - T')) →
      let c : ℝ := 1 + 1 / Real.log x
      ‖dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' -
          ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
            ∑ ρ ∈ nontrivialZerosUpTo T', (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ))‖ ≤
        C * (x * (Real.log x) ^ 2 / T) := by
  obtain ⟨C_h, hCh_pos, hhoriz⟩ := norm_explicitHorizontalIntegral_le c_gap hcgap
  obtain ⟨C_v, hCv_pos, hvert⟩ := norm_explicitVerticalLeftIntegral_le
  refine ⟨2 * C_h + C_v, by positivity, fun x T T' hx hT2 hTx hT_lt hT_hi hgap ↦ ?_⟩
  intro c
  have hT'_pos : 0 < T' := by linarith
  have hT'2 : 2 ≤ T' := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hc_gt1 : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlogx_pos]
  have havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T' := by
    intro ρ hρz hre0 hre1 heq
    have hle := hgap ρ hρz hre0 hre1
    rw [heq, sub_self, abs_zero] at hle
    have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
    linarith [div_pos hcgap hlogT_pos]
  have hshift := explicit_contour_shift_identity (x := x) (c := c) (T' := T') hx hc_gt1 hT'2 havoid
  have hbot := hhoriz x T T' (-T') hx hT2 hTx hT_lt hT_hi hgap (by simp [abs_of_pos hT'_pos])
  have htop := hhoriz x T T' T' hx hT2 hTx hT_lt hT_hi hgap (by simp [abs_of_pos hT'_pos])
  have hleft := hvert x T T' hx hT2 hTx hT_lt hT_hi
  have hK_le : ‖-(1 / (2 * (Real.pi : ℂ) * I))‖ ≤ 1 := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_neg, norm_div, norm_one, norm_mul, norm_mul, h2,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    exact div_le_one_of_le₀ (by linarith [Real.pi_gt_three]) (by positivity)
  let I_bot : ℂ := ∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (-T' : ℂ) * I)
  let I_top : ℂ := ∫ u : ℝ in (-1 / 2 : ℝ)..c, explicitIntegrand x ((u : ℂ) + (T' : ℂ) * I)
  let I_left : ℂ := ∫ t : ℝ in (-T')..T', explicitIntegrand x ((-1 / 2 : ℂ) + (t : ℂ) * I)
  have hbox : ‖I_bot - I_top - I * I_left‖ ≤ (2 * C_h + C_v) * (x * (Real.log x) ^ 2 / T) := by
    have htri1 : ‖I_bot - I_top - I * I_left‖ ≤ ‖I_bot - I_top‖ + ‖I * I_left‖ :=
      norm_sub_le (I_bot - I_top) (I * I_left)
    have htri2 : ‖I_bot - I_top‖ + ‖I * I_left‖ ≤ (‖I_bot‖ + ‖I_top‖) + ‖I_left‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact add_le_add (norm_sub_le I_bot I_top) le_rfl
    calc
      ‖I_bot - I_top - I * I_left‖ ≤ (‖I_bot‖ + ‖I_top‖) + ‖I_left‖ := htri1.trans htri2
      _ ≤ (C_h * (x * (Real.log x) ^ 2 / T) + C_h * (x * (Real.log x) ^ 2 / T)) +
              C_v * (x * (Real.log x) ^ 2 / T) := add_le_add (add_le_add hbot htop) hleft
      _ = (2 * C_h + C_v) * (x * (Real.log x) ^ 2 / T) := by ring
  rw [hshift, norm_mul]
  change ‖-(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I_bot - I_top - I * I_left‖ ≤
    (2 * C_h + C_v) * (x * (Real.log x) ^ 2 / T)
  calc
    ‖-(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I_bot - I_top - I * I_left‖
        ≤ 1 * ((2 * C_h + C_v) * (x * (Real.log x) ^ 2 / T)) :=
      mul_le_mul hK_le hbox (norm_nonneg _) zero_le_one
    _ = (2 * C_h + C_v) * (x * (Real.log x) ^ 2 / T) := one_mul _

/-- **Truncated Riemann–von Mangoldt explicit formula for `ψ(x)`**:
there exists an absolute constant `C > 0` such that for all `x ≥ 2` and `2 ≤ T ≤ x`,
the difference between `Chebyshev.psi x` and `x + (-deriv riemannZeta 0 / riemannZeta 0) - ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ) * (x ^ ρ / ρ)` is bounded in norm by `C * (x * (Real.log x) ^ 2 / T + Real.log x)`. -/
theorem explicit_formula_psi :
    ∃ C > 0, ∀ (x T : ℝ), 2 ≤ x → 2 ≤ T → T ≤ x →
      ‖(Chebyshev.psi x : ℂ) -
          ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
            ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ))‖ ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨c_gap, hcg_pos, hgood⟩ := exists_good_T_avoiding_zeros
  obtain ⟨C_r, hCr_pos, hrem⟩ := norm_contour_shift_remainder_le c_gap hcg_pos
  obtain ⟨C_t, hCt_pos, htail⟩ := sum_zero_tail_T_to_T'_le
  refine ⟨900 + C_r + C_t, by positivity, fun x T hx hT2 hTx ↦ ?_⟩
  obtain ⟨T', hT_lt, hT_hi, hgap⟩ := hgood T hT2
  have hT'_pos : 0 < T' := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  let c : ℝ := 1 + 1 / Real.log x
  have hperr := perron_truncated_vonMangoldt (x := x) (T := T') hx hT'_pos
  dsimp only at hperr
  have hT_div : x * (Real.log x) ^ 2 / T' ≤ x * (Real.log x) ^ 2 / T :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hT_lt.le
  have hperr_T :
      ‖dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' - (Chebyshev.psi x : ℂ)‖ ≤
        900 * (x * (Real.log x) ^ 2 / T + Real.log x) :=
    hperr.trans (by gcongr)
  have hrem_norm := hrem x T T' hx hT2 hTx hT_lt hT_hi hgap
  dsimp only at hrem_norm
  have htail_T := htail x T T' hx hT2 hTx hT_lt hT_hi
  let A : ℂ := dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' - (Chebyshev.psi x : ℂ)
  let B : ℂ := dirichletContourIntegral (fun n : ℕ ↦ (Λ n : ℂ)) x c T' -
    ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
      ∑ ρ ∈ nontrivialZerosUpTo T', (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ))
  let D : ℂ := ∑ ρ ∈ nontrivialZerosUpTo T', (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ) -
    ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)
  have hsplit_eq :
      (Chebyshev.psi x : ℂ) -
          ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
            ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) =
        -A + (B - D) := by
    dsimp [A, B, D]
    ring
  rw [hsplit_eq]
  have htri1 : ‖-A + (B - D)‖ ≤ ‖-A‖ + ‖B - D‖ := norm_add_le (-A) (B - D)
  have htri2 : ‖-A‖ + ‖B - D‖ ≤ ‖A‖ + (‖B‖ + ‖D‖) := by
    rw [norm_neg]
    exact add_le_add le_rfl (norm_sub_le B D)
  have hperr_A : ‖A‖ ≤ 900 * (x * (Real.log x) ^ 2 / T + Real.log x) := hperr_T
  have hrem_B : ‖B‖ ≤ C_r * (x * (Real.log x) ^ 2 / T) := hrem_norm
  have htail_D : ‖D‖ ≤ C_t * (x * (Real.log x) ^ 2 / T) := htail_T
  have hCrCt_le : (C_r + C_t) * (x * (Real.log x) ^ 2 / T) ≤
      (C_r + C_t) * (x * (Real.log x) ^ 2 / T + Real.log x) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlogx_pos.le) (by positivity)
  calc
    ‖-A + (B - D)‖ ≤ ‖A‖ + (‖B‖ + ‖D‖) := htri1.trans htri2
    _ ≤ 900 * (x * (Real.log x) ^ 2 / T + Real.log x) +
          (C_r * (x * (Real.log x) ^ 2 / T) + C_t * (x * (Real.log x) ^ 2 / T)) :=
        add_le_add hperr_A (add_le_add hrem_B htail_D)
    _ = 900 * (x * (Real.log x) ^ 2 / T + Real.log x) +
          (C_r + C_t) * (x * (Real.log x) ^ 2 / T) := by ring
    _ ≤ 900 * (x * (Real.log x) ^ 2 / T + Real.log x) +
          (C_r + C_t) * (x * (Real.log x) ^ 2 / T + Real.log x) := add_le_add le_rfl hCrCt_le
    _ = (900 + C_r + C_t) * (x * (Real.log x) ^ 2 / T + Real.log x) := by ring

/-- **Half-integer truncated explicit formula for `ψ(N + 1/2)`**:
there exists an absolute constant `C > 0` such that for all `N ≥ 2` and `2 ≤ T ≤ N + 1 / 2`,
setting `x = N + 1 / 2`, the approximation error for `Chebyshev.psi x` is bounded by
`C * (x * (Real.log x) ^ 2 / T)`. -/
theorem explicit_formula_psi_half_integer :
    ∃ C > 0, ∀ (N : ℕ) (T : ℝ), 2 ≤ N → 2 ≤ T → T ≤ (N : ℝ) + 1 / 2 →
      let x : ℝ := N + 1 / 2
      ‖(Chebyshev.psi x : ℂ) -
          ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
            ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ))‖ ≤
        C * (x * (Real.log x) ^ 2 / T) := by
  obtain ⟨C, hC_pos, hpsi⟩ := explicit_formula_psi
  refine ⟨3 * C, by positivity, fun N T hN hT2 hTx ↦ ?_⟩
  intro x
  have hx2 : 2 ≤ x := by
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]
    linarith
  have hT_pos : 0 < T := by linarith
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx_gt : (1 / 2 : ℝ) < Real.log x := lt_of_lt_of_le hlog2_gt (Real.log_le_log zero_lt_two hx2)
  have h1_le : 1 ≤ x / T := (one_le_div hT_pos).mpr hTx
  have hlog_le : Real.log x ≤ 2 * (x * (Real.log x) ^ 2 / T) := by
    have h1 : Real.log x ≤ (x / T) * Real.log x := by
      calc
        Real.log x = 1 * Real.log x := (one_mul _).symm
        _ ≤ (x / T) * Real.log x := mul_le_mul_of_nonneg_right h1_le (by linarith)
    have h2 : (x / T) * Real.log x ≤ (x / T) * Real.log x * (2 * Real.log x) := by
      have hnn : 0 ≤ (x / T) * Real.log x := by positivity
      calc
        (x / T) * Real.log x = (x / T) * Real.log x * 1 := (mul_one _).symm
        _ ≤ (x / T) * Real.log x * (2 * Real.log x) := mul_le_mul_of_nonneg_left (by linarith) hnn
    calc
      Real.log x ≤ (x / T) * Real.log x * (2 * Real.log x) := h1.trans h2
      _ = 2 * (x * (Real.log x) ^ 2 / T) := by ring
  calc
    ‖(Chebyshev.psi x : ℂ) -
        ((x : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
          ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ))‖
        ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := hpsi x T hx2 hT2 hTx
    _ ≤ C * (x * (Real.log x) ^ 2 / T + 2 * (x * (Real.log x) ^ 2 / T)) := by gcongr
    _ = 3 * C * (x * (Real.log x) ^ 2 / T) := by ring

end AnalyticNumberTheory.PrimeDistribution
