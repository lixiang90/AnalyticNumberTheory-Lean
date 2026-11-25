import AnalyticNumberTheory.DirichletSeries.Convergence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Perron's Formula for Dirichlet Series

This file develops Perron's discontinuous integral and Perron's summation formulas for Dirichlet
series:

- `perronKernel y c T`: the truncated vertical integral `(1 / (2πi)) ∫_{c - iT}^{c + iT} (y^s / s) ds`
  (parameterized as `(1 / (2π)) ∫_{-T}^T y^(c + it) / (c + it) dt`), with effective error bounds for
  `y > 1`, `0 < y < 1`, and `y = 1`, as well as an unconditional `O(1 + log(max T c / c))` bound.
- `perron_truncated_sum_with_half`, `perron_truncated_nonintegral`,
  `perron_truncated_explicit`, and `perron_truncated_half_integer`: truncated Perron formulas for
  `LSeries a` in the half-plane of absolute convergence (`LSeriesSummable a c`, `c > 0`).
- `rieszKernel k y c` and `riesz_perron_formula`: Riesz / Cesàro smoothed Perron formulas for
  orders `k ≥ 1`, proved via absolute vertical-line integrability, Fubini term-by-term interchange,
  and induction from `k = 1`.
-/

open Complex Filter MeasureTheory Topology

namespace AnalyticNumberTheory.DirichletSeries

/-! ### Elementary integral and complex helpers -/

private theorem norm_cexp_sub_one_le (w : ℂ) : ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun x : ℝ ↦ Complex.exp ((x : ℂ) * w))
      (w * Complex.exp ((t : ℂ) * w)) t := by
    intro t
    have hmul : HasDerivAt (fun x : ℝ ↦ (x : ℂ) * w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    simpa [mul_comm] using hmul.cexp
  have hcont : Continuous fun x : ℝ ↦ w * Complex.exp ((x : ℂ) * w) :=
    continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  have hint :
      (∫ x : ℝ in (0 : ℝ)..1, w * Complex.exp ((x : ℂ) * w)) = Complex.exp w - 1 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ hderiv x) (hcont.intervalIntegrable 0 1)
  rw [← hint]
  have hle :
      ‖∫ x : ℝ in (0 : ℝ)..1, w * Complex.exp ((x : ℂ) * w)‖ ≤
        ∫ x : ℝ in (0 : ℝ)..1, ‖w * Complex.exp ((x : ℂ) * w)‖ :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hbound :
      (∫ x : ℝ in (0 : ℝ)..1, ‖w * Complex.exp ((x : ℂ) * w)‖) ≤
        ∫ _ : ℝ in (0 : ℝ)..1, ‖w‖ * Real.exp ‖w‖ := by
    refine intervalIntegral.integral_mono_on zero_le_one (hcont.norm.intervalIntegrable 0 1)
      intervalIntegrable_const fun x hx ↦ ?_
    rw [norm_mul, Complex.norm_exp]
    have hre_le : ((x : ℂ) * w).re ≤ ‖w‖ := by
      calc
        ((x : ℂ) * w).re ≤ ‖(x : ℂ) * w‖ := Complex.re_le_norm _
        _ = |x| * ‖w‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = x * ‖w‖ := by rw [abs_of_nonneg hx.1]
        _ ≤ 1 * ‖w‖ := by gcongr; exact hx.2
        _ = ‖w‖ := one_mul _
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre_le) (norm_nonneg w)
  simpa using hle.trans hbound

private theorem cpow_div_cpow_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    (x : ℂ) ^ s / (y : ℂ) ^ s = ((x / y : ℝ) : ℂ) ^ s := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hxy0 : ((x / y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_pos hx hy).ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hy0,
    Complex.cpow_def_of_ne_zero hxy0, ← Complex.exp_sub, ← Complex.ofReal_log hx.le,
    ← Complex.ofReal_log hy.le, ← Complex.ofReal_log (div_pos hx hy).le,
    Real.log_div hx.ne' hy.ne']
  congr 1
  push_cast
  ring

private theorem differentiableAt_ofReal_cpow_const {y : ℝ} (hy : 0 < y) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ ↦ (y : ℂ) ^ z) s := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hfun : (fun z : ℂ ↦ (y : ℂ) ^ z) = fun z : ℂ ↦ Complex.exp (Complex.log (y : ℂ) * z) := by
    funext z
    exact Complex.cpow_def_of_ne_zero hy0 z
  rw [hfun]
  exact (differentiableAt_id.const_mul _).cexp

private theorem continuous_ofReal_cpow_add_mul_I {y : ℝ} (hy : 0 < y) (x0 : ℝ) :
    Continuous fun t : ℝ ↦ (y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hfun : (fun t : ℝ ↦ (y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ ↦ Complex.exp (Complex.log (y : ℂ) * ((x0 : ℂ) + (t : ℂ) * I)) := by
    funext t
    exact Complex.cpow_def_of_ne_zero hy0 _
  rw [hfun]
  exact Complex.continuous_exp.comp
    (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))

private theorem continuous_ofReal_add_mul_I_cpow {y : ℝ} (hy : 0 < y) (y0 : ℝ) :
    Continuous fun x : ℝ ↦ (y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I) := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hfun : (fun x : ℝ ↦ (y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I)) =
      fun x : ℝ ↦ Complex.exp (Complex.log (y : ℂ) * ((x : ℂ) + (y0 : ℂ) * I)) := by
    funext x
    exact Complex.cpow_def_of_ne_zero hy0 _
  rw [hfun]
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.add continuous_const))

private theorem integral_rpow_base_const {y a b : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    (∫ σ : ℝ in a..b, y ^ σ) = (y ^ b - y ^ a) / Real.log y := by
  have hlog : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hfun : (fun σ : ℝ ↦ y ^ σ) = fun σ : ℝ ↦ Real.exp (Real.log y * σ) := by
    funext σ
    rw [Real.rpow_def_of_pos hy, mul_comm]
  rw [hfun]
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun t : ℝ ↦ Real.exp (Real.log y * t) / Real.log y)
      (Real.exp (Real.log y * σ)) σ := by
    intro σ
    have hmul : HasDerivAt (fun t : ℝ ↦ Real.log y * t) (Real.log y) σ := by
      simpa using (hasDerivAt_id σ).const_mul (Real.log y)
    have hexp := hmul.exp.div_const (Real.log y)
    refine hexp.congr_deriv ?_
    rw [mul_div_cancel_right₀ _ hlog]
  have hcont : Continuous fun σ : ℝ ↦ Real.exp (Real.log y * σ) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun σ _ ↦ hderiv σ) (hcont.intervalIntegrable a b)
  rw [hint, ← sub_div]
  congr 1
  simp_rw [Real.rpow_def_of_pos hy]

private theorem arctan_le_self_of_nonneg {u : ℝ} (hu : 0 ≤ u) : Real.arctan u ≤ u := by
  have hcont : Continuous fun x : ℝ ↦ 1 / (1 + x ^ 2) :=
    continuous_const.div (continuous_const.add (continuous_pow 2)) fun x ↦
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x))
  have hint :
      (∫ x : ℝ in (0 : ℝ)..u, 1 / (1 + x ^ 2)) = Real.arctan u := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ Real.hasDerivAt_arctan x) (hcont.intervalIntegrable 0 u)
    rw [Real.arctan_zero, sub_zero] at h
    exact h
  rw [← hint]
  have hmono :
      (∫ x : ℝ in (0 : ℝ)..u, 1 / (1 + x ^ 2)) ≤ ∫ _ : ℝ in (0 : ℝ)..u, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on hu (hcont.intervalIntegrable 0 u)
      intervalIntegrable_const fun x _ ↦ ?_
    exact div_le_one_of_le₀ (by nlinarith [sq_nonneg x]) (by positivity)
  simpa using hmono

private theorem integral_const_div_add_sq {r a b : ℝ} (hr : r ≠ 0) :
    (∫ x : ℝ in a..b, r / (x ^ 2 + r ^ 2)) = Real.arctan (b / r) - Real.arctan (a / r) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ Real.arctan (t / r)) (r / (x ^ 2 + r ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ ↦ t / r) (1 / r) x := (hasDerivAt_id x).div_const r
    have h2 := (Real.hasDerivAt_arctan (x / r)).comp x h1
    refine h2.congr_deriv ?_
    field_simp [hr]
    ring
  have hcont : Continuous fun x : ℝ ↦ r / (x ^ 2 + r ^ 2) :=
    continuous_const.div ((continuous_pow 2).add continuous_const) fun x ↦
      ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hr))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
    (hcont.intervalIntegrable a b)

private theorem integral_odd_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ∀ t : ℝ, f (-t) = -f t) (T : ℝ) :
    (∫ t in (-T)..T, f t) = 0 := by
  have hneg : -(∫ t in (-T)..T, f t) = ∫ t in (-T)..T, f t := by
    rw [← intervalIntegral.integral_neg]
    have hcomp := intervalIntegral.integral_comp_neg f (a := -T) (b := T)
    rw [neg_neg] at hcomp
    calc
      ∫ t in (-T)..T, -f t = ∫ t in (-T)..T, f (-t) :=
        intervalIntegral.integral_congr fun t _ ↦ (hf t).symm
      _ = ∫ t in (-T)..T, f t := hcomp
  have htwo : (2 : ℝ) • (∫ t in (-T)..T, f t) = 0 := by
    rw [two_smul]
    nth_rw 2 [← hneg]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

private theorem integral_even_symm (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf : ∀ t : ℝ, f (-t) = f t) (T : ℝ) :
    (∫ t in (-T)..T, f t) = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have hsplit : (∫ t in (-T)..T, f t) = (∫ t in (-T)..0, f t) + ∫ t in (0 : ℝ)..T, f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (-T) 0) (hf_cont.intervalIntegrable 0 T)).symm
  have hneg_eq : (∫ t in (-T)..0, f t) = ∫ t in (0 : ℝ)..T, f t := by
    have hcomp := intervalIntegral.integral_comp_neg f (a := -T) (b := 0)
    rw [neg_zero, neg_neg] at hcomp
    rw [← hcomp]
    exact intervalIntegral.integral_congr fun t _ ↦ (hf t).symm
  rw [hsplit, hneg_eq]
  ring

/-! ### Perron's discontinuous integral -/

/-- Perron's discontinuous integral `(1 / (2πi)) ∫_{c - iT}^{c + iT} (y^s / s) ds`,
parameterized along `s = c + it` (`ds = i dt`) as
`(1 / (2π)) ∫ t in (-T)..T, y^(c + it) / (c + it)`. -/
noncomputable def perronKernel (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)

/-- Contour parameterization identity relating `perronKernel` to `(1 / (2πi)) * (i * ∫ ...)`. -/
theorem perronKernel_eq_div_two_pi_mul_I (y c T : ℝ) :
    (1 / (2 * Real.pi * I)) *
        (I * ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
      perronKernel y c T := by
  rw [perronKernel]
  field_simp [Complex.I_ne_zero]

/-- The limiting indicator function of Perron's integral: `1` for `y > 1`, `1/2` for `y = 1`,
and `0` for `y < 1`. -/
noncomputable def perronLimit (y : ℝ) : ℝ :=
  if 1 < y then 1 else if y = 1 then 1 / 2 else 0

/-- Exact evaluation of `perronKernel` at `y = 1`: `arctan(T / c) / π`. -/
theorem perronKernel_one {c : ℝ} (hc : 0 < c) (T : ℝ) :
    perronKernel 1 c T = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
  rw [perronKernel]
  simp only [Complex.ofReal_one]
  have hcongr :
      (∫ t in (-T)..T, (1 : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T,
          (((c / (t ^ 2 + c ^ 2) : ℝ) : ℂ) - (((t / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [Complex.one_cpow]
    have hdenom : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp at hre
      linarith
    have hsq : (t ^ 2 + c ^ 2 : ℝ) ≠ 0 := by positivity
    have hcc : ((c : ℂ) - (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I) = (t : ℂ) ^ 2 + (c : ℂ) ^ 2 := by
      calc ((c : ℂ) - (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I)
          = (c : ℂ) ^ 2 - (t : ℂ) ^ 2 * I ^ 2 := by ring
        _ = (t : ℂ) ^ 2 + (c : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
    have hsqc : (t : ℂ) ^ 2 + (c : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hsq
    rw [div_eq_iff hdenom]
    push_cast
    calc (1 : ℂ) = ((t : ℂ) ^ 2 + (c : ℂ) ^ 2) * ((t : ℂ) ^ 2 + (c : ℂ) ^ 2)⁻¹ :=
          (mul_inv_cancel₀ hsqc).symm
      _ = (((c : ℂ) - (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I)) * ((t : ℂ) ^ 2 + (c : ℂ) ^ 2)⁻¹ := by
          rw [hcc]
      _ = _ := by ring
  have hcont1 : Continuous fun t : ℝ ↦ ((c / (t ^ 2 + c ^ 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_const.div ((continuous_pow 2).add continuous_const) fun t ↦
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hc)))
  have hcont2 : Continuous fun t : ℝ ↦ (((t / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * I) :=
    (Complex.continuous_ofReal.comp
      (continuous_id.div ((continuous_pow 2).add continuous_const) fun t ↦
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hc)))).mul
      continuous_const
  have hodd :
      (∫ t in (-T)..T, (((t / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * I)) = 0 := by
    refine integral_odd_symm _ (fun t ↦ ?_) T
    push_cast
    ring
  have hreal_int :
      (∫ t in (-T)..T, ((c / (t ^ 2 + c ^ 2) : ℝ) : ℂ)) =
        (((2 * Real.arctan (T / c) : ℝ) : ℂ)) := by
    have hofReal :
        (∫ t in (-T)..T, ((c / (t ^ 2 + c ^ 2) : ℝ) : ℂ)) =
          ((∫ t in (-T)..T, c / (t ^ 2 + c ^ 2) : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    rw [hofReal, integral_const_div_add_sq hc.ne', neg_div, Real.arctan_neg]
    push_cast
    ring
  rw [hcongr, intervalIntegral.integral_sub (hcont1.intervalIntegrable (-T) T)
      (hcont2.intervalIntegrable (-T) T), hodd, sub_zero, hreal_int]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]

/-- Effective bound at `y = 1`: `‖perronKernel 1 c T - 1 / 2‖ ≤ c / (π * T)`. -/
theorem norm_perronKernel_one_sub_half_le {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel 1 c T - 1 / 2‖ ≤ c / (Real.pi * T) := by
  rw [perronKernel_one hc T]
  have heq : ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) - 1 / 2 =
      ((Real.arctan (T / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hinv := Real.arctan_inv_of_pos (div_pos hT hc)
  rw [inv_div] at hinv
  have hdiff : Real.arctan (T / c) / Real.pi - 1 / 2 = -(Real.arctan (c / T) / Real.pi) := by
    rw [hinv]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hdiff, abs_neg, abs_of_nonneg (div_nonneg (Real.arctan_nonneg.mpr (div_pos hc hT).le)
    Real.pi_pos.le)]
  calc
    Real.arctan (c / T) / Real.pi ≤ (c / T) / Real.pi := by
      gcongr
      exact arctan_le_self_of_nonneg (div_pos hc hT).le
    _ = c / (Real.pi * T) := by ring

/-- Crude bound at `y = 1` relative to `1`: `‖perronKernel 1 c T - 1‖ ≤ 1`. -/
theorem norm_perronKernel_one_sub_one_le_one {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel 1 c T - 1‖ ≤ 1 := by
  rw [perronKernel_one hc T]
  have heq : ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) - 1 =
      ((Real.arctan (T / c) / Real.pi - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 ≤ Real.arctan (T / c) / Real.pi :=
    div_nonneg (Real.arctan_nonneg.mpr (div_pos hT hc).le) Real.pi_pos.le
  have hle : Real.arctan (T / c) / Real.pi ≤ 1 / 2 := by
    have hat : Real.arctan (T / c) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
    calc
      Real.arctan (T / c) / Real.pi ≤ (Real.pi / 2) / Real.pi := by gcongr
      _ = 1 / 2 := by field_simp [Real.pi_ne_zero]
  rw [abs_le]
  constructor <;> linarith

/-- Boundary integral of a function around the rectangle `[x₁, x₂] × [y₁, y₂]`. -/
private noncomputable def rectBoundary (g : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : ℂ :=
  (∫ x : ℝ in x₁..x₂, g ((x : ℂ) + (y₁ : ℂ) * I)) -
    (∫ x : ℝ in x₁..x₂, g ((x : ℂ) + (y₂ : ℂ) * I)) +
      I * (∫ t : ℝ in y₁..y₂, g ((x₂ : ℂ) + (t : ℂ) * I)) -
        I * (∫ t : ℝ in y₁..y₂, g ((x₁ : ℂ) + (t : ℂ) * I))

private theorem rectBoundary_eq_zero_of_differentiableOn {g : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hg : DifferentiableOn ℂ g (Set.Icc x₁ x₂ ×ℂ Set.Icc y₁ y₂)) :
    rectBoundary g x₁ x₂ y₁ y₂ = 0 := by
  have hu : Set.uIcc ((x₁ : ℂ) + (y₁ : ℂ) * I).re ((x₂ : ℂ) + (y₂ : ℂ) * I).re ×ℂ
      Set.uIcc ((x₁ : ℂ) + (y₁ : ℂ) * I).im ((x₂ : ℂ) + (y₂ : ℂ) * I).im =
      Set.Icc x₁ x₂ ×ℂ Set.Icc y₁ y₂ := by
    simp [Set.uIcc_of_le hx, Set.uIcc_of_le hy]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
    ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₂ : ℂ) * I) (hu ▸ hg)
  simpa [rectBoundary, smul_eq_mul] using h

private theorem rectBoundary_inv_square {r : ℝ} (hr : 0 < r) :
    rectBoundary (fun s : ℂ ↦ s⁻¹) (-r) r (-r) r = 2 * Real.pi * I := by
  have hhoriz :
      (∫ x : ℝ in (-r)..r, ((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹) -
          (∫ x : ℝ in (-r)..r, ((x : ℂ) + (r : ℂ) * I)⁻¹) =
        Real.pi * I := by
    have hc1 : Continuous fun x : ℝ ↦ ((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹ :=
      Continuous.inv₀ (Complex.continuous_ofReal.add continuous_const) fun x h ↦ by
        have him := congr_arg Complex.im h
        simp at him
        linarith
    have hc2 : Continuous fun x : ℝ ↦ ((x : ℂ) + (r : ℂ) * I)⁻¹ :=
      Continuous.inv₀ (Complex.continuous_ofReal.add continuous_const) fun x h ↦ by
        have him := congr_arg Complex.im h
        simp at him
        linarith
    rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable (-r) r)
      (hc2.intervalIntegrable (-r) r)]
    have hcongr :
        (∫ x : ℝ in (-r)..r, (((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹ - ((x : ℂ) + (r : ℂ) * I)⁻¹)) =
          (2 * I) * ((∫ x : ℝ in (-r)..r, r / (x ^ 2 + r ^ 2) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      have hz1 : (x : ℂ) + ((-r : ℝ) : ℂ) * I ≠ 0 := by
        intro h
        have him := congr_arg Complex.im h
        simp at him
        linarith
      have hz2 : (x : ℂ) + (r : ℂ) * I ≠ 0 := by
        intro h
        have him := congr_arg Complex.im h
        simp at him
        linarith
      have hsq : (x ^ 2 + r ^ 2 : ℝ) ≠ 0 := by
        have := sq_pos_of_pos hr
        positivity
      rw [inv_sub_inv hz1 hz2, div_eq_mul_inv]
      have hden : ((x : ℂ) + ((-r : ℝ) : ℂ) * I) * ((x : ℂ) + (r : ℂ) * I) =
          ((x ^ 2 + r ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring_nf
        simp [Complex.I_sq]
      rw [hden]
      push_cast
      ring
    rw [hcongr, integral_const_div_add_sq hr.ne', div_self hr.ne', neg_div, div_self hr.ne',
      Real.arctan_neg, Real.arctan_one]
    push_cast
    ring
  have hvert :
      I * (∫ t : ℝ in (-r)..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) -
          I * (∫ t : ℝ in (-r)..r, (((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) =
        Real.pi * I := by
    have hc1 : Continuous fun t : ℝ ↦ ((r : ℂ) + (t : ℂ) * I)⁻¹ :=
      Continuous.inv₀ (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        fun t h ↦ by
          have hre := congr_arg Complex.re h
          simp at hre
          linarith
    have hc2 : Continuous fun t : ℝ ↦ (((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ :=
      Continuous.inv₀ (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        fun t h ↦ by
          have hre := congr_arg Complex.re h
          simp at hre
          linarith
    rw [← mul_sub, ← intervalIntegral.integral_sub (hc1.intervalIntegrable (-r) r)
      (hc2.intervalIntegrable (-r) r)]
    have hcongr :
        (∫ t : ℝ in (-r)..r, (((r : ℂ) + (t : ℂ) * I)⁻¹ - (((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)) =
          2 * ((∫ t : ℝ in (-r)..r, r / (t ^ 2 + r ^ 2) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      have hz1 : (r : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h
        have hre := congr_arg Complex.re h
        simp at hre
        linarith
      have hz2 : ((-r : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h
        have hre := congr_arg Complex.re h
        simp at hre
        linarith
      have hsq : (t ^ 2 + r ^ 2 : ℝ) ≠ 0 := by
        have := sq_pos_of_pos hr
        positivity
      rw [inv_sub_inv hz1 hz2, div_eq_mul_inv]
      have hden : ((r : ℂ) + (t : ℂ) * I) * (((-r : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((t ^ 2 + r ^ 2 : ℝ) : ℂ)) := by
        push_cast
        ring_nf
        simp [Complex.I_sq]
        ring
      rw [hden, inv_neg]
      push_cast
      ring
    rw [hcongr, integral_const_div_add_sq hr.ne', div_self hr.ne', neg_div, div_self hr.ne',
      Real.arctan_neg, Real.arctan_one]
    push_cast
    ring
  unfold rectBoundary
  calc
    (∫ x : ℝ in (-r)..r, ((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹) -
          (∫ x : ℝ in (-r)..r, ((x : ℂ) + (r : ℂ) * I)⁻¹) +
        I * (∫ t : ℝ in (-r)..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) -
      I * (∫ t : ℝ in (-r)..r, (((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)
        = ((∫ x : ℝ in (-r)..r, ((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹) -
            (∫ x : ℝ in (-r)..r, ((x : ℂ) + (r : ℂ) * I)⁻¹)) +
          (I * (∫ t : ℝ in (-r)..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) -
            I * (∫ t : ℝ in (-r)..r, (((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)) := by ring
    _ = Real.pi * I + Real.pi * I := by rw [hhoriz, hvert]
    _ = 2 * Real.pi * I := by ring

private theorem rectBoundary_sub_hole_eq_zero {g : ℂ → ℂ} {R c T r : ℝ}
    (hR : r < R) (hc : r < c) (hT : r < T) (hr : 0 < r)
    (hg : DifferentiableOn ℂ g ((Set.Icc (-R) c ×ℂ Set.Icc (-T) T) \ {0})) :
    rectBoundary g (-R) c (-T) T = rectBoundary g (-r) r (-r) r := by
  have hnot0_left : (0 : ℂ) ∉ Set.Icc (-R) (-r) ×ℂ Set.Icc (-T) T := fun h ↦ by
    have := h.1.2
    simp at this
    linarith
  have hnot0_right : (0 : ℂ) ∉ Set.Icc r c ×ℂ Set.Icc (-T) T := fun h ↦ by
    have := h.1.1
    simp at this
    linarith
  have hnot0_bot : (0 : ℂ) ∉ Set.Icc (-r) r ×ℂ Set.Icc (-T) (-r) := fun h ↦ by
    have := h.2.2
    simp at this
    linarith
  have hnot0_top : (0 : ℂ) ∉ Set.Icc (-r) r ×ℂ Set.Icc r T := fun h ↦ by
    have := h.2.1
    simp at this
    linarith
  have hd_left : DifferentiableOn ℂ g (Set.Icc (-R) (-r) ×ℂ Set.Icc (-T) T) :=
    hg.mono fun z hz ↦ ⟨⟨⟨hz.1.1, hz.1.2.trans (by linarith)⟩, hz.2⟩,
      fun h0 ↦ hnot0_left (h0 ▸ hz)⟩
  have hd_right : DifferentiableOn ℂ g (Set.Icc r c ×ℂ Set.Icc (-T) T) :=
    hg.mono fun z hz ↦ ⟨⟨⟨(by linarith : -R ≤ r).trans hz.1.1, hz.1.2⟩, hz.2⟩,
      fun h0 ↦ hnot0_right (h0 ▸ hz)⟩
  have hd_bot : DifferentiableOn ℂ g (Set.Icc (-r) r ×ℂ Set.Icc (-T) (-r)) :=
    hg.mono fun z hz ↦ ⟨⟨⟨(by linarith : -R ≤ -r).trans hz.1.1,
        hz.1.2.trans (by linarith : r ≤ c)⟩, ⟨hz.2.1, hz.2.2.trans (by linarith)⟩⟩,
      fun h0 ↦ hnot0_bot (h0 ▸ hz)⟩
  have hd_top : DifferentiableOn ℂ g (Set.Icc (-r) r ×ℂ Set.Icc r T) :=
    hg.mono fun z hz ↦ ⟨⟨⟨(by linarith : -R ≤ -r).trans hz.1.1,
        hz.1.2.trans (by linarith : r ≤ c)⟩, ⟨(by linarith : -T ≤ r).trans hz.2.1, hz.2.2⟩⟩,
      fun h0 ↦ hnot0_top (h0 ▸ hz)⟩
  have h0_left := rectBoundary_eq_zero_of_differentiableOn (by linarith : -R ≤ -r)
    (by linarith : -T ≤ T) hd_left
  have h0_right := rectBoundary_eq_zero_of_differentiableOn hc.le (by linarith : -T ≤ T) hd_right
  have h0_bot := rectBoundary_eq_zero_of_differentiableOn (by linarith : -r ≤ r)
    (by linarith : -T ≤ -r) hd_bot
  have h0_top := rectBoundary_eq_zero_of_differentiableOn (by linarith : -r ≤ r) hT.le hd_top
  have hint_x (y : ℝ) (hy_mem : y = -T ∨ y = T) :
      (∫ x : ℝ in (-R)..c, g ((x : ℂ) + (y : ℂ) * I)) =
        (∫ x : ℝ in (-R)..(-r), g ((x : ℂ) + (y : ℂ) * I)) +
          (∫ x : ℝ in (-r)..r, g ((x : ℂ) + (y : ℂ) * I)) +
            (∫ x : ℝ in r..c, g ((x : ℂ) + (y : ℂ) * I)) := by
    have hcont : ContinuousOn (fun x : ℝ ↦ g ((x : ℂ) + (y : ℂ) * I)) (Set.Icc (-R) c) := by
      have hm : ContinuousOn (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * I) (Set.Icc (-R) c) :=
        (Complex.continuous_ofReal.add continuous_const).continuousOn
      refine (hg.continuousOn).comp hm fun x hx ↦ ?_
      refine ⟨?_, ?_⟩
      · have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
        have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
        rw [Complex.mem_reProdIm, hre, him]
        refine ⟨hx, ?_⟩
        rcases hy_mem with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
      · intro h0
        have him := congr_arg Complex.im h0
        simp at him
        rcases hy_mem with rfl | rfl <;> linarith
    have hi1 : IntervalIntegrable (fun x : ℝ ↦ g ((x : ℂ) + (y : ℂ) * I)) volume (-R) (-r) :=
      (hcont.mono (Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ ↦ g ((x : ℂ) + (y : ℂ) * I)) volume (-r) r :=
      (hcont.mono (Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩)).intervalIntegrable
    have hi3 : IntervalIntegrable (fun x : ℝ ↦ g ((x : ℂ) + (y : ℂ) * I)) volume r c :=
      (hcont.mono (Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩)).intervalIntegrable
    calc
      ∫ x : ℝ in (-R)..c, g ((x : ℂ) + (y : ℂ) * I)
          = (∫ x : ℝ in (-R)..r, g ((x : ℂ) + (y : ℂ) * I)) +
              ∫ x : ℝ in r..c, g ((x : ℂ) + (y : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3).symm
      _ = (∫ x : ℝ in (-R)..(-r), g ((x : ℂ) + (y : ℂ) * I)) +
            (∫ x : ℝ in (-r)..r, g ((x : ℂ) + (y : ℂ) * I)) +
              ∫ x : ℝ in r..c, g ((x : ℂ) + (y : ℂ) * I) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hint_t (x : ℝ) (hx_mem : x = -r ∨ x = r) :
      (∫ t : ℝ in (-T)..T, g ((x : ℂ) + (t : ℂ) * I)) =
        (∫ t : ℝ in (-T)..(-r), g ((x : ℂ) + (t : ℂ) * I)) +
          (∫ t : ℝ in (-r)..r, g ((x : ℂ) + (t : ℂ) * I)) +
            (∫ t : ℝ in r..T, g ((x : ℂ) + (t : ℂ) * I)) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ g ((x : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
      have hm : ContinuousOn (fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * I) (Set.Icc (-T) T) :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      refine (hg.continuousOn).comp hm fun t ht ↦ ?_
      refine ⟨?_, ?_⟩
      · have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
        have him : ((x : ℂ) + (t : ℂ) * I).im = t := by simp
        rw [Complex.mem_reProdIm, hre, him]
        refine ⟨?_, ht⟩
        rcases hx_mem with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
      · intro h0
        have hre := congr_arg Complex.re h0
        simp at hre
        rcases hx_mem with rfl | rfl <;> linarith
    have hi1 : IntervalIntegrable (fun t : ℝ ↦ g ((x : ℂ) + (t : ℂ) * I)) volume (-T) (-r) :=
      (hcont.mono (Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t : ℝ ↦ g ((x : ℂ) + (t : ℂ) * I)) volume (-r) r :=
      (hcont.mono (Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩)).intervalIntegrable
    have hi3 : IntervalIntegrable (fun t : ℝ ↦ g ((x : ℂ) + (t : ℂ) * I)) volume r T :=
      (hcont.mono (Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩)).intervalIntegrable
    calc
      ∫ t : ℝ in (-T)..T, g ((x : ℂ) + (t : ℂ) * I)
          = (∫ t : ℝ in (-T)..r, g ((x : ℂ) + (t : ℂ) * I)) +
              ∫ t : ℝ in r..T, g ((x : ℂ) + (t : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3).symm
      _ = (∫ t : ℝ in (-T)..(-r), g ((x : ℂ) + (t : ℂ) * I)) +
            (∫ t : ℝ in (-r)..r, g ((x : ℂ) + (t : ℂ) * I)) +
              ∫ t : ℝ in r..T, g ((x : ℂ) + (t : ℂ) * I) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hsum_zero :
      rectBoundary g (-R) (-r) (-T) T + rectBoundary g r c (-T) T +
          rectBoundary g (-r) r (-T) (-r) + rectBoundary g (-r) r r T = 0 := by
    rw [h0_left, h0_right, h0_bot, h0_top]
    ring
  rw [← sub_eq_zero, ← hsum_zero]
  unfold rectBoundary
  rw [hint_x (-T) (Or.inl rfl), hint_x T (Or.inr rfl), hint_t (-r) (Or.inl rfl),
    hint_t r (Or.inr rfl)]
  ring

private theorem norm_horiz_integral_cpow_div_le {y a b y0 : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hab : a ≤ b) (hy0 : y0 ≠ 0) :
    ‖∫ σ : ℝ in a..b, (y : ℂ) ^ ((σ : ℂ) + (y0 : ℂ) * I) / ((σ : ℂ) + (y0 : ℂ) * I)‖ ≤
      (y ^ b - y ^ a) / (|y0| * Real.log y) := by
  have hy0_abs : 0 < |y0| := abs_pos.mpr hy0
  have hdenom_ne : ∀ σ : ℝ, (σ : ℂ) + (y0 : ℂ) * I ≠ 0 := by
    intro σ h
    have him := congr_arg Complex.im h
    simp at him
    exact hy0 him
  have hcont_c : Continuous fun σ : ℝ ↦
      (y : ℂ) ^ ((σ : ℂ) + (y0 : ℂ) * I) / ((σ : ℂ) + (y0 : ℂ) * I) :=
    (continuous_ofReal_add_mul_I_cpow hy y0).div
      (Complex.continuous_ofReal.add continuous_const) hdenom_ne
  have hle1 :
      ‖∫ σ : ℝ in a..b, (y : ℂ) ^ ((σ : ℂ) + (y0 : ℂ) * I) / ((σ : ℂ) + (y0 : ℂ) * I)‖ ≤
        ∫ σ : ℝ in a..b, ‖(y : ℂ) ^ ((σ : ℂ) + (y0 : ℂ) * I) / ((σ : ℂ) + (y0 : ℂ) * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hcont_r : Continuous fun σ : ℝ ↦ y ^ σ / |y0| :=
    (continuous_const.rpow continuous_id (fun _ ↦ Or.inl hy.ne')).div_const _
  have hle2 :
      (∫ σ : ℝ in a..b, ‖(y : ℂ) ^ ((σ : ℂ) + (y0 : ℂ) * I) / ((σ : ℂ) + (y0 : ℂ) * I)‖) ≤
        ∫ σ : ℝ in a..b, y ^ σ / |y0| := by
    refine intervalIntegral.integral_mono_on hab (hcont_c.norm.intervalIntegrable a b)
      (hcont_r.intervalIntegrable a b) fun σ _ ↦ ?_
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have him_le : |y0| ≤ ‖(σ : ℂ) + (y0 : ℂ) * I‖ := by
      simpa using Complex.abs_im_le_norm ((σ : ℂ) + (y0 : ℂ) * I)
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le σ) hy0_abs him_le
  have hint_r :
      (∫ σ : ℝ in a..b, y ^ σ / |y0|) = (y ^ b - y ^ a) / (|y0| * Real.log y) := by
    rw [intervalIntegral.integral_div, integral_rpow_base_const hy hy1]
    ring
  exact (hle1.trans hle2).trans_eq hint_r

private theorem norm_vert_integral_cpow_div_le {y x0 T : ℝ} (hy : 0 < y) (hx0 : x0 ≠ 0)
    (hT : 0 ≤ T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) / ((x0 : ℂ) + (t : ℂ) * I)‖ ≤
      (2 * T * y ^ x0) / |x0| := by
  have hx0_abs : 0 < |x0| := abs_pos.mpr hx0
  have hdenom_ne : ∀ t : ℝ, (x0 : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have hre := congr_arg Complex.re h
    simp at hre
    exact hx0 hre
  have hcont_c : Continuous fun t : ℝ ↦
      (y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) / ((x0 : ℂ) + (t : ℂ) * I) :=
    (continuous_ofReal_cpow_add_mul_I hy x0).div
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) hdenom_ne
  have hle1 :
      ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) / ((x0 : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ in (-T)..T, ‖(y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) / ((x0 : ℂ) + (t : ℂ) * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hle2 :
      (∫ t : ℝ in (-T)..T, ‖(y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) / ((x0 : ℂ) + (t : ℂ) * I)‖) ≤
        ∫ _ : ℝ in (-T)..T, y ^ x0 / |x0| := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (hcont_c.norm.intervalIntegrable (-T) T) intervalIntegrable_const fun t _ ↦ ?_
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hre_le : |x0| ≤ ‖(x0 : ℂ) + (t : ℂ) * I‖ := by
      simpa using Complex.abs_re_le_norm ((x0 : ℂ) + (t : ℂ) * I)
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x0) hx0_abs hre_le
  have hconst : (∫ _ : ℝ in (-T)..T, y ^ x0 / |x0|) = (2 * T * y ^ x0) / |x0| := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  exact (hle1.trans hle2).trans_eq hconst

/-- Effective bound for `0 < y < 1`: `‖perronKernel y c T‖ ≤ y ^ c / (π * T * |log y|)`. -/
theorem norm_perronKernel_lt_one_le {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  have hlog_neg : Real.log y < 0 := Real.log_neg hy hy1
  have hlog_abs : |Real.log y| = -Real.log y := abs_of_neg hlog_neg
  have hbound_R : ∀ R : ℝ, c ≤ R →
      ‖perronKernel y c T‖ ≤
        (y ^ c - y ^ R) / (Real.pi * T * (-Real.log y)) + T * y ^ R / (Real.pi * R) := by
    intro R hR
    have hR_pos : 0 < R := hc.trans_le hR
    let f : ℂ → ℂ := fun s ↦ (y : ℂ) ^ s / s
    have hf_diff : DifferentiableOn ℂ f (Set.Icc c R ×ℂ Set.Icc (-T) T) := by
      intro s hs
      have hs0 : s ≠ 0 := by
        intro h0
        have := hs.1.1
        rw [h0, Complex.zero_re] at this
        linarith
      exact ((differentiableAt_ofReal_cpow_const hy s).div differentiableAt_id hs0).differentiableWithinAt
    have hrect := rectBoundary_eq_zero_of_differentiableOn hR (by linarith : -T ≤ T) hf_diff
    unfold rectBoundary at hrect
    have hleft_eq :
        I * (∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)) =
          (∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
            (∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I)) +
              I * (∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I)) := by
      linear_combination -hrect
    have hmul := congr_arg (fun z : ℂ ↦ (-I) * z) hleft_eq
    have hlhs : (-I) * (I * ∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I) := by
      rw [← mul_assoc]
      simp
    rw [hlhs] at hmul
    have hnorm_int :
        ‖∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)‖ ≤
          ‖∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ +
            ‖∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I)‖ +
              ‖∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I)‖ := by
      rw [hmul]
      calc
        ‖(-I) * ((∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
              (∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I)) +
                I * (∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I)))‖
            = ‖(∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
                (∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I)) +
                  I * (∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I))‖ := by
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
        _ ≤ ‖(∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
              (∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I))‖ +
                ‖I * (∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I))‖ := norm_add_le _ _
        _ ≤ (‖∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ +
              ‖∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I)‖) +
                ‖∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I)‖ := by
          gcongr
          · exact norm_sub_le _ _
          · rw [norm_mul, Complex.norm_I, one_mul]
    have hbot := norm_horiz_integral_cpow_div_le hy hy1.ne hR (neg_ne_zero.mpr hT.ne')
    have htop := norm_horiz_integral_cpow_div_le hy hy1.ne hR hT.ne'
    have hright := norm_vert_integral_cpow_div_le hy hR_pos.ne' hT.le
    rw [abs_neg, abs_of_pos hT] at hbot
    rw [abs_of_pos hT] at htop
    rw [abs_of_pos hR_pos] at hright
    have hcomb :
        ‖∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)‖ ≤
          2 * ((y ^ R - y ^ c) / (T * Real.log y)) + (2 * T * y ^ R) / R := by
      have h1 : ‖∫ σ : ℝ in c..R, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
          (y ^ R - y ^ c) / (T * Real.log y) := hbot
      have h2 : ‖∫ σ : ℝ in c..R, f ((σ : ℂ) + (T : ℂ) * I)‖ ≤
          (y ^ R - y ^ c) / (T * Real.log y) := htop
      have h3 : ‖∫ t : ℝ in (-T)..T, f ((R : ℂ) + (t : ℂ) * I)‖ ≤
          (2 * T * y ^ R) / R := hright
      linarith
    have hperron_norm :
        ‖perronKernel y c T‖ =
          (1 / (2 * Real.pi)) * ‖∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)‖ := by
      rw [perronKernel, norm_mul]
      congr 1
      rw [show (1 / (2 * Real.pi : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hperron_norm]
    calc
      (1 / (2 * Real.pi)) * ‖∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)‖
          ≤ (1 / (2 * Real.pi)) * (2 * ((y ^ R - y ^ c) / (T * Real.log y)) +
              (2 * T * y ^ R) / R) := by gcongr
      _ = (y ^ c - y ^ R) / (Real.pi * T * (-Real.log y)) + T * y ^ R / (Real.pi * R) := by
        field_simp [Real.pi_ne_zero, hT.ne', hlog_neg.ne, hR_pos.ne']
        ring
  have hlim_pow : Tendsto (fun R : ℝ ↦ y ^ R) atTop (𝓝 0) :=
    tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1
  have hlim_rhs :
      Tendsto (fun R : ℝ ↦
          (y ^ c - y ^ R) / (Real.pi * T * (-Real.log y)) + T * y ^ R / (Real.pi * R))
        atTop (𝓝 (y ^ c / (Real.pi * T * (-Real.log y)))) := by
    have h1 : Tendsto (fun R : ℝ ↦ (y ^ c - y ^ R) / (Real.pi * T * (-Real.log y)))
        atTop (𝓝 ((y ^ c - 0) / (Real.pi * T * (-Real.log y)))) :=
      (tendsto_const_nhds.sub hlim_pow).div_const _
    have h2 : Tendsto (fun R : ℝ ↦ T * y ^ R / (Real.pi * R)) atTop (𝓝 0) := by
      have hmul : Tendsto (fun R : ℝ ↦ (T / Real.pi) * y ^ R * R⁻¹)
          atTop (𝓝 ((T / Real.pi) * 0 * 0)) :=
        (tendsto_const_nhds.mul hlim_pow).mul tendsto_inv_atTop_zero
      simp only [mul_zero] at hmul
      refine hmul.congr fun R ↦ ?_
      ring
    simpa using h1.add h2
  have hle_lim : ‖perronKernel y c T‖ ≤ y ^ c / (Real.pi * T * (-Real.log y)) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim_rhs ((eventually_ge_atTop c).mono hbound_R)
  rwa [← hlog_abs] at hle_lim

/-- Effective bound for `1 < y`: `‖perronKernel y c T - 1‖ ≤ y ^ c / (π * T * log y)`. -/
theorem norm_perronKernel_gt_one_sub_one_le {y c T : ℝ} (hy1 : 1 < y)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T - 1‖ ≤ y ^ c / (Real.pi * T * Real.log y) := by
  have hy : 0 < y := zero_lt_one.trans hy1
  have hlog_pos : 0 < Real.log y := Real.log_pos hy1
  let f : ℂ → ℂ := fun s ↦ (y : ℂ) ^ s / s
  have hf_diff : ∀ {S : Set ℂ}, (0 : ℂ) ∉ S → DifferentiableOn ℂ f S := by
    intro S h0 s hs
    have hs0 : s ≠ 0 := fun h ↦ h0 (h ▸ hs)
    exact ((differentiableAt_ofReal_cpow_const hy s).div differentiableAt_id hs0).differentiableWithinAt
  have hrect_outer : ∀ R : ℝ, 0 < R →
      rectBoundary f (-R) c (-T) T = 2 * Real.pi * I := by
    intro R hR
    let M : ℝ := min (min R c) T
    have hM : 0 < M := lt_min (lt_min hR hc) hT
    have hsub_eq : ∀ r : ℝ, 0 < r → r < M →
        rectBoundary f (-R) c (-T) T =
          2 * Real.pi * I + rectBoundary (fun s ↦ ((y : ℂ) ^ s - 1) / s) (-r) r (-r) r := by
      intro r hr hrM
      have hrR : r < R := hrM.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hrc : r < c := hrM.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      have hrT : r < T := hrM.trans_le (min_le_right _ _)
      have hh := rectBoundary_sub_hole_eq_zero hrR hrc hrT hr
        (hf_diff (S := (Set.Icc (-R) c ×ℂ Set.Icc (-T) T) \ {0}) fun h ↦ h.2 rfl)
      rw [hh]
      have hdecomp : ∀ s : ℂ, s ≠ 0 → f s = s⁻¹ + ((y : ℂ) ^ s - 1) / s := by
        intro s hs0
        dsimp [f]
        field_simp [hs0]
        ring
      have hc_inv_x (y0 : ℝ) (hy0 : y0 ≠ 0) :
          Continuous fun x : ℝ ↦ ((x : ℂ) + (y0 : ℂ) * I)⁻¹ :=
        Continuous.inv₀ (Complex.continuous_ofReal.add continuous_const) fun x h ↦ by
          have him := congr_arg Complex.im h
          simp at him
          exact hy0 him
      have hc_inv_t (x0 : ℝ) (hx0 : x0 ≠ 0) :
          Continuous fun t : ℝ ↦ ((x0 : ℂ) + (t : ℂ) * I)⁻¹ :=
        Continuous.inv₀ (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
          fun t h ↦ by
            have hre := congr_arg Complex.re h
            simp at hre
            exact hx0 hre
      have hc_rem_x (y0 : ℝ) (hy0 : y0 ≠ 0) :
          Continuous fun x : ℝ ↦ ((y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I) - 1) /
            ((x : ℂ) + (y0 : ℂ) * I) :=
        ((continuous_ofReal_add_mul_I_cpow hy y0).sub continuous_const).div
          (Complex.continuous_ofReal.add continuous_const) fun x h ↦ by
            have him := congr_arg Complex.im h
            simp at him
            exact hy0 him
      have hc_rem_t (x0 : ℝ) (hx0 : x0 ≠ 0) :
          Continuous fun t : ℝ ↦ ((y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) - 1) /
            ((x0 : ℂ) + (t : ℂ) * I) :=
        ((continuous_ofReal_cpow_add_mul_I hy x0).sub continuous_const).div
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t h ↦ by
            have hre := congr_arg Complex.re h
            simp at hre
            exact hx0 hre
      have hsplit_rect :
          rectBoundary f (-r) r (-r) r =
            rectBoundary (fun s ↦ s⁻¹) (-r) r (-r) r +
              rectBoundary (fun s ↦ ((y : ℂ) ^ s - 1) / s) (-r) r (-r) r := by
        have hbot_eq :
            (∫ x : ℝ in (-r)..r, f ((x : ℂ) + ((-r : ℝ) : ℂ) * I)) =
              (∫ x : ℝ in (-r)..r, ((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹) +
                ∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + ((-r : ℝ) : ℂ) * I) - 1) /
                  ((x : ℂ) + ((-r : ℝ) : ℂ) * I) := by
          have hcongr :
              (∫ x : ℝ in (-r)..r, f ((x : ℂ) + ((-r : ℝ) : ℂ) * I)) =
                ∫ x : ℝ in (-r)..r, (((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹ +
                  ((y : ℂ) ^ ((x : ℂ) + ((-r : ℝ) : ℂ) * I) - 1) /
                    ((x : ℂ) + ((-r : ℝ) : ℂ) * I)) :=
            intervalIntegral.integral_congr fun x _ ↦ hdecomp _ fun h ↦ by
              have him := congr_arg Complex.im h; simp at him; linarith
          rw [hcongr, intervalIntegral.integral_add
            ((hc_inv_x (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (-r) r)
            ((hc_rem_x (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (-r) r)]
        have htop_eq :
            (∫ x : ℝ in (-r)..r, f ((x : ℂ) + (r : ℂ) * I)) =
              (∫ x : ℝ in (-r)..r, ((x : ℂ) + (r : ℂ) * I)⁻¹) +
                ∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + (r : ℂ) * I) - 1) /
                  ((x : ℂ) + (r : ℂ) * I) := by
          have hcongr :
              (∫ x : ℝ in (-r)..r, f ((x : ℂ) + (r : ℂ) * I)) =
                ∫ x : ℝ in (-r)..r, (((x : ℂ) + (r : ℂ) * I)⁻¹ +
                  ((y : ℂ) ^ ((x : ℂ) + (r : ℂ) * I) - 1) / ((x : ℂ) + (r : ℂ) * I)) :=
            intervalIntegral.integral_congr fun x _ ↦ hdecomp _ fun h ↦ by
              have him := congr_arg Complex.im h; simp at him; linarith
          rw [hcongr, intervalIntegral.integral_add
            ((hc_inv_x r hr.ne').intervalIntegrable (-r) r)
            ((hc_rem_x r hr.ne').intervalIntegrable (-r) r)]
        have hright_eq :
            (∫ t : ℝ in (-r)..r, f ((r : ℂ) + (t : ℂ) * I)) =
              (∫ t : ℝ in (-r)..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) +
                ∫ t : ℝ in (-r)..r, ((y : ℂ) ^ ((r : ℂ) + (t : ℂ) * I) - 1) /
                  ((r : ℂ) + (t : ℂ) * I) := by
          have hcongr :
              (∫ t : ℝ in (-r)..r, f ((r : ℂ) + (t : ℂ) * I)) =
                ∫ t : ℝ in (-r)..r, (((r : ℂ) + (t : ℂ) * I)⁻¹ +
                  ((y : ℂ) ^ ((r : ℂ) + (t : ℂ) * I) - 1) / ((r : ℂ) + (t : ℂ) * I)) :=
            intervalIntegral.integral_congr fun t _ ↦ hdecomp _ fun h ↦ by
              have hre := congr_arg Complex.re h; simp at hre; linarith
          rw [hcongr, intervalIntegral.integral_add
            ((hc_inv_t r hr.ne').intervalIntegrable (-r) r)
            ((hc_rem_t r hr.ne').intervalIntegrable (-r) r)]
        have hleft_eq :
            (∫ t : ℝ in (-r)..r, f (((-r : ℝ) : ℂ) + (t : ℂ) * I)) =
              (∫ t : ℝ in (-r)..r, (((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) +
                ∫ t : ℝ in (-r)..r, ((y : ℂ) ^ (((-r : ℝ) : ℂ) + (t : ℂ) * I) - 1) /
                  (((-r : ℝ) : ℂ) + (t : ℂ) * I) := by
          have hcongr :
              (∫ t : ℝ in (-r)..r, f (((-r : ℝ) : ℂ) + (t : ℂ) * I)) =
                ∫ t : ℝ in (-r)..r, ((((-r : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ +
                  ((y : ℂ) ^ (((-r : ℝ) : ℂ) + (t : ℂ) * I) - 1) /
                    (((-r : ℝ) : ℂ) + (t : ℂ) * I)) :=
            intervalIntegral.integral_congr fun t _ ↦ hdecomp _ fun h ↦ by
              have hre := congr_arg Complex.re h; simp at hre; linarith
          rw [hcongr, intervalIntegral.integral_add
            ((hc_inv_t (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (-r) r)
            ((hc_rem_t (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (-r) r)]
        unfold rectBoundary
        rw [hbot_eq, htop_eq, hright_eq, hleft_eq]
        ring
      rw [hsplit_rect, rectBoundary_inv_square hr]
    have hrem_bound : ∀ r : ℝ, 0 < r → r < M →
        ‖rectBoundary (fun s ↦ ((y : ℂ) ^ s - 1) / s) (-r) r (-r) r‖ ≤
          8 * r * Real.log y * Real.exp (2 * r * Real.log y) := by
      intro r hr _
      have hpt : ∀ s : ℂ, |s.re| ≤ r → |s.im| ≤ r → s ≠ 0 →
          ‖((y : ℂ) ^ s - 1) / s‖ ≤ Real.log y * Real.exp (2 * r * Real.log y) := by
        intro s hre him hs0
        have hy0c : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
        have hcpow : (y : ℂ) ^ s = Complex.exp ((Real.log y : ℂ) * s) := by
          rw [Complex.cpow_def_of_ne_zero hy0c, ← Complex.ofReal_log hy.le, mul_comm]
        have hsnorm : ‖s‖ ≤ 2 * r := by
          calc
            ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * I‖ := by rw [Complex.re_add_im]
            _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * I‖ := norm_add_le _ _
            _ = |s.re| + |s.im| := by simp [Complex.norm_real]
            _ ≤ r + r := add_le_add hre him
            _ = 2 * r := by ring
        have hwnorm : ‖(Real.log y : ℂ) * s‖ = Real.log y * ‖s‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog_pos.le]
        rw [hcpow, norm_div]
        calc
          ‖Complex.exp ((Real.log y : ℂ) * s) - 1‖ / ‖s‖
              ≤ (‖(Real.log y : ℂ) * s‖ * Real.exp ‖(Real.log y : ℂ) * s‖) / ‖s‖ :=
            div_le_div_of_nonneg_right (norm_cexp_sub_one_le _) (norm_nonneg s)
          _ = Real.log y * Real.exp (Real.log y * ‖s‖) := by
            rw [hwnorm]
            field_simp [norm_ne_zero_iff.mpr hs0]
          _ ≤ Real.log y * Real.exp (2 * r * Real.log y) := by
            have hmul : Real.log y * ‖s‖ ≤ 2 * r * Real.log y :=
              (mul_le_mul_of_nonneg_left hsnorm hlog_pos.le).trans_eq (by ring)
            gcongr
      have hside_x (y0 : ℝ) (hy0_abs : |y0| ≤ r) (hy0 : y0 ≠ 0) :
          ‖∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I) - 1) /
              ((x : ℂ) + (y0 : ℂ) * I)‖ ≤
            2 * r * Real.log y * Real.exp (2 * r * Real.log y) := by
        have hcont : Continuous fun x : ℝ ↦
            ((y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I) - 1) / ((x : ℂ) + (y0 : ℂ) * I) :=
          ((continuous_ofReal_add_mul_I_cpow hy y0).sub continuous_const).div
            (Complex.continuous_ofReal.add continuous_const) fun x h ↦ by
              have him := congr_arg Complex.im h; simp at him; exact hy0 him
        have hle1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x : ℝ ↦ ((y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I) - 1) /
            ((x : ℂ) + (y0 : ℂ) * I)) (by linarith : -r ≤ r)
        have hle2 :
            (∫ x : ℝ in (-r)..r, ‖((y : ℂ) ^ ((x : ℂ) + (y0 : ℂ) * I) - 1) /
                ((x : ℂ) + (y0 : ℂ) * I)‖) ≤
              ∫ _ : ℝ in (-r)..r, Real.log y * Real.exp (2 * r * Real.log y) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hcont.norm.intervalIntegrable (-r) r) intervalIntegrable_const fun x hx ↦ ?_
          apply hpt
          · simpa [abs_le] using hx
          · simpa using hy0_abs
          · intro h; have him := congr_arg Complex.im h; simp at him; exact hy0 him
        have hconst :
            (∫ _ : ℝ in (-r)..r, Real.log y * Real.exp (2 * r * Real.log y)) =
              2 * r * Real.log y * Real.exp (2 * r * Real.log y) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        exact (hle1.trans hle2).trans_eq hconst
      have hside_t (x0 : ℝ) (hx0_abs : |x0| ≤ r) (hx0 : x0 ≠ 0) :
          ‖∫ t : ℝ in (-r)..r, ((y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) - 1) /
              ((x0 : ℂ) + (t : ℂ) * I)‖ ≤
            2 * r * Real.log y * Real.exp (2 * r * Real.log y) := by
        have hcont : Continuous fun t : ℝ ↦
            ((y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) - 1) / ((x0 : ℂ) + (t : ℂ) * I) :=
          ((continuous_ofReal_cpow_add_mul_I hy x0).sub continuous_const).div
            (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t h ↦ by
              have hre := congr_arg Complex.re h; simp at hre; exact hx0 hre
        have hle1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun t : ℝ ↦ ((y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) - 1) /
            ((x0 : ℂ) + (t : ℂ) * I)) (by linarith : -r ≤ r)
        have hle2 :
            (∫ t : ℝ in (-r)..r, ‖((y : ℂ) ^ ((x0 : ℂ) + (t : ℂ) * I) - 1) /
                ((x0 : ℂ) + (t : ℂ) * I)‖) ≤
              ∫ _ : ℝ in (-r)..r, Real.log y * Real.exp (2 * r * Real.log y) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hcont.norm.intervalIntegrable (-r) r) intervalIntegrable_const fun t ht ↦ ?_
          apply hpt
          · simpa using hx0_abs
          · simpa [abs_le] using ht
          · intro h; have hre := congr_arg Complex.re h; simp at hre; exact hx0 hre
        have hconst :
            (∫ _ : ℝ in (-r)..r, Real.log y * Real.exp (2 * r * Real.log y)) =
              2 * r * Real.log y * Real.exp (2 * r * Real.log y) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        exact (hle1.trans hle2).trans_eq hconst
      unfold rectBoundary
      have hb1 := hside_x (-r) (by rw [abs_neg, abs_of_pos hr]) (neg_ne_zero.mpr hr.ne')
      have hb2 := hside_x r (by rw [abs_of_pos hr]) hr.ne'
      have hb3 := hside_t r (by rw [abs_of_pos hr]) hr.ne'
      have hb4 := hside_t (-r) (by rw [abs_neg, abs_of_pos hr]) (neg_ne_zero.mpr hr.ne')
      have hsub := norm_sub_le
        (∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + ((-r : ℝ) : ℂ) * I) - 1) /
          ((x : ℂ) + ((-r : ℝ) : ℂ) * I))
        (∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + (r : ℂ) * I) - 1) /
          ((x : ℂ) + (r : ℂ) * I))
      have hadd := norm_add_le
        ((∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + ((-r : ℝ) : ℂ) * I) - 1) /
          ((x : ℂ) + ((-r : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + (r : ℂ) * I) - 1) /
            ((x : ℂ) + (r : ℂ) * I)))
        (I * (∫ t : ℝ in (-r)..r, ((y : ℂ) ^ ((r : ℂ) + (t : ℂ) * I) - 1) /
          ((r : ℂ) + (t : ℂ) * I)))
      have hall := norm_sub_le
        ((∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + ((-r : ℝ) : ℂ) * I) - 1) /
          ((x : ℂ) + ((-r : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (-r)..r, ((y : ℂ) ^ ((x : ℂ) + (r : ℂ) * I) - 1) /
            ((x : ℂ) + (r : ℂ) * I)) +
          I * (∫ t : ℝ in (-r)..r, ((y : ℂ) ^ ((r : ℂ) + (t : ℂ) * I) - 1) /
            ((r : ℂ) + (t : ℂ) * I)))
        (I * (∫ t : ℝ in (-r)..r, ((y : ℂ) ^ (((-r : ℝ) : ℂ) + (t : ℂ) * I) - 1) /
          (((-r : ℝ) : ℂ) + (t : ℂ) * I)))
      rw [norm_mul, Complex.norm_I, one_mul] at hadd hall
      linarith
    have hnorm_diff : ∀ ε : ℝ, 0 < ε → ‖rectBoundary f (-R) c (-T) T - 2 * Real.pi * I‖ < ε := by
      intro ε hε
      have ht0 : Tendsto (fun r : ℝ ↦ 8 * r * Real.log y * Real.exp (2 * r * Real.log y))
          (𝓝 0) (𝓝 0) := by
        have hcont : Continuous fun r : ℝ ↦ 8 * r * Real.log y * Real.exp (2 * r * Real.log y) :=
          ((continuous_const.mul continuous_id).mul continuous_const).mul
            (Real.continuous_exp.comp ((continuous_const.mul continuous_id).mul continuous_const))
        simpa using (hcont.continuousAt (x := 0)).tendsto
      obtain ⟨δ0, hδ0, hball⟩ := Metric.tendsto_nhds_nhds.mp ht0 ε hε
      let r := min (M / 2) (δ0 / 2)
      have hr : 0 < r := lt_min (half_pos hM) (half_pos hδ0)
      have hrM : r < M := (min_le_left _ _).trans_lt (half_lt_self hM)
      have hrδ : dist r 0 < δ0 := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr]
        exact (min_le_right _ _).trans_lt (half_lt_self hδ0)
      have hbd := hball hrδ
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hbd
      have heq := hsub_eq r hr hrM
      rw [heq, add_sub_cancel_left]
      exact (hrem_bound r hr hrM).trans_lt hbd
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε ↦ by
      simpa using (hnorm_diff ε hε).le))
  have hbound_R : ∀ R : ℝ, 0 < R →
      ‖perronKernel y c T - 1‖ ≤
        (y ^ c - y ^ (-R)) / (Real.pi * T * Real.log y) + T * y ^ (-R) / (Real.pi * R) := by
    intro R hR
    have hrect := hrect_outer R hR
    unfold rectBoundary at hrect
    have hright_eq :
        I * (∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)) - 2 * Real.pi * I =
          (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + (T : ℂ) * I)) -
            (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) +
              I * (∫ t : ℝ in (-T)..T, f (((-R : ℝ) : ℂ) + (t : ℂ) * I)) := by
      linear_combination hrect
    have hmul := congr_arg (fun z : ℂ ↦ (1 / (2 * Real.pi * I)) * z) hright_eq
    have hlhs :
        (1 / (2 * Real.pi * I)) *
            (I * (∫ t : ℝ in (-T)..T, f ((c : ℂ) + (t : ℂ) * I)) - 2 * Real.pi * I) =
          perronKernel y c T - 1 := by
      rw [mul_sub, perronKernel_eq_div_two_pi_mul_I]
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [div_mul_cancel₀ _ hpi]
    rw [hlhs] at hmul
    have hbot := norm_horiz_integral_cpow_div_le hy hy1.ne' (by linarith : -R ≤ c)
      (neg_ne_zero.mpr hT.ne')
    have htop := norm_horiz_integral_cpow_div_le hy hy1.ne' (by linarith : -R ≤ c) hT.ne'
    have hleft := norm_vert_integral_cpow_div_le hy (neg_ne_zero.mpr hR.ne') hT.le
    rw [abs_neg, abs_of_pos hT] at hbot
    rw [abs_of_pos hT] at htop
    rw [abs_neg, abs_of_pos hR] at hleft
    have hnorm_num : ‖(1 / (2 * Real.pi * I) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_I, mul_one, norm_mul,
        show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg Real.pi_pos.le]
    rw [hmul, norm_mul, hnorm_num]
    have hsum :
        ‖(∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + (T : ℂ) * I)) -
            (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) +
              I * (∫ t : ℝ in (-T)..T, f (((-R : ℝ) : ℂ) + (t : ℂ) * I))‖ ≤
          2 * ((y ^ c - y ^ (-R)) / (T * Real.log y)) + (2 * T * y ^ (-R)) / R := by
      have h1 : ‖∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + (T : ℂ) * I)‖ ≤
          (y ^ c - y ^ (-R)) / (T * Real.log y) := htop
      have h2 : ‖∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
          (y ^ c - y ^ (-R)) / (T * Real.log y) := hbot
      have h3 : ‖∫ t : ℝ in (-T)..T, f (((-R : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
          (2 * T * y ^ (-R)) / R := hleft
      have hsub := norm_sub_le
        (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + (T : ℂ) * I))
        (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      have hadd := norm_add_le
        ((∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + (T : ℂ) * I)) -
          (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
        (I * (∫ t : ℝ in (-T)..T, f (((-R : ℝ) : ℂ) + (t : ℂ) * I)))
      rw [norm_mul, Complex.norm_I, one_mul] at hadd
      linarith
    calc
      (1 / (2 * Real.pi)) *
          ‖(∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + (T : ℂ) * I)) -
              (∫ σ : ℝ in (-R)..c, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) +
                I * (∫ t : ℝ in (-T)..T, f (((-R : ℝ) : ℂ) + (t : ℂ) * I))‖
          ≤ (1 / (2 * Real.pi)) *
              (2 * ((y ^ c - y ^ (-R)) / (T * Real.log y)) + (2 * T * y ^ (-R)) / R) := by
        gcongr
      _ = (y ^ c - y ^ (-R)) / (Real.pi * T * Real.log y) + T * y ^ (-R) / (Real.pi * R) := by
        field_simp [Real.pi_ne_zero, hT.ne', hlog_pos.ne, hR.ne']
  have hlim_pow : Tendsto (fun R : ℝ ↦ y ^ (-R)) atTop (𝓝 0) := by
    have hinv : y⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy1
    have ht := tendsto_rpow_atTop_of_base_lt_one y⁻¹ (by linarith [inv_pos.mpr hy]) hinv
    refine ht.congr fun R ↦ ?_
    rw [Real.rpow_neg hy.le, Real.inv_rpow hy.le]
  have hlim_rhs :
      Tendsto (fun R : ℝ ↦
          (y ^ c - y ^ (-R)) / (Real.pi * T * Real.log y) + T * y ^ (-R) / (Real.pi * R))
        atTop (𝓝 (y ^ c / (Real.pi * T * Real.log y))) := by
    have h1 : Tendsto (fun R : ℝ ↦ (y ^ c - y ^ (-R)) / (Real.pi * T * Real.log y))
        atTop (𝓝 ((y ^ c - 0) / (Real.pi * T * Real.log y))) :=
      (tendsto_const_nhds.sub hlim_pow).div_const _
    have h2 : Tendsto (fun R : ℝ ↦ T * y ^ (-R) / (Real.pi * R)) atTop (𝓝 0) := by
      have hmul : Tendsto (fun R : ℝ ↦ (T / Real.pi) * y ^ (-R) * R⁻¹)
          atTop (𝓝 ((T / Real.pi) * 0 * 0)) :=
        (tendsto_const_nhds.mul hlim_pow).mul tendsto_inv_atTop_zero
      simp only [mul_zero] at hmul
      refine hmul.congr fun R ↦ ?_
      ring
    simpa using h1.add h2
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim_rhs
    ((eventually_gt_atTop (0 : ℝ)).mono hbound_R)

/-- Convergence of `perronKernel y c T` to `perronLimit y` as `T → ∞` for `y > 0` and `c > 0`. -/
theorem tendsto_perronKernel {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Tendsto (perronKernel y c) atTop (𝓝 (perronLimit y : ℂ)) := by
  rcases lt_trichotomy y 1 with hy_lt | rfl | hy_gt
  · have hlim : Tendsto (fun T : ℝ ↦ y ^ c / (Real.pi * T * |Real.log y|)) atTop (𝓝 0) := by
      have hinv := tendsto_inv_atTop_zero.const_mul (y ^ c / (Real.pi * |Real.log y|))
      rw [mul_zero] at hinv
      refine hinv.congr fun T ↦ ?_
      ring
    rw [perronLimit, ite_eq_right hy_lt.not_gt, ite_eq_right hy_lt.ne, Complex.ofReal_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa using norm_perronKernel_lt_one_le hy hy_lt hc hT
  · have hlim : Tendsto (fun T : ℝ ↦ c / (Real.pi * T)) atTop (𝓝 0) := by
      have hinv := tendsto_inv_atTop_zero.const_mul (c / Real.pi)
      rw [mul_zero] at hinv
      refine hinv.congr fun T ↦ ?_
      ring
    have heq : (perronLimit 1 : ℂ) = 1 / 2 := by
      simp [perronLimit]
    rw [heq, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact norm_perronKernel_one_sub_half_le hc hT
  · have hlim : Tendsto (fun T : ℝ ↦ y ^ c / (Real.pi * T * Real.log y)) atTop (𝓝 0) := by
      have hinv := tendsto_inv_atTop_zero.const_mul (y ^ c / (Real.pi * Real.log y))
      rw [mul_zero] at hinv
      refine hinv.congr fun T ↦ ?_
      ring
    have heq : (perronLimit y : ℂ) = 1 := by
      simp [perronLimit, hy_gt]
    rw [heq, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact norm_perronKernel_gt_one_sub_one_le hy_gt hc hT

/-- Unconditional upper bound `‖perronKernel y c T‖ ≤ (y ^ c / π) * (1 + log (max T c / c))`
for all `y > 0`, `c > 0`, `T > 0`. -/
theorem norm_perronKernel_le {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T‖ ≤ (y ^ c / Real.pi) * (1 + Real.log (max T c / c)) := by
  have hcont_c : Continuous fun t : ℝ ↦ (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) :=
    (continuous_ofReal_cpow_add_mul_I hy c).div
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t h ↦ by
        have hre := congr_arg Complex.re h
        simp at hre
        linarith
  have hnorm_pt (t : ℝ) :
      ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖ =
        y ^ c * (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹ := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, div_eq_mul_inv]
    have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    rw [hre]
  have hle1 :
      ‖∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖ ≤
        y ^ c * ∫ t in (-T)..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹ := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t : ℝ ↦ (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))
      (by linarith : -T ≤ T)
    have h2 : (∫ t in (-T)..T, ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖) =
        y ^ c * ∫ t in (-T)..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ ↦ hnorm_pt t
    exact h1.trans_eq h2
  have hcont_inv : Continuous fun t : ℝ ↦ (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹ :=
    Continuous.inv₀ (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).norm
      fun t h ↦ by
        have hre := congr_arg Complex.re (norm_eq_zero.mp h)
        simp at hre
        linarith
  have heven : ∀ t : ℝ, (‖(c : ℂ) + ((-t : ℝ) : ℂ) * I‖)⁻¹ = (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹ := by
    intro t
    congr 1
    have heq : (c : ℂ) + ((-t : ℝ) : ℂ) * I = starRingEnd ℂ ((c : ℂ) + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [heq, Complex.norm_conj]
  rw [integral_even_symm _ hcont_inv heven T] at hle1
  let m : ℝ := min T c
  have hm0 : 0 ≤ m := le_min hT.le hc.le
  have hmT : m ≤ T := min_le_left T c
  have hsplit :
      (∫ t in (0 : ℝ)..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) =
        (∫ t in (0 : ℝ)..m, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) +
          ∫ t in m..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont_inv.intervalIntegrable 0 m) (hcont_inv.intervalIntegrable m T)).symm
  have hpart1 : (∫ t in (0 : ℝ)..m, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) ≤ 1 := by
    have hmono :
        (∫ t in (0 : ℝ)..m, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) ≤ ∫ _ in (0 : ℝ)..m, c⁻¹ := by
      refine intervalIntegral.integral_mono_on hm0 (hcont_inv.intervalIntegrable 0 m)
        intervalIntegrable_const fun t _ ↦ ?_
      have hre : c ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
        simpa [abs_of_pos hc] using Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
      exact inv_anti₀ hc hre
    have hconst : (∫ _ in (0 : ℝ)..m, c⁻¹) = m / c := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, div_eq_mul_inv]
    rw [hconst] at hmono
    have hle_one : m / c ≤ 1 := (div_le_one hc).mpr (min_le_right T c)
    exact hmono.trans hle_one
  have hpart2 : (∫ t in m..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) ≤ Real.log (max T c / c) := by
    rcases le_or_gt T c with hTc | hcT
    · have hm_eq : m = T := min_eq_left hTc
      have hmax_eq : max T c = c := max_eq_right hTc
      rw [hm_eq, hmax_eq, div_self hc.ne', Real.log_one, intervalIntegral.integral_same]
    · have hm_eq : m = c := min_eq_right hcT.le
      have hmax_eq : max T c = T := max_eq_left hcT.le
      rw [hm_eq, hmax_eq]
      have hcont_t : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.uIcc c T) := by
        refine continuousOn_inv₀.mono fun t ht ↦ ?_
        rw [Set.uIcc_of_le hcT.le] at ht
        exact (lt_of_lt_of_le hc ht.1).ne'
      have hmono :
          (∫ t in c..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) ≤ ∫ t in c..T, t⁻¹ := by
        refine intervalIntegral.integral_mono_on hcT.le (hcont_inv.intervalIntegrable c T)
          hcont_t.intervalIntegrable fun t ht ↦ ?_
        have ht_pos : 0 < t := lt_of_lt_of_le hc ht.1
        have him : t ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
          simpa [abs_of_pos ht_pos] using Complex.abs_im_le_norm ((c : ℂ) + (t : ℂ) * I)
        exact inv_anti₀ ht_pos him
      have hlog : (∫ t in c..T, t⁻¹) = Real.log (T / c) := by
        rw [integral_inv_of_pos hc hT]
      exact hmono.trans_eq hlog
  have hsum_inv : (∫ t in (0 : ℝ)..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹) ≤ 1 + Real.log (max T c / c) :=
    hsplit.trans_le (add_le_add hpart1 hpart2)
  have hperron_norm :
      ‖perronKernel y c T‖ =
        (1 / (2 * Real.pi)) *
          ‖∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖ := by
    rw [perronKernel, norm_mul]
    congr 1
    rw [show (1 / (2 * Real.pi : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hperron_norm]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖
        ≤ (1 / (2 * Real.pi)) * (y ^ c * (2 * ∫ t in (0 : ℝ)..T, (‖(c : ℂ) + (t : ℂ) * I‖)⁻¹)) :=
      mul_le_mul_of_nonneg_left hle1 (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (y ^ c * (2 * (1 + Real.log (max T c / c)))) := by
      gcongr
    _ = (y ^ c / Real.pi) * (1 + Real.log (max T c / c)) := by
      field_simp [Real.pi_ne_zero]

/-! ### Truncated Perron's formula for Dirichlet series -/

/-- The truncated Perron vertical contour integral
`(1 / (2πi)) ∫_{c - iT}^{c + iT} LSeries a s * (x^s / s) ds` parameterized along `s = c + it`. -/
noncomputable def dirichletContourIntegral (a : ℕ → ℂ) (x c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    ∫ t in (-T)..T, LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
      ((c : ℂ) + (t : ℂ) * I)

/-- Contour parameterization identity relating `dirichletContourIntegral` to
`(1 / (2πi)) * (i * ∫ ...)`. -/
theorem dirichletContourIntegral_eq_div_two_pi_mul_I (a : ℕ → ℂ) (x c T : ℝ) :
    (1 / (2 * Real.pi * I)) *
        (I * ∫ t in (-T)..T,
          LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            ((c : ℂ) + (t : ℂ) * I)) =
      dirichletContourIntegral a x c T := by
  rw [dirichletContourIntegral]
  field_simp [Complex.I_ne_zero]

private theorem norm_LSeries_term_le_of_re_le_re {a : ℕ → ℂ} {s₁ s₂ : ℂ}
    (h : s₁.re ≤ s₂.re) (n : ℕ) : ‖LSeries.term a s₂ n‖ ≤ ‖LSeries.term a s₁ n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hpow : (n : ℝ) ^ s₁.re ≤ (n : ℝ) ^ s₂.re :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hn) h
    have hpos : 0 < (n : ℝ) ^ s₁.re :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hpow

private theorem continuous_LSeries_vertical {a : ℕ → ℂ} {c : ℝ}
    (ha : LSeriesSummable a (c : ℂ)) :
    Continuous fun t : ℝ ↦ LSeries a ((c : ℂ) + (t : ℂ) * I) := by
  have hu : UniformCauchySeqOn (fun N z ↦ ∑ n ∈ Finset.range N, LSeries.term a z n)
      atTop {z : ℂ | c ≤ z.re} := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hcauchy : CauchySeq (fun N ↦ ∑ n ∈ Finset.range N, ‖LSeries.term a (c : ℂ) n‖) :=
      ha.norm.hasSum.tendsto_sum_nat.cauchySeq
    obtain ⟨N₀, hN₀⟩ := (Metric.cauchySeq_iff.mp hcauchy) ε hε
    refine ⟨N₀, fun m hm n hn z hz ↦ ?_⟩
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]
      exact this n hn m hm (le_of_not_ge hmn)
    rw [dist_comm, dist_eq_norm]
    have hsplit :
        (∑ k ∈ Finset.range n, LSeries.term a z k) - (∑ k ∈ Finset.range m, LSeries.term a z k) =
          ∑ k ∈ Finset.Ico m n, LSeries.term a z k :=
      (Finset.sum_Ico_eq_sub _ hmn).symm
    have hsplit_norm :
        (∑ k ∈ Finset.range n, ‖LSeries.term a (c : ℂ) k‖) -
            (∑ k ∈ Finset.range m, ‖LSeries.term a (c : ℂ) k‖) =
          ∑ k ∈ Finset.Ico m n, ‖LSeries.term a (c : ℂ) k‖ :=
      (Finset.sum_Ico_eq_sub _ hmn).symm
    rw [hsplit]
    have hsum_le :
        ‖∑ k ∈ Finset.Ico m n, LSeries.term a z k‖ ≤
          ∑ k ∈ Finset.Ico m n, ‖LSeries.term a (c : ℂ) k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦
        norm_LSeries_term_le_of_re_le_re (by simpa using hz) k)
    have hlt := hN₀ n hn m hm
    rw [Real.dist_eq, hsplit_norm, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at hlt
    exact hsum_le.trans_lt hlt
  have htu : TendstoUniformlyOn (fun N z ↦ ∑ n ∈ Finset.range N, LSeries.term a z n)
      (LSeries a) atTop {z : ℂ | c ≤ z.re} := by
    refine hu.tendstoUniformlyOn_of_tendsto fun z hz ↦ ?_
    have hz_sum : LSeriesSummable a z := ha.of_re_le_re (by simpa using hz)
    exact hz_sum.hasSum.tendsto_sum_nat
  have htu_t : TendstoUniformlyOn
      (fun N (t : ℝ) ↦ ∑ n ∈ Finset.range N, LSeries.term a ((c : ℂ) + (t : ℂ) * I) n)
      (fun t : ℝ ↦ LSeries a ((c : ℂ) + (t : ℂ) * I)) atTop Set.univ := by
    refine (htu.comp (fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * I)).mono fun t _ ↦ ?_
    simp
  have hcont_on : ContinuousOn (fun t : ℝ ↦ LSeries a ((c : ℂ) + (t : ℂ) * I)) Set.univ := by
    refine htu_t.continuousOn (Eventually.of_forall fun N ↦ ?_).frequently
    have hcont_term : ∀ n : ℕ, Continuous fun t : ℝ ↦ LSeries.term a ((c : ℂ) + (t : ℂ) * I) n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]
        exact continuous_const
      · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have hfun : (fun t : ℝ ↦ LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) =
            fun t : ℝ ↦ a n * Complex.exp (-Complex.log (n : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
          funext t
          rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
            Complex.cpow_def_of_ne_zero hn0]
          ring_nf
        rw [hfun]
        exact continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))))
    refine Continuous.continuousOn ?_
    induction N with
    | zero => simpa using continuous_const
    | succ N ih =>
      have hfun : (fun t : ℝ ↦ ∑ n ∈ Finset.range (N + 1),
            LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) =
          fun t : ℝ ↦ (∑ n ∈ Finset.range N, LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) +
            LSeries.term a ((c : ℂ) + (t : ℂ) * I) N := by
        funext t
        exact Finset.sum_range_succ _ N
      rw [hfun]
      exact ih.add (hcont_term N)
  exact continuousOn_univ.mp hcont_on

/-- Exact series expansion for `dirichletContourIntegral`:
`dirichletContourIntegral a x c T = ∑' n, (if n = 0 then 0 else a n * perronKernel (x / n) c T)`. -/
theorem dirichletContourIntegral_eq_tsum {a : ℕ → ℂ} {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 ≤ T) (ha : LSeriesSummable a (c : ℂ)) :
    dirichletContourIntegral a x c T =
      ∑' n : ℕ, (if n = 0 then 0 else a n * perronKernel (x / n) c T) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-T) T)
  let F : ℕ → ℝ → ℂ := fun n t ↦
    LSeries.term a ((c : ℂ) + (t : ℂ) * I) n * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
      ((c : ℂ) + (t : ℂ) * I)
  have hF_cont (n : ℕ) : Continuous (F n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term_zero]
      exact continuous_const
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hterm_cont : Continuous fun t : ℝ ↦ LSeries.term a ((c : ℂ) + (t : ℂ) * I) n := by
        have hfun : (fun t : ℝ ↦ LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) =
            fun t : ℝ ↦ a n * Complex.exp (-Complex.log (n : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
          funext t
          rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
            Complex.cpow_def_of_ne_zero hn0]
          ring_nf
        rw [hfun]
        exact continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))))
      exact (hterm_cont.mul (continuous_ofReal_cpow_add_mul_I hx c)).div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t h ↦ by
          have hre := congr_arg Complex.re h
          simp at hre
          linarith
  have hF_int (n : ℕ) : Integrable (F n) μ :=
    ((hF_cont n).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hF_norm_le (n : ℕ) (t : ℝ) :
      ‖F n t‖ ≤ (x ^ c / c) * ‖LSeries.term a (c : ℂ) n‖ := by
    dsimp [F]
    have hre_cpow : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre_cpow]
    have hre : c ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
      simpa [abs_of_pos hc] using Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
    have hterm_le : ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ ≤ ‖LSeries.term a (c : ℂ) n‖ :=
      norm_LSeries_term_le_of_re_le_re (by simp) n
    calc
      ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ * x ^ c / ‖(c : ℂ) + (t : ℂ) * I‖
          ≤ ‖LSeries.term a (c : ℂ) n‖ * x ^ c / c :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hterm_le (Real.rpow_nonneg hx.le c))
          hc hre
      _ = (x ^ c / c) * ‖LSeries.term a (c : ℂ) n‖ := by ring
  have hF_sum : Summable fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖ ∂μ := by
    have hmaj : Summable fun n : ℕ ↦ ((2 * T) * (x ^ c / c)) * ‖LSeries.term a (c : ℂ) n‖ :=
      ha.norm.mul_left _
    refine hmaj.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
    have hconst : (∫ _ : ℝ, (x ^ c / c) * ‖LSeries.term a (c : ℂ) n‖ ∂μ) =
        ((2 * T) * (x ^ c / c)) * ‖LSeries.term a (c : ℂ) n‖ := by
      dsimp [μ]
      rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    have hIntConst : Integrable (fun _ : ℝ ↦ (x ^ c / c) * ‖LSeries.term a (c : ℂ) n‖) μ :=
      (continuous_const.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    exact integral_mono (hF_int n).norm hIntConst (hF_norm_le n)
  have hfub := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  have htsum_pt (t : ℝ) :
      (∑' n : ℕ, F n t) = LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
        ((c : ℂ) + (t : ℂ) * I) := by
    have ht_sum : LSeriesSummable a ((c : ℂ) + (t : ℂ) * I) :=
      ha.of_re_le_re (by simp)
    exact ((ht_sum.hasSum.mul_right _).div_const _).tsum_eq
  rw [dirichletContourIntegral, intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hLHS :
      (∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          ((c : ℂ) + (t : ℂ) * I) ∂μ) =
        ∑' n : ℕ, ∫ t : ℝ, F n t ∂μ := by
    rw [integral_congr_ae (ae_of_all _ fun t ↦ (htsum_pt t).symm), hfub]
  rw [hLHS, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F, LSeries.term_zero]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hcongr :
        (∫ t : ℝ, F n t ∂μ) =
          a n * ∫ t in (-T)..T, ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            ((c : ℂ) + (t : ℂ) * I) := by
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp [F]
      rw [LSeries.term_of_ne_zero hn, div_mul_eq_mul_div, div_div, mul_comm ((n : ℂ) ^ _),
        ← div_div, mul_div_assoc', ← cpow_div_cpow_of_pos hx hn_pos, Complex.ofReal_natCast]
      ring
    rw [hcongr, ite_eq_right hn, perronKernel]
    ring

private theorem one_sub_inv_le_log_of_pos {t : ℝ} (ht : 0 < t) : 1 - t⁻¹ ≤ Real.log t := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h
  linarith

private theorem abs_log_div_ge_of_band {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlo : x / 2 ≤ y) (hhi : y ≤ 2 * x) :
    |x - y| / (2 * x) ≤ |Real.log (x / y)| := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hratio : 1 < y / x := (one_lt_div hx).mpr hxy
    have h1 := one_sub_inv_le_log_of_pos (zero_lt_one.trans hratio)
    rw [inv_div] at h1
    have hlog_neg : Real.log (x / y) < 0 := Real.log_neg (div_pos hx hy) ((div_lt_one hy).mpr hxy)
    rw [abs_of_neg hlog_neg, ← Real.log_inv, inv_div]
    rw [abs_of_neg (sub_neg.mpr hxy), neg_sub]
    calc
      (y - x) / (2 * x) ≤ (y - x) / y := by
        refine div_le_div_of_nonneg_left (sub_nonneg.mpr hxy.le) hy hhi
      _ = 1 - x / y := by field_simp [hy.ne']
      _ ≤ Real.log (y / x) := h1
  · simp
  · have hratio : 1 < x / y := (one_lt_div hy).mpr hyx
    have h1 := one_sub_inv_le_log_of_pos (zero_lt_one.trans hratio)
    rw [inv_div] at h1
    rw [abs_of_pos (Real.log_pos hratio), abs_of_pos (sub_pos.mpr hyx)]
    calc
      (x - y) / (2 * x) ≤ (x - y) / x := by
        refine div_le_div_of_nonneg_left (sub_nonneg.mpr hyx.le) hx (by linarith)
      _ = 1 - y / x := by field_simp [hx.ne']
      _ ≤ Real.log (x / y) := h1

private theorem abs_log_div_ge_log_two_of_not_band {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hnot : y < x / 2 ∨ 2 * x < y) : Real.log 2 ≤ |Real.log (x / y)| := by
  rcases hnot with hlo | hhi
  · have hgt : 2 < x / y := by
      rw [lt_div_iff₀ hy]
      linarith
    rw [abs_of_pos (Real.log_pos (by linarith : 1 < x / y))]
    exact Real.log_le_log (by norm_num) hgt.le
  · have hgt : 2 < y / x := by
      rw [lt_div_iff₀ hx]
      linarith
    have hneg : Real.log (x / y) < 0 := Real.log_neg (div_pos hx hy) ((div_lt_one hy).mpr (by linarith))
    rw [abs_of_neg hneg, ← Real.log_inv, inv_div]
    exact Real.log_le_log (by norm_num) hgt.le

private theorem finset_sum_Icc_eq_tsum_ite {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (g : ℕ → E) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, g n = ∑' n : ℕ, (if n ∈ Finset.Icc 1 M then g n else 0) := by
  symm
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.Icc 1 M)
    (f := fun n : ℕ ↦ if n ∈ Finset.Icc 1 M then g n else 0) fun n hn ↦ ite_eq_right hn]
  exact Finset.sum_congr rfl fun n hn ↦ by simp [hn]

private theorem summable_ite_mem_Icc {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (g : ℕ → E) (M : ℕ) :
    Summable fun n : ℕ ↦ if n ∈ Finset.Icc 1 M then g n else 0 := by
  refine summable_of_hasFiniteSupport ?_
  exact (Finset.finite_toSet (Finset.Icc 1 M)).subset fun n hn ↦ by
    simp only [Function.mem_support, ne_eq] at hn
    by_contra hmem
    exact hn (ite_eq_right hmem)

/-- **Truncated Perron's Formula (half-weight at integer `x`)**:
effective pointwise error bound comparing `dirichletContourIntegral a x c T` to
`∑_{1 ≤ n ≤ x} a n` (with weight `1/2` when `n = x`). -/
theorem perron_truncated_sum_with_half {a : ℕ → ℂ} {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) (ha : LSeriesSummable a (c : ℂ)) :
    let offBand := (x ^ c / (Real.pi * T * Real.log 2)) * ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖
    let nearBand := ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
        ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|))
      else 0
    let hitTerm := ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if (n : ℝ) = x then ‖a n‖ * (c / (Real.pi * T)) else 0
    ‖dirichletContourIntegral a x c T -
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n)‖ ≤
      offBand + nearBand + hitTerm := by
  intro offBand nearBand hitTerm
  let g : ℕ → ℂ := fun n ↦
    (if n = 0 then 0 else a n * perronKernel (x / n) c T) -
      (if n ∈ Finset.Icc 1 ⌊x⌋₊ then (if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n) else 0)
  let bOff : ℕ → ℝ := fun n ↦
    if n = 0 then 0 else if (n : ℝ) < x / 2 ∨ 2 * x < n then
      (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term a (c : ℂ) n‖ else 0
  let bNear : ℕ → ℝ := fun n ↦
    if n ∈ Finset.Icc 1 ⌊2 * x⌋₊ then
      (if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
        ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|))
      else 0)
    else 0
  let bHit : ℕ → ℝ := fun n ↦
    if n ∈ Finset.Icc 1 ⌊2 * x⌋₊ then
      (if (n : ℝ) = x then ‖a n‖ * (c / (Real.pi * T)) else 0)
    else 0
  have hbOff_sum : Summable bOff := by
    have hmaj : Summable fun n : ℕ ↦
        (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term a (c : ℂ) n‖ :=
      ha.norm.mul_left _
    refine hmaj.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
    · dsimp [bOff]
      split_ifs <;> positivity
    · dsimp [bOff]
      split_ifs with h0 hband
      · positivity
      · exact le_rfl
      · positivity
  have hbNear_sum : Summable bNear := summable_ite_mem_Icc _ ⌊2 * x⌋₊
  have hbHit_sum : Summable bHit := summable_ite_mem_Icc _ ⌊2 * x⌋₊
  have hg_bound (n : ℕ) : ‖g n‖ ≤ bOff n + bNear n + bHit n := by
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [g, bOff, bNear, bHit]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hyn_pos : 0 < x / n := div_pos hx hn_pos
    have hgn_eq : ‖g n‖ ≤
        (if (n : ℝ) = x then ‖a n‖ * (c / (Real.pi * T))
         else ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|))) := by
      rcases lt_trichotomy (n : ℝ) x with hnx | hnx | hxn
      · have hmem : n ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr
          ⟨Nat.pos_of_ne_zero hn0, (Nat.le_floor_iff hx.le).mpr hnx.le⟩
        have hy1 : 1 < x / n := (one_lt_div hn_pos).mpr hnx
        have hne : (n : ℝ) ≠ x := hnx.ne
        simp only [g, hn0, ↓reduceIte, hmem, hne]
        rw [show a n * perronKernel (x / n) c T - a n = a n * (perronKernel (x / n) c T - 1) by ring,
          norm_mul]
        exact mul_le_mul_of_nonneg_left ((norm_perronKernel_gt_one_sub_one_le hy1 hc hT).trans_eq
          (by rw [abs_of_pos (Real.log_pos hy1)])) (norm_nonneg _)
      · have hmem : n ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr
          ⟨Nat.pos_of_ne_zero hn0, (Nat.le_floor_iff hx.le).mpr hnx.le⟩
        have hy1 : x / n = 1 := by rw [hnx, div_self hx.ne']
        simp only [g, hn0, ↓reduceIte, hmem, hnx]
        rw [div_self hx.ne', show a n * perronKernel 1 c T - (1 / 2 : ℂ) * a n =
          a n * (perronKernel 1 c T - 1 / 2) by ring, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_perronKernel_one_sub_half_le hc hT) (norm_nonneg _)
      · have hnmem : n ∉ Finset.Icc 1 ⌊x⌋₊ := by
          simp only [Finset.mem_Icc, not_and]
          intro _
          exact not_le_of_gt ((Nat.floor_lt hx.le).mpr hxn)
        have hne : (n : ℝ) ≠ x := hxn.ne'
        have hy1 : x / n < 1 := (div_lt_one hn_pos).mpr hxn
        simp only [g, hn0, ↓reduceIte, hnmem, sub_zero, hne]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_perronKernel_lt_one_le hyn_pos hy1 hc hT)
          (norm_nonneg _)
    by_cases heq : (n : ℝ) = x
    · have hmem2 : n ∈ Finset.Icc 1 ⌊2 * x⌋₊ := Finset.mem_Icc.mpr
        ⟨Nat.pos_of_ne_zero hn0, (Nat.le_floor_iff (by positivity)).mpr (by linarith)⟩
      have hbHit_val : bHit n = ‖a n‖ * (c / (Real.pi * T)) := by
        dsimp [bHit]
        rw [ite_eq_left hmem2, ite_eq_left heq]
      have hb1 : 0 ≤ bOff n := by dsimp [bOff]; split_ifs <;> positivity
      have hb2 : 0 ≤ bNear n := by dsimp [bNear]; split_ifs <;> positivity
      simp only [heq, ↓reduceIte] at hgn_eq
      linarith
    · by_cases hband : (n : ℝ) < x / 2 ∨ 2 * x < n
      · have hlog_ge : Real.log 2 ≤ |Real.log (x / n)| :=
          abs_log_div_ge_log_two_of_not_band hx hn_pos hband
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
        have hterm_n :
            ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) ≤
              (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term a (c : ℂ) n‖ := by
          rw [LSeries.term_of_ne_zero hn0, norm_div,
            Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0)]
          simp only [Complex.ofReal_re]
          rw [Real.div_rpow hx.le hn_pos.le]
          calc
            ‖a n‖ * ((x ^ c / (n : ℝ) ^ c) / (Real.pi * T * |Real.log (x / n)|))
                ≤ ‖a n‖ * ((x ^ c / (n : ℝ) ^ c) / (Real.pi * T * Real.log 2)) := by
              gcongr
            _ = (x ^ c / (Real.pi * T * Real.log 2)) * (‖a n‖ / (n : ℝ) ^ c) := by ring
        have hbOff_val : bOff n =
            (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term a (c : ℂ) n‖ := by
          simp [bOff, hn0, hband]
        have hb2 : 0 ≤ bNear n := by dsimp [bNear]; split_ifs <;> positivity
        have hb3 : 0 ≤ bHit n := by simp [bHit, heq]
        simp only [heq, ↓reduceIte] at hgn_eq
        linarith
      · have hle_2x : (n : ℝ) ≤ 2 * x := not_lt.mp fun h ↦ hband (Or.inr h)
        have hge_x2 : x / 2 ≤ n := not_lt.mp fun h ↦ hband (Or.inl h)
        have hmem2 : n ∈ Finset.Icc 1 ⌊2 * x⌋₊ := Finset.mem_Icc.mpr
          ⟨Nat.pos_of_ne_zero hn0, (Nat.le_floor_iff (by positivity)).mpr hle_2x⟩
        have hbNear_val : bNear n =
            ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) := by
          dsimp [bNear]
          rw [ite_eq_left hmem2, ite_eq_left ⟨hge_x2, heq⟩]
        have hb1 : 0 ≤ bOff n := by dsimp [bOff]; split_ifs <;> positivity
        have hb3 : 0 ≤ bHit n := by simp [bHit, heq]
        simp only [heq, ↓reduceIte] at hgn_eq
        linarith
  have hg_sum : Summable g :=
    (((hbOff_sum.add hbNear_sum).add hbHit_sum).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) hg_bound).of_norm
  have hdiff_tsum :
      dirichletContourIntegral a x c T -
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n) =
        ∑' n : ℕ, g n := by
    have h2 : Summable fun n : ℕ ↦
        if n ∈ Finset.Icc 1 ⌊x⌋₊ then (if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n) else 0 :=
      summable_ite_mem_Icc _ ⌊x⌋₊
    have h1 : Summable fun n : ℕ ↦ if n = 0 then 0 else a n * perronKernel (x / n) c T :=
      (hg_sum.add h2).congr fun n ↦ by dsimp [g]; ring
    rw [dirichletContourIntegral_eq_tsum hx hc hT.le ha,
      finset_sum_Icc_eq_tsum_ite (fun n ↦ if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n) ⌊x⌋₊,
      ← h1.tsum_sub h2]
  have hnorm_le : ‖∑' n : ℕ, g n‖ ≤ ∑' n : ℕ, (bOff n + bNear n + bHit n) :=
    (norm_tsum_le_tsum_norm hg_sum.norm).trans
      (hg_sum.norm.tsum_le_tsum hg_bound ((hbOff_sum.add hbNear_sum).add hbHit_sum))
  have hbOff_le : ∑' n : ℕ, bOff n ≤ offBand := by
    have hmaj : Summable fun n : ℕ ↦
        (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term a (c : ℂ) n‖ :=
      ha.norm.mul_left _
    calc
      ∑' n : ℕ, bOff n ≤ ∑' n : ℕ,
          (x ^ c / (Real.pi * T * Real.log 2)) * ‖LSeries.term a (c : ℂ) n‖ := by
        refine hbOff_sum.tsum_le_tsum (fun n ↦ ?_) hmaj
        dsimp [bOff]
        split_ifs
        · positivity
        · exact le_rfl
        · positivity
      _ = offBand := tsum_mul_left
  have hbNear_eq : ∑' n : ℕ, bNear n = nearBand := by
    rw [← finset_sum_Icc_eq_tsum_ite _ ⌊2 * x⌋₊]
  have hbHit_eq : ∑' n : ℕ, bHit n = hitTerm := by
    rw [← finset_sum_Icc_eq_tsum_ite _ ⌊2 * x⌋₊]
  rw [hdiff_tsum]
  calc
    ‖∑' n : ℕ, g n‖ ≤ ∑' n : ℕ, (bOff n + bNear n + bHit n) := hnorm_le
    _ = ∑' n : ℕ, bOff n + ∑' n : ℕ, bNear n + ∑' n : ℕ, bHit n := by
      rw [(hbOff_sum.add hbNear_sum).tsum_add hbHit_sum, hbOff_sum.tsum_add hbNear_sum]
    _ ≤ offBand + nearBand + hitTerm := by
      rw [hbNear_eq, hbHit_eq]
      gcongr

/-- **Truncated Perron's Formula (non-integral `x`)**: when `∀ n : ℕ, (n : ℝ) ≠ x`
(for example `x = N + 1 / 2`), the `1/2`-weight and integer-hit error term vanish cleanly. -/
theorem perron_truncated_nonintegral {a : ℕ → ℂ} {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) (hx_nonint : ∀ n : ℕ, (n : ℝ) ≠ x)
    (ha : LSeriesSummable a (c : ℂ)) :
    ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ +
        ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if x / 2 ≤ n then ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) else 0 := by
  have h := perron_truncated_sum_with_half hx hc hT ha
  dsimp only at h
  have hsum_eq :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n)) =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n :=
    Finset.sum_congr rfl fun n _ ↦ ite_eq_right (hx_nonint n)
  have hnear_eq :
      (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|))
          else 0) =
        ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if x / 2 ≤ n then ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) else 0 :=
    Finset.sum_congr rfl fun n _ ↦ by simp [hx_nonint n]
  have hhit_eq :
      (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if (n : ℝ) = x then ‖a n‖ * (c / (Real.pi * T)) else 0) = 0 :=
    Finset.sum_eq_zero fun n _ ↦ ite_eq_right (hx_nonint n)
  rwa [hsum_eq, hnear_eq, hhit_eq, add_zero] at h

/-- **Explicit Truncated Perron's Formula** in terms of `|x - n|` for the near-band terms
`x / 2 ≤ n ≤ 2 * x`, valid for arbitrary `x > 0`. -/
theorem perron_truncated_explicit {a : ℕ → ℂ} {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) (ha : LSeriesSummable a (c : ℂ)) :
    ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ +
        (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖a n‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
          else 0) +
        (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if (n : ℝ) = x then ‖a n‖ * (1 / 2 + c / (Real.pi * T)) else 0) := by
  have hhalf := perron_truncated_sum_with_half hx hc hT ha
  dsimp only at hhalf
  let S_main := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n
  let S_half := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) * a n else a n)
  have hS_diff : ‖S_half - S_main‖ ≤
      ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, if (n : ℝ) = x then ‖a n‖ * (1 / 2 : ℝ) else 0 := by
    have heq : S_half - S_main =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then -(1 / 2 : ℂ) * a n else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      split_ifs <;> ring
    rw [heq]
    have hnorm :
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then -(1 / 2 : ℂ) * a n else 0)‖ ≤
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if (n : ℝ) = x then ‖a n‖ * (1 / 2 : ℝ) else 0 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
      split_ifs
      · rw [norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, mul_comm]
      · simp
    refine hnorm.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦ by
      split_ifs <;> positivity)
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono (by linarith))⟩
  have hnear_le :
      (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖a n‖ * ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|))
          else 0) ≤
        ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖a n‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
          else 0 := by
    refine Finset.sum_le_sum fun n hn ↦ ?_
    split_ifs with hcond
    · have hn_mem := Finset.mem_Icc.mp hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_mem.1
      have hle_2x : (n : ℝ) ≤ 2 * x := (Nat.le_floor_iff (by positivity)).mp hn_mem.2
      have hlog := abs_log_div_ge_of_band hx hn_pos hcond.1 hle_2x
      have hpow : (x / n) ^ c ≤ 2 ^ c := by
        refine Real.rpow_le_rpow (by positivity) ?_ hc.le
        rw [div_le_iff₀ hn_pos]
        linarith [hcond.1]
      have h1 : (x / n) ^ c / (Real.pi * T * |Real.log (x / n)|) ≤
          2 ^ c / (Real.pi * T * (|x - n| / (2 * x))) := by
        refine div_le_div₀ (by positivity) hpow
          (mul_pos (mul_pos Real.pi_pos hT) (div_pos (abs_pos.mpr (sub_ne_zero.mpr hcond.2.symm))
            (by positivity))) (by gcongr)
      have h2 : 2 ^ c / (Real.pi * T * (|x - n| / (2 * x))) =
          2 ^ c * (2 * x) / (Real.pi * T * |x - n|) := by
        have hxn : |x - n| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hcond.2.symm)
        field_simp [Real.pi_ne_zero, hT.ne', hx.ne', hxn]
      exact mul_le_mul_of_nonneg_left (h1.trans_eq h2) (norm_nonneg _)
    · exact le_rfl
  have hhit_eq :
      (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if (n : ℝ) = x then ‖a n‖ * (c / (Real.pi * T)) else 0) +
        (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, if (n : ℝ) = x then ‖a n‖ * (1 / 2 : ℝ) else 0) =
      ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        if (n : ℝ) = x then ‖a n‖ * (1 / 2 + c / (Real.pi * T)) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    split_ifs <;> ring
  calc
    ‖dirichletContourIntegral a x c T - S_main‖
        = ‖(dirichletContourIntegral a x c T - S_half) + (S_half - S_main)‖ := by ring_nf
    _ ≤ ‖dirichletContourIntegral a x c T - S_half‖ + ‖S_half - S_main‖ := norm_add_le _ _
    _ ≤ _ := by linarith [hhalf, hS_diff, hnear_le, hhit_eq]

/-- Half-integer specialization `x = N + 1 / 2` (`|x - n| ≥ 1 / 2` for all `n`), giving a
completely clean `O(1 / T)` Perron truncation formula. -/
theorem perron_truncated_half_integer {a : ℕ → ℂ} {N : ℕ} {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T) (ha : LSeriesSummable a (c : ℂ)) :
    let x : ℝ := N + 1 / 2
    ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 N, a n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ +
        (2 ^ c * (4 * x) / (Real.pi * T)) * ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖ := by
  intro x
  have hx_pos : 0 < x := by positivity
  have hx_nonint : ∀ n : ℕ, (n : ℝ) ≠ x := by
    intro n h
    dsimp [x] at h
    rcases le_or_gt n N with hn | hn
    · have : (n : ℝ) ≤ N := by exact_mod_cast hn
      linarith
    · have : (N + 1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hfloor : ⌊x⌋₊ = N := by
    rw [Nat.floor_eq_iff hx_pos.le]
    dsimp [x]
    constructor <;> linarith
  have hfloor2 : ⌊2 * x⌋₊ = 2 * N + 1 := by
    have h2x : 2 * x = ((2 * N + 1 : ℕ) : ℝ) := by
      dsimp [x]
      push_cast
      ring
    rw [h2x, Nat.floor_natCast]
  have hex := perron_truncated_explicit hx_pos hc hT ha
  have hhit0 :
      (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if (n : ℝ) = x then ‖a n‖ * (1 / 2 + c / (Real.pi * T)) else 0) = 0 :=
    Finset.sum_eq_zero fun n _ ↦ ite_eq_right (hx_nonint n)
  rw [hfloor2] at hhit0
  rw [hfloor, hfloor2, hhit0, add_zero] at hex
  refine hex.trans (add_le_add le_rfl ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  split_ifs with hcond
  · have hdist : (1 / 2 : ℝ) ≤ |x - n| := by
      dsimp [x]
      rcases le_or_gt n N with hn | hn
      · have : (n : ℝ) ≤ N := by exact_mod_cast hn
        rw [abs_of_pos (by linarith)]
        linarith
      · have : (N + 1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_neg (by linarith)]
        linarith
    have h1 : 2 ^ c * (2 * x) / (Real.pi * T * |x - n|) ≤
        2 ^ c * (2 * x) / (Real.pi * T * (1 / 2)) := by
      gcongr
    have h2 : 2 ^ c * (2 * x) / (Real.pi * T * (1 / 2)) = 2 ^ c * (4 * x) / (Real.pi * T) := by
      field_simp [Real.pi_ne_zero, hT.ne']
      ring
    rw [mul_comm (‖a n‖)]
    exact mul_le_mul_of_nonneg_right (h1.trans_eq h2) (norm_nonneg _)
  · positivity

/-! ### Riesz / Cesàro smoothed Perron formula (`k ≥ 1`) -/

/-- The Riesz denominator `s (s + 1) ⋯ (s + k)`. -/
def rieszDenom (k : ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range (k + 1), (s + j)

/-- The vertical line Riesz Perron kernel
`(1 / (2π)) ∫ t : ℝ, y^(c + it) / (s (s + 1) ⋯ (s + k))`. -/
noncomputable def rieszKernel (k : ℕ) (y c : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom k ((c : ℂ) + (t : ℂ) * I)

/-- Shift identity `rieszDenom k (s + 1) = ∏ j ∈ Ico 1 (k + 2), (s + j)`. -/
theorem rieszDenom_succ_left (k : ℕ) (s : ℂ) :
    rieszDenom k (s + 1) = ∏ j ∈ Finset.Ico 1 (k + 2), (s + j) := by
  unfold rieszDenom
  refine Finset.prod_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    omega
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    push_cast
    ring

/-- Partial fraction identity for the Riesz denominator:
`1 / rieszDenom (k + 1) s = (1 / (k + 1)) * (1 / rieszDenom k s - 1 / rieszDenom k (s + 1))`. -/
theorem rieszDenom_partial_fraction (k : ℕ) (s : ℂ)
    (hs : ∀ j : ℕ, j ≤ k + 1 → s + j ≠ 0) :
    (1 / rieszDenom (k + 1) s) =
      (1 / ((k + 1 : ℕ) : ℂ)) * (1 / rieszDenom k s - 1 / rieszDenom k (s + 1)) := by
  have h1 : rieszDenom (k + 1) s = rieszDenom k s * (s + ((k + 1 : ℕ) : ℂ)) := by
    simp [rieszDenom, Finset.prod_range_succ]
  have h2 : rieszDenom (k + 1) s = s * rieszDenom k (s + 1) := by
    rw [rieszDenom_succ_left, rieszDenom]
    have hsplit : Finset.range (k + 2) = insert 0 (Finset.Ico 1 (k + 2)) := by
      ext j; simp; omega
    rw [hsplit, Finset.prod_insert (by simp)]
    simp
  have hk_ne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hd_k : rieszDenom k s ≠ 0 := by
    rw [rieszDenom, Finset.prod_ne_zero_iff]
    intro j hj
    exact hs j (by simp only [Finset.mem_range] at hj; omega)
  have hd_k1 : rieszDenom k (s + 1) ≠ 0 := by
    rw [rieszDenom_succ_left, Finset.prod_ne_zero_iff]
    intro j hj
    exact hs j (by simp only [Finset.mem_Ico] at hj; omega)
  have hd_full : rieszDenom (k + 1) s ≠ 0 := by
    rw [h1]
    exact mul_ne_zero hd_k (hs (k + 1) le_rfl)
  rw [div_sub_div _ _ hd_k hd_k1, one_mul, mul_one]
  have hnum : (rieszDenom k (s + 1) - rieszDenom k s) * rieszDenom (k + 1) s =
      ((k + 1 : ℕ) : ℂ) * (rieszDenom k s * rieszDenom k (s + 1)) := by
    have hsub : (s + ((k + 1 : ℕ) : ℂ)) - s = ((k + 1 : ℕ) : ℂ) := by ring
    calc
      (rieszDenom k (s + 1) - rieszDenom k s) * rieszDenom (k + 1) s
          = rieszDenom k (s + 1) * rieszDenom (k + 1) s -
              rieszDenom k s * rieszDenom (k + 1) s := sub_mul _ _ _
      _ = rieszDenom k (s + 1) * (rieszDenom k s * (s + ((k + 1 : ℕ) : ℂ))) -
            rieszDenom k s * (s * rieszDenom k (s + 1)) := by
          nth_rw 1 [h1]
          nth_rw 1 [h2]
      _ = ((s + ((k + 1 : ℕ) : ℂ)) - s) * (rieszDenom k s * rieszDenom k (s + 1)) := by ring
      _ = ((k + 1 : ℕ) : ℂ) * (rieszDenom k s * rieszDenom k (s + 1)) := by rw [hsub]
  rw [div_eq_mul_inv (a := 1), one_mul, div_eq_mul_inv (a := 1), one_mul]
  field_simp [hk_ne, hd_k, hd_k1, hd_full]
  linear_combination -hnum

private theorem continuous_rieszDenom (k : ℕ) (c : ℝ) :
    Continuous fun t : ℝ ↦ rieszDenom k ((c : ℂ) + (t : ℂ) * I) := by
  induction k with
  | zero =>
    have hfun : (fun t : ℝ ↦ rieszDenom 0 ((c : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * I := by
      funext t
      simp [rieszDenom]
    rw [hfun]
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  | succ k ih =>
    have hfun : (fun t : ℝ ↦ rieszDenom (k + 1) ((c : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ rieszDenom k ((c : ℂ) + (t : ℂ) * I) *
          (((c : ℂ) + (t : ℂ) * I) + ((k + 1 : ℕ) : ℂ)) := by
      funext t
      simp [rieszDenom, Finset.prod_range_succ]
    rw [hfun]
    exact ih.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).add
      continuous_const)

private theorem prod_norm_ge_one (z : ℂ) (S : Finset ℕ) (hS : ∀ j ∈ S, (1 : ℝ) ≤ ‖z + j‖) :
    1 ≤ ∏ j ∈ S, ‖z + j‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact one_le_mul_of_one_le_of_one_le (hS a (Finset.mem_insert_self a s))
      (ih fun j hj ↦ hS j (Finset.mem_insert_of_mem hj))

/-- Lower bound `c^2 + t^2 ≤ ‖rieszDenom k (c + it)‖` for `k ≥ 1` and `c > 0`. -/
theorem norm_rieszDenom_ge {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    c ^ 2 + t ^ 2 ≤ ‖rieszDenom k ((c : ℂ) + (t : ℂ) * I)‖ := by
  let s : ℂ := (c : ℂ) + (t : ℂ) * I
  have hnorm_j01 : c ^ 2 + t ^ 2 ≤ ‖s + (0 : ℕ)‖ * ‖s + (1 : ℕ)‖ := by
    have hsq : c ^ 2 + t ^ 2 = ‖s‖ * ‖s‖ := by
      rw [← sq, Complex.sq_norm, Complex.normSq_apply]
      simp [s]
      ring
    have hs1 : ‖s‖ ≤ ‖s + 1‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re,
        Complex.add_im, Complex.mul_im, Complex.one_im]
      nlinarith
    calc
      c ^ 2 + t ^ 2 = ‖s‖ * ‖s‖ := hsq
      _ ≤ ‖s‖ * ‖s + 1‖ := by gcongr
      _ = ‖s + (0 : ℕ)‖ * ‖s + (1 : ℕ)‖ := by simp
  have hsplit : Finset.range (k + 1) = insert 0 (insert 1 (Finset.Ico 2 (k + 1))) := by
    ext j; simp; omega
  have h0_nmem : 0 ∉ insert 1 (Finset.Ico 2 (k + 1)) := by simp
  have h1_nmem : 1 ∉ Finset.Ico 2 (k + 1) := by simp
  rw [rieszDenom, norm_prod, hsplit, Finset.prod_insert h0_nmem, Finset.prod_insert h1_nmem,
    ← mul_assoc]
  have htail_ge_one : 1 ≤ ∏ j ∈ Finset.Ico 2 (k + 1), ‖s + j‖ := by
    refine prod_norm_ge_one s (Finset.Ico 2 (k + 1)) fun j hj ↦ ?_
    simp only [Finset.mem_Ico] at hj
    have hre : c + j ≤ ‖s + j‖ := by
      simpa [s, abs_of_pos (by positivity : 0 < c + j)] using Complex.abs_re_le_norm (s + j)
    have h2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.1
    linarith
  calc
    c ^ 2 + t ^ 2 ≤ ‖s + (0 : ℕ)‖ * ‖s + (1 : ℕ)‖ := hnorm_j01
    _ = (‖s + (0 : ℕ)‖ * ‖s + (1 : ℕ)‖) * 1 := (mul_one _).symm
    _ ≤ (‖s + (0 : ℕ)‖ * ‖s + (1 : ℕ)‖) * ∏ j ∈ Finset.Ico 2 (k + 1), ‖s + j‖ :=
      mul_le_mul_of_nonneg_left htail_ge_one (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Integrability of the reciprocal quadratic weight on a positive vertical line. -/
theorem integrable_inv_sq_add {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹ := by
  have hint : Integrable fun t : ℝ ↦ c ^ (-2 : ℝ) * (1 + (c⁻¹ * t) ^ 2)⁻¹ :=
    (integrable_inv_one_add_mul_sq (inv_ne_zero hc.ne')).const_mul _
  refine hint.congr (ae_of_all _ fun t ↦ ?_)
  rw [Real.rpow_neg hc.le, Real.rpow_two]
  field_simp [hc.ne']

/-- Absolute vertical-line integrability of `y^(c + it) / (s (s + 1) ⋯ (s + k))` for `k ≥ 1`. -/
theorem integrable_cpow_div_rieszDenom {k : ℕ} (hk : 1 ≤ k) {y c : ℝ}
    (hy : 0 < y) (hc : 0 < c) :
    Integrable fun t : ℝ ↦
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom k ((c : ℂ) + (t : ℂ) * I) := by
  have hdenom_ne : ∀ t : ℝ, rieszDenom k ((c : ℂ) + (t : ℂ) * I) ≠ 0 := fun t h0 ↦ by
    have hge := norm_rieszDenom_ge hk hc t
    rw [h0, norm_zero] at hge
    have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
    linarith
  have hcont : Continuous fun t : ℝ ↦
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom k ((c : ℂ) + (t : ℂ) * I) :=
    (continuous_ofReal_cpow_add_mul_I hy c).div (continuous_rieszDenom k c) hdenom_ne
  refine ((integrable_inv_sq_add hc).const_mul (y ^ c)).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun t ↦ ?_)
  have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hge := norm_rieszDenom_ge hk hc t
  have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
  calc
    y ^ c / ‖rieszDenom k ((c : ℂ) + (t : ℂ) * I)‖ ≤ y ^ c / (c ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le c) hpos hge
    _ = y ^ c * (c ^ 2 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

private theorem rieszKernel_one {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    rieszKernel 1 y c = if 1 ≤ y then ((1 - y⁻¹ : ℝ) : ℂ) else 0 := by
  let g : ℝ → ℂ := fun t ↦
    (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom 1 ((c : ℂ) + (t : ℂ) * I)
  have hg_int : Integrable g volume := integrable_cpow_div_rieszDenom le_rfl hy hc
  have hlim_int :
      Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi : ℂ)) * ∫ t in (-T)..T, g t)
        atTop (𝓝 (rieszKernel 1 y c)) := by
    have ht := intervalIntegral_tendsto_integral hg_int tendsto_neg_atTop_atBot tendsto_id
    simpa [rieszKernel] using ht.const_mul (1 / (2 * Real.pi : ℂ))
  have hg_eq (t : ℝ) :
      g t = (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) -
        ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
          (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    let s : ℂ := (c : ℂ) + (t : ℂ) * I
    have hs : ∀ j : ℕ, j ≤ 1 → s + j ≠ 0 := fun j _ h ↦ by
      have hre := congr_arg Complex.re h
      simp [s] at hre
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hpf := rieszDenom_partial_fraction 0 s hs
    have hd0 : rieszDenom 0 s = s := by simp [rieszDenom]
    have hd0' : rieszDenom 0 (s + 1) = s + 1 := by simp [rieszDenom]
    rw [hd0, hd0'] at hpf
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hpow : (y : ℂ) ^ (s + 1) = (y : ℂ) ^ s * (y : ℂ) := by
      rw [Complex.cpow_add _ _ hyc, Complex.cpow_one]
    have hs1 : (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) = s + 1 := by
      simp only [s]
      push_cast
      ring
    change (y : ℂ) ^ s / rieszDenom (0 + 1) s =
      (y : ℂ) ^ s / s - ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
        (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I))
    rw [div_eq_mul_inv (a := (y : ℂ) ^ s), ← one_div, hpf, hs1, hpow]
    push_cast
    field_simp [hyc, hs 0 (by omega), hs 1 (by omega)]
  have hperron_split (T : ℝ) :
      (1 / (2 * Real.pi : ℂ)) * ∫ t in (-T)..T, g t =
        perronKernel y c T - ((y⁻¹ : ℝ) : ℂ) * perronKernel y (c + 1) T := by
    have hc1 : Continuous fun t : ℝ ↦
        (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) :=
      (continuous_ofReal_cpow_add_mul_I hy c).div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t h ↦ by
          have hre := congr_arg Complex.re h; simp at hre; linarith
    have hc2 : Continuous fun t : ℝ ↦
        ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
          (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)) :=
      continuous_const.mul ((continuous_ofReal_cpow_add_mul_I hy (c + 1)).div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t h ↦ by
          have hre := congr_arg Complex.re h; simp at hre; linarith)
    have hint_eq :
        (∫ t in (-T)..T, g t) =
          (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
            ((y⁻¹ : ℝ) : ℂ) * ∫ t in (-T)..T,
              (y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) / (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) := by
      have hcongr :
          (∫ t in (-T)..T, g t) =
            ∫ t in (-T)..T,
              ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) -
                ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
                  (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I))) :=
        intervalIntegral.integral_congr fun t _ ↦ hg_eq t
      rw [hcongr, intervalIntegral.integral_sub (hc1.intervalIntegrable (-T) T)
        (hc2.intervalIntegrable (-T) T), intervalIntegral.integral_const_mul]
    rw [hint_eq, perronKernel, perronKernel]
    ring
  have hlim_perron :
      Tendsto (fun T : ℝ ↦ perronKernel y c T - ((y⁻¹ : ℝ) : ℂ) * perronKernel y (c + 1) T)
        atTop (𝓝 ((perronLimit y : ℂ) - ((y⁻¹ : ℝ) : ℂ) * (perronLimit y : ℂ))) :=
    (tendsto_perronKernel hy hc).sub ((tendsto_perronKernel hy (by linarith)).const_mul _)
  have heq_lim :
      rieszKernel 1 y c = (perronLimit y : ℂ) - ((y⁻¹ : ℝ) : ℂ) * (perronLimit y : ℂ) :=
    tendsto_nhds_unique hlim_int (hlim_perron.congr fun T ↦ (hperron_split T).symm)
  rw [heq_lim]
  rcases lt_trichotomy y 1 with hlt | rfl | hgt
  · simp [perronLimit, not_lt_of_gt hlt, hlt.ne, not_le_of_gt hlt]
  · simp [perronLimit]
  · simp [perronLimit, hgt, hgt.le]

/-- Exact evaluation of the Riesz kernel for `k ≥ 1`, `y > 0`, `c > 0`:
`rieszKernel k y c = (1 - y⁻¹) ^ k / k!` if `1 ≤ y`, and `0` otherwise. -/
theorem rieszKernel_eq {k : ℕ} (hk : 1 ≤ k) {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    rieszKernel k y c =
      if 1 ≤ y then (((1 - y⁻¹) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) else 0 := by
  induction k, hk using Nat.le_induction generalizing c with
  | base =>
    simpa [Nat.factorial_one] using rieszKernel_one hy hc
  | succ k hk ih =>
    have hc1 : 0 < c + 1 := by linarith
    have hint1 := integrable_cpow_div_rieszDenom hk hy hc
    have hint2 := integrable_cpow_div_rieszDenom hk hy hc1
    have hsplit : ∀ t : ℝ,
        (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom (k + 1) ((c : ℂ) + (t : ℂ) * I) =
          (1 / ((k + 1 : ℕ) : ℂ)) *
            ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom k ((c : ℂ) + (t : ℂ) * I) -
              ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
                rieszDenom k (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I))) := by
      intro t
      let s : ℂ := (c : ℂ) + (t : ℂ) * I
      have hs : ∀ j : ℕ, j ≤ k + 1 → s + j ≠ 0 := fun j _ h ↦ by
        have hre := congr_arg Complex.re h
        simp [s] at hre
        linarith [Nat.cast_nonneg (α := ℝ) j]
      have hpf := rieszDenom_partial_fraction k s hs
      have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have hpow : (y : ℂ) ^ (s + 1) = (y : ℂ) ^ s * (y : ℂ) := by
        rw [Complex.cpow_add _ _ hyc, Complex.cpow_one]
      have hs1 : (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) = s + 1 := by
        simp only [s]; push_cast; ring
      change (y : ℂ) ^ s / rieszDenom (k + 1) s =
        (1 / ((k + 1 : ℕ) : ℂ)) *
          ((y : ℂ) ^ s / rieszDenom k s -
            ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
              rieszDenom k (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)))
      rw [hs1, hpow, div_eq_mul_inv (a := (y : ℂ) ^ s), ← one_div, hpf]
      push_cast
      have hy_cancel : ((y : ℂ)⁻¹) * ((y : ℂ) ^ s * (y : ℂ)) = (y : ℂ) ^ s := by
        rw [mul_left_comm, inv_mul_cancel₀ hyc, mul_one]
      rw [mul_div_assoc' ((y : ℂ)⁻¹), hy_cancel]
      ring
    have hrec : rieszKernel (k + 1) y c =
        (1 / ((k + 1 : ℕ) : ℂ)) * (rieszKernel k y c - ((y⁻¹ : ℝ) : ℂ) * rieszKernel k y (c + 1)) := by
      rw [rieszKernel]
      have hcongr :
          (∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom (k + 1) ((c : ℂ) + (t : ℂ) * I)) =
            (1 / ((k + 1 : ℕ) : ℂ)) *
              ((∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom k ((c : ℂ) + (t : ℂ) * I)) -
                ((y⁻¹ : ℝ) : ℂ) * ∫ t : ℝ,
                  (y : ℂ) ^ (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I) /
                    rieszDenom k (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
        rw [integral_congr_ae (ae_of_all _ hsplit), integral_const_mul,
          integral_sub hint1 (hint2.const_mul _), integral_const_mul]
      rw [hcongr, rieszKernel, rieszKernel]
      ring
    rw [hrec, ih hc, ih hc1]
    split_ifs with hy1
    · rw [Nat.factorial_succ]
      push_cast
      have hk1_ne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hk_fac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      field_simp [hk1_ne, hk_fac]
      ring
    · simp

/-- Absolute vertical-line integrability of `LSeries a (c + it) * x^(c + it + k) / rieszDenom k (c + it)`
for `k ≥ 1`, `x > 0`, `c > 0`, and `LSeriesSummable a c`. -/
theorem integrable_LSeries_riesz {a : ℕ → ℂ} {k : ℕ} (hk : 1 ≤ k) {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ)) :
    Integrable fun t : ℝ ↦
      LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
        rieszDenom k ((c : ℂ) + (t : ℂ) * I) := by
  let M : ℝ := ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖
  have hcont_L := continuous_LSeries_vertical ha
  have hdenom_ne : ∀ t : ℝ, rieszDenom k ((c : ℂ) + (t : ℂ) * I) ≠ 0 := fun t h0 ↦ by
    have hge := norm_rieszDenom_ge hk hc t
    rw [h0, norm_zero] at hge
    have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
    linarith
  have hpow_cont : Continuous fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) := by
    have hfun : (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k)) =
        fun t : ℝ ↦ (x : ℂ) ^ (k : ℂ) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) := by
      funext t
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
      congr 1
      ring
    rw [hfun]
    exact continuous_const.mul (continuous_ofReal_cpow_add_mul_I hx c)
  have hcont : Continuous fun t : ℝ ↦
      LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
        rieszDenom k ((c : ℂ) + (t : ℂ) * I) :=
    (hcont_L.mul hpow_cont).div (continuous_rieszDenom k c) hdenom_ne
  refine ((integrable_inv_sq_add hc).const_mul (M * x ^ (c + k))).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun t ↦ ?_)
  have hL_le : ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖ ≤ M := by
    have ht_sum : LSeriesSummable a ((c : ℂ) + (t : ℂ) * I) := ha.of_re_le_re (by simp)
    calc
      ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖
          ≤ ∑' n : ℕ, ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ :=
        norm_tsum_le_tsum_norm ht_sum.norm
      _ ≤ M := ht_sum.norm.tsum_le_tsum (fun n ↦ norm_LSeries_term_le_of_re_le_re (by simp) n)
          ha.norm
  have hpow_norm : ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k)‖ = x ^ (c + k) := by
    have hre : ((c : ℂ) + (t : ℂ) * I + (k : ℂ)).re = c + k := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  have hge := norm_rieszDenom_ge hk hc t
  have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
  rw [norm_div, norm_mul, hpow_norm]
  calc
    ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖ * x ^ (c + k) / ‖rieszDenom k ((c : ℂ) + (t : ℂ) * I)‖
        ≤ M * x ^ (c + k) / (c ^ 2 + t ^ 2) := by
      refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hL_le
        (Real.rpow_nonneg hx.le _)) hpos hge
    _ = M * x ^ (c + k) * (c ^ 2 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- **Riesz / Cesàro Smoothed Perron's Formula** (`k ≥ 1`):
`(1 / (2πi)) ∫_{(c)} LSeries a s * x^(s + k) / (s (s + 1) ⋯ (s + k)) ds = ∑_{1 ≤ n ≤ x} a n * (x - n)^k / k!`,
parameterized along `s = c + it` (`c > 0`, `x > 0`, `LSeriesSummable a c`). -/
theorem riesz_perron_formula {a : ℕ → ℂ} {k : ℕ} (hk : 1 ≤ k) {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ)) :
    (1 / (2 * Real.pi : ℂ)) *
        ∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
          rieszDenom k ((c : ℂ) + (t : ℂ) * I) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (((x - n : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun n t ↦
    LSeries.term a ((c : ℂ) + (t : ℂ) * I) n * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
      rieszDenom k ((c : ℂ) + (t : ℂ) * I)
  have hdenom_ne : ∀ t : ℝ, rieszDenom k ((c : ℂ) + (t : ℂ) * I) ≠ 0 := fun t h0 ↦ by
    have hge := norm_rieszDenom_ge hk hc t
    rw [h0, norm_zero] at hge
    have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
    linarith
  have hpow_cont : Continuous fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) := by
    have hfun : (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k)) =
        fun t : ℝ ↦ (x : ℂ) ^ (k : ℂ) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) := by
      funext t
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
      congr 1
      ring
    rw [hfun]
    exact continuous_const.mul (continuous_ofReal_cpow_add_mul_I hx c)
  have hF_cont (n : ℕ) : Continuous (F n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term_zero]
      exact continuous_const
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hterm_cont : Continuous fun t : ℝ ↦ LSeries.term a ((c : ℂ) + (t : ℂ) * I) n := by
        have hfun : (fun t : ℝ ↦ LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) =
            fun t : ℝ ↦ a n * Complex.exp (-Complex.log (n : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
          funext t
          rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
            Complex.cpow_def_of_ne_zero hn0]
          ring_nf
        rw [hfun]
        exact continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))))
      exact (hterm_cont.mul hpow_cont).div (continuous_rieszDenom k c) hdenom_ne
  have hF_norm_le (n : ℕ) (t : ℝ) :
      ‖F n t‖ ≤ ‖LSeries.term a (c : ℂ) n‖ * x ^ (c + k) * (c ^ 2 + t ^ 2)⁻¹ := by
    dsimp [F]
    rw [norm_div, norm_mul]
    have hpow_norm : ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k)‖ = x ^ (c + k) := by
      have hre : ((c : ℂ) + (t : ℂ) * I + (k : ℂ)).re = c + k := by simp
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    have hterm_le : ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ ≤ ‖LSeries.term a (c : ℂ) n‖ :=
      norm_LSeries_term_le_of_re_le_re (by simp) n
    have hge := norm_rieszDenom_ge hk hc t
    have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
    rw [hpow_norm]
    calc
      ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ * x ^ (c + k) / ‖rieszDenom k ((c : ℂ) + (t : ℂ) * I)‖
          ≤ ‖LSeries.term a (c : ℂ) n‖ * x ^ (c + k) / (c ^ 2 + t ^ 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right hterm_le (Real.rpow_nonneg hx.le _)) hpos hge
      _ = ‖LSeries.term a (c : ℂ) n‖ * x ^ (c + k) * (c ^ 2 + t ^ 2)⁻¹ := div_eq_mul_inv _ _
  have hF_int (n : ℕ) : Integrable (F n) volume :=
    ((integrable_inv_sq_add hc).const_mul (‖LSeries.term a (c : ℂ) n‖ * x ^ (c + k))).mono'
      (hF_cont n).aestronglyMeasurable (ae_of_all _ fun t ↦ by
        simpa [mul_assoc] using hF_norm_le n t)
  have hF_sum : Summable fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖ := by
    let I0 : ℝ := ∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹
    have hmaj : Summable fun n : ℕ ↦ (x ^ (c + k) * I0) * ‖LSeries.term a (c : ℂ) n‖ :=
      ha.norm.mul_left _
    refine hmaj.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
    have hconst : (∫ t : ℝ, ‖LSeries.term a (c : ℂ) n‖ * x ^ (c + k) * (c ^ 2 + t ^ 2)⁻¹) =
        (x ^ (c + k) * I0) * ‖LSeries.term a (c : ℂ) n‖ := by
      rw [integral_const_mul]
      dsimp [I0]
      ring
    rw [← hconst]
    exact integral_mono (hF_int n).norm ((integrable_inv_sq_add hc).const_mul _) (hF_norm_le n)
  have hfub := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  have htsum_pt (t : ℝ) :
      (∑' n : ℕ, F n t) =
        LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
          rieszDenom k ((c : ℂ) + (t : ℂ) * I) := by
    have ht_sum : LSeriesSummable a ((c : ℂ) + (t : ℂ) * I) := ha.of_re_le_re (by simp)
    exact ((ht_sum.hasSum.mul_right _).div_const _).tsum_eq
  have hLHS :
      (1 / (2 * Real.pi : ℂ)) *
          ∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
            rieszDenom k ((c : ℂ) + (t : ℂ) * I) =
        ∑' n : ℕ, (1 / (2 * Real.pi : ℂ)) * ∫ t : ℝ, F n t := by
    have heq_int :
        (∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) /
            rieszDenom k ((c : ℂ) + (t : ℂ) * I)) =
          ∑' n : ℕ, ∫ t : ℝ, F n t := by
      rw [integral_congr_ae (ae_of_all _ fun t ↦ (htsum_pt t).symm), hfub]
    rw [heq_int, tsum_mul_left]
  rw [hLHS, finset_sum_Icc_eq_tsum_ite]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [F, LSeries.term_zero]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hcongr :
        (∫ t : ℝ, F n t) =
          (a n * (x : ℂ) ^ (k : ℂ)) * ∫ t : ℝ,
            ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / rieszDenom k ((c : ℂ) + (t : ℂ) * I) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp [F]
      rw [LSeries.term_of_ne_zero hn0]
      have hpow_x : (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + k) =
          (x : ℂ) ^ (k : ℂ) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
        congr 1
        ring
      rw [hpow_x]
      have hdiv := cpow_div_cpow_of_pos hx hn_pos ((c : ℂ) + (t : ℂ) * I)
      rw [Complex.ofReal_natCast] at hdiv
      calc
        a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
              ((x : ℂ) ^ (k : ℂ) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) /
            rieszDenom k ((c : ℂ) + (t : ℂ) * I)
            = (a n * (x : ℂ) ^ (k : ℂ)) *
                (((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) /
                  rieszDenom k ((c : ℂ) + (t : ℂ) * I)) := by ring
        _ = (a n * (x : ℂ) ^ (k : ℂ)) *
              (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
                rieszDenom k ((c : ℂ) + (t : ℂ) * I)) := by rw [hdiv]
    rw [hcongr, show (1 / (2 * Real.pi : ℂ)) * ((a n * (x : ℂ) ^ (k : ℂ)) *
        ∫ t : ℝ, ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          rieszDenom k ((c : ℂ) + (t : ℂ) * I)) =
        (a n * (x : ℂ) ^ (k : ℂ)) * rieszKernel k (x / n) c by rw [rieszKernel]; ring]
    rw [rieszKernel_eq hk (div_pos hx hn_pos) hc]
    have hmem_iff : n ∈ Finset.Icc 1 ⌊x⌋₊ ↔ 1 ≤ x / n := by
      rw [Finset.mem_Icc, one_le_div hn_pos, Nat.le_floor_iff hx.le]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨Nat.pos_of_ne_zero hn0, h⟩
    by_cases hmem : n ∈ Finset.Icc 1 ⌊x⌋₊
    · have hy1 : 1 ≤ x / n := hmem_iff.mp hmem
      simp only [hmem, ↓reduceIte, hy1]
      have hx_pow : (x : ℂ) ^ (k : ℂ) = (((x ^ k : ℝ) : ℂ)) := by
        rw [Complex.cpow_natCast, Complex.ofReal_pow]
      rw [hx_pow, mul_assoc]
      congr 1
      have heq_r : x ^ k * ((1 - (x / n)⁻¹) ^ k / (k.factorial : ℝ)) =
          (x - n) ^ k / (k.factorial : ℝ) := by
        rw [inv_div, mul_div_assoc', ← mul_pow, mul_sub, mul_one,
          mul_div_cancel₀ _ hx.ne']
      rw [← Complex.ofReal_mul, heq_r]
    · have hnot1 : ¬(1 ≤ x / n) := fun h ↦ hmem (hmem_iff.mpr h)
      simp only [hmem, ↓reduceIte, hnot1, mul_zero]

end AnalyticNumberTheory.DirichletSeries
