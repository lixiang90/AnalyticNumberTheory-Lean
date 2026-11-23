import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Finite-Order Entire Functions, Weierstrass Primary Factors, and Canonical Products

This file develops the theory of entire functions of finite order, Weierstrass primary factors,
convergence exponents of zero sequences, and convergence and order bounds for canonical products.

## Main Definitions

* `EntireOrderLe f ρ` : `f` is entire (`Differentiable ℂ f`) and satisfies
  `∀ ε > 0, ∃ C ≥ 0, ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ (ρ + ε))`.
* `HasFiniteOrder f` : `∃ ρ ≥ 0, EntireOrderLe f ρ`.
* `exactOrder f` : infimum of all nonnegative `ρ` with `EntireOrderLe f ρ`.
* `weierstrassPrimaryFactor p z` : the Weierstrass primary factor
  `(1 - z) * Complex.exp (∑ k ∈ Finset.Icc 1 p, z ^ k / k)`.
* `HasFiniteConvergenceExponent a` / `convergenceExponent a` : exponent of convergence of a
  sequence `a : ℕ → ℂ` via summability of `∑ ‖a n‖ ^ (-σ)`.
* `canonicalProduct a p z` : the canonical product `∏' n, weierstrassPrimaryFactor p (z / a n)`.

## Main Theorems

* `entireOrderLe_exactOrder` / `entireOrderLe_iff_exactOrder_le` : attainment and characterization
  of the exact order of a finite-order entire function.
* `EntireOrderLe.add` / `EntireOrderLe.mul` / `EntireOrderLe.deriv` : closure of finite-order
  entire functions under arithmetic operations and complex differentiation.
* `norm_one_sub_weierstrassPrimaryFactor_le` : `‖1 - weierstrassPrimaryFactor p z‖ ≤ 2 * ‖z‖ ^ (p + 1)`
  for `‖z‖ ≤ 1 / 2`.
* `differentiable_canonicalProduct` / `canonicalProduct_eq_zero_iff` /
  `entireOrderLe_canonicalProduct` : entireness, zero set, and order bound for canonical products.
-/

open Complex Filter Metric Real Set
open scoped BigOperators Topology

namespace AnalyticNumberTheory.AnalyticTools.EntireFunctions

/-!
### Section 1: Finite-Order Entire Functions and Exact Order
-/

/-- An entire function `f : ℂ → ℂ` has order at most `ρ` if it is differentiable everywhere on `ℂ`
and for every `ε > 0` there exists `C ≥ 0` such that `‖f z‖ ≤ C * Real.exp (‖z‖ ^ (ρ + ε))` for
all `z : ℂ`. -/
def EntireOrderLe (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  Differentiable ℂ f ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ (ρ + ε))

/-- An entire function `f : ℂ → ℂ` has finite order if `EntireOrderLe f ρ` holds for some
`ρ ≥ 0`. -/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ EntireOrderLe f ρ

/-- The exact order of an entire function `f : ℂ → ℂ`, defined as the infimum of all `ρ ≥ 0`
satisfying `EntireOrderLe f ρ`. -/
noncomputable def exactOrder (f : ℂ → ℂ) : ℝ :=
  sInf {ρ : ℝ | 0 ≤ ρ ∧ EntireOrderLe f ρ}

/-- Every function satisfying `EntireOrderLe f ρ` is complex differentiable everywhere on `ℂ`. -/
lemma EntireOrderLe.differentiable {f : ℂ → ℂ} {ρ : ℝ} (hf : EntireOrderLe f ρ) :
    Differentiable ℂ f :=
  hf.1

/-- Extract the asymptotic bound from `EntireOrderLe f ρ`. -/
lemma EntireOrderLe.norm_le {f : ℂ → ℂ} {ρ ε : ℝ} (hf : EntireOrderLe f ρ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ (ρ + ε)) :=
  hf.2 ε hε

/-- Derive `EntireOrderLe f ρ` from an eventual exponential bound
`‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ (ρ + δ))` for each `δ > 0` and sufficiently large `‖z‖`. -/
theorem entireOrderLe_of_eventually_exp {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f)
    (h : ∀ δ : ℝ, 0 < δ → ∃ A B R : ℝ, 1 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ (ρ + δ))) :
    EntireOrderLe f ρ := by
  refine ⟨hf, fun ε hε ↦ ?_⟩
  obtain ⟨A, B, R, hR, hbound⟩ := h (ε / 2) (half_pos hε)
  let B₁ : ℝ := max B 1
  have hB₁_ge : 1 ≤ B₁ := le_max_right _ _
  let R' : ℝ := max R (B₁ ^ (2 / ε))
  have hR'_ge_one : 1 ≤ R' := le_max_of_le_left hR
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_closedBall (0 : ℂ) R').image_of_continuousOn hf.continuous.continuousOn.norm).bddAbove
  let C : ℝ := max (max A 0) (max M₀ 0)
  refine ⟨C, by positivity, fun z ↦ ?_⟩
  by_cases hz : R' ≤ ‖z‖
  · have hz_R : R ≤ ‖z‖ := (le_max_left _ _).trans hz
    have hz_B : B₁ ^ (2 / ε) ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one (hR'_ge_one.trans hz)
    have hB_le : B ≤ ‖z‖ ^ (ε / 2) := by
      have hrpow := Real.rpow_le_rpow (by positivity) hz_B (half_pos hε).le
      have hexp_eq : (B₁ ^ (2 / ε)) ^ (ε / 2) = B₁ := by
        rw [← Real.rpow_mul (by positivity)]
        have hmul : 2 / ε * (ε / 2) = 1 := by field_simp [hε.ne']
        rw [hmul, Real.rpow_one]
      rw [hexp_eq] at hrpow
      exact (le_max_left B 1).trans hrpow
    have hpow_le : B * ‖z‖ ^ (ρ + ε / 2) ≤ ‖z‖ ^ (ρ + ε) := by
      calc
        B * ‖z‖ ^ (ρ + ε / 2) ≤ ‖z‖ ^ (ε / 2) * ‖z‖ ^ (ρ + ε / 2) :=
          mul_le_mul_of_nonneg_right hB_le (Real.rpow_nonneg hz_pos.le _)
        _ = ‖z‖ ^ (ε / 2 + (ρ + ε / 2)) := (Real.rpow_add hz_pos _ _).symm
        _ = ‖z‖ ^ (ρ + ε) := by congr 1; ring
    calc
      ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ (ρ + ε / 2)) := hbound z hz_R
      _ ≤ max A 0 * Real.exp (‖z‖ ^ (ρ + ε)) :=
        mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr hpow_le) (Real.exp_pos _).le (by positivity)
      _ ≤ C * Real.exp (‖z‖ ^ (ρ + ε)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R' := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (not_le.mp hz).le
    have h1 : ‖f z‖ ≤ C := (hM₀ ⟨z, hz_ball, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
    have h2 : 1 ≤ Real.exp (‖z‖ ^ (ρ + ε)) := by
      rw [Real.one_le_exp_iff]
      exact Real.rpow_nonneg (norm_nonneg z) _
    calc
      ‖f z‖ ≤ C := h1
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp (‖z‖ ^ (ρ + ε)) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Derive `EntireOrderLe f ρ` from a global bound `‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)`. -/
theorem entireOrderLe_of_exp_rpow_le {f : ℂ → ℂ} {ρ A B : ℝ}
    (hf : Differentiable ℂ f) (hA : 0 ≤ A)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) :
    EntireOrderLe f ρ := by
  refine entireOrderLe_of_eventually_exp hf fun δ hδ ↦ ⟨A, max B 0, 1, le_rfl, fun z hz ↦ ?_⟩
  have h1 : B * ‖z‖ ^ ρ ≤ max B 0 * ‖z‖ ^ (ρ + δ) := by
    calc
      B * ‖z‖ ^ ρ ≤ max B 0 * ‖z‖ ^ ρ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg z) _)
      _ ≤ max B 0 * ‖z‖ ^ (ρ + δ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz (by linarith)) (le_max_right _ _)
  exact (hbound z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hA)

/-- Monotonicity of `EntireOrderLe f ρ` in `ρ`. -/
lemma EntireOrderLe.mono {f : ℂ → ℂ} {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ ≤ ρ₂) (hf : EntireOrderLe f ρ₁) :
    EntireOrderLe f ρ₂ := by
  refine entireOrderLe_of_eventually_exp hf.1 fun δ hδ ↦ ?_
  obtain ⟨C, hC, hbound⟩ := hf.2 δ hδ
  refine ⟨C, 1, 1, le_rfl, fun z hz ↦ ?_⟩
  have hpow : ‖z‖ ^ (ρ₁ + δ) ≤ 1 * ‖z‖ ^ (ρ₂ + δ) := by
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  exact (hbound z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) hC)

/-- Any nonnegative order witness establishes `HasFiniteOrder f`. -/
lemma EntireOrderLe.hasFiniteOrder {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : EntireOrderLe f ρ) :
    HasFiniteOrder f :=
  ⟨ρ, hρ, hf⟩

/-- The exact order `exactOrder f` is always nonnegative. -/
lemma exactOrder_nonneg (f : ℂ → ℂ) : 0 ≤ exactOrder f :=
  Real.sInf_nonneg fun _ hx ↦ hx.1

/-- Any `ρ ≥ 0` with `EntireOrderLe f ρ` satisfies `exactOrder f ≤ ρ`. -/
lemma exactOrder_le {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : EntireOrderLe f ρ) :
    exactOrder f ≤ ρ :=
  csInf_le ⟨0, fun _ hx ↦ hx.1⟩ ⟨hρ, hf⟩

/-- A finite-order entire function attains its `exactOrder`: `EntireOrderLe f (exactOrder f)`. -/
theorem entireOrderLe_exactOrder {f : ℂ → ℂ} (hf : HasFiniteOrder f) :
    EntireOrderLe f (exactOrder f) := by
  obtain ⟨ρ₀, hρ₀, hfρ₀⟩ := hf
  have hne : {ρ : ℝ | 0 ≤ ρ ∧ EntireOrderLe f ρ}.Nonempty := ⟨ρ₀, hρ₀, hfρ₀⟩
  refine ⟨hfρ₀.1, fun ε hε ↦ ?_⟩
  have hlt : exactOrder f < exactOrder f + ε / 2 := by linarith
  obtain ⟨ρ₁, ⟨_, hfρ₁⟩, hρ₁_lt⟩ := exists_lt_of_csInf_lt hne hlt
  have hε' : 0 < exactOrder f + ε - ρ₁ := by linarith
  obtain ⟨C, hC, hbound⟩ := hfρ₁.2 (exactOrder f + ε - ρ₁) hε'
  refine ⟨C, hC, fun z ↦ ?_⟩
  have hexp : ρ₁ + (exactOrder f + ε - ρ₁) = exactOrder f + ε := by ring
  simpa [hexp] using hbound z

/-- If `f` has finite order and `exactOrder f ≤ ρ`, then `EntireOrderLe f ρ`. -/
lemma entireOrderLe_of_exactOrder_le {f : ℂ → ℂ} {ρ : ℝ} (hf : HasFiniteOrder f)
    (hρ : exactOrder f ≤ ρ) :
    EntireOrderLe f ρ :=
  (entireOrderLe_exactOrder hf).mono hρ

/-- Characterization of `EntireOrderLe f ρ` in terms of `exactOrder f` for `0 ≤ ρ`
when `HasFiniteOrder f` holds. -/
theorem entireOrderLe_iff_exactOrder_le {f : ℂ → ℂ} {ρ : ℝ} (hf : HasFiniteOrder f) (hρ : 0 ≤ ρ) :
    EntireOrderLe f ρ ↔ exactOrder f ≤ ρ :=
  ⟨exactOrder_le hρ, entireOrderLe_of_exactOrder_le hf⟩

/-!
### Section 2: Standard Examples and Closure Under Arithmetic and Differentiation
-/

/-- Every constant function has order `≤ 0`. -/
lemma entireOrderLe_const (c : ℂ) : EntireOrderLe (fun _ : ℂ ↦ c) 0 :=
  entireOrderLe_of_exp_rpow_le (B := 0) (differentiable_const c) (norm_nonneg c) fun _ ↦ by simp

/-- The zero function has order `≤ 0`. -/
lemma entireOrderLe_zero : EntireOrderLe (0 : ℂ → ℂ) 0 :=
  entireOrderLe_const 0

/-- Constant functions have exact order `0`. -/
lemma exactOrder_const (c : ℂ) : exactOrder (fun _ : ℂ ↦ c) = 0 :=
  le_antisymm (exactOrder_le le_rfl (entireOrderLe_const c)) (exactOrder_nonneg _)

/-- Every monomial `z ↦ z ^ n` has order `≤ 0`. -/
lemma entireOrderLe_pow (n : ℕ) : EntireOrderLe (fun z : ℂ ↦ z ^ n) 0 := by
  refine entireOrderLe_of_eventually_exp (differentiable_id.pow n) fun δ hδ ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) / δ)
  refine ⟨(Nat.factorial m : ℝ), 1, 1, le_rfl, fun z hz ↦ ?_⟩
  have hm_ge : (n : ℝ) ≤ m * δ := ((div_lt_iff₀ hδ).mp hm).le
  have h1 : ‖z‖ ^ n ≤ ‖z‖ ^ (m * δ) := by
    rw [← Real.rpow_natCast ‖z‖ n]
    exact Real.rpow_le_rpow_of_exponent_le hz hm_ge
  have h2 : ‖z‖ ^ (m * δ) = (‖z‖ ^ δ) ^ m := by
    rw [mul_comm, Real.rpow_mul (norm_nonneg z), Real.rpow_natCast]
  have h3 : (‖z‖ ^ δ) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp (‖z‖ ^ δ) :=
    Real.pow_div_factorial_le_exp (‖z‖ ^ δ) (Real.rpow_nonneg (norm_nonneg z) δ) m
  rw [div_le_iff₀ (by positivity)] at h3
  rw [zero_add, one_mul, norm_pow]
  calc
    ‖z‖ ^ n ≤ (‖z‖ ^ δ) ^ m := h1.trans_eq h2
    _ ≤ Real.exp (‖z‖ ^ δ) * (Nat.factorial m : ℝ) := h3
    _ = (Nat.factorial m : ℝ) * Real.exp (‖z‖ ^ δ) := mul_comm _ _

/-- The identity function `z ↦ z` has order `≤ 0`. -/
lemma entireOrderLe_id : EntireOrderLe (fun z : ℂ ↦ z) 0 := by
  simpa using entireOrderLe_pow 1

/-- The complex exponential `Complex.exp` has order `≤ 1`. -/
lemma entireOrderLe_cexp : EntireOrderLe Complex.exp 1 := by
  refine entireOrderLe_of_exp_rpow_le (B := 1) Complex.differentiable_exp zero_le_one fun z ↦ ?_
  rw [Complex.norm_exp, one_mul, Real.rpow_one]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans_eq (one_mul _).symm)

private lemma not_entireOrderLe_cexp_of_lt {ρ₀ : ℝ} (hρ₀ : ρ₀ < 1) :
    ¬ EntireOrderLe Complex.exp ρ₀ := by
  intro hle
  let ε : ℝ := (1 - ρ₀) / 2
  have hε_pos : 0 < ε := by dsimp only [ε]; linarith
  let α : ℝ := ρ₀ + ε
  have hα_lt : α < 1 := by dsimp only [α, ε]; linarith
  let δ : ℝ := 1 - α
  have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
  obtain ⟨C, _, hbound⟩ := hle.2 ε hε_pos
  let C₁ : ℝ := max C 1
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  let x : ℝ := max (2 ^ (1 / δ)) (2 * (Real.log C₁ + 1))
  have hx_ge_pow : 2 ^ (1 / δ) ≤ x := le_max_left _ _
  have hx_ge_log : 2 * (Real.log C₁ + 1) ≤ x := le_max_right _ _
  have h_pow_ge_one : (1 : ℝ) ≤ 2 ^ (1 / δ) :=
    Real.one_le_rpow one_le_two (one_div_nonneg.mpr hδ_pos.le)
  have hx_ge_one : 1 ≤ x := h_pow_ge_one.trans hx_ge_pow
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_ge_one
  have hx_delta : 2 ≤ x ^ δ := by
    have hrpow := Real.rpow_le_rpow (by positivity) hx_ge_pow hδ_pos.le
    have heq : ((2 : ℝ) ^ (1 / δ)) ^ δ = 2 := by
      rw [← Real.rpow_mul zero_le_two, one_div_mul_cancel hδ_pos.ne', Real.rpow_one]
    rwa [heq] at hrpow
  have h_pow : x ^ α ≤ x / 2 := by
    have h1 : 2 * x ^ α ≤ x := by
      calc
        2 * x ^ α ≤ x ^ δ * x ^ α :=
          mul_le_mul_of_nonneg_right hx_delta (Real.rpow_nonneg hx_pos.le α)
        _ = x ^ (δ + α) := (Real.rpow_add hx_pos δ α).symm
        _ = x ^ (1 : ℝ) := by dsimp only [δ]; ring_nf
        _ = x := Real.rpow_one x
    linarith
  have h_C_lt : C < Real.exp (x / 2) := by
    have hlog_lt : Real.log C₁ < x / 2 := by linarith
    calc
      C ≤ C₁ := le_max_left C 1
      _ = Real.exp (Real.log C₁) := (Real.exp_log hC₁_pos).symm
      _ < Real.exp (x / 2) := Real.exp_lt_exp.mpr hlog_lt
  have hbx : Real.exp x ≤ C * Real.exp (x ^ α) := by
    have h1 := hbound (x : ℂ)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, Complex.norm_exp,
      Complex.ofReal_re] at h1
  have h_gt : C * Real.exp (x ^ α) < Real.exp x := by
    calc
      C * Real.exp (x ^ α) < Real.exp (x / 2) * Real.exp (x ^ α) :=
        mul_lt_mul_of_pos_right h_C_lt (Real.exp_pos _)
      _ = Real.exp (x / 2 + x ^ α) := (Real.exp_add _ _).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  exact lt_irrefl _ (hbx.trans_lt h_gt)

/-- The complex exponential `Complex.exp` has exact order `1`. -/
theorem exactOrder_cexp : exactOrder Complex.exp = 1 := by
  refine le_antisymm (exactOrder_le zero_le_one entireOrderLe_cexp) ?_
  by_contra hlt
  push Not at hlt
  exact not_entireOrderLe_cexp_of_lt hlt
    (entireOrderLe_exactOrder ⟨1, zero_le_one, entireOrderLe_cexp⟩)

/-- Negation preserves `EntireOrderLe`. -/
lemma EntireOrderLe.neg {f : ℂ → ℂ} {ρ : ℝ} (hf : EntireOrderLe f ρ) :
    EntireOrderLe (-f) ρ :=
  ⟨hf.1.neg, fun ε hε ↦ by simpa using hf.2 ε hε⟩

/-- Scalar multiplication by a constant preserves `EntireOrderLe`. -/
lemma EntireOrderLe.const_mul {f : ℂ → ℂ} {ρ : ℝ} (c : ℂ) (hf : EntireOrderLe f ρ) :
    EntireOrderLe (fun z ↦ c * f z) ρ := by
  refine ⟨hf.1.const_mul c, fun ε hε ↦ ?_⟩
  obtain ⟨C, hC, hbound⟩ := hf.2 ε hε
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun z ↦ ?_⟩
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm

/-- Right scalar multiplication by a constant preserves `EntireOrderLe`. -/
lemma EntireOrderLe.mul_const {f : ℂ → ℂ} {ρ : ℝ} (c : ℂ) (hf : EntireOrderLe f ρ) :
    EntireOrderLe (fun z ↦ f z * c) ρ := by
  simpa only [mul_comm] using hf.const_mul c

/-- Sum of two entire functions of orders `≤ ρ₁` and `≤ ρ₂` has order `≤ max ρ₁ ρ₂`. -/
theorem EntireOrderLe.add {f g : ℂ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hf : EntireOrderLe f ρ₁) (hg : EntireOrderLe g ρ₂) :
    EntireOrderLe (f + g) (max ρ₁ ρ₂) := by
  have hf' := hf.mono (le_max_left ρ₁ ρ₂)
  have hg' := hg.mono (le_max_right ρ₁ ρ₂)
  refine ⟨hf.1.add hg.1, fun ε hε ↦ ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hf'.2 ε hε
  obtain ⟨C₂, hC₂, h₂⟩ := hg'.2 ε hε
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun z ↦ ?_⟩
  calc
    ‖(f + g) z‖ = ‖f z + g z‖ := rfl
    _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C₁ * Real.exp (‖z‖ ^ (max ρ₁ ρ₂ + ε)) + C₂ * Real.exp (‖z‖ ^ (max ρ₁ ρ₂ + ε)) :=
      add_le_add (h₁ z) (h₂ z)
    _ = (C₁ + C₂) * Real.exp (‖z‖ ^ (max ρ₁ ρ₂ + ε)) := by ring

/-- Difference of two entire functions of orders `≤ ρ₁` and `≤ ρ₂` has order `≤ max ρ₁ ρ₂`. -/
theorem EntireOrderLe.sub {f g : ℂ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hf : EntireOrderLe f ρ₁) (hg : EntireOrderLe g ρ₂) :
    EntireOrderLe (f - g) (max ρ₁ ρ₂) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Product of two entire functions of orders `≤ ρ₁` and `≤ ρ₂` has order `≤ max ρ₁ ρ₂`. -/
theorem EntireOrderLe.mul {f g : ℂ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hf : EntireOrderLe f ρ₁) (hg : EntireOrderLe g ρ₂) :
    EntireOrderLe (f * g) (max ρ₁ ρ₂) := by
  have hf' := hf.mono (le_max_left ρ₁ ρ₂)
  have hg' := hg.mono (le_max_right ρ₁ ρ₂)
  refine entireOrderLe_of_eventually_exp (hf.1.mul hg.1) fun δ hδ ↦ ?_
  obtain ⟨C₁, hC₁, h₁⟩ := hf'.2 δ hδ
  obtain ⟨C₂, hC₂, h₂⟩ := hg'.2 δ hδ
  refine ⟨C₁ * C₂, 2, 1, le_rfl, fun z _ ↦ ?_⟩
  calc
    ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C₁ * Real.exp (‖z‖ ^ (max ρ₁ ρ₂ + δ))) * (C₂ * Real.exp (‖z‖ ^ (max ρ₁ ρ₂ + δ))) :=
      mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) (by positivity)
    _ = (C₁ * C₂) * Real.exp (2 * ‖z‖ ^ (max ρ₁ ρ₂ + δ)) := by
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring

/-- Natural-number power of an entire function of order `≤ ρ` has order `≤ ρ`. -/
lemma EntireOrderLe.pow {f : ℂ → ℂ} {ρ : ℝ} (n : ℕ) (hf : EntireOrderLe f ρ) :
    EntireOrderLe (fun z ↦ f z ^ n) ρ := by
  refine entireOrderLe_of_eventually_exp (hf.1.pow n) fun δ hδ ↦ ?_
  obtain ⟨C, hC, hbound⟩ := hf.2 δ hδ
  refine ⟨C ^ n, (n : ℝ), 1, le_rfl, fun z _ ↦ ?_⟩
  calc
    ‖f z ^ n‖ = ‖f z‖ ^ n := norm_pow _ _
    _ ≤ (C * Real.exp (‖z‖ ^ (ρ + δ))) ^ n := pow_le_pow_left₀ (norm_nonneg _) (hbound z) n
    _ = C ^ n * Real.exp (n * ‖z‖ ^ (ρ + δ)) := by
      rw [mul_pow, ← Real.exp_nat_mul]

/-- Complex differentiation preserves order bounds `EntireOrderLe f ρ` for `0 ≤ ρ`, proved via
Cauchy's integral formula on unit circles. -/
theorem EntireOrderLe.deriv {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : EntireOrderLe f ρ) :
    EntireOrderLe (_root_.deriv f) ρ := by
  have hf_diff : Differentiable ℂ (_root_.deriv f) := Differentiable.deriv hf.1
  refine entireOrderLe_of_eventually_exp hf_diff fun δ hδ ↦ ?_
  obtain ⟨C, hC, hbound⟩ := hf.2 (δ / 2) (half_pos hδ)
  let α : ℝ := ρ + δ / 2
  have hα_pos : 0 < α := by simp only [α]; linarith
  refine ⟨C, 2 ^ α, 1, le_rfl, fun z hz ↦ ?_⟩
  have hcauchy := hf.1.differentiableOn.circleIntegral_one_div_sub_center_pow_smul zero_lt_one 1 (c := z)
  rw [Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one] at hcauchy
  have h_sphere : ∀ w ∈ Metric.sphere z 1,
      ‖(1 / (w - z) ^ (1 + 1)) • f w‖ ≤ C * Real.exp ((‖z‖ + 1) ^ α) := by
    intro w hw
    have hw_dist : ‖w - z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hw_norm : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + 1 := by rw [hw_dist]; ring
    have hw_pow : ‖w‖ ^ α ≤ (‖z‖ + 1) ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) hw_norm hα_pos.le
    simp only [smul_eq_mul, one_div]
    rw [norm_mul, norm_inv, norm_pow, hw_dist, one_pow, inv_one, one_mul]
    exact (hbound w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw_pow) hC)
  have hint := circleIntegral.norm_integral_le_of_norm_le_const zero_le_one h_sphere
  rw [hcauchy, smul_eq_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one] at hint
  have h2pi_pos : 0 < 2 * π := by positivity
  have hderiv_le : ‖_root_.deriv f z‖ ≤ C * Real.exp ((‖z‖ + 1) ^ α) := by
    have hmul : 2 * π * ‖_root_.deriv f z‖ ≤ 2 * π * (C * Real.exp ((‖z‖ + 1) ^ α)) := by
      simpa [mul_one, mul_assoc] using hint
    exact le_of_mul_le_mul_left hmul h2pi_pos
  have hz1 : ‖z‖ + 1 ≤ 2 * ‖z‖ := by linarith
  have hpow1 : (‖z‖ + 1) ^ α ≤ (2 * ‖z‖) ^ α :=
    Real.rpow_le_rpow (by positivity) hz1 hα_pos.le
  rw [Real.mul_rpow zero_le_two (norm_nonneg z)] at hpow1
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hpow2 : ‖z‖ ^ α ≤ ‖z‖ ^ (ρ + δ) :=
    Real.rpow_le_rpow_of_exponent_le hz (by simp only [α]; linarith)
  have hpow_comb : (‖z‖ + 1) ^ α ≤ 2 ^ α * ‖z‖ ^ (ρ + δ) :=
    hpow1.trans (mul_le_mul_of_nonneg_left hpow2 (by positivity))
  exact hderiv_le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow_comb) hC)

/-- Sum of two finite-order entire functions has finite order. -/
lemma HasFiniteOrder.add {f g : ℂ → ℂ} (hf : HasFiniteOrder f) (hg : HasFiniteOrder g) :
    HasFiniteOrder (f + g) := by
  obtain ⟨ρ₁, hρ₁, hf₁⟩ := hf
  obtain ⟨ρ₂, _, hg₂⟩ := hg
  exact ⟨max ρ₁ ρ₂, le_max_of_le_left hρ₁, hf₁.add hg₂⟩

/-- Product of two finite-order entire functions has finite order. -/
lemma HasFiniteOrder.mul {f g : ℂ → ℂ} (hf : HasFiniteOrder f) (hg : HasFiniteOrder g) :
    HasFiniteOrder (f * g) := by
  obtain ⟨ρ₁, hρ₁, hf₁⟩ := hf
  obtain ⟨ρ₂, _, hg₂⟩ := hg
  exact ⟨max ρ₁ ρ₂, le_max_of_le_left hρ₁, hf₁.mul hg₂⟩

/-- Complex derivative of a finite-order entire function has finite order. -/
lemma HasFiniteOrder.deriv {f : ℂ → ℂ} (hf : HasFiniteOrder f) : HasFiniteOrder (deriv f) := by
  obtain ⟨ρ, hρ, hfρ⟩ := hf
  exact ⟨ρ, hρ, hfρ.deriv hρ⟩

/-- Exact order bound for sums: `exactOrder (f + g) ≤ max (exactOrder f) (exactOrder g)`. -/
lemma exactOrder_add_le {f g : ℂ → ℂ} (hf : HasFiniteOrder f) (hg : HasFiniteOrder g) :
    exactOrder (f + g) ≤ max (exactOrder f) (exactOrder g) :=
  exactOrder_le (le_max_of_le_left (exactOrder_nonneg f))
    ((entireOrderLe_exactOrder hf).add (entireOrderLe_exactOrder hg))

/-- Exact order bound for products: `exactOrder (f * g) ≤ max (exactOrder f) (exactOrder g)`. -/
lemma exactOrder_mul_le {f g : ℂ → ℂ} (hf : HasFiniteOrder f) (hg : HasFiniteOrder g) :
    exactOrder (f * g) ≤ max (exactOrder f) (exactOrder g) :=
  exactOrder_le (le_max_of_le_left (exactOrder_nonneg f))
    ((entireOrderLe_exactOrder hf).mul (entireOrderLe_exactOrder hg))

/-- Exact order bound for derivatives: `exactOrder (deriv f) ≤ exactOrder f`. -/
lemma exactOrder_deriv_le {f : ℂ → ℂ} (hf : HasFiniteOrder f) :
    exactOrder (deriv f) ≤ exactOrder f :=
  exactOrder_le (exactOrder_nonneg f) ((entireOrderLe_exactOrder hf).deriv (exactOrder_nonneg f))

/-!
### Section 3: Weierstrass Primary Factors
-/

/-- The Weierstrass primary factor of genus `p : ℕ`:
`E_p(z) := (1 - z) * Complex.exp (∑ k ∈ Finset.Icc 1 p, z ^ k / k)`. -/
noncomputable def weierstrassPrimaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ))

/-- The genus-`0` Weierstrass primary factor simplifies to `1 - z`. -/
@[simp]
lemma weierstrassPrimaryFactor_zero (z : ℂ) : weierstrassPrimaryFactor 0 z = 1 - z := by
  simp [weierstrassPrimaryFactor]

/-- Every Weierstrass primary factor takes the value `1` at `0`. -/
@[simp]
lemma weierstrassPrimaryFactor_at_zero (p : ℕ) : weierstrassPrimaryFactor p 0 = 1 := by
  have hsum : ∑ k ∈ Finset.Icc 1 p, (0 : ℂ) ^ k / (k : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk_pos : k ≠ 0 := by
      simp only [Finset.mem_Icc] at hk
      omega
    simp [zero_pow hk_pos]
  simp [weierstrassPrimaryFactor, hsum]

/-- A Weierstrass primary factor vanishes if and only if its argument equals `1`. -/
@[simp]
lemma weierstrassPrimaryFactor_eq_zero_iff (p : ℕ) (z : ℂ) :
    weierstrassPrimaryFactor p z = 0 ↔ z = 1 := by
  rw [weierstrassPrimaryFactor, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm]

/-- Each Weierstrass primary factor `weierstrassPrimaryFactor p` is entire. -/
lemma differentiable_weierstrassPrimaryFactor (p : ℕ) :
    Differentiable ℂ (weierstrassPrimaryFactor p) := by
  refine ((differentiable_const 1).sub differentiable_id).mul ?_
  have hsum_eq : (fun z : ℂ ↦ ∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ)) =
      ∑ k ∈ Finset.Icc 1 p, fun z : ℂ ↦ z ^ k / (k : ℂ) := by
    ext z
    simp
  refine Differentiable.cexp ?_
  rw [hsum_eq]
  exact Differentiable.sum fun k _ ↦ (differentiable_id.pow k).div_const _

/-- Each Weierstrass primary factor `weierstrassPrimaryFactor p` is continuous. -/
lemma continuous_weierstrassPrimaryFactor (p : ℕ) :
    Continuous (weierstrassPrimaryFactor p) :=
  (differentiable_weierstrassPrimaryFactor p).continuous

private lemma sum_Icc_div_eq_neg_logTaylor (p : ℕ) (z : ℂ) :
    ∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ) = -Complex.logTaylor (p + 1) (-z) := by
  rw [Complex.logTaylor, Finset.sum_range_succ']
  have h0 : ((-1 : ℂ) ^ (0 + 1) * (-z) ^ 0 / ((0 : ℕ) : ℂ)) = 0 := by simp
  rw [h0, add_zero, ← Finset.sum_neg_distrib, eq_comm]
  refine Finset.sum_bij (fun k _ ↦ k + 1)
    (fun k hk ↦ by simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega)
    (fun k₁ _ k₂ _ h ↦ by omega)
    (fun b hb ↦ ⟨b - 1, by simp only [Finset.mem_Icc, Finset.mem_range] at hb ⊢; omega,
      by simp only [Finset.mem_Icc] at hb; omega⟩)
    fun k _ ↦ ?_
  have hneg1 : (-1 : ℂ) ^ (k + 1 + 1) * (-1 : ℂ) ^ (k + 1) = -1 := by
    rw [← pow_add]
    have hpow_eq : (k + 1 + 1 + (k + 1)) = 2 * (k + 1) + 1 := by omega
    rw [hpow_eq, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  calc
    -((-1 : ℂ) ^ (k + 1 + 1) * (-z) ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      = -((-1 : ℂ) ^ (k + 1 + 1) * (-1 : ℂ) ^ (k + 1) * z ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) := by
        rw [mul_assoc, ← mul_pow, neg_one_mul]
    _ = -((-1 : ℂ) * z ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) := by rw [hneg1]
    _ = z ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by ring

/-- **Fundamental Weierstrass primary factor bound**: for all `‖z‖ ≤ 1 / 2` and `p : ℕ`,
`‖1 - weierstrassPrimaryFactor p z‖ ≤ 2 * ‖z‖ ^ (p + 1)`. -/
theorem norm_one_sub_weierstrassPrimaryFactor_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖1 - weierstrassPrimaryFactor p z‖ ≤ 2 * ‖z‖ ^ (p + 1) := by
  by_cases hp : p = 0
  · subst hp
    rw [weierstrassPrimaryFactor_zero, pow_one, sub_sub_cancel]
    linarith [norm_nonneg z]
  · have hp_ge : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    have hz_lt : ‖z‖ < 1 := hz.trans_lt (by norm_num)
    have hneg_lt : ‖-z‖ < 1 := by simpa using hz_lt
    have hslit : 1 - z ∈ Complex.slitPlane := by
      simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hneg_lt
    have hne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero hslit
    have harg : (1 - z).arg ≠ π := by
      intro hpi
      obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hpi
      rcases Complex.mem_slitPlane_iff.mp hslit with hpos | hne_im
      · linarith
      · exact hne_im him
    let w : ℂ := Complex.log (1 - z) + ∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ)
    have hexp_w : Complex.exp w = weierstrassPrimaryFactor p z := by
      rw [weierstrassPrimaryFactor, Complex.exp_add, Complex.exp_log hne]
    have hw_eq : w = -(Complex.log (1 - z)⁻¹ + Complex.logTaylor (p + 1) (-z)) := by
      dsimp only [w]
      rw [Complex.log_inv _ harg, sum_Icc_div_eq_neg_logTaylor]
      ring
    have hlog_bound := Complex.norm_log_one_sub_inv_add_logTaylor_neg_le p hz_lt
    rw [← norm_neg, ← hw_eq] at hlog_bound
    have hw_norm_le : ‖w‖ ≤ ‖z‖ ^ (p + 1) := by
      have h1 : (1 - ‖z‖)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        linarith
      have h2 : (2 : ℝ) ≤ (p : ℝ) + 1 := by
        exact_mod_cast (by omega : 2 ≤ p + 1)
      have h3 : (1 - ‖z‖)⁻¹ / ((p : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h1.trans h2
      calc
        ‖w‖ ≤ ‖z‖ ^ (p + 1) * (1 - ‖z‖)⁻¹ / ((p : ℝ) + 1) := hlog_bound
        _ = ‖z‖ ^ (p + 1) * ((1 - ‖z‖)⁻¹ / ((p : ℝ) + 1)) := by ring
        _ ≤ ‖z‖ ^ (p + 1) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ‖z‖ ^ (p + 1) := mul_one _
    have hw_le_one : ‖w‖ ≤ 1 := by
      have hpow_le : ‖z‖ ^ (p + 1) ≤ (1 / 2 : ℝ) ^ (p + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hz (p + 1)
      have hhalf_le : (1 / 2 : ℝ) ^ (p + 1) ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      exact hw_norm_le.trans (hpow_le.trans hhalf_le)
    have hexp_bound := Complex.norm_exp_sub_one_sub_id_le hw_le_one
    have hexp_split : Complex.exp w - 1 = (Complex.exp w - 1 - w) + w := by ring
    rw [norm_sub_rev, ← hexp_w, hexp_split]
    calc
      ‖(Complex.exp w - 1 - w) + w‖
        ≤ ‖Complex.exp w - 1 - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ := add_le_add hexp_bound le_rfl
      _ ≤ 1 * ‖w‖ + ‖w‖ := by
        have hw_sq : ‖w‖ ^ 2 ≤ 1 * ‖w‖ := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right hw_le_one (norm_nonneg w)
        exact add_le_add hw_sq le_rfl
      _ = 2 * ‖w‖ := by ring
      _ ≤ 2 * ‖z‖ ^ (p + 1) := mul_le_mul_of_nonneg_left hw_norm_le zero_le_two

/-- Variant of `norm_one_sub_weierstrassPrimaryFactor_le` with `weierstrassPrimaryFactor p z - 1`. -/
lemma norm_weierstrassPrimaryFactor_sub_one_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassPrimaryFactor p z - 1‖ ≤ 2 * ‖z‖ ^ (p + 1) := by
  rw [norm_sub_rev]
  exact norm_one_sub_weierstrassPrimaryFactor_le p hz

/-- Exponential upper bound on `‖weierstrassPrimaryFactor p z‖` for `‖z‖ ≤ 1 / 2`. -/
lemma norm_weierstrassPrimaryFactor_le_exp_of_norm_le_half (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassPrimaryFactor p z‖ ≤ Real.exp (2 * ‖z‖ ^ (p + 1)) := by
  have h1 : ‖weierstrassPrimaryFactor p z‖ ≤ 1 + ‖weierstrassPrimaryFactor p z - 1‖ := by
    have hsplit : weierstrassPrimaryFactor p z = 1 + (weierstrassPrimaryFactor p z - 1) := by ring
    calc
      ‖weierstrassPrimaryFactor p z‖ = ‖1 + (weierstrassPrimaryFactor p z - 1)‖ := by rw [← hsplit]
      _ ≤ ‖(1 : ℂ)‖ + ‖weierstrassPrimaryFactor p z - 1‖ := norm_add_le _ _
      _ = 1 + ‖weierstrassPrimaryFactor p z - 1‖ := by simp
  have h2 : 1 + ‖weierstrassPrimaryFactor p z - 1‖ ≤ 1 + 2 * ‖z‖ ^ (p + 1) := by
    linarith [norm_weierstrassPrimaryFactor_sub_one_le p hz]
  have h3 : 1 + 2 * ‖z‖ ^ (p + 1) ≤ Real.exp (2 * ‖z‖ ^ (p + 1)) := by
    linarith [Real.add_one_le_exp (2 * ‖z‖ ^ (p + 1))]
  exact h1.trans (h2.trans h3)

/-- Global coarse norm bound for `weierstrassPrimaryFactor p z`. -/
lemma norm_weierstrassPrimaryFactor_le (p : ℕ) (z : ℂ) :
    ‖weierstrassPrimaryFactor p z‖ ≤
      (1 + ‖z‖) * Real.exp (∑ k ∈ Finset.Icc 1 p, ‖z‖ ^ k / (k : ℝ)) := by
  rw [weierstrassPrimaryFactor, norm_mul, Complex.norm_exp]
  have h1 : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by simp
  have hre : (∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ)).re ≤
      ∑ k ∈ Finset.Icc 1 p, ‖z‖ ^ k / (k : ℝ) := by
    calc
      (∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ)).re
        ≤ ‖∑ k ∈ Finset.Icc 1 p, z ^ k / (k : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ∑ k ∈ Finset.Icc 1 p, ‖z ^ k / (k : ℂ)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.Icc 1 p, ‖z‖ ^ k / (k : ℝ) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [norm_div, norm_pow, Complex.norm_natCast]
  exact mul_le_mul h1 (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)

private lemma one_add_rpow_le_exp {s : ℝ} (hs : 0 < s) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ u : ℝ, 1 / 2 ≤ u → 1 + u ≤ Real.exp (C₀ * u ^ s) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (1 / s)
  have hm_ge_one : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, Nat.cast_zero] at hm
    have hpos : 0 < 1 / s := one_div_pos.mpr hs
    linarith
  have hms : 1 ≤ (m : ℝ) * s := (div_le_iff₀ hs).mp hm
  let C₀ : ℝ := max (m : ℝ) (Real.log 2 * 2 ^ s)
  have hC₀_pos : 0 < C₀ := lt_max_of_lt_left (by exact_mod_cast hm_ge_one)
  refine ⟨C₀, hC₀_pos, fun u hu ↦ ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le (by norm_num) hu
  by_cases hu1 : 1 ≤ u
  · have h_step1 : u ≤ (u ^ s) ^ m := by
      calc
        u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
        _ ≤ u ^ ((m : ℝ) * s) := Real.rpow_le_rpow_of_exponent_le hu1 hms
        _ = (u ^ s) ^ m := by
          rw [mul_comm, Real.rpow_mul hu_pos.le, Real.rpow_natCast]
    have h_step2 : ∀ (n : ℕ) (x : ℝ), 0 ≤ x → 1 ≤ n → 1 + x ^ n ≤ (1 + x) ^ n := by
      intro n x hx hn
      induction n with
      | zero => omega
      | succ k ih =>
        rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
        · simp
        · have hk1 := ih hk_pos
          have hx_pow : 0 ≤ x ^ k := pow_nonneg hx k
          calc
            1 + x ^ (k + 1) ≤ 1 + x ^ (k + 1) + x ^ k + x := by linarith
            _ = (1 + x ^ k) * (1 + x) := by ring
            _ ≤ (1 + x) ^ k * (1 + x) := mul_le_mul_of_nonneg_right hk1 (by linarith)
            _ = (1 + x) ^ (k + 1) := (pow_succ (1 + x) k).symm
    have h1 : 1 + u ≤ (1 + u ^ s) ^ m := by
      have h2 := h_step2 m (u ^ s) (Real.rpow_nonneg hu_pos.le s) hm_ge_one
      linarith [h_step1, h2]
    have h2 : (1 + u ^ s) ^ m ≤ (Real.exp (u ^ s)) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (u ^ s)]) m
    rw [← Real.exp_nat_mul] at h2
    have h3 : (m : ℝ) * u ^ s ≤ C₀ * u ^ s :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu_pos.le s)
    exact h1.trans (h2.trans (Real.exp_le_exp.mpr h3))
  · have hu_le : u ≤ 1 := (not_le.mp hu1).le
    have h1 : 1 + u ≤ 2 := by linarith
    have h2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log zero_lt_two).symm
    have hpow_half : (1 / 2 : ℝ) ^ s ≤ u ^ s := Real.rpow_le_rpow (by norm_num) hu hs.le
    have h_mul : 1 ≤ 2 ^ s * u ^ s := by
      have heq : (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s = 1 := by
        rw [← Real.mul_rpow zero_le_two (by norm_num)]
        norm_num
      calc
        1 = 2 ^ s * (1 / 2 : ℝ) ^ s := heq.symm
        _ ≤ 2 ^ s * u ^ s := mul_le_mul_of_nonneg_left hpow_half (by positivity)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : Real.log 2 ≤ (Real.log 2 * 2 ^ s) * u ^ s := by
      calc
        Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
        _ ≤ Real.log 2 * (2 ^ s * u ^ s) := mul_le_mul_of_nonneg_left h_mul hlog2_pos.le
        _ = (Real.log 2 * 2 ^ s) * u ^ s := by ring
    have h4 : (Real.log 2 * 2 ^ s) * u ^ s ≤ C₀ * u ^ s :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu_pos.le s)
    exact h1.trans (h2.symm ▸ Real.exp_le_exp.mpr (h3.trans h4))

/-- **Global polynomial-exponential primary factor bound**: for any `p : ℕ` and `s : ℝ` with
`0 < s` and `(p : ℝ) ≤ s ≤ (p : ℝ) + 1`, there exists `C > 0` such that
`‖weierstrassPrimaryFactor p z‖ ≤ Real.exp (C * ‖z‖ ^ s)` for every `z : ℂ`. -/
theorem norm_weierstrassPrimaryFactor_le_exp (p : ℕ) {s : ℝ}
    (hs : 0 < s) (hps : (p : ℝ) ≤ s) (hsp : s ≤ (p : ℝ) + 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖weierstrassPrimaryFactor p z‖ ≤ Real.exp (C * ‖z‖ ^ s) := by
  obtain ⟨C₀, hC₀_pos, h1u⟩ := one_add_rpow_le_exp hs
  let C₁ : ℝ := ∑ k ∈ Finset.Icc 1 p, (2 : ℝ) ^ (s - k) / (k : ℝ)
  have hC₁_nonneg : 0 ≤ C₁ := Finset.sum_nonneg fun k _ ↦ by positivity
  let C : ℝ := max 2 (C₀ + C₁)
  refine ⟨C, lt_max_of_lt_left zero_lt_two, fun z ↦ ?_⟩
  by_cases hz : ‖z‖ ≤ 1 / 2
  · have h_half := norm_weierstrassPrimaryFactor_le_exp_of_norm_le_half p hz
    have hpow : ‖z‖ ^ (p + 1) ≤ ‖z‖ ^ s := by
      rcases eq_or_lt_of_le (norm_nonneg z) with hz0 | hz_pos
      · rw [← hz0, zero_pow (Nat.succ_ne_zero p), Real.zero_rpow hs.ne']
      · rw [← Real.rpow_natCast ‖z‖ (p + 1), Nat.cast_add, Nat.cast_one]
        exact Real.rpow_le_rpow_of_exponent_ge hz_pos (hz.trans (by norm_num)) hsp
    have h_exp : 2 * ‖z‖ ^ (p + 1) ≤ C * ‖z‖ ^ s :=
      (mul_le_mul_of_nonneg_left hpow zero_le_two).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg z) s))
    exact h_half.trans (Real.exp_le_exp.mpr h_exp)
  · have hz_ge : 1 / 2 ≤ ‖z‖ := (not_le.mp hz).le
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz_ge
    have h_coarse := norm_weierstrassPrimaryFactor_le p z
    have h_one_z : 1 + ‖z‖ ≤ Real.exp (C₀ * ‖z‖ ^ s) := h1u ‖z‖ hz_ge
    have h_sum_le : ∑ k ∈ Finset.Icc 1 p, ‖z‖ ^ k / (k : ℝ) ≤ C₁ * ‖z‖ ^ s := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hk_le : (k : ℝ) ≤ p := by
        simp only [Finset.mem_Icc] at hk
        exact_mod_cast hk.2
      have hsk : 0 ≤ s - k := by linarith
      have h_half_pow : (1 / 2 : ℝ) ^ (s - k) ≤ ‖z‖ ^ (s - k) :=
        Real.rpow_le_rpow (by norm_num) hz_ge hsk
      have h_pow_k : ‖z‖ ^ k ≤ 2 ^ (s - k) * ‖z‖ ^ s := by
        have hmul_two : (2 : ℝ) ^ (s - k) * (1 / 2 : ℝ) ^ (s - k) = 1 := by
          rw [← Real.mul_rpow zero_le_two (by norm_num)]
          norm_num
        calc
          ‖z‖ ^ k = ‖z‖ ^ (k : ℝ) * 1 := by rw [Real.rpow_natCast, mul_one]
          _ = ‖z‖ ^ (k : ℝ) * (2 ^ (s - k) * (1 / 2 : ℝ) ^ (s - k)) := by rw [hmul_two]
          _ ≤ ‖z‖ ^ (k : ℝ) * (2 ^ (s - k) * ‖z‖ ^ (s - k)) := by
            gcongr
          _ = 2 ^ (s - k) * (‖z‖ ^ (k : ℝ) * ‖z‖ ^ (s - k)) := by ring
          _ = 2 ^ (s - k) * ‖z‖ ^ s := by
            rw [← Real.rpow_add hz_pos]
            congr 2
            ring
      calc
        ‖z‖ ^ k / (k : ℝ) ≤ (2 ^ (s - k) * ‖z‖ ^ s) / (k : ℝ) :=
          div_le_div_of_nonneg_right h_pow_k (Nat.cast_nonneg k)
        _ = ((2 : ℝ) ^ (s - k) / (k : ℝ)) * ‖z‖ ^ s := by ring
    calc
      ‖weierstrassPrimaryFactor p z‖
        ≤ (1 + ‖z‖) * Real.exp (∑ k ∈ Finset.Icc 1 p, ‖z‖ ^ k / (k : ℝ)) := h_coarse
      _ ≤ Real.exp (C₀ * ‖z‖ ^ s) * Real.exp (C₁ * ‖z‖ ^ s) :=
        mul_le_mul h_one_z (Real.exp_le_exp.mpr h_sum_le) (Real.exp_pos _).le (by positivity)
      _ = Real.exp ((C₀ + C₁) * ‖z‖ ^ s) := by
        rw [← Real.exp_add, add_mul]
      _ ≤ Real.exp (C * ‖z‖ ^ s) := by
        refine Real.exp_le_exp.mpr ?_
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg z) s)

/-- Each Weierstrass primary factor `weierstrassPrimaryFactor p` has order at most `p`. -/
theorem entireOrderLe_weierstrassPrimaryFactor (p : ℕ) :
    EntireOrderLe (weierstrassPrimaryFactor p) (p : ℝ) := by
  by_cases hp : p = 0
  · subst hp
    have heq : weierstrassPrimaryFactor 0 = (fun _ : ℂ ↦ 1) - (fun z : ℂ ↦ z) := by
      ext z; simp
    rw [heq, Nat.cast_zero]
    simpa using (entireOrderLe_const 1).sub entireOrderLe_id
  · have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
    obtain ⟨C, _, hbound⟩ :=
      norm_weierstrassPrimaryFactor_le_exp p (s := (p : ℝ)) hp_pos le_rfl (by linarith)
    exact entireOrderLe_of_exp_rpow_le (differentiable_weierstrassPrimaryFactor p) zero_le_one
      fun z ↦ by simpa using hbound z

/-!
### Section 4: Exponent of Convergence and Canonical Products
-/

/-- A sequence `a : ℕ → ℂ` has finite exponent of convergence if `∑ ‖a n‖ ^ (-σ)` converges
for some `σ > 0`. -/
def HasFiniteConvergenceExponent (a : ℕ → ℂ) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ Summable (fun n : ℕ ↦ ‖a n‖ ^ (-σ : ℝ))

/-- The exponent of convergence of a sequence `a : ℕ → ℂ`, defined as the infimum of all
`σ ≥ 0` such that `Summable (fun n ↦ ‖a n‖ ^ (-σ))`. -/
noncomputable def convergenceExponent (a : ℕ → ℂ) : ℝ :=
  sInf {σ : ℝ | 0 ≤ σ ∧ Summable (fun n : ℕ ↦ ‖a n‖ ^ (-σ : ℝ))}

/-- The exponent of convergence is always nonnegative. -/
lemma convergenceExponent_nonneg (a : ℕ → ℂ) : 0 ≤ convergenceExponent a :=
  Real.sInf_nonneg fun _ hx ↦ hx.1

/-- Any `σ ≥ 0` for which `∑ ‖a n‖ ^ (-σ)` converges bounds `convergenceExponent a` above. -/
lemma convergenceExponent_le {a : ℕ → ℂ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hs : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-σ : ℝ))) :
    convergenceExponent a ≤ σ :=
  csInf_le ⟨0, fun _ hx ↦ hx.1⟩ ⟨hσ, hs⟩

private lemma summable_of_nonneg_of_le_eventually {f g : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hfg : ∀ᶠ n in atTop, f n ≤ g n) (hg : Summable g) :
    Summable f := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfg
  have h_shift : Summable fun k : ℕ ↦ f (k + N) :=
    Summable.of_nonneg_of_le (fun k ↦ hf (k + N)) (fun k ↦ hN (k + N) (by omega))
      ((summable_nat_add_iff N).mpr hg)
  exact (summable_nat_add_iff N).mp h_shift

/-- If `∀ n, a n ≠ 0` and `∑ ‖a n‖ ^ (-s)` converges for some `s > 0`, then `‖a n‖ → ∞`. -/
theorem tendsto_norm_atTop_of_summable {a : ℕ → ℂ} {s : ℝ} (ha : ∀ n, a n ≠ 0) (hs : 0 < s)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s : ℝ))) :
    Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop := by
  have htend_zero : Tendsto (fun n : ℕ ↦ ‖a n‖ ^ (-s : ℝ)) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  rw [Filter.tendsto_atTop]
  intro M
  let M' : ℝ := max M 1
  have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ_pos : 0 < M' ^ (-s) := Real.rpow_pos_of_pos hM'_pos _
  have hev := htend_zero.eventually (Iio_mem_nhds hδ_pos)
  refine hev.mono fun n hn ↦ ?_
  have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
  have hle : M' ≤ ‖a n‖ := by
    by_contra hlt
    push Not at hlt
    have hbad : M' ^ (-s) ≤ ‖a n‖ ^ (-s) := Real.rpow_le_rpow_of_nonpos han_pos hlt.le (by linarith)
    linarith
  exact (le_max_left M 1).trans hle

/-- Monotonicity of summability for `∑ ‖a n‖ ^ (-σ)` when `∀ n, a n ≠ 0` and `0 < s₁ ≤ s₂`. -/
theorem summable_norm_rpow_neg_of_le {a : ℕ → ℂ} {s₁ s₂ : ℝ} (ha : ∀ n, a n ≠ 0)
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s₁ : ℝ))) :
    Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s₂ : ℝ)) := by
  have htend := tendsto_norm_atTop_of_summable ha hs₁ hsum
  have hev : ∀ᶠ n : ℕ in atTop, ‖a n‖ ^ (-s₂ : ℝ) ≤ ‖a n‖ ^ (-s₁ : ℝ) := by
    refine (htend.eventually_ge_atTop (1 : ℝ)).mono fun n hn ↦ ?_
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  exact summable_of_nonneg_of_le_eventually (fun n ↦ Real.rpow_nonneg (norm_nonneg _) _) hev hsum

/-- For every `σ > convergenceExponent a`, the series `∑ ‖a n‖ ^ (-σ)` converges
whenever `∀ n, a n ≠ 0` and `HasFiniteConvergenceExponent a`. -/
theorem summable_norm_rpow_neg_of_convergenceExponent_lt {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfin : HasFiniteConvergenceExponent a) {σ : ℝ} (hσ : convergenceExponent a < σ) :
    Summable (fun n : ℕ ↦ ‖a n‖ ^ (-σ : ℝ)) := by
  obtain ⟨σ₀, hσ₀_pos, hσ₀_sum⟩ := hfin
  have hne : {s : ℝ | 0 ≤ s ∧ Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s : ℝ))}.Nonempty :=
    ⟨σ₀, hσ₀_pos.le, hσ₀_sum⟩
  obtain ⟨s₁, ⟨hs₁_nonneg, hs₁_sum⟩, hs₁_lt⟩ := exists_lt_of_csInf_lt hne hσ
  have hs₁_pos : 0 < s₁ := by
    refine lt_of_le_of_ne hs₁_nonneg ?_
    intro hzero
    subst hzero
    have hone : (fun n : ℕ ↦ ‖a n‖ ^ (-(0 : ℝ))) = fun _ ↦ (1 : ℝ) := by
      ext n
      simp [Real.rpow_zero]
    rw [hone] at hs₁_sum
    exact Set.infinite_univ (Set.Finite.of_summable_const (b := (1 : ℝ)) (by norm_num) hs₁_sum)
  exact summable_norm_rpow_neg_of_le ha hs₁_pos hs₁_lt.le hs₁_sum

/-- The Weierstrass canonical product of genus `p : ℕ` associated with the sequence `a : ℕ → ℂ`:
`canonicalProduct a p z = ∏' n, weierstrassPrimaryFactor p (z / a n)`. -/
noncomputable def canonicalProduct (a : ℕ → ℂ) (p : ℕ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassPrimaryFactor p (z / a n)

/-- Every canonical product takes the value `1` at `0`. -/
@[simp]
lemma canonicalProduct_at_zero (a : ℕ → ℂ) (p : ℕ) : canonicalProduct a p 0 = 1 := by
  simp [canonicalProduct]

/-- **Locally uniform convergence on every ball** for a canonical product when `∀ n, a n ≠ 0` and
`∑ ‖a n‖ ^ (-(p + 1 : ℝ))` converges. -/
theorem hasProdLocallyUniformlyOn_canonicalProduct {a : ℕ → ℂ} {p : ℕ}
    (ha : ∀ n, a n ≠ 0) (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)))) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassPrimaryFactor p (z / a n))
      (canonicalProduct a p) (Metric.ball (0 : ℂ) R) := by
  let R₁ : ℝ := max R 1
  have hR₁_pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp_pos : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos p)
  have htend := tendsto_norm_atTop_of_summable ha hp_pos hsum
  let f : ℕ → ℂ → ℂ := fun n z ↦ weierstrassPrimaryFactor p (z / a n) - 1
  let u : ℕ → ℝ := fun n ↦ (2 * R₁ ^ (p + 1)) * ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))
  have hu : Summable u := hsum.mul_left _
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f n z‖ ≤ u n := by
    refine (htend.eventually_ge_atTop (2 * R₁)).mono fun n hn z hz ↦ ?_
    have hz_norm : ‖z‖ < R₁ := by
      have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
      exact hzR.trans_le (le_max_left _ _)
    have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
    have hdiv_le : ‖z / a n‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ han_pos]
      linarith [hz_norm]
    have hfac := norm_weierstrassPrimaryFactor_sub_one_le p hdiv_le
    dsimp only [f, u]
    refine hfac.trans ?_
    rw [norm_div, div_pow, div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz_norm.le (p + 1)) ?_
      (by positivity) (by positivity)
    rw [← Real.rpow_natCast ‖a n‖ (p + 1), Real.rpow_neg (norm_nonneg _)]
  have hcts : ∀ n, ContinuousOn (f n) (Metric.ball (0 : ℂ) R) := fun n ↦
    ((continuous_weierstrassPrimaryFactor p).comp (continuous_id.div_const (a n))).sub
      continuous_const |>.continuousOn
  have hprod := hu.hasProdLocallyUniformlyOn_nat_one_add isOpen_ball hbound hcts
  simp only [f, add_sub_cancel] at hprod
  exact hprod

/-- Pointwise multipliability of the canonical product factors when `∀ n, a n ≠ 0` and
`∑ ‖a n‖ ^ (-(p + 1 : ℝ))` converges. -/
theorem multipliable_canonicalProduct {a : ℕ → ℂ} {p : ℕ}
    (ha : ∀ n, a n ≠ 0) (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)))) (z : ℂ) :
    Multipliable (fun n : ℕ ↦ weierstrassPrimaryFactor p (z / a n)) := by
  have hprod := hasProdLocallyUniformlyOn_canonicalProduct ha hsum (‖z‖ + 1)
  have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    simp [Metric.mem_ball, dist_zero_right]
  exact ⟨canonicalProduct a p z, hprod.hasProd hz⟩

/-- **Entireness of canonical products**: if `∀ n, a n ≠ 0` and `∑ ‖a n‖ ^ (-(p + 1 : ℝ))`
converges, then `canonicalProduct a p` is complex differentiable everywhere on `ℂ`. -/
theorem differentiable_canonicalProduct {a : ℕ → ℂ} {p : ℕ}
    (ha : ∀ n, a n ≠ 0) (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)))) :
    Differentiable ℂ (canonicalProduct a p) := by
  intro z
  let R : ℝ := ‖z‖ + 1
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simp [R, Metric.mem_ball, dist_zero_right]
  have hprod := hasProdLocallyUniformlyOn_canonicalProduct ha hsum R
  have htend : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (w : ℂ) ↦ ∏ j ∈ Finset.range n, weierstrassPrimaryFactor p (w / a j))
      (canonicalProduct a p) atTop (Metric.ball (0 : ℂ) R) :=
    hprod.tendstoLocallyUniformlyOn_finsetRange
  have hF : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ
        (fun w : ℂ ↦ ∏ j ∈ Finset.range n, weierstrassPrimaryFactor p (w / a j))
        (Metric.ball (0 : ℂ) R) := by
    refine Filter.Eventually.of_forall fun n ↦ ?_
    refine Differentiable.differentiableOn ?_
    induction n with
    | zero => simp [differentiable_const]
    | succ k ih =>
      simp only [Finset.prod_range_succ]
      exact ih.mul ((differentiable_weierstrassPrimaryFactor p).comp (differentiable_id.div_const _))
  have hdiffOn : DifferentiableOn ℂ (canonicalProduct a p) (Metric.ball (0 : ℂ) R) :=
    htend.differentiableOn hF isOpen_ball
  exact hdiffOn.differentiableAt (isOpen_ball.mem_nhds hz)

/-- **Zero characterization for canonical products**: if `∀ n, a n ≠ 0` and
`∑ ‖a n‖ ^ (-(p + 1 : ℝ))` converges, then `canonicalProduct a p z = 0` if and only if
`z = a n` for some `n : ℕ`. -/
theorem canonicalProduct_eq_zero_iff {a : ℕ → ℂ} {p : ℕ}
    (ha : ∀ n, a n ≠ 0) (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)))) (z : ℂ) :
    canonicalProduct a p z = 0 ↔ ∃ n : ℕ, z = a n := by
  have hm := multipliable_canonicalProduct ha hsum z
  constructor
  · intro hzero
    by_contra hnone
    push Not at hnone
    have hf_ne : ∀ n : ℕ, 1 + (weierstrassPrimaryFactor p (z / a n) - 1) ≠ 0 := by
      intro n
      rw [add_sub_cancel, ne_eq, weierstrassPrimaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha n)]
      exact hnone n
    have hp_pos : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos p)
    have htend := tendsto_norm_atTop_of_summable ha hp_pos hsum
    have hev : ∀ᶠ n : ℕ in atTop,
        ‖weierstrassPrimaryFactor p (z / a n) - 1‖ ≤
          (2 * ‖z‖ ^ (p + 1)) * ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)) := by
      refine (htend.eventually_ge_atTop (2 * max ‖z‖ 1)).mono fun n hn ↦ ?_
      have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
      have hdiv_le : ‖z / a n‖ ≤ 1 / 2 := by
        rw [norm_div, div_le_iff₀ han_pos]
        linarith [le_max_left ‖z‖ 1]
      refine (norm_weierstrassPrimaryFactor_sub_one_le p hdiv_le).trans ?_
      rw [norm_div, div_pow, div_eq_mul_inv, ← Real.rpow_natCast ‖a n‖ (p + 1),
        Real.rpow_neg (norm_nonneg _)]
      ring_nf
      rfl
    have hsum_diff : Summable (fun n : ℕ ↦ ‖weierstrassPrimaryFactor p (z / a n) - 1‖) :=
      summable_of_nonneg_of_le_eventually (fun _ ↦ norm_nonneg _) hev (hsum.mul_left _)
    have hne0 := tprod_one_add_ne_zero_of_summable hf_ne hsum_diff
    simp only [add_sub_cancel] at hne0
    exact hne0 hzero
  · rintro ⟨n, rfl⟩
    have h0 : weierstrassPrimaryFactor p (a n / a n) = 0 := by
      rw [div_self (ha n), weierstrassPrimaryFactor_eq_zero_iff]
    have htend := hm.hasProd.tendsto_prod_nat
    have hev_zero : ∀ᶠ N : ℕ in atTop,
        (∏ j ∈ Finset.range N, weierstrassPrimaryFactor p (a n / a j)) = 0 := by
      refine (Filter.eventually_ge_atTop (n + 1)).mono fun N hN ↦ ?_
      exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega)) h0
    exact tendsto_nhds_unique htend (tendsto_const_nhds.congr' (hev_zero.mono fun _ h ↦ h.symm))

/-- **Quantitative exponential growth bound for canonical products**: if `∀ n, a n ≠ 0`,
`0 < s`, `(p : ℝ) ≤ s ≤ (p : ℝ) + 1`, and `∑ ‖a n‖ ^ (-s)` converges, then there exists `C > 0`
such that `‖canonicalProduct a p z‖ ≤ Real.exp (C * (∑' n, ‖a n‖ ^ (-s)) * ‖z‖ ^ s)` for all
`z : ℂ`. -/
theorem norm_canonicalProduct_le_exp {a : ℕ → ℂ} {p : ℕ} {s : ℝ}
    (ha : ∀ n, a n ≠ 0) (hs : 0 < s) (hps : (p : ℝ) ≤ s) (hsp : s ≤ (p : ℝ) + 1)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖canonicalProduct a p z‖ ≤ Real.exp (C * (∑' n : ℕ, ‖a n‖ ^ (-s : ℝ)) * ‖z‖ ^ s) := by
  have hsum_p1 : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))) := by
    have hle : s ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast hsp
    exact summable_norm_rpow_neg_of_le ha hs hle hsum
  obtain ⟨C, hC_pos, hfac⟩ := norm_weierstrassPrimaryFactor_le_exp p hs hps hsp
  refine ⟨C, hC_pos, fun z ↦ ?_⟩
  have hm := multipliable_canonicalProduct ha hsum_p1 z
  rw [canonicalProduct, hm.norm_tprod]
  have hm_norm : Multipliable (fun n : ℕ ↦ ‖weierstrassPrimaryFactor p (z / a n)‖) := hm.norm
  have htend_prod : Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.range N, ‖weierstrassPrimaryFactor p (z / a n)‖)
      atTop (𝓝 (∏' n : ℕ, ‖weierstrassPrimaryFactor p (z / a n)‖)) :=
    hm_norm.hasProd.tendsto_prod_nat
  have hsum_terms : Summable (fun n : ℕ ↦ C * ‖z / a n‖ ^ s) := by
    have heq : (fun n : ℕ ↦ C * ‖z / a n‖ ^ s) = fun n ↦ (C * ‖z‖ ^ s) * ‖a n‖ ^ (-s : ℝ) := by
      ext n
      rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _), div_eq_mul_inv,
        ← Real.rpow_neg (norm_nonneg _)]
      ring
    rw [heq]
    exact hsum.mul_left _
  have htsum_eq : ∑' n : ℕ, C * ‖z / a n‖ ^ s = C * (∑' n : ℕ, ‖a n‖ ^ (-s : ℝ)) * ‖z‖ ^ s := by
    have heq : (fun n : ℕ ↦ C * ‖z / a n‖ ^ s) = fun n ↦ (C * ‖z‖ ^ s) * ‖a n‖ ^ (-s : ℝ) := by
      ext n
      rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _), div_eq_mul_inv,
        ← Real.rpow_neg (norm_nonneg _)]
      ring
    rw [heq, tsum_mul_left]
    ring
  have hle_fin : ∀ N : ℕ,
      ∏ n ∈ Finset.range N, ‖weierstrassPrimaryFactor p (z / a n)‖ ≤
        Real.exp (C * (∑' n : ℕ, ‖a n‖ ^ (-s : ℝ)) * ‖z‖ ^ s) := by
    intro N
    have h1 : ∏ n ∈ Finset.range N, ‖weierstrassPrimaryFactor p (z / a n)‖ ≤
        ∏ n ∈ Finset.range N, Real.exp (C * ‖z / a n‖ ^ s) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun n _ ↦ hfac (z / a n)
    have h2 : ∏ n ∈ Finset.range N, Real.exp (C * ‖z / a n‖ ^ s) =
        Real.exp (∑ n ∈ Finset.range N, C * ‖z / a n‖ ^ s) :=
      (Real.exp_sum (Finset.range N) (fun n ↦ C * ‖z / a n‖ ^ s)).symm
    have h3 : ∑ n ∈ Finset.range N, C * ‖z / a n‖ ^ s ≤ ∑' n : ℕ, C * ‖z / a n‖ ^ s :=
      hsum_terms.sum_le_tsum (Finset.range N) fun n _ ↦ by positivity
    exact h1.trans (h2 ▸ (Real.exp_le_exp.mpr h3).trans_eq (congrArg Real.exp htsum_eq))
  exact le_of_tendsto htend_prod (Filter.Eventually.of_forall hle_fin)

/-- **Order bound for canonical products**: if `∀ n, a n ≠ 0`, `∑ ‖a n‖ ^ (-(p + 1 : ℝ))`
converges, `(p : ℝ) ≤ ρ`, `ρ ≤ (p : ℝ) + 1`, and `convergenceExponent a ≤ ρ`, then
`EntireOrderLe (canonicalProduct a p) ρ`. -/
theorem entireOrderLe_canonicalProduct {a : ℕ → ℂ} {p : ℕ} {ρ : ℝ}
    (ha : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))))
    (hpρ : (p : ℝ) ≤ ρ) (_hρp : ρ ≤ (p : ℝ) + 1) (hconv : convergenceExponent a ≤ ρ) :
    EntireOrderLe (canonicalProduct a p) ρ := by
  have hdiff := differentiable_canonicalProduct ha hsum
  refine entireOrderLe_of_eventually_exp hdiff fun δ hδ ↦ ?_
  let s : ℝ := min (ρ + δ / 2) ((p : ℝ) + 1)
  have hs_pos : 0 < s := by
    have h1 : 0 ≤ ρ := (Nat.cast_nonneg p).trans hpρ
    exact lt_min (by linarith) (by positivity)
  have hps : (p : ℝ) ≤ s := le_min (by linarith) (by linarith)
  have hsp : s ≤ (p : ℝ) + 1 := min_le_right _ _
  have hsum_s : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s : ℝ)) := by
    rcases le_or_gt ((p : ℝ) + 1) (ρ + δ / 2) with hmin | hmin
    · have hs_eq : s = ((p + 1 : ℕ) : ℝ) := by
        simp only [s, Nat.cast_add, Nat.cast_one]
        exact min_eq_right hmin
      rwa [hs_eq]
    · have hs_eq : s = ρ + δ / 2 := min_eq_left hmin.le
      have hs_gt : convergenceExponent a < s := by rw [hs_eq]; linarith
      have hfin : HasFiniteConvergenceExponent a :=
        ⟨((p + 1 : ℕ) : ℝ), Nat.cast_pos.mpr (Nat.succ_pos p), hsum⟩
      exact summable_norm_rpow_neg_of_convergenceExponent_lt ha hfin hs_gt
  obtain ⟨C, hC_pos, hbound⟩ := norm_canonicalProduct_le_exp ha hs_pos hps hsp hsum_s
  let B : ℝ := C * ∑' n : ℕ, ‖a n‖ ^ (-s : ℝ)
  refine ⟨1, B, 1, le_rfl, fun z hz ↦ ?_⟩
  rw [one_mul]
  have hs_le_exp : s ≤ ρ + δ := (min_le_left _ _).trans (by linarith)
  have hpow : ‖z‖ ^ s ≤ ‖z‖ ^ (ρ + δ) := Real.rpow_le_rpow_of_exponent_le hz hs_le_exp
  have hB_nonneg : 0 ≤ B := mul_nonneg hC_pos.le (tsum_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
  exact (hbound z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hB_nonneg))

/-- **Canonical product order at the convergence exponent**: when `∀ n, a n ≠ 0`, `∑ ‖a n‖ ^ (-(p + 1))`
converges, and `(p : ℝ) ≤ convergenceExponent a`, the canonical product has order at most
`convergenceExponent a`. -/
theorem entireOrderLe_canonicalProduct_convergenceExponent {a : ℕ → ℂ} {p : ℕ}
    (ha : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))))
    (hp_le : (p : ℝ) ≤ convergenceExponent a) :
    EntireOrderLe (canonicalProduct a p) (convergenceExponent a) := by
  have hconv_le : convergenceExponent a ≤ (p : ℝ) + 1 := by
    have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; rfl
    rw [← hcast]
    exact convergenceExponent_le (Nat.cast_nonneg _) hsum
  exact entireOrderLe_canonicalProduct ha hsum hp_le hconv_le le_rfl

end AnalyticNumberTheory.AnalyticTools.EntireFunctions
