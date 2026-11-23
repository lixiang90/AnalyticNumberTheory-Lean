/-
Copyright (c) 2026 AnalyticNumberTheory-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Basic Theory of the Gamma and Digamma Functions

This file provides a unified API around `Complex.Gamma`, `Real.Gamma`, and `Complex.digamma`,
including:
- Euler's integral representation for `0 < s.re` (and `0 < x`), recurrence `Γ(s + 1) = s * Γ(s)`,
  and factorial values `Γ(n + 1) = n!`
- Non-vanishing away from `{0, -1, -2, ...}`, entirety of `1 / Γ`, and simple poles at `-n`
  with exact residue `(-1)^n / n!` (both limit form and `meromorphicOrderAt Complex.Gamma (-n) = -1`)
- Euler's reflection formula `Γ(s) * Γ(1 - s) = π / sin(π * s)` and Legendre's duplication formula
  `Γ(s) * Γ(s + 1/2) = 2^(1 - 2*s) * √π * Γ(2 * s)`
- Euler's limit formula, Weierstrass's infinite product representation for `1 / Γ(s)` and `Γ(s)`,
  and Euler's infinite product representation
- The digamma function `digamma s := deriv Complex.Gamma s / Complex.Gamma s`, its recurrence,
  special values, reflection and duplication formulas, and partial fraction expansion
  `digamma s = -γ + ∑' n, (1 / (n + 1) - 1 / (n + s))`.
-/

open Filter Function MeasureTheory Set Topology

open scoped BigOperators Nat Real

namespace AnalyticNumberTheory.AnalyticTools.Gamma

section IntegralAndRecurrence

/-- Integral representation of `Complex.Gamma s` for `0 < s.re`. -/
theorem gamma_eq_integral {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s = ∫ x in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1) :=
  Complex.Gamma_eq_integral hs

/-- Integral representation of `Real.Gamma s` for `0 < s`. -/
theorem real_gamma_eq_integral {s : ℝ} (hs : 0 < s) :
    Real.Gamma s = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s - 1) :=
  Real.Gamma_eq_integral hs

/-- Functional equation `Γ(s + 1) = s * Γ(s)` for `s ≠ 0` in `ℂ`. -/
theorem gamma_add_one {s : ℂ} (hs : s ≠ 0) :
    Complex.Gamma (s + 1) = s * Complex.Gamma s :=
  Complex.Gamma_add_one s hs

/-- Functional equation `Γ(s + 1) = s * Γ(s)` for `s ≠ 0` in `ℝ`. -/
theorem real_gamma_add_one {s : ℝ} (hs : s ≠ 0) :
    Real.Gamma (s + 1) = s * Real.Gamma s :=
  Real.Gamma_add_one hs

/-- Value of `Complex.Gamma` at positive integers: `Γ(n + 1) = n!`. -/
theorem gamma_nat_eq_factorial (n : ℕ) : Complex.Gamma (n + 1) = (n ! : ℂ) :=
  Complex.Gamma_nat_eq_factorial n

/-- Value of `Real.Gamma` at positive integers: `Γ(n + 1) = n!`. -/
theorem real_gamma_nat_eq_factorial (n : ℕ) : Real.Gamma (n + 1) = (n ! : ℝ) :=
  Real.Gamma_nat_eq_factorial n

/-- `Complex.Gamma 1 = 1`. -/
theorem gamma_one : Complex.Gamma 1 = 1 :=
  Complex.Gamma_one

/-- `Real.Gamma 1 = 1`. -/
theorem real_gamma_one : Real.Gamma 1 = 1 :=
  Real.Gamma_one

/-- `Complex.Gamma (1 / 2) = √π`. -/
theorem gamma_one_half : Complex.Gamma (1 / 2) = (√π : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_nonneg]
  norm_num

/-- `Real.Gamma (1 / 2) = √π`. -/
theorem real_gamma_one_half : Real.Gamma (1 / 2) = √π :=
  Real.Gamma_one_half_eq

/-- Compatibility of `Complex.Gamma` with real coercion. -/
theorem gamma_ofReal (s : ℝ) : Complex.Gamma (s : ℂ) = (Real.Gamma s : ℂ) :=
  Complex.Gamma_ofReal s

/-- Positivity of `Real.Gamma` on `(0, ∞)`. -/
theorem real_gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Real.Gamma s :=
  Real.Gamma_pos_of_pos hs

/-- Beta-Gamma relation for `0 < u.re` and `0 < v.re`. -/
theorem gamma_mul_gamma_eq_betaIntegral {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Complex.Gamma u * Complex.Gamma v = Complex.Gamma (u + v) * Complex.betaIntegral u v :=
  Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv

/-- Iterated recurrence `Γ(z + n) / Γ(z) = ∏ k ∈ Finset.range n, (z + k)` away from poles. -/
theorem gamma_add_nat_div_gamma {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (n : ℕ) :
    Complex.Gamma (z + n) / Complex.Gamma z = ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero =>
    simp [Complex.Gamma_ne_zero hz]
  | succ n ih =>
    have hzn : z + (n : ℂ) ≠ 0 := by
      intro h
      exact hz n (eq_neg_of_add_eq_zero_left h)
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hzn,
      Finset.prod_range_succ, ← ih]
    field_simp [Complex.Gamma_ne_zero hz]

end IntegralAndRecurrence

section PolesAndNonvanishing

/-- The open complement of `{0, -1, -2, ...}` in `ℂ`. -/
def nonPoleSet : Set ℂ := {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)}

/-- Membership characterization for `nonPoleSet`. -/
theorem mem_nonPoleSet_iff {z : ℂ} : z ∈ nonPoleSet ↔ ∀ m : ℕ, z ≠ -(m : ℂ) :=
  Iff.rfl

/-- Any complex number with `0 < z.re` belongs to `nonPoleSet`. -/
theorem mem_nonPoleSet_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∈ nonPoleSet := by
  intro m h
  have : (-(m : ℂ)).re ≤ 0 := by simp
  linarith [congr_arg Complex.re h]

/-- `nonPoleSet` is an open subset of `ℂ`. -/
theorem isOpen_nonPoleSet : IsOpen nonPoleSet := by
  rw [Metric.isOpen_iff]
  intro z hz
  let S : Finset ℂ := (Finset.range (⌊‖z‖⌋₊ + 2)).image (fun m : ℕ => -(m : ℂ))
  have hzS : z ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro m _ hm
    exact hz m hm.symm
  have hpos : ∃ ε > 0, ∀ w ∈ S, ε ≤ dist w z := by
    by_cases hSe : S.Nonempty
    · obtain ⟨w₀, hw₀, hmin⟩ := S.exists_min_image (fun w => dist w z) hSe
      refine ⟨dist w₀ z, dist_pos.mpr (fun h => hzS (h ▸ hw₀)), hmin⟩
    · exact ⟨1, one_pos, fun w hw => (hSe ⟨w, hw⟩).elim⟩
  obtain ⟨ε, hε, hmin⟩ := hpos
  refine ⟨min 1 ε, lt_min one_pos hε, fun w hw m hwm => ?_⟩
  have hw_dist : dist w z < min 1 ε := Metric.mem_ball.mp hw
  have hnorm_w : ‖w‖ < ‖z‖ + 1 := by
    have h1 : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
    have h2 : ‖w - z‖ < 1 := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hw_dist (min_le_left _ _)
    linarith
  have hm_lt : m < ⌊‖z‖⌋₊ + 2 := by
    have hmn : (m : ℝ) = ‖w‖ := by rw [hwm, norm_neg, Complex.norm_natCast]
    have hfloor : ‖z‖ < (⌊‖z‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖z‖
    have hlt : (m : ℝ) < (⌊‖z‖⌋₊ + 2 : ℕ) := by
      push_cast
      linarith
    exact_mod_cast hlt
  have hmemS : w ∈ S := by
    simp only [S, Finset.mem_image, Finset.mem_range]
    exact ⟨m, hm_lt, hwm.symm⟩
  have hle : ε ≤ dist w z := hmin w hmemS
  have hlt : dist w z < ε := lt_of_lt_of_le hw_dist (min_le_right _ _)
  linarith

/-- Non-vanishing of `Complex.Gamma s` away from `{0, -1, -2, ...}`. -/
theorem gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) : Complex.Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero hs

/-- Characterization of zeros (and pole convention values) of `Complex.Gamma`. -/
theorem gamma_eq_zero_iff (s : ℂ) : Complex.Gamma s = 0 ↔ ∃ m : ℕ, s = -(m : ℂ) :=
  Complex.Gamma_eq_zero_iff s

/-- Non-vanishing of `Complex.Gamma s` for `0 < s.re`. -/
theorem gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hs

/-- Complex differentiability of `Complex.Gamma` away from `{0, -1, -2, ...}`. -/
theorem differentiableAt_gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    DifferentiableAt ℂ Complex.Gamma s :=
  Complex.differentiableAt_Gamma s hs

/-- Holomorphicity of `Complex.Gamma` on `nonPoleSet`. -/
theorem differentiableOn_gamma : DifferentiableOn ℂ Complex.Gamma nonPoleSet :=
  fun _ hz => (differentiableAt_gamma hz).differentiableWithinAt

/-- Analyticity of `Complex.Gamma` on `nonPoleSet`. -/
theorem analyticOnNhd_gamma : AnalyticOnNhd ℂ Complex.Gamma nonPoleSet :=
  differentiableOn_gamma.analyticOnNhd isOpen_nonPoleSet

/-- Meromorphicity of `Complex.Gamma` on `ℂ`. -/
theorem meromorphic_gamma : Meromorphic Complex.Gamma :=
  Meromorphic.Gamma

/-- The reciprocal `fun s => (Complex.Gamma s)⁻¹` is entire. -/
theorem differentiable_one_div_gamma : Differentiable ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) :=
  Complex.differentiable_one_div_Gamma

/-- The reciprocal `fun s => (Complex.Gamma s)⁻¹` is analytic everywhere on `ℂ`. -/
theorem analyticOnNhd_one_div_gamma : AnalyticOnNhd ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) univ :=
  Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ

/-- Residue of `Complex.Gamma` at `s = -n`: `(s + n) * Γ(s) → (-1)^n / n!` as `s → -n`. -/
theorem tendsto_add_nat_mul_gamma_nhdsNE (n : ℕ) :
    Tendsto (fun s : ℂ => (s + (n : ℂ)) * Complex.Gamma s)
      (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1 : ℂ) ^ n / (n ! : ℂ))) := by
  induction n with
  | zero =>
    simpa using Complex.tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
    have hne0 : -((n + 1 : ℕ) : ℂ) ≠ 0 :=
      neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    have ht_shift : Tendsto (fun s : ℂ => s + 1)
        (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have heq : (-(n : ℂ)) = -((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
        rw [heq]
        exact (continuous_add_const 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ -((n + 1 : ℕ) : ℂ))
        change s + 1 ≠ -(n : ℂ)
        intro h
        apply hs
        push_cast at h ⊢
        linear_combination h
    have hnum : Tendsto (fun s : ℂ => (s + 1 + (n : ℂ)) * Complex.Gamma (s + 1))
        (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝 ((-1 : ℂ) ^ n / (n ! : ℂ))) :=
      ih.comp ht_shift
    have hden : Tendsto (fun s : ℂ => s)
        (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝 (-((n + 1 : ℕ) : ℂ))) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hquot := hnum.div hden hne0
    have hlim : ((-1 : ℂ) ^ n / (n ! : ℂ)) / (-((n + 1 : ℕ) : ℂ)) =
        (-1 : ℂ) ^ (n + 1) / ((n + 1)! : ℂ) := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
      have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      field_simp [hfac, hn1]
    rw [hlim] at hquot
    refine hquot.congr' ?_
    have hev : ∀ᶠ s : ℂ in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), s ≠ 0 :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hne0)
    filter_upwards [hev] with s hs0
    simp only [Pi.div_apply, Complex.Gamma_add_one s hs0]
    push_cast
    field_simp [hs0]
    ring

/-- Real version of the residue at `-n`: `(x + n) * Real.Gamma x → (-1)^n / n!` as `x → -n`. -/
theorem real_tendsto_add_nat_mul_gamma_nhdsNE (n : ℕ) :
    Tendsto (fun x : ℝ => (x + (n : ℝ)) * Real.Gamma x)
      (𝓝[≠] (-(n : ℝ))) (𝓝 ((-1 : ℝ) ^ n / (n ! : ℝ))) := by
  have hmap : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] (-(n : ℝ))) (𝓝[≠] (-(n : ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).trans ?_
      simp
    · filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ -(n : ℝ))
      change (x : ℂ) ≠ -(n : ℂ)
      intro h
      exact hx (Complex.ofReal_inj.mp (by simpa using h))
  have hcomp := (Complex.continuous_re.tendsto _).comp
    ((tendsto_add_nat_mul_gamma_nhdsNE n).comp hmap)
  refine hcomp.congr' ?_ |>.trans ?_
  · filter_upwards with x
    simp [Complex.Gamma_ofReal]
  · norm_cast

/-- Each non-positive integer `-n` is a simple pole of `Complex.Gamma` (`meromorphicOrderAt = -1`). -/
theorem meromorphicOrderAt_gamma_neg_nat (n : ℕ) :
    meromorphicOrderAt Complex.Gamma (-(n : ℂ)) = (-1 : ℤ) := by
  have hG : AnalyticAt ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) (-(n : ℂ)) :=
    analyticOnNhd_one_div_gamma (-(n : ℂ)) (mem_univ _)
  have hG0 : (Complex.Gamma (-(n : ℂ)))⁻¹ = 0 := by
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
  have hres := tendsto_add_nat_mul_gamma_nhdsNE n
  have hres_ne : (-1 : ℂ) ^ n / (n ! : ℂ) ≠ 0 :=
    div_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hinv_res : Tendsto (fun s : ℂ => ((s - -(n : ℂ))⁻¹ * (Complex.Gamma s)⁻¹))
      (𝓝[≠] (-(n : ℂ))) (𝓝 (((-1 : ℂ) ^ n / (n ! : ℂ))⁻¹)) := by
    refine (hres.inv₀ hres_ne).congr fun s => ?_
    rw [sub_neg_eq_add, mul_inv]
  have hslope :
      Tendsto (fun s : ℂ => (s - -(n : ℂ))⁻¹ * (Complex.Gamma s)⁻¹)
        (𝓝[≠] (-(n : ℂ))) (𝓝 (deriv (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)))) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hG.differentiableAt.hasDerivAt).congr fun s => ?_
    simp [slope_def_module, smul_eq_mul, hG0]
  have hderiv_eq : deriv (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) =
      ((-1 : ℂ) ^ n / (n ! : ℂ))⁻¹ :=
    tendsto_nhds_unique hslope hinv_res
  have hderiv_ne : deriv (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) ≠ 0 := by
    rw [hderiv_eq]
    exact inv_ne_zero hres_ne
  have hord_inv : analyticOrderAt (fun z : ℂ => (Complex.Gamma z)⁻¹) (-(n : ℂ)) = 1 :=
    hG.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hG0 hderiv_ne
  have hm_inv : meromorphicOrderAt (fun z : ℂ => (Complex.Gamma z)⁻¹) (-(n : ℂ)) = (1 : ℤ) := by
    rw [hG.meromorphicOrderAt_eq, hord_inv]
    rfl
  have hm_eq : Complex.Gamma = (fun z : ℂ => (Complex.Gamma z)⁻¹)⁻¹ := by
    ext z; simp
  rw [hm_eq, meromorphicOrderAt_inv, hm_inv]
  rfl

end PolesAndNonvanishing

section ReflectionAndDuplication

/-- Euler's reflection formula: `Γ(s) * Γ(1 - s) = π / sin(π * s)` for `s : ℂ`. -/
theorem gamma_mul_gamma_one_sub (s : ℂ) :
    Complex.Gamma s * Complex.Gamma (1 - s) = (π : ℂ) / Complex.sin ((π : ℂ) * s) :=
  Complex.Gamma_mul_Gamma_one_sub s

/-- Euler's reflection formula on `ℝ`: `Γ(s) * Γ(1 - s) = π / sin(π * s)`. -/
theorem real_gamma_mul_gamma_one_sub (s : ℝ) :
    Real.Gamma s * Real.Gamma (1 - s) = π / Real.sin (π * s) :=
  Real.Gamma_mul_Gamma_one_sub s

/-- Legendre's duplication formula for `Complex.Gamma`:
`Γ(s) * Γ(s + 1/2) = 2^(1 - 2*s) * √π * Γ(2 * s)`. -/
theorem gamma_mul_gamma_add_half (s : ℂ) :
    Complex.Gamma s * Complex.Gamma (s + 1 / 2) =
      (2 : ℂ) ^ (1 - 2 * s) * (√π : ℂ) * Complex.Gamma (2 * s) := by
  rw [Complex.Gamma_mul_Gamma_add_half]
  ring

/-- Legendre's duplication formula for `Real.Gamma`:
`Γ(s) * Γ(s + 1/2) = 2^(1 - 2*s) * √π * Γ(2 * s)`. -/
theorem real_gamma_mul_gamma_add_half (s : ℝ) :
    Real.Gamma s * Real.Gamma (s + 1 / 2) =
      (2 : ℝ) ^ (1 - 2 * s) * √π * Real.Gamma (2 * s) := by
  rw [Real.Gamma_mul_Gamma_add_half]
  ring

end ReflectionAndDuplication

section WeierstrassAndEulerProduct

/-- Euler's limit formula for `Complex.Gamma`: `GammaSeq s n → Γ(s)` as `n → ∞`. -/
theorem gammaSeq_tendsto_gamma (s : ℂ) :
    Tendsto (Complex.GammaSeq s) atTop (𝓝 (Complex.Gamma s)) :=
  Complex.GammaSeq_tendsto_Gamma s

/-- Euler's limit formula for `Real.Gamma`: `GammaSeq s n → Γ(s)` as `n → ∞`. -/
theorem real_gammaSeq_tendsto_gamma (s : ℝ) :
    Tendsto (Real.GammaSeq s) atTop (𝓝 (Real.Gamma s)) :=
  Real.GammaSeq_tendsto_Gamma s

/-- The `n`-th Weierstrass factor `(1 + s / (n + 1)) * exp(-s / (n + 1))` for `1 / Γ(s)`. -/
noncomputable def weierstrassFactor (s : ℂ) (n : ℕ) : ℂ :=
  (1 + s / ((n : ℂ) + 1)) * Complex.exp (-s / ((n : ℂ) + 1))

/-- The `n`-th Weierstrass factor vanishes iff `s = -(n + 1)`. -/
theorem weierstrassFactor_eq_zero_iff (s : ℂ) (n : ℕ) :
    weierstrassFactor s n = 0 ↔ s = -((n : ℂ) + 1) := by
  rw [weierstrassFactor, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _)]
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  constructor
  · intro h
    have h1 : (n : ℂ) + 1 + s = 0 := by
      have := mul_eq_zero_of_right ((n : ℂ) + 1) h
      field_simp [hn] at this
      linear_combination this
    linear_combination h1
  · intro h
    rw [h]
    field_simp [hn]
    ring

/-- The `n`-th Weierstrass factor is non-zero whenever `s ≠ -(n + 1)`. -/
theorem weierstrassFactor_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    weierstrassFactor s n ≠ 0 := by
  rw [ne_eq, weierstrassFactor_eq_zero_iff]
  simpa [Nat.cast_add, Nat.cast_one] using hs (n + 1)

/-- Uniform quadratic bound on `weierstrassFactor s n - 1`: for `‖s‖ ≤ R` and `2 * R ≤ n + 1`,
`‖weierstrassFactor s n - 1‖ ≤ 2 * R^2 / (n + 1)^2`. -/
theorem norm_weierstrassFactor_sub_one_le {s : ℂ} {R : ℝ} {n : ℕ}
    (hs : ‖s‖ ≤ R) (hn : 2 * R ≤ (n : ℝ) + 1) :
    ‖weierstrassFactor s n - 1‖ ≤ 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg s).trans hs
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set z : ℂ := s / ((n : ℂ) + 1)
  have hnorm_n : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn_pos]
  have hz_norm : ‖z‖ ≤ R / ((n : ℝ) + 1) := by
    rw [norm_div, hnorm_n]
    exact div_le_div_of_nonneg_right hs hn_pos.le
  have hz_half : ‖z‖ ≤ 1 / 2 := by
    refine hz_norm.trans ?_
    rw [div_le_iff₀ hn_pos]
    linarith
  have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz_half (by norm_num)
  have h1z_slit : 1 + z ∈ Complex.slitPlane := Complex.mem_slitPlane_of_norm_lt_one hz_lt
  have hwf : weierstrassFactor s n = Complex.exp (Complex.log (1 + z) - z) := by
    rw [weierstrassFactor, show -s / ((n : ℂ) + 1) = -z by rw [neg_div],
      Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero h1z_slit), Complex.exp_neg,
      mul_comm, div_eq_mul_inv]
    ring
  set w : ℂ := Complex.log (1 + z) - z
  have hw_bound : ‖w‖ ≤ ‖z‖ ^ 2 := by
    have hlog := Complex.norm_log_one_add_sub_self_le hz_lt
    have h1z_inv : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have h1 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    linarith
  have hw_le_one : ‖w‖ ≤ 1 := by
    have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [norm_nonneg z]
    linarith
  rw [hwf]
  calc ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := Complex.norm_exp_sub_one_le hw_le_one
    _ ≤ 2 * ‖z‖ ^ 2 := by linarith
    _ ≤ 2 * (R / ((n : ℝ) + 1)) ^ 2 := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    _ = 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
      rw [div_pow]
      ring

/-- The series `∑' n, ‖weierstrassFactor s n - 1‖` converges for every `s : ℂ`. -/
theorem summable_norm_weierstrassFactor_sub_one (s : ℂ) :
    Summable fun n : ℕ => ‖weierstrassFactor s n - 1‖ := by
  set R : ℝ := ‖s‖
  have hsum_p2 : Summable fun n : ℕ => 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr one_lt_two
    rw [← summable_nat_add_iff 1] at h
    refine (h.mul_left (2 * R ^ 2)).congr fun n => ?_
    simp [div_eq_mul_inv, Nat.cast_add]
  refine hsum_p2.of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈2 * R⌉₊, fun n hn => ?_⟩
  have h2R : 2 * R ≤ (n : ℝ) + 1 := by
    have hceil : 2 * R ≤ (⌈2 * R⌉₊ : ℝ) := Nat.le_ceil _
    have hn' : (⌈2 * R⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_weierstrassFactor_sub_one_le (le_refl R) h2R

/-- The Weierstrass product `∏' n, weierstrassFactor s n` converges for every `s : ℂ`. -/
theorem multipliable_weierstrassFactor (s : ℂ) : Multipliable (weierstrassFactor s) := by
  have h : Multipliable fun n : ℕ => 1 + (weierstrassFactor s n - 1) :=
    multipliable_one_add_of_summable (summable_norm_weierstrassFactor_sub_one s)
  simpa using h

/-- Locally uniform convergence of `∏' n, weierstrassFactor s n` on any open set `U ⊆ ℂ`. -/
theorem multipliableLocallyUniformlyOn_weierstrassFactor {U : Set ℂ} (hU : IsOpen U) :
    MultipliableLocallyUniformlyOn (fun n (s : ℂ) => weierstrassFactor s n) U := by
  refine ⟨fun s => ∏' n, weierstrassFactor s n, ?_⟩
  refine hasProdLocallyUniformlyOn_of_forall_compact hU fun K _ hK => ?_
  obtain ⟨R, hR_bd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ K, ‖s‖ ≤ R := by
    by_cases hKe : K = ∅
    · exact ⟨0, le_rfl, fun _ hs => (hKe ▸ hs).elim⟩
    · obtain ⟨s₀, hs₀, hs₀_max⟩ := hK.exists_isMaxOn (Set.nonempty_iff_ne_empty.mpr hKe)
        continuous_norm.continuousOn
      exact ⟨‖s₀‖, norm_nonneg _, fun s hs => hs₀_max hs⟩
  obtain ⟨hR0, hR⟩ := hR_bd
  have hu : Summable fun n : ℕ => 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr one_lt_two
    rw [← summable_nat_add_iff 1] at h
    refine (h.mul_left (2 * R ^ 2)).congr fun n => ?_
    simp [div_eq_mul_inv, Nat.cast_add]
  have hcts : ∀ n : ℕ, ContinuousOn (fun s : ℂ => weierstrassFactor s n - 1) K := fun n => by
    unfold weierstrassFactor
    fun_prop
  have hle : ∀ᶠ n : ℕ in atTop, ∀ s ∈ K, ‖weierstrassFactor s n - 1‖ ≤ 2 * R ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈2 * R⌉₊, fun n hn s hs => ?_⟩
    have h2R : 2 * R ≤ (n : ℝ) + 1 := by
      have hceil : 2 * R ≤ (⌈2 * R⌉₊ : ℝ) := Nat.le_ceil _
      have hn' : (⌈2 * R⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact norm_weierstrassFactor_sub_one_le (hR s hs) h2R
  simpa using hu.hasProdUniformlyOn_nat_one_add hK hle hcts

/-- Locally uniform convergence of `∏' n, weierstrassFactor s n` on all of `ℂ`. -/
theorem multipliableLocallyUniformly_weierstrassFactor :
    MultipliableLocallyUniformly fun n (s : ℂ) => weierstrassFactor s n := by
  obtain ⟨g, hg⟩ := multipliableLocallyUniformlyOn_weierstrassFactor isOpen_univ
  refine ⟨g, ?_⟩
  rw [hasProdLocallyUniformly_iff_tendstoLocallyUniformly, ← tendstoLocallyUniformlyOn_univ]
  exact hg

/-- Exact formula for the `N`-th partial product of the Weierstrass product for `1 / Γ(s)`. -/
theorem prod_range_weierstrassFactor (s : ℂ) {N : ℕ} (hN : N ≠ 0) :
    s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
        ∏ n ∈ Finset.range N, weierstrassFactor s n =
      (Complex.GammaSeq s N)⁻¹ *
        Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
          (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)))) := by
  have hprod_split :
      ∏ n ∈ Finset.range N, weierstrassFactor s n =
        (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)) / ((n : ℂ) + 1)) *
          ∏ n ∈ Finset.range N, Complex.exp (-s / ((n : ℂ) + 1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [weierstrassFactor]
    field_simp [hn]
    ring
  have hrat :
      s * ∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)) / ((n : ℂ) + 1) =
        (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / (N ! : ℂ) := by
    rw [Finset.prod_div_distrib, mul_div_assoc', Finset.prod_range_succ']
    have hfac : (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) = (N ! : ℂ) := by
      have hnat : ∏ n ∈ Finset.range N, (n + 1) = N ! := Finset.prod_range_add_one_eq_factorial N
      exact_mod_cast hnat
    rw [hfac, Nat.cast_zero, add_zero, mul_comm s]
    have hnum : (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1))) =
        ∏ k ∈ Finset.range N, (s + ((k + 1 : ℕ) : ℂ)) :=
      Finset.prod_congr rfl fun n _ => by push_cast; ring
    rw [hnum]
  have hexp_sum :
      ∏ n ∈ Finset.range N, Complex.exp (-s / ((n : ℂ) + 1)) =
        Complex.exp (-s * ((harmonic N : ℚ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    unfold harmonic
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hcpow_inv :
      Complex.exp (-s * (Real.log N : ℂ)) = ((N : ℂ) ^ s)⁻¹ := by
    rw [Complex.cpow_def_of_ne_zero hN_ne, ← Complex.exp_neg, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hN_pos.le]
    congr 1
    ring
  have hexp_comb :
      Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) * Complex.exp (-s * ((harmonic N : ℚ) : ℂ)) =
        ((N : ℂ) ^ s)⁻¹ * Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
          (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)))) := by
    rw [← hcpow_inv, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hgamma_seq :
      (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / (N ! : ℂ) * ((N : ℂ) ^ s)⁻¹ =
        (Complex.GammaSeq s N)⁻¹ := by
    rw [Complex.GammaSeq]
    by_cases hP : (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) = 0
    · simp [hP]
    · have hpow_ne : (N : ℂ) ^ s ≠ 0 := (Complex.cpow_ne_zero_iff.mpr (Or.inl hN_ne))
      have hfac_ne : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
      field_simp [hP, hpow_ne, hfac_ne]
  calc s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
        ∏ n ∈ Finset.range N, weierstrassFactor s n
      = (s * ∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)) / ((n : ℂ) + 1)) *
          (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
            Complex.exp (-s * ((harmonic N : ℚ) : ℂ))) := by
        rw [hprod_split, hexp_sum]
        ring
    _ = ((∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / (N ! : ℂ) * ((N : ℂ) ^ s)⁻¹) *
          Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
            (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)))) := by
        rw [hrat, hexp_comb]
        ring
    _ = (Complex.GammaSeq s N)⁻¹ *
          Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
            (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)))) := by
        rw [hgamma_seq]

/-- **Weierstrass infinite product representation** of `1 / Γ(s)` for all `s : ℂ`:
`(Complex.Gamma s)⁻¹ = s * exp(γ * s) * ∏' n : ℕ, (1 + s / (n + 1)) * exp(-s / (n + 1))`. -/
theorem inv_gamma_eq_weierstrass_tprod (s : ℂ) :
    (Complex.Gamma s)⁻¹ =
      s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
        ∏' n : ℕ, (1 + s / ((n : ℂ) + 1)) * Complex.exp (-s / ((n : ℂ) + 1)) := by
  change (Complex.Gamma s)⁻¹ =
    s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) * ∏' n : ℕ, weierstrassFactor s n
  by_cases hs : ∀ m : ℕ, s ≠ -(m : ℂ)
  · have hlim_lhs :
        Tendsto (fun N : ℕ => s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
            ∏ n ∈ Finset.range N, weierstrassFactor s n)
          atTop (𝓝 (s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
            ∏' n : ℕ, weierstrassFactor s n)) :=
      ((multipliable_weierstrassFactor s).hasProd.tendsto_prod_nat).const_mul _
    have hgamma_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    have hlim_seq : Tendsto (fun N : ℕ => (Complex.GammaSeq s N)⁻¹)
        atTop (𝓝 (Complex.Gamma s)⁻¹) :=
      (Complex.GammaSeq_tendsto_Gamma s).inv₀ hgamma_ne
    have hlim_harm :
        Tendsto (fun N : ℕ => Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
            (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)))))
          atTop (𝓝 1) := by
      have hreal : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - Real.log N)
          atTop (𝓝 Real.eulerMascheroniConstant) :=
        Real.tendsto_harmonic_sub_log
      have hc : Tendsto (fun N : ℕ => (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ)))
          atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
        ((Complex.continuous_ofReal.tendsto _).comp hreal).congr fun N => by
          exact Complex.ofReal_sub _ _
      have h0 : Tendsto (fun N : ℕ => s * ((Real.eulerMascheroniConstant : ℂ) -
            (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ))))
          atTop (𝓝 0) := by
        have hsub : Tendsto (fun N : ℕ => (Real.eulerMascheroniConstant : ℂ) -
              (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ)))
            atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) - (Real.eulerMascheroniConstant : ℂ))) :=
          tendsto_const_nhds.sub hc
        rw [sub_self] at hsub
        have hm := hsub.const_mul s
        rwa [mul_zero] at hm
      have he : Tendsto (fun N : ℕ => Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
            (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ)))))
          atTop (𝓝 (Complex.exp 0)) :=
        (Complex.continuous_exp.tendsto _).comp h0
      rwa [Complex.exp_zero] at he
    have hlim_rhs :
        Tendsto (fun N : ℕ => (Complex.GammaSeq s N)⁻¹ *
            Complex.exp (s * ((Real.eulerMascheroniConstant : ℂ) -
              (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)))))
          atTop (𝓝 (Complex.Gamma s)⁻¹) := by
      simpa using hlim_seq.mul hlim_harm
    have hlim_rhs' :
        Tendsto (fun N : ℕ => s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
            ∏ n ∈ Finset.range N, weierstrassFactor s n)
          atTop (𝓝 (Complex.Gamma s)⁻¹) := by
      refine hlim_rhs.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with N hN
      exact (prod_range_weierstrassFactor s hN).symm
    exact tendsto_nhds_unique hlim_rhs' hlim_lhs
  · push Not at hs
    obtain ⟨m, rfl⟩ := hs
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    rcases m with _ | k
    · simp
    · have hzero : weierstrassFactor (-((k + 1 : ℕ) : ℂ)) k = 0 := by
        rw [weierstrassFactor_eq_zero_iff]
        push_cast
        ring
      have ht : ∏' n : ℕ, weierstrassFactor (-((k + 1 : ℕ) : ℂ)) n = 0 :=
        (hasProd_zero_of_exists_eq_zero ⟨k, hzero⟩).tprod_eq
      rw [ht, mul_zero]

/-- `ℕ+`-indexed form of the Weierstrass infinite product representation for `1 / Γ(s)`. -/
theorem inv_gamma_eq_weierstrass_tprod_pnat (s : ℂ) :
    (Complex.Gamma s)⁻¹ =
      s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
        ∏' n : ℕ+, (1 + s / (n : ℂ)) * Complex.exp (-s / (n : ℂ)) := by
  rw [inv_gamma_eq_weierstrass_tprod]
  congr 1
  rw [tprod_pnat_eq_tprod_succ (f := fun n : ℕ => (1 + s / (n : ℂ)) * Complex.exp (-s / (n : ℂ)))]
  simp [Nat.cast_add, Nat.cast_one]

/-- Weierstrass infinite product representation for `Complex.Gamma s` away from poles. -/
theorem gamma_eq_inv_weierstrass_tprod {s : ℂ} (_hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    Complex.Gamma s =
      (s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) *
        ∏' n : ℕ, (1 + s / ((n : ℂ) + 1)) * Complex.exp (-s / ((n : ℂ) + 1)))⁻¹ := by
  rw [← inv_gamma_eq_weierstrass_tprod s, inv_inv]

/-- Real Weierstrass infinite product representation of `1 / Γ(x)` for all `x : ℝ`. -/
theorem real_inv_gamma_eq_weierstrass_tprod (x : ℝ) :
    (Real.Gamma x)⁻¹ =
      x * Real.exp (Real.eulerMascheroniConstant * x) *
        ∏' n : ℕ, (1 + x / ((n : ℝ) + 1)) * Real.exp (-x / ((n : ℝ) + 1)) := by
  have hm : Multipliable fun n : ℕ => (1 + x / ((n : ℝ) + 1)) * Real.exp (-x / ((n : ℝ) + 1)) := by
    have hnorm : Summable fun n : ℕ =>
        ‖((1 + x / ((n : ℝ) + 1)) * Real.exp (-x / ((n : ℝ) + 1)) - 1 : ℝ)‖ := by
      have hc := summable_norm_weierstrassFactor_sub_one (x : ℂ)
      refine hc.congr fun n => ?_
      rw [weierstrassFactor]
      have hcast :
          ((1 + (x : ℂ) / ((n : ℂ) + 1)) * Complex.exp (-(x : ℂ) / ((n : ℂ) + 1)) - 1) =
            ((((1 + x / ((n : ℝ) + 1)) * Real.exp (-x / ((n : ℝ) + 1)) - 1 : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [hcast, Complex.norm_real]
    simpa using multipliable_one_add_of_summable hnorm
  have hre :
      Complex.re ((Complex.Gamma (x : ℂ))⁻¹) =
        Complex.re ((x : ℂ) * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (x : ℂ)) *
          ∏' n : ℕ, (1 + (x : ℂ) / ((n : ℂ) + 1)) * Complex.exp (-(x : ℂ) / ((n : ℂ) + 1))) :=
    congr_arg Complex.re (inv_gamma_eq_weierstrass_tprod (x : ℂ))
  have hprod :
      ∏' n : ℕ, (1 + (x : ℂ) / ((n : ℂ) + 1)) * Complex.exp (-(x : ℂ) / ((n : ℂ) + 1)) =
        ((∏' n : ℕ, (1 + x / ((n : ℝ) + 1)) * Real.exp (-x / ((n : ℝ) + 1)) : ℝ) : ℂ) := by
    have hp := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
    have hpt := hp.tprod_eq.symm
    have hpt' :
        (((∏' n : ℕ, (1 + x / ((n : ℝ) + 1)) * Real.exp (-x / ((n : ℝ) + 1)) : ℝ) : ℂ)) =
          ∏' n : ℕ, (1 + (x : ℂ) / ((n : ℂ) + 1)) * Complex.exp (-(x : ℂ) / ((n : ℂ) + 1)) := by
      simpa [Complex.ofReal_exp] using hpt
    exact hpt'.symm
  rw [Complex.Gamma_ofReal, hprod, ← Complex.ofReal_inv, Complex.ofReal_re,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hre
  exact hre

/-- Euler's infinite product factor `(1 + s / (n + 1)) * (1 + 1 / (n + 1)) ^ (-s)`. -/
noncomputable def eulerFactor (s : ℂ) (n : ℕ) : ℂ :=
  (1 + s / ((n : ℂ) + 1)) * (1 + (1 : ℂ) / ((n : ℂ) + 1)) ^ (-s)

/-- Convergence of Euler's infinite product `∏' n, eulerFactor s n` for every `s : ℂ`. -/
theorem multipliable_eulerFactor (s : ℂ) : Multipliable (eulerFactor s) := by
  have h1 : Multipliable (weierstrassFactor s) := multipliable_weierstrassFactor s
  have hsum_u : Summable fun n : ℕ =>
      ‖Complex.exp (-s * (Complex.log (1 + (1 : ℂ) / ((n : ℂ) + 1)) -
        (1 : ℂ) / ((n : ℂ) + 1))) - 1‖ := by
    have hsum_p2 : Summable fun n : ℕ => 2 * ‖s‖ / ((n : ℝ) + 1) ^ 2 := by
      have h := (Real.summable_nat_pow_inv (p := 2)).mpr one_lt_two
      rw [← summable_nat_add_iff 1] at h
      refine (h.mul_left (2 * ‖s‖)).congr fun n => ?_
      simp [div_eq_mul_inv, Nat.cast_add]
    refine hsum_p2.of_norm_bounded_eventually_nat ?_
    rw [Filter.eventually_atTop]
    refine ⟨⌈√‖s‖⌉₊ + 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hz_norm : ‖(1 : ℂ) / ((n : ℂ) + 1)‖ = 1 / ((n : ℝ) + 1) := by
      rw [norm_div, norm_one]
      have : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hn_pos]
      rw [this]
    have hz_half : ‖(1 : ℂ) / ((n : ℂ) + 1)‖ ≤ 1 / 2 := by
      rw [hz_norm, one_div, one_div]
      gcongr
      exact_mod_cast (by omega : 2 ≤ n + 1)
    have hz_lt : ‖(1 : ℂ) / ((n : ℂ) + 1)‖ < 1 := lt_of_le_of_lt hz_half (by norm_num)
    have hlog_bd := Complex.norm_log_one_add_sub_self_le hz_lt
    have h1z_inv : (1 - ‖(1 : ℂ) / ((n : ℂ) + 1)‖)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have hw_bd : ‖-s * (Complex.log (1 + (1 : ℂ) / ((n : ℂ) + 1)) -
        (1 : ℂ) / ((n : ℂ) + 1))‖ ≤ ‖s‖ / ((n : ℝ) + 1) ^ 2 := by
      rw [norm_mul, norm_neg]
      have hlog2 : ‖Complex.log (1 + (1 : ℂ) / ((n : ℂ) + 1)) - (1 : ℂ) / ((n : ℂ) + 1)‖ ≤
          1 / ((n : ℝ) + 1) ^ 2 := by
        have h1 : ‖(1 : ℂ) / ((n : ℂ) + 1)‖ ^ 2 * (1 - ‖(1 : ℂ) / ((n : ℂ) + 1)‖)⁻¹ / 2 ≤
            ‖(1 : ℂ) / ((n : ℂ) + 1)‖ ^ 2 * 2 / 2 := by gcongr
        rw [hz_norm] at h1 hlog_bd
        have h2 : (1 / ((n : ℝ) + 1)) ^ 2 * 2 / 2 = 1 / ((n : ℝ) + 1) ^ 2 := by
          rw [div_pow]
          ring
        exact hlog_bd.trans (h1.trans_eq h2)
      calc ‖s‖ * ‖Complex.log (1 + (1 : ℂ) / ((n : ℂ) + 1)) - (1 : ℂ) / ((n : ℂ) + 1)‖
          ≤ ‖s‖ * (1 / ((n : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hlog2 (norm_nonneg _)
        _ = ‖s‖ / ((n : ℝ) + 1) ^ 2 := by ring
    have hw_le_one : ‖-s * (Complex.log (1 + (1 : ℂ) / ((n : ℂ) + 1)) -
        (1 : ℂ) / ((n : ℂ) + 1))‖ ≤ 1 := by
      refine hw_bd.trans ?_
      rw [div_le_one (by positivity)]
      have hceil : √‖s‖ ≤ (⌈√‖s‖⌉₊ : ℝ) := Nat.le_ceil _
      have hn' : (⌈√‖s‖⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have hsq : √‖s‖ ≤ (n : ℝ) + 1 := by linarith
      have hsq2 : (√‖s‖) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg ‖s‖]
      rwa [Real.sq_sqrt (norm_nonneg s)] at hsq2
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_div_assoc] using
      (Complex.norm_exp_sub_one_le hw_le_one).trans (mul_le_mul_of_nonneg_left hw_bd (by positivity))
  have h2 : Multipliable fun n : ℕ =>
      Complex.exp (-s * (Complex.log (1 + (1 : ℂ) / ((n : ℂ) + 1)) - (1 : ℂ) / ((n : ℂ) + 1))) := by
    have hm := multipliable_one_add_of_summable hsum_u
    simpa using hm
  refine (h1.mul h2).congr fun n => ?_
  have h1n_ne : (1 : ℂ) + (1 : ℂ) / ((n : ℂ) + 1) ≠ 0 := by
    have hcast : ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 + (1 : ℂ) / ((n : ℂ) + 1) := by
      push_cast; rfl
    rw [← hcast, Complex.ofReal_ne_zero]
    positivity
  rw [eulerFactor, weierstrassFactor, Complex.cpow_def_of_ne_zero h1n_ne, mul_comm _ (-s),
    mul_sub, Complex.exp_sub, mul_assoc]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- **Euler's infinite product representation** of `1 / Γ(s)` for all `s : ℂ`:
`(Complex.Gamma s)⁻¹ = s * ∏' n : ℕ, (1 + s / (n + 1)) * (1 + 1 / (n + 1)) ^ (-s)`. -/
theorem inv_gamma_eq_euler_tprod (s : ℂ) :
    (Complex.Gamma s)⁻¹ =
      s * ∏' n : ℕ, (1 + s / ((n : ℂ) + 1)) * (1 + (1 : ℂ) / ((n : ℂ) + 1)) ^ (-s) := by
  change (Complex.Gamma s)⁻¹ = s * ∏' n : ℕ, eulerFactor s n
  by_cases hs : ∀ m : ℕ, s ≠ -(m : ℂ)
  · have hlim_lhs :
        Tendsto (fun N : ℕ => s * ∏ n ∈ Finset.range N, eulerFactor s n)
          atTop (𝓝 (s * ∏' n : ℕ, eulerFactor s n)) :=
      ((multipliable_eulerFactor s).hasProd.tendsto_prod_nat).const_mul s
    have hprod_N : ∀ {N : ℕ}, N ≠ 0 →
        s * ∏ n ∈ Finset.range N, eulerFactor s n =
          (Complex.GammaSeq s N)⁻¹ * ((N : ℂ) / ((N : ℂ) + 1)) ^ s := by
      intro N hN
      have hsplit :
          ∏ n ∈ Finset.range N, eulerFactor s n =
            (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)) / ((n : ℂ) + 1)) *
              ∏ n ∈ Finset.range N, (1 + (1 : ℂ) / ((n : ℂ) + 1)) ^ (-s) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun n _ => ?_
        have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
        rw [eulerFactor]
        field_simp [hn]
        ring
      have hrat :
          s * ∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)) / ((n : ℂ) + 1) =
            (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / (N ! : ℂ) := by
        rw [Finset.prod_div_distrib, mul_div_assoc', Finset.prod_range_succ']
        have hfac : (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) = (N ! : ℂ) := by
          have hnat : ∏ n ∈ Finset.range N, (n + 1) = N ! := Finset.prod_range_add_one_eq_factorial N
          exact_mod_cast hnat
        rw [hfac, Nat.cast_zero, add_zero, mul_comm s]
        have hnum : (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1))) =
            ∏ k ∈ Finset.range N, (s + ((k + 1 : ℕ) : ℂ)) :=
          Finset.prod_congr rfl fun n _ => by push_cast; ring
        rw [hnum]
      have htele :
          ∏ n ∈ Finset.range N, (1 + (1 : ℂ) / ((n : ℂ) + 1)) ^ (-s) =
            ((N : ℂ) + 1) ^ (-s) := by
        have hterm : ∀ n : ℕ,
            (1 + (1 : ℂ) / ((n : ℂ) + 1)) ^ (-s) =
              Complex.exp (-s * ((Real.log ((n : ℝ) + 2) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))) := by
          intro n
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
          have h1eq : (1 + (1 : ℂ) / ((n : ℂ) + 1)) =
              ((((n : ℝ) + 2) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
            push_cast
            field_simp [hn1.ne']
            ring
          rw [h1eq, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hn2 hn1).ne'),
            ← Complex.ofReal_log (div_pos hn2 hn1).le, Real.log_div hn2.ne' hn1.ne',
            Complex.ofReal_sub, mul_comm]
        simp_rw [hterm, ← Complex.exp_sum]
        have hsum_tele :
            ∑ n ∈ Finset.range N, (-s * ((Real.log ((n : ℝ) + 2) : ℂ) -
                (Real.log ((n : ℝ) + 1) : ℂ))) =
              -s * (Real.log ((N : ℝ) + 1) : ℂ) := by
          rw [← Finset.mul_sum]
          have htele' :
              ∑ n ∈ Finset.range N,
                  ((Real.log ((n : ℝ) + 2) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)) =
                (Real.log ((N : ℝ) + 1) : ℂ) - (Real.log ((0 : ℝ) + 1) : ℂ) := by
            have hst := Finset.sum_range_sub (fun n : ℕ => (Real.log ((n : ℝ) + 1) : ℂ)) N
            convert hst using 2 with n
            · push_cast
              ring_nf
            · push_cast
              rfl
          rw [htele', zero_add, Real.log_one, Complex.ofReal_zero, sub_zero]
        have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have hNp1_ne : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
        rw [hsum_tele, Complex.cpow_def_of_ne_zero hNp1_ne,
          show (N : ℂ) + 1 = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_log hNp1_pos.le, mul_comm (-s)]
      have hpow_ratio :
          ((N : ℂ) + 1) ^ (-s) = ((N : ℂ) ^ s)⁻¹ * ((N : ℂ) / ((N : ℂ) + 1)) ^ s := by
        have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
        have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        have hdiv := Complex.div_cpow_ofReal_nonneg hN_pos.le hNp1_pos.le s
        rw [Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_natCast,
          Complex.ofReal_one] at hdiv
        rw [Complex.cpow_neg, hdiv]
        have hpow_ne : (N : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hN_ne)
        field_simp [hpow_ne]
      have hgamma_seq :
          (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / (N ! : ℂ) * ((N : ℂ) ^ s)⁻¹ =
            (Complex.GammaSeq s N)⁻¹ := by
        rw [Complex.GammaSeq]
        by_cases hP : (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) = 0
        · simp [hP]
        · have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
          have hpow_ne : (N : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hN_ne)
          have hfac_ne : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
          field_simp [hP, hpow_ne, hfac_ne]
      rw [hsplit, htele, ← mul_assoc, hrat, hpow_ratio, ← mul_assoc, hgamma_seq]
    have hgamma_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    have hlim_seq : Tendsto (fun N : ℕ => (Complex.GammaSeq s N)⁻¹)
        atTop (𝓝 (Complex.Gamma s)⁻¹) :=
      (Complex.GammaSeq_tendsto_Gamma s).inv₀ hgamma_ne
    have hlim_ratio : Tendsto (fun N : ℕ => ((N : ℂ) / ((N : ℂ) + 1)) ^ s) atTop (𝓝 1) := by
      have hbase : Tendsto (fun N : ℕ => (N : ℂ) / ((N : ℂ) + 1)) atTop (𝓝 1) := by
        simpa [add_comm] using tendsto_natCast_div_add_atTop (1 : ℂ)
      have hcont : ContinuousAt (fun z : ℂ => z ^ s) 1 :=
        continuousAt_cpow_const (by simp)
      have hcomp : Tendsto (fun N : ℕ => ((N : ℂ) / ((N : ℂ) + 1)) ^ s) atTop (𝓝 ((1 : ℂ) ^ s)) :=
        hcont.tendsto.comp hbase
      rwa [Complex.one_cpow] at hcomp
    have hlim_rhs : Tendsto (fun N : ℕ => s * ∏ n ∈ Finset.range N, eulerFactor s n)
        atTop (𝓝 (Complex.Gamma s)⁻¹) := by
      have hm := hlim_seq.mul hlim_ratio
      rw [mul_one] at hm
      refine hm.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with N hN
      exact (hprod_N hN).symm
    exact tendsto_nhds_unique hlim_rhs hlim_lhs
  · push Not at hs
    obtain ⟨m, rfl⟩ := hs
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    rcases m with _ | k
    · simp
    · have hzero : eulerFactor (-((k + 1 : ℕ) : ℂ)) k = 0 := by
        rw [eulerFactor, mul_eq_zero]
        left
        have hk : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
        push_cast
        field_simp [hk]
        ring
      have ht : ∏' n : ℕ, eulerFactor (-((k + 1 : ℕ) : ℂ)) n = 0 :=
        (hasProd_zero_of_exists_eq_zero ⟨k, hzero⟩).tprod_eq
      rw [ht, mul_zero]

end WeierstrassAndEulerProduct

section Digamma

/-- The complex digamma function, defined as the logarithmic derivative `deriv Γ(s) / Γ(s)`. -/
noncomputable def digamma (s : ℂ) : ℂ :=
  deriv Complex.Gamma s / Complex.Gamma s

/-- Compatibility with Mathlib's `Complex.digamma`. -/
theorem digamma_eq_complex_digamma : digamma = Complex.digamma :=
  rfl

/-- Definition unfolding lemma `digamma s = deriv Complex.Gamma s / Complex.Gamma s`. -/
theorem digamma_def (s : ℂ) : digamma s = deriv Complex.Gamma s / Complex.Gamma s :=
  rfl

/-- `digamma 0 = 0` by Mathlib convention. -/
theorem digamma_zero : digamma 0 = 0 :=
  Complex.digamma_zero

/-- `digamma 1 = -γ` where `γ = Real.eulerMascheroniConstant`. -/
theorem digamma_one : digamma 1 = -(Real.eulerMascheroniConstant : ℂ) :=
  Complex.digamma_one

/-- `digamma (1 / 2) = -2 * log 2 - γ`. -/
theorem digamma_one_half :
    digamma (1 / 2) = -2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) :=
  Complex.digamma_one_half

/-- `digamma (n + 1) = harmonic n - γ` for `n : ℕ`. -/
theorem digamma_nat_add_one (n : ℕ) :
    digamma (n + 1) = ((harmonic n : ℚ) : ℂ) - (Real.eulerMascheroniConstant : ℂ) := by
  simpa [digamma_eq_complex_digamma] using Complex.digamma_nat_add_one n

/-- Recurrence `digamma (s + 1) = digamma s + 1 / s` away from poles `{0, -1, -2, ...}`. -/
theorem digamma_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma (s + 1) = digamma s + s⁻¹ :=
  Complex.digamma_apply_add_one s hs

/-- Iterated recurrence `digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹`. -/
theorem digamma_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹ :=
  Complex.digamma_apply_add_nat hs n

/-- Euler's reflection formula for digamma: `digamma (1 - s) = digamma s + π * cot (π * s)`. -/
theorem digamma_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ (n : ℂ)) :
    digamma (1 - s) = digamma s + (π : ℂ) * Complex.cot ((π : ℂ) * s) :=
  Complex.digamma_one_sub hs

/-- Legendre's duplication formula for digamma:
`digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2`. -/
theorem digamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ)) :
    digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + Complex.log 2 :=
  Complex.digamma_two_mul hs

/-- Meromorphicity of `digamma` on `ℂ`. -/
theorem meromorphic_digamma : Meromorphic digamma :=
  Complex.meromorphic_digamma

/-- Complex differentiability of `digamma` away from `{0, -1, -2, ...}`. -/
theorem differentiableAt_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    DifferentiableAt ℂ digamma s := by
  have hG : AnalyticAt ℂ Complex.Gamma s := analyticOnNhd_gamma s hs
  have hdG : AnalyticAt ℂ (deriv Complex.Gamma) s := hG.deriv
  exact (hdG.differentiableAt.div hG.differentiableAt (Complex.Gamma_ne_zero hs))

/-- Holomorphicity of `digamma` on `nonPoleSet`. -/
theorem differentiableOn_digamma : DifferentiableOn ℂ digamma nonPoleSet :=
  fun _ hz => (differentiableAt_digamma hz).differentiableWithinAt

/-- Analyticity of `digamma` on `nonPoleSet`. -/
theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ digamma nonPoleSet :=
  differentiableOn_digamma.analyticOnNhd isOpen_nonPoleSet

/-- Logarithmic derivative of a single Weierstrass factor at `s ∉ {0, -1, -2, ...}`. -/
theorem logDeriv_weierstrassFactor_eq {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    logDeriv (fun z => weierstrassFactor z n) s =
      1 / ((n : ℂ) + 1 + s) - 1 / ((n : ℂ) + 1) := by
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hsn : (n : ℂ) + 1 + s ≠ 0 := by
    intro h
    apply hs (n + 1)
    push_cast
    linear_combination h
  have hlin_ne : 1 + s / ((n : ℂ) + 1) ≠ 0 := by
    intro h
    apply hsn
    have := mul_eq_zero_of_right ((n : ℂ) + 1) h
    field_simp [hn] at this
    linear_combination this
  have hlin_diff : DifferentiableAt ℂ (fun z : ℂ => 1 + z / ((n : ℂ) + 1)) s := by fun_prop
  have hexp_diff : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-z / ((n : ℂ) + 1))) s := by
    fun_prop
  have hlin_deriv : HasDerivAt (fun z : ℂ => 1 + z / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) s := by
    have h1 := ((hasDerivAt_id s).div_const ((n : ℂ) + 1)).const_add (1 : ℂ)
    simpa [one_div] using h1
  have hexp_deriv : HasDerivAt (fun z : ℂ => Complex.exp (-z / ((n : ℂ) + 1)))
      ((-1 / ((n : ℂ) + 1)) * Complex.exp (-s / ((n : ℂ) + 1))) s := by
    have hinner : HasDerivAt (fun z : ℂ => -z / ((n : ℂ) + 1)) (-1 / ((n : ℂ) + 1)) s := by
      simpa using (hasDerivAt_neg s).div_const ((n : ℂ) + 1)
    simpa [mul_comm] using hinner.cexp
  calc logDeriv (fun z => weierstrassFactor z n) s
      = logDeriv (fun z => 1 + z / ((n : ℂ) + 1)) s +
          logDeriv (fun z => Complex.exp (-z / ((n : ℂ) + 1))) s :=
        logDeriv_fun_mul s hlin_ne (Complex.exp_ne_zero _) hlin_diff hexp_diff
    _ = (1 / ((n : ℂ) + 1)) / (1 + s / ((n : ℂ) + 1)) +
          ((-1 / ((n : ℂ) + 1)) * Complex.exp (-s / ((n : ℂ) + 1))) /
            Complex.exp (-s / ((n : ℂ) + 1)) := by
        rw [logDeriv_apply, logDeriv_apply, hlin_deriv.deriv, hexp_deriv.deriv]
    _ = 1 / ((n : ℂ) + 1 + s) - 1 / ((n : ℂ) + 1) := by
        have hexp_ne : Complex.exp (-s / ((n : ℂ) + 1)) ≠ 0 := Complex.exp_ne_zero _
        field_simp [hn, hsn, hexp_ne]
        ring

/-- Summability of the partial fraction terms `1 / (n + 1) - 1 / (n + 1 + s)` for `s ∉ {0, -1, ...}`. -/
theorem summable_digamma_shifted_term {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    Summable fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s) := by
  have hsum_p2 : Summable fun n : ℕ => 2 * ‖s‖ / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr one_lt_two
    rw [← summable_nat_add_iff 1] at h
    refine (h.mul_left (2 * ‖s‖)).congr fun n => ?_
    simp [div_eq_mul_inv, Nat.cast_add]
  refine hsum_p2.of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈2 * ‖s‖⌉₊, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2s : 2 * ‖s‖ ≤ (n : ℝ) + 1 := by
    have hceil : 2 * ‖s‖ ≤ (⌈2 * ‖s‖⌉₊ : ℝ) := Nat.le_ceil _
    have hn' : (⌈2 * ‖s‖⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnorm_n : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn_pos]
  have hnorm_ns : ((n : ℝ) + 1) / 2 ≤ ‖((n : ℂ) + 1 + s)‖ := by
    have := norm_sub_norm_le ((n : ℂ) + 1) (-s)
    rw [hnorm_n, norm_neg, sub_neg_eq_add] at this
    linarith
  have hn_ne : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hsn_ne : (n : ℂ) + 1 + s ≠ 0 := by
    intro h
    apply hs (n + 1)
    push_cast
    linear_combination h
  have hid : 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s) =
      s / (((n : ℂ) + 1) * ((n : ℂ) + 1 + s)) := by
    field_simp [hn_ne, hsn_ne]
    ring
  rw [hid, norm_div, norm_mul, hnorm_n]
  have hdenom_pos : 0 < ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) := by positivity
  have hbd : ‖s‖ / (((n : ℝ) + 1) * ‖(n : ℂ) + 1 + s‖) ≤ 2 * ‖s‖ / ((n : ℝ) + 1) ^ 2 := by
    calc ‖s‖ / (((n : ℝ) + 1) * ‖(n : ℂ) + 1 + s‖)
        ≤ ‖s‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by gcongr
      _ = 2 * ‖s‖ / ((n : ℝ) + 1) ^ 2 := by
        field_simp [hn_pos.ne']
  exact hbd

/-- Summability of `1 / (n + 1) - 1 / (n + s)` for `s ∉ {0, -1, -2, ...}`. -/
theorem summable_digamma_term {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    Summable fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s) := by
  have hsum_p2 : Summable fun n : ℕ => 2 * ‖s - 1‖ / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr one_lt_two
    rw [← summable_nat_add_iff 1] at h
    refine (h.mul_left (2 * ‖s - 1‖)).congr fun n => ?_
    simp [div_eq_mul_inv, Nat.cast_add]
  refine hsum_p2.of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈2 * ‖s‖⌉₊ + 1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2s : 2 * ‖s‖ ≤ (n : ℝ) - 1 := by
    have hceil : 2 * ‖s‖ ≤ (⌈2 * ‖s‖⌉₊ : ℝ) := Nat.le_ceil _
    have hn' : (⌈2 * ‖s‖⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnorm_n1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn_pos]
  have hnorm_n : ‖(n : ℂ)‖ = (n : ℝ) := Complex.norm_natCast n
  have hnorm_ns : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + s‖ := by
    have h1 := norm_sub_norm_le (n : ℂ) (-s)
    rw [hnorm_n, norm_neg, sub_neg_eq_add] at h1
    linarith
  have hn_ne : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hsn_ne : (n : ℂ) + s ≠ 0 := by
    intro h
    apply hs n
    linear_combination h
  have hid : 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s) =
      (s - 1) / (((n : ℂ) + 1) * ((n : ℂ) + s)) := by
    field_simp [hn_ne, hsn_ne]
    ring
  rw [hid, norm_div, norm_mul, hnorm_n1]
  have hdenom_pos : 0 < ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) := by positivity
  have hbd : ‖s - 1‖ / (((n : ℝ) + 1) * ‖(n : ℂ) + s‖) ≤ 2 * ‖s - 1‖ / ((n : ℝ) + 1) ^ 2 := by
    calc ‖s - 1‖ / (((n : ℝ) + 1) * ‖(n : ℂ) + s‖)
        ≤ ‖s - 1‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by gcongr
      _ = 2 * ‖s - 1‖ / ((n : ℝ) + 1) ^ 2 := by
        field_simp [hn_pos.ne']
  exact hbd

/-- Shifted partial fraction expansion of `digamma`:
`digamma s = -γ - s⁻¹ + ∑' n : ℕ, (1 / (n + 1) - 1 / (n + 1 + s))` for `s ∉ {0, -1, -2, ...}`. -/
theorem digamma_eq_neg_eulerMascheroni_sub_inv_add_tsum {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s =
      -(Real.eulerMascheroniConstant : ℂ) - s⁻¹ +
        ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s)) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hgamma_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hgamma_diff : DifferentiableAt ℂ Complex.Gamma s := differentiableAt_gamma hs
  have hinv_lhs : logDeriv (fun z : ℂ => (Complex.Gamma z)⁻¹) s = -digamma s := by
    rw [logDeriv_apply, digamma_def]
    have hderiv_inv : deriv (fun z : ℂ => (Complex.Gamma z)⁻¹) s =
        -deriv Complex.Gamma s / (Complex.Gamma s) ^ 2 := by
      have hhd : HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹)
          (-(deriv Complex.Gamma s) / (Complex.Gamma s) ^ 2) s :=
        hgamma_diff.hasDerivAt.inv hgamma_ne
      exact hhd.deriv
    rw [hderiv_inv]
    field_simp [hgamma_ne]
  have hprod_ne : ∏' n : ℕ, weierstrassFactor s n ≠ 0 := by
    have hm : ∏' n : ℕ, (1 + (weierstrassFactor s n - 1)) ≠ 0 :=
      tprod_one_add_ne_zero_of_summable
        (fun n => by simpa using weierstrassFactor_ne_zero hs n)
        (summable_norm_weierstrassFactor_sub_one s)
    simpa using hm
  have hwf_diff : ∀ n : ℕ, DifferentiableOn ℂ (fun z => weierstrassFactor z n) nonPoleSet := by
    intro n
    unfold weierstrassFactor
    fun_prop
  have hsum_ld : Summable fun n : ℕ => logDeriv (fun z => weierstrassFactor z n) s := by
    refine (summable_digamma_shifted_term hs).neg.congr fun n => ?_
    rw [logDeriv_weierstrassFactor_eq hs n]
    ring
  have hprod_ld :
      logDeriv (fun z => ∏' n : ℕ, weierstrassFactor z n) s =
        ∑' n : ℕ, logDeriv (fun z => weierstrassFactor z n) s :=
    _root_.logDeriv_tprod_eq_tsum isOpen_nonPoleSet hs (weierstrassFactor_ne_zero hs)
      hwf_diff hsum_ld (multipliableLocallyUniformlyOn_weierstrassFactor isOpen_nonPoleSet)
      hprod_ne
  have hprod_diff : DifferentiableAt ℂ (fun z => ∏' n : ℕ, weierstrassFactor z n) s := by
    have hm := multipliableLocallyUniformlyOn_weierstrassFactor isOpen_nonPoleSet
    have hdiff_on : DifferentiableOn ℂ (fun z => ∏' n : ℕ, weierstrassFactor z n) nonPoleSet := by
      refine hm.hasProdLocallyUniformlyOn.differentiableOn (Eventually.of_forall fun S => ?_)
        isOpen_nonPoleSet
      induction S using Finset.induction_on with
      | empty => simp [differentiableOn_const]
      | insert n S hn ih =>
        simpa only [Finset.prod_insert hn] using (hwf_diff n).fun_mul ih
    exact hdiff_on.differentiableAt (isOpen_nonPoleSet.mem_nhds hs)
  have hexp_diff : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) s := by
    fun_prop
  have hexp_ld : logDeriv (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) s =
      (Real.eulerMascheroniConstant : ℂ) := by
    have hd : HasDerivAt (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))
        ((Real.eulerMascheroniConstant : ℂ) * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s)) s := by
      have h1 : HasDerivAt (fun z : ℂ => (Real.eulerMascheroniConstant : ℂ) * z)
          (Real.eulerMascheroniConstant : ℂ) s := by
        simpa using (hasDerivAt_id s).const_mul (Real.eulerMascheroniConstant : ℂ)
      simpa [mul_comm] using h1.cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp [Complex.exp_ne_zero _]
  have hweier_fun :
      (fun z : ℂ => (Complex.Gamma z)⁻¹) =
        fun z : ℂ => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) *
          ∏' n : ℕ, weierstrassFactor z n := by
    ext z
    exact inv_gamma_eq_weierstrass_tprod z
  have hrhs_ld :
      logDeriv (fun z : ℂ => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) *
          ∏' n : ℕ, weierstrassFactor z n) s =
        s⁻¹ + (Real.eulerMascheroniConstant : ℂ) +
          ∑' n : ℕ, (1 / ((n : ℂ) + 1 + s) - 1 / ((n : ℂ) + 1)) := by
    have hmul1 :
        logDeriv (fun z : ℂ => (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) *
            ∏' n : ℕ, weierstrassFactor z n) s =
          logDeriv (fun z : ℂ => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) s +
            logDeriv (fun z => ∏' n : ℕ, weierstrassFactor z n) s :=
      logDeriv_fun_mul s (mul_ne_zero hs0 (Complex.exp_ne_zero _)) hprod_ne
        (differentiableAt_id.mul hexp_diff) hprod_diff
    have hmul2 :
        logDeriv (fun z : ℂ => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) s =
          logDeriv id s + logDeriv (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) s :=
      logDeriv_fun_mul s hs0 (Complex.exp_ne_zero _) differentiableAt_id hexp_diff
    rw [hmul1, hmul2, logDeriv_id, hexp_ld, hprod_ld, one_div]
    congr 1
    exact tsum_congr fun n => logDeriv_weierstrassFactor_eq hs n
  have hcomb : -digamma s =
      s⁻¹ + (Real.eulerMascheroniConstant : ℂ) +
        ∑' n : ℕ, (1 / ((n : ℂ) + 1 + s) - 1 / ((n : ℂ) + 1)) := by
    rw [← hinv_lhs, hweier_fun]
    exact hrhs_ld
  have hneg : digamma s =
      -(Real.eulerMascheroniConstant : ℂ) - s⁻¹ -
        ∑' n : ℕ, (1 / ((n : ℂ) + 1 + s) - 1 / ((n : ℂ) + 1)) := by
    linear_combination -hcomb
  rw [hneg, sub_eq_add_neg, sub_eq_add_neg, ← tsum_neg]
  congr 1
  rw [tsum_congr fun n => ?_]
  ring

/-- **Partial fraction expansion of the digamma function**:
`digamma s = -γ + ∑' n : ℕ, (1 / (n + 1) - 1 / (n + s))` for all `s ∉ {0, -1, -2, ...}`. -/
theorem digamma_eq_neg_eulerMascheroni_add_tsum {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s =
      -(Real.eulerMascheroniConstant : ℂ) +
        ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) := by
  rw [digamma_eq_neg_eulerMascheroni_sub_inv_add_tsum hs]
  have hs1 : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s) :=
    summable_digamma_term hs
  have hs2 : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s) :=
    summable_digamma_shifted_term hs
  have hdiff_lim :
      Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))) -
            (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s))))
        atTop (𝓝 (-s⁻¹)) := by
    have htele : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))) -
          (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s))) =
          1 / ((N : ℂ) + s) - s⁻¹ := by
      intro N
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ n : ℕ,
          (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s)) -
            (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s)) =
            1 / ((n : ℂ) + 1 + s) - 1 / ((n : ℂ) + s) := fun n => by ring
      simp_rw [hterm]
      have hst := Finset.sum_range_sub (fun n : ℕ => 1 / ((n : ℂ) + s)) N
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, one_div] using hst
    simp_rw [htele]
    have hinv_zero : Tendsto (fun N : ℕ => 1 / ((N : ℂ) + s)) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      refine ⟨⌈ε⁻¹ + ‖s‖⌉₊ + 1, fun N hN => ?_⟩
      have hN' : ε⁻¹ + ‖s‖ + 1 ≤ (N : ℝ) := by
        have h1 : ε⁻¹ + ‖s‖ ≤ (⌈ε⁻¹ + ‖s‖⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈ε⁻¹ + ‖s‖⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hnorm : ε⁻¹ + 1 ≤ ‖(N : ℂ) + s‖ := by
        have h1 := norm_sub_norm_le ((N : ℂ)) (-s)
        rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add] at h1
        linarith
      have hpos : 0 < ‖(N : ℂ) + s‖ := lt_of_lt_of_le (by positivity) hnorm
      rw [dist_zero_right, one_div, norm_inv, inv_lt_comm₀ hpos hε]
      linarith
    simpa using hinv_zero.sub tendsto_const_nhds
  have hsum_lim :
      Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))) -
            (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s))))
        atTop (𝓝 ((∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + s))) -
          (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s))))) :=
    (hs1.hasSum.tendsto_sum_nat).sub (hs2.hasSum.tendsto_sum_nat)
  have heq := tendsto_nhds_unique hsum_lim hdiff_lim
  linear_combination -heq

/-- The real digamma function `deriv Real.Gamma x / Real.Gamma x`. -/
noncomputable def realDigamma (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

/-- Compatibility between `digamma` and `realDigamma` on `ℝ`. -/
theorem digamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma (x : ℂ) = (realDigamma x : ℂ) := by
  have hx_c : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := fun m h =>
    hx m (by exact_mod_cast h)
  have hG_diff : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := differentiableAt_gamma hx_c
  have hR_diff : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma hx
  have hderiv : deriv Complex.Gamma (x : ℂ) = Complex.ofReal (deriv Real.Gamma x) := by
    have h1 : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ)) (deriv Complex.Gamma (x : ℂ)) x :=
      hG_diff.hasDerivAt.comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => (Real.Gamma t : ℂ)) (Complex.ofReal (deriv Real.Gamma x)) x :=
      hR_diff.hasDerivAt.ofReal_comp
    have heq : (fun t : ℝ => Complex.Gamma (t : ℂ)) = fun t : ℝ => (Real.Gamma t : ℂ) := by
      ext t
      exact Complex.Gamma_ofReal t
    rw [heq] at h1
    exact h1.deriv.symm.trans h2.deriv
  rw [digamma_def, realDigamma, hderiv, Complex.Gamma_ofReal]
  push_cast
  rfl

/-- Partial fraction expansion of `realDigamma`:
`realDigamma x = -γ + ∑' n : ℕ, (1 / (n + 1) - 1 / (n + x))` for `x ∉ {0, -1, -2, ...}`. -/
theorem real_digamma_eq_neg_eulerMascheroni_add_tsum {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    realDigamma x =
      -Real.eulerMascheroniConstant +
        ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x)) := by
  have hx_c : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := fun m h =>
    hx m (by exact_mod_cast h)
  have hsum : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x) := by
    have hc := (summable_digamma_term hx_c).norm
    refine hc.of_norm_bounded_eventually_nat ?_
    filter_upwards with n
    have hcast :
        (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + (x : ℂ))) =
          (((1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x) : ℝ) : ℂ)) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hre := congr_arg Complex.re (digamma_eq_neg_eulerMascheroni_add_tsum hx_c)
  have htsum :
      Complex.re (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + (x : ℂ)))) =
        ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x)) := by
    have hs := hsum.hasSum.map Complex.ofRealHom Complex.continuous_ofReal
    have hceq :
        (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + (x : ℂ)))) =
          ((∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x)) : ℝ) : ℂ) := by
      simpa [Complex.ofRealHom_eq_coe] using hs.tsum_eq
    rw [hceq, Complex.ofReal_re]
  rw [digamma_ofReal hx, Complex.ofReal_re, Complex.add_re, Complex.neg_re,
    Complex.ofReal_re, htsum] at hre
  exact hre

end Digamma

end AnalyticNumberTheory.AnalyticTools.Gamma
