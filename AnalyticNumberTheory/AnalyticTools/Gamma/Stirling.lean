import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Stirling's Formula and Vertical Strip Bounds for the Gamma Function

This file develops the real and complex Stirling asymptotics for the Euler Gamma function
together with explicit Euler–Maclaurin remainder integral representations and vertical strip
bounds needed in analytic number theory.

## Main Results

* `real_log_gamma_eq_stirling`: for `0 < x`,
  `Real.log (Real.Gamma x) = (x - 1/2) * Real.log x - x + Real.log (2 * π) / 2 + stirlingRemainderReal x`,
  where `stirlingRemainderReal x = 1 / (12 * x) - ∫ u in Ioi 0, bernoulliKernel 2 u / (u + x) ^ 2`.
* `stirlingRemainderReal_nonneg` and `stirlingRemainderReal_le`: for `0 < x`,
  `0 ≤ stirlingRemainderReal x ≤ 1 / (8 * x)` (and `|stirlingRemainderReal x| ≤ 1 / (6 * x)`).
* `real_gamma_isEquivalent_stirling`: `Real.Gamma (x + 1) ~ √(2 * π * x) * (x / exp 1) ^ x`
  as `x → +∞`.
* `complex_gamma_eq_stirling`: for `s ∈ Complex.slitPlane`,
  `Complex.Gamma s = √(2 * π) * s ^ (s - 1/2) * Complex.exp (-s + stirlingRemainder s)`,
  where `stirlingRemainder` is holomorphic on `Complex.slitPlane` and satisfies the remainder
  bound `norm_stirlingRemainder_le`.
* `norm_complex_gamma_strip_bounds`, `norm_complex_gamma_strip_tendsto_one`, and
  `norm_complex_gamma_strip_asymptotic_explicit`: uniform upper/lower vertical strip bounds and
  exact Stirling asymptotics for `‖Complex.Gamma (σ + t * I)‖` on `σ ∈ [σ₁, σ₂]`, `1 ≤ |t|`.
* `digamma_eq_stirling` and `norm_digamma_strip_le`: Stirling asymptotic for the logarithmic
  derivative of `Complex.Gamma` on `Complex.slitPlane` and vertical strips.
-/

open Complex Real MeasureTheory Filter Set
open scoped Topology Asymptotics

namespace AnalyticNumberTheory.AnalyticTools.Gamma

open AnalyticNumberTheory.AnalyticTools.Summation

section Helpers

private lemma integrableOn_inv_add_sq_Ioi {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => ((u + r) ^ 2)⁻¹) (Set.Ioi 0) ∧
      ∫ u in Set.Ioi (0 : ℝ), ((u + r) ^ 2)⁻¹ = r⁻¹ := by
  let g : ℝ → ℝ := fun u => -(u + r)⁻¹
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt g (((u + r) ^ 2)⁻¹) u := by
    intro u hu
    have hur : u + r ≠ 0 := by
      have : 0 ≤ u := hu
      linarith
    have hadd : HasDerivAt (fun t : ℝ => t + r) 1 u := (hasDerivAt_id' u).add_const r
    have hinv := hadd.inv hur
    convert hinv.neg using 1
    ring
  have hg'pos : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ ((u + r) ^ 2)⁻¹ := fun u _ => by positivity
  have htend : Tendsto g atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun u : ℝ => u + r) atTop atTop :=
      tendsto_id.atTop_add tendsto_const_nhds
    simpa [g] using h1.inv_tendsto_atTop.neg
  have hint : IntegrableOn (fun u : ℝ => ((u + r) ^ 2)⁻¹) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hg'pos htend
  have heval : ∫ u in Set.Ioi (0 : ℝ), ((u + r) ^ 2)⁻¹ = r⁻¹ := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
    simp [g]
  exact ⟨hint, heval⟩

private lemma integrableOn_inv_add_cube_Ioi {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => ((u + r) ^ 3)⁻¹) (Set.Ioi 0) ∧
      ∫ u in Set.Ioi (0 : ℝ), ((u + r) ^ 3)⁻¹ = (2 * r ^ 2)⁻¹ := by
  let g : ℝ → ℝ := fun u => -(2 * (u + r) ^ 2)⁻¹
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt g (((u + r) ^ 3)⁻¹) u := by
    intro u hu
    have hur : 0 < u + r := by
      have : 0 ≤ u := hu
      linarith
    have hsq : HasDerivAt (fun t : ℝ => 2 * (t + r) ^ 2) (4 * (u + r)) u := by
      have h1 : HasDerivAt (fun t : ℝ => t + r) 1 u := (hasDerivAt_id' u).add_const r
      convert (h1.pow 2).const_mul (2 : ℝ) using 1
      ring
    have hne : 2 * (u + r) ^ 2 ≠ 0 := by positivity
    convert hsq.inv hne |>.neg using 1
    field_simp [hur.ne']
    ring
  have hg'pos : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ ((u + r) ^ 3)⁻¹ := by
    intro u hu
    have : 0 < u := hu
    positivity
  have htend : Tendsto g atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun u : ℝ => u + r) atTop atTop :=
      tendsto_id.atTop_add tendsto_const_nhds
    have h2 : Tendsto (fun u : ℝ => 2 * (u + r) ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop zero_lt_two ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h1)
    simpa [g] using h2.inv_tendsto_atTop.neg
  have hint : IntegrableOn (fun u : ℝ => ((u + r) ^ 3)⁻¹) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hg'pos htend
  have heval : ∫ u in Set.Ioi (0 : ℝ), ((u + r) ^ 3)⁻¹ = (2 * r ^ 2)⁻¹ := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
    simp [g]
  exact ⟨hint, heval⟩

private lemma bernoulliKernel_two_ge_neg_inv_24 (u : ℝ) : -((1 : ℝ) / 24) ≤ bernoulliKernel 2 u := by
  rw [bernoulliKernel_two]
  have h1 : (0 : ℝ) ≤ (Int.fract u - 1 / 2) ^ 2 := sq_nonneg _
  linarith

private lemma zero_le_one_div_12_sub_bernoulliKernel_two (u : ℝ) :
    0 ≤ (1 / 12 : ℝ) - bernoulliKernel 2 u := by
  have h := bernoulliKernel_two_abs_le u
  rw [abs_le] at h
  linarith

private lemma one_div_12_sub_bernoulliKernel_two_le (u : ℝ) :
    (1 / 12 : ℝ) - bernoulliKernel 2 u ≤ 1 / 8 := by
  have h := bernoulliKernel_two_ge_neg_inv_24 u
  linarith

end Helpers

section RealStirling

/-- Explicit Euler–Maclaurin remainder term in Stirling's formula for `log (Real.Gamma x)`
(`x > 0`): `stirlingRemainderReal x = 1 / (12 * x) - ∫ u in Ioi 0, bernoulliKernel 2 u / (u + x) ^ 2`. -/
noncomputable def stirlingRemainderReal (x : ℝ) : ℝ :=
  1 / (12 * x) - ∫ u in Set.Ioi (0 : ℝ), bernoulliKernel 2 u / (u + x) ^ 2

/-- Integrability of `u ↦ bernoulliKernel 2 u / (u + x) ^ 2` on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_bernoulliKernel_two_div_add_sq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => bernoulliKernel 2 u / (u + x) ^ 2) (Set.Ioi 0) := by
  have hdom := (integrableOn_inv_add_sq_Ioi hx).1.const_mul (1 / 12 : ℝ)
  refine Integrable.mono hdom ?_ ?_
  · have hcont : ContinuousOn (fun u : ℝ => bernoulliKernel 2 u / (u + x) ^ 2) (Set.Ioi 0) := by
      refine (continuous_bernoulliKernel (by norm_num)).continuousOn.div ?_ ?_
      · exact (continuous_id.add continuous_const).pow 2 |>.continuousOn
      · intro u hu
        have : 0 < u := hu
        positivity
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos (add_pos hu0 hx)), div_eq_mul_inv]
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (bernoulliKernel_two_abs_le u) (by positivity)

/-- Alternative non-negative integral representation of `stirlingRemainderReal x` for `x > 0`:
`stirlingRemainderReal x = ∫ u in Ioi 0, (1 / 12 - bernoulliKernel 2 u) / (u + x) ^ 2`. -/
theorem stirlingRemainderReal_eq_integral {x : ℝ} (hx : 0 < x) :
    stirlingRemainderReal x =
      ∫ u in Set.Ioi (0 : ℝ), ((1 / 12 : ℝ) - bernoulliKernel 2 u) / (u + x) ^ 2 := by
  have h1 := (integrableOn_inv_add_sq_Ioi hx).1.const_mul (1 / 12 : ℝ)
  have h2 := integrableOn_bernoulliKernel_two_div_add_sq hx
  have heval : ∫ u in Set.Ioi (0 : ℝ), (1 / 12 : ℝ) * ((u + x) ^ 2)⁻¹ = 1 / (12 * x) := by
    rw [integral_const_mul, (integrableOn_inv_add_sq_Ioi hx).2]
    ring
  have hsub : (fun u : ℝ => ((1 / 12 : ℝ) - bernoulliKernel 2 u) / (u + x) ^ 2) =
      fun u : ℝ => (1 / 12 : ℝ) * ((u + x) ^ 2)⁻¹ - bernoulliKernel 2 u / (u + x) ^ 2 := by
    ext u
    ring
  rw [hsub, integral_sub h1 h2, heval]
  rfl

/-- `stirlingRemainderReal x ≥ 0` for all `x > 0`. -/
theorem stirlingRemainderReal_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ stirlingRemainderReal x := by
  rw [stirlingRemainderReal_eq_integral hx]
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  exact div_nonneg (zero_le_one_div_12_sub_bernoulliKernel_two u) (sq_nonneg _)

/-- Upper bound `stirlingRemainderReal x ≤ 1 / (8 * x)` for all `x > 0`. -/
theorem stirlingRemainderReal_le {x : ℝ} (hx : 0 < x) :
    stirlingRemainderReal x ≤ 1 / (8 * x) := by
  rw [stirlingRemainderReal_eq_integral hx]
  have h1 := (integrableOn_inv_add_sq_Ioi hx).1.const_mul (1 / 12 : ℝ)
  have h2 := integrableOn_bernoulliKernel_two_div_add_sq hx
  have hL_int : IntegrableOn (fun u : ℝ => ((1 / 12 : ℝ) - bernoulliKernel 2 u) / (u + x) ^ 2)
      (Set.Ioi 0) := by
    have hsub : (fun u : ℝ => ((1 / 12 : ℝ) - bernoulliKernel 2 u) / (u + x) ^ 2) =
        fun u : ℝ => (1 / 12 : ℝ) * ((u + x) ^ 2)⁻¹ - bernoulliKernel 2 u / (u + x) ^ 2 := by
      ext u; ring
    rw [hsub]
    exact h1.sub h2
  have hR_int : IntegrableOn (fun u : ℝ => (1 / 8 : ℝ) * ((u + x) ^ 2)⁻¹) (Set.Ioi 0) :=
    (integrableOn_inv_add_sq_Ioi hx).1.const_mul (1 / 8 : ℝ)
  calc ∫ u in Set.Ioi (0 : ℝ), ((1 / 12 : ℝ) - bernoulliKernel 2 u) / (u + x) ^ 2
      ≤ ∫ u in Set.Ioi (0 : ℝ), (1 / 8 : ℝ) * ((u + x) ^ 2)⁻¹ := by
        refine setIntegral_mono_on hL_int hR_int measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (one_div_12_sub_bernoulliKernel_two_le u) (by positivity)
    _ = 1 / (8 * x) := by
        rw [integral_const_mul, (integrableOn_inv_add_sq_Ioi hx).2]
        ring

/-- Explicit remainder bound `|stirlingRemainderReal x| ≤ 1 / (6 * x)` (in fact `≤ 1 / (8 * x)`)
for all `x > 0`. -/
theorem abs_stirlingRemainderReal_le {x : ℝ} (hx : 0 < x) :
    |stirlingRemainderReal x| ≤ 1 / (6 * x) := by
  rw [abs_of_nonneg (stirlingRemainderReal_nonneg hx)]
  have hle := stirlingRemainderReal_le hx
  have hinv : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
  linarith [show 1 / (8 * x) = (1 / 8 : ℝ) * x⁻¹ by ring,
    show 1 / (6 * x) = (1 / 6 : ℝ) * x⁻¹ by ring]

/-- Asymptotic `stirlingRemainderReal x = O(x⁻¹)` as `x → +∞`. -/
theorem stirlingRemainderReal_isBigO_inv :
    stirlingRemainderReal =O[atTop] (fun x : ℝ => x⁻¹) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1 / 6, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr hx.le)]
  exact (abs_stirlingRemainderReal_le hx).trans_eq (by ring)

private lemma integral_log_add_zero_to_nat {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∫ t in (0 : ℝ)..N, Real.log (t + x) =
      ((N : ℝ) + x) * Real.log ((N : ℝ) + x) - N - x * Real.log x := by
  let F : ℝ → ℝ := fun t => (t + x) * Real.log (t + x) - (t + x)
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) N, HasDerivAt F (Real.log (t + x)) t := by
    intro t ht
    rw [Set.uIcc_of_le (Nat.cast_nonneg N)] at ht
    have htx : 0 < t + x := add_pos_of_nonneg_of_pos ht.1 hx
    have h1 : HasDerivAt (fun u : ℝ => u + x) 1 t := (hasDerivAt_id' t).add_const x
    have h2 : HasDerivAt (fun u : ℝ => Real.log (u + x)) (t + x)⁻¹ t := by
      simpa [Function.comp_def] using (Real.hasDerivAt_log htx.ne').comp t h1
    have h3 : HasDerivAt (fun u : ℝ => (u + x) * Real.log (u + x))
        (1 * Real.log (t + x) + (t + x) * (t + x)⁻¹) t := h1.mul h2
    convert h3.sub h1 using 1
    field_simp [htx.ne']
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.log (t + x)) volume 0 N := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (Nat.cast_nonneg N)]
    refine ContinuousOn.comp Real.continuousOn_log (continuous_id.add continuous_const).continuousOn
      fun t ht => ?_
    exact (add_pos_of_nonneg_of_pos ht.1 hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F, zero_add]
  ring

private lemma logGammaSeq_eq_eulerMaclaurin {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    Real.BohrMollerup.logGammaSeq x N =
      (x - 1 / 2) * Real.log x +
        (Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2) -
        ((N : ℝ) + x + 1 / 2) * Real.log (1 + x / N) +
        1 / (12 * x) - 1 / (12 * ((N : ℝ) + x)) -
        ∫ t in (0 : ℝ)..N, bernoulliKernel 2 t / (t + x) ^ 2 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h0N : (0 : ℝ) ≤ N := hN0.le
  have hNx : 0 < (N : ℝ) + x := add_pos hN0 hx
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivAt (fun u => Real.log (u + x)) (t + x)⁻¹ t := by
    intro t ht
    have htx : 0 < t + x := add_pos_of_nonneg_of_pos ht.1 hx
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log htx.ne').comp t ((hasDerivAt_id' t).add_const x)
  have hf' : ContinuousOn (fun t : ℝ => (t + x)⁻¹) (Set.Icc (0 : ℝ) N) :=
    ((continuous_id.add continuous_const).continuousOn).inv₀ fun t ht =>
      (add_pos_of_nonneg_of_pos ht.1 hx).ne'
  have hem1 := euler_maclaurin_first_order_Icc (Nat.zero_le N) hf hf'
  simp only [Nat.cast_zero, zero_add] at hem1
  rw [integral_log_add_zero_to_nat hx N] at hem1
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) N,
      HasDerivAt (fun u : ℝ => (u + x)⁻¹) (-((t + x) ^ 2)⁻¹) t := by
    intro t ht
    have htx : 0 < t + x := add_pos_of_nonneg_of_pos ht.1 hx
    have hinv := ((hasDerivAt_id' t).add_const x).inv htx.ne'
    convert hinv using 1
    ring
  have hg' : ContinuousOn (fun t : ℝ => -((t + x) ^ 2)⁻¹) (Set.Icc (0 : ℝ) N) := by
    refine (((continuous_id.add continuous_const).pow 2).continuousOn.inv₀ fun t ht => ?_).neg
    exact pow_ne_zero 2 (add_pos_of_nonneg_of_pos ht.1 hx).ne'
  have hibp := integral_bernoulliKernel_mul_eq_sub (j := 1) le_rfl h0N hg hg'
  have hbk20 : bernoulliKernel 2 (0 : ℝ) = 1 / 12 := by simpa using bernoulliKernel_two_natCast 0
  have hbk2N : bernoulliKernel 2 (N : ℝ) = 1 / 12 := bernoulliKernel_two_natCast N
  simp only [bernoulliKernel_one, show (1 + 1 : ℕ) = 2 by rfl, hbk20, hbk2N] at hibp
  have hcongr2 : ∫ t in (0 : ℝ)..N, bernoulliKernel 2 t * -((t + x) ^ 2)⁻¹ =
      -∫ t in (0 : ℝ)..N, bernoulliKernel 2 t / (t + x) ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hcongr2] at hibp
  have hsum_range : ∑ m ∈ Finset.range (N + 1), Real.log (x + m) =
      ∑ m ∈ Finset.Icc 0 N, Real.log (m + x) := by
    rw [← Nat.Ico_zero_eq_range]
    have hset : Finset.Ico 0 (N + 1) = Finset.Icc 0 N := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring_nf
  have hlog_fac : Real.log (Nat.factorial N : ℝ) =
      Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2 + ((N : ℝ) + 1 / 2) * Real.log N - N := by
    have hst_pos : 0 < Stirling.stirlingSeq N := by
      rw [Stirling.stirlingSeq]
      positivity
    have hfac_eq : (Nat.factorial N : ℝ) =
        Stirling.stirlingSeq N * (Real.sqrt (2 * N) * ((N : ℝ) / Real.exp 1) ^ N) := by
      rw [Stirling.stirlingSeq]
      have hden : Real.sqrt (2 * (N : ℝ)) * ((N : ℝ) / Real.exp 1) ^ N ≠ 0 := by positivity
      field_simp [hden]
    rw [hfac_eq, Real.log_mul hst_pos.ne' (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by positivity), Real.log_mul two_ne_zero hN0.ne',
      Real.log_pow, Real.log_div hN0.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have hlog_add : Real.log ((N : ℝ) + x) = Real.log N + Real.log (1 + x / N) := by
    have h1 : (N : ℝ) + x = (N : ℝ) * (1 + x / N) := by
      field_simp [hN0.ne']
    rw [h1, Real.log_mul hN0.ne' (by positivity)]
  rw [Real.BohrMollerup.logGammaSeq]
  change x * Real.log N + Real.log (Nat.factorial N : ℝ) -
      ∑ m ∈ Finset.range (N + 1), Real.log (x + m) = _
  rw [hsum_range, hem1, hibp, hlog_fac, hlog_add]
  have h12 : (1 : ℝ) / (12 * ((N : ℝ) + x)) = 1 / 12 * ((N : ℝ) + x)⁻¹ := by
    rw [one_div, mul_inv, one_div]
  rw [h12]
  ring

private lemma tendsto_add_mul_log_one_add_div {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => ((N : ℝ) + x + 1 / 2) * Real.log (1 + x / N)) atTop (𝓝 x) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hxN : Tendsto (fun N : ℕ => x / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul x
  have hder : HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := (hasDerivAt_id' 0).const_add 1
    have hne : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    simpa [Function.comp_def] using (Real.hasDerivAt_log hne).comp 0 h1
  have hslope : Tendsto (fun u : ℝ => Real.log (1 + u) / u) (𝓝[≠] 0) (𝓝 1) := by
    have hs := hder.tendsto_slope_zero
    simpa [slope, sub_zero, add_zero, Real.log_one, div_eq_inv_mul] using hs
  have hNx_ratio : Tendsto (fun N : ℕ => Real.log (1 + x / N) / (x / N)) atTop (𝓝 1) := by
    have hxN_ne : ∀ᶠ N : ℕ in atTop, x / (N : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact div_ne_zero hx.ne' (Nat.cast_ne_zero.mpr (by omega))
    exact hslope.comp (tendsto_nhdsWithin_iff.mpr ⟨hxN, hxN_ne⟩)
  have hmain : Tendsto (fun N : ℕ => (N : ℝ) * Real.log (1 + x / N)) atTop (𝓝 x) := by
    have heq : ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Real.log (1 + x / N) = x * (Real.log (1 + x / N) / (x / N)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hx.ne', hNne]
    rw [tendsto_congr' heq]
    simpa using hNx_ratio.const_mul x
  have hrest : Tendsto (fun N : ℕ => (x + 1 / 2) * Real.log (1 + x / N)) atTop (𝓝 0) := by
    have hlog0 : Tendsto (fun N : ℕ => Real.log (1 + x / N)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => 1 + x / (N : ℝ)) atTop (𝓝 1) := by
        simpa using hxN.const_add 1
      have hcomp := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
      simpa [Function.comp_def, Real.log_one] using hcomp
    simpa using hlog0.const_mul (x + 1 / 2)
  have hsum : (fun N : ℕ => ((N : ℝ) + x + 1 / 2) * Real.log (1 + x / N)) =
      fun N : ℕ => (N : ℝ) * Real.log (1 + x / N) + (x + 1 / 2) * Real.log (1 + x / N) := by
    ext N
    ring
  rw [hsum]
  simpa using hmain.add hrest

/-- Exact Euler–Maclaurin formula for `Real.log (Real.Gamma x)` (`0 < x`):
`Real.log (Real.Gamma x) = (x - 1/2) * Real.log x - x + Real.log (2 * π) / 2 + stirlingRemainderReal x`. -/
theorem real_log_gamma_eq_stirling {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + stirlingRemainderReal x := by
  have h1 := Real.BohrMollerup.tendsto_log_gamma hx
  have hst : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2)
      atTop (𝓝 (Real.log (2 * Real.pi) / 2)) := by
    have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hlog_st := (Real.continuousAt_log hsq.ne').tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
    have hlim : Real.log (Real.sqrt Real.pi) + Real.log 2 / 2 = Real.log (2 * Real.pi) / 2 := by
      rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul two_ne_zero Real.pi_pos.ne']
      ring
    simpa [Function.comp_def, hlim] using hlog_st.add (tendsto_const_nhds (x := Real.log 2 / 2))
  have htail1 : Tendsto (fun N : ℕ => (1 : ℝ) / (12 * ((N : ℝ) + x))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 12 * ((N : ℝ) + x)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine h1.inv_tendsto_atTop.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [← one_div]
    rfl
  have hint_tendsto : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..N, bernoulliKernel 2 t / (t + x) ^ 2)
      atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), bernoulliKernel 2 t / (t + x) ^ 2)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_bernoulliKernel_two_div_add_sq hx)
      tendsto_natCast_atTop_atTop
  have hrhs : Tendsto (fun N : ℕ =>
      (x - 1 / 2) * Real.log x +
        (Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2) -
        ((N : ℝ) + x + 1 / 2) * Real.log (1 + x / N) +
        1 / (12 * x) - 1 / (12 * ((N : ℝ) + x)) -
        ∫ t in (0 : ℝ)..N, bernoulliKernel 2 t / (t + x) ^ 2)
      atTop
      (𝓝 ((x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + stirlingRemainderReal x)) := by
    have h2 := (tendsto_const_nhds (x := (x - 1 / 2) * Real.log x)).add hst
    have h3 := h2.sub (tendsto_add_mul_log_one_add_div hx)
    have h4 := h3.add (tendsto_const_nhds (x := 1 / (12 * x)))
    have h5 := h4.sub htail1
    have h6 := h5.sub hint_tendsto
    refine h6.trans_eq ?_
    congr 1
    rw [stirlingRemainderReal]
    ring
  have hev : (fun N : ℕ => Real.BohrMollerup.logGammaSeq x N) =ᶠ[atTop] fun N : ℕ =>
      (x - 1 / 2) * Real.log x +
        (Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2) -
        ((N : ℝ) + x + 1 / 2) * Real.log (1 + x / N) +
        1 / (12 * x) - 1 / (12 * ((N : ℝ) + x)) -
        ∫ t in (0 : ℝ)..N, bernoulliKernel 2 t / (t + x) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact logGammaSeq_eq_eulerMaclaurin hx hN
  exact tendsto_nhds_unique h1 (hrhs.congr' hev.symm)

/-- Multiplicative real Stirling identity for `Real.Gamma x` (`0 < x`):
`Real.Gamma x = Real.sqrt (2 * π) * x ^ (x - 1/2) * Real.exp (-x + stirlingRemainderReal x)`. -/
theorem real_gamma_eq_stirling {x : ℝ} (hx : 0 < x) :
    Real.Gamma x =
      Real.sqrt (2 * Real.pi) * x ^ (x - 1 / 2) * Real.exp (-x + stirlingRemainderReal x) := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rw [← Real.exp_log hG, real_log_gamma_eq_stirling hx]
  have hsqrt : Real.sqrt (2 * Real.pi) = Real.exp (Real.log (2 * Real.pi) / 2) := by
    rw [← Real.log_sqrt (by positivity), Real.exp_log (Real.sqrt_pos.mpr (by positivity))]
  have hrpow : x ^ (x - 1 / 2) = Real.exp ((x - 1 / 2) * Real.log x) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  rw [hsqrt, hrpow, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Explicit `1 / (6 * x)` error bound for `Real.log (Real.Gamma x)` (`0 < x`). -/
theorem abs_real_log_gamma_sub_le {x : ℝ} (hx : 0 < x) :
    |Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2)| ≤
      1 / (6 * x) := by
  rw [real_log_gamma_eq_stirling hx]
  convert abs_stirlingRemainderReal_le hx using 2
  ring

/-- Big-O asymptotic for `Real.log (Real.Gamma x)` as `x → +∞`:
`Real.log (Real.Gamma x) - ((x - 1/2) * Real.log x - x + Real.log (2 * π) / 2) = O(x⁻¹)`. -/
theorem real_log_gamma_sub_isBigO_inv :
    (fun x : ℝ =>
      Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2))
      =O[atTop] (fun x : ℝ => x⁻¹) := by
  refine stirlingRemainderReal_isBigO_inv.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [real_log_gamma_eq_stirling hx]
  ring

/-- Ratio limit form of real Stirling's formula for `Real.Gamma x` as `x → +∞`. -/
theorem real_gamma_div_stirling_tendsto :
    Tendsto
      (fun x : ℝ => Real.Gamma x / (Real.sqrt (2 * Real.pi) * x ^ (x - 1 / 2) * Real.exp (-x)))
      atTop (𝓝 1) := by
  have hev : (fun x : ℝ =>
      Real.Gamma x / (Real.sqrt (2 * Real.pi) * x ^ (x - 1 / 2) * Real.exp (-x))) =ᶠ[atTop]
      fun x : ℝ => Real.exp (stirlingRemainderReal x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [real_gamma_eq_stirling hx, Real.exp_add]
    have hden : Real.sqrt (2 * Real.pi) * x ^ (x - 1 / 2) * Real.exp (-x) ≠ 0 := by positivity
    field_simp [hden]
  have hrem0 : Tendsto stirlingRemainderReal atTop (𝓝 0) :=
    stirlingRemainderReal_isBigO_inv.trans_tendsto tendsto_inv_atTop_zero
  exact (Real.continuous_exp.tendsto 0 |>.comp hrem0).congr' hev.symm |>.trans (by simp)

/-- Real Stirling asymptotic for `Real.Gamma (n + 1)` over `ℕ`:
`Real.Gamma (n + 1) ~ √(2 * n * π) * (n / exp 1) ^ n` as `n → ∞`. -/
theorem real_gamma_nat_isEquivalent_stirling :
    (fun n : ℕ => Real.Gamma (n + 1)) ~[atTop]
      fun n => Real.sqrt (2 * n * Real.pi) * (n / Real.exp 1) ^ n := by
  simpa only [Real.Gamma_nat_eq_factorial] using Stirling.factorial_isEquivalent_stirling

/-- Real Stirling asymptotic for `Real.Gamma (x + 1)` over `ℝ`:
`Real.Gamma (x + 1) ~ √(2 * π * x) * (x / exp 1) ^ x` as `x → +∞`. -/
theorem real_gamma_isEquivalent_stirling :
    (fun x : ℝ => Real.Gamma (x + 1)) ~[atTop]
      fun x => Real.sqrt (2 * Real.pi * x) * (x / Real.exp 1) ^ x := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · have hev : (fun x : ℝ => Real.Gamma (x + 1) /
        (Real.sqrt (2 * Real.pi * x) * (x / Real.exp 1) ^ x)) =ᶠ[atTop]
        fun x : ℝ => Real.exp (stirlingRemainderReal x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.Gamma_add_one hx.ne', real_gamma_eq_stirling hx, Real.exp_add]
      have hxpow : x * x ^ (x - 1 / 2) = x ^ (1 / 2 : ℝ) * x ^ x := by
        calc x * x ^ (x - 1 / 2)
            = x ^ (1 : ℝ) * x ^ (x - 1 / 2) := by rw [Real.rpow_one]
          _ = x ^ (1 + (x - 1 / 2)) := (Real.rpow_add hx _ _).symm
          _ = x ^ ((1 / 2 : ℝ) + x) := by congr 1; ring
          _ = x ^ (1 / 2 : ℝ) * x ^ x := Real.rpow_add hx _ _
      have hsq : Real.sqrt (2 * Real.pi * x) = Real.sqrt (2 * Real.pi) * x ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow]
        congr 1
        exact Real.sqrt_eq_rpow x
      have hdivpow : (x / Real.exp 1) ^ x = x ^ x * Real.exp (-x) := by
        rw [Real.div_rpow hx.le (Real.exp_pos 1).le, ← Real.exp_mul, one_mul,
          div_eq_mul_inv, ← Real.exp_neg]
      rw [hsq, hdivpow]
      calc x * (Real.sqrt (2 * Real.pi) * x ^ (x - 1 / 2) * (Real.exp (-x) * Real.exp (stirlingRemainderReal x))) /
            (Real.sqrt (2 * Real.pi) * x ^ (1 / 2 : ℝ) * (x ^ x * Real.exp (-x)))
          = (Real.sqrt (2 * Real.pi) * (x * x ^ (x - 1 / 2)) * Real.exp (-x) * Real.exp (stirlingRemainderReal x)) /
            (Real.sqrt (2 * Real.pi) * (x ^ (1 / 2 : ℝ) * x ^ x) * Real.exp (-x)) := by ring
        _ = (Real.sqrt (2 * Real.pi) * (x ^ (1 / 2 : ℝ) * x ^ x) * Real.exp (-x) * Real.exp (stirlingRemainderReal x)) /
            (Real.sqrt (2 * Real.pi) * (x ^ (1 / 2 : ℝ) * x ^ x) * Real.exp (-x)) := by rw [hxpow]
        _ = Real.exp (stirlingRemainderReal x) := by
            have hden : Real.sqrt (2 * Real.pi) * (x ^ (1 / 2 : ℝ) * x ^ x) * Real.exp (-x) ≠ 0 := by positivity
            field_simp [hden]
    have hrem0 : Tendsto stirlingRemainderReal atTop (𝓝 0) :=
      stirlingRemainderReal_isBigO_inv.trans_tendsto tendsto_inv_atTop_zero
    exact (Real.continuous_exp.tendsto 0 |>.comp hrem0).congr' hev.symm |>.trans (by simp)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity

end RealStirling

section ComplexRemainder

/-- Complex Euler–Maclaurin Stirling remainder on `Complex.slitPlane`:
`stirlingRemainder s = 1 / (12 * s) - ∫ u in Ioi 0, (bernoulliKernel 2 u : ℂ) / (u + s) ^ 2`. -/
noncomputable def stirlingRemainder (s : ℂ) : ℂ :=
  (1 : ℂ) / (12 * s) -
    ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2

/-- For `s ∈ Complex.slitPlane`, `0 < Real.cos (s.arg / 2)`. -/
theorem cos_half_arg_pos_of_mem_slitPlane {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    0 < Real.cos (s.arg / 2) := by
  have h1 : -Real.pi < s.arg := Complex.neg_pi_lt_arg s
  have h2 : s.arg < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi s) (Complex.slitPlane_arg_ne_pi hs)
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- Geometric lower bound for `u + s` (`0 ≤ u`, `s ∈ Complex.slitPlane`):
`Real.cos (s.arg / 2) * (u + ‖s‖) ≤ ‖(u : ℂ) + s‖`. -/
theorem cos_half_arg_mul_le_norm_ofReal_add {s : ℂ} (hs : s ∈ Complex.slitPlane) {u : ℝ}
    (hu : 0 ≤ u) :
    Real.cos (s.arg / 2) * (u + ‖s‖) ≤ ‖(u : ℂ) + s‖ := by
  have hc : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  have hsq : (Real.cos (s.arg / 2) * (u + ‖s‖)) ^ 2 ≤ ‖(u : ℂ) + s‖ ^ 2 := by
    have hnormSq : ‖(u : ℂ) + s‖ ^ 2 = u ^ 2 + 2 * u * s.re + ‖s‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hsSq : s.re * s.re + s.im * s.im = ‖s‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
      linarith
    have hcos : Real.cos s.arg = 2 * Real.cos (s.arg / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (s.arg / 2)
      rwa [show 2 * (s.arg / 2) = s.arg by ring] at h
    have hre : s.re = ‖s‖ * Real.cos s.arg := (Complex.norm_mul_cos_arg s).symm
    have hsin : Real.sin (s.arg / 2) ^ 2 = 1 - Real.cos (s.arg / 2) ^ 2 :=
      Real.sin_sq (s.arg / 2)
    have hdiff : ‖(u : ℂ) + s‖ ^ 2 - (Real.cos (s.arg / 2) * (u + ‖s‖)) ^ 2 =
        Real.sin (s.arg / 2) ^ 2 * (u - ‖s‖) ^ 2 := by
      rw [hnormSq, hre, hcos, hsin]
      ring
    have hpos : 0 ≤ Real.sin (s.arg / 2) ^ 2 * (u - ‖s‖) ^ 2 := by positivity
    linarith
  have hnn : 0 ≤ Real.cos (s.arg / 2) * (u + ‖s‖) := by positivity
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- For `s ∈ Complex.slitPlane` and `0 ≤ u`, `(u : ℂ) + s ≠ 0`. -/
theorem ofReal_add_ne_zero_of_mem_slitPlane {s : ℂ} (hs : s ∈ Complex.slitPlane) {u : ℝ}
    (hu : 0 ≤ u) :
    (u : ℂ) + s ≠ 0 := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hpos : 0 < Real.cos (s.arg / 2) * (u + ‖s‖) := by
    have := cos_half_arg_pos_of_mem_slitPlane hs
    have : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    positivity
  exact norm_pos_iff.mp (hpos.trans_le (cos_half_arg_mul_le_norm_ofReal_add hs hu))

/-- Integrability of `u ↦ (bernoulliKernel 2 u : ℂ) / ((u : ℂ) + s) ^ 2` on `(0, ∞)` for
`s ∈ Complex.slitPlane`. -/
theorem integrableOn_complex_bernoulliKernel_two_div_sq {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    IntegrableOn (fun u : ℝ => ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2)
      (Set.Ioi 0) := by
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  have hc : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  let C : ℝ := (1 / 12 : ℝ) * (Real.cos (s.arg / 2))⁻¹ ^ 2
  have hdom : IntegrableOn (fun u : ℝ => C * ((u + ‖s‖) ^ 2)⁻¹) (Set.Ioi 0) :=
    (integrableOn_inv_add_sq_Ioi hs0).1.const_mul C
  refine Integrable.mono hdom ?_ ?_
  · have hcont : ContinuousOn
        (fun u : ℝ => ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2) (Set.Ioi 0) := by
      refine (Complex.continuous_ofReal.comp
        (continuous_bernoulliKernel (by norm_num))).continuousOn.div ?_ ?_
      · exact ((Complex.continuous_ofReal.add continuous_const).pow 2).continuousOn
      · intro u hu
        exact pow_ne_zero 2 (ofReal_add_ne_zero_of_mem_slitPlane hs (le_of_lt hu))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hlow : Real.cos (s.arg / 2) * (u + ‖s‖) ≤ ‖(u : ℂ) + s‖ :=
      cos_half_arg_mul_le_norm_ofReal_add hs hu0.le
    have hinv : ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by
      calc ‖(u : ℂ) + s‖⁻¹
          ≤ (Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹ := inv_anti₀ (by positivity) hlow
        _ = (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, div_eq_mul_inv, ← inv_pow]
    have hsqinv : (‖(u : ℂ) + s‖⁻¹) ^ 2 ≤ ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hCnn : 0 ≤ C * ((u + ‖s‖) ^ 2)⁻¹ := by positivity
    rw [Real.norm_of_nonneg hCnn]
    calc |bernoulliKernel 2 u| * (‖(u : ℂ) + s‖⁻¹) ^ 2
        ≤ (1 / 12 : ℝ) * ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 :=
          mul_le_mul (bernoulliKernel_two_abs_le u) hsqinv (by positivity) (by positivity)
      _ = C * ((u + ‖s‖) ^ 2)⁻¹ := by
          simp only [C, mul_pow, inv_pow]
          ring

private lemma integral_one_div_twelve_ofReal_add_sq {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    ∫ u in Set.Ioi (0 : ℝ), ((1 / 12 : ℂ) / ((u : ℂ) + s) ^ 2) = (1 : ℂ) / (12 * s) := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hr0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  let F : ℝ → ℂ := fun u => -(1 : ℂ) / (12 * ((u : ℂ) + s))
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt F ((1 / 12 : ℂ) / ((u : ℂ) + s) ^ 2) u := by
    intro u hu
    have hu_ne : (u : ℂ) + s ≠ 0 := ofReal_add_ne_zero_of_mem_slitPlane hs hu
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + s) 1 u := by
      simpa using Complex.ofRealCLM.hasDerivAt.add_const s
    have h2 : HasDerivAt (fun t : ℝ => 12 * ((t : ℂ) + s)) 12 u := by
      simpa using h1.const_mul (12 : ℂ)
    have hden : 12 * ((u : ℂ) + s) ≠ 0 := mul_ne_zero (by norm_num) hu_ne
    have hinv := (h2.inv hden).neg
    have hF : F = fun t : ℝ => -(12 * ((t : ℂ) + s))⁻¹ := by
      ext t
      simp [F, div_eq_mul_inv]
    rw [hF]
    convert hinv using 1
    field_simp [hu_ne]
  have hint : IntegrableOn (fun u : ℝ => (1 / 12 : ℂ) / ((u : ℂ) + s) ^ 2) (Set.Ioi 0) := by
    let C : ℝ := (1 / 12 : ℝ) * (Real.cos (s.arg / 2))⁻¹ ^ 2
    refine Integrable.mono ((integrableOn_inv_add_sq_Ioi hr0).1.const_mul C) ?_ ?_
    · refine (ContinuousOn.div continuousOn_const
        ((Complex.continuous_ofReal.add continuous_const).pow 2).continuousOn fun u hu =>
          pow_ne_zero 2 (ofReal_add_ne_zero_of_mem_slitPlane hs (le_of_lt hu))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      have hlow : Real.cos (s.arg / 2) * (u + ‖s‖) ≤ ‖(u : ℂ) + s‖ :=
        cos_half_arg_mul_le_norm_ofReal_add hs hu0.le
      have hinv : ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by
        calc ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹ :=
              inv_anti₀ (by positivity) hlow
          _ = (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
      have hsqinv : (‖(u : ℂ) + s‖⁻¹) ^ 2 ≤ ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinv 2
      rw [norm_div, norm_pow, show ‖(1 / 12 : ℂ)‖ = (1 / 12 : ℝ) by norm_num, div_eq_mul_inv,
        ← inv_pow, Real.norm_of_nonneg (by positivity)]
      calc (1 / 12 : ℝ) * (‖(u : ℂ) + s‖⁻¹) ^ 2
          ≤ (1 / 12 : ℝ) * ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 := by gcongr
        _ = C * ((u + ‖s‖) ^ 2)⁻¹ := by simp only [C, mul_pow, inv_pow]; ring
  have htend : Tendsto F atTop (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlow : Tendsto (fun u : ℝ => (12 * Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹) atTop (𝓝 0) := by
      have hpos : 0 < 12 * Real.cos (s.arg / 2) := by positivity
      exact ((tendsto_id.atTop_add tendsto_const_nhds).const_mul_atTop hpos).inv_tendsto_atTop
    refine squeeze_zero' ?_ ?_ hlow
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      have hnorm : 0 < 12 * Real.cos (s.arg / 2) * (u + ‖s‖) := by positivity
      have hbound : 12 * Real.cos (s.arg / 2) * (u + ‖s‖) ≤ 12 * ‖(u : ℂ) + s‖ := by
        have := cos_half_arg_mul_le_norm_ofReal_add hs hu
        linarith
      simp only [F, norm_div, norm_neg, norm_one, norm_mul,
        show ‖(12 : ℂ)‖ = 12 by norm_num, one_div]
      exact inv_anti₀ hnorm hbound
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  simp [F, div_eq_mul_inv]

/-- Single-integral form of `stirlingRemainder s` on `Complex.slitPlane`. -/
theorem stirlingRemainder_eq_integral {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    stirlingRemainder s =
      ∫ u in Set.Ioi (0 : ℝ), (((1 / 12 : ℝ) - bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2 := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hr0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  have h1 : IntegrableOn (fun u : ℝ => (1 / 12 : ℂ) / ((u : ℂ) + s) ^ 2) (Set.Ioi 0) := by
    let C : ℝ := (1 / 12 : ℝ) * (Real.cos (s.arg / 2))⁻¹ ^ 2
    refine Integrable.mono ((integrableOn_inv_add_sq_Ioi hr0).1.const_mul C) ?_ ?_
    · refine (ContinuousOn.div continuousOn_const
        ((Complex.continuous_ofReal.add continuous_const).pow 2).continuousOn fun u hu =>
          pow_ne_zero 2 (ofReal_add_ne_zero_of_mem_slitPlane hs (le_of_lt hu))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      have hlow := cos_half_arg_mul_le_norm_ofReal_add hs hu0.le
      have hinv : ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by
        calc ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹ :=
              inv_anti₀ (by positivity) hlow
          _ = (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
      have hsqinv : (‖(u : ℂ) + s‖⁻¹) ^ 2 ≤ ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinv 2
      rw [norm_div, norm_pow, show ‖(1 / 12 : ℂ)‖ = (1 / 12 : ℝ) by norm_num, div_eq_mul_inv,
        ← inv_pow, Real.norm_of_nonneg (by positivity)]
      calc (1 / 12 : ℝ) * (‖(u : ℂ) + s‖⁻¹) ^ 2
          ≤ (1 / 12 : ℝ) * ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 := by gcongr
        _ = C * ((u + ‖s‖) ^ 2)⁻¹ := by simp only [C, mul_pow, inv_pow]; ring
  have h2 := integrableOn_complex_bernoulliKernel_two_div_sq hs
  have hsub : (fun u : ℝ => (((1 / 12 : ℝ) - bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2) =
      fun u : ℝ => (1 / 12 : ℂ) / ((u : ℂ) + s) ^ 2 -
        ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2 := by
    ext u
    push_cast
    ring
  rw [hsub, integral_sub h1 h2, integral_one_div_twelve_ofReal_add_sq hs]
  rfl

/-- Explicit upper bound for `‖stirlingRemainder s‖` on `Complex.slitPlane`:
`‖stirlingRemainder s‖ ≤ (1 + (Real.cos (s.arg / 2))⁻¹ ^ 2) / (12 * ‖s‖)`. -/
theorem norm_stirlingRemainder_le {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    ‖stirlingRemainder s‖ ≤ (1 + (Real.cos (s.arg / 2))⁻¹ ^ 2) / (12 * ‖s‖) := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hr0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  have hint_bd :
      ‖∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2‖ ≤
        (Real.cos (s.arg / 2))⁻¹ ^ 2 / (12 * ‖s‖) := by
    let C : ℝ := (1 / 12 : ℝ) * (Real.cos (s.arg / 2))⁻¹ ^ 2
    have hdom : IntegrableOn (fun u : ℝ => C * ((u + ‖s‖) ^ 2)⁻¹) (Set.Ioi 0) :=
      (integrableOn_inv_add_sq_Ioi hr0).1.const_mul C
    calc ‖∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2‖
        ≤ ∫ u in Set.Ioi (0 : ℝ), ‖((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), C * ((u + ‖s‖) ^ 2)⁻¹ := by
          refine setIntegral_mono_on (integrableOn_complex_bernoulliKernel_two_div_sq hs).norm hdom
            measurableSet_Ioi fun u hu => ?_
          have hu0 : 0 < u := hu
          have hlow := cos_half_arg_mul_le_norm_ofReal_add hs hu0.le
          have hinv : ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by
            calc ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹ :=
                  inv_anti₀ (by positivity) hlow
              _ = (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
          have hsqinv : (‖(u : ℂ) + s‖⁻¹) ^ 2 ≤ ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hinv 2
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, div_eq_mul_inv, ← inv_pow]
          calc |bernoulliKernel 2 u| * (‖(u : ℂ) + s‖⁻¹) ^ 2
              ≤ (1 / 12 : ℝ) * ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 2 :=
                mul_le_mul (bernoulliKernel_two_abs_le u) hsqinv (by positivity) (by positivity)
            _ = C * ((u + ‖s‖) ^ 2)⁻¹ := by simp only [C, mul_pow, inv_pow]; ring
      _ = (Real.cos (s.arg / 2))⁻¹ ^ 2 / (12 * ‖s‖) := by
          rw [integral_const_mul, (integrableOn_inv_add_sq_Ioi hr0).2]
          simp only [C]
          ring
  rw [stirlingRemainder]
  calc ‖(1 : ℂ) / (12 * s) -
        ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2‖
      ≤ ‖(1 : ℂ) / (12 * s)‖ +
        ‖∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 2‖ :=
        norm_sub_le _ _
    _ ≤ 1 / (12 * ‖s‖) + (Real.cos (s.arg / 2))⁻¹ ^ 2 / (12 * ‖s‖) := by
        have hlead : ‖(1 : ℂ) / (12 * s)‖ = 1 / (12 * ‖s‖) := by
          rw [norm_div, norm_one, norm_mul, show ‖(12 : ℂ)‖ = 12 by norm_num]
        linarith
    _ = (1 + (Real.cos (s.arg / 2))⁻¹ ^ 2) / (12 * ‖s‖) := by ring

/-- Derivative of `stirlingRemainder` on `Complex.slitPlane`, proved by parametric dominated
differentiation under the integral sign. -/
theorem hasDerivAt_stirlingRemainder {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    HasDerivAt stirlingRemainder
      (-1 / (12 * s ^ 2) +
        2 * ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3)
      s := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hr0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc0 : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  let δ : ℝ := Real.cos (s.arg / 2) * ‖s‖ / 2
  have hδ : 0 < δ := by positivity
  have hlow_ball : ∀ z ∈ Metric.ball s δ, ∀ u : ℝ, 0 ≤ u →
      Real.cos (s.arg / 2) / 2 * (u + ‖s‖) ≤ ‖(u : ℂ) + z‖ := by
    intro z hz u hu
    have hz_dist : ‖z - s‖ < δ := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
    have htri : ‖(u : ℂ) + s‖ - ‖z - s‖ ≤ ‖(u : ℂ) + z‖ := by
      have heq : (u : ℂ) + s = ((u : ℂ) + z) + (s - z) := by ring
      have h := norm_add_le ((u : ℂ) + z) (s - z)
      rw [← heq, norm_sub_rev] at h
      linarith
    have hs_low := cos_half_arg_mul_le_norm_ofReal_add hs hu
    nlinarith [show δ = Real.cos (s.arg / 2) * ‖s‖ / 2 by rfl]
  have hne_ball : ∀ z ∈ Metric.ball s δ, ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ≠ 0 := by
    intro z hz u hu
    have hpos : 0 < Real.cos (s.arg / 2) / 2 * (u + ‖s‖) := by positivity
    exact norm_pos_iff.mp (hpos.trans_le (hlow_ball z hz u hu))
  let F : ℂ → ℝ → ℂ := fun z u => ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + z) ^ 2
  let F' : ℂ → ℝ → ℂ := fun z u => -2 * ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + z) ^ 3
  let bound : ℝ → ℝ := fun u => (1 / 6 : ℝ) * (Real.cos (s.arg / 2) / 2)⁻¹ ^ 3 * ((u + ‖s‖) ^ 3)⁻¹
  have hF_meas : ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds s hδ] with z hz
    have hcont : ContinuousOn (F z) (Set.Ioi 0) := by
      refine (Complex.continuous_ofReal.comp
        (continuous_bernoulliKernel (by norm_num))).continuousOn.div ?_ ?_
      · exact ((Complex.continuous_ofReal.add continuous_const).pow 2).continuousOn
      · intro u hu
        exact pow_ne_zero 2 (hne_ball z hz u (le_of_lt hu))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hF_int : Integrable (F s) (volume.restrict (Set.Ioi 0)) :=
    integrableOn_complex_bernoulliKernel_two_div_sq hs
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (F' s) (Set.Ioi 0) := by
      refine ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_bernoulliKernel (by norm_num))))).continuousOn.div ?_ ?_
      · exact ((Complex.continuous_ofReal.add continuous_const).pow 3).continuousOn
      · intro u hu
        exact pow_ne_zero 3 (ofReal_add_ne_zero_of_mem_slitPlane hs (le_of_lt hu))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have h_bound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hu0 : 0 < u := hu
    have hlow := hlow_ball z hz u hu0.le
    have hinv : ‖(u : ℂ) + z‖⁻¹ ≤ (Real.cos (s.arg / 2) / 2)⁻¹ * (u + ‖s‖)⁻¹ := by
      calc ‖(u : ℂ) + z‖⁻¹ ≤ (Real.cos (s.arg / 2) / 2 * (u + ‖s‖))⁻¹ :=
            inv_anti₀ (by positivity) hlow
        _ = (Real.cos (s.arg / 2) / 2)⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
    have hcub : (‖(u : ℂ) + z‖⁻¹) ^ 3 ≤ ((Real.cos (s.arg / 2) / 2)⁻¹ * (u + ‖s‖)⁻¹) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hinv 3
    rw [show F' z u = -2 * ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + z) ^ 3 from rfl]
    rw [norm_div, norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num, Complex.norm_real,
      Real.norm_eq_abs, norm_pow, div_eq_mul_inv, ← inv_pow]
    calc 2 * |bernoulliKernel 2 u| * (‖(u : ℂ) + z‖⁻¹) ^ 3
        ≤ 2 * (1 / 12 : ℝ) * ((Real.cos (s.arg / 2) / 2)⁻¹ * (u + ‖s‖)⁻¹) ^ 3 := by
          gcongr
          exact bernoulliKernel_two_abs_le u
      _ = bound u := by
          simp only [bound, mul_pow, inv_pow]
          ring
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_inv_add_cube_Ioi hr0).1.const_mul _
  have h_diff : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ∀ z ∈ Metric.ball s δ, HasDerivAt (F · u) (F' z u) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hne : (u : ℂ) + z ≠ 0 := hne_ball z hz u (le_of_lt hu)
    have h1 : HasDerivAt (fun w : ℂ => ((u : ℂ) + w) ^ 2) (2 * ((u : ℂ) + z)) z := by
      have h0 : HasDerivAt (fun w : ℂ => ((u : ℂ) + w) ^ 2)
          ((2 : ℕ) * ((u : ℂ) + z) ^ (2 - 1) * 1) z :=
        ((hasDerivAt_id' z).const_add (u : ℂ)).pow 2
      convert h0 using 1
      ring
    have hsqne : ((u : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have hinv := (h1.inv hsqne).const_mul ((bernoulliKernel 2 u : ℝ) : ℂ)
    have hFeq : (fun w : ℂ => F w u) =
        fun w : ℂ => ((bernoulliKernel 2 u : ℝ) : ℂ) * (((u : ℂ) + w) ^ 2)⁻¹ := by
      ext w
      simp [F, div_eq_mul_inv]
    rw [hFeq]
    convert hinv using 1
    simp only [F']
    field_simp [hne]
  obtain ⟨_, hderiv_int⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hδ) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hlead : HasDerivAt (fun z : ℂ => (1 : ℂ) / (12 * z)) (-1 / (12 * s ^ 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => 12 * z) 12 s := by simpa using (hasDerivAt_id' s).const_mul 12
    have hinv := h1.inv (mul_ne_zero (by norm_num) hs0)
    have heq : (fun z : ℂ => (1 : ℂ) / (12 * z)) = fun z : ℂ => (12 * z)⁻¹ := by
      ext z; simp [one_div]
    rw [heq]
    convert hinv using 1
    field_simp [hs0]
  have hF'eq : (∫ u in Set.Ioi (0 : ℝ), F' s u) =
      -2 * ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3 := by
    have heq : (fun u : ℝ => F' s u) =
        fun u : ℝ => (-2 : ℂ) * (((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3) := by
      ext u
      dsimp only [F']
      ring
    rw [heq, integral_const_mul]
  have hres := hlead.sub hderiv_int
  rw [hF'eq] at hres
  convert hres using 1
  · ext z
    simp [stirlingRemainder, F]
  · ring

/-- `stirlingRemainder` is complex-differentiable on `Complex.slitPlane`. -/
theorem differentiableOn_stirlingRemainder : DifferentiableOn ℂ stirlingRemainder Complex.slitPlane :=
  fun _ hs => (hasDerivAt_stirlingRemainder hs).differentiableAt.differentiableWithinAt

/-- `stirlingRemainder` is holomorphic (`AnalyticOnNhd`) on `Complex.slitPlane`. -/
theorem analyticOnNhd_stirlingRemainder : AnalyticOnNhd ℂ stirlingRemainder Complex.slitPlane :=
  differentiableOn_stirlingRemainder.analyticOnNhd Complex.isOpen_slitPlane

/-- Explicit bound on `‖deriv stirlingRemainder s‖` for `s ∈ Complex.slitPlane`:
`‖deriv stirlingRemainder s‖ ≤ (1 + (Real.cos (s.arg / 2))⁻¹ ^ 3) / (12 * ‖s‖ ^ 2)`. -/
theorem norm_deriv_stirlingRemainder_le {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    ‖deriv stirlingRemainder s‖ ≤ (1 + (Real.cos (s.arg / 2))⁻¹ ^ 3) / (12 * ‖s‖ ^ 2) := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hr0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  rw [(hasDerivAt_stirlingRemainder hs).deriv]
  let C : ℝ := (1 / 12 : ℝ) * (Real.cos (s.arg / 2))⁻¹ ^ 3
  have hdom : IntegrableOn (fun u : ℝ => C * ((u + ‖s‖) ^ 3)⁻¹) (Set.Ioi 0) :=
    (integrableOn_inv_add_cube_Ioi hr0).1.const_mul C
  have h_int : IntegrableOn
      (fun u : ℝ => ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3) (Set.Ioi 0) := by
    refine Integrable.mono hdom ?_ ?_
    · refine ((Complex.continuous_ofReal.comp
        (continuous_bernoulliKernel (by norm_num))).continuousOn.div
          ((Complex.continuous_ofReal.add continuous_const).pow 3).continuousOn
          fun u hu => pow_ne_zero 3
            (ofReal_add_ne_zero_of_mem_slitPlane hs (le_of_lt hu))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      have hlow := cos_half_arg_mul_le_norm_ofReal_add hs hu0.le
      have hinv : ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by
        calc ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹ :=
              inv_anti₀ (by positivity) hlow
          _ = (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
      have hcub : (‖(u : ℂ) + s‖⁻¹) ^ 3 ≤ ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hinv 3
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, div_eq_mul_inv, ← inv_pow,
        Real.norm_of_nonneg (by positivity)]
      calc |bernoulliKernel 2 u| * (‖(u : ℂ) + s‖⁻¹) ^ 3
          ≤ (1 / 12 : ℝ) * ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 3 :=
            mul_le_mul (bernoulliKernel_two_abs_le u) hcub (by positivity) (by positivity)
        _ = C * ((u + ‖s‖) ^ 3)⁻¹ := by simp only [C, mul_pow, inv_pow]; ring
  have hint_bd :
      ‖∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3‖ ≤
        (Real.cos (s.arg / 2))⁻¹ ^ 3 / (24 * ‖s‖ ^ 2) := by
    calc ‖∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3‖
        ≤ ∫ u in Set.Ioi (0 : ℝ), ‖((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), C * ((u + ‖s‖) ^ 3)⁻¹ := by
          refine setIntegral_mono_on h_int.norm hdom measurableSet_Ioi fun u hu => ?_
          have hu0 : 0 < u := hu
          have hlow := cos_half_arg_mul_le_norm_ofReal_add hs hu0.le
          have hinv : ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by
            calc ‖(u : ℂ) + s‖⁻¹ ≤ (Real.cos (s.arg / 2) * (u + ‖s‖))⁻¹ :=
                  inv_anti₀ (by positivity) hlow
              _ = (Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹ := by rw [mul_inv, mul_comm]
          have hcub : (‖(u : ℂ) + s‖⁻¹) ^ 3 ≤ ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hinv 3
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, div_eq_mul_inv, ← inv_pow]
          calc |bernoulliKernel 2 u| * (‖(u : ℂ) + s‖⁻¹) ^ 3
              ≤ (1 / 12 : ℝ) * ((Real.cos (s.arg / 2))⁻¹ * (u + ‖s‖)⁻¹) ^ 3 :=
                mul_le_mul (bernoulliKernel_two_abs_le u) hcub (by positivity) (by positivity)
            _ = C * ((u + ‖s‖) ^ 3)⁻¹ := by simp only [C, mul_pow, inv_pow]; ring
      _ = (Real.cos (s.arg / 2))⁻¹ ^ 3 / (24 * ‖s‖ ^ 2) := by
          rw [integral_const_mul, (integrableOn_inv_add_cube_Ioi hr0).2]
          simp only [C]
          ring
  calc ‖-1 / (12 * s ^ 2) +
        2 * ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3‖
      ≤ ‖-1 / (12 * s ^ 2)‖ +
        ‖2 * ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3‖ :=
        norm_add_le _ _
    _ = 1 / (12 * ‖s‖ ^ 2) +
        2 * ‖∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + s) ^ 3‖ := by
        rw [norm_div, norm_neg, norm_one, norm_mul, norm_mul, norm_pow,
          show ‖(12 : ℂ)‖ = 12 by norm_num, show ‖(2 : ℂ)‖ = 2 by norm_num]
    _ ≤ 1 / (12 * ‖s‖ ^ 2) + 2 * ((Real.cos (s.arg / 2))⁻¹ ^ 3 / (24 * ‖s‖ ^ 2)) := by
        linarith
    _ = (1 + (Real.cos (s.arg / 2))⁻¹ ^ 3) / (12 * ‖s‖ ^ 2) := by ring

/-- Compatibility of `stirlingRemainder` with `stirlingRemainderReal` on `(0, ∞)`. -/
theorem stirlingRemainder_ofReal {x : ℝ} (_hx : 0 < x) :
    stirlingRemainder (x : ℂ) = (stirlingRemainderReal x : ℂ) := by
  have hint :
      ∫ u in Set.Ioi (0 : ℝ), ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + (x : ℂ)) ^ 2 =
        ((∫ u in Set.Ioi (0 : ℝ), bernoulliKernel 2 u / (u + x) ^ 2 : ℝ) : ℂ) := by
    have heq : (fun u : ℝ => ((bernoulliKernel 2 u : ℝ) : ℂ) / ((u : ℂ) + (x : ℂ)) ^ 2) =
        fun u : ℝ => ((bernoulliKernel 2 u / (u + x) ^ 2 : ℝ) : ℂ) := by
      ext u
      push_cast
      rfl
    rw [heq, integral_complex_ofReal]
  rw [stirlingRemainder, hint, stirlingRemainderReal]
  push_cast
  rfl

/-- Complex Stirling representation on `Complex.slitPlane`:
`Complex.Gamma s = √(2 * π) * s ^ (s - 1/2) * Complex.exp (-s + stirlingRemainder s)`. -/
theorem complex_gamma_eq_stirling {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    Complex.Gamma s =
      (Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) *
        Complex.exp (-s + stirlingRemainder s) := by
  let L : ℂ → ℂ := Complex.Gamma
  let R : ℂ → ℂ := fun z =>
    (Real.sqrt (2 * Real.pi) : ℂ) * z ^ (z - 1 / 2) * Complex.exp (-z + stirlingRemainder z)
  have hL_diff : DifferentiableOn ℂ L Complex.slitPlane := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z fun m hm => ?_).differentiableWithinAt
    have hnot : (-(m : ℂ)) ∉ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff_not_le_zero]
      push Not
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_zero,
        Complex.real_le_real]
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    exact hnot (hm ▸ hz)
  have hL_an : AnalyticOnNhd ℂ L Complex.slitPlane :=
    hL_diff.analyticOnNhd Complex.isOpen_slitPlane
  have hR_an : AnalyticOnNhd ℂ R Complex.slitPlane := by
    have hcpow : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (z - 1 / 2)) Complex.slitPlane :=
      analyticOnNhd_id.cpow (analyticOnNhd_id.sub analyticOnNhd_const) fun _ hz => hz
    have hexp : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-z + stirlingRemainder z))
        Complex.slitPlane :=
      (analyticOnNhd_id.neg.add analyticOnNhd_stirlingRemainder).cexp
    exact (analyticOnNhd_const.mul hcpow).mul hexp
  have h_pos_real : ∀ {x : ℝ}, 0 < x → L (x : ℂ) = R (x : ℂ) := by
    intro x hx
    have hG := real_gamma_eq_stirling hx
    simp only [L, R, Complex.Gamma_ofReal, stirlingRemainder_ofReal hx]
    have hcp : (x : ℂ) ^ ((x : ℂ) - 1 / 2) = ((x ^ (x - 1 / 2) : ℝ) : ℂ) := by
      rw [show ((x : ℂ) - 1 / 2) = ((x - 1 / 2 : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow hx.le _).symm
    rw [hcp]
    rw [show -(x : ℂ) + (stirlingRemainderReal x : ℂ) = ((-x + stirlingRemainderReal x : ℝ) : ℂ) by
        push_cast; ring,
      ← Complex.ofReal_exp, hG]
    push_cast
    rfl
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), L z = R z := by
    have htend : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
        simpa [Function.comp_def] using Complex.continuous_ofReal.tendsto 1 |>.comp h0
      · filter_upwards with n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        intro heq
        have hre := congrArg Complex.re heq
        simp only [Complex.ofReal_re, Complex.one_re] at hre
        linarith
    refine htend.frequently (Frequently.of_forall fun n => ?_)
    have hx : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    exact h_pos_real hx
  have h1mem : (1 : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr zero_lt_one
  exact hL_an.eqOn_of_preconnected_of_frequently_eq hR_an
    (Complex.starConvex_one_slitPlane.isPathConnected h1mem).isConnected.isPreconnected
    h1mem hfreq hs

/-- Exact norm identity for `Complex.Gamma s` on `Complex.slitPlane`:
`‖Complex.Gamma s‖ = √(2 * π) * exp ((s.re - 1/2) * log ‖s‖ - s.im * s.arg - s.re + (stirlingRemainder s).re)`. -/
theorem norm_complex_gamma_eq_of_mem_slitPlane {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    ‖Complex.Gamma s‖ =
      Real.sqrt (2 * Real.pi) *
        Real.exp ((s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re + (stirlingRemainder s).re) := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  rw [complex_gamma_eq_stirling hs, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.cpow_def_of_ne_zero hs0,
    Complex.norm_exp, Complex.norm_exp]
  have hre1 : (Complex.log s * (s - 1 / 2)).re = (s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  have hre2 : (-s + stirlingRemainder s).re = -s.re + (stirlingRemainder s).re := by simp
  rw [hre1, hre2, mul_assoc, ← Real.exp_add]
  congr 2
  ring

end ComplexRemainder

section VerticalStripStirling

private lemma abs_arctan_sub_self_le (y : ℝ) : |Real.arctan y - y| ≤ |y| ^ 3 := by
  let f : ℝ → ℝ := fun u => Real.arctan u - u
  have hdiff : ∀ u ∈ Metric.closedBall (0 : ℝ) |y|,
      HasDerivWithinAt f ((1 + u ^ 2)⁻¹ - 1) (Metric.closedBall (0 : ℝ) |y|) u := fun u _ =>
    ((Real.hasDerivAt_arctan' u).sub (hasDerivAt_id u)).hasDerivWithinAt
  have hbd : ∀ u ∈ Metric.closedBall (0 : ℝ) |y|, ‖(1 + u ^ 2)⁻¹ - 1‖ ≤ |y| ^ 2 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hu
    have h1 : 1 + u ^ 2 ≠ 0 := by positivity
    have heq : (1 + u ^ 2)⁻¹ - 1 = -(u ^ 2) / (1 + u ^ 2) := by
      field_simp [h1]
      ring
    rw [Real.norm_eq_abs, heq, abs_div, abs_neg, abs_of_nonneg (sq_nonneg u),
      abs_of_pos (by positivity : 0 < 1 + u ^ 2)]
    have hden : 1 ≤ 1 + u ^ 2 := by linarith [sq_nonneg u]
    have husq : u ^ 2 ≤ |y| ^ 2 := by
      rw [← sq_abs u]
      gcongr
    exact (div_le_self (sq_nonneg u) hden).trans husq
  have hmvt := (convex_closedBall (0 : ℝ) |y|).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdiff hbd (Metric.mem_closedBall_self (abs_nonneg y))
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs])
  simpa [f, Real.arctan_zero, sub_zero, dist_zero_right, pow_succ] using hmvt

private lemma abs_exp_sub_one_le_of_abs_le {u B : ℝ} (hu : |u| ≤ B) :
    |Real.exp u - 1| ≤ Real.exp B * |u| := by
  have hB : 0 ≤ B := (abs_nonneg u).trans hu
  have hdiff : ∀ ξ ∈ Metric.closedBall (0 : ℝ) B,
      HasDerivWithinAt Real.exp (Real.exp ξ) (Metric.closedBall (0 : ℝ) B) ξ := fun ξ _ =>
    (Real.hasDerivAt_exp ξ).hasDerivWithinAt
  have hbd : ∀ ξ ∈ Metric.closedBall (0 : ℝ) B, ‖Real.exp ξ‖ ≤ Real.exp B := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hξ
    rw [Real.norm_of_nonneg (Real.exp_pos ξ).le, Real.exp_le_exp]
    exact (le_abs_self ξ).trans hξ
  have hmvt := (convex_closedBall (0 : ℝ) B).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdiff hbd (Metric.mem_closedBall_self hB)
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hu)
  simpa [Real.exp_zero] using hmvt

/-- Every point `σ + t * I` with `t ≠ 0` lies in `Complex.slitPlane`. -/
theorem add_mul_I_mem_slitPlane (σ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (σ : ℂ) + (t : ℂ) * Complex.I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using ht

/-- Argument formula for `σ + t * I` when `t > 0`:
`((σ : ℂ) + (t : ℂ) * I).arg = π / 2 - Real.arctan (σ / t)`. -/
theorem arg_add_mul_I_of_pos {σ t : ℝ} (ht : 0 < t) :
    ((σ : ℂ) + (t : ℂ) * Complex.I).arg = Real.pi / 2 - Real.arctan (σ / t) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have him : 0 < s.im := by simpa [s] using ht
  have hre : s.re = σ := by simp [s]
  have him_eq : s.im = t := by simp [s]
  have hr : ‖s‖ = Real.sqrt (σ ^ 2 + t ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg s), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre,
      him_eq]
    ring_nf
  have hsq_pos : 0 < σ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg σ) (sq_pos_of_ne_zero ht.ne')
  have hrpos : 0 < Real.sqrt (σ ^ 2 + t ^ 2) := Real.sqrt_pos.mpr hsq_pos
  rw [Complex.arg_of_im_pos him, Real.arccos_eq_pi_div_two_sub_arcsin, hre, hr,
    Real.arctan_eq_arcsin]
  congr 2
  have hden : Real.sqrt (1 + (σ / t) ^ 2) = Real.sqrt (σ ^ 2 + t ^ 2) / t := by
    have heq : 1 + (σ / t) ^ 2 = (σ ^ 2 + t ^ 2) / t ^ 2 := by
      field_simp [ht.ne']
      ring
    rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq ht.le]
  rw [hden]
  field_simp [ht.ne', hrpos.ne']

/-- Argument formula for `σ + t * I` when `t < 0`:
`((σ : ℂ) + (t : ℂ) * I).arg = -(π / 2) - Real.arctan (σ / t)`. -/
theorem arg_add_mul_I_of_neg {σ t : ℝ} (ht : t < 0) :
    ((σ : ℂ) + (t : ℂ) * Complex.I).arg = -(Real.pi / 2) - Real.arctan (σ / t) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have him : s.im < 0 := by simpa [s] using ht
  have hre : s.re = σ := by simp [s]
  have him_eq : s.im = t := by simp [s]
  have hr : ‖s‖ = Real.sqrt (σ ^ 2 + t ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg s), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre,
      him_eq]
    ring_nf
  have hneg_t : 0 < -t := neg_pos.mpr ht
  have hsq_pos : 0 < σ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg σ) (sq_pos_of_ne_zero ht.ne)
  have hrpos : 0 < Real.sqrt (σ ^ 2 + t ^ 2) := Real.sqrt_pos.mpr hsq_pos
  rw [Complex.arg_of_im_neg him, Real.arccos_eq_pi_div_two_sub_arcsin, hre, hr]
  have harc : Real.arcsin (σ / Real.sqrt (σ ^ 2 + t ^ 2)) = -Real.arctan (σ / t) := by
    rw [show -Real.arctan (σ / t) = Real.arctan (-(σ / t)) by rw [Real.arctan_neg],
      show -(σ / t) = σ / (-t) by ring, Real.arctan_eq_arcsin]
    congr 1
    have hden : Real.sqrt (1 + (σ / (-t)) ^ 2) = Real.sqrt (σ ^ 2 + t ^ 2) / (-t) := by
      have heq : 1 + (σ / (-t)) ^ 2 = (σ ^ 2 + t ^ 2) / (-t) ^ 2 := by
        field_simp [ht.ne, hneg_t.ne']
        ring
      rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq hneg_t.le]
    rw [hden]
    field_simp [ht.ne, hneg_t.ne', hrpos.ne']
  rw [harc]
  ring

/-- Uniform cosine lower bound on vertical strips: for `σ ∈ [σ₁, σ₂]` and `1 ≤ |t|`,
`(Real.cos (((σ : ℂ) + (t : ℂ) * Complex.I).arg / 2)) ^ 2 ≥ 1 / (4 * (max |σ₁| |σ₂| ^ 2 + 1))`. -/
theorem cos_half_arg_sq_strip_ge {σ₁ σ₂ σ t : ℝ} (hσ : σ ∈ Set.Icc σ₁ σ₂) (ht : 1 ≤ |t|) :
    1 / (4 * ((max |σ₁| |σ₂|) ^ 2 + 1)) ≤
      (Real.cos (((σ : ℂ) + (t : ℂ) * Complex.I).arg / 2)) ^ 2 := by
  let M : ℝ := max |σ₁| |σ₂|
  have hσM : |σ| ≤ M := abs_le.mpr ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hσ.1],
    by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hσ.2]⟩
  have hsqM : σ ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs σ]
    exact sq_le_sq' (by linarith [abs_nonneg σ, hσM]) hσM
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero (add_mul_I_mem_slitPlane σ ht0)
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have hnormSq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    ring
  have hσ_lt : |σ| < ‖s‖ := by
    have : σ ^ 2 < ‖s‖ ^ 2 := by rw [hnormSq]; nlinarith [sq_abs t]
    exact abs_lt.mpr (abs_lt_of_sq_lt_sq' this hnorm_pos.le)
  have hsub_pos : 0 < ‖s‖ - σ := by linarith [le_abs_self σ]
  have hsub_le : ‖s‖ - σ ≤ 2 * ‖s‖ := by linarith [neg_le_abs σ]
  have hprod : (‖s‖ - σ) * (‖s‖ + σ) = t ^ 2 := by linarith [hnormSq]
  have hcos_arg : 1 + Real.cos s.arg = t ^ 2 / (‖s‖ * (‖s‖ - σ)) := by
    have h1 := Complex.norm_mul_cos_arg s
    rw [hre] at h1
    have h2 : 1 + Real.cos s.arg = (‖s‖ + σ) / ‖s‖ := by
      field_simp [hnorm_pos.ne']
      linarith
    rw [h2]
    field_simp [hnorm_pos.ne', hsub_pos.ne']
    linarith [hprod]
  have hhalf : Real.cos (s.arg / 2) ^ 2 = (1 + Real.cos s.arg) / 2 := by
    have := Real.cos_two_mul (s.arg / 2)
    rw [show 2 * (s.arg / 2) = s.arg by ring] at this
    linarith
  have ht2_ge : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hnorm_ub : ‖s‖ ^ 2 ≤ (M ^ 2 + 1) * t ^ 2 := by
    rw [hnormSq]
    nlinarith [sq_nonneg M]
  have ht2pos : 0 < t ^ 2 := by linarith
  calc 1 / (4 * (M ^ 2 + 1))
      = t ^ 2 / (4 * ((M ^ 2 + 1) * t ^ 2)) := by field_simp [ht2pos.ne']
    _ ≤ t ^ 2 / (4 * ‖s‖ ^ 2) := by gcongr
    _ = t ^ 2 / (2 * (‖s‖ * (2 * ‖s‖))) := by ring
    _ ≤ t ^ 2 / (2 * (‖s‖ * (‖s‖ - σ))) := by gcongr
    _ = Real.cos (s.arg / 2) ^ 2 := by
        rw [hhalf, hcos_arg]
        field_simp [hnorm_pos.ne', hsub_pos.ne']

/-- Uniform bound for `stirlingRemainder` on vertical strips `σ ∈ [σ₁, σ₂]`, `1 ≤ |t|`. -/
theorem norm_stirlingRemainder_strip_le {σ₁ σ₂ σ t : ℝ} (hσ : σ ∈ Set.Icc σ₁ σ₂)
    (ht : 1 ≤ |t|) :
    ‖stirlingRemainder ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * (max |σ₁| |σ₂|) ^ 2 + 5) / (12 * |t|) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hs := add_mul_I_mem_slitPlane σ ht0
  have hrem := norm_stirlingRemainder_le hs
  have hcos_sq := cos_half_arg_sq_strip_ge hσ ht
  have hinv_sq : (Real.cos (s.arg / 2))⁻¹ ^ 2 ≤ 4 * ((max |σ₁| |σ₂|) ^ 2 + 1) := by
    rw [inv_pow]
    exact inv_le_of_inv_le₀ (by positivity) (by simpa [one_div] using hcos_sq)
  have hnorm_ge : |t| ≤ ‖s‖ := by
    have him : s.im = t := by simp [s]
    rw [← him]
    exact Complex.abs_im_le_norm s
  calc ‖stirlingRemainder s‖
      ≤ (1 + (Real.cos (s.arg / 2))⁻¹ ^ 2) / (12 * ‖s‖) := hrem
    _ ≤ (1 + 4 * ((max |σ₁| |σ₂|) ^ 2 + 1)) / (12 * |t|) := by
        gcongr
    _ = (4 * (max |σ₁| |σ₂|) ^ 2 + 5) / (12 * |t|) := by ring

/-- Explicit vertical strip constant controlling the `O(|t|⁻¹)` error in the exponent of
Stirling's formula for `Complex.Gamma (σ + t * I)` on `σ ∈ [σ₁, σ₂]`, `1 ≤ |t|`. -/
noncomputable def stirlingStripErrorConst (σ₁ σ₂ : ℝ) : ℝ :=
  let M := max |σ₁| |σ₂|
  (M + 1 / 2) * M ^ 2 / 2 + M ^ 3 + (4 * M ^ 2 + 5) / 12

/-- Nonnegativity of `stirlingStripErrorConst σ₁ σ₂`. -/
theorem stirlingStripErrorConst_nonneg (σ₁ σ₂ : ℝ) : 0 ≤ stirlingStripErrorConst σ₁ σ₂ := by
  dsimp only [stirlingStripErrorConst]
  positivity

/-- Positivity of `stirlingStripErrorConst σ₁ σ₂`. -/
theorem stirlingStripErrorConst_pos (σ₁ σ₂ : ℝ) : 0 < stirlingStripErrorConst σ₁ σ₂ := by
  dsimp only [stirlingStripErrorConst]
  positivity

/-- Exact vertical strip norm representation for `Complex.Gamma (σ + t * I)` (`σ ∈ [σ₁, σ₂]`,
`1 ≤ |t|`) with explicit exponent error bounded by `stirlingStripErrorConst σ₁ σ₂ / |t|`. -/
theorem norm_complex_gamma_strip_log_error_le {σ₁ σ₂ σ t : ℝ} (hσ : σ ∈ Set.Icc σ₁ σ₂)
    (ht : 1 ≤ |t|) :
    ∃ r : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2) *
          Real.exp r ∧
        |r| ≤ stirlingStripErrorConst σ₁ σ₂ / |t| := by
  let M : ℝ := max |σ₁| |σ₂|
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have htpos : 0 < |t| := by linarith
  have hs := add_mul_I_mem_slitPlane σ ht0
  have hσM : |σ| ≤ M := abs_le.mpr ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hσ.1],
    by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hσ.2]⟩
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hnormSq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hs_re, hs_im]
    ring
  have hts_arg : -s.im * s.arg - s.re =
      -(Real.pi / 2) * |t| + (|t| * Real.arctan (σ / |t|) - σ) := by
    rw [hs_im, hs_re]
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · rw [arg_add_mul_I_of_neg hneg]
      have hdiv : σ / |t| = -(σ / t) := by rw [abs_of_neg hneg]; ring
      rw [hdiv, Real.arctan_neg, abs_of_neg hneg]
      ring
    · rw [arg_add_mul_I_of_pos hpos, abs_of_pos hpos]
      ring
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  let r : ℝ := (σ - 1 / 2) * (Real.log ‖s‖ - Real.log (|t|)) +
    (|t| * Real.arctan (σ / |t|) - σ) + (stirlingRemainder s).re
  refine ⟨r, ?_, ?_⟩
  · have hrpow : |t| ^ (σ - 1 / 2) = Real.exp ((σ - 1 / 2) * Real.log (|t|)) := by
      rw [Real.rpow_def_of_pos htpos, mul_comm]
    rw [norm_complex_gamma_eq_of_mem_slitPlane hs, hrpow]
    rw [mul_assoc (Real.sqrt (2 * Real.pi)), ← Real.exp_add,
      mul_assoc (Real.sqrt (2 * Real.pi)), ← Real.exp_add]
    congr 2
    change (s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re + (stirlingRemainder s).re =
      (-(Real.pi / 2) * |t| + (σ - 1 / 2) * Real.log (|t|)) + r
    dsimp only [r]
    have hts := hts_arg
    rw [hs_re] at hts ⊢
    linarith [hts]
  · have hA : |(σ - 1 / 2) * (Real.log ‖s‖ - Real.log (|t|))| ≤
        (M + 1 / 2) * M ^ 2 / 2 / |t| := by
      have hlog_eq : Real.log ‖s‖ - Real.log (|t|) = (1 / 2 : ℝ) * Real.log (1 + (σ / |t|) ^ 2) := by
        have h1 : ‖s‖ ^ 2 = |t| ^ 2 * (1 + (σ / |t|) ^ 2) := by
          rw [hnormSq]
          field_simp [htpos.ne']
          rw [sq_abs]
          ring
        have hpos1 : 0 < 1 + (σ / |t|) ^ 2 := by positivity
        have hlog2 : 2 * (Real.log ‖s‖ - Real.log (|t|)) = Real.log (1 + (σ / |t|) ^ 2) := by
          have hs2 : Real.log (‖s‖ ^ 2) = 2 * Real.log ‖s‖ := by
            rw [Real.log_pow]
            norm_cast
          have ht2 : Real.log (|t| ^ 2) = 2 * Real.log (|t|) := by
            rw [Real.log_pow]
            norm_cast
          rw [mul_sub, ← hs2, ← ht2, h1, Real.log_mul (pow_ne_zero 2 htpos.ne') hpos1.ne']
          ring
        linarith
      have hlog_nn : 0 ≤ Real.log (1 + (σ / |t|) ^ 2) :=
        Real.log_nonneg (by linarith [sq_nonneg (σ / |t|)])
      have hlog_ub : Real.log (1 + (σ / |t|) ^ 2) ≤ (σ / |t|) ^ 2 := by
        have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + (σ / |t|) ^ 2)
        linarith
      have habs_log : |Real.log ‖s‖ - Real.log (|t|)| ≤ (M ^ 2 / 2) / |t| := by
        rw [hlog_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hlog_nn]
        have hsq : (σ / |t|) ^ 2 ≤ M ^ 2 / |t| := by
          rw [div_pow, ← sq_abs σ]
          have h1 : |σ| ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [abs_nonneg σ, hσM]) hσM
          have h2 : |t| ≤ |t| ^ 2 := by nlinarith
          calc |σ| ^ 2 / |t| ^ 2 ≤ M ^ 2 / |t| ^ 2 := by gcongr
            _ ≤ M ^ 2 / |t| := div_le_div_of_nonneg_left (sq_nonneg M) htpos h2
        have hmul : 1 / 2 * (M ^ 2 / |t|) = (M ^ 2 / 2) / |t| := by ring
        linarith
      have hσhalf : |σ - 1 / 2| ≤ M + 1 / 2 :=
        (abs_sub _ _).trans (by linarith [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num])
      rw [abs_mul]
      calc |σ - 1 / 2| * |Real.log ‖s‖ - Real.log (|t|)|
          ≤ (M + 1 / 2) * ((M ^ 2 / 2) / |t|) :=
            mul_le_mul hσhalf habs_log (abs_nonneg _) (by positivity)
        _ = (M + 1 / 2) * M ^ 2 / 2 / |t| := by ring
    have hB : |(|t|) * Real.arctan (σ / |t|) - σ| ≤ M ^ 3 / |t| := by
      have heq : |t| * Real.arctan (σ / |t|) - σ = |t| * (Real.arctan (σ / |t|) - σ / |t|) := by
        field_simp [htpos.ne']
      rw [heq, abs_mul, abs_of_pos htpos]
      have h1 := (abs_arctan_sub_self_le (σ / |t|)).trans_eq (by
        rw [abs_div, abs_of_pos htpos, div_pow])
      calc |t| * |Real.arctan (σ / |t|) - σ / (|t|)|
          ≤ |t| * (|σ| ^ 3 / |t| ^ 3) := mul_le_mul_of_nonneg_left h1 htpos.le
        _ = |σ| ^ 3 / |t| ^ 2 := by field_simp [htpos.ne']
        _ ≤ M ^ 3 / |t| ^ 2 := by gcongr
        _ ≤ M ^ 3 / |t| := div_le_div_of_nonneg_left (pow_nonneg (by positivity) 3) htpos (by nlinarith)
    have hC : |(stirlingRemainder s).re| ≤ (4 * M ^ 2 + 5) / 12 / |t| := by
      calc |(stirlingRemainder s).re| ≤ ‖stirlingRemainder s‖ := Complex.abs_re_le_norm _
        _ ≤ (4 * M ^ 2 + 5) / (12 * |t|) := norm_stirlingRemainder_strip_le hσ ht
        _ = (4 * M ^ 2 + 5) / 12 / |t| := by ring
    calc |r|
        ≤ |(σ - 1 / 2) * (Real.log ‖s‖ - Real.log (|t|))| +
            |(|t|) * Real.arctan (σ / |t|) - σ| + |(stirlingRemainder s).re| := by
          exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ (M + 1 / 2) * M ^ 2 / 2 / |t| + M ^ 3 / |t| + (4 * M ^ 2 + 5) / 12 / |t| := by
          linarith
      _ = stirlingStripErrorConst σ₁ σ₂ / |t| := by
          simp only [stirlingStripErrorConst, M]
          ring

/-- Uniform explicit multiplicative error bound for `‖Complex.Gamma (σ + t * I)‖` on any
vertical strip `σ ∈ [σ₁, σ₂]`, `1 ≤ |t|`. -/
theorem norm_complex_gamma_strip_asymptotic_explicit {σ₁ σ₂ σ t : ℝ} (hσ : σ ∈ Set.Icc σ₁ σ₂)
    (ht : 1 ≤ |t|) :
    |‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ -
        Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)| ≤
      (Real.exp (stirlingStripErrorConst σ₁ σ₂) * stirlingStripErrorConst σ₁ σ₂ / |t|) *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) := by
  obtain ⟨r, hnorm, hr⟩ := norm_complex_gamma_strip_log_error_le hσ ht
  let main : ℝ := Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)
  have htpos : 0 < |t| := by linarith
  have hmain_pos : 0 < main := by positivity
  have hr_B : |r| ≤ stirlingStripErrorConst σ₁ σ₂ := by
    calc |r| ≤ stirlingStripErrorConst σ₁ σ₂ / |t| := hr
      _ ≤ stirlingStripErrorConst σ₁ σ₂ :=
        div_le_self (stirlingStripErrorConst_nonneg σ₁ σ₂) ht
  have hexp_diff : |Real.exp r - 1| ≤
      Real.exp (stirlingStripErrorConst σ₁ σ₂) * (stirlingStripErrorConst σ₁ σ₂ / |t|) := by
    calc |Real.exp r - 1| ≤ Real.exp (stirlingStripErrorConst σ₁ σ₂) * |r| :=
          abs_exp_sub_one_le_of_abs_le hr_B
      _ ≤ Real.exp (stirlingStripErrorConst σ₁ σ₂) * (stirlingStripErrorConst σ₁ σ₂ / |t|) := by
          gcongr
  rw [hnorm, show main * Real.exp r - main = main * (Real.exp r - 1) by ring, abs_mul,
    abs_of_pos hmain_pos]
  calc main * |Real.exp r - 1|
      ≤ main * (Real.exp (stirlingStripErrorConst σ₁ σ₂) * (stirlingStripErrorConst σ₁ σ₂ / |t|)) :=
        mul_le_mul_of_nonneg_left hexp_diff hmain_pos.le
    _ = (Real.exp (stirlingStripErrorConst σ₁ σ₂) * stirlingStripErrorConst σ₁ σ₂ / |t|) * main := by
        ring

/-- Uniform upper and lower vertical strip bounds for `‖Complex.Gamma (σ + t * I)‖` on
`σ ∈ [σ₁, σ₂]`, `1 ≤ |t|`: there exist `0 < c ≤ C` depending only on `σ₁, σ₂` such that
`c * exp (-π/2 * |t|) * |t| ^ (σ - 1/2) ≤ ‖Complex.Gamma (σ + t * I)‖ ≤ C * exp (-π/2 * |t|) * |t| ^ (σ - 1/2)`. -/
theorem norm_complex_gamma_strip_bounds (σ₁ σ₂ : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ ⦃σ t : ℝ⦄, σ ∈ Set.Icc σ₁ σ₂ → 1 ≤ |t| →
        c * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2) ≤
          ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
          ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2) := by
  let B := stirlingStripErrorConst σ₁ σ₂
  let c := Real.sqrt (2 * Real.pi) * Real.exp (-B)
  let C := Real.sqrt (2 * Real.pi) * Real.exp B
  have hc_pos : 0 < c := by positivity
  have hB : 0 ≤ B := stirlingStripErrorConst_nonneg σ₁ σ₂
  have hcC : c ≤ C := by
    dsimp only [c, C]
    gcongr
    linarith
  refine ⟨c, C, hc_pos, hcC, fun σ t hσ ht => ?_⟩
  obtain ⟨r, hnorm, hr⟩ := norm_complex_gamma_strip_log_error_le hσ ht
  have hrB : |r| ≤ B := hr.trans (div_le_self hB ht)
  rw [abs_le] at hrB
  have hexp_l : Real.exp (-B) ≤ Real.exp r := Real.exp_le_exp.mpr hrB.1
  have hexp_u : Real.exp r ≤ Real.exp B := Real.exp_le_exp.mpr hrB.2
  have hmain : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2) := by
    have : 0 ≤ |t| := abs_nonneg t
    positivity
  rw [hnorm]
  constructor
  · calc c * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)
        = (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) * Real.exp (-B) := by
          dsimp only [c]; ring
      _ ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) * Real.exp r := by
          gcongr
  · calc (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) * Real.exp r
        ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) * Real.exp B := by
          gcongr
      _ = C * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2) := by
          dsimp only [C]; ring

/-- Uniform ratio convergence `‖Complex.Gamma (σ + t * I)‖ / (√(2π) exp (-π/2 * |t|) |t| ^ (σ - 1/2)) → 1`
as `|t| → ∞`, uniformly for `σ ∈ [σ₁, σ₂]`. -/
theorem norm_complex_gamma_strip_tendsto_one (σ₁ σ₂ : ℝ) :
    ∀ ε > 0, ∃ T : ℝ, 1 ≤ T ∧
      ∀ ⦃σ t : ℝ⦄, σ ∈ Set.Icc σ₁ σ₂ → T ≤ |t| →
        |‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ /
            (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) - 1| < ε := by
  intro ε hε
  let K := Real.exp (stirlingStripErrorConst σ₁ σ₂) * stirlingStripErrorConst σ₁ σ₂
  have hK : 0 < K := by positivity [stirlingStripErrorConst_pos σ₁ σ₂]
  refine ⟨max 1 (K / ε + 1), le_max_left _ _, fun σ t hσ ht => ?_⟩
  have ht1 : 1 ≤ |t| := (le_max_left _ _).trans ht
  have htK : K / ε < |t| := by linarith [le_max_right 1 (K / ε + 1)]
  have hmain_pos :
      0 < Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2) := by
    have : 0 < |t| := by linarith
    positivity
  have hasymp := norm_complex_gamma_strip_asymptotic_explicit hσ ht1
  have hdiv :
      |‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ /
          (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) - 1| ≤
        K / |t| := by
    rw [show ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ /
          (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) - 1 =
        (‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ -
          Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) /
          (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |t|) * |t| ^ (σ - 1 / 2)) by
      field_simp [hmain_pos.ne']]
    rw [abs_div, abs_of_pos hmain_pos]
    exact (div_le_iff₀ hmain_pos).mpr hasymp
  have hKeps : K / |t| < ε := (div_lt_iff₀ (by linarith)).mpr (by
    calc K = ε * (K / ε) := by field_simp [hε.ne']
      _ < ε * |t| := mul_lt_mul_of_pos_left htK hε)
  exact hdiv.trans_lt hKeps

/-- Big-O growth bound for `Complex.Gamma (σ + t * I)` along a vertical line `Re s = σ` as
`t → +∞`. -/
theorem norm_complex_gamma_vertical_isBigO (σ : ℝ) :
    (fun t : ℝ => ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi / 2) * t) * t ^ (σ - 1 / 2)) := by
  obtain ⟨_, C, _, _, hbd⟩ := norm_complex_gamma_strip_bounds σ σ
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hst := (hbd (Set.left_mem_Icc.mpr le_rfl) (by rwa [abs_of_nonneg (zero_le_one.trans ht)])).2
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  rw [abs_of_nonneg ht0] at hst
  rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by positivity)]
  exact hst.trans_eq (mul_assoc _ _ _)

/-- Asymptotic equivalence `‖Complex.Gamma (σ + t * I)‖ ~ √(2π) exp (-π/2 * t) t ^ (σ - 1/2)`
along a vertical line `Re s = σ` as `t → +∞`. -/
theorem norm_complex_gamma_vertical_isEquivalent (σ : ℝ) :
    (fun t : ℝ => ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ~[atTop]
      fun t : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * t) * t ^ (σ - 1 / 2) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT1, hT⟩ := norm_complex_gamma_strip_tendsto_one σ σ ε hε
    refine ⟨T, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := by linarith
    have htT : T ≤ |t| := by rwa [abs_of_nonneg ht0]
    have h := hT (Set.left_mem_Icc.mpr le_rfl) htT
    rw [abs_of_nonneg ht0] at h
    simpa [Real.dist_eq] using h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    positivity

/-- Stirling representation of the digamma function `digamma s = deriv Gamma s / Gamma s` on
`Complex.slitPlane`:
`digamma s = Complex.log s - 1 / (2 * s) + deriv stirlingRemainder s`. -/
theorem digamma_eq_stirling {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    digamma s = Complex.log s - 1 / (2 * s) + deriv stirlingRemainder s := by
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hs
  have hG_ne : Complex.Gamma s ≠ 0 := by
    refine gamma_ne_zero fun m hm => ?_
    have hnot : (-(m : ℂ)) ∉ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff_not_le_zero]
      push Not
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_zero,
        Complex.real_le_real]
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    exact hnot (hm ▸ hs)
  have hev : Complex.Gamma =ᶠ[𝓝 s] fun z : ℂ =>
      (Real.sqrt (2 * Real.pi) : ℂ) * z ^ (z - 1 / 2) *
        Complex.exp (-z + stirlingRemainder z) := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hs] with z hz
    exact complex_gamma_eq_stirling hz
  have hlog : HasDerivAt Complex.log s⁻¹ s := Complex.hasDerivAt_log hs
  have hcpow_ev : (fun z : ℂ => z ^ (z - 1 / 2)) =ᶠ[𝓝 s]
      fun z : ℂ => Complex.exp ((z - 1 / 2) * Complex.log z) := by
    filter_upwards [isOpen_ne.mem_nhds hs0] with z hz
    rw [Complex.cpow_def_of_ne_zero hz, mul_comm]
  have hexp1 : HasDerivAt (fun z : ℂ => z ^ (z - 1 / 2))
      (Complex.exp ((s - 1 / 2) * Complex.log s) * (Complex.log s + (s - 1 / 2) * s⁻¹)) s := by
    have hinner : HasDerivAt (fun z : ℂ => (z - 1 / 2) * Complex.log z)
        (1 * Complex.log s + (s - 1 / 2) * s⁻¹) s :=
      ((hasDerivAt_id' s).sub_const _).mul hlog
    have hcexp := (hinner.cexp).congr_of_eventuallyEq hcpow_ev
    convert hcexp using 1
    ring
  have hexp2 : HasDerivAt (fun z : ℂ => Complex.exp (-z + stirlingRemainder z))
      (Complex.exp (-s + stirlingRemainder s) * (-1 + deriv stirlingRemainder s)) s := by
    have hst := (hasDerivAt_stirlingRemainder hs).deriv
    have hder : HasDerivAt stirlingRemainder (deriv stirlingRemainder s) s :=
      hst ▸ hasDerivAt_stirlingRemainder hs
    exact ((hasDerivAt_id' s).neg.add hder).cexp
  have hprod := (hexp1.const_mul (Real.sqrt (2 * Real.pi) : ℂ)).fun_mul hexp2
  have hG_deriv : HasDerivAt Complex.Gamma
      ((Real.sqrt (2 * Real.pi) : ℂ) *
        (Complex.exp ((s - 1 / 2) * Complex.log s) * (Complex.log s + (s - 1 / 2) * s⁻¹)) *
        Complex.exp (-s + stirlingRemainder s) +
        (Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) *
        (Complex.exp (-s + stirlingRemainder s) * (-1 + deriv stirlingRemainder s))) s :=
    hprod.congr_of_eventuallyEq hev
  rw [digamma, hG_deriv.deriv]
  have hG_eq := complex_gamma_eq_stirling hs
  have hs_cpow : s ^ (s - 1 / 2) = Complex.exp ((s - 1 / 2) * Complex.log s) := by
    rw [Complex.cpow_def_of_ne_zero hs0, mul_comm]
  rw [← hs_cpow]
  conv_lhs => rhs; rw [hG_eq]
  have hexp_ne : Complex.exp (-s + stirlingRemainder s) ≠ 0 := Complex.exp_ne_zero _
  have hc_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcp_ne : s ^ (s - 1 / 2) ≠ 0 := by
    rw [hs_cpow]
    exact Complex.exp_ne_zero _
  field_simp [hs0, hexp_ne, hc_ne, hcp_ne]
  ring

/-- Uniform error bound for `digamma (σ + t * I) - Complex.log (σ + t * I)` on vertical strips
`σ ∈ [σ₁, σ₂]`, `1 ≤ |t|`. -/
theorem norm_digamma_sub_log_strip_le {σ₁ σ₂ σ t : ℝ} (hσ : σ ∈ Set.Icc σ₁ σ₂) (ht : 1 ≤ |t|) :
    ‖digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (1 / 2 + (1 + 8 * ((max |σ₁| |σ₂|) ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12) / |t| := by
  let M := max |σ₁| |σ₂|
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hs := add_mul_I_mem_slitPlane σ ht0
  have hcos_sq := cos_half_arg_sq_strip_ge hσ ht
  have hcos_pos : 0 < Real.cos (s.arg / 2) := cos_half_arg_pos_of_mem_slitPlane hs
  have hinv_le : (Real.cos (s.arg / 2))⁻¹ ≤ 2 * Real.sqrt (M ^ 2 + 1) := by
    have hsq : (Real.cos (s.arg / 2))⁻¹ ^ 2 ≤ (2 * Real.sqrt (M ^ 2 + 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), inv_pow]
      have : (Real.cos (s.arg / 2) ^ 2)⁻¹ ≤ (1 / (4 * (M ^ 2 + 1)))⁻¹ :=
        inv_anti₀ (by positivity) hcos_sq
      simpa [one_div, inv_inv, show (4 : ℝ) = 2 ^ 2 by norm_num] using this
    exact le_of_sq_le_sq hsq (by positivity)
  have hcub_le : (Real.cos (s.arg / 2))⁻¹ ^ 3 ≤ 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ) := by
    have h3 : (2 * Real.sqrt (M ^ 2 + 1)) ^ 3 = 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ) := by
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((M ^ 2 + 1) ^ (1 / 2 : ℝ)) 3,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [← h3]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hcos_pos.le) hinv_le 3
  have hnorm_ge : |t| ≤ ‖s‖ := by
    have him : s.im = t := by simp [s]
    rw [← him]
    exact Complex.abs_im_le_norm s
  have hnorm_sq_ge : |t| ≤ ‖s‖ ^ 2 := by
    have : |t| ≤ |t| ^ 2 := by nlinarith
    exact this.trans (pow_le_pow_left₀ (by linarith) hnorm_ge 2)
  rw [digamma_eq_stirling hs, show Complex.log s - 1 / (2 * s) + deriv stirlingRemainder s -
      Complex.log s = -1 / (2 * s) + deriv stirlingRemainder s by ring]
  have h1 : ‖-1 / (2 * s)‖ ≤ (1 / 2 : ℝ) / |t| := by
    rw [norm_div, norm_neg, norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc 1 / (2 * ‖s‖) ≤ 1 / (2 * |t|) := by gcongr
      _ = (1 / 2 : ℝ) / |t| := by ring
  have h2 : ‖deriv stirlingRemainder s‖ ≤ (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12 / |t| := by
    calc ‖deriv stirlingRemainder s‖
        ≤ (1 + (Real.cos (s.arg / 2))⁻¹ ^ 3) / (12 * ‖s‖ ^ 2) :=
          norm_deriv_stirlingRemainder_le hs
      _ ≤ (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / (12 * |t|) := by
          gcongr
      _ = (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12 / |t| := by ring
  have hsplit : (1 / 2 + (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12) / |t| =
      (1 / 2 : ℝ) / |t| + (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12 / |t| := by ring
  exact (norm_add_le _ _).trans (by linarith)

/-- Logarithmic upper bound for `‖digamma (σ + t * I)‖` on vertical strips `σ ∈ [σ₁, σ₂]`,
`2 ≤ |t|`. -/
theorem norm_digamma_strip_le {σ₁ σ₂ σ t : ℝ} (hσ : σ ∈ Set.Icc σ₁ σ₂) (ht : 2 ≤ |t|) :
    ‖digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log |t| + Real.log (1 + (max |σ₁| |σ₂|) ^ 2) / 2 + Real.pi +
        (1 / 2 + (1 + 8 * ((max |σ₁| |σ₂|) ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12) := by
  let M := max |σ₁| |σ₂|
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have ht1 : 1 ≤ |t| := by linarith
  have htpos : 0 < |t| := by linarith
  have hσM : |σ| ≤ M := abs_le.mpr ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hσ.1],
    by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hσ.2]⟩
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have hnormSq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    ring
  have hnorm_pos : 0 < ‖s‖ := by
    have : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
    linarith
  have hlog_re : |Real.log ‖s‖| ≤ Real.log |t| + Real.log (1 + M ^ 2) / 2 := by
    have hnorm_ge : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
    have hlog_nn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (ht1.trans hnorm_ge)
    rw [abs_of_nonneg hlog_nn]
    have hle : σ ^ 2 + t ^ 2 ≤ t ^ 2 * (1 + M ^ 2) := by
      have : σ ^ 2 ≤ M ^ 2 * t ^ 2 := by
        rw [← sq_abs σ, ← sq_abs t]
        have h1 : |σ| ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [abs_nonneg σ, hσM]) hσM
        have h2 : 1 ≤ |t| ^ 2 := by nlinarith
        nlinarith [sq_nonneg M]
      linarith
    have hsum_pos : 0 < σ ^ 2 + t ^ 2 := by
      have : 0 < |t| ^ 2 := sq_pos_of_pos htpos
      rw [sq_abs] at this
      linarith [sq_nonneg σ]
    have htsq_pos : 0 < t ^ 2 := by
      rw [← sq_abs t]
      exact sq_pos_of_pos htpos
    have hlog_le : Real.log (σ ^ 2 + t ^ 2) ≤ Real.log (t ^ 2 * (1 + M ^ 2)) :=
      Real.log_le_log hsum_pos hle
    have h2s : Real.log (σ ^ 2 + t ^ 2) = 2 * Real.log ‖s‖ := by
      rw [← hnormSq, Real.log_pow]
      norm_cast
    rw [h2s, Real.log_mul htsq_pos.ne' (by positivity), ← sq_abs t, Real.log_pow] at hlog_le
    push_cast at hlog_le
    linarith
  have hlog_s : ‖Complex.log s‖ ≤ Real.log |t| + Real.log (1 + M ^ 2) / 2 + Real.pi := by
    have hdec : Complex.log s = (Real.log ‖s‖ : ℂ) + (s.arg : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
    rw [hdec]
    calc ‖(Real.log ‖s‖ : ℂ) + (s.arg : ℂ) * Complex.I‖
        ≤ ‖(Real.log ‖s‖ : ℂ)‖ + ‖(s.arg : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |Real.log ‖s‖| + |s.arg| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ Real.log |t| + Real.log (1 + M ^ 2) / 2 + Real.pi := by
          linarith [Complex.abs_arg_le_pi s]
  have hdiff := norm_digamma_sub_log_strip_le hσ ht1
  have hdiff1 : ‖digamma s - Complex.log s‖ ≤
      1 / 2 + (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12 :=
    hdiff.trans (div_le_self (by positivity) ht1)
  calc ‖digamma s‖ = ‖Complex.log s + (digamma s - Complex.log s)‖ := by ring_nf
    _ ≤ ‖Complex.log s‖ + ‖digamma s - Complex.log s‖ := norm_add_le _ _
    _ ≤ Real.log |t| + Real.log (1 + M ^ 2) / 2 + Real.pi +
        (1 / 2 + (1 + 8 * (M ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12) := by linarith

end VerticalStripStirling

end AnalyticNumberTheory.AnalyticTools.Gamma
