import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.LSeries.Nonvanishing
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.RiemannZeta.HadamardProduct

/-!
# Zero Counting, Stirling Argument Asymptotic, and Riemann–von Mangoldt Formula

This file develops the vertical distribution and counting theory of the non-trivial zeros of
`riemannZeta`:

- The zero-counting function `zeroCountUpTo T` (`N(T)`, counting zeros in `0 < Im ρ ≤ T` and
  `0 < Re ρ < 1` with multiplicity), monotonicity, and local unit-interval bounds from
  `HadamardProduct.unitIntervalZeroCount_le_log`.
- Stirling's imaginary-part asymptotic for the gamma factor:
  `(1 / π) * Im log Γ(1/4 + iT/2) - (T / (2π)) * log π = (T / (2π)) * log (T / (2πe)) - 1/8 + O(1/T)`
  and the shifted `5/4 + iT/2` plus `arg (-1/2 + iT)` version yielding `+ 7/8`.
- Unconditional rectangular Argument Principle for entire functions, the definition of `argumentS T`
  (`S(T)`), Backlund/Jensen's bound `|argumentS T| ≤ C * Real.log T`, and the explicit and
  asymptotic Riemann–von Mangoldt formulas `N(T) = (T / (2π)) * log (T / (2πe)) + 7/8 + O(log T)`.
-/

open Complex Filter Topology Metric Set Real MeasureTheory
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.RiemannZeta

/-! ### Zero-Counting Function `zeroCountUpTo` and Local Unit-Interval Bounds -/

/-- Number of non-trivial zeros of `riemannZeta` in the critical strip `0 < Re ρ < 1` with
imaginary part `0 < Im ρ ≤ T`, counted with analytic multiplicity. -/
noncomputable def zeroCountUpTo (T : ℝ) : ℕ := by
  classical
  exact ∑ᶠ ρ : ℂ, if ρ ∈ CriticalStripZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T then
    analyticOrderNatAt riemannZeta ρ else 0

/-- For `T ≤ 0`, `zeroCountUpTo T = 0`. -/
theorem zeroCountUpTo_nonpos {T : ℝ} (hT : T ≤ 0) : zeroCountUpTo T = 0 := by
  classical
  unfold zeroCountUpTo
  have h0 : ∀ ρ : ℂ, (if ρ ∈ CriticalStripZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T then
      analyticOrderNatAt riemannZeta ρ else 0) = 0 := fun ρ ↦ by
    split_ifs with h
    · exfalso; linarith [h.2.1, h.2.2]
    · rfl
  simp_rw [h0]
  exact finsum_zero

open Classical in
private lemma zeroCountUpTo_support_subset (T : ℝ) :
    (fun ρ : ℂ ↦ if ρ ∈ CriticalStripZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T then
        analyticOrderNatAt riemannZeta ρ else 0).support ⊆
      ((criticalStripZeros_strip_finite 0 T).toFinset : Set ℂ) := by
  intro ρ hρ
  simp only [Function.mem_support, ne_eq] at hρ
  split_ifs at hρ with h
  · exact (criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr ⟨h.1, ⟨h.2.1.le, h.2.2⟩⟩
  · exact absurd rfl hρ

/-- Finite-sum representation of `zeroCountUpTo T`. -/
theorem zeroCountUpTo_eq_sum (T : ℝ) :
    zeroCountUpTo T =
      ∑ ρ ∈ (criticalStripZeros_strip_finite 0 T).toFinset.filter (fun ρ : ℂ ↦ 0 < ρ.im),
        analyticOrderNatAt riemannZeta ρ := by
  classical
  let S : Finset ℂ :=
    (criticalStripZeros_strip_finite 0 T).toFinset.filter (fun ρ : ℂ ↦ 0 < ρ.im)
  have hsupp : (fun ρ : ℂ ↦ if ρ ∈ CriticalStripZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T then
      analyticOrderNatAt riemannZeta ρ else 0).support ⊆ (S : Set ℂ) := by
    intro ρ hρ
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hρ
    rcases hρ with ⟨⟨hcrit, h1, h2⟩, _⟩
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr ⟨hcrit, ⟨h1.le, h2⟩⟩, h1⟩)
  unfold zeroCountUpTo
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  have hmem := Finset.mem_filter.mp hρ
  have hstrip := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp hmem.1
  simp [hstrip.1, hmem.2, hstrip.2.2]

/-- Monotonicity of `zeroCountUpTo`: if `T₁ ≤ T₂`, then `zeroCountUpTo T₁ ≤ zeroCountUpTo T₂`. -/
theorem zeroCountUpTo_mono {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    zeroCountUpTo T₁ ≤ zeroCountUpTo T₂ := by
  classical
  rw [zeroCountUpTo_eq_sum T₁, zeroCountUpTo_eq_sum T₂]
  refine Finset.sum_le_sum_of_subset fun ρ hρ ↦ ?_
  have hmem := Finset.mem_filter.mp hρ
  have hstrip := (criticalStripZeros_strip_finite 0 T₁).mem_toFinset.mp hmem.1
  exact Finset.mem_filter.mpr
    ⟨(criticalStripZeros_strip_finite 0 T₂).mem_toFinset.mpr
      ⟨hstrip.1, ⟨hstrip.2.1, hstrip.2.2.trans hT⟩⟩, hmem.2⟩

/-- Equivalence with the closed strip `0 ≤ Re ρ ≤ 1`: `zeroCountUpTo T` also counts all zeros
of `riemannZeta` in `0 ≤ Re ρ ≤ 1` with `0 < Im ρ ≤ T`. -/
theorem zeroCountUpTo_eq_Icc_zero_one (T : ℝ) :
    zeroCountUpTo T =
      by
        classical
        exact ∑ᶠ ρ : ℂ, if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T then
          analyticOrderNatAt riemannZeta ρ else 0 := by
  classical
  unfold zeroCountUpTo
  refine finsum_congr fun ρ ↦ ?_
  have hiff : (ρ ∈ CriticalStripZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T) ↔
      (riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T) := by
    constructor
    · rintro ⟨⟨hz, h0, h1⟩, him0, himT⟩
      exact ⟨hz, h0.le, h1.le, him0, himT⟩
    · rintro ⟨hz, h0, h1, him0, himT⟩
      have hne1 : ρ ≠ 1 := fun h ↦ by simp [h] at him0
      have hm : ∀ m : ℕ, ρ ≠ -2 * (m : ℂ) := fun m h ↦ by
        have him := congrArg Complex.im h
        simp only [Complex.neg_im, Complex.mul_im, Complex.im_ofNat,
          Complex.natCast_im, mul_zero, zero_mul, add_zero, neg_zero] at him
        linarith
      have hxi0 : xi ρ = 0 := by
        rw [xi_eq_formula hm hne1, hz, mul_zero]
      have hcrit := (xi_eq_zero_iff).mp hxi0
      exact ⟨⟨hcrit.1, hcrit.2.1, hcrit.2.2⟩, him0, himT⟩
  simp [hiff]

private lemma unitIntervalZeroCount_eq_sum_strip (T : ℝ) :
    unitIntervalZeroCount T =
      ∑ ρ ∈ (criticalStripZeros_strip_finite T (T + 1)).toFinset,
        analyticOrderNatAt riemannZeta ρ := by
  classical
  let S : Finset ℂ := (criticalStripZeros_strip_finite T (T + 1)).toFinset
  unfold unitIntervalZeroCount
  have hsupp : (fun ρ : ℂ ↦
      if ρ ∈ CriticalStripZeros ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1 then
        analyticOrderNatAt riemannZeta ρ else 0).support ⊆ (S : Set ℂ) := by
    intro ρ hρ
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hρ
    rcases hρ with ⟨⟨hcrit, h1, h2⟩, _⟩
    exact (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mpr ⟨hcrit, ⟨h1, h2⟩⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  have hmem := (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp hρ
  simp [hmem.1, hmem.2.1, hmem.2.2]

/-- Local zero-count difference bound: for `T ≤ T' ≤ T + 1`, the number of non-trivial zeros
with imaginary part in `(T, T']` is at most `unitIntervalZeroCount T`. -/
theorem zeroCountUpTo_sub_le_unitIntervalZeroCount {T T' : ℝ} (h1 : T ≤ T') (h2 : T' ≤ T + 1) :
    zeroCountUpTo T' - zeroCountUpTo T ≤ unitIntervalZeroCount T := by
  classical
  rw [zeroCountUpTo_eq_sum T, zeroCountUpTo_eq_sum T', unitIntervalZeroCount_eq_sum_strip T]
  let S1 := (criticalStripZeros_strip_finite 0 T).toFinset.filter (fun ρ : ℂ ↦ 0 < ρ.im)
  let S2 := (criticalStripZeros_strip_finite 0 T').toFinset.filter (fun ρ : ℂ ↦ 0 < ρ.im)
  let U := (criticalStripZeros_strip_finite T (T + 1)).toFinset
  have hS12 : S1 ⊆ S2 := by
    intro ρ hρ
    have hm := Finset.mem_filter.mp hρ
    have hs := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp hm.1
    exact Finset.mem_filter.mpr
      ⟨(criticalStripZeros_strip_finite 0 T').mem_toFinset.mpr
        ⟨hs.1, ⟨hs.2.1, hs.2.2.trans h1⟩⟩, hm.2⟩
  have hdiff_sub : S2 \ S1 ⊆ U := by
    intro ρ hρ
    rw [Finset.mem_sdiff] at hρ
    have hm2 := Finset.mem_filter.mp hρ.1
    have hs2 := (criticalStripZeros_strip_finite 0 T').mem_toFinset.mp hm2.1
    have hgtT : T < ρ.im := by
      by_contra! hle
      apply hρ.2
      exact Finset.mem_filter.mpr
        ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr ⟨hs2.1, ⟨hs2.2.1, hle⟩⟩, hm2.2⟩
    exact (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mpr
      ⟨hs2.1, ⟨hgtT.le, hs2.2.2.trans h2⟩⟩
  have hsplit : ∑ ρ ∈ S2, analyticOrderNatAt riemannZeta ρ =
      ∑ ρ ∈ S1, analyticOrderNatAt riemannZeta ρ +
        ∑ ρ ∈ S2 \ S1, analyticOrderNatAt riemannZeta ρ := by
    rw [← Finset.sum_sdiff hS12, add_comm]
  rw [hsplit, Nat.add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset hdiff_sub

/-- **Local unit-interval zero-count bound**:
`zeroCountUpTo (T + 1) - zeroCountUpTo T ≤ C * Real.log (|T| + 2)`. -/
theorem zeroCountUpTo_sub_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
      ((zeroCountUpTo (T + 1) - zeroCountUpTo T : ℕ) : ℝ) ≤ C * Real.log (|T| + 2) := by
  obtain ⟨C, hC_pos, hC_bd⟩ := unitIntervalZeroCount_le_log
  refine ⟨C, hC_pos, fun T ↦ ?_⟩
  have hnat : zeroCountUpTo (T + 1) - zeroCountUpTo T ≤ unitIntervalZeroCount T :=
    zeroCountUpTo_sub_le_unitIntervalZeroCount (by linarith) le_rfl
  have hle : ((zeroCountUpTo (T + 1) - zeroCountUpTo T : ℕ) : ℝ) ≤ (unitIntervalZeroCount T : ℝ) := by
    exact_mod_cast hnat
  exact hle.trans (hC_bd T)

/-- Coarse global upper bound `zeroCountUpTo T ≤ C * T * Real.log T` for `T ≥ 2`. -/
theorem zeroCountUpTo_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zeroCountUpTo T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨C₁, hC₁_pos, hC₁_bd⟩ := zeroCountUpTo_sub_le_log
  let C : ℝ := 6 * C₁
  refine ⟨C, by positivity, fun T hT ↦ ?_⟩
  let N : ℕ := Nat.ceil T
  have hN_ge2 : 2 ≤ N := by
    exact_mod_cast (hT.trans (Nat.le_ceil T) : (2 : ℝ) ≤ N)
  have hN_le_twoT : (N : ℝ) ≤ 2 * T := by
    have hlt : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hnat_bound : ∀ k : ℕ, (zeroCountUpTo (k : ℝ) : ℝ) ≤ (k : ℝ) * C₁ * Real.log ((k : ℝ) + 2) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      rw [zeroCountUpTo_nonpos le_rfl]
      simp
    | succ k ih =>
      have hk1 : (zeroCountUpTo (k : ℝ) : ℝ) ≤ (zeroCountUpTo ((k : ℝ) + 1) : ℝ) := by
        exact_mod_cast zeroCountUpTo_mono (by linarith : (k : ℝ) ≤ k + 1)
      have hdiff_nat : zeroCountUpTo ((k : ℝ) + 1) =
          zeroCountUpTo (k : ℝ) + (zeroCountUpTo ((k : ℝ) + 1) - zeroCountUpTo (k : ℝ)) := by
        have hle : zeroCountUpTo (k : ℝ) ≤ zeroCountUpTo ((k : ℝ) + 1) :=
          zeroCountUpTo_mono (by linarith)
        omega
      have hsub := hC₁_bd (k : ℝ)
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)] at hsub
      have hlog_mono : Real.log ((k : ℝ) + 2) ≤ Real.log ((k + 1 : ℕ) + 2) := by
        refine Real.log_le_log (by positivity) ?_
        push_cast; linarith
      have hadd_eq : ((zeroCountUpTo ((k + 1 : ℕ) : ℝ) : ℕ) : ℝ) =
          (zeroCountUpTo (k : ℝ) : ℝ) + ((zeroCountUpTo ((k : ℝ) + 1) - zeroCountUpTo (k : ℝ) : ℕ) : ℝ) := by
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        conv_lhs => rw [hdiff_nat]
        rw [Nat.cast_add]
      rw [hadd_eq]
      have ih' : (zeroCountUpTo (k : ℝ) : ℝ) ≤ (k : ℝ) * C₁ * Real.log ((k + 1 : ℕ) + 2) :=
        ih.trans (mul_le_mul_of_nonneg_left hlog_mono (by positivity))
      have hsub' : ((zeroCountUpTo ((k : ℝ) + 1) - zeroCountUpTo (k : ℝ) : ℕ) : ℝ) ≤
          C₁ * Real.log ((k + 1 : ℕ) + 2) :=
        hsub.trans (mul_le_mul_of_nonneg_left hlog_mono hC₁_pos.le)
      calc
        (zeroCountUpTo (k : ℝ) : ℝ) + ((zeroCountUpTo ((k : ℝ) + 1) - zeroCountUpTo (k : ℝ) : ℕ) : ℝ)
            ≤ (k : ℝ) * C₁ * Real.log ((k + 1 : ℕ) + 2) + C₁ * Real.log ((k + 1 : ℕ) + 2) :=
          add_le_add ih' hsub'
        _ = ((k + 1 : ℕ) : ℝ) * C₁ * Real.log ((k + 1 : ℕ) + 2) := by push_cast; ring
  have hmono : (zeroCountUpTo T : ℝ) ≤ (zeroCountUpTo (N : ℝ) : ℝ) := by
    exact_mod_cast zeroCountUpTo_mono (Nat.le_ceil T)
  have hlog_N : Real.log ((N : ℝ) + 2) ≤ 3 * Real.log T := by
    have hle_T3 : (N : ℝ) + 2 ≤ T ^ 3 := by
      have hN_lt : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      have hTsq : 4 ≤ T ^ 2 := by nlinarith
      have hTcube : 4 * T ≤ T ^ 3 := by nlinarith
      linarith
    calc
      Real.log ((N : ℝ) + 2) ≤ Real.log (T ^ 3) := Real.log_le_log (by positivity) hle_T3
      _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
  have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc
    (zeroCountUpTo T : ℝ) ≤ (zeroCountUpTo (N : ℝ) : ℝ) := hmono
    _ ≤ (N : ℝ) * C₁ * Real.log ((N : ℝ) + 2) := hnat_bound N
    _ ≤ (2 * T) * C₁ * (3 * Real.log T) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hN_le_twoT hC₁_pos.le) hlog_N
        (Real.log_nonneg (by linarith)) (by positivity)
    _ = C * T * Real.log T := by dsimp only [C]; ring

/-! ### Stirling Gamma-Term Imaginary Part Asymptotic -/

/-- Branch of `log Γ(w)` on `Complex.slitPlane` given by Stirling's representation:
`stirlingLogGamma w = (1 / 2) * log (2 * π) + (w - 1 / 2) * log w - w + stirlingRemainder w`. -/
noncomputable def stirlingLogGamma (w : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.log ((2 * Real.pi : ℝ) : ℂ) +
    (w - 1 / 2) * Complex.log w - w + stirlingRemainder w

/-- Exponential identity `Complex.exp (stirlingLogGamma w) = Complex.Gamma w` on
`Complex.slitPlane`. -/
theorem exp_stirlingLogGamma {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    Complex.exp (stirlingLogGamma w) = Complex.Gamma w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hexp_half : Complex.exp ((1 / 2 : ℂ) * Complex.log ((2 * Real.pi : ℝ) : ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [← Complex.ofReal_log h2pi_pos.le,
      show (1 / 2 : ℂ) * ((Real.log (2 * Real.pi) : ℝ) : ℂ) =
        (((Real.log (2 * Real.pi) * (1 / 2 : ℝ) : ℝ) : ℂ)) by push_cast; ring,
      ← Complex.ofReal_exp, ← Real.rpow_def_of_pos h2pi_pos, Real.sqrt_eq_rpow]
  have hcpow : w ^ (w - 1 / 2) = Complex.exp ((w - 1 / 2) * Complex.log w) := by
    rw [Complex.cpow_def_of_ne_zero hw0, mul_comm]
  rw [complex_gamma_eq_stirling hw, ← hexp_half, hcpow, stirlingLogGamma, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  ring

/-- Holomorphic derivative of `stirlingLogGamma` on `Complex.slitPlane` equals `digamma`. -/
theorem hasDerivAt_stirlingLogGamma {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt stirlingLogGamma (AnalyticNumberTheory.AnalyticTools.Gamma.digamma w) w := by
  have hlog : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hw
  have hmul : HasDerivAt (fun z : ℂ ↦ (z - 1 / 2) * Complex.log z)
      (1 * Complex.log w + (w - 1 / 2) * w⁻¹) w :=
    ((hasDerivAt_id w).sub_const (1 / 2 : ℂ)).mul hlog
  have hrem : HasDerivAt stirlingRemainder (deriv stirlingRemainder w) w :=
    (hasDerivAt_stirlingRemainder hw).differentiableAt.hasDerivAt
  have hsum : HasDerivAt stirlingLogGamma
      ((0 + (1 * Complex.log w + (w - 1 / 2) * w⁻¹)) - 1 + deriv stirlingRemainder w) w :=
    (((hasDerivAt_const w _).add hmul).sub (hasDerivAt_id w)).add hrem
  refine hsum.congr_deriv ?_
  rw [digamma_eq_stirling hw]
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  field_simp [hw0]
  ring

private lemma continuousOn_digamma_slitPlane :
    ContinuousOn AnalyticNumberTheory.AnalyticTools.Gamma.digamma Complex.slitPlane := by
  have hdiff : DifferentiableOn ℂ stirlingLogGamma Complex.slitPlane := fun w hw ↦
    (hasDerivAt_stirlingLogGamma hw).differentiableAt.differentiableWithinAt
  have han : AnalyticOnNhd ℂ stirlingLogGamma Complex.slitPlane :=
    hdiff.analyticOnNhd Complex.isOpen_slitPlane
  have heq : Set.EqOn AnalyticNumberTheory.AnalyticTools.Gamma.digamma (deriv stirlingLogGamma)
      Complex.slitPlane := fun w hw ↦ (hasDerivAt_stirlingLogGamma hw).deriv.symm
  exact ((han.deriv).continuousOn).congr heq

/-- On the positive real axis `(0, ∞)`, `stirlingLogGamma` is real-valued. -/
theorem stirlingLogGamma_ofReal_im {x : ℝ} (hx : 0 < x) :
    (stirlingLogGamma (x : ℂ)).im = 0 := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have heq : stirlingLogGamma (x : ℂ) =
      (((1 / 2 : ℝ) * Real.log (2 * Real.pi) + (x - 1 / 2) * Real.log x - x +
        stirlingRemainderReal x : ℝ) : ℂ) := by
    unfold stirlingLogGamma
    rw [← Complex.ofReal_log h2pi_pos.le, ← Complex.ofReal_log hx.le,
      stirlingRemainder_ofReal hx]
    push_cast
    ring
  rw [heq, Complex.ofReal_im]

/-- Main Riemann–von Mangoldt smooth counting term `(T / (2 * π)) * log (T / (2 * π * e))`. -/
noncomputable def thetaMain (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))

private lemma stirlingLogGamma_vertical_strip_im_asymptotic (a : ℝ) (ha_pos : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(1 / Real.pi) * (stirlingLogGamma ((a : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi -
        (thetaMain T + (a - 1 / 2) / 2)| ≤ C / T := by
  let K : ℝ := (4 * (max |a| |a|) ^ 2 + 5) / 6
  let C : ℝ := (2 * |a - 1 / 2| * a + a ^ 2 + K) / Real.pi + 1
  refine ⟨C, by positivity, fun T hT ↦ ?_⟩
  let w : ℂ := (a : ℂ) + ((T / 2 : ℝ) : ℂ) * I
  have hT_pos : 0 < T := by linarith
  have hT2_ge1 : 1 ≤ |T / 2| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hT2_pos : 0 < T / 2 := by linarith
  have hw_im_pos : 0 < w.im := by simp [w, hT2_pos]
  have hw_ne : w ≠ 0 := fun h ↦ by simp [h] at hw_im_pos
  have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  have harg : w.arg = Real.pi / 2 - Real.arctan (a / (T / 2)) :=
    arg_add_mul_I_of_pos hT2_pos
  have hw_norm_sq : ‖w‖ ^ 2 = (T / 2) ^ 2 * (1 + (2 * a / T) ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add]
    field_simp [hT_pos.ne']
    ring
  have hnorm_log : Real.log ‖w‖ =
      Real.log (T / 2) + (1 / 2 : ℝ) * Real.log (1 + (2 * a / T) ^ 2) := by
    have hmul : ‖w‖ = (T / 2) * Real.sqrt (1 + (2 * a / T) ^ 2) := by
      have hsq : ‖w‖ ^ 2 = ((T / 2) * Real.sqrt (1 + (2 * a / T) ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), hw_norm_sq]
      exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
    rw [hmul, Real.log_mul hT2_pos.ne' (Real.sqrt_pos.mpr (by positivity)).ne',
      Real.sqrt_eq_rpow, Real.log_rpow (by positivity)]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have him_exact : (stirlingLogGamma w).im =
      (a - 1 / 2) * (Real.pi / 2 - Real.arctan (2 * a / T)) +
        (T / 2) * (Real.log (T / 2) + (1 / 2 : ℝ) * Real.log (1 + (2 * a / T) ^ 2)) -
        T / 2 + (stirlingRemainder w).im := by
    have hlog_im : ((1 / 2 : ℂ) * Complex.log ((2 * Real.pi : ℝ) : ℂ)).im = 0 := by
      rw [← Complex.ofReal_log h2pi_pos.le]
      simp [Complex.mul_im]
    unfold stirlingLogGamma
    rw [Complex.add_im, Complex.sub_im, Complex.add_im, hlog_im, zero_add,
      Complex.mul_im, Complex.log_re, Complex.log_im, hnorm_log, harg]
    have hw_re : (w - 1 / 2).re = a - 1 / 2 := by simp [w]
    have hw_im : (w - 1 / 2).im = T / 2 := by simp [w]
    have hw_im' : w.im = T / 2 := by simp [w]
    have hdiv_eq : a / (T / 2) = 2 * a / T := by ring
    rw [hw_re, hw_im, hw_im', hdiv_eq]
  have hmain_id :
      (1 / Real.pi) * ((a - 1 / 2) * (Real.pi / 2) + (T / 2) * Real.log (T / 2) - T / 2) -
        (T / (2 * Real.pi)) * Real.log Real.pi =
      thetaMain T + (a - 1 / 2) / 2 := by
    have hlog_eq : Real.log (T / (2 * Real.pi * Real.exp 1)) =
        Real.log (T / 2) - Real.log Real.pi - 1 := by
      have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
      have hdiv : T / (2 * Real.pi * Real.exp 1) = (T / 2) / (Real.pi * Real.exp 1) := by ring
      rw [hdiv, Real.log_div hT2_pos.ne' (mul_pos Real.pi_pos he_pos).ne',
        Real.log_mul Real.pi_pos.ne' he_pos.ne', Real.log_exp]
      ring
    dsimp only [thetaMain]
    rw [hlog_eq]
    field_simp [Real.pi_pos.ne']
    ring
  have hdiff :
      (1 / Real.pi) * (stirlingLogGamma w).im - (T / (2 * Real.pi)) * Real.log Real.pi -
        (thetaMain T + (a - 1 / 2) / 2) =
      (1 / Real.pi) * (-(a - 1 / 2) * Real.arctan (2 * a / T) +
        (T / 4) * Real.log (1 + (2 * a / T) ^ 2) + (stirlingRemainder w).im) := by
    rw [← hmain_id, him_exact]
    ring
  have harctan_le : |Real.arctan (2 * a / T)| ≤ 2 * a / T := by
    have hg_abs : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
      intro u hu
      have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 u)
        (continuous_arctan.sub continuous_id).continuousOn
        (fun x _ ↦ ((Real.hasDerivAt_arctan' x).sub (hasDerivAt_id x)).hasDerivWithinAt)
        (fun x _ ↦ by
          have : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
          have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
          linarith)
      have hle := hanti (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
      change Real.arctan u - u ≤ Real.arctan 0 - 0 at hle
      simp only [Real.arctan_zero, sub_zero] at hle
      linarith
    have hpos_arg : 0 ≤ 2 * a / T := by positivity
    rw [abs_of_nonneg (Real.arctan_nonneg.mpr hpos_arg)]
    exact hg_abs (2 * a / T) hpos_arg
  have hrem_bd : |(stirlingRemainder w).im| ≤ K / T := by
    have hst := norm_stirlingRemainder_strip_le (σ₁ := a) (σ₂ := a) (σ := a) (t := T / 2)
      (Set.left_mem_Icc.mpr le_rfl) hT2_ge1
    have him_le : |(stirlingRemainder w).im| ≤ ‖stirlingRemainder w‖ :=
      Complex.abs_im_le_norm _
    have hbound_eq : (4 * (max |a| |a|) ^ 2 + 5) / (12 * |T / 2|) = K / T := by
      rw [abs_of_pos hT2_pos]
      dsimp only [K]
      field_simp [hT_pos.ne']
      ring
    exact him_le.trans (hst.trans_eq hbound_eq)
  have hterm1 : |-(a - 1 / 2) * Real.arctan (2 * a / T)| ≤ (2 * |a - 1 / 2| * a) / T := by
    rw [abs_mul, abs_neg]
    calc
      |a - 1 / 2| * |Real.arctan (2 * a / T)| ≤ |a - 1 / 2| * (2 * a / T) :=
        mul_le_mul_of_nonneg_left harctan_le (abs_nonneg _)
      _ = (2 * |a - 1 / 2| * a) / T := by ring
  have hlog_err2 : |(T / 4) * Real.log (1 + (2 * a / T) ^ 2)| ≤ a ^ 2 / T := by
    have hnn : 0 ≤ (T / 4) * Real.log (1 + (2 * a / T) ^ 2) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by linarith [sq_nonneg (2 * a / T)]))
    rw [abs_of_nonneg hnn]
    have h1 : Real.log (1 + (2 * a / T) ^ 2) ≤ (2 * a / T) ^ 2 := by
      have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + (2 * a / T) ^ 2)
      linarith
    calc
      (T / 4) * Real.log (1 + (2 * a / T) ^ 2) ≤ (T / 4) * (2 * a / T) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = a ^ 2 / T := by field_simp [hT_pos.ne']; ring
  rw [hdiff, abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  have htri : |-(a - 1 / 2) * Real.arctan (2 * a / T) +
      (T / 4) * Real.log (1 + (2 * a / T) ^ 2) + (stirlingRemainder w).im| ≤
      (2 * |a - 1 / 2| * a + a ^ 2 + K) / T := by
    have h1 := abs_add_le (-(a - 1 / 2) * Real.arctan (2 * a / T) +
      (T / 4) * Real.log (1 + (2 * a / T) ^ 2)) (stirlingRemainder w).im
    have h2 := abs_add_le (-(a - 1 / 2) * Real.arctan (2 * a / T))
      ((T / 4) * Real.log (1 + (2 * a / T) ^ 2))
    linarith [hterm1, hlog_err2, hrem_bd, show (2 * |a - 1 / 2| * a) / T + a ^ 2 / T + K / T =
      (2 * |a - 1 / 2| * a + a ^ 2 + K) / T by ring]
  calc
    1 / Real.pi * |-(a - 1 / 2) * Real.arctan (2 * a / T) +
        (T / 4) * Real.log (1 + (2 * a / T) ^ 2) + (stirlingRemainder w).im|
        ≤ 1 / Real.pi * ((2 * |a - 1 / 2| * a + a ^ 2 + K) / T) :=
      mul_le_mul_of_nonneg_left htri (by positivity)
    _ ≤ C / T := by
      have h1 : (2 * |a - 1 / 2| * a + a ^ 2 + K) / Real.pi ≤ C := by
        dsimp only [C]; linarith
      calc
        1 / Real.pi * ((2 * |a - 1 / 2| * a + a ^ 2 + K) / T)
            = ((2 * |a - 1 / 2| * a + a ^ 2 + K) / Real.pi) / T := by ring
        _ ≤ C / T := div_le_div_of_nonneg_right h1 hT_pos.le

/-- **Stirling gamma-term imaginary part asymptotic**:
`(1 / π) * Im stirlingLogGamma (1/4 + iT/2) - (T / (2π)) * log π = (T / (2π)) * log (T / (2πe)) - 1/8 + O(1/T)`. -/
theorem gamma_quarter_im_sub_log_pi_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(1 / Real.pi) * (stirlingLogGamma ((1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi - (thetaMain T - 1 / 8)| ≤ C / T := by
  obtain ⟨C, hC_pos, hbd⟩ := stirlingLogGamma_vertical_strip_im_asymptotic (1 / 4) (by norm_num)
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  have h := hbd T hT
  have hcast : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by push_cast; ring
  have hconst : (1 / 4 - 1 / 2 : ℝ) / 2 = -1 / 8 := by norm_num
  rw [hcast, hconst] at h
  refine le_of_eq_of_le (congrArg abs ?_) h
  ring

/-- Adding `1` (from the `s * (s - 1)` factor) gives `+ 7 / 8` in the Stirling gamma term. -/
theorem gamma_quarter_im_sub_log_pi_add_one_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(1 / Real.pi) * (stirlingLogGamma ((1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi + 1 - (thetaMain T + 7 / 8)| ≤ C / T := by
  obtain ⟨C, hC_pos, hbd⟩ := gamma_quarter_im_sub_log_pi_asymptotic
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  have heq : (1 / Real.pi) * (stirlingLogGamma ((1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
      (T / (2 * Real.pi)) * Real.log Real.pi + 1 - (thetaMain T + 7 / 8) =
      (1 / Real.pi) * (stirlingLogGamma ((1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi - (thetaMain T - 1 / 8) := by ring
  rw [heq]
  exact hbd T hT

/-- Contour-shifted Stirling asymptotic (`s/2 + 1 = 5/4 + iT/2` plus `(1 / π) * arg (-1/2 + iT)`):
equals `thetaMain T + 7 / 8 + O(1 / T)` for `T ≥ 2`. -/
theorem gamma_five_quarters_add_arg_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi +
        (1 / Real.pi) * ((-1 / 2 : ℂ) + (T : ℂ) * I).arg - (thetaMain T + 7 / 8)| ≤ C / T := by
  obtain ⟨C₁, hC₁_pos, hbd⟩ := stirlingLogGamma_vertical_strip_im_asymptotic (5 / 4) (by norm_num)
  refine ⟨C₁ + 1 / (2 * Real.pi), by positivity, fun T hT ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  have h1 := hbd T hT
  have hcast54 : ((5 / 4 : ℝ) : ℂ) = (5 / 4 : ℂ) := by push_cast; ring
  have hconst38 : (5 / 4 - 1 / 2 : ℝ) / 2 = 3 / 8 := by norm_num
  rw [hcast54, hconst38] at h1
  have harg : ((-1 / 2 : ℂ) + (T : ℂ) * I).arg = Real.pi / 2 + Real.arctan (1 / (2 * T)) := by
    have h := arg_add_mul_I_of_pos (σ := -1 / 2) hT_pos
    have hcast_half : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by push_cast; ring
    rw [hcast_half] at h
    rw [h, show (-1 / 2 : ℝ) / T = -(1 / (2 * T)) by ring, Real.arctan_neg]
    ring
  have harctan_bd : |(1 / Real.pi) * Real.arctan (1 / (2 * T))| ≤ (1 / (2 * Real.pi)) / T := by
    have hnn : 0 ≤ Real.arctan (1 / (2 * T)) := Real.arctan_nonneg.mpr (by positivity)
    have harc : Real.arctan (1 / (2 * T)) ≤ 1 / (2 * T) := by
      have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / (2 * T)))
        (continuous_arctan.sub continuous_id).continuousOn
        (fun x _ ↦ ((Real.hasDerivAt_arctan' x).sub (hasDerivAt_id x)).hasDerivWithinAt)
        (fun x _ ↦ by
          have : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
          have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
          linarith)
      have hle := hanti (Set.left_mem_Icc.mpr (by positivity))
        (Set.right_mem_Icc.mpr (by positivity)) (by positivity)
      change Real.arctan (1 / (2 * T)) - 1 / (2 * T) ≤ Real.arctan 0 - 0 at hle
      simp only [Real.arctan_zero, sub_zero] at hle
      linarith
    rw [abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos), abs_of_nonneg hnn]
    calc
      1 / Real.pi * Real.arctan (1 / (2 * T)) ≤ 1 / Real.pi * (1 / (2 * T)) :=
        mul_le_mul_of_nonneg_left harc (by positivity)
      _ = (1 / (2 * Real.pi)) / T := by ring
  have hid : (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
      (T / (2 * Real.pi)) * Real.log Real.pi +
      (1 / Real.pi) * ((-1 / 2 : ℂ) + (T : ℂ) * I).arg - (thetaMain T + 7 / 8) =
      ((1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi - (thetaMain T + 3 / 8)) +
      (1 / Real.pi) * Real.arctan (1 / (2 * T)) := by
    rw [harg]
    field_simp [Real.pi_pos.ne']
    ring
  rw [hid]
  calc
    |((1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi - (thetaMain T + 3 / 8)) +
      (1 / Real.pi) * Real.arctan (1 / (2 * T))|
        ≤ |(1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
            (T / (2 * Real.pi)) * Real.log Real.pi - (thetaMain T + 3 / 8)| +
          |(1 / Real.pi) * Real.arctan (1 / (2 * T))| := abs_add_le _ _
    _ ≤ C₁ / T + (1 / (2 * Real.pi)) / T := add_le_add h1 harctan_bd
    _ = (C₁ + 1 / (2 * Real.pi)) / T := by ring

/-! ### Rectangular Argument Principle for Entire Functions -/

private lemma riemannZeta_ofReal_re_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hs0 : 0 < ((σ : ℂ)).re := by simpa using h0
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  rw [riemannZeta_eq_eulerMaclaurin_of_re_pos hs0 hs1]
  have hdom_int : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-σ - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul (1 / 2)
  have h_int : IntegrableOn (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1))
      (Set.Ioi 1) := by
    refine Integrable.mono' hdom_int ?_ ?_
    · have hmeas_saw : Measurable fun u : ℝ ↦ (sawtooth u : ℂ) :=
        Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const _)
      have hcont_pow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (-(σ : ℂ) - 1)) (Set.Ioi 1) :=
        Complex.continuous_ofReal.continuousOn.cpow_const fun u hu ↦
          Or.inl (by exact_mod_cast (lt_trans zero_lt_one hu))
      exact (hmeas_saw.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
        (hcont_pow.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_pos : 0 < u := lt_trans zero_lt_one hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
      exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)
  have hmono : ∫ u in Set.Ioi (1 : ℝ), ‖(sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖ ≤
      ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) := by
    refine setIntegral_mono_on h_int.norm hdom_int measurableSet_Ioi fun u hu ↦ ?_
    have hu_pos : 0 < u := lt_trans zero_lt_one hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
    exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)
  have heval : ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) = (1 / 2) / σ := by
    rw [integral_const_mul]
    have hint_rpow : ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 1) = 1 / σ := by
      have htend : Tendsto (fun R : ℝ ↦ ∫ u in (1 : ℝ)..R, u ^ (-σ - 1)) atTop
          (𝓝 (∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 1))) :=
        intervalIntegral_tendsto_integral_Ioi 1
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one) tendsto_id
      have hcalc : ∀ R : ℝ, 1 ≤ R →
          ∫ u in (1 : ℝ)..R, u ^ (-σ - 1) = (1 - R ^ (-σ)) / σ := by
        intro R hR
        rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
          rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
        simp only [Real.one_rpow]
        have hexp : -σ - 1 + 1 = -σ := by ring
        rw [hexp]
        field_simp [h0.ne']
        ring
      have hlim : Tendsto (fun R : ℝ ↦ (1 - R ^ (-σ)) / σ) atTop (𝓝 (1 / σ)) := by
        have hr : Tendsto (fun R : ℝ ↦ R ^ (-σ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop h0
        simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hr).div_const σ
      exact tendsto_nhds_unique htend (hlim.congr' (by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR; exact (hcalc R hR).symm))
    rw [hint_rpow]; ring
  have hint_bd : ‖(σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ),
      (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖ ≤ 1 / 2 := by
    have hnorm_int : ‖∫ u in Set.Ioi (1 : ℝ),
        (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖ ≤ (1 / 2) / σ :=
      (norm_integral_le_integral_norm _).trans (hmono.trans_eq heval)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le]
    calc
      σ * ‖∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖
          ≤ σ * ((1 / 2) / σ) := mul_le_mul_of_nonneg_left hnorm_int h0.le
      _ = 1 / 2 := by field_simp [h0.ne']
  have hterm_re : ((1 : ℂ) / ((σ : ℂ) - 1) + 1 / 2).re = 1 / (σ - 1) + 1 / 2 := by
    have heq : (1 : ℂ) / ((σ : ℂ) - 1) + 1 / 2 = (((1 / (σ - 1) + 1 / 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [heq, Complex.ofReal_re]
  have h1_lt : 1 / (σ - 1) < -1 := by
    rw [div_lt_iff_of_neg (by linarith)]
    linarith
  have hre_sub : -((σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ),
      (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)).re ≤ 1 / 2 := by
    have h := Complex.abs_re_le_norm ((σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ),
      (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1))
    linarith [(neg_le_abs _).trans h, hint_bd]
  rw [Complex.sub_re, hterm_re]
  linarith

private lemma xi_ne_zero_ofReal (x : ℝ) : xi (x : ℂ) ≠ 0 := by
  rcases le_or_gt x 0 with hx0 | hx0
  · exact xi_ne_zero_of_re_nonpos (by simpa using hx0)
  · rcases le_or_gt 1 x with hx1 | hx1
    · exact xi_ne_zero_of_one_le_re (by simpa using hx1)
    · intro hzero
      have hcrit := (xi_eq_zero_iff).mp hzero
      have hre := riemannZeta_ofReal_re_neg hx0 hx1
      rw [hcrit.1, Complex.zero_re] at hre
      exact lt_irrefl 0 hre

private lemma extract_zeros_from_finset (U : Set ℂ) (K : Set ℂ)
    (Z : Finset ℂ) (hZK : (Z : Set ℂ) ⊆ K) (n : ℕ) :
    ∀ (f : ℂ → ℂ), AnalyticOnNhd ℂ f U →
      (∀ ρ ∈ K, f ρ = 0 → ρ ∈ Z) →
      (∀ ρ ∈ Z, ρ ∈ U ∧ analyticOrderAt f ρ ≠ ⊤) →
      (∑ ρ ∈ Z, analyticOrderNatAt f ρ) = n →
      ∃ (zs : List ℂ) (g : ℂ → ℂ),
        (∀ ρ ∈ zs, ρ ∈ K ∧ f ρ = 0) ∧
        zs.length = n ∧
        AnalyticOnNhd ℂ g U ∧
        (∀ ρ ∈ K, g ρ ≠ 0) ∧
        (∀ z : ℂ, f z = (zs.map (fun ρ ↦ z - ρ)).prod * g z) := by
  classical
  induction n with
  | zero =>
    intro f hf hKZ _ hsum
    refine ⟨[], f, fun _ h ↦ by simp at h, rfl, hf, fun ρ hρK h0 ↦ ?_, fun z ↦ by simp⟩
    have hρZ : ρ ∈ Z := hKZ ρ hρK h0
    have hord0 : analyticOrderNatAt f ρ = 0 := by
      have hle : analyticOrderNatAt f ρ ≤ ∑ u ∈ Z, analyticOrderNatAt f u :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hρZ
      omega
    have htop := (by assumption : ∀ u ∈ Z, u ∈ U ∧ analyticOrderAt f u ≠ ⊤) ρ hρZ
    have hord_eq0 : analyticOrderAt f ρ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop.2, hord0]; rfl
    exact ((hf ρ htop.1).analyticOrderAt_eq_zero.mp hord_eq0) h0
  | succ n ih =>
    intro f hf hKZ hU hsum
    have hpos_sum : 0 < ∑ ρ ∈ Z, analyticOrderNatAt f ρ := by omega
    obtain ⟨a, haZ, ha_pos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos_sum.ne'
    have haK : a ∈ K := hZK haZ
    have ha0 : f a = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero ha_pos
    let g₁ : ℂ → ℂ := dslope f a
    have hg₁_an : AnalyticOnNhd ℂ g₁ U := hf.dslope a
    have hfac : ∀ z : ℂ, f z = (z - a) * g₁ z := fun z ↦ by
      simpa [smul_eq_mul] using (sub_smul_dslope_of_zero ha0 z).symm
    have hg₁_KZ : ∀ ρ ∈ K, g₁ ρ = 0 → ρ ∈ Z := fun ρ hρK h0 ↦
      hKZ ρ hρK (by rw [hfac ρ, h0, mul_zero])
    have hg₁_ord_all : ∀ ρ ∈ Z,
        ρ ∈ U ∧ analyticOrderAt g₁ ρ ≠ ⊤ ∧
          (ρ = a → analyticOrderNatAt f ρ = analyticOrderNatAt g₁ ρ + 1) ∧
          (ρ ≠ a → analyticOrderNatAt f ρ = analyticOrderNatAt g₁ ρ) := by
      intro ρ hρZ
      obtain ⟨hρU, htop⟩ := hU ρ hρZ
      have hlin_an : AnalyticAt ℂ (fun z : ℂ ↦ z - a) ρ := by fun_prop
      have hg₁_at : AnalyticAt ℂ g₁ ρ := hg₁_an ρ hρU
      have hfeq : f = (fun z : ℂ ↦ z - a) * g₁ := funext hfac
      have hord_mul : analyticOrderAt f ρ =
          analyticOrderAt (fun z : ℂ ↦ z - a) ρ + analyticOrderAt g₁ ρ := by
        rw [hfeq]; exact analyticOrderAt_mul hlin_an hg₁_at
      have hg₁_top : analyticOrderAt g₁ ρ ≠ ⊤ := by
        intro h
        rw [h, add_top] at hord_mul
        exact htop hord_mul
      refine ⟨hρU, hg₁_top, fun hEq ↦ ?_, fun hNe ↦ ?_⟩
      · subst hEq
        have hlin_ord : analyticOrderAt (fun z : ℂ ↦ z - ρ) ρ = 1 := by
          have h1 : AnalyticAt ℂ (fun z : ℂ ↦ z - ρ) ρ := by fun_prop
          exact h1.analyticOrderAt_eq_natCast.mpr
            ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
              Filter.Eventually.of_forall fun z ↦ by simp⟩
        rw [hlin_ord] at hord_mul
        have hcast : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) =
            ((analyticOrderNatAt g₁ ρ + 1 : ℕ) : ℕ∞) := by
          push_cast
          rw [Nat.cast_analyticOrderNatAt htop, Nat.cast_analyticOrderNatAt hg₁_top, hord_mul,
            add_comm]
        exact Nat.cast_injective hcast
      · have hlin_ord : analyticOrderAt (fun z : ℂ ↦ z - a) ρ = 0 :=
          hlin_an.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hNe)
        rw [hlin_ord, zero_add] at hord_mul
        have hcast : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) = ((analyticOrderNatAt g₁ ρ : ℕ) : ℕ∞) := by
          rw [Nat.cast_analyticOrderNatAt htop, Nat.cast_analyticOrderNatAt hg₁_top, hord_mul]
        exact Nat.cast_injective hcast
    have hg₁_sum : ∑ ρ ∈ Z, analyticOrderNatAt g₁ ρ = n := by
      have hsplit : ∑ ρ ∈ Z, analyticOrderNatAt f ρ =
          ∑ ρ ∈ Z, (analyticOrderNatAt g₁ ρ + if ρ = a then 1 else 0) := by
        refine Finset.sum_congr rfl fun ρ hρZ ↦ ?_
        split_ifs with hEq
        · rw [(hg₁_ord_all ρ hρZ).2.2.1 hEq]
        · rw [(hg₁_ord_all ρ hρZ).2.2.2 hEq, add_zero]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsplit
      split_ifs at hsplit
      omega
    obtain ⟨zs', g, hzs'_prop, hzs'_len, hg_an, hg_ne, hprod'⟩ :=
      ih g₁ hg₁_an hg₁_KZ (fun ρ hρZ ↦ ⟨(hg₁_ord_all ρ hρZ).1, (hg₁_ord_all ρ hρZ).2.1⟩) hg₁_sum
    refine ⟨a :: zs', g, fun ρ hρ ↦ ?_, by simp [hzs'_len], hg_an, hg_ne, fun z ↦ ?_⟩
    · rcases List.mem_cons.mp hρ with rfl | hmem
      · exact ⟨haK, ha0⟩
      · obtain ⟨hK, hg10⟩ := hzs'_prop ρ hmem
        exact ⟨hK, by rw [hfac ρ, hg10, mul_zero]⟩
    · rw [List.map_cons, List.prod_cons, hfac z, hprod' z]
      ring

private lemma continuousOn_one_div_horiz (y₀ : ℝ) (ρ : ℂ) (hne : y₀ - ρ.im ≠ 0) (s : Set ℝ) :
    ContinuousOn (fun x : ℝ ↦ (1 : ℂ) / ((x : ℂ) + (y₀ : ℂ) * I - ρ)) s := by
  have hden : Continuous fun x : ℝ ↦ (x : ℂ) + (y₀ : ℂ) * I - ρ :=
    (Complex.continuous_ofReal.add continuous_const).sub continuous_const
  have hne' : ∀ x : ℝ, (x : ℂ) + (y₀ : ℂ) * I - ρ ≠ 0 := fun x h0 ↦ by
    have := congrArg Complex.im (sub_eq_zero.mp h0)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, mul_zero, mul_one, add_zero, zero_add] at this
    exact hne (sub_eq_zero.mpr this)
  exact (continuous_const.div hden hne').continuousOn

private lemma continuousOn_one_div_vert (x₀ : ℝ) (ρ : ℂ) (hne : x₀ - ρ.re ≠ 0) (s : Set ℝ) :
    ContinuousOn (fun y : ℝ ↦ (1 : ℂ) / ((x₀ : ℂ) + (y : ℂ) * I - ρ)) s := by
  have hden : Continuous fun y : ℝ ↦ (x₀ : ℂ) + (y : ℂ) * I - ρ :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const
  have hne' : ∀ y : ℝ, (x₀ : ℂ) + (y : ℂ) * I - ρ ≠ 0 := fun y h0 ↦ by
    have := congrArg Complex.re (sub_eq_zero.mp h0)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at this
    exact hne (sub_eq_zero.mpr this)
  exact (continuous_const.div hden hne').continuousOn

private noncomputable def rectEdgeHorizAnti (y₀ : ℝ) (u : ℝ) : ℂ :=
  ((1 / 2 * Real.log (u ^ 2 + y₀ ^ 2) : ℝ) : ℂ) - I * ((Real.arctan (u / y₀) : ℝ) : ℂ)

private noncomputable def rectEdgeVertAnti (u₀ : ℝ) (v : ℝ) : ℂ :=
  ((1 / 2 * Real.log (u₀ ^ 2 + v ^ 2) : ℝ) : ℂ) + I * ((Real.arctan (v / u₀) : ℝ) : ℂ)

private lemma hasDerivAt_rectEdgeHorizAnti {y₀ : ℝ} (hy₀ : y₀ ≠ 0) (u : ℝ) :
    HasDerivAt (rectEdgeHorizAnti y₀) (1 / ((u : ℂ) + (y₀ : ℂ) * I)) u := by
  have hden_pos : 0 < u ^ 2 + y₀ ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * Real.log (t ^ 2 + y₀ ^ 2))
      (u / (u ^ 2 + y₀ ^ 2)) u := by
    have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2 + y₀ ^ 2) (2 * u) u := by
      simpa using ((hasDerivAt_pow 2 u).add_const (y₀ ^ 2))
    have hlog := hsq.log hden_pos.ne'
    exact (hlog.const_mul (1 / 2 : ℝ)).congr_deriv (by
      field_simp [hden_pos.ne'])
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.arctan (t / y₀)) (y₀ / (u ^ 2 + y₀ ^ 2)) u := by
    have hdiv : HasDerivAt (fun t : ℝ ↦ t / y₀) (1 / y₀) u := by
      simpa using (hasDerivAt_id u).div_const y₀
    have harc := (Real.hasDerivAt_arctan (u / y₀)).comp u hdiv
    refine harc.congr_deriv ?_
    field_simp [hy₀, hden_pos.ne']
    ring
  have hc : HasDerivAt (rectEdgeHorizAnti y₀)
      (((u / (u ^ 2 + y₀ ^ 2) : ℝ) : ℂ) - I * ((y₀ / (u ^ 2 + y₀ ^ 2) : ℝ) : ℂ)) u :=
    (h1.ofReal_comp).sub ((h2.ofReal_comp).const_mul I)
  refine hc.congr_deriv ?_
  have hden_c : ((u : ℂ) + (y₀ : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hy₀ this
  have hden2_c : ((u : ℂ) ^ 2 + (y₀ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden_pos.ne'
  push_cast
  field_simp [hden_c, hden2_c]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma hasDerivAt_rectEdgeVertAnti {u₀ : ℝ} (hu₀ : u₀ ≠ 0) (v : ℝ) :
    HasDerivAt (rectEdgeVertAnti u₀) (I / ((u₀ : ℂ) + (v : ℂ) * I)) v := by
  have hden_pos : 0 < u₀ ^ 2 + v ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * Real.log (u₀ ^ 2 + t ^ 2))
      (v / (u₀ ^ 2 + v ^ 2)) v := by
    have hsq : HasDerivAt (fun t : ℝ ↦ u₀ ^ 2 + t ^ 2) (2 * v) v := by
      simpa using ((hasDerivAt_pow 2 v).const_add (u₀ ^ 2))
    have hlog := hsq.log hden_pos.ne'
    exact (hlog.const_mul (1 / 2 : ℝ)).congr_deriv (by
      field_simp [hden_pos.ne'])
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.arctan (t / u₀)) (u₀ / (u₀ ^ 2 + v ^ 2)) v := by
    have hdiv : HasDerivAt (fun t : ℝ ↦ t / u₀) (1 / u₀) v := by
      simpa using (hasDerivAt_id v).div_const u₀
    have harc := (Real.hasDerivAt_arctan (v / u₀)).comp v hdiv
    refine harc.congr_deriv ?_
    field_simp [hu₀, hden_pos.ne']
  have hc : HasDerivAt (rectEdgeVertAnti u₀)
      (((v / (u₀ ^ 2 + v ^ 2) : ℝ) : ℂ) + I * ((u₀ / (u₀ ^ 2 + v ^ 2) : ℝ) : ℂ)) v :=
    (h1.ofReal_comp).add ((h2.ofReal_comp).const_mul I)
  refine hc.congr_deriv ?_
  have hden_c : ((u₀ : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hu₀ this
  have hden2_c : ((u₀ : ℂ) ^ 2 + (v : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden_pos.ne'
  push_cast
  field_simp [hden_c, hden2_c]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma arctan_div_add_arctan_div_inv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.arctan (p / q) + Real.arctan (q / p) = Real.pi / 2 := by
  have h := Real.arctan_inv_of_pos (div_pos hq hp)
  rw [inv_div] at h
  linarith

private lemma integral_boundary_rect_inv_sub {a b c d : ℝ} {ρ : ℂ}
    (ha : a < ρ.re) (hb : ρ.re < b) (hc : c < ρ.im) (hd : ρ.im < d) :
    (∫ x in a..b, (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ)) -
      (∫ x in a..b, (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ)) +
      I * (∫ y in c..d, (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ)) -
      I * (∫ y in c..d, (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ)) =
      2 * Real.pi * I := by
  let x₀ := ρ.re
  let y₀ := ρ.im
  have hc_ne : c - y₀ ≠ 0 := sub_ne_zero.mpr hc.ne
  have hd_ne : d - y₀ ≠ 0 := sub_ne_zero.mpr hd.ne'
  have ha_ne : a - x₀ ≠ 0 := sub_ne_zero.mpr ha.ne
  have hb_ne : b - x₀ ≠ 0 := sub_ne_zero.mpr hb.ne'
  have heval_bot : ∫ x in a..b, (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ) =
      rectEdgeHorizAnti (c - y₀) (b - x₀) - rectEdgeHorizAnti (c - y₀) (a - x₀) := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun t : ℝ ↦ rectEdgeHorizAnti (c - y₀) (t - x₀))
          ((1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ)) x := by
      intro x _
      have hsub : HasDerivAt (fun t : ℝ ↦ t - x₀) 1 x := (hasDerivAt_id x).sub_const x₀
      have hc' := (hasDerivAt_rectEdgeHorizAnti hc_ne (x - x₀)).scomp x hsub
      refine hc'.congr_deriv ?_
      have hz_eq : ((x - x₀ : ℝ) : ℂ) + ((c - y₀ : ℝ) : ℂ) * I =
          (x : ℂ) + (c : ℂ) * I - ρ := by
        apply Complex.ext <;> simp [x₀, y₀]
      rw [one_smul, hz_eq]
    have hcont : ContinuousOn (fun x : ℝ ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ))
        (Set.uIcc a b) :=
      continuousOn_one_div_horiz c ρ hc_ne (Set.uIcc a b)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have heval_top : ∫ x in a..b, (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ) =
      rectEdgeHorizAnti (d - y₀) (b - x₀) - rectEdgeHorizAnti (d - y₀) (a - x₀) := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun t : ℝ ↦ rectEdgeHorizAnti (d - y₀) (t - x₀))
          ((1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ)) x := by
      intro x _
      have hsub : HasDerivAt (fun t : ℝ ↦ t - x₀) 1 x := (hasDerivAt_id x).sub_const x₀
      have hc' := (hasDerivAt_rectEdgeHorizAnti hd_ne (x - x₀)).scomp x hsub
      refine hc'.congr_deriv ?_
      have hz_eq : ((x - x₀ : ℝ) : ℂ) + ((d - y₀ : ℝ) : ℂ) * I =
          (x : ℂ) + (d : ℂ) * I - ρ := by
        apply Complex.ext <;> simp [x₀, y₀]
      rw [one_smul, hz_eq]
    have hcont : ContinuousOn (fun x : ℝ ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ))
        (Set.uIcc a b) :=
      continuousOn_one_div_horiz d ρ hd_ne (Set.uIcc a b)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have heval_right : I * ∫ y in c..d, (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ) =
      rectEdgeVertAnti (b - x₀) (d - y₀) - rectEdgeVertAnti (b - x₀) (c - y₀) := by
    have hderiv : ∀ y ∈ Set.uIcc c d,
        HasDerivAt (fun t : ℝ ↦ rectEdgeVertAnti (b - x₀) (t - y₀))
          (I * ((1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ))) y := by
      intro y _
      have hsub : HasDerivAt (fun t : ℝ ↦ t - y₀) 1 y := (hasDerivAt_id y).sub_const y₀
      have hc' := (hasDerivAt_rectEdgeVertAnti hb_ne (y - y₀)).scomp y hsub
      refine hc'.congr_deriv ?_
      have hz_eq : ((b - x₀ : ℝ) : ℂ) + ((y - y₀ : ℝ) : ℂ) * I =
          (b : ℂ) + (y : ℂ) * I - ρ := by
        apply Complex.ext <;> simp [x₀, y₀]
      rw [one_smul, hz_eq, mul_one_div]
    have hcont : ContinuousOn (fun y : ℝ ↦ I * ((1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ)))
        (Set.uIcc c d) :=
      continuousOn_const.mul (continuousOn_one_div_vert b ρ hb_ne (Set.uIcc c d))
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rwa [intervalIntegral.integral_const_mul] at hint
  have heval_left : I * ∫ y in c..d, (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ) =
      rectEdgeVertAnti (a - x₀) (d - y₀) - rectEdgeVertAnti (a - x₀) (c - y₀) := by
    have hderiv : ∀ y ∈ Set.uIcc c d,
        HasDerivAt (fun t : ℝ ↦ rectEdgeVertAnti (a - x₀) (t - y₀))
          (I * ((1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))) y := by
      intro y _
      have hsub : HasDerivAt (fun t : ℝ ↦ t - y₀) 1 y := (hasDerivAt_id y).sub_const y₀
      have hc' := (hasDerivAt_rectEdgeVertAnti ha_ne (y - y₀)).scomp y hsub
      refine hc'.congr_deriv ?_
      have hz_eq : ((a - x₀ : ℝ) : ℂ) + ((y - y₀ : ℝ) : ℂ) * I =
          (a : ℂ) + (y : ℂ) * I - ρ := by
        apply Complex.ext <;> simp [x₀, y₀]
      rw [one_smul, hz_eq, mul_one_div]
    have hcont : ContinuousOn (fun y : ℝ ↦ I * ((1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ)))
        (Set.uIcc c d) :=
      continuousOn_const.mul (continuousOn_one_div_vert a ρ ha_ne (Set.uIcc c d))
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rwa [intervalIntegral.integral_const_mul] at hint
  rw [heval_bot, heval_top, heval_right, heval_left]
  unfold rectEdgeHorizAnti rectEdgeVertAnti
  have hreal_sq : ∀ p q : ℝ, p ^ 2 + q ^ 2 = q ^ 2 + p ^ 2 := fun p q ↦ add_comm _ _
  have hc1 : Real.arctan ((b - x₀) / (y₀ - c)) + Real.arctan ((y₀ - c) / (b - x₀)) = Real.pi / 2 :=
    arctan_div_add_arctan_div_inv (sub_pos.mpr hb) (sub_pos.mpr hc)
  have hc2 : Real.arctan ((d - y₀) / (b - x₀)) + Real.arctan ((b - x₀) / (d - y₀)) = Real.pi / 2 :=
    arctan_div_add_arctan_div_inv (sub_pos.mpr hd) (sub_pos.mpr hb)
  have hc3 : Real.arctan ((x₀ - a) / (d - y₀)) + Real.arctan ((d - y₀) / (x₀ - a)) = Real.pi / 2 :=
    arctan_div_add_arctan_div_inv (sub_pos.mpr ha) (sub_pos.mpr hd)
  have hc4 : Real.arctan ((y₀ - c) / (x₀ - a)) + Real.arctan ((x₀ - a) / (y₀ - c)) = Real.pi / 2 :=
    arctan_div_add_arctan_div_inv (sub_pos.mpr hc) (sub_pos.mpr ha)
  have harc_sum :
      -Real.arctan ((b - x₀) / (c - y₀)) + Real.arctan ((a - x₀) / (c - y₀)) +
        Real.arctan ((b - x₀) / (d - y₀)) - Real.arctan ((a - x₀) / (d - y₀)) +
        Real.arctan ((d - y₀) / (b - x₀)) - Real.arctan ((c - y₀) / (b - x₀)) -
        Real.arctan ((d - y₀) / (a - x₀)) + Real.arctan ((c - y₀) / (a - x₀)) =
      2 * Real.pi := by
    rw [show c - y₀ = -(y₀ - c) by ring, show a - x₀ = -(x₀ - a) by ring]
    simp only [div_neg, neg_div, neg_neg, Real.arctan_neg]
    linarith [hc1, hc2, hc3, hc4]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, mul_one, sub_zero, add_zero]
    rw [hreal_sq (b - x₀) (d - y₀), hreal_sq (b - x₀) (c - y₀),
      hreal_sq (a - x₀) (d - y₀), hreal_sq (a - x₀) (c - y₀)]
    ring
  · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.re_ofNat, Complex.im_ofNat,
      one_mul, mul_zero, add_zero, mul_one, zero_add, sub_zero, zero_mul]
    linarith [harc_sum]

private lemma continuousOn_list_sum_inv_sub (s : Set ℝ) (l : List ℂ) (p : ℝ → ℂ)
    (hp : ContinuousOn p s) (hp_ne : ∀ t ∈ s, ∀ r ∈ l, p t ≠ r) :
    ContinuousOn (fun t : ℝ ↦ (l.map (fun r ↦ (1 : ℂ) / (p t - r))).sum) s := by
  induction l with
  | nil => simp; exact continuousOn_const
  | cons r l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuousOn_const.div (hp.sub continuousOn_const) fun t ht h0 ↦
      hp_ne t ht r List.mem_cons_self (sub_eq_zero.mp h0)).add
      (ih fun t ht r' hr' ↦ hp_ne t ht r' (List.mem_cons_of_mem _ hr'))

private lemma argument_principle_rect_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (Z : Finset ℂ) (hZ_int : ∀ ρ ∈ Z, ρ.re ∈ Set.Ioo a b ∧ ρ.im ∈ Set.Ioo c d)
    (hZ_all : ∀ w ∈ Set.Icc a b ×ℂ Set.Icc c d, f w = 0 → w ∈ Z) :
    (∫ x in a..b, deriv f ((x : ℂ) + (c : ℂ) * I) / f ((x : ℂ) + (c : ℂ) * I)) -
      (∫ x in a..b, deriv f ((x : ℂ) + (d : ℂ) * I) / f ((x : ℂ) + (d : ℂ) * I)) +
      I * (∫ y in c..d, deriv f ((b : ℂ) + (y : ℂ) * I) / f ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y in c..d, deriv f ((a : ℂ) + (y : ℂ) * I) / f ((a : ℂ) + (y : ℂ) * I)) =
      2 * Real.pi * I * ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) := by
  let K : Set ℂ := Set.Icc a b ×ℂ Set.Icc c d
  have hZK : (Z : Set ℂ) ⊆ K := fun ρ hρ ↦ by
    have hi := hZ_int ρ hρ
    exact ⟨Set.Ioo_subset_Icc_self hi.1, Set.Ioo_subset_Icc_self hi.2⟩
  have hf_ne : f ≠ 0 := by
    intro h0
    have ha_mem : (a : ℂ) + (c : ℂ) * I ∈ K :=
      ⟨by simp [hab.le], by simp [hcd.le]⟩
    have hz : f ((a : ℂ) + (c : ℂ) * I) = 0 := by simp [h0]
    have hin := hZ_int _ (hZ_all _ ha_mem hz)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.I_im, Complex.ofReal_im, mul_one, sub_zero, add_zero, Set.mem_Ioo] at hin
    exact lt_irrefl a hin.1.1
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hU_ord : ∀ ρ ∈ Z, ρ ∈ (Set.univ : Set ℂ) ∧ analyticOrderAt f ρ ≠ ⊤ := by
    obtain ⟨w₀, hw₀⟩ := Function.ne_iff.mp hf_ne
    intro ρ _
    refine ⟨Set.mem_univ ρ, hf_an.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ w₀) (Set.mem_univ ρ) ?_⟩
    rw [(hf_an w₀ (Set.mem_univ w₀)).analyticOrderAt_eq_zero.mpr hw₀]
    simp
  obtain ⟨zs, g, hzs_prop, hzs_len, hg_an, hg_ne, hprod⟩ :=
    extract_zeros_from_finset Set.univ K Z hZK (∑ ρ ∈ Z, analyticOrderNatAt f ρ) f hf_an
      hZ_all hU_ord rfl
  have hg_diff : Differentiable ℂ g := fun w ↦ (hg_an w (Set.mem_univ w)).differentiableAt
  have hK_eq : Set.uIcc a b ×ℂ Set.uIcc c d = K := by
    rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le hcd.le]
  have hg_ld_diff : DifferentiableOn ℂ (fun w : ℂ ↦ deriv g w / g w) K := by
    intro w hw
    have hg_deriv_diff : DifferentiableAt ℂ (deriv g) w :=
      ((hg_an w (Set.mem_univ w)).deriv).differentiableAt
    exact (hg_deriv_diff.div (hg_diff w) (hg_ne w hw)).differentiableWithinAt
  have hg_rect_zero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun w ↦ deriv g w / g w) ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I)
    (by simpa [hK_eq] using hg_ld_diff)
  have hrect_g :
      (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * I) / g ((x : ℂ) + (c : ℂ) * I)) -
        (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * I) / g ((x : ℂ) + (d : ℂ) * I)) +
        I * (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * I) / g ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * I) / g ((a : ℂ) + (y : ℂ) * I)) = 0 := by
    simpa [smul_eq_mul] using hg_rect_zero
  have hld_split : ∀ w : ℂ, (∀ ρ ∈ zs, w ≠ ρ) → g w ≠ 0 →
      deriv f w / f w = (zs.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum + deriv g w / g w := by
    intro w hw_ne hgw
    have hf_eq : f = fun z ↦ (zs.map (fun ρ ↦ z - ρ)).prod * g z := funext hprod
    have hP_ld : ∀ (l : List ℂ), (∀ ρ ∈ l, w ≠ ρ) →
        HasDerivAt (fun z : ℂ ↦ (l.map (fun ρ ↦ z - ρ)).prod)
          ((l.map (fun ρ ↦ w - ρ)).prod * (l.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum) w ∧
          (l.map (fun ρ ↦ w - ρ)).prod ≠ 0 := by
      intro l hl
      induction l with
      | nil =>
        simp only [List.map_nil, List.prod_nil, List.sum_nil, mul_zero, ne_eq, one_ne_zero,
          not_false_eq_true, and_true]
        exact hasDerivAt_const w (1 : ℂ)
      | cons ρ l ih =>
        obtain ⟨ih_d, ih_ne⟩ := ih fun r hr ↦ hl r (List.mem_cons_of_mem ρ hr)
        have hwρ : w - ρ ≠ 0 := sub_ne_zero.mpr (hl ρ (List.mem_cons_self))
        have hd1 : HasDerivAt (fun z : ℂ ↦ z - ρ) 1 w := (hasDerivAt_id w).sub_const ρ
        have hmul := hd1.mul ih_d
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        refine ⟨hmul.congr_deriv ?_, mul_ne_zero hwρ ih_ne⟩
        field_simp [hwρ, ih_ne]
    obtain ⟨hPd, hPne⟩ := hP_ld zs hw_ne
    have hfg := hPd.mul (hg_diff w).hasDerivAt
    have hf_deriv : deriv f w =
        ((zs.map (fun ρ ↦ w - ρ)).prod * (zs.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum) * g w +
          (zs.map (fun ρ ↦ w - ρ)).prod * deriv g w := by
      rw [hf_eq]
      exact hfg.deriv
    rw [hf_deriv, hprod w]
    field_simp [hPne, hgw]
  have hzs_int : ∀ ρ ∈ zs, ρ.re ∈ Set.Ioo a b ∧ ρ.im ∈ Set.Ioo c d := by
    intro ρ hρ
    obtain ⟨hK, hf0⟩ := hzs_prop ρ hρ
    exact hZ_int ρ (hZ_all ρ hK hf0)
  have hzs_avoid : ∀ w : ℂ, ¬ (w.re ∈ Set.Ioo a b ∧ w.im ∈ Set.Ioo c d) →
      ∀ ρ ∈ zs, w ≠ ρ := by
    intro w hw ρ hρ heq
    subst heq
    exact hw (hzs_int w hρ)
  have hbot_avoid : ∀ x ∈ Set.uIcc a b, ∀ ρ ∈ zs, (x : ℂ) + (c : ℂ) * I ≠ ρ := by
    intro x _ ρ hρ
    exact hzs_avoid _ (fun h ↦ by simp at h) ρ hρ
  have htop_avoid : ∀ x ∈ Set.uIcc a b, ∀ ρ ∈ zs, (x : ℂ) + (d : ℂ) * I ≠ ρ := by
    intro x _ ρ hρ
    exact hzs_avoid _ (fun h ↦ by simp at h) ρ hρ
  have hright_avoid : ∀ y ∈ Set.uIcc c d, ∀ ρ ∈ zs, (b : ℂ) + (y : ℂ) * I ≠ ρ := by
    intro y _ ρ hρ
    exact hzs_avoid _ (fun h ↦ by simp at h) ρ hρ
  have hleft_avoid : ∀ y ∈ Set.uIcc c d, ∀ ρ ∈ zs, (a : ℂ) + (y : ℂ) * I ≠ ρ := by
    intro y _ ρ hρ
    exact hzs_avoid _ (fun h ↦ by simp at h) ρ hρ
  have hbot_ne_g : ∀ x ∈ Set.uIcc a b, g ((x : ℂ) + (c : ℂ) * I) ≠ 0 := by
    intro x hx
    apply hg_ne
    rw [Set.uIcc_of_le hab.le] at hx
    exact ⟨by simpa using hx, by simpa using hcd.le⟩
  have htop_ne_g : ∀ x ∈ Set.uIcc a b, g ((x : ℂ) + (d : ℂ) * I) ≠ 0 := by
    intro x hx
    apply hg_ne
    rw [Set.uIcc_of_le hab.le] at hx
    exact ⟨by simpa using hx, by simpa using hcd.le⟩
  have hright_ne_g : ∀ y ∈ Set.uIcc c d, g ((b : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy
    apply hg_ne
    rw [Set.uIcc_of_le hcd.le] at hy
    exact ⟨by simpa using hab.le, by simpa using hy⟩
  have hleft_ne_g : ∀ y ∈ Set.uIcc c d, g ((a : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy
    apply hg_ne
    rw [Set.uIcc_of_le hcd.le] at hy
    exact ⟨by simpa using hab.le, by simpa using hy⟩
  have hsum_rect : ∀ (l : List ℂ), (∀ ρ ∈ l, ρ.re ∈ Set.Ioo a b ∧ ρ.im ∈ Set.Ioo c d) →
      (∫ x in a..b, (l.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ))).sum) -
        (∫ x in a..b, (l.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ))).sum) +
        I * (∫ y in c..d, (l.map (fun ρ ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ))).sum) -
        I * (∫ y in c..d, (l.map (fun ρ ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))).sum) =
        2 * Real.pi * I * (l.length : ℂ) := by
    intro l hl
    induction l with
    | nil => simp
    | cons ρ l ih =>
      have hρ := hl ρ (List.mem_cons_self)
      have ihl := ih fun r hr ↦ hl r (List.mem_cons_of_mem ρ hr)
      have hc_term : ContinuousOn (fun x : ℝ ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ))
          (Set.uIcc a b) :=
        continuousOn_one_div_horiz c ρ (sub_ne_zero.mpr hρ.2.1.ne) (Set.uIcc a b)
      have hd_term : ContinuousOn (fun x : ℝ ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ))
          (Set.uIcc a b) :=
        continuousOn_one_div_horiz d ρ (sub_ne_zero.mpr hρ.2.2.ne') (Set.uIcc a b)
      have hb_term : ContinuousOn (fun y : ℝ ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ))
          (Set.uIcc c d) :=
        continuousOn_one_div_vert b ρ (sub_ne_zero.mpr hρ.1.2.ne') (Set.uIcc c d)
      have ha_term : ContinuousOn (fun y : ℝ ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))
          (Set.uIcc c d) :=
        continuousOn_one_div_vert a ρ (sub_ne_zero.mpr hρ.1.1.ne) (Set.uIcc c d)
      have hlist_cont : ∀ (s : Set ℝ) (m : List ℂ) (g1 : ℂ → ℝ → ℂ),
          (∀ r ∈ m, ContinuousOn (fun t : ℝ ↦ (1 : ℂ) / (g1 r t)) s) →
          ContinuousOn (fun t : ℝ ↦ (m.map (fun r ↦ (1 : ℂ) / (g1 r t))).sum) s := by
        intro s m g1 hg1
        induction m with
        | nil => simp; exact continuousOn_const
        | cons r' l' ihl' =>
          simp only [List.map_cons, List.sum_cons]
          exact (hg1 r' List.mem_cons_self).add
            (ihl' fun u hu ↦ hg1 u (List.mem_cons_of_mem r' hu))
      have hcl_bot : ContinuousOn (fun x : ℝ ↦
          (l.map (fun r ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - r))).sum) (Set.uIcc a b) :=
        hlist_cont (Set.uIcc a b) l (fun r x ↦ (x : ℂ) + (c : ℂ) * I - r) fun r hr ↦
          continuousOn_one_div_horiz c r (sub_ne_zero.mpr (hl r (List.mem_cons_of_mem ρ hr)).2.1.ne)
            (Set.uIcc a b)
      have hcl_top : ContinuousOn (fun x : ℝ ↦
          (l.map (fun r ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - r))).sum) (Set.uIcc a b) :=
        hlist_cont (Set.uIcc a b) l (fun r x ↦ (x : ℂ) + (d : ℂ) * I - r) fun r hr ↦
          continuousOn_one_div_horiz d r (sub_ne_zero.mpr (hl r (List.mem_cons_of_mem ρ hr)).2.2.ne')
            (Set.uIcc a b)
      have hcl_right : ContinuousOn (fun y : ℝ ↦
          (l.map (fun r ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - r))).sum) (Set.uIcc c d) :=
        hlist_cont (Set.uIcc c d) l (fun r y ↦ (b : ℂ) + (y : ℂ) * I - r) fun r hr ↦
          continuousOn_one_div_vert b r (sub_ne_zero.mpr (hl r (List.mem_cons_of_mem ρ hr)).1.2.ne')
            (Set.uIcc c d)
      have hcl_left : ContinuousOn (fun y : ℝ ↦
          (l.map (fun r ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - r))).sum) (Set.uIcc c d) :=
        hlist_cont (Set.uIcc c d) l (fun r y ↦ (a : ℂ) + (y : ℂ) * I - r) fun r hr ↦
          continuousOn_one_div_vert a r (sub_ne_zero.mpr (hl r (List.mem_cons_of_mem ρ hr)).1.1.ne)
            (Set.uIcc c d)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [intervalIntegral.integral_add hc_term.intervalIntegrable hcl_bot.intervalIntegrable,
        intervalIntegral.integral_add hd_term.intervalIntegrable hcl_top.intervalIntegrable,
        intervalIntegral.integral_add hb_term.intervalIntegrable hcl_right.intervalIntegrable,
        intervalIntegral.integral_add ha_term.intervalIntegrable hcl_left.intervalIntegrable]
      have hρ_rect := integral_boundary_rect_inv_sub hρ.1.1 hρ.1.2 hρ.2.1 hρ.2.2
      calc
        _ = ((∫ x in a..b, (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ)) -
              (∫ x in a..b, (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ)) +
              I * (∫ y in c..d, (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ)) -
              I * (∫ y in c..d, (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))) +
            ((∫ x in a..b, (l.map (fun r ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - r))).sum) -
              (∫ x in a..b, (l.map (fun r ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - r))).sum) +
              I * (∫ y in c..d, (l.map (fun r ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - r))).sum) -
              I * (∫ y in c..d, (l.map (fun r ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - r))).sum)) := by
          ring
        _ = 2 * Real.pi * I + 2 * Real.pi * I * (l.length : ℂ) := by rw [hρ_rect, ihl]
        _ = 2 * Real.pi * I * ((l.length : ℂ) + 1) := by ring
  have hcont_sum_edge : ∀ (p : ℝ → ℂ) (t₁ t₂ : ℝ), ContinuousOn p (Set.uIcc t₁ t₂) →
      (∀ t ∈ Set.uIcc t₁ t₂, ∀ ρ ∈ zs, p t ≠ ρ) →
      IntervalIntegrable (fun t : ℝ ↦ (zs.map (fun ρ ↦ (1 : ℂ) / (p t - ρ))).sum) volume t₁ t₂ :=
    fun p t₁ t₂ hp hp_ne ↦ (continuousOn_list_sum_inv_sub (Set.uIcc t₁ t₂) zs p hp hp_ne).intervalIntegrable
  have hg_cont_edge : ∀ (p : ℝ → ℂ) (t₁ t₂ : ℝ), ContinuousOn p (Set.uIcc t₁ t₂) →
      (∀ t ∈ Set.uIcc t₁ t₂, g (p t) ≠ 0) →
      IntervalIntegrable (fun t : ℝ ↦ deriv g (p t) / g (p t)) volume t₁ t₂ := by
    intro p t₁ t₂ hp hne
    refine ContinuousOn.intervalIntegrable ?_
    have hdg_cont : Continuous (deriv g) :=
      continuous_iff_continuousAt.mpr fun w ↦ ((hg_an w (Set.mem_univ w)).deriv).continuousAt
    exact (hdg_cont.comp_continuousOn hp).div (hg_diff.continuous.comp_continuousOn hp) hne
  have hp_bot : ContinuousOn (fun x : ℝ ↦ (x : ℂ) + (c : ℂ) * I) (Set.uIcc a b) :=
    Complex.continuous_ofReal.continuousOn.add continuousOn_const
  have hp_top : ContinuousOn (fun x : ℝ ↦ (x : ℂ) + (d : ℂ) * I) (Set.uIcc a b) :=
    Complex.continuous_ofReal.continuousOn.add continuousOn_const
  have hp_right : ContinuousOn (fun y : ℝ ↦ (b : ℂ) + (y : ℂ) * I) (Set.uIcc c d) :=
    continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
  have hp_left : ContinuousOn (fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * I) (Set.uIcc c d) :=
    continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
  have hbot_eq : ∫ x in a..b, deriv f ((x : ℂ) + (c : ℂ) * I) / f ((x : ℂ) + (c : ℂ) * I) =
      (∫ x in a..b, (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ))).sum) +
        (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * I) / g ((x : ℂ) + (c : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add
      (hcont_sum_edge _ a b hp_bot hbot_avoid) (hg_cont_edge _ a b hp_bot hbot_ne_g)]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    exact hld_split _ (hbot_avoid x hx) (hbot_ne_g x hx)
  have htop_eq : ∫ x in a..b, deriv f ((x : ℂ) + (d : ℂ) * I) / f ((x : ℂ) + (d : ℂ) * I) =
      (∫ x in a..b, (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ))).sum) +
        (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * I) / g ((x : ℂ) + (d : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add
      (hcont_sum_edge _ a b hp_top htop_avoid) (hg_cont_edge _ a b hp_top htop_ne_g)]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    exact hld_split _ (htop_avoid x hx) (htop_ne_g x hx)
  have hright_eq : ∫ y in c..d, deriv f ((b : ℂ) + (y : ℂ) * I) / f ((b : ℂ) + (y : ℂ) * I) =
      (∫ y in c..d, (zs.map (fun ρ ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ))).sum) +
        (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * I) / g ((b : ℂ) + (y : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add
      (hcont_sum_edge _ c d hp_right hright_avoid) (hg_cont_edge _ c d hp_right hright_ne_g)]
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    exact hld_split _ (hright_avoid y hy) (hright_ne_g y hy)
  have hleft_eq : ∫ y in c..d, deriv f ((a : ℂ) + (y : ℂ) * I) / f ((a : ℂ) + (y : ℂ) * I) =
      (∫ y in c..d, (zs.map (fun ρ ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))).sum) +
        (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * I) / g ((a : ℂ) + (y : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add
      (hcont_sum_edge _ c d hp_left hleft_avoid) (hg_cont_edge _ c d hp_left hleft_ne_g)]
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    exact hld_split _ (hleft_avoid y hy) (hleft_ne_g y hy)
  rw [hbot_eq, htop_eq, hright_eq, hleft_eq]
  have hcombine :
      ((∫ x in a..b, (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ))).sum) +
          (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * I) / g ((x : ℂ) + (c : ℂ) * I))) -
        ((∫ x in a..b, (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ))).sum) +
          (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * I) / g ((x : ℂ) + (d : ℂ) * I))) +
        I * ((∫ y in c..d, (zs.map (fun ρ ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ))).sum) +
          (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * I) / g ((b : ℂ) + (y : ℂ) * I))) -
        I * ((∫ y in c..d, (zs.map (fun ρ ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))).sum) +
          (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * I) / g ((a : ℂ) + (y : ℂ) * I))) =
      ((∫ x in a..b, (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (c : ℂ) * I - ρ))).sum) -
        (∫ x in a..b, (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (d : ℂ) * I - ρ))).sum) +
        I * (∫ y in c..d, (zs.map (fun ρ ↦ (1 : ℂ) / ((b : ℂ) + (y : ℂ) * I - ρ))).sum) -
        I * (∫ y in c..d, (zs.map (fun ρ ↦ (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I - ρ))).sum)) +
      ((∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * I) / g ((x : ℂ) + (c : ℂ) * I)) -
        (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * I) / g ((x : ℂ) + (d : ℂ) * I)) +
        I * (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * I) / g ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * I) / g ((a : ℂ) + (y : ℂ) * I))) := by
    ring
  rw [hcombine, hsum_rect zs hzs_int, hrect_g, add_zero, hzs_len, Nat.cast_sum]

/-! ### Argument Function `S(T)`, Backlund's `O(log T)` Bound, and Riemann–von Mangoldt -/

/-- Predicate asserting that `T` is the imaginary part of a non-trivial zero of `riemannZeta`. -/
def IsZeroOrdinate (T : ℝ) : Prop :=
  ∃ ρ ∈ CriticalStripZeros, ρ.im = T

/-- Normalized horizontal variation of `arg ζ` from `2 + t * I` to `1/2 + t * I`, divided by `π`,
plus `(1/π) arg ζ(2 + t * I)` for heights `t` avoiding zero ordinates. -/
noncomputable def argumentSApprox (t : ℝ) : ℝ :=
  (1 / Real.pi) * ((riemannZeta ((2 : ℂ) + (t : ℂ) * I)).arg -
    ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
      (deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) / riemannZeta ((x : ℂ) + (t : ℂ) * I)).im)

/-- The Riemann–von Mangoldt argument term `S(T) = (1 / π) arg ζ(1/2 + iT)` defined across all
`T : ℝ` as the right-hand limit `lim_{t → T⁺} argumentSApprox t`. -/
noncomputable def argumentS (T : ℝ) : ℝ :=
  Filter.limUnder (𝓝[>] T) argumentSApprox

private lemma riemannZeta_two_add_mul_I_re_ge (y : ℝ) :
    (1 / 4 : ℝ) ≤ (riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
  let s : ℂ := (2 : ℂ) + (y : ℂ) * I
  have hs : 1 < s.re := by simp [s]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hsumm_c : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s := by
    refine (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs) |>.congr
      fun n ↦ ?_
    simp [Nat.cast_add, Nat.cast_one]
  rw [hsumm_c.tsum_eq_zero_add]
  have h0 : 1 / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by simp
  rw [h0]
  have htail_bd : ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤ 3 / 4 := by
    have hsumm_tail : Summable fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s :=
      (summable_nat_add_iff 1).mpr hsumm_c
    have hterm_le : ∀ n : ℕ, ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤
        1 / ((n : ℝ) + 2) ^ 2 := by
      intro n
      have hn_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hcast : (((n + 1 : ℕ) : ℂ) + 1) = (((n : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
      have hs_re : s.re = ((2 : ℕ) : ℝ) := by simp [s]
      rw [one_div, norm_inv, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
        hs_re, Real.rpow_natCast, one_div]
    have htel : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 3)) (1 / 2) := by
      have hpart : ∀ N : ℕ,
          ∑ n ∈ Finset.range N, ((1 : ℝ) / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 3)) =
            1 / 2 - 1 / ((N : ℝ) + 2) := by
        intro N
        induction N with
        | zero => norm_num
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast; ring
      rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by
        have h1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have h2 : (n : ℝ) + 2 ≤ (n : ℝ) + 3 := by linarith
        exact sub_nonneg.mpr (one_div_le_one_div_of_le h1 h2))]
      simp_rw [hpart]
      have h0' : Tendsto (fun N : ℕ ↦ (1 : ℝ) / ((N : ℝ) + 2)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun N ↦ by
          dsimp only [Function.comp_apply]; push_cast; ring
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h0'
    have hmaj : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 ≤
        if n = 0 then (1 / 4 : ℝ) else 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        simp only [hn, ↓reduceIte]
        have hmul : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
        calc
          1 / ((n : ℝ) + 2) ^ 2 ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
            one_div_le_one_div_of_le (by positivity) hmul
          _ = 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
            field_simp [h1.ne', h2.ne']; ring
    have hmaj_sum : HasSum (fun n : ℕ ↦
        if n = 0 then (1 / 4 : ℝ) else 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) (3 / 4) := by
      rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by
        split_ifs
        · norm_num
        · exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith)))]
      have hpart_maj : ∀ N : ℕ,
          ∑ n ∈ Finset.range (N + 1),
            (if n = 0 then (1 / 4 : ℝ) else 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) =
            3 / 4 - 1 / ((N : ℝ) + 2) := by
        intro N
        induction N with
        | zero => norm_num
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [Nat.succ_ne_zero, ↓reduceIte]
          push_cast; ring
      have h0' : Tendsto (fun N : ℕ ↦ (1 : ℝ) / ((N : ℝ) + 2)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun N ↦ by
          dsimp only [Function.comp_apply]; push_cast; ring
      refine (tendsto_add_atTop_iff_nat 1).mp ?_
      simp_rw [hpart_maj]
      simpa using (tendsto_const_nhds (x := (3 / 4 : ℝ))).sub h0'
    have hsumm_n : Summable fun n : ℕ ↦ ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ :=
      hsumm_tail.norm
    calc
      ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖
          ≤ ∑' n : ℕ, ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hsumm_n
      _ ≤ ∑' n : ℕ, (if n = 0 then (1 / 4 : ℝ) else 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) :=
        hsumm_n.tsum_le_tsum (fun n ↦ (hterm_le n).trans (hmaj n)) hmaj_sum.summable
      _ = 3 / 4 := hmaj_sum.tsum_eq
  have h1_re : (1 + ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s).re =
      1 + (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s).re := by simp
  have hre_ge : -(3 / 4 : ℝ) ≤ (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s).re := by
    have h := Complex.abs_re_le_norm (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s)
    linarith [(neg_le_abs _).trans h]
  rw [h1_re]
  linarith

private lemma xi_logDeriv_one_sub_star (z : ℂ) (hz : xi z ≠ 0) :
    deriv xi (1 - star z) / xi (1 - star z) = -star (deriv xi z / xi z) := by
  have hstar_ne : xi (star z) ≠ 0 := by
    change xi (starRingEnd ℂ z) ≠ 0
    rw [xi_conj]
    exact fun h ↦ hz (by have := congrArg (starRingEnd ℂ) h; simpa using this)
  have h1 : deriv xi (star z) / xi (star z) = star (deriv xi z / xi z) := by
    have hd_at : HasDerivAt (fun w : ℂ ↦ star (xi (star w))) (star (deriv xi z)) (star z) := by
      have hsl : Tendsto (slope (fun w : ℂ ↦ star (xi (star w))) (star z)) (𝓝[≠] (star z))
          (𝓝 (star (deriv xi z))) := by
        have hsl_xi : Tendsto (slope xi z) (𝓝[≠] z) (𝓝 (deriv xi z)) :=
          (differentiable_xi z).hasDerivAt.tendsto_slope
        have hstar_tend : Tendsto (star : ℂ → ℂ) (𝓝[≠] (star z)) (𝓝[≠] z) := by
          rw [tendsto_nhdsWithin_iff]
          have hc : Tendsto (star : ℂ → ℂ) (𝓝 (star z)) (𝓝 z) := by
            simpa only [star_star] using continuous_star.tendsto (star z)
          refine ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
          filter_upwards [self_mem_nhdsWithin] with w hw
          intro heq
          apply hw
          calc
            w = star (star w) := (star_star w).symm
            _ = star z := by rw [heq]
        have hcont_star : Tendsto (fun w : ℂ ↦ star (slope xi z (star w))) (𝓝[≠] (star z))
            (𝓝 (star (deriv xi z))) :=
          continuous_star.continuousAt.tendsto.comp (hsl_xi.comp hstar_tend)
        refine hcont_star.congr fun w ↦ ?_
        simp only [slope_def_module, smul_eq_mul, star_mul, star_sub, star_inv₀, star_star]
        ring
      exact hasDerivAt_iff_tendsto_slope.mpr hsl
    have hfun : (fun w : ℂ ↦ star (xi (star w))) = xi := by
      ext w
      change starRingEnd ℂ (xi (starRingEnd ℂ w)) = xi w
      rw [xi_conj, starRingEnd_self_apply]
    rw [hfun] at hd_at
    have hdx : deriv xi (star z) = starRingEnd ℂ (deriv xi z) := hd_at.deriv
    have hxi_s : xi (star z) = starRingEnd ℂ (xi z) := xi_conj z
    change deriv xi (star z) / xi (star z) = starRingEnd ℂ (deriv xi z / xi z)
    rw [hdx, hxi_s, map_div₀]
  have h2 : deriv xi (1 - star z) / xi (1 - star z) = -(deriv xi (star z) / xi (star z)) := by
    have hcomp : HasDerivAt (fun w : ℂ ↦ xi (1 - w)) (-deriv xi (1 - star z)) (star z) := by
      have hlin : HasDerivAt (fun w : ℂ ↦ 1 - w) (0 - 1 : ℂ) (star z) :=
        (hasDerivAt_const (star z) (1 : ℂ)).sub (hasDerivAt_id' (star z))
      have hd := (differentiable_xi (1 - star z)).hasDerivAt.comp (star z) hlin
      exact hd.congr_deriv (by ring)
    have hfun : (fun w : ℂ ↦ xi (1 - w)) = xi := funext xi_one_sub
    rw [hfun] at hcomp
    rw [hcomp.deriv, xi_one_sub (star z)]
    ring
  rw [h2, h1]

private lemma xi_logDeriv_ofReal_im (x : ℝ) :
    (deriv xi (x : ℂ) / xi (x : ℂ)).im = 0 := by
  have hx := xi_ne_zero_ofReal x
  have hd_at : HasDerivAt (fun w : ℂ ↦ star (xi (star w))) (star (deriv xi (x : ℂ))) (x : ℂ) := by
    have hsl : Tendsto (slope (fun w : ℂ ↦ star (xi (star w))) (x : ℂ)) (𝓝[≠] (x : ℂ))
        (𝓝 (star (deriv xi (x : ℂ)))) := by
      have hsl_xi : Tendsto (slope xi (x : ℂ)) (𝓝[≠] (x : ℂ)) (𝓝 (deriv xi (x : ℂ))) :=
        (differentiable_xi (x : ℂ)).hasDerivAt.tendsto_slope
      have hstar_tend : Tendsto (star : ℂ → ℂ) (𝓝[≠] (x : ℂ)) (𝓝[≠] (x : ℂ)) := by
        rw [tendsto_nhdsWithin_iff]
        have hstarx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
        have hc : Tendsto (star : ℂ → ℂ) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) :=
          hstarx ▸ continuous_star.tendsto (x : ℂ)
        refine ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with w hw
        intro heq
        apply hw
        calc
          w = star (star w) := (star_star w).symm
          _ = star (x : ℂ) := by rw [heq]
          _ = (x : ℂ) := Complex.conj_ofReal x
      have hcont_star : Tendsto (fun w : ℂ ↦ star (slope xi (x : ℂ) (star w))) (𝓝[≠] (x : ℂ))
          (𝓝 (star (deriv xi (x : ℂ)))) :=
        continuous_star.continuousAt.tendsto.comp (hsl_xi.comp hstar_tend)
      refine hcont_star.congr fun w ↦ ?_
      have hstarx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
      simp only [slope_def_module, smul_eq_mul, star_mul, star_sub, star_inv₀, star_star, hstarx]
      ring
    exact hasDerivAt_iff_tendsto_slope.mpr hsl
  have hfun : (fun w : ℂ ↦ star (xi (star w))) = xi := by
    ext w
    change starRingEnd ℂ (xi (starRingEnd ℂ w)) = xi w
    rw [xi_conj, starRingEnd_self_apply]
  rw [hfun] at hd_at
  have hstar_eq : star (deriv xi (x : ℂ) / xi (x : ℂ)) = deriv xi (x : ℂ) / xi (x : ℂ) := by
    rw [star_div₀, ← hd_at.deriv]
    have hxi_star : star (xi (x : ℂ)) = xi (x : ℂ) := by
      change starRingEnd ℂ (xi (x : ℂ)) = xi (x : ℂ)
      rw [← xi_conj]
      simp
    rw [hxi_star]
  have him := congrArg Complex.im hstar_eq
  change -(deriv xi (x : ℂ) / xi (x : ℂ)).im = (deriv xi (x : ℂ) / xi (x : ℂ)).im at him
  linarith

private lemma xi_ne_zero_on_top_edge {T : ℝ} (_hT : 0 < T) (hno : ¬ IsZeroOrdinate T)
    (x : ℝ) : xi ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  intro h0
  have hcrit := (xi_eq_zero_iff).mp h0
  apply hno
  refine ⟨(x : ℂ) + (T : ℂ) * I, hcrit, ?_⟩
  simp

private lemma riemannZeta_ne_zero_on_right_strip {T : ℝ} (_hT : 0 < T) (hno : ¬ IsZeroOrdinate T)
    {x : ℝ} (hx0 : 0 < x) : riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  rcases le_or_gt 1 x with hx1 | hx1
  · exact riemannZeta_ne_zero_of_one_le_re (by simp [hx1])
  · intro h0
    apply hno
    exact ⟨(x : ℂ) + (T : ℂ) * I, ⟨h0, by simp [hx0], by simp [hx1]⟩, by simp⟩

/-- **Halved contour identity** for `zeroCountUpTo T`: for any `T > 0` avoiding zero ordinates,
`zeroCountUpTo T = (1 / π) * (∫_0^T Re (ξ'/ξ)(2 + iy) dy - ∫_{1/2}^2 Im (ξ'/ξ)(x + iT) dx)`. -/
theorem zeroCountUpTo_eq_contour_halved {T : ℝ} (hT : 0 < T) (hno : ¬ IsZeroOrdinate T) :
    (zeroCountUpTo T : ℝ) =
      (1 / Real.pi) *
        ((∫ y in (0 : ℝ)..T, (deriv xi ((2 : ℂ) + (y : ℂ) * I) /
            xi ((2 : ℂ) + (y : ℂ) * I)).re) -
          (∫ x in (1 / 2 : ℝ)..(2 : ℝ), (deriv xi ((x : ℂ) + (T : ℂ) * I) /
            xi ((x : ℂ) + (T : ℂ) * I)).im)) := by
  classical
  let Z : Finset ℂ :=
    (criticalStripZeros_strip_finite 0 T).toFinset.filter (fun ρ : ℂ ↦ 0 < ρ.im)
  have hZ_int : ∀ ρ ∈ Z, ρ.re ∈ Set.Ioo (-1 : ℝ) 2 ∧ ρ.im ∈ Set.Ioo 0 T := by
    intro ρ hρ
    have hm := Finset.mem_filter.mp hρ
    have hs := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp hm.1
    have hneT : ρ.im ≠ T := fun h ↦ hno ⟨ρ, hs.1, h⟩
    refine ⟨⟨by linarith [hs.1.2.1], by linarith [hs.1.2.2]⟩,
      ⟨hm.2, lt_of_le_of_ne hs.2.2 hneT⟩⟩
  have hZ_all : ∀ w ∈ Set.Icc (-1 : ℝ) 2 ×ℂ Set.Icc 0 T, xi w = 0 → w ∈ Z := by
    intro w hw h0
    have hcrit := (xi_eq_zero_iff).mp h0
    have him0 : 0 < w.im := by
      rcases eq_or_lt_of_le hw.2.1 with him_eq | him_pos
      · exfalso
        have hw_eq : w = (w.re : ℂ) := by apply Complex.ext <;> simp [him_eq.symm]
        rw [hw_eq] at h0
        exact xi_ne_zero_ofReal w.re h0
      · exact him_pos
    exact Finset.mem_filter.mpr
      ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr ⟨hcrit, ⟨hw.2.1, hw.2.2⟩⟩, him0⟩
  have hap := argument_principle_rect_entire differentiable_xi
    (a := -1) (b := 2) (c := 0) (d := T) (by norm_num) hT Z hZ_int hZ_all
  have hap_im := congrArg Complex.im hap
  have hZ_sum_eq : ∑ ρ ∈ Z, analyticOrderNatAt xi ρ = zeroCountUpTo T := by
    rw [zeroCountUpTo_eq_sum T]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hs := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp (Finset.mem_filter.mp hρ).1
    exact (analyticOrderNatAt_riemannZeta_eq_xi hs.1.2.1 hs.1.2.2).symm
  have hrhs_im : (2 * (Real.pi : ℂ) * I * ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ)).im =
      2 * Real.pi * (zeroCountUpTo T : ℝ) := by
    have hnat : (∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ)) = ((zeroCountUpTo T : ℕ) : ℂ) := by
      rw [← hZ_sum_eq]
      push_cast; rfl
    rw [hnat]
    simp only [Complex.mul_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.natCast_im]
    ring
  have hxi_cont : Continuous (deriv xi) :=
    continuous_iff_continuousAt.mpr fun w ↦
      ((differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ).deriv w
        (Set.mem_univ w)).continuousAt
  have hint_bot : IntervalIntegrable
      (fun x : ℝ ↦ deriv xi ((x : ℂ) + (0 : ℂ) * I) / xi ((x : ℂ) + (0 : ℂ) * I))
      volume (-1 : ℝ) 2 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (hxi_cont.comp_continuousOn
      (Complex.continuous_ofReal.continuousOn.add continuousOn_const)).div
      (differentiable_xi.continuous.comp_continuousOn
        (Complex.continuous_ofReal.continuousOn.add continuousOn_const))
      fun x _ ↦ ?_
    simpa using xi_ne_zero_ofReal x
  have hint_top : IntervalIntegrable
      (fun x : ℝ ↦ deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I))
      volume (-1 : ℝ) 2 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (hxi_cont.comp_continuousOn
      (Complex.continuous_ofReal.continuousOn.add continuousOn_const)).div
      (differentiable_xi.continuous.comp_continuousOn
        (Complex.continuous_ofReal.continuousOn.add continuousOn_const))
      fun x _ ↦ ?_
    exact xi_ne_zero_on_top_edge hT hno x
  have hint_right : IntervalIntegrable
      (fun y : ℝ ↦ deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I))
      volume 0 T := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (hxi_cont.comp_continuousOn
      (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))).div
      (differentiable_xi.continuous.comp_continuousOn
        (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)))
      fun y _ ↦ ?_
    exact xi_ne_zero_of_one_le_re (by simp)
  have hint_left : IntervalIntegrable
      (fun y : ℝ ↦ deriv xi ((-1 : ℂ) + (y : ℂ) * I) / xi ((-1 : ℂ) + (y : ℂ) * I))
      volume 0 T := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (hxi_cont.comp_continuousOn
      (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))).div
      (differentiable_xi.continuous.comp_continuousOn
        (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)))
      fun y _ ↦ ?_
    exact xi_ne_zero_of_re_nonpos (by simp)
  have hbot_zero : (∫ x in (-1 : ℝ)..2,
      deriv xi ((x : ℂ) + (0 : ℂ) * I) / xi ((x : ℂ) + (0 : ℂ) * I)).im = 0 := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hint_bot]
    have hcongr_zero : (∫ x in (-1 : ℝ)..2,
        Complex.imCLM (deriv xi ((x : ℂ) + (0 : ℂ) * I) / xi ((x : ℂ) + (0 : ℂ) * I))) =
        ∫ _ in (-1 : ℝ)..2, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      simpa [Complex.imCLM_apply] using xi_logDeriv_ofReal_im x
    rw [hcongr_zero]
    simp
  have htop_symm : (∫ x in (-1 : ℝ)..2,
      deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im =
      2 * ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hint_top]
    simp only [Complex.imCLM_apply]
    have hint_top_im : IntervalIntegrable
        (fun x : ℝ ↦ (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im)
        volume (-1 : ℝ) 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      exact Complex.continuous_im.comp_continuousOn
        ((hxi_cont.comp_continuousOn
            (Complex.continuous_ofReal.add continuous_const).continuousOn).div
          (differentiable_xi.continuous.comp_continuousOn
            (Complex.continuous_ofReal.add continuous_const).continuousOn)
          fun x _ ↦ xi_ne_zero_on_top_edge hT hno x)
    have hint_left_half : IntervalIntegrable
        (fun x : ℝ ↦ (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im)
        volume (-1 : ℝ) (1 / 2 : ℝ) :=
      hint_top_im.mono_set (by
        rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
        exact Set.Icc_subset_Icc_right (by norm_num))
    have hint_right_half : IntervalIntegrable
        (fun x : ℝ ↦ (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im)
        volume (1 / 2 : ℝ) 2 :=
      hint_top_im.mono_set (by
        rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
        exact Set.Icc_subset_Icc_left (by norm_num))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_left_half hint_right_half]
    have hsub_eq : ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im =
        ∫ u in (1 / 2 : ℝ)..(2 : ℝ),
          (deriv xi ((u : ℂ) + (T : ℂ) * I) / xi ((u : ℂ) + (T : ℂ) * I)).im := by
      have hcomp := intervalIntegral.integral_comp_sub_left
        (fun u : ℝ ↦ (deriv xi ((u : ℂ) + (T : ℂ) * I) / xi ((u : ℂ) + (T : ℂ) * I)).im) 1
        (a := (1 / 2 : ℝ)) (b := (2 : ℝ))
      norm_num at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      have h1 : (1 - (u : ℂ) + (T : ℂ) * I) = 1 - star ((u : ℂ) + (T : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [h1, xi_logDeriv_one_sub_star _ (xi_ne_zero_on_top_edge hT hno u)]
      simp only [Complex.neg_im]
      change -(starRingEnd ℂ (deriv xi ((u : ℂ) + (T : ℂ) * I) /
        xi ((u : ℂ) + (T : ℂ) * I))).im = _
      rw [Complex.conj_im]
      ring
    rw [hsub_eq]
    ring
  have hright_re : (I * ∫ y in (0 : ℝ)..T,
      deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).im =
      ∫ y in (0 : ℝ)..T,
        (deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re := by
    rw [Complex.I_mul_im, ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint_right]
    rfl
  have hleft_re : (I * ∫ y in (0 : ℝ)..T,
      deriv xi ((-1 : ℂ) + (y : ℂ) * I) / xi ((-1 : ℂ) + (y : ℂ) * I)).im =
      -(∫ y in (0 : ℝ)..T,
        (deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re) := by
    rw [Complex.I_mul_im, ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint_left]
    simp only [Complex.reCLM_apply]
    have hcongr : ∫ y in (0 : ℝ)..T,
        (deriv xi ((-1 : ℂ) + (y : ℂ) * I) / xi ((-1 : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T,
          -(deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re := by
      refine intervalIntegral.integral_congr fun y _ ↦ ?_
      have h1 : ((-1 : ℂ) + (y : ℂ) * I) = 1 - star ((2 : ℂ) + (y : ℂ) * I) := by
        apply Complex.ext <;> simp; norm_num
      rw [h1, xi_logDeriv_one_sub_star _ (xi_ne_zero_of_one_le_re (by simp))]
      simp only [Complex.neg_re]
      change -(starRingEnd ℂ (deriv xi ((2 : ℂ) + (y : ℂ) * I) /
        xi ((2 : ℂ) + (y : ℂ) * I))).re = _
      rw [Complex.conj_re]
    rw [hcongr, intervalIntegral.integral_neg]
  have hlhs_im : ((∫ x in (-1 : ℝ)..2,
        deriv xi ((x : ℂ) + (0 : ℂ) * I) / xi ((x : ℂ) + (0 : ℂ) * I)) -
      (∫ x in (-1 : ℝ)..2,
        deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)) +
      I * (∫ y in (0 : ℝ)..T,
        deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)) -
      I * (∫ y in (0 : ℝ)..T,
        deriv xi ((-1 : ℂ) + (y : ℂ) * I) / xi ((-1 : ℂ) + (y : ℂ) * I))).im =
      2 * ((∫ y in (0 : ℝ)..T,
          (deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re) -
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ),
          (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im)) := by
    simp only [Complex.sub_im, Complex.add_im]
    rw [hbot_zero, htop_symm, hright_re, hleft_re]
    ring
  simp only [Complex.ofReal_zero, Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one]
    at hap_im
  rw [hlhs_im, hrhs_im] at hap_im
  have h_eq : (zeroCountUpTo T : ℝ) * Real.pi =
      (∫ y in (0 : ℝ)..T,
          (deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re) -
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ),
          (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im) := by
    linarith [hap_im]
  rw [← h_eq]
  field_simp [Real.pi_pos.ne']

private lemma xi_logDeriv_eq_parts {s : ℂ} (hs_re : 0 < s.re) (hs1 : s ≠ 1)
    (hs_zeta : riemannZeta s ≠ 0) :
    deriv xi s / xi s =
      1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma (s / 2 + 1) +
        deriv riemannZeta s / riemannZeta s := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs_re
  have hs_ne1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hπ_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs_half_ne : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      Complex.neg_re, Complex.natCast_re, mul_zero] at hre
    norm_num [Complex.normSq] at hre
    have hm_nonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hG_ne : Complex.Gamma (s / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero hs_half_ne
  have hev_eq : xi =ᶠ[𝓝 s] fun z : ℂ ↦
      (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1) * riemannZeta z := by
    let r : ℝ := min (s.re / 2) (‖s - 1‖ / 2)
    have hr_pos : 0 < r := lt_min (half_pos hs_re) (half_pos (norm_pos_iff.mpr hs_ne1))
    filter_upwards [Metric.ball_mem_nhds s hr_pos] with z hz_ball
    have hz_dist : ‖z - s‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
    have hz_re : 0 < z.re := by
      have h1 : |z.re - s.re| ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
      have h2 := hz_dist.trans_le (min_le_left _ _)
      linarith [(abs_le.mp (h1.trans h2.le)).1]
    have hz1 : z ≠ 1 := by
      intro h; subst h
      have h2 := hz_dist.trans_le (min_le_right _ _)
      rw [norm_sub_rev] at h2
      linarith [norm_pos_iff.mpr hs_ne1]
    have hz0 : z / 2 ≠ 0 := div_ne_zero (fun h ↦ by simp [h] at hz_re) two_ne_zero
    rw [xi_eq_formula_of_re_pos hz_re hz1, Complex.Gamma_add_one (z / 2) hz0]
    ring
  have hd1 : HasDerivAt (fun z : ℂ ↦ z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hlogπ : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hd2 : HasDerivAt (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ))) s := by
    have hexp : HasDerivAt (fun z : ℂ ↦ -z / 2) (-(1 / 2 : ℂ)) s := by
      have h := ((hasDerivAt_id s).neg).div_const (2 : ℂ)
      exact h.congr_deriv (by ring)
    have hc := HasDerivAt.const_cpow hexp (Or.inl hπ_ne)
    refine hc.congr_deriv ?_
    rw [hlogπ]
    ring
  have hd3 : HasDerivAt (fun z : ℂ ↦ Complex.Gamma (z / 2 + 1))
      (deriv Complex.Gamma (s / 2 + 1) * (1 / 2 : ℂ)) s := by
    have hG_diff : DifferentiableAt ℂ Complex.Gamma (s / 2 + 1) :=
      Complex.differentiableAt_Gamma _ hs_half_ne
    have hlin : HasDerivAt (fun z : ℂ ↦ z / 2 + 1) (1 / 2 : ℂ) s := by
      have h := ((hasDerivAt_id s).div_const (2 : ℂ)).add_const (1 : ℂ)
      exact h.congr_deriv (by ring)
    exact (hG_diff.hasDerivAt).comp s hlin
  have hd4 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hd_all : HasDerivAt (fun z : ℂ ↦
      (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1) * riemannZeta z)
      (((1 * (Real.pi : ℂ) ^ (-s / 2) + (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) *
          (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)))) *
          Complex.Gamma (s / 2 + 1) +
        ((s - 1) * (Real.pi : ℂ) ^ (-s / 2)) *
          (deriv Complex.Gamma (s / 2 + 1) * (1 / 2 : ℂ))) * riemannZeta s +
      ((s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)) *
        deriv riemannZeta s) s :=
    (((hd1.mul hd2).mul hd3).mul hd4)
  have hderiv_xi : deriv xi s =
      (1 * (Real.pi : ℂ) ^ (-s / 2) + (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) *
          (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)))) *
        Complex.Gamma (s / 2 + 1) * riemannZeta s +
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * (deriv Complex.Gamma (s / 2 + 1) * (1 / 2 : ℂ)) *
        riemannZeta s +
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) * deriv riemannZeta s := by
    rw [hev_eq.deriv_eq, hd_all.deriv]
    ring
  have hxi_eq_prod : xi s =
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) * riemannZeta s :=
    hev_eq.eq_of_nhds
  have hπ_pow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ_ne)
  rw [hderiv_xi, hxi_eq_prod, AnalyticNumberTheory.AnalyticTools.Gamma.digamma_def]
  set G := Complex.Gamma (s / 2 + 1)
  set G' := deriv Complex.Gamma (s / 2 + 1)
  have hG_ne' : G ≠ 0 := hG_ne
  field_simp [hs_ne1, hπ_pow_ne, hG_ne', hs_zeta]
  ring

private lemma hasDerivAt_im_log_zeta_two_add_mul_I (y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im)
      (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) / riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re y := by
  have hslit : riemannZeta ((2 : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := by
    left; linarith [riemannZeta_two_add_mul_I_re_ge y]
  have hne1 : ((2 : ℂ) + (y : ℂ) * I) ≠ 1 := fun h ↦ by
    have := congrArg Complex.re h; simp at this
  have hlin : HasDerivAt (fun w : ℂ ↦ (2 : ℂ) + w * I) I (y : ℂ) :=
    (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (2 : ℂ)).congr_deriv (by simp)
  have hz_d : HasDerivAt (fun w : ℂ ↦ riemannZeta ((2 : ℂ) + w * I))
      (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) * I) (y : ℂ) :=
    (differentiableAt_riemannZeta hne1).hasDerivAt.comp (y : ℂ) hlin
  have hlog := hz_d.comp_ofReal.clog_real hslit
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hlog
  refine him.congr_deriv ?_
  rw [Complex.imCLM_apply, mul_div_right_comm, Complex.mul_I_im]

/-- **Exact Riemann–von Mangoldt contour identity** for heights `T > 0` avoiding zero ordinates:
`zeroCountUpTo T = (1 / π) * arg (-1/2 + iT) + (1 / π) * Im stirlingLogGamma (5/4 + iT/2) - (T / (2π)) * log π + argumentSApprox T`. -/
theorem zeroCountUpTo_eq_stirling_add_argumentSApprox {T : ℝ} (hT : 0 < T)
    (hno : ¬ IsZeroOrdinate T) :
    (zeroCountUpTo T : ℝ) =
      (1 / Real.pi) * ((-1 / 2 : ℂ) + (T : ℂ) * I).arg +
        (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi + argumentSApprox T := by
  have hcont_zeta_v : ContinuousOn (fun y : ℝ ↦
      deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) / riemannZeta ((2 : ℂ) + (y : ℂ) * I))
      (Set.uIcc 0 T) := by
    have hz_diff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    have hdz_cont : ContinuousOn (deriv riemannZeta) {w : ℂ | w ≠ 1} :=
      ((hz_diff.analyticOnNhd isOpen_ne).deriv).continuousOn
    have hpath_v : Continuous fun y : ℝ ↦ (2 : ℂ) + (y : ℂ) * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    refine ContinuousOn.div
      (hdz_cont.comp hpath_v.continuousOn fun y _ ↦ by
        intro h; have := congrArg Complex.re h; simp at this)
      ((hz_diff.continuousOn).comp hpath_v.continuousOn fun y _ ↦ by
        intro h; have := congrArg Complex.re h; simp at this)
      fun y _ ↦ riemannZeta_ne_zero_of_one_lt_re (by simp)
  have hcont_zeta_h : ContinuousOn (fun x : ℝ ↦
      deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) / riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.uIcc (1 / 2 : ℝ) 2) := by
    have hz_diff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    have hdz_cont : ContinuousOn (deriv riemannZeta) {w : ℂ | w ≠ 1} :=
      ((hz_diff.analyticOnNhd isOpen_ne).deriv).continuousOn
    have hpath_h : Continuous fun x : ℝ ↦ (x : ℂ) + (T : ℂ) * I :=
      Complex.continuous_ofReal.add continuous_const
    refine ContinuousOn.div
      (hdz_cont.comp hpath_h.continuousOn fun x _ h ↦ by
        have := congrArg Complex.im h; simp at this; linarith)
      ((hz_diff.continuousOn).comp hpath_h.continuousOn fun x _ h ↦ by
        have := congrArg Complex.im h; simp at this; linarith)
      fun x hx ↦ by
        rw [Set.uIcc_of_le (by norm_num)] at hx
        exact riemannZeta_ne_zero_on_right_strip hT hno (by linarith [hx.1])
  have hcont_dig_v : ContinuousOn (fun y : ℝ ↦
      (1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
        (((2 : ℂ) + (y : ℂ) * I) / 2 + 1))
      (Set.uIcc 0 T) := by
    have hpath_dv : Continuous fun y : ℝ ↦ (((2 : ℂ) + (y : ℂ) * I) / 2 + 1) :=
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).div_const 2).add
        continuous_const
    refine continuousOn_const.mul (continuousOn_digamma_slitPlane.comp hpath_dv.continuousOn
      fun y _ ↦ ?_)
    left
    simp only [Complex.add_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num [Complex.normSq]
  have hcont_dig_h : ContinuousOn (fun x : ℝ ↦
      (1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
        (((x : ℂ) + (T : ℂ) * I) / 2 + 1))
      (Set.uIcc (1 / 2 : ℝ) 2) := by
    have hpath_dh : Continuous fun x : ℝ ↦ (((x : ℂ) + (T : ℂ) * I) / 2 + 1) :=
      ((Complex.continuous_ofReal.add continuous_const).div_const 2).add continuous_const
    refine continuousOn_const.mul (continuousOn_digamma_slitPlane.comp hpath_dh.continuousOn
      fun x hx ↦ ?_)
    rw [Set.uIcc_of_le (by norm_num)] at hx
    left
    have hx_pos : (0 : ℝ) < x := by linarith [hx.1]
    simp only [Complex.add_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num [Complex.normSq]
    linarith
  have hcont_inv_v : ContinuousOn (fun y : ℝ ↦
      (1 : ℂ) / (((2 : ℂ) + (y : ℂ) * I) - 1)) (Set.uIcc 0 T) :=
    continuousOn_one_div_vert 2 1 (by simp; norm_num) (Set.uIcc 0 T)
  have hcont_inv_h : ContinuousOn (fun x : ℝ ↦
      (1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)) (Set.uIcc (1 / 2 : ℝ) 2) :=
    continuousOn_one_div_horiz T 1 (by simp; exact hT.ne') (Set.uIcc (1 / 2 : ℝ) 2)
  have hsplit_v : ∫ y in (0 : ℝ)..T,
      (deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re =
      (∫ y in (0 : ℝ)..T, ((1 : ℂ) / (((2 : ℂ) + (y : ℂ) * I) - 1)).re) -
        (∫ y in (0 : ℝ)..T, ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).re) +
        (∫ y in (0 : ℝ)..T, ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
          (((2 : ℂ) + (y : ℂ) * I) / 2 + 1)).re) +
        (∫ y in (0 : ℝ)..T, (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re) := by
    have h1 : IntervalIntegrable (fun y : ℝ ↦ ((1 : ℂ) / (((2 : ℂ) + (y : ℂ) * I) - 1)).re)
        volume 0 T :=
      (Complex.continuous_re.comp_continuousOn hcont_inv_v).intervalIntegrable (μ := volume)
    have h2 : IntervalIntegrable (fun _ : ℝ ↦ ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).re) volume 0 T :=
      intervalIntegrable_const
    have h3 : IntervalIntegrable (fun y : ℝ ↦ ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
        (((2 : ℂ) + (y : ℂ) * I) / 2 + 1)).re) volume 0 T :=
      (Complex.continuous_re.comp_continuousOn hcont_dig_v).intervalIntegrable (μ := volume)
    have h4 : IntervalIntegrable (fun y : ℝ ↦ (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) /
        riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re) volume 0 T :=
      (Complex.continuous_re.comp_continuousOn hcont_zeta_v).intervalIntegrable (μ := volume)
    have hcongr : ∫ y in (0 : ℝ)..T,
        (deriv xi ((2 : ℂ) + (y : ℂ) * I) / xi ((2 : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T,
          ((((1 : ℂ) / (((2 : ℂ) + (y : ℂ) * I) - 1)).re -
            ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).re) +
            ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
              (((2 : ℂ) + (y : ℂ) * I) / 2 + 1)).re +
            (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) /
              riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re) := by
      refine intervalIntegral.integral_congr fun y _ ↦ ?_
      rw [xi_logDeriv_eq_parts (by simp) (fun h ↦ by
        have := congrArg Complex.re h; simp at this)
        (riemannZeta_ne_zero_of_one_lt_re (by simp))]
      simp only [Complex.add_re, Complex.sub_re]
    rw [hcongr,
      intervalIntegral.integral_add ((h1.sub h2).add h3) h4,
      intervalIntegral.integral_add (h1.sub h2) h3,
      intervalIntegral.integral_sub h1 h2]
  have hsplit_h : ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
      (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im =
      (∫ x in (1 / 2 : ℝ)..(2 : ℝ), ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im) -
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ), ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).im) +
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ), ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
          (((x : ℂ) + (T : ℂ) * I) / 2 + 1)).im) +
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ), (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
          riemannZeta ((x : ℂ) + (T : ℂ) * I)).im) := by
    have h1 : IntervalIntegrable (fun x : ℝ ↦ ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im)
        volume (1 / 2 : ℝ) 2 :=
      (Complex.continuous_im.comp_continuousOn hcont_inv_h).intervalIntegrable (μ := volume)
    have h2 : IntervalIntegrable (fun _ : ℝ ↦ ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).im)
        volume (1 / 2 : ℝ) 2 := intervalIntegrable_const
    have h3 : IntervalIntegrable (fun x : ℝ ↦ ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
        (((x : ℂ) + (T : ℂ) * I) / 2 + 1)).im) volume (1 / 2 : ℝ) 2 :=
      (Complex.continuous_im.comp_continuousOn hcont_dig_h).intervalIntegrable (μ := volume)
    have h4 : IntervalIntegrable (fun x : ℝ ↦ (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
        riemannZeta ((x : ℂ) + (T : ℂ) * I)).im) volume (1 / 2 : ℝ) 2 :=
      (Complex.continuous_im.comp_continuousOn hcont_zeta_h).intervalIntegrable (μ := volume)
    have hcongr : ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        (deriv xi ((x : ℂ) + (T : ℂ) * I) / xi ((x : ℂ) + (T : ℂ) * I)).im =
        ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
          ((((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im -
            ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).im) +
            ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
              (((x : ℂ) + (T : ℂ) * I) / 2 + 1)).im +
            (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
              riemannZeta ((x : ℂ) + (T : ℂ) * I)).im) := by
      refine intervalIntegral.integral_congr fun x hx ↦ ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [xi_logDeriv_eq_parts (by simpa using hx0) (fun h ↦ by
        have := congrArg Complex.im h; simp at this; linarith)
        (riemannZeta_ne_zero_on_right_strip hT hno hx0)]
      simp only [Complex.add_im, Complex.sub_im]
    rw [hcongr,
      intervalIntegral.integral_add ((h1.sub h2).add h3) h4,
      intervalIntegral.integral_add (h1.sub h2) h3,
      intervalIntegral.integral_sub h1 h2]
  have hpi_v : ∫ y in (0 : ℝ)..T, ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).re =
      (T / 2) * Real.log Real.pi := by
    have hre_c : ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).re = 1 / 2 * Real.log Real.pi := by
      simp [Complex.mul_re]
    simp_rw [hre_c]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have hpi_h : ∫ x in (1 / 2 : ℝ)..(2 : ℝ), ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).im = 0 := by
    have him_c : ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)).im = 0 := by simp [Complex.mul_im]
    simp_rw [him_c]
    simp
  have hinv_v : ∫ y in (0 : ℝ)..T, ((1 : ℂ) / (((2 : ℂ) + (y : ℂ) * I) - 1)).re =
      (Complex.log ((1 : ℂ) + (T : ℂ) * I)).im := by
    have hderiv : ∀ y ∈ Set.uIcc 0 T,
        HasDerivAt (fun t : ℝ ↦ (Complex.log ((1 : ℂ) + (t : ℂ) * I)).im)
          ((1 : ℂ) / (((2 : ℂ) + (y : ℂ) * I) - 1)).re y := by
      intro y _
      have hslit : (1 : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := by left; simp
      have hlin : HasDerivAt (fun w : ℂ ↦ (1 : ℂ) + w * I) I (y : ℂ) := by
        have h := ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (1 : ℂ)
        exact h.congr_deriv (by simp)
      have hlog := ((Complex.hasDerivAt_log hslit).comp (y : ℂ) hlin).comp_ofReal
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hlog
      refine him.congr_deriv ?_
      have heq : (1 : ℂ) + (y : ℂ) * I = ((2 : ℂ) + (y : ℂ) * I) - 1 := by ring
      rw [Complex.imCLM_apply, heq, Complex.mul_I_im, one_div]
    have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Complex.continuous_re.comp_continuousOn hcont_inv_v).intervalIntegrable (μ := volume))
    have h0 : (Complex.log ((1 : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 := by simp
    rwa [h0, sub_zero] at hev
  have hinv_h : ∫ x in (1 / 2 : ℝ)..(2 : ℝ), ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im =
      (Complex.log ((1 : ℂ) + (T : ℂ) * I)).im - ((-1 / 2 : ℂ) + (T : ℂ) * I).arg := by
    have hderiv : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
        HasDerivAt (fun t : ℝ ↦ (Complex.log ((t : ℂ) - 1 + (T : ℂ) * I)).im)
          ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im x := by
      intro x _
      have hslit : (x : ℂ) - 1 + (T : ℂ) * I ∈ Complex.slitPlane := by right; simp [hT.ne']
      have hlin : HasDerivAt (fun w : ℂ ↦ w - 1 + (T : ℂ) * I) 1 (x : ℂ) := by
        have h := ((hasDerivAt_id (x : ℂ)).sub_const (1 : ℂ)).add_const ((T : ℂ) * I)
        exact h.congr_deriv (by simp)
      have hlog := ((Complex.hasDerivAt_log hslit).comp (x : ℂ) hlin).comp_ofReal
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hlog
      refine him.congr_deriv ?_
      have heq : (x : ℂ) - 1 + (T : ℂ) * I = ((x : ℂ) + (T : ℂ) * I) - 1 := by ring
      rw [Complex.imCLM_apply, mul_one, heq, one_div]
    have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Complex.continuous_im.comp_continuousOn hcont_inv_h).intervalIntegrable (μ := volume))
    have h2 : ((2 : ℝ) : ℂ) - 1 + (T : ℂ) * I = (1 : ℂ) + (T : ℂ) * I := by push_cast; ring
    have hhalf : ((1 / 2 : ℝ) : ℂ) - 1 + (T : ℂ) * I = (-1 / 2 : ℂ) + (T : ℂ) * I := by
      push_cast; ring
    rw [h2, hhalf, Complex.log_im (-1 / 2 + (T : ℂ) * I)] at hev
    exact hev
  have hgam_v : ∫ y in (0 : ℝ)..T, ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
      (((2 : ℂ) + (y : ℂ) * I) / 2 + 1)).re =
      (stirlingLogGamma ((2 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im := by
    have hderiv : ∀ y ∈ Set.uIcc 0 T,
        HasDerivAt (fun t : ℝ ↦ (stirlingLogGamma ((2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).im)
          ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
            (((2 : ℂ) + (y : ℂ) * I) / 2 + 1)).re y := by
      intro y _
      have hslit : (2 : ℂ) + ((y : ℂ) / 2) * I ∈ Complex.slitPlane := by
        left; simp
      have hlin : HasDerivAt (fun w : ℂ ↦ (2 : ℂ) + (w / 2) * I) ((1 / 2 : ℂ) * I) (y : ℂ) := by
        have h := (((hasDerivAt_id (y : ℂ)).div_const (2 : ℂ)).mul_const I).const_add (2 : ℂ)
        exact h.congr_deriv (by ring)
      have hst0 := ((hasDerivAt_stirlingLogGamma hslit).comp (y : ℂ) hlin).comp_ofReal
      have hst : HasDerivAt (fun t : ℝ ↦ stirlingLogGamma ((2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I))
          (AnalyticNumberTheory.AnalyticTools.Gamma.digamma ((2 : ℂ) + ((y : ℂ) / 2) * I) *
            ((1 / 2 : ℂ) * I)) y :=
        hst0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by push_cast; rfl)
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hst
      refine him.congr_deriv ?_
      have heq : (2 : ℂ) + ((y : ℂ) / 2) * I = ((2 : ℂ) + (y : ℂ) * I) / 2 + 1 := by ring
      rw [Complex.imCLM_apply, heq,
        show AnalyticNumberTheory.AnalyticTools.Gamma.digamma (((2 : ℂ) + (y : ℂ) * I) / 2 + 1) *
            ((1 / 2 : ℂ) * I) =
            ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
              (((2 : ℂ) + (y : ℂ) * I) / 2 + 1)) * I by ring,
        Complex.mul_I_im]
    have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Complex.continuous_re.comp_continuousOn hcont_dig_v).intervalIntegrable (μ := volume))
    have h0 : (stirlingLogGamma ((2 : ℂ) + (((0 : ℝ) / 2 : ℝ) : ℂ) * I)).im = 0 := by
      have heq : (2 : ℂ) + (((0 : ℝ) / 2 : ℝ) : ℂ) * I = ((2 : ℝ) : ℂ) := by simp
      rw [heq, stirlingLogGamma_ofReal_im (by norm_num)]
    rwa [h0, sub_zero] at hev
  have hgam_h : ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
      ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
        (((x : ℂ) + (T : ℂ) * I) / 2 + 1)).im =
      (stirlingLogGamma ((2 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im := by
    have hderiv : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
        HasDerivAt (fun t : ℝ ↦
            (stirlingLogGamma (((t / 2 + 1 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im)
          ((1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma
            (((x : ℂ) + (T : ℂ) * I) / 2 + 1)).im x := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hslit : (x : ℂ) / 2 + 1 + ((T / 2 : ℝ) : ℂ) * I ∈ Complex.slitPlane := by
        left; simp; linarith [hx.1]
      have hlin : HasDerivAt (fun w : ℂ ↦ w / 2 + 1 + ((T / 2 : ℝ) : ℂ) * I) (1 / 2 : ℂ)
          (x : ℂ) := by
        have h := (((hasDerivAt_id (x : ℂ)).div_const (2 : ℂ)).add_const (1 : ℂ)).add_const
          (((T / 2 : ℝ) : ℂ) * I)
        exact h.congr_deriv (by ring)
      have hst0 := ((hasDerivAt_stirlingLogGamma hslit).comp (x : ℂ) hlin).comp_ofReal
      have hst : HasDerivAt (fun t : ℝ ↦
          stirlingLogGamma (((t / 2 + 1 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I))
          (AnalyticNumberTheory.AnalyticTools.Gamma.digamma
            ((x : ℂ) / 2 + 1 + ((T / 2 : ℝ) : ℂ) * I) * (1 / 2 : ℂ)) x :=
        hst0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by push_cast; rfl)
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hst
      refine him.congr_deriv ?_
      have heq : (x : ℂ) / 2 + 1 + ((T / 2 : ℝ) : ℂ) * I =
          ((x : ℂ) + (T : ℂ) * I) / 2 + 1 := by push_cast; ring
      rw [Complex.imCLM_apply, heq, mul_comm]
    have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Complex.continuous_im.comp_continuousOn hcont_dig_h).intervalIntegrable (μ := volume))
    have h2 : (((2 / 2 + 1 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) =
        (2 : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by push_cast; ring
    have hhalf : ((((1 / 2 : ℝ) / 2 + 1 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) =
        (5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by push_cast; ring
    rw [h2, hhalf] at hev
    exact hev
  have hzeta_v : ∫ y in (0 : ℝ)..T, (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) /
      riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re =
      (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg := by
    have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ ↦ hasDerivAt_im_log_zeta_two_add_mul_I y)
      ((Complex.continuous_re.comp_continuousOn hcont_zeta_v).intervalIntegrable (μ := volume))
    have h0 : (Complex.log (riemannZeta ((2 : ℂ) + ((0 : ℝ) : ℂ) * I))).im = 0 := by
      rw [Complex.log_im]
      have hre : 0 < (riemannZeta ((2 : ℂ) + ((0 : ℝ) : ℂ) * I)).re := by
        linarith [riemannZeta_two_add_mul_I_re_ge 0]
      have him : (riemannZeta ((2 : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 := by
        have heq : (2 : ℂ) + ((0 : ℝ) : ℂ) * I = ((2 : ℝ) : ℂ) := by simp
        rw [heq]
        have hs : 1 < ((2 : ℝ) : ℂ).re := by simp
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
        have hsumm_c : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ ((2 : ℝ) : ℂ) := by
          refine (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs) |>.congr
            fun n ↦ ?_
          simp [Nat.cast_add, Nat.cast_one]
        rw [← Complex.imCLM_apply, Complex.imCLM.map_tsum hsumm_c]
        have h0' : ∀ n : ℕ, Complex.imCLM (1 / ((n : ℂ) + 1) ^ ((2 : ℝ) : ℂ)) = 0 := by
          intro n
          have hcast : 1 / ((n : ℂ) + 1) ^ ((2 : ℝ) : ℂ) =
              (((1 / ((n : ℝ) + 1) ^ 2 : ℝ)) : ℂ) := by
            push_cast; simp [Complex.cpow_ofNat]
          rw [hcast, Complex.imCLM_apply, Complex.ofReal_im]
        simp_rw [h0']
        simp
      exact Complex.arg_eq_zero_iff.mpr ⟨hre.le, him⟩
    rw [h0, sub_zero, Complex.log_im] at hev
    exact hev
  rw [zeroCountUpTo_eq_contour_halved hT hno, hsplit_v, hsplit_h, hinv_v, hpi_v, hgam_v, hzeta_v,
    hinv_h, hpi_h, hgam_h]
  unfold argumentSApprox
  ring

private lemma list_prod_ratio_sphere_le (z₀ w : ℂ) (hw : ‖w - z₀‖ = 27 / 16) :
    ∀ zs : List ℂ, (∀ ρ ∈ zs, ‖ρ - z₀‖ ≤ 13 / 8) →
      ‖(zs.map (fun ρ ↦ z₀ - ρ)).prod / (zs.map (fun ρ ↦ w - ρ)).prod‖ ≤ 26 ^ zs.length ∧
        (zs.map (fun ρ ↦ w - ρ)).prod ≠ 0 := by
  intro zs hzs
  induction zs with
  | nil => simp
  | cons ρ l ih =>
    obtain ⟨ih_le, ih_ne⟩ := ih fun u hu ↦ hzs u (List.mem_cons_of_mem ρ hu)
    have hρ_dist : ‖ρ - z₀‖ ≤ 13 / 8 := hzs ρ List.mem_cons_self
    have hwρ_ge : (1 / 16 : ℝ) ≤ ‖w - ρ‖ := by
      have htri : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by
        calc
          ‖w - z₀‖ = ‖(w - ρ) + (ρ - z₀)‖ := by ring_nf
          _ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := norm_add_le _ _
      linarith
    have hwρ_ne : w - ρ ≠ 0 := fun h ↦ by rw [h, norm_zero] at hwρ_ge; linarith
    have hz₀ρ_le : ‖z₀ - ρ‖ ≤ 13 / 8 := by rw [norm_sub_rev]; exact hρ_dist
    have hfac : ‖(z₀ - ρ) / (w - ρ)‖ ≤ 26 := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      linarith
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    refine ⟨?_, mul_ne_zero hwρ_ne ih_ne⟩
    have hdiv_eq : (z₀ - ρ) * (l.map (fun u ↦ z₀ - u)).prod /
        ((w - ρ) * (l.map (fun u ↦ w - u)).prod) =
        ((z₀ - ρ) / (w - ρ)) *
          ((l.map (fun u ↦ z₀ - u)).prod / (l.map (fun u ↦ w - u)).prod) :=
      (div_mul_div_comm _ _ _ _).symm
    rw [hdiv_eq, norm_mul]
    exact mul_le_mul hfac ih_le (norm_nonneg _) (by norm_num)

private lemma list_prod_logDeriv_eq (w : ℂ) :
    ∀ l : List ℂ, (∀ ρ ∈ l, w ≠ ρ) →
      HasDerivAt (fun z : ℂ ↦ (l.map (fun ρ ↦ z - ρ)).prod)
        ((l.map (fun ρ ↦ w - ρ)).prod * (l.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum) w ∧
        (l.map (fun ρ ↦ w - ρ)).prod ≠ 0 := by
  intro l hl
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, mul_zero, ne_eq, one_ne_zero,
      not_false_eq_true, and_true]
    exact hasDerivAt_const w (1 : ℂ)
  | cons ρ l ih =>
    obtain ⟨ih_d, ih_ne⟩ := ih fun u hu ↦ hl u (List.mem_cons_of_mem ρ hu)
    have hwρ : w - ρ ≠ 0 := sub_ne_zero.mpr (hl ρ List.mem_cons_self)
    have hd1 : HasDerivAt (fun z : ℂ ↦ z - ρ) 1 w := (hasDerivAt_id w).sub_const ρ
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨(hd1.mul ih_d).congr_deriv ?_, mul_ne_zero hwρ ih_ne⟩
    calc
      1 * (l.map (fun u ↦ w - u)).prod +
          (w - ρ) * ((l.map (fun u ↦ w - u)).prod * (l.map (fun u ↦ (1 : ℂ) / (w - u))).sum)
          = (w - ρ) * (1 / (w - ρ)) * (l.map (fun u ↦ w - u)).prod +
              (w - ρ) * (l.map (fun u ↦ w - u)).prod *
                (l.map (fun u ↦ (1 : ℂ) / (w - u))).sum := by
        rw [mul_one_div_cancel hwρ, one_mul]; ring
      _ = (w - ρ) * (l.map (fun u ↦ w - u)).prod *
            (1 / (w - ρ) + (l.map (fun u ↦ (1 : ℂ) / (w - u))).sum) := by ring

private lemma list_sum_inv_im_continuousOn (T : ℝ) :
    ∀ l : List ℂ, (∀ ρ ∈ l, T - ρ.im ≠ 0) →
      ContinuousOn (fun x : ℝ ↦
        ((l.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ))).sum).im)
        (Set.uIcc (1 / 2 : ℝ) 2) := by
  intro l hl
  induction l with
  | nil => simp; exact continuousOn_const
  | cons ρ l ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_im]
    exact (Complex.continuous_im.comp_continuousOn
      (continuousOn_one_div_horiz T ρ (hl ρ List.mem_cons_self) (Set.uIcc (1 / 2 : ℝ) 2))).add
      (ih fun u hu ↦ hl u (List.mem_cons_of_mem ρ hu))

private lemma list_sum_inv_im_integral_le (T : ℝ) :
    ∀ l : List ℂ, (∀ ρ ∈ l, T - ρ.im ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        ((l.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ))).sum).im| ≤
        Real.pi * (l.length : ℝ) := by
  intro l hl
  induction l with
  | nil => simp
  | cons ρ l ih =>
    have hne : T - ρ.im ≠ 0 := hl ρ List.mem_cons_self
    have hterm_cont : ContinuousOn (fun x : ℝ ↦ ((1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ)).im)
        (Set.uIcc (1 / 2 : ℝ) 2) :=
      Complex.continuous_im.comp_continuousOn
        (continuousOn_one_div_horiz T ρ hne (Set.uIcc (1 / 2 : ℝ) 2))
    have hterm_bd : |∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        ((1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ)).im| ≤ Real.pi := by
      have hderiv : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
          HasDerivAt (fun t : ℝ ↦ -Real.arctan ((t - ρ.re) / (T - ρ.im)))
            ((1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ)).im x := by
        intro x _
        have hsub : HasDerivAt (fun t : ℝ ↦ (t - ρ.re) / (T - ρ.im)) (1 / (T - ρ.im)) x := by
          simpa using ((hasDerivAt_id x).sub_const ρ.re).div_const (T - ρ.im)
        have harc := ((Real.hasDerivAt_arctan ((x - ρ.re) / (T - ρ.im))).comp x hsub).neg
        refine harc.congr_deriv ?_
        have hden_pos : 0 < (x - ρ.re) ^ 2 + (T - ρ.im) ^ 2 := by positivity
        have him_eq : ((1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ)).im =
            -(T - ρ.im) / ((x - ρ.re) ^ 2 + (T - ρ.im) ^ 2) := by
          rw [one_div, Complex.inv_im]
          have hre : ((x : ℂ) + (T : ℂ) * I - ρ).re = x - ρ.re := by simp
          have him : ((x : ℂ) + (T : ℂ) * I - ρ).im = T - ρ.im := by simp
          rw [Complex.normSq_apply, hre, him]
          ring
        rw [him_eq]
        field_simp [hne, hden_pos.ne']
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hterm_cont.intervalIntegrable]
      have hb1 : |Real.arctan ((2 - ρ.re) / (T - ρ.im))| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
      have hb2 : |Real.arctan ((1 / 2 - ρ.re) / (T - ρ.im))| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
      calc
        |-Real.arctan ((2 - ρ.re) / (T - ρ.im)) -
            (-Real.arctan ((1 / 2 - ρ.re) / (T - ρ.im)))|
            ≤ |-Real.arctan ((2 - ρ.re) / (T - ρ.im))| +
                |Real.arctan ((1 / 2 - ρ.re) / (T - ρ.im))| := by
          rw [sub_neg_eq_add]; exact abs_add_le _ _
        _ ≤ Real.pi / 2 + Real.pi / 2 := by rw [abs_neg]; linarith
        _ = Real.pi := by ring
    have hl_cont := list_sum_inv_im_continuousOn T l fun u hu ↦ hl u (List.mem_cons_of_mem ρ hu)
    have ihl := ih fun u hu ↦ hl u (List.mem_cons_of_mem ρ hu)
    simp only [List.map_cons, List.sum_cons, Complex.add_im, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    rw [intervalIntegral.integral_add hterm_cont.intervalIntegrable hl_cont.intervalIntegrable]
    have htri := abs_add_le
      (∫ x in (1 / 2 : ℝ)..(2 : ℝ), ((1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ)).im)
      (∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        ((l.map (fun r ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - r))).sum).im)
    linarith [hterm_bd, ihl, show Real.pi * ((l.length : ℝ) + 1) =
      Real.pi + Real.pi * (l.length : ℝ) by ring]

/-- **Backlund–Jensen `O(log T)` bound** for `argumentSApprox T` at all `T ≥ 2` avoiding zero
ordinates. -/
theorem argumentSApprox_abs_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ¬ IsZeroOrdinate T →
      |argumentSApprox T| ≤ C * Real.log T := by
  obtain ⟨Cs, hCs_pos, hCs_bd⟩ := norm_riemannZeta_critical_strip_le (ε := 1 / 2) (by norm_num)
  obtain ⟨C₁, hC₁_pos, hC₁_bd⟩ := norm_riemannZeta_re_ge_one_le
  let K_low : Set ℂ := Set.Icc (0 : ℝ) 4 ×ℂ Set.Icc (1 / 4 : ℝ) 6
  have hK_low_cpt : IsCompact K_low := isCompact_Icc.reProdIm isCompact_Icc
  have hzeta_cont_low : ContinuousOn riemannZeta K_low := by
    have hz_diff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact hz_diff.continuousOn.mono fun w hw ↦ fun h1 ↦ by
      have him := congrArg Complex.im h1
      simp only [Complex.one_im] at him
      linarith [hw.2.1]
  obtain ⟨M₀, hM₀_bd⟩ := hK_low_cpt.exists_bound_of_continuousOn hzeta_cont_low
  let C_zeta : ℝ := max (max Cs C₁) (max M₀ 0) + 1
  have hC_zeta_ge1 : 1 ≤ C_zeta := by
    have hnn : 0 ≤ max (max Cs C₁) (max M₀ 0) := le_trans (le_max_right M₀ 0) (le_max_right _ _)
    dsimp only [C_zeta]; linarith
  have hC_zeta_pos : 0 < C_zeta := by linarith
  have hCs_le : Cs ≤ C_zeta := by
    have := le_trans (le_max_left Cs C₁) (le_max_left (max Cs C₁) (max M₀ 0))
    dsimp only [C_zeta]; linarith
  have hC₁_le : C₁ ≤ C_zeta := by
    have := le_trans (le_max_right Cs C₁) (le_max_left (max Cs C₁) (max M₀ 0))
    dsimp only [C_zeta]; linarith
  have hM₀_le : M₀ ≤ C_zeta := by
    have := le_trans (le_max_left M₀ 0) (le_max_right (max Cs C₁) (max M₀ 0))
    dsimp only [C_zeta]; linarith
  let K_M : ℝ := 16 * C_zeta
  have hK_M_ge : 1 ≤ K_M := by dsimp only [K_M]; nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden_j_pos : 0 < Real.log ((7 / 4 : ℝ) / (13 / 8)) := Real.log_pos (by norm_num)
  let C_j : ℝ := (Real.log K_M / Real.log 2 + 2) / Real.log ((7 / 4 : ℝ) / (13 / 8))
  have hC_j_pos : 0 < C_j := by
    have hlogK_nn : 0 ≤ Real.log K_M := Real.log_nonneg hK_M_ge
    dsimp only [C_j]
    positivity
  let C_ld : ℝ := 2 * ((13 / 8 : ℝ) + 3 / 2) / ((13 / 8 : ℝ) - 3 / 2) ^ 2 *
    (Real.log K_M / Real.log 2 + 2 + C_j * Real.log 26)
  have hC_ld_pos : 0 < C_ld := by
    have hlogK_nn : 0 ≤ Real.log K_M := Real.log_nonneg hK_M_ge
    have hlog26_pos : 0 < Real.log 26 := Real.log_pos (by norm_num)
    dsimp only [C_ld]
    positivity
  let C : ℝ := (1 / Real.pi) * (Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) + 1
  have hC_pos : 0 < C := by
    have hpi_pos := Real.pi_pos
    dsimp only [C]
    positivity
  refine ⟨C, hC_pos, fun T hT hno ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hone_le_logT : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log T := by
    rw [one_div_mul_eq_div, one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) hT
  let z₀ : ℂ := (2 : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = 2 := by simp [z₀]
  have hz₀_im : z₀.im = T := by simp [z₀]
  have hz₀_ne : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp [z₀])
  have hz₀_inv : ‖riemannZeta z₀‖⁻¹ ≤ 4 := by
    have hre := riemannZeta_two_add_mul_I_re_ge T
    have hnorm : (1 / 4 : ℝ) ≤ ‖riemannZeta z₀‖ := hre.trans (Complex.re_le_norm _)
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hclosed_prop : ∀ w ∈ Metric.closedBall z₀ (7 / 4),
      w ≠ 1 ∧ 0 ≤ w.re ∧ w.re ≤ 4 ∧ (1 / 4 : ℝ) ≤ w.im ∧ w.im ≤ 2 * T := by
    intro w hw
    have hdist : ‖w - z₀‖ ≤ 7 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hre_diff : |w.re - 2| ≤ 7 / 4 := by
      rw [← hz₀_re]; exact (Complex.abs_re_le_norm (w - z₀)).trans hdist
    have him_diff : |w.im - T| ≤ 7 / 4 := by
      rw [← hz₀_im]; exact (Complex.abs_im_le_norm (w - z₀)).trans hdist
    have hw_re0 : 0 ≤ w.re := by linarith [(abs_le.mp hre_diff).1]
    have hw_re4 : w.re ≤ 4 := by linarith [(abs_le.mp hre_diff).2]
    have hw_im0 : (1 / 4 : ℝ) ≤ w.im := by linarith [(abs_le.mp him_diff).1]
    have hw_im2T : w.im ≤ 2 * T := by linarith [(abs_le.mp him_diff).2]
    have hw1 : w ≠ 1 := fun h ↦ by rw [h, Complex.one_im] at hw_im0; linarith
    exact ⟨hw1, hw_re0, hw_re4, hw_im0, hw_im2T⟩
  have han : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ (7 / 4)) := by
    have hdiff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact (hdiff.analyticOnNhd isOpen_ne).mono fun w hw ↦ (hclosed_prop w hw).1
  let M_ζ : ℝ := C_zeta * (2 * T + 2)
  have hM_ζ_pos : 0 < M_ζ := by positivity
  have hzeta_bd : ∀ w ∈ Metric.closedBall z₀ (7 / 4), ‖riemannZeta w‖ ≤ M_ζ := by
    intro w hw
    obtain ⟨_, hw_re0, hw_re4, hw_im0, hw_im2T⟩ := hclosed_prop w hw
    have hpos_im : 0 < w.im := by linarith
    rcases le_or_gt w.im 2 with hw_low | hw_high
    · have hwK : w ∈ K_low := ⟨⟨hw_re0, hw_re4⟩, ⟨hw_im0, by linarith⟩⟩
      have h1 : 1 ≤ 2 * T + 2 := by linarith
      calc
        ‖riemannZeta w‖ ≤ M₀ := hM₀_bd w hwK
        _ ≤ C_zeta * 1 := by linarith
        _ ≤ C_zeta * (2 * T + 2) := mul_le_mul_of_nonneg_left h1 hC_zeta_pos.le
    · have hw_eq : riemannZeta w = riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I) := by
        congr 1; exact (Complex.re_add_im w).symm
      rw [hw_eq]
      have habs_im : |w.im| = w.im := abs_of_pos hpos_im
      rcases le_or_gt w.re 1 with hw1 | hw1
      · have hstrip := hCs_bd ⟨hw_re0, hw1⟩ (by rw [habs_im]; linarith)
        have hexp : (1 - w.re) / 2 + 1 / 2 ≤ 1 := by linarith
        have hpow : (|w.im| + 2) ^ ((1 - w.re) / 2 + 1 / 2) ≤ |w.im| + 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im] :
            (1 : ℝ) ≤ |w.im| + 2) hexp
        calc
          ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
              ≤ Cs * (|w.im| + 2) ^ ((1 - w.re) / 2 + 1 / 2) := hstrip
          _ ≤ Cs * (|w.im| + 2) := mul_le_mul_of_nonneg_left hpow hCs_pos.le
          _ ≤ C_zeta * (2 * T + 2) := by
            rw [habs_im]
            exact mul_le_mul hCs_le (by linarith) (by positivity) hC_zeta_pos.le
      · have hge1 := hC₁_bd hw1.le (by rw [habs_im]; linarith)
        have hlog_le : Real.log (|w.im| + 2) ≤ |w.im| + 2 := by
          have h := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg w.im] : (0 : ℝ) < |w.im| + 2)
          linarith
        calc
          ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
              ≤ C₁ * Real.log (|w.im| + 2) := hge1
          _ ≤ C₁ * (|w.im| + 2) := mul_le_mul_of_nonneg_left hlog_le hC₁_pos.le
          _ ≤ C_zeta * (2 * T + 2) := by
            rw [habs_im]
            exact mul_le_mul hC₁_le (by linarith) (by positivity) hC_zeta_pos.le
  let M_ratio : ℝ := 4 * M_ζ
  have hM_ratio_ge1 : 1 ≤ M_ratio := by
    have h1 := hzeta_bd z₀ (Metric.mem_closedBall_self (by norm_num))
    have h14 : (1 / 4 : ℝ) ≤ ‖riemannZeta z₀‖ :=
      (riemannZeta_two_add_mul_I_re_ge T).trans (Complex.re_le_norm _)
    dsimp only [M_ratio]; linarith
  have hratio_bd : ∀ w ∈ Metric.closedBall z₀ (7 / 4),
      ‖riemannZeta w / riemannZeta z₀‖ ≤ M_ratio := by
    intro w hw
    rw [norm_div, div_eq_mul_inv]
    dsimp only [M_ratio]
    calc
      ‖riemannZeta w‖ * ‖riemannZeta z₀‖⁻¹ ≤ M_ζ * 4 :=
        mul_le_mul (hzeta_bd w hw) hz₀_inv (by positivity) hM_ζ_pos.le
      _ = 4 * M_ζ := by ring
  have hM_ratio_le_K : M_ratio ≤ K_M * T ^ 2 := by
    have hlin : 2 * T + 2 ≤ 4 * T := by linarith
    have hT2 : 4 * T ≤ 4 * T ^ 2 := by nlinarith
    dsimp only [M_ratio, M_ζ, K_M]
    nlinarith [hC_zeta_pos]
  have hlog_M_ratio : Real.log M_ratio ≤ (Real.log K_M / Real.log 2 + 2) * Real.log T := by
    have h1 : Real.log M_ratio ≤ Real.log (K_M * T ^ 2) :=
      Real.log_le_log (by linarith) hM_ratio_le_K
    have hK_nn : 0 ≤ Real.log K_M := Real.log_nonneg hK_M_ge
    rw [Real.log_mul (by linarith) (pow_ne_zero 2 hT_pos.ne'), Real.log_pow] at h1
    have hK_scale : Real.log K_M ≤ (Real.log K_M / Real.log 2) * Real.log T := by
      calc
        Real.log K_M = Real.log K_M * 1 := (mul_one _).symm
        _ ≤ Real.log K_M * ((1 / Real.log 2) * Real.log T) :=
          mul_le_mul_of_nonneg_left hone_le_logT hK_nn
        _ = (Real.log K_M / Real.log 2) * Real.log T := by ring
    push_cast at h1
    linarith
  have hjensen := AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount_le_sub_log_div_log
    (r := (13 / 8 : ℝ)) (R := (7 / 4 : ℝ)) (M := M_ζ) (by norm_num) (by norm_num)
    hM_ζ_pos han hz₀_ne (fun w hw ↦ hzeta_bd w (Metric.sphere_subset_closedBall hw))
  have hcnt_le_jensen :
      (AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount riemannZeta z₀ (13 / 8) : ℝ) ≤
        C_j * Real.log T := by
    have hneg_log : -Real.log ‖riemannZeta z₀‖ ≤ Real.log 4 := by
      have h14 : (1 / 4 : ℝ) ≤ ‖riemannZeta z₀‖ :=
        (riemannZeta_two_add_mul_I_re_ge T).trans (Complex.re_le_norm _)
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) h14
      rw [one_div, Real.log_inv] at hl
      linarith
    have hnum : Real.log M_ζ - Real.log ‖riemannZeta z₀‖ ≤ Real.log M_ratio := by
      calc
        Real.log M_ζ - Real.log ‖riemannZeta z₀‖ ≤ Real.log M_ζ + Real.log 4 := by linarith
        _ = Real.log (4 * M_ζ) := by
          rw [mul_comm, Real.log_mul hM_ζ_pos.ne' (by norm_num)]
    calc
      (AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount
          riemannZeta z₀ (13 / 8) : ℝ)
          ≤ (Real.log M_ζ - Real.log ‖riemannZeta z₀‖) /
              Real.log ((7 / 4 : ℝ) / (13 / 8)) := hjensen
      _ ≤ Real.log M_ratio / Real.log ((7 / 4 : ℝ) / (13 / 8)) :=
        div_le_div_of_nonneg_right hnum hden_j_pos.le
      _ ≤ ((Real.log K_M / Real.log 2 + 2) * Real.log T) /
            Real.log ((7 / 4 : ℝ) / (13 / 8)) :=
        div_le_div_of_nonneg_right hlog_M_ratio hden_j_pos.le
      _ = C_j * Real.log T := by dsimp only [C_j]; ring
  let han_r0 : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ (13 / 8)) :=
    han.mono (Metric.closedBall_subset_closedBall (by norm_num))
  let hZ_fin := AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroSet_finite
    (by norm_num : (0 : ℝ) ≤ (13 / 8 : ℝ)) han_r0 hz₀_ne
  let Z : Finset ℂ := hZ_fin.toFinset
  have hZK : (Z : Set ℂ) ⊆ Metric.closedBall z₀ (13 / 8) :=
    fun ρ hρ ↦ (hZ_fin.mem_toFinset.mp hρ).1
  have hKZ : ∀ ρ ∈ Metric.closedBall z₀ (13 / 8), riemannZeta ρ = 0 → ρ ∈ Z :=
    fun ρ h1 h2 ↦ hZ_fin.mem_toFinset.mpr ⟨h1, h2⟩
  have hU_ord : ∀ ρ ∈ Z, ρ ∈ Metric.ball z₀ (7 / 4) ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro ρ hρ
    have hρK : ρ ∈ Metric.closedBall z₀ (13 / 8) := hZK hρ
    have hρ_ball : ρ ∈ Metric.ball z₀ (7 / 4) :=
      Metric.closedBall_subset_ball (by norm_num) hρK
    have han_ball : AnalyticOnNhd ℂ riemannZeta (Metric.ball z₀ (7 / 4)) :=
      han.mono Metric.ball_subset_closedBall
    have htop := han_ball.analyticOrderAt_ne_top_of_isPreconnected
      (convex_ball z₀ (7 / 4)).isPreconnected (Metric.mem_ball_self (by norm_num)) hρ_ball
      ((han_ball z₀ (Metric.mem_ball_self (by norm_num))).analyticOrderAt_eq_zero.mpr hz₀_ne |>.symm ▸
        by simp)
    exact ⟨hρ_ball, htop⟩
  obtain ⟨zs, g, hzs_prop, hzs_len, hg_an, hg_ne, hprod⟩ :=
    extract_zeros_from_finset (Metric.ball z₀ (7 / 4)) (Metric.closedBall z₀ (13 / 8)) Z hZK
      (∑ ρ ∈ Z, analyticOrderNatAt riemannZeta ρ) riemannZeta
      (han.mono Metric.ball_subset_closedBall) hKZ hU_ord rfl
  have hzs_len_eq : zs.length =
      AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount riemannZeta z₀ (13 / 8) := by
    rw [hzs_len, AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount_eq_sum_analyticOrderNatAt
      (by norm_num : (0 : ℝ) ≤ (13 / 8 : ℝ)) han_r0 hz₀_ne hZ_fin.coe_toFinset]
  let M_g : ℝ := M_ratio * 26 ^ zs.length
  have hM_g_ge1 : 1 ≤ M_g := by
    have : 1 ≤ (26 : ℝ) ^ zs.length := one_le_pow₀ (by norm_num)
    dsimp only [M_g]; nlinarith [hM_ratio_ge1]
  have hzs_dist : ∀ ρ ∈ zs, ‖ρ - z₀‖ ≤ 13 / 8 := fun ρ hρ ↦ by
    simpa [Metric.mem_closedBall, dist_eq_norm] using (hzs_prop ρ hρ).1
  have hg_z₀_ne : g z₀ ≠ 0 := hg_ne z₀ (Metric.mem_closedBall_self (by norm_num))
  have hg_sphere : ∀ w ∈ Metric.sphere z₀ (27 / 16), ‖g w / g z₀‖ ≤ M_g := by
    intro w hw
    have hw_dist : ‖w - z₀‖ = 27 / 16 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    obtain ⟨hP_bd, hPw_ne⟩ := list_prod_ratio_sphere_le z₀ w hw_dist zs hzs_dist
    have hPz₀_ne : (zs.map (fun ρ ↦ z₀ - ρ)).prod ≠ 0 := by
      intro h0
      have := hprod z₀
      rw [h0, zero_mul] at this
      exact hz₀_ne this
    have heq : g w / g z₀ = (riemannZeta w / riemannZeta z₀) *
        ((zs.map (fun ρ ↦ z₀ - ρ)).prod / (zs.map (fun ρ ↦ w - ρ)).prod) := by
      have hw_eq := hprod w
      have hz₀_eq := hprod z₀
      rw [hw_eq, hz₀_eq]
      field_simp [hg_z₀_ne, hPw_ne, hPz₀_ne]
    rw [heq, norm_mul]
    exact mul_le_mul (hratio_bd w (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall hw))) hP_bd (norm_nonneg _) (by positivity)
  have hg_closed : ∀ w ∈ Metric.closedBall z₀ (27 / 16), ‖g w / g z₀‖ ≤ M_g := by
    have hdiff : DiffContOnCl ℂ (fun w ↦ g w / g z₀) (Metric.ball z₀ (27 / 16)) := by
      have hsub : Metric.closedBall z₀ (27 / 16) ⊆ Metric.ball z₀ (7 / 4) :=
        Metric.closedBall_subset_ball (by norm_num)
      exact ((hg_an.mono hsub).differentiableOn.div_const (g z₀)).diffContOnCl_ball Subset.rfl
    intro w hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff
      (fun x hx ↦ hg_sphere x (Metric.frontier_ball_subset_sphere hx))
      (closure_ball z₀ (by norm_num : (27 / 16 : ℝ) ≠ 0) ▸ hw)
  have hg_ball : ∀ w ∈ Metric.ball z₀ (13 / 8), ‖g w / g z₀‖ ≤ M_g := fun w hw ↦
    hg_closed w ((Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by norm_num))) hw)
  have hg_diff_r0 : DifferentiableOn ℂ g (Metric.ball z₀ (13 / 8)) :=
    (hg_an.mono (Metric.ball_subset_ball (by norm_num))).differentiableOn
  have hg_ne_r0 : ∀ w ∈ Metric.ball z₀ (13 / 8), g w ≠ 0 := fun w hw ↦
    hg_ne w (Metric.ball_subset_closedBall hw)
  have hld_g_bd : ∀ z ∈ Metric.closedBall z₀ (3 / 2), ‖deriv g z / g z‖ ≤ C_ld * Real.log T := by
    intro z hz
    have hb := landau_logDeriv_le_of_ne_zero (by norm_num : (0 : ℝ) ≤ (3 / 2 : ℝ))
      (by norm_num : (3 / 2 : ℝ) < (13 / 8 : ℝ)) hg_diff_r0 hg_ne_r0 hg_ball hz
    rw [logDeriv_apply] at hb
    have hlogMg : Real.log M_g ≤ (Real.log K_M / Real.log 2 + 2 + C_j * Real.log 26) * Real.log T := by
      dsimp only [M_g]
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow, hzs_len_eq]
      have h26_nn : 0 ≤ Real.log 26 := Real.log_nonneg (by norm_num)
      nlinarith [hcnt_le_jensen]
    have hcoeff : 2 * ((13 / 8 : ℝ) + 3 / 2) / ((13 / 8 : ℝ) - 3 / 2) ^ 2 * Real.log M_g ≤
        C_ld * Real.log T := by
      dsimp only [C_ld]
      calc
        2 * ((13 / 8 : ℝ) + 3 / 2) / ((13 / 8 : ℝ) - 3 / 2) ^ 2 * Real.log M_g
            ≤ 2 * ((13 / 8 : ℝ) + 3 / 2) / ((13 / 8 : ℝ) - 3 / 2) ^ 2 *
                ((Real.log K_M / Real.log 2 + 2 + C_j * Real.log 26) * Real.log T) :=
          mul_le_mul_of_nonneg_left hlogMg (by norm_num)
        _ = (2 * ((13 / 8 : ℝ) + 3 / 2) / ((13 / 8 : ℝ) - 3 / 2) ^ 2 *
                (Real.log K_M / Real.log 2 + 2 + C_j * Real.log 26)) * Real.log T := by ring
    exact hb.trans hcoeff
  have hzeta_split : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) / riemannZeta ((x : ℂ) + (T : ℂ) * I) =
        (zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ))).sum +
          deriv g ((x : ℂ) + (T : ℂ) * I) / g ((x : ℂ) + (T : ℂ) * I) := by
    intro x hx
    let w : ℂ := (x : ℂ) + (T : ℂ) * I
    have hw_ball : w ∈ Metric.ball z₀ (13 / 8) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : w - z₀ = (((x - 2 : ℝ) : ℂ)) := by apply Complex.ext <;> simp [w, z₀]
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hgw : g w ≠ 0 := hg_ne_r0 w hw_ball
    have hw_ne_zs : ∀ ρ ∈ zs, w ≠ ρ := by
      intro ρ hρ heq
      subst heq
      exact riemannZeta_ne_zero_on_right_strip hT_pos hno (by linarith [hx.1]) (hzs_prop w hρ).2
    obtain ⟨hPd, hPne⟩ := list_prod_logDeriv_eq w zs hw_ne_zs
    have hfg := hPd.mul ((hg_an w (Metric.ball_subset_ball (by norm_num) hw_ball)).differentiableAt).hasDerivAt
    have hev : riemannZeta =ᶠ[𝓝 w] fun z ↦ (zs.map (fun ρ ↦ z - ρ)).prod * g z :=
      Filter.Eventually.of_forall hprod
    have hderiv_zeta : deriv riemannZeta w =
        ((zs.map (fun ρ ↦ w - ρ)).prod * (zs.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum) * g w +
          (zs.map (fun ρ ↦ w - ρ)).prod * deriv g w := by
      rw [hev.deriv_eq]
      exact hfg.deriv
    rw [hderiv_zeta, hprod w]
    change ((((zs.map (fun ρ ↦ w - ρ)).prod * (zs.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum) * g w +
        (zs.map (fun ρ ↦ w - ρ)).prod * deriv g w) /
        ((zs.map (fun ρ ↦ w - ρ)).prod * g w)) =
        (zs.map (fun ρ ↦ (1 : ℂ) / (w - ρ))).sum + deriv g w / g w
    field_simp [hPne, hgw]
  have hρ_im_ne : ∀ ρ ∈ zs, T - ρ.im ≠ 0 := by
    intro ρ hρ h0
    obtain ⟨hρK, hζ0⟩ := hzs_prop ρ hρ
    have hdist : ‖ρ - z₀‖ ≤ 13 / 8 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hρK
    have hre_diff : |ρ.re - 2| ≤ 13 / 8 := by
      rw [← hz₀_re]; exact (Complex.abs_re_le_norm (ρ - z₀)).trans hdist
    have hρ_re_pos : 0 < ρ.re := by linarith [(abs_le.mp hre_diff).1]
    have hρ_re_lt1 : ρ.re < 1 := by
      by_contra! hge1
      exact riemannZeta_ne_zero_of_one_le_re hge1 hζ0
    exact hno ⟨ρ, ⟨hζ0, hρ_re_pos, hρ_re_lt1⟩, by linarith⟩
  have hint_g_bd : |∫ x in (1 / 2 : ℝ)..(2 : ℝ),
      (deriv g ((x : ℂ) + (T : ℂ) * I) / g ((x : ℂ) + (T : ℂ) * I)).im| ≤
      (3 / 2 : ℝ) * (C_ld * Real.log T) := by
    have hnorm_le : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 2,
        ‖(deriv g ((x : ℂ) + (T : ℂ) * I) / g ((x : ℂ) + (T : ℂ) * I)).im‖ ≤
          C_ld * Real.log T := by
      intro x hx
      have hx' := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by norm_num)] at hx'
      have hx_mem : (x : ℂ) + (T : ℂ) * I ∈ Metric.closedBall z₀ (3 / 2) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hdiff : (x : ℂ) + (T : ℂ) * I - z₀ = (((x - 2 : ℝ) : ℂ)) := by
          apply Complex.ext <;> simp [z₀]
        rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hx'.1, hx'.2]
      exact (Complex.abs_im_le_norm _).trans (hld_g_bd _ hx_mem)
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const hnorm_le
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2 - 1 / 2)] at hbd
    linarith
  have hint_zs_bd : |∫ x in (1 / 2 : ℝ)..(2 : ℝ),
      ((zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ))).sum).im| ≤
      Real.pi * (C_j * Real.log T) := by
    have h1 := list_sum_inv_im_integral_le T zs hρ_im_ne
    have h2 : (zs.length : ℝ) ≤ C_j * Real.log T := by rw [hzs_len_eq]; exact hcnt_le_jensen
    exact h1.trans (mul_le_mul_of_nonneg_left h2 Real.pi_pos.le)
  have hcont_g : ContinuousOn (fun x : ℝ ↦
      (deriv g ((x : ℂ) + (T : ℂ) * I) / g ((x : ℂ) + (T : ℂ) * I)).im)
      (Set.uIcc (1 / 2 : ℝ) 2) := by
    have hg_an_ball : AnalyticOnNhd ℂ g (Metric.ball z₀ (7 / 4)) := hg_an
    have hdg_cont : ContinuousOn (deriv g) (Metric.ball z₀ (7 / 4)) :=
      (hg_an_ball.deriv).continuousOn
    have hg_cont : ContinuousOn g (Metric.ball z₀ (7 / 4)) := hg_an_ball.continuousOn
    have hpath : Continuous fun x : ℝ ↦ (x : ℂ) + (T : ℂ) * I :=
      Complex.continuous_ofReal.add continuous_const
    have hmem_ball : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (x : ℂ) + (T : ℂ) * I ∈ Metric.ball z₀ (13 / 8) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : (x : ℂ) + (T : ℂ) * I - z₀ = (((x - 2 : ℝ) : ℂ)) := by
        apply Complex.ext <;> simp [z₀]
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hmem_outer : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (x : ℂ) + (T : ℂ) * I ∈ Metric.ball z₀ (7 / 4) := fun x hx ↦
      Metric.ball_subset_ball (by norm_num) (hmem_ball x hx)
    have hne_g : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2, g ((x : ℂ) + (T : ℂ) * I) ≠ 0 := fun x hx ↦
      hg_ne _ (Metric.ball_subset_closedBall (hmem_ball x hx))
    exact Complex.continuous_im.comp_continuousOn
      ((hdg_cont.comp hpath.continuousOn hmem_outer).div
        (hg_cont.comp hpath.continuousOn hmem_outer) hne_g)
  have hcont_zs : ContinuousOn (fun x : ℝ ↦
      ((zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ))).sum).im)
      (Set.uIcc (1 / 2 : ℝ) 2) :=
    list_sum_inv_im_continuousOn T zs hρ_im_ne
  have hint_zeta_eq :
      ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) / riemannZeta ((x : ℂ) + (T : ℂ) * I)).im =
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ),
          ((zs.map (fun ρ ↦ (1 : ℂ) / ((x : ℂ) + (T : ℂ) * I - ρ))).sum).im) +
        (∫ x in (1 / 2 : ℝ)..(2 : ℝ),
          (deriv g ((x : ℂ) + (T : ℂ) * I) / g ((x : ℂ) + (T : ℂ) * I)).im) := by
    rw [← intervalIntegral.integral_add hcont_zs.intervalIntegrable hcont_g.intervalIntegrable]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hzeta_split x hx, Complex.add_im]
  have hint_zeta_bd :
      |∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) / riemannZeta ((x : ℂ) + (T : ℂ) * I)).im| ≤
        (3 / 2 : ℝ) * (C_ld * Real.log T) + Real.pi * (C_j * Real.log T) := by
    rw [hint_zeta_eq]
    exact (abs_add_le _ _).trans (by linarith [hint_zs_bd, hint_g_bd])
  have harg2_bd : |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg| ≤
      (Real.pi / Real.log 2) * Real.log T := by
    have hpi : |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg| ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    calc
      |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg| ≤ Real.pi * 1 := by linarith
      _ ≤ Real.pi * ((1 / Real.log 2) * Real.log T) :=
        mul_le_mul_of_nonneg_left hone_le_logT Real.pi_pos.le
      _ = (Real.pi / Real.log 2) * Real.log T := by ring
  unfold argumentSApprox
  rw [abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  have hdiff_bd : |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg -
      ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) / riemannZeta ((x : ℂ) + (T : ℂ) * I)).im| ≤
      (Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) * Real.log T := by
    have htri := abs_sub ((riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg)
      (∫ x in (1 / 2 : ℝ)..(2 : ℝ),
        (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) / riemannZeta ((x : ℂ) + (T : ℂ) * I)).im)
    linarith [htri, harg2_bd, hint_zeta_bd]
  calc
    1 / Real.pi * |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg -
        ∫ x in (1 / 2 : ℝ)..(2 : ℝ),
          (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
            riemannZeta ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ 1 / Real.pi * ((Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) *
            Real.log T) := mul_le_mul_of_nonneg_left hdiff_bd (by positivity)
    _ ≤ C * Real.log T := by
      dsimp only [C]
      have h1 : (1 / Real.pi) * (Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) ≤
          (1 / Real.pi) * (Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) + 1 := by linarith
      calc
        1 / Real.pi * ((Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) * Real.log T)
            = ((1 / Real.pi) * (Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j)) *
                Real.log T := by ring
        _ ≤ ((1 / Real.pi) * (Real.pi / Real.log 2 + (3 / 2) * C_ld + Real.pi * C_j) + 1) *
              Real.log T := mul_le_mul_of_nonneg_right h1 hlogT_pos.le

private lemma exists_right_nhd_no_zero_ordinate (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo T (T + δ), ¬ IsZeroOrdinate t := by
  classical
  let S : Finset ℂ :=
    (criticalStripZeros_strip_finite T (T + 1)).toFinset.filter (fun ρ : ℂ ↦ T < ρ.im)
  by_cases hne : S.Nonempty
  · let D : Finset ℝ := S.image (fun ρ : ℂ ↦ ρ.im - T)
    have hD_ne : D.Nonempty := hne.image _
    let m : ℝ := D.min' hD_ne
    have hm_mem : m ∈ D := D.min'_mem hD_ne
    rcases Finset.mem_image.mp hm_mem with ⟨ρ₀, hρ₀, hm_eq⟩
    have hm_pos : 0 < m := by
      have := (Finset.mem_filter.mp hρ₀).2
      linarith
    refine ⟨min 1 m, lt_min zero_lt_one hm_pos, fun t ht ⟨ρ, hρ_crit, hρ_im⟩ ↦ ?_⟩
    have hρS : ρ ∈ S := by
      refine Finset.mem_filter.mpr ⟨(criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mpr
        ⟨hρ_crit, ⟨?_, ?_⟩⟩, ?_⟩
      · linarith [ht.1]
      · have hle1 : min 1 m ≤ 1 := min_le_left 1 m
        linarith [ht.2]
      · linarith [ht.1]
    have hm_le : m ≤ ρ.im - T := Finset.min'_le D (ρ.im - T) (Finset.mem_image.mpr ⟨ρ, hρS, rfl⟩)
    have hlt_m : t - T < m := lt_of_lt_of_le (by linarith [ht.2]) (min_le_right 1 m)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, zero_lt_one, fun t ht ⟨ρ, hρ_crit, hρ_im⟩ ↦ ?_⟩
    have hρS : ρ ∈ S := Finset.mem_filter.mpr ⟨(criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mpr
      ⟨hρ_crit, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, by linarith [ht.1]⟩
    rw [hne] at hρS
    simp at hρS

private lemma continuousAt_stirlingMain {T : ℝ} (hT : 0 < T) :
    ContinuousAt (fun t : ℝ ↦
      (1 / Real.pi) * ((-1 / 2 : ℂ) + (t : ℂ) * I).arg +
        (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).im -
        (t / (2 * Real.pi)) * Real.log Real.pi) T := by
  have hslit1 : (-1 / 2 : ℂ) + (T : ℂ) * I ∈ Complex.slitPlane := by
    right; simp [hT.ne']
  have hc_line1 : Continuous (fun t : ℝ ↦ (-1 / 2 : ℂ) + (t : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have harg_cont : ContinuousAt (fun t : ℝ ↦ ((-1 / 2 : ℂ) + (t : ℂ) * I).arg) T :=
    ContinuousAt.comp (f := fun t : ℝ ↦ (-1 / 2 : ℂ) + (t : ℂ) * I)
      (Complex.continuousAt_arg hslit1) hc_line1.continuousAt
  have hst_d : HasDerivAt (fun t : ℝ ↦ stirlingLogGamma ((5 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I))
      (AnalyticNumberTheory.AnalyticTools.Gamma.digamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I) *
        ((1 / 2 : ℂ) * I)) T := by
    have hslit2 : (5 / 4 : ℂ) + ((T : ℂ) / 2) * I ∈ Complex.slitPlane := by
      left; simp
    have hlin : HasDerivAt (fun w : ℂ ↦ (5 / 4 : ℂ) + (w / 2) * I) ((1 / 2 : ℂ) * I) (T : ℂ) :=
      ((((hasDerivAt_id (T : ℂ)).div_const (2 : ℂ)).mul_const I).const_add (5 / 4 : ℂ)).congr_deriv
        (by ring)
    exact ((((hasDerivAt_stirlingLogGamma hslit2).comp (T : ℂ) hlin).comp_ofReal).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t ↦ by dsimp only [Function.comp_def]; push_cast; rfl)).congr_deriv
      (by push_cast; rfl)
  have hst_cont : ContinuousAt (fun t : ℝ ↦
      (stirlingLogGamma ((5 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).im) T :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt T hst_d).continuousAt
  exact ((continuousAt_const.mul harg_cont).add (continuousAt_const.mul hst_cont)).sub
    ((continuousAt_id.div_const (2 * Real.pi)).mul continuousAt_const)

/-- **Exact Riemann–von Mangoldt identity** for all `T > 0` (including zero ordinates):
`zeroCountUpTo T = (1 / π) * arg (-1/2 + iT) + (1 / π) * Im stirlingLogGamma (5/4 + iT/2) - (T / (2π)) * log π + argumentS T`. -/
theorem zeroCountUpTo_eq_stirling_add_argumentS {T : ℝ} (hT : 0 < T) :
    (zeroCountUpTo T : ℝ) =
      (1 / Real.pi) * ((-1 / 2 : ℂ) + (T : ℂ) * I).arg +
        (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi + argumentS T := by
  let mainTerm : ℝ → ℝ := fun t ↦
    (1 / Real.pi) * ((-1 / 2 : ℂ) + (t : ℂ) * I).arg +
      (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).im -
      (t / (2 * Real.pi)) * Real.log Real.pi
  obtain ⟨δ, hδ_pos, hδ_no⟩ := exists_right_nhd_no_zero_ordinate T
  have hev_eq : ∀ᶠ t : ℝ in 𝓝[>] T,
      argumentSApprox t = (zeroCountUpTo T : ℝ) - mainTerm t := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ_pos, fun t ht ht_gt ↦ ?_⟩
    have ht_mem : t ∈ Set.Ioo T (T + δ) := ⟨ht_gt, by
      rw [Real.dist_eq, abs_lt] at ht; linarith⟩
    have ht_pos : 0 < t := hT.trans ht_mem.1
    have ht_no : ¬ IsZeroOrdinate t := hδ_no t ht_mem
    have hcnt_eq : zeroCountUpTo t = zeroCountUpTo T := by
      classical
      rw [zeroCountUpTo_eq_sum t, zeroCountUpTo_eq_sum T]
      refine Finset.sum_congr (by
        ext ρ
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hm, him⟩
          have hs := (criticalStripZeros_strip_finite 0 t).mem_toFinset.mp hm
          have hleT : ρ.im ≤ T := by
            by_contra! hgt
            exact hδ_no ρ.im ⟨hgt, hs.2.2.trans_lt ht_mem.2⟩ ⟨ρ, hs.1, rfl⟩
          exact ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr ⟨hs.1, ⟨hs.2.1, hleT⟩⟩, him⟩
        · rintro ⟨hm, him⟩
          have hs := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp hm
          exact ⟨(criticalStripZeros_strip_finite 0 t).mem_toFinset.mpr
            ⟨hs.1, ⟨hs.2.1, hs.2.2.trans ht_mem.1.le⟩⟩, him⟩) fun _ _ ↦ rfl
    have hexact := zeroCountUpTo_eq_stirling_add_argumentSApprox ht_pos ht_no
    dsimp only [mainTerm]
    rw [hcnt_eq] at hexact
    linarith
  have htend_main : Tendsto mainTerm (𝓝[>] T) (𝓝 (mainTerm T)) :=
    (continuousAt_stirlingMain hT).tendsto.mono_left nhdsWithin_le_nhds
  have htend_S : Tendsto argumentSApprox (𝓝[>] T) (𝓝 ((zeroCountUpTo T : ℝ) - mainTerm T)) :=
    (tendsto_const_nhds.sub htend_main).congr' (hev_eq.mono fun _ h ↦ h.symm)
  have hS_eq : argumentS T = (zeroCountUpTo T : ℝ) - mainTerm T := by
    unfold argumentS
    exact htend_S.limUnder_eq
  dsimp only [mainTerm] at hS_eq
  linarith

private lemma argumentSApprox_tendsto_argumentS {T : ℝ} (hT : 0 < T) :
    Tendsto argumentSApprox (𝓝[>] T) (𝓝 (argumentS T)) := by
  let mainTerm : ℝ → ℝ := fun t ↦
    (1 / Real.pi) * ((-1 / 2 : ℂ) + (t : ℂ) * I).arg +
      (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).im -
      (t / (2 * Real.pi)) * Real.log Real.pi
  obtain ⟨δ, hδ_pos, hδ_no⟩ := exists_right_nhd_no_zero_ordinate T
  have hev_eq : ∀ᶠ t : ℝ in 𝓝[>] T,
      argumentSApprox t = (zeroCountUpTo T : ℝ) - mainTerm t := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ_pos, fun t ht ht_gt ↦ ?_⟩
    have ht_mem : t ∈ Set.Ioo T (T + δ) := ⟨ht_gt, by
      rw [Real.dist_eq, abs_lt] at ht; linarith⟩
    have ht_pos : 0 < t := hT.trans ht_mem.1
    have ht_no : ¬ IsZeroOrdinate t := hδ_no t ht_mem
    have hcnt_eq : zeroCountUpTo t = zeroCountUpTo T := by
      classical
      rw [zeroCountUpTo_eq_sum t, zeroCountUpTo_eq_sum T]
      refine Finset.sum_congr (by
        ext ρ
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hm, him⟩
          have hs := (criticalStripZeros_strip_finite 0 t).mem_toFinset.mp hm
          have hleT : ρ.im ≤ T := by
            by_contra! hgt
            exact hδ_no ρ.im ⟨hgt, hs.2.2.trans_lt ht_mem.2⟩ ⟨ρ, hs.1, rfl⟩
          exact ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr ⟨hs.1, ⟨hs.2.1, hleT⟩⟩, him⟩
        · rintro ⟨hm, him⟩
          have hs := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp hm
          exact ⟨(criticalStripZeros_strip_finite 0 t).mem_toFinset.mpr
            ⟨hs.1, ⟨hs.2.1, hs.2.2.trans ht_mem.1.le⟩⟩, him⟩) fun _ _ ↦ rfl
    have hexact := zeroCountUpTo_eq_stirling_add_argumentSApprox ht_pos ht_no
    dsimp only [mainTerm]
    rw [hcnt_eq] at hexact
    linarith
  have htend_main : Tendsto mainTerm (𝓝[>] T) (𝓝 (mainTerm T)) :=
    (continuousAt_stirlingMain hT).tendsto.mono_left nhdsWithin_le_nhds
  have hS_eq : argumentS T = (zeroCountUpTo T : ℝ) - mainTerm T := by
    have h := zeroCountUpTo_eq_stirling_add_argumentS hT
    dsimp only [mainTerm]
    linarith
  rw [hS_eq]
  exact (tendsto_const_nhds.sub htend_main).congr' (hev_eq.mono fun _ h ↦ h.symm)

/-- When `T > 0` is not a zero ordinate, `argumentS T` agrees with `argumentSApprox T`. -/
theorem argumentS_eq_argumentSApprox_of_not_isZeroOrdinate {T : ℝ} (hT : 0 < T)
    (hno : ¬ IsZeroOrdinate T) :
    argumentS T = argumentSApprox T := by
  classical
  let S : Finset ℂ := (criticalStripZeros_strip_finite (T - 1) (T + 1)).toFinset
  have hδ₁ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ δ₁ ≤ T ∧
      ∀ t ∈ Set.Ioo (T - δ₁) (T + δ₁), ¬ IsZeroOrdinate t := by
    by_cases hne : S.Nonempty
    · let D : Finset ℝ := S.image (fun ρ : ℂ ↦ |ρ.im - T|)
      let m : ℝ := D.min' (hne.image _)
      rcases Finset.mem_image.mp (D.min'_mem (hne.image _)) with ⟨ρ₀, hρ₀, hm_eq⟩
      have hm_pos : 0 < m := by
        have hcrit := ((criticalStripZeros_strip_finite (T - 1) (T + 1)).mem_toFinset.mp hρ₀).1
        have hneT : ρ₀.im ≠ T := fun h ↦ hno ⟨ρ₀, hcrit, h⟩
        dsimp only [m]
        rw [← hm_eq]
        exact abs_pos.mpr (sub_ne_zero.mpr hneT)
      refine ⟨min (min 1 T) m, lt_min (lt_min zero_lt_one hT) hm_pos,
        (min_le_left _ _).trans (min_le_left _ _),
        (min_le_left _ _).trans (min_le_right _ _), fun t ht ⟨ρ, hρ_crit, hρ_im⟩ ↦ ?_⟩
      have hρS : ρ ∈ S := (criticalStripZeros_strip_finite (T - 1) (T + 1)).mem_toFinset.mpr
        ⟨hρ_crit, ⟨by linarith [ht.1, min_le_left (min 1 T) m, min_le_left (1 : ℝ) T],
          by linarith [ht.2, min_le_left (min 1 T) m, min_le_left (1 : ℝ) T]⟩⟩
      have hm_le : m ≤ |ρ.im - T| :=
        Finset.min'_le D |ρ.im - T| (Finset.mem_image.mpr ⟨ρ, hρS, rfl⟩)
      have hlt_m : |t - T| < m := by
        rw [abs_lt]
        have hm1 : min (min 1 T) m ≤ m := min_le_right _ _
        constructor <;> linarith [ht.1, ht.2]
      rw [hρ_im] at hm_le
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨min 1 T, lt_min zero_lt_one hT, min_le_left _ _, min_le_right _ _,
        fun t ht ⟨ρ, hρ_crit, hρ_im⟩ ↦ ?_⟩
      have hρS : ρ ∈ S := (criticalStripZeros_strip_finite (T - 1) (T + 1)).mem_toFinset.mpr
        ⟨hρ_crit, ⟨by linarith [ht.1, min_le_left (1 : ℝ) T],
          by linarith [ht.2, min_le_left (1 : ℝ) T]⟩⟩
      rw [hne] at hρS
      simp at hρS
  obtain ⟨δ₁, hδ₁_pos, _, hδ₁_le_T, hδ₁_no⟩ := hδ₁
  let δ₂ : ℝ := δ₁ / 2
  have hδ₂_pos : 0 < δ₂ := half_pos hδ₁_pos
  let K_box : Set (ℝ × ℝ) := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (T - δ₂) (T + δ₂)
  let F : ℝ × ℝ → ℝ := fun p ↦
    (deriv riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I) /
      riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I)).im
  have hbox_prop : ∀ p ∈ K_box, (p.1 : ℂ) + (p.2 : ℂ) * I ≠ 1 ∧
      riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I) ≠ 0 := by
    intro p hp
    have hp1 : p.1 ∈ Set.Icc (1 / 2 : ℝ) 2 := hp.1
    have hp2 : p.2 ∈ Set.Icc (T - δ₂) (T + δ₂) := hp.2
    have hp2_pos : 0 < p.2 := by dsimp only [δ₂] at hp2; linarith [hp2.1, hδ₁_le_T]
    have hp_ne1 : (p.1 : ℂ) + (p.2 : ℂ) * I ≠ 1 := fun h ↦ by
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hp2_no : ¬ IsZeroOrdinate p.2 :=
      hδ₁_no p.2 ⟨by dsimp only [δ₂] at hp2; linarith [hp2.1],
        by dsimp only [δ₂] at hp2; linarith [hp2.2]⟩
    exact ⟨hp_ne1, riemannZeta_ne_zero_on_right_strip hp2_pos hp2_no (by linarith [hp1.1])⟩
  have hz_diff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
    (differentiableAt_riemannZeta hw).differentiableWithinAt
  have hdz_cont : ContinuousOn (deriv riemannZeta) {w : ℂ | w ≠ 1} :=
    ((hz_diff.analyticOnNhd isOpen_ne).deriv).continuousOn
  have hF_cont : ContinuousOn F K_box := by
    have hmap : Continuous fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * I :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hnum_cont : ContinuousOn (fun p : ℝ × ℝ ↦
        deriv riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I)) K_box :=
      hdz_cont.comp hmap.continuousOn fun p hp ↦ (hbox_prop p hp).1
    have hden_cont : ContinuousOn (fun p : ℝ × ℝ ↦
        riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I)) K_box :=
      hz_diff.continuousOn.comp hmap.continuousOn fun p hp ↦ (hbox_prop p hp).1
    exact Complex.continuous_im.comp_continuousOn
      (hnum_cont.div hden_cont fun p hp ↦ (hbox_prop p hp).2)
  have hK_box_cpt : IsCompact K_box := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM_bd⟩ := hK_box_cpt.exists_bound_of_continuousOn hF_cont
  have htend_int : Tendsto (fun t : ℝ ↦ ∫ x in (1 / 2 : ℝ)..(2 : ℝ), F (x, t))
      (𝓝[>] T) (𝓝 (∫ x in (1 / 2 : ℝ)..(2 : ℝ), F (x, T))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M) ?_ ?_
      intervalIntegrable_const ?_
    · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨δ₂, hδ₂_pos, fun t ht _ ↦ ?_⟩
      have ht_mem : t ∈ Set.Icc (T - δ₂) (T + δ₂) := by
        rw [Real.dist_eq, abs_lt] at ht
        exact ⟨by linarith, by linarith⟩
      have hslice : Continuous fun x : ℝ ↦ (x, t) := continuous_id.prodMk continuous_const
      have hcont_x : ContinuousOn (fun x : ℝ ↦ F (x, t)) (Set.uIcc (1 / 2 : ℝ) 2) := by
        refine hF_cont.comp hslice.continuousOn fun x hx ↦ ?_
        rw [Set.uIcc_of_le (by norm_num)] at hx
        exact ⟨hx, ht_mem⟩
      exact (hcont_x.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨δ₂, hδ₂_pos, fun t ht _ ↦ ?_⟩
      refine ae_of_all _ fun x hx ↦ ?_
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have ht_mem : t ∈ Set.Icc (T - δ₂) (T + δ₂) := by
        rw [Real.dist_eq, abs_lt] at ht
        exact ⟨by linarith, by linarith⟩
      exact hM_bd (x, t) ⟨⟨hx.1.le, hx.2⟩, ht_mem⟩
    · refine ae_of_all _ fun x hx ↦ ?_
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have hpt : (x : ℂ) + (T : ℂ) * I ≠ 1 ∧ riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
        hbox_prop (x, T) ⟨⟨hx.1.le, hx.2⟩, by linarith, by linarith⟩
      have hpath_t : ContinuousAt (fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * I) T :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      have hd_t : ContinuousAt (fun t : ℝ ↦ deriv riemannZeta ((x : ℂ) + (t : ℂ) * I)) T :=
        ContinuousAt.comp (f := fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * I)
          (hdz_cont.continuousAt (isOpen_ne.mem_nhds hpt.1)) hpath_t
      have hz_t : ContinuousAt (fun t : ℝ ↦ riemannZeta ((x : ℂ) + (t : ℂ) * I)) T :=
        ContinuousAt.comp (f := fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * I)
          (hz_diff.continuousOn.continuousAt (isOpen_ne.mem_nhds hpt.1)) hpath_t
      dsimp only [F]
      exact ((Complex.continuous_im.continuousAt.comp
        (f := fun t : ℝ ↦ deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) /
          riemannZeta ((x : ℂ) + (t : ℂ) * I))
        (hd_t.div hz_t hpt.2)).tendsto.mono_left nhdsWithin_le_nhds)
  have harg_cont : ContinuousAt (fun t : ℝ ↦ (riemannZeta ((2 : ℂ) + (t : ℂ) * I)).arg) T := by
    have hslit : riemannZeta ((2 : ℂ) + (T : ℂ) * I) ∈ Complex.slitPlane := by
      left; linarith [riemannZeta_two_add_mul_I_re_ge T]
    have hzc : ContinuousAt (fun t : ℝ ↦ riemannZeta ((2 : ℂ) + (t : ℂ) * I)) T := by
      have hz_at : ContinuousAt riemannZeta ((2 : ℂ) + (T : ℂ) * I) :=
        (differentiableAt_riemannZeta (fun h ↦ by
          have := congrArg Complex.re h; simp at this)).continuousAt
      exact ContinuousAt.comp (f := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I) hz_at
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact ContinuousAt.comp (f := fun t : ℝ ↦ riemannZeta ((2 : ℂ) + (t : ℂ) * I))
      (Complex.continuousAt_arg hslit) hzc
  have htend_approx : Tendsto argumentSApprox (𝓝[>] T) (𝓝 (argumentSApprox T)) := by
    have h1 : Tendsto (fun t : ℝ ↦ (riemannZeta ((2 : ℂ) + (t : ℂ) * I)).arg) (𝓝[>] T)
        (𝓝 (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg) :=
      harg_cont.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_const_nhds.mul (h1.sub htend_int)
  exact tendsto_nhds_unique (argumentSApprox_tendsto_argumentS hT) htend_approx

/-- **Backlund–Jensen `O(log T)` bound** on `argumentS T` for all `T ≥ 2` (unconditionally,
including zero ordinates). -/
theorem argumentS_abs_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → |argumentS T| ≤ C * Real.log T := by
  obtain ⟨C, hC_pos, hC_bd⟩ := argumentSApprox_abs_le_log
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  obtain ⟨δ, hδ_pos, hδ_no⟩ := exists_right_nhd_no_zero_ordinate T
  have hev_bd : ∀ᶠ t : ℝ in 𝓝[>] T, |argumentSApprox t| ≤ C * Real.log t := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ_pos, fun t ht ht_gt ↦ ?_⟩
    have ht_mem : t ∈ Set.Ioo T (T + δ) := ⟨ht_gt, by
      rw [Real.dist_eq, abs_lt] at ht; linarith⟩
    exact hC_bd t (hT.trans ht_mem.1.le) (hδ_no t ht_mem)
  have htend_abs : Tendsto (fun t : ℝ ↦ |argumentSApprox t|) (𝓝[>] T) (𝓝 |argumentS T|) :=
    (argumentSApprox_tendsto_argumentS hT_pos).abs
  have htend_rhs : Tendsto (fun t : ℝ ↦ C * Real.log t) (𝓝[>] T) (𝓝 (C * Real.log T)) :=
    tendsto_const_nhds.mul
      ((Real.continuousAt_log hT_pos.ne').tendsto.mono_left nhdsWithin_le_nhds)
  exact le_of_tendsto_of_tendsto htend_abs htend_rhs hev_bd

/-- **Explicit Riemann–von Mangoldt formula**: for all `T ≥ 2`,
`zeroCountUpTo T = (T / (2π)) * log (T / (2πe)) + 7/8 + argumentS T + O(1 / T)`. -/
theorem riemannVonMangoldt_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCountUpTo T : ℝ) -
          ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) +
            7 / 8 + argumentS T)| ≤ C / T := by
  obtain ⟨C, hC_pos, hbd⟩ := gamma_five_quarters_add_arg_asymptotic
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  have h_id := zeroCountUpTo_eq_stirling_add_argumentS hT_pos
  have hsub : (zeroCountUpTo T : ℝ) -
      ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) +
        7 / 8 + argumentS T) =
      (1 / Real.pi) * (stirlingLogGamma ((5 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        (T / (2 * Real.pi)) * Real.log Real.pi +
        (1 / Real.pi) * ((-1 / 2 : ℂ) + (T : ℂ) * I).arg - (thetaMain T + 7 / 8) := by
    rw [h_id, thetaMain]
    ring
  rw [hsub]
  exact hbd T hT

/-- **Riemann–von Mangoldt asymptotic formula**: there exists `C > 0` such that for all `T ≥ 2`,
`|zeroCountUpTo T - ((T / (2 * π)) * log (T / (2 * π * e)) + 7 / 8)| ≤ C * log T`. -/
theorem riemannVonMangoldt_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCountUpTo T : ℝ) -
          ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8)| ≤
        C * Real.log T := by
  obtain ⟨C₁, hC₁_pos, hbd1⟩ := riemannVonMangoldt_explicit
  obtain ⟨C₂, hC₂_pos, hbd2⟩ := argumentS_abs_le_log
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₁ / (2 * Real.log 2) + C₂, by positivity, fun T hT ↦ ?_⟩
  have h1 := hbd1 T hT
  have h2 := hbd2 T hT
  have htri : |(zeroCountUpTo T : ℝ) -
      ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8)| ≤
      C₁ / T + C₂ * Real.log T := by
    have hsplit : (zeroCountUpTo T : ℝ) -
        ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8) =
        ((zeroCountUpTo T : ℝ) -
          ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) +
            7 / 8 + argumentS T)) + argumentS T := by ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hC1_le : C₁ / T ≤ (C₁ / (2 * Real.log 2)) * Real.log T := by
    have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have hinv : C₁ / T ≤ C₁ / 2 := div_le_div_of_nonneg_left hC₁_pos.le (by norm_num) hT
    calc
      C₁ / T ≤ C₁ / 2 := hinv
      _ = (C₁ / (2 * Real.log 2)) * Real.log 2 := by
        field_simp [hlog2_pos.ne']
      _ ≤ (C₁ / (2 * Real.log 2)) * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
  calc
    |(zeroCountUpTo T : ℝ) -
        ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8)|
        ≤ C₁ / T + C₂ * Real.log T := htri
    _ ≤ (C₁ / (2 * Real.log 2)) * Real.log T + C₂ * Real.log T :=
      add_le_add hC1_le le_rfl
    _ = (C₁ / (2 * Real.log 2) + C₂) * Real.log T := by ring

end AnalyticNumberTheory.RiemannZeta





