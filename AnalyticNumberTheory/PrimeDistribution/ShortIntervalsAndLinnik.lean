import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Short Intervals, Zero-Density Estimates, Bombieri–Vinogradov, and Linnik's Theorem

This file develops the prime-distribution deductions around zero-density estimates, short
intervals, the Bombieri–Vinogradov theorem, and Linnik's theorem in
`AnalyticNumberTheory.PrimeDistribution`:

1. **Zero-density counting function**: defines `zeroDensityN σ T` counting nontrivial zeros of
   `riemannZeta` with `σ ≤ Re ρ < 1` and `0 < Im ρ ≤ T`, proves finiteness via `xi` and
   `Jensen.zeroSet_finite`, establishes monotonicity/antitonicity and boundary vanishing, and
   proves the unconditional Jensen upper bound `zeroDensityN σ T ≤ C * T * log (T + 2)`.
2. **Hoheisel–Ingham short-interval deduction**: defines `ZeroDensityHypothesis`,
   `TruncatedExplicitFormulaHypothesis`, and `SuperLogZeroFreeHypothesis`, and proves
   `psi_shortInterval_isEquivalent_of_zeroDensity` (`ψ(x + x^θ) - ψ(x) ~ x^θ`) together with
   `theta_shortInterval_isEquivalent_of_zeroDensity` and `eventually_exists_prime_shortInterval`
   for `1 / 2 < θ < 1`.
3. **Bombieri–Vinogradov theorem**: defines `BombieriVinogradovStatement`, deduces the `thetaAP`
   version `bombieriVinogradov_thetaAP`, and proves the primitive character reduction
   `bombieriVinogradov_primitive_char_reduction` via character orthogonality and conductor
   factorization.
4. **Linnik's theorem**: defines `LinnikStatement`, `LogFreeZeroDensityData`,
   `DeuringHeilbronnData`, and `LinnikSmoothedHypothesis`, and proves
   `linnik_of_logFreeZeroDensity_and_deuringHeilbronn` covering both the non-exceptional and
   Siegel–Landau exceptional-zero regimes.
-/

noncomputable section

open Nat hiding log
open Finset MeasureTheory Set Filter Asymptotics Complex
open scoped Topology ArithmeticFunction.vonMangoldt ComplexConjugate Classical
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.RiemannZeta
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-! ### Zero-Density Counting Function -/

/-- The set of nontrivial zeros `ρ` of `riemannZeta` in the half-strip `σ ≤ Re ρ < 1` and
`0 < Im ρ ≤ T`. -/
def zeroDensitySet (σ T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Every element of `zeroDensitySet σ T` automatically satisfies `0 < ρ.re < 1` and is a zero of
the completed zeta function `xi`. -/
theorem mem_zeroDensitySet_iff_xi {σ T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroDensitySet σ T ↔ xi ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  constructor
  · rintro ⟨hz, hσ, hlt, him0, himT⟩
    have hpos : 0 < ρ.re := by
      by_contra hle
      push Not at hle
      obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos_bridge hle).mp hz
      have him : ρ.im = 0 := by
        rw [hn]
        simp
      linarith
    exact ⟨xi_eq_zero_iff.mpr ⟨hz, hpos, hlt⟩, hσ, him0, himT⟩
  · rintro ⟨hxi, hσ, him0, himT⟩
    obtain ⟨hz, _, hlt⟩ := xi_eq_zero_iff.mp hxi
    exact ⟨hz, hσ, hlt, him0, himT⟩

/-- Embedding `zeroDensitySet σ T` inside `Jensen.zeroSet xi 1 (max T 0 + 1)`. -/
theorem zeroDensitySet_subset_zeroSet (σ T : ℝ) :
    zeroDensitySet σ T ⊆ zeroSet xi 1 (max T 0 + 1) := by
  intro ρ hρ
  obtain ⟨hxi, _, him0, himT⟩ := mem_zeroDensitySet_iff_xi.mp hρ
  obtain ⟨_, hpos, hlt⟩ := xi_eq_zero_iff.mp hxi
  rw [mem_zeroSet, Metric.mem_closedBall, dist_eq_norm]
  have hre_sq : (ρ - 1).re ^ 2 ≤ 1 := by
    have hre_eq : (ρ - 1).re = ρ.re - 1 := by simp
    rw [hre_eq]
    have hre1 : -1 < ρ.re - 1 := by linarith
    have hre2 : ρ.re - 1 < 0 := by linarith
    nlinarith
  have him_sq : (ρ - 1).im ^ 2 ≤ max T 0 ^ 2 := by
    have him_eq : (ρ - 1).im = ρ.im := by simp
    rw [him_eq]
    have hle : ρ.im ≤ max T 0 := himT.trans (le_max_left T 0)
    nlinarith
  have hnorm_sq : ‖ρ - 1‖ ^ 2 ≤ (max T 0 + 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hT0 : 0 ≤ max T 0 := le_max_right T 0
    nlinarith
  have hR0 : 0 ≤ max T 0 + 1 := by positivity
  refine ⟨?_, hxi⟩
  nlinarith [norm_nonneg (ρ - 1), hR0]

/-- Finiteness of `zeroDensitySet σ T` via `xi` and `Jensen.zeroSet_finite`. -/
theorem zeroDensitySet_finite (σ T : ℝ) : (zeroDensitySet σ T).Finite := by
  have hr : 0 ≤ max T 0 + 1 := by positivity
  have hfin := zeroSet_finite (z₀ := (1 : ℂ)) hr
    (analyticOnNhd_xi.mono (Set.subset_univ _)) (by simp : xi 1 ≠ 0)
  exact hfin.subset (zeroDensitySet_subset_zeroSet σ T)

/-- Finite set of nontrivial zeros of `riemannZeta` in `σ ≤ Re ρ < 1` and `0 < Im ρ ≤ T`. -/
def zeroDensityFinset (σ T : ℝ) : Finset ℂ :=
  (zeroDensitySet_finite σ T).toFinset

/-- Membership characterization for `zeroDensityFinset σ T`. -/
@[simp]
theorem mem_zeroDensityFinset {σ T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroDensityFinset σ T ↔
      riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  simp [zeroDensityFinset, zeroDensitySet]

/-- The zero-density counting function `N(σ, T)`: number of nontrivial zeros of `riemannZeta`
with `σ ≤ Re ρ < 1` and `0 < Im ρ ≤ T`. -/
def zeroDensityN (σ T : ℝ) : ℕ :=
  (zeroDensitySet σ T).ncard

/-- `zeroDensityN σ T` equals the cardinality of `zeroDensityFinset σ T`. -/
theorem zeroDensityN_eq_card (σ T : ℝ) :
    zeroDensityN σ T = (zeroDensityFinset σ T).card := by
  rw [zeroDensityN, zeroDensityFinset, Set.ncard_eq_toFinset_card _ (zeroDensitySet_finite σ T)]

/-- Explicit `Finset` existence theorem `zeroDensityN_finset`: the zero set in `[σ, 1) × (0, T]`
forms a `Finset` whose cardinality is `zeroDensityN σ T`. -/
theorem zeroDensityN_finset (σ T : ℝ) :
    ∃ S : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ S ↔ riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T) ∧
      zeroDensityN σ T = S.card :=
  ⟨zeroDensityFinset σ T, fun _ => mem_zeroDensityFinset, zeroDensityN_eq_card σ T⟩

/-- Monotonicity of `zeroDensityN σ T` in the height `T`. -/
theorem zeroDensityN_mono_T {σ T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    zeroDensityN σ T₁ ≤ zeroDensityN σ T₂ := by
  refine Set.ncard_le_ncard (fun ρ hρ => ?_) (zeroDensitySet_finite σ T₂)
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2.trans hT⟩

/-- Antitonicity of `zeroDensityN σ T` in the abscissa `σ`. -/
theorem zeroDensityN_antitone_sigma {σ₁ σ₂ T : ℝ} (hσ : σ₁ ≤ σ₂) :
    zeroDensityN σ₂ T ≤ zeroDensityN σ₁ T := by
  refine Set.ncard_le_ncard (fun ρ hρ => ?_) (zeroDensitySet_finite σ₁ T)
  exact ⟨hρ.1, hσ.trans hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2⟩

/-- `zeroDensityN σ T = 0` whenever `1 ≤ σ`. -/
theorem zeroDensityN_eq_zero_of_one_le {σ T : ℝ} (hσ : 1 ≤ σ) : zeroDensityN σ T = 0 := by
  have hempty : zeroDensitySet σ T = ∅ := by
    ext ρ
    simp only [zeroDensitySet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, h1, h2, _⟩
    linarith
  simp [zeroDensityN, hempty]

/-- `zeroDensityN σ T = 0` whenever `T ≤ 0`. -/
theorem zeroDensityN_eq_zero_of_nonpos_T {σ T : ℝ} (hT : T ≤ 0) : zeroDensityN σ T = 0 := by
  have hempty : zeroDensitySet σ T = ∅ := by
    ext ρ
    simp only [zeroDensitySet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, _, _, h1, h2⟩
    linarith
  simp [zeroDensityN, hempty]

/-- For `σ ≤ 0`, `zeroDensityN σ T` coincides with `zeroDensityN 0 T`. -/
theorem zeroDensityN_eq_zeroDensityN_zero_of_le_zero {σ T : ℝ} (hσ : σ ≤ 0) :
    zeroDensityN σ T = zeroDensityN 0 T := by
  have hset : zeroDensitySet σ T = zeroDensitySet 0 T := by
    ext ρ
    simp only [mem_zeroDensitySet_iff_xi]
    constructor
    · rintro ⟨hxi, _, him0, himT⟩
      obtain ⟨_, hpos, _⟩ := xi_eq_zero_iff.mp hxi
      exact ⟨hxi, hpos.le, him0, himT⟩
    · rintro ⟨hxi, h0, him0, himT⟩
      exact ⟨hxi, hσ.trans h0, him0, himT⟩
  simp [zeroDensityN, hset]

/-- **Unconditional Jensen upper bound** for `zeroDensityN`:
there exists `C > 0` such that `zeroDensityN σ T ≤ C * T * Real.log (T + 2)` for all `σ : ℝ`
and all `T ≥ 2`. -/
theorem zeroDensityN_le_mul_log :
    ∃ C > 0, ∀ (σ T : ℝ), 2 ≤ T →
      (zeroDensityN σ T : ℝ) ≤ C * T * Real.log (T + 2) := by
  obtain ⟨A, B, hA_pos, hB_pos, hxi_bd⟩ := norm_xi_le_exp_norm_mul_log
  let A₁ : ℝ := max A 1
  have hA₁_pos : 0 < A₁ := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hA₁_ge1 : 1 ≤ A₁ := le_max_right A 1
  have hA_le : A ≤ A₁ := le_max_left A 1
  let C₀ : ℝ := Real.log A₁ + Real.log 2
  have hC₀_pos : 0 < C₀ := add_pos_of_nonneg_of_pos (Real.log_nonneg hA₁_ge1) (Real.log_pos one_lt_two)
  let C : ℝ := (C₀ + 8 * B) / Real.log 2
  have hC_pos : 0 < C := div_pos (by positivity) (Real.log_pos one_lt_two)
  refine ⟨C, hC_pos, fun σ T hT => ?_⟩
  let r : ℝ := T + 1
  let R : ℝ := 2 * r
  have hr_pos : 0 < r := by positivity
  have hrR : r < R := by dsimp [R]; linarith
  have hsub : zeroDensitySet σ T ⊆ zeroSet xi 1 r := by
    have h1 := zeroDensitySet_subset_zeroSet σ T
    rwa [max_eq_left (by linarith : 0 ≤ T)] at h1
  have hcard_le : (zeroDensityN σ T : ℝ) ≤ ((zeroSet xi 1 r).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub
      (zeroSet_finite hr_pos.le (analyticOnNhd_xi.mono (Set.subset_univ _)) (by simp))
  have hlogT2_ge1 : 1 ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  let M : ℝ := A₁ * Real.exp (8 * B * T * Real.log (T + 2))
  have hM_pos : 0 < M := by positivity
  have hsphere : ∀ z ∈ Metric.sphere (1 : ℂ) R, ‖xi z‖ ≤ M := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hz_norm : ‖z‖ ≤ 4 * T := by
      have htri : ‖z‖ ≤ ‖(1 : ℂ)‖ + ‖z - 1‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_add_le (1 : ℂ) (z - 1)
      rw [norm_one, hz] at htri
      dsimp [R, r] at htri
      linarith
    have hz_log : Real.log (‖z‖ + 2) ≤ 2 * Real.log (T + 2) := by
      have harg : ‖z‖ + 2 ≤ (T + 2) ^ 2 := by nlinarith
      calc
        Real.log (‖z‖ + 2) ≤ Real.log ((T + 2) ^ 2) :=
          Real.log_le_log (by positivity) harg
        _ = 2 * Real.log (T + 2) := by rw [Real.log_pow]; norm_cast
    have hexp_le : B * ‖z‖ * Real.log (‖z‖ + 2) ≤ 8 * B * T * Real.log (T + 2) := by
      have hlog_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg z])
      calc
        B * ‖z‖ * Real.log (‖z‖ + 2) ≤ B * (4 * T) * Real.log (‖z‖ + 2) := by gcongr
        _ ≤ B * (4 * T) * (2 * Real.log (T + 2)) := by gcongr
        _ = 8 * B * T * Real.log (T + 2) := by ring
    exact (hxi_bd z).trans (mul_le_mul hA_le (Real.exp_le_exp.mpr hexp_le) (Real.exp_pos _).le hA₁_pos.le)
  have hj := ncard_zeroSet_le_sub_log_div_log hr_pos hrR hM_pos
    (analyticOnNhd_xi.mono (Set.subset_univ _)) (by simp) hsphere
  have hlogM : Real.log M = Real.log A₁ + 8 * B * T * Real.log (T + 2) := by
    dsimp [M]
    rw [Real.log_mul hA₁_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hxi1_norm : ‖xi 1‖ = 1 / 2 := by
    rw [xi_one]
    norm_num
  have hlog_xi1 : -Real.log ‖xi 1‖ = Real.log 2 := by
    rw [hxi1_norm, one_div, Real.log_inv]
    ring
  have hRr : R / r = 2 := by dsimp [R]; field_simp
  rw [hlogM, hRr, sub_eq_add_neg, hlog_xi1] at hj
  have hnum : Real.log A₁ + 8 * B * T * Real.log (T + 2) + Real.log 2 ≤
      (C₀ + 8 * B) * T * Real.log (T + 2) := by
    have hT_ge1 : 1 ≤ T := by linarith
    have hC0_le : C₀ ≤ C₀ * T * Real.log (T + 2) := by
      calc
        C₀ = C₀ * 1 * 1 := by ring
        _ ≤ C₀ * T * Real.log (T + 2) := by gcongr
    dsimp [C₀] at hC0_le ⊢
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    (zeroDensityN σ T : ℝ) ≤ ((zeroSet xi 1 r).ncard : ℝ) := hcard_le
    _ ≤ (Real.log A₁ + 8 * B * T * Real.log (T + 2) + Real.log 2) / Real.log 2 := hj
    _ ≤ ((C₀ + 8 * B) * T * Real.log (T + 2)) / Real.log 2 := by gcongr
    _ = C * T * Real.log (T + 2) := by dsimp [C]; ring

/-! ### Auxiliary Structural Lemmas for Zeta Zeros and Multiplicities -/

private lemma cpow_ofReal_hasDerivAt' {t : ℝ} (ht : 0 < t) (c : ℂ) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hmem : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
  simpa using ((hasDerivAt_id (t : ℂ)).cpow_const hmem).comp_ofReal

private theorem integrableOn_sawtooth_rpow_Ioi {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)) (Set.Ioi 1) := by
  have hpow_int : IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-σ - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul (1 / 2)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hmeas_saw : Measurable fun u : ℝ => (sawtooth u : ℂ) :=
      Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const _)
    have hcont_pow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-(σ : ℂ) - 1)) (Set.Ioi 1) := by
      refine continuousOn_of_forall_continuousAt fun u hu => ?_
      exact (cpow_ofReal_hasDerivAt' (lt_trans zero_lt_one hu) (-(σ : ℂ) - 1)).continuousAt
    exact (hmeas_saw.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
      (hcont_pow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re, ofReal_re, one_re]
    exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)

/-- `riemannZeta` is strictly negative on the open real interval `(0, 1)`. -/
theorem riemannZeta_re_lt_zero_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hs_re : 0 < (σ : ℂ).re := by simp [hσ.1]
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hσ.2]
  rw [riemannZeta_eq_eulerMaclaurin_of_re_pos hs_re hs1]
  have hint_bd :
      ‖∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖ ≤ (1 / 2) / σ := by
    have hdom_int : IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-σ - 1)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith [hσ.1]) zero_lt_one).const_mul (1 / 2)
    have hint := integrableOn_sawtooth_rpow_Ioi hσ.1
    have hmono : ∫ u in Set.Ioi (1 : ℝ), ‖(sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖ ≤
        ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) := by
      refine setIntegral_mono_on hint.norm hdom_int measurableSet_Ioi fun u hu => ?_
      have hu_pos : 0 < u := lt_trans zero_lt_one hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
      simp only [sub_re, neg_re, ofReal_re, one_re]
      exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)
    have heval : ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) = (1 / 2) / σ := by
      rw [integral_const_mul]
      have htend : Tendsto (fun R : ℝ => ∫ u in (1 : ℝ)..R, u ^ (-σ - 1)) atTop
          (𝓝 (∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 1))) :=
        intervalIntegral_tendsto_integral_Ioi 1
          (integrableOn_Ioi_rpow_of_lt (by linarith [hσ.1]) zero_lt_one) tendsto_id
      have hcalc : ∀ R : ℝ, 1 ≤ R → ∫ u in (1 : ℝ)..R, u ^ (-σ - 1) = (1 - R ^ (-σ)) / σ := by
        intro R hR
        rw [integral_rpow (Or.inr ⟨by linarith [hσ.1], fun h => by
          rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
        simp only [Real.one_rpow]
        have hexp : -σ - 1 + 1 = -σ := by ring
        rw [hexp]
        field_simp [hσ.1.ne']
        ring
      have hlim : Tendsto (fun R : ℝ => (1 - R ^ (-σ)) / σ) atTop (𝓝 (1 / σ)) := by
        have hr : Tendsto (fun R : ℝ => R ^ (-σ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hσ.1
        simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hr).div_const σ
      have h1 : ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 1) = 1 / σ :=
        tendsto_nhds_unique htend (hlim.congr' (by
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR; exact (hcalc R hR).symm))
      rw [h1]
      ring
    exact (norm_integral_le_integral_norm _).trans (hmono.trans_eq heval)
  have hmul_bd :
      ‖(σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.1.le]
    calc
      σ * ‖∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)‖
          ≤ σ * ((1 / 2) / σ) := mul_le_mul_of_nonneg_left hint_bd hσ.1.le
      _ = 1 / 2 := mul_div_cancel₀ _ hσ.1.ne'
  have hre_tail :
      -((σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)).re ≤ 1 / 2 :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hmul_bd)
  have h1_lt : ((1 : ℂ) / ((σ : ℂ) - 1)).re < -1 := by
    have heq : (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, Complex.ofReal_re]
    have hneg : σ - 1 < 0 := by linarith [hσ.2]
    rw [div_lt_iff_of_neg hneg]
    linarith [hσ.1]
  have hre_sub :
      (1 / ((σ : ℂ) - 1) + 1 / 2 -
        (σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)).re =
      ((1 : ℂ) / ((σ : ℂ) - 1)).re + 1 / 2 -
        ((σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)).re := by
    simp
  rw [hre_sub]
  linarith [abs_re_le_norm ((σ : ℂ) * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 1)),
    hmul_bd, h1_lt]

/-- `riemannZeta` has no zeros on the open real interval `(0, 1)`. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro h
  have hlt := riemannZeta_re_lt_zero_of_mem_Ioo hσ
  rw [h, zero_re] at hlt
  linarith

/-- Symmetric zero set `{ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}` as a
`Finset`. -/
def zeroDensityFinsetSymmetric (T : ℝ) : Finset ℂ :=
  zeroDensityFinset 0 T ∪ (zeroDensityFinset 0 T).image star

/-- Membership characterization for `zeroDensityFinsetSymmetric T`. -/
@[simp]
theorem mem_zeroDensityFinsetSymmetric {T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroDensityFinsetSymmetric T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h1 | h2
    · obtain ⟨hz, h0, h1, him0, himT⟩ := mem_zeroDensityFinset.mp h1
      have hpos : 0 < ρ.re := (xi_eq_zero_iff.mp (mem_zeroDensitySet_iff_xi.mp ⟨hz, h0, h1, him0, himT⟩).1).2.1
      exact ⟨hz, hpos, h1, abs_le.mpr ⟨by linarith, himT⟩⟩
    · rcases Finset.mem_image.mp h2 with ⟨w, hw, rfl⟩
      obtain ⟨hz, h0, h1, him0, himT⟩ := mem_zeroDensityFinset.mp hw
      have hpos : 0 < w.re := (xi_eq_zero_iff.mp (mem_zeroDensitySet_iff_xi.mp ⟨hz, h0, h1, him0, himT⟩).1).2.1
      have hxi : xi (star w) = 0 := by
        have hxw := xi_eq_zero_iff.mpr ⟨hz, hpos, h1⟩
        change xi (conj w) = 0
        rw [xi_conj, hxw, map_zero]
      obtain ⟨hz', h0', h1'⟩ := xi_eq_zero_iff.mp hxi
      have him : |(star w).im| ≤ T := by
        simpa [abs_neg, abs_of_pos him0] using himT
      exact ⟨hz', h0', h1', him⟩
  · rintro ⟨hz, h0, h1, him⟩
    rcases lt_trichotomy ρ.im 0 with him_neg | him_zero | him_pos
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨star ρ, ?_, by simp⟩)
      have hxi : xi (star ρ) = 0 := by
        have hx := xi_eq_zero_iff.mpr ⟨hz, h0, h1⟩
        change xi (conj ρ) = 0
        rw [xi_conj, hx, map_zero]
      obtain ⟨hz', h0', h1'⟩ := xi_eq_zero_iff.mp hxi
      refine mem_zeroDensityFinset.mpr ⟨hz', h0'.le, h1', ?_, ?_⟩
      · change 0 < -ρ.im; linarith
      · change -ρ.im ≤ T; linarith [abs_le.mp him]
    · exfalso
      have hρ_real : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him_zero])
      rw [hρ_real] at hz
      exact riemannZeta_ne_zero_of_mem_Ioo ⟨h0, h1⟩ hz
    · refine Finset.mem_union_left _ (mem_zeroDensityFinset.mpr ⟨hz, h0.le, h1, him_pos, ?_⟩)
      exact (abs_le.mp him).2

/-- For `0 < ρ.re < 1`, the analytic zero multiplicity of `xi` at `ρ` agrees with that of
`riemannZeta` at `ρ`. -/
theorem analyticOrderNatAt_xi_eq_riemannZeta {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt xi ρ = analyticOrderNatAt riemannZeta ρ := by
  let g : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    isOpen_Ioo.preimage Complex.continuous_re
  have hρ_mem : ρ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} := ⟨h0, h1⟩
  have hev : xi =ᶠ[𝓝 ρ] fun s => g s * riemannZeta s := by
    filter_upwards [hopen.mem_nhds hρ_mem] with s hs
    have hs1 : s ≠ 1 := fun h => by simp [h] at hs
    exact xi_eq_formula_of_re_pos hs.1 hs1
  have hg_an : AnalyticAt ℂ g ρ := by
    have hdiff : DifferentiableOn ℂ g {s : ℂ | 0 < s.re ∧ s.re < 1} := by
      intro s hs
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hG : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
        intro m hm
        have hre := congrArg Complex.re hm
        simp only [div_ofNat_re, neg_re, natCast_re] at hre
        linarith [hs.1]
      have hd1 : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s := by fun_prop
      have hd2 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
        ((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi))
      have hd3 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
        (Complex.differentiableAt_Gamma _ hG).comp s (differentiableAt_id.div_const 2)
      exact ((hd1.mul hd2).mul hd3).differentiableWithinAt
    exact (hdiff.analyticOnNhd hopen) ρ hρ_mem
  have hg_ne : g ρ ≠ 0 := by
    have hpi : (Real.pi : ℂ) ^ (-ρ / 2) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hG : Complex.Gamma (ρ / 2) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp [h0])
    have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
    have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr (fun h => by simp [h] at h1)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hρ0) hρ1) hpi) hG
  have hzeta_an : AnalyticAt ℂ riemannZeta ρ :=
    analyticOn_riemannZeta ρ (fun h => by rw [Set.mem_singleton_iff] at h; rw [h] at h1; norm_num at h1)
  have htop_zeta : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank
        (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (1 : ℂ)).isPreconnected
    have hρ_compl : ρ ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at h1
      simp at h1
    have h2_compl : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      norm_num
    refine (analyticOn_riemannZeta.mono Set.Subset.rfl).analyticOrderAt_ne_top_of_isPreconnected
      hconn h2_compl hρ_compl ?_
    exact (analyticOn_riemannZeta 2 h2_compl).analyticOrderAt_eq_zero.mpr
      (AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by norm_num)) |>.symm ▸
      by simp
  have hord_g : analyticOrderAt g ρ = 0 := hg_an.analyticOrderAt_eq_zero.mpr hg_ne
  have hmul : analyticOrderAt xi ρ = analyticOrderAt g ρ + analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_congr hev]
    exact analyticOrderAt_mul hg_an hzeta_an
  rw [hord_g, zero_add] at hmul
  simp [analyticOrderNatAt, hmul]

private lemma analyticOrderNatAt_conj_conj {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : star z₀ ∈ U) :
    analyticOrderNatAt (fun z => star (f (star z))) z₀ = analyticOrderNatAt f (star z₀) := by
  let g : ℂ → ℂ := fun z => star (f (star z))
  have hf_an : AnalyticAt ℂ f (star z₀) := (hf.analyticOnNhd hU) (star z₀) hz₀
  have hg_an : AnalyticAt ℂ g z₀ := by
    have hU' : IsOpen ((star : ℂ → ℂ) ⁻¹' U) := hU.preimage Complex.continuous_conj
    have hg_diff : DifferentiableOn ℂ g ((star : ℂ → ℂ) ⁻¹' U) := by
      intro z hz
      exact (differentiableAt_conj_conj_iff.mpr
        ((hf (star z) hz).differentiableAt (hU.mem_nhds hz))).differentiableWithinAt
    exact (hg_diff.analyticOnNhd hU') z₀ hz₀
  by_cases htop : analyticOrderAt f (star z₀) = ⊤
  · have htop' : analyticOrderAt g z₀ = ⊤ := by
      rw [analyticOrderAt_eq_top] at htop ⊢
      have htend : Tendsto (star : ℂ → ℂ) (𝓝 z₀) (𝓝 (star z₀)) :=
        Complex.continuous_conj.continuousAt.tendsto
      filter_upwards [htend.eventually htop] with z hz
      exact star_eq_zero.mpr hz
    change (analyticOrderAt g z₀).toNat = (analyticOrderAt f (star z₀)).toNat
    rw [htop, htop']
  · obtain ⟨u, hu_an, hu0, hfu⟩ := hf_an.analyticOrderAt_ne_top.mp htop
    have htop' : analyticOrderAt g z₀ ≠ ⊤ := by
      intro htopg
      rw [analyticOrderAt_eq_top] at htopg
      have hcontra : analyticOrderAt f (star z₀) = ⊤ := by
        rw [analyticOrderAt_eq_top]
        have htend : Tendsto (star : ℂ → ℂ) (𝓝 (star z₀)) (𝓝 z₀) := by
          simpa using Complex.continuous_conj.continuousAt.tendsto (x := star z₀)
        filter_upwards [htend.eventually htopg] with w hw
        have hw' : star (f w) = 0 := by simpa [g] using hw
        exact star_eq_zero.mp hw'
      exact htop hcontra
    rw [hg_an.analyticOrderNatAt_eq_iff htop']
    let n := analyticOrderNatAt f (star z₀)
    let v : ℂ → ℂ := fun z => star (u (star z))
    have hv_an : AnalyticAt ℂ v z₀ := by
      obtain ⟨r, hr, hu_diff⟩ := hu_an.exists_ball_analyticOnNhd
      have hv_diff : DifferentiableOn ℂ v (Metric.ball z₀ r) := by
        intro z hz
        have hst : star z ∈ Metric.ball (star z₀) r := by
          simpa [Complex.dist_conj_conj] using hz
        exact (differentiableAt_conj_conj_iff.mpr
          ((hu_diff (star z) hst).differentiableAt)).differentiableWithinAt
      exact (hv_diff.analyticOnNhd Metric.isOpen_ball) z₀ (Metric.mem_ball_self hr)
    refine ⟨v, hv_an, ?_, ?_⟩
    · simpa [v] using star_ne_zero.mpr hu0
    · have htend : Tendsto (star : ℂ → ℂ) (𝓝 z₀) (𝓝 (star z₀)) :=
        Complex.continuous_conj.continuousAt.tendsto
      filter_upwards [htend.eventually hfu] with z hz
      change star (f (star z)) = (z - z₀) ^ n • star (u (star z))
      have hz' : f (star z) = (star z - star z₀) ^ n • u (star z) := hz
      rw [hz', smul_eq_mul, smul_eq_mul, star_mul', star_pow, star_sub, star_star, star_star,
        mul_comm]

private lemma analyticOrderNatAt_xi_conj {ρ : ℂ} :
    analyticOrderNatAt xi (star ρ) = analyticOrderNatAt xi ρ := by
  have h := analyticOrderNatAt_conj_conj isOpen_univ differentiable_xi.differentiableOn
    (z₀ := ρ) (Set.mem_univ _)
  have heq : (fun z : ℂ => star (xi (star z))) = xi := by
    ext z
    change conj (xi (conj z)) = xi z
    rw [xi_conj, Complex.conj_conj]
  simpa [heq] using h.symm

private lemma analyticOrderNatAt_xi_one_sub {ρ : ℂ} :
    analyticOrderNatAt xi (1 - ρ) = analyticOrderNatAt xi ρ := by
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun z : ℂ => 1 - z)
    ((differentiable_id.const_sub (1 : ℂ)).analyticAt ρ) (by simp)
  have hcongr : (xi ∘ fun z : ℂ => 1 - z) = xi := by
    ext z
    exact xi_one_sub z
  rw [hcongr] at hcomp
  simp only [analyticOrderNatAt, hcomp]

/-- Logarithmic upper bound on the multiplicity of any zero `ρ` of `xi`:
there exists `C > 0` such that `(analyticOrderNatAt xi ρ : ℝ) ≤ C * Real.log (|ρ.im| + 6)`. -/
theorem analyticOrderNatAt_xi_le_log :
    ∃ C > 0, ∀ ρ : ℂ, xi ρ = 0 →
      (analyticOrderNatAt xi ρ : ℝ) ≤ C * Real.log (|ρ.im| + 6) := by
  obtain ⟨Ccs, hCcs_pos, hcs⟩ := norm_riemannZeta_critical_strip_le (ε := 1 / 2) (by norm_num)
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_closedBall (0 : ℂ) 6).image_of_continuousOn
      differentiable_riemannZeta₁_bridge.continuous.continuousOn.norm).bddAbove
  let K : ℝ := max (max M₀ 1) (max (7 * Ccs) 14)
  have hK_pos : 0 < K := by positivity
  let C : ℝ := (max (Real.log K) 0 + 3 + Real.log 2) / Real.log (4 / 3)
  have hlog43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun ρ hxi => ?_⟩
  obtain ⟨_, hpos, hlt⟩ := xi_eq_zero_iff.mp hxi
  suffices hmain : ∀ w : ℂ, xi w = 0 → 1 / 2 ≤ w.re →
      (analyticOrderNatAt xi w : ℝ) ≤ C * Real.log (|w.im| + 6) by
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt_half
    · exact hmain ρ hxi hge
    · have h1w : xi (1 - ρ) = 0 := by rw [xi_one_sub, hxi]
      have hre : 1 / 2 ≤ (1 - ρ).re := by simp; linarith
      have him : |(1 - ρ).im| = |ρ.im| := by simp [abs_neg]
      rw [← analyticOrderNatAt_xi_one_sub, ← him]
      exact hmain (1 - ρ) h1w hre
  intro w hw hre_half
  obtain ⟨hwz, hw0, hw1⟩ := xi_eq_zero_iff.mp hw
  let z₀ : ℂ := (2 : ℂ) + (w.im : ℂ) * I
  let r : ℝ := 3 / 2
  let R : ℝ := 2
  have hR_pos : 0 < R := by norm_num
  have hr_pos : 0 < r := by norm_num
  have hrR : r < R := by norm_num
  have hw_ball : w ∈ Metric.closedBall z₀ r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : w - z₀ = ((w.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z₀]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    dsimp [r]
    linarith
  have hz₀_val : riemannZeta₁ z₀ ≠ 0 := by
    have hz₀_ne1 : z₀ ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp [z₀] at this
    have hz_eq : riemannZeta₁ z₀ = (z₀ - 1) * riemannZeta z₀ := by
      have h := riemannZeta_eq_inv_sub_mul hz₀_ne1
      have hne : z₀ - 1 ≠ 0 := sub_ne_zero.mpr hz₀_ne1
      rw [h]
      field_simp [hne]
    rw [hz_eq]
    have hnorm_z1 : 1 ≤ ‖z₀ - 1‖ := by
      have hre : (z₀ - 1).re = 1 := by simp [z₀]; norm_num
      have h1 := Complex.abs_re_le_norm (z₀ - 1)
      rw [hre, abs_one] at h1
      exact h1
    have hnorm_zeta : 1 / 2 ≤ ‖riemannZeta z₀‖ := by
      have h := norm_riemannZeta_ge_of_one_lt_re (by norm_num : (1 : ℝ) < 2) w.im
      norm_num at h
      simpa [z₀] using h
    have hnorm_prod : 1 / 2 ≤ ‖(z₀ - 1) * riemannZeta z₀‖ := by
      rw [norm_mul]
      nlinarith
    intro h0
    rw [h0, norm_zero] at hnorm_prod
    linarith
  have hnorm_z₀_ge : 1 / 2 ≤ ‖riemannZeta₁ z₀‖ := by
    have hz₀_ne1 : z₀ ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp [z₀] at this
    have hz_eq : riemannZeta₁ z₀ = (z₀ - 1) * riemannZeta z₀ := by
      have h := riemannZeta_eq_inv_sub_mul hz₀_ne1
      have hne : z₀ - 1 ≠ 0 := sub_ne_zero.mpr hz₀_ne1
      rw [h]
      field_simp [hne]
    rw [hz_eq, norm_mul]
    have hnorm_z1 : 1 ≤ ‖z₀ - 1‖ := by
      have hre : (z₀ - 1).re = 1 := by simp [z₀]; norm_num
      have h1 := Complex.abs_re_le_norm (z₀ - 1)
      rw [hre, abs_one] at h1
      exact h1
    have hnorm_zeta : 1 / 2 ≤ ‖riemannZeta z₀‖ := by
      have h := norm_riemannZeta_ge_of_one_lt_re (by norm_num : (1 : ℝ) < 2) w.im
      norm_num at h
      simpa [z₀] using h
    nlinarith
  let M : ℝ := K * (|w.im| + 6) ^ 3
  have hM_pos : 0 < M := by positivity
  have hball_bd : ∀ z ∈ Metric.ball z₀ R, ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hz_re_ge : 0 < z.re := by
      have h := Complex.abs_re_le_norm (z - z₀)
      have hre : (z - z₀).re = z.re - 2 := by simp [z₀]
      rw [hre] at h
      have h1 := abs_lt.mp (lt_of_le_of_lt h hz)
      dsimp [R] at h1
      linarith [h1.1, h1.2]
    have hz_re_le : z.re < 4 := by
      have h := Complex.abs_re_le_norm (z - z₀)
      have hre : (z - z₀).re = z.re - 2 := by simp [z₀]
      rw [hre] at h
      have h1 := abs_lt.mp (lt_of_le_of_lt h hz)
      dsimp [R] at h1
      linarith [h1.1, h1.2]
    have hz_im_le : |z.im| ≤ |w.im| + 2 := by
      have h := Complex.abs_im_le_norm (z - z₀)
      have him : (z - z₀).im = z.im - w.im := by simp [z₀]
      rw [him] at h
      have h1 := abs_le.mp (h.trans hz.le)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, neg_abs_le w.im, le_abs_self w.im]
    by_cases him_small : |z.im| ≤ 2
    · have hz_norm : ‖z‖ ≤ 6 := by
        have hre_abs : |z.re| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hre_sq : z.re ^ 2 ≤ 16 := by
          have : |z.re| ^ 2 ≤ 16 := by nlinarith [abs_nonneg z.re]
          rwa [sq_abs] at this
        have him_sq : z.im ^ 2 ≤ 4 := by
          have : |z.im| ^ 2 ≤ 4 := by nlinarith [abs_nonneg z.im]
          rwa [sq_abs] at this
        have hsq : ‖z‖ ^ 2 ≤ 6 ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith
        nlinarith [norm_nonneg z]
      have hz_mem : z ∈ Metric.closedBall (0 : ℂ) 6 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz_norm
      have h1 : ‖riemannZeta₁ z‖ ≤ M₀ := hM₀ ⟨z, hz_mem, rfl⟩
      have h2 : M₀ ≤ K := le_trans (le_max_left _ 1) (le_max_left _ _)
      have hpow1 : 1 ≤ (|w.im| + 6) ^ 3 := by
        have : (1 : ℝ) ≤ |w.im| + 6 := by linarith [abs_nonneg w.im]
        exact one_le_pow₀ this
      calc
        ‖riemannZeta₁ z‖ ≤ M₀ := h1
        _ ≤ K * 1 := by linarith
        _ ≤ K * (|w.im| + 6) ^ 3 := mul_le_mul_of_nonneg_left hpow1 hK_pos.le
    · push Not at him_small
      have hz1 : z ≠ 1 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        rw [him, abs_zero] at him_small
        linarith
      have hzeq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
        have h := riemannZeta_eq_inv_sub_mul hz1
        have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
        rw [h]
        field_simp [hne]
      have hz_sub1 : ‖z - 1‖ ≤ |w.im| + 6 := by
        have hre_abs : |z.re - 1| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
        have him_abs : |z.im| ≤ |w.im| + 2 := hz_im_le
        have htri : ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        simp only [sub_re, one_re, sub_im, one_im, sub_zero] at htri
        linarith
      rw [hzeq, norm_mul]
      rcases le_or_gt (1 / 2 : ℝ) z.re with hz_half | hz_lt_half
      · have hz_norm_ge : 2 ≤ ‖z‖ := him_small.le.trans (Complex.abs_im_le_norm z)
        have hzeta := norm_riemannZeta_re_ge_half_le hz_half hz_norm_ge
        have hz_norm_le : ‖z‖ ≤ |w.im| + 6 := by
          have htri : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          have hre_abs : |z.re| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
        have hK14 : 2 ≤ K := by
          have h1 : (14 : ℝ) ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
          linarith
        have hpow1 : 1 ≤ |w.im| + 6 := by linarith [abs_nonneg w.im]
        calc
          ‖z - 1‖ * ‖riemannZeta z‖ ≤ (|w.im| + 6) * (2 * (|w.im| + 6)) := by
            gcongr
            exact hzeta.trans (mul_le_mul_of_nonneg_left hz_norm_le zero_le_two)
          _ = 2 * (|w.im| + 6) ^ 2 * 1 := by ring
          _ ≤ K * (|w.im| + 6) ^ 2 * (|w.im| + 6) := by gcongr
          _ = K * (|w.im| + 6) ^ 3 := by ring
      · have hz_mem : z.re ∈ Set.Icc (0 : ℝ) 1 := ⟨hz_re_ge.le, by linarith⟩
        have hz_im_ge1 : 1 ≤ |z.im| := by linarith
        have hzeta := hcs hz_mem hz_im_ge1
        have hzeq' : z = ((z.re : ℝ) : ℂ) + (z.im : ℂ) * I := by
          apply Complex.ext <;> simp
        rw [← hzeq'] at hzeta
        have hexp_le : (1 - z.re) / 2 + 1 / 2 ≤ 1 := by linarith [hz_re_ge]
        have him2_le : (|z.im| + 2) ^ ((1 - z.re) / 2 + 1 / 2) ≤ (|w.im| + 6) ^ 1 := by
          have h1 : (|z.im| + 2) ^ ((1 - z.re) / 2 + 1 / 2) ≤ (|z.im| + 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) hexp_le
          rw [Real.rpow_one] at h1
          linarith
        have hC_le : Ccs ≤ K := by
          have h1 : 7 * Ccs ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
          linarith
        have hpow1 : 1 ≤ |w.im| + 6 := by linarith [abs_nonneg w.im]
        calc
          ‖z - 1‖ * ‖riemannZeta z‖ ≤ (|w.im| + 6) * (Ccs * (|w.im| + 6) ^ 1) := by
            gcongr
            exact hzeta.trans (mul_le_mul_of_nonneg_left him2_le hCcs_pos.le)
          _ = Ccs * (|w.im| + 6) ^ 2 * 1 := by ring
          _ ≤ K * (|w.im| + 6) ^ 2 * (|w.im| + 6) := by gcongr
          _ = K * (|w.im| + 6) ^ 3 := by ring
  have hcount := zeroCount_le_sub_log_div_log_of_ball hr_pos hrR hM_pos
    differentiable_riemannZeta₁_bridge.differentiableOn hz₀_val hball_bd
  have hord_le_count : analyticOrderNatAt riemannZeta₁ w ≤ zeroCount riemannZeta₁ z₀ r := by
    have han_r : AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall z₀ r) :=
      differentiable_riemannZeta₁_bridge.differentiableOn.analyticOnNhd isOpen_univ |>.mono
        (Set.subset_univ _)
    rw [zeroCount_eq_sum_analyticOrderNatAt hr_pos.le han_r hz₀_val
      (Set.Finite.coe_toFinset (zeroSet_finite hr_pos.le han_r hz₀_val))]
    have hw_mem : w ∈ (zeroSet_finite hr_pos.le han_r hz₀_val).toFinset := by
      rw [Set.Finite.mem_toFinset, mem_zeroSet]
      refine ⟨hw_ball, ?_⟩
      have hw1' : w ≠ 1 := fun h => by simp [h] at hw1
      have h_eq : riemannZeta₁ w = (w - 1) * riemannZeta w := by
        have h := riemannZeta_eq_inv_sub_mul hw1'
        have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hw1'
        rw [h]
        field_simp [hne]
      rw [h_eq, hwz, mul_zero]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw_mem
  have hord_eq : analyticOrderNatAt xi w = analyticOrderNatAt riemannZeta₁ w := by
    rw [analyticOrderNatAt_xi_eq_riemannZeta hw0 hw1]
    have hw1' : w ≠ 1 := fun h => by simp [h] at hw1
    have hev : riemannZeta₁ =ᶠ[𝓝 w] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_ne.mem_nhds hw1'] with s hs
      have h := riemannZeta_eq_inv_sub_mul hs
      have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
      rw [h]
      field_simp [hne]
    have hmul : analyticOrderAt (fun s => (s - 1) * riemannZeta s) w =
        analyticOrderAt (fun s : ℂ => s - 1) w + analyticOrderAt riemannZeta w :=
      analyticOrderAt_mul ((differentiable_id.sub_const 1).analyticAt w)
        (analyticOn_riemannZeta w hw1')
    have hord_s1 : analyticOrderAt (fun s : ℂ => s - 1) w = 0 :=
      ((differentiable_id.sub_const 1).analyticAt w).analyticOrderAt_eq_zero.mpr
        (sub_ne_zero.mpr hw1')
    have hmul' := (analyticOrderAt_congr hev).trans hmul
    rw [hord_s1, zero_add] at hmul'
    simp [analyticOrderNatAt, hmul']
  rw [hord_eq]
  have hlog_M : Real.log M = Real.log K + 3 * Real.log (|w.im| + 6) := by
    dsimp [M]
    rw [Real.log_mul hK_pos.ne' (pow_pos (by linarith [abs_nonneg w.im]) 3).ne', Real.log_pow]
    push_cast
    ring
  have hlog_z0 : -Real.log ‖riemannZeta₁ z₀‖ ≤ Real.log 2 := by
    have h1 : Real.log (1 / 2 : ℝ) ≤ Real.log ‖riemannZeta₁ z₀‖ :=
      Real.log_le_log (by norm_num) hnorm_z₀_ge
    rw [one_div, Real.log_inv] at h1
    linarith
  have hRr_eq : R / r = 4 / 3 := by dsimp [R, r]; norm_num
  have hlog6_ge1 : 1 ≤ Real.log (|w.im| + 6) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg w.im])]
    exact Real.exp_one_lt_d9.le.trans (by linarith [abs_nonneg w.im])
  calc
    (analyticOrderNatAt riemannZeta₁ w : ℝ) ≤ (zeroCount riemannZeta₁ z₀ r : ℝ) := by
      exact_mod_cast hord_le_count
    _ ≤ (Real.log M - Real.log ‖riemannZeta₁ z₀‖) / Real.log (R / r) := hcount
    _ ≤ (Real.log K + 3 * Real.log (|w.im| + 6) + Real.log 2) / Real.log (4 / 3) := by
      rw [hlog_M, hRr_eq]
      gcongr
      linarith
    _ ≤ ((max (Real.log K) 0 + 3 + Real.log 2) * Real.log (|w.im| + 6)) / Real.log (4 / 3) := by
      have hK_le : Real.log K ≤ max (Real.log K) 0 * Real.log (|w.im| + 6) := by
        calc
          Real.log K ≤ max (Real.log K) 0 := le_max_left _ _
          _ = max (Real.log K) 0 * 1 := (mul_one _).symm
          _ ≤ max (Real.log K) 0 * Real.log (|w.im| + 6) := by gcongr
      have hlog2_le : Real.log 2 ≤ Real.log 2 * Real.log (|w.im| + 6) := by
        calc
          Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
          _ ≤ Real.log 2 * Real.log (|w.im| + 6) :=
            mul_le_mul_of_nonneg_left hlog6_ge1 (Real.log_pos one_lt_two).le
      exact div_le_div_of_nonneg_right (by linarith [hK_le, hlog2_le]) hlog43.le
    _ = C * Real.log (|w.im| + 6) := by dsimp [C]; ring

/-! ### Hoheisel–Ingham Deduction of Primes in Short Intervals -/

/-- Zero-density hypothesis `N(σ, T) ≤ C * T^(A * (1 - σ)) * (log T)^B` uniformly for
`σ ∈ [1/2, 1]` and `T ≥ 2`. -/
def ZeroDensityHypothesis (A B : ℝ) : Prop :=
  ∃ C > 0, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ T : ℝ, 2 ≤ T →
    (zeroDensityN σ T : ℝ) ≤ C * T ^ (A * (1 - σ)) * Real.log T ^ B

/-- Truncated von Mangoldt explicit-formula hypothesis for `Chebyshev.psi` up to height `T`:
`ψ(x) = x - ∑_{|Im ρ| ≤ T} mult(ρ) * x^ρ / ρ + O((x * (log x)²) / T + log x)` for `2 ≤ T ≤ x`. -/
def TruncatedExplicitFormulaHypothesis : Prop :=
  ∃ C > 0, ∀ {x T : ℝ}, 2 ≤ T → T ≤ x →
    ‖(Chebyshev.psi x : ℂ) - (x : ℂ) +
      ∑ ρ ∈ zeroDensityFinsetSymmetric T,
        (analyticOrderNatAt xi ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      C * (x * Real.log x ^ 2 / T + Real.log x)

/-- Super-logarithmic zero-free region hypothesis (such as Littlewood / Vinogradov–Korobov):
there exists a nonincreasing positive width `δ(T)` for `T ≥ T₀ ≥ 2` satisfying
`δ(T) * log T / log(log T) → ∞` such that `riemannZeta ρ = 0` (`0 < Re ρ < 1`, `T₀ ≤ |Im ρ|`)
implies `Re ρ ≤ 1 - δ(|Im ρ|)`. -/
def SuperLogZeroFreeHypothesis : Prop :=
  ∃ δ : ℝ → ℝ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    (∀ T : ℝ, T₀ ≤ T → 0 < δ T) ∧
    AntitoneOn δ (Set.Ici T₀) ∧
    Tendsto (fun T : ℝ => δ T * Real.log T / Real.log (Real.log T)) atTop atTop ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - δ |ρ.im|

private lemma intervalIntegral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ t in a..b, ∑ i ∈ s, f i t = ∑ i ∈ s, ∫ t in a..b, f i t := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hi_int : IntervalIntegrable (f i) volume a b := hf i (Finset.mem_insert_self i s)
    have hs_int : IntervalIntegrable (fun t => ∑ j ∈ s, f j t) volume a b := by
      have hfn : (fun t => ∑ j ∈ s, f j t) = ∑ j ∈ s, f j := by
        ext t
        rw [Finset.sum_apply]
      rw [hfn]
      exact IntervalIntegrable.sum s fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [intervalIntegral.integral_add hi_int hs_int,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- Reusable layer-cake summation identity: for any finite set `S : Finset ℂ` with real parts in
`[a, b]`, weight `w : ℂ → ℝ`, and `1 < x`,
`∑ ρ ∈ S, w ρ * x ^ (ρ.re - 1) = (∑ ρ ∈ S, w ρ) * x ^ (a - 1) + log x * ∫ σ in a..b, (∑ ρ ∈ S with σ ≤ ρ.re, w ρ) * x ^ (σ - 1)`. -/
theorem sum_rpow_sub_one_eq_add_integral {S : Finset ℂ} (w : ℂ → ℝ) {a b x : ℝ}
    (_hab : a ≤ b) (hx : 1 < x) (hS : ∀ ρ ∈ S, a ≤ ρ.re ∧ ρ.re ≤ b) :
    ∑ ρ ∈ S, w ρ * x ^ (ρ.re - 1) =
      (∑ ρ ∈ S, w ρ) * x ^ (a - 1) +
        Real.log x * ∫ σ in a..b, (∑ ρ ∈ S with σ ≤ ρ.re, w ρ) * x ^ (σ - 1) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hint_each : ∀ ρ ∈ S, IntervalIntegrable
      (fun σ : ℝ => if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0) volume a b := by
    intro ρ _
    have hcont_pow : Continuous (fun σ : ℝ => x ^ (σ - 1)) := by
      have hfn : (fun σ : ℝ => x ^ (σ - 1)) = fun σ => Real.exp (Real.log x * (σ - 1)) := by
        ext σ; rw [Real.rpow_def_of_pos hx_pos]
      rw [hfn]
      fun_prop
    have hcont : Continuous (fun σ : ℝ => w ρ * x ^ (σ - 1)) := continuous_const.mul hcont_pow
    have heq : (fun σ : ℝ => if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0) =
        (Set.Iic ρ.re).indicator (fun σ : ℝ => w ρ * x ^ (σ - 1)) := by
      ext σ
      by_cases h : σ ≤ ρ.re <;> simp [h]
    rw [heq]
    exact ⟨(hcont.intervalIntegrable a b).1.indicator measurableSet_Iic,
      (hcont.intervalIntegrable a b).2.indicator measurableSet_Iic⟩
  have hsum_int :
      ∫ σ in a..b, (∑ ρ ∈ S with σ ≤ ρ.re, w ρ) * x ^ (σ - 1) =
        ∑ ρ ∈ S, ∫ σ in a..b, (if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0) := by
    have hfn : (fun σ : ℝ => (∑ ρ ∈ S with σ ≤ ρ.re, w ρ) * x ^ (σ - 1)) =
        fun σ : ℝ => ∑ ρ ∈ S, (if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0) := by
      ext σ
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> ring
    rw [hfn]
    exact intervalIntegral_finset_sum' S
      (fun ρ σ => if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0) a b hint_each
  have heach : ∀ ρ ∈ S,
      Real.log x * ∫ σ in a..b, (if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0) =
        w ρ * x ^ (ρ.re - 1) - w ρ * x ^ (a - 1) := by
    intro ρ hρ
    obtain ⟨haρ, hρb⟩ := hS ρ hρ
    let f : ℝ → ℝ := fun σ => if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0
    have hf_int : IntervalIntegrable f volume a b := hint_each ρ hρ
    have hmem : ρ.re ∈ Set.uIcc a b := Set.mem_uIcc.mpr (Or.inl ⟨haρ, hρb⟩)
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hf_int.mono_set (Set.uIcc_subset_uIcc_left hmem))
      (hf_int.mono_set (Set.uIcc_subset_uIcc_right hmem))
    have hleft : ∫ σ in a..ρ.re, f σ =
        w ρ * (x ^ (ρ.re - 1) - x ^ (a - 1)) / Real.log x := by
      have hcongr : ∫ σ in a..ρ.re, f σ = ∫ σ in a..ρ.re, w ρ * x ^ (σ - 1) := by
        refine intervalIntegral.integral_congr fun σ hσ => ?_
        rw [Set.uIcc_of_le haρ] at hσ
        dsimp [f]
        simp [hσ.2]
      rw [hcongr]
      have hderiv : ∀ σ ∈ Set.uIcc a ρ.re,
          HasDerivAt (fun t : ℝ => w ρ * x ^ (t - 1) / Real.log x) (w ρ * x ^ (σ - 1)) σ := by
        intro σ _
        have hlin : HasDerivAt (fun t : ℝ => Real.log x * (t - 1)) (Real.log x) σ := by
          simpa using ((hasDerivAt_id' σ).sub_const 1).const_mul (Real.log x)
        have h1 : HasDerivAt (fun t : ℝ => Real.exp (Real.log x * (t - 1)))
            (Real.exp (Real.log x * (σ - 1)) * Real.log x) σ := hlin.exp
        have h1' : HasDerivAt (fun t : ℝ => x ^ (t - 1)) (x ^ (σ - 1) * Real.log x) σ := by
          refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
          · rw [Real.rpow_def_of_pos hx_pos]
          · rw [Real.rpow_def_of_pos hx_pos]
        have h2 := (h1'.const_mul (w ρ)).div_const (Real.log x)
        refine h2.congr_deriv ?_
        field_simp [hlog_pos.ne']
      have hint_c : IntervalIntegrable (fun σ : ℝ => w ρ * x ^ (σ - 1)) volume a ρ.re := by
        have hcont_pow : Continuous (fun σ : ℝ => x ^ (σ - 1)) := by
          have hfn : (fun σ : ℝ => x ^ (σ - 1)) = fun σ => Real.exp (Real.log x * (σ - 1)) := by
            ext σ; rw [Real.rpow_def_of_pos hx_pos]
          rw [hfn]
          fun_prop
        exact (continuous_const.mul hcont_pow).intervalIntegrable a ρ.re
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_c]
      ring
    have hright : ∫ σ in ρ.re..b, f σ = 0 := by
      rw [intervalIntegral.integral_of_le hρb]
      refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => ?_
      have hnot : ¬ σ ≤ ρ.re := not_le.mpr hσ.1
      dsimp [f]
      simp [hnot]
    rw [← hadj, hleft, hright, add_zero]
    field_simp [hlog_pos.ne']
  rw [hsum_int, Finset.mul_sum]
  symm
  calc
    (∑ ρ ∈ S, w ρ) * x ^ (a - 1) +
        ∑ ρ ∈ S, Real.log x * ∫ σ in a..b, (if σ ≤ ρ.re then w ρ * x ^ (σ - 1) else 0)
        = ∑ ρ ∈ S, w ρ * x ^ (a - 1) + ∑ ρ ∈ S, (w ρ * x ^ (ρ.re - 1) - w ρ * x ^ (a - 1)) := by
          rw [Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl heach
    _ = ∑ ρ ∈ S, (w ρ * x ^ (a - 1) + (w ρ * x ^ (ρ.re - 1) - w ρ * x ^ (a - 1))) :=
          (Finset.sum_add_distrib).symm
    _ = ∑ ρ ∈ S, w ρ * x ^ (ρ.re - 1) := by
          refine Finset.sum_congr rfl fun ρ _ => by ring

/-- Exact exponential-integral bound on `[a, b]`: for `1 < x`, `0 < c`, and `a ≤ b ≤ 1`,
`Real.log x * ∫ σ in a..b, x ^ (-c * (1 - σ)) ≤ x ^ (-c * (1 - b)) / c`. -/
theorem log_mul_integral_rpow_neg_le {a b x c : ℝ} (_hab : a ≤ b) (_hb : b ≤ 1)
    (hx : 1 < x) (hc : 0 < c) :
    Real.log x * ∫ σ in a..b, x ^ (-c * (1 - σ)) ≤ x ^ (-c * (1 - b)) / c := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hderiv : ∀ σ ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => x ^ (c * (t - 1)) / (c * Real.log x)) (x ^ (-c * (1 - σ))) σ := by
    intro σ _
    have hlin : HasDerivAt (fun t : ℝ => Real.log x * (c * (t - 1))) (Real.log x * c) σ := by
      simpa using (((hasDerivAt_id' σ).sub_const 1).const_mul c).const_mul (Real.log x)
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (Real.log x * (c * (t - 1))))
        (Real.exp (Real.log x * (c * (σ - 1))) * (Real.log x * c)) σ := hlin.exp
    have h1' : HasDerivAt (fun t : ℝ => x ^ (c * (t - 1)))
        (x ^ (c * (σ - 1)) * (Real.log x * c)) σ := by
      refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
      · rw [Real.rpow_def_of_pos hx_pos]
      · rw [Real.rpow_def_of_pos hx_pos]
    have h2 := h1'.div_const (c * Real.log x)
    refine h2.congr_deriv ?_
    have hexp : c * (σ - 1) = -c * (1 - σ) := by ring
    rw [hexp]
    field_simp [hc.ne', hlog_pos.ne']
  have hint : IntervalIntegrable (fun σ : ℝ => x ^ (-c * (1 - σ))) volume a b := by
    have hcont : Continuous (fun σ : ℝ => x ^ (-c * (1 - σ))) := by
      have hfn : (fun σ : ℝ => x ^ (-c * (1 - σ))) = fun σ => Real.exp (Real.log x * (-c * (1 - σ))) := by
        ext σ; rw [Real.rpow_def_of_pos hx_pos]
      rw [hfn]
      fun_prop
    exact hcont.intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hnn : 0 ≤ x ^ (c * (a - 1)) := Real.rpow_nonneg hx_pos.le _
  have hexp_b : c * (b - 1) = -c * (1 - b) := by ring
  rw [hexp_b]
  calc
    Real.log x * (x ^ (-c * (1 - b)) / (c * Real.log x) - x ^ (c * (a - 1)) / (c * Real.log x))
        = (x ^ (-c * (1 - b)) - x ^ (c * (a - 1))) / c := by
          field_simp [hc.ne', hlog_pos.ne']
    _ ≤ x ^ (-c * (1 - b)) / c := by
          gcongr
          linarith

private lemma norm_cpow_sub_cpow_div_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ ≤ h * x ^ (ρ.re - 1) := by
  have hρ_ne : ρ ≠ 0 := fun h0 => by simp [h0] at hρ0
  have hx_le : x ≤ x + h := by linarith
  have hderiv : ∀ t ∈ Set.uIcc x (x + h),
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ ρ / ρ) ((t : ℂ) ^ (ρ - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx_le] at ht
    have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
    have hc : HasDerivAt (fun u : ℝ => (u : ℂ) ^ ρ) (ρ * (t : ℂ) ^ (ρ - 1)) t :=
      cpow_ofReal_hasDerivAt' ht_pos ρ
    have hd := hc.div_const ρ
    refine hd.congr_deriv ?_
    field_simp [hρ_ne]
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) volume x (x + h) := by
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) (Set.Icc x (x + h)) := by
      refine continuousOn_of_forall_continuousAt fun t ht => ?_
      exact (cpow_ofReal_hasDerivAt' (lt_of_lt_of_le hx ht.1) (ρ - 1)).continuousAt
    exact hcont.intervalIntegrable_of_Icc hx_le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hftc]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm hx_le (μ := volume)
    (f := fun t : ℝ => (t : ℂ) ^ (ρ - 1))
  have hmono : ∫ t in x..(x + h), ‖(t : ℂ) ^ (ρ - 1)‖ ≤ ∫ _t in x..(x + h), x ^ (ρ.re - 1) := by
    refine intervalIntegral.integral_mono_on hx_le hint.norm (by simp) fun t ht => ?_
    have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    simp only [sub_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  refine hnorm.trans (hmono.trans_eq ?_)
  simp

private lemma explicitFormula_diff_id' (S : Finset ℂ) (w : ℂ → ℕ) (p1 p2 x h : ℝ) :
    ((p1 - p2 : ℝ) : ℂ) - (h : ℂ) =
      ((p1 : ℂ) - ((x + h : ℝ) : ℂ) + ∑ ρ ∈ S, (w ρ : ℂ) * ((x + h : ℝ) : ℂ) ^ ρ / ρ) -
      ((p2 : ℂ) - (x : ℂ) + ∑ ρ ∈ S, (w ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
      ∑ ρ ∈ S, (w ρ : ℂ) * (((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ) := by
  push_cast
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

private lemma tendsto_halfLine_term_atTop {A B α : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1)
    (h_neg : α * (max A 0 / 2) - 1 / 2 < 0) :
    Tendsto (fun x : ℝ =>
      Real.log (x ^ α + 6) * (x ^ α) ^ (A / 2) * Real.log (x ^ α) ^ B * x ^ (-1 / 2 : ℝ))
      atTop (𝓝 0) := by
  let Apos : ℝ := max A 0
  let γ₀ : ℝ := (1 / 2 - α * (Apos / 2)) / 2
  have hγ₀_pos : 0 < γ₀ := by dsimp [γ₀, Apos]; linarith
  have hT_atTop : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα_pos
  have hlog_pow :
      Tendsto (fun x : ℝ => Real.log x ^ (max (|B| + 1) 1) * x ^ (-γ₀)) atTop (𝓝 0) := by
    let m : ℕ := Nat.ceil (max (|B| + 1) 1)
    have hm_ge : max (|B| + 1) 1 ≤ m := Nat.le_ceil _
    have h0 : Tendsto (fun x : ℝ => Real.log x ^ m / x ^ γ₀) atTop (𝓝 0) := by
      have h := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hγ₀_pos).tendsto_div_nhds_zero
      simpa [Real.rpow_natCast] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
      positivity
    · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
      have hlog_ge1 : 1 ≤ Real.log x :=
        (Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])).mpr hx
      have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
      rw [Real.rpow_neg hx0.le, div_eq_mul_inv]
      gcongr
      calc
        Real.log x ^ max (|B| + 1) 1 ≤ Real.log x ^ (m : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog_ge1 hm_ge
        _ = Real.log x ^ m := Real.rpow_natCast _ m
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((hlog_pow.const_mul (2 * max (α ^ B) (α ^ (-|B|)) + 2)).trans_eq (by simp)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hT1 : 1 ≤ x ^ α := Real.one_le_rpow (by linarith) hα_pos.le
    have hlogT_nn : 0 ≤ Real.log (x ^ α) := Real.log_nonneg hT1
    have hlog6_nn : 0 ≤ Real.log (x ^ α + 6) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [hT_atTop.eventually_ge_atTop 6,
      eventually_ge_atTop (Real.exp (1 / α))] with x hx6 hxexp
    have hx_pos : 0 < x := by
      have h1 : 0 < Real.exp (1 / α) := Real.exp_pos _
      linarith
    have hT_pos : 0 < x ^ α := by linarith
    have hlogx_ge : 1 / α ≤ Real.log x := (Real.le_log_iff_exp_le hx_pos).mpr hxexp
    have hlogT_eq : Real.log (x ^ α) = α * Real.log x := Real.log_rpow hx_pos α
    have hlogx_ge1 : 1 ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hxexp
      rw [Real.log_exp] at this
      calc (1 : ℝ) ≤ 1 / α := (one_le_div hα_pos).mpr hα_lt.le
        _ ≤ Real.log x := this
    have hx1 : 1 ≤ x := by
      by_contra hlt
      push Not at hlt
      linarith [Real.log_nonpos hx_pos.le hlt.le]
    have hlog6 : Real.log (x ^ α + 6) ≤ 2 * Real.log x := by
      have h1 : x ^ α + 6 ≤ 2 * x ^ α := by linarith
      have h2 : Real.log (x ^ α + 6) ≤ Real.log (2 * x ^ α) := Real.log_le_log (by positivity) h1
      have h3 : Real.log (2 * x ^ α) = Real.log 2 + α * Real.log x := by
        rw [Real.log_mul zero_lt_two.ne' hT_pos.ne', hlogT_eq]
      have hlog2_le : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp zero_lt_two]
        linarith [Real.add_one_lt_exp (one_ne_zero)]
      nlinarith [hα_lt, hlogx_ge1]
    have hlogB : Real.log (x ^ α) ^ B ≤ max (α ^ B) (α ^ (-|B|)) * Real.log x ^ |B| := by
      rw [hlogT_eq, Real.mul_rpow hα_pos.le (by linarith)]
      have h1 : Real.log x ^ B ≤ Real.log x ^ |B| :=
        Real.rpow_le_rpow_of_exponent_le hlogx_ge1 (le_abs_self B)
      have h2 : α ^ B ≤ max (α ^ B) (α ^ (-|B|)) := le_max_left _ _
      exact mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith) _) (by positivity)
    have hTA : (x ^ α) ^ (A / 2) ≤ x ^ (α * (Apos / 2)) := by
      rw [← Real.rpow_mul hx_pos.le]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : A / 2 ≤ Apos / 2 := by dsimp [Apos]; linarith [le_max_left A 0]
        nlinarith)
    have hxpow : x ^ (α * (Apos / 2)) * x ^ (-1 / 2 : ℝ) = x ^ (-(2 * γ₀)) := by
      rw [← Real.rpow_add hx_pos]
      congr 1
      dsimp [γ₀]
      ring
    have hlog_comb : Real.log x * Real.log x ^ |B| ≤ Real.log x ^ (max (|B| + 1) 1) := by
      rw [← Real.rpow_one_add' (by linarith : 0 ≤ Real.log x) (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hlogx_ge1 (by rw [add_comm]; exact le_max_left _ _)
    have hγ_le : x ^ (-(2 * γ₀)) ≤ x ^ (-γ₀) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hC_ge : 2 * max (α ^ B) (α ^ (-|B|)) ≤ 2 * max (α ^ B) (α ^ (-|B|)) + 2 := by linarith
    calc
      Real.log (x ^ α + 6) * (x ^ α) ^ (A / 2) * Real.log (x ^ α) ^ B * x ^ (-1 / 2 : ℝ)
          ≤ (2 * Real.log x) * x ^ (α * (Apos / 2)) *
              (max (α ^ B) (α ^ (-|B|)) * Real.log x ^ |B|) * x ^ (-1 / 2 : ℝ) := by
            have hnn1 : 0 ≤ Real.log (x ^ α + 6) := Real.log_nonneg (by linarith)
            have hnn2 : 0 ≤ (x ^ α) ^ (A / 2) := Real.rpow_nonneg hT_pos.le _
            have hnn3 : 0 ≤ Real.log (x ^ α) ^ B :=
              Real.rpow_nonneg (by rw [hlogT_eq]; exact mul_nonneg hα_pos.le (by linarith)) _
            have hnn4 : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx_pos.le _
            gcongr
      _ = (2 * max (α ^ B) (α ^ (-|B|))) * (Real.log x * Real.log x ^ |B|) *
            (x ^ (α * (Apos / 2)) * x ^ (-1 / 2 : ℝ)) := by ring
      _ ≤ (2 * max (α ^ B) (α ^ (-|B|))) * Real.log x ^ (max (|B| + 1) 1) * x ^ (-γ₀) := by
            rw [hxpow]
            gcongr
      _ ≤ (2 * max (α ^ B) (α ^ (-|B|)) + 2) * (Real.log x ^ (max (|B| + 1) 1) * x ^ (-γ₀)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hC_ge (by positivity)

private lemma tendsto_superLog_term_atTop {B α ε₀ : ℝ} (δ : ℝ → ℝ) (hα_pos : 0 < α)
    (hε₀_pos : 0 < ε₀)
    (hδ_lim : Tendsto (fun T : ℝ => δ T * Real.log T / Real.log (Real.log T)) atTop atTop) :
    Tendsto (fun x : ℝ => Real.log (x ^ α + 6) * Real.log (x ^ α) ^ B * x ^ (-ε₀ * δ (x ^ α)))
      atTop (𝓝 0) := by
  have hT_atTop : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα_pos
  let M₁ : ℝ := |B| + 2
  let c₁ : ℝ := ε₀ / α
  have hc₁_pos : 0 < c₁ := div_pos hε₀_pos hα_pos
  have hT_large : ∀ᶠ x in atTop,
      Real.exp (Real.exp 1) ≤ x ^ α ∧
      (M₁ + 1) / c₁ ≤ δ (x ^ α) * Real.log (x ^ α) / Real.log (Real.log (x ^ α)) :=
    (hT_atTop.eventually_ge_atTop (Real.exp (Real.exp 1))).and
      ((hδ_lim.comp hT_atTop).eventually_ge_atTop ((M₁ + 1) / c₁))
  have hll_atTop : Tendsto (fun x : ℝ => (Real.log (x ^ α))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hT_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((hll_atTop.const_mul 2).trans_eq (by simp)) ?_ ?_
  · filter_upwards [hT_atTop.eventually_ge_atTop 2, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlog6 : 0 ≤ Real.log (x ^ α + 6) := Real.log_nonneg (by linarith)
    have hlogT : 0 ≤ Real.log (x ^ α) := Real.log_nonneg (by linarith)
    have hx_pos : 0 ≤ x := by linarith
    positivity
  · filter_upwards [hT_large, eventually_gt_atTop (1 : ℝ)] with x ⟨hxT_exp, hratio⟩ hx1
    have hx_pos : 0 < x := lt_trans zero_lt_one hx1
    have hT_pos : 0 < x ^ α := lt_of_lt_of_le (Real.exp_pos _) hxT_exp
    have hlogT_ge : Real.exp 1 ≤ Real.log (x ^ α) :=
      (Real.le_log_iff_exp_le hT_pos).mpr hxT_exp
    have hlogT_pos : 0 < Real.log (x ^ α) := lt_of_lt_of_le (Real.exp_pos 1) hlogT_ge
    have hll_ge1 : 1 ≤ Real.log (Real.log (x ^ α)) :=
      (Real.le_log_iff_exp_le hlogT_pos).mpr hlogT_ge
    have hll_pos : 0 < Real.log (Real.log (x ^ α)) := lt_of_lt_of_le zero_lt_one hll_ge1
    have hlogT_eq : Real.log (x ^ α) = α * Real.log x := Real.log_rpow hx_pos α
    have hlog6 : Real.log (x ^ α + 6) ≤ 2 * Real.log (x ^ α) := by
      have h1 : x ^ α + 6 ≤ (x ^ α) ^ 2 := by
        have : 6 ≤ x ^ α := by
          have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
          have h1' : Real.exp (2 : ℝ) ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr he2.le
          have h2' : (6 : ℝ) ≤ Real.exp 2 := by
            rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
            nlinarith [Real.exp_one_gt_d9]
          linarith
        nlinarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      simpa using h2
    have hB_pow : Real.log (x ^ α) * Real.log (x ^ α) ^ B ≤ Real.log (x ^ α) ^ M₁ := by
      have h1 : 1 ≤ Real.log (x ^ α) := by linarith [Real.add_one_lt_exp (one_ne_zero)]
      have h2 := Real.rpow_le_rpow_of_exponent_le h1 (by dsimp [M₁]; linarith [le_abs_self B] : 1 + B ≤ M₁)
      rw [Real.rpow_add hlogT_pos, Real.rpow_one] at h2
      exact h2
    have hpow_exp :
        Real.log (x ^ α) ^ M₁ = Real.exp (M₁ * Real.log (Real.log (x ^ α))) := by
      rw [Real.rpow_def_of_pos hlogT_pos, mul_comm]
    have hneg_exp :
        x ^ (-ε₀ * δ (x ^ α)) =
          Real.exp (-c₁ * δ (x ^ α) * Real.log (x ^ α)) := by
      rw [Real.rpow_def_of_pos hx_pos]
      congr 1
      dsimp [c₁]
      rw [hlogT_eq]
      field_simp [hα_pos.ne']
    have hexp_diff :
        M₁ * Real.log (Real.log (x ^ α)) - c₁ * δ (x ^ α) * Real.log (x ^ α) ≤
          -Real.log (Real.log (x ^ α)) := by
      have h1 : (M₁ + 1) * Real.log (Real.log (x ^ α)) ≤ c₁ * δ (x ^ α) * Real.log (x ^ α) := by
        have hmul := (le_div_iff₀ hll_pos).mp hratio
        calc
          (M₁ + 1) * Real.log (Real.log (x ^ α))
              = c₁ * (((M₁ + 1) / c₁) * Real.log (Real.log (x ^ α))) := by
                field_simp [hc₁_pos.ne']
          _ ≤ c₁ * (δ (x ^ α) * Real.log (x ^ α)) := mul_le_mul_of_nonneg_left hmul hc₁_pos.le
          _ = c₁ * δ (x ^ α) * Real.log (x ^ α) := by ring
      linarith
    calc
      Real.log (x ^ α + 6) * Real.log (x ^ α) ^ B * x ^ (-ε₀ * δ (x ^ α))
          ≤ (2 * Real.log (x ^ α)) * Real.log (x ^ α) ^ B * x ^ (-ε₀ * δ (x ^ α)) := by gcongr
      _ = 2 * (Real.log (x ^ α) * Real.log (x ^ α) ^ B) * x ^ (-ε₀ * δ (x ^ α)) := by ring
      _ ≤ 2 * Real.log (x ^ α) ^ M₁ * x ^ (-ε₀ * δ (x ^ α)) := by gcongr
      _ = 2 * Real.exp (M₁ * Real.log (Real.log (x ^ α)) - c₁ * δ (x ^ α) * Real.log (x ^ α)) := by
            rw [hpow_exp, hneg_exp, mul_assoc, ← Real.exp_add]
            ring_nf
      _ ≤ 2 * Real.exp (-Real.log (Real.log (x ^ α))) := by gcongr
      _ = 2 * (Real.log (x ^ α))⁻¹ := by
            rw [Real.exp_neg, Real.exp_log hlogT_pos]

private lemma shortInterval_zeroSum_bound
    {A B Czd Cm T₀ ε₀ x T h : ℝ} (δ : ℝ → ℝ)
    (hCzd_pos : 0 < Czd) (hCm_pos : 0 < Cm) (hε₀_pos : 0 < ε₀)
    (hx1 : 1 < x) (hh_pos : 0 < h) (hT2 : 2 ≤ T) (hT_T₀ : T₀ ≤ T)
    (hzd : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (zeroDensityN σ T : ℝ) ≤ Czd * T ^ (A * (1 - σ)) * Real.log T ^ B)
    (hδ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < δ T) (hδ_anti : AntitoneOn δ (Set.Ici T₀))
    (hzf : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → T₀ ≤ |ρ.im| → ρ.re ≤ 1 - δ |ρ.im|)
    (hm_bd : ∀ ρ : ℂ, xi ρ = 0 → (analyticOrderNatAt xi ρ : ℝ) ≤ Cm * Real.log (|ρ.im| + 6))
    (hε₀_def : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1, T ^ (max A 0 * (1 - σ)) * x ^ (σ - 1) ≤ x ^ (-ε₀ * (1 - σ))) :
    (∑ ρ ∈ zeroDensityFinsetSymmetric T,
      (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖) / h ≤
      4 * Cm * Czd * (Real.log (T + 6) * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ)) +
        (2 * Cm * Czd / ε₀) * (Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T)) +
        2 * ∑ ρ ∈ zeroDensityFinset (1 / 2) T₀, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx1
  let S := zeroDensityFinsetSymmetric T
  have hzero_term :
      (∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖) / h ≤
        2 * ∑ ρ ∈ zeroDensityFinset 0 T, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
    have hstep1 :
        ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ ≤
          h * ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      obtain ⟨_, h0, h1, _⟩ := mem_zeroDensityFinsetSymmetric.mp hρ
      have hbd := norm_cpow_sub_cpow_div_le hx_pos hh_pos.le h0 h1
      calc
        (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖
            ≤ (analyticOrderNatAt xi ρ : ℝ) * (h * x ^ (ρ.re - 1)) := by gcongr
        _ = h * ((analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) := by ring
    have hstep2 :
        ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
          2 * ∑ ρ ∈ zeroDensityFinset 0 T, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
      let S₁ : Finset ℂ := zeroDensityFinset 0 T
      let S₂ : Finset ℂ := S₁.image (starRingEnd ℂ : ℂ → ℂ)
      have hS_eq : S = S₁ ∪ S₂ := rfl
      rw [hS_eq]
      have h_ui := Finset.sum_union_inter (s₁ := S₁) (s₂ := S₂)
        (f := fun ρ => (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1))
      have hint_nn : 0 ≤ ∑ ρ ∈ S₁ ∩ S₂,
          (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) :=
        Finset.sum_nonneg fun _ _ => by positivity
      have himage :
          ∑ ρ ∈ S₂,
              (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
            ∑ ρ ∈ S₁, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
        have himg : ∑ ρ ∈ S₂, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) =
            ∑ ρ ∈ S₁, (analyticOrderNatAt xi (star ρ) : ℝ) * x ^ ((star ρ).re - 1) := by
          dsimp [S₂]
          exact Finset.sum_image (fun a _ b _ hab => star_injective hab)
        rw [himg]
        refine Finset.sum_le_sum fun ρ _ => ?_
        rw [analyticOrderNatAt_xi_conj]
        simp
      linarith
    calc
      (∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖) / h
          ≤ (h * ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) / h := by gcongr
      _ = ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
            field_simp [hh_pos.ne']
      _ ≤ 2 * ∑ ρ ∈ zeroDensityFinset 0 T, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := hstep2
  let S_pos := zeroDensityFinset 0 T
  let S_lt := S_pos.filter (fun ρ => ρ.re < 1 / 2)
  let S_ge := S_pos.filter (fun ρ => 1 / 2 ≤ ρ.re)
  have hsplit_S :
      ∑ ρ ∈ S_pos, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) =
        (∑ ρ ∈ S_lt, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) +
        (∑ ρ ∈ S_ge, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) := by
    have h1 := Finset.sum_filter_add_sum_filter_not S_pos (fun ρ : ℂ => ρ.re < 1 / 2)
      (fun ρ : ℂ => (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1))
    have hnot : S_pos.filter (fun ρ : ℂ => ¬ ρ.re < 1 / 2) = S_ge := by
      ext ρ; simp [S_ge]
    rw [← hnot, h1]
  have hS_lt_bd :
      ∑ ρ ∈ S_lt, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
        Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) := by
    have hcard_lt : S_lt.card ≤ zeroDensityN (1 / 2) T := by
      rw [zeroDensityN_eq_card]
      refine Finset.card_le_card_of_injOn (fun ρ => 1 - star ρ) ?_ ?_
      · intro ρ hρ
        simp only [S_lt, S_pos, Finset.mem_coe, Finset.mem_filter, mem_zeroDensityFinset] at hρ
        obtain ⟨⟨hz, h0, h1, him0, himT⟩, hlt⟩ := hρ
        have hpos : 0 < ρ.re := (xi_eq_zero_iff.mp (mem_zeroDensitySet_iff_xi.mp
          (⟨hz, h0, h1, him0, himT⟩ : ρ ∈ zeroDensitySet 0 T)).1).2.1
        have hxi : xi (1 - star ρ) = 0 := by
          have hx := xi_eq_zero_iff.mpr ⟨hz, hpos, h1⟩
          change xi (1 - conj ρ) = 0
          rw [xi_one_sub, xi_conj, hx, map_zero]
        rw [Finset.mem_coe, mem_zeroDensityFinset]
        obtain ⟨hz', _, h1'⟩ := xi_eq_zero_iff.mp hxi
        have him_eq : (1 - star ρ).im = ρ.im := by simp
        refine ⟨hz', ?_, h1', ?_, ?_⟩
        · change 1 / 2 ≤ 1 - ρ.re; linarith [hlt]
        · rw [him_eq]; exact him0
        · rw [him_eq]; exact himT
      · intro ρ₁ _ ρ₂ _ heq
        have heq' : star ρ₁ = star ρ₂ := by linear_combination -heq
        exact star_injective heq'
    have hzd_half := hzd (1 / 2) (by constructor <;> norm_num) T hT2
    have heach : ∀ ρ ∈ S_lt,
        (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
          Cm * Real.log (T + 6) * x ^ (-1 / 2 : ℝ) := by
      intro ρ hρ
      simp only [S_lt, S_pos, Finset.mem_filter, mem_zeroDensityFinset] at hρ
      obtain ⟨⟨hz, h0, h1, him0, himT⟩, hlt⟩ := hρ
      have hxi : xi ρ = 0 := (mem_zeroDensitySet_iff_xi.mp
        (⟨hz, h0, h1, him0, himT⟩ : ρ ∈ zeroDensitySet 0 T)).1
      have hm := hm_bd ρ hxi
      have hlog_nn : 0 ≤ Real.log (|ρ.im| + 6) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
      have hlog_le : Real.log (|ρ.im| + 6) ≤ Real.log (T + 6) := by
        refine Real.log_le_log (by positivity) ?_
        rw [abs_of_pos him0]
        linarith
      have hxpow_le : x ^ (ρ.re - 1) ≤ x ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      calc
        (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)
            ≤ (Cm * Real.log (|ρ.im| + 6)) * x ^ (-1 / 2 : ℝ) :=
              mul_le_mul hm hxpow_le (Real.rpow_nonneg hx_pos.le _) (by positivity)
        _ ≤ (Cm * Real.log (T + 6)) * x ^ (-1 / 2 : ℝ) := by gcongr
        _ = Cm * Real.log (T + 6) * x ^ (-1 / 2 : ℝ) := by ring
    calc
      ∑ ρ ∈ S_lt, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)
          ≤ (S_lt.card : ℝ) * (Cm * Real.log (T + 6) * x ^ (-1 / 2 : ℝ)) := by
            rw [← nsmul_eq_mul]
            exact Finset.sum_le_card_nsmul _ _ _ heach
      _ ≤ (Czd * T ^ (A * (1 - (1 / 2 : ℝ))) * Real.log T ^ B) *
            (Cm * Real.log (T + 6) * x ^ (-1 / 2 : ℝ)) := by
            have hcard_r : (S_lt.card : ℝ) ≤ Czd * T ^ (A * (1 - (1 / 2 : ℝ))) * Real.log T ^ B :=
              (Nat.cast_le.mpr hcard_lt).trans hzd_half
            have hnn : 0 ≤ Cm * Real.log (T + 6) * x ^ (-1 / 2 : ℝ) := by
              have : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
              positivity
            exact mul_le_mul_of_nonneg_right hcard_r hnn
      _ = Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) := by
            rw [show A * (1 - (1 / 2 : ℝ)) = A / 2 by ring]
            ring
  let S_low := zeroDensityFinset (1 / 2) T₀
  let S_ge_low := S_ge.filter (fun ρ => ρ.im < T₀)
  let S_ge_high := S_ge.filter (fun ρ => T₀ ≤ ρ.im)
  have hsplit_ge :
      ∑ ρ ∈ S_ge, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) =
        (∑ ρ ∈ S_ge_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) +
        (∑ ρ ∈ S_ge_high, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) := by
    have h1 := Finset.sum_filter_add_sum_filter_not S_ge (fun ρ : ℂ => ρ.im < T₀)
      (fun ρ : ℂ => (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1))
    have hnot : S_ge.filter (fun ρ : ℂ => ¬ ρ.im < T₀) = S_ge_high := by
      ext ρ; simp [S_ge_high]
    rw [← hnot, h1]
  have hS_ge_low_bd :
      ∑ ρ ∈ S_ge_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
        ∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) (fun _ _ _ => by positivity)
    simp only [S_ge_low, S_ge, S_pos, Finset.mem_filter, mem_zeroDensityFinset, S_low] at hρ ⊢
    exact ⟨hρ.1.1.1, hρ.1.2, hρ.1.1.2.2.1, hρ.1.1.2.2.2.1, hρ.2.le⟩
  have hS_ge_high_bd :
      ∑ ρ ∈ S_ge_high, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
        Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) +
          (Cm * Czd / ε₀) * Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T) := by
    by_cases hδT : 1 - δ T < 1 / 2
    · have hempty : S_ge_high = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ρ hρ
        simp only [S_ge_high, S_ge, S_pos, Finset.mem_filter, mem_zeroDensityFinset] at hρ
        obtain ⟨⟨⟨hz, h0, h1, him0, himT⟩, hge⟩, hT0_ρ⟩ := hρ
        have hpos : 0 < ρ.re := (xi_eq_zero_iff.mp (mem_zeroDensitySet_iff_xi.mp
          (⟨hz, h0, h1, him0, himT⟩ : ρ ∈ zeroDensitySet 0 T)).1).2.1
        have hzf_ρ := hzf ρ hz hpos h1 (by rwa [abs_of_pos him0])
        have hanti : δ T ≤ δ ρ.im := hδ_anti hT0_ρ hT_T₀ himT
        rw [abs_of_pos him0] at hzf_ρ
        linarith
      rw [hempty, Finset.sum_empty]
      have hlog6 : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
      have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      positivity
    · push Not at hδT
      have hmem_bd : ∀ ρ ∈ S_ge_high, 1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 - δ T := by
        intro ρ hρ
        simp only [S_ge_high, S_ge, S_pos, Finset.mem_filter, mem_zeroDensityFinset] at hρ
        obtain ⟨⟨⟨hz, h0, h1, him0, himT⟩, hge⟩, hT0_ρ⟩ := hρ
        have hpos : 0 < ρ.re := (xi_eq_zero_iff.mp (mem_zeroDensitySet_iff_xi.mp
          (⟨hz, h0, h1, him0, himT⟩ : ρ ∈ zeroDensitySet 0 T)).1).2.1
        have hzf_ρ := hzf ρ hz hpos h1 (by rwa [abs_of_pos him0])
        have hanti : δ T ≤ δ ρ.im := hδ_anti hT0_ρ hT_T₀ himT
        rw [abs_of_pos him0] at hzf_ρ
        exact ⟨hge, by linarith⟩
      have hmult_le :
          ∑ ρ ∈ S_ge_high, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) ≤
            (Cm * Real.log (T + 6)) * ∑ ρ ∈ S_ge_high, (1 : ℝ) * x ^ (ρ.re - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ρ hρ => ?_
        simp only [S_ge_high, S_ge, S_pos, Finset.mem_filter, mem_zeroDensityFinset] at hρ
        obtain ⟨⟨⟨hz, h0, h1, him0, himT⟩, _⟩, _⟩ := hρ
        have hxi := (mem_zeroDensitySet_iff_xi.mp
          (⟨hz, h0, h1, him0, himT⟩ : ρ ∈ zeroDensitySet 0 T)).1
        have hm := hm_bd ρ hxi
        have hlog_le : Real.log (|ρ.im| + 6) ≤ Real.log (T + 6) := by
          refine Real.log_le_log (by positivity) ?_
          rw [abs_of_pos him0]; linarith
        have hxpow_nn : 0 ≤ x ^ (ρ.re - 1) := Real.rpow_nonneg hx_pos.le _
        calc
          (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)
              ≤ (Cm * Real.log (|ρ.im| + 6)) * x ^ (ρ.re - 1) :=
                mul_le_mul_of_nonneg_right hm hxpow_nn
          _ ≤ (Cm * Real.log (T + 6)) * x ^ (ρ.re - 1) := by gcongr
          _ = (Cm * Real.log (T + 6)) * ((1 : ℝ) * x ^ (ρ.re - 1)) := by ring
      have hlc := sum_rpow_sub_one_eq_add_integral (fun _ => (1 : ℝ)) hδT hx1 hmem_bd
      have hcard_ge_high : (S_ge_high.card : ℝ) ≤ zeroDensityN (1 / 2) T := by
        rw [zeroDensityN_eq_card]
        refine Nat.cast_le.mpr (Finset.card_le_card fun ρ hρ => ?_)
        simp only [S_ge_high, S_ge, S_pos, Finset.mem_filter, mem_zeroDensityFinset] at hρ ⊢
        exact ⟨hρ.1.1.1, hρ.1.2, hρ.1.1.2.2.1, hρ.1.1.2.2.2.1, hρ.1.1.2.2.2.2⟩
      have hfirst :
          (Cm * Real.log (T + 6)) * ((∑ _ρ ∈ S_ge_high, (1 : ℝ)) * x ^ ((1 / 2 : ℝ) - 1)) ≤
            Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) := by
        have hzd_half := hzd (1 / 2) (by constructor <;> norm_num) T hT2
        have hsum1 : ∑ _ρ ∈ S_ge_high, (1 : ℝ) = (S_ge_high.card : ℝ) := by simp
        rw [hsum1]
        have hlog6 : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
        have hpow_eq : x ^ ((1 / 2 : ℝ) - 1) = x ^ (-1 / 2 : ℝ) := by congr 1; norm_num
        rw [hpow_eq]
        calc
          (Cm * Real.log (T + 6)) * ((S_ge_high.card : ℝ) * x ^ (-1 / 2 : ℝ))
              ≤ (Cm * Real.log (T + 6)) *
                  ((Czd * T ^ (A * (1 - (1 / 2 : ℝ))) * Real.log T ^ B) * x ^ (-1 / 2 : ℝ)) := by
                gcongr
                exact hcard_ge_high.trans hzd_half
          _ = Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) := by
                rw [show A * (1 - (1 / 2 : ℝ)) = A / 2 by ring]
                ring
      have hint_mono :
          ∫ σ in (1 / 2 : ℝ)..(1 - δ T), (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) * x ^ (σ - 1) ≤
            ∫ σ in (1 / 2 : ℝ)..(1 - δ T), (Czd * Real.log T ^ B) * x ^ (-ε₀ * (1 - σ)) := by
        have hint1 : IntervalIntegrable
            (fun σ : ℝ => (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) * x ^ (σ - 1))
            volume (1 / 2 : ℝ) (1 - δ T) := by
          have hfn :
              (fun σ : ℝ => (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) * x ^ (σ - 1)) =
                fun σ : ℝ => ∑ ρ ∈ S_ge_high, if σ ≤ ρ.re then x ^ (σ - 1) else 0 := by
            ext σ
            rw [Finset.sum_filter, Finset.sum_mul]
            refine Finset.sum_congr rfl fun ρ _ => by split_ifs <;> ring
          rw [hfn]
          have hint_each_ge : ∀ ρ ∈ S_ge_high, IntervalIntegrable
              (fun σ : ℝ => if σ ≤ ρ.re then x ^ (σ - 1) else 0) volume (1 / 2 : ℝ) (1 - δ T) := by
            intro ρ _
            have hcont : Continuous (fun σ : ℝ => x ^ (σ - 1)) := by
              have hfn2 : (fun σ : ℝ => x ^ (σ - 1)) = fun σ => Real.exp (Real.log x * (σ - 1)) := by
                ext σ; rw [Real.rpow_def_of_pos hx_pos]
              rw [hfn2]
              fun_prop
            have heq : (fun σ : ℝ => if σ ≤ ρ.re then x ^ (σ - 1) else 0) =
                (Set.Iic ρ.re).indicator (fun σ : ℝ => x ^ (σ - 1)) := by
              ext σ; by_cases h : σ ≤ ρ.re <;> simp [h]
            rw [heq]
            exact ⟨(hcont.intervalIntegrable _ _).1.indicator measurableSet_Iic,
              (hcont.intervalIntegrable _ _).2.indicator measurableSet_Iic⟩
          have hsum_fn : (fun σ : ℝ => ∑ ρ ∈ S_ge_high, if σ ≤ ρ.re then x ^ (σ - 1) else 0) =
              ∑ ρ ∈ S_ge_high, fun σ : ℝ => if σ ≤ ρ.re then x ^ (σ - 1) else 0 := by
            ext σ; simp
          rw [hsum_fn]
          exact IntervalIntegrable.sum S_ge_high hint_each_ge
        have hint2 : IntervalIntegrable
            (fun σ : ℝ => (Czd * Real.log T ^ B) * x ^ (-ε₀ * (1 - σ)))
            volume (1 / 2 : ℝ) (1 - δ T) := by
          have hcont_pow : Continuous (fun σ : ℝ => x ^ (-ε₀ * (1 - σ))) := by
            have hfn2 : (fun σ : ℝ => x ^ (-ε₀ * (1 - σ))) =
                fun σ => Real.exp (Real.log x * (-ε₀ * (1 - σ))) := by
              ext σ; rw [Real.rpow_def_of_pos hx_pos]
            rw [hfn2]
            fun_prop
          exact (continuous_const.mul hcont_pow).intervalIntegrable _ _
        refine intervalIntegral.integral_mono_on hδT hint1 hint2 fun σ hσ => ?_
        have hσ_mem : σ ∈ Set.Icc (1 / 2 : ℝ) 1 :=
          ⟨hσ.1, hσ.2.trans (by linarith [hδ_pos T hT_T₀])⟩
        have hcount_σ : (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) ≤ (zeroDensityN σ T : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, zeroDensityN_eq_card]
          refine Nat.cast_le.mpr (Finset.card_le_card fun ρ hρ => ?_)
          simp only [Finset.mem_filter, S_ge_high, S_ge, S_pos, mem_zeroDensityFinset] at hρ ⊢
          exact ⟨hρ.1.1.1.1, hρ.2, hρ.1.1.1.2.2.1, hρ.1.1.1.2.2.2.1, hρ.1.1.1.2.2.2.2⟩
        have hzd_σ := hzd σ hσ_mem T hT2
        have hTA_le : T ^ (A * (1 - σ)) ≤ T ^ (max A 0 * (1 - σ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          exact mul_le_mul_of_nonneg_right (le_max_left A 0) (by linarith [hσ_mem.2])
        have hpow_comb := hε₀_def σ hσ_mem
        have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hprod_le : (zeroDensityN σ T : ℝ) * x ^ (σ - 1) ≤
            (Czd * Real.log T ^ B) * x ^ (-ε₀ * (1 - σ)) := by
          calc
            (zeroDensityN σ T : ℝ) * x ^ (σ - 1)
                ≤ (Czd * T ^ (A * (1 - σ)) * Real.log T ^ B) * x ^ (σ - 1) := by gcongr
            _ ≤ (Czd * T ^ (max A 0 * (1 - σ)) * Real.log T ^ B) * x ^ (σ - 1) := by gcongr
            _ = (Czd * Real.log T ^ B) * (T ^ (max A 0 * (1 - σ)) * x ^ (σ - 1)) := by ring
            _ ≤ (Czd * Real.log T ^ B) * x ^ (-ε₀ * (1 - σ)) := by
                  exact mul_le_mul_of_nonneg_left hpow_comb (by positivity)
        exact (mul_le_mul_of_nonneg_right hcount_σ (Real.rpow_nonneg hx_pos.le _)).trans hprod_le
      have hsecond :
          (Cm * Real.log (T + 6)) *
              (Real.log x * ∫ σ in (1 / 2 : ℝ)..(1 - δ T),
                (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) * x ^ (σ - 1)) ≤
            (Cm * Czd / ε₀) * Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T) := by
        have hlogx_nn : 0 ≤ Real.log x := (Real.log_pos hx1).le
        have hlog6 : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
        have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hint_eval := log_mul_integral_rpow_neg_le hδT (by linarith [hδ_pos T hT_T₀]) hx1 hε₀_pos
        have hexp_b : 1 - (1 - δ T) = δ T := by ring
        rw [hexp_b] at hint_eval
        calc
          (Cm * Real.log (T + 6)) *
              (Real.log x * ∫ σ in (1 / 2 : ℝ)..(1 - δ T),
                (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) * x ^ (σ - 1))
              ≤ (Cm * Real.log (T + 6)) *
                  (Real.log x * ∫ σ in (1 / 2 : ℝ)..(1 - δ T),
                    (Czd * Real.log T ^ B) * x ^ (-ε₀ * (1 - σ))) := by
                gcongr
          _ = (Cm * Real.log (T + 6)) * (Czd * Real.log T ^ B) *
                (Real.log x * ∫ σ in (1 / 2 : ℝ)..(1 - δ T), x ^ (-ε₀ * (1 - σ))) := by
                rw [intervalIntegral.integral_const_mul]
                ring
          _ ≤ (Cm * Real.log (T + 6)) * (Czd * Real.log T ^ B) * (x ^ (-ε₀ * δ T) / ε₀) := by
                gcongr
          _ = (Cm * Czd / ε₀) * Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T) := by ring
      calc
        ∑ ρ ∈ S_ge_high, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)
            ≤ (Cm * Real.log (T + 6)) * ∑ ρ ∈ S_ge_high, (1 : ℝ) * x ^ (ρ.re - 1) := hmult_le
        _ = (Cm * Real.log (T + 6)) * ((∑ _ρ ∈ S_ge_high, (1 : ℝ)) * x ^ ((1 / 2 : ℝ) - 1)) +
              (Cm * Real.log (T + 6)) *
                (Real.log x * ∫ σ in (1 / 2 : ℝ)..(1 - δ T),
                  (∑ ρ ∈ S_ge_high with σ ≤ ρ.re, (1 : ℝ)) * x ^ (σ - 1)) := by
              rw [hlc, mul_add]
        _ ≤ Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) +
              (Cm * Czd / ε₀) * Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T) :=
              add_le_add hfirst hsecond
  calc
    (∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖) / h
        ≤ 2 * ∑ ρ ∈ S_pos, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := hzero_term
    _ = 2 * ((∑ ρ ∈ S_lt, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) +
          (∑ ρ ∈ S_ge_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) +
          (∑ ρ ∈ S_ge_high, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1))) := by
          rw [hsplit_S, hsplit_ge]; ring
    _ ≤ 2 * ((Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ)) +
          (∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) +
          (Cm * Real.log (T + 6) * Czd * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) +
            (Cm * Czd / ε₀) * Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T))) := by
          gcongr
    _ = 4 * Cm * Czd * (Real.log (T + 6) * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ)) +
          (2 * Cm * Czd / ε₀) * (Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T)) +
          2 * ∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) := by
          ring

/-- **Hoheisel–Ingham short-interval asymptotic for `Chebyshev.psi`**:
if `ZeroDensityHypothesis A B`, `TruncatedExplicitFormulaHypothesis`, and
`SuperLogZeroFreeHypothesis` hold, and `1 / 2 ≤ θ < 1` satisfies `A * (1 - θ) < 1`, then
`ψ(x + x^θ) - ψ(x) ~ x^θ` as `x → ∞`. -/
theorem psi_shortInterval_isEquivalent_of_zeroDensity {A B θ : ℝ}
    (hZD : ZeroDensityHypothesis A B)
    (hEF : TruncatedExplicitFormulaHypothesis)
    (hZF : SuperLogZeroFreeHypothesis)
    (hθ₀ : 1 / 2 ≤ θ) (hθ₁ : θ < 1) (hA : A * (1 - θ) < 1) :
    (fun x : ℝ => Chebyshev.psi (x + x ^ θ) - Chebyshev.psi x) ~[atTop] fun x : ℝ => x ^ θ := by
  obtain ⟨Czd, hCzd_pos, hzd⟩ := hZD
  obtain ⟨Cef, hCef_pos, hef⟩ := hEF
  obtain ⟨δ, T₀, hT₀_ge2, hδ_pos, hδ_anti, hδ_lim, hzf⟩ := hZF
  obtain ⟨Cm, hCm_pos, hm_bd⟩ := analyticOrderNatAt_xi_le_log
  let Apos : ℝ := max A 0
  have hApos_nn : 0 ≤ Apos := le_max_right A 0
  have hApos_lt : Apos * (1 - θ) < 1 := by
    by_cases hA0 : A ≤ 0
    · have : Apos = 0 := max_eq_right hA0
      simp [this]
    · have : Apos = A := max_eq_left (le_of_not_ge hA0)
      simpa [this] using hA
  let η : ℝ := min (1 / 4 : ℝ) ((1 - Apos * (1 - θ)) / (2 * (Apos + 1)))
  have hη_pos : 0 < η := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hη_le_quarter : η ≤ 1 / 4 := min_le_left _ _
  let α : ℝ := 1 - θ + η
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hα_lt_one : α < 1 := by dsimp [α]; linarith
  have hε₀_pos : 0 < 1 - Apos * α := by
    have hη_bd : η ≤ (1 - Apos * (1 - θ)) / (2 * (Apos + 1)) := min_le_right _ _
    have h1 : Apos * η ≤ (1 - Apos * (1 - θ)) / 2 := by
      calc
        Apos * η ≤ Apos * ((1 - Apos * (1 - θ)) / (2 * (Apos + 1))) :=
          mul_le_mul_of_nonneg_left hη_bd hApos_nn
        _ ≤ (Apos + 1) * ((1 - Apos * (1 - θ)) / (2 * (Apos + 1))) := by gcongr; linarith
        _ = (1 - Apos * (1 - θ)) / 2 := by field_simp [show Apos + 1 ≠ 0 by linarith]
    have h2 : Apos * α = Apos * (1 - θ) + Apos * η := by dsimp [α]; ring
    linarith
  let ε₀ : ℝ := 1 - Apos * α
  have hθ_pos : 0 < θ := by linarith
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  swap
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_pos_of_pos hx θ).ne'
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hT_atTop : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα_pos
  have h1_lim : Tendsto (fun x : ℝ => x ^ (-η) * Real.log x ^ 2) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη_pos).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm, Real.rpow_two]
  have h2_lim : Tendsto (fun x : ℝ => Real.log x / x ^ θ) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hθ_pos).tendsto_div_nhds_zero
    simpa [Real.rpow_one] using h
  let S_low : Finset ℂ := zeroDensityFinset (1 / 2) T₀
  have hlow_lim :
      Tendsto (fun x : ℝ => ∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1))
        atTop (𝓝 0) := by
    have heach : ∀ ρ ∈ S_low,
        Tendsto (fun x : ℝ => (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) atTop (𝓝 0) := by
      intro ρ hρ
      obtain ⟨_, _, hlt, _⟩ := mem_zeroDensityFinset.mp hρ
      have hsub : Tendsto (fun x : ℝ => x ^ (-(1 - ρ.re))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      have heq : (fun x : ℝ => (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1)) =
          fun x : ℝ => (analyticOrderNatAt xi ρ : ℝ) * x ^ (-(1 - ρ.re)) := by
        ext x; ring_nf
      rw [heq]
      simpa using hsub.const_mul (analyticOrderNatAt xi ρ : ℝ)
    simpa using tendsto_finsetSum S_low fun ρ hρ => heach ρ hρ
  have hhalf_exp_neg : α * (Apos / 2) - 1 / 2 < 0 := by
    have h1 : Apos * α < 1 := by linarith
    linarith
  have hhalf_lim := tendsto_halfLine_term_atTop (B := B) hα_pos hα_lt_one hhalf_exp_neg
  have hzf_lim := tendsto_superLog_term_atTop (B := B) δ hα_pos hε₀_pos hδ_lim
  let K_err : ℝ := 16 * Cef
  let K_half : ℝ := 4 * Cm * Czd
  let K_zf : ℝ := 2 * Cm * Czd / ε₀
  have hK_err_pos : 0 < K_err := by positivity
  have hK_half_pos : 0 < K_half := by positivity
  have hK_zf_pos : 0 < K_zf := by positivity
  filter_upwards [
    eventually_ge_atTop (4 : ℝ),
    hT_atTop.eventually_ge_atTop (max 2 T₀),
    h1_lim.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / (4 * K_err) by positivity)),
    h2_lim.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / (4 * K_err) by positivity)),
    hlow_lim.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 12 by positivity)),
    hhalf_lim.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / (6 * K_half) by positivity)),
    hzf_lim.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / (6 * K_zf) by positivity))
  ] with x hx4 hT_ge h1_small h2_small hlow_small hhalf_small hzf_small
  have hx1 : 1 < x := by linarith
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx1
  let h : ℝ := x ^ θ
  have hh_pos : 0 < h := Real.rpow_pos_of_pos hx_pos θ
  have hh_le_x : h ≤ x := by
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le hθ₁.le
      _ = x := Real.rpow_one x
  let T : ℝ := x ^ α
  have hT2 : 2 ≤ T := (le_max_left 2 T₀).trans hT_ge
  have hT_T₀ : T₀ ≤ T := (le_max_right 2 T₀).trans hT_ge
  have hT_le_x : T ≤ x := by
    calc x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le hα_lt_one.le
      _ = x := Real.rpow_one x
  have hT_le_xh : T ≤ x + h := by linarith
  have hef_xh := hef (x := x + h) (T := T) hT2 hT_le_xh
  have hef_x := hef (x := x) (T := T) hT2 hT_le_x
  let S := zeroDensityFinsetSymmetric T
  have hdiff_id := explicitFormula_diff_id' S (analyticOrderNatAt xi)
    (Chebyshev.psi (x + h)) (Chebyshev.psi x) x h
  have htri_ef :
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤
        Cef * ((x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h)) +
        Cef * (x * Real.log x ^ 2 / T + Real.log x) +
        ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ := by
    have hnorm_eq :
        |Chebyshev.psi (x + h) - Chebyshev.psi x - h| =
          ‖((Chebyshev.psi (x + h) - Chebyshev.psi x : ℝ) : ℂ) - (h : ℂ)‖ := by
      have : ((Chebyshev.psi (x + h) - Chebyshev.psi x : ℝ) : ℂ) - (h : ℂ) =
          (((Chebyshev.psi (x + h) - Chebyshev.psi x - h : ℝ)) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hsum_bd :
        ‖∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) *
            (((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ)‖ ≤
          ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) *
            ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
      rw [norm_mul, Complex.norm_natCast]
    have h1 :
        |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤
          ‖((Chebyshev.psi (x + h) : ℂ) - ((x + h : ℝ) : ℂ) +
              ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * ((x + h : ℝ) : ℂ) ^ ρ / ρ)‖ +
            ‖((Chebyshev.psi x : ℂ) - (x : ℂ) +
              ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ +
            ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) *
              ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ := by
      calc
        |Chebyshev.psi (x + h) - Chebyshev.psi x - h|
            = ‖((Chebyshev.psi (x + h) : ℂ) - ((x + h : ℝ) : ℂ) +
                  ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * ((x + h : ℝ) : ℂ) ^ ρ / ρ) -
                ((Chebyshev.psi x : ℂ) - (x : ℂ) +
                  ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
                ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) *
                  (((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ)‖ := by
              rw [hnorm_eq, hdiff_id]
        _ ≤ ‖((Chebyshev.psi (x + h) : ℂ) - ((x + h : ℝ) : ℂ) +
                ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * ((x + h : ℝ) : ℂ) ^ ρ / ρ) -
              ((Chebyshev.psi x : ℂ) - (x : ℂ) +
                ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ +
            ‖∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) *
              (((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ)‖ := norm_sub_le _ _
        _ ≤ ‖((Chebyshev.psi (x + h) : ℂ) - ((x + h : ℝ) : ℂ) +
                ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * ((x + h : ℝ) : ℂ) ^ ρ / ρ)‖ +
            ‖((Chebyshev.psi x : ℂ) - (x : ℂ) +
                ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ +
            ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) *
              ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ :=
            add_le_add (norm_sub_le _ _) hsum_bd
    have hef_xh' : ‖(Chebyshev.psi (x + h) : ℂ) - ((x + h : ℝ) : ℂ) +
        ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * ((x + h : ℝ) : ℂ) ^ ρ / ρ‖ ≤
      Cef * ((x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h)) := hef_xh
    have hef_x' : ‖(Chebyshev.psi x : ℂ) - (x : ℂ) +
        ∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      Cef * (x * Real.log x ^ 2 / T + Real.log x) := hef_x
    linarith [hef_xh', hef_x', h1]
  have hlog_xh : Real.log (x + h) ≤ 2 * Real.log x := by
    have h1 : x + h ≤ x ^ 2 := by nlinarith
    calc Real.log (x + h) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_cast
  have hef_div :
      (Cef * ((x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h)) +
        Cef * (x * Real.log x ^ 2 / T + Real.log x)) / h < ε / 2 := by
    have hxh_bound : (x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h) ≤
        8 * (x * Real.log x ^ 2 / T) + 2 * Real.log x := by
      have h1 : x + h ≤ 2 * x := by linarith
      have h2 : Real.log (x + h) ^ 2 ≤ (2 * Real.log x) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_xh 2
      have h3 : (x + h) * Real.log (x + h) ^ 2 / T ≤ 8 * (x * Real.log x ^ 2 / T) := by
        calc (x + h) * Real.log (x + h) ^ 2 / T ≤ (2 * x) * (4 * Real.log x ^ 2) / T := by
              gcongr; linarith
          _ = 8 * (x * Real.log x ^ 2 / T) := by ring
      linarith
    have hdiv_T : (x * Real.log x ^ 2 / T) / h = x ^ (-η) * Real.log x ^ 2 := by
      dsimp [T, h]
      have hpow : x ^ α * x ^ θ = x * x ^ η := by
        calc x ^ α * x ^ θ = x ^ (α + θ) := (Real.rpow_add hx_pos α θ).symm
          _ = x ^ (1 + η) := by congr 1; dsimp [α]; ring
          _ = x * x ^ η := by rw [Real.rpow_add hx_pos, Real.rpow_one]
      rw [div_div, hpow, Real.rpow_neg hx_pos.le]
      field_simp [hx_pos.ne', (Real.rpow_pos_of_pos hx_pos η).ne']
    have hcomb :
        (Cef * ((x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h)) +
          Cef * (x * Real.log x ^ 2 / T + Real.log x)) / h ≤
          K_err * ((x ^ (-η) * Real.log x ^ 2) + (Real.log x / x ^ θ)) := by
      calc
        (Cef * ((x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h)) +
          Cef * (x * Real.log x ^ 2 / T + Real.log x)) / h
            ≤ (Cef * (8 * (x * Real.log x ^ 2 / T) + 2 * Real.log x) +
                Cef * (x * Real.log x ^ 2 / T + Real.log x)) / h := by gcongr
        _ = 9 * Cef * ((x * Real.log x ^ 2 / T) / h) + 3 * Cef * (Real.log x / h) := by ring
        _ = 9 * Cef * (x ^ (-η) * Real.log x ^ 2) + 3 * Cef * (Real.log x / x ^ θ) := by rw [hdiv_T]
        _ ≤ K_err * (x ^ (-η) * Real.log x ^ 2) + K_err * (Real.log x / x ^ θ) := by
              have hnn1 : 0 ≤ x ^ (-η) * Real.log x ^ 2 := by positivity
              have hnn2 : 0 ≤ Real.log x / x ^ θ := by positivity
              dsimp [K_err]
              gcongr <;> linarith
        _ = K_err * ((x ^ (-η) * Real.log x ^ 2) + (Real.log x / x ^ θ)) := by ring
    have h1d : x ^ (-η) * Real.log x ^ 2 < ε / (4 * K_err) := by
      have hnn : 0 ≤ x ^ (-η) * Real.log x ^ 2 := by positivity
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h1_small
      exact h1_small
    have h2d : Real.log x / x ^ θ < ε / (4 * K_err) := by
      have hnn : 0 ≤ Real.log x / x ^ θ := by positivity
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h2_small
      exact h2_small
    refine hcomb.trans_lt ?_
    calc K_err * ((x ^ (-η) * Real.log x ^ 2) + (Real.log x / x ^ θ))
        < K_err * (ε / (4 * K_err) + ε / (4 * K_err)) :=
          mul_lt_mul_of_pos_left (add_lt_add h1d h2d) hK_err_pos
      _ = ε / 2 := by field_simp [hK_err_pos.ne']; ring
  have hε₀_def : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      T ^ (max A 0 * (1 - σ)) * x ^ (σ - 1) ≤ x ^ (-ε₀ * (1 - σ)) := by
    intro σ _
    dsimp [T, ε₀, Apos]
    rw [← Real.rpow_mul hx_pos.le, ← Real.rpow_add hx_pos]
    refine le_of_eq (congrArg (x ^ ·) ?_)
    ring
  have hzs := shortInterval_zeroSum_bound δ hCzd_pos hCm_pos hε₀_pos hx1 hh_pos hT2 hT_T₀
    hzd hδ_pos hδ_anti hzf hm_bd hε₀_def
  have hlow_d : ∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) < ε / 12 := by
    have hnn : 0 ≤ ∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) :=
      Finset.sum_nonneg fun _ _ => by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hlow_small
    exact hlow_small
  have hhalf_d : Real.log (T + 6) * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) <
      ε / (6 * K_half) := by
    have hlog6 : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hnn : 0 ≤ Real.log (T + 6) * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ) := by
      positivity
    dsimp only [T] at hnn ⊢
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hhalf_small
    exact hhalf_small
  have hzf_d : Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T) < ε / (6 * K_zf) := by
    have hlog6 : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hnn : 0 ≤ Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T) := by positivity
    dsimp only [T, ε₀] at hnn ⊢
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hzf_small
    exact hzf_small
  have hzero_div :
      (∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖) / h <
        ε / 2 := by
    have hb1 : K_half * (Real.log (T + 6) * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ)) <
        ε / 6 := by
      calc K_half * (Real.log (T + 6) * T ^ (A / 2) * Real.log T ^ B * x ^ (-1 / 2 : ℝ))
          < K_half * (ε / (6 * K_half)) := mul_lt_mul_of_pos_left hhalf_d hK_half_pos
        _ = ε / 6 := by field_simp [hK_half_pos.ne']
    have hb2 : K_zf * (Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T)) < ε / 6 := by
      calc K_zf * (Real.log (T + 6) * Real.log T ^ B * x ^ (-ε₀ * δ T))
          < K_zf * (ε / (6 * K_zf)) := mul_lt_mul_of_pos_left hzf_d hK_zf_pos
        _ = ε / 6 := by field_simp [hK_zf_pos.ne']
    have hb3 : 2 * ∑ ρ ∈ S_low, (analyticOrderNatAt xi ρ : ℝ) * x ^ (ρ.re - 1) < ε / 6 := by
      linarith
    dsimp [K_half, K_zf] at hb1 hb2
    exact hzs.trans_lt (by linarith)
  have hfinal_div : |Chebyshev.psi (x + h) - Chebyshev.psi x - h| / h < ε := by
    have h1 : |Chebyshev.psi (x + h) - Chebyshev.psi x - h| / h ≤
        (Cef * ((x + h) * Real.log (x + h) ^ 2 / T + Real.log (x + h)) +
          Cef * (x * Real.log x ^ 2 / T + Real.log x)) / h +
        (∑ ρ ∈ S, (analyticOrderNatAt xi ρ : ℝ) * ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖) / h := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right htri_ef hh_pos.le
    linarith
  rw [Real.dist_eq, Pi.div_apply]
  have heq : (Chebyshev.psi (x + h) - Chebyshev.psi x) / h - 1 =
      (Chebyshev.psi (x + h) - Chebyshev.psi x - h) / h := by
    field_simp [hh_pos.ne']
  change |(Chebyshev.psi (x + h) - Chebyshev.psi x) / h - 1| < ε
  rw [heq, abs_div, abs_of_pos hh_pos]
  exact hfinal_div

/-- **Hoheisel–Ingham short-interval asymptotic for `Chebyshev.theta`**:
for `1 / 2 < θ < 1` with `A * (1 - θ) < 1`, `θ(x + x^θ) - θ(x) ~ x^θ` as `x → ∞`. -/
theorem theta_shortInterval_isEquivalent_of_zeroDensity {A B θ : ℝ}
    (hZD : ZeroDensityHypothesis A B)
    (hEF : TruncatedExplicitFormulaHypothesis)
    (hZF : SuperLogZeroFreeHypothesis)
    (hθ₀ : 1 / 2 < θ) (hθ₁ : θ < 1) (hA : A * (1 - θ) < 1) :
    (fun x : ℝ => Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x) ~[atTop] fun x : ℝ => x ^ θ := by
  have hpsi := psi_shortInterval_isEquivalent_of_zeroDensity hZD hEF hZF hθ₀.le hθ₁ hA
  have hdiff :
      (fun x : ℝ =>
        (Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x) -
          (Chebyshev.psi (x + x ^ θ) - Chebyshev.psi x)) =o[atTop]
        (fun x : ℝ => x ^ θ) := by
    let C₀ : ℝ := (Real.log 4 + 4) * 3
    have hC₀_pos : 0 < C₀ := by positivity
    have hsqrt_o : (fun x : ℝ => Real.sqrt x) =o[atTop] (fun x : ℝ => x ^ θ) := by
      have hsub : 0 < θ - 1 / 2 := by linarith
      have htend : Tendsto (fun x : ℝ => Real.sqrt x / x ^ θ) atTop (𝓝 0) := by
        have h0 := tendsto_rpow_neg_atTop hsub
        refine h0.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
        congr 1
        ring
      rw [Asymptotics.isLittleO_iff_tendsto']
      · simpa using htend
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx h0
        exact absurd h0 (Real.rpow_pos_of_pos hx θ).ne'
    have hO :
        (fun x : ℝ =>
          (Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x) -
            (Chebyshev.psi (x + x ^ θ) - Chebyshev.psi x)) =O[atTop]
          Real.sqrt := by
      refine Asymptotics.IsBigO.of_bound (C₀ * (Real.sqrt 2 + 1)) ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : 0 ≤ x := by linarith
      have hxh_le : x + x ^ θ ≤ 2 * x := by
        have : x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ₁.le
        rw [Real.rpow_one] at this
        linarith
      have hsqrt_xh : Real.sqrt (x + x ^ θ) ≤ Real.sqrt 2 * Real.sqrt x := by
        calc
          Real.sqrt (x + x ^ θ) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hxh_le
          _ = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul zero_le_two x
      have hbd1 := abs_psi_sub_theta_le_mul_sqrt (x + x ^ θ)
      have hbd2 := abs_psi_sub_theta_le_mul_sqrt x
      have hid :
          (Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x) -
            (Chebyshev.psi (x + x ^ θ) - Chebyshev.psi x) =
            -(Chebyshev.psi (x + x ^ θ) - Chebyshev.theta (x + x ^ θ)) +
              (Chebyshev.psi x - Chebyshev.theta x) := by ring
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg x), hid]
      calc
        |-(Chebyshev.psi (x + x ^ θ) - Chebyshev.theta (x + x ^ θ)) +
            (Chebyshev.psi x - Chebyshev.theta x)|
            ≤ |-(Chebyshev.psi (x + x ^ θ) - Chebyshev.theta (x + x ^ θ))| +
                |Chebyshev.psi x - Chebyshev.theta x| :=
              abs_add_le (-(Chebyshev.psi (x + x ^ θ) - Chebyshev.theta (x + x ^ θ)))
                (Chebyshev.psi x - Chebyshev.theta x)
        _ = |Chebyshev.psi (x + x ^ θ) - Chebyshev.theta (x + x ^ θ)| +
              |Chebyshev.psi x - Chebyshev.theta x| := by rw [abs_neg]
        _ ≤ C₀ * Real.sqrt (x + x ^ θ) + C₀ * Real.sqrt x := add_le_add hbd1 hbd2
        _ ≤ C₀ * (Real.sqrt 2 * Real.sqrt x) + C₀ * Real.sqrt x := by gcongr
        _ = C₀ * (Real.sqrt 2 + 1) * Real.sqrt x := by ring
    exact hO.trans_isLittleO hsqrt_o
  exact (hpsi.add_isLittleO hdiff).congr_left (Eventually.of_forall fun x => by
    simp only [Pi.add_apply]; ring)

/-- **Existence of primes in short intervals** `(x, x + x^θ]` for `1 / 2 < θ < 1` under
`ZeroDensityHypothesis A B` (`A * (1 - θ) < 1`), `TruncatedExplicitFormulaHypothesis`, and
`SuperLogZeroFreeHypothesis`. -/
theorem eventually_exists_prime_shortInterval {A B θ : ℝ}
    (hZD : ZeroDensityHypothesis A B)
    (hEF : TruncatedExplicitFormulaHypothesis)
    (hZF : SuperLogZeroFreeHypothesis)
    (hθ₀ : 1 / 2 < θ) (hθ₁ : θ < 1) (hA : A * (1 - θ) < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ θ := by
  have htheta := theta_shortInterval_isEquivalent_of_zeroDensity hZD hEF hZF hθ₀ hθ₁ hA
  rw [Asymptotics.isEquivalent_iff_tendsto_one] at htheta
  swap
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_pos_of_pos hx θ).ne'
  filter_upwards [htheta.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)] with x hx_div hx1
  have hx_pos : 0 < x := by linarith
  have hh_pos : 0 < x ^ θ := Real.rpow_pos_of_pos hx_pos θ
  have hdiff_pos : 0 < Chebyshev.theta (x + x ^ θ) - Chebyshev.theta x := by
    have := (lt_div_iff₀ hh_pos).mp hx_div
    linarith
  rw [theta_eq_sum_primesLE, theta_eq_sum_primesLE] at hdiff_pos
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊x + x ^ θ⌋₊ := by
    intro p hp
    simp only [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.floor_mono (by linarith)), hp.2⟩
  rw [← Finset.sum_sdiff_eq_sub hsub] at hdiff_pos
  have hne : (Nat.primesLE ⌊x + x ^ θ⌋₊ \ Nat.primesLE ⌊x⌋₊).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hdiff_pos
    exact lt_irrefl 0 hdiff_pos
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
  refine ⟨p, hp.1.2, ?_, ?_⟩
  · have hnot : ¬ p ≤ ⌊x⌋₊ := fun hle => hp.2 ⟨hle, hp.1.2⟩
    have hlt_fl : ⌊x⌋₊ < p := Nat.lt_of_not_le hnot
    exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hlt_fl)
  · exact (Nat.cast_le.mpr hp.1.1).trans (Nat.floor_le (by positivity))

/-! ## 3. Bombieri–Vinogradov Theorem and Primitive Character Reduction -/

section BombieriVinogradov

open AnalyticNumberTheory.DirichletLFunctions

/-- Finite set of reduced residue representatives `a ∈ [1, q]` coprime to `q`. -/
def coprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter (fun a => a.Coprime q)

/-- `1` belongs to `coprimeResidues q` whenever `1 ≤ q`. -/
theorem one_mem_coprimeResidues {q : ℕ} (hq : 1 ≤ q) : 1 ∈ coprimeResidues q := by
  simp [coprimeResidues, hq]

/-- `coprimeResidues q` is nonempty whenever `1 ≤ q`. -/
theorem coprimeResidues_nonempty {q : ℕ} (hq : 1 ≤ q) : (coprimeResidues q).Nonempty :=
  ⟨1, one_mem_coprimeResidues hq⟩

/-- Maximum arithmetic-progression error `max_{(a,q)=1} |ψ(x; q, a) - x / φ(q)|` for `1 ≤ q`,
and `0` for `q = 0`. -/
def maxPsiAPError (x : ℝ) (q : ℕ) : ℝ :=
  if hq : 1 ≤ q then
    (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (fun a => |psiAP x q a - x / (q.totient : ℝ)|)
  else 0

/-- Maximum prime-counting arithmetic-progression error `max_{(a,q)=1} |θ(x; q, a) - x / φ(q)|`
for `1 ≤ q`, and `0` for `q = 0`. -/
def maxThetaAPError (x : ℝ) (q : ℕ) : ℝ :=
  if hq : 1 ≤ q then
    (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (fun a => |thetaAP x q a - x / (q.totient : ℝ)|)
  else 0

/-- `maxPsiAPError x q` is always nonnegative. -/
theorem maxPsiAPError_nonneg (x : ℝ) (q : ℕ) : 0 ≤ maxPsiAPError x q := by
  by_cases hq : 1 ≤ q
  · dsimp only [maxPsiAPError]
    split_ifs
    exact (abs_nonneg _).trans
      (Finset.le_sup' (fun a => |psiAP x q a - x / (q.totient : ℝ)|) (one_mem_coprimeResidues hq))
  · simp [maxPsiAPError, hq]

/-- `maxThetaAPError x q` is always nonnegative. -/
theorem maxThetaAPError_nonneg (x : ℝ) (q : ℕ) : 0 ≤ maxThetaAPError x q := by
  by_cases hq : 1 ≤ q
  · dsimp only [maxThetaAPError]
    split_ifs
    exact (abs_nonneg _).trans
      (Finset.le_sup' (fun a => |thetaAP x q a - x / (q.totient : ℝ)|) (one_mem_coprimeResidues hq))
  · simp [maxThetaAPError, hq]

private lemma psiAP_modEq_congr (x : ℝ) {q a b : ℕ} (hab : a ≡ b [MOD q]) :
    psiAP x q a = psiAP x q b := by
  unfold psiAP
  refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) (fun _ _ => rfl)
  exact ⟨fun hn => hn.trans hab, fun hn => hn.trans hab.symm⟩

private lemma thetaAP_modEq_congr (x : ℝ) {q a b : ℕ} (hab : a ≡ b [MOD q]) :
    thetaAP x q a = thetaAP x q b := by
  unfold thetaAP
  refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) (fun _ _ => rfl)
  exact ⟨fun h => ⟨h.1, h.2.trans hab⟩, fun h => ⟨h.1, h.2.trans hab.symm⟩⟩

private lemma mod_rep_mem_coprimeResidues {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    (if a % q = 0 then q else a % q) ∈ coprimeResidues q ∧
      a ≡ (if a % q = 0 then q else a % q) [MOD q] := by
  split_ifs with h0
  · have hq1 : q = 1 := by
      have hdvd : q ∣ a := Nat.dvd_of_mod_eq_zero h0
      have h1 : q ∣ a.gcd q := Nat.dvd_gcd hdvd dvd_rfl
      rw [ha.gcd_eq_one] at h1
      exact Nat.dvd_one.mp h1
    refine ⟨?_, ?_⟩
    · simp [coprimeResidues, hq1]
    · rw [Nat.ModEq, h0, Nat.mod_self]
  · have hpos : 0 < a % q := Nat.pos_of_ne_zero h0
    have hlt : a % q < q := Nat.mod_lt a hq
    have hcop : (a % q).Coprime q := by
      refine Nat.coprime_of_dvd fun p hp hp1 hp2 => ?_
      have hpa : p ∣ a := by
        rw [← Nat.div_add_mod a q]
        exact dvd_add (dvd_mul_of_dvd_left hp2 _) hp1
      exact hp.not_dvd_one (ha.gcd_eq_one ▸ Nat.dvd_gcd hpa hp2)
    refine ⟨?_, ?_⟩
    · simp only [coprimeResidues, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpos, hlt.le⟩, hcop⟩
    · rw [Nat.ModEq, Nat.mod_mod]

/-- Pointwise bound: for any `1 ≤ q` and `a` coprime to `q`,
`|ψ(x; q, a) - x / φ(q)| ≤ maxPsiAPError x q`. -/
theorem abs_psiAP_sub_le_maxPsiAPError (x : ℝ) {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    |psiAP x q a - x / (q.totient : ℝ)| ≤ maxPsiAPError x q := by
  obtain ⟨hmem, hmod⟩ := mod_rep_mem_coprimeResidues hq ha
  rw [psiAP_modEq_congr x hmod]
  have hmax : maxPsiAPError x q =
      (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
        (fun a => |psiAP x q a - x / (q.totient : ℝ)|) := by
    dsimp only [maxPsiAPError]
    split_ifs
    rfl
  rw [hmax]
  exact Finset.le_sup' (fun b => |psiAP x q b - x / (q.totient : ℝ)|) hmem

/-- Pointwise bound: for any `1 ≤ q` and `a` coprime to `q`,
`|θ(x; q, a) - x / φ(q)| ≤ maxThetaAPError x q`. -/
theorem abs_thetaAP_sub_le_maxThetaAPError (x : ℝ) {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    |thetaAP x q a - x / (q.totient : ℝ)| ≤ maxThetaAPError x q := by
  obtain ⟨hmem, hmod⟩ := mod_rep_mem_coprimeResidues hq ha
  rw [thetaAP_modEq_congr x hmod]
  have hmax : maxThetaAPError x q =
      (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
        (fun a => |thetaAP x q a - x / (q.totient : ℝ)|) := by
    dsimp only [maxThetaAPError]
    split_ifs
    rfl
  rw [hmax]
  exact Finset.le_sup' (fun b => |thetaAP x q b - x / (q.totient : ℝ)|) hmem

/-- **Bombieri–Vinogradov statement**: for every `A : ℝ`, there exist `B, C > 0` such that
`∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, max_{(a, q) = 1} |ψ(x; q, a) - x / φ(q)| ≤ C * x / (log x)^A`
uniformly for `x ≥ 2` and `1 ≤ Q ≤ x^(1/2) / (log x)^B`. -/
def BombieriVinogradovStatement : Prop :=
  ∀ A : ℝ, ∃ B C : ℝ, 0 < C ∧ ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
    Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B →
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q ≤ C * x / Real.log x ^ A

private lemma maxThetaAPError_le_maxPsiAPError_add (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    maxThetaAPError x q ≤ maxPsiAPError x q + (Real.log 4 + 4) * 3 * Real.sqrt x := by
  have hmax : maxThetaAPError x q =
      (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
        (fun a => |thetaAP x q a - x / (q.totient : ℝ)|) := by
    dsimp only [maxThetaAPError]
    split_ifs
    rfl
  rw [hmax]
  rw [Finset.sup'_le_iff]
  intro a ha
  have htri : |thetaAP x q a - x / (q.totient : ℝ)| ≤
      |psiAP x q a - x / (q.totient : ℝ)| + |psiAP x q a - thetaAP x q a| := by
    have : thetaAP x q a - x / (q.totient : ℝ) =
        (psiAP x q a - x / (q.totient : ℝ)) - (psiAP x q a - thetaAP x q a) := by ring
    rw [this]
    exact abs_sub _ _
  have h1 : |psiAP x q a - x / (q.totient : ℝ)| ≤ maxPsiAPError x q := by
    dsimp only [maxPsiAPError]
    split_ifs
    exact Finset.le_sup' (fun b => |psiAP x q b - x / (q.totient : ℝ)|) ha
  exact htri.trans (add_le_add h1 (abs_psiAP_sub_thetaAP_le x q a))

/-- **Bombieri–Vinogradov theorem for `thetaAP`**: assuming `BombieriVinogradovStatement`,
for every `A : ℝ` there exist `B, C > 0` such that
`∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, max_{(a, q) = 1} |θ(x; q, a) - x / φ(q)| ≤ C * x / (log x)^A`
uniformly for `x ≥ 2` and `1 ≤ Q ≤ x^(1/2) / (log x)^B`. -/
theorem bombieriVinogradov_thetaAP (hBV : BombieriVinogradovStatement) :
    ∀ A : ℝ, ∃ B C : ℝ, 0 < C ∧ ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B →
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxThetaAPError x q ≤ C * x / Real.log x ^ A := by
  intro A
  obtain ⟨B₁, C₁, hC₁_pos, hbv⟩ := hBV A
  let B : ℝ := max (max B₁ A) 0
  let C₀ : ℝ := (Real.log 4 + 4) * 3
  have hC₀_pos : 0 < C₀ := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp [C₀]
    positivity
  let Q₀ : ℝ := Real.exp (1 / 2 : ℝ) / Real.log 2 ^ B
  have hQ₀_pos : 0 < Q₀ := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    dsimp [Q₀]
    positivity
  let K_small : ℝ := Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) * max 1 (Real.log 2 ^ A)
  have hpsi_e_nn : 0 ≤ Chebyshev.psi (Real.exp 1) := by
    unfold Chebyshev.psi
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  let C : ℝ := max (C₁ + C₀) (K_small + 1)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨B, C, hC_pos, ?_⟩
  intro x Q hx2 hQ1 hQ_bd
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxe : Real.exp 1 ≤ x
  · have hlogx_ge1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx_pos).mpr hxe
    have hlogB1 : Real.log x ^ B₁ ≤ Real.log x ^ B :=
      Real.rpow_le_rpow_of_exponent_le hlogx_ge1 ((le_max_left B₁ A).trans (le_max_left _ 0))
    have hlogA : Real.log x ^ A ≤ Real.log x ^ B :=
      Real.rpow_le_rpow_of_exponent_le hlogx_ge1 ((le_max_right B₁ A).trans (le_max_left _ 0))
    have hlogB_pos : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hlogx_pos B
    have hlogB1_pos : 0 < Real.log x ^ B₁ := Real.rpow_pos_of_pos hlogx_pos B₁
    have hQ_B1 : Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B₁ :=
      hQ_bd.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hx_pos.le _) hlogB1_pos hlogB1)
    have hpsi_sum := hbv hx2 hQ1 hQ_B1
    have hsum_step :
        ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxThetaAPError x q ≤
          ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (maxPsiAPError x q + C₀ * Real.sqrt x) :=
      Finset.sum_le_sum fun q hq =>
        maxThetaAPError_le_maxPsiAPError_add x (Finset.mem_Icc.mp hq).1
    have hcard_le : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
    have hsqrt_sum : ∑ _q ∈ Finset.Icc 1 ⌊Q⌋₊, C₀ * Real.sqrt x ≤ C₀ * x / Real.log x ^ A := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      have hsqrt_mul : Real.sqrt x * x ^ (1 / 2 : ℝ) = x := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx_pos]
        norm_num
      have hQ_A : Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ A :=
        hQ_bd.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hx_pos.le _)
          (Real.rpow_pos_of_pos hlogx_pos A) hlogA)
      calc
        (⌊Q⌋₊ : ℝ) * (C₀ * Real.sqrt x) ≤ Q * (C₀ * Real.sqrt x) := by gcongr
        _ ≤ (x ^ (1 / 2 : ℝ) / Real.log x ^ A) * (C₀ * Real.sqrt x) := by gcongr
        _ = C₀ * (Real.sqrt x * x ^ (1 / 2 : ℝ)) / Real.log x ^ A := by ring
        _ = C₀ * x / Real.log x ^ A := by rw [hsqrt_mul]
    rw [Finset.sum_add_distrib] at hsum_step
    calc
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxThetaAPError x q
          ≤ (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q) +
              ∑ _q ∈ Finset.Icc 1 ⌊Q⌋₊, C₀ * Real.sqrt x := hsum_step
      _ ≤ C₁ * x / Real.log x ^ A + C₀ * x / Real.log x ^ A := add_le_add hpsi_sum hsqrt_sum
      _ = (C₁ + C₀) * x / Real.log x ^ A := by ring
      _ ≤ C * x / Real.log x ^ A := by
            have hlogA_pos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogx_pos A
            gcongr
            exact le_max_left _ _
  · push Not at hxe
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx2
    have hlogx_le1 : Real.log x ≤ 1 := by
      have := Real.log_le_log hx_pos hxe.le
      rwa [Real.log_exp] at this
    have hB_nn : 0 ≤ B := le_max_right _ 0
    have hlog2B : Real.log 2 ^ B ≤ Real.log x ^ B := Real.rpow_le_rpow hlog2_pos.le hlog2_le hB_nn
    have hsqrt_le : x ^ (1 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
      calc
        x ^ (1 / 2 : ℝ) ≤ (Real.exp 1) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hx_pos.le hxe.le (by norm_num)
        _ = Real.exp (1 / 2 : ℝ) := by
              rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul]
    have hQ_le_Q₀ : Q ≤ Q₀ := by
      have hlog2B_pos : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hlog2_pos B
      calc
        Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B := hQ_bd
        _ ≤ Real.exp (1 / 2 : ℝ) / Real.log 2 ^ B :=
              div_le_div₀ (Real.exp_pos _).le hsqrt_le hlog2B_pos hlog2B
        _ = Q₀ := rfl
    have heach_q : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊,
        maxThetaAPError x q ≤ Chebyshev.psi (Real.exp 1) + Real.exp 1 := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      dsimp only [maxThetaAPError]
      split_ifs
      rw [Finset.sup'_le_iff]
      intro a _
      have htheta_nn : 0 ≤ thetaAP x q a := by
        unfold thetaAP
        exact Finset.sum_nonneg fun p hp =>
          Real.log_nonneg (Nat.one_le_cast.mpr (Finset.mem_filter.mp hp).2.1.one_le)
      have htheta_le : thetaAP x q a ≤ Chebyshev.psi (Real.exp 1) := by
        calc
          thetaAP x q a ≤ Chebyshev.theta x := thetaAP_le_theta x q a
          _ ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
          _ ≤ Chebyshev.psi (Real.exp 1) := by
                unfold Chebyshev.psi
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
                exact Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxe.le)
      have hphi1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hdiv_nn : 0 ≤ x / (q.totient : ℝ) := by positivity
      have hdiv_le : x / (q.totient : ℝ) ≤ Real.exp 1 := by
        calc
          x / (q.totient : ℝ) ≤ x / 1 := by gcongr
          _ = x := div_one x
          _ ≤ Real.exp 1 := hxe.le
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hsum_le : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxThetaAPError x q ≤
        Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
      calc
        ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxThetaAPError x q
            ≤ ∑ _q ∈ Finset.Icc 1 ⌊Q⌋₊, (Chebyshev.psi (Real.exp 1) + Real.exp 1) :=
              Finset.sum_le_sum heach_q
        _ = (⌊Q⌋₊ : ℝ) * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ Q * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
              gcongr
        _ ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              gcongr
    have hlogA_le : Real.log x ^ A ≤ max 1 (Real.log 2 ^ A) := by
      by_cases hA0 : 0 ≤ A
      · calc
          Real.log x ^ A ≤ (1 : ℝ) ^ A := Real.rpow_le_rpow hlogx_pos.le hlogx_le1 hA0
          _ = 1 := Real.one_rpow A
          _ ≤ max 1 (Real.log 2 ^ A) := le_max_left _ _
      · push Not at hA0
        have h1 : Real.log x ^ A ≤ Real.log 2 ^ A :=
          Real.rpow_le_rpow_of_nonpos hlog2_pos hlog2_le hA0.le
        exact h1.trans (le_max_right _ _)
    have hlogA_pos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogx_pos A
    have hx_half : (1 : ℝ) ≤ x := by linarith
    calc
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxThetaAPError x q
          ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := hsum_le
      _ ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) * (max 1 (Real.log 2 ^ A) / Real.log x ^ A) := by
            have hge1 : 1 ≤ max 1 (Real.log 2 ^ A) / Real.log x ^ A :=
              (one_le_div hlogA_pos).mpr hlogA_le
            have hnn : 0 ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              have := Real.exp_pos (1 : ℝ)
              positivity
            calc
              Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1)
                  = Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) * 1 := (mul_one _).symm
              _ ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) *
                    (max 1 (Real.log 2 ^ A) / Real.log x ^ A) := by gcongr
      _ = K_small * 1 / Real.log x ^ A := by dsimp [K_small]; ring
      _ ≤ C * x / Real.log x ^ A := by
            have hKC : K_small ≤ C := by dsimp [C]; linarith [le_max_right (C₁ + C₀) (K_small + 1)]
            have hKnn : 0 ≤ K_small := by
              have := Real.exp_pos (1 : ℝ)
              positivity
            gcongr

/-- Replacing a Dirichlet character `χ` modulo `q` by its inducing primitive character
`χ.primitiveCharacter` alters `psiChar x χ` by at most `(Real.log q / Real.log 2) * Real.log x`. -/
theorem norm_psiChar_sub_primitive_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) :
    ‖psiChar x χ - psiChar x χ.primitiveCharacter‖ ≤ (Real.log q / Real.log 2) * Real.log x := by
  have : NeZero q := ⟨by omega⟩
  have hdiff_eq :
      psiChar x χ - psiChar x χ.primitiveCharacter =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (χ n - χ.primitiveCharacter n) * (Λ n : ℂ) := by
    unfold psiChar
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hpoint : ∀ n : ℕ,
      ‖(χ n - χ.primitiveCharacter n) * (Λ n : ℂ)‖ ≤
        (1 - ((1 : DirichletCharacter ℂ q) n).re) * Λ n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine mul_le_mul_of_nonneg_right ?_ ArithmeticFunction.vonMangoldt_nonneg
    by_cases hcop : n.Coprime q
    · have hcop' : IsCoprime (n : ℤ) q := Nat.isCoprime_iff_coprime.mpr hcop
      have h1_eq : (1 : DirichletCharacter ℂ q) n = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hcop)
      have hchi_eq : χ n = χ.primitiveCharacter n := by
        have h1 := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hcop'
        simpa using h1.symm
      simp [hchi_eq, h1_eq]
    · have h1_eq : (1 : DirichletCharacter ℂ q) n = 0 := by
        by_contra hne
        exact hcop ((char_nat_ne_zero_iff_coprime (1 : DirichletCharacter ℂ q) n).mp hne)
      have hchi_eq : χ n = 0 := by
        by_contra hne
        exact hcop ((char_nat_ne_zero_iff_coprime χ n).mp hne)
      have hprim_le : ‖χ.primitiveCharacter n‖ ≤ 1 := χ.primitiveCharacter.norm_le_one n
      rw [hchi_eq, zero_sub, norm_neg, h1_eq, Complex.zero_re, sub_zero]
      exact hprim_le
  have hpsi_sum : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
    unfold Chebyshev.psi
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  have hsum_rhs :
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 - ((1 : DirichletCharacter ℂ q) n).re) * Λ n =
        ((Chebyshev.psi x : ℂ) - psiChar x (1 : DirichletCharacter ℂ q)).re := by
    rw [Complex.sub_re, Complex.ofReal_re, hpsi_sum]
    unfold psiChar
    rw [Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  calc
    ‖psiChar x χ - psiChar x χ.primitiveCharacter‖
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(χ n - χ.primitiveCharacter n) * (Λ n : ℂ)‖ := by
          rw [hdiff_eq]
          exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 - ((1 : DirichletCharacter ℂ q) n).re) * Λ n :=
          Finset.sum_le_sum fun n _ => hpoint n
    _ = ((Chebyshev.psi x : ℂ) - psiChar x (1 : DirichletCharacter ℂ q)).re := hsum_rhs
    _ ≤ ‖(Chebyshev.psi x : ℂ) - psiChar x (1 : DirichletCharacter ℂ q)‖ :=
          Complex.re_le_norm _
    _ ≤ (Real.log q / Real.log 2) * Real.log x := norm_psi_sub_psiChar_one_le hx hq

private lemma sum_Icc_divisors_swap (N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 N, ∑ d ∈ r.divisors, f d (r / d) =
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), f d k := by
  trans ∑ p ∈ (Finset.Icc 1 N).sigma (fun r => r.divisors), f p.2 (p.1 / p.2)
  · exact Finset.sum_sigma' (Finset.Icc 1 N) (fun r => r.divisors) (fun r d => f d (r / d))
  trans ∑ q ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)), f q.1 q.2
  swap
  · exact (Finset.sum_sigma' (Finset.Icc 1 N) (fun d => Finset.Icc 1 (N / d)) (fun d k => f d k)).symm
  refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1 / p.2⟩) (fun q _ => ⟨q.1 * q.2, q.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hr1, hrN⟩, hd_dvd, hr0⟩ := hp
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hr1
    have hq_pos : 0 < r / d := Nat.div_pos (Nat.le_of_dvd hr1 hd_dvd) hd_pos
    exact ⟨⟨hd_pos, (Nat.le_of_dvd hr1 hd_dvd).trans hrN⟩,
      ⟨hq_pos, Nat.div_le_div_right hrN⟩⟩
  · rintro ⟨d, k⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨hd1, _⟩, ⟨hk1, hkN⟩⟩ := hq
    have hdk_pos : 1 ≤ d * k := Nat.mul_pos hd1 hk1
    have hdk_le : d * k ≤ N := (Nat.mul_le_mul_left d hkN).trans (Nat.mul_div_le N d)
    exact ⟨⟨hdk_pos, hdk_le⟩, ⟨dvd_mul_right d k, Nat.pos_iff_ne_zero.mp hdk_pos⟩⟩
  · rintro ⟨r, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    ext <;> dsimp
    · exact Nat.mul_div_cancel' hp.2.1
    · rfl
  · rintro ⟨d, k⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hq
    ext <;> dsimp
    exact heq_of_eq (Nat.mul_div_cancel_left k hq.1.1)
  · rintro ⟨r, d⟩ _
    rfl

private lemma sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ ≤ 1 + Real.log (N + 2) := by
  by_cases hN0 : N = 0
  · subst hN0
    have : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
    simp; linarith
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hsplit : ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ =
      1 + ∑ k ∈ Finset.Ico 2 (N + 1), (k : ℝ)⁻¹ := by
    have h1 : Finset.Icc 1 N = insert 1 (Finset.Ico 2 (N + 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h1, Finset.sum_insert (by simp)]
    norm_num
  rw [hsplit]
  have hterm : ∀ k ∈ Finset.Ico 2 (N + 1),
      (k : ℝ)⁻¹ ≤ Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk_pos : (0 : ℝ) < k := by positivity
    have hkm_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hkm_eq : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hle := Real.log_le_sub_one_of_pos (div_pos hkm_pos hk_pos)
    rw [Real.log_div hkm_pos.ne' hk_pos.ne', hkm_eq] at hle
    have hid : ((k : ℝ) - 1) / (k : ℝ) - 1 = -(k : ℝ)⁻¹ := by
      field_simp [hk_pos.ne']
      ring
    rw [hid] at hle
    rw [hkm_eq]
    linarith
  have htele : ∑ k ∈ Finset.Ico 2 (N + 1), (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
      Real.log (N : ℝ) := by
    have hIco : Finset.Ico 2 (N + 1) = (Finset.Ico 1 N).image (· + 1) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_image]
      constructor
      · intro ⟨h2, hN1⟩
        exact ⟨k - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨m, ⟨h1, hm⟩, rfl⟩
        omega
    rw [hIco, Finset.sum_image (fun a _ b _ h => by omega)]
    have hsub : ∑ m ∈ Finset.Ico 1 N,
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (((m + 1 - 1 : ℕ) : ℝ))) =
        ∑ m ∈ Finset.Ico 1 N, (Real.log (((m + 1 : ℕ) : ℝ)) - Real.log (m : ℝ)) := by
      refine Finset.sum_congr rfl fun m _ => by simp
    rw [hsub]
    have htele_ind : ∀ n : ℕ, 1 ≤ n →
        ∑ m ∈ Finset.Ico 1 n, (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) =
          Real.log (n : ℝ) - Real.log 1 := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
          rw [Finset.sum_Ico_succ_top hk, ih]
          push_cast
          ring
    rw [htele_ind N hN1, Real.log_one, sub_zero]
  have hsum_le : ∑ k ∈ Finset.Ico 2 (N + 1), (k : ℝ)⁻¹ ≤ Real.log (N : ℝ) :=
    (Finset.sum_le_sum hterm).trans_eq htele
  have hlog_le : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by linarith)
  linarith

private lemma primeFactors_prod_eq : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    (∏ p ∈ S, p).primeFactors = S := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert p S hpS ih =>
      intro hprimes
      have hp : p.Prime := hprimes p (Finset.mem_insert_self p S)
      have hS_primes : ∀ q ∈ S, q.Prime := fun q hq => hprimes q (Finset.mem_insert_of_mem hq)
      have hprod_ne : ∏ q ∈ S, q ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr fun q hq => (hS_primes q hq).ne_zero
      rw [Finset.prod_insert hpS, Nat.primeFactors_mul hp.ne_zero hprod_ne,
        hp.primeFactors, ih hS_primes]
      ext q
      simp

private lemma prod_rpow_half_le_two_mul_prod_sub_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (p : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) := by
  have hge3 : ∀ p ∈ S, p ≠ 2 → (p : ℝ) ^ (1 / 2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    intro p hp hne2
    have hprime := hS p hp
    have hp3 : 3 ≤ p := by
      have := hprime.two_le
      omega
    have hkm : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    have hsq : (p : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
      rw [hkm]
      have hp_r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      nlinarith
    calc
      (p : ℝ) ^ (1 / 2 : ℝ) ≤ (((p - 1 : ℕ) : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hsq (by norm_num)
      _ = ((p - 1 : ℕ) : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
  by_cases h2 : 2 ∈ S
  · have hprod1 : ∏ p ∈ S, (p : ℝ) ^ (1 / 2 : ℝ) =
        (2 : ℝ) ^ (1 / 2 : ℝ) * ∏ p ∈ S.erase 2, (p : ℝ) ^ (1 / 2 : ℝ) :=
      (Finset.mul_prod_erase S (fun p => (p : ℝ) ^ (1 / 2 : ℝ)) h2).symm
    have hprod2 : ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) =
        ((2 - 1 : ℕ) : ℝ) * ∏ p ∈ S.erase 2, ((p - 1 : ℕ) : ℝ) :=
      (Finset.mul_prod_erase S (fun p => ((p - 1 : ℕ) : ℝ)) h2).symm
    have hrest : ∏ p ∈ S.erase 2, (p : ℝ) ^ (1 / 2 : ℝ) ≤ ∏ p ∈ S.erase 2, ((p - 1 : ℕ) : ℝ) := by
      gcongr with p hp
      exact hge3 p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    have h2_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = ((2 : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by norm_num
        _ = 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [hprod1, hprod2]
    norm_num
    gcongr
  · have hrest : ∏ p ∈ S, (p : ℝ) ^ (1 / 2 : ℝ) ≤ ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) := by
      gcongr with p hp
      exact hge3 p hp (fun h => h2 (h ▸ hp))
    have hnn : 0 ≤ ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
    linarith

/-- Sum of reciprocals of Euler's totient function up to `N`: there exists a constant `C > 0`
such that `∑ r ∈ Finset.Icc 1 N, (r.totient : ℝ)⁻¹ ≤ C * Real.log (N + 2)` for all `N : ℕ`. -/
theorem sum_inv_totient_le_mul_log :
    ∃ C > 0, ∀ N : ℕ, ∑ r ∈ Finset.Icc 1 N, (r.totient : ℝ)⁻¹ ≤ C * Real.log (N + 2) := by
  have hsumm : Summable (fun d : ℕ => ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  let S_half : ℝ := ∑' d : ℕ, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹
  have hS_half_pos : 0 < S_half := by
    have hle := hsumm.le_tsum (1 : ℕ) (fun _ _ => by positivity)
    norm_num at hle
    linarith
  let C : ℝ := 2 * S_half * (1 / Real.log 2 + 1)
  have hC_pos : 0 < C := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  refine ⟨C, hC_pos, fun N => ?_⟩
  have hinv_r : ∀ r ∈ Finset.Icc 1 N,
      (r.totient : ℝ)⁻¹ ≤
        ∑ d ∈ r.divisors, 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * ((r / d : ℕ) : ℝ)⁻¹ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr_pos : 0 < r := hr1
    have hphi_pos : 0 < r.totient := Nat.totient_pos.mpr hr1
    have hmul_fac := Nat.totient_mul_prod_primeFactors r
    have hmul_real : (r.totient : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ) =
        (r : ℝ) * ∏ p ∈ r.primeFactors, ((p - 1 : ℕ) : ℝ) := by
      have h := congrArg (Nat.cast (R := ℝ)) hmul_fac
      push_cast at h
      exact h
    have hprod_pm1_pos : 0 < ∏ p ∈ r.primeFactors, ((p - 1 : ℕ) : ℝ) := by
      refine Finset.prod_pos fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      exact_mod_cast Nat.sub_pos_of_lt hp_prime.one_lt
    have hprod_p_pos : 0 < ∏ p ∈ r.primeFactors, (p : ℝ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hratio_eq : (r : ℝ) / (r.totient : ℝ) =
        ∏ p ∈ r.primeFactors, (1 + ((p - 1 : ℕ) : ℝ)⁻¹) := by
      have h1 : (r : ℝ) / (r.totient : ℝ) =
          (∏ p ∈ r.primeFactors, (p : ℝ)) / ∏ p ∈ r.primeFactors, ((p - 1 : ℕ) : ℝ) := by
        field_simp [show (r.totient : ℝ) ≠ 0 by exact_mod_cast hphi_pos.ne', hprod_pm1_pos.ne']
        linarith
      rw [h1, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hkm : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hp_prime.one_lt.le, Nat.cast_one]
      have hpm1_pos : 0 < ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hp_prime.one_lt
      rw [div_eq_iff hpm1_pos.ne', add_mul, one_mul, inv_mul_cancel₀ hpm1_pos.ne', hkm]
      ring
    rw [Finset.prod_one_add] at hratio_eq
    have hr_inv_eq : (r.totient : ℝ)⁻¹ =
        ∑ S ∈ r.primeFactors.powerset, (r : ℝ)⁻¹ * ∏ p ∈ S, ((p - 1 : ℕ) : ℝ)⁻¹ := by
      have h : (r.totient : ℝ)⁻¹ = (r : ℝ)⁻¹ * ((r : ℝ) / (r.totient : ℝ)) := by
        field_simp [show (r : ℝ) ≠ 0 by exact_mod_cast hr_pos.ne',
          show (r.totient : ℝ) ≠ 0 by exact_mod_cast hphi_pos.ne']
      rw [h, hratio_eq, Finset.mul_sum]
    have hterm_S : ∀ S ∈ r.primeFactors.powerset,
        (r : ℝ)⁻¹ * ∏ p ∈ S, ((p - 1 : ℕ) : ℝ)⁻¹ ≤
          2 * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (-3 / 2 : ℝ) * ((r / (∏ p ∈ S, p) : ℕ) : ℝ)⁻¹ := by
      intro S hS
      have hS_sub : S ⊆ r.primeFactors := Finset.mem_powerset.mp hS
      have hS_primes : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS_sub hp)
      let d : ℕ := ∏ p ∈ S, p
      have hd_pos : 0 < d := Finset.prod_pos fun p hp => (hS_primes p hp).pos
      have hd_dvd : d ∣ r :=
        (Finset.prod_dvd_prod_of_subset _ _ id hS_sub).trans (Nat.prod_primeFactors_dvd r)
      have hr_eq : r = d * (r / d) := (Nat.mul_div_cancel' hd_dvd).symm
      have hk_pos : 0 < r / d := Nat.div_pos (Nat.le_of_dvd hr_pos hd_dvd) hd_pos
      have hhalf_eq : (d : ℝ) ^ (1 / 2 : ℝ) = ∏ p ∈ S, (p : ℝ) ^ (1 / 2 : ℝ) := by
        have hgen : ∀ T : Finset ℕ, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (1 / 2 : ℝ) =
            ∏ p ∈ T, (p : ℝ) ^ (1 / 2 : ℝ) := by
          intro T
          induction T using Finset.induction_on with
          | empty => simp
          | @insert p T hpT ih =>
              rw [Finset.prod_insert hpT, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
                Finset.prod_insert hpT, ih]
        exact hgen S
      have hprod_le := prod_rpow_half_le_two_mul_prod_sub_one S hS_primes
      rw [← hhalf_eq] at hprod_le
      have hprod_pm1_pos : 0 < ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) := by
        refine Finset.prod_pos fun p hp => ?_
        exact_mod_cast Nat.sub_pos_of_lt (hS_primes p hp).one_lt
      have hinv_prod : ∏ p ∈ S, ((p - 1 : ℕ) : ℝ)⁻¹ ≤ 2 * (d : ℝ) ^ (-1 / 2 : ℝ) := by
        rw [Finset.prod_inv_distrib, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
          Real.rpow_neg (by positivity)]
        have h1 : (∏ p ∈ S, ((p - 1 : ℕ) : ℝ))⁻¹ ≤ (2⁻¹ * (d : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
          gcongr
          linarith
        have h2 : (2⁻¹ * (d : ℝ) ^ (1 / 2 : ℝ))⁻¹ = 2 * ((d : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
          rw [mul_inv, inv_inv]
        exact h1.trans_eq h2
      have hpow_split : (d : ℝ)⁻¹ * (d : ℝ) ^ (-1 / 2 : ℝ) = (d : ℝ) ^ (-3 / 2 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add (by exact_mod_cast hd_pos)]
        congr 1; norm_num
      have hr_inv : (r : ℝ)⁻¹ = (d : ℝ)⁻¹ * ((r / d : ℕ) : ℝ)⁻¹ := by
        nth_rw 1 [hr_eq]
        push_cast
        rw [mul_inv]
      calc
        (r : ℝ)⁻¹ * ∏ p ∈ S, ((p - 1 : ℕ) : ℝ)⁻¹
            ≤ ((d : ℝ)⁻¹ * ((r / d : ℕ) : ℝ)⁻¹) * (2 * (d : ℝ) ^ (-1 / 2 : ℝ)) := by
              rw [hr_inv]
              gcongr
        _ = 2 * ((d : ℝ)⁻¹ * (d : ℝ) ^ (-1 / 2 : ℝ)) * ((r / d : ℕ) : ℝ)⁻¹ := by ring
        _ = 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * ((r / d : ℕ) : ℝ)⁻¹ := by rw [hpow_split]
    have hpow_le_div :
        ∑ S ∈ r.primeFactors.powerset,
            2 * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (-3 / 2 : ℝ) * ((r / (∏ p ∈ S, p) : ℕ) : ℝ)⁻¹ ≤
          ∑ d ∈ r.divisors, 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * ((r / d : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_le_sum_of_injOn (fun S => ∏ p ∈ S, p) ?_ ?_ ?_ (fun _ _ _ => by positivity)
      · intro S₁ hS₁ S₂ hS₂ heq
        have hp1 := primeFactors_prod_eq S₁ fun p hp =>
          Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS₁ hp)
        have hp2 := primeFactors_prod_eq S₂ fun p hp =>
          Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS₂ hp)
        dsimp only at heq
        rw [← hp1, ← hp2, heq]
      · intro d hd
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
        have hS_sub := Finset.mem_powerset.mp hS
        exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr
          ⟨(Finset.prod_dvd_prod_of_subset _ _ id hS_sub).trans (Nat.prod_primeFactors_dvd r), hr_pos.ne'⟩)
      · intro S _
        exact le_rfl
    rw [hr_inv_eq]
    exact (Finset.sum_le_sum hterm_S).trans hpow_le_div
  have hsum1 : ∑ r ∈ Finset.Icc 1 N, (r.totient : ℝ)⁻¹ ≤
      ∑ r ∈ Finset.Icc 1 N, ∑ d ∈ r.divisors, 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * ((r / d : ℕ) : ℝ)⁻¹ :=
    Finset.sum_le_sum hinv_r
  rw [sum_Icc_divisors_swap N (fun d k => 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * (k : ℝ)⁻¹)] at hsum1
  have hsum2 :
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * (k : ℝ)⁻¹ ≤
        ∑ d ∈ Finset.Icc 1 N, 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * (1 + Real.log (N + 2)) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [← Finset.mul_sum]
    have hlog_mono : Real.log ((N / d : ℕ) + 2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have hnd : (N / d : ℕ) ≤ N := Nat.div_le_self N d
      have hnd_r : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnd
      linarith
    have hk_le := (sum_Icc_inv_le_one_add_log (N / d)).trans (add_le_add_right hlog_mono 1)
    exact mul_le_mul_of_nonneg_left hk_le (by positivity)
  have hsum_d_le : ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-3 / 2 : ℝ) ≤ S_half := by
    have heq : ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-3 / 2 : ℝ) =
        ∑ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
    rw [heq]
    exact hsumm.sum_le_tsum (Finset.Icc 1 N) (fun _ _ => by positivity)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogN2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log zero_lt_two (by linarith)
  have hone_add_log : 1 + Real.log ((N : ℝ) + 2) ≤ (1 / Real.log 2 + 1) * Real.log ((N : ℝ) + 2) := by
    have h1 : 1 ≤ (1 / Real.log 2) * Real.log ((N : ℝ) + 2) := by
      rw [one_div_mul_eq_div, le_div_iff₀ hlog2_pos, one_mul]
      exact hlogN2
    linarith
  calc
    ∑ r ∈ Finset.Icc 1 N, (r.totient : ℝ)⁻¹
        ≤ ∑ d ∈ Finset.Icc 1 N, 2 * (d : ℝ) ^ (-3 / 2 : ℝ) * (1 + Real.log ((N : ℝ) + 2)) :=
          hsum1.trans hsum2
    _ = 2 * (∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-3 / 2 : ℝ)) * (1 + Real.log ((N : ℝ) + 2)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ 2 * S_half * ((1 / Real.log 2 + 1) * Real.log ((N : ℝ) + 2)) := by
          have hnn : 0 ≤ 1 + Real.log ((N : ℝ) + 2) := by linarith
          gcongr
    _ = C * Real.log ((N : ℝ) + 2) := by dsimp [C]; ring

private lemma psiChar_primitiveCharacter_changeLevel {x : ℝ} {q d : ℕ}
    [NeZero q] [NeZero d] (hd : d ∣ q) {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive) :
    psiChar x (DirichletCharacter.changeLevel hd ψ).primitiveCharacter = psiChar x ψ := by
  have hψ_cond : ψ.conductor = d := (DirichletCharacter.isPrimitive_def ψ).mp hψ
  unfold psiChar
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have h1 : (DirichletCharacter.changeLevel hd ψ).primitiveCharacter (n : ℤ) =
      ψ.primitiveCharacter (n : ℤ) :=
    DirichletCharacter.primitiveCharacter_changeLevel_apply hd ψ (n : ℤ)
  have h2 : ψ.primitiveCharacter (n : ℤ) = ψ (n : ℤ) := by
    by_cases hcop : IsCoprime (n : ℤ) d
    · exact DirichletCharacter.primitiveCharacter_apply_of_isCoprime ψ hcop
    · have h0a : ψ (n : ℤ) = 0 := (DirichletCharacter.apply_eq_zero_iff ψ _).mpr hcop
      have h0b : ψ.primitiveCharacter (n : ℤ) = 0 := by
        rw [DirichletCharacter.apply_eq_zero_iff]
        rwa [hψ_cond]
      rw [h0a, h0b]
  simpa using h1.trans h2

private lemma sum_erase_one_norm_psiChar_primitive_le {x : ℝ} {q : ℕ} (hq : 1 ≤ q) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChar x χ.primitiveCharacter‖ ≤
      ∑ d ∈ q.divisors with 2 ≤ d,
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
          (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ := by
  have : NeZero q := ⟨by omega⟩
  let S_d := q.divisors.filter (fun d => 2 ≤ d)
  have hfib :
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖psiChar x χ.primitiveCharacter‖ =
        ∑ d ∈ S_d,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
            (fun χ => χ.conductor = d), ‖psiChar x χ.primitiveCharacter‖ := by
    refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro χ hχ
    have hne1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have hcond_ne1 : χ.conductor ≠ 1 := by
      intro h1
      exact hne1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1)
    have hcond_pos : 0 < χ.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ)
    simp only [S_d, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨χ.conductor_dvd_level, (by omega : q ≠ 0)⟩, by omega⟩
  rw [hfib]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd_dvd : d ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hd2 : 2 ≤ d := (Finset.mem_filter.mp hd).2
  have : NeZero d := ⟨by omega⟩
  refine le_of_eq (Finset.sum_bij (fun ψ _ => DirichletCharacter.changeLevel hd_dvd ψ)
    ?_ ?_ ?_ ?_).symm
  · intro ψ hψ
    have hprim : ψ.IsPrimitive := (Finset.mem_filter.mp hψ).2
    have hcond : (DirichletCharacter.changeLevel hd_dvd ψ).conductor = d := by
      rw [DirichletCharacter.conductor_changeLevel ψ hd_dvd,
        (DirichletCharacter.isPrimitive_def ψ).mp hprim]
    have hne1 : DirichletCharacter.changeLevel hd_dvd ψ ≠ 1 := by
      intro h1
      have hc1 : (DirichletCharacter.changeLevel hd_dvd ψ).conductor = 1 := by
        rw [h1, DirichletCharacter.conductor_one]
      omega
    simp [Finset.mem_filter, Finset.mem_erase, hne1, hcond]
  · intro ψ₁ _ ψ₂ _ heq
    exact DirichletCharacter.changeLevel_injective hd_dvd heq
  · intro χ hχ
    have hcd : χ.conductor = d := (Finset.mem_filter.mp hχ).2
    refine ⟨DirichletCharacter.changeLevel (dvd_of_eq hcd) χ.primitiveCharacter, ?_, ?_⟩
    · have hprim : (DirichletCharacter.changeLevel (dvd_of_eq hcd) χ.primitiveCharacter).IsPrimitive := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_changeLevel,
          (DirichletCharacter.isPrimitive_def χ.primitiveCharacter).mp
            χ.primitiveCharacter_isPrimitive, hcd]
      simp [hprim]
    · rw [← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
  · intro ψ hψ
    rw [psiChar_primitiveCharacter_changeLevel hd_dvd (Finset.mem_filter.mp hψ).2]

/-- **Primitive character reduction for Bombieri–Vinogradov**:
reduces `∑ q ≤ Q, maxPsiAPError x q` to the `q = 1` PNT term `|ψ(x) - x| * log(Q + 2)`,
a negligible modulus-change error `Q * (log Q / log 2) * log x`, and the primitive character sum
`log(Q + 2) * ∑ 2 ≤ d ≤ Q, (φ d)⁻¹ * ∑ ψ primitive mod d, ‖psiChar x ψ‖`. -/
theorem bombieriVinogradov_primitive_char_reduction :
    ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q ≤
        |Chebyshev.psi x - x| * (C * Real.log (Q + 2)) +
          Q * (Real.log Q / Real.log 2) * Real.log x +
          C * Real.log (Q + 2) * ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
            ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
              (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ := by
  obtain ⟨C_φ, hCφ_pos, hphi_sum⟩ := sum_inv_totient_le_mul_log
  refine ⟨C_φ, hCφ_pos, ?_⟩
  intro x Q hx2 hQ1
  have hx1 : 1 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsingle_q : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊,
      maxPsiAPError x q ≤
        (q.totient : ℝ)⁻¹ * |Chebyshev.psi x - x| +
          (Real.log q / Real.log 2) * Real.log x +
          (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with 2 ≤ d,
            ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
              (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : q ≠ 0 := by omega
    have hphi_pos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq1
    dsimp only [maxPsiAPError]
    split_ifs
    rw [Finset.sup'_le_iff]
    intro a ha
    have ha_cop : a.Coprime q := (Finset.mem_filter.mp ha).2
    have horth := psiAP_eq_inv_totient_mul_sum_psiChar (x := x) hq0 ha_cop
    have h1_mem : (1 : DirichletCharacter ℂ q) ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) :=
      Finset.mem_univ _
    have hsplit_chi :
        ∑ χ : DirichletCharacter ℂ q, star (χ a) * psiChar x χ =
          star ((1 : DirichletCharacter ℂ q) a) * psiChar x (1 : DirichletCharacter ℂ q) +
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              star (χ a) * psiChar x χ := by
      rw [← Finset.add_sum_erase Finset.univ (fun χ : DirichletCharacter ℂ q => star (χ a) * psiChar x χ) h1_mem]
    have h1a : (1 : DirichletCharacter ℂ q) a = 1 := by
      have hunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha_cop
      exact MulChar.one_apply hunit
    have hid_complex :
        ((psiAP x q a - x / (q.totient : ℝ) : ℝ) : ℂ) =
          (q.totient : ℂ)⁻¹ * (((Chebyshev.psi x : ℂ) - (x : ℂ)) +
            (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)) +
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter) +
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              star (χ a) * psiChar x χ.primitiveCharacter) := by
      push_cast
      rw [horth, hsplit_chi, h1a, star_one, one_mul]
      have hdecomp :
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, star (χ a) * psiChar x χ =
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter) +
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                star (χ a) * psiChar x χ.primitiveCharacter := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun χ _ => by ring
      rw [hdecomp]
      field_simp [hphi_pos.ne']
      ring
    have hnorm_eq : |psiAP x q a - x / (q.totient : ℝ)| =
        ‖((psiAP x q a - x / (q.totient : ℝ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hchi_one_norm :
        ‖psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)‖ ≤
          (Real.log q / Real.log 2) * Real.log x := by
      rw [norm_sub_rev]
      exact norm_psi_sub_psiChar_one_le hx1 hq1
    have hstar_le : ∀ χ : DirichletCharacter ℂ q, ‖star (χ a)‖ ≤ 1 := fun χ =>
      (norm_star (χ a)).trans_le (χ.norm_le_one _)
    have hsum_diff_norm :
        ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter)‖ ≤
          ((q.totient : ℝ) - 1) * ((Real.log q / Real.log 2) * Real.log x) := by
      calc
        ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter)‖
            ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                ‖star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter)‖ := norm_sum_le _ _
        _ ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              ((Real.log q / Real.log 2) * Real.log x) := by
            refine Finset.sum_le_sum fun χ _ => ?_
            rw [norm_mul]
            calc
              ‖star (χ a)‖ * ‖psiChar x χ - psiChar x χ.primitiveCharacter‖
                  ≤ 1 * ((Real.log q / Real.log 2) * Real.log x) :=
                    mul_le_mul (hstar_le χ) (norm_psiChar_sub_primitive_le hx1 hq1 χ)
                      (norm_nonneg _) zero_le_one
              _ = (Real.log q / Real.log 2) * Real.log x := one_mul _
        _ = ((q.totient : ℝ) - 1) * ((Real.log q / Real.log 2) * Real.log x) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem h1_mem, Finset.card_univ]
              have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
                have : NeZero q := ⟨hq0⟩
                exact card_dirichletCharacter_eq_totient
              have hle1 : 1 ≤ q.totient := Nat.totient_pos.mpr hq1
              rw [hcard, nsmul_eq_mul, Nat.cast_sub hle1, Nat.cast_one]
    have hsum_prim_norm :
        ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            star (χ a) * psiChar x χ.primitiveCharacter‖ ≤
          ∑ d ∈ q.divisors with 2 ≤ d,
            ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
              (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ := by
      calc
        ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            star (χ a) * psiChar x χ.primitiveCharacter‖
            ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                ‖star (χ a) * psiChar x χ.primitiveCharacter‖ := norm_sum_le _ _
        _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              ‖psiChar x χ.primitiveCharacter‖ := by
            refine Finset.sum_le_sum fun χ _ => ?_
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (hstar_le χ)
        _ ≤ _ := sum_erase_one_norm_psiChar_primitive_le hq1
    have hpsi_x_norm : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ = |Chebyshev.psi x - x| := by
      have : (Chebyshev.psi x : ℂ) - (x : ℂ) = ((Chebyshev.psi x - x : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm_eq, hid_complex, norm_mul, norm_inv, Complex.norm_natCast]
    have htri :
        ‖((Chebyshev.psi x : ℂ) - (x : ℂ)) +
            (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)) +
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter) +
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              star (χ a) * psiChar x χ.primitiveCharacter‖ ≤
          |Chebyshev.psi x - x| +
            (q.totient : ℝ) * ((Real.log q / Real.log 2) * Real.log x) +
            ∑ d ∈ q.divisors with 2 ≤ d,
              ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
                (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ := by
      have h1 := norm_add_le
        (((Chebyshev.psi x : ℂ) - (x : ℂ)) +
          (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)) +
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter))
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          star (χ a) * psiChar x χ.primitiveCharacter)
      have h2 := norm_add_le
        (((Chebyshev.psi x : ℂ) - (x : ℂ)) +
          (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)))
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          star (χ a) * (psiChar x χ - psiChar x χ.primitiveCharacter))
      have h3 := norm_add_le
        ((Chebyshev.psi x : ℂ) - (x : ℂ))
        (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ))
      rw [hpsi_x_norm] at h3
      linarith
    calc
      (q.totient : ℝ)⁻¹ * ‖_‖
          ≤ (q.totient : ℝ)⁻¹ * (|Chebyshev.psi x - x| +
              (q.totient : ℝ) * ((Real.log q / Real.log 2) * Real.log x) +
              ∑ d ∈ q.divisors with 2 ≤ d,
                ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
                  (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖) := by
            gcongr
      _ = (q.totient : ℝ)⁻¹ * |Chebyshev.psi x - x| +
            (Real.log q / Real.log 2) * Real.log x +
            (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with 2 ≤ d,
              ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
                (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ := by
            field_simp [hphi_pos.ne']
  have hsum_all := Finset.sum_le_sum hsingle_q
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_all
  have hpart1 :
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ * |Chebyshev.psi x - x| ≤
        |Chebyshev.psi x - x| * (C_φ * Real.log (Q + 2)) := by
    rw [← Finset.sum_mul]
    have hlog_mono : Real.log ((⌊Q⌋₊ : ℝ) + 2) ≤ Real.log (Q + 2) := by
      refine Real.log_le_log (by positivity) ?_
      linarith [Nat.floor_le (by linarith : 0 ≤ Q)]
    have hphi := (hphi_sum ⌊Q⌋₊).trans (mul_le_mul_of_nonneg_left hlog_mono hCφ_pos.le)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hphi (abs_nonneg _)
  have hpart2 :
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (Real.log q / Real.log 2) * Real.log x ≤
        Q * (Real.log Q / Real.log 2) * Real.log x := by
    have hterm : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊,
        (Real.log q / Real.log 2) * Real.log x ≤ (Real.log Q / Real.log 2) * Real.log x := by
      intro q hq
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      have hq_le : (q : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hq).2
      have hqQ : (q : ℝ) ≤ Q := hq_le.trans (Nat.floor_le (by linarith))
      have hlog_le : Real.log q ≤ Real.log Q := Real.log_le_log (by linarith) hqQ
      gcongr
    calc
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (Real.log q / Real.log 2) * Real.log x
          ≤ ∑ _q ∈ Finset.Icc 1 ⌊Q⌋₊, (Real.log Q / Real.log 2) * Real.log x :=
            Finset.sum_le_sum hterm
      _ = (⌊Q⌋₊ : ℝ) * ((Real.log Q / Real.log 2) * Real.log x) := by simp
      _ ≤ Q * ((Real.log Q / Real.log 2) * Real.log x) := by
            have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
            have hlogQ_nn : 0 ≤ Real.log Q := Real.log_nonneg hQ1
            gcongr
      _ = Q * (Real.log Q / Real.log 2) * Real.log x := by ring
  let F : ℕ → ℝ := fun d =>
    ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
      (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖
  have hF_nn : ∀ d : ℕ, 0 ≤ F d := fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpart3 :
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with 2 ≤ d, F d ≤
        C_φ * Real.log (Q + 2) * ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ * F d := by
    have hrw1 :
        ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with 2 ≤ d, F d =
          ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ d ∈ q.divisors,
            if 2 ≤ d then ((d * (q / d)).totient : ℝ)⁻¹ * F d else 0 := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_dvd : d ∣ q := (Nat.mem_divisors.mp hd).1
      split_ifs <;> simp [Nat.mul_div_cancel' hd_dvd]
    rw [hrw1, sum_Icc_divisors_swap ⌊Q⌋₊ (fun d k => if 2 ≤ d then ((d * k).totient : ℝ)⁻¹ * F d else 0)]
    have hrw2 :
        ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (if 2 ≤ d then ((d * k).totient : ℝ)⁻¹ * F d else 0) ≤
          ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊,
            (C_φ * Real.log (Q + 2)) * ((d.totient : ℝ)⁻¹ * F d) := by
      have hsub_12 :
          ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
              (if 2 ≤ d then ((d * k).totient : ℝ)⁻¹ * F d else 0) =
            ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
              ((d * k).totient : ℝ)⁻¹ * F d := by
        have hite : ∀ d ∈ Finset.Icc 1 ⌊Q⌋₊,
            (∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), if 2 ≤ d then ((d * k).totient : ℝ)⁻¹ * F d else 0) =
              if 2 ≤ d then ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), ((d * k).totient : ℝ)⁻¹ * F d else 0 :=
          fun d _ => by split_ifs <;> simp
        rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
        have hflt : (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => 2 ≤ d) = Finset.Icc 2 ⌊Q⌋₊ := by
          ext d; simp [Finset.mem_Icc]; omega
        rw [hflt]
      rw [hsub_12]
      refine Finset.sum_le_sum fun d hd => ?_
      have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
      have hterm_k : ∀ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
          ((d * k).totient : ℝ)⁻¹ * F d ≤ (k.totient : ℝ)⁻¹ * ((d.totient : ℝ)⁻¹ * F d) := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hphi_d : 0 < d.totient := Nat.totient_pos.mpr (by omega)
        have hphi_k : 0 < k.totient := Nat.totient_pos.mpr hk1
        have hmult : d.totient * k.totient ≤ (d * k).totient := Nat.totient_super_multiplicative d k
        have hinv : ((d * k).totient : ℝ)⁻¹ ≤ (d.totient : ℝ)⁻¹ * (k.totient : ℝ)⁻¹ := by
          rw [← mul_inv]
          refine inv_anti₀ (by exact_mod_cast Nat.mul_pos hphi_d hphi_k) (by exact_mod_cast hmult)
        calc
          ((d * k).totient : ℝ)⁻¹ * F d ≤ ((d.totient : ℝ)⁻¹ * (k.totient : ℝ)⁻¹) * F d :=
            mul_le_mul_of_nonneg_right hinv (hF_nn d)
          _ = (k.totient : ℝ)⁻¹ * ((d.totient : ℝ)⁻¹ * F d) := by ring
      have hlog_mono : Real.log (((⌊Q⌋₊ / d : ℕ) : ℝ) + 2) ≤ Real.log (Q + 2) := by
        refine Real.log_le_log (by positivity) ?_
        have h1 : (⌊Q⌋₊ / d : ℕ) ≤ ⌊Q⌋₊ := Nat.div_le_self _ _
        have h2 : ((⌊Q⌋₊ / d : ℕ) : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast h1
        linarith [Nat.floor_le (by linarith : 0 ≤ Q)]
      have hphi_d_bd := (hphi_sum (⌊Q⌋₊ / d)).trans
        (mul_le_mul_of_nonneg_left hlog_mono hCφ_pos.le)
      calc
        ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), ((d * k).totient : ℝ)⁻¹ * F d
            ≤ ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (k.totient : ℝ)⁻¹ * ((d.totient : ℝ)⁻¹ * F d) :=
              Finset.sum_le_sum hterm_k
        _ = (∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (k.totient : ℝ)⁻¹) * ((d.totient : ℝ)⁻¹ * F d) := by
              rw [← Finset.sum_mul]
        _ ≤ (C_φ * Real.log (Q + 2)) * ((d.totient : ℝ)⁻¹ * F d) := by
              have hnn : 0 ≤ (d.totient : ℝ)⁻¹ * F d := mul_nonneg (by positivity) (hF_nn d)
              exact mul_le_mul_of_nonneg_right hphi_d_bd hnn
    rw [← Finset.mul_sum] at hrw2
    exact hrw2
  linarith

/-- **Bombieri–Vinogradov from primitive character bounds and PNT**:
combines `bombieriVinogradov_primitive_char_reduction` with a polylogarithmic PNT error bound for
`|ψ(x) - x|` and a mean-value bound for primitive character sums `‖psiChar x ψ‖` over `2 ≤ d ≤ Q`
to conclude `BombieriVinogradovStatement`. -/
theorem bombieriVinogradov_of_primitive_char_bound
    (hpnt : ∀ A : ℝ, ∃ C > 0, ∀ {x : ℝ}, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x / Real.log x ^ A)
    (hprim : ∀ A : ℝ, ∃ B C : ℝ, 0 < C ∧ ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B →
      ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
          (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ ≤ C * x / Real.log x ^ A) :
    BombieriVinogradovStatement := by
  intro A
  obtain ⟨Cred, hCred_pos, hred⟩ := bombieriVinogradov_primitive_char_reduction
  obtain ⟨Cpnt, hCpnt_pos, hpntA⟩ := hpnt (A + 1)
  obtain ⟨B₁, C₁, hC₁_pos, hprimA⟩ := hprim (A + 1)
  let B : ℝ := max (max B₁ (A + 2)) 0
  let Q₀ : ℝ := Real.exp (1 / 2 : ℝ) / Real.log 2 ^ B
  have hQ₀_pos : 0 < Q₀ := by
    have := Real.log_pos one_lt_two
    dsimp [Q₀]
    positivity
  let K_small : ℝ := Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) * max 1 (Real.log 2 ^ A)
  have hpsi_e_nn : 0 ≤ Chebyshev.psi (Real.exp 1) := by
    unfold Chebyshev.psi
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  let C : ℝ := max (2 * Cred * Cpnt + 1 / Real.log 2 + 2 * Cred * C₁) (K_small + 1)
  have hC_pos : 0 < C := by
    have := Real.log_pos one_lt_two
    dsimp [C]
    positivity
  refine ⟨B, C, hC_pos, ?_⟩
  intro x Q hx2 hQ1 hQ_bd
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  by_cases hxe : Real.exp 1 ≤ x
  · have hlogx_ge1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx_pos).mpr hxe
    have hlogB1 : Real.log x ^ B₁ ≤ Real.log x ^ B :=
      Real.rpow_le_rpow_of_exponent_le hlogx_ge1 ((le_max_left B₁ _).trans (le_max_left _ 0))
    have hQ_B1 : Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B₁ :=
      hQ_bd.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hx_pos.le _)
        (Real.rpow_pos_of_pos hlogx_pos B₁) hlogB1)
    have hQ_le_x : Q ≤ x := by
      have hlogB_ge1 : 1 ≤ Real.log x ^ B :=
        Real.one_le_rpow hlogx_ge1 (le_max_right _ 0)
      calc
        Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B := hQ_bd
        _ ≤ x ^ (1 / 2 : ℝ) / 1 := div_le_div_of_nonneg_left (Real.rpow_nonneg hx_pos.le _)
              zero_lt_one hlogB_ge1
        _ = x ^ (1 / 2 : ℝ) := div_one _
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = x := Real.rpow_one x
    have hlogQ_le : Real.log Q ≤ Real.log x := Real.log_le_log (by linarith) hQ_le_x
    have hlogQ2_le : Real.log (Q + 2) ≤ 2 * Real.log x := by
      have h1 : Q + 2 ≤ x ^ 2 := by nlinarith [Real.exp_one_gt_d9]
      calc
        Real.log (Q + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) h1
        _ = 2 * Real.log x := by rw [Real.log_pow]; norm_cast
    have hlogA1_eq : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
      rw [Real.rpow_add hlogx_pos, Real.rpow_one]
    have hpnt_term :
        |Chebyshev.psi x - x| * (Cred * Real.log (Q + 2)) ≤
          2 * Cred * Cpnt * x / Real.log x ^ A := by
      have hp := hpntA hx2
      have h1 : |Chebyshev.psi x - x| * (Cred * Real.log (Q + 2)) ≤
          (Cpnt * x / Real.log x ^ (A + 1)) * (Cred * (2 * Real.log x)) := by
        have hlogQ2_nn : 0 ≤ Real.log (Q + 2) := Real.log_nonneg (by linarith)
        gcongr
      calc
        |Chebyshev.psi x - x| * (Cred * Real.log (Q + 2))
            ≤ (Cpnt * x / (Real.log x ^ A * Real.log x)) * (Cred * (2 * Real.log x)) := by
              simpa [hlogA1_eq] using h1
        _ = 2 * Cred * Cpnt * x / Real.log x ^ A := by
              field_simp [hlogx_pos.ne']
    have hmod_term :
        Q * (Real.log Q / Real.log 2) * Real.log x ≤ (1 / Real.log 2) * x / Real.log x ^ A := by
      have hB_ge : A + 2 ≤ B := (le_max_right B₁ (A + 2)).trans (le_max_left _ 0)
      have hlogA2_le : Real.log x ^ (A + 2) ≤ Real.log x ^ B :=
        Real.rpow_le_rpow_of_exponent_le hlogx_ge1 hB_ge
      have hQ_A2 : Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ (A + 2) :=
        hQ_bd.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hx_pos.le _)
          (Real.rpow_pos_of_pos hlogx_pos (A + 2)) hlogA2_le)
      have hx_half_le : x ^ (1 / 2 : ℝ) ≤ x := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
          (by norm_num : (1 / 2 : ℝ) ≤ 1)
      have hlogA2_eq : Real.log x ^ (A + 2) = Real.log x ^ A * Real.log x ^ 2 := by
        rw [Real.rpow_add hlogx_pos, Real.rpow_two]
      have hlogQ_nn : 0 ≤ Real.log Q := Real.log_nonneg hQ1
      calc
        Q * (Real.log Q / Real.log 2) * Real.log x
            ≤ (x ^ (1 / 2 : ℝ) / Real.log x ^ (A + 2)) * (Real.log x / Real.log 2) * Real.log x := by
              gcongr
        _ ≤ (x / (Real.log x ^ A * Real.log x ^ 2)) * (Real.log x / Real.log 2) * Real.log x := by
              rw [hlogA2_eq]
              gcongr
        _ = (1 / Real.log 2) * x / Real.log x ^ A := by
              field_simp [hlogx_pos.ne', hlog2_pos.ne']
    have hprim_term :
        Cred * Real.log (Q + 2) * ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
            ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
              (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ ≤
          2 * Cred * C₁ * x / Real.log x ^ A := by
      have hp := hprimA hx2 hQ1 hQ_B1
      have hsum_nn : 0 ≤ ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
            (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖ :=
        Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      calc
        Cred * Real.log (Q + 2) * ∑ d ∈ Finset.Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
              ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
                (fun ψ => ψ.IsPrimitive), ‖psiChar x ψ‖
            ≤ (Cred * (2 * Real.log x)) * (C₁ * x / (Real.log x ^ A * Real.log x)) := by
              rw [← hlogA1_eq]
              gcongr
        _ = 2 * Cred * C₁ * x / Real.log x ^ A := by
              field_simp [hlogx_pos.ne']
    have hcomb := (hred hx2 hQ1).trans (add_le_add (add_le_add hpnt_term hmod_term) hprim_term)
    calc
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q
          ≤ 2 * Cred * Cpnt * x / Real.log x ^ A + (1 / Real.log 2) * x / Real.log x ^ A +
              2 * Cred * C₁ * x / Real.log x ^ A := hcomb
      _ = (2 * Cred * Cpnt + 1 / Real.log 2 + 2 * Cred * C₁) * x / Real.log x ^ A := by ring
      _ ≤ C * x / Real.log x ^ A := by
            have hlogA_pos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogx_pos A
            gcongr
            exact le_max_left _ _
  · push Not at hxe
    have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx2
    have hlogx_le1 : Real.log x ≤ 1 := by
      have := Real.log_le_log hx_pos hxe.le
      rwa [Real.log_exp] at this
    have hB_nn : 0 ≤ B := le_max_right _ 0
    have hlog2B : Real.log 2 ^ B ≤ Real.log x ^ B := Real.rpow_le_rpow hlog2_pos.le hlog2_le hB_nn
    have hsqrt_le : x ^ (1 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
      calc
        x ^ (1 / 2 : ℝ) ≤ (Real.exp 1) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hx_pos.le hxe.le (by norm_num)
        _ = Real.exp (1 / 2 : ℝ) := by
              rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul]
    have hQ_le_Q₀ : Q ≤ Q₀ := by
      have hlog2B_pos : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hlog2_pos B
      calc
        Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B := hQ_bd
        _ ≤ Real.exp (1 / 2 : ℝ) / Real.log 2 ^ B :=
              div_le_div₀ (Real.exp_pos _).le hsqrt_le hlog2B_pos hlog2B
        _ = Q₀ := rfl
    have heach_q : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊,
        maxPsiAPError x q ≤ Chebyshev.psi (Real.exp 1) + Real.exp 1 := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      dsimp only [maxPsiAPError]
      split_ifs
      rw [Finset.sup'_le_iff]
      intro a _
      have hpsi_le : psiAP x q a ≤ Chebyshev.psi (Real.exp 1) := by
        calc
          psiAP x q a ≤ Chebyshev.psi x := psiAP_le_psi x q a
          _ ≤ Chebyshev.psi (Real.exp 1) := by
                unfold Chebyshev.psi
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                  (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
                exact Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxe.le)
      have hpsi_nn : 0 ≤ psiAP x q a := psiAP_nonneg x q a
      have hphi1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hdiv_le : x / (q.totient : ℝ) ≤ Real.exp 1 := by
        calc
          x / (q.totient : ℝ) ≤ x / 1 := by gcongr
          _ = x := div_one x
          _ ≤ Real.exp 1 := hxe.le
      have hdiv_nn : 0 ≤ x / (q.totient : ℝ) := by positivity
      rw [abs_le]
      constructor <;> linarith
    have hsum_le : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q ≤
        Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
      calc
        ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q
            ≤ ∑ _q ∈ Finset.Icc 1 ⌊Q⌋₊, (Chebyshev.psi (Real.exp 1) + Real.exp 1) :=
              Finset.sum_le_sum heach_q
        _ = (⌊Q⌋₊ : ℝ) * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ Q * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
              gcongr
        _ ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              gcongr
    have hlogA_le : Real.log x ^ A ≤ max 1 (Real.log 2 ^ A) := by
      by_cases hA0 : 0 ≤ A
      · calc
          Real.log x ^ A ≤ (1 : ℝ) ^ A := Real.rpow_le_rpow hlogx_pos.le hlogx_le1 hA0
          _ = 1 := Real.one_rpow A
          _ ≤ max 1 (Real.log 2 ^ A) := le_max_left _ _
      · push Not at hA0
        have h1 : Real.log x ^ A ≤ Real.log 2 ^ A :=
          Real.rpow_le_rpow_of_nonpos hlog2_pos hlog2_le hA0.le
        exact h1.trans (le_max_right _ _)
    have hlogA_pos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogx_pos A
    have hx1' : (1 : ℝ) ≤ x := by linarith
    calc
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, maxPsiAPError x q
          ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := hsum_le
      _ ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) * (max 1 (Real.log 2 ^ A) / Real.log x ^ A) := by
            have hge1 : 1 ≤ max 1 (Real.log 2 ^ A) / Real.log x ^ A :=
              (one_le_div hlogA_pos).mpr hlogA_le
            have hnn : 0 ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) := by
              have := Real.exp_pos (1 : ℝ); positivity
            calc
              Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1)
                  = Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) * 1 := (mul_one _).symm
              _ ≤ Q₀ * (Chebyshev.psi (Real.exp 1) + Real.exp 1) *
                    (max 1 (Real.log 2 ^ A) / Real.log x ^ A) := by gcongr
      _ = K_small * 1 / Real.log x ^ A := by dsimp [K_small]; ring
      _ ≤ C * x / Real.log x ^ A := by
            have hKC : K_small ≤ C := by dsimp [C]; linarith [le_max_right (2 * Cred * Cpnt + 1 / Real.log 2 + 2 * Cred * C₁) (K_small + 1)]
            have hKnn : 0 ≤ K_small := by have := Real.exp_pos (1 : ℝ); positivity
            gcongr

end BombieriVinogradov

end AnalyticNumberTheory.PrimeDistribution

