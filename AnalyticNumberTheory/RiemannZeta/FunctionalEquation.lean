import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import AnalyticNumberTheory.AnalyticTools.Transforms
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.Order

/-!
# Functional Equation and Analytic Continuation of the Riemann Zeta Function

This file develops the Euler–Maclaurin analytic continuation of `riemannZeta` to the half-planes
`0 < Re s` and `-1 < Re s` (away from `s = 1`), defines the completed Riemann zeta function `xi`,
proves its symmetric functional equation `xi (1 - s) = xi s` and asymmetric functional equation
bridges, proves entireness of `xi`, and determines its exact entire order `exactOrder xi = 1`.
-/

open Complex Real Filter MeasureTheory Set Asymptotics
open scoped Topology Nat ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.RiemannZeta

section Helpers

private lemma isPathConnected_re_gt_sdiff_one {σ₀ : ℝ} (hσ₀ : σ₀ < 1) :
    IsPathConnected {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | σ₀ < s.re ∧ s ≠ 1}
  have h2 : (2 : ℂ) ∈ U := ⟨by norm_num; linarith, by norm_num⟩
  refine ⟨(2 : ℂ), h2, fun {z} hz ↦ ?_⟩
  have hz_re : σ₀ < z.re := hz.1
  have hz_ne : z ≠ 1 := hz.2
  by_cases him : z.im ≠ 0
  · let γ : unitInterval → ℂ := fun t ↦ ((1 - (t : ℝ) : ℝ) : ℂ) * 2 + ((t : ℝ) : ℂ) * z
    refine ⟨⟨⟨γ, by fun_prop⟩, by simp [γ], by simp [γ]⟩, fun t ↦ ?_⟩
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    refine ⟨?_, ?_⟩
    · change σ₀ < (γ t).re
      simp only [γ, add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, mul_zero, sub_zero,
        zero_mul]
      rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
      · rw [← ht_zero]
        linarith
      · have hmul1 : (1 - (t : ℝ)) * σ₀ ≤ (1 - (t : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have hmul2 : (t : ℝ) * σ₀ < (t : ℝ) * z.re :=
          mul_lt_mul_of_pos_left hz_re ht_pos
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
    have hmid : mid ∈ U := ⟨by simp [mid]; linarith, by simp [mid, Complex.ext_iff]⟩
    have hpath1 : JoinedIn U (2 : ℂ) mid := by
      refine ⟨⟨⟨fun t : unitInterval ↦ (2 : ℂ) + ((t : ℝ) : ℂ) * I, by fun_prop⟩,
        by simp, by simp [mid]⟩, fun t ↦ ?_⟩
      refine ⟨by simp; linarith, ?_⟩
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp at hRe
    have hpath2 : JoinedIn U mid z := by
      let γ : unitInterval → ℂ := fun t ↦ ((1 - (t : ℝ) : ℝ) : ℂ) * mid + ((t : ℝ) : ℂ) * z
      refine ⟨⟨⟨γ, by fun_prop⟩, by simp [γ], by simp [γ]⟩, fun t ↦ ?_⟩
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      refine ⟨?_, ?_⟩
      · change σ₀ < (γ t).re
        simp only [γ, mid, add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, I_re, add_zero,
          zero_mul, sub_zero]
        rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
        · rw [← ht_zero]
          linarith
        · have hmul1 : (1 - (t : ℝ)) * σ₀ ≤ (1 - (t : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          have hmul2 : (t : ℝ) * σ₀ < (t : ℝ) * z.re :=
            mul_lt_mul_of_pos_left hz_re ht_pos
          linarith
      · intro hEq
        have hEq' : γ t = 1 := hEq
        rcases eq_or_lt_of_le ht1 with ht_one | ht_lt
        · have hEnd : γ t = z := by simp [γ, ht_one]
          exact hz_ne (hEnd ▸ hEq')
        · have hIm : (γ t).im = (1 : ℂ).im := congrArg Complex.im hEq'
          simp [γ, mid, him] at hIm
          linarith
    exact hpath1.trans hpath2

private lemma isOpen_re_gt_sdiff_one (σ₀ : ℝ) :
    IsOpen {s : ℂ | σ₀ < s.re ∧ s ≠ 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

private lemma cpow_ofReal_hasDerivAt {t : ℝ} (ht : 0 < t) (c : ℂ) :
    HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hmem : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
  simpa using ((hasDerivAt_id (t : ℂ)).cpow_const hmem).comp_ofReal

private lemma cpow_ofReal_continuousOn (a : ℝ) (ha : 0 < a) (b : ℝ) (c : ℂ) :
    ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ c) (Set.Icc a b) := by
  refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
  have hu_pos : 0 < u := lt_of_lt_of_le ha hu.1
  exact (cpow_ofReal_hasDerivAt hu_pos c).continuousAt

private lemma integral_cpow_ofReal_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : s ≠ 1) :
    ∫ u in a..b, (u : ℂ) ^ (-s) = ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  have hderiv : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ (x : ℂ) ^ (1 - s) / (1 - s)) ((u : ℂ) ^ (-s)) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu_pos : 0 < u := lt_of_lt_of_le ha hu.1
    have hd := (cpow_ofReal_hasDerivAt hu_pos (1 - s)).div_const (1 - s)
    convert hd using 1
    have hexp : (1 - s) - 1 = -s := by ring
    rw [hexp, mul_div_cancel_left₀ _ hne]
  have hint : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ) ^ (-s)) volume a b :=
    (cpow_ofReal_continuousOn a ha b (-s)).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

private lemma euler_maclaurin_first_order_Icc_complex {M N : ℕ} (hMN : M ≤ N)
    {f f' : ℝ → ℂ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Icc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f M + f N) / 2 +
        ∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t := by
  have hle : (M : ℝ) ≤ N := Nat.cast_le.mpr hMN
  have hre_deriv : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt (fun x ↦ (f x).re) (f' t).re t :=
    fun t ht ↦ Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht)
  have him_deriv : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt (fun x ↦ (f x).im) (f' t).im t :=
    fun t ht ↦ Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht)
  have hre_cont : ContinuousOn (fun x ↦ (f' x).re) (Set.Icc (M : ℝ) N) :=
    Complex.continuous_re.comp_continuousOn hf'
  have him_cont : ContinuousOn (fun x ↦ (f' x).im) (Set.Icc (M : ℝ) N) :=
    Complex.continuous_im.comp_continuousOn hf'
  have hre_em := euler_maclaurin_first_order_Icc hMN hre_deriv hre_cont
  have him_em := euler_maclaurin_first_order_Icc hMN him_deriv him_cont
  have hf_cont : ContinuousOn f (Set.Icc (M : ℝ) N) :=
    fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hf_int : IntervalIntegrable f volume (M : ℝ) N :=
    hf_cont.intervalIntegrable_of_Icc hle
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
  · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.re_sum]
    have h1 : (∫ t in (M : ℝ)..N, f t).re = Complex.reCLM (∫ t in (M : ℝ)..N, f t) := rfl
    have h2 : (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t).re =
        Complex.reCLM (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t) := rfl
    rw [h1, h2, ← hint_re1, ← hint_re2]
    simpa [Complex.reCLM_apply] using hre_em
  · simp only [Complex.add_im, Complex.div_ofNat_im, Complex.im_sum]
    have h1 : (∫ t in (M : ℝ)..N, f t).im = Complex.imCLM (∫ t in (M : ℝ)..N, f t) := rfl
    have h2 : (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t).im =
        Complex.imCLM (∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t) := rfl
    rw [h1, h2, ← hint_im1, ← hint_im2]
    simpa [Complex.imCLM_apply] using him_em

private lemma euler_maclaurin_first_order_Ioc_complex {M N : ℕ} (hMN : M ≤ N)
    {f f' : ℝ → ℂ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Ioc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f N - f M) / 2 +
        ∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t := by
  have h := euler_maclaurin_first_order_Icc_complex hMN hf hf'
  rw [Finset.Icc_eq_cons_Ioc hMN, Finset.sum_cons] at h
  linear_combination h

private lemma integral_bernoulliKernel_one_mul_eq_sub_complex {M N : ℕ} (hMN : M ≤ N)
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

private lemma integrableOn_sawtooth_cpow_Ioi {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi a) := by
  have hpow_int : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-s.re - 1)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul (1 / 2)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hmeas_saw : Measurable fun u : ℝ ↦ (sawtooth u : ℂ) :=
      Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const _)
    have hcont_pow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (-s - 1)) (Set.Ioi a) := by
      refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
      exact (cpow_ofReal_hasDerivAt (lt_trans ha hu) (-s - 1)).continuousAt
    exact (hmeas_saw.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
      (hcont_pow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := lt_trans ha hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)

private lemma integrableOn_bernoulliKernel_two_cpow_Ioi {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : -1 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-s - 2)) (Set.Ioi a) := by
  have hpow_int : IntegrableOn (fun u : ℝ ↦ (1 / 12 : ℝ) * u ^ (-s.re - 2)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul (1 / 12)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hcont_b2 : Continuous fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))
    have hcont_pow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (-s - 2)) (Set.Ioi a) := by
      refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
      exact (cpow_ofReal_hasDerivAt (lt_trans ha hu) (-s - 2)).continuousAt
    exact (hcont_b2.continuousOn.mul hcont_pow).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := lt_trans ha hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re, re_ofNat]
    exact mul_le_mul (bernoulliKernel_two_abs_le u) le_rfl (by positivity) (by positivity)

private lemma mellin_sawtooth_eq_integral (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    mellin (Set.indicator (Set.Ioi (N : ℝ)) (fun u : ℝ ↦ (sawtooth u : ℂ))) (-s) =
      ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [mellin]
  have hcongr : Set.EqOn
      (fun u : ℝ ↦ (u : ℂ) ^ (-s - 1) •
        Set.indicator (Set.Ioi (N : ℝ)) (fun v : ℝ ↦ (sawtooth v : ℂ)) u)
      (Set.indicator (Set.Ioi (N : ℝ)) (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)))
      (Set.Ioi (0 : ℝ)) := by
    intro u _
    by_cases huN : (N : ℝ) < u
    · simp [Set.mem_Ioi, huN, smul_eq_mul, mul_comm]
    · simp [Set.mem_Ioi, huN]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (fun _ hu ↦ lt_trans hN_pos hu)]

private lemma differentiableOn_integral_sawtooth (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1))
      {s : ℂ | 0 < s.re} := by
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
  intro s hs
  have hs_pos : 0 < s.re := hs
  let b : ℝ := -(s.re + 1)
  have hf_bot : f =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-b)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT hN_pos] with u hu
    have huN : ¬ (N : ℝ) < u := not_lt.mpr hu.2.le
    simp [f, huN]
  have hmel := mellin_differentiableOn_strip (a := 0) (b := b) hf_loc hf_top hf_bot
  have hstrip : -s ∈ {z : ℂ | b < z.re ∧ z.re < 0} := by
    simp only [Set.mem_ofPred_eq, neg_re, b]
    exact ⟨by linarith, by linarith⟩
  have hdiff := (hmel (-s) hstrip).differentiableAt (by
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hstrip)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ ↦ mellin f (-z)) s :=
    hdiff.comp s (hasDerivAt_neg s).differentiableAt
  have heq : (fun z : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1)) =
      fun z : ℂ ↦ mellin f (-z) := by
    ext z
    exact (mellin_sawtooth_eq_integral N hN z).symm
  rw [heq]
  exact hcomp.differentiableWithinAt

private lemma differentiableOn_integral_bernoulliKernel_two (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-s - 2))
      {s : ℂ | -1 < s.re} := by
  let f : ℝ → ℂ := Set.indicator (Set.Ioi (N : ℝ)) (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ))
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf_loc : LocallyIntegrableOn f (Set.Ioi 0) := by
    have hcont : Continuous (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))
    have hloc : LocallyIntegrable f volume := by
      refine (locallyIntegrable_const (1 / 12 : ℝ)).mono
        (hcont.measurable.indicator measurableSet_Ioi).aestronglyMeasurable
        (Eventually.of_forall fun u ↦ ?_)
      rw [Real.norm_of_nonneg (by norm_num)]
      by_cases hu : (N : ℝ) < u
      · simpa [f, hu, Complex.norm_real, Real.norm_eq_abs] using bernoulliKernel_two_abs_le u
      · simp [f, hu]
    exact hloc.locallyIntegrableOn _
  have hf_top : f =O[atTop] (fun u : ℝ ↦ u ^ (0 : ℝ)) := by
    refine IsBigO.of_bound (1 / 12) ?_
    filter_upwards [eventually_gt_atTop (N : ℝ)] with u hu
    simpa [f, hu, Complex.norm_real, Real.norm_eq_abs] using bernoulliKernel_two_abs_le u
  intro s hs
  have hs_gt : -1 < s.re := hs
  let b : ℝ := -(s.re + 2)
  have hf_bot : f =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-b)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT hN_pos] with u hu
    have huN : ¬ (N : ℝ) < u := not_lt.mpr hu.2.le
    simp [f, huN]
  have hmel := mellin_differentiableOn_strip (a := 0) (b := b) hf_loc hf_top hf_bot
  have hstrip : -s - 1 ∈ {z : ℂ | b < z.re ∧ z.re < 0} := by
    simp only [Set.mem_ofPred_eq, sub_re, neg_re, one_re, b]
    exact ⟨by linarith, by linarith⟩
  have hdiff := (hmel (-s - 1) hstrip).differentiableAt (by
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hstrip)
  have hsub1 : DifferentiableAt ℂ (fun z : ℂ ↦ -z - 1) s :=
    (hasDerivAt_neg s).differentiableAt.sub_const 1
  have hcomp : DifferentiableAt ℂ (fun z : ℂ ↦ mellin f (-z - 1)) s :=
    DifferentiableAt.comp (g := mellin f) (f := fun z : ℂ ↦ -z - 1) s hdiff hsub1
  have heq : (fun z : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)) =
      fun z : ℂ ↦ mellin f (-z - 1) := by
    ext z
    rw [mellin]
    have hcongr : Set.EqOn
        (fun u : ℝ ↦ (u : ℂ) ^ ((-z - 1) - 1) • f u)
        (Set.indicator (Set.Ioi (N : ℝ))
          (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)))
        (Set.Ioi (0 : ℝ)) := by
      intro u _
      have hexp : (-z - 1) - 1 = -z - 2 := by ring
      by_cases huN : (N : ℝ) < u
      · simp [f, Set.mem_Ioi, huN, smul_eq_mul, mul_comm, hexp]
      · simp [f, Set.mem_Ioi, huN]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (fun _ hu ↦ lt_trans hN_pos hu)]
  rw [heq]
  exact hcomp.differentiableWithinAt

end Helpers

section EulerMaclaurinContinuation

/-- **Euler–Maclaurin analytic continuation** of `riemannZeta` to the right half-plane
`0 < s.re` (`s ≠ 1`) at basepoint `N = 1`:
`ζ(s) = 1 / (s - 1) + 1 / 2 - s * ∫ u in Ioi 1, ({u} - 1/2) * u^(-s-1) du`. -/
theorem riemannZeta_eq_eulerMaclaurin_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 -
      s * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  let L : ℂ → ℂ := riemannZeta
  let R : ℂ → ℂ := fun z ↦ 1 / (z - 1) + 1 / 2 -
    z * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1)
  have hL_an : AnalyticOnNhd ℂ L U :=
    analyticOn_riemannZeta.mono (fun _ hz ↦ hz.2)
  have hR_diff : DifferentiableOn ℂ R U := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / (w - 1) + 1 / 2) z := by
      have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz.2
      fun_prop (disch := exact hne)
    have h2 : DifferentiableAt ℂ
        (fun w : ℂ ↦ ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-w - 1)) z :=
      ((differentiableOn_integral_sawtooth 1 le_rfl) z hz.1).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1)
    exact (h1.sub (differentiableAt_id.mul h2)).differentiableWithinAt
  have hR_an : AnalyticOnNhd ℂ R U :=
    hR_diff.analyticOnNhd (isOpen_re_gt_sdiff_one 0)
  have h_gt_one : ∀ {z : ℂ}, 1 < z.re → L z = R z := by
    intro z hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hz0 : 0 < z.re := lt_trans zero_lt_one hz
    have hem (N : ℕ) (hN : 1 ≤ N) :
        ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z) =
          ((N : ℂ) ^ (1 - z) - 1) / (1 - z) + (1 + (N : ℂ) ^ (-z)) / 2 -
            z * ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) := by
      have hf : ∀ t ∈ Set.Icc (1 : ℝ) N,
          HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-z)) (-z * (t : ℂ) ^ (-z - 1)) t :=
        fun t ht ↦ cpow_ofReal_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (-z)
      have hf' : ContinuousOn (fun u : ℝ ↦ -z * (u : ℂ) ^ (-z - 1)) (Set.Icc (1 : ℝ) N) :=
        continuousOn_const.mul (cpow_ofReal_continuousOn 1 zero_lt_one N (-z - 1))
      have h_em := euler_maclaurin_first_order_Icc_complex hN hf hf'
      simp only [Nat.cast_one] at h_em
      rw [integral_cpow_ofReal_eq zero_lt_one (Nat.one_le_cast.mpr hN) hz1] at h_em
      simp only [Complex.ofReal_one, one_cpow] at h_em
      have hpull : ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (-z * (t : ℂ) ^ (-z - 1)) =
          -z * ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) := by
        have hcongr : (fun t : ℝ ↦ (sawtooth t : ℂ) * (-z * (t : ℂ) ^ (-z - 1))) =
            fun t : ℝ ↦ (-z) * ((sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
          ext t; ring
        rw [hcongr, intervalIntegral.integral_const_mul]
      rw [hpull] at h_em
      linear_combination h_em
    have hsum_lim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
        atTop (𝓝 (riemannZeta z)) := by
      have hsumm : Summable fun n : ℕ ↦ 1 / (n + 1 : ℂ) ^ z := by
        have h := Complex.summable_one_div_nat_cpow.mpr hz
        simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
      refine hsumm.hasSum.tendsto_sum_nat.congr fun N ↦ ?_
      refine Finset.sum_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
      · intro a _ b _ h; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb; exact ⟨b - 1, by simp; omega, by omega⟩
      · intro n _
        rw [Nat.cast_add, Nat.cast_one, one_div, cpow_neg]
    have hpow1 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (1 - z)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hreal : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 - z.re)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < z.re - 1)).comp tendsto_natCast_atTop_atTop
          |>.congr fun N ↦ by rw [Function.comp_apply, show -(z.re - 1) = 1 - z.re by ring]
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Complex.norm_natCast_cpow_of_pos hN, sub_re, one_re]
    have hpow2 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-z)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hreal : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hz0).comp tendsto_natCast_atTop_atTop
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Complex.norm_natCast_cpow_of_pos hN, neg_re]
    have hint_lim : Tendsto
        (fun N : ℕ ↦ ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))) :=
      (intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_sawtooth_cpow_Ioi zero_lt_one hz0)
        tendsto_id).comp tendsto_natCast_atTop_atTop
    have hrhs_lim : Tendsto (fun N : ℕ ↦
        ((N : ℂ) ^ (1 - z) - 1) / (1 - z) + (1 + (N : ℂ) ^ (-z)) / 2 -
          z * ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (R z)) := by
      have hlim1 : Tendsto
          (fun N : ℕ ↦ ((N : ℂ) ^ (1 - z) - 1) / (1 - z) + (1 + (N : ℂ) ^ (-z)) / 2)
          atTop (𝓝 ((0 - 1) / (1 - z) + (1 + 0) / 2)) :=
        ((hpow1.sub_const 1).div_const (1 - z)).add ((tendsto_const_nhds.add hpow2).div_const 2)
      have hlim2 := hlim1.sub (hint_lim.const_mul z)
      refine hlim2.trans_eq (congrArg 𝓝 ?_)
      dsimp only [R]
      have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
      have hne' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      field_simp [hne, hne']
      ring
    have hrhs_lim' : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
        atTop (𝓝 (R z)) :=
      hrhs_lim.congr' (by filter_upwards [eventually_ge_atTop 1] with N hN; exact (hem N hN).symm)
    exact tendsto_nhds_unique hsum_lim hrhs_lim'
  have h2mem : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : L =ᶠ[𝓝 (2 : ℂ)] R := by
    have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with z hz
    exact h_gt_one hz
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an
    (isPathConnected_re_gt_sdiff_one (by norm_num : (0 : ℝ) < 1)).isConnected.isPreconnected
    h2mem hev ⟨hs, hs1⟩

/-- **Truncated Euler–Maclaurin continuation** of `riemannZeta` to `0 < s.re` (`s ≠ 1`) at any
integer cutoff `N ≥ 1`:
`ζ(s) = ∑ n ∈ Icc 1 N, n^(-s) - N^(1-s)/(1-s) - (1/2) * N^(-s) - s ∫_N^∞ ({u} - 1/2) u^(-s-1) du`. -/
theorem riemannZeta_eq_eulerMaclaurin_Icc_of_re_pos {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) -
      (N : ℂ) ^ (1 - s) / (1 - s) - (1 / 2 : ℂ) * (N : ℂ) ^ (-s) -
      s * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have h1 := riemannZeta_eq_eulerMaclaurin_of_re_pos hs hs1
  have hint_full : IntegrableOn (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi 1) :=
    integrableOn_sawtooth_cpow_Ioi zero_lt_one hs
  have hIoi_split : ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1) =
      (∫ u in (1 : ℝ)..N, (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)) +
        ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    have hle : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
    have hint_tail : IntegrableOn (fun u : ℝ ↦ (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1))
        (Set.Ioi (N : ℝ)) :=
      hint_full.mono_set (Set.Ioi_subset_Ioi hle)
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Set.Ioc_disjoint_Ioi_same
        measurableSet_Ioi (hint_full.mono_set Set.Ioc_subset_Ioi_self) hint_tail,
      intervalIntegral.integral_of_le hle]
  have hf : ∀ t ∈ Set.Icc (1 : ℝ) N,
      HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t :=
    fun t ht ↦ cpow_ofReal_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (-s)
  have hf' : ContinuousOn (fun u : ℝ ↦ -s * (u : ℂ) ^ (-s - 1)) (Set.Icc (1 : ℝ) N) :=
    continuousOn_const.mul (cpow_ofReal_continuousOn 1 zero_lt_one N (-s - 1))
  have h_em := euler_maclaurin_first_order_Ioc_complex hN hf hf'
  simp only [Nat.cast_one] at h_em
  rw [integral_cpow_ofReal_eq zero_lt_one (Nat.one_le_cast.mpr hN) hs1] at h_em
  simp only [Complex.ofReal_one, one_cpow] at h_em
  have hpull : ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (-s * (t : ℂ) ^ (-s - 1)) =
      -s * ∫ t in (1 : ℝ)..N, (sawtooth t : ℂ) * (t : ℂ) ^ (-s - 1) := by
    have hcongr : (fun t : ℝ ↦ (sawtooth t : ℂ) * (-s * (t : ℂ) ^ (-s - 1))) =
        fun t : ℝ ↦ (-s) * ((sawtooth t : ℂ) * (t : ℂ) ^ (-s - 1)) := by
      ext t; ring
    rw [hcongr, intervalIntegral.integral_const_mul]
  rw [hpull] at h_em
  have hIcc : ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      1 + ∑ n ∈ Finset.Ioc 1 N, (n : ℂ) ^ (-s) := by
    rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons]
    simp
  rw [h1, hIoi_split, hIcc]
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hne' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hrecip : 1 / (s - 1) = -1 / (1 - s) := by
    field_simp [hne, hne']
    ring
  rw [hrecip]
  linear_combination -h_em

/-- **Second-order Euler–Maclaurin analytic continuation** of `riemannZeta` to `-1 < s.re` (`s ≠ 1`)
at any integer cutoff `N ≥ 1`. -/
theorem riemannZeta_eq_eulerMaclaurin_second_order_of_re_gt_neg_one {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) -
      (N : ℂ) ^ (1 - s) / (1 - s) - (1 / 2 : ℂ) * (N : ℂ) ^ (-s) +
      (1 / 12 : ℂ) * s * (N : ℂ) ^ (-s - 1) -
      s * (s + 1) * ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-s - 2) := by
  let U : Set ℂ := {z : ℂ | -1 < z.re ∧ z ≠ 1}
  let L : ℂ → ℂ := riemannZeta
  let R : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z) -
    (N : ℂ) ^ (1 - z) / (1 - z) - (1 / 2 : ℂ) * (N : ℂ) ^ (-z) +
    (1 / 12 : ℂ) * z * (N : ℂ) ^ (-z - 1) -
    z * (z + 1) * ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2)
  have hN_pos : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hL_an : AnalyticOnNhd ℂ L U :=
    analyticOn_riemannZeta.mono (fun _ hz ↦ hz.2)
  have hR_diff : DifferentiableOn ℂ R U := by
    intro z hz
    have hsum : DifferentiableAt ℂ (fun w : ℂ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-w)) z := by
      refine DifferentiableAt.fun_sum fun n hn ↦ ?_
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp only [Finset.mem_Icc] at hn; omega)
      exact (differentiableAt_id.neg).const_cpow (Or.inl hn0)
    have hterm1 : DifferentiableAt ℂ (fun w : ℂ ↦ (N : ℂ) ^ (1 - w) / (1 - w)) z := by
      have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.2.symm
      fun_prop (disch := first | exact hne | exact Or.inl hN_pos)
    have hterm2 : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 2 : ℂ) * (N : ℂ) ^ (-w)) z :=
      (differentiableAt_id.neg.const_cpow (Or.inl hN_pos)).const_mul _
    have hterm3 : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 12 : ℂ) * w * (N : ℂ) ^ (-w - 1)) z :=
      (differentiableAt_id.const_mul _).mul
        ((differentiableAt_id.neg.sub_const 1).const_cpow (Or.inl hN_pos))
    have hint : DifferentiableAt ℂ
        (fun w : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-w - 2)) z :=
      ((differentiableOn_integral_bernoulliKernel_two N hN) z hz.1).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1)
    have hterm4 : DifferentiableAt ℂ (fun w : ℂ ↦
        w * (w + 1) * ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-w - 2)) z :=
      (differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul hint
    exact ((((hsum.sub hterm1).sub hterm2).add hterm3).sub hterm4).differentiableWithinAt
  have hR_an : AnalyticOnNhd ℂ R U :=
    hR_diff.analyticOnNhd (isOpen_re_gt_sdiff_one (-1))
  have h_pos : ∀ {z : ℂ}, 0 < z.re → z ≠ 1 → L z = R z := by
    intro z hz hz1
    have h1 := riemannZeta_eq_eulerMaclaurin_Icc_of_re_pos hN hz hz1
    have hN_real_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hibp (M : ℕ) (hNM : N ≤ M) :
        ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) =
          ((1 / 12 : ℂ) * (M : ℂ) ^ (-z - 1) - (1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1)) +
            (z + 1) * ∫ t in (N : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2) := by
      have hg : ∀ t ∈ Set.Icc (N : ℝ) M,
          HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-z - 1)) ((-z - 1) * (t : ℂ) ^ (-z - 2)) t := by
        intro t ht
        have hd := cpow_ofReal_hasDerivAt (lt_of_lt_of_le hN_real_pos ht.1) (-z - 1)
        convert hd using 1
        ring_nf
      have hg' : ContinuousOn (fun u : ℝ ↦ (-z - 1) * (u : ℂ) ^ (-z - 2)) (Set.Icc (N : ℝ) M) :=
        continuousOn_const.mul (cpow_ofReal_continuousOn N hN_real_pos M (-z - 2))
      have hres := integral_bernoulliKernel_one_mul_eq_sub_complex hNM hg hg'
      have hpull : ∫ t in (N : ℝ)..M, (bernoulliKernel 2 t : ℂ) * ((-z - 1) * (t : ℂ) ^ (-z - 2)) =
          (-z - 1) * ∫ t in (N : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2) := by
        have hcongr : (fun t : ℝ ↦ (bernoulliKernel 2 t : ℂ) * ((-z - 1) * (t : ℂ) ^ (-z - 2))) =
            fun t : ℝ ↦ (-z - 1) * ((bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2)) := by
          ext t; ring
        rw [hcongr, intervalIntegral.integral_const_mul]
      rw [hpull] at hres
      linear_combination hres
    have hint1 : Tendsto (fun M : ℕ ↦ ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1))) :=
      (intervalIntegral_tendsto_integral_Ioi N (integrableOn_sawtooth_cpow_Ioi hN_real_pos hz)
        tendsto_id).comp tendsto_natCast_atTop_atTop
    have hint2 : Tendsto
        (fun M : ℕ ↦ ∫ t in (N : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2))
        atTop (𝓝 (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))) :=
      (intervalIntegral_tendsto_integral_Ioi N
        (integrableOn_bernoulliKernel_two_cpow_Ioi hN_real_pos (by linarith))
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
        ((1 / 12 : ℂ) * (M : ℂ) ^ (-z - 1) - (1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1)) +
          (z + 1) * ∫ t in (N : ℝ)..M, (bernoulliKernel 2 t : ℂ) * (t : ℂ) ^ (-z - 2))
        atTop (𝓝 (-(1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1) +
          (z + 1) * ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2))) := by
      have hsub : Tendsto (fun M : ℕ ↦
          (1 / 12 : ℂ) * (M : ℂ) ^ (-z - 1) - (1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1))
          atTop (𝓝 (0 - (1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1))) := by
        simpa using (hpowM.const_mul (1 / 12 : ℂ)).sub_const ((1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1))
      have hres := hsub.add (hint2.const_mul (z + 1))
      refine hres.trans_eq (congrArg 𝓝 ?_)
      ring
    have heq_tail :
        ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-z - 1) =
          -(1 / 12 : ℂ) * (N : ℂ) ^ (-z - 1) +
            (z + 1) * ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-z - 2) :=
      tendsto_nhds_unique hint1 (hlim_rhs.congr' (by
        filter_upwards [eventually_ge_atTop N] with M hNM; exact (hibp M hNM).symm))
    dsimp only [L, R]
    rw [h1, heq_tail]
    ring
  have h2mem : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : L =ᶠ[𝓝 (2 : ℂ)] R := by
    have hopen : {z : ℂ | 0 < z.re ∧ z ≠ 1} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_re_gt_sdiff_one 0).mem_nhds ⟨by norm_num, by norm_num⟩
    filter_upwards [hopen] with z hz
    exact h_pos hz.1 hz.2
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an
    (isPathConnected_re_gt_sdiff_one (by norm_num : (-1 : ℝ) < 1)).isConnected.isPreconnected
    h2mem hev ⟨hs, hs1⟩

end EulerMaclaurinContinuation

section CompletedZetaAndFunctionalEquation

/-- The completed Riemann zeta function `ξ(s)`, defined as the entire extension of
`(1 / 2) * s * (s - 1) * π ^ (-s / 2) * Γ(s / 2) * ζ(s)` across `s = 0`, `s = 1`,
and the poles of `Γ(s / 2)`. -/
noncomputable def xi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- `xi` is entire (`Differentiable ℂ xi`). -/
theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).const_mul (1 / 2 : ℂ)

/-- `xi` is analytic everywhere on `ℂ`. -/
theorem analyticOnNhd_xi : AnalyticOnNhd ℂ xi Set.univ :=
  differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ

/-- Value of `xi` at `s = 0`: `xi 0 = 1 / 2`. -/
@[simp]
theorem xi_zero : xi 0 = 1 / 2 := by
  simp [xi]

/-- Value of `xi` at `s = 1`: `xi 1 = 1 / 2`. -/
@[simp]
theorem xi_one : xi 1 = 1 / 2 := by
  simp [xi]

/-- Symmetric functional equation for `xi`: `xi (1 - s) = xi s` for all `s : ℂ`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

/-- Symmetry of `xi` about the critical line `Re s = 1 / 2`:
`xi (1 / 2 - w) = xi (1 / 2 + w)`. -/
theorem xi_half_sub_eq_add (w : ℂ) : xi (1 / 2 - w) = xi (1 / 2 + w) := by
  have heq : (1 : ℂ) - (1 / 2 + w) = 1 / 2 - w := by ring
  rw [← heq, xi_one_sub]

/-- Conjugation symmetry of `xi`: `xi (conj s) = conj (xi s)`. -/
@[simp]
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp only [map_zero, xi_zero, map_div₀, map_one, conj_ofNat]
  rcases eq_or_ne s 1 with rfl | hs1
  · simp only [map_one, xi_one, map_div₀, map_one, conj_ofNat]
  have h1 : completedRiemannZeta (conj s) = conj (completedRiemannZeta s) :=
    completedRiemannZeta_conj s
  have h0 : completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
    have hL := completedRiemannZeta_eq (conj s)
    have hR := congrArg conj (completedRiemannZeta_eq s)
    simp only [map_sub, map_div₀, map_one] at hR
    rw [← h1] at hR
    linear_combination hR - hL
  simp only [xi, map_mul, map_div₀, map_one, map_ofNat, map_add, map_sub, h0]

/-- `xi` takes real values on the critical line `1 / 2 + t * I`. -/
theorem xi_half_add_mul_I_im (t : ℝ) : (xi (1 / 2 + (t : ℂ) * I)).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [← xi_conj]
  have hconj : conj ((1 / 2 : ℂ) + (t : ℂ) * I) = 1 - ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp; norm_num
  rw [hconj, xi_one_sub]

/-- Relation between `xi` and Mathlib's `completedRiemannZeta` away from `s = 0` and `s = 1`. -/
theorem xi_eq_half_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, hs1']
  ring

/-- Classical formula for `xi` away from `s = 1` and the poles of `Γ(s / 2)`:
`xi s = (1 / 2) * s * (s - 1) * π ^ (-s / 2) * Γ(s / 2) * ζ(s)`. -/
theorem xi_eq_formula {s : ℂ} (hs : ∀ m : ℕ, s ≠ -2 * (m : ℂ)) (hs1 : s ≠ 1) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
      riemannZeta s := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm ↦ ?_
    apply hs m
    linear_combination 2 * hm
  have hpi : (π : ℂ) ^ (-s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hGr : Gammaℝ s ≠ 0 := by
    rw [Gammaℝ_def]
    exact mul_ne_zero hpi hG_ne
  rw [xi_eq_half_mul_completedRiemannZeta hs0 hs1, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hpi, hG_ne]

/-- Classical formula for `xi` on the open right half-plane `0 < s.re` (`s ≠ 1`). -/
theorem xi_eq_formula_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
      riemannZeta s := by
  refine xi_eq_formula (fun m h ↦ ?_) hs1
  have hre := congrArg Complex.re h
  simp only [neg_mul, neg_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
    sub_zero] at hre
  linarith

/-- Limit formula for `xi` at `s = 0`, `s = 1`, or any point `s₀`: the classical product agrees
with `xi s₀` in the limit along `𝓝[≠] s₀`. -/
theorem tendsto_xi_formula (s₀ : ℂ) :
    Tendsto (fun s : ℂ ↦
        (1 / 2 : ℂ) * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s)
      (𝓝[≠] s₀) (𝓝 (xi s₀)) := by
  refine (differentiable_xi.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev_ne1 : ∀ᶠ s in 𝓝[≠] s₀, s ≠ 1 := by
    by_cases h : s₀ = 1
    · subst h; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)
  have hev_nonpole : ∀ᶠ s in 𝓝[≠] s₀, ∀ m : ℕ, s ≠ -2 * (m : ℂ) := by
    have hopen : IsOpen ((fun s : ℂ ↦ s / 2) ⁻¹' nonPoleSet) :=
      isOpen_nonPoleSet.preimage (continuous_id.div_const 2)
    by_cases hmem : s₀ / 2 ∈ nonPoleSet
    · filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem)] with s hs m hsm
      exact hs m (by rw [hsm]; ring)
    · simp only [mem_nonPoleSet_iff, not_forall, not_not] at hmem
      obtain ⟨m₀, hm₀⟩ := hmem
      have hs₀_eq : s₀ = -2 * (m₀ : ℂ) := by linear_combination 2 * hm₀
      let r : ℝ := 1
      have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ zero_lt_one
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with s hs_ne hs_ball m hm
      have hs_dist : dist s s₀ < 1 := Metric.mem_ball.mp hs_ball
      have hdiff : dist s s₀ = 2 * |(m : ℝ) - (m₀ : ℝ)| := by
        rw [dist_eq_norm, hm, hs₀_eq]
        have hsub : (-2 * (m : ℂ) - -2 * (m₀ : ℂ)) = ((-2 : ℝ) * ((m : ℝ) - m₀) : ℝ) := by
          push_cast; ring
        rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hm_eq : m = m₀ := by
        by_contra hne
        have h1 : (1 : ℝ) ≤ |(m : ℝ) - (m₀ : ℝ)| := by
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · have : (m : ℝ) + 1 ≤ m₀ := by exact_mod_cast hlt
            rw [abs_of_neg (by linarith)]
            linarith
          · have : (m₀ : ℝ) + 1 ≤ m := by exact_mod_cast hlt
            rw [abs_of_nonneg (by linarith)]
            linarith
        linarith
      exact hs_ne (by simp [hm, hs₀_eq, hm_eq])
  filter_upwards [hev_ne1, hev_nonpole] with s hs1 hspole
  exact xi_eq_formula hspole hs1

/-- Bridge to Mathlib's asymmetric functional equation for `riemannZeta`. -/
theorem riemannZeta_functional_equation {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Complex.Gamma s * cos (π * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

/-- Asymmetric functional equation written with `s` on the left and `1 - s` on the right, valid
for `∀ n : ℕ, 1 - s ≠ -n` and `s ≠ 0`. -/
theorem riemannZeta_eq_functional_equation {s : ℂ} (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) (hs0 : s ≠ 0) :
    riemannZeta s =
      2 * (2 * π) ^ (s - 1) * Complex.Gamma (1 - s) * sin (π * s / 2) * riemannZeta (1 - s) := by
  have h1 : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h
    exact hs n (by linear_combination -h)
  have h2 : 1 - s ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have hfe := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at hfe
  have hcos : Complex.cos (π * (1 - s) / 2) = Complex.sin (π * s / 2) := by
    rw [show (π : ℂ) * (1 - s) / 2 = π / 2 - π * s / 2 by ring, Complex.cos_pi_div_two_sub]
  have hexp : -(1 - s) = s - 1 := by ring
  rw [hcos, hexp] at hfe
  exact hfe

/-- `xi s ≠ 0` whenever `1 ≤ s.re`. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have hs0 : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  rw [xi_eq_formula_of_re_pos hs0 hs1]
  have hpi : (π : ℂ) ^ (-s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [hs0])
  have hs_ne : s ≠ 0 := fun h ↦ by simp [h] at hs0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (by norm_num) hs_ne) hs1') hpi) hG) hz

/-- `xi s ≠ 0` whenever `s.re ≤ 0` (in particular at `s = 0` and at trivial zeros `-2 * (k + 1)`). -/
theorem xi_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_one_sub]
  exact xi_ne_zero_of_one_le_re (by simp only [sub_re, one_re]; linarith)

/-- Characterization of zeros of `xi`: `xi s = 0` if and only if `riemannZeta s = 0` and
`0 < s.re < 1`. -/
theorem xi_eq_zero_iff {s : ℂ} :
    xi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hxi
    have hre_pos : 0 < s.re := by
      by_contra hle
      push Not at hle
      exact xi_ne_zero_of_re_nonpos hle hxi
    have hre_lt : s.re < 1 := by
      by_contra hge
      push Not at hge
      exact xi_ne_zero_of_one_le_re hge hxi
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hre_lt
    have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hre_pos
    rw [xi_eq_formula_of_re_pos hre_pos hs1] at hxi
    have hpi : (π : ℂ) ^ (-s / 2) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hG : Complex.Gamma (s / 2) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp [hre_pos])
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hpre : (1 / 2 : ℂ) * s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1') hpi) hG
    have hz : riemannZeta s = 0 := (mul_eq_zero.mp hxi).resolve_left hpre
    exact ⟨hz, hre_pos, hre_lt⟩
  · rintro ⟨hz, hre_pos, hre_lt⟩
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hre_lt
    rw [xi_eq_formula_of_re_pos hre_pos hs1, hz, mul_zero]

end CompletedZetaAndFunctionalEquation

section OrderOfXi

/-- Explicit polynomial bound for `riemannZeta s` on the half-plane `1 / 2 ≤ s.re` away from
`s = 1` (`2 ≤ ‖s‖`): `‖riemannZeta s‖ ≤ 2 * ‖s‖`. -/
theorem norm_riemannZeta_re_ge_half_le {s : ℂ} (hs_re : 1 / 2 ≤ s.re) (hs_norm : 2 ≤ ‖s‖) :
    ‖riemannZeta s‖ ≤ 2 * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, norm_one] at hs_norm
    linarith
  have h1s : 1 ≤ ‖s - 1‖ := by
    have h := norm_sub_norm_le s 1
    rw [norm_one] at h
    linarith
  rw [riemannZeta_eq_eulerMaclaurin_of_re_pos hs0 hs1]
  have hint_bd : ‖∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    have hdom_int : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-s.re - 1)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul (1 / 2)
    have h_int := integrableOn_sawtooth_cpow_Ioi zero_lt_one hs0
    have hmono : ∫ u in Set.Ioi (1 : ℝ), ‖(sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤
        ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-s.re - 1) := by
      refine setIntegral_mono_on h_int.norm hdom_int measurableSet_Ioi fun u hu ↦ ?_
      have hu_pos : 0 < u := lt_trans zero_lt_one hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
      simp only [sub_re, neg_re, one_re]
      exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)
    have heval : ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-s.re - 1) = (1 / 2) / s.re := by
      rw [integral_const_mul]
      have hint_rpow : ∫ u in Set.Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
        have htend : Tendsto (fun R : ℝ ↦ ∫ u in (1 : ℝ)..R, u ^ (-s.re - 1)) atTop
            (𝓝 (∫ u in Set.Ioi (1 : ℝ), u ^ (-s.re - 1))) :=
          intervalIntegral_tendsto_integral_Ioi 1
            (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one) tendsto_id
        have hcalc : ∀ R : ℝ, 1 ≤ R →
            ∫ u in (1 : ℝ)..R, u ^ (-s.re - 1) = (1 - R ^ (-s.re)) / s.re := by
          intro R hR
          rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
            rw [Set.uIcc_of_le hR] at h; linarith [h.1]⟩)]
          simp only [Real.one_rpow]
          have hexp : -s.re - 1 + 1 = -s.re := by ring
          rw [hexp]
          field_simp [hs0.ne']
          ring
        have hlim : Tendsto (fun R : ℝ ↦ (1 - R ^ (-s.re)) / s.re) atTop (𝓝 (1 / s.re)) := by
          have hr : Tendsto (fun R : ℝ ↦ R ^ (-s.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hs0
          simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hr).div_const s.re
        exact tendsto_nhds_unique htend (hlim.congr' (by
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR; exact (hcalc R hR).symm))
      rw [hint_rpow]
      ring
    calc
      ‖∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖
          ≤ ∫ u in Set.Ioi (1 : ℝ), ‖(sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-s.re - 1) := hmono
      _ = (1 / 2) / s.re := heval
      _ ≤ 1 := by
        rw [div_le_one hs0]
        linarith
  have hterm1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact div_le_one_of_le₀ h1s (by positivity)
  have hterm2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  calc
    ‖1 / (s - 1) + 1 / 2 - s * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖
        ≤ ‖(1 : ℂ) / (s - 1)‖ + ‖(1 / 2 : ℂ)‖ +
            ‖s * ∫ u in Set.Ioi (1 : ℝ), (sawtooth u : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 1 + 1 / 2 + ‖s‖ * 1 := by
      rw [norm_mul, hterm2]
      gcongr
    _ ≤ 2 * ‖s‖ := by linarith

private lemma norm_gamma_half_le_of_re_ge_half {z : ℂ} (hz_re : 1 / 2 ≤ z.re)
    (hz_norm : 2 ≤ ‖z‖) :
    ‖Complex.Gamma (z / 2)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp 1 *
        Real.exp ((‖z‖ / 2) * Real.log (‖z‖ / 2) + (Real.pi / 4) * ‖z‖) := by
  let w : ℂ := z / 2
  have hw_re : 1 / 4 ≤ w.re := by simp [w]; linarith
  have hw_pos : 0 < w.re := by linarith
  have hw_norm_ge : 1 ≤ ‖w‖ := by
    have heq : ‖w‖ = ‖z‖ / 2 := by simp [w]
    linarith
  have hw_norm_eq : ‖w‖ = ‖z‖ / 2 := by simp [w]
  have hw_slit : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw_pos)
  have hw_arg : |w.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw_pos)
  have hcos_ge : Real.sqrt 2 / 2 ≤ Real.cos (w.arg / 2) := by
    have h1 : |w.arg / 2| ≤ Real.pi / 4 := by
      rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
      linarith
    have hcos_abs : Real.cos (w.arg / 2) = Real.cos |w.arg / 2| := by
      rcases le_or_gt 0 (w.arg / 2) with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, Real.cos_neg]
    rw [hcos_abs, ← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [Real.pi_pos]) h1
  have hcos_pos : 0 < Real.cos (w.arg / 2) := lt_of_lt_of_le (by positivity) hcos_ge
  have hcos_inv_sq : (Real.cos (w.arg / 2))⁻¹ ^ 2 ≤ 2 := by
    have hinv : (Real.cos (w.arg / 2))⁻¹ ≤ Real.sqrt 2 := by
      rw [inv_le_comm₀ hcos_pos (by positivity)]
      have hsq : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
        rw [inv_eq_one_div, div_eq_div_iff (Real.sqrt_ne_zero'.mpr two_pos) two_ne_zero,
          one_mul, Real.mul_self_sqrt zero_le_two]
      linarith
    calc
      (Real.cos (w.arg / 2))⁻¹ ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr hcos_pos.le) hinv 2
      _ = 2 := Real.sq_sqrt zero_le_two
  have hrem : ‖stirlingRemainder w‖ ≤ 1 := by
    have h1 := norm_stirlingRemainder_le hw_slit
    have hden : (3 : ℝ) ≤ 12 * ‖w‖ := by linarith
    calc
      ‖stirlingRemainder w‖ ≤ (1 + (Real.cos (w.arg / 2))⁻¹ ^ 2) / (12 * ‖w‖) := h1
      _ ≤ (1 + 2) / 3 := by gcongr
      _ = 1 := by norm_num
  have hrem_re : (stirlingRemainder w).re ≤ 1 :=
    (Complex.re_le_norm _).trans hrem
  have hlog_nn : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw_norm_ge
  have hre_le : (w.re - 1 / 2) * Real.log ‖w‖ ≤ ‖w‖ * Real.log ‖w‖ := by
    refine mul_le_mul_of_nonneg_right ?_ hlog_nn
    linarith [Complex.re_le_norm w]
  have him_le : -w.im * w.arg ≤ (Real.pi / 2) * ‖w‖ := by
    calc
      -w.im * w.arg ≤ |-w.im * w.arg| := le_abs_self _
      _ = |w.im| * |w.arg| := by rw [abs_mul, abs_neg]
      _ ≤ ‖w‖ * (Real.pi / 2) :=
        mul_le_mul (Complex.abs_im_le_norm w) hw_arg.le (abs_nonneg _) (norm_nonneg _)
      _ = (Real.pi / 2) * ‖w‖ := by ring
  rw [show z / 2 = w by rfl, norm_complex_gamma_eq_of_mem_slitPlane hw_slit]
  have hexp_le : (w.re - 1 / 2) * Real.log ‖w‖ - w.im * w.arg - w.re + (stirlingRemainder w).re ≤
      1 + ((‖z‖ / 2) * Real.log (‖z‖ / 2) + (Real.pi / 4) * ‖z‖) := by
    rw [hw_norm_eq] at hre_le him_le ⊢
    linarith [hw_pos]
  calc
    Real.sqrt (2 * Real.pi) *
        Real.exp ((w.re - 1 / 2) * Real.log ‖w‖ - w.im * w.arg - w.re + (stirlingRemainder w).re)
        ≤ Real.sqrt (2 * Real.pi) *
            Real.exp (1 + ((‖z‖ / 2) * Real.log (‖z‖ / 2) + (Real.pi / 4) * ‖z‖)) := by
      gcongr
    _ = Real.sqrt (2 * Real.pi) * Real.exp 1 *
          Real.exp ((‖z‖ / 2) * Real.log (‖z‖ / 2) + (Real.pi / 4) * ‖z‖) := by
      rw [Real.exp_add, mul_assoc]

/-- Explicit growth bound `‖xi z‖ ≤ A * Real.exp (B * ‖z‖ * Real.log (‖z‖ + 2))` for all
`z : ℂ`. -/
theorem norm_xi_le_exp_norm_mul_log :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ z : ℂ, ‖xi z‖ ≤ A * Real.exp (B * ‖z‖ * Real.log (‖z‖ + 2)) := by
  let C₀ : ℝ := 12 * Real.sqrt (2 * Real.pi) * Real.exp 1
  have hC₀_pos : 0 < C₀ := by positivity
  let B₀ : ℝ := 4 + Real.pi
  have hB₀_pos : 0 < B₀ := by positivity
  have hhalf_bound : ∀ w : ℂ, 1 / 2 ≤ w.re → 2 ≤ ‖w‖ →
      ‖xi w‖ ≤ C₀ * Real.exp (B₀ * ‖w‖ * Real.log (‖w‖ + 2)) := by
    intro w hw_re hw_norm
    have hw0 : 0 < w.re := by linarith
    have hw1 : w ≠ 1 := by intro h; rw [h, norm_one] at hw_norm; linarith
    rw [xi_eq_formula_of_re_pos hw0 hw1]
    have hpi_le : ‖(π : ℂ) ^ (-w / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) ?_
      simp only [div_ofNat_re, neg_re]
      linarith
    have hw_sub : ‖w - 1‖ ≤ 2 * ‖w‖ := by
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖w‖ + 1 := by rw [norm_one]
        _ ≤ 2 * ‖w‖ := by linarith
    have hzeta := norm_riemannZeta_re_ge_half_le hw_re hw_norm
    have hgamma := norm_gamma_half_le_of_re_ge_half hw_re hw_norm
    have hcube : ‖w‖ ^ 3 ≤ 6 * Real.exp ‖w‖ := by
      have h := Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) 3
      norm_num [Nat.factorial] at h
      linarith
    have hlog_ge_one : 1 ≤ Real.log (‖w‖ + 2) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    have hlog_half : Real.log (‖w‖ / 2) ≤ Real.log (‖w‖ + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hexp_comb : ‖w‖ + ((‖w‖ / 2) * Real.log (‖w‖ / 2) + (Real.pi / 4) * ‖w‖) ≤
        B₀ * ‖w‖ * Real.log (‖w‖ + 2) := by
      have h1 : (‖w‖ / 2) * Real.log (‖w‖ / 2) ≤ ‖w‖ * Real.log (‖w‖ + 2) := by
        have hpos : 0 ≤ ‖w‖ / 2 := by positivity
        calc
          (‖w‖ / 2) * Real.log (‖w‖ / 2) ≤ (‖w‖ / 2) * Real.log (‖w‖ + 2) :=
            mul_le_mul_of_nonneg_left hlog_half hpos
          _ ≤ ‖w‖ * Real.log (‖w‖ + 2) := by
            gcongr
            linarith
      have h2 : (1 + Real.pi / 4) * ‖w‖ ≤ (1 + Real.pi / 4) * ‖w‖ * Real.log (‖w‖ + 2) := by
        have hnn : 0 ≤ (1 + Real.pi / 4) * ‖w‖ := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlog_ge_one hnn
      have h3 : (1 + Real.pi / 4 + 1) * ‖w‖ * Real.log (‖w‖ + 2) ≤
          B₀ * ‖w‖ * Real.log (‖w‖ + 2) := by
        have hnn : 0 ≤ ‖w‖ * Real.log (‖w‖ + 2) := mul_nonneg (norm_nonneg _) (by linarith)
        have hB : 1 + Real.pi / 4 + 1 ≤ B₀ := by
          dsimp only [B₀]
          linarith [Real.pi_pos]
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hB hnn
      linarith
    have hpre : ‖(1 / 2 : ℂ) * w * (w - 1) * (π : ℂ) ^ (-w / 2) *
        Complex.Gamma (w / 2) * riemannZeta w‖ ≤
        (1 / 2 : ℝ) * ‖w‖ * (2 * ‖w‖) * 1 * ‖Complex.Gamma (w / 2)‖ * (2 * ‖w‖) := by
      simp only [norm_mul]
      have hhalf_norm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [hhalf_norm]
      gcongr
    calc
      ‖(1 / 2 : ℂ) * w * (w - 1) * (π : ℂ) ^ (-w / 2) *
          Complex.Gamma (w / 2) * riemannZeta w‖
          ≤ 2 * ‖w‖ ^ 3 * ‖Complex.Gamma (w / 2)‖ := by linarith
      _ ≤ 2 * (6 * Real.exp ‖w‖) * (Real.sqrt (2 * Real.pi) * Real.exp 1 *
            Real.exp ((‖w‖ / 2) * Real.log (‖w‖ / 2) + (Real.pi / 4) * ‖w‖)) := by
          gcongr
      _ = C₀ * Real.exp (‖w‖ + ((‖w‖ / 2) * Real.log (‖w‖ / 2) + (Real.pi / 4) * ‖w‖)) := by
          dsimp only [C₀]
          simp only [Real.exp_add]
          ring
      _ ≤ C₀ * Real.exp (B₀ * ‖w‖ * Real.log (‖w‖ + 2)) := by gcongr
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_closedBall (0 : ℂ) 3).image_of_continuousOn
      differentiable_xi.continuous.continuousOn.norm).bddAbove
  let A : ℝ := max C₀ (max M₀ 1)
  let B : ℝ := 2 * B₀ * 2
  have hA_pos : 0 < A := lt_of_lt_of_le hC₀_pos (le_max_left _ _)
  have hB_pos : 0 < B := by positivity
  refine ⟨A, B, hA_pos, hB_pos, fun z ↦ ?_⟩
  by_cases hz3 : 3 ≤ ‖z‖
  · have hlog_le_two : ∀ x : ℝ, 2 ≤ x → Real.log (2 * x + 2) ≤ 2 * Real.log (x + 2) := by
      intro x hx
      have hle : 2 * x + 2 ≤ (x + 2) ^ 2 := by nlinarith
      calc
        Real.log (2 * x + 2) ≤ Real.log ((x + 2) ^ 2) := Real.log_le_log (by linarith) hle
        _ = 2 * Real.log (x + 2) := by rw [Real.log_pow]; norm_cast
    rcases le_or_gt (1 / 2 : ℝ) z.re with hz_re | hz_re
    · have hbd := hhalf_bound z hz_re (by linarith)
      have hA : C₀ ≤ A := le_max_left _ _
      have hexp : B₀ * ‖z‖ * Real.log (‖z‖ + 2) ≤ B * ‖z‖ * Real.log (‖z‖ + 2) := by
        have hnn : 0 ≤ ‖z‖ * Real.log (‖z‖ + 2) :=
          mul_nonneg (norm_nonneg _) (Real.log_nonneg (by linarith))
        have hB : B₀ ≤ B := by dsimp only [B]; linarith
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hB hnn
      exact hbd.trans (mul_le_mul hA (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le hA_pos.le)
    · rw [← xi_one_sub]
      have h1z_re : 1 / 2 ≤ (1 - z).re := by simp; linarith
      have h1z_ge : 2 ≤ ‖1 - z‖ := by
        have h := norm_sub_norm_le z 1
        rw [norm_sub_rev, norm_one] at h
        linarith
      have h1z_le : ‖1 - z‖ ≤ 2 * ‖z‖ := by
        calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
          _ = 1 + ‖z‖ := by rw [norm_one]
          _ ≤ 2 * ‖z‖ := by linarith
      have hbd := hhalf_bound (1 - z) h1z_re h1z_ge
      have hlog : Real.log (‖1 - z‖ + 2) ≤ 2 * Real.log (‖z‖ + 2) := by
        calc Real.log (‖1 - z‖ + 2) ≤ Real.log (2 * ‖z‖ + 2) :=
              Real.log_le_log (by linarith) (by linarith)
          _ ≤ 2 * Real.log (‖z‖ + 2) := hlog_le_two ‖z‖ (by linarith)
      have hexp : B₀ * ‖1 - z‖ * Real.log (‖1 - z‖ + 2) ≤ B * ‖z‖ * Real.log (‖z‖ + 2) := by
        have h1 : B₀ * ‖1 - z‖ ≤ B₀ * (2 * ‖z‖) :=
          mul_le_mul_of_nonneg_left h1z_le hB₀_pos.le
        have hnn : 0 ≤ Real.log (‖1 - z‖ + 2) := Real.log_nonneg (by linarith)
        calc
          B₀ * ‖1 - z‖ * Real.log (‖1 - z‖ + 2)
              ≤ (B₀ * (2 * ‖z‖)) * (2 * Real.log (‖z‖ + 2)) :=
            mul_le_mul h1 hlog hnn (by positivity)
          _ = B * ‖z‖ * Real.log (‖z‖ + 2) := by dsimp only [B]; ring
      have hA : C₀ ≤ A := le_max_left _ _
      exact hbd.trans (mul_le_mul hA (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le hA_pos.le)
  · have hz_ball : z ∈ Metric.closedBall (0 : ℂ) 3 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hnorm : ‖xi z‖ ≤ A :=
      (hM₀ ⟨z, hz_ball, rfl⟩).trans ((le_max_left _ 1).trans (le_max_right _ _))
    have hexp_ge : 1 ≤ Real.exp (B * ‖z‖ * Real.log (‖z‖ + 2)) := by
      rw [Real.one_le_exp_iff]
      have hlog_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg z])
      positivity
    calc
      ‖xi z‖ ≤ A := hnorm
      _ = A * 1 := (mul_one A).symm
      _ ≤ A * Real.exp (B * ‖z‖ * Real.log (‖z‖ + 2)) := mul_le_mul_of_nonneg_left hexp_ge hA_pos.le

/-- `xi` is an entire function of order at most `1`: `EntireOrderLe xi 1`. -/
theorem entireOrderLe_xi_one : EntireOrderLe xi 1 := by
  obtain ⟨A, B, hA_pos, hB_pos, hbd⟩ := norm_xi_le_exp_norm_mul_log
  refine entireOrderLe_of_eventually_exp differentiable_xi fun δ hδ ↦ ?_
  let δ' : ℝ := min δ 1
  have hδ'_pos : 0 < δ' := lt_min hδ zero_lt_one
  have hδ'_le1 : δ' ≤ 1 := min_le_right _ _
  have hδ'_leδ : δ' ≤ δ := min_le_left _ _
  refine ⟨A, (2 / δ') * B, 2, by norm_num, fun z hz ↦ ?_⟩
  have hlog_bd : Real.log (‖z‖ + 2) ≤ (1 / δ') * (‖z‖ + 2) ^ δ' := by
    have hpos : 0 < ‖z‖ + 2 := by linarith
    have h1 : Real.log ((‖z‖ + 2) ^ δ') ≤ (‖z‖ + 2) ^ δ' - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos _)
    rw [Real.log_rpow hpos] at h1
    have h2 : δ' * Real.log (‖z‖ + 2) ≤ (‖z‖ + 2) ^ δ' := by linarith
    calc
      Real.log (‖z‖ + 2) = (1 / δ') * (δ' * Real.log (‖z‖ + 2)) := by
        field_simp [hδ'_pos.ne']
      _ ≤ (1 / δ') * (‖z‖ + 2) ^ δ' := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hrpow_bd : (‖z‖ + 2) ^ δ' ≤ 2 * ‖z‖ ^ δ := by
    have h1 : (‖z‖ + 2) ^ δ' ≤ (2 * ‖z‖) ^ δ' :=
      Real.rpow_le_rpow (by linarith) (by linarith) hδ'_pos.le
    have h2 : (2 * ‖z‖) ^ δ' = (2 : ℝ) ^ δ' * ‖z‖ ^ δ' :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h3 : (2 : ℝ) ^ δ' ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ'_le1
    have h4 : ‖z‖ ^ δ' ≤ ‖z‖ ^ δ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hδ'_leδ
    calc
      (‖z‖ + 2) ^ δ' ≤ (2 : ℝ) ^ δ' * ‖z‖ ^ δ' := h1.trans_eq h2
      _ ≤ 2 * ‖z‖ ^ δ := mul_le_mul h3 h4 (by positivity) (by norm_num)
  have hexp_le : B * ‖z‖ * Real.log (‖z‖ + 2) ≤ ((2 / δ') * B) * ‖z‖ ^ (1 + δ) := by
    have hrpow_eq : ‖z‖ ^ (1 + δ) = ‖z‖ * ‖z‖ ^ δ := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hlog_le2 : Real.log (‖z‖ + 2) ≤ (2 / δ') * ‖z‖ ^ δ := by
      calc
        Real.log (‖z‖ + 2) ≤ (1 / δ') * (‖z‖ + 2) ^ δ' := hlog_bd
        _ ≤ (1 / δ') * (2 * ‖z‖ ^ δ) := mul_le_mul_of_nonneg_left hrpow_bd (by positivity)
        _ = (2 / δ') * ‖z‖ ^ δ := by ring
    calc
      B * ‖z‖ * Real.log (‖z‖ + 2) ≤ B * ‖z‖ * ((2 / δ') * ‖z‖ ^ δ) :=
        mul_le_mul_of_nonneg_left hlog_le2 (by positivity)
      _ = ((2 / δ') * B) * (‖z‖ * ‖z‖ ^ δ) := by ring
      _ = ((2 / δ') * B) * ‖z‖ ^ (1 + δ) := by rw [hrpow_eq]
  exact (hbd z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) hA_pos.le)

/-- `xi` has finite order (`HasFiniteOrder xi`). -/
theorem hasFiniteOrder_xi : HasFiniteOrder xi :=
  entireOrderLe_xi_one.hasFiniteOrder zero_le_one

private lemma norm_xi_ofReal_ge_lower {x : ℝ} (hx : 4 ≤ x) :
    Real.exp (x * (Real.log (x / 2) / 4 - (1 + Real.log Real.pi) / 2)) ≤ ‖xi (x : ℂ)‖ := by
  have hx_pos : 0 < x := by linarith
  have hx_gt1 : 1 < (x : ℂ).re := by simp; linarith
  have hx_ne1 : (x : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzeta_ge : 1 ≤ ‖riemannZeta (x : ℂ)‖ := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hx_gt1]
    have hsumm_real : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ x) := by
      have h := Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < x)
      refine (summable_nat_add_iff 1).mpr h |>.congr fun n ↦ ?_
      simp [Nat.cast_add, Nat.cast_one]
    have htsum_eq : ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (x : ℂ) =
        ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ x : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      rw [Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      push_cast
      rfl
    rw [htsum_eq, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun n ↦ by positivity)]
    have h0 := hsumm_real.le_tsum 0 fun n _ ↦ by positivity
    simpa using h0
  have hpi_eq : ‖(π : ℂ) ^ (-(x : ℂ) / 2)‖ = Real.exp (-(x / 2) * Real.log Real.pi) := by
    rw [show -(x : ℂ) / 2 = ((- (x / 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re,
      Real.rpow_def_of_pos Real.pi_pos, mul_comm]
  have hgamma_ge : Real.exp ((x / 2 - 1 / 2) * Real.log (x / 2) - x / 2) ≤
      ‖Complex.Gamma ((x : ℂ) / 2)‖ := by
    have hx2_pos : 0 < x / 2 := by linarith
    have heq : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (real_gamma_pos_of_pos hx2_pos).le]
    have hst := real_log_gamma_eq_stirling hx2_pos
    have hrem := stirlingRemainderReal_nonneg hx2_pos
    have hlog_pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
      have h1 : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
      exact div_nonneg (Real.log_nonneg h1) zero_le_two
    have hlog_ge : (x / 2 - 1 / 2) * Real.log (x / 2) - x / 2 ≤
        Real.log (Real.Gamma (x / 2)) := by
      linarith
    rw [← Real.exp_log (real_gamma_pos_of_pos hx2_pos)]
    exact Real.exp_le_exp.mpr hlog_ge
  have hpre_ge : 1 ≤ ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1)‖ := by
    have heq : (1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1) =
        (((1 / 2 : ℝ) * x * (x - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]
    nlinarith
  have hlog_half_nn : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by linarith)
  have hexp_ge : x * (Real.log (x / 2) / 4 - (1 + Real.log Real.pi) / 2) ≤
      -(x / 2) * Real.log Real.pi + ((x / 2 - 1 / 2) * Real.log (x / 2) - x / 2) := by
    have h1 : x / 4 ≤ x / 2 - 1 / 2 := by linarith
    have h2 : (x / 4) * Real.log (x / 2) ≤ (x / 2 - 1 / 2) * Real.log (x / 2) :=
      mul_le_mul_of_nonneg_right h1 hlog_half_nn
    linarith
  rw [xi_eq_formula_of_re_pos (by simp; linarith) hx_ne1]
  have hnorm_prod : ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1) * (π : ℂ) ^ (-(x : ℂ) / 2) *
      Complex.Gamma ((x : ℂ) / 2) * riemannZeta (x : ℂ)‖ =
      ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1)‖ * ‖(π : ℂ) ^ (-(x : ℂ) / 2)‖ *
        ‖Complex.Gamma ((x : ℂ) / 2)‖ * ‖riemannZeta (x : ℂ)‖ := by
    simp only [norm_mul]
  rw [hnorm_prod]
  calc
    Real.exp (x * (Real.log (x / 2) / 4 - (1 + Real.log Real.pi) / 2))
        ≤ Real.exp (-(x / 2) * Real.log Real.pi + ((x / 2 - 1 / 2) * Real.log (x / 2) - x / 2)) :=
      Real.exp_le_exp.mpr hexp_ge
    _ = Real.exp (-(x / 2) * Real.log Real.pi) *
          Real.exp ((x / 2 - 1 / 2) * Real.log (x / 2) - x / 2) := Real.exp_add _ _
    _ = 1 * ‖(π : ℂ) ^ (-(x : ℂ) / 2)‖ *
          Real.exp ((x / 2 - 1 / 2) * Real.log (x / 2) - x / 2) * 1 := by
        rw [hpi_eq]; ring
    _ ≤ ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1)‖ * ‖(π : ℂ) ^ (-(x : ℂ) / 2)‖ *
          ‖Complex.Gamma ((x : ℂ) / 2)‖ * ‖riemannZeta (x : ℂ)‖ := by
        gcongr

private lemma not_entireOrderLe_xi_of_lt {ρ₀ : ℝ} (hρ₀ : ρ₀ < 1) : ¬ EntireOrderLe xi ρ₀ := by
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
  let X₀ : ℝ := 2 * Real.exp (4 + 2 * (1 + Real.log Real.pi))
  let x : ℝ := max (max 4 X₀) (max (2 ^ (1 / δ)) (2 * (Real.log C₁ + 1)))
  have hx4 : 4 ≤ x := (le_max_left 4 X₀).trans (le_max_left _ _)
  have hxX₀ : X₀ ≤ x := (le_max_right 4 X₀).trans (le_max_left _ _)
  have hx_pow : 2 ^ (1 / δ) ≤ x := (le_max_left _ _).trans (le_max_right _ _)
  have hx_log : 2 * (Real.log C₁ + 1) ≤ x := (le_max_right _ _).trans (le_max_right _ _)
  have hx_pos : 0 < x := by linarith
  have hx_delta : 2 ≤ x ^ δ := by
    have h1 : (1 : ℝ) ≤ 2 ^ (1 / δ) := Real.one_le_rpow one_le_two (one_div_nonneg.mpr hδ_pos.le)
    have hr := Real.rpow_le_rpow (by positivity) hx_pow hδ_pos.le
    have heq : ((2 : ℝ) ^ (1 / δ)) ^ δ = 2 := by
      rw [← Real.rpow_mul zero_le_two, one_div_mul_cancel hδ_pos.ne', Real.rpow_one]
    rwa [heq] at hr
  have hx_alpha : x ^ α ≤ x / 2 := by
    have h1 : 2 * x ^ α ≤ x := by
      calc
        2 * x ^ α ≤ x ^ δ * x ^ α :=
          mul_le_mul_of_nonneg_right hx_delta (Real.rpow_nonneg hx_pos.le α)
        _ = x ^ (δ + α) := (Real.rpow_add hx_pos δ α).symm
        _ = x ^ (1 : ℝ) := by dsimp only [δ]; ring_nf
        _ = x := Real.rpow_one x
    linarith
  have hlog_ge : 1 ≤ Real.log (x / 2) / 4 - (1 + Real.log Real.pi) / 2 := by
    have hle_exp : Real.exp (4 + 2 * (1 + Real.log Real.pi)) ≤ x / 2 := by
      dsimp only [X₀] at hxX₀
      linarith
    have hlog_x2 := (Real.le_log_iff_exp_le (by linarith)).mpr hle_exp
    linarith
  have hlow : Real.exp x ≤ ‖xi (x : ℂ)‖ := by
    have h1 : x ≤ x * (Real.log (x / 2) / 4 - (1 + Real.log Real.pi) / 2) := by
      simpa using mul_le_mul_of_nonneg_left hlog_ge hx_pos.le
    exact (Real.exp_le_exp.mpr h1).trans (norm_xi_ofReal_ge_lower hx4)
  have hC_lt : C < Real.exp (x / 2) := by
    have hlog_lt : Real.log C₁ < x / 2 := by linarith
    calc
      C ≤ C₁ := le_max_left C 1
      _ = Real.exp (Real.log C₁) := (Real.exp_log hC₁_pos).symm
      _ < Real.exp (x / 2) := Real.exp_lt_exp.mpr hlog_lt
  have hup : ‖xi (x : ℂ)‖ ≤ C * Real.exp (x ^ α) := by
    have h1 := hbound (x : ℂ)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos] at h1
  have hgt : C * Real.exp (x ^ α) < Real.exp x := by
    calc
      C * Real.exp (x ^ α) < Real.exp (x / 2) * Real.exp (x ^ α) :=
        mul_lt_mul_of_pos_right hC_lt (Real.exp_pos _)
      _ = Real.exp (x / 2 + x ^ α) := (Real.exp_add _ _).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  exact lt_irrefl _ (hlow.trans_lt (hup.trans_lt hgt))

/-- The completed Riemann zeta function `xi` has exact entire order `1`. -/
theorem exactOrder_xi : exactOrder xi = 1 := by
  refine le_antisymm (exactOrder_le zero_le_one entireOrderLe_xi_one) ?_
  by_contra hlt
  push Not at hlt
  exact not_entireOrderLe_xi_of_lt hlt (entireOrderLe_exactOrder hasFiniteOrder_xi)

end OrderOfXi

end AnalyticNumberTheory.RiemannZeta
