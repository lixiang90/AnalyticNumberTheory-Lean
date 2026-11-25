import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.HardyZ
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import AnalyticNumberTheory.AnalyticTools.Transforms
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-!
# Hurwitz Zeta Asymptotics, Approximate Dirichlet Polynomials, and Mean-Square Theorems

This file develops:
1. First- and second-order Euler–Maclaurin analytic continuations for `HurwitzZeta.hurwitzZeta`.
2. Explicit approximate Dirichlet polynomial representations with uniform `O((N + a) ^ (-σ))`
   and `O(N ^ (-σ))` error terms in `0 < σ` when `|t| ≤ c * N` (`0 < c < 2π`), proved by Fourier
   expansion of `bernoulliKernel 2` and oscillatory integration by parts.
3. Mean-square convergence theorems on vertical lines `σ > 1 / 2` (both on `[1, T]` for all
   `σ > 1 / 2` and symmetrically on `[-T, T]` for `σ > 1 / 2` with `σ ≠ 1`, bridging
   `DirichletSeries.VerticalOrder`), critical-line `O(log (T + 2))` and `O(T ^ ε)` mean-square
   bounds at `σ = 1 / 2`, and bridges to `hardyZ`.
-/

open Complex Real Filter MeasureTheory Set Asymptotics
open scoped Topology Nat ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

section Helpers

private lemma isPathConnected_re_gt_sdiff_one' {σ₀ : ℝ} (hσ₀ : σ₀ < 1) :
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
      · rw [← ht_zero]; linarith
      · have h1 : (1 - (t : ℝ)) * σ₀ ≤ (1 - (t : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have h2' : (t : ℝ) * σ₀ < (t : ℝ) * z.re := mul_lt_mul_of_pos_left hz_re ht_pos
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
        · rw [← ht_zero]; linarith
        · have h1 : (1 - (t : ℝ)) * σ₀ ≤ (1 - (t : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          have h2' : (t : ℝ) * σ₀ < (t : ℝ) * z.re := mul_lt_mul_of_pos_left hz_re ht_pos
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

/-- Derivative of a shifted Dirichlet monomial on the positive real axis. -/
lemma cpow_shift_hasDerivAt {t a : ℝ} (hta : 0 < t + a) (c : ℂ) :
    HasDerivAt (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ c) (c * ((t + a : ℝ) : ℂ) ^ (c - 1)) t := by
  have hmem : ((t + a : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hta
  have hc : HasDerivAt (fun z : ℂ ↦ z ^ c) (c * ((t + a : ℝ) : ℂ) ^ (c - 1)) ((t + a : ℝ) : ℂ) :=
    (Complex.hasStrictDerivAt_cpow_const hmem).hasDerivAt
  have hr : HasDerivAt (fun x : ℝ ↦ (x : ℂ) ^ c) (c * ((t + a : ℝ) : ℂ) ^ (c - 1)) (t + a) :=
    hc.comp_ofReal
  have hres := hr.scomp t ((hasDerivAt_id t).add_const a)
  rw [one_smul] at hres
  exact hres

private lemma cpow_shift_continuousOn {a₀ b c₀ : ℝ} (hpos : 0 < a₀ + c₀) (z : ℂ) :
    ContinuousOn (fun u : ℝ ↦ ((u + c₀ : ℝ) : ℂ) ^ z) (Set.Icc a₀ b) := by
  refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
  exact (cpow_shift_hasDerivAt (by linarith [hu.1]) z).continuousAt

private lemma integral_cpow_shift_ofReal_eq {a₀ b c₀ : ℝ} (hpos : 0 < a₀ + c₀) (hab : a₀ ≤ b)
    {s : ℂ} (hs : s ≠ 1) :
    ∫ u in a₀..b, ((u + c₀ : ℝ) : ℂ) ^ (-s) =
      (((b + c₀ : ℝ) : ℂ) ^ (1 - s) - ((a₀ + c₀ : ℝ) : ℂ) ^ (1 - s)) / (1 - s) := by
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  have hderiv : ∀ u ∈ Set.uIcc a₀ b,
      HasDerivAt (fun x : ℝ ↦ ((x + c₀ : ℝ) : ℂ) ^ (1 - s) / (1 - s))
        (((u + c₀ : ℝ) : ℂ) ^ (-s)) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hd := (cpow_shift_hasDerivAt (t := u) (a := c₀) (by linarith [hu.1, hpos]) (1 - s)).div_const (1 - s)
    rw [show (1 - s) - 1 = -s by ring, mul_div_cancel_left₀ _ hne] at hd
    exact hd
  have hint : IntervalIntegrable (fun u : ℝ ↦ ((u + c₀ : ℝ) : ℂ) ^ (-s)) volume a₀ b :=
    (cpow_shift_continuousOn hpos (-s)).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, sub_div]

private lemma euler_maclaurin_Icc_complex {M N : ℕ} (hMN : M ≤ N)
    {f f' : ℝ → ℂ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Icc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f M + f N) / 2 +
        ∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t := by
  have hle : (M : ℝ) ≤ N := Nat.cast_le.mpr hMN
  have hre_em := euler_maclaurin_first_order_Icc hMN
    (fun t ht ↦ Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht))
    (Complex.continuous_re.comp_continuousOn hf')
  have him_em := euler_maclaurin_first_order_Icc hMN
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

private lemma euler_maclaurin_Ioc_complex' {M N : ℕ} (hMN : M ≤ N)
    {f f' : ℝ → ℂ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Ioc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f N - f M) / 2 +
        ∫ t in (M : ℝ)..N, (sawtooth t : ℂ) * f' t := by
  have h := euler_maclaurin_Icc_complex hMN hf hf'
  rw [Finset.Icc_eq_cons_Ioc hMN, Finset.sum_cons] at h
  linear_combination h

private lemma integral_bernoulliKernel_one_mul_eq_sub_complex'' {M N : ℕ} (hMN : M ≤ N)
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

private lemma integrableOn_shift_rpow_Ioi {a₀ a : ℝ} (ha₀ : 0 ≤ a₀) (ha : 0 < a) {r : ℝ}
    (hr : r < -1) :
    IntegrableOn (fun u : ℝ ↦ (u + a) ^ r) (Set.Ioi a₀) := by
  let b : ℝ := max a₀ 1
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have ha0_le_b : a₀ ≤ b := le_max_left _ _
  have h1 : IntegrableOn (fun u : ℝ ↦ (u + a) ^ r) (Set.Ioc a₀ b) := by
    have hcont : ContinuousOn (fun u : ℝ ↦ (u + a) ^ r) (Set.Icc a₀ b) := by
      refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
      have hpos : 0 < u + a := by linarith [hu.1]
      exact (continuousAt_id.add continuousAt_const).rpow_const (Or.inl hpos.ne')
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ ↦ (u + a) ^ r) (Set.Ioi b) := by
    have hdom : IntegrableOn (fun u : ℝ ↦ u ^ r) (Set.Ioi b) := integrableOn_Ioi_rpow_of_lt hr hb_pos
    refine Integrable.mono' hdom ?_ ?_
    · refine (continuousOn_of_forall_continuousAt fun u hu ↦ ?_).aestronglyMeasurable measurableSet_Ioi
      have hbu : b < u := hu
      have hpos : 0 < u + a := by linarith
      exact (continuousAt_id.add continuousAt_const).rpow_const (Or.inl hpos.ne')
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hbu : b < u := hu
      have hu_pos : 0 < u := lt_trans hb_pos hbu
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.rpow_le_rpow_of_nonpos hu_pos (by linarith) (by linarith : r ≤ 0)
  rw [← Set.Ioc_union_Ioi_eq_Ioi ha0_le_b]
  exact h1.union h2

private lemma integral_shift_rpow_Ioi {a₀ a : ℝ} (ha₀ : 0 ≤ a₀) (ha : 0 < a) {r : ℝ}
    (hr : 1 < r) :
    ∫ u in Set.Ioi a₀, (u + a) ^ (-r) = (a₀ + a) ^ (1 - r) / (r - 1) := by
  have hint := integrableOn_shift_rpow_Ioi ha₀ ha (by linarith : -r < -1)
  have htend : Tendsto (fun R : ℝ ↦ ∫ u in a₀..R, (u + a) ^ (-r)) atTop
      (𝓝 (∫ u in Set.Ioi a₀, (u + a) ^ (-r))) :=
    intervalIntegral_tendsto_integral_Ioi a₀ hint tendsto_id
  have hcalc : ∀ R : ℝ, a₀ ≤ R →
      ∫ u in a₀..R, (u + a) ^ (-r) =
        ((a₀ + a) ^ (1 - r) - (R + a) ^ (1 - r)) / (r - 1) := by
    intro R hR
    rw [intervalIntegral.integral_comp_add_right (fun v : ℝ ↦ v ^ (-r)) a]
    rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
      rw [Set.uIcc_of_le (by linarith : a₀ + a ≤ R + a)] at h
      linarith [h.1]⟩)]
    have hexp : -r + 1 = 1 - r := by ring
    rw [hexp]
    field_simp [show r - 1 ≠ 0 by linarith, show 1 - r ≠ 0 by linarith]
    ring
  have hlim : Tendsto (fun R : ℝ ↦ ((a₀ + a) ^ (1 - r) - (R + a) ^ (1 - r)) / (r - 1))
      atTop (𝓝 ((a₀ + a) ^ (1 - r) / (r - 1))) := by
    have hadd : Tendsto (fun R : ℝ ↦ R + a) atTop atTop :=
      tendsto_atTop_add_const_right atTop a tendsto_id
    have hr' : Tendsto (fun R : ℝ ↦ (R + a) ^ (1 - r)) atTop (𝓝 0) :=
      ((tendsto_rpow_neg_atTop (by linarith : 0 < r - 1)).comp hadd).congr fun R ↦ by
        dsimp; rw [show -(r - 1) = 1 - r by ring]
    simpa using (tendsto_const_nhds (x := (a₀ + a) ^ (1 - r)).sub hr').div_const (r - 1)
  exact tendsto_nhds_unique htend (hlim.congr' (by
    filter_upwards [eventually_ge_atTop a₀] with R hR; exact (hcalc R hR).symm))

private lemma integrableOn_sawtooth_shift_cpow_Ioi {a₀ a : ℝ} (ha₀ : 0 ≤ a₀) (ha : 0 < a)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) (Set.Ioi a₀) := by
  have hpow_int : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * (u + a) ^ (-s.re - 1)) (Set.Ioi a₀) :=
    (integrableOn_shift_rpow_Ioi ha₀ ha (by linarith)).const_mul (1 / 2)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hmeas_saw : Measurable fun u : ℝ ↦ (sawtooth u : ℂ) :=
      Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const _)
    have hcont_pow : ContinuousOn (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 1)) (Set.Ioi a₀) :=
      continuousOn_of_forall_continuousAt fun u hu ↦ by
        have hu_gt : a₀ < u := hu
        exact (cpow_shift_hasDerivAt (by linarith) (-s - 1)).continuousAt
    exact (hmeas_saw.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
      (hcont_pow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_gt : a₀ < u := hu
    have hu_pos : 0 < u + a := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)

/-- Absolute convergence of the second Euler–Maclaurin remainder for Hurwitz zeta. -/
lemma integrableOn_bernoulliKernel_two_shift_cpow_Ioi {a₀ a : ℝ} (ha₀ : 0 ≤ a₀) (ha : 0 < a)
    {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2))
      (Set.Ioi a₀) := by
  have hpow_int : IntegrableOn (fun u : ℝ ↦ (1 / 12 : ℝ) * (u + a) ^ (-s.re - 2)) (Set.Ioi a₀) :=
    (integrableOn_shift_rpow_Ioi ha₀ ha (by linarith)).const_mul (1 / 12)
  refine Integrable.mono' hpow_int ?_ ?_
  · have hcont_b2 : Continuous fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))
    have hcont_pow : ContinuousOn (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 2)) (Set.Ioi a₀) :=
      continuousOn_of_forall_continuousAt fun u hu ↦ by
        have hu_gt : a₀ < u := hu
        exact (cpow_shift_hasDerivAt (by linarith) (-s - 2)).continuousAt
    exact (hcont_b2.continuousOn.mul hcont_pow).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_gt : a₀ < u := hu
    have hu_pos : 0 < u + a := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, neg_re, re_ofNat]
    exact mul_le_mul (bernoulliKernel_two_abs_le u) le_rfl (by positivity) (by positivity)

private lemma shift_Ioi_integral_sawtooth {N : ℕ} {a : ℝ} (z : ℂ) :
    ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1) =
      ∫ v in Set.Ioi ((N : ℝ) + a), (sawtooth (v - a) : ℂ) * (v : ℂ) ^ (-z - 1) := by
  have hmp : MeasurePreserving (fun v : ℝ ↦ v - a) volume volume :=
    measurePreserving_sub_right volume a
  have hset : (fun v : ℝ ↦ v - a) ⁻¹' Set.Ioi (N : ℝ) = Set.Ioi ((N : ℝ) + a) := by
    ext v; simp only [Set.mem_preimage, Set.mem_Ioi]; constructor <;> intro h <;> linarith
  rw [← hset]
  simpa [sub_add_cancel] using (MeasurePreserving.setIntegral_preimage_emb hmp
    (measurableEmbedding_subRight a)
    (fun u : ℝ ↦ (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1))
    (Set.Ioi (N : ℝ))).symm

private lemma shift_Ioi_integral_bernoulliKernel_two {N : ℕ} {a : ℝ} (z : ℂ) :
    ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2) =
      ∫ v in Set.Ioi ((N : ℝ) + a), (bernoulliKernel 2 (v - a) : ℂ) * (v : ℂ) ^ (-z - 2) := by
  have hmp : MeasurePreserving (fun v : ℝ ↦ v - a) volume volume :=
    measurePreserving_sub_right volume a
  have hset : (fun v : ℝ ↦ v - a) ⁻¹' Set.Ioi (N : ℝ) = Set.Ioi ((N : ℝ) + a) := by
    ext v; simp only [Set.mem_preimage, Set.mem_Ioi]; constructor <;> intro h <;> linarith
  rw [← hset]
  simpa [sub_add_cancel] using (MeasurePreserving.setIntegral_preimage_emb hmp
    (measurableEmbedding_subRight a)
    (fun u : ℝ ↦ (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2))
    (Set.Ioi (N : ℝ))).symm

private lemma differentiableOn_integral_sawtooth_shift (N : ℕ) {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1))
      {s : ℂ | 0 < s.re} := by
  have hNa_pos : (0 : ℝ) < (N : ℝ) + a := by positivity
  let f : ℝ → ℂ := Set.indicator (Set.Ioi ((N : ℝ) + a)) (fun v : ℝ ↦ (sawtooth (v - a) : ℂ))
  have hf_loc : LocallyIntegrableOn f (Set.Ioi 0) := by
    have hm : Measurable f :=
      Measurable.indicator (Complex.continuous_ofReal.measurable.comp
        ((measurable_fract.sub_const _).comp (measurable_id.sub_const a))) measurableSet_Ioi
    have hloc : LocallyIntegrable f volume := by
      refine (locallyIntegrable_const (1 / 2 : ℝ)).mono hm.aestronglyMeasurable
        (Eventually.of_forall fun v ↦ ?_)
      rw [Real.norm_of_nonneg (by norm_num)]
      by_cases hv : (N : ℝ) + a < v
      · simpa [f, hv, Complex.norm_real, Real.norm_eq_abs] using sawtooth_abs_le (v - a)
      · simp [f, hv]
    exact hloc.locallyIntegrableOn _
  have hf_top : f =O[atTop] (fun u : ℝ ↦ u ^ (0 : ℝ)) := by
    refine IsBigO.of_bound (1 / 2) ?_
    filter_upwards [eventually_gt_atTop ((N : ℝ) + a)] with v hv
    simpa [f, hv, Complex.norm_real, Real.norm_eq_abs] using sawtooth_abs_le (v - a)
  intro s hs
  let b : ℝ := -(s.re + 1)
  have hf_bot : f =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-b)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT hNa_pos] with v hv
    have hvNa : ¬ (N : ℝ) + a < v := not_lt.mpr hv.2.le
    simp [f, hvNa]
  have hmel := mellin_differentiableOn_strip (a := 0) (b := b) hf_loc hf_top hf_bot
  have hstrip : -s ∈ {z : ℂ | b < z.re ∧ z.re < 0} := by
    have hs_gt : 0 < s.re := hs
    simp only [Set.mem_ofPred_eq, neg_re, b]
    exact ⟨by linarith, by linarith⟩
  have hdiff := (hmel (-s) hstrip).differentiableAt (by
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hstrip)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ ↦ mellin f (-z)) s :=
    DifferentiableAt.comp (g := mellin f) (f := fun z : ℂ ↦ -z) s hdiff (hasDerivAt_neg s).differentiableAt
  have heq :
      (fun z : ℂ ↦ ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1)) =
        fun z : ℂ ↦ mellin f (-z) := by
    ext z
    rw [shift_Ioi_integral_sawtooth z, mellin]
    have hcongr : Set.EqOn
        (fun v : ℝ ↦ (v : ℂ) ^ (-z - 1) • f v)
        (Set.indicator (Set.Ioi ((N : ℝ) + a))
          (fun v : ℝ ↦ (sawtooth (v - a) : ℂ) * (v : ℂ) ^ (-z - 1)))
        (Set.Ioi (0 : ℝ)) := by
      intro v _
      by_cases hv : (N : ℝ) + a < v
      · simp [f, Set.mem_Ioi, hv, smul_eq_mul, mul_comm]
      · simp [f, Set.mem_Ioi, hv]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hNa_pos.le)]
  rw [heq]
  exact hcomp.differentiableWithinAt

private lemma differentiableOn_integral_bernoulliKernel_two_shift (N : ℕ) {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦
        ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2))
      {s : ℂ | -1 < s.re} := by
  have hNa_pos : (0 : ℝ) < (N : ℝ) + a := by positivity
  let f : ℝ → ℂ := Set.indicator (Set.Ioi ((N : ℝ) + a)) (fun v : ℝ ↦ (bernoulliKernel 2 (v - a) : ℂ))
  have hf_loc : LocallyIntegrableOn f (Set.Ioi 0) := by
    have hcont : Continuous (fun v : ℝ ↦ (bernoulliKernel 2 (v - a) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_bernoulliKernel (by norm_num)).comp (continuous_sub_right a))
    have hloc : LocallyIntegrable f volume := by
      refine (locallyIntegrable_const (1 / 12 : ℝ)).mono
        (hcont.measurable.indicator measurableSet_Ioi).aestronglyMeasurable
        (Eventually.of_forall fun v ↦ ?_)
      rw [Real.norm_of_nonneg (by norm_num)]
      by_cases hv : (N : ℝ) + a < v
      · simpa [f, hv, Complex.norm_real, Real.norm_eq_abs] using bernoulliKernel_two_abs_le (v - a)
      · simp [f, hv]
    exact hloc.locallyIntegrableOn _
  have hf_top : f =O[atTop] (fun u : ℝ ↦ u ^ (0 : ℝ)) := by
    refine IsBigO.of_bound (1 / 12) ?_
    filter_upwards [eventually_gt_atTop ((N : ℝ) + a)] with v hv
    simpa [f, hv, Complex.norm_real, Real.norm_eq_abs] using bernoulliKernel_two_abs_le (v - a)
  intro s hs
  let b : ℝ := -(s.re + 2)
  have hf_bot : f =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-b)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT hNa_pos] with v hv
    have hvNa : ¬ (N : ℝ) + a < v := not_lt.mpr hv.2.le
    simp [f, hvNa]
  have hmel := mellin_differentiableOn_strip (a := 0) (b := b) hf_loc hf_top hf_bot
  have hstrip : -s - 1 ∈ {z : ℂ | b < z.re ∧ z.re < 0} := by
    have hs_gt : -1 < s.re := hs
    simp only [Set.mem_ofPred_eq, sub_re, neg_re, one_re, b]
    exact ⟨by linarith, by linarith⟩
  have hdiff := (hmel (-s - 1) hstrip).differentiableAt (by
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hstrip)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ ↦ mellin f (-z - 1)) s :=
    DifferentiableAt.comp (g := mellin f) (f := fun z : ℂ ↦ -z - 1) s hdiff
      ((hasDerivAt_neg s).differentiableAt.sub_const 1)
  have heq :
      (fun z : ℂ ↦
        ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2)) =
        fun z : ℂ ↦ mellin f (-z - 1) := by
    ext z
    rw [shift_Ioi_integral_bernoulliKernel_two z, mellin]
    have hcongr : Set.EqOn
        (fun v : ℝ ↦ (v : ℂ) ^ ((-z - 1) - 1) • f v)
        (Set.indicator (Set.Ioi ((N : ℝ) + a))
          (fun v : ℝ ↦ (bernoulliKernel 2 (v - a) : ℂ) * (v : ℂ) ^ (-z - 2)))
        (Set.Ioi (0 : ℝ)) := by
      intro v _
      have hexp : (-z - 1) - 1 = -z - 2 := by ring
      by_cases hv : (N : ℝ) + a < v
      · simp [f, Set.mem_Ioi, hv, smul_eq_mul, mul_comm, hexp]
      · simp [f, Set.mem_Ioi, hv]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hNa_pos.le)]
  rw [heq]
  exact hcomp.differentiableWithinAt

end Helpers

section HurwitzEulerMaclaurin

/-- **First-order Euler–Maclaurin continuation** of `HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s`
to `0 < s.re` (`s ≠ 1`) for `a ∈ (0, 1]`. -/
theorem hurwitzZeta_eq_eulerMaclaurin_of_re_pos {a : ℝ} (ha : a ∈ Set.Ioc (0 : ℝ) 1) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s =
      (a : ℂ) ^ (1 - s) / (s - 1) + (1 / 2 : ℂ) * (a : ℂ) ^ (-s) -
        s * ∫ u in Set.Ioi (0 : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  let L : ℂ → ℂ := HurwitzZeta.hurwitzZeta (a : UnitAddCircle)
  let R : ℂ → ℂ := fun z ↦ (a : ℂ) ^ (1 - z) / (z - 1) + (1 / 2 : ℂ) * (a : ℂ) ^ (-z) -
    z * ∫ u in Set.Ioi (0 : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1)
  have ha_pos : 0 < a := ha.1
  have ha_ne : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha_pos.ne'
  have hL_diff : DifferentiableOn ℂ L U := fun z hz ↦
    (HurwitzZeta.differentiableAt_hurwitzZeta (a : UnitAddCircle) hz.2).differentiableWithinAt
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (0 : ℝ) < z.re}).inter
      (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})
  have hL_an : AnalyticOnNhd ℂ L U := hL_diff.analyticOnNhd hU_open
  have hR_diff : DifferentiableOn ℂ R U := by
    intro z hz
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz.2
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ (a : ℂ) ^ (1 - w) / (w - 1)) z := by
      fun_prop (disch := first | exact hne | exact Or.inl ha_ne)
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 2 : ℂ) * (a : ℂ) ^ (-w)) z :=
      (differentiableAt_id.neg.const_cpow (Or.inl ha_ne)).const_mul _
    have hint : DifferentiableAt ℂ
        (fun w : ℂ ↦ ∫ u in Set.Ioi (0 : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-w - 1)) z :=
      (differentiableOn_integral_sawtooth_shift 0 ha_pos z hz.1).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1)
    have h3 : DifferentiableAt ℂ
        (fun w : ℂ ↦ w * ∫ u in Set.Ioi (0 : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-w - 1))
        z := differentiableAt_id.mul hint
    exact ((h1.add h2).sub h3).differentiableWithinAt
  have hR_an : AnalyticOnNhd ℂ R U := hR_diff.analyticOnNhd hU_open
  have h_gt_one : ∀ {z : ℂ}, 1 < z.re → L z = R z := by
    intro z hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hz0 : 0 < z.re := lt_trans zero_lt_one hz
    have hem (M : ℕ) :
        ∑ n ∈ Finset.Icc 0 M, ((n : ℂ) + a) ^ (-z) =
          (((M : ℝ) + a : ℝ) : ℂ) ^ (1 - z) / (1 - z) - (a : ℂ) ^ (1 - z) / (1 - z) +
            ((a : ℂ) ^ (-z) + (((M : ℝ) + a : ℝ) : ℂ) ^ (-z)) / 2 -
            z * ∫ t in (0 : ℝ)..M, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1) := by
      have hf : ∀ t ∈ Set.Icc ((0 : ℕ) : ℝ) M,
          HasDerivAt (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-z))
            (-z * ((t + a : ℝ) : ℂ) ^ (-z - 1)) t := by
        intro t ht
        simp only [Nat.cast_zero] at ht
        exact cpow_shift_hasDerivAt (by linarith [ht.1]) (-z)
      have hf' : ContinuousOn (fun u : ℝ ↦ -z * ((u + a : ℝ) : ℂ) ^ (-z - 1))
          (Set.Icc ((0 : ℕ) : ℝ) M) := by
        simp only [Nat.cast_zero]
        exact continuousOn_const.mul (cpow_shift_continuousOn (by linarith) (-z - 1))
      have h_em := euler_maclaurin_Icc_complex (Nat.zero_le M) hf hf'
      simp only [Nat.cast_zero, zero_add] at h_em
      rw [integral_cpow_shift_ofReal_eq (by linarith) (Nat.cast_nonneg M) hz1] at h_em
      simp only [zero_add] at h_em
      have hpull : ∫ t in (0 : ℝ)..M, (sawtooth t : ℂ) * (-z * ((t + a : ℝ) : ℂ) ^ (-z - 1)) =
          -z * ∫ t in (0 : ℝ)..M, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1) := by
        have hcongr : (fun t : ℝ ↦ (sawtooth t : ℂ) * (-z * ((t + a : ℝ) : ℂ) ^ (-z - 1))) =
            fun t : ℝ ↦ (-z) * ((sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1)) := by
          ext t; ring
        rw [hcongr, intervalIntegral.integral_const_mul]
      rw [hpull] at h_em
      have hcast_sum : ∑ n ∈ Finset.Icc 0 M, (((n : ℝ) + a : ℝ) : ℂ) ^ (-z) =
          ∑ n ∈ Finset.Icc 0 M, ((n : ℂ) + a) ^ (-z) :=
        Finset.sum_congr rfl fun n _ ↦ by push_cast; rfl
      rw [hcast_sum] at h_em
      linear_combination h_em
    have hsum_lim : Tendsto (fun M : ℕ ↦ ∑ n ∈ Finset.Icc 0 M, ((n : ℂ) + a) ^ (-z))
        atTop (𝓝 (HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z)) := by
      have hhas := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨ha.1.le, ha.2⟩ hz
      refine (hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun M ↦ ?_
      have hrg : Finset.Icc 0 M = Finset.range (M + 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
      rw [Function.comp_apply, hrg]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [one_div, cpow_neg]
    have hpow1 : Tendsto (fun M : ℕ ↦ (((M : ℝ) + a : ℝ) : ℂ) ^ (1 - z)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hadd : Tendsto (fun M : ℕ ↦ (M : ℝ) + a) atTop atTop :=
        tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
      have hreal : Tendsto (fun M : ℕ ↦ ((M : ℝ) + a) ^ (1 - z.re)) atTop (𝓝 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < z.re - 1)).comp hadd).congr fun M ↦ by
          dsimp; rw [show -(z.re - 1) = 1 - z.re by ring]
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with M _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), sub_re, one_re]
    have hpow2 : Tendsto (fun M : ℕ ↦ (((M : ℝ) + a : ℝ) : ℂ) ^ (-z)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hadd : Tendsto (fun M : ℕ ↦ (M : ℝ) + a) atTop atTop :=
        tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
      have hreal : Tendsto (fun M : ℕ ↦ ((M : ℝ) + a) ^ (-z.re)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hz0).comp hadd
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with M _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
    have hint_lim : Tendsto
        (fun M : ℕ ↦ ∫ t in (0 : ℝ)..M, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1))
        atTop (𝓝 (∫ u in Set.Ioi (0 : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1))) :=
      (intervalIntegral_tendsto_integral_Ioi 0
        (integrableOn_sawtooth_shift_cpow_Ioi le_rfl ha_pos hz0) tendsto_id).comp
        tendsto_natCast_atTop_atTop
    have hrhs_lim : Tendsto (fun M : ℕ ↦
        (((M : ℝ) + a : ℝ) : ℂ) ^ (1 - z) / (1 - z) - (a : ℂ) ^ (1 - z) / (1 - z) +
          ((a : ℂ) ^ (-z) + (((M : ℝ) + a : ℝ) : ℂ) ^ (-z)) / 2 -
          z * ∫ t in (0 : ℝ)..M, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1))
        atTop (𝓝 (R z)) := by
      have hlim1 : Tendsto (fun M : ℕ ↦
          (((M : ℝ) + a : ℝ) : ℂ) ^ (1 - z) / (1 - z) - (a : ℂ) ^ (1 - z) / (1 - z) +
            ((a : ℂ) ^ (-z) + (((M : ℝ) + a : ℝ) : ℂ) ^ (-z)) / 2)
          atTop (𝓝 (0 / (1 - z) - (a : ℂ) ^ (1 - z) / (1 - z) + ((a : ℂ) ^ (-z) + 0) / 2)) :=
        ((hpow1.div_const (1 - z)).sub_const _).add ((tendsto_const_nhds.add hpow2).div_const 2)
      have hlim2 := hlim1.sub (hint_lim.const_mul z)
      refine hlim2.trans_eq (congrArg 𝓝 ?_)
      dsimp only [R]
      have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
      have hne' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      field_simp [hne, hne']
      ring
    exact tendsto_nhds_unique hsum_lim (hrhs_lim.congr fun M ↦ (hem M).symm)
  have h2mem : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : L =ᶠ[𝓝 (2 : ℂ)] R := by
    have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with z hz
    exact h_gt_one hz
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an
    (isPathConnected_re_gt_sdiff_one' (by norm_num : (0 : ℝ) < 1)).isConnected.isPreconnected
    h2mem hev ⟨hs, hs1⟩

/-- **Truncated Euler–Maclaurin continuation** of `HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s`
to `0 < s.re` (`s ≠ 1`) at any cutoff `N : ℕ` for `a ∈ (0, 1]`. -/
theorem hurwitzZeta_eq_eulerMaclaurin_Icc_of_re_pos {a : ℝ} (ha : a ∈ Set.Ioc (0 : ℝ) 1) (N : ℕ)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s =
      ∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) -
        ((N : ℂ) + a) ^ (1 - s) / (1 - s) - (1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
        s * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1) := by
  have ha_pos : 0 < a := ha.1
  have h0 := hurwitzZeta_eq_eulerMaclaurin_of_re_pos ha hs hs1
  have hint_full := integrableOn_sawtooth_shift_cpow_Ioi le_rfl ha_pos hs
  have hIoi_split : ∫ u in Set.Ioi (0 : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1) =
      (∫ u in (0 : ℝ)..N, (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) +
        ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1) := by
    have hle : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hint_tail := hint_full.mono_set (Set.Ioi_subset_Ioi hle)
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Set.Ioc_disjoint_Ioi_same
        measurableSet_Ioi (hint_full.mono_set Set.Ioc_subset_Ioi_self) hint_tail,
      intervalIntegral.integral_of_le hle]
  have hf : ∀ t ∈ Set.Icc ((0 : ℕ) : ℝ) N,
      HasDerivAt (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s))
        (-s * ((t + a : ℝ) : ℂ) ^ (-s - 1)) t := by
    intro t ht
    simp only [Nat.cast_zero] at ht
    exact cpow_shift_hasDerivAt (by linarith [ht.1]) (-s)
  have hf' : ContinuousOn (fun u : ℝ ↦ -s * ((u + a : ℝ) : ℂ) ^ (-s - 1))
      (Set.Icc ((0 : ℕ) : ℝ) N) := by
    simp only [Nat.cast_zero]
    exact continuousOn_const.mul (cpow_shift_continuousOn (by linarith [ha_pos] : 0 < (0 : ℝ) + a) (-s - 1))
  have h_em := euler_maclaurin_Ioc_complex' (Nat.zero_le N) hf hf'
  simp only [Nat.cast_zero, zero_add] at h_em
  rw [integral_cpow_shift_ofReal_eq (by linarith [ha_pos] : 0 < (0 : ℝ) + a)
    (Nat.cast_nonneg N) hs1] at h_em
  simp only [zero_add] at h_em
  have hpull : ∫ t in (0 : ℝ)..N, (sawtooth t : ℂ) * (-s * ((t + a : ℝ) : ℂ) ^ (-s - 1)) =
      -s * ∫ t in (0 : ℝ)..N, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-s - 1) := by
    have hcongr : (fun t : ℝ ↦ (sawtooth t : ℂ) * (-s * ((t + a : ℝ) : ℂ) ^ (-s - 1))) =
        fun t : ℝ ↦ (-s) * ((sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-s - 1)) := by
      ext t; ring
    rw [hcongr, intervalIntegral.integral_const_mul]
  rw [hpull] at h_em
  have hIcc : ∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) =
      (a : ℂ) ^ (-s) + ∑ n ∈ Finset.Ioc 0 N, ((n : ℂ) + a) ^ (-s) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
    simp
  rw [h0, hIoi_split, hIcc]
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hne' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hrecip : (a : ℂ) ^ (1 - s) / (s - 1) = -((a : ℂ) ^ (1 - s) / (1 - s)) := by
    field_simp [hne, hne']
    ring
  rw [hrecip]
  have hcast : ((N + a : ℝ) : ℂ) = (N : ℂ) + (a : ℂ) := by push_cast; rfl
  have hsum_cast : (∑ n ∈ Finset.Ioc 0 N, (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.Ioc 0 N, ((n : ℂ) + a) ^ (-s) := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    push_cast; rfl
  rw [hcast, hsum_cast] at h_em
  linear_combination -h_em

/-- **Second-order Euler–Maclaurin continuation** of `HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s`
to `-1 < s.re` (`s ≠ 1`) at any cutoff `N : ℕ` for `a ∈ (0, 1]`. -/
theorem hurwitzZeta_eq_eulerMaclaurin_second_order_of_re_gt_neg_one
    {a : ℝ} (ha : a ∈ Set.Ioc (0 : ℝ) 1) (N : ℕ) {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s =
      ∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) -
        ((N : ℂ) + a) ^ (1 - s) / (1 - s) - (1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) +
        (1 / 12 : ℂ) * s * ((N : ℂ) + a) ^ (-s - 1) -
        s * (s + 1) * ∫ u in Set.Ioi (N : ℝ),
          (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2) := by
  let U : Set ℂ := {z : ℂ | -1 < z.re ∧ z ≠ 1}
  let L : ℂ → ℂ := HurwitzZeta.hurwitzZeta (a : UnitAddCircle)
  let R : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-z) -
    ((N : ℂ) + a) ^ (1 - z) / (1 - z) - (1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-z) +
    (1 / 12 : ℂ) * z * ((N : ℂ) + a) ^ (-z - 1) -
    z * (z + 1) * ∫ u in Set.Ioi (N : ℝ),
      (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2)
  have ha_pos : 0 < a := ha.1
  have hNa_pos : (0 : ℝ) < (N : ℝ) + a := by positivity
  have hNa_ne : ((N : ℂ) + a) ≠ 0 := by
    have : ((N : ℂ) + a) = (((N : ℝ) + a : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.ofReal_ne_zero.mpr hNa_pos.ne'
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (-1 : ℝ) < z.re}).inter
      (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})
  have hL_diff : DifferentiableOn ℂ L U := fun z hz ↦
    (HurwitzZeta.differentiableAt_hurwitzZeta (a : UnitAddCircle) hz.2).differentiableWithinAt
  have hL_an : AnalyticOnNhd ℂ L U := hL_diff.analyticOnNhd hU_open
  have hR_diff : DifferentiableOn ℂ R U := by
    intro z hz
    have hsum : DifferentiableAt ℂ
        (fun w : ℂ ↦ ∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-w)) z := by
      refine DifferentiableAt.fun_sum fun n _ ↦ ?_
      have hn_pos : (0 : ℝ) < (n : ℝ) + a := by positivity
      have hne : ((n : ℂ) + a) ≠ 0 := by
        rw [show ((n : ℂ) + a) = (((n : ℝ) + a : ℝ) : ℂ) by push_cast; rfl]
        exact Complex.ofReal_ne_zero.mpr hn_pos.ne'
      exact differentiableAt_id.neg.const_cpow (Or.inl hne)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ ((N : ℂ) + a) ^ (1 - w) / (1 - w)) z := by
      have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.2.symm
      fun_prop (disch := first | exact hne | exact Or.inl hNa_ne)
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-w)) z :=
      (differentiableAt_id.neg.const_cpow (Or.inl hNa_ne)).const_mul _
    have h3 : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 12 : ℂ) * w * ((N : ℂ) + a) ^ (-w - 1)) z :=
      (differentiableAt_id.const_mul _).mul
        ((differentiableAt_id.neg.sub_const 1).const_cpow (Or.inl hNa_ne))
    have hint : DifferentiableAt ℂ
        (fun w : ℂ ↦ ∫ u in Set.Ioi (N : ℝ),
          (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-w - 2)) z :=
      (differentiableOn_integral_bernoulliKernel_two_shift N ha_pos z hz.1).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1)
    have h4 : DifferentiableAt ℂ
        (fun w : ℂ ↦ w * (w + 1) * ∫ u in Set.Ioi (N : ℝ),
          (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-w - 2)) z :=
      (differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul hint
    exact ((((hsum.sub h1).sub h2).add h3).sub h4).differentiableWithinAt
  have hR_an : AnalyticOnNhd ℂ R U := hR_diff.analyticOnNhd hU_open
  have h_pos : ∀ {z : ℂ}, 0 < z.re → z ≠ 1 → L z = R z := by
    intro z hz hz1
    have h1 := hurwitzZeta_eq_eulerMaclaurin_Icc_of_re_pos ha N hz hz1
    have hibp (M : ℕ) (hNM : N ≤ M) :
        ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1) =
          ((1 / 12 : ℂ) * (((M : ℝ) + a : ℝ) : ℂ) ^ (-z - 1) -
            (1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1)) +
            (z + 1) * ∫ t in (N : ℝ)..M,
              (bernoulliKernel 2 t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 2) := by
      have hg : ∀ t ∈ Set.Icc (N : ℝ) M,
          HasDerivAt (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-z - 1))
            ((-z - 1) * ((t + a : ℝ) : ℂ) ^ (-z - 2)) t := by
        intro t ht
        have hd := cpow_shift_hasDerivAt (t := t) (a := a)
          (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) N, ha_pos]) (-z - 1)
        rw [show (-z - 1) - 1 = -z - 2 by ring] at hd
        exact hd
      have hg' : ContinuousOn (fun u : ℝ ↦ (-z - 1) * ((u + a : ℝ) : ℂ) ^ (-z - 2))
          (Set.Icc (N : ℝ) M) :=
        continuousOn_const.mul (cpow_shift_continuousOn hNa_pos (-z - 2))
      have hres := integral_bernoulliKernel_one_mul_eq_sub_complex'' hNM hg hg'
      have hpull : ∫ t in (N : ℝ)..M,
          (bernoulliKernel 2 t : ℂ) * ((-z - 1) * ((t + a : ℝ) : ℂ) ^ (-z - 2)) =
          (-z - 1) * ∫ t in (N : ℝ)..M,
            (bernoulliKernel 2 t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 2) := by
        have hcongr :
            (fun t : ℝ ↦ (bernoulliKernel 2 t : ℂ) * ((-z - 1) * ((t + a : ℝ) : ℂ) ^ (-z - 2))) =
              fun t : ℝ ↦ (-z - 1) * ((bernoulliKernel 2 t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 2)) := by
          ext t; ring
        rw [hcongr, intervalIntegral.integral_const_mul]
      rw [hpull] at hres
      linear_combination hres
    have hint1 :
        Tendsto (fun M : ℕ ↦ ∫ t in (N : ℝ)..M, (sawtooth t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 1))
          atTop (𝓝 (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1))) :=
      (intervalIntegral_tendsto_integral_Ioi N
        (integrableOn_sawtooth_shift_cpow_Ioi (Nat.cast_nonneg N) ha_pos hz) tendsto_id).comp
        tendsto_natCast_atTop_atTop
    have hint2 : Tendsto (fun M : ℕ ↦
        ∫ t in (N : ℝ)..M, (bernoulliKernel 2 t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 2))
        atTop (𝓝 (∫ u in Set.Ioi (N : ℝ),
          (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2))) :=
      (intervalIntegral_tendsto_integral_Ioi N
        (integrableOn_bernoulliKernel_two_shift_cpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith))
        tendsto_id).comp tendsto_natCast_atTop_atTop
    have hpowM : Tendsto (fun M : ℕ ↦ (((M : ℝ) + a : ℝ) : ℂ) ^ (-z - 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hadd : Tendsto (fun M : ℕ ↦ (M : ℝ) + a) atTop atTop :=
        tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
      have hreal : Tendsto (fun M : ℕ ↦ ((M : ℝ) + a) ^ (-z.re - 1)) atTop (𝓝 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < z.re + 1)).comp hadd).congr fun M ↦ by
          dsimp; rw [show -(z.re + 1) = -z.re - 1 by ring]
      refine hreal.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with M _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), sub_re, neg_re, one_re]
    have hlim_rhs : Tendsto (fun M : ℕ ↦
        ((1 / 12 : ℂ) * (((M : ℝ) + a : ℝ) : ℂ) ^ (-z - 1) -
          (1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1)) +
          (z + 1) * ∫ t in (N : ℝ)..M,
            (bernoulliKernel 2 t : ℂ) * ((t + a : ℝ) : ℂ) ^ (-z - 2))
        atTop (𝓝 (-(1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1) +
          (z + 1) * ∫ u in Set.Ioi (N : ℝ),
            (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2))) := by
      have hsub : Tendsto (fun M : ℕ ↦
          (1 / 12 : ℂ) * (((M : ℝ) + a : ℝ) : ℂ) ^ (-z - 1) -
            (1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1))
          atTop (𝓝 (0 - (1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1))) := by
        simpa using (hpowM.const_mul (1 / 12 : ℂ)).sub_const
          ((1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1))
      have hres := hsub.add (hint2.const_mul (z + 1))
      refine hres.trans_eq (congrArg 𝓝 ?_)
      ring
    have heq_tail :
        ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 1) =
          -(1 / 12 : ℂ) * (((N : ℝ) + a : ℝ) : ℂ) ^ (-z - 1) +
            (z + 1) * ∫ u in Set.Ioi (N : ℝ),
              (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-z - 2) :=
      tendsto_nhds_unique hint1 (hlim_rhs.congr' (by
        filter_upwards [eventually_ge_atTop N] with M hNM; exact (hibp M hNM).symm))
    dsimp only [L, R]
    rw [h1, heq_tail]
    have hcast : ((N + a : ℝ) : ℂ) = (N : ℂ) + (a : ℂ) := by push_cast; rfl
    rw [hcast]
    ring
  have h2mem : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : L =ᶠ[𝓝 (2 : ℂ)] R := by
    have hopen : {z : ℂ | 0 < z.re ∧ z ≠ 1} ∈ 𝓝 (2 : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re : IsOpen {z : ℂ | (0 : ℝ) < z.re}).inter
        (isOpen_ne : IsOpen {z : ℂ | z ≠ 1})).mem_nhds ⟨by norm_num, by norm_num⟩
    filter_upwards [hopen] with z hz
    exact h_pos hz.1 hz.2
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an
    (isPathConnected_re_gt_sdiff_one' (by norm_num : (-1 : ℝ) < 1)).isConnected.isPreconnected
    h2mem hev ⟨hs, hs1⟩

end HurwitzEulerMaclaurin

section ApproximateDirichletPolynomial

private lemma bernoulli_two_eval_real (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x = x ^ 2 - x + 1 / 6 := by
  have hpoly : Polynomial.bernoulli 2 =
      Polynomial.C (1 / 6 : ℚ) - Polynomial.X + Polynomial.X ^ 2 := by
    simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [_root_.bernoulli_one, bernoulli_eq_bernoulli'_of_ne_one zero_ne_one, bernoulli'_zero,
      bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two]
    ext k
    rcases k with _ | _ | _ | k <;>
      simp [Polynomial.coeff_monomial, Polynomial.coeff_X, Polynomial.coeff_C, Nat.choose]
  rw [hpoly]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, eq_ratCast]
  norm_num
  ring

private lemma bernoulliKernel_two_hasSum_cos (u : ℝ) :
    HasSum (fun m : ℕ ↦ (1 / (2 * Real.pi ^ 2)) *
        ((1 / ((m : ℝ) + 1) ^ 2) * Real.cos (2 * Real.pi * ((m : ℝ) + 1) * u)))
      (bernoulliKernel 2 u) := by
  have hfx : Int.fract u ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hraw := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hfx
  simp only [mul_one, Nat.factorial_two, Nat.cast_ofNat] at hraw
  rw [bernoulli_two_eval_real] at hraw
  have hsum_val :
      (-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ 2 / 2 / 2 * (Int.fract u ^ 2 - Int.fract u + 1 / 6) =
        (2 * Real.pi ^ 2) * bernoulliKernel 2 u := by
    rw [bernoulliKernel_two]
    norm_num
    ring
  rw [hsum_val] at hraw
  have hshift := (hasSum_nat_add_iff' 1).mpr hraw
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, zero_mul, sub_zero] at hshift
  have hscaled := hshift.mul_left (1 / (2 * Real.pi ^ 2))
  have h2pi_ne : 2 * Real.pi ^ 2 ≠ 0 := by positivity
  rw [← mul_assoc, one_div_mul_cancel h2pi_ne, one_mul] at hscaled
  refine hscaled.congr_fun fun m ↦ ?_
  have hcos : Real.cos (2 * Real.pi * ((m : ℝ) + 1) * Int.fract u) =
      Real.cos (2 * Real.pi * ((m : ℝ) + 1) * u) := by
    rw [Int.fract]
    have harg : 2 * Real.pi * ((m : ℝ) + 1) * u =
        2 * Real.pi * ((m : ℝ) + 1) * (u - ⌊u⌋) +
          ((⌊u⌋ * ((m : ℤ) + 1) : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  rw [Nat.cast_add, Nat.cast_one, hcos]

/-- Absolutely convergent positive and negative Fourier expansion of the second Bernoulli kernel. -/
theorem hasSum_bernoulliKernel_two_exp (u : ℝ) : HasSum (fun m : ℕ ↦
      ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
        (Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
          Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)))
      (bernoulliKernel 2 u : ℂ) := by
  have hhas := (Complex.ofRealCLM.hasSum (bernoulliKernel_two_hasSum_cos u))
  refine hhas.congr_fun fun m ↦ ?_
  simp only [Complex.ofRealCLM_apply]
  have hcos_c : ((Real.cos (2 * Real.pi * ((m : ℝ) + 1) * u) : ℝ) : ℂ) =
      (Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
        Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
  have h12 : ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi ^ 2) : ℝ) : ℂ) * ((1 / ((m : ℝ) + 1) ^ 2 : ℝ) : ℂ) / 2 := by
    push_cast; field_simp; ring
  conv_rhs => rw [Complex.ofReal_mul, Complex.ofReal_mul, hcos_c]
  rw [h12]
  ring

theorem bernoulliKernel_two_eq_tsum_exp (u : ℝ) :
    (bernoulliKernel 2 u : ℂ) =
      ∑' m : ℕ, ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
        (Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
          Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)) := by
  exact (hasSum_bernoulliKernel_two_exp u).tsum_eq.symm

private lemma oscillatory_integral_bound {N : ℕ} {a σ t ω : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (hω_gt : 0 < |ω| - |t| / ((N : ℝ) + a)) :
    ‖∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
        Complex.exp ((ω * u : ℝ) * I)‖ ≤
      ((N : ℝ) + a) ^ (-σ - 2) / (|ω| - |t| / ((N : ℝ) + a)) +
        ((N : ℝ) + a) ^ (-σ - 2) / (|ω| - |t| / ((N : ℝ) + a)) +
        |t| * ((N : ℝ) + a) ^ (-σ - 3) / (3 * (|ω| - |t| / ((N : ℝ) + a)) ^ 2) := by
  let M : ℝ := (N : ℝ) + a
  have hM_pos : 0 < M := by positivity
  let δ : ℝ := |ω| - |t| / M
  have hδ_pos : 0 < δ := hω_gt
  let psi : ℝ → ℝ := fun u ↦ ω - t / (u + a)
  have hpsi_lb : ∀ u : ℝ, (N : ℝ) ≤ u → δ ≤ |psi u| := by
    intro u hu
    have hua : M ≤ u + a := by dsimp [M]; linarith
    have ht_le : |t / (u + a)| ≤ |t| / M := by
      have hua_pos : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
      rw [abs_div, abs_of_pos hua_pos]
      exact div_le_div_of_nonneg_left (abs_nonneg t) hM_pos hua
    calc
      δ = |ω| - |t| / M := rfl
      _ ≤ |ω| - |t / (u + a)| := sub_le_sub_left ht_le |ω|
      _ ≤ |ω - t / (u + a)| := abs_sub_abs_le_abs_sub ω (t / (u + a))
  have hpsi_ne : ∀ u : ℝ, (N : ℝ) ≤ u → psi u ≠ 0 := fun u hu h0 ↦ by
    have h := hpsi_lb u hu
    rw [h0, abs_zero] at h
    linarith
  have hpsi_deriv : ∀ u : ℝ, (N : ℝ) ≤ u →
      HasDerivAt psi (t / (u + a) ^ 2) u := by
    intro u hu
    have hua : u + a ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
    have h1 : HasDerivAt (fun x : ℝ ↦ t / (x + a)) (-t / (u + a) ^ 2) u := by
      have hden : HasDerivAt (fun x : ℝ ↦ x + a) 1 u := by
        simpa using (hasDerivAt_id u).add_const a
      have hd := (hasDerivAt_const u t).div hden hua
      change HasDerivAt (fun x : ℝ ↦ t / (x + a)) _ u at hd
      simpa using hd
    have hsub := (hasDerivAt_const u ω).sub h1
    rw [zero_sub, neg_div, neg_neg] at hsub
    exact hsub
  let F_r : ℝ → ℝ := fun u ↦ (u + a) ^ (-σ - 2) / psi u
  let F'_r : ℝ → ℝ := fun u ↦
    ((-σ - 2) * (u + a) ^ (-σ - 3) * psi u - (u + a) ^ (-σ - 2) * (t / (u + a) ^ 2)) / (psi u) ^ 2
  have hF_deriv : ∀ u : ℝ, (N : ℝ) ≤ u → HasDerivAt F_r (F'_r u) u := by
    intro u hu
    have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
    have hnum : HasDerivAt (fun x : ℝ ↦ (x + a) ^ (-σ - 2))
        ((-σ - 2) * (u + a) ^ (-σ - 3)) u := by
      have hadd : HasDerivAt (fun x : ℝ ↦ x + a) 1 u := (hasDerivAt_id u).add_const a
      have hd : HasDerivAt (fun x : ℝ ↦ (x + a) ^ (-σ - 2))
          (1 * (-σ - 2) * (u + a) ^ ((-σ - 2) - 1)) u := hadd.rpow_const (Or.inl hua.ne')
      rw [one_mul, show (-σ - 2) - 1 = -σ - 3 by ring] at hd
      exact hd
    exact hnum.div (hpsi_deriv u hu) (hpsi_ne u hu)
  let θ : ℝ → ℝ := fun u ↦ ω * u - t * Real.log (u + a)
  let E : ℝ → ℂ := fun u ↦ Complex.exp ((θ u : ℝ) * I)
  have hE_deriv : ∀ u : ℝ, (N : ℝ) ≤ u → HasDerivAt E ((I * (psi u : ℂ)) * E u) u := by
    intro u hu
    have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
    have hθ : HasDerivAt θ (psi u) u := by
      have hd1 : HasDerivAt (fun x : ℝ ↦ ω * x) ω u := by
        simpa using (hasDerivAt_id u).const_mul ω
      have hd2 : HasDerivAt (fun x : ℝ ↦ t * Real.log (x + a)) (t * (u + a)⁻¹) u := by
        simpa [one_div] using (((hasDerivAt_id u).add_const a).log hua.ne').const_mul t
      convert hd1.sub hd2 using 1
      simp [psi, div_eq_mul_inv]
    have hθc : HasDerivAt (fun x : ℝ ↦ ((θ x : ℝ) : ℂ) * I) ((psi u : ℂ) * I) u :=
      hθ.ofReal_comp.mul_const I
    convert hθc.cexp using 1
    ring
  have hibp (K : ℕ) (hNK : N ≤ K) :
      ∫ u in (N : ℝ)..K, ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
          Complex.exp ((ω * u : ℝ) * I) =
        (-I) * (((F_r K : ℂ) * E K - (F_r N : ℂ) * E N) -
          ∫ u in (N : ℝ)..K, (F'_r u : ℂ) * E u) := by
    have hle : (N : ℝ) ≤ K := Nat.cast_le.mpr hNK
    have hF_c : ∀ u ∈ Set.uIcc (N : ℝ) K,
        HasDerivAt (fun x : ℝ ↦ (F_r x : ℂ)) (F'_r u : ℂ) u := by
      intro u hu
      rw [Set.uIcc_of_le hle] at hu
      exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hF_deriv u hu.1)
    have hE_c : ∀ u ∈ Set.uIcc (N : ℝ) K, HasDerivAt E ((I * (psi u : ℂ)) * E u) u := by
      intro u hu
      rw [Set.uIcc_of_le hle] at hu
      exact hE_deriv u hu.1
    have hF'_cont : ContinuousOn (fun u : ℝ ↦ (F'_r u : ℂ)) (Set.Icc (N : ℝ) K) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
      have hua : 0 < u + a := by linarith [hu.1, Nat.cast_nonneg (α := ℝ) N, ha]
      have hpsi_c : ContinuousAt psi u :=
        continuousAt_const.sub (continuousAt_const.div (continuousAt_id.add continuousAt_const) hua.ne')
      have hpow1 : ContinuousAt (fun x : ℝ ↦ (x + a) ^ (-σ - 3)) u :=
        (continuousAt_id.add continuousAt_const).rpow_const (Or.inl hua.ne')
      have hpow2 : ContinuousAt (fun x : ℝ ↦ (x + a) ^ (-σ - 2)) u :=
        (continuousAt_id.add continuousAt_const).rpow_const (Or.inl hua.ne')
      refine (((continuousAt_const.mul hpow1).mul hpsi_c).sub
        (hpow2.mul (continuousAt_const.div ((continuousAt_id.add continuousAt_const).pow 2)
          (pow_ne_zero 2 hua.ne')))).div (hpsi_c.pow 2) (pow_ne_zero 2 (hpsi_ne u hu.1))
    have hE'_cont : ContinuousOn (fun u : ℝ ↦ (I * (psi u : ℂ)) * E u) (Set.Icc (N : ℝ) K) := by
      refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
      have hua : 0 < u + a := by linarith [hu.1, Nat.cast_nonneg (α := ℝ) N, ha]
      have hpsi_c : ContinuousAt psi u :=
        continuousAt_const.sub (continuousAt_const.div (continuousAt_id.add continuousAt_const) hua.ne')
      have hθ_c : ContinuousAt θ u :=
        (continuousAt_const.mul continuousAt_id).sub
          (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log hua.ne'))
      exact (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hpsi_c)).mul
        (Complex.continuous_exp.continuousAt.comp
          ((Complex.continuous_ofReal.continuousAt.comp hθ_c).mul continuousAt_const))
    have hmul := intervalIntegral.integral_mul_deriv_eq_deriv_mul hF_c hE_c
      (hF'_cont.intervalIntegrable_of_Icc hle) (hE'_cont.intervalIntegrable_of_Icc hle)
    have hid : ∀ u ∈ Set.Icc (N : ℝ) K,
        (F_r u : ℂ) * ((I * (psi u : ℂ)) * E u) =
          I * (((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
            Complex.exp ((ω * u : ℝ) * I)) := by
      intro u hu
      have hua : 0 < u + a := by linarith [hu.1, Nat.cast_nonneg (α := ℝ) N, ha]
      have hpsi_nz : (psi u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpsi_ne u hu.1)
      have hcpow : ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) =
          (((u + a) ^ (-σ - 2) : ℝ) : ℂ) * Complex.exp (-(t * Real.log (u + a) : ℝ) * I) := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hua.ne'),
          ← Complex.ofReal_log hua.le, Real.rpow_def_of_pos hua, Complex.ofReal_exp]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      dsimp only [F_r, E, θ]
      rw [hcpow, Complex.ofReal_div]
      have hid1 : (((u + a) ^ (-σ - 2) : ℝ) : ℂ) / (psi u : ℂ) * (I * (psi u : ℂ)) =
          I * (((u + a) ^ (-σ - 2) : ℝ) : ℂ) := by
        field_simp [hpsi_nz]
      have hexp_split : Complex.exp (((ω * u - t * Real.log (u + a) : ℝ) : ℂ) * I) =
          Complex.exp (-(t * Real.log (u + a) : ℝ) * I) * Complex.exp ((ω * u : ℝ) * I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        (((u + a) ^ (-σ - 2) : ℝ) : ℂ) / (psi u : ℂ) *
            ((I * (psi u : ℂ)) * Complex.exp (((ω * u - t * Real.log (u + a) : ℝ) : ℂ) * I))
            = ((((u + a) ^ (-σ - 2) : ℝ) : ℂ) / (psi u : ℂ) * (I * (psi u : ℂ))) *
                Complex.exp (((ω * u - t * Real.log (u + a) : ℝ) : ℂ) * I) := by ring
        _ = (I * (((u + a) ^ (-σ - 2) : ℝ) : ℂ)) *
              (Complex.exp (-(t * Real.log (u + a) : ℝ) * I) * Complex.exp ((ω * u : ℝ) * I)) := by
            rw [hid1, hexp_split]
        _ = I * ((((u + a) ^ (-σ - 2) : ℝ) : ℂ) *
              Complex.exp (-(t * Real.log (u + a) : ℝ) * I) * Complex.exp ((ω * u : ℝ) * I)) := by
            ring
    have hid' : ∀ u ∈ Set.uIcc (N : ℝ) K,
        (F_r u : ℂ) * ((I * (psi u : ℂ)) * E u) =
          I * (((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
            Complex.exp ((ω * u : ℝ) * I)) := by
      intro u hu; rw [Set.uIcc_of_le hle] at hu; exact hid u hu
    have hcongr : ∫ u in (N : ℝ)..K, (F_r u : ℂ) * ((I * (psi u : ℂ)) * E u) =
        I * ∫ u in (N : ℝ)..K, ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
          Complex.exp ((ω * u : ℝ) * I) := by
      rw [intervalIntegral.integral_congr hid', intervalIntegral.integral_const_mul]
    rw [hcongr] at hmul
    have hii : (-I) * I = 1 := by
      calc (-I) * I = -(I * I) := by ring
        _ = -(-1) := by rw [I_mul_I]
        _ = 1 := by ring
    calc
      ∫ u in (N : ℝ)..K, ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
          Complex.exp ((ω * u : ℝ) * I)
          = (-I) * (I * ∫ u in (N : ℝ)..K,
              ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) *
                Complex.exp ((ω * u : ℝ) * I)) := by
        rw [← mul_assoc, hii, one_mul]
      _ = (-I) * (((F_r K : ℂ) * E K - (F_r N : ℂ) * E N) -
            ∫ u in (N : ℝ)..K, (F'_r u : ℂ) * E u) := by
        rw [hmul]
  have hint_lhs : IntegrableOn (fun u : ℝ ↦
      ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) * Complex.exp ((ω * u : ℝ) * I))
      (Set.Ioi (N : ℝ)) := by
    have hdom := (integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : -σ - 2 < -1))
    refine Integrable.mono' hdom ?_ ?_
    · have hc1 : ContinuousOn (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2))
          (Set.Ioi (N : ℝ)) :=
        continuousOn_of_forall_continuousAt fun u hu ↦ by
          have hu_gt : (N : ℝ) < u := hu
          exact (cpow_shift_hasDerivAt (by linarith [Nat.cast_nonneg (α := ℝ) N, ha]) _).continuousAt
      have hc2 : Continuous (fun u : ℝ ↦ Complex.exp ((ω * u : ℝ) * I)) := by fun_prop
      exact (hc1.mul hc2.continuousOn).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_gt : (N : ℝ) < u := hu
      have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hua, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [sub_re, neg_re, re_ofNat]
  have hF'_dom : ∀ u ∈ Set.Ioi (N : ℝ),
      ‖(F'_r u : ℂ) * E u‖ ≤
        ((σ + 2) / δ) * (u + a) ^ (-σ - 3) + (|t| / δ ^ 2) * (u + a) ^ (-σ - 4) := by
    intro u hu
    have hu_gt : (N : ℝ) < u := hu
    have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
    have hpsiu : δ ≤ |psi u| := hpsi_lb u (le_of_lt hu)
    have hE_norm : ‖E u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hE_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : F'_r u =
        (-σ - 2) * (u + a) ^ (-σ - 3) / psi u -
          t * (u + a) ^ (-σ - 4) / (psi u) ^ 2 := by
      dsimp only [F'_r]
      have hpow_eq : (u + a) ^ (-σ - 2) / (u + a) ^ 2 = (u + a) ^ (-σ - 4) := by
        rw [← Real.rpow_natCast (u + a) 2, ← Real.rpow_sub hua]
        congr 1; ring
      have hpsi_ne' := hpsi_ne u (le_of_lt hu)
      calc
        ((-σ - 2) * (u + a) ^ (-σ - 3) * psi u - (u + a) ^ (-σ - 2) * (t / (u + a) ^ 2)) / (psi u) ^ 2
            = (-σ - 2) * (u + a) ^ (-σ - 3) / psi u -
                t * ((u + a) ^ (-σ - 2) / (u + a) ^ 2) / (psi u) ^ 2 := by
          field_simp [hpsi_ne']
        _ = (-σ - 2) * (u + a) ^ (-σ - 3) / psi u - t * (u + a) ^ (-σ - 4) / (psi u) ^ 2 := by
          rw [hpow_eq]
    rw [hsplit]
    have h1 : |(-σ - 2) * (u + a) ^ (-σ - 3) / psi u| ≤ ((σ + 2) / δ) * (u + a) ^ (-σ - 3) := by
      rw [abs_div, abs_mul, abs_of_neg (by linarith : -σ - 2 < 0),
        abs_of_pos (Real.rpow_pos_of_pos hua _), show -(-σ - 2) = σ + 2 by ring]
      calc
        (σ + 2) * (u + a) ^ (-σ - 3) / |psi u|
            ≤ (σ + 2) * (u + a) ^ (-σ - 3) / δ := div_le_div_of_nonneg_left (by positivity) hδ_pos hpsiu
        _ = ((σ + 2) / δ) * (u + a) ^ (-σ - 3) := by ring
    have h2 : |t * (u + a) ^ (-σ - 4) / (psi u) ^ 2| ≤ (|t| / δ ^ 2) * (u + a) ^ (-σ - 4) := by
      rw [abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hua _), abs_pow]
      have hsq : δ ^ 2 ≤ |psi u| ^ 2 := sq_le_sq' (by linarith) hpsiu
      calc
        |t| * (u + a) ^ (-σ - 4) / |psi u| ^ 2
            ≤ |t| * (u + a) ^ (-σ - 4) / δ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ_pos) hsq
        _ = (|t| / δ ^ 2) * (u + a) ^ (-σ - 4) := by ring
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hint_F'_dom : IntegrableOn
      (fun u : ℝ ↦ ((σ + 2) / δ) * (u + a) ^ (-σ - 3) + (|t| / δ ^ 2) * (u + a) ^ (-σ - 4))
      (Set.Ioi (N : ℝ)) :=
    ((integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : -σ - 3 < -1)).const_mul _).add
      ((integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : -σ - 4 < -1)).const_mul _)
  have hint_F' : IntegrableOn (fun u : ℝ ↦ (F'_r u : ℂ) * E u) (Set.Ioi (N : ℝ)) := by
    refine Integrable.mono' hint_F'_dom ?_ ?_
    · have hc1 : ContinuousOn (fun u : ℝ ↦ (F'_r u : ℂ)) (Set.Ioi (N : ℝ)) := by
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
        have hu_gt : (N : ℝ) < u := hu
        have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
        have hpsi_c : ContinuousAt psi u :=
          continuousAt_const.sub (continuousAt_const.div (continuousAt_id.add continuousAt_const) hua.ne')
        have hpow1 : ContinuousAt (fun x : ℝ ↦ (x + a) ^ (-σ - 3)) u :=
          (continuousAt_id.add continuousAt_const).rpow_const (Or.inl hua.ne')
        have hpow2 : ContinuousAt (fun x : ℝ ↦ (x + a) ^ (-σ - 2)) u :=
          (continuousAt_id.add continuousAt_const).rpow_const (Or.inl hua.ne')
        refine (((continuousAt_const.mul hpow1).mul hpsi_c).sub
          (hpow2.mul (continuousAt_const.div ((continuousAt_id.add continuousAt_const).pow 2)
            (pow_ne_zero 2 hua.ne')))).div (hpsi_c.pow 2) (pow_ne_zero 2 (hpsi_ne u (le_of_lt hu)))
      have hc2 : ContinuousOn E (Set.Ioi (N : ℝ)) := by
        refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
        have hu_gt : (N : ℝ) < u := hu
        have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha]
        have hθ_c : ContinuousAt θ u :=
          (continuousAt_const.mul continuousAt_id).sub
            (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log hua.ne'))
        exact Complex.continuous_exp.continuousAt.comp
          ((Complex.continuous_ofReal.continuousAt.comp hθ_c).mul continuousAt_const)
      exact (hc1.mul hc2).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hF'_dom u hu
  have hint_lhs_lim :
      Tendsto (fun K : ℕ ↦ ∫ u in (N : ℝ)..K,
          ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) * Complex.exp ((ω * u : ℝ) * I))
        atTop (𝓝 (∫ u in Set.Ioi (N : ℝ),
          ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) * Complex.exp ((ω * u : ℝ) * I))) :=
    (intervalIntegral_tendsto_integral_Ioi N hint_lhs tendsto_id).comp tendsto_natCast_atTop_atTop
  have hint_F'_lim :
      Tendsto (fun K : ℕ ↦ ∫ u in (N : ℝ)..K, (F'_r u : ℂ) * E u)
        atTop (𝓝 (∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u)) :=
    (intervalIntegral_tendsto_integral_Ioi N hint_F' tendsto_id).comp tendsto_natCast_atTop_atTop
  have hFE_lim : Tendsto (fun K : ℕ ↦ (F_r K : ℂ) * E K) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hadd : Tendsto (fun K : ℕ ↦ (K : ℝ) + a) atTop atTop :=
      tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
    have hpow : Tendsto (fun K : ℕ ↦ ((K : ℝ) + a) ^ (-σ - 2) / δ) atTop (𝓝 0) := by
      have h0 : Tendsto (fun K : ℕ ↦ ((K : ℝ) + a) ^ (-σ - 2)) atTop (𝓝 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < σ + 2)).comp hadd).congr fun K ↦ by
          dsimp; rw [show -(σ + 2) = -σ - 2 by ring]
      simpa using h0.div_const δ
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hpow
    filter_upwards [eventually_ge_atTop N] with K hNK
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hKa : 0 < (K : ℝ) + a := by positivity
    have hpsiK : δ ≤ |psi K| := hpsi_lb K (Nat.cast_le.mpr hNK)
    dsimp only [F_r]
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hKa _)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hKa.le _) hδ_pos hpsiK
  have hrhs_lim :
      Tendsto (fun K : ℕ ↦ (-I) * (((F_r K : ℂ) * E K - (F_r N : ℂ) * E N) -
          ∫ u in (N : ℝ)..K, (F'_r u : ℂ) * E u))
        atTop (𝓝 ((-I) * ((0 - (F_r N : ℂ) * E N) -
          ∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u))) :=
    ((hFE_lim.sub_const _).sub hint_F'_lim).const_mul (-I)
  have heq_int :
      ∫ u in Set.Ioi (N : ℝ),
          ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2) * Complex.exp ((ω * u : ℝ) * I) =
        (-I) * (-(F_r N : ℂ) * E N - ∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u) := by
    have hlim' := hrhs_lim.congr' (by
      filter_upwards [eventually_ge_atTop N] with K hNK; exact (hibp K hNK).symm)
    simpa only [zero_sub, neg_mul] using tendsto_nhds_unique hint_lhs_lim hlim'
  have hFN_bd : ‖(F_r N : ℂ) * E N‖ ≤ M ^ (-σ - 2) / δ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    dsimp only [F_r]
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hM_pos _)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hM_pos.le _) hδ_pos (hpsi_lb N le_rfl)
  have hF'_int_bd :
      ‖∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u‖ ≤
        M ^ (-σ - 2) / δ + |t| * M ^ (-σ - 3) / (3 * δ ^ 2) := by
    have h1 := integral_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : 1 < σ + 3)
    have h2 := integral_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : 1 < σ + 4)
    have hdom_eval :
        ∫ u in Set.Ioi (N : ℝ),
            (((σ + 2) / δ) * (u + a) ^ (-σ - 3) + (|t| / δ ^ 2) * (u + a) ^ (-σ - 4)) =
          ((σ + 2) / δ) * (M ^ (-σ - 2) / (σ + 2)) +
            (|t| / δ ^ 2) * (M ^ (-σ - 3) / (σ + 3)) := by
      rw [integral_add
        ((integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : -σ - 3 < -1)).const_mul _)
        ((integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha (by linarith : -σ - 4 < -1)).const_mul _),
        integral_const_mul, integral_const_mul]
      have ha3 : ∫ u in Set.Ioi (N : ℝ), (u + a) ^ (-σ - 3) = M ^ (-σ - 2) / (σ + 2) := by
        simpa [show -(σ + 3) = -σ - 3 by ring, show 1 - (σ + 3) = -σ - 2 by ring,
          show (σ + 3) - 1 = σ + 2 by ring] using h1
      have ha4 : ∫ u in Set.Ioi (N : ℝ), (u + a) ^ (-σ - 4) = M ^ (-σ - 3) / (σ + 3) := by
        simpa [show -(σ + 4) = -σ - 4 by ring, show 1 - (σ + 4) = -σ - 3 by ring,
          show (σ + 4) - 1 = σ + 3 by ring] using h2
      rw [ha3, ha4]
    calc
      ‖∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u‖
          ≤ ∫ u in Set.Ioi (N : ℝ), ‖(F'_r u : ℂ) * E u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (N : ℝ),
            (((σ + 2) / δ) * (u + a) ^ (-σ - 3) + (|t| / δ ^ 2) * (u + a) ^ (-σ - 4)) :=
          setIntegral_mono_on hint_F'.norm hint_F'_dom measurableSet_Ioi fun u hu ↦ hF'_dom u hu
      _ = ((σ + 2) / δ) * (M ^ (-σ - 2) / (σ + 2)) +
            (|t| / δ ^ 2) * (M ^ (-σ - 3) / (σ + 3)) := hdom_eval
      _ = M ^ (-σ - 2) / δ + (|t| / δ ^ 2) * (M ^ (-σ - 3) / (σ + 3)) := by
          rw [show ((σ + 2) / δ) * (M ^ (-σ - 2) / (σ + 2)) = M ^ (-σ - 2) / δ by
            field_simp [show σ + 2 ≠ 0 by linarith, hδ_pos.ne']]
      _ ≤ M ^ (-σ - 2) / δ + (|t| / δ ^ 2) * (M ^ (-σ - 3) / 3) := by
          gcongr
          linarith
      _ = M ^ (-σ - 2) / δ + |t| * M ^ (-σ - 3) / (3 * δ ^ 2) := by ring
  rw [heq_int, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    ‖-(F_r N : ℂ) * E N - ∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u‖
        ≤ ‖-(F_r N : ℂ) * E N‖ + ‖∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u‖ := norm_sub_le _ _
    _ = ‖(F_r N : ℂ) * E N‖ + ‖∫ u in Set.Ioi (N : ℝ), (F'_r u : ℂ) * E u‖ := by
        rw [show -(F_r N : ℂ) * E N = -((F_r N : ℂ) * E N) by ring, norm_neg]
    _ ≤ M ^ (-σ - 2) / δ + (M ^ (-σ - 2) / δ + |t| * M ^ (-σ - 3) / (3 * δ ^ 2)) :=
        add_le_add hFN_bd hF'_int_bd
    _ = M ^ (-σ - 2) / δ + M ^ (-σ - 2) / δ + |t| * M ^ (-σ - 3) / (3 * δ ^ 2) := by ring

private lemma tsum_one_div_nat_add_one_cube_summable :
    Summable fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1) ^ 3 := by
  have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
  refine (summable_nat_add_iff 1).mpr h |>.congr fun m ↦ ?_
  simp [Nat.cast_add, Nat.cast_one]

/-- Paired positive and negative Fourier modes of the second Bernoulli
remainder in the Hurwitz Euler–Maclaurin formula. -/
noncomputable def hurwitzBernoulliMode (a : ℝ) (s : ℂ) (m : ℕ) (u : ℝ) : ℂ :=
    ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
      ((Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
        Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)) *
          ((u + a : ℝ) : ℂ) ^ (-s - 2))

/-- The Fourier expansion of the second Bernoulli remainder may be integrated
term by term on the infinite tail. -/
theorem hasSum_hurwitzBernoulliMode {a σ t : ℝ} (ha_pos : 0 < a) (hσ : 0 < σ) {N : ℝ} (hN : 0≤N) :
    let s := (σ:ℂ)+(t:ℂ)*I
    HasSum (fun m : ℕ => ∫ u in Set.Ioi (N:ℝ), hurwitzBernoulliMode a s m u)
      (∫ u in Set.Ioi (N:ℝ), (bernoulliKernel 2 u:ℂ)*((u+a:ℝ):ℂ)^(-s-2)) := by
  intro s
  let M : ℝ := (N:ℝ)+a
  let term := hurwitzBernoulliMode a s
  have hterm_eq : ∀ u : ℝ,
      (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2) = ∑' m : ℕ, term m u := by
    intro u
    rw [bernoulliKernel_two_eq_tsum_exp u, ← tsum_mul_right]
    refine tsum_congr fun m ↦ ?_
    dsimp only [term,hurwitzBernoulliMode]
    ring
  have hint_term : ∀ m : ℕ, IntegrableOn (term m) (Set.Ioi (N : ℝ)) := by
    intro m
    have hdom : IntegrableOn (fun u : ℝ ↦
        (1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (u + a) ^ (-σ - 2)) (Set.Ioi (N : ℝ)) :=
      (integrableOn_shift_rpow_Ioi hN ha_pos (by linarith)).const_mul _
    refine Integrable.mono' hdom ?_ ?_
    · have hc_pow : ContinuousOn (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
        continuousOn_of_forall_continuousAt fun u hu ↦ by
          have hu_gt : (N : ℝ) < u := hu
          exact (cpow_shift_hasDerivAt (by linarith [hN, ha_pos])
            (-s - 2)).continuousAt
      have hc_exp : Continuous (fun u : ℝ ↦
          ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
            (Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
              Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I))) := by fun_prop
      have hreord : term m = fun u : ℝ ↦
          (((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
            (Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
              Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I))) *
            ((u + a : ℝ) : ℂ) ^ (-s - 2) := by
        ext u; dsimp [term,hurwitzBernoulliMode]; ring
      rw [hreord]
      exact (hc_exp.continuousOn.mul hc_pow).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_gt : (N : ℝ) < u := hu
      have hua : 0 < u + a := by linarith [hN, ha_pos]
      dsimp only [term,hurwitzBernoulliMode]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Complex.norm_cpow_eq_rpow_re_of_pos hua, show (-s - 2).re = -σ - 2 by simp [s]]
      have hexp2 :
          ‖Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
              Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ ≤ 2 := by
        have h1 : ‖Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ = 1 :=
          Complex.norm_exp_ofReal_mul_I _
        have h2 : ‖Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ = 1 := by
          simpa using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi * ((m : ℝ) + 1) * u))
        exact (norm_add_le _ _).trans (by linarith)
      calc
        1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) *
            (‖Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
              Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ * (u + a) ^ (-σ - 2))
            ≤ 1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) * (2 * (u + a) ^ (-σ - 2)) := by
          gcongr
        _ = 1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) * (u + a) ^ (-σ - 2) := by
          field_simp; ring
  have hnorm_int_le : ∀ m : ℕ,
      ∫ u in Set.Ioi (N : ℝ), ‖term m u‖ ≤
        (M ^ (-σ - 1) / (2 * Real.pi ^ 2 * (σ + 1))) * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    have hdom : IntegrableOn (fun u : ℝ ↦
        (1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (u + a) ^ (-σ - 2)) (Set.Ioi (N : ℝ)) :=
      (integrableOn_shift_rpow_Ioi hN ha_pos (by linarith)).const_mul _
    calc
      ∫ u in Set.Ioi (N : ℝ), ‖term m u‖
          ≤ ∫ u in Set.Ioi (N : ℝ),
              (1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (u + a) ^ (-σ - 2) := by
        refine setIntegral_mono_on (hint_term m).norm hdom measurableSet_Ioi fun u hu ↦ ?_
        have hu_gt : (N : ℝ) < u := hu
        have hua : 0 < u + a := by linarith [hN, ha_pos]
        dsimp only [term,hurwitzBernoulliMode]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          Complex.norm_cpow_eq_rpow_re_of_pos hua, show (-s - 2).re = -σ - 2 by simp [s]]
        have hexp2 :
            ‖Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
                Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ ≤ 2 := by
          have h1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((m : ℝ) + 1) * u)
          have h2 : ‖Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ = 1 := by
            simpa using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi * ((m : ℝ) + 1) * u))
          exact (norm_add_le _ _).trans (by linarith)
        calc
          1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) *
              (‖Complex.exp ((2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I) +
                Complex.exp (-(2 * Real.pi * ((m : ℝ) + 1) * u : ℝ) * I)‖ * (u + a) ^ (-σ - 2))
              ≤ 1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) * (2 * (u + a) ^ (-σ - 2)) := by
            gcongr
          _ = 1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) * (u + a) ^ (-σ - 2) := by
            field_simp; ring
      _ = (1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
            ∫ u in Set.Ioi (N : ℝ), (u + a) ^ (-σ - 2) := integral_const_mul _ _
      _ = (1 / (2 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (M ^ (-σ - 1) / (σ + 1)) := by
          have hint_val := integral_shift_rpow_Ioi hN ha_pos (by linarith : 1 < σ + 2)
          rw [show -(σ + 2) = -σ - 2 by ring, show 1 - (σ + 2) = -σ - 1 by ring,
            show (σ + 2) - 1 = σ + 1 by ring] at hint_val
          rw [hint_val]
      _ = (M ^ (-σ - 1) / (2 * Real.pi ^ 2 * (σ + 1))) * (1 / ((m : ℝ) + 1) ^ 2) := by
          field_simp
  have hsumm_norms : Summable fun m : ℕ ↦ ∫ u in Set.Ioi (N : ℝ), ‖term m u‖ := by
    have h2 : Summable fun m : ℕ ↦
        (M ^ (-σ - 1) / (2 * Real.pi ^ 2 * (σ + 1))) * (1 / ((m : ℝ) + 1) ^ 2) := by
      have hraw := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left
        (M ^ (-σ - 1) / (2 * Real.pi ^ 2 * (σ + 1)))
      have hshift := (summable_nat_add_iff 1).mpr hraw
      refine hshift.congr fun m ↦ ?_
      simp [Nat.cast_add, Nat.cast_one]
    exact Summable.of_nonneg_of_le (fun m ↦ integral_nonneg fun u ↦ norm_nonneg _)
      hnorm_int_le h2
  convert hasSum_integral_of_summable_integral_norm hint_term hsumm_norms using 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => hterm_eq u

private lemma bernoulliKernel_two_oscillatory_tail_bound {c : ℝ} (hc0 : 0 < c)
    (hc2pi : c < 2 * Real.pi) :
    ∃ C_b : ℝ, 0 < C_b ∧ ∀ ⦃N : ℕ⦄ ⦃a σ t : ℝ⦄, a ∈ Set.Ioc (0 : ℝ) 1 → 0 < σ →
      |t| ≤ c * ((N : ℝ) + a) →
        ‖(t : ℂ) ^ 2 * ∫ u in Set.Ioi (N : ℝ),
            (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I) - 2)‖ ≤
          C_b * ((N : ℝ) + a) ^ (-σ) := by
  let S3 : ℝ := ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ 3
  have hS3_pos : 0 < S3 := by
    have h0 := tsum_one_div_nat_add_one_cube_summable.le_tsum 0 fun m _ ↦ by positivity
    simp only [Nat.cast_zero, zero_add, one_pow, div_one] at h0
    linarith
  let gap : ℝ := 2 * Real.pi - c
  have hgap_pos : 0 < gap := sub_pos.mpr hc2pi
  let C_b : ℝ := S3 * (c ^ 2 / (Real.pi ^ 2 * gap) + c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2))
  have hCb_pos : 0 < C_b := by positivity
  refine ⟨C_b, hCb_pos, fun N a σ t ha hσ ht_le ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let M : ℝ := (N : ℝ) + a
  have ha_pos : 0 < a := ha.1
  have hM_pos : 0 < M := by positivity
  let term := hurwitzBernoulliMode a s
  have hint_tsum := (hasSum_hurwitzBernoulliMode (t:=t) ha_pos hσ (Nat.cast_nonneg N)).tsum_eq.symm
  have hterm_bd : ∀ m : ℕ,
      ‖(t : ℂ) ^ 2 * ∫ u in Set.Ioi (N : ℝ), term m u‖ ≤
        (c ^ 2 / (Real.pi ^ 2 * gap) + c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2)) *
          M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3) := by
    intro m
    let ω : ℝ := 2 * Real.pi * ((m : ℝ) + 1)
    have hω_pos : 0 < ω := by positivity
    have hgap_m : ((m : ℝ) + 1) * gap ≤ ω - |t| / M := by
      have htM : |t| / M ≤ c := (div_le_iff₀ hM_pos).mpr ht_le
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      calc
        ((m : ℝ) + 1) * gap = 2 * Real.pi * ((m : ℝ) + 1) - ((m : ℝ) + 1) * c := by
          dsimp [gap, ω]; ring
        _ ≤ 2 * Real.pi * ((m : ℝ) + 1) - 1 * c := by gcongr
        _ = ω - c := by ring
        _ ≤ ω - |t| / M := by linarith
    have hδ_pos : 0 < ω - |t| / M := lt_of_lt_of_le (mul_pos (by positivity) hgap_pos) hgap_m
    have hδ_pos' : 0 < |-ω| - |t| / M := by simpa [abs_neg, abs_of_pos hω_pos] using hδ_pos
    have hosc_pos := oscillatory_integral_bound (N := N) (a := a) (σ := σ) (t := t) (ω := ω)
      ha_pos hσ (by simpa [abs_of_pos hω_pos] using hδ_pos)
    have hosc_neg := oscillatory_integral_bound (N := N) (a := a) (σ := σ) (t := t) (ω := -ω)
      ha_pos hσ hδ_pos'
    simp only [abs_neg, abs_of_pos hω_pos] at hosc_pos hosc_neg
    have hint1 : IntegrableOn
        (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((ω * u : ℝ) * I))
        (Set.Ioi (N : ℝ)) := by
      have hdom := integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith : -σ - 2 < -1)
      refine Integrable.mono' hdom ?_ ?_
      · have hc1 : ContinuousOn (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
          continuousOn_of_forall_continuousAt fun u hu ↦ by
            have hu_gt : (N : ℝ) < u := hu
            exact (cpow_shift_hasDerivAt (by linarith [Nat.cast_nonneg (α := ℝ) N, ha_pos])
              (-s - 2)).continuousAt
        exact (hc1.mul (by fun_prop : Continuous fun u : ℝ ↦ Complex.exp ((ω * u : ℝ) * I)).continuousOn).aestronglyMeasurable
          measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu_gt : (N : ℝ) < u := hu
        have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha_pos]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hua, Complex.norm_exp_ofReal_mul_I, mul_one]
        simp [s, sub_re, neg_re, re_ofNat]
    have hint2 : IntegrableOn
        (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((-ω * u : ℝ) * I))
        (Set.Ioi (N : ℝ)) := by
      have hdom := integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith : -σ - 2 < -1)
      refine Integrable.mono' hdom ?_ ?_
      · have hc1 : ContinuousOn (fun u : ℝ ↦ ((u + a : ℝ) : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
          continuousOn_of_forall_continuousAt fun u hu ↦ by
            have hu_gt : (N : ℝ) < u := hu
            exact (cpow_shift_hasDerivAt (by linarith [Nat.cast_nonneg (α := ℝ) N, ha_pos])
              (-s - 2)).continuousAt
        exact (hc1.mul (by fun_prop : Continuous fun u : ℝ ↦ Complex.exp ((-ω * u : ℝ) * I)).continuousOn).aestronglyMeasurable
          measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu_gt : (N : ℝ) < u := hu
        have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha_pos]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hua, Complex.norm_exp_ofReal_mul_I, mul_one]
        simp [s, sub_re, neg_re, re_ofNat]
    have hsplit_int : ∫ u in Set.Ioi (N : ℝ), term m u =
        ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
          ((∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((ω * u : ℝ) * I)) +
            ∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((-ω * u : ℝ) * I)) := by
      have h1 : (fun u : ℝ ↦ term m u) = fun u : ℝ ↦
          ((1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
            (((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((ω * u : ℝ) * I) +
              ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((-ω * u : ℝ) * I)) := by
        ext u; dsimp [term, hurwitzBernoulliMode, ω]; push_cast; ring
      rw [h1, integral_const_mul, integral_add hint1 hint2]
    rw [hsplit_int, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hosc_pos' : ‖∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) *
        Complex.exp ((ω * u : ℝ) * I)‖ ≤
        M ^ (-σ - 2) / (ω - |t| / M) + M ^ (-σ - 2) / (ω - |t| / M) +
          |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2) := hosc_pos
    have hosc_neg' : ‖∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) *
        Complex.exp ((-ω * u : ℝ) * I)‖ ≤
        M ^ (-σ - 2) / (ω - |t| / M) + M ^ (-σ - 2) / (ω - |t| / M) +
          |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2) := hosc_neg
    have hsum_osc :
        ‖(∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((ω * u : ℝ) * I)) +
            ∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((-ω * u : ℝ) * I)‖ ≤
          4 * M ^ (-σ - 2) / (ω - |t| / M) + 2 * |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      have hsum := add_le_add hosc_pos' hosc_neg'
      exact hsum.trans_eq (by ring)
    have hinv1 : (ω - |t| / M)⁻¹ ≤ (((m : ℝ) + 1) * gap)⁻¹ :=
      inv_anti₀ (mul_pos (by positivity) hgap_pos) hgap_m
    have hinv2 : ((ω - |t| / M) ^ 2)⁻¹ ≤ ((((m : ℝ) + 1) * gap) ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos (mul_pos (by positivity) hgap_pos))
        (sq_le_sq' (by linarith [mul_pos (by positivity : 0 < (m : ℝ) + 1) hgap_pos]) hgap_m)
    have ht_sq : t ^ 2 ≤ c ^ 2 * M ^ 2 := by
      rw [← sq_abs t]
      exact (pow_le_pow_left₀ (abs_nonneg t) ht_le 2).trans_eq (by ring)
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have h1_term :
        t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
            (4 * M ^ (-σ - 2) / (ω - |t| / M)) ≤
          (c ^ 2 / (Real.pi ^ 2 * gap)) * M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3) := by
      have hpowM : M ^ 2 * M ^ (-σ - 2) = M ^ (-σ) := by
        rw [← Real.rpow_natCast M 2, ← Real.rpow_add hM_pos]
        congr 1; ring
      calc
        t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (4 * M ^ (-σ - 2) / (ω - |t| / M))
            = (t ^ 2 * M ^ (-σ - 2)) * (1 / (Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (ω - |t| / M)⁻¹ := by
          field_simp
        _ ≤ (c ^ 2 * M ^ 2 * M ^ (-σ - 2)) * (1 / (Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
              (((m : ℝ) + 1) * gap)⁻¹ := by gcongr
        _ = (c ^ 2 / (Real.pi ^ 2 * gap)) * (M ^ 2 * M ^ (-σ - 2)) * (1 / ((m : ℝ) + 1) ^ 3) := by
          field_simp
        _ = (c ^ 2 / (Real.pi ^ 2 * gap)) * M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3) := by rw [hpowM]
    have h2_term :
        t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
            (2 * |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2)) ≤
          (c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2)) * M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3) := by
      have hpowM : M ^ 3 * M ^ (-σ - 3) = M ^ (-σ) := by
        rw [← Real.rpow_natCast M 3, ← Real.rpow_add hM_pos]
        congr 1; ring
      have ht_cube : t ^ 2 * |t| ≤ c ^ 3 * M ^ 3 := by
        have ht_le' : |t| ≤ c * M := ht_le
        calc
          t ^ 2 * |t| ≤ (c ^ 2 * M ^ 2) * (c * M) :=
            mul_le_mul ht_sq ht_le' (abs_nonneg t) (by positivity)
          _ = c ^ 3 * M ^ 3 := by ring
      have hm4 : (1 / ((m : ℝ) + 1) ^ 4) ≤ 1 / ((m : ℝ) + 1) ^ 3 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hm1 (by norm_num : 3 ≤ 4))
      calc
        t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
              (2 * |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2))
            = (t ^ 2 * |t| * M ^ (-σ - 3)) * (1 / (6 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
                ((ω - |t| / M) ^ 2)⁻¹ := by
          field_simp; ring
        _ ≤ (c ^ 3 * M ^ 3 * M ^ (-σ - 3)) * (1 / (6 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
              ((((m : ℝ) + 1) * gap) ^ 2)⁻¹ := by gcongr
        _ = (c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2)) * (M ^ 3 * M ^ (-σ - 3)) *
              (1 / ((m : ℝ) + 1) ^ 4) := by
          field_simp
        _ ≤ (c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2)) * M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3) := by
          rw [hpowM]; gcongr
    calc
      t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) *
          ‖(∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((ω * u : ℝ) * I)) +
            ∫ u in Set.Ioi (N : ℝ), ((u + a : ℝ) : ℂ) ^ (-s - 2) * Complex.exp ((-ω * u : ℝ) * I)‖)
          ≤ t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
              (4 * M ^ (-σ - 2) / (ω - |t| / M) + 2 * |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2)) := by
        rw [← mul_assoc]
        gcongr
      _ = t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) * (4 * M ^ (-σ - 2) / (ω - |t| / M)) +
            t ^ 2 * (1 / (4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) *
              (2 * |t| * M ^ (-σ - 3) / (3 * (ω - |t| / M) ^ 2)) := by ring
      _ ≤ (c ^ 2 / (Real.pi ^ 2 * gap) + c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2)) *
            M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3) := by
        linarith [h1_term, h2_term]
  have hsumm_final : Summable fun m : ℕ ↦ ‖(t : ℂ) ^ 2 * ∫ u in Set.Ioi (N : ℝ), term m u‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_bd ?_
    exact tsum_one_div_nat_add_one_cube_summable.mul_left _
  rw [hint_tsum, ← tsum_mul_left]
  calc
    ‖∑' m : ℕ, (t : ℂ) ^ 2 * ∫ u in Set.Ioi (N : ℝ), term m u‖
        ≤ ∑' m : ℕ, ‖(t : ℂ) ^ 2 * ∫ u in Set.Ioi (N : ℝ), term m u‖ :=
      norm_tsum_le_tsum_norm hsumm_final
    _ ≤ ∑' m : ℕ, ((c ^ 2 / (Real.pi ^ 2 * gap) + c ^ 3 / (6 * Real.pi ^ 2 * gap ^ 2)) *
          M ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 3)) :=
      hsumm_final.tsum_le_tsum hterm_bd (tsum_one_div_nat_add_one_cube_summable.mul_left _)
    _ = C_b * M ^ (-σ) := by
      rw [tsum_mul_left]
      dsimp only [C_b, S3]
      ring

/-- **Approximate Dirichlet polynomial representation for `HurwitzZeta.hurwitzZeta`**:
for any `0 < c < 2 * π`, there exists `K > 0` such that whenever `a ∈ (0, 1]`, `σ > 0`,
`s = σ + t * I ≠ 1`, and `|t| ≤ c * (N + a)`,
`‖hurwitzZeta a s - (∑ n ∈ Icc 0 N, (n + a)^(-s) - (N + a)^(1 - s) / (1 - s))‖ ≤ K * (N + a)^(-σ)`. -/
theorem hurwitzZeta_approx_dirichletPoly {c : ℝ} (hc0 : 0 < c) (hc2pi : c < 2 * Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ ⦃a : ℝ⦄, a ∈ Set.Ioc (0 : ℝ) 1 → ∀ ⦃N : ℕ⦄, ∀ ⦃σ t : ℝ⦄,
      0 < σ → ((σ : ℂ) + (t : ℂ) * I) ≠ 1 → |t| ≤ c * ((N : ℝ) + a) →
        ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * I) -
          (∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-((σ : ℂ) + (t : ℂ) * I)) -
            ((N : ℂ) + a) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) /
              (1 - ((σ : ℂ) + (t : ℂ) * I)))‖ ≤
          K * ((N : ℝ) + a) ^ (-σ) := by
  obtain ⟨C_b, hCb_pos, hosc⟩ := bernoulliKernel_two_oscillatory_tail_bound hc0 hc2pi
  let K : ℝ := 1 + c / 6 + C_b
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, fun a ha N σ t hσ hs1 ht_le ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let M : ℝ := (N : ℝ) + a
  have ha_pos : 0 < a := ha.1
  have hM_pos : 0 < M := by positivity
  have hs_re : 0 < s.re := by simp [s, hσ]
  have h1 := hurwitzZeta_eq_eulerMaclaurin_Icc_of_re_pos ha N hs_re hs1
  have h2 := hurwitzZeta_eq_eulerMaclaurin_second_order_of_re_gt_neg_one ha N
    (by linarith : -1 < s.re) hs1
  have hibp_tail :
      ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1) =
        -(1 / 12 : ℂ) * ((N : ℂ) + a) ^ (-s - 1) +
          (s + 1) * (∫ u in Set.Ioi (N : ℝ),
            (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)) := by
    have hdiff_eq := congrArg (· - ∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) +
      ((N : ℂ) + a) ^ (1 - s) / (1 - s) + (1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s)) (h1.symm.trans h2)
    have hs_ne : s ≠ 0 := fun h ↦ by simp [h] at hs_re
    have hmul_eq : s * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) =
        s * (-(1 / 12 : ℂ) * ((N : ℂ) + a) ^ (-s - 1) +
          (s + 1) * (∫ u in Set.Ioi (N : ℝ),
            (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2))) := by
      linear_combination -hdiff_eq
    exact mul_left_cancel₀ hs_ne hmul_eq
  have hexp_diff :
      HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s -
          (∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) - ((N : ℂ) + a) ^ (1 - s) / (1 - s)) =
        -(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
          (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) +
          (1 / 12 : ℂ) * ((t : ℂ) * I) * ((N : ℂ) + a) ^ (-s - 1) -
          ((t : ℂ) * I * ((σ + 1 : ℝ) : ℂ)) *
            (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)) +
          (t : ℂ) ^ 2 *
            (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)) := by
    have hs_decomp : s = (σ : ℂ) + (t : ℂ) * I := rfl
    have hs1_decomp : s + 1 = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      dsimp only [s]; push_cast; ring
    have hii : ((t : ℂ) * I) * ((t : ℂ) * I) = -((t : ℂ) ^ 2) := by
      calc ((t : ℂ) * I) * ((t : ℂ) * I) = (t : ℂ) ^ 2 * (I * I) := by ring
        _ = (t : ℂ) ^ 2 * (-1) := by rw [I_mul_I]
        _ = -((t : ℂ) ^ 2) := by ring
    have hs_int : s * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) =
        (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) +
          ((t : ℂ) * I) *
            (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) := by
      rw [hs_decomp, add_mul]
    have hmul_I :
        ((t : ℂ) * I) * (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I) =
          ((t : ℂ) * I * ((σ + 1 : ℝ) : ℂ)) - (t : ℂ) ^ 2 := by
      linear_combination hii
    rw [h1]
    calc
      (∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) - ((N : ℂ) + a) ^ (1 - s) / (1 - s) -
          (1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
          s * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1))) -
          (∑ n ∈ Finset.Icc 0 N, ((n : ℂ) + a) ^ (-s) - ((N : ℂ) + a) ^ (1 - s) / (1 - s))
          = -(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
              (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) -
              ((t : ℂ) * I) *
                (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) := by
        rw [hs_int]; ring
      _ = -(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
            (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) -
            ((t : ℂ) * I) * (-(1 / 12 : ℂ) * ((N : ℂ) + a) ^ (-s - 1) +
              (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I) * (∫ u in Set.Ioi (N : ℝ),
                (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2))) := by
        rw [hibp_tail, hs1_decomp]
      _ = _ := by
        have h2' : ((t : ℂ) * I) * ((((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I) *
            (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2))) =
            (((t : ℂ) * I * ((σ + 1 : ℝ) : ℂ)) - (t : ℂ) ^ 2) *
              (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)) := by
          rw [← mul_assoc, hmul_I]
        rw [mul_add, h2']
        ring
  have hcast : ((N : ℂ) + (a : ℂ)) = ((M : ℝ) : ℂ) := by dsimp [M]; push_cast; rfl
  have h_bd1 : ‖-(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s)‖ = (1 / 2) * M ^ (-σ) := by
    rw [hcast, norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hM_pos, show (-s).re = -σ by simp [s]]
  have h_bd2 :
      ‖(σ : ℂ) * ∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)‖ ≤
        (1 / 2) * M ^ (-σ) := by
    have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * (u + a) ^ (-σ - 1)) (Set.Ioi (N : ℝ)) :=
      (integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith)).const_mul (1 / 2)
    have h_int := integrableOn_sawtooth_shift_cpow_Ioi (Nat.cast_nonneg N) ha_pos hs_re
    have hint_eval := integral_shift_rpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith : 1 < σ + 1)
    have hint_norm :
        ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)‖ ≤
          M ^ (-σ) / (2 * σ) := by
      calc
        ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)‖
            ≤ ∫ u in Set.Ioi (N : ℝ), ‖(sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℝ) * (u + a) ^ (-σ - 1) := by
          refine setIntegral_mono_on h_int.norm hdom measurableSet_Ioi fun u hu ↦ ?_
          have hu_gt : (N : ℝ) < u := hu
          have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha_pos]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos hua, show (-s - 1).re = -σ - 1 by simp [s]]
          exact mul_le_mul (sawtooth_abs_le u) le_rfl (by positivity) (by positivity)
        _ = (1 / 2) * ∫ u in Set.Ioi (N : ℝ), (u + a) ^ (-σ - 1) := integral_const_mul _ _
        _ = (1 / 2) * (M ^ (-σ) / σ) := by
          rw [show -(σ + 1) = -σ - 1 by ring, show 1 - (σ + 1) = -σ by ring,
            show (σ + 1) - 1 = σ by ring] at hint_eval
          rw [hint_eval]
        _ = M ^ (-σ) / (2 * σ) := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le]
    calc
      σ * ‖∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)‖
          ≤ σ * (M ^ (-σ) / (2 * σ)) := by gcongr
      _ = (1 / 2) * M ^ (-σ) := by field_simp [hσ.ne']
  have h_bd3 : ‖(1 / 12 : ℂ) * ((t : ℂ) * I) * ((N : ℂ) + a) ^ (-s - 1)‖ ≤ (c / 12) * M ^ (-σ) := by
    rw [hcast, norm_mul, norm_mul, show ‖(1 / 12 : ℂ)‖ = 1 / 12 by norm_num, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hM_pos, show (-s - 1).re = -σ - 1 by simp [s]]
    have hpow : M * M ^ (-σ - 1) = M ^ (-σ) := by
      nth_rw 1 [← Real.rpow_one M]
      rw [← Real.rpow_add hM_pos]
      congr 1; ring
    calc
      1 / 12 * |t| * M ^ (-σ - 1) ≤ 1 / 12 * (c * M) * M ^ (-σ - 1) := by gcongr
      _ = (c / 12) * (M * M ^ (-σ - 1)) := by ring
      _ = (c / 12) * M ^ (-σ) := by rw [hpow]
  have h_bd4 :
      ‖((t : ℂ) * I * ((σ + 1 : ℝ) : ℂ)) *
          ∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)‖ ≤
        (c / 12) * M ^ (-σ) := by
    have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 12 : ℝ) * (u + a) ^ (-σ - 2)) (Set.Ioi (N : ℝ)) :=
      (integrableOn_shift_rpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith)).const_mul (1 / 12)
    have h_int := integrableOn_bernoulliKernel_two_shift_cpow_Ioi (Nat.cast_nonneg N) ha_pos
      (by linarith : -1 < s.re)
    have hint_eval := integral_shift_rpow_Ioi (Nat.cast_nonneg N) ha_pos (by linarith : 1 < σ + 2)
    have hint_norm :
        ‖∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)‖ ≤
          M ^ (-σ - 1) / (12 * (σ + 1)) := by
      calc
        ‖∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)‖
            ≤ ∫ u in Set.Ioi (N : ℝ),
                ‖(bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ u in Set.Ioi (N : ℝ), (1 / 12 : ℝ) * (u + a) ^ (-σ - 2) := by
          refine setIntegral_mono_on h_int.norm hdom measurableSet_Ioi fun u hu ↦ ?_
          have hu_gt : (N : ℝ) < u := hu
          have hua : 0 < u + a := by linarith [Nat.cast_nonneg (α := ℝ) N, ha_pos]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos hua, show (-s - 2).re = -σ - 2 by simp [s]]
          exact mul_le_mul (bernoulliKernel_two_abs_le u) le_rfl (by positivity) (by positivity)
        _ = (1 / 12) * ∫ u in Set.Ioi (N : ℝ), (u + a) ^ (-σ - 2) := integral_const_mul _ _
        _ = (1 / 12) * (M ^ (-σ - 1) / (σ + 1)) := by
          rw [show -(σ + 2) = -σ - 2 by ring, show 1 - (σ + 2) = -σ - 1 by ring,
            show (σ + 2) - 1 = σ + 1 by ring] at hint_eval
          rw [hint_eval]
        _ = M ^ (-σ - 1) / (12 * (σ + 1)) := by field_simp
    have hpow : M * M ^ (-σ - 1) = M ^ (-σ) := by
      nth_rw 1 [← Real.rpow_one M]
      rw [← Real.rpow_add hM_pos]
      congr 1; ring
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    calc
      |t| * (σ + 1) *
          ‖∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)‖
          ≤ (c * M) * (σ + 1) * (M ^ (-σ - 1) / (12 * (σ + 1))) := by gcongr
      _ = (c / 12) * (M * M ^ (-σ - 1)) := by field_simp [show σ + 1 ≠ 0 by linarith]
      _ = (c / 12) * M ^ (-σ) := by rw [hpow]
  have h_bd5 : ‖(t : ℂ) ^ 2 * ∫ u in Set.Ioi (N : ℝ),
      (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)‖ ≤ C_b * ((N : ℝ) + a) ^ (-σ) :=
    hosc ha hσ ht_le
  rw [hexp_diff]
  have htri1 := norm_add_le
    (-(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
      (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) +
      (1 / 12 : ℂ) * ((t : ℂ) * I) * ((N : ℂ) + a) ^ (-s - 1) -
      ((t : ℂ) * I * ((σ + 1 : ℝ) : ℂ)) *
        (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)))
    ((t : ℂ) ^ 2 * (∫ u in Set.Ioi (N : ℝ),
      (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)))
  have htri2 := norm_sub_le
    (-(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
      (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)) +
      (1 / 12 : ℂ) * ((t : ℂ) * I) * ((N : ℂ) + a) ^ (-s - 1))
    (((t : ℂ) * I * ((σ + 1 : ℝ) : ℂ)) *
      (∫ u in Set.Ioi (N : ℝ), (bernoulliKernel 2 u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 2)))
  have htri3 := norm_add_le
    (-(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s) -
      (σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)))
    ((1 / 12 : ℂ) * ((t : ℂ) * I) * ((N : ℂ) + a) ^ (-s - 1))
  have htri4 := norm_sub_le
    (-(1 / 2 : ℂ) * ((N : ℂ) + a) ^ (-s))
    ((σ : ℂ) * (∫ u in Set.Ioi (N : ℝ), (sawtooth u : ℂ) * ((u + a : ℝ) : ℂ) ^ (-s - 1)))
  dsimp only [K, M] at *
  linarith

/-- **Approximate Dirichlet polynomial representation for `riemannZeta`**:
for any `0 < c < 2 * π`, there exists `K > 0` such that for all `N ≥ 1`, `σ > 0`,
`s = σ + t * I ≠ 1`, and `|t| ≤ c * N`,
`‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s))‖ ≤ K * (N : ℝ) ^ (-σ)`. -/
theorem riemannZeta_approx_dirichletPoly {c : ℝ} (hc0 : 0 < c) (hc2pi : c < 2 * Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ ⦃N : ℕ⦄, 1 ≤ N → ∀ ⦃σ t : ℝ⦄, 0 < σ → ((σ : ℂ) + (t : ℂ) * I) ≠ 1 →
      |t| ≤ c * (N : ℝ) →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
          (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) -
            (N : ℂ) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) /
              (1 - ((σ : ℂ) + (t : ℂ) * I)))‖ ≤
          K * (N : ℝ) ^ (-σ) := by
  obtain ⟨K, hK_pos, hbd⟩ := hurwitzZeta_approx_dirichletPoly hc0 hc2pi
  refine ⟨K, hK_pos, fun N hN σ t hσ hs1 ht_le ↦ ?_⟩
  have ha1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hcast_N : ((N - 1 : ℕ) : ℝ) + (1 : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub hN, Nat.cast_one]
    ring
  have hcast_Nc : ((N - 1 : ℕ) : ℂ) + (1 : ℂ) = (N : ℂ) := by
    rw [Nat.cast_sub hN, Nat.cast_one]
    ring
  have hsum_eq : ∑ n ∈ Finset.Icc 0 (N - 1), ((n : ℂ) + 1) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    refine Finset.sum_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
    · intro a _ b _ h; omega
    · intro b hb; simp only [Finset.mem_Icc] at hb; exact ⟨b - 1, by simp; omega, by omega⟩
    · intro n _; rw [Nat.cast_add, Nat.cast_one]
  have hhz_eq : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * I) =
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
    have h1 : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period 1
    rw [h1, HurwitzZeta.hurwitzZeta_zero]
  have hres := hbd ha1 (N := N - 1) hσ hs1 (by simpa [hcast_N] using ht_le)
  simp only [Complex.ofReal_one] at hres
  rw [hhz_eq, hsum_eq, hcast_Nc, hcast_N] at hres
  exact hres

/-- Explicit Dirichlet polynomial approximation error bound for `riemannZeta`:
for `0 < c < 2 * π`, `N ≥ 1`, `σ > 0`, and `1 ≤ |t| ≤ c * N`,
`‖riemannZeta (σ + t * I) - dirichletPoly (fun _ ↦ 1) N (σ + t * I)‖ ≤ (N : ℝ) ^ (1 - σ) / |t| + K * (N : ℝ) ^ (-σ)`. -/
theorem riemannZeta_approx_dirichletPoly_sub_bound {c : ℝ} (hc0 : 0 < c)
    (hc2pi : c < 2 * Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ ⦃N : ℕ⦄, 1 ≤ N → ∀ ⦃σ t : ℝ⦄, 0 < σ → 1 ≤ |t| →
      |t| ≤ c * (N : ℝ) →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
          dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          (N : ℝ) ^ (1 - σ) / |t| + K * (N : ℝ) ^ (-σ) := by
  obtain ⟨K, hK_pos, hbd⟩ := riemannZeta_approx_dirichletPoly hc0 hc2pi
  refine ⟨K, hK_pos, fun N hN σ t hσ ht1 ht_le ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := fun h ↦ by
    have him := congrArg Complex.im h
    simp [s] at him
    rw [him, abs_zero] at ht1
    linarith
  have hdir : dirichletPoly (fun _ ↦ 1) N s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
    simp [dirichletPoly]
  have hterm : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ (N : ℝ) ^ (1 - σ) / |t| := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hN, show (1 - s).re = 1 - σ by simp [s]]
    have h1s : |t| ≤ ‖1 - s‖ := by
      have him : (1 - s).im = -t := by simp [s]
      calc |t| = |(-t)| := (abs_neg t).symm
        _ = |(1 - s).im| := by rw [him]
        _ ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by linarith) h1s
  have htri : ‖riemannZeta s - dirichletPoly (fun _ ↦ 1) N s‖ ≤
      ‖riemannZeta s - (dirichletPoly (fun _ ↦ 1) N s - (N : ℂ) ^ (1 - s) / (1 - s))‖ +
        ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      norm_add_le (riemannZeta s - (dirichletPoly (fun _ ↦ 1) N s - (N : ℂ) ^ (1 - s) / (1 - s)))
        (-( (N : ℂ) ^ (1 - s) / (1 - s)))
  have hmain := hbd hN hσ hs1 ht_le
  rw [← hdir] at hmain
  linarith

end ApproximateDirichletPolynomial

section MeanSquareCriticalHalfPlane

/-- Mean-square theorem for `riemannZeta` in the region of absolute convergence `1 < σ`,
bridging directly to `DirichletSeries.VerticalOrder.tendsto_mean_sq_LSeries_eq_tsum_norm_sq_mul`. -/
theorem tendsto_mean_sq_riemannZeta_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * T)) *
        ∫ t in (-T)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, (n : ℝ) ^ (-2 * σ))) := by
  have heq : (fun t : ℝ ↦ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      fun t : ℝ ↦ ‖LSeries (1 : ℕ → ℂ) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    ext t
    have hs : 1 < ((σ : ℂ) + (t : ℂ) * I).re := by simp [hσ]
    rw [LSeries_one_eq_riemannZeta hs]
  rw [heq]
  have habs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (σ : EReal) := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact EReal.coe_lt_coe_iff.mpr hσ
  have h := tendsto_mean_sq_LSeries_of_abscissaOfAbsConv_lt habs (Or.inl (by linarith))
  simpa using h

private lemma one_sub_inv_add_le_half_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have h1 : 1 - (1 + x)⁻¹ ≤ Real.log (1 + x) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have h2 : x / 2 ≤ 1 - (1 + x)⁻¹ := by
    have hpos : 0 < 1 + x := by linarith
    have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      field_simp [hpos.ne']
      ring
    rw [heq]
    exact div_le_div_of_nonneg_left hx0 hpos (by linarith)
  exact h2.trans h1

private lemma sum_Icc_one_rpow_neg_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-α) ≤ 1 + (N : ℝ) ^ (1 - α) / (1 - α) := by
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-α) =
      1 + ∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-α) := by
    rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons, Nat.cast_one, Real.one_rpow]
    rfl
  rw [hsplit]
  gcongr
  have hterm (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) ^ (-α) ≤ ∫ u in ((n : ℝ) - 1)..(n : ℝ), u ^ (-α) := by
    have hconst : (n : ℝ) ^ (-α) = ∫ _ in ((n : ℝ) - 1)..(n : ℝ), (n : ℝ) ^ (-α) := by
      simp [intervalIntegral.integral_const]
    rw [hconst]
    have hcont : ContinuousOn (fun u : ℝ ↦ u ^ (-α)) (Set.Icc ((n : ℝ) - 1) n) := by
      refine continuousOn_of_forall_continuousAt fun u hu ↦ ?_
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hu_pos : 0 < u := by linarith [hu.1]
      exact continuousAt_id.rpow_const (Or.inl hu_pos.ne')
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hcont.intervalIntegrable_of_Icc (by linarith)) fun u hu ↦ ?_
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hu.1]) hu.2 (by linarith)
  have hsum_int : ∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-α) ≤
      ∑ n ∈ Finset.Icc 2 N, ∫ u in ((n : ℝ) - 1)..(n : ℝ), u ^ (-α) :=
    Finset.sum_le_sum fun n hn ↦ hterm n (Finset.mem_Icc.mp hn).1
  have htele (M : ℕ) (hM : 1 ≤ M) : ∑ n ∈ Finset.Icc 2 M, ∫ u in ((n : ℝ) - 1)..(n : ℝ), u ^ (-α) =
      ∫ u in (1 : ℝ)..(M : ℝ), u ^ (-α) := by
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
        have h1k : ContinuousOn (fun u : ℝ ↦ u ^ (-α)) (Set.Icc (1 : ℝ) k) :=
          continuousOn_of_forall_continuousAt fun u hu ↦ by
            have hu_pos : 0 < u := by linarith [hu.1]
            exact continuousAt_id.rpow_const (Or.inl hu_pos.ne')
        have hkk : ContinuousOn (fun u : ℝ ↦ u ^ (-α)) (Set.Icc (k : ℝ) (k + 1)) :=
          continuousOn_of_forall_continuousAt fun u hu ↦ by
            have hk1r : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk1'
            have hu_pos : 0 < u := by linarith [hu.1]
            exact continuousAt_id.rpow_const (Or.inl hu_pos.ne')
        exact intervalIntegral.integral_add_adjacent_intervals
          (h1k.intervalIntegrable_of_Icc (Nat.one_le_cast.mpr hk1'))
          (hkk.intervalIntegrable_of_Icc (by linarith))
  have hint_eval : ∫ u in (1 : ℝ)..(N : ℝ), u ^ (-α) = ((N : ℝ) ^ (1 - α) - 1) / (1 - α) := by
    rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
      rw [Set.uIcc_of_le (Nat.one_le_cast.mpr hN)] at h; linarith [h.1]⟩)]
    simp only [Real.one_rpow, show -α + 1 = 1 - α by ring]
  have hle_end : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) ≤ (N : ℝ) ^ (1 - α) / (1 - α) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  exact hsum_int.trans ((htele N hN).trans hint_eval |>.trans_le hle_end)

private lemma harmonic_Icc_one_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n = 1 + ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n := by
    rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons, Nat.cast_one, div_one]
    rfl
  rw [hsplit]
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

private lemma offDiag_dirichlet_sum_bound_of_ge_half {σ : ℝ} (hσ : 1 / 2 ≤ σ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m = n then 0 else 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m|) ≤
      (4 / Real.log 2) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ)) ^ 2 +
        8 * (1 + Real.log N) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) := by
  let f : ℕ → ℕ → ℝ := fun m n ↦
    if m = n then 0 else 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m|
  have hf_symm : ∀ m n : ℕ, f m n = f n m := fun m n ↦ by
    by_cases h : m = n
    · subst h; simp [f]
    · simp only [f, h, ↓reduceIte, Ne.symm h, abs_sub_comm]
      ring
  have hdiag_split : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, f m n =
      2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ioc m N, f m n := by
    have hsplit_pair : ∀ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N, f m n =
          (∑ n ∈ Finset.Ico 1 m, f m n) + ∑ n ∈ Finset.Ioc m N, f m n := by
      intro m hm
      have h1m : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
      have hset : Finset.Icc 1 N = Finset.Ico 1 m ∪ insert m (Finset.Ioc m N) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico, Finset.mem_insert,
          Finset.mem_Ioc]; omega
      rw [hset, Finset.sum_union (by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_Ico] at hk1; simp only [Finset.mem_insert, Finset.mem_Ioc] at hk2
        omega), Finset.sum_insert (by simp)]
      simp only [f, ↓reduceIte, zero_add]
    rw [Finset.sum_congr rfl hsplit_pair, Finset.sum_add_distrib]
    have hswap : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 m, f m n =
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc n N, f n m := by
      have hid1 : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 m, f m n =
          ∑ x ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), if x.2 < x.1 then f x.1 x.2 else 0 := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun m hm ↦ ?_
        rw [← Finset.sum_filter]
        have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
        refine Finset.sum_congr (by ext n; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_Icc]; omega)
          fun _ _ ↦ rfl
      have hid2 : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc n N, f n m =
          ∑ x ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), if x.1 < x.2 then f x.1 x.2 else 0 := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun n hn ↦ ?_
        rw [← Finset.sum_filter]
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        refine Finset.sum_congr (by ext m; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega)
          fun _ _ ↦ rfl
      rw [hid1, hid2]
      refine Finset.sum_bij (fun x _ ↦ (x.2, x.1)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_product, Finset.mem_Icc] at hx ⊢
        exact ⟨hx.2, hx.1⟩
      · intro a _ b _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro b hb
        simp only [Finset.mem_product, Finset.mem_Icc] at hb ⊢
        exact ⟨(b.2, b.1), ⟨hb.2, hb.1⟩, rfl⟩
      · intro x _; split_ifs <;> [exact hf_symm x.1 x.2; rfl]
    rw [hswap, two_mul]
  have hinner_bd : ∀ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Ioc m N, f m n ≤
        (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) +
          4 * (1 + Real.log N) * (m : ℝ) ^ (1 - 2 * σ) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
    have hsplit_n : Finset.Ioc m N ⊆ Finset.Ioc m (min (2 * m - 1) N) ∪ Finset.Icc (2 * m) N := by
      intro n hn
      simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_Icc] at hn ⊢
      omega
    have h1_part : ∑ n ∈ Finset.Icc (2 * m) N, f m n ≤
        (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) := by
      have hterm : ∀ n ∈ Finset.Icc (2 * m) N,
          f m n ≤ (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := by
        intro n hn
        have hn_ge : 2 * m ≤ n := (Finset.mem_Icc.mp hn).1
        have hne : m ≠ n := by omega
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have h2mn : (2 : ℝ) * m ≤ n := by exact_mod_cast hn_ge
        have hlog_ge : Real.log 2 ≤ |Real.log n - Real.log m| := by
          have hlog_sub : Real.log 2 ≤ Real.log n - Real.log m := by
            rw [← Real.log_div hn_pos.ne' hm_pos.ne']
            exact Real.log_le_log zero_lt_two ((le_div_iff₀ hm_pos).mpr h2mn)
          exact hlog_sub.trans (le_abs_self _)
        dsimp only [f]
        simp only [hne, ↓reduceIte]
        calc
          2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m|
              ≤ 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / Real.log 2 :=
            div_le_div_of_nonneg_left (by positivity) (Real.log_pos one_lt_two) hlog_ge
          _ = (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := by ring
      calc
        ∑ n ∈ Finset.Icc (2 * m) N, f m n
            ≤ ∑ n ∈ Finset.Icc (2 * m) N,
                (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := Finset.sum_le_sum hterm
        _ ≤ ∑ n ∈ Finset.Icc 1 N, (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ by
            have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
            positivity)
          intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
        _ = (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    have h2_part : ∑ n ∈ Finset.Ioc m (min (2 * m - 1) N), f m n ≤
        4 * (1 + Real.log N) * (m : ℝ) ^ (1 - 2 * σ) := by
      have hterm : ∀ n ∈ Finset.Ioc m (min (2 * m - 1) N),
          f m n ≤ 4 * (m : ℝ) ^ (1 - 2 * σ) * (1 / ((n - m : ℕ) : ℝ)) := by
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have hne : m ≠ n := by omega
        have hmn_lt : n < 2 * m := by omega
        have hrm_le : ((n - m : ℕ) : ℝ) / m ≤ 1 := by
          rw [div_le_one hm_pos]
          exact_mod_cast (by omega : n - m ≤ m)
        have hrm_nn : 0 ≤ ((n - m : ℕ) : ℝ) / m := by positivity
        have hlog_lb : ((n - m : ℕ) : ℝ) / (2 * m) ≤ |Real.log n - Real.log m| := by
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hdiv_eq : (n : ℝ) / m = 1 + ((n - m : ℕ) : ℝ) / m := by
            rw [Nat.cast_sub hn.1.le]
            field_simp [hm_pos.ne']
            ring
          have hlog_sub := one_sub_inv_add_le_half_mul hrm_nn hrm_le
          rw [← hdiv_eq, Real.log_div hn_pos.ne' hm_pos.ne'] at hlog_sub
          have heq : (((n - m : ℕ) : ℝ) / m) / 2 = ((n - m : ℕ) : ℝ) / (2 * m) := by ring
          rw [heq] at hlog_sub
          exact hlog_sub.trans (le_abs_self _)
        have hn_rpow : (n : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hm_pos (by exact_mod_cast hn.1.le) (by linarith)
        have hpow_comb : (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) * (2 * m) = 2 * (m : ℝ) ^ (1 - 2 * σ) := by
          have hm_r : (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          calc
            (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) * (2 * m)
                = 2 * ((m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) * (m : ℝ) ^ (1 : ℝ)) := by
              rw [← hm_r]; ring
            _ = 2 * (m : ℝ) ^ (-σ + -σ + 1) := by
              rw [← Real.rpow_add hm_pos, ← Real.rpow_add hm_pos]
            _ = 2 * (m : ℝ) ^ (1 - 2 * σ) := by congr 2; ring
        have hdiff_pos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - m)
        dsimp only [f]
        simp only [hne, ↓reduceIte]
        calc
          2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m|
              ≤ 2 * (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) / (((n - m : ℕ) : ℝ) / (2 * m)) := by
            refine div_le_div₀ (by positivity) (by gcongr) (by positivity) hlog_lb
          _ = 2 * ((m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) * (2 * m)) * (1 / ((n - m : ℕ) : ℝ)) := by
            field_simp [hm_pos.ne', hdiff_pos.ne']
          _ = 4 * (m : ℝ) ^ (1 - 2 * σ) * (1 / ((n - m : ℕ) : ℝ)) := by
            rw [hpow_comb]; ring
      calc
        ∑ n ∈ Finset.Ioc m (min (2 * m - 1) N), f m n
            ≤ ∑ n ∈ Finset.Ioc m (min (2 * m - 1) N),
                4 * (m : ℝ) ^ (1 - 2 * σ) * (1 / ((n - m : ℕ) : ℝ)) := Finset.sum_le_sum hterm
        _ = 4 * (m : ℝ) ^ (1 - 2 * σ) *
              ∑ n ∈ Finset.Ioc m (min (2 * m - 1) N), (1 / ((n - m : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum]
        _ = 4 * (m : ℝ) ^ (1 - 2 * σ) *
              ∑ r ∈ Finset.image (fun n ↦ n - m) (Finset.Ioc m (min (2 * m - 1) N)),
                (1 : ℝ) / r := by
          congr 1
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_Ioc] at ha hb
          dsimp only at hab
          omega
        _ ≤ 4 * (m : ℝ) ^ (1 - 2 * σ) * ∑ r ∈ Finset.Icc 1 N, (1 : ℝ) / r := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ by positivity)) (by positivity)
          intro r hr
          simp only [Finset.mem_image, Finset.mem_Ioc] at hr
          rcases hr with ⟨n, hn, rfl⟩
          simp only [Finset.mem_Icc]
          omega
        _ ≤ 4 * (m : ℝ) ^ (1 - 2 * σ) * (1 + Real.log N) := by
          gcongr
          exact harmonic_Icc_one_le hN
        _ = 4 * (1 + Real.log N) * (m : ℝ) ^ (1 - 2 * σ) := by ring
    have hdisj : Disjoint (Finset.Ioc m (min (2 * m - 1) N)) (Finset.Icc (2 * m) N) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_Ioc] at hn1
      simp only [Finset.mem_Icc] at hn2
      omega
    calc
      ∑ n ∈ Finset.Ioc m N, f m n
          ≤ ∑ n ∈ Finset.Ioc m (min (2 * m - 1) N) ∪ Finset.Icc (2 * m) N, f m n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsplit_n (fun _ _ _ ↦ by dsimp [f]; split_ifs <;> positivity)
      _ = ∑ n ∈ Finset.Ioc m (min (2 * m - 1) N), f m n + ∑ n ∈ Finset.Icc (2 * m) N, f m n :=
        Finset.sum_union hdisj
      _ ≤ 4 * (1 + Real.log N) * (m : ℝ) ^ (1 - 2 * σ) +
            (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) :=
        add_le_add h2_part h1_part
      _ = (2 / Real.log 2) * ((m : ℝ) ^ (-σ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) +
            4 * (1 + Real.log N) * (m : ℝ) ^ (1 - 2 * σ) := by ring
  rw [hdiag_split]
  calc
    2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ioc m N, f m n
        ≤ 2 * ∑ m ∈ Finset.Icc 1 N,
            ((2 / Real.log 2) * ((m : ℝ) ^ (-σ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) +
              4 * (1 + Real.log N) * (m : ℝ) ^ (1 - 2 * σ)) := by
      gcongr with m hm
      exact hinner_bd m hm
    _ = (4 / Real.log 2) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ)) ^ 2 +
          8 * (1 + Real.log N) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

private lemma log_le_inv_eps_rpow {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 ≤ u) :
    Real.log u ≤ (1 / ε) * u ^ ε := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h1 : Real.log (u ^ ε) ≤ u ^ ε - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu_pos ε)
  rw [Real.log_rpow hu_pos] at h1
  have h2 : ε * Real.log u ≤ u ^ ε := by linarith
  have h3 : Real.log u ≤ u ^ ε / ε := (le_div_iff₀ hε).mpr (by linarith)
  simpa [div_eq_mul_inv, mul_comm] using h3

private lemma tendsto_rpow_sub_one_div_self {γ : ℝ} (hγ : γ < 1) :
    Tendsto (fun T : ℝ ↦ (T + 1) ^ γ / T) atTop (𝓝 0) := by
  have hpow : Tendsto (fun T : ℝ ↦ (T + 1) ^ (γ - 1)) atTop (𝓝 0) :=
    ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - γ)).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)).congr fun T ↦ by
      dsimp; rw [show -(1 - γ) = γ - 1 by ring]
  have hratio : Tendsto (fun T : ℝ ↦ (T + 1) / T) atTop (𝓝 1) := by
    have h1 : Tendsto (fun T : ℝ ↦ (1 : ℝ) + 1 / T) atTop (𝓝 (1 + 0)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp [hT.ne']
  have hmul := hpow.mul hratio
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTp1 : 0 < T + 1 := by linarith
  have hadd : (T + 1) ^ (γ - 1) * (T + 1) = (T + 1) ^ γ := by
    rw [← Real.rpow_add_one hTp1.ne']
    congr 1; ring
  calc
    (T + 1) ^ (γ - 1) * ((T + 1) / T) = ((T + 1) ^ (γ - 1) * (T + 1)) / T := by ring
    _ = (T + 1) ^ γ / T := by rw [hadd]

lemma continuous_dirichletPoly_one (N : ℕ) (σ : ℝ) :
    Continuous fun t : ℝ ↦ dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I) := by
  induction N with
  | zero =>
    have h0 : (fun t : ℝ ↦ dirichletPoly (fun _ ↦ 1) 0 ((σ : ℂ) + (t : ℂ) * I)) = fun _ ↦ 0 := by
      ext t; simp [dirichletPoly]
    rw [h0]
    exact continuous_const
  | succ N ih =>
    have hsplit : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    have hfn : (fun t : ℝ ↦ dirichletPoly (fun _ ↦ 1) (N + 1) ((σ : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ ((N + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) +
          dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I) := by
      ext t
      simp only [dirichletPoly, hsplit, Finset.sum_insert hnot, one_mul]
    rw [hfn]
    have hne : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
    have hterm : Continuous fun t : ℝ ↦ ((N + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
      have heq : (fun t : ℝ ↦ ((N + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) =
          fun t : ℝ ↦ Complex.exp (Complex.log ((N + 1 : ℕ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))) := by
        ext t; rw [Complex.cpow_def_of_ne_zero hne]
      rw [heq]
      fun_prop
    exact hterm.add ih

private lemma continuousOn_riemannZeta_Icc {σ a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + (t : ℂ) * I)) (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 ≤ t := ha.trans ht.1
  have hne1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hlin : Continuous fun u : ℝ ↦ (σ : ℂ) + (u : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hz : ContinuousAt riemannZeta ((σ : ℂ) + (t : ℂ) * I) :=
    (differentiableAt_riemannZeta hne1).continuousAt
  exact (hz.comp_of_eq (hlin.continuousAt (x := t)) rfl).continuousWithinAt

lemma continuous_riemannZeta_half :
    Continuous fun t : ℝ ↦ riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne1 : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
    have hre := congrArg Complex.re h
    simp at hre
  have hlin : Continuous fun u : ℝ ↦ (1 / 2 : ℂ) + (u : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hz : ContinuousAt riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    (differentiableAt_riemannZeta hne1).continuousAt
  exact hz.comp_of_eq (hlin.continuousAt (x := t)) rfl

private lemma dirichletPoly_even_integral (N : ℕ) (σ : ℝ) {T : ℝ} :
    ∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      2 * ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hcont_poly : Continuous fun t : ℝ ↦
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    Continuous.pow (continuous_dirichletPoly_one N σ).norm 2
  have heven : ∀ t : ℝ,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (-t : ℂ) * I)‖ ^ 2 =
        ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t
    have hconj : dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (-t : ℂ) * I) =
        conj (dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)) := by
      simp only [dirichletPoly, one_mul, map_sum]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp only [Finset.mem_Icc] at hn; omega)
      rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj]
      congr 1
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
      simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hconj, Complex.norm_conj]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont_poly.intervalIntegrable (μ := volume) (-T) 0)
    (hcont_poly.intervalIntegrable (μ := volume) 0 T)
  rw [← hsplit]
  have href : ∫ t in (-T)..0, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    calc
      ∫ t in (-T)..0, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
          = ∫ t in (-T)..(-0), ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
        rw [neg_zero]
      _ = ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 2 :=
        (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
          (f := fun t : ℝ ↦ ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)).symm
      _ = ∫ t in (0 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_congr fun t _ ↦ by simpa only [Complex.ofReal_neg] using heven t
  rw [href, two_mul]

private lemma dirichletPoly_half_gt_diff_le {σ α β : ℝ} (hσ : 1 / 2 < σ)
    (hα_nn : 0 ≤ α) (hα_lt1 : α < 1) (hα_le : α ≤ σ) (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (hβ_le : β ≤ 2 * σ - 1) {T : ℝ} (hT : 1 ≤ T) :
    |(1 / T) * (∫ t in (1 : ℝ)..T,
          ‖dirichletPoly (fun _ ↦ 1) (Nat.floor T + 1) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        ∑ n ∈ Finset.Icc 1 (Nat.floor T + 1), (n : ℝ) ^ (-2 * σ)| ≤
      (2 / Real.log 2) * (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 / T +
        (4 * (1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β)) / T +
          (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 / T) := by
  have hT_pos : 0 < T := by linarith
  have hTp1 : 1 ≤ T + 1 := by linarith
  let N : ℕ := Nat.floor T + 1
  have hN1 : 1 ≤ N := Nat.succ_pos _
  have hN_le : (N : ℝ) ≤ T + 1 := by
    have := Nat.floor_le (by linarith : 0 ≤ T)
    push_cast [N]
    linarith
  have hcont_poly : Continuous fun t : ℝ ↦
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    Continuous.pow (continuous_dirichletPoly_one N σ).norm 2
  have hsum_alpha : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ) ≤
      1 + (T + 1) ^ (1 - α) / (1 - α) := by
    calc
      ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ)
          ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-α) := by
        refine Finset.sum_le_sum fun m hm ↦ ?_
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Finset.mem_Icc.mp hm).1) (by linarith)
      _ ≤ 1 + (N : ℝ) ^ (1 - α) / (1 - α) :=
        sum_Icc_one_rpow_neg_le hα_nn hα_lt1 N hN1
      _ ≤ 1 + (T + 1) ^ (1 - α) / (1 - α) := by
        gcongr
  have hsum_beta : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) ≤
      1 + (T + 1) ^ (1 - β) / (1 - β) := by
    calc
      ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ)
          ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-β) := by
        refine Finset.sum_le_sum fun m hm ↦ ?_
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Finset.mem_Icc.mp hm).1) (by linarith)
      _ ≤ 1 + (N : ℝ) ^ (1 - β) / (1 - β) :=
        sum_Icc_one_rpow_neg_le hβ_pos.le hβ_lt1 N hN1
      _ ≤ 1 + (T + 1) ^ (1 - β) / (1 - β) := by
        gcongr
  have hlogN_bd : 1 + Real.log (N : ℝ) ≤ 1 + (2 / β) * (T + 1) ^ (β / 2) := by
    have hlog1 : Real.log (N : ℝ) ≤ Real.log (T + 1) :=
      Real.log_le_log (by positivity) hN_le
    have hlog2 := log_le_inv_eps_rpow (half_pos hβ_pos) hTp1
    rw [one_div_div] at hlog2
    linarith
  have hoff := offDiag_dirichlet_sum_bound_of_ge_half (by linarith : 1 / 2 ≤ σ) N hN1
  have hpoly_symm := integral_norm_sq_dirichletPoly_sub_diag_le (fun _ ↦ 1) N σ T
  simp only [norm_one, one_pow, one_mul, mul_one] at hpoly_symm
  have hoff_div :
      ‖(∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)‖ / (2 * T) ≤
        (2 / Real.log 2) * (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 / T +
          4 * (1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β)) / T := by
    have h1_le : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ)) ^ 2 ≤
        (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 := by
      have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ) :=
        Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact pow_le_pow_left₀ hnn hsum_alpha 2
    have h2_le : (1 + Real.log (N : ℝ)) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) ≤
        (1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β)) := by
      have hsum_nn : 0 ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) :=
        Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact mul_le_mul hlogN_bd hsum_beta hsum_nn (by positivity)
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hnum_le :
        ‖(∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
            2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)‖ ≤
          (4 / Real.log 2) * (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 +
            8 * ((1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β))) := by
      have hterm1 : (4 / Real.log 2) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-σ)) ^ 2 ≤
          (4 / Real.log 2) * (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1_le (by positivity)
      have hterm2 : 8 * (1 + Real.log (N : ℝ)) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * σ) ≤
          8 * ((1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β))) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h2_le (by norm_num)
      linarith [hpoly_symm, hoff, hterm1, hterm2]
    calc
      _ ≤ ((4 / Real.log 2) * (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 +
            8 * ((1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β)))) / (2 * T) :=
        div_le_div_of_nonneg_right hnum_le (by linarith)
      _ = _ := by ring
  have hint_01_le : (∫ t in (0 : ℝ)..1,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T ≤
        (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 / T := by
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 := fun t _ ↦ by
      have hnorm : ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := by
        calc
          ‖∑ n ∈ Finset.Icc 1 N, (1 : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
              ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ := by
            simpa only [one_mul] using norm_sum_le _ _
          _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := by
            refine Finset.sum_congr rfl fun n hn ↦ ?_
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
            rw [Complex.norm_natCast_cpow_of_pos hn1]
            simp
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hsum_alpha) 2
    have hint_le : ∫ t in (0 : ℝ)..1,
        ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 := by
      have hconst : ∫ _ in (0 : ℝ)..1, (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 =
          (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 := by
        simp [intervalIntegral.integral_const]
      rw [← hconst]
      exact intervalIntegral.integral_mono_on (by norm_num) (hcont_poly.intervalIntegrable 0 1)
        intervalIntegrable_const hpt
    exact div_le_div_of_nonneg_right hint_le hT_pos.le
  have hint_01_nn : 0 ≤ ∫ t in (0 : ℝ)..1,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ sq_nonneg _
  have hsplit_0T : ∫ t in (0 : ℝ)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      (∫ t in (0 : ℝ)..1, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
        ∫ t in (1 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont_poly.intervalIntegrable (μ := volume) 0 1)
      (hcont_poly.intervalIntegrable (μ := volume) 1 T)).symm
  have heq_main :
      (1 / T) * (∫ t in (1 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) =
        ((∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
            2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)) / (2 * T) -
          (∫ t in (0 : ℝ)..1, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T := by
    have halg : ∀ a b c : ℝ, (1 / T) * b - c = (2 * (a + b) - 2 * T * c) / (2 * T) - a / T := by
      intro a b c; field_simp [hT_pos.ne']; ring
    rw [dirichletPoly_even_integral N σ, hsplit_0T]
    exact halg
      (∫ t in (0 : ℝ)..1, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (∫ t in (1 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ))
  rw [heq_main]
  have hsub := abs_sub
    (((∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)) / (2 * T))
    ((∫ t in (0 : ℝ)..1, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T)
  rw [abs_div, abs_of_pos (by linarith : 0 < 2 * T),
    abs_of_nonneg (div_nonneg hint_01_nn hT_pos.le),
    ← Real.norm_eq_abs ((∫ t in (-T)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ))] at hsub
  linarith [hsub, hoff_div, hint_01_le]

private lemma tendsto_mean_sq_dirichletPoly_of_half_lt {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun T : ℝ ↦ (1 / T) * ∫ t in (1 : ℝ)..T,
        ‖dirichletPoly (fun _ ↦ 1) (Nat.floor T + 1) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * σ))) := by
  let S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * σ)
  have hsumm_S : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-2 * σ) := by
    have h := Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * σ)
    refine (summable_nat_add_iff 1).mpr h |>.congr fun n ↦ ?_
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg _), neg_mul]
    push_cast
    rfl
  let α : ℝ := min σ (3 / 4)
  have hα_half : 1 / 2 < α := lt_min hσ (by norm_num)
  have hα_lt1 : α < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hα_le : α ≤ σ := min_le_left _ _
  let β : ℝ := min (2 * σ - 1) (1 / 2)
  have hβ_pos : 0 < β := lt_min (by linarith) (by norm_num)
  have hβ_lt1 : β < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hβ_le : β ≤ 2 * σ - 1 := min_le_left _ _
  let rem1 : ℝ → ℝ := fun T ↦
    (2 / Real.log 2) * (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 / T
  let rem2 : ℝ → ℝ := fun T ↦
    4 * (1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β)) / T
  let rem3 : ℝ → ℝ := fun T ↦
    (1 + (T + 1) ^ (1 - α) / (1 - α)) ^ 2 / T
  have hlim_rem1 : Tendsto rem1 atTop (𝓝 0) := by
    have hdom : Tendsto (fun T : ℝ ↦
        (4 / Real.log 2) * ((1 : ℝ) / T) +
          (4 / (Real.log 2 * (1 - α) ^ 2)) * ((T + 1) ^ (2 * (1 - α)) / T)) atTop (𝓝 0) := by
      have h0 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id
      have h1 := tendsto_rpow_sub_one_div_self (by linarith : 2 * (1 - α) < 1)
      have hsum := (h0.const_mul (4 / Real.log 2)).add
        (h1.const_mul (4 / (Real.log 2 * (1 - α) ^ 2)))
      simpa using hsum
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT_pos : 0 < T := by linarith
      have hTp1 : 0 < T + 1 := by linarith
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      let X : ℝ := (T + 1) ^ (1 - α) / (1 - α)
      have hsq : (1 + X) ^ 2 ≤ 2 + 2 * X ^ 2 := by nlinarith [sq_nonneg (1 - X)]
      have hXsq : X ^ 2 = (T + 1) ^ (2 * (1 - α)) / (1 - α) ^ 2 := by
        dsimp [X]
        rw [div_pow, ← Real.rpow_natCast ((T + 1) ^ (1 - α)) 2, ← Real.rpow_mul hTp1.le]
        congr 2; ring
      dsimp only [rem1]
      calc
        (2 / Real.log 2) * (1 + X) ^ 2 / T
            ≤ (2 / Real.log 2) * (2 + 2 * X ^ 2) / T := by gcongr
        _ = (4 / Real.log 2) * ((1 : ℝ) / T) +
              (4 / (Real.log 2 * (1 - α) ^ 2)) * ((T + 1) ^ (2 * (1 - α)) / T) := by
          rw [hXsq]; field_simp [hlog2.ne', show (1 - α) ≠ 0 by linarith, hT_pos.ne']; ring
  have hlim_rem3 : Tendsto rem3 atTop (𝓝 0) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have heq : rem3 = fun T ↦ (Real.log 2 / 2) * rem1 T := by
      ext T; dsimp only [rem3, rem1]; field_simp [hlog2.ne']
    rw [heq]
    simpa using hlim_rem1.const_mul (Real.log 2 / 2)
  have hlim_rem2 : Tendsto rem2 atTop (𝓝 0) := by
    have hdom : Tendsto (fun T : ℝ ↦
        4 * ((1 : ℝ) / T) + (8 / β) * ((T + 1) ^ (β / 2) / T) +
          (4 / (1 - β)) * ((T + 1) ^ (1 - β) / T) +
          (8 / (β * (1 - β))) * ((T + 1) ^ (1 - β / 2) / T)) atTop (𝓝 0) := by
      have h0 := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id).const_mul 4
      have h1 := (tendsto_rpow_sub_one_div_self (by linarith : β / 2 < 1)).const_mul (8 / β)
      have h2 := (tendsto_rpow_sub_one_div_self (by linarith : 1 - β < 1)).const_mul (4 / (1 - β))
      have h3 := (tendsto_rpow_sub_one_div_self (by linarith : 1 - β / 2 < 1)).const_mul
        (8 / (β * (1 - β)))
      simpa using ((h0.add h1).add h2).add h3
    refine hdom.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hTp1 : 0 < T + 1 := by linarith
    have hpow_mul : (T + 1) ^ (β / 2) * (T + 1) ^ (1 - β) = (T + 1) ^ (1 - β / 2) := by
      rw [← Real.rpow_add hTp1]
      congr 1; ring
    dsimp only [rem2]
    calc
      4 * ((1 : ℝ) / T) + (8 / β) * ((T + 1) ^ (β / 2) / T) +
          (4 / (1 - β)) * ((T + 1) ^ (1 - β) / T) +
          (8 / (β * (1 - β))) * ((T + 1) ^ (1 - β / 2) / T)
          = (4 + (8 / β) * (T + 1) ^ (β / 2) + (4 / (1 - β)) * (T + 1) ^ (1 - β) +
              (8 / (β * (1 - β))) * ((T + 1) ^ (β / 2) * (T + 1) ^ (1 - β))) / T := by
        rw [hpow_mul]; ring
      _ = 4 * (1 + (2 / β) * (T + 1) ^ (β / 2)) * (1 + (T + 1) ^ (1 - β) / (1 - β)) / T := by
        field_simp [show β ≠ 0 by linarith, show 1 - β ≠ 0 by linarith]; ring
  have hpartial_lim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)) atTop (𝓝 S) := by
    refine hsumm_S.hasSum.tendsto_sum_nat.congr fun N ↦ ?_
    refine Finset.sum_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
    · intro a _ b _ h; omega
    · intro b hb; simp only [Finset.mem_Icc] at hb; exact ⟨b - 1, by simp; omega, by omega⟩
    · intro n _; rw [Nat.cast_add, Nat.cast_one]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hpartial_lim) (ε / 2) (by linarith)
  obtain ⟨T₁, hT₁⟩ := (Metric.tendsto_atTop.mp (hlim_rem1.add (hlim_rem2.add hlim_rem3)))
    (ε / 2) (by linarith)
  refine ⟨max (max (N₀ : ℝ) 1) T₁, fun T hT ↦ ?_⟩
  have hT_ge1 : 1 ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hT_N0 : (N₀ : ℝ) ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hT_T1 : T₁ ≤ T := le_trans (le_max_right _ _) hT
  have hT_pos : 0 < T := by linarith
  let N : ℕ := Nat.floor T + 1
  have hNT_lt : T < (N : ℝ) := by
    push_cast [N]
    exact Nat.lt_floor_add_one T
  have hN_ge_N0 : N₀ ≤ N := by
    have : (N₀ : ℝ) < (N : ℝ) := lt_of_le_of_lt hT_N0 hNT_lt
    exact_mod_cast this.le
  have hdiff_bd : |(1 / T) * (∫ t in (1 : ℝ)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)| ≤ rem1 T + (rem2 T + rem3 T) :=
    dirichletPoly_half_gt_diff_le hσ (by linarith : 0 ≤ α) hα_lt1 hα_le hβ_pos hβ_lt1 hβ_le hT_ge1
  have hrem_bd : rem1 T + (rem2 T + rem3 T) < ε / 2 := by
    have hlt := hT₁ T hT_T1
    rw [Real.dist_eq, add_zero, add_zero, sub_zero, abs_of_nonneg] at hlt
    · exact hlt
    · have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hr1 : 0 ≤ rem1 T := by positivity
      have hr2 : 0 ≤ rem2 T := by
        dsimp only [rem2]
        exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
          (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))) hT_pos.le
      have hr3 : 0 ≤ rem3 T := by positivity
      linarith
  have hdiag_bd : |∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) - S| < ε / 2 := by
    have h := hN₀ N hN_ge_N0
    rw [Real.dist_eq] at h
    exact h
  rw [Real.dist_eq]
  have htri1 : |(1 / T) * (∫ t in (1 : ℝ)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - S| ≤
      |(1 / T) * (∫ t in (1 : ℝ)..T, ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)| +
        |∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) - S| :=
    abs_sub_le ((1 / T) * (∫ t in (1 : ℝ)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2))
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)) S
  linarith

/-- Mean-square theorem on `[1, T]` for `riemannZeta` on every vertical line `σ > 1 / 2`
(including `σ = 1`):
`(1 / T) ∫ t in 1..T, ‖riemannZeta (σ + t * I)‖ ^ 2 → ∑' n : ℕ, (n + 1 : ℝ) ^ (-2 * σ)`. -/
theorem tendsto_mean_sq_riemannZeta_Icc_one_of_half_lt {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun T : ℝ ↦ (1 / T) *
        ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * σ))) := by
  let S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * σ)
  have hS_nn : 0 ≤ S := tsum_nonneg fun n ↦ Real.rpow_nonneg (by positivity) _
  have hc2pi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.two_le_pi]
  obtain ⟨K, hK_pos, happrox⟩ := riemannZeta_approx_dirichletPoly_sub_bound zero_lt_one hc2pi
  have hrem_zero : Tendsto (fun T : ℝ ↦ (1 / T) * ∫ t in (1 : ℝ)..T,
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
        dirichletPoly (fun _ ↦ 1) (Nat.floor T + 1) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 0) := by
    let γ : ℝ := max (2 - 2 * σ) 0
    have hγ_nn : 0 ≤ γ := le_max_right _ _
    have hγ_lt1 : γ < 1 := max_lt (by linarith) zero_lt_one
    have hdom : Tendsto (fun T : ℝ ↦
        2 * ((T + 1) ^ γ / T) + (2 * K ^ 2) * T ^ (-2 * σ)) atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_sub_one_div_self hγ_lt1).const_mul 2
      have h2 := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * σ)).const_mul (2 * K ^ 2)
      simpa using h1.add h2
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hT fun _ _ ↦ sq_nonneg _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT_pos : 0 < T := by linarith
      let N : ℕ := Nat.floor T + 1
      have hN1 : 1 ≤ N := Nat.succ_pos _
      have hNT_lt : T < (N : ℝ) := by
        push_cast [N]
        exact Nat.lt_floor_add_one T
      have hN_le : (N : ℝ) ≤ T + 1 := by
        have := Nat.floor_le (by linarith : 0 ≤ T)
        push_cast [N]
        linarith
      have hN_pow1 : (N : ℝ) ^ (2 - 2 * σ) ≤ (T + 1) ^ γ := by
        calc
          (N : ℝ) ^ (2 - 2 * σ) ≤ (N : ℝ) ^ γ :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (le_max_left _ _)
          _ ≤ (T + 1) ^ γ := Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le hγ_nn
      have hN_pow2 : (N : ℝ) ^ (-2 * σ) ≤ T ^ (-2 * σ) :=
        Real.rpow_le_rpow_of_nonpos hT_pos hNT_lt.le (by linarith)
      have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T,
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
              dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
            2 * (N : ℝ) ^ (2 - 2 * σ) * t ^ (-2 : ℝ) + 2 * K ^ 2 * (N : ℝ) ^ (-2 * σ) := by
        intro t ht
        have ht1 : 1 ≤ |t| := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1
        have htN : |t| ≤ (1 : ℝ) * (N : ℝ) := by
          rw [one_mul, abs_of_nonneg (by linarith [ht.1])]
          exact ht.2.trans hNT_lt.le
        have hbd := happrox hN1 (by linarith : 0 < σ) ht1 htN
        rw [abs_of_nonneg (by linarith [ht.1])] at hbd
        have hsq : ((N : ℝ) ^ (1 - σ) / t + K * (N : ℝ) ^ (-σ)) ^ 2 ≤
            2 * ((N : ℝ) ^ (1 - σ) / t) ^ 2 + 2 * (K * (N : ℝ) ^ (-σ)) ^ 2 := by
          nlinarith [sq_nonneg ((N : ℝ) ^ (1 - σ) / t - K * (N : ℝ) ^ (-σ))]
        have h1 : ((N : ℝ) ^ (1 - σ) / t) ^ 2 = (N : ℝ) ^ (2 - 2 * σ) * t ^ (-2 : ℝ) := by
          rw [div_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 - σ)) 2,
            ← Real.rpow_mul (Nat.cast_nonneg N), div_eq_mul_inv,
            ← Real.rpow_natCast t 2, ← Real.rpow_neg (by linarith [ht.1] : 0 ≤ t)]
          congr 2; ring
        have h2 : (K * (N : ℝ) ^ (-σ)) ^ 2 = K ^ 2 * (N : ℝ) ^ (-2 * σ) := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (-σ)) 2,
            ← Real.rpow_mul (Nat.cast_nonneg N)]
          congr 2; ring
        have hsq0 : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
            ((N : ℝ) ^ (1 - σ) / t + K * (N : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hbd 2
        linarith [hsq0, hsq, h1, h2]
      have hdiff_int : IntervalIntegrable (fun t : ℝ ↦
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
        (((continuousOn_riemannZeta_Icc (σ := σ) (b := T) le_rfl).sub
          (continuous_dirichletPoly_one N σ).continuousOn).norm.pow 2).intervalIntegrable_of_Icc hT
      have hrhs_int1 : IntervalIntegrable (fun t : ℝ ↦
          2 * (N : ℝ) ^ (2 - 2 * σ) * t ^ (-2 : ℝ)) volume 1 T :=
        (continuousOn_const.mul
          (continuousOn_id.rpow_const fun t ht ↦ Or.inl (by dsimp; linarith [ht.1]))).intervalIntegrable_of_Icc hT
      have hint_mono : ∫ t in (1 : ℝ)..T,
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          2 * (N : ℝ) ^ (2 - 2 * σ) * (1 - T ^ (-1 : ℝ)) +
            2 * K ^ 2 * (N : ℝ) ^ (-2 * σ) * (T - 1) := by
        have hle := intervalIntegral.integral_mono_on hT hdiff_int
          (hrhs_int1.add intervalIntegrable_const) hpt
        have hrpow_eval : ∫ t in (1 : ℝ)..T, t ^ (-2 : ℝ) = 1 - T ^ (-1 : ℝ) := by
          rw [integral_rpow (Or.inr ⟨by norm_num, fun h ↦ by
            rw [Set.uIcc_of_le hT] at h; linarith [h.1]⟩)]
          simp only [Real.one_rpow, show (-2 : ℝ) + 1 = -1 by norm_num]
          ring
        rw [intervalIntegral.integral_add hrhs_int1 intervalIntegrable_const,
          intervalIntegral.integral_const_mul, hrpow_eval, intervalIntegral.integral_const,
          smul_eq_mul] at hle
        linarith
      have h1mT : 1 - T ^ (-1 : ℝ) ≤ 1 := by
        have hpow_nn : 0 ≤ T ^ (-1 : ℝ) := Real.rpow_nonneg hT_pos.le _
        linarith
      have hTm1 : T - 1 ≤ T := by linarith
      calc
        (1 / T) * ∫ t in (1 : ℝ)..T,
            ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
              dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
            ≤ (1 / T) * (2 * (N : ℝ) ^ (2 - 2 * σ) * 1 +
                2 * K ^ 2 * (N : ℝ) ^ (-2 * σ) * T) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 : 2 * (N : ℝ) ^ (2 - 2 * σ) * (1 - T ^ (-1 : ℝ)) ≤ 2 * (N : ℝ) ^ (2 - 2 * σ) * 1 :=
            mul_le_mul_of_nonneg_left h1mT (by positivity)
          have h2 : 2 * K ^ 2 * (N : ℝ) ^ (-2 * σ) * (T - 1) ≤ 2 * K ^ 2 * (N : ℝ) ^ (-2 * σ) * T :=
            mul_le_mul_of_nonneg_left hTm1 (by positivity)
          linarith
        _ ≤ (1 / T) * (2 * (T + 1) ^ γ * 1 + 2 * K ^ 2 * T ^ (-2 * σ) * T) := by
          gcongr
        _ = 2 * ((T + 1) ^ γ / T) + (2 * K ^ 2) * T ^ (-2 * σ) := by
          field_simp [hT_pos.ne']
  have hpoly_lim := tendsto_mean_sq_dirichletPoly_of_half_lt hσ
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := min (1 / 2) (ε / (8 * max S 1))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδS1 : δ * S ≤ ε / 8 := by
    calc
      δ * S ≤ (ε / (8 * max S 1)) * max S 1 :=
        mul_le_mul (min_le_right _ _) (le_max_left _ _) hS_nn (by positivity)
      _ = ε / 8 := by
        have hmax : max S 1 ≠ 0 := by positivity
        field_simp [hmax]
  have hδS2 : (δ / (1 + δ)) * S ≤ ε / 8 := by
    calc
      (δ / (1 + δ)) * S ≤ δ * S :=
        mul_le_mul_of_nonneg_right (div_le_self hδ_pos.le (by linarith)) hS_nn
      _ ≤ ε / 8 := hδS1
  obtain ⟨T₁, hT₁⟩ := (Metric.tendsto_atTop.mp hpoly_lim) (ε / 4) (by linarith)
  obtain ⟨T₂, hT₂⟩ := (Metric.tendsto_atTop.mp hrem_zero)
    (ε / (4 * (1 + δ⁻¹))) (by positivity)
  refine ⟨max (max 1 T₁) T₂, fun T hT ↦ ?_⟩
  have hT_ge1 : 1 ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hT_T1 : T₁ ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hT_T2 : T₂ ≤ T := le_trans (le_max_right _ _) hT
  have hT_pos : 0 < T := by linarith
  let N : ℕ := Nat.floor T + 1
  let IZ : ℝ := (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  let ID : ℝ := (1 / T) * ∫ t in (1 : ℝ)..T,
    ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  let IR : ℝ := (1 / T) * ∫ t in (1 : ℝ)..T,
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
      dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  have hIZ_int : IntervalIntegrable
      (fun t : ℝ ↦ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    ((continuousOn_riemannZeta_Icc (σ := σ) (b := T) le_rfl).norm.pow 2).intervalIntegrable_of_Icc hT_ge1
  have hID_int : IntervalIntegrable
      (fun t : ℝ ↦ ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    ((continuous_dirichletPoly_one N σ).norm.pow 2).continuousOn.intervalIntegrable_of_Icc hT_ge1
  have hIR_int : IntervalIntegrable (fun t : ℝ ↦
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
        dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    (((continuousOn_riemannZeta_Icc (σ := σ) (b := T) le_rfl).sub
      (continuous_dirichletPoly_one N σ).continuousOn).norm.pow 2).intervalIntegrable_of_Icc hT_ge1
  have hyoung : ∀ a b : ℂ,
      ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 := by
    intro a b
    have htri : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    have hsq : 0 ≤ δ * ((1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 - (‖a‖ + ‖b‖) ^ 2) := by
      have hid : δ * ((1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 - (‖a‖ + ‖b‖) ^ 2) =
          (δ * ‖a‖ - ‖b‖) ^ 2 := by
        field_simp [hδ_pos.ne']
        ring
      rw [hid]
      exact sq_nonneg _
    have hle := nonneg_of_mul_nonneg_right hsq hδ_pos
    linarith
  have hupper_pt : ∀ t ∈ Set.Icc (1 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        (1 + δ) * ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          (1 + δ⁻¹) * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t _ ↦ by
    simpa [add_sub_cancel] using hyoung (dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I))
      (riemannZeta ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I))
  have hlower_pt : ∀ t ∈ Set.Icc (1 : ℝ) T,
      ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        (1 + δ) * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          (1 + δ⁻¹) * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t _ ↦ by
    have h := hyoung (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
      (-(riemannZeta ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)))
    rw [norm_neg] at h
    simpa using h
  have hupper : IZ ≤ (1 + δ) * ID + (1 + δ⁻¹) * IR := by
    have hint := intervalIntegral.integral_mono_on hT_ge1 hIZ_int
      ((hID_int.const_mul (1 + δ)).add (hIR_int.const_mul (1 + δ⁻¹))) hupper_pt
    rw [intervalIntegral.integral_add (hID_int.const_mul _) (hIR_int.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
    calc
      IZ = (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := rfl
      _ ≤ (1 / T) * ((1 + δ) * (∫ t in (1 : ℝ)..T,
            ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
          (1 + δ⁻¹) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
      _ = (1 + δ) * ID + (1 + δ⁻¹) * IR := by dsimp only [ID, IR]; ring
  have hlower : ID ≤ (1 + δ) * IZ + (1 + δ⁻¹) * IR := by
    have hint := intervalIntegral.integral_mono_on hT_ge1 hID_int
      ((hIZ_int.const_mul (1 + δ)).add (hIR_int.const_mul (1 + δ⁻¹))) hlower_pt
    rw [intervalIntegral.integral_add (hIZ_int.const_mul _) (hIR_int.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
    calc
      ID = (1 / T) * ∫ t in (1 : ℝ)..T,
            ‖dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := rfl
      _ ≤ (1 / T) * ((1 + δ) * (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
          (1 + δ⁻¹) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
      _ = (1 + δ) * IZ + (1 + δ⁻¹) * IR := by dsimp only [IZ, IR]; ring
  have hID_bd : |ID - S| < ε / 4 := by
    have h := hT₁ T hT_T1
    rw [Real.dist_eq] at h
    exact h
  have hIR_nn : 0 ≤ IR :=
    mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hT_ge1 fun _ _ ↦ sq_nonneg _)
  have hIR_bd : (1 + δ⁻¹) * IR < ε / 4 := by
    have hlt := hT₂ T hT_T2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hIR_nn] at hlt
    have hpos : 0 < 1 + δ⁻¹ := by positivity
    calc
      (1 + δ⁻¹) * IR < (1 + δ⁻¹) * (ε / (4 * (1 + δ⁻¹))) :=
        mul_lt_mul_of_pos_left hlt hpos
      _ = ε / 4 := by field_simp [hpos.ne']
  have hupper_S : IZ - S < ε := by
    have hID_le : ID - S ≤ ε / 4 := by linarith [(abs_lt.mp hID_bd).2]
    have hmul : (1 + δ) * (ID - S) ≤ (1 + δ) * (ε / 4) := by gcongr
    have h32 : (1 + δ) * (ε / 4) ≤ (3 / 2 : ℝ) * (ε / 4) := by gcongr; linarith
    calc
      IZ - S ≤ (1 + δ) * ID + (1 + δ⁻¹) * IR - S := by linarith
      _ = (1 + δ) * (ID - S) + δ * S + (1 + δ⁻¹) * IR := by ring
      _ ≤ (3 / 2 : ℝ) * (ε / 4) + ε / 8 + ε / 4 := by linarith
      _ < ε := by linarith
  have hlower_S : S - IZ < ε := by
    have h1pδ_pos : 0 < 1 + δ := by linarith
    have hlow' : ID - (1 + δ⁻¹) * IR ≤ (1 + δ) * IZ := by linarith
    have hdiv : (ID - (1 + δ⁻¹) * IR) / (1 + δ) ≤ IZ :=
      (div_le_iff₀ h1pδ_pos).mpr (by linarith)
    have hS_sub : S - ID ≤ ε / 4 := by linarith [(abs_lt.mp hID_bd).1]
    have hdiv1 : (S - ID) / (1 + δ) ≤ ε / 4 := by
      calc
        (S - ID) / (1 + δ) ≤ (ε / 4) / (1 + δ) := div_le_div_of_nonneg_right hS_sub h1pδ_pos.le
        _ ≤ (ε / 4) / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one (by linarith)
        _ = ε / 4 := div_one _
    have hdiv2 : ((1 + δ⁻¹) * IR) / (1 + δ) ≤ ε / 4 := by
      calc
        ((1 + δ⁻¹) * IR) / (1 + δ) ≤ (ε / 4) / (1 + δ) :=
          div_le_div_of_nonneg_right hIR_bd.le h1pδ_pos.le
        _ ≤ (ε / 4) / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one (by linarith)
        _ = ε / 4 := div_one _
    calc
      S - IZ ≤ S - (ID - (1 + δ⁻¹) * IR) / (1 + δ) := by linarith
      _ = (δ / (1 + δ)) * S + (S - ID) / (1 + δ) + ((1 + δ⁻¹) * IR) / (1 + δ) := by
        field_simp [h1pδ_pos.ne']; ring
      _ ≤ ε / 8 + ε / 4 + ε / 4 := by linarith
      _ < ε := by linarith
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, hupper_S⟩

/-- Mean-square theorem on `[-T, T]` for `riemannZeta` on every vertical line `σ > 1 / 2`
with `σ ≠ 1`, bridging `DirichletSeries.VerticalOrder` (`σ > 1`) into the critical strip
(`1 / 2 < σ < 1`):
`(1 / (2 * T)) ∫ t in (-T)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 → ∑' n : ℕ, (n : ℝ) ^ (-2 * σ)`. -/
theorem tendsto_mean_sq_riemannZeta_of_half_lt {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≠ 1) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * T)) *
        ∫ t in (-T)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, (n : ℝ) ^ (-2 * σ))) := by
  have htsum_eq : ∑' n : ℕ, (n : ℝ) ^ (-2 * σ) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * σ) := by
    have hsumm : Summable fun n : ℕ ↦ (n : ℝ) ^ (-2 * σ) := by
      have h := Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * σ)
      refine h.congr fun n ↦ ?_
      rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n), neg_mul]
    rw [Summable.tsum_eq_zero_add hsumm, Nat.cast_zero,
      Real.zero_rpow (by linarith : -2 * σ ≠ 0), zero_add]
    refine tsum_congr fun n ↦ ?_
    simp [Nat.cast_add, Nat.cast_one]
  rw [htsum_eq]
  have hcont : Continuous fun t : ℝ ↦ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have hlin : Continuous fun u : ℝ ↦ (σ : ℂ) + (u : ℂ) * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcz : Continuous fun t : ℝ ↦ riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hne1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
        have hre := congrArg Complex.re h
        simp at hre
        exact hσ1 hre
      have hz : ContinuousAt riemannZeta ((σ : ℂ) + (t : ℂ) * I) :=
        (differentiableAt_riemannZeta hne1).continuousAt
      exact hz.comp_of_eq (hlin.continuousAt (x := t)) rfl
    exact Continuous.pow hcz.norm 2
  have heven : ∀ t : ℝ,
      ‖riemannZeta ((σ : ℂ) + (-t : ℂ) * I)‖ ^ 2 =
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t ↦ by
    have hconj_arg : (σ : ℂ) + (-t : ℂ) * I = conj ((σ : ℂ) + (t : ℂ) * I) := by
      simp
    rw [hconj_arg, riemannZeta_conj, Complex.norm_conj]
  have hbase := tendsto_mean_sq_riemannZeta_Icc_one_of_half_lt hσ
  have hconst_zero : Tendsto (fun T : ℝ ↦
      (1 / T) * ∫ t in (0 : ℝ)..1, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ ↦
        (1 / T) * ∫ t in (0 : ℝ)..1, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        atTop (𝓝 (0 * ∫ t in (0 : ℝ)..1, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)) :=
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id).mul_const _
    rw [zero_mul] at h1
    exact h1
  have hsum := hconst_zero.add hbase
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT_pos : 0 < T := by linarith
  have hsplit_symm := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-T) 0)
    (hcont.intervalIntegrable (μ := volume) 0 T)
  have href : ∫ t in (-T)..0, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    calc
      ∫ t in (-T)..0, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
          = ∫ t in (-T)..(-0), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
        rw [neg_zero]
      _ = ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 2 :=
        (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
          (f := fun t : ℝ ↦ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)).symm
      _ = ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_congr fun t _ ↦ by simpa only [Complex.ofReal_neg] using heven t
  have hsplit_0T := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 1)
    (hcont.intervalIntegrable (μ := volume) 1 T)
  have halg : ∀ a b : ℝ, (1 / T) * a + (1 / T) * b = (1 / (2 * T)) * (2 * (a + b)) := by
    intro a b; field_simp [hT_pos.ne']
  have hadd_eq :
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
          ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
        2 * ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (two_mul _).symm
  rw [← hsplit_symm, href, hadd_eq, ← hsplit_0T]
  exact halg
    (∫ t in (0 : ℝ)..1, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)

private lemma poly_half_Icc_mean_sq_bound {T : ℝ} (hT : 1 ≤ T) :
    (1 / T) * ∫ t in (1 : ℝ)..T,
        ‖dirichletPoly (fun _ ↦ 1) (Nat.floor T + 1) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (2 + 36 / Real.log 2 + 16) * Real.log (T + 2) := by
  have hhalf_eq : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hcont_poly : ∀ N : ℕ, Continuous fun t : ℝ ↦
      ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun N ↦ by
    have hc : Continuous fun t : ℝ ↦
        ‖dirichletPoly (fun _ ↦ 1) N (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      (continuous_dirichletPoly_one N (1 / 2)).norm.pow 2
    simpa only [hhalf_eq] using hc
  have hlog3 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hT_pos : 0 < T := by linarith
  have hlog_ge1 : 1 ≤ Real.log (T + 2) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  let N : ℕ := Nat.floor T + 1
  have hN1 : 1 ≤ N := Nat.succ_pos _
  have hN_le : (N : ℝ) ≤ T + 1 := by
    have := Nat.floor_le (by linarith : 0 ≤ T)
    push_cast [N]
    linarith
  have hN_le_2T : (N : ℝ) ≤ 2 * T := by linarith
  have hlogN_le : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (T + 2) := by
    have hlog_le : Real.log (N : ℝ) ≤ Real.log (T + 2) := Real.log_le_log (by positivity) (by linarith)
    linarith
  have hsum_half : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      3 * Real.sqrt (T + 1) := by
    have hbd := sum_Icc_one_rpow_neg_le (α := 1 / 2) (by norm_num) (by norm_num) N hN1
    have hr1 : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [hr1] at hbd
    have hsqrt_le : (N : ℝ) ^ (1 / 2 : ℝ) ≤ Real.sqrt (T + 1) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hN_le
    have hsqrt_ge1 : 1 ≤ Real.sqrt (T + 1) := Real.one_le_sqrt.mpr (by linarith)
    linarith
  have hharm_bd : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) ≤ 2 * Real.log (T + 2) := by
    have heq : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [show (-2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
    rw [heq]
    exact (harmonic_Icc_one_le hN1).trans hlogN_le
  have hoff := offDiag_dirichlet_sum_bound_of_ge_half (σ := 1 / 2) le_rfl N hN1
  have hpoly_symm :
      ‖(∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 : ℝ))‖ ≤
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if m = n then 0 else
            2 * (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) / |Real.log n - Real.log m| := by
    have h := integral_norm_sq_dirichletPoly_sub_diag_le (fun _ ↦ 1) N (1 / 2) T
    simp only [norm_one, one_pow, one_mul, mul_one, hhalf_eq] at h
    exact h
  have h_even_poly : ∫ t in (-T)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      2 * ∫ t in (0 : ℝ)..T,
        ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    simpa only [hhalf_eq] using dirichletPoly_even_integral N (1 / 2) (T := T)
  have hint_01_nn : 0 ≤ ∫ t in (0 : ℝ)..1,
      ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ sq_nonneg _
  have hsplit_0T := intervalIntegral.integral_add_adjacent_intervals
    ((hcont_poly N).intervalIntegrable (μ := volume) 0 1)
    ((hcont_poly N).intervalIntegrable (μ := volume) 1 T)
  have hIcc_le : 2 * ∫ t in (1 : ℝ)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ∫ t in (-T)..T, ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    rw [h_even_poly, ← hsplit_0T]
    linarith
  have hdiag_le : ∫ t in (-T)..T,
      ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * T * (2 * Real.log (T + 2)) +
        ((4 / Real.log 2) * (9 * (T + 1)) + 8 * (2 * Real.log (T + 2)) * (N : ℝ)) := by
    have habs := (Real.norm_eq_abs _).le.trans hpoly_symm
    have hsub_le : (∫ t in (-T)..T,
        ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) ≤
        (4 / Real.log 2) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 +
          8 * (1 + Real.log N) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * (1 / 2 : ℝ)) :=
      (le_abs_self _).trans (habs.trans hoff)
    have hsum_sq : (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ 9 * (T + 1) := by
      have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc
        (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
            ≤ (3 * Real.sqrt (T + 1)) ^ 2 := pow_le_pow_left₀ hnn hsum_half 2
        _ = 9 * (Real.sqrt (T + 1)) ^ 2 := by ring
        _ = 9 * (T + 1) := by rw [Real.sq_sqrt (by linarith)]
    have hsum_zero : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (1 - 2 * (1 / 2 : ℝ)) = N := by
      simp [Nat.card_Icc]
    rw [hsum_zero] at hsub_le
    have h1 : 2 * T * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) ≤
        2 * T * (2 * Real.log (T + 2)) := by gcongr
    have h2 : (4 / Real.log 2) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤
        (4 / Real.log 2) * (9 * (T + 1)) := by gcongr
    have h3 : 8 * (1 + Real.log (N : ℝ)) * (N : ℝ) ≤ 8 * (2 * Real.log (T + 2)) * (N : ℝ) := by
      gcongr
    linarith
  have hT1_le : 9 * (T + 1) ≤ 18 * T := by linarith
  have h2_le : (4 / Real.log 2) * (9 * (T + 1)) ≤ (4 / Real.log 2) * (18 * T) :=
    mul_le_mul_of_nonneg_left hT1_le (by positivity)
  have hN_le' : 8 * (2 * Real.log (T + 2)) * (N : ℝ) ≤ 8 * (2 * Real.log (T + 2)) * (2 * T) :=
    mul_le_mul_of_nonneg_left hN_le_2T (by positivity)
  have h2T_pos : 0 < 2 * T := by linarith
  have halg1 : ∀ X : ℝ, (1 / T) * X = (2 * X) / (2 * T) := fun X ↦ by
    field_simp [hT_pos.ne']
  calc
    (1 / T) * ∫ t in (1 : ℝ)..T,
        ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        = (2 * ∫ t in (1 : ℝ)..T,
            ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) / (2 * T) :=
      halg1 _
    _ ≤ (2 * T * (2 * Real.log (T + 2)) +
          ((4 / Real.log 2) * (18 * T) + 8 * (2 * Real.log (T + 2)) * (2 * T))) / (2 * T) := by
      refine div_le_div_of_nonneg_right (by linarith [hIcc_le, hdiag_le, h2_le, hN_le']) h2T_pos.le
    _ = 2 * Real.log (T + 2) + (36 / Real.log 2) * 1 + 16 * Real.log (T + 2) := by
      have hfac : (2 * T * (2 * Real.log (T + 2)) +
            ((4 / Real.log 2) * (18 * T) + 8 * (2 * Real.log (T + 2)) * (2 * T))) =
          (2 * Real.log (T + 2) + (36 / Real.log 2) * 1 + 16 * Real.log (T + 2)) * (2 * T) := by
        ring
      rw [hfac, mul_div_cancel_right₀ _ h2T_pos.ne']
    _ ≤ 2 * Real.log (T + 2) + (36 / Real.log 2) * Real.log (T + 2) + 16 * Real.log (T + 2) := by
      have h36 : (36 / Real.log 2) * 1 ≤ (36 / Real.log 2) * Real.log (T + 2) :=
        mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
      linarith
    _ = (2 + 36 / Real.log 2 + 16) * Real.log (T + 2) := by ring

private lemma zeta_sub_poly_half_Icc_mean_sq_bound {K : ℝ} (hK_pos : 0 < K)
    (happrox : ∀ ⦃N : ℕ⦄, 1 ≤ N → ∀ ⦃σ t : ℝ⦄, 0 < σ → 1 ≤ |t| → |t| ≤ (1 : ℝ) * (N : ℝ) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly (fun _ ↦ 1) N ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        (N : ℝ) ^ (1 - σ) / |t| + K * (N : ℝ) ^ (-σ))
    {T : ℝ} (hT : 1 ≤ T) :
    (1 / T) * ∫ t in (1 : ℝ)..T,
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
          dirichletPoly (fun _ ↦ 1) (Nat.floor T + 1) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      4 + 2 * K ^ 2 := by
  have hhalf_eq : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hT_pos : 0 < T := by linarith
  let N : ℕ := Nat.floor T + 1
  have hN1 : 1 ≤ N := Nat.succ_pos _
  have hNT_lt : T < (N : ℝ) := by
    push_cast [N]
    exact Nat.lt_floor_add_one T
  have hN_le : (N : ℝ) ≤ T + 1 := by
    have := Nat.floor_le (by linarith : 0 ≤ T)
    push_cast [N]
    linarith
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T,
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
          dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        2 * (T + 1) * t ^ (-2 : ℝ) + 2 * K ^ 2 := by
    intro t ht
    have ht1 : 1 ≤ |t| := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1
    have htN : |t| ≤ (1 : ℝ) * (N : ℝ) := by
      rw [one_mul, abs_of_nonneg (by linarith [ht.1])]
      exact ht.2.trans hNT_lt.le
    have hbd := happrox (N := N) hN1 (σ := 1 / 2) (t := t) (by norm_num) ht1 htN
    rw [abs_of_nonneg (by linarith [ht.1]), hhalf_eq] at hbd
    have hNhalf : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by norm_num)
    have hNpow1 : ((N : ℝ) ^ (1 - (1 / 2 : ℝ))) ^ 2 = (N : ℝ) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 - (1 / 2 : ℝ))) 2,
        ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    have hbd' : ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
        dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        (N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t + K := by
      calc
        _ ≤ (N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t + K * (N : ℝ) ^ (-(1 / 2 : ℝ)) := hbd
        _ ≤ (N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t + K * 1 := by gcongr
        _ = (N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t + K := by ring
    have hsq : ((N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t + K) ^ 2 ≤
        2 * ((N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t) ^ 2 + 2 * K ^ 2 := by
      nlinarith [sq_nonneg ((N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t - K)]
    have h1 : ((N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t) ^ 2 = (N : ℝ) * t ^ (-2 : ℝ) := by
      rw [div_pow, hNpow1, div_eq_mul_inv, ← Real.rpow_natCast t 2,
        ← Real.rpow_neg (by linarith [ht.1] : 0 ≤ t)]
      simp only [Nat.cast_ofNat]
    have h2 : (N : ℝ) * t ^ (-2 : ℝ) ≤ (T + 1) * t ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hN_le (Real.rpow_nonneg (by linarith [ht.1]) _)
    have hsq0 : ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
        dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        ((N : ℝ) ^ (1 - (1 / 2 : ℝ)) / t + K) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd' 2
    linarith [hsq0, hsq, h1, h2]
  have hdiff_int : IntervalIntegrable (fun t : ℝ ↦
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
        dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T := by
    have hcp : ContinuousOn (fun t : ℝ ↦
        dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)) (Set.Icc 1 T) := by
      simpa only [hhalf_eq] using (continuous_dirichletPoly_one N (1 / 2)).continuousOn
    exact ((continuous_riemannZeta_half.continuousOn.sub hcp).norm.pow 2).intervalIntegrable_of_Icc hT
  have hrhs_int1 : IntervalIntegrable (fun t : ℝ ↦ 2 * (T + 1) * t ^ (-2 : ℝ)) volume 1 T :=
    (continuousOn_const.mul
      (continuousOn_id.rpow_const fun t ht ↦ Or.inl (by dsimp; linarith [ht.1]))).intervalIntegrable_of_Icc hT
  have hint_mono := intervalIntegral.integral_mono_on hT hdiff_int
    (hrhs_int1.add intervalIntegrable_const) hpt
  have hrpow_eval : ∫ t in (1 : ℝ)..T, t ^ (-2 : ℝ) = 1 - T ^ (-1 : ℝ) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, fun h ↦ by
      rw [Set.uIcc_of_le hT] at h; linarith [h.1]⟩)]
    simp only [Real.one_rpow, show (-2 : ℝ) + 1 = -1 by norm_num]
    ring
  rw [intervalIntegral.integral_add hrhs_int1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hrpow_eval, intervalIntegral.integral_const,
    smul_eq_mul] at hint_mono
  have h1mT : 1 - T ^ (-1 : ℝ) ≤ 1 := by
    have hpow_nn : 0 ≤ T ^ (-1 : ℝ) := Real.rpow_nonneg hT_pos.le _
    linarith
  calc
    (1 / T) * ∫ t in (1 : ℝ)..T,
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
          dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ (1 / T) * (2 * (T + 1) * 1 + 2 * K ^ 2 * T) := by
      have hle1 : 2 * (T + 1) * (1 - T ^ (-1 : ℝ)) ≤ 2 * (T + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1mT (by positivity)
      have hle2 : (T - 1) * (2 * K ^ 2) ≤ T * (2 * K ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * ((T + 1) / T) + 2 * K ^ 2 := by field_simp [hT_pos.ne']
    _ ≤ 2 * 2 + 2 * K ^ 2 := by
      have hdiv2 : (T + 1) / T ≤ 2 := (div_le_iff₀ hT_pos).mpr (by linarith)
      linarith
    _ = 4 + 2 * K ^ 2 := by norm_num

/-- The Dirichlet approximation of length `⌊T⌋+1` on the critical line has
bounded mean square error on `[1,T]`, with an absolute constant. -/
theorem mean_sq_zeta_sub_long_dirichletPoly_half :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I) -
        dirichletPoly (fun _ => 1) (⌊T⌋₊+1) ((1/2:ℂ)+t*I)‖^2) / T ≤ C := by
  obtain ⟨K,hK,H⟩ := riemannZeta_approx_dirichletPoly_sub_bound zero_lt_one
    (by linarith [Real.two_le_pi] : (1:ℝ) < 2*Real.pi)
  refine ⟨4+2*K^2,by positivity,fun {T} hT => ?_⟩
  simpa only [one_div,div_eq_inv_mul,mul_one] using zeta_sub_poly_half_Icc_mean_sq_bound hK H hT

/-- Critical-line mean-square upper bound on `[1, T]` (`σ = 1 / 2`):
`(1 / T) ∫ t in 1..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 ≤ C * Real.log (T + 2)` for `1 ≤ T`. -/
theorem mean_sq_riemannZeta_half_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃T : ℝ⦄, 1 ≤ T →
      (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * Real.log (T + 2) := by
  have hc2pi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.two_le_pi]
  obtain ⟨K, hK_pos, happrox⟩ := riemannZeta_approx_dirichletPoly_sub_bound zero_lt_one hc2pi
  have hhalf_eq : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hlog3 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let C : ℝ := 2 * (2 + 36 / Real.log 2 + 16 + (4 + 2 * K ^ 2))
  refine ⟨C, by positivity, fun T hT ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  have hlog_ge1 : 1 ≤ Real.log (T + 2) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  let N : ℕ := Nat.floor T + 1
  have hpoly_Icc := poly_half_Icc_mean_sq_bound hT
  have hrem_Icc := zeta_sub_poly_half_Icc_mean_sq_bound hK_pos happrox hT
  have hzeta_int : IntervalIntegrable
      (fun t : ℝ ↦ ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    (Continuous.pow continuous_riemannZeta_half.norm 2).intervalIntegrable 1 T
  have hcp : Continuous fun t : ℝ ↦
      dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    simpa only [hhalf_eq] using continuous_dirichletPoly_one N (1 / 2)
  have hD_int : IntervalIntegrable
      (fun t : ℝ ↦ ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    (Continuous.pow hcp.norm 2).intervalIntegrable 1 T
  have hR_int : IntervalIntegrable (fun t : ℝ ↦
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
        dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) volume 1 T :=
    (Continuous.pow (continuous_riemannZeta_half.sub hcp).norm 2).intervalIntegrable 1 T
  have hpt_z : ∀ t ∈ Set.Icc (1 : ℝ) T,
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        2 * ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          2 * ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
            dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t _ ↦ by
    let d := dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)
    let r := riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - d
    have htri : ‖d + r‖ ≤ ‖d‖ + ‖r‖ := norm_add_le d r
    have hpow : ‖d + r‖ ^ 2 ≤ (‖d‖ + ‖r‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hsq : ‖d + r‖ ^ 2 ≤ 2 * ‖d‖ ^ 2 + 2 * ‖r‖ ^ 2 := by nlinarith [sq_nonneg (‖d‖ - ‖r‖)]
    have hsum : d + r = riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) := by dsimp [r]; ring
    rwa [hsum] at hsq
  have hint_z := intervalIntegral.integral_mono_on hT hzeta_int
    ((hD_int.const_mul 2).add (hR_int.const_mul 2)) hpt_z
  rw [intervalIntegral.integral_add (hD_int.const_mul 2) (hR_int.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint_z
  calc
    (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ 2 * ((1 / T) * ∫ t in (1 : ℝ)..T,
            ‖dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) +
          2 * ((1 / T) * ∫ t in (1 : ℝ)..T,
            ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
              dirichletPoly (fun _ ↦ 1) N ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hint_z (by positivity : 0 ≤ 1 / T)
      linarith
    _ ≤ 2 * ((2 + 36 / Real.log 2 + 16) * Real.log (T + 2)) + 2 * (4 + 2 * K ^ 2) := by
      gcongr
    _ ≤ 2 * ((2 + 36 / Real.log 2 + 16) * Real.log (T + 2)) +
          2 * ((4 + 2 * K ^ 2) * Real.log (T + 2)) := by
      have h4k : 4 + 2 * K ^ 2 ≤ (4 + 2 * K ^ 2) * Real.log (T + 2) :=
        le_mul_of_one_le_right (by positivity) hlog_ge1
      linarith
    _ ≤ C * Real.log (T + 2) := by
      dsimp only [C]
      linarith [hlog_ge1]

/-- Symmetric critical-line mean-square upper bound on `[-T, T]` (`σ = 1 / 2`):
`(1 / (2 * T)) ∫ t in (-T)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 ≤ C * Real.log (T + 2)` for `1 ≤ T`. -/
theorem mean_sq_riemannZeta_half_symm_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃T : ℝ⦄, 1 ≤ T →
      (1 / (2 * T)) * ∫ t in (-T)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * Real.log (T + 2) := by
  obtain ⟨C₀, hC₀_pos, hbd⟩ := mean_sq_riemannZeta_half_upper_bound
  have hcont : Continuous fun t : ℝ ↦ ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    Continuous.pow continuous_riemannZeta_half.norm 2
  let A : ℝ := ∫ t in (0 : ℝ)..1, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
  let B : ℝ := max A 0
  have hB_nn : 0 ≤ B := le_max_right _ _
  have hlog3 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  refine ⟨B + C₀, by positivity, fun T hT ↦ ?_⟩
  have hT_pos : 0 < T := by linarith
  have hlog_ge1 : 1 ≤ Real.log (T + 2) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have heven : ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + (-t : ℂ) * I)‖ ^ 2 =
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t ↦ by
    have hconj_arg : (1 / 2 : ℂ) + (-t : ℂ) * I = conj ((1 / 2 : ℂ) + (t : ℂ) * I) := by
      rw [Complex.ext_iff]; simp
    rw [hconj_arg, riemannZeta_conj, Complex.norm_conj]
  have hsplit_symm := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-T) 0)
    (hcont.intervalIntegrable (μ := volume) 0 T)
  have href : ∫ t in (-T)..0, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    calc
      ∫ t in (-T)..0, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
          = ∫ t in (-T)..(-0), ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
        rw [neg_zero]
      _ = ∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 2 :=
        (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
          (f := fun t : ℝ ↦ ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2)).symm
      _ = ∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_congr fun t _ ↦ by simpa only [Complex.ofReal_neg] using heven t
  have hsplit_0T := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 1)
    (hcont.intervalIntegrable (μ := volume) 1 T)
  let I1T : ℝ := ∫ t in (1 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
  let IT : ℝ := ∫ t in (-T)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
  have hIT_eq : IT = 2 * (A + I1T) := by
    dsimp only [IT, A, I1T]
    rw [← hsplit_symm, href, two_mul, ← hsplit_0T]
  have heq : (1 / (2 * T)) * IT = A / T + (1 / T) * I1T := by
    rw [hIT_eq]
    field_simp [hT_pos.ne']
  change (1 / (2 * T)) * IT ≤ (B + C₀) * Real.log (T + 2)
  rw [heq]
  have h01_le : A / T ≤ B := by
    calc
      A / T ≤ B / T := div_le_div_of_nonneg_right (le_max_left A 0) hT_pos.le
      _ ≤ B / 1 := div_le_div_of_nonneg_left hB_nn zero_lt_one hT
      _ = B := div_one B
  calc
    A / T + (1 / T) * I1T ≤ B + C₀ * Real.log (T + 2) := add_le_add h01_le (hbd hT)
    _ ≤ B * Real.log (T + 2) + C₀ * Real.log (T + 2) := by
      have hB_mul : B ≤ B * Real.log (T + 2) := le_mul_of_one_le_right hB_nn hlog_ge1
      linarith
    _ = (B + C₀) * Real.log (T + 2) := by ring

/-- Critical-line power-growth mean-square upper bound on `[1, T]` (`σ = 1 / 2`):
for every `ε > 0`, `(1 / T) ∫ t in 1..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 ≤ C * T ^ ε` for `1 ≤ T`. -/
theorem mean_sq_riemannZeta_half_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃T : ℝ⦄, 1 ≤ T →
      (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * T ^ ε := by
  obtain ⟨C₀, hC₀_pos, hbd⟩ := mean_sq_riemannZeta_half_upper_bound
  let C : ℝ := C₀ * (Real.log 3 + 1 / ε)
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨C, by positivity, fun T hT ↦ ?_⟩
  have hT3 : T + 2 ≤ 3 * T := by linarith
  have hlog_le : Real.log (T + 2) ≤ Real.log 3 + Real.log T := by
    calc
      Real.log (T + 2) ≤ Real.log (3 * T) := Real.log_le_log (by linarith) hT3
      _ = Real.log 3 + Real.log T := Real.log_mul (by norm_num) (by linarith)
  have hpow_ge1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hlogT : Real.log T ≤ (1 / ε) * T ^ ε := log_le_inv_eps_rpow hε hT
  calc
    (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ C₀ * Real.log (T + 2) := hbd hT
    _ ≤ C₀ * (Real.log 3 * T ^ ε + (1 / ε) * T ^ ε) := by
      gcongr
      have hlog3_mul : Real.log 3 ≤ Real.log 3 * T ^ ε := le_mul_of_one_le_right hlog3_pos.le hpow_ge1
      linarith
    _ = C * T ^ ε := by dsimp only [C]; ring

/-- Bridge between Hardy's `hardyZ` function and `riemannZeta` on the critical line:
`|hardyZ t| = ‖riemannZeta (1 / 2 + t * I)‖`. -/
theorem hardyZ_abs_eq (t : ℝ) :
    |hardyZ t| = ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ :=
  abs_hardyZ t

/-- Square identity bridging Hardy's `hardyZ` function and `riemannZeta` on the critical line:
`(hardyZ t) ^ 2 = ‖riemannZeta (1 / 2 + t * I)‖ ^ 2`. -/
theorem hardyZ_sq_eq (t : ℝ) :
    (hardyZ t) ^ 2 = ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  rw [← sq_abs (hardyZ t), hardyZ_abs_eq]

/-- Mean-square logarithmic upper bound on `[1, T]` for Hardy's `hardyZ` function:
`(1 / T) ∫ t in 1..T, (hardyZ t) ^ 2 ≤ C * Real.log (T + 2)` for `1 ≤ T`. -/
theorem mean_sq_hardyZ_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃T : ℝ⦄, 1 ≤ T →
      (1 / T) * ∫ t in (1 : ℝ)..T, (hardyZ t) ^ 2 ≤ C * Real.log (T + 2) := by
  obtain ⟨C, hC_pos, hbd⟩ := mean_sq_riemannZeta_half_upper_bound
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  simpa only [hardyZ_sq_eq] using hbd hT

/-- Symmetric mean-square logarithmic upper bound on `[-T, T]` for Hardy's `hardyZ` function:
`(1 / (2 * T)) ∫ t in (-T)..T, (hardyZ t) ^ 2 ≤ C * Real.log (T + 2)` for `1 ≤ T`. -/
theorem mean_sq_hardyZ_symm_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃T : ℝ⦄, 1 ≤ T →
      (1 / (2 * T)) * ∫ t in (-T)..T, (hardyZ t) ^ 2 ≤ C * Real.log (T + 2) := by
  obtain ⟨C, hC_pos, hbd⟩ := mean_sq_riemannZeta_half_symm_upper_bound
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  simpa only [hardyZ_sq_eq] using hbd hT

/-- Mean-square power-growth upper bound on `[1, T]` for Hardy's `hardyZ` function:
for every `ε > 0`, `(1 / T) ∫ t in 1..T, (hardyZ t) ^ 2 ≤ C * T ^ ε` for `1 ≤ T`. -/
theorem mean_sq_hardyZ_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃T : ℝ⦄, 1 ≤ T →
      (1 / T) * ∫ t in (1 : ℝ)..T, (hardyZ t) ^ 2 ≤ C * T ^ ε := by
  obtain ⟨C, hC_pos, hbd⟩ := mean_sq_riemannZeta_half_rpow_bound hε
  refine ⟨C, hC_pos, fun T hT ↦ ?_⟩
  simpa only [hardyZ_sq_eq] using hbd hT

end MeanSquareCriticalHalfPlane

end AnalyticNumberTheory.RiemannZeta