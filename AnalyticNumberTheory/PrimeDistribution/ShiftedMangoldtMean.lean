import AnalyticNumberTheory.AnalyticTools.IntegratedPartialFractions
import AnalyticNumberTheory.AnalyticTools.LogarithmicPoleSlope
import AnalyticNumberTheory.DirichletSeries.LogarithmicTaper
import AnalyticNumberTheory.DirichletSeries.LogWeightedInversion
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.RiemannZeta.TranslatedPartialFractions

/-! # The complex von Mangoldt mean and Selberg's smoothed explicit formula -/

noncomputable section

open Complex Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem translated_zero_re_le (Z : ZetaZeroEnumeration) (s : ℂ) (n : ℕ) :
    (Z.zero n - s).re ≤ 1 - s.re :=
  sub_le_sub_right (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le _

private theorem translated_trivial_re_le (s : ℂ) (n : ℕ) :
    (trivialZetaZero n - s).re ≤ 1 - s.re := by
  rw [Complex.sub_re]
  apply sub_le_sub_right
  simp [trivialZetaZero, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The first logarithmic mean of Λ(n)n⁻ˢ has an absolutely convergent integrated
explicit formula about every regular center s, for any enumeration with multiplicities. -/
theorem logWeightedSum_shifted_vonMangoldt (Z : ZetaZeroEnumeration) {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    logWeightedSum (powMul (-s) (fun n => (Λ n : ℂ))) x =
      integratedPartialFractions (1-s) (-deriv riemannZeta s / riemannZeta s)
        (fun n => Z.zero n-s) (fun n => trivialZetaZero n-s) (Real.log x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [logWeightedSum, integratedPartialFractions, integratedPole]
  let M := max 0 (1-s.re)
  have hM : 0 ≤ M := le_max_left _ _
  have hMs : 1-s.re ≤ M := le_max_right _ _
  let G := integratedPartialFractions (1-s) (-deriv riemannZeta s / riemannZeta s)
    (fun n => Z.zero n-s) (fun n => trivialZetaZero n-s)
  let a := powMul (-s) (fun n => (Λ n : ℂ))
  have hA (n : ℕ) : (Z.zero n-s).re ≤ M := (translated_zero_re_le Z s n).trans hMs
  have hB (n : ℕ) : (trivialZetaZero n-s).re ≤ M := (translated_trivial_re_le s n).trans hMs
  have h₁ (n : ℕ) : Z.zero n - s ≠ 0 := sub_ne_zero.mpr fun he =>
    hζ (he ▸ (mem_criticalStripZeros.mp (Z.mem_strip n)).1)
  have h₂ (n : ℕ) : trivialZetaZero n - s ≠ 0 := sub_ne_zero.mpr fun he =>
    hζ (he ▸ riemannZeta_trivialZetaZero n)
  have H (w : ℂ) (hw : M < w.re) :
      IntegrableOn (fun u : ℝ => Complex.exp (-w*u)*G u) (Ioi 0) ∧
      laplaceTransform G w = LSeries a w / w^2 := by
    have hws : 1 < (w+s).re := by rw [Complex.add_re]; linarith
    have hw₁ : w+s ≠ 1 := fun he => by simp [he] at hws
    have ht := laplaceTransform_integratedPartialFractions (-deriv riemannZeta s / riemannZeta s)
      hM (sub_ne_zero.mpr hs.symm) (by simpa only [Complex.sub_re, Complex.one_re] using hMs)
      h₁ h₂ hA hB (Z.summable_inv_sq_sub s) (summable_trivialZetaZero_inv_sq_sub s) hw
    refine ⟨ht.1, ?_⟩
    rw [ht.2]
    unfold a
    rw [LSeries_powMul, sub_neg_eq_add, LSeries_vonMangoldt_eq hws,
      neg_logDeriv_riemannZeta_translate Z hs hζ hw₁ (_root_.riemannZeta_ne_zero_of_one_lt_re hws)]
  have hσ : 0 < M+1 := by linarith
  have hσM : M < ((M+1 : ℝ) : ℂ).re := by simp
  have hσa : LSeriesSummable a ((M+1 : ℝ) : ℂ) := by
    unfold a
    rw [LSeriesSummable_powMul_iff, sub_neg_eq_add, LSeriesSummable_vonMangoldt_iff,
      Complex.add_re, Complex.ofReal_re]
    linarith
  exact logWeightedSum_eq_of_laplaceTransform hσ hσa hx
    (continuous_integratedPartialFractions _ _ hM hA hB (Z.summable_inv_sq_sub s)
      (summable_trivialZetaZero_inv_sq_sub s)).continuousAt (H _ hσM).1
    (fun t => (H _ (by simp)).2)

/-- For a signed logarithmic step, the slope of the tilted von Mangoldt mean is the
logarithmic derivative plus the slope of the pole minus both absolute zero sums. -/
theorem shifted_vonMangoldt_slope (Z : ZetaZeroEnumeration) {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) {u h : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ u+h) (hh : h ≠ 0) :
    (logWeightedSum (powMul (-s) (fun n => (Λ n : ℂ))) (Real.exp (u+h)) -
      logWeightedSum (powMul (-s) (fun n => (Λ n : ℂ))) (Real.exp u))/(h : ℂ) =
      -deriv riemannZeta s / riemannZeta s + logarithmicPoleSlope (1-s) u h -
        (∑' n, logarithmicPoleSlope (Z.zero n-s) u h) -
          ∑' n, logarithmicPoleSlope (trivialZetaZero n-s) u h := by
  have H (v : ℝ) (hv' : 0 ≤ v) := logWeightedSum_shifted_vonMangoldt Z hs hζ
    (Real.one_le_exp_iff.mpr hv')
  rw [H _ hv, H _ hu, Real.log_exp, Real.log_exp,
    logarithmicPoleSlope_eq_difference _ hu hv,
    (hasSum_logarithmicPoleSlope (translated_zero_re_le Z s) (Z.summable_inv_sq_sub s) hu hv).tsum_eq,
    (hasSum_logarithmicPoleSlope (translated_trivial_re_le s)
      (summable_trivialZetaZero_inv_sq_sub s) hu hv).tsum_eq]
  simp only [integratedPartialFractions, Complex.ofReal_add]
  field_simp [Complex.ofReal_ne_zero.mpr hh]
  ring

/-- At any regular center the negative logarithmic derivative of ζ is exactly
the tapered Dirichlet polynomial with the pole, nontrivial-zero, and trivial-zero
corrections. The parameter u is the logarithm of the inner cutoff. -/
theorem selberg_logDeriv_explicit_formula (Z : ZetaZeroEnumeration) {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) {u : ℝ} (hu : 0 < u) :
    -deriv riemannZeta s / riemannZeta s =
      logTaperedSum (powMul (-s) (fun n => (Λ n : ℂ))) u - logarithmicPoleSlope (1-s) u u +
        (∑' n, logarithmicPoleSlope (Z.zero n-s) u u) +
          ∑' n, logarithmicPoleSlope (trivialZetaZero n-s) u u := by
  rw [logTaperedSum_eq_difference _ hu,
    shifted_vonMangoldt_slope Z hs hζ hu.le (add_nonneg hu.le hu.le) hu.ne']
  ring

/-- Both zero sums in Selberg's formula converge absolutely at each cutoff,
independently of the order of enumeration. -/
theorem summable_selberg_zero_slopes (Z : ZetaZeroEnumeration) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (Summable fun n => logarithmicPoleSlope (Z.zero n-s) u u) ∧
      Summable fun n => logarithmicPoleSlope (trivialZetaZero n-s) u u := by
  exact ⟨(hasSum_logarithmicPoleSlope (translated_zero_re_le Z s) (Z.summable_inv_sq_sub s)
      hu.le (add_nonneg hu.le hu.le)).summable,
    (hasSum_logarithmicPoleSlope (translated_trivial_re_le s) (summable_trivialZetaZero_inv_sq_sub s)
      hu.le (add_nonneg hu.le hu.le)).summable⟩

end AnalyticNumberTheory.PrimeDistribution
