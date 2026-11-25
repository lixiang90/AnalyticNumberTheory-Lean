import AnalyticNumberTheory.DirichletSeries.FrequencyCutoffs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Partial summation for ordinary Dirichlet series at real cutoffs -/

noncomputable section

open Complex MeasureTheory Set

namespace AnalyticNumberTheory.DirichletSeries

open DirichletFrequency

/-- For logarithmic frequencies the inclusive cutoff at `log x` counts
exactly the positive integers at most `x`. -/
theorem DirichletFrequency.logarithmic_count_log {x : ℝ} (hx : 0 < x) :
    logarithmic.count (Real.log x) = ⌊x⌋₊ := by
  apply eq_of_forall_lt_iff
  intro n
  rw [lt_count_iff, ← Nat.succ_le_iff, Nat.le_floor_iff hx.le]
  change Real.log ((n+1 : ℕ) : ℝ) ≤ Real.log x ↔ _
  exact Real.log_le_log_iff (by positivity) hx

/-- The cutoff of a logarithmic Dirichlet frequency at `log x` agrees with
the ordinary partial sum through the integer part of `x`. -/
theorem DirichletFrequency.logarithmic_summatory_log (a : ℕ → ℂ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    logarithmic.summatory (fun n => a (n+1)) s (Real.log x) = dirichletPartialSum a s ⌊x⌋₊ := by
  rw [summatory, logarithmic_count_log hx, logarithmic_partialSum]

private lemma exp_neg_mul_log (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Complex.exp (-z * (Real.log x : ℂ)) = (x : ℂ) ^ (-z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

/-- Finite Abel summation for ordinary Dirichlet series with two arbitrary
positive real cutoffs and an arbitrary complex displacement. The floor
at each endpoint gives the right-continuous convention for the partial sums. -/
theorem dirichletPartialSum_sub_eq_abel_integral (a : ℕ → ℂ) (s₀ z : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    dirichletPartialSum a (s₀+z) ⌊y⌋₊ - dirichletPartialSum a (s₀+z) ⌊x⌋₊ =
      dirichletPartialSum a s₀ ⌊y⌋₊ * (y : ℂ)^(-z) -
      dirichletPartialSum a s₀ ⌊x⌋₊ * (x : ℂ)^(-z) +
      z * ∫ t : ℝ in x..y, dirichletPartialSum a s₀ ⌊t⌋₊ * (t : ℂ)^(-z-1) := by
  let g := fun u : ℝ => logarithmic.summatory (fun n => a (n+1)) s₀ u * Complex.exp (-z * u)
  have hpos {t : ℝ} (ht : t ∈ uIcc x y) : 0 < t := (lt_min hx hy).trans_le ht.1
  have hchange := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := x) (b := y)
    (f := Real.log) (f' := fun t : ℝ => t⁻¹) (g := g)
    (Real.continuousOn_log.mono (fun t ht => (hpos ht).ne'))
    (fun t ht => Real.hasDerivAt_log (hpos (Ioo_subset_Icc_self ht)).ne')
    (fun t ht => (inv_pos.mpr (hpos (Ioo_subset_Icc_self ht))).le)
  have hI : (∫ u in Real.log x..Real.log y, g u) =
      ∫ t : ℝ in x..y, dirichletPartialSum a s₀ ⌊t⌋₊ * (t : ℂ)^(-z-1) := by
    rw [← hchange]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' := hpos ht
    dsimp only [g, Function.comp_apply]
    rw [logarithmic_summatory_log a s₀ ht', exp_neg_mul_log z ht', Complex.real_smul,
      Complex.ofReal_inv, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht'.ne'), Complex.cpow_one,
      div_eq_mul_inv]
    ring
  have H := logarithmic.summatory_sub_eq_boundary_add_integral (fun n => a (n+1)) s₀ z
    (Real.log x) (Real.log y)
  dsimp only [g] at hI
  simpa only [logarithmic_summatory_log a _ hx, logarithmic_summatory_log a _ hy,
    exp_neg_mul_log z hx, exp_neg_mul_log z hy, hI] using H

/-- Ordinary partial summation in terms of the unweighted coefficient sums. -/
theorem dirichletPartialSum_sub_eq_coeffPartialSum_integral (a : ℕ → ℂ) (s : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    dirichletPartialSum a s ⌊y⌋₊ - dirichletPartialSum a s ⌊x⌋₊ =
      coeffPartialSum a ⌊y⌋₊ * (y : ℂ)^(-s) - coeffPartialSum a ⌊x⌋₊ * (x : ℂ)^(-s) +
      s * ∫ t : ℝ in x..y, coeffPartialSum a ⌊t⌋₊ * (t : ℂ)^(-s-1) := by
  simpa only [zero_add, coeffPartialSum_eq_dirichletPartialSum_zero] using
    dirichletPartialSum_sub_eq_abel_integral a 0 s hx hy

end AnalyticNumberTheory.DirichletSeries
