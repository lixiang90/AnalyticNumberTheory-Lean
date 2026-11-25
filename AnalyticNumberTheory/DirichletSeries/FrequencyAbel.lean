import AnalyticNumberTheory.DirichletSeries.FrequencyCutoffs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Abel's integral formula for general Dirichlet series -/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

private lemma norm_weight_le {s₀ z : ℂ} {C α u : ℝ}
    (h : ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u)) :
    ‖F.summatory a s₀ u * Complex.exp (-z*u)‖ ≤ C * Real.exp (-(z.re-α)*u) := by
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re]
  calc
    _ ≤ (C * Real.exp (α*u)) * Real.exp (-z.re*u) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private lemma integrable_summatory_weight {s₀ z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u))
    (hz : α < z.re) {v : ℝ} (hv : F 0 ≤ v) :
    IntegrableOn (fun u : ℝ => F.summatory a s₀ u * Complex.exp (-z*u)) (Ioi v) := by
  have hm : Measurable (fun u : ℝ => F.summatory a s₀ u * Complex.exp (-z*u)) :=
    (F.measurable_summatory a s₀).mul (by fun_prop)
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sub_pos.mpr hz)) v).const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  exact F.norm_weight_le a (h u (hv.trans hu.le))

/-- If the partial sums at `s₀` grow at most as `C exp(αu)` in frequency height,
the series at `s₀ + z` is the Laplace integral of those sums multiplied by `z`,
throughout `Re z > α`. -/
theorem tendsto_partialSum_integral {s₀ z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u))
    (hz : α < z.re) :
    Tendsto (F.partialSum a (s₀+z)) atTop
      (𝓝 (z * ∫ u : ℝ in Ioi (F 0), F.summatory a s₀ u * Complex.exp (-z*u))) := by
  have hi := F.integrable_summatory_weight a h hz le_rfl
  have he : Tendsto (fun n => C * Real.exp (-(z.re-α) * F n)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (F.tendsto_atTop.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (sub_pos.mpr hz)))).const_mul C
  have hb : Tendsto (fun n => F.partialSum a s₀ (n+1) * Complex.exp (-z*F n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) he
    simpa only [summatory, count_exponent] using
      F.norm_weight_le a (h (F n) (F.strictMono.monotone (Nat.zero_le n)))
  have hI := (intervalIntegral_tendsto_integral_Ioi (F 0) hi F.tendsto_atTop).const_mul z
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [← F.partialSum_eq_boundary_add_integral, zero_add] using hb.add hI

/-- Explicit error at any real frequency cutoff `y ≥ λ₀`, throughout
`Re z > α`. The bound uses the actual height even when it lies between exponents. -/
theorem norm_summatory_sub_sum_le {s₀ z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u))
    (hz : α < z.re) {y : ℝ} (hy : F 0 ≤ y) :
    ‖F.summatory a (s₀+z) y - F.sum a (s₀+z)‖ ≤
      C * (1 + ‖z‖ / (z.re-α)) * Real.exp (-(z.re-α) * y) := by
  let d := z.re-α
  have hd : 0 < d := sub_pos.mpr hz
  have hI := F.tendsto_partialSum_integral a h hz
  have hsum := tendsto_nhds_unique (ConvergesAt.tendsto (show F.ConvergesAt a (s₀+z) from ⟨_,hI⟩)) hI
  have hi := F.integrable_summatory_weight a h hz hy
  have hsplit := intervalIntegral.integral_interval_add_Ioi (F.integrable_summatory_weight a h hz le_rfl) hi
  have hB := F.norm_weight_le a (h y hy) (z := z)
  have ht : ‖∫ u : ℝ in Ioi y, F.summatory a s₀ u * Complex.exp (-z*u)‖ ≤
      C * Real.exp (-d * y) / d := by
    calc
      _ ≤ ∫ u : ℝ in Ioi y, C * Real.exp (-d*u) := by
        apply norm_integral_le_of_norm_le (g := fun u : ℝ => C * Real.exp (-d*u))
          ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) _).const_mul C)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
        exact F.norm_weight_le a (h u (hy.trans hu.le))
      _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd), neg_div_neg_eq, mul_div_assoc]
  rw [F.summatory_eq_boundary_add_integral, hsum, ← hsplit, mul_add, show ∀ A B C : ℂ, A+B-(B+C) = A-C by intros; abel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ C * Real.exp (-d * y) + ‖z‖ * (C * Real.exp (-d * y) / d) := by
      rw [norm_mul z]
      exact add_le_add hB (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
    _ = _ := by dsimp [d]; ring

/-- Explicit truncation error for the integral representation on any line
`Re z > α`. The constant also records the imaginary part of the shift. -/
theorem norm_partialSum_sub_sum_le {s₀ z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u))
    (hz : α < z.re) (n : ℕ) :
    ‖F.partialSum a (s₀+z) (n+1) - F.sum a (s₀+z)‖ ≤
      C * (1 + ‖z‖ / (z.re-α)) * Real.exp (-(z.re-α) * F n) := by
  simpa only [summatory, count_exponent] using
    F.norm_summatory_sub_sum_le a h hz (F.strictMono.monotone (Nat.zero_le n))

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
