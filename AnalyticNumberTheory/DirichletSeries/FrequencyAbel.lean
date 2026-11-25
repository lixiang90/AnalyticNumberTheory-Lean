import AnalyticNumberTheory.DirichletSeries.GeneralFrequency
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Abel's integral formula for general Dirichlet series -/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

private lemma step_eq (s₀ z : ℂ) (n : ℕ) :
    EqOn (fun u : ℝ => F.summatory a s₀ u * Complex.exp (-z * u))
      (fun u : ℝ => F.partialSum a s₀ (n+1) * Complex.exp (-z * u))
      (Ioo (F n) (F (n+1))) := by
  intro u hu
  change F.partialSum a s₀ (F.count u) * _ = F.partialSum a s₀ (n+1) * _
  rw [F.count_eq_succ hu.1.le hu.2]

private lemma intervalIntegrable_step (s₀ z : ℂ) (n : ℕ) :
    IntervalIntegrable (fun u : ℝ => F.summatory a s₀ u * Complex.exp (-z * u))
      volume (F n) (F (n+1)) := by
  apply (intervalIntegrable_congr_uIoo (uIoo_of_le (F.strictMono.monotone (Nat.le_succ n)) ▸
    F.step_eq a s₀ z n)).mpr
  exact (by fun_prop : Continuous (fun u : ℝ => F.partialSum a s₀ (n+1) * Complex.exp (-z * u))).intervalIntegrable _ _

private lemma intervalIntegrable_initial (s₀ z : ℂ) (n : ℕ) :
    IntervalIntegrable (fun u : ℝ => F.summatory a s₀ u * Complex.exp (-z * u))
      volume (F 0) (F n) := by
  induction n with
  | zero => exact IntervalIntegrable.refl
  | succ n ih => exact ih.trans (F.intervalIntegrable_step a s₀ z n)

private lemma step_integral (s₀ z : ℂ) (n : ℕ) :
    z * (∫ u : ℝ in F n..F (n+1), F.summatory a s₀ u * Complex.exp (-z * u)) =
    F.partialSum a s₀ (n+1) * (Complex.exp (-z * F n) - Complex.exp (-z * F (n+1))) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (F.strictMono.monotone (Nat.le_succ n)) (F.step_eq a s₀ z n),
    intervalIntegral.integral_const_mul]
  by_cases hz : z = 0
  · simp [hz]
  · rw [integral_exp_mul_complex (neg_ne_zero.mpr hz)]
    field_simp
    ring

private lemma exp_shift (s₀ z : ℂ) (v : ℝ) :
    Complex.exp (-(s₀+z) * v) = Complex.exp (-s₀ * v) * Complex.exp (-z * v) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Finite Abel summation at an arbitrary frequency. The integral contains the
step function cut off in the frequency variable, and includes a possible
constant term with zero frequency. -/
theorem partialSum_eq_boundary_add_integral (s₀ z : ℂ) (n : ℕ) :
    F.partialSum a (s₀+z) (n+1) =
      F.partialSum a s₀ (n+1) * Complex.exp (-z * F n) +
      z * ∫ u : ℝ in F 0..F n, F.summatory a s₀ u * Complex.exp (-z * u) := by
  induction n with
  | zero => simp only [partialSum, Nat.zero_add, Finset.sum_range_one, intervalIntegral.integral_same, mul_zero, add_zero, exp_shift, mul_assoc]
  | succ n ih =>
    rw [F.partialSum_succ a (s₀+z) (n+1), ih, F.partialSum_succ a s₀ (n+1),
      ← intervalIntegral.integral_add_adjacent_intervals (F.intervalIntegrable_initial a s₀ z n)
        (F.intervalIntegrable_step a s₀ z n), mul_add z, F.step_integral, exp_shift]
    ring

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

/-- Explicit truncation error for the integral representation on any line
`Re z > α`. The constant also records the imaginary part of the shift. -/
theorem norm_partialSum_sub_sum_le {s₀ z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u))
    (hz : α < z.re) (n : ℕ) :
    ‖F.partialSum a (s₀+z) (n+1) - F.sum a (s₀+z)‖ ≤
      C * (1 + ‖z‖ / (z.re-α)) * Real.exp (-(z.re-α) * F n) := by
  let d := z.re-α
  have hd : 0 < d := sub_pos.mpr hz
  have hn : F 0 ≤ F n := F.strictMono.monotone (Nat.zero_le n)
  have hI := F.tendsto_partialSum_integral a h hz
  have hsum := tendsto_nhds_unique (ConvergesAt.tendsto (show F.ConvergesAt a (s₀+z) from ⟨_,hI⟩)) hI
  have hi := F.integrable_summatory_weight a h hz hn
  have hsplit := intervalIntegral.integral_interval_add_Ioi (F.integrable_summatory_weight a h hz le_rfl) hi
  have hB := F.norm_weight_le a (h (F n) hn) (z := z)
  simp only [summatory, count_exponent] at hB
  have ht : ‖∫ u : ℝ in Ioi (F n), F.summatory a s₀ u * Complex.exp (-z*u)‖ ≤
      C * Real.exp (-d * F n) / d := by
    calc
      _ ≤ ∫ u : ℝ in Ioi (F n), C * Real.exp (-d*u) := by
        apply norm_integral_le_of_norm_le (g := fun u : ℝ => C * Real.exp (-d*u))
          ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) _).const_mul C)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
        exact F.norm_weight_le a (h u (hn.trans hu.le))
      _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd), neg_div_neg_eq, mul_div_assoc]
  rw [F.partialSum_eq_boundary_add_integral, hsum, ← hsplit, mul_add, show ∀ A B C : ℂ, A+B-(B+C) = A-C by intros; abel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ C * Real.exp (-d * F n) + ‖z‖ * (C * Real.exp (-d * F n) / d) := by
      rw [norm_mul z]
      exact add_le_add hB (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
    _ = _ := by dsimp [d]; ring

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
