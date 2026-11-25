import AnalyticNumberTheory.DirichletSeries.GeneralFrequency
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Abel summation at real frequency cutoffs -/

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

private lemma step_integral_to (s₀ z : ℂ) (n : ℕ) {y : ℝ} (hl : F n ≤ y) (hr : y ≤ F (n+1)) :
    z * (∫ u : ℝ in F n..y, F.summatory a s₀ u * Complex.exp (-z * u)) =
    F.partialSum a s₀ (n+1) * (Complex.exp (-z * F n) - Complex.exp (-z * y)) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hl
    ((F.step_eq a s₀ z n).mono (Ioo_subset_Ioo_right hr)), intervalIntegral.integral_const_mul]
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
        (F.intervalIntegrable_step a s₀ z n), mul_add z, F.step_integral_to a s₀ z n (F.strictMono.monotone (Nat.le_succ n)) le_rfl, exp_shift]
    ring

/-- The height is below the first exponent precisely when the cutoff is empty. -/
theorem count_eq_zero_iff {u : ℝ} : F.count u = 0 ↔ u < F 0 := by
  rw [← not_le, ← F.lt_count_iff, Nat.not_lt, Nat.le_zero]

/-- The number of included exponents tends to infinity with the real cutoff. -/
theorem tendsto_count_atTop : Tendsto F.count atTop atTop :=
  Filter.tendsto_atTop.2 fun n => (eventually_ge_atTop (F n)).mono fun _ h => (F.lt_count_iff.mpr h).le

/-- Real frequency cutoffs and ordered partial sums have exactly the same limits. -/
theorem tendsto_summatory_iff (s : ℂ) (L : ℂ) :
    Tendsto (F.summatory a s) atTop (𝓝 L) ↔ Tendsto (F.partialSum a s) atTop (𝓝 L) := by
  constructor
  · intro h
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Function.comp_def, summatory, count_exponent] using h.comp F.tendsto_atTop
  · intro h
    exact h.comp F.tendsto_count_atTop

private lemma exists_last {u : ℝ} (hu : F 0 ≤ u) :
    ∃ n, F n ≤ u ∧ u < F (n+1) := by
  have hpos := F.lt_count_iff.mpr hu
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  refine ⟨n, F.lt_count_iff.mp (by omega), lt_of_not_ge fun h => ?_⟩
  have := F.lt_count_iff.mpr h
  omega

private lemma below_first (s₀ z : ℂ) (u : ℝ) :
    EqOn (fun t : ℝ => F.summatory a s₀ t * Complex.exp (-z * t)) (fun _ => 0) (Ioo u (F 0)) := by
  intro t ht
  simp [summatory, F.count_eq_zero_iff.mpr ht.2, partialSum]

private lemma intervalIntegrable_from_first (s₀ z : ℂ) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => F.summatory a s₀ t * Complex.exp (-z * t)) volume (F 0) u := by
  by_cases hu : F 0 ≤ u
  · obtain ⟨n, hl, hr⟩ := F.exists_last hu
    exact (F.intervalIntegrable_initial a s₀ z n).trans
      ((F.intervalIntegrable_step a s₀ z n).mono_set
        (uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hl hr.le)))
  · apply IntervalIntegrable.symm
    apply (intervalIntegrable_congr_uIoo (uIoo_of_le (le_of_not_ge hu) ▸
      F.below_first a s₀ z u)).mpr
    exact continuous_const.intervalIntegrable _ _

/-- The Abel integrand is integrable between any two finite real cutoffs. -/
theorem intervalIntegrable_summatory_weight (s₀ z : ℂ) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => F.summatory a s₀ t * Complex.exp (-z * t)) volume x y :=
  (F.intervalIntegrable_from_first a s₀ z x).symm.trans (F.intervalIntegrable_from_first a s₀ z y)

/-- Abel summation to an arbitrary real height, including a cutoff at a jump
or before the first exponent. -/
theorem summatory_eq_boundary_add_integral (s₀ z : ℂ) (y : ℝ) :
    F.summatory a (s₀+z) y = F.summatory a s₀ y * Complex.exp (-z*y) +
      z * ∫ t : ℝ in F 0..y, F.summatory a s₀ t * Complex.exp (-z*t) := by
  by_cases hy : F 0 ≤ y
  · obtain ⟨n, hl, hr⟩ := F.exists_last hy
    have hstep := F.step_integral_to a s₀ z n hl hr.le
    rw [summatory, summatory, F.count_eq_succ hl hr, F.partialSum_eq_boundary_add_integral,
      ← intervalIntegral.integral_add_adjacent_intervals (F.intervalIntegrable_initial a s₀ z n)
        (F.intervalIntegrable_summatory_weight a s₀ z (F n) y), mul_add, hstep]
    ring
  · have hlt := lt_of_not_ge hy
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr_Ioo_of_le hlt.le
      (F.below_first a s₀ z y)]
    simp [summatory, F.count_eq_zero_iff.mpr hlt, partialSum]

/-- Two-endpoint Abel summation. For `x ≤ y` the difference on the left
includes the exponent at `y` and excludes the exponent at `x`. The same
identity holds for reversed endpoints with the oriented interval integral. -/
theorem summatory_sub_eq_boundary_add_integral (s₀ z : ℂ) (x y : ℝ) :
    F.summatory a (s₀+z) y - F.summatory a (s₀+z) x =
      F.summatory a s₀ y * Complex.exp (-z*y) - F.summatory a s₀ x * Complex.exp (-z*x) +
      z * ∫ t : ℝ in x..y, F.summatory a s₀ t * Complex.exp (-z*t) := by
  rw [F.summatory_eq_boundary_add_integral a s₀ z y, F.summatory_eq_boundary_add_integral a s₀ z x,
    ← intervalIntegral.integral_interval_sub_left (F.intervalIntegrable_from_first a s₀ z y)
      (F.intervalIntegrable_from_first a s₀ z x)]
  ring

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
