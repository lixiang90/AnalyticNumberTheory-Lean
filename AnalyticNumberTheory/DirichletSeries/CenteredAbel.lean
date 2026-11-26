import AnalyticNumberTheory.DirichletSeries.FrequencyConvergence

/-! # Abel summation with a limiting constant -/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

private def centeredCoeffs (s₀ M : ℂ) (n : ℕ) : ℂ :=
  a n - if n = 0 then M * Complex.exp (s₀ * F 0) else 0

private lemma partialSum_centered (s₀ M z : ℂ) {N : ℕ} (hN : 0 < N) :
    F.partialSum (F.centeredCoeffs a s₀ M) (s₀ + z) N =
      F.partialSum a (s₀ + z) N - M * Complex.exp (-z * F 0) := by
  have hweight : M * Complex.exp (s₀ * F 0) * Complex.exp (-(s₀ + z) * F 0) =
      M * Complex.exp (-z * F 0) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp [partialSum, centeredCoeffs, sub_mul, Finset.sum_sub_distrib, ite_mul, hN]
  simpa using hweight

private lemma summatory_centered (s₀ M z : ℂ) {u : ℝ} (hu : F 0 ≤ u) :
    F.summatory (F.centeredCoeffs a s₀ M) (s₀ + z) u =
      F.summatory a (s₀ + z) u - M * Complex.exp (-z * F 0) :=
  F.partialSum_centered a s₀ M z (F.lt_count_iff.mpr hu)

private lemma summatory_centered_base (s₀ M : ℂ) {u : ℝ} (hu : F 0 ≤ u) :
    F.summatory (F.centeredCoeffs a s₀ M) s₀ u = F.summatory a s₀ u - M := by
  simpa using F.summatory_centered a s₀ M 0 hu

private lemma restore_centered_limit {s₀ M z L : ℂ}
    (h : Tendsto (F.partialSum (F.centeredCoeffs a s₀ M) (s₀ + z)) atTop (𝓝 L)) :
    Tendsto (F.partialSum a (s₀ + z)) atTop (𝓝 (M * Complex.exp (-z * F 0) + L)) := by
  apply (tendsto_const_nhds.add h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [F.partialSum_centered a s₀ M z hN]
  abel

/-- If the partial sums at the base point differ from a constant by at most
`C exp(αu)`, their centered Abel integral gives the series throughout
`Re z > α`. The first exponent contributes the boundary term, including when
it is zero. Negative values of `α` extend convergence to the left. -/
theorem tendsto_partialSum_centered_integral {s₀ M z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u - M‖ ≤ C * Real.exp (α * u))
    (hz : α < z.re) :
    Tendsto (F.partialSum a (s₀ + z)) atTop
      (𝓝 (M * Complex.exp (-z * F 0) +
        z * ∫ u : ℝ in Ioi (F 0), (F.summatory a s₀ u - M) * Complex.exp (-z * u))) := by
  apply F.restore_centered_limit a
  have h' := F.tendsto_partialSum_integral (F.centeredCoeffs a s₀ M) (s₀ := s₀)
    (fun u hu => by rw [F.summatory_centered_base a s₀ M hu]; exact h u hu) hz
  convert h' using 2
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [F.summatory_centered_base a s₀ M (le_of_lt hu)]

/-- Explicit truncation error for centered Abel summation at every real cutoff
above the first frequency. The same bound works when the center is nonzero. -/
theorem norm_summatory_sub_sum_le_centered {s₀ M z : ℂ} {C α : ℝ}
    (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u - M‖ ≤ C * Real.exp (α * u))
    (hz : α < z.re) {y : ℝ} (hy : F 0 ≤ y) :
    ‖F.summatory a (s₀ + z) y - F.sum a (s₀ + z)‖ ≤
      C * (1 + ‖z‖ / (z.re - α)) * Real.exp (-(z.re - α) * y) := by
  let b := F.centeredCoeffs a s₀ M
  have hb (u : ℝ) (hu : F 0 ≤ u) : ‖F.summatory b s₀ u‖ ≤ C * Real.exp (α * u) := by
    simpa only [b, F.summatory_centered_base a s₀ M hu] using h u hu
  have hc : F.ConvergesAt b (s₀ + z) := ⟨_, F.tendsto_partialSum_integral b hb hz⟩
  have ht := F.restore_centered_limit a (M := M) hc.tendsto
  have hsum := tendsto_nhds_unique (ConvergesAt.tendsto (show F.ConvergesAt a (s₀ + z) from ⟨_, ht⟩)) ht
  have H := F.norm_summatory_sub_sum_le b hb hz hy
  rw [show F.summatory b (s₀ + z) y = _ from F.summatory_centered a s₀ M z hy] at H
  rw [hsum, ← sub_sub]
  exact H

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
