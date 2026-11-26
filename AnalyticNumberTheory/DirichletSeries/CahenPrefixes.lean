import AnalyticNumberTheory.DirichletSeries.FrequencyConvergence
import AnalyticNumberTheory.DirichletSeries.ExponentialRate
import Mathlib.Algebra.BigOperators.Module

/-! # Cahen's formula from coefficient partial sums -/

noncomputable section

open Complex Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- Bounded partial sums at a nonnegative real argument bound the unweighted
partial sums by twice that bound times the exponential of the last included
frequency. -/
theorem norm_prefix_le_of_bounded_right {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (h : ∀ u, ‖F.summatory a (r : ℂ) u‖ ≤ C) (n : ℕ) :
    ‖F.partialSum a 0 (n+1)‖ ≤ (C * 2) * Real.exp (r * F n) := by
  let w (k : ℕ) := Real.exp (r * F k)
  let b (k : ℕ) := a k * Complex.exp (-(r : ℂ) * F k)
  have hw (k : ℕ) : 0 ≤ w k := (Real.exp_pos _).le
  have hd (k : ℕ) : 0 ≤ w (k+1) - w k := sub_nonneg.mpr (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (F.strictMono.monotone (Nat.le_succ k)) hr))
  have hb (k : ℕ) : ‖∑ j ∈ Finset.range (k+1), b j‖ ≤ C := by
    simpa only [summatory, count_exponent, partialSum, b] using h (F k)
  have hterm (k : ℕ) : w k • b k = a k := by
    change Real.exp (r * F k) • (a k * Complex.exp (-(r : ℂ) * F k)) = a k
    rw [Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_mul, mul_left_comm, ← Complex.exp_add]
    simp
  have H := Finset.sum_range_by_parts w b (n+1)
  simp only [Nat.add_sub_cancel, hterm] at H
  have hvar : ‖∑ k ∈ Finset.range n, (w (k+1) - w k) • (∑ j ∈ Finset.range (k+1), b j)‖ ≤
      (w n - w 0) * C := by
    calc
      _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range n, (w (k+1) - w k) * C := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd k)]
        exact mul_le_mul_of_nonneg_left (hb k) (hd k)
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub]
  simp only [partialSum, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [H]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ w n * C + (w n - w 0) * C := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw n)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb n) (hw n)) hvar
    _ ≤ _ := by change _ ≤ (C * 2) * w n; nlinarith [mul_nonneg (hw 0) hC]

/-- A nonnegative exponential bound for coefficient prefixes gives ordered
convergence to the right of that exponent. -/
theorem convergesAt_of_prefix_bound {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (h : ∀ n, ‖F.partialSum a 0 (n+1)‖ ≤ C * Real.exp (r * F n))
    {s : ℂ} (hs : r < s.re) : F.ConvergesAt a s := by
  have hb (u : ℝ) (hu : F 0 ≤ u) : ‖F.summatory a 0 u‖ ≤ C * Real.exp (r * u) := by
    have hpos := F.lt_count_iff.mpr hu
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hlast : F n ≤ u := F.lt_count_iff.mp (by omega)
    rw [summatory, hn]
    exact (h n).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlast hr)) hC)
  obtain ⟨L, hL⟩ : F.ConvergesAt a (0 + s) := ⟨_, F.tendsto_partialSum_integral a hb hs⟩
  exact ⟨L, by simpa using hL⟩

private lemma nonneg_prefix_rate (h0 : ¬ F.ConvergesAt a 0) :
    0 ≤ F.exponentialRate (fun n => F.partialSum a 0 (n+1)) := by
  by_contra! ht
  obtain ⟨r, hr, hr0⟩ := EReal.exists_between_coe_real ht
  have hdec := F.eventually_norm_le_exp_of_exponentialRate_lt _ hr
  have hlim := Real.tendsto_exp_atBot.comp
    (F.tendsto_atTop.const_mul_atTop_of_neg (EReal.coe_lt_coe_iff.mp (show (r : EReal) < ((0 : ℝ) : EReal) from hr0)))
  exact h0 ⟨0, (tendsto_add_atTop_iff_nat 1).mp (squeeze_zero_norm' hdec hlim)⟩

/-- If the coefficient series diverges at zero, the ordered abscissa equals
the upper exponential rate of the prefixes through the current frequency.
This also covers a series that converges nowhere. -/
theorem abscissa_eq_exponentialRate_prefix (h0 : ¬ F.ConvergesAt a 0) :
    F.abscissa a = F.exponentialRate (fun n => F.partialSum a 0 (n+1)) := by
  have hσ : (0 : EReal) ≤ F.abscissa a :=
    le_of_not_gt fun h => h0 (convergesAt_of_abscissa_lt (s := 0) (by simpa using h))
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    obtain ⟨r, hr, hrt⟩ := EReal.exists_between_coe_real ht
    obtain ⟨C, hC, h⟩ := F.exists_bound_of_exponentialRate_lt _ hr
    have hr0 := EReal.coe_nonneg.mp ((F.nonneg_prefix_rate a h0).trans hr.le)
    exact abscissa_le_re (s := (t : ℂ)) (F.convergesAt_of_prefix_bound a hr0 hC h
      (EReal.coe_lt_coe_iff.mp hrt))
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    have ht0 := EReal.coe_nonneg.mp (hσ.trans ht.le)
    have hcv : F.ConvergesAt a (t : ℂ) := convergesAt_of_abscissa_lt ht
    obtain ⟨C, hC, hb⟩ := hcv.exists_bound
    exact F.exponentialRate_le_of_eventually_norm_le _ (.of_forall (F.norm_prefix_le_of_bounded_right a ht0 hC hb))

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
