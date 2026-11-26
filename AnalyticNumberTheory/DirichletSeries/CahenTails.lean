import AnalyticNumberTheory.DirichletSeries.CenteredAbel
import AnalyticNumberTheory.DirichletSeries.ExponentialRate

/-! # Cahen's formula from coefficient tails -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- A bound on the remainder before the first omitted frequency gives
convergence at every point to the right of its nonpositive decay exponent. -/
theorem convergesAt_of_tail_bound {M : ℂ} {C r : ℝ} (hC : 0 ≤ C) (hr : r ≤ 0)
    (h : ∀ n, ‖M - F.partialSum a 0 n‖ ≤ C * Real.exp (r * F n))
    {s : ℂ} (hs : r < s.re) : F.ConvergesAt a s := by
  have hb (u : ℝ) (_ : F 0 ≤ u) : ‖F.summatory a 0 u - M‖ ≤ C * Real.exp (r * u) := by
    have hu : u < F (F.count u) := lt_of_not_ge fun hle => (lt_irrefl _) (F.lt_count_iff.mpr hle)
    rw [norm_sub_rev, summatory]
    exact (h (F.count u)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.le hr)) hC)
  obtain ⟨L, hL⟩ : F.ConvergesAt a (0 + s) :=
    ⟨_, F.tendsto_partialSum_centered_integral a hb hs⟩
  exact ⟨L, by simpa using hL⟩

/-- Bounded partial sums at a real negative argument control the coefficient
tail by the exponential of its first omitted frequency. Approaching that
frequency from the left keeps the estimate valid across arbitrarily large gaps. -/
theorem norm_tail_le_of_bounded_left {r C : ℝ} (hr : r < 0)
    (h : ∀ u, ‖F.summatory a (r : ℂ) u‖ ≤ C) (n : ℕ) :
    ‖F.sum a 0 - F.partialSum a 0 (n+1)‖ ≤ C * 2 * Real.exp (r * F (n+1)) := by
  have hb (u : ℝ) (hu : F 0 ≤ u) : ‖F.summatory a 0 u - F.sum a 0‖ ≤
      C * 2 * Real.exp (r * u) := by
    have H := F.norm_summatory_sub_sum_le a (s₀ := (r : ℂ)) (z := -(r : ℂ)) (α := 0)
      (fun v _ => by simpa using h v) (by simpa using neg_pos.mpr hr) hu
    have hz : ‖-(r : ℂ)‖ = -r := by simp [abs_of_neg hr]
    simpa [hz, hr.ne, one_add_one_eq_two] using H
  have hc : Continuous (fun u : ℝ => C * 2 * Real.exp (r * u)) := by fun_prop
  apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] F (n+1) ≤ 𝓝 (F (n+1))))
  filter_upwards [Ioo_mem_nhdsLT (F.strictMono (Nat.lt_succ_self n))] with y hy
  have H := hb y ((F.strictMono.monotone (Nat.zero_le n)).trans hy.1.le)
  simpa only [summatory, F.count_eq_succ hy.1.le hy.2, norm_sub_rev (F.sum a 0)] using H

/-- If the coefficient series converges at zero, the ordered convergence
abscissa is the upper exponential rate of its remainders. Index `n` denotes
the first term omitted from the partial sum. The equality holds in the
extended reals and includes an abscissa of minus infinity. -/
theorem abscissa_eq_exponentialRate_tail (h0 : F.ConvergesAt a 0) :
    F.abscissa a = F.exponentialRate (fun n => F.sum a 0 - F.partialSum a 0 n) := by
  let g (n : ℕ) := F.sum a 0 - F.partialSum a 0 n
  have hσ : F.abscissa a ≤ (0 : EReal) := by simpa using abscissa_le_re h0
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact hσ.trans (EReal.coe_nonneg.mpr ht0)
    obtain ⟨r, hr, hrt⟩ := EReal.exists_between_coe_real ht
    obtain ⟨C, hC, h⟩ := F.exists_bound_of_exponentialRate_lt g hr
    have hrt' := EReal.coe_lt_coe_iff.mp hrt
    exact abscissa_le_re (s := (t : ℂ)) (F.convergesAt_of_tail_bound a hC
      (hrt'.le.trans (le_of_not_ge ht0)) h hrt')
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    by_cases ht0 : t < 0
    · have hcv : F.ConvergesAt a (t : ℂ) := convergesAt_of_abscissa_lt ht
      obtain ⟨C, _, hC⟩ := hcv.exists_bound
      apply F.exponentialRate_le_of_eventually_norm_le g (C := C * 2)
      filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact F.norm_tail_le_of_bounded_left a ht0 hC k
    · have hlim : Tendsto g atTop (𝓝 (F.sum a 0 - F.sum a 0)) := tendsto_const_nhds.sub h0.tendsto
      obtain ⟨C, hC⟩ := hlim.norm.bddAbove_range
      have hrate := F.exponentialRate_le_of_eventually_norm_le g (t := 0) (C := C)
        (.of_forall fun n => by simpa using hC ⟨n, rfl⟩)
      exact hrate.trans (EReal.coe_le_coe_iff.mpr (le_of_not_gt ht0))

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
