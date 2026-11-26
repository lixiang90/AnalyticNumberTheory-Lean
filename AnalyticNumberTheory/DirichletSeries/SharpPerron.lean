import AnalyticNumberTheory.DirichletSeries.PerronKernelUniform

/-!
# Pointwise sharp Perron inversion

On a positive line of absolute convergence, symmetric truncations recover the partial sum at
every positive cutoff, with half the coefficient at a jump. At a fixed cutoff and abscissa
the error is bounded by a constant times the reciprocal of the truncation height.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries

/-- The positive-index partial sum with half the last coefficient if `x` is an integer. -/
def midpointPartialSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, if (n : ℝ) = x then (1/2 : ℂ) * a n else a n

/-- The sharp vertical Perron integral on a line of absolute convergence is bounded
independently of the height, uniformly for cutoffs in bounded positive intervals. -/
theorem norm_dirichletContourIntegral_le {a : ℕ → ℂ} {x c T : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hT : 0 < T) (ha : LSeriesSummable a (c : ℂ)) :
    ‖dirichletContourIntegral a x c T‖ ≤ (2*x^c) * ∑' n, ‖LSeries.term a (c : ℂ) n‖ := by
  rw [dirichletContourIntegral_eq_tsum hx hc hT.le ha]
  let f (n : ℕ) := if n = 0 then 0 else a n * perronKernel (x/n) c T
  have hm (n : ℕ) : ‖f n‖ ≤ (2*x^c) * ‖LSeries.term a (c : ℂ) n‖ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    have hn₀ : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [show f n = _ from ite_eq_right hn, norm_mul, LSeries.norm_term_eq, ite_eq_right hn, Complex.ofReal_re]
    apply (mul_le_mul_of_nonneg_left (norm_perronKernel_le_two_mul_rpow (div_pos hx hn₀) hc hT) (norm_nonneg _)).trans_eq
    rw [Real.div_rpow hx.le hn₀.le]
    ring
  have hs := ha.norm.mul_left (2*x^c)
  have hf := hs.of_nonneg_of_le (fun n => norm_nonneg (f n)) hm
  exact (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum hm hs).trans_eq tsum_mul_left)

/-- Sharp Perron inversion has a reciprocal-height error at each fixed cutoff, including
an integer cutoff. The constant may depend on the coefficients, the line and the cutoff. -/
theorem norm_dirichletContourIntegral_sub_midpointPartialSum_le {a : ℕ → ℂ} {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ)) :
    ∃ C : ℝ, ∀ T : ℝ, 0 < T →
      ‖dirichletContourIntegral a x c T - midpointPartialSum a x‖ ≤ C / T := by
  let A := x ^ c / (Real.pi * Real.log 2) * ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖
  let B := ∑ n ∈ Icc 1 ⌊2*x⌋₊, if x/2 ≤ n ∧ (n : ℝ) ≠ x then
    ‖a n‖ * ((x / n) ^ c / (Real.pi * |Real.log (x / n)|)) else 0
  let D := ∑ n ∈ Icc 1 ⌊2*x⌋₊, if (n : ℝ) = x then ‖a n‖ * (c / Real.pi) else 0
  refine ⟨A + B + D, fun T hT => (perron_truncated_sum_with_half hx hc hT ha).trans_eq ?_⟩
  simp only [A, B, D, add_div, sum_div]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp [div_eq_mul_inv, mul_inv_rev]
    ring
  · refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Symmetric vertical truncations of the sharp Perron integral converge to the midpoint
partial sum for every `x > 0` on any positive line of absolute convergence. -/
theorem tendsto_dirichletContourIntegral_midpointPartialSum {a : ℕ → ℂ} {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) (ha : LSeriesSummable a (c : ℂ)) :
    Tendsto (dirichletContourIntegral a x c) atTop (𝓝 (midpointPartialSum a x)) := by
  obtain ⟨C, hC⟩ := norm_dirichletContourIntegral_sub_midpointPartialSum_le hx hc ha
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 0 (C / ε))] with T hT
  have hT0 := (le_max_left 0 _).trans_lt hT
  rw [dist_eq_norm]
  apply (hC T hT0).trans_lt
  rw [div_lt_iff₀ hT0, mul_comm ε]
  exact (div_lt_iff₀ hε).mp ((le_max_right 0 _).trans_lt hT)

end AnalyticNumberTheory.DirichletSeries
