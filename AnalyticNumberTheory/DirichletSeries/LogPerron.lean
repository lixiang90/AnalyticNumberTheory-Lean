import AnalyticNumberTheory.DirichletSeries.RightHalfPlaneLowerBound
import AnalyticNumberTheory.DirichletSeries.SmoothedPerron
import AnalyticNumberTheory.DirichletSeries.LogPerronKernel

/-! # Logarithmically weighted Perron inversion for general Dirichlet series -/

noncomputable section

open Complex Filter MeasureTheory Finset Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- Each term of a finite exponential polynomial acquires its positive-part
weight when integrated against the squared Perron denominator. -/
theorem integral_partialSum_logPerron {σ : ℝ} (hσ : 0 < σ) (u : ℝ) (N : ℕ) :
    (∫ t : ℝ, F.partialSum a ((σ : ℂ)+t*I) N * logPerronKernel σ u t)/(2*Real.pi) =
      ∑ n ∈ range N, a n * ((max (u-F n) 0 : ℝ) : ℂ) :=
  F.integral_partialSum_smoothedPerron a (fun z => z^2) (fun v => ((max v 0 : ℝ) : ℂ)) σ
    (integrable_logPerronKernel hσ) (integral_logPerronKernel hσ) u N

/-- On an absolute line the sum at every height is bounded by the real sum of
the norms of the terms on that line. -/
theorem norm_sum_absolute_line_le {σ : ℝ} (h : F.AbsConvergesAt a (σ : ℂ)) (t : ℝ) :
    ‖F.sum a ((σ : ℂ)+t*I)‖ ≤ ∑' n, ‖a n‖ * Real.exp (-σ*F n) :=
  h.norm_sum_le_right_halfPlane (by simp)

/-- An absolute vertical line bounds the squared-denominator integrand in `L¹`,
even when the absolute abscissa itself lies on that line. -/
theorem integrable_sum_logPerron {σ : ℝ} (hσ : 0 < σ) (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    Integrable (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t) :=
  (F.integrable_tendsto_integral_partialSum_mul a h (integrable_logPerronKernel hσ u)).1

/-- Logarithmically smoothed Perron inversion at every real frequency cutoff.
An exponent equal to the cutoff has zero weight. Only absolute convergence on
the chosen line and positivity of its real part are required. -/
theorem logPerron_formula {σ : ℝ} (hσ : 0 < σ) (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t)/(2*Real.pi) =
      ∑ n ∈ range (F.count u), a n * ((u-F n : ℝ) : ℂ) := by
  have H := F.smoothedPerron_formula a (fun z => z^2) (fun v => ((max v 0 : ℝ) : ℂ)) h
    (integrable_logPerronKernel hσ) (integral_logPerronKernel hσ)
    (fun v hv => by simp [max_eq_right hv.le]) u
  apply H.trans
  refine sum_congr rfl fun n hn => ?_
  rw [max_eq_left (sub_nonneg.mpr (F.lt_count_iff.mp (mem_range.mp hn)))]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
