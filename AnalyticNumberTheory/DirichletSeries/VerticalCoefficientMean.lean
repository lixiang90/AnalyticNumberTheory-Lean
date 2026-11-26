import AnalyticNumberTheory.AnalyticTools.IntervalMeans
import AnalyticNumberTheory.DirichletSeries.FrequencyDensity

/-! # Coefficient recovery by vertical means of general Dirichlet series -/

noncomputable section

open Complex Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℂ} {σ : ℝ}

/-- On a line of absolute convergence the sum has an absolutely summable
exponential expansion in the height variable. Multiplication by a frequency
`u` translates all the frequencies by `u`. -/
theorem AbsConvergesAt.vertical_expansion (h : F.AbsConvergesAt a (σ : ℂ)) (u t : ℝ) :
    F.sum a ((σ : ℂ) + t * I) * Complex.exp (((σ : ℂ) + t * I) * u) =
      ∑' n, (a n * (Real.exp (σ * (u-F n)) : ℂ)) * Complex.exp (((u-F n)*t : ℝ) * I) := by
  have ht : F.AbsConvergesAt a ((σ : ℂ) + t * I) := h.of_re_le (by simp)
  rw [ht.sum_eq_tsum, ← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [mul_assoc, ← Complex.exp_add, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- On any sequence or family of growing intervals, the vertical mean at a
frequency recovers its coefficient and vanishes at an absent frequency. -/
theorem tendsto_vertical_interval_frequency_mean {α : Type*} {l : Filter α}
    (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) (x y : α → ℝ)
    (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (fun t : ℝ =>
      F.sum a ((σ : ℂ) + t * I) * Complex.exp (((σ : ℂ) + t * I) * u)) (x k) (y k)) l
      (𝓝 (∑' n, if F n = u then a n else 0)) := by
  let c (n : ℕ) := a n * (Real.exp (σ * (u-F n)) : ℂ)
  let ω (n : ℕ) := u - F n
  have hc : Summable (fun n => ‖c n‖) := by
    apply ((F.absConvergesAt_iff.mp h).mul_right (Real.exp (σ*u))).congr
    intro n
    dsimp only [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ofReal_re,
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have H := tendsto_intervalMean_expansion c ω hc x y hlen
  have hg : (∑' n, if ω n = 0 then c n else 0) = (∑' n, if F n = u then a n else 0) := by
    apply tsum_congr
    intro n
    by_cases hn : F n = u
    · simp [ω,c,hn]
    · simp [ω,sub_ne_zero.mpr (Ne.symm hn),hn]
  rw [hg] at H
  have hfun : (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * Complex.exp (((σ : ℂ)+t*I)*u)) = exponentialSeries c ω := by
    funext t
    exact h.vertical_expansion u t
  rw [hfun]
  exact H

/-- Bohr's formula for a specified coefficient on intervals with arbitrary
endpoints whose difference tends to infinity. -/
theorem tendsto_vertical_interval_coefficient {α : Type*} {l : Filter α}
    (h : F.AbsConvergesAt a (σ : ℂ)) (n : ℕ) (x y : α → ℝ)
    (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (fun t : ℝ =>
      F.sum a ((σ : ℂ) + t * I) * Complex.exp (((σ : ℂ) + t * I) * F n)) (x k) (y k)) l (𝓝 (a n)) := by
  simpa only [F.strictMono.injective.eq_iff, tsum_ite_eq] using
    tendsto_vertical_interval_frequency_mean h (F n) x y hlen

/-- The symmetric vertical mean at an arbitrary real frequency `u` recovers
the matching coefficient and vanishes when `u` is outside the frequency sequence. -/
theorem tendsto_vertical_frequency_mean (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    Tendsto (symmetricMean (fun t : ℝ =>
      F.sum a ((σ : ℂ) + t * I) * Complex.exp (((σ : ℂ) + t * I) * u))) atTop
      (𝓝 (∑' n, if F n = u then a n else 0)) := by
  have hlen : Tendsto (fun T : ℝ => T - -T) atTop atTop := by
    simpa only [id_eq, sub_neg_eq_add, two_mul] using
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  simpa only [id_eq, intervalMean_neg_self] using
    tendsto_vertical_interval_frequency_mean h u (fun T => -T) id hlen

/-- Bohr's coefficient formula on every line of absolute convergence,
including a boundary line if the series is absolutely convergent there. -/
theorem tendsto_vertical_coefficient (h : F.AbsConvergesAt a (σ : ℂ)) (k : ℕ) :
    Tendsto (symmetricMean (fun t : ℝ =>
      F.sum a ((σ : ℂ) + t * I) * Complex.exp (((σ : ℂ) + t * I) * F k))) atTop (𝓝 (a k)) := by
  have H := tendsto_vertical_frequency_mean h (F k)
  simpa only [F.strictMono.injective.eq_iff, tsum_ite_eq] using H

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
