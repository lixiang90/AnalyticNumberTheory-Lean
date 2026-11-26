import AnalyticNumberTheory.DirichletSeries.CahenPrefixes
import AnalyticNumberTheory.DirichletSeries.CahenTails
import AnalyticNumberTheory.DirichletSeries.FrequencyPositive

/-! # Cahen's formulas for the absolute convergence abscissa -/

noncomputable section

open Complex Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- Taking the coefficient norms turns the absolute abscissa into an ordered
convergence abscissa for the same frequency. -/
theorem absoluteAbscissa_eq_abscissa_norm :
    F.absoluteAbscissa a = F.abscissa (fun n => (‖a n‖ : ℂ)) := by
  rw [← absoluteAbscissa_eq_of_nonneg (F := F) (fun n => norm_nonneg (a n))]
  simp only [absoluteAbscissa, absConvergesAt_iff, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _)]

private lemma convergesAt_norm_zero_iff :
    F.ConvergesAt (fun n => (‖a n‖ : ℂ)) 0 ↔ Summable (fun n => ‖a n‖) := by
  have he : F.AbsConvergesAt (fun n => (‖a n‖ : ℂ)) 0 ↔ Summable (fun n => ‖a n‖) := by
    simp [absConvergesAt_iff]
  refine ⟨fun h => he.mp ?_, fun h => (he.mpr h).convergesAt⟩
  exact absConvergesAt_of_nonneg (σ := 0) (fun n => norm_nonneg (a n)) (by simpa using h)

private lemma norm_prefix (n : ℕ) :
    F.partialSum (fun k => (‖a k‖ : ℂ)) 0 n = ((∑ k ∈ Finset.range n, ‖a k‖ : ℝ) : ℂ) := by
  simp [partialSum]

/-- When the sum of the coefficient norms diverges, its prefixes give the
absolute convergence abscissa. The endpoint of each prefix is included. -/
theorem absoluteAbscissa_eq_exponentialRate_prefix (h : ¬ Summable (fun n => ‖a n‖)) :
    F.absoluteAbscissa a =
      F.exponentialRate (fun n => ((∑ k ∈ Finset.range (n+1), ‖a k‖ : ℝ) : ℂ)) := by
  rw [F.absoluteAbscissa_eq_abscissa_norm a,
    F.abscissa_eq_exponentialRate_prefix _ (fun hc => h ((F.convergesAt_norm_zero_iff a).mp hc))]
  simp only [F.norm_prefix]

/-- When the sum of the coefficient norms converges, its infinite tails give
the absolute convergence abscissa, including minus infinity. Term `n` is the
first term of the displayed tail. -/
theorem absoluteAbscissa_eq_exponentialRate_tail (h : Summable (fun n => ‖a n‖)) :
    F.absoluteAbscissa a = F.exponentialRate (fun n => ((∑' k, ‖a (k+n)‖ : ℝ) : ℂ)) := by
  have hc := (F.convergesAt_norm_zero_iff a).mpr h
  have hsum : F.sum (fun k => (‖a k‖ : ℂ)) 0 = ((∑' k, ‖a k‖ : ℝ) : ℂ) := by
    apply tendsto_nhds_unique hc.tendsto
    change Tendsto (fun n => F.partialSum (fun k => (‖a k‖ : ℂ)) 0 n) atTop _
    simpa only [Function.comp_def, F.norm_prefix] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp h.hasSum.tendsto_sum_nat
  rw [F.absoluteAbscissa_eq_abscissa_norm a, F.abscissa_eq_exponentialRate_tail _ hc]
  congr 1
  funext n
  rw [hsum, F.norm_prefix, ← Complex.ofReal_sub]
  exact congrArg Complex.ofReal (sub_eq_of_eq_add' (h.sum_add_tsum_nat_add n).symm)

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
