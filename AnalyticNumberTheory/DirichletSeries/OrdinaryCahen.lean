import AnalyticNumberTheory.DirichletSeries.CahenAbsolute

/-! # Cahen's formulas for ordinary Dirichlet series -/

noncomputable section

namespace AnalyticNumberTheory.DirichletSeries

open DirichletFrequency

/-- For an ordinary series whose unweighted coefficients diverge in their
natural order, the partial sums through `n+1` give the convergence abscissa
with denominator `log (n+1)`. The coefficient at zero is unused. -/
theorem abscissaOfConvergence_eq_prefix_rate {a : ℕ → ℂ} (h : ¬ DirichletConvergesAt a 0) :
    abscissaOfConvergence a = logarithmic.exponentialRate (fun n => coeffPartialSum a (n+1)) := by
  simpa only [logarithmic_abscissa, logarithmic_partialSum, coeffPartialSum_eq_dirichletPartialSum_zero]
    using logarithmic.abscissa_eq_exponentialRate_prefix (fun n => a (n+1))
      (fun hc => h ((logarithmic_convergesAt a 0).mp hc))

/-- For an ordinary series convergent at zero, the remainder after `n` terms
gives the convergence abscissa with denominator `log (n+1)`, also when the
abscissa is negative or minus infinity. -/
theorem abscissaOfConvergence_eq_tail_rate {a : ℕ → ℂ} (h : DirichletConvergesAt a 0) :
    abscissaOfConvergence a =
      logarithmic.exponentialRate (fun n => dirichletSum a 0 - coeffPartialSum a n) := by
  simpa only [logarithmic_abscissa, logarithmic_sum, logarithmic_partialSum,
    coeffPartialSum_eq_dirichletPartialSum_zero] using
    logarithmic.abscissa_eq_exponentialRate_tail (fun n => a (n+1)) ((logarithmic_convergesAt a 0).mpr h)

/-- The ordinary absolute abscissa from the finite sums of the positive-index
coefficient norms, when these norms have divergent sum. -/
theorem abscissaOfAbsConv_eq_prefix_rate {a : ℕ → ℂ} (h : ¬ Summable (fun k => ‖a (k+1)‖)) :
    LSeries.abscissaOfAbsConv a =
      logarithmic.exponentialRate (fun n => ((∑ k ∈ Finset.range (n+1), ‖a (k+1)‖ : ℝ) : ℂ)) := by
  simpa only [logarithmic_absoluteAbscissa] using
    logarithmic.absoluteAbscissa_eq_exponentialRate_prefix (fun k => a (k+1)) h

/-- The ordinary absolute abscissa from the sum of coefficient norms starting
at `n+1`, when their total mass is finite. -/
theorem abscissaOfAbsConv_eq_tail_rate {a : ℕ → ℂ} (h : Summable (fun k => ‖a (k+1)‖)) :
    LSeries.abscissaOfAbsConv a =
      logarithmic.exponentialRate (fun n => ((∑' k, ‖a (k+n+1)‖ : ℝ) : ℂ)) := by
  simpa only [logarithmic_absoluteAbscissa] using
    logarithmic.absoluteAbscissa_eq_exponentialRate_tail (fun k => a (k+1)) h

end AnalyticNumberTheory.DirichletSeries
