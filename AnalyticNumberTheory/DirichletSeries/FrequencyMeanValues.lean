import AnalyticNumberTheory.DirichletSeries.VerticalCoefficientMean
import AnalyticNumberTheory.AnalyticTools.ExponentialMeanSquare

/-! # Vertical mixed and second moments of general Dirichlet series -/

noncomputable section

open Complex Filter
open scoped Topology ComplexConjugate
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a b : ℕ → ℂ} {σ τ : ℝ}

private lemma line_expansion (h : F.AbsConvergesAt a (σ : ℂ)) (t : ℝ) :
    F.sum a ((σ : ℂ) + t*I) = exponentialSeries
      (fun n => a n * (Real.exp (-σ*F n) : ℂ)) (fun n => -F n) t := by
  simpa [exponentialSeries] using h.vertical_expansion 0 t

private lemma line_summable (h : F.AbsConvergesAt a (σ : ℂ)) :
    Summable (fun n => ‖a n * (Real.exp (-σ*F n) : ℂ)‖) := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.ofReal_re] using (F.absConvergesAt_iff.mp h)

private lemma injective_neg_frequency (F : DirichletFrequency) : Function.Injective (fun n => -F n) :=
  fun _ _ h => F.strictMono.injective (neg_injective h)

/-- The mixed vertical mean for two general Dirichlet series on any two lines
of absolute convergence. The surviving diagonal carries the sum of the two abscissae. -/
theorem tendsto_vertical_mixed_mean (ha : F.AbsConvergesAt a (σ : ℂ)) (hb : F.AbsConvergesAt b (τ : ℂ)) :
    Tendsto (symmetricMean (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * conj (F.sum b ((τ : ℂ)+t*I))))
      atTop (𝓝 (∑' n, a n * conj (b n) * (Real.exp (-(σ+τ)*F n) : ℂ))) := by
  have H := tendsto_symmetricMean_mul_conj (fun n => a n * (Real.exp (-σ*F n) : ℂ))
    (fun n => b n * (Real.exp (-τ*F n) : ℂ)) (fun n => -F n) (injective_neg_frequency F) (line_summable ha) (line_summable hb)
  simp only [← line_expansion ha, ← line_expansion hb] at H
  convert H using 2
  apply tsum_congr
  intro n
  rw [map_mul,Complex.conj_ofReal,show -(σ+τ)*F n = -σ*F n + -τ*F n by ring,
    Real.exp_add,Complex.ofReal_mul]
  ring

/-- The vertical mean square on an absolutely convergent line of a general
Dirichlet series equals the exponentially weighted diagonal sum. -/
theorem tendsto_vertical_mean_square (h : F.AbsConvergesAt a (σ : ℂ)) :
    Tendsto (fun T : ℝ => (∫ t : ℝ in -T..T, ‖F.sum a ((σ : ℂ)+t*I)‖^2) / (2*T))
      atTop (𝓝 (∑' n, ‖a n‖^2 * Real.exp (-2*σ*F n))) := by
  have H := tendsto_meanSquare_exponentialSeries (fun n => a n * (Real.exp (-σ*F n) : ℂ))
    (fun n => -F n) (injective_neg_frequency F) (line_summable h)
  simp only [← line_expansion h] at H
  convert H using 2
  apply tsum_congr
  intro n
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,
    sq (Real.exp _), ← Real.exp_add, show -2*σ*F n = -σ*F n + -σ*F n by ring]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
