import AnalyticNumberTheory.DirichletSeries.VerticalCoefficientMean
import AnalyticNumberTheory.AnalyticTools.MixedIntervalMeans

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

private lemma reflected_line_expansion (h : F.AbsConvergesAt a (σ : ℂ)) (t : ℝ) :
    F.sum a ((σ : ℂ) - t*I) = exponentialSeries
      (fun n => a n * (Real.exp (-σ*F n) : ℂ)) (fun n => -F n) (-t) := by
  simpa [sub_eq_add_neg] using line_expansion h (-t)

/-- The bilinear mean with opposite heights on two possibly different
frequency sequences. Only pairs with equal exponents survive on any family
of intervals whose lengths tend to infinity. -/
theorem tendsto_vertical_interval_matching_mean {G : DirichletFrequency} {α : Type*} {l : Filter α}
    (ha : F.AbsConvergesAt a (σ : ℂ)) (hb : G.AbsConvergesAt b (τ : ℂ))
    (x y : α → ℝ) (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * G.sum b ((τ : ℂ)-t*I))
      (x k) (y k)) l (𝓝 (∑' p : ℕ × ℕ, if F p.1 = G p.2 then
        a p.1 * b p.2 * (Real.exp (-(σ+τ)*F p.1) : ℂ) else 0)) := by
  have H := tendsto_intervalMean_mul_reflected _ _ (fun n => -F n) (fun n => -G n)
    (line_summable ha) (line_summable hb) x y hlen
  simp only [← line_expansion ha, ← reflected_line_expansion hb, neg_inj] at H
  convert H using 2
  apply tsum_congr
  intro p
  by_cases he : F p.1 = G p.2
  · simp only [he, ↓reduceIte]
    rw [show -(σ+τ)*G p.2 = -σ*G p.2 + -τ*G p.2 by ring, Real.exp_add, Complex.ofReal_mul]
    ring
  · simp [he]

/-- The moving-interval mixed mean for a common frequency sequence. The
opposite heights pair the complex coefficients bilinearly, and the diagonal
weight contains the sum of the two real arguments. -/
theorem tendsto_vertical_interval_bilinear_mean {α : Type*} {l : Filter α}
    (ha : F.AbsConvergesAt a (σ : ℂ)) (hb : F.AbsConvergesAt b (τ : ℂ))
    (x y : α → ℝ) (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * F.sum b ((τ : ℂ)-t*I))
      (x k) (y k)) l (𝓝 (∑' n, a n * b n * (Real.exp (-(σ+τ)*F n) : ℂ))) := by
  have H := tendsto_intervalMean_mul_reflected_diagonal _ _ (fun n => -F n)
    (injective_neg_frequency F) (line_summable ha) (line_summable hb) x y hlen
  simp only [← line_expansion ha, ← reflected_line_expansion hb] at H
  convert H using 2
  apply tsum_congr
  intro n
  rw [show -(σ+τ)*F n = -σ*F n + -τ*F n by ring, Real.exp_add, Complex.ofReal_mul]
  ring

/-- The mean square of a general Dirichlet series on a line of absolute
convergence has the same diagonal limit on every family of growing intervals. -/
theorem tendsto_vertical_interval_mean_square {α : Type*} {l : Filter α}
    (h : F.AbsConvergesAt a (σ : ℂ)) (x y : α → ℝ) (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => (∫ t : ℝ in x k..y k, ‖F.sum a ((σ : ℂ)+t*I)‖^2) / (y k - x k)) l
      (𝓝 (∑' n, ‖a n‖^2 * Real.exp (-2*σ*F n))) := by
  let c (n : ℕ) := a n * (Real.exp (-σ*F n) : ℂ)
  have hc : Summable (fun n => ‖c n‖) := line_summable h
  have hd : Summable (fun n => ‖conj (c n)‖) := by simpa only [Complex.norm_conj] using hc
  have H := tendsto_intervalMean_mul_reflected_diagonal c (fun n => conj (c n)) (fun n => -F n)
    (injective_neg_frequency F) hc hd x y hlen
  simp only [exponentialSeries_neg_time, conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_tsum, intervalMean, intervalIntegral.integral_ofReal, ← Complex.ofReal_div] at H
  have HR := Complex.continuous_re.continuousAt.tendsto.comp H
  simp only [Function.comp_def, Complex.ofReal_re] at HR
  change Tendsto (fun k => _) l _ at HR
  simp only [c, ← line_expansion h] at HR
  convert HR using 2
  apply tsum_congr
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    sq (Real.exp _), ← Real.exp_add, show -2*σ*F n = -σ*F n + -σ*F n by ring]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
