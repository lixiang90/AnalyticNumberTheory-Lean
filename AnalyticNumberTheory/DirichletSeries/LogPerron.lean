import AnalyticNumberTheory.DirichletSeries.FrequencyDensity
import AnalyticNumberTheory.DirichletSeries.LogPerronKernel

/-! # Logarithmically weighted Perron inversion for general Dirichlet series -/

noncomputable section

open Complex Filter MeasureTheory Finset Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

private lemma partialSum_mul_logPerronKernel (σ u t : ℝ) (N : ℕ) :
    F.partialSum a ((σ : ℂ)+t*I) N * logPerronKernel σ u t =
      ∑ n ∈ range N, a n * logPerronKernel σ (u-F n) t := by
  simp only [partialSum, sum_mul]
  refine sum_congr rfl fun n _ => ?_
  let z := (σ : ℂ)+t*I
  have he : Complex.exp (z*((u : ℂ)-F n)) = Complex.exp (-z*F n)*Complex.exp (z*u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  dsimp only [logPerronKernel]
  rw [Complex.ofReal_sub]
  change a n * Complex.exp (-z*F n) * (Complex.exp (z*u)/z^2) =
    a n * (Complex.exp (z*((u : ℂ)-F n))/z^2)
  rw [he]
  ring

/-- Each term of a finite exponential polynomial acquires its positive-part
weight when integrated against the squared Perron denominator. -/
theorem integral_partialSum_logPerron {σ : ℝ} (hσ : 0 < σ) (u : ℝ) (N : ℕ) :
    (∫ t : ℝ, F.partialSum a ((σ : ℂ)+t*I) N * logPerronKernel σ u t)/(2*Real.pi) =
      ∑ n ∈ range N, a n * ((max (u-F n) 0 : ℝ) : ℂ) := by
  simp_rw [F.partialSum_mul_logPerronKernel]
  rw [integral_finsetSum _ (fun n _ => (integrable_logPerronKernel hσ (u-F n)).const_mul (a n)), sum_div]
  apply sum_congr rfl
  intro n _
  rw [integral_const_mul, mul_div_assoc, integral_logPerronKernel hσ]

private lemma norm_partialSum_absolute_line {σ : ℝ} (h : F.AbsConvergesAt a (σ : ℂ)) (t : ℝ) (N : ℕ) :
    ‖F.partialSum a ((σ : ℂ)+t*I) N‖ ≤ ∑' n, ‖a n‖ * Real.exp (-σ*F n) := by
  have hsum : Summable (fun n => ‖a n‖ * Real.exp (-σ*F n)) := by
    simpa only [Complex.ofReal_re] using (F.absConvergesAt_iff (s := (σ : ℂ)) (a := a)).mp h
  unfold partialSum
  apply (norm_sum_le ..).trans
  calc _ = ∑ n ∈ range N, ‖a n‖ * Real.exp (-σ*F n) := by simp [Complex.norm_exp, Complex.mul_re]
       _ ≤ _ := hsum.sum_le_tsum _ (fun n _ => by positivity)

/-- On an absolute line the sum at every height is bounded by the real sum of
the norms of the terms on that line. -/
theorem norm_sum_absolute_line_le {σ : ℝ} (h : F.AbsConvergesAt a (σ : ℂ)) (t : ℝ) :
    ‖F.sum a ((σ : ℂ)+t*I)‖ ≤ ∑' n, ‖a n‖ * Real.exp (-σ*F n) :=
  le_of_tendsto ((h.of_re_le (w := (σ : ℂ)+t*I) (by simp)).convergesAt.tendsto.norm)
    (.of_forall (F.norm_partialSum_absolute_line a h t))

private lemma logPerron_dominated_limit {σ : ℝ} (hσ : 0 < σ) (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    Integrable (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t) ∧
    Tendsto (fun N => ∫ t : ℝ, F.partialSum a ((σ : ℂ)+t*I) N * logPerronKernel σ u t) atTop
      (𝓝 (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t)) := by
  let g := fun N (t : ℝ) => F.partialSum a ((σ : ℂ)+t*I) N * logPerronKernel σ u t
  have hm (N : ℕ) : AEStronglyMeasurable (g N) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul _ (continuous_logPerronKernel hσ u)
    unfold partialSum
    fun_prop
  have he (t : ℝ) : Tendsto (fun N => g N t) atTop
      (𝓝 (F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t)) :=
    ((h.of_re_le (s := (σ : ℂ)) (w := (σ : ℂ)+t*I) (by simp)).convergesAt.tendsto).mul_const _
  let B := fun t : ℝ => (∑' n, ‖a n‖ * Real.exp (-σ*F n)) * ‖logPerronKernel σ u t‖
  have hB : Integrable B := (integrable_logPerronKernel hσ u).norm.const_mul _
  have hbound (N : ℕ) (t : ℝ) : ‖g N t‖ ≤ B t := (norm_mul _ _).le.trans
    (mul_le_mul_of_nonneg_right (F.norm_partialSum_absolute_line a h t N) (norm_nonneg _))
  refine ⟨hB.mono' (aestronglyMeasurable_of_tendsto_ae _ hm (ae_of_all _ he)) ?_,
    tendsto_integral_of_dominated_convergence B hm hB (fun N => ae_of_all _ (hbound N)) (ae_of_all _ he)⟩
  exact ae_of_all _ fun t => le_of_tendsto (he t).norm (.of_forall fun N => hbound N t)

/-- An absolute vertical line bounds the squared-denominator integrand in `L¹`,
even when the absolute abscissa itself lies on that line. -/
theorem integrable_sum_logPerron {σ : ℝ} (hσ : 0 < σ) (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    Integrable (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t) :=
  (F.logPerron_dominated_limit a hσ h u).1

/-- Logarithmically smoothed Perron inversion at every real frequency cutoff.
An exponent equal to the cutoff has zero weight. Only absolute convergence on
the chosen line and positivity of its real part are required. -/
theorem logPerron_formula {σ : ℝ} (hσ : 0 < σ) (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * logPerronKernel σ u t)/(2*Real.pi) =
      ∑ n ∈ range (F.count u), a n * ((u-F n : ℝ) : ℂ) := by
  apply tendsto_nhds_unique ((F.logPerron_dominated_limit a hσ h u).2.div_const (2*Real.pi : ℂ))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (F.count u)] with N hN
  rw [F.integral_partialSum_logPerron a hσ]
  symm
  calc
    _ = ∑ n ∈ range (F.count u), a n * ((max (u-F n) 0 : ℝ) : ℂ) := by
      symm
      apply sum_subset (range_mono hN)
      intro n _ hn
      have hneg := le_of_not_ge (fun hn' : F n ≤ u => hn (mem_range.mpr (F.lt_count_iff.mpr hn')))
      simp [max_eq_right (sub_nonpos.mpr hneg)]
    _ = _ := by
      refine sum_congr rfl fun n hn => ?_
      rw [max_eq_left (sub_nonneg.mpr (F.lt_count_iff.mp (mem_range.mp hn)))]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
