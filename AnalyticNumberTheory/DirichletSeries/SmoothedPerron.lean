import AnalyticNumberTheory.DirichletSeries.FrequencyDensity
import AnalyticNumberTheory.DirichletSeries.FrequencyVerticalBounds

/-! # Transfer of inverse vertical kernels to arbitrary Dirichlet frequencies -/

noncomputable section

open Complex Filter MeasureTheory Finset Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- On a line of absolute convergence an integrable function of the height
may be multiplied by the series. Integration commutes with ordered partial sums. -/
theorem integrable_tendsto_integral_partialSum_mul {σ : ℝ} (h : F.AbsConvergesAt a (σ : ℂ))
    {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun t : ℝ => F.sum a ((σ : ℂ)+t*I) * g t) ∧
    Tendsto (fun N => ∫ t : ℝ, F.partialSum a ((σ : ℂ)+t*I) N * g t) atTop
      (𝓝 (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * g t)) := by
  let A := ∑' n, ‖a n‖ * Real.exp (-σ*F n)
  have hmass : Summable (fun n => ‖a n‖ * Real.exp (-σ*F n)) := by
    simpa only [Complex.ofReal_re] using (F.absConvergesAt_iff (a := a) (s := (σ : ℂ))).mp h
  let B := fun t : ℝ => A * ‖g t‖
  have hB : Integrable B := hg.norm.const_mul A
  have hm (N : ℕ) : AEStronglyMeasurable (fun t : ℝ => F.partialSum a ((σ : ℂ)+t*I) N * g t) := by
    have hc : Continuous (fun t : ℝ => F.partialSum a ((σ : ℂ)+t*I) N) := by unfold partialSum; fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have he (t : ℝ) : Tendsto (fun N => F.partialSum a ((σ : ℂ)+t*I) N * g t) atTop
      (𝓝 (F.sum a ((σ : ℂ)+t*I) * g t)) :=
    ((h.of_re_le (w := (σ : ℂ)+t*I) (by simp)).convergesAt.tendsto).mul_const _
  have hb (N : ℕ) (t : ℝ) : ‖F.partialSum a ((σ : ℂ)+t*I) N * g t‖ ≤ B t := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (F.norm_partialSum_le_of_re_ge a (β := σ) (by simp) N).trans
      (hmass.sum_le_tsum _ (fun _ _ => by positivity))
  refine ⟨hB.mono' (aestronglyMeasurable_of_tendsto_ae _ hm (ae_of_all _ he)) ?_,
    tendsto_integral_of_dominated_convergence B hm hB (fun N => ae_of_all _ (hb N)) (ae_of_all _ he)⟩
  exact ae_of_all _ fun t => le_of_tendsto (he t).norm (.of_forall fun N => hb N t)

/-- Inverting a vertical denominator termwise translates its inverse kernel
by each frequency of a Dirichlet polynomial. -/
theorem integral_partialSum_smoothedPerron (D : ℂ → ℂ) (w : ℝ → ℂ) (σ : ℝ)
    (hK : ∀ v : ℝ, Integrable (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*v)/D ((σ : ℂ)+t*I)))
    (hw : ∀ v : ℝ, (∫ t : ℝ, Complex.exp (((σ : ℂ)+t*I)*v)/D ((σ : ℂ)+t*I))/(2*Real.pi) = w v)
    (u : ℝ) (N : ℕ) :
    (∫ t : ℝ, F.partialSum a ((σ : ℂ)+t*I) N * (Complex.exp (((σ : ℂ)+t*I)*u)/D ((σ : ℂ)+t*I))) /
      (2*Real.pi) = ∑ n ∈ range N, a n * w (u-F n) := by
  have he (t : ℝ) :
      F.partialSum a ((σ : ℂ)+t*I) N * (Complex.exp (((σ : ℂ)+t*I)*u)/D ((σ : ℂ)+t*I)) =
      ∑ n ∈ range N, a n * (Complex.exp (((σ : ℂ)+t*I)*((u-F n : ℝ) : ℂ))/D ((σ : ℂ)+t*I)) := by
    simp only [partialSum, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    let z := (σ : ℂ)+t*I
    have hshift : Complex.exp (z*((u : ℂ)-F n)) = Complex.exp (-z*F n)*Complex.exp (z*u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [Complex.ofReal_sub]
    change a n * Complex.exp (-z*F n) * (Complex.exp (z*u)/D z) =
      a n * (Complex.exp (z*((u : ℂ)-F n))/D z)
    rw [hshift]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun n _ => (hK (u-F n)).const_mul (a n)), sum_div]
  refine sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, mul_div_assoc, hw]

/-- If the inverse kernel vanishes on the negative axis, its integral against
an absolutely convergent general Dirichlet series is a finite weighted sum. -/
theorem smoothedPerron_formula (D : ℂ → ℂ) (w : ℝ → ℂ) {σ : ℝ} (h : F.AbsConvergesAt a (σ : ℂ))
    (hK : ∀ v : ℝ, Integrable (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*v)/D ((σ : ℂ)+t*I)))
    (hw : ∀ v : ℝ, (∫ t : ℝ, Complex.exp (((σ : ℂ)+t*I)*v)/D ((σ : ℂ)+t*I))/(2*Real.pi) = w v)
    (hneg : ∀ v < 0, w v = 0) (u : ℝ) :
    (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * (Complex.exp (((σ : ℂ)+t*I)*u)/D ((σ : ℂ)+t*I))) /
      (2*Real.pi) = ∑ n ∈ range (F.count u), a n * w (u-F n) := by
  apply tendsto_nhds_unique ((F.integrable_tendsto_integral_partialSum_mul a h (hK u)).2.div_const (2*Real.pi : ℂ))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (F.count u)] with N hN
  rw [F.integral_partialSum_smoothedPerron a D w σ hK hw u N]
  apply sum_subset (range_mono hN)
  intro n _ hn
  have hu : u < F n := lt_of_not_ge fun hle => hn (mem_range.mpr (F.lt_count_iff.mpr hle))
  rw [hneg _ (sub_neg.mpr hu), mul_zero]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
