import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin

/-! # Sharp bounds and integration of periodic Bernoulli kernels -/

noncomputable section

open Complex MeasureTheory Set
open scoped Nat

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- The absolute maximum of an even periodic Bernoulli kernel is attained
at each integer. The cosine Fourier series gives the sharp constant. -/
theorem abs_bernoulliKernel_even_le {m : ℕ} (hm : 0 < m) (x : ℝ) :
    |bernoulliKernel (2*m) x| ≤ |bernoulliKernel (2*m) 0| := by
  let C := (-1 : ℝ)^(m+1) * (2*Real.pi)^(2*m) / 2 / (2*m)!
  let a := fun n : ℕ => 1/(n : ℝ)^(2*m)
  have hx : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have h (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      HasSum (fun n : ℕ => a n * Real.cos (2*Real.pi*n*y)) (C * bernoulliFun (2*m) y) :=
    hasSum_one_div_nat_pow_mul_cos hm.ne' hy
  have h0 : HasSum a (C * bernoulliFun (2*m) 0) := by simpa using h 0 (by simp)
  have hF := h _ hx
  have hsum : |C * bernoulliFun (2*m) (Int.fract x)| ≤ |C * bernoulliFun (2*m) 0| := by
    calc
      _ = ‖∑' n, a n * Real.cos (2*Real.pi*n*Int.fract x)‖ := by rw [hF.tsum_eq, Real.norm_eq_abs]
      _ ≤ ∑' n, ‖a n * Real.cos (2*Real.pi*n*Int.fract x)‖ := norm_tsum_le_tsum_norm hF.summable.norm
      _ ≤ ∑' n, a n := by
        apply hF.summable.norm.tsum_le_tsum _ h0.summable
        intro n
        have hn : 0 ≤ a n := by dsimp [a]; positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn]
        exact mul_le_of_le_one_right hn (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
      _ ≤ _ := h0.tsum_eq.le.trans (le_abs_self _)
  rw [abs_mul, abs_mul] at hsum
  have hC : C ≠ 0 := by dsimp [C]; positivity
  have hb := le_of_mul_le_mul_left hsum (abs_pos.mpr hC)
  simpa [bernoulliKernel, periodicBernoulli, abs_div] using
    div_le_div_of_nonneg_right hb (abs_nonneg (((2*m)! : ℕ) : ℝ))

/-- Integration by parts for complex multipliers of a periodic Bernoulli
kernel on any real interval, including integer endpoints. -/
theorem integral_bernoulliKernel_mul_complex {j : ℕ} (hj : 1 ≤ j) {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℂ} (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Icc a b)) :
    ∫ t in a..b, (bernoulliKernel j t : ℂ) * g t =
      ((bernoulliKernel (j+1) b : ℂ) * g b - (bernoulliKernel (j+1) a : ℂ) * g a) -
        ∫ t in a..b, (bernoulliKernel (j+1) t : ℂ) * g' t := by
  have hint (k : ℕ) {f : ℝ → ℂ} (hf : ContinuousOn f (Icc a b)) :
      IntervalIntegrable (fun t => (bernoulliKernel k t : ℂ)*f t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    obtain ⟨M, _, hM⟩ := bernoulliKernel_bounded k
    have hm : Measurable (bernoulliKernel k) :=
      ((continuous_bernoulliFun k).measurable.comp measurable_fract).div_const _
    apply (hf.norm.integrableOn_Icc.const_mul M).mono'
    · exact (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.mul
        (hf.aestronglyMeasurable measurableSet_Icc)
    · filter_upwards with t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)
  have h₁ := hint j (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
  have h₂ := hint (j+1) hg'
  have project (L : ℂ →L[ℝ] ℝ) :
      L (∫ t in a..b, (bernoulliKernel j t : ℂ)*g t) =
        L (((bernoulliKernel (j+1) b : ℂ)*g b - (bernoulliKernel (j+1) a : ℂ)*g a) -
          ∫ t in a..b, (bernoulliKernel (j+1) t : ℂ)*g' t) := by
    have hscale (v : ℝ) (z : ℂ) : L ((v : ℂ)*z) = v * L z := L.map_smul v z
    rw [map_sub, map_sub, ← L.intervalIntegral_comp_comm h₁, ← L.intervalIntegral_comp_comm h₂]
    simp_rw [hscale]
    exact integral_bernoulliKernel_mul_eq_sub hj hab (fun t ht => L.hasFDerivAt.comp_hasDerivAt t (hg t ht))
      (L.continuous.comp_continuousOn hg')
  exact Complex.ext (project Complex.reCLM) (project Complex.imCLM)

end AnalyticNumberTheory.AnalyticTools.Summation
