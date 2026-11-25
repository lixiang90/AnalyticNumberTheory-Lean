import AnalyticNumberTheory.AnalyticTools.SquareMeanComparison

/-!
# Limits of normalized square means

A family of functions whose normalized square means converge can be replaced by
a second family when the normalized square mean of the difference tends to zero.
-/

open Filter MeasureTheory Set
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- The integral of the squared norm divided by the chosen normalization. -/
noncomputable def intervalSquareMean {E : Type*} [NormedAddCommGroup E]
    (a b w : ℝ) (f : ℝ → E) : ℝ := (∫ t in a..b, ‖f t‖^2)/w

/-- Stability under a perturbation of vanishing normalized square mean. -/
theorem tendsto_squareMean_of_difference {E : Type*} [NormedAddCommGroup E] {ι : Type*} {l : Filter ι}
    {a b w : ι → ℝ} {F G : ι → ℝ → E} {c : ℝ}
    (hab : ∀ᶠ i in l, a i ≤ b i) (hw : ∀ᶠ i in l, 0 < w i)
    (hF : ∀ᶠ i in l, ContinuousOn (F i) (Icc (a i) (b i)))
    (hG : ∀ᶠ i in l, ContinuousOn (G i) (Icc (a i) (b i)))
    (hmain : Tendsto (fun i => intervalSquareMean (a i) (b i) (w i) (F i)) l (𝓝 c))
    (herr : Tendsto (fun i => intervalSquareMean (a i) (b i) (w i) (F i-G i)) l (𝓝 0)) :
    Tendsto (fun i => intervalSquareMean (a i) (b i) (w i) (G i)) l (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(|c|+1))
  have hη : 0<η := by dsimp [η]; positivity
  have hηc : η*c < ε := calc η*c ≤ η*(|c|+1) :=
                                mul_le_mul_of_nonneg_left (by linarith [le_abs_self c]) hη.le
                             _ = ε/2 := by dsimp [η]; field_simp
                             _ < ε := by linarith
  have H := ((hmain.const_mul η).add (herr.const_mul (1+1/η))).add (hmain.sub_const c).abs
  simp only [mul_zero,add_zero,sub_self,abs_zero] at H
  filter_upwards [hab,hw,hF,hG,H.eventually_lt_const hηc] with i hi hwi hf hg hh
  rw [Real.dist_eq]
  apply lt_of_le_of_lt _ hh
  apply (abs_sub_le _ (intervalSquareMean (a i) (b i) (w i) (F i)) _).trans
  apply add_le_add _ (le_refl _)
  rw [abs_sub_comm]
  have h := div_le_div_of_nonneg_right (abs_integral_norm_sq_sub_le hi hη hf hg) hwi.le
  unfold intervalSquareMean
  rw [← sub_div,abs_div,abs_of_pos hwi]
  simpa only [Pi.sub_apply,add_div,mul_div_assoc] using h

end AnalyticNumberTheory.AnalyticTools
