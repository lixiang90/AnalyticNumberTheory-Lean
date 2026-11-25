import AnalyticNumberTheory.AnalyticTools.Gamma.VerticalDecay
import AnalyticNumberTheory.AnalyticTools.Transforms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Inverting the Mellin transform of the exponential

The Gamma integral on any positive vertical line recovers the real
exponential cutoff. Its absolute convergence also permits termwise
inversion in Dirichlet series.
-/

open Complex Real MeasureTheory Set
namespace AnalyticNumberTheory.AnalyticTools

/-- Gamma is absolutely integrable on each positive vertical line. -/
theorem verticalIntegrable_Gamma {c : ℝ} (hc : 0<c) : Complex.VerticalIntegrable Complex.Gamma c := by
  obtain ⟨A,hA,H⟩ := norm_Gamma_positive_strip_weight hc (le_refl c) 2
  let w (t : ℝ) : ℂ := c+t*I
  have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hd (t : ℝ) : DifferentiableAt ℂ Complex.Gamma (w t) := by
    apply Complex.differentiableAt_Gamma
    intro m h; have he := congrArg Complex.re h
    simp [w] at he; linarith [Nat.cast_nonneg (α:=ℝ) m]
  apply (integrable_inv_one_add_sq.const_mul A).mono' (Continuous.aestronglyMeasurable
    (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt.comp (hw.continuousAt)))
  filter_upwards with t
  have h := H (w t) (by simp [w])
  simp only [w,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at h
  change ‖Complex.Gamma (w t)‖ ≤ A*(1+t^2)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
  have ht : 1+t^2 ≤ (1+|t|)^2 := by nlinarith only [abs_nonneg t,sq_abs t]
  exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans (by rw [mul_comm]; exact h)

/-- Mellin inversion of the exponential at every positive argument. -/
theorem mellinInv_Gamma {c x : ℝ} (hc : 0<c) (hx : 0<x) :
    mellinInv c Complex.Gamma x = (Real.exp (-x):ℂ) := by
  let f (t : ℝ) : ℂ := Real.exp (-t)
  have H (t : ℝ) : mellin f (c+t*I)=Complex.Gamma (c+t*I) := mellin_exp_neg (by simpa using hc)
  have hint : Complex.VerticalIntegrable (mellin f) c := by
    change Integrable (fun t : ℝ => mellin f (c+t*I))
    simp_rw [H]
    exact verticalIntegrable_Gamma hc
  have hconv : MellinConvergent f (c:ℂ) := by
    simpa only [f,neg_one_mul] using mellinConvergent_exp_neg_mul (a:=1) zero_lt_one (s:=(c:ℂ)) (by simpa using hc)
  have hi := mellin_inversion_bridge c f hx hconv hint (by dsimp [f];fun_prop)
  simpa only [mellinInv,H,f] using hi

end AnalyticNumberTheory.AnalyticTools
