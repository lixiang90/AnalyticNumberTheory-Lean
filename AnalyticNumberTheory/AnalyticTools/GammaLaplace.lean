import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The complex Laplace integral for gamma

Both the exponent and the Laplace parameter may be complex. Analytic
continuation in the Laplace parameter extends the positive-real evaluation
to the entire open right half-plane.
-/
open Complex Real Filter MeasureTheory Set
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

noncomputable def gammaLaplaceKernel (s : ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z*t) * (t:ℂ)^(s-1)

theorem norm_gammaLaplaceKernel (s : ℂ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gammaLaplaceKernel s z t‖ = t^(s.re-1) * Real.exp (-z.re*t) := by
  rw [gammaLaplaceKernel,norm_mul,Complex.norm_exp,Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp [Complex.mul_re,mul_comm]

private theorem integrable_gammaBound {r b : ℝ} (hr : -1 < r) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t^r*Real.exp (-b*t)) (Ioi 0) := by
  simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow hr zero_lt_one hb

theorem integrable_gammaLaplaceKernel {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (gammaLaplaceKernel s z) (Ioi 0) := by
  refine (integrable_gammaBound (by linarith : -1 < s.re-1) hz).mono' ?_ ?_
  · unfold gammaLaplaceKernel; fun_prop
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => (norm_gammaLaplaceKernel s z ht).le

private theorem differentiableAt_gammaLaplace {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w => ∫ t in Ioi (0:ℝ), gammaLaplaceKernel s w t) z := by
  let D (w : ℂ) (t : ℝ) := -(t:ℂ) * gammaLaplaceKernel s w t
  let U := {w : ℂ | z.re/2 < w.re}
  have hU : U ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [U]; linarith)
  have hd (w : ℂ) (t : ℝ) : HasDerivAt (fun w => gammaLaplaceKernel s w t) (D w t) w := by
    have h := (((hasDerivAt_id w).neg.mul_const (t:ℂ)).cexp.mul_const ((t:ℂ)^(s-1)))
    convert h using 1 <;> dsimp [D, gammaLaplaceKernel]; ring
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := gammaLaplaceKernel s) (F' := D) (bound := fun t : ℝ => t^s.re*Real.exp (-(z.re/2)*t)) hU
    (Eventually.of_forall fun w => by unfold gammaLaplaceKernel; fun_prop)
    (integrable_gammaLaplaceKernel hs hz) (by dsimp only [D]; unfold gammaLaplaceKernel; fun_prop) ?_
    (integrable_gammaBound (by linarith) (half_pos hz)) (ae_of_all _ fun t w _ => hd w t)
  · exact hint.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    intro w hw
    change ‖-(t:ℂ) * gammaLaplaceKernel s w t‖ ≤ _
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_gammaLaplaceKernel _ _ ht,
      ← mul_assoc, show t * t^(s.re-1) = t^s.re by nth_rw 1 [← Real.rpow_one t]; rw [← Real.rpow_add ht]; congr 1; ring]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    rw [Real.exp_le_exp]
    change z.re/2 < w.re at hw
    nlinarith [mul_pos (sub_pos.mpr hw) ht]

/-- The gamma Laplace integral at a complex parameter with positive real part. -/
theorem integral_gammaLaplaceKernel_rightHalfPlane {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z*t) * (t:ℂ)^(s-1)) =
      z^(-s) * Complex.Gamma s := by
  let f (w : ℂ) := ∫ t : ℝ in Ioi 0, gammaLaplaceKernel s w t
  let g (w : ℂ) := w^(-s) * Complex.Gamma s
  let U := {w : ℂ | 0 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ f U := DifferentiableOn.analyticOnNhd (fun _ hw =>
    (differentiableAt_gammaLaplace hs hw).differentiableWithinAt) hU
  have hg : AnalyticOnNhd ℂ g U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro w hw
    exact ((differentiableAt_id.cpow_const (Or.inl hw)).mul_const _).differentiableWithinAt
  have hreal {x : ℝ} (hx : 0 < x) : f x = g x := by
    have he := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a:=s) hs hx
    dsimp only [f,g,gammaLaplaceKernel]
    have hcon (t : ℝ) : Complex.exp (-(x:ℂ)*t) * (t:ℂ)^(s-1) =
        (t:ℂ)^(s-1) * Complex.exp (-((x:ℂ)*(t:ℂ))) := by rw [neg_mul,mul_comm]
    simp_rw [hcon]
    rw [he,one_div,Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne),Complex.cpow_neg]
  apply hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 1)
    (by simp [U]) _ hz
  have hr : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (Complex.continuous_ofReal.continuousAt (x := 1)).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
    simpa using ht.ne'
  have he : ∀ᶠ t : ℝ in 𝓝[>] 1, 1 < t := self_mem_nhdsWithin
  exact hr.frequently (he.frequently.mono fun t ht => hreal (zero_lt_one.trans ht))

end AnalyticNumberTheory.AnalyticTools
