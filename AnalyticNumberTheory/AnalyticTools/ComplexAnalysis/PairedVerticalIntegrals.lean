import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic dependence of paired vertical integrals

Integrating two analytic functions with opposite imaginary displacements
produces a holomorphic function of their common base point in a strip.
-/

open Complex Set MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Paired analytic values at positive and negative vertical displacements. -/
noncomputable def pairedVerticalIntegral (f g : ℂ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ t in a..b, f (z+t*I)*g (z-t*I)

/-- Holomorphy of the paired vertical integral on any open vertical strip
where its factors are analytic. -/
theorem differentiableAt_pairedVerticalIntegral {f g : ℂ → ℂ} {l u : ℝ}
    (hf : ∀ z : ℂ, z.re∈Ioo l u → AnalyticAt ℂ f z)
    (hg : ∀ z : ℂ, z.re∈Ioo l u → AnalyticAt ℂ g z)
    (a b : ℝ) {z : ℂ} (hz : z.re∈Ioo l u) :
    DifferentiableAt ℂ (pairedVerticalIntegral f g a b) z := by
  let U := Complex.re ⁻¹' Ioo l u
  let P (x : ℂ×ℝ) := x.1+x.2*I
  let Q (x : ℂ×ℝ) := x.1-x.2*I
  let F (x : ℂ) (t : ℝ) := f (P (x,t))*g (Q (x,t))
  let G (x : ℂ×ℝ) := deriv f (P x)*g (Q x)+f (P x)*deriv g (Q x)
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hP : Continuous P := by dsimp [P];fun_prop
  have hQ : Continuous Q := by dsimp [Q];fun_prop
  have hpa (x : ℂ×ℝ) (hx : x.1∈U) := hf (P x) (by simpa [P,U] using hx)
  have hqa (x : ℂ×ℝ) (hx : x.1∈U) := hg (Q x) (by simpa [Q,U] using hx)
  have hD (x : ℂ) (hx : x∈U) (t : ℝ) :
      HasDerivAt (fun y => F y t) (G (x,t)) x := by
    have hp := (hpa (x,t) hx).differentiableAt.hasDerivAt.comp (h:=fun y : ℂ => y+(t:ℂ)*I) x ((hasDerivAt_id x).add_const ((t:ℂ)*I))
    have hq := (hqa (x,t) hx).differentiableAt.hasDerivAt.comp (h:=fun y : ℂ => y-(t:ℂ)*I) x ((hasDerivAt_id x).sub_const ((t:ℂ)*I))
    simpa [F,G,P,Q,Function.comp_def,Pi.mul_def] using hp.mul hq
  change DifferentiableAt ℂ (fun x => ∫ t in a..b,F x t) z
  apply (intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv (𝕜:=ℂ) (hU.mem_nhds hz) _ _ _).differentiableAt
  · intro x hx
    exact (((hpa x hx.1).continuousAt.comp hP.continuousAt).mul ((hqa x hx.1).continuousAt.comp hQ.continuousAt)).continuousWithinAt
  · exact fun t _ x hx => (hD x hx t).differentiableAt.differentiableWithinAt
  · have hG : ContinuousOn G (U ×ˢ uIcc a b) := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      have hp := (hpa x hx.1).continuousAt.comp hP.continuousAt
      have hq := (hqa x hx.1).continuousAt.comp hQ.continuousAt
      have hp' := (hpa x hx.1).deriv.continuousAt.comp hP.continuousAt
      have hq' := (hqa x hx.1).deriv.continuousAt.comp hQ.continuousAt
      exact (hp'.mul hq).add (hp.mul hq')
    apply (hG.smul (continuousOn_const (c:=ContinuousLinearMap.id ℂ ℂ))).congr
    intro x hx
    ext y
    rw [fderiv_eq_deriv_mul,(hD x.1 hx.1 x.2).deriv]
    rfl

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
