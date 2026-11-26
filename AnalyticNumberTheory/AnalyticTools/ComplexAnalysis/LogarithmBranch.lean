import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.MeanValue

/-! # A normalized holomorphic logarithm on a simply connected domain -/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- A continuous logarithm of a differentiable nonvanishing function has derivative f'/f. -/
theorem hasDerivAt_logarithm_of_eventually_exp_eq {f g : ℂ → ℂ} {z a : ℂ}
    (hg : ContinuousAt g z) (hf : HasDerivAt f a z)
    (he : (fun w => Complex.exp (g w)) =ᶠ[𝓝 z] f) :
    HasDerivAt g (a/f z) z := by
  have hz : Complex.exp (g z) = f z := he.eq_of_nhds
  have hn : f z ≠ 0 := hz ▸ Complex.exp_ne_zero _
  have hq : f z / f z ∈ slitPlane := by simp [hn]
  have hd := ((hf.div_const (f z)).clog hq).const_add (g z)
  have him : Tendsto (fun w => (g w - g z).im) (𝓝 z) (𝓝 0) := by
    have hc : ContinuousAt (fun w => (g w - g z).im) z := by fun_prop
    simpa only [sub_self,Complex.zero_im] using hc.tendsto
  apply (hd.congr_deriv (by simp [hn])).congr_of_eventuallyEq
  filter_upwards [him.eventually (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos),he] with w hw hwe
  change g w = g z + Complex.log (f w / f z)
  rw [←hwe,←hz,←Complex.exp_sub,Complex.log_exp hw.1 hw.2.le]
  ring

/-- On an open simply connected domain, a nonvanishing holomorphic function has a
holomorphic logarithm taking any prescribed logarithm of its value at a base point. -/
theorem exists_holomorphic_logarithm {U : Set ℂ} (ho : IsOpen U) (hs : IsSimplyConnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hn : ∀ z ∈ U, f z ≠ 0)
    {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ U) (hw₀ : Complex.exp w₀ = f z₀) :
    ∃ g : ℂ → ℂ, g z₀ = w₀ ∧ (∀ z ∈ U, Complex.exp (g z) = f z) ∧
      ∀ z ∈ U, HasDerivAt g (deriv f z/f z) z := by
  obtain ⟨h,hc,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hs ho hf.continuousOn
    (show 0 ∉ f '' U from fun ⟨z,hz,hf₀⟩ => hn z hz hf₀)
  let g (z : ℂ) := h z - h z₀ + w₀
  have hgc : ContinuousOn g U := (hc.sub continuousOn_const).add continuousOn_const
  have heg (z : ℂ) (hz : z ∈ U) : Complex.exp (g z) = f z := by
    dsimp only [g]
    rw [Complex.exp_add,Complex.exp_sub,show Complex.exp (h z) = f z from he hz,
      show Complex.exp (h z₀) = f z₀ from he hz₀,hw₀,div_mul_cancel₀ _ (hn _ hz₀)]
  refine ⟨g,by simp [g],heg,fun z hz => ?_⟩
  apply hasDerivAt_logarithm_of_eventually_exp_eq (hgc.continuousAt (ho.mem_nhds hz))
    (hf.differentiableAt (ho.mem_nhds hz)).hasDerivAt
  filter_upwards [ho.mem_nhds hz] with w hw using heg w hw

/-- Two holomorphic logarithms agreeing at one point agree throughout a connected open set. -/
theorem eqOn_holomorphic_logarithms {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    {f g h : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : ContinuousOn g U) (hh : ContinuousOn h U)
    (heg : ∀ z ∈ U, Complex.exp (g z) = f z) (heh : ∀ z ∈ U, Complex.exp (h z) = f z)
    {a : ℂ} (ha : a ∈ U) (hbase : g a = h a) : U.EqOn g h := by
  have hd (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w => g w-h w) 0 z := by
    have hU := ho.mem_nhds hz
    have hf' := (hf.differentiableAt hU).hasDerivAt
    have h₁ := hasDerivAt_logarithm_of_eventually_exp_eq (hg.continuousAt hU) hf' (by filter_upwards [hU] with w hw using heg w hw)
    have h₂ := hasDerivAt_logarithm_of_eventually_exp_eq (hh.continuousAt hU) hf' (by filter_upwards [hU] with w hw using heh w hw)
    simpa only [sub_self] using h₁.fun_sub h₂
  intro z hz
  have he := ho.is_const_of_deriv_eq_zero hc (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz ha
  exact sub_eq_zero.mp (by simpa [hbase] using he)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
