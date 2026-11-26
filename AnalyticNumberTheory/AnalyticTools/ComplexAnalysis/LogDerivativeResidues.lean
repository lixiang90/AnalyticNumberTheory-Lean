import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.EntireZeroFactors
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleResidues

/-! # Rectangular argument principle with a simple pole in the weight -/

noncomputable section

open Complex Finset Set Filter
open scoped Topology Classical

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- The principal part of a logarithmic derivative at a zero of finite analytic order
has residue equal to that order. This also applies at regular nonzero points. -/
theorem hasSimplePrincipalPartAt_logDeriv {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hfin : analyticOrderAt f p ≠ ⊤) :
    HasSimplePrincipalPartAt (logDeriv f) p (analyticOrderNatAt f p : ℂ) := by
  let m := analyticOrderNatAt f p
  obtain ⟨v, hv, hvp, he⟩ := (hf.analyticOrderNatAt_eq_iff hfin).mp (Eq.refl m)
  have he' : f =ᶠ[𝓝 p] (fun z : ℂ => (z-p)^m) * v := by
    simpa only [Filter.EventuallyEq, Pi.mul_apply, smul_eq_mul] using he
  have hlog : AnalyticAt ℂ (logDeriv v) p := hv.deriv.div hv hvp
  refine ⟨logDeriv v, hlog, ?_⟩
  filter_upwards [self_mem_nhdsWithin, (logDeriv_congr_nhds he').filter_mono nhdsWithin_le_nhds,
    hv.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hv.continuousAt.eventually_ne hvp).filter_mono nhdsWithin_le_nhds] with z hz hL hvz hvnz
  change z ≠ p at hz
  have hne := sub_ne_zero.mpr hz
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => (z-p)^m) z := by fun_prop
  rw [hL, logDeriv_mul (f := fun w : ℂ => (w-p)^m) (g := v) z (pow_ne_zero m hne) hvnz hdiff hvz.differentiableAt,
    logDeriv_fun_pow (f := fun w : ℂ => w-p) (by fun_prop), logDeriv_apply,
    show deriv (fun w : ℂ => w-p) z = 1 from ((hasDerivAt_id z).sub_const p).deriv]
  dsimp only [m]
  ring

/-- Cauchy-weighted argument principle. The distinguished point contributes the logarithmic
derivative there, and each enclosed zero contributes its analytic multiplicity times
`g(p)/(p-q)`. The entire functions may have other zeros outside the rectangle. -/
theorem cauchy_weighted_argument_principle_rect {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {a b c d : ℝ} {q : ℂ}
    (hq : q.re ∈ Ioo a b ∧ q.im ∈ Ioo c d) (hqf : f q ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ p ∈ Z, (p.re ∈ Ioo a b ∧ p.im ∈ Ioo c d) ∧ f p = 0)
    (hall : ∀ z ∈ Icc a b ×ℂ Icc c d, f z = 0 → z ∈ Z) :
    rectangleBoundary (fun z => g z*logDeriv f z/(z-q)) ⟨a,c⟩ ⟨b,d⟩ =
      2*Real.pi*I*(g q*logDeriv f q +
        ∑ p ∈ Z, (analyticOrderNatAt f p : ℂ)*g p/(p-q)) := by
  let r (p : ℂ) := if p=q then g q*logDeriv f q else (analyticOrderNatAt f p : ℂ)*g p/(p-q)
  have hqZ : q ∉ Z := fun h => hqf (hZ q h).2
  have hfi (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
    apply hf.differentiableOn.analyticOnNhd isOpen_univ |>.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ q) (mem_univ z)
    rw [(hf.analyticAt q).analyticOrderAt_eq_zero.mpr hqf]
    simp
  have hsum : (∑ p ∈ insert q Z, r p) = g q*logDeriv f q+
      ∑ p ∈ Z, (analyticOrderNatAt f p : ℂ)*g p/(p-q) := by
    rw [sum_insert hqZ]
    congr 1
    · simp [r]
    · refine sum_congr rfl fun p hp => ?_
      exact ite_eq_right (show p ≠ q from fun he => hqZ (he ▸ hp))
  rw [← hsum]
  apply rectangleBoundary_eq_sum_simpleResidues (hq.1.1.trans hq.1.2) (hq.2.1.trans hq.2.2)
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hq
    · exact (hZ p hp).1
  · intro z hz hnot
    have hzne : z ≠ q := fun he => hnot (mem_insert.mpr (Or.inl he))
    have hfn : f z ≠ 0 := fun he => hnot (mem_insert_of_mem (hall z hz he))
    have hlog : AnalyticAt ℂ (logDeriv f) z := (hf.analyticAt z).deriv.div (hf.analyticAt z) hfn
    exact ((hg z).mul hlog.differentiableAt).div (differentiableAt_id.sub_const q) (sub_ne_zero.mpr hzne)
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · have hlog : AnalyticAt ℂ (logDeriv f) p := (hf.analyticAt p).deriv.div (hf.analyticAt p) hqf
      simpa [r] using hasSimplePrincipalPartAt_div_sub ((hg.analyticAt p).mul hlog)
    · have hne : p ≠ q := fun he => hqZ (he ▸ hp)
      have hw : AnalyticAt ℂ (fun z => g z/(z-q)) p :=
        (hg.analyticAt p).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne)
      have H := (hasSimplePrincipalPartAt_logDeriv (hf.analyticAt p) (hfi p)).mul_analytic hw
      convert H using 1
      · funext z; ring
      · simp [r, hne, mul_div_assoc]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
