import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCorrection
import Mathlib.Analysis.Calculus.DSlope

/-!
# Regularity of the first Riemann–Siegel coefficient

At each zero of the cosine denominator, divide the numerator and
denominator by the linear factor using their analytic divided slopes.
Continuity identifies the result at the removable point.
-/
noncomputable section
open Real Set Filter
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem analyticAt_of_simple_product {f g u : ℝ→ℝ}
    (hf : ∀x,AnalyticAt ℝ f x) (hg : ∀x,AnalyticAt ℝ g x) (hu : Continuous u)
    (H : ∀x, f x*u x=g x) {a : ℝ} (hder : f a=0 → deriv f a≠0) : AnalyticAt ℝ u a := by
  by_cases ha : f a=0
  · have hga : g a=0 := by rw [←H,ha,zero_mul]
    have hfc : Continuous (dslope f a) := continuous_iff_continuousAt.mpr fun x => ((hf x).dslope a).continuousAt
    have hgc : Continuous (dslope g a) := continuous_iff_continuousAt.mpr fun x => ((hg x).dslope a).continuousAt
    have he : (fun x => dslope f a x*u x)=dslope g a := by
      apply Continuous.ext_on (dense_compl_singleton a) (hfc.mul hu) hgc
      intro x hx
      have hx' : x≠a := hx
      change dslope f a x*u x=dslope g a x
      rw [dslope_of_ne _ hx',dslope_of_ne _ hx',slope_def_field,slope_def_field,ha,hga,sub_zero,sub_zero,←H]
      ring
    have hn : dslope f a a≠0 := by rw [dslope_same];exact hder ha
    apply (((hg a).dslope a).div ((hf a).dslope a) hn).congr
    filter_upwards [hfc.continuousAt.eventually_ne hn] with x hx
    exact (div_eq_iff hx).mpr (by rw [←he];ring)
  · apply ((hg a).div (hf a) ha).congr
    filter_upwards [(hf a).continuousAt.eventually_ne ha] with x hx
    exact (div_eq_iff hx).mpr (by rw [←H];ring)

/-- The first Riemann–Siegel coefficient is real analytic, including at
both removable points of its elementary formula on [0,2]. -/
theorem analyticAt_riemannSiegelCorrection (c : ℝ) : AnalyticAt ℝ riemannSiegelCorrection c := by
  let f := fun x : ℝ => Real.cos (Real.pi*x)
  let g := fun x : ℝ => Real.cos (Real.pi*(x^2/2-x-1/8))
  have hf (x : ℝ) : AnalyticAt ℝ f x := by dsimp [f];fun_prop
  have hg (x : ℝ) : AnalyticAt ℝ g x := by dsimp [g];fun_prop
  apply analyticAt_of_simple_product hf hg continuous_riemannSiegelCorrection cos_mul_riemannSiegelCorrection
  intro h
  have hh := (((hasDerivAt_id c).const_mul Real.pi).cos).deriv
  change deriv f c= -Real.sin (Real.pi*c)*(Real.pi*1) at hh
  rw [hh];apply mul_ne_zero _ (by positivity)
  apply neg_ne_zero.mpr
  intro hs
  have H := Real.sin_sq_add_cos_sq (Real.pi*c)
  change Real.cos (Real.pi*c)=0 at h
  rw [hs,h] at H;norm_num at H

/-- Uniform bounds for the coefficient and its first derivative on the
complete interval of fractional parts. -/
theorem riemannSiegelCorrection_C1_bound : ∃ C : ℝ,0<C ∧ ∀ {c : ℝ},c∈Icc (0:ℝ) 2 →
    |riemannSiegelCorrection c|≤C ∧ |deriv riemannSiegelCorrection c|≤C := by
  have h : ContDiff ℝ 1 riemannSiegelCorrection := (show AnalyticOnNhd ℝ riemannSiegelCorrection univ from
    fun x _ => analyticAt_riemannSiegelCorrection x).contDiff
  have hdr : Continuous (deriv riemannSiegelCorrection) := h.continuous_deriv (by norm_num)
  let f := fun c => |riemannSiegelCorrection c|+|deriv riemannSiegelCorrection c|
  have hf : Continuous f := continuous_riemannSiegelCorrection.abs.add hdr.abs
  obtain ⟨u,hu,H⟩ := isCompact_Icc.exists_isMaxOn (f:=f) (by exact ⟨0,le_rfl,by norm_num⟩ : (Icc (0:ℝ) 2).Nonempty) hf.continuousOn
  refine ⟨1+f u,by dsimp [f];positivity,?_⟩
  intro c hc
  have hh := H hc
  change |riemannSiegelCorrection c|+|deriv riemannSiegelCorrection c|≤f u at hh
  constructor <;> linarith [abs_nonneg (riemannSiegelCorrection c),abs_nonneg (deriv riemannSiegelCorrection c)]

end AnalyticNumberTheory.RiemannZeta
