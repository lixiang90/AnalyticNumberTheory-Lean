import AnalyticNumberTheory.PrimeDistribution.WeakMertens
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-! # Consequences of the weak Mertens hypothesis for nontrivial zeros -/

noncomputable section

open Real Complex Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- Mellin integral of the Mertens summatory function with exponent −s−1. -/
def mertensMellin (s : ℂ) : ℂ := ∫ x in Ioi (1:ℝ), (mertensM x:ℂ)*(x:ℂ)^(-s-1)

/-- The product sζ(s) times the Mellin integral of M is one throughout Re(s)>1/2,
away from the pole at one, under the weak Mertens hypothesis. -/
theorem WeakMertensHypothesis.mellin_mul_zeta (h : WeakMertensHypothesis)
    {s : ℂ} (hs : 1/2 < s.re) (hs₁ : s ≠ 1) : s*riemannZeta s*mertensMellin s = 1 := by
  obtain ⟨_,_,_,_,hb⟩ := h.absolute_mellin_bound
  let U := {z : ℂ | 1/2 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hM : AnalyticOnNhd ℂ mertensMellin U :=
    (differentiableOn_mellin_of_abs_integrable zero_lt_one measurable_mertensM
      (fun σ hσ => (hb σ hσ).1)).analyticOnNhd hopen
  have hp : AnalyticOnNhd ℂ (fun z : ℂ => z*zetaOne z*mertensMellin z) U :=
    fun z hz => (analyticAt_id.mul (differentiable_zetaOne.analyticAt z)).mul (hM z hz)
  have hl : AnalyticOnNhd ℂ (fun z : ℂ => z-1) U := fun _ _ => analyticAt_id.sub analyticAt_const
  have hr : (fun z : ℂ => z*zetaOne z*mertensMellin z) =ᶠ[𝓝 (2:ℂ)] (fun z => z-1) := by
    have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (x := (2:ℂ)) (by change (1:ℝ) < 2; norm_num)] with z hz
    change 1 < z.re at hz
    have hn : z ≠ 1 := by intro he; simp [he] at hz
    have hn₀ : z ≠ 0 := by intro he; norm_num [he] at hz
    rw [mertensMellin,(mertensM_mellin_of_one_lt z hz).2.2,zetaOne_eq_sub_one_mul hn]
    field_simp [hn₀,_root_.riemannZeta_ne_zero_of_one_lt_re hz]
  have hbase : (2:ℂ) ∈ U := by change (1/2:ℝ) < 2; norm_num
  have he := hp.eqOn_of_preconnected_of_eventuallyEq hl (convex_halfSpace_re_gt (1/2)).isPreconnected
    hbase hr (show s ∈ U from hs)
  change s*zetaOne s*mertensMellin s = s-1 at he
  rw [zetaOne_eq_sub_one_mul hs₁] at he
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs₁)
  linear_combination he

/-- The weak Mertens hypothesis implies the Riemann hypothesis. -/
theorem WeakMertensHypothesis.riemannHypothesis (h : WeakMertensHypothesis) :
    RiemannHypothesisProp := by
  apply riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mpr
  intro s hs hz
  have hn : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  simpa [hz] using h.mellin_mul_zeta hs hn

/-- Under weak Mertens, |ρ ζ′(ρ)| is bounded away from zero by one common
positive constant for all nontrivial zeros, including zeros at negative heights. -/
theorem WeakMertensHypothesis.uniform_deriv_lower_bound (h : WeakMertensHypothesis) :
    ∃ c > 0, ∀ ρ ∈ CriticalStripZeros, c ≤ ‖ρ * deriv riemannZeta ρ‖ := by
  obtain ⟨B,hB,C,hC,hb⟩ := h.absolute_mellin_bound
  refine ⟨1/C,by positivity,?_⟩
  intro ρ hρ
  have hz := hρ.1
  have hr : ρ.re = 1/2 := h.riemannHypothesis ρ hz hρ.2.1 hρ.2.2
  have hn : ρ ≠ 1 := by intro he; simp [he] at hr
  have hδ : Tendsto (fun δ : ℝ => (δ:ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hδ).ne'
  have hlin : Tendsto (fun δ : ℝ => ρ+(δ:ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa using (tendsto_const_nhds (x := ρ)).add (hδ.mono_right nhdsWithin_le_nhds)
  have hsl : Tendsto (fun δ : ℝ => riemannZeta (ρ+δ)/(δ:ℂ)) (𝓝[>] 0)
      (𝓝 (deriv riemannZeta ρ)) := by
    apply ((analyticOn_riemannZeta ρ hn).differentiableAt.hasDerivAt.tendsto_slope_zero.comp hδ).congr'
    filter_upwards with δ
    simp [Function.comp_apply,hz,smul_eq_mul,div_eq_inv_mul]
  have hreal : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun δ : ℝ =>
      ‖(ρ+(δ:ℂ))*(riemannZeta (ρ+δ)/(δ:ℂ))‖*(δ*B+C)) (𝓝[>] 0)
      (𝓝 (‖ρ*deriv riemannZeta ρ‖*C)) := by
    simpa using ((hlin.mul hsl).norm.mul ((hreal.mul_const B).add_const C))
  have hl : 1 ≤ ‖ρ*deriv riemannZeta ρ‖*C := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,hlin.eventually_ne hn] with δ hδpos hne
    have hd : 0 < δ := hδpos
    let z := ρ+(δ:ℂ)
    have hzr : z.re = 1/2+δ := by simp [z,hr]
    have hhalf : 1/2 < z.re := by linarith
    have hnorm : ‖mertensMellin z‖ ≤ B+C/δ := by
      calc
        _ ≤ ∫ x in Ioi (1:ℝ), ‖(mertensM x:ℂ)*(x:ℂ)^(-z-1)‖ := norm_integral_le_integral_norm _
        _ = ∫ x in Ioi (1:ℝ), |mertensM x| * x^(-z.re-1) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          simp [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx),Real.norm_eq_abs]
        _ ≤ _ := by simpa [hzr] using (hb z.re hhalf).2
    have hid := h.mellin_mul_zeta hhalf hne
    have hfact : z*(riemannZeta z/(δ:ℂ))*((δ:ℂ)*mertensMellin z) = 1 := by
      calc
        _ = z*riemannZeta z*mertensMellin z := by field_simp [Complex.ofReal_ne_zero.mpr hd.ne']
        _ = _ := hid
    have hbound : ‖(δ:ℂ)*mertensMellin z‖ ≤ δ*B+C := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
      calc
        _ ≤ δ*(B+C/δ) := mul_le_mul_of_nonneg_left hnorm hd.le
        _ = _ := by field_simp [hd.ne']
    calc
      1 = ‖z*(riemannZeta z/(δ:ℂ))*((δ:ℂ)*mertensMellin z)‖ := by rw [hfact,norm_one]
      _ ≤ _ := by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  exact (div_le_iff₀ hC).mpr hl

/-- Every nontrivial zero has analytic multiplicity one under the weak Mertens hypothesis. -/
theorem WeakMertensHypothesis.simple_zeros (h : WeakMertensHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ CriticalStripZeros) : analyticOrderAt riemannZeta ρ = 1 := by
  obtain ⟨c,hc,hb⟩ := h.uniform_deriv_lower_bound
  have hn : ρ ≠ 1 := by intro he; have := hρ.2.2; simp [he] at this
  apply (analyticOn_riemannZeta ρ hn).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ.1
  intro hz
  have hh := hb ρ hρ
  rw [hz,mul_zero,norm_zero] at hh
  exact hc.not_ge hh

end AnalyticNumberTheory.PrimeDistribution
