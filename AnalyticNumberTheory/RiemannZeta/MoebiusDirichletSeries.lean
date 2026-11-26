import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion
import AnalyticNumberTheory.RiemannZeta.HardyTheorem
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis

/-!
# The ordinary Möbius series and the reciprocal of zeta

In the open half-plane of ordinary convergence the product with the entire
function (s−1)ζ(s) is s−1. Hardy's theorem therefore puts the abscissa at
least at one half, and RH is equivalent to equality and to the pointwise
convergence of the partial sums throughout the corresponding half-plane.
-/

noncomputable section

open Complex Filter Set
open scoped Topology ArithmeticFunction.Moebius LSeries.notation
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.RiemannZeta

/-- The conditional Möbius series times the entire pole-removed zeta function
is s−1 on its entire open half-plane of ordinary convergence. -/
theorem moebiusDirichletSum_mul_zetaOne {s : ℂ}
    (hs : abscissaOfConvergence ↗μ < (s.re:EReal)) :
    dirichletSum ↗μ s*zetaOne s = s-1 := by
  obtain ⟨b,hb,hbs⟩ := EReal.exists_between_coe_real hs
  let U := {z : ℂ | b < z.re}
  have hD : AnalyticOnNhd ℂ (dirichletSum ↗μ) U :=
    (dirichletSum_analyticOnNhd _).mono (fun z hz => hb.trans (EReal.coe_lt_coe_iff.mpr hz))
  have hG : AnalyticOnNhd ℂ (fun z => dirichletSum ↗μ z*zetaOne z) U :=
    hD.mul (fun z _ => differentiable_zetaOne.analyticAt z)
  have hlin : AnalyticOnNhd ℂ (fun z : ℂ => z-1) U := fun z _ =>
    analyticAt_id.sub analyticAt_const
  let r := max b 1 + 1
  have hr : 1 < r := by dsimp only [r]; linarith [le_max_right b 1]
  have hrb : (r:ℂ) ∈ U := by change b < r; dsimp only [r]; linarith [le_max_left b 1]
  have hright : (fun z => dirichletSum ↗μ z*zetaOne z) =ᶠ[𝓝 (r:ℂ)] (fun z => z-1) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (x := (r:ℂ)) hr] with z hz
    change 1 < z.re at hz
    have hz₁ : z ≠ 1 := by intro he; simp [he] at hz
    rw [(DirichletSeries.LSeriesSummable_moebius_iff.mpr hz).dirichletSum_eq_LSeries,
      LSeries_moebius_eq_inv_riemannZeta hz,zetaOne_eq_sub_one_mul hz₁]
    field_simp [riemannZeta_ne_zero_of_one_lt_re hz]
  exact hG.eqOn_of_preconnected_of_eventuallyEq hlin (convex_halfSpace_re_gt b).isPreconnected
    hrb hright (EReal.coe_lt_coe_iff.mp hbs)

/-- In its open half-plane of convergence the ordinary Möbius sum equals the
holomorphic reciprocal of zeta, taking value zero at the pole s = 1. -/
theorem moebiusDirichletSum_eq_riemannZetaInv {s : ℂ} (hs : abscissaOfConvergence ↗μ < (s.re:EReal)) :
    dirichletSum ↗μ s = riemannZetaInv s := by
  have H := moebiusDirichletSum_mul_zetaOne hs
  rcases eq_or_ne s 1 with rfl | hs₁
  · simpa [riemannZetaInv] using H
  rw [zetaOne_eq_sub_one_mul hs₁] at H
  rw [riemannZetaInv_eq_inv_of_ne_one hs₁]
  apply eq_inv_of_mul_eq_one_left
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs₁)
  calc
    (s-1)*(dirichletSum ↗μ s*riemannZeta s) = dirichletSum ↗μ s*((s-1)*riemannZeta s) := by ring
    _ = _ := H.trans (mul_one _).symm

/-- Each nontrivial zero bounds the ordinary Möbius abscissa from below. -/
theorem re_le_moebiusAbscissa_of_nontrivial_zero {ρ : ℂ} (hz : ρ ∈ CriticalStripZeros) :
    (ρ.re:EReal) ≤ abscissaOfConvergence ↗μ := by
  by_contra! h
  obtain ⟨hζ,_,h₁⟩ := mem_criticalStripZeros.mp hz
  have hne : ρ ≠ 1 := by intro he; simp [he] at h₁
  have H := moebiusDirichletSum_mul_zetaOne h
  rw [zetaOne_eq_sub_one_mul hne,hζ,mul_zero,mul_zero] at H
  exact sub_ne_zero.mpr hne H.symm

/-- The ordinary abscissa of the Möbius Dirichlet series is unconditionally at
least one half, since zeta has a zero on the critical line. -/
theorem half_le_moebiusAbscissa : (((1/2:ℝ)):EReal) ≤ abscissaOfConvergence ↗μ := by
  obtain ⟨t,_,hz⟩ := exists_critical_zero_above 0
  have hr : (1/2+(t:ℂ)*I).re = 1/2 := by norm_num
  have H := re_le_moebiusAbscissa_of_nontrivial_zero (mem_criticalStripZeros.mpr
    ⟨hz,by rw [hr]; norm_num,by rw [hr]; norm_num⟩)
  simpa only [hr] using H

/-- RH is equivalent to the ordinary Möbius abscissa being exactly one half. -/
theorem riemannHypothesisProp_iff_moebiusAbscissa_eq_half :
    RiemannHypothesisProp ↔ abscissaOfConvergence ↗μ = ((1/2:ℝ):EReal) :=
  ⟨fun h => le_antisymm (riemannHypothesisProp_iff_abscissaOfConvergence_moebius_le_half.mp h)
    half_le_moebiusAbscissa,fun h => riemannHypothesisProp_iff_abscissaOfConvergence_moebius_le_half.mpr h.le⟩

/-- Under RH the partial sums in natural order converge to the reciprocal of
zeta throughout Re(s) > 1/2, including its regularized value at one. -/
theorem tendsto_moebiusDirichletPartialSum_of_rh (hRH : RiemannHypothesisProp) {s : ℂ} (hs : 1/2 < s.re) :
    Tendsto (dirichletPartialSum ↗μ s) atTop (𝓝 (riemannZetaInv s)) := by
  have ha := (riemannHypothesisProp_iff_moebiusAbscissa_eq_half.mp hRH).le.trans_lt (EReal.coe_lt_coe_iff.mpr hs)
  rw [←moebiusDirichletSum_eq_riemannZetaInv ha]
  exact (dirichletConvergesAt_of_abscissaOfConvergence_lt_re ha).tendsto

/-- RH is equivalent to the pointwise ordinary convergence of the Möbius
Dirichlet series at every complex s with Re(s) > 1/2. -/
theorem riemannHypothesisProp_iff_moebiusDirichletConverges :
    RiemannHypothesisProp ↔ ∀ s : ℂ, 1/2 < s.re → DirichletConvergesAt ↗μ s := by
  refine ⟨fun h s hs => ⟨_,tendsto_moebiusDirichletPartialSum_of_rh h hs⟩,fun H => ?_⟩
  apply riemannHypothesisProp_iff_abscissaOfConvergence_moebius_le_half.mpr
  apply EReal.le_of_forall_lt_iff_le.mp
  intro b hb
  exact abscissaOfConvergence_le_of_dirichletConvergesAt (H b (EReal.coe_lt_coe_iff.mp hb))

/-- On RH the convergence in 1/2 < Re(s) ≤ 1 is ordinary and conditional. -/
theorem moebiusDirichletSeries_conditionally_convergent_of_rh (hRH : RiemannHypothesisProp)
    {s : ℂ} (h₀ : 1/2 < s.re) (h₁ : s.re ≤ 1) :
    Tendsto (dirichletPartialSum ↗μ s) atTop (𝓝 (riemannZetaInv s)) ∧ ¬LSeriesSummable ↗μ s :=
  ⟨tendsto_moebiusDirichletPartialSum_of_rh hRH h₀,
    fun h => (not_lt_of_ge h₁) (DirichletSeries.LSeriesSummable_moebius_iff.mp h)⟩

end AnalyticNumberTheory.RiemannZeta
