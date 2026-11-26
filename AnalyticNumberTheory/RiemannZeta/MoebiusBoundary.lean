import AnalyticNumberTheory.DirichletSeries.BoundaryAbel
import AnalyticNumberTheory.RiemannZeta.MertensCancellation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Möbius Dirichlet series on the line of real part one

The classical Mertens bound gives every fixed logarithmic saving. Partial
summation gives convergence on the boundary, and Abel's theorem identifies
the limit with the reciprocal of zeta, extended by zero at the pole.
-/

noncomputable section

open Complex Filter
open scoped Topology ArithmeticFunction.Moebius LSeries.notation
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-- The Mertens function saves any fixed natural power of log x, with leading
constant one beyond a threshold depending on that power. -/
theorem mertensM_eventually_le_div_log_pow (m : ℕ) :
    ∀ᶠ x : ℝ in atTop, |(mertensM x : ℝ)| ≤ x/(Real.log x)^m := by
  obtain ⟨C,hC,γ,hγ,H⟩ := mertensM_exp_sqrt_log_bound
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*m : ℕ) γ hγ).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  have hsmall := (ht.const_mul C).eventually_le_const (show C*0 < 1 by simp)
  filter_upwards [H,hsmall,eventually_gt_atTop 1] with x hx hsmall hx₁
  have hlog := Real.log_pos hx₁
  have hx0 := zero_lt_one.trans hx₁
  simp only [Function.comp_apply,Real.rpow_natCast,pow_mul,Real.sq_sqrt hlog.le] at hsmall
  apply hx.trans
  rw [le_div_iff₀ (pow_pos hlog m)]
  calc
    _ = (C*((Real.log x)^m * Real.exp (-γ * Real.sqrt (Real.log x))))*x := by ring
    _ ≤ 1*x := mul_le_mul_of_nonneg_right hsmall hx0.le
    _ = _ := one_mul _

/-- Without RH, the ordinary Möbius partial sums converge on the whole line
of real part one to the pole-regularized reciprocal of zeta. -/
theorem tendsto_moebiusDirichletPartialSum_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    Tendsto (dirichletPartialSum ↗μ s) atTop (𝓝 (riemannZetaInv s)) := by
  have hc : DirichletConvergesAt ↗μ s := dirichletConvergesAt_of_coeffPartialSum_log_sq
    (C := 1) one_pos (by
      filter_upwards [mertensM_eventually_le_div_log_pow 2] with x hx
      simpa only [coeffPartialSum_moebius_floor,Complex.norm_intCast,one_mul] using hx) hs
  have hpath : Tendsto (fun u : ℝ => s+(u:ℂ)) (𝓝[>] 0) (𝓝 s) := by
    have h : Continuous (fun u : ℝ => s+(u:ℂ)) := continuous_const.add Complex.continuous_ofReal
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have han := analyticAt_riemannZetaInv_of_ne_zero (riemannZeta_ne_zero_of_one_le_re hs.ge)
  have hlim := han.continuousAt.tendsto.comp hpath
  have hid : dirichletSum ↗μ s = riemannZetaInv s := by
    apply tendsto_nhds_unique hc.tendsto_dirichletSum_add_real
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0 < u := hu
    have hr : 1 < (s+(u:ℂ)).re := by simp [hs,hu']
    have hn : s+(u:ℂ) ≠ 1 := by intro e; simp [e] at hr
    change riemannZetaInv _ = dirichletSum ↗μ _
    rw [riemannZetaInv_eq_inv_of_ne_one hn,
      (DirichletSeries.LSeriesSummable_moebius_iff.mpr hr).dirichletSum_eq_LSeries,
      LSeries_moebius_eq_inv_riemannZeta hr]
  rw [← hid]
  exact hc.tendsto

/-- The full boundary line has ordinary convergence without absolute convergence. -/
theorem moebius_conditionally_converges_of_re_eq_one {s : ℂ} (hs : s.re = 1) :
    DirichletConvergesAt ↗μ s ∧ ¬LSeriesSummable ↗μ s := by
  refine ⟨⟨_,tendsto_moebiusDirichletPartialSum_of_re_eq_one hs⟩,?_⟩
  exact fun h => (not_lt_of_ge hs.le) (DirichletSeries.LSeriesSummable_moebius_iff.mp h)

/-- At the pole the familiar real sum of μ(n)/n, taken in natural order, is zero. -/
theorem tendsto_sum_moebius_div_natCast :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ)/n) atTop (𝓝 0) := by
  have H := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_moebiusDirichletPartialSum_of_re_eq_one (s := 1) (by simp))
  simp only [riemannZetaInv] at H
  apply H.congr'
  filter_upwards with N
  simp only [Function.comp_apply,dirichletPartialSum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ := (Finset.mem_Icc.mp hn).1
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0),Complex.cpow_one]
  change (((μ n : ℝ):ℂ)/((n:ℝ):ℂ)).re = _
  rw [← Complex.ofReal_div,Complex.ofReal_re]

end AnalyticNumberTheory.RiemannZeta
