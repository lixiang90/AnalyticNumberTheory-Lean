import AnalyticNumberTheory.AnalyticTools.GammaLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The oscillatory gamma integral at nonzero real frequency

One integration by parts at a positive cutoff replaces the conditionally
convergent Fourier integral by two absolutely convergent integrals.
Passing to the boundary of the complex Laplace half-plane identifies the
result with the classical gamma factor.
-/
noncomputable section
open Complex Filter Set MeasureTheory Real
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

private theorem norm_kernel_le {s z : ℂ} (hz : 0≤z.re) {u : ℝ} (hu : 0<u) :
    ‖gammaLaplaceKernel s z u‖ ≤ u^(s.re-1) := by
  rw [norm_gammaLaplaceKernel _ _ hu]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hu.le _) (Real.exp_le_one_iff.mpr (by nlinarith))

theorem integrable_gammaLaplaceKernel_tail {s z : ℂ} (hs₁ : s.re<1) (hz : 0≤z.re)
    {x : ℝ} (hx : 0<x) : IntegrableOn (gammaLaplaceKernel (s-1) z) (Ioi x) := by
  apply (integrableOn_Ioi_rpow_of_lt (by dsimp; linarith : (s-1).re-1 < -1) hx).mono'
  · unfold gammaLaplaceKernel; fun_prop
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun u hu => norm_kernel_le hz (hx.trans hu)

/-- Tail integration by parts in the closed Laplace half-plane. -/
theorem gammaLaplace_tail_recurrence {s z : ℂ} (hs₁ : s.re<1) (hz : 0≤z.re)
    {x : ℝ} (hx : 0<x) (h₁ : IntegrableOn (gammaLaplaceKernel s z) (Ioi x)) :
    z*(∫ u in Ioi x,gammaLaplaceKernel s z u)=
      gammaLaplaceKernel s z x+(s-1)*∫ u in Ioi x,gammaLaplaceKernel (s-1) z u := by
  have hsne : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h₂ := integrable_gammaLaplaceKernel_tail hs₁ hz hx
  have hder (u : ℝ) (hu : u∈Ici x) : HasDerivAt (gammaLaplaceKernel s z)
      (-z*gammaLaplaceKernel s z u+(s-1)*gammaLaplaceKernel (s-1) z u) u := by
    have hp := hasDerivAt_ofReal_cpow_const (hx.trans_le hu).ne' hsne
    have he := (((hasDerivAt_id u).ofReal_comp).const_mul (-z)).cexp
    convert he.mul hp using 1
    · ext v; simp [gammaLaplaceKernel,neg_mul]
    · dsimp [gammaLaplaceKernel]; ring
  have ht : Tendsto (gammaLaplaceKernel s z) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu using norm_kernel_le hz hu
    · simpa only [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0<1-s.re)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hder ((h₁.const_mul (-z)).add (h₂.const_mul (s-1))) ht
  rw [integral_add (h₁.const_mul (-z)) (h₂.const_mul (s-1)),integral_const_mul,integral_const_mul,zero_sub] at hi
  linear_combination -hi

private theorem laplace_split {s z : ℂ} (hs₀ : 0<s.re) (hs₁ : s.re<1) (hz : 0<z.re)
    {x : ℝ} (hx : 0<x) :
    z^(-s)*Complex.Gamma s = (∫ u in Ioc 0 x,gammaLaplaceKernel s z u) +
      (gammaLaplaceKernel s z x+(s-1)*∫ u in Ioi x,gammaLaplaceKernel (s-1) z u)/z := by
  have hzne : z≠0 := by intro he; simpa [he] using hz
  have h₀ := integrable_gammaLaplaceKernel hs₀ hz
  have h₁ := h₀.mono_set (Ioi_subset_Ioi hx.le)
  have hi := gammaLaplace_tail_recurrence hs₁ hz.le hx h₁
  rw [←integral_gammaLaplaceKernel_rightHalfPlane hs₀ hz]
  change (∫ u in Ioi (0:ℝ),gammaLaplaceKernel s z u)=_
  rw [←Ioc_union_Ioi_eq_Ioi hx.le,setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (h₀.mono_set Ioc_subset_Ioi_self) h₁]
  congr 1
  apply (eq_div_iff hzne).mpr
  linear_combination hi

private theorem tendsto_boundary_integral (s z : ℂ) (hz : z.re=0) {S : Set ℝ}
    (hS : MeasurableSet S) (hpos : ∀ u∈S,0<u) (hdom : IntegrableOn (fun u : ℝ => u^(s.re-1)) S) :
    Tendsto (fun ε : ℝ => ∫ u in S,gammaLaplaceKernel s ((ε:ℂ)+z) u) (𝓝[>] 0)
      (𝓝 (∫ u in S,gammaLaplaceKernel s z u)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => u^(s.re-1))
  · exact Eventually.of_forall fun ε => by unfold gammaLaplaceKernel; fun_prop
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0<ε)
    exact (ae_restrict_mem hS).mono fun u hu => norm_kernel_le (by simp [hz,hε.le]) (hpos u hu)
  · exact hdom
  · apply ae_of_all; intro u
    have hc : Continuous (fun ε : ℝ => gammaLaplaceKernel s ((ε:ℂ)+z) u) := by unfold gammaLaplaceKernel; fun_prop
    simpa only [Complex.ofReal_zero,zero_add] using (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds

/-- Fourier–Mellin transform of a power on the half-line at the boundary
of the Laplace half-plane. The upper tail is integrated by parts once. -/
theorem oscillatoryGamma_split {s z : ℂ} (hs₀ : 0<s.re) (hs₁ : s.re<1)
    (hz : z.re=0) (hz₀ : z≠0) {x : ℝ} (hx : 0<x) :
    z^(-s)*Complex.Gamma s = (∫ u in Ioc 0 x,gammaLaplaceKernel s z u) +
      (gammaLaplaceKernel s z x+(s-1)*∫ u in Ioi x,gammaLaplaceKernel (s-1) z u)/z := by
  let Z (ε : ℝ) := (ε:ℂ)+z
  have hZ : Tendsto Z (𝓝[>] 0) (𝓝 z) := by
    have hcont : Continuous Z := by dsimp [Z]; fun_prop
    simpa [Z] using (hcont.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have hzsl : z∈Complex.slitPlane := Or.inr (by
    intro he; exact hz₀ (Complex.ext (by simpa using hz) (by simpa using he)))
  have hl := (continuousAt_cpow_const (b:=-s) hzsl).tendsto.comp hZ
  have hleft := tendsto_boundary_integral s z hz measurableSet_Ioc (fun u hu => hu.1)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<s.re-1)))
  have hright := tendsto_boundary_integral (s-1) z hz measurableSet_Ioi (fun u hu => hx.trans hu)
    (integrableOn_Ioi_rpow_of_lt (by dsimp; linarith : (s-1).re-1 < -1) hx)
  have hc : Continuous (fun w => gammaLaplaceKernel s w x) := by unfold gammaLaplaceKernel; fun_prop
  apply tendsto_nhds_unique (hl.mul_const (Complex.Gamma s))
  apply (hleft.add (((hc.continuousAt.tendsto.comp hZ).add (hright.const_mul (s-1))).div hZ hz₀)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0<ε)
  exact (laplace_split hs₀ hs₁ (by simp [Z,hz,hε] : 0<(Z ε).re) hx).symm

end AnalyticNumberTheory.AnalyticTools
