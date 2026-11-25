import AnalyticNumberTheory.SieveMethods.BuchstabFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace transform of Buchstab's function

The delay equation yields a first-order differential equation for one plus
the Laplace transform. Integration determines the transform explicitly.
-/
noncomputable section
open Filter Set MeasureTheory Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

attribute [local fun_prop] continuous_buchstab

/-- The Laplace transform on the natural domain [1,∞) of Buchstab's function. -/
def buchstabLaplace (s : ℝ) : ℝ := ∫ t in Ioi (1:ℝ), buchstab t*exp (-s*t)

private theorem moment_integrable {s : ℝ} (hs : 0<s) (a : ℝ) (ha : 0≤a) :
    IntegrableOn (fun t : ℝ => t*exp (-s*t)) (Ioi a) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : (-1:ℝ)<1)
    (by norm_num : (0:ℝ)<1) hs
  simpa only [Real.rpow_one] using h.mono_set (Ioi_subset_Ioi ha)

private theorem laplace_integrable {s a : ℝ} (hs : 0<s) (ha : 1≤a) :
    IntegrableOn (fun t : ℝ => buchstab t*exp (-s*t)) (Ioi a) := by
  apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) a).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  have ht' : 1≤t := ha.trans ht.le
  have hb := buchstab_mem_Icc ht'
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith [hb.1]) (exp_pos _).le)]
  exact mul_le_of_le_one_left (exp_pos _).le hb.2

private theorem weighted_integrable {s a : ℝ} (hs : 0<s) (ha : 1≤a) :
    IntegrableOn (fun t : ℝ => t*buchstab t*exp (-s*t)) (Ioi a) := by
  apply (moment_integrable hs a (zero_le_one.trans ha)).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  have ht' := ha.trans ht.le
  have hb := buchstab_mem_Icc ht'
  have ht₀ : 0≤t := zero_le_one.trans ht'
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity [show 0≤buchstab t by linarith [hb.1]])]
  gcongr; exact mul_le_of_le_one_right ht₀ hb.2

private theorem laplace_deriv {s : ℝ} (hs : 0<s) :
    HasDerivAt buchstabLaplace (-(∫t in Ioi (1:ℝ),t*buchstab t*exp (-s*t))) s := by
  let F := fun a t : ℝ => buchstab t*exp (-a*t)
  let G := fun a t : ℝ => -(t*buchstab t*exp (-a*t))
  have hmeas (a : ℝ) : Continuous (F a) := by dsimp [F]; fun_prop
  have hG (a : ℝ) : Continuous (G a) := by dsimp [G]; fun_prop
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (1:ℝ)),∀a∈Ioi (s/2),‖G a t‖≤t*exp (-(s/2)*t) := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht a ha
    have hb := buchstab_mem_Icc ht.le
    have ht₀ : 0≤t := zero_le_one.trans ht.le
    dsimp only [G]
    rw [Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity [show 0≤buchstab t by linarith [hb.1]])]
    apply mul_le_mul (mul_le_of_le_one_right ht₀ hb.2) _ (exp_pos _).le ht₀
    apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonneg_right (neg_le_neg ha.le) ht₀
  have hder (a t : ℝ) : HasDerivAt (fun b => F b t) (G a t) a := by
    have h := ((((hasDerivAt_id' a).neg).mul_const t).exp).const_mul (buchstab t)
    change HasDerivAt (fun b : ℝ => buchstab t*exp (-b*t)) _ a
    convert h using 1 <;> dsimp [G] <;> ring
  obtain ⟨_,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (show s/2<s by linarith)) (Eventually.of_forall (fun a => (hmeas a).aestronglyMeasurable))
    (laplace_integrable hs le_rfl) (hG s).aestronglyMeasurable hbound
    (moment_integrable (show 0<s/2 by linarith) 1 zero_le_one)
    (Eventually.of_forall (fun t a _ => hder a t))
  simpa only [G,integral_neg] using! hd

theorem buchstabLaplace_nonneg (s : ℝ) : 0≤buchstabLaplace s :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (by linarith [(buchstab_mem_Icc ht.le).1]) (exp_pos _).le

/-- A pointwise bound from 0≤ω≤1. -/
theorem buchstabLaplace_le {s : ℝ} (hs : 0<s) :
    buchstabLaplace s≤exp (-s)/s := by
  have h := setIntegral_mono_on (laplace_integrable hs le_rfl)
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 1) measurableSet_Ioi
    (fun t (ht : t∈Ioi (1:ℝ)) => mul_le_of_le_one_left (exp_pos _).le (buchstab_mem_Icc ht.le).2)
  simpa only [buchstabLaplace,integral_exp_mul_Ioi (neg_lt_zero.mpr hs),mul_one,neg_div_neg_eq] using h


private theorem delay_integrable {s : ℝ} (hs : 0<s) :
    IntegrableOn (fun t : ℝ => buchstab (t-1)*exp (-s*t)) (Ioi 2) := by
  apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 2).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  have hb := buchstab_mem_Icc (show 1≤t-1 by change 2<t at ht; linarith)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith [hb.1]) (exp_pos _).le)]
  exact mul_le_of_le_one_left (exp_pos _).le hb.2

private theorem shift_integral (s : ℝ) :
    (∫t in Ioi (2:ℝ),buchstab (t-1)*exp (-s*t))=exp (-s)*buchstabLaplace s := by
  have H := (measurePreserving_add_right (volume : Measure ℝ) (-1:ℝ)).setIntegral_preimage_emb
    (h₂:=(Homeomorph.addRight (-1:ℝ)).isClosedEmbedding.measurableEmbedding)
    (fun t : ℝ => buchstab t*exp (-s*t)) (Ioi 1)
  have he : (fun t : ℝ => t+(-1)) ⁻¹' Ioi 1=Ioi 2 := by
    ext x; change 1<x+ -1 ↔ 2<x; constructor <;> intro hh <;> linarith
  rw [he] at H
  rw [buchstabLaplace,←H,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [←mul_assoc,show exp (-s)*buchstab (t+ -1)*exp (-s*(t+ -1))=
    buchstab (t-1)*(exp (-s)*exp (-s*(t+ -1))) by ring_nf,←Real.exp_add]
  congr 2; ring

private theorem moment_eq {s : ℝ} (hs : 0<s) :
    s*(∫t in Ioi (1:ℝ),t*buchstab t*exp (-s*t))=exp (-s)*(1+buchstabLaplace s) := by
  let U := fun t : ℝ => t*buchstab t
  let K := fun t : ℝ => exp (-s*t)
  have hU (t : ℝ) (ht : t∈Ioi 2) : HasDerivAt U (buchstab (t-1)) t := hasDerivAt_mul_buchstab ht
  have hK (t : ℝ) : HasDerivAt K ((-s)*K t) t := by
    simpa only [K,mul_one,mul_comm] using! ((hasDerivAt_id' t).const_mul (-s)).exp
  have hint : IntegrableOn (U*(fun t => (-s)*K t)) (Ioi 2) := by
    rw [show U*(fun t => -s*K t)=(fun t => -s*(t*buchstab t*exp (-s*t))) by ext t; dsimp [U,K]; ring]
    exact (weighted_integrable hs (show (1:ℝ)≤2 by norm_num)).const_mul (-s)
  have htend : Tendsto (U*K) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s hs)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      change 0≤t*buchstab t*exp (-s*t)
      positivity [show 0≤buchstab t by linarith [(buchstab_mem_Icc ht).1],zero_le_one.trans ht]
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      change t*buchstab t*exp (-s*t)≤t^(1:ℝ)*exp (-s*t)
      rw [Real.rpow_one]; gcongr; exact mul_le_of_le_one_right (zero_le_one.trans ht) (buchstab_mem_Icc ht).2
  have hBd : Tendsto (U*K) (𝓝[>] 2) (𝓝 (exp (-s*2))) := by
    have hc : Continuous (U*K) := by dsimp [U,K]; fun_prop
    have he : (U*K) 2=exp (-s*2) := by
      change 2*buchstab 2*_=_
      rw [buchstab_initial (by norm_num : (2:ℝ)∈Icc 1 2)]
      norm_num [K]
    exact he ▸ (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul hU (fun t _ => hK t) hint (delay_integrable hs) hBd htend
  rw [show (fun t => U t*((-s)*K t))=(fun t => (-s)*(t*buchstab t*exp (-s*t))) by
    ext t; dsimp [U,K]; ring,integral_const_mul] at hip
  change (-s)*(∫t in Ioi (2:ℝ),t*buchstab t*exp (-s*t))=0-exp (-s*2)-
    (∫t in Ioi (2:ℝ),buchstab (t-1)*exp (-s*t)) at hip
  rw [shift_integral] at hip
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (weighted_integrable hs (a:=1) le_rfl) (b:=2) (by norm_num)
  have hsmall : (∫t in (1:ℝ)..2,t*buchstab t*exp (-s*t))=∫t in (1:ℝ)..2,exp (-s*t) := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le (by norm_num)] at ht
    dsimp only
    rw [buchstab_initial ht,mul_inv_cancel₀ (show t≠0 by linarith [ht.1]),one_mul]
  rw [hsmall,←intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 1) (b:=2) (by norm_num),
    integral_exp_mul_Ioi (neg_lt_zero.mpr hs),integral_exp_mul_Ioi (neg_lt_zero.mpr hs),mul_one] at hsplit
  rw [neg_div_neg_eq,neg_div_neg_eq,←sub_div,eq_div_iff hs.ne'] at hsplit
  linarith only [hip,hsplit]

/-- Differential equation for the transform on the positive axis. -/
theorem hasDerivAt_buchstabLaplace {s : ℝ} (hs : 0<s) :
    HasDerivAt buchstabLaplace (-exp (-s)*(1+buchstabLaplace s)/s) s := by
  have hh := moment_eq hs
  convert laplace_deriv hs using 1
  rw [div_eq_iff hs.ne']; linarith only [hh]


/-- Explicit Laplace-transform formula:
log(1+∫₁^∞ ω(t)e^(−st)dt)=∫ₛ^∞ e^(−t)/t dt for s>0. -/
theorem log_one_add_buchstabLaplace {s : ℝ} (hs : 0<s) :
    log (1+buchstabLaplace s)=∫t in Ioi s,exp (-t)/t := by
  have hder (t : ℝ) (ht : s≤t) : HasDerivAt (fun x => log (1+buchstabLaplace x)) (-(exp (-t)/t)) t := by
    have h₁ : 0<1+buchstabLaplace t := by linarith [buchstabLaplace_nonneg t]
    have h := ((hasDerivAt_buchstabLaplace (hs.trans_le ht)).const_add 1).log h₁.ne'
    convert h using 1
    field_simp [h₁.ne',(hs.trans_le ht).ne']
  have hzero : Tendsto buchstabLaplace atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall buchstabLaplace_nonneg) _ tendsto_inv_atTop_zero
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hpos : 0<t := by linarith
    exact (buchstabLaplace_le hpos).trans (by rw [←one_div]; gcongr; exact Real.exp_le_one_iff.mpr (by linarith))
  have hlim : Tendsto (fun t => log (1+buchstabLaplace t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using! (Real.continuousAt_log (x:=1+0) (by norm_num)).tendsto.comp (tendsto_const_nhds.add hzero)
  have hsub := integral_Ioi_of_hasDerivAt_of_nonpos' (a:=s) (fun t ht => hder t ht)
    (fun t ht => neg_nonpos.mpr (div_nonneg (exp_pos _).le (hs.trans (mem_Ioi.mp ht)).le)) hlim
  rw [integral_neg] at hsub; linarith

end AnalyticNumberTheory.SieveMethods
