import AnalyticNumberTheory.SieveMethods.BuchstabLaplace
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Normalization of Buchstab's function and the linear sieve

The constant in the small-parameter expansion of the exponential integral
is determined by the logarithmic derivative of the gamma function at one.
Abelian convergence then identifies Buchstab's limiting value.
-/
noncomputable section
open Filter Set MeasureTheory Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

private theorem log_exp_integrable : IntegrableOn (fun t : ℝ => log t*exp (-t)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  intro hz
  have he := Real.eulerMascheroniConstant_eq_neg_integral_log
  rw [hz] at he
  linarith [Real.one_half_lt_eulerMascheroniConstant]

private theorem log_tail_parts {s : ℝ} (hs : 0<s) :
    log s+(∫t in Ioi s,exp (-t)/t)=
      (∫t in Ioi s,log t*exp (-t))+(1-exp (-s))*log s := by
  let U := Real.log
  let V := fun t : ℝ => exp (-t)
  have hU (t : ℝ) (ht : t∈Ioi s) : HasDerivAt U t⁻¹ t := Real.hasDerivAt_log (hs.trans ht).ne'
  have hV (t : ℝ) : HasDerivAt V (-exp (-t)) t := by simpa [V] using! (hasDerivAt_id' t).neg.exp
  have h₁ : IntegrableOn (U*(fun t => -exp (-t))) (Ioi s) := by
    simpa only [U,Pi.mul_def,mul_neg] using! (log_exp_integrable.mono_set (Ioi_subset_Ioi hs.le)).neg
  have h₂ : IntegrableOn ((fun t : ℝ => t⁻¹)*V) (Ioi s) := by
    apply ((integrableOn_exp_neg_Ioi s).const_mul s⁻¹).mono' (by dsimp [V,Pi.mul_def]; fun_prop)
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    change ‖t⁻¹*exp (-t)‖≤s⁻¹*exp (-t)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity [hs.trans ht])]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hs ht.le) (exp_pos _).le
  have hzero : Tendsto (U*V) (𝓝[>] s) (𝓝 (log s*exp (-s))) :=
    ((Real.continuousAt_log hs.ne').mul (by fun_prop : ContinuousAt V s)).tendsto.mono_left nhdsWithin_le_nhds
  have htop : Tendsto (U*V) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 zero_lt_one)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      exact mul_nonneg (Real.log_nonneg ht) (exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      change log t*exp (-t)≤t^(1:ℝ)*exp (-1*t)
      rw [Real.rpow_one,neg_one_mul]; gcongr; linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le ht)]
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul hU (fun t _ => hV t) h₁ h₂ hzero htop
  dsimp [U,V] at hip
  simp only [mul_neg,integral_neg,←div_eq_inv_mul] at hip
  linarith only [hip]

/-- The constant term of the exponential integral at zero is −γ. -/
theorem tendsto_log_add_expIntegral :
    Tendsto (fun s : ℝ => log s+∫t in Ioi s,exp (-t)/t) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  let f := fun t : ℝ => log t*exp (-t)
  have hcover : AECover (volume.restrict (Ioi (0:ℝ))) (𝓝[>] 0) (fun s : ℝ => Ioi s) :=
    aecover_Ioi_of_Ioi (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hlim : Tendsto (fun s : ℝ => ∫t in Ioi s,f t) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
    have h := hcover.integral_tendsto_of_countably_generated log_exp_integrable
    rw [Real.eulerMascheroniConstant_eq_neg_integral_log,neg_neg]
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi (mem_Ioi.mp hs).le)]
  have hr : Tendsto (fun s : ℝ => (1-exp (-s))*log s) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_log_mul_rpow_nhdsGT_zero (r:=1) zero_lt_one).norm)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0<s)
    simp only [Real.norm_eq_abs,abs_mul,Real.rpow_one]
    have hnon : 0≤1-exp (-s) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    rw [abs_of_nonneg hnon,abs_of_pos hs,mul_comm]
    gcongr; linarith [Real.add_one_le_exp (-s)]
  have hh := hlim.add hr
  apply (show Tendsto (fun s : ℝ => (∫t in Ioi s,f t)+(1-exp (-s))*log s) (𝓝[>] 0)
    (𝓝 (-eulerMascheroniConstant)) by simpa using! hh).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs using (log_tail_parts hs).symm


private theorem abelian_buchstab {L : ℝ} (hL : Tendsto buchstab atTop (𝓝 L)) :
    Tendsto (fun s : ℝ => s*buchstabLaplace s) (𝓝[>] 0) (𝓝 L) := by
  let F := fun s : ℝ => (Ioi s).indicator (fun t : ℝ => buchstab (t/s)*exp (-t))
  let G := fun t : ℝ => L*exp (-t)
  let μ := volume.restrict (Ioi (0:ℝ))
  have hmeas (s : ℝ) : AEStronglyMeasurable (F s) μ := by
    apply AEStronglyMeasurable.indicator _ measurableSet_Ioi
    exact ((continuous_buchstab.comp (continuous_id.div_const s)).mul (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ s in 𝓝[>] (0:ℝ),∀ᵐ t ∂μ, ‖F s t‖≤exp (-t) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0<s)
    apply Eventually.of_forall
    intro t; dsimp [F]; by_cases ht : s<t
    · rw [indicator_of_mem ht]
      have hb := buchstab_mem_Icc ((one_le_div hs).mpr ht.le)
      rw [abs_of_nonneg (mul_nonneg (by linarith [hb.1]) (exp_pos _).le)]
      exact mul_le_of_le_one_left (exp_pos _).le hb.2
    · rw [indicator_of_notMem ht,abs_zero]; exact (exp_pos _).le
  have hpoint : ∀ᵐ t ∂μ,Tendsto (fun s => F s t) (𝓝[>] 0) (𝓝 (G t)) := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t (ht : 0<t)
    have hdiv : Tendsto (fun s : ℝ => t/s) (𝓝[>] 0) atTop := by
      simpa [div_eq_mul_inv] using! tendsto_const_nhds.pos_mul_atTop ht tendsto_inv_nhdsGT_zero
    apply ((hL.comp hdiv).mul_const (exp (-t))).congr'
    filter_upwards [(eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs
    simp only [F,indicator_of_mem (show t∈Ioi s from hs),Function.comp_def]
  have h := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (F:=F) (f:=G)
    (fun t => exp (-t)) (Eventually.of_forall hmeas) hbound (integrableOn_exp_neg_Ioi 0) hpoint
  have hG : (∫t,G t ∂μ)=L := by
    change (∫t in Ioi (0:ℝ),L*exp (-t))=L
    rw [integral_const_mul]
    have hv := integral_exp_mul_Ioi (a:= -1) (by norm_num) 0
    simpa [neg_one_mul] using congrArg (fun z => L*z) hv
  rw [hG] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0<s)
  change (∫t in Ioi (0:ℝ),(Ioi s).indicator (fun t => buchstab (t/s)*exp (-t)) t)=_
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hs.le)]
  have hscale := integral_comp_mul_left_Ioi' (fun t : ℝ => buchstab (t/s)*exp (-t)) 1 hs
  simpa only [smul_eq_mul,mul_one,mul_div_cancel_left₀ _ hs.ne',neg_mul,buchstabLaplace] using hscale.symm

/-- Buchstab's normalization at infinity is e^(−γ). -/
theorem tendsto_buchstab : Tendsto buchstab atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
  obtain ⟨L,hL⟩ := buchstab_exists_limit
  have h₁ : Tendsto (fun s : ℝ => s*(1+buchstabLaplace s)) (𝓝[>] 0) (𝓝 L) := by
    have h := (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[>] (0:ℝ)) (𝓝 0)).add (abelian_buchstab hL)
    simpa only [id_eq,zero_add,mul_add,mul_one] using! h
  have h₂ : Tendsto (fun s : ℝ => s*(1+buchstabLaplace s)) (𝓝[>] 0) (𝓝 (exp (-eulerMascheroniConstant))) := by
    apply (Real.continuous_exp.continuousAt.tendsto.comp tendsto_log_add_expIntegral).congr'
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0<s)
    change exp (log s+_)=_
    rw [←log_one_add_buchstabLaplace hs,Real.exp_add,Real.exp_log hs,Real.exp_log (by linarith [buchstabLaplace_nonneg s])]
  exact tendsto_nhds_unique h₁ h₂ ▸ hL

/-- Both the upper and the lower one-dimensional linear sieve function tend
to one, with the conventional Euler–Mascheroni normalization. -/
theorem tendsto_linearSieve :
    Tendsto linearSieveUpper atTop (𝓝 1) ∧ Tendsto linearSieveLower atTop (𝓝 1) := by
  have hsum : Tendsto (fun t : ℝ => linearSieveUpper t+linearSieveLower t) atTop (𝓝 2) := by
    have h := tendsto_buchstab.const_mul (2*exp eulerMascheroniConstant)
    rw [Real.exp_neg,mul_inv_cancel_right₀ (Real.exp_ne_zero _)] at h
    exact h.congr' ((eventually_ge_atTop (1:ℝ)).mono (fun t ht => (linearSieve_sum_eq_buchstab ht).symm))
  have hgap : Tendsto (fun t : ℝ => linearSieveUpper t-linearSieveLower t) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.const_mul (2*exp eulerMascheroniConstant)
    rw [mul_zero] at h
    apply squeeze_zero' _ _ h
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      exact (linearSieve_gap_le_factorial 0 (by simpa using ht)).1.le
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      simpa [div_eq_mul_inv] using (linearSieve_gap_le_factorial 0 (by simpa using ht)).2
  constructor
  · have h := (hsum.add hgap).div_const 2
    norm_num at h
    apply h.congr; intro t; ring
  · have h := (hsum.sub hgap).div_const 2
    norm_num at h
    apply h.congr; intro t; ring

end AnalyticNumberTheory.SieveMethods
