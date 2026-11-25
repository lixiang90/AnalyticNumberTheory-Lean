import AnalyticNumberTheory.RiemannZeta.HurwitzEndpointExpansion

/-!
# Uniform incomplete Hurwitz integrals at the end of the critical strip

Combining the derivative of the amplitude with the derivative of the
phase denominator introduces a factor 1−Re(s). It cancels the integral
of u^{-Re(s)} as the upper edge of the strip is approached.
-/
noncomputable section
open Real Complex Filter Set MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

theorem norm_hurwitzEndpoint (s : ℂ) (ω : ℝ) {u : ℝ} (hu : 0<u) :
    ‖hurwitzEndpoint s ω u‖ = u^(1-s.re)/|ω*u-s.im| := by
  rw [hurwitzEndpoint,norm_mul,norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu,Complex.norm_real,Real.norm_eq_abs,norm_hurwitzMode s ω hu,
    show 1-s.re= -s.re+1 by ring,Real.rpow_add hu,Real.rpow_one];ring

/-- First-derivative head estimate with a constant uniform up to Re(s)=1. -/
theorem hurwitzMode_head_uniform {s : ℂ} {ω x d : ℝ} (hx : 0<x) (hσ : s.re<1)
    (hd : 0<d) (hD : ∀ u : ℝ, 0<u → u≤x → d≤|ω*u-s.im|) :
    ‖∫ u in 0..x,hurwitzMode s ω u‖ ≤ x^(1-s.re)*(3/d+|ω| * x/d^2) := by
  have hpos : 0<1-s.re := by linarith
  have hpart (a : ℝ) (ha : 0<a) (hax : a≤x) :
      ‖∫ u in a..x,hurwitzMode s ω u‖ ≤ x^(1-s.re)*(3/d+|ω| * x/d^2) := by
    let D (u : ℝ) := ω*u-s.im
    let F := hurwitzMode s ω
    let w (u : ℝ) := s.re/D u+s.im/(D u)^2
    have hne (u : ℝ) (hu : u∈Icc a x) : D u≠0 := abs_pos.mp (hd.trans_le (hD u (ha.trans_le hu.1) hu.2))
    have hdc : ContinuousOn D (Icc a x) := by dsimp [D];fun_prop
    have hwc : ContinuousOn w (Icc a x) := (continuousOn_const.div hdc hne).add
      (continuousOn_const.div (hdc.pow 2) (fun u hu => pow_ne_zero 2 (hne u hu)))
    have hfc : ContinuousOn F (Icc a x) := fun u hu => (hurwitzMode_deriv s ω (ha.trans_le hu.1)).continuousAt.continuousWithinAt
    have hrc : ContinuousOn (fun u : ℝ => u^(-s.re)) (Icc a x) := fun u hu =>
      (Real.hasDerivAt_rpow_const (p:= -s.re) (Or.inl (ha.trans_le hu.1).ne')).continuousAt.continuousWithinAt
    let K := |ω| * x^(1-s.re)/d^2
    have hi : ‖∫ u in a..x,(w u:ℂ)*F u‖ ≤
        (1-s.re)/d*(∫ u in a..x,u^(-s.re))+(x-a)*K := by
      apply (intervalIntegral.norm_integral_le_integral_norm hax).trans
      have hi' : (∫ u in a..x,((1-s.re)/d*u^(-s.re)+K)) =
          (1-s.re)/d*(∫ u in a..x,u^(-s.re))+(x-a)*K := by
        rw [intervalIntegral.integral_add (f:=fun u : ℝ => (1-s.re)/d*u^(-s.re)) (g:=fun _ : ℝ => K) ((continuousOn_const.mul hrc).intervalIntegrable_of_Icc hax) intervalIntegrable_const,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul]
      rw [←hi']
      apply intervalIntegral.integral_mono_on hax
        (((Complex.continuous_ofReal.comp_continuousOn hwc).mul hfc).norm.intervalIntegrable_of_Icc hax)
        (((continuousOn_const.mul hrc).add continuousOn_const).intervalIntegrable_of_Icc hax)
      intro u hu
      have hup := ha.trans_le hu.1
      have hdu := hD u hup hu.2
      have hh : w u= -(1-s.re)/D u+ω*u/(D u)^2 := by dsimp only [w];field_simp [hne u hu];dsimp [D];ring
      change ‖(w u:ℂ)*hurwitzMode s ω u‖≤_
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_hurwitzMode s ω hup,hh]
      apply (mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.rpow_nonneg hup.le _)).trans
      rw [abs_div,abs_neg,abs_of_pos hpos,abs_div,abs_mul,abs_of_pos hup,abs_pow,add_mul]
      apply add_le_add (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hpos.le hd hdu) (by positivity))
      have hp : u*u^(-s.re)=u^(1-s.re) := by rw [show 1-s.re= -s.re+1 by ring,Real.rpow_add hup,Real.rpow_one];ring
      calc
        _ = |ω| * (u*u^(-s.re))/|D u|^2 := by ring
        _ ≤ K := by rw [hp]; apply div_le_div₀ (by positivity) _ (sq_pos_of_pos hd) (pow_le_pow_left₀ hd.le hdu 2)
                    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hup.le hu.2 hpos.le) (abs_nonneg _)
    have hi' : ‖∫ u in a..x,(w u:ℂ)*F u‖ ≤ x^(1-s.re)/d+x*K := by
      apply hi.trans
      rw [integral_rpow (Or.inl (by linarith : -1 < -s.re)),show -s.re+1=1-s.re by ring]
      have hh : (1-s.re)/d*((x^(1-s.re)-a^(1-s.re))/(1-s.re))=(x^(1-s.re)-a^(1-s.re))/d := by field_simp
      rw [hh]
      apply add_le_add (div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) hd.le)
      exact mul_le_mul_of_nonneg_right (by linarith) (by dsimp [K];positivity)
    have hends (u : ℝ) (hu : u∈Icc a x) : ‖hurwitzEndpoint s ω u‖≤x^(1-s.re)/d := by
      rw [norm_hurwitzEndpoint _ _ (ha.trans_le hu.1)]
      exact div_le_div₀ (by positivity) (Real.rpow_le_rpow (ha.trans_le hu.1).le hu.2 hpos.le) hd (hD _ (ha.trans_le hu.1) hu.2)
    have H := hurwitzMode_sub_endpoint_eq (s:=s) (ω:=ω) ha hax hne
    apply (show ‖∫ u in a..x,F u‖≤‖hurwitzEndpoint s ω x‖+‖hurwitzEndpoint s ω a‖+‖∫ u in a..x,(w u:ℂ)*F u‖ by
      rw [show (∫ u in a..x,F u)=(hurwitzEndpoint s ω x-hurwitzEndpoint s ω a)+
          -I*(∫ u in a..x,(w u:ℂ)*F u) by linear_combination H]
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (by simp))).trans
    apply (add_le_add (add_le_add (hends _ (right_mem_Icc.mpr hax)) (hends _ (left_mem_Icc.mpr hax))) hi').trans_eq
    dsimp [K];ring
  have hInt := hurwitzMode_integrable_at_zero hσ ω hx.le
  have hcont := intervalIntegral.continuousOn_primitive_interval_left
    (show IntegrableOn (hurwitzMode s ω) (uIcc 0 x) from by
      rw [uIcc_of_le hx.le,integrableOn_Icc_iff_integrableOn_Ioc];exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp hInt)
  have hfilt : 𝓝[>] (0:ℝ) ≤ 𝓝[uIcc 0 x] 0 := by
    apply nhdsWithin_le_of_mem
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hx)] with v (hv : 0<v) hvx
    rw [uIcc_of_le hx.le]; exact ⟨hv.le,hvx.le⟩
  apply le_of_tendsto (hcont 0 left_mem_uIcc |>.tendsto.norm.mono_left hfilt)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hx)] with v (hv : 0<v) hvx
  exact hpart v hv hvx.le

end AnalyticNumberTheory.RiemannZeta
