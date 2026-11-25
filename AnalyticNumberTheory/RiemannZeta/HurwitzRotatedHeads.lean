import AnalyticNumberTheory.RiemannZeta.HurwitzRotatedTails

/-!
# Rotating the initial segments of a Hurwitz Fourier mode

The path from 0 to b goes first along a lower diagonal and then follows
the steepest descent diagonal through b. The integrable endpoint at the
origin is handled by a shrinking vertical segment.
-/
noncomputable section
open Real Complex MeasureTheory Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem radial_majorant {s : ℂ} (hσ : 0≤s.re) {b : ℝ} (hb : 0<b) (ω k : ℝ) {z : ℂ}
    (hz : 0<z.re) (him : |z.im|≤b) :
    ‖fourierPowerMode s ω z‖≤ z.re^(-s.re)*Real.exp (Real.pi*|s.im|+|ω| *b) := by
  rw [norm_fourierPowerMode s ω (by intro he;simpa [he] using hz)]
  apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hz (Complex.re_le_norm _) (neg_nonpos.mpr hσ)) _ (by positivity) (Real.rpow_nonneg hz.le _)
  apply Real.exp_le_exp.mpr
  have H : z.arg*s.im≤Real.pi*|s.im| := (le_abs_self (z.arg*s.im)).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi _) (abs_nonneg _))
  have H' : -(ω*z.im)≤|ω| *b := (neg_le_abs (ω*z.im)).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left him (abs_nonneg ω))
  linarith

private theorem radial_integrable {s : ℂ} (hσ : 0≤s.re) (hσ' : s.re<1) {b : ℝ} (hb : 0<b)
    (ω : ℝ) {k : ℝ} (hk : |k|≤1) :
    IntervalIntegrable (fun t : ℝ => fourierPowerMode s ω ((1+k*I)*t)) volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  have H := (intervalIntegral.intervalIntegrable_rpow' (a:=(0:ℝ)) (b:=b) (by linarith : -1 < -s.re)).1
  apply (H.mul_const (Real.exp (Real.pi*|s.im|+|ω| *b))).mono'
  · unfold fourierPowerMode;fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hre : (((1:ℂ)+k*I)*t).re=t := by simp [mul_re]
    have him : |(((1:ℂ)+k*I)*t).im|≤b := by
      simp [mul_im,abs_mul,abs_of_pos ht.1];nlinarith [mul_le_mul_of_nonneg_right hk ht.1.le,ht.2]
    simpa [hre] using radial_majorant hσ hb ω k (by simpa [hre] using ht.1) him

private theorem tendsto_start_integral {f : ℝ → ℂ} {b : ℝ} (hb : 0<b) (hi : IntervalIntegrable f volume 0 b) :
    Tendsto (fun v => ∫ u in v..b,f u) (𝓝[>] 0) (𝓝 (∫ u in (0:ℝ)..b,f u)) := by
  have h := intervalIntegral.continuousOn_primitive_interval' hi (right_mem_uIcc (a:=0) (b:=b))
  have hh := (h 0 left_mem_uIcc).tendsto
  rw [uIcc_of_le hb.le,nhdsWithin_Icc_eq_nhdsGE hb] at hh
  simpa only [←intervalIntegral.integral_symm b] using (hh.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).neg

/-- Rotate an integrable power at the origin into the lower diagonal. -/
theorem hurwitzMode_head_eq_diagonals {s : ℂ} (hσ : 0≤s.re) (hσ' : s.re<1) (ω : ℝ) {b : ℝ} (hb : 0<b) :
    (∫ t in (0:ℝ)..b,hurwitzMode s ω t) =
      (1-I)*(∫ t in (0:ℝ)..(b/2),fourierPowerMode s ω ((1-I)*t))+
      (1+I)*(∫ t in (-b/2)..0,fourierPowerMode s ω (hurwitzRay b 1 t)) := by
  let V (r : ℝ) := (-I)*(∫ t in (0:ℝ)..r,fourierPowerMode s ω ((r:ℂ)-I*t))
  have hV : Tendsto V (𝓝[>] 0) (𝓝 0) := by
    let E := Real.exp (Real.pi*|s.im|+|ω| *b)
    apply squeeze_zero_norm' (a:=fun u => E*u^(1-s.re)) _
      (by simpa only [Real.zero_rpow (by linarith : 1-s.re≠0),mul_zero] using
        ((Real.continuous_rpow_const (by linarith : 0≤1-s.re)).continuousAt (x:=0)).continuousWithinAt (s:=Ioi 0) |>.tendsto.const_mul E)
    filter_upwards [Ioo_mem_nhdsGT hb] with r hr
    dsimp only [V];rw [norm_mul,norm_neg,Complex.norm_I,one_mul]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=r) (f:=fun t : ℝ => fourierPowerMode s ω ((r:ℂ)-I*t))
      (C:=r^(-s.re)*E) (fun t ht => by
        rw [uIoc_of_le hr.1.le] at ht
        simpa [Complex.sub_re,mul_re,E] using radial_majorant hσ hb ω (-1) (z:=(r:ℂ)-I*t)
          (by simpa [mul_re] using hr.1) (by simp [mul_im,abs_of_pos ht.1];linarith [ht.2,hr.2]))
    rw [sub_zero,abs_of_pos hr.1] at H
    apply H.trans_eq
    rw [show 1-s.re= -s.re+1 by ring,Real.rpow_add_one hr.1.ne'];ring
  let d := b/2
  have hd : 0<d := by dsimp [d];linarith
  have hreal := radial_integrable hσ hσ' hb ω (k:=0) (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,add_zero,one_mul,fourierPowerMode_ofReal] at hreal
  have hlow := radial_integrable hσ hσ' hd ω (k:= -1) (by norm_num)
  simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,←sub_eq_add_neg] at hlow
  have hL := tendsto_start_integral hd hlow
  have hR := tendsto_start_integral hb hreal
  let J := (1+I)*(∫ t in (-b/2)..0,fourierPowerMode s ω (hurwitzRay b 1 t))
  have H : ∀ᶠ r : ℝ in 𝓝[>] 0, V r+(1-I)*(∫ t in r..d,fourierPowerMode s ω ((1-I)*t))+J =
      ∫ t in r..b,hurwitzMode s ω t := by
    filter_upwards [Ioo_mem_nhdsGT hd] with r hr
    have he := integral_fourierPowerMode_line s ω (r:ℂ) (-I) 0 r (fun _ _ => Or.inl (by simpa [mul_re] using hr.1))
    have hl := integral_fourierPowerMode_line s ω 0 (1-I) r d (fun t ht => Or.inl (by
      rw [uIcc_of_le hr.2.le] at ht;simpa [mul_re] using hr.1.trans_le ht.1))
    have hr' := integral_fourierPowerMode_line s ω 0 1 r b (fun t ht => Or.inl (by
      rw [uIcc_of_le (by dsimp [d] at hr;linarith [hr.2] : r≤b)] at ht;simpa using hr.1.trans_le ht.1))
    have hj := integral_fourierPowerMode_line s ω (b:ℂ) (1+I) (-b/2) 0 (fun t ht => Or.inl (by
      rw [uIcc_of_le (by linarith : -b/2≤0)] at ht;simp [mul_re];linarith [ht.1]))
    simp only [ofReal_zero,mul_zero,add_zero,zero_add,one_mul,fourierPowerMode_ofReal] at he hl hr' hj
    have hp : (r:ℂ)+ -I*r=(1-I)*(r:ℂ) := by ring
    have hp' : (b:ℂ)+(1+I)*((-b/2:ℝ):ℂ)=(1-I)*(d:ℂ) := by dsimp [d];push_cast;ring
    rw [hp] at he;rw [hp'] at hj
    dsimp only [V,J,hurwitzRay];simp only [ofReal_one,one_mul,←sub_eq_add_neg,neg_mul] at he ⊢
    linear_combination he+hl+hj-hr'
  have h := tendsto_nhds_unique ((((hV.add (hL.const_mul (1-I))).add_const J).congr' H)) hR
  simpa only [zero_add] using h.symm

end AnalyticNumberTheory.RiemannZeta
