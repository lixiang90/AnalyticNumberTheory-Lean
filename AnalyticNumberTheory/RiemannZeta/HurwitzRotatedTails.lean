import AnalyticNumberTheory.RiemannZeta.HurwitzFourierTails
import AnalyticNumberTheory.AnalyticTools.FourierPowerContours

/-!
# Rotating the tails of the Hurwitz Fourier modes

A sloped ray in the half-plane of exponential decay gives an absolutely
convergent representative of the original conditionally convergent tail.
-/
noncomputable section
open Real Complex MeasureTheory Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- The upper or lower Fourier contour starting on the positive real axis. -/
def hurwitzRay (b k v : ℝ) : ℂ := (b:ℂ)+(1+k*I)*v

@[simp] theorem hurwitzRay_re (b k v : ℝ) : (hurwitzRay b k v).re=b+v := by simp [hurwitzRay,mul_re]
@[simp] theorem hurwitzRay_im (b k v : ℝ) : (hurwitzRay b k v).im=k*v := by simp [hurwitzRay,mul_im]

theorem fourierPowerMode_ofReal (s : ℂ) (ω v : ℝ) :
    fourierPowerMode s ω v=hurwitzMode s ω v := by unfold fourierPowerMode hurwitzMode;push_cast;rfl

theorem norm_fourierPowerMode (s : ℂ) (ω : ℝ) {z : ℂ} (hz : z≠0) :
    ‖fourierPowerMode s ω z‖=‖z‖^(-s.re)*Real.exp (Complex.arg z*s.im-ω*z.im) := by
  rw [fourierPowerMode,norm_mul,Complex.norm_exp,Complex.norm_cpow_of_ne_zero hz]
  simp only [mul_I_re,im_ofReal_mul,neg_re,neg_im]
  rw [show z.arg* -s.im= -(z.arg*s.im) by ring,Real.exp_sub]
  simp only [Real.exp_neg,div_eq_mul_inv,inv_inv];ring

private theorem mode_majorant (s : ℂ) (hσ : 0≤s.re) (ω k b v : ℝ) {z : ℂ}
    (hb : 0<b) (hbr : b≤z.re) (him : z.im=k*v) :
    ‖fourierPowerMode s ω z‖≤ b^(-s.re)*Real.exp (Real.pi*|s.im|)*Real.exp (-(ω*k)*v) := by
  have hz := hb.trans_le hbr
  have hg : z.arg*s.im≤Real.pi*|s.im| := (le_abs_self _).trans (by
    rw [abs_mul];exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi _) (abs_nonneg _))
  rw [norm_fourierPowerMode s ω (by intro he;simpa [he] using hz)]
  rw [mul_assoc,←Real.exp_add]
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hb (hbr.trans (Complex.re_le_norm z)) (neg_nonpos.mpr hσ))
    (Real.exp_le_exp.mpr (by rw [him];linarith [hg])) (Real.exp_nonneg _) (Real.rpow_nonneg hb.le _)

theorem integrable_fourierPowerMode_ray {s : ℂ} (hσ : 0≤s.re) {ω k b : ℝ} (hb : 0<b) (hk : 0<ω*k) :
    IntegrableOn (fun v : ℝ => fourierPowerMode s ω (hurwitzRay b k v)) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hk) 0).const_mul (b^(-s.re)*Real.exp (Real.pi*|s.im|))).mono'
  · unfold fourierPowerMode hurwitzRay;fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mode_majorant s hσ ω k b v hb (by simp;linarith [mem_Ioi.mp hv]) (by simp)

private theorem norm_vertical_edge {s : ℂ} (hσ : 0≤s.re) {ω k b R : ℝ} (hb : 0<b) (hR : 0≤R) (hk : 0<ω*k) :
    ‖(∫ v in (0:ℝ)..R,fourierPowerMode s ω (((b+R:ℝ):ℂ)+(k*I)*(v:ℂ)))‖ ≤
      (b+R)^(-s.re)*Real.exp (Real.pi*|s.im|)/(ω*k) := by
  have hr : 0<b+R := by linarith
  let A := (b+R)^(-s.re)*Real.exp (Real.pi*|s.im|)
  let f (v : ℝ) := fourierPowerMode s ω (((b+R:ℝ):ℂ)+(k*I)*(v:ℂ))
  have hf : Continuous f := by
    unfold f fourierPowerMode
    apply Continuous.mul (by fun_prop)
    apply continuous_iff_continuousAt.mpr
    intro v
    change ContinuousAt ((fun z : ℂ => z^(-s)) ∘ (fun u : ℝ => ((b+R:ℝ):ℂ)+(k*I)*(u:ℂ))) v
    exact (continuousAt_cpow_const (b:= -s) (Or.inl (by simp [mul_re];linarith : 0<(((b+R:ℝ):ℂ)+(k*I)*(v:ℂ)).re))).comp (f:=fun u : ℝ => ((b+R:ℝ):ℂ)+(k*I)*(u:ℂ)) (x:=v) (show ContinuousAt (fun u : ℝ => ((b+R:ℝ):ℂ)+(k*I)*(u:ℂ)) v by fun_prop)
  rw [intervalIntegral.integral_of_le hR]
  apply (norm_integral_le_integral_norm _).trans
  have hg : IntegrableOn (fun v : ℝ => A*Real.exp (-(ω*k)*v)) (Ioi 0) := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hk) 0).const_mul A
  have hs : Ioc 0 R⊆Ioi 0 := Ioc_subset_Ioi_self
  apply (setIntegral_mono_on (hf.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.mono_set hs) measurableSet_Ioc (fun v hv => ?_)).trans
  · apply (setIntegral_mono_set hg (by filter_upwards with v;dsimp [A];positivity) (Filter.Eventually.of_forall hs)).trans_eq
    rw [MeasureTheory.integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr hk),mul_zero,Real.exp_zero]
    dsimp [A];ring
  · apply mode_majorant s hσ ω k (b+R) v hr <;> simp [mul_re,mul_im]

/-- An exact absolutely convergent integral on either sloped ray. -/
theorem hurwitzTail_eq_ray {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) {ω k b : ℝ}
    (hb : 0<b) (hk : 0<ω*k) :
    hurwitzTail s ω b=(1+(k:ℂ)*I)*∫ v in Ioi (0:ℝ),fourierPowerMode s ω (hurwitzRay b k v) := by
  have hω : ω≠0 := fun he => by simp [he] at hk
  let V (R : ℝ) := ∫ v in (0:ℝ)..R,fourierPowerMode s ω (((b+R:ℝ):ℂ)+(k*I)*(v:ℂ))
  have hV : Tendsto V atTop (𝓝 0) := by
    apply squeeze_zero_norm' ((eventually_ge_atTop (0:ℝ)).mono fun R hR => norm_vertical_edge hσ.le hb hR hk)
    have hr := (tendsto_rpow_neg_atTop hσ).comp (tendsto_const_nhds.add_atTop (tendsto_id (α:=ℝ)) (C:=b))
    simpa using (hr.mul_const (Real.exp (Real.pi*|s.im|))).div_const (ω*k)
  have hR := intervalIntegral_tendsto_integral_Ioi (0:ℝ) (integrable_fourierPowerMode_ray hσ.le hb hk) (tendsto_id (α:=ℝ))
  have hT := (tendsto_integral_hurwitzMode hσ hσ' hω hb).comp (tendsto_const_nhds.add_atTop (tendsto_id (α:=ℝ)) (C:=b))
  have he : ∀ᶠ R : ℝ in atTop,(∫ v in b..(b+R),hurwitzMode s ω v)+(k*I)*V R =
      (1+(k:ℂ)*I)*(∫ v in 0..R,fourierPowerMode s ω (hurwitzRay b k v)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    have hg := integral_fourierPowerMode_line s ω 0 1 b (b+R) (fun v hv => Or.inl (by
      have hl := (uIcc_of_le (by linarith : b≤b+R)) ▸ hv;simpa using hb.trans_le hl.1))
    have hv := integral_fourierPowerMode_line s ω (b+R:ℝ) (k*I) 0 R (fun v _ => Or.inl (by simp [mul_re];linarith))
    have hd := integral_fourierPowerMode_line s ω b (1+k*I) 0 R (fun v hv => Or.inl (by
      have hl := (uIcc_of_le hR) ▸ hv;change 0<(hurwitzRay b k v).re;rw [hurwitzRay_re];linarith [hl.1]))
    simp only [one_mul,zero_add,fourierPowerMode_ofReal] at hg
    simp only [Complex.ofReal_zero,mul_zero,add_zero] at hv hd
    rw [show ((b+R:ℝ):ℂ)+(k*I)*(R:ℂ)=(b:ℂ)+(1+k*I)*(R:ℂ) by push_cast;ring] at hv
    change _+(k*I)*V R=_;dsimp only [V,hurwitzRay]
    linear_combination hg+hv-hd
  have h := tendsto_nhds_unique ((hT.add (hV.const_mul ((k:ℂ)*I))).congr' he) (hR.const_mul (1+(k:ℂ)*I))
  simpa using h

end AnalyticNumberTheory.RiemannZeta
