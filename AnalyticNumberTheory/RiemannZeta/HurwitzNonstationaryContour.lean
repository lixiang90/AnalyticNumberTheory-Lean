import AnalyticNumberTheory.RiemannZeta.HurwitzGeometricTails

/-!
# The nonstationary contour of the Hurwitz equation

All negative-frequency modes have a single geometric tail on the lower
ray. The power itself decays there on the scale b/t.
-/
noncomputable section
open Real Complex MeasureTheory Filter Set
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem lower_ray_arg {b v : ℝ} (hb : 0<b) (hv : 0<v) :
    (hurwitzRay b (-1) v).arg ≤ -v/(b+2*v) := by
  let z := hurwitzRay b (-1) v
  have hi : z.im= -v := by simp [z]
  have hr : z.re=b+v := by simp [z]
  have hneg : z.arg<0 := Complex.arg_neg_iff.mpr (by rw [hi];linarith)
  have hnorm : ‖z‖≤b+2*v := (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [hr,hi,abs_neg,abs_of_pos hv,abs_of_pos (by linarith)];linarith)
  have hp : 0<‖z‖ := (by linarith : 0<b+v).trans_le (hr ▸ Complex.re_le_norm z)
  have h := Real.sin_le (show 0≤ -z.arg by linarith)
  rw [Real.sin_neg,Complex.sin_arg,hi,neg_div,neg_neg] at h
  apply le_trans (by linarith : z.arg≤ -(v/‖z‖)) _
  rw [neg_div];exact neg_le_neg (div_le_div_of_nonneg_left hv.le hp hnorm)

private theorem norm_lower_integrand {s : ℂ} (hσ : 0≤s.re) (ht : 0<s.im) {b v C : ℝ} (hb : 0<b) (hv : 0<v)
    (hC : ‖(1-hurwitzRayRatio (-1) v)⁻¹‖≤C) :
    ‖(hurwitzRay b (-1) v)^(-s)*hurwitzRayRatio (-1) v/(1-hurwitzRayRatio (-1) v)‖ ≤
      C*b^(-s.re)*(Real.exp (-(s.im/(3*b))*v)+Real.exp (-(s.im/3))*Real.exp (-2*Real.pi*v)) := by
  let z := hurwitzRay b (-1) v
  have hr : 0<z.re := by simp [z];linarith
  have hn : z≠0 := by intro he;simpa [he] using hr
  have hbase := Real.rpow_le_rpow_of_nonpos hb (show b≤‖z‖ from (by simp [z];linarith : b≤z.re).trans (Complex.re_le_norm z)) (neg_nonpos.mpr hσ)
  have hnorm : ‖z^(-s)‖=‖z‖^(-s.re)*Real.exp (z.arg*s.im) := by
    rw [Complex.norm_cpow_of_ne_zero hn,neg_re,neg_im,mul_neg,Real.exp_neg,div_inv_eq_mul]
  have harg := lower_ray_arg hb hv
  change z.arg≤_ at harg
  have hexp : Real.exp (z.arg*s.im)*Real.exp (-2*Real.pi*v) ≤
      Real.exp (-(s.im/(3*b))*v)+Real.exp (-(s.im/3))*Real.exp (-2*Real.pi*v) := by
    by_cases h : v≤b
    · apply le_trans _ (le_add_of_nonneg_right (by positivity))
      have ha : z.arg≤ -v/(3*b) := harg.trans (by rw [neg_div,neg_div];apply neg_le_neg;exact div_le_div_of_nonneg_left hv.le (by positivity) (by linarith))
      rw [←Real.exp_add];apply Real.exp_le_exp.mpr
      have H := mul_le_mul_of_nonneg_right ha ht.le
      calc _ ≤ (-v/(3*b))*s.im := by nlinarith [mul_pos Real.pi_pos hv]
           _ = _ := by ring
    · apply le_trans _ (le_add_of_nonneg_left (by positivity))
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      have ha : z.arg≤ -(1/3) := harg.trans (by apply (div_le_iff₀ (by positivity)).mpr;linarith)
      nlinarith [mul_le_mul_of_nonneg_right ha ht.le]
  change ‖z^(-s)*hurwitzRayRatio (-1) v/(1-hurwitzRayRatio (-1) v)‖≤_
  rw [div_eq_mul_inv,norm_mul,norm_mul,hnorm,norm_hurwitzRayRatio]
  calc
    _ = ‖(1-hurwitzRayRatio (-1) v)⁻¹‖*‖z‖^(-s.re)*(Real.exp (z.arg*s.im)*Real.exp (-2*Real.pi*v)) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul hC hbase (Real.rpow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hC)) hexp (by positivity) (mul_nonneg ((norm_nonneg _).trans hC) (Real.rpow_nonneg hb.le _))

/-- Uniform bound for the combined negative-frequency tail. On the
balanced contour b≈√t the additional factor b/t saves a square root. -/
theorem norm_hurwitzGeometricTail_negative : ∃ C : ℝ,0<C ∧ ∀ {s : ℂ} {b : ℝ},
    0≤s.re → 0<s.im → 1≤b →
    ‖hurwitzGeometricTail s b (-1) 0‖≤C*b^(-s.re)*b/s.im := by
  obtain ⟨C,hC,hB⟩ := hurwitzRayRatio_inv_bound (-1)
  refine ⟨12*C,by positivity,?_⟩
  intro s b hσ ht hb
  have hb' : 0<b := by linarith
  let A := C*b^(-s.re)
  let F (v : ℝ) := (hurwitzRay b (-1) v)^(-s)*hurwitzRayRatio (-1) v/(1-hurwitzRayRatio (-1) v)
  let g (v : ℝ) := A*(Real.exp (-(s.im/(3*b))*v)+Real.exp (-(s.im/3))*Real.exp (-2*Real.pi*v))
  have hg : IntegrableOn g (Ioi 0) := by
    apply Integrable.const_mul
    apply Integrable.add (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0)
    exact (integrableOn_exp_mul_Ioi (show -2*Real.pi<0 by linarith [Real.pi_pos]) 0).const_mul _
  have hdom : ∀ᵐ v ∂volume.restrict (Ioi 0), ‖F v‖≤g v :=
    (ae_restrict_mem measurableSet_Ioi).mono fun v hv => norm_lower_integrand hσ ht hb' hv (hB v hv.le)
  have hmeas : AEStronglyMeasurable F (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.div _ _ (fun v _ => sub_ne_zero.mpr (hurwitzRayRatio_ne_one _ _).symm)
    · apply ContinuousOn.mul _ (by unfold hurwitzRayRatio;fun_prop)
      apply ContinuousOn.cpow_const (by unfold hurwitzRay;fun_prop)
      intro v hv;left;rw [hurwitzRay_re];linarith [mem_Ioi.mp hv]
    · unfold hurwitzRayRatio;fun_prop
  have hf := hg.mono' hmeas hdom
  have hi := (norm_integral_le_integral_norm F (μ:=volume.restrict (Ioi 0))).trans (integral_mono_ae hf.norm hg hdom)
  have hG : (∫ v in Ioi (0:ℝ),g v)=A*(3*b/s.im+Real.exp (-(s.im/3))/(2*Real.pi)) := by
    dsimp only [g];rw [integral_const_mul,integral_add (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0)
      ((integrableOn_exp_mul_Ioi (show -2*Real.pi<0 by linarith [Real.pi_pos]) 0).const_mul _),
      integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)),integral_exp_mul_Ioi (show -2*Real.pi<0 by linarith [Real.pi_pos])]
    simp only [mul_zero,Real.exp_zero];field_simp
  have hE : Real.exp (-(s.im/3))≤3/s.im := by
    rw [Real.exp_neg,show 3/s.im=(s.im/3)⁻¹ by ring];apply (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr
    linarith [Real.add_one_le_exp (s.im/3)]
  have hE' : Real.exp (-(s.im/3))/(2*Real.pi)≤3*b/s.im :=
    (div_le_self (Real.exp_nonneg _) (by linarith [Real.pi_gt_three])).trans (hE.trans (div_le_div_of_nonneg_right (by linarith) ht.le))
  rw [hG] at hi
  have hn : ‖(1:ℂ)+((-1:ℝ):ℂ)*I‖≤2 := ((norm_add_le _ _).trans (by norm_num))
  rw [hurwitzGeometricTail,norm_mul];simp only [zero_add,pow_one]
  apply (mul_le_mul hn hi (norm_nonneg _) (by norm_num)).trans
  dsimp [A]
  calc
    _ ≤ 2*(C*b^(-s.re)*(3*b/s.im+3*b/s.im)) := by gcongr
    _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
