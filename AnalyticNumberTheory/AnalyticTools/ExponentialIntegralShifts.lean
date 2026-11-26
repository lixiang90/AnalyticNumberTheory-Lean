import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralAsymptotic
import AnalyticNumberTheory.AnalyticTools.ShiftedIntegratedPoles

/-! # Integrating shifted residues on a horizontal ray -/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private theorem shifted_real_part (z : ℂ) (u y : ℝ) :
    ((z-(y:ℂ))*(u:ℂ)).re = (z.re-y)*u := by simp

private theorem shifted_imaginary_part (z : ℂ) (u y : ℝ) :
    ((z-(y:ℂ))*(u:ℂ)).im = z.im*u := by simp

private theorem away_from_shift_ray {z : ℂ} (hz : -z ∈ slitPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 ≤ y → δ ≤ ‖z-y‖ := by
  rcases mem_slitPlane_iff.mp hz with hr | hi
  · have h : z.re < 0 := by simpa using hr
    refine ⟨-z.re,neg_pos.mpr h,fun y hy => ?_⟩
    apply le_trans _ (abs_re_le_norm (z-y))
    rw [Complex.sub_re,Complex.ofReal_re,abs_of_neg (by linarith)]
    linarith
  · have h : z.im ≠ 0 := by simpa using hi
    exact ⟨|z.im|,abs_pos.mpr h,fun y _ => by simpa using abs_im_le_norm (z-y)⟩

/-- A pole off the nonnegative real ray has an integrable residue as the shift runs to infinity. -/
theorem integrableOn_shiftedPoleResidue {z : ℂ} (hz : -z ∈ slitPlane) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun y : ℝ => shiftedPoleResidue z y u) (Ioi 0) := by
  obtain ⟨δ,hδ,H⟩ := away_from_shift_ray hz
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hu) 0).const_mul (Real.exp (z.re*u)/δ)).mono'
    ((show Measurable (fun y : ℝ => shiftedPoleResidue z y u) by unfold shiftedPoleResidue; fun_prop).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  rw [shiftedPoleResidue,norm_div,Complex.norm_exp,shifted_real_part,sub_mul,Real.exp_sub]
  calc
    _ ≤ (Real.exp (z.re*u)/Real.exp (y*u))/δ :=
      div_le_div_of_nonneg_left (by positivity) hδ (H y hy.le)
    _ = _ := by rw [neg_mul,Real.exp_neg,mul_comm u y]; ring

/-- The integral of the shifted residue is the horizontal branch of Ei, normalized
to zero at the negative end of each horizontal ray. -/
theorem integral_Ioi_shiftedPoleResidue {z : ℂ} (hz : -z ∈ slitPlane) {u : ℝ} (hu : 0 < u) :
    (∫ y in Ioi (0:ℝ), shiftedPoleResidue z y u) = leftExponentialIntegral (z*u) := by
  let F (y : ℝ) := -leftExponentialIntegral ((z-(y:ℂ))*u)
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt F (shiftedPoleResidue z y u) y := by
    have hs : -((z-(y:ℂ))*(u:ℂ)) ∈ slitPlane := by
      rcases mem_slitPlane_iff.mp hz with h | h
      · apply mem_slitPlane_iff.mpr ∘ Or.inl
        rw [Complex.neg_re,shifted_real_part,neg_pos]
        exact mul_neg_of_neg_of_pos (by simp only [Complex.neg_re,neg_pos] at h; linarith) hu
      · apply mem_slitPlane_iff.mpr ∘ Or.inr
        simp only [Complex.neg_im,shifted_imaginary_part,neg_ne_zero] at h ⊢
        exact mul_ne_zero h hu.ne'
    have hl := (((hasDerivAt_id' (y:ℂ)).const_sub z).mul_const (u:ℂ))
    have hh := ((hasDerivAt_leftExponentialIntegral hs).comp (y:ℂ) hl).neg
    apply hh.comp_ofReal.congr_deriv
    have hden := neg_ne_zero.mp (slitPlane_ne_zero hs)
    dsimp [shiftedPoleResidue]
    field_simp [Complex.ofReal_ne_zero.mpr hu.ne', left_ne_zero_of_mul hden]
  have htop : Tendsto F atTop (𝓝 0) := by
    have hY : Tendsto (fun y : ℝ => (y-z.re)*u) atTop atTop := by
      simpa only [sub_eq_add_neg,id_eq] using (tendsto_atTop_add_const_right atTop (-z.re) tendsto_id).atTop_mul_const hu
    have h := (tendsto_leftExponentialIntegral_neg_add_im (z.im*u)).comp hY
    apply (by simpa using h.neg : Tendsto (fun y : ℝ =>
      -leftExponentialIntegral (-(((y-z.re)*u : ℝ):ℂ)+((z.im*u : ℝ):ℂ)*I)) atTop (𝓝 0)).congr
    intro y
    congr 2
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0:ℝ)) hd (integrableOn_shiftedPoleResidue hz hu) htop
  simpa [F] using h

/-- A uniform bound for the corrected residue of a nonreal pole. The shift dependence
is y exp(−uy), integrable for u>0, and the pole dependence has two powers of the ordinate. -/
theorem norm_shiftedPoleCorrection_le {z : ℂ} (hz : z.im ≠ 0) {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hb : z.re ≤ 1) :
    ‖shiftedPoleCorrection z y u‖ ≤ (Real.exp u * (z.im^2)⁻¹) * (y*Real.exp (-u*y)) := by
  have hd : z.im^2 ≤ ‖z‖*‖z-y‖ := by
    calc
      _ = |z.im| * |z.im| := by rw [←sq,sq_abs]
      _ ≤ _ := mul_le_mul (abs_im_le_norm z) (by simpa using abs_im_le_norm (z-y)) (abs_nonneg _) (norm_nonneg _)
  have he : Real.exp ((z.re-y)*u) ≤ Real.exp u*Real.exp (-u*y) := by
    rw [←Real.exp_add,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hb hu]
  rw [shiftedPoleCorrection,norm_div,norm_mul,norm_mul,Complex.norm_exp,shifted_real_part,Complex.norm_real,Real.norm_of_nonneg hy]
  apply (div_le_div₀ (mul_nonneg hy (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (mul_le_mul_of_nonneg_left he hy)
    (sq_pos_of_ne_zero hz) hd).trans_eq
  ring

/-- Integrating the corrected residue gives Ei with its leading exponential term removed. -/
theorem integral_Ioi_shiftedPoleCorrection {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) :
    (∫ y in Ioi (0:ℝ), shiftedPoleCorrection z y u) =
      leftExponentialIntegral (z*u) - Complex.exp (z*u)/(z*u) := by
  have hω : z ≠ 0 := fun he => hz (by simp [he])
  have hzy (y : ℝ) : z ≠ y := fun h => hz (by rw [h]; simp)
  have hs : -z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simpa using hz))
  have hE := integrableOn_exp_mul_complex_Ioi (a := -(u:ℂ)) (by simpa using hu) 0
  let c := Complex.exp (z*u)/z
  have he (y : ℝ) : shiftedPoleCorrection z y u =
      shiftedPoleResidue z y u - Complex.exp (-(u:ℂ)*y)*c := by
    rw [shiftedPoleResidue_eq_damped_add u hω (hzy y),show -(y:ℂ)*u = -(u:ℂ)*y by ring]
    dsimp only [c]
    ring
  simp_rw [he]
  rw [integral_sub (integrableOn_shiftedPoleResidue hs hu) (hE.mul_const c),
    integral_Ioi_shiftedPoleResidue hs hu,integral_mul_const,integral_exp_mul_complex_Ioi (by simpa using hu)]
  simp [c,div_eq_mul_inv,mul_comm,mul_assoc]

end AnalyticNumberTheory.AnalyticTools
