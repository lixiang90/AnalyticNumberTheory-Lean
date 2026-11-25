import AnalyticNumberTheory.ModularAndPartitions.DedekindLogTransformation
import AnalyticNumberTheory.ModularAndPartitions.EisensteinConeContinuation
import AnalyticNumberTheory.ModularAndPartitions.EisensteinTiltedContour

/-!
# The modular correction at weight zero

The logarithmic eta transformation evaluates the removable value of
the continued cone sum at weight zero, including its Dedekind term.
-/

open Complex Real Set Filter UpperHalfPlane
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

private theorem gammaInv_deriv_zero : HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹) 1 0 := by
  have he (s : ℂ) : (Complex.Gamma s)⁻¹=s*(Complex.Gamma (s+1))⁻¹ := by
    rcases eq_or_ne s 0 with rfl|hs
    · simp
    · rw [Complex.Gamma_add_one s hs,mul_inv_rev]; field_simp
  rw [show (fun s : ℂ => (Complex.Gamma s)⁻¹)=(fun s : ℂ => s*(Complex.Gamma (s+1))⁻¹) by funext s; exact he s]
  have h : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s+1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  simpa using (hasDerivAt_id (0:ℂ)).fun_mul (h 0).hasDerivAt

/-- The continued Eisenstein series is constant in the upper
half-plane at weight zero. -/
theorem eisensteinG_zero (z : ℂ) : eisensteinG z 0= -1 := by
  simp [eisensteinG,eisensteinConstant,Function.update_of_ne (by norm_num : (0:ℂ)≠1),
    eisensteinReflection,riemannZeta_zero]; ring

private theorem eisensteinG_deriv_zero (z : ℍ) : HasDerivAt (eisensteinG z)
    (deriv eisensteinConstant 0+2*eisensteinLambert (eisensteinNome z) 0) 0 := by
  let B (s : ℂ) := (1+eisensteinReflection s)*(-2*π*Complex.I)^s*eisensteinLambert (eisensteinNome z) s
  have hN : -2*(π:ℂ)*Complex.I≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hB : Differentiable ℂ B := by
    apply Differentiable.mul _ (differentiable_eisensteinLambert_weight (norm_eisensteinNome_lt_one z.im_pos))
    exact (show Differentiable ℂ (fun s : ℂ => 1+eisensteinReflection s) by unfold eisensteinReflection; fun_prop).mul
      (differentiable_id.const_cpow (Or.inl hN))
  have he : eisensteinG z=fun s => eisensteinConstant s+B s*(Complex.Gamma s)⁻¹ := by
    funext s; simp only [eisensteinG,B]; ring
  rw [he]
  have H := (differentiable_eisensteinConstant 0).hasDerivAt.fun_add ((hB 0).hasDerivAt.fun_mul gammaInv_deriv_zero)
  apply H.congr_deriv
  simp [B,eisensteinReflection] <;> ring <;> simp

private theorem period_deriv_eta (γ : SL(2,ℤ)) (z : ℍ) : HasDerivAt (eisensteinPeriod γ z)
    (Complex.log (denom γ z)+2*(eisensteinLambert (eisensteinNome (γ • z : ℍ)) 0-
      eisensteinLambert (eisensteinNome z) 0)) 0 := by
  have hd := ((hasDerivAt_id (0:ℂ)).neg).const_cpow (Or.inl (denom_ne_zero (γ : GL (Fin 2) ℝ) z))
  have H := (hd.fun_mul (eisensteinG_deriv_zero (γ • z))).fun_sub (eisensteinG_deriv_zero z)
  apply H.congr_deriv; simp [eisensteinG_zero]; ring

private theorem log_denom_right (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    Complex.log (-Complex.I*denom γ z)=Complex.log (denom γ z)-π*Complex.I/2 := by
  have hj : 0<(denom γ z).im := by simpa [denom,Complex.mul_im] using mul_pos (Int.cast_pos.mpr hc : 0<(γ 1 0:ℝ)) z.im_pos
  have harg : 0≤(denom γ z).arg := Complex.arg_nonneg_iff.mpr hj.le
  rw [Complex.log_mul (neg_ne_zero.mpr Complex.I_ne_zero) (denom_ne_zero (γ : GL (Fin 2) ℝ) z)
    ⟨by rw [Complex.arg_neg_I]; linarith [Real.pi_pos],
      by rw [Complex.arg_neg_I]; linarith [Complex.arg_le_pi (denom γ z),Real.pi_pos]⟩]
  rw [Complex.log_neg_I]; ring

/-- Derivative of the entire period at weight zero, in terms of the
real Dedekind phase and the modular action. -/
theorem eisensteinPeriod_hasDerivAt_zero (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    HasDerivAt (eisensteinPeriod γ z) ((π:ℂ)*Complex.I*
      ((((γ • z : ℍ):ℂ)-(z:ℂ))/6-2*(etaLogPhase γ:ℂ)+1/2)) 0 := by
  apply (period_deriv_eta γ z).congr_deriv
  have h := dedekindLogEta_SL2Z_of_pos γ hc z
  simp only [dedekindLogEta,etaLogFactor] at h
  have hj : denom γ z=(γ 1 0:ℂ)*(z:ℂ)+γ 1 1 := rfl
  rw [←hj,log_denom_right γ z hc] at h
  linear_combination -2*h

/-- The value at the removable weight-zero singularity of the cone
quotient is expressed by the eta phase and the modular displacement. -/
theorem eisensteinConeContinuation_limit_zero (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    Tendsto (eisensteinConeContinuation γ z) (𝓝[≠] 0)
      (𝓝 ((etaLogPhase γ:ℂ)-(((γ • z : ℍ):ℂ)-(z:ℂ))/12-1/4)) := by
  have h₁ := (eisensteinPeriod_hasDerivAt_zero γ z hc).tendsto_slope
  have hW : HasDerivAt eisensteinWinding (-2*(π:ℂ)*Complex.I) 0 := by
    have H := (((hasDerivAt_id (0:ℂ)).const_mul (-(π:ℂ)*Complex.I)).cexp.fun_sub
      (((hasDerivAt_id (0:ℂ)).const_mul ((π:ℂ)*Complex.I)).cexp))
    apply H.congr_deriv; simp; ring
  have hn : -2*(π:ℂ)*Complex.I≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have H := h₁.div hW.tendsto_slope hn
  have hP : eisensteinPeriod γ z 0=0 := by simp [eisensteinPeriod,eisensteinG_zero]
  have hW₀ : eisensteinWinding 0=0 := by simp [eisensteinWinding]
  have hval : (π:ℂ)*Complex.I*((((γ • z : ℍ):ℂ)-(z:ℂ))/6-2*(etaLogPhase γ:ℂ)+1/2)/
      (-2*(π:ℂ)*Complex.I)=(etaLogPhase γ:ℂ)-(((γ • z : ℍ):ℂ)-(z:ℂ))/12-1/4 := by
    field_simp [Real.pi_ne_zero,Complex.I_ne_zero]; ring
  rw [←hval]
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s≠0 := hs
  simp only [slope_def_field,Pi.div_apply,hP,hW₀,sub_zero,eisensteinConeContinuation]
  rw [div_div_div_cancel_right₀ hs']


/-- Closed form of the finite part at zero in terms of the modular
denominator and the classical Dedekind sum. -/
theorem eisensteinConeContinuation_limit_zero_dedekind (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    Tendsto (eisensteinConeContinuation γ z) (𝓝[≠] 0)
      (𝓝 ((denom γ z+(denom γ z)⁻¹)/(12*(γ 1 0:ℂ))-
        (dedekindSum (γ 1 1) (γ 1 0).natAbs:ℂ)-1/4)) := by
  have he := eisensteinConeContinuation_limit_zero γ z hc
  convert he using 2
  let A : ℂ := γ 0 0; let B : ℂ := γ 0 1; let C : ℂ := γ 1 0; let D : ℂ := γ 1 1
  let j := denom γ z
  have hj : j≠0 := denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have hC : C≠0 := Int.cast_ne_zero.mpr hc.ne'
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by rw [←Matrix.det_fin_two]; exact γ.2
  have hdet : A*D-B*C=1 := by dsimp [A,B,C,D]; exact_mod_cast hd
  have hjdef : j=C*(z:ℂ)+D := rfl
  have hgeo : ((γ • z : ℍ):ℂ)=(A*(z:ℂ)+B)/j := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; rfl
  simp only [etaLogPhase,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul,
    Complex.ofReal_intCast,Complex.ofReal_ofNat]
  rw [hgeo]
  change (j+j⁻¹)/(12*C)-_-1/4=((A+D)/(12*C)-_)-((A*(z:ℂ)+B)/j-(z:ℂ))/12-1/4
  field_simp [hC,hj]
  rw [hjdef] at *
  linear_combination -4*hdet


/-- Evaluation of the sum of Hankel contours at zero. At this weight
the integrals on the two infinite sides cancel, leaving the circular residues. -/
theorem eisensteinHankel_zero (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    let c := (γ 1 0).toNat
    let b : ℂ := (c:ℂ)*z+γ 1 1
    let ω := eisensteinRay b
    ∃ X : ℝ, (∀ j : Fin c, AnalyticTools.TiltedBarnesRadius (eisensteinBarnesOffset c (γ 1 1) z j) b ω X) ∧
      (∑ j : Fin c,AnalyticTools.tiltedBarnesHankel (eisensteinBarnesOffset c (γ 1 1) z j) b ω X 0)=
        2*π*Complex.I*((denom γ z+(denom γ z)⁻¹)/(12*(γ 1 0:ℂ))-
          (dedekindSum (γ 1 1) (γ 1 0).natAbs:ℂ)-1/4) := by
  obtain ⟨X,hR,hD,H⟩ := eisensteinPeriod_eq_tiltedHankel_with_radius γ z hc
  refine ⟨X,hR,?_⟩
  let c := (γ 1 0).toNat
  let b : ℂ := (c:ℂ)*z+γ 1 1
  let ω := eisensteinRay b
  let Z (s : ℂ) := ∑ j : Fin c,AnalyticTools.tiltedBarnesHankel (eisensteinBarnesOffset c (γ 1 1) z j) b ω X s
  let D (s : ℂ) := -Complex.exp (-π*Complex.I*s)*ω^s*Z s
  have hω : ω≠0 := by
    have h : ω.re=1 := by simp [ω,eisensteinRay]
    rintro e; rw [e] at h; norm_num at h
  have hZ : Differentiable ℂ Z := Differentiable.fun_sum (fun j _ => hD j)
  have hDD : Differentiable ℂ D := by
    exact ((show Differentiable ℂ (fun s : ℂ => -Complex.exp (-π*Complex.I*s)) by fun_prop).mul
      (differentiable_id.const_cpow (Or.inl hω))).mul hZ
  have he : (fun s : ℂ => D s*(Complex.Gamma s)⁻¹)=eisensteinPeriod γ z := by
    funext s; rw [H s]
    change -Complex.exp (-π*Complex.I*s)*ω^s*Z s*(Complex.Gamma s)⁻¹=
      -Complex.exp (-π*Complex.I*s)*(Complex.Gamma s)⁻¹*ω^s*Z s
    ring
  have h := (hDD 0).hasDerivAt.fun_mul gammaInv_deriv_zero
  rw [he] at h
  have hp := (eisensteinPeriod_hasDerivAt_zero γ z hc).unique h
  simp only [D,mul_zero,Complex.exp_zero,Complex.Gamma_zero,inv_zero,zero_mul,
    Complex.cpow_zero,one_mul,neg_one_mul,mul_one,add_zero,zero_add] at hp
  have hv := tendsto_nhds_unique (eisensteinConeContinuation_limit_zero γ z hc)
    (eisensteinConeContinuation_limit_zero_dedekind γ z hc)
  rw [←hv]
  change Z 0=_
  linear_combination hp

end AnalyticNumberTheory.ModularAndPartitions
