import AnalyticNumberTheory.ModularAndPartitions.DedekindLogEta

/-!
# The additive eta transformation factor

The arguments of the geometric factors lie in a right half-plane.
This fixes the logarithmic cocycle, including its exact quarter turn.
-/

open Complex Real Set Matrix
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

/-- The real Dedekind phase for positive lower-left entry. -/
noncomputable def etaLogPhase (γ : SL(2,ℤ)) : ℝ :=
  ((γ 0 0:ℝ)+γ 1 1)/(12*(γ 1 0:ℝ))-dedekindSum (γ 1 1) (γ 1 0).natAbs

/-- Additive logarithmic factor in the positive lower-left case. -/
noncomputable def etaLogFactor (γ : SL(2,ℤ)) (z : ℍ) : ℂ :=
  π*I*(etaLogPhase γ:ℂ)+Complex.log (-I*((γ 1 0:ℂ)*(z:ℂ)+γ 1 1))/2

private theorem entries_T (γ : SL(2,ℤ)) (q : ℤ) :
    (γ*ModularGroup.T^q) 0 0=γ 0 0 ∧ (γ*ModularGroup.T^q) 1 0=γ 1 0 ∧
    (γ*ModularGroup.T^q) 1 1=γ 1 0*q+γ 1 1 := by
  simp [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_T_zpow]

private theorem entries_S (γ : SL(2,ℤ)) :
    (γ*ModularGroup.S) 0 0=γ 0 1 ∧ (γ*ModularGroup.S) 1 0=γ 1 1 ∧ (γ*ModularGroup.S) 1 1= -γ 1 0 := by
  simp [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_S]

theorem etaLogPhase_mul_T (γ : SL(2,ℤ)) (hc : 0<γ 1 0) (q : ℤ) :
    etaLogPhase (γ*ModularGroup.T^q)=etaLogPhase γ+q/12 := by
  obtain ⟨ha,hc',hd⟩ := entries_T γ q
  have hs : dedekindSum (γ 1 0*q+γ 1 1) (γ 1 0).natAbs=dedekindSum (γ 1 1) (γ 1 0).natAbs := by
    convert dedekindSum_add_int (γ 1 1) q (γ 1 0).natAbs using 2
    rw [Int.natAbs_of_nonneg hc.le]; ring
  simp only [etaLogPhase,ha,hc',hd,hs]; push_cast
  have hcr : (γ 1 0:ℝ)≠0 := by exact_mod_cast hc.ne'
  field_simp; ring

theorem etaLogPhase_mul_S (γ : SL(2,ℤ)) (hc : 0<γ 1 0) (hd : 0<γ 1 1) :
    etaLogPhase (γ*ModularGroup.S)+1/4=etaLogPhase γ := by
  obtain ⟨ha,hc',hd'⟩ := entries_S γ
  have hrec := dedekind_reciprocity_int hc hd (Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_row 1))
  have hdet : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by rw [←Matrix.det_fin_two]; exact γ.2
  have hdetR : (γ 0 0:ℝ)*γ 1 1-(γ 0 1:ℝ)*γ 1 0=1 := by exact_mod_cast hdet
  have hcr : (γ 1 0:ℝ)≠0 := by exact_mod_cast hc.ne'
  have hdr : (γ 1 1:ℝ)≠0 := by exact_mod_cast hd.ne'
  simp only [etaLogPhase,ha,hc',hd',Int.cast_neg,dedekindSum_neg,sub_neg_eq_add]
  field_simp; nlinarith only [hrec,hdetR]

theorem etaLogFactor_mul_T (γ : SL(2,ℤ)) (hc : 0<γ 1 0) (q : ℤ) (z : ℍ) :
    etaLogFactor (γ*ModularGroup.T^q) z=etaLogFactor γ (ModularGroup.T^q • z)+(q:ℂ)*π*I/12 := by
  obtain ⟨_,h₁,h₂⟩ := entries_T γ q
  have hz : (((ModularGroup.T^q) • z : ℍ):ℂ)=(z:ℂ)+q := by
    rw [UpperHalfPlane.modular_T_zpow_smul,UpperHalfPlane.coe_vadd,Complex.ofReal_intCast,add_comm]
  simp only [etaLogFactor,etaLogPhase_mul_T γ hc,h₁,h₂,hz]; push_cast; ring_nf

private theorem log_quarter_turn {u v w : ℂ} (hu : 0<u.re) (hv : 0<v.re) (hw : 0<w.re) (h : u*v=I*w) :
    Complex.log u+Complex.log v=π*I/2+Complex.log w := by
  have argBound (x : ℂ) (hx : 0<x.re) := abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hx))
  have H₁ := argBound u hu; have H₂ := argBound v hv; have H₃ := argBound w hw
  have ne (x : ℂ) (hx : 0<x.re) : x≠0 := by rintro rfl; simp at hx
  rw [←Complex.log_mul (ne u hu) (ne v hv) ⟨by linarith,by linarith⟩,h,
    Complex.log_mul Complex.I_ne_zero (ne w hw) ⟨by rw [Complex.arg_I]; linarith [Real.pi_pos],
      by rw [Complex.arg_I]; linarith [Real.pi_pos]⟩,Complex.log_I]
  ring

/-- Exact logarithmic cocycle for the inversion step of Euclid's algorithm. -/
theorem etaLogFactor_mul_S (γ : SL(2,ℤ)) (hc : 0<γ 1 0) (hd : 0<γ 1 1) (z : ℍ) :
    etaLogFactor (γ*ModularGroup.S) (ModularGroup.S • z)+Complex.log (-I*(z:ℂ))/2=etaLogFactor γ z := by
  obtain ⟨_,h₁,h₂⟩ := entries_S γ
  let u : ℂ := -I*((γ 1 1:ℂ)*(↑(ModularGroup.S • z : ℍ):ℂ)+(- (γ 1 0:ℂ)))
  let v : ℂ := -I*(z:ℂ)
  let w : ℂ := -I*((γ 1 0:ℂ)*(z:ℂ)+γ 1 1)
  have hu : 0<u.re := by
    dsimp [u]; simpa [Complex.mul_re] using mul_pos (Int.cast_pos.mpr hd : 0<(γ 1 1:ℝ)) (ModularGroup.S • z).im_pos
  have hv : 0<v.re := neg_I_mul_re_pos z
  have hw : 0<w.re := by
    simpa [w,Complex.mul_re] using mul_pos (Int.cast_pos.mpr hc : 0<(γ 1 0:ℝ)) z.im_pos
  have he : u*v=I*w := by
    dsimp only [u,v,w]; rw [UpperHalfPlane.modular_S_smul,UpperHalfPlane.coe_mk,inv_neg]
    field_simp [z.ne_zero]; ring_nf
  have hlog := log_quarter_turn hu hv hw he
  have hp : (etaLogPhase (γ*ModularGroup.S):ℂ)+1/4=etaLogPhase γ := by
    simpa using congrArg Complex.ofReal (etaLogPhase_mul_S γ hc hd)
  simp only [etaLogFactor,h₁,h₂,Int.cast_neg]
  change π*I*(etaLogPhase (γ*ModularGroup.S):ℂ)+Complex.log u/2+Complex.log v/2=π*I*(etaLogPhase γ:ℂ)+Complex.log w/2
  linear_combination (1/2:ℂ)*hlog + (π:ℂ)*I*hp

end AnalyticNumberTheory.ModularAndPartitions
