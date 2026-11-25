import AnalyticNumberTheory.ModularAndPartitions.DedekindLogCocycle

/-!
# Modular transformations of the canonical logarithm of eta

Euclid's algorithm on the bottom row of a unimodular matrix combines
translation and inversion. The additive cocycle retains the exact
integer phase in each matrix transformation.
-/

open Complex Real Matrix
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

private theorem zero_remainder (γ : SL(2,ℤ)) (hc : 0<γ 1 0) (hd : γ 1 1=0) (z : ℍ) :
    dedekindLogEta (γ • z)=dedekindLogEta z+etaLogFactor γ z := by
  have det : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by rw [←Matrix.det_fin_two]; exact γ.2
  rw [hd,mul_zero,zero_sub] at det
  have hc' : γ 1 0=1 := by
    have hdvd : γ 1 0∣1 := ⟨-γ 0 1,by linarith⟩
    have := Int.le_of_dvd one_pos hdvd; omega
  have hb : γ 0 1= -1 := by rw [hc',mul_one] at det; omega
  have hγ : γ=ModularGroup.T^(γ 0 0)*ModularGroup.S := by
    ext i j
    have H : ((ModularGroup.T^(γ 0 0)*ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j=
        (ModularGroup.T^(γ 0 0) : SL(2,ℤ)) i 0*ModularGroup.S 0 j+
        (ModularGroup.T^(γ 0 0) : SL(2,ℤ)) i 1*ModularGroup.S 1 j := by
      rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    change (γ : Matrix (Fin 2) (Fin 2) ℤ) i j=_
    rw [H,ModularGroup.coe_T_zpow,ModularGroup.coe_S]
    fin_cases i <;> fin_cases j <;> simp [hc',hb,hd]
  conv_lhs => rw [hγ,mul_smul,dedekindLogEta_T_zpow,dedekindLogEta_S]
  simp [etaLogFactor,etaLogPhase,hc',hd,dedekindSum_one_right]; ring

private theorem positive_log_transform (k : ℕ) : ∀ γ : SL(2,ℤ), γ 1 0=(k:ℤ) → 0<γ 1 0 →
    ∀ z : ℍ, dedekindLogEta (γ • z)=dedekindLogEta z+etaLogFactor γ z := by
  induction k using Nat.strong_induction_on with
  | ind k IH =>
    intro γ hk hc z
    let q : ℤ := γ 1 1/γ 1 0
    let r : ℤ := γ 1 1%γ 1 0
    let A := γ*ModularGroup.T^(-q)
    have hr : 0≤r := Int.emod_nonneg _ hc.ne'
    have hr' : r<γ 1 0 := Int.emod_lt_of_pos _ hc
    have he : γ 1 0*q+r=γ 1 1 := Int.mul_ediv_add_emod _ _
    have hAc : A 1 0=γ 1 0 := by simp [A,SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_T_zpow]
    have hAd : A 1 1=r := by
      simp [A,SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_T_zpow]; linarith
    have hA : ∀ w : ℍ,dedekindLogEta (A • w)=dedekindLogEta w+etaLogFactor A w := by
      intro w
      rcases hr.eq_or_lt with h₀|hrpos
      · exact zero_remainder A (hAc ▸ hc) (hAd.trans h₀.symm) w
      let B := A*ModularGroup.S
      have hBc : B 1 0=r := by simp [B,SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_S,hAd]
      have hB := IH r.toNat (by omega) B (hBc.trans (Int.toNat_of_nonneg hr).symm) (hBc ▸ hrpos) (ModularGroup.S • w)
      have hs : B • (ModularGroup.S • w)=A • w := by
        rw [←mul_smul]; dsimp only [B]
        rw [mul_assoc,ModularGroup.S_mul_S_eq,mul_neg_one,ModularGroup.SL_neg_smul]
      rw [hs,dedekindLogEta_S] at hB
      have hC := etaLogFactor_mul_S A (hAc ▸ hc) (hAd ▸ hrpos) w
      dsimp only [B] at hB; linear_combination hB + hC
    have hγ : A*ModularGroup.T^q=γ := by
      dsimp only [A]; rw [mul_assoc,←_root_.zpow_add,neg_add_cancel,zpow_zero,mul_one]
    rw [←hγ,mul_smul,hA,dedekindLogEta_T_zpow,etaLogFactor_mul_T A (hAc ▸ hc)]
    ring

/-- Exact logarithmic eta transformation at every positive lower-left entry. -/
theorem dedekindLogEta_SL2Z_of_pos (γ : SL(2,ℤ)) (hc : 0<γ 1 0) (z : ℍ) :
    dedekindLogEta (γ • z)=dedekindLogEta z+etaLogFactor γ z :=
  positive_log_transform _ γ (Int.toNat_of_nonneg hc.le).symm hc z

/-- The negative lower-left entry uses the opposite imaginary unit in
the logarithm to keep its argument in the right half-plane. -/
theorem dedekindLogEta_SL2Z_of_neg (γ : SL(2,ℤ)) (hc : γ 1 0<0) (z : ℍ) :
    dedekindLogEta (γ • z)=dedekindLogEta z+
      π*I*((((γ 0 0:ℝ)+γ 1 1)/(12*(γ 1 0:ℝ))+dedekindSum (γ 1 1) (γ 1 0).natAbs:ℝ):ℂ)+
      Complex.log (I*((γ 1 0:ℂ)*(z:ℂ)+γ 1 1))/2 := by
  have hn : 0<(-γ) 1 0 := by change 0< -γ 1 0; omega
  have H := dedekindLogEta_SL2Z_of_pos (-γ) hn z
  rw [ModularGroup.SL_neg_smul] at H
  have hneg (i j : Fin 2) : (-γ) i j= -γ i j := rfl
  simp only [etaLogFactor,etaLogPhase,hneg,Int.natAbs_neg,dedekindSum_neg,Int.cast_neg,sub_neg_eq_add] at H
  rw [H]
  have hp : ((-(γ 0 0:ℝ)+ -(γ 1 1:ℝ))/(12* -(γ 1 0:ℝ)))=((γ 0 0:ℝ)+γ 1 1)/(12*(γ 1 0:ℝ)) := by ring
  rw [hp,show -I*(-(γ 1 0:ℂ)*(z:ℂ)+ -(γ 1 1:ℂ))=I*((γ 1 0:ℂ)*(z:ℂ)+γ 1 1) by ring]
  ring

/-- Upper triangular matrices act by an integral translation. -/
theorem dedekindLogEta_SL2Z_of_zero (γ : SL(2,ℤ)) (hc : γ 1 0=0) (z : ℍ) :
    dedekindLogEta (γ • z)=dedekindLogEta z+((γ 0 0*γ 0 1:ℤ):ℂ)*π*I/12 := by
  have det : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by rw [←Matrix.det_fin_two]; exact γ.2
  rw [hc,mul_zero,sub_zero] at det
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp det with ⟨ha,hd⟩|⟨ha,hd⟩
  · have h : γ=ModularGroup.T^(γ 0 1) := by
      ext i j; rw [ModularGroup.coe_T_zpow]; fin_cases i <;> fin_cases j <;> simp [ha,hc,hd]
    conv_lhs => rw [h,dedekindLogEta_T_zpow]
    rw [ha,one_mul]
  · have h : -γ=ModularGroup.T^(-γ 0 1) := by
      ext i j; rw [ModularGroup.coe_T_zpow]; fin_cases i <;> fin_cases j <;> simp [ha,hc,hd]
    rw [←ModularGroup.SL_neg_smul,h,dedekindLogEta_T_zpow,ha,neg_one_mul]

end AnalyticNumberTheory.ModularAndPartitions
