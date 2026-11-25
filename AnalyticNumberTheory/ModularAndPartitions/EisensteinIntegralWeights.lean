import AnalyticNumberTheory.ModularAndPartitions.EisensteinContinuation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Integral weights of the continued Eisenstein series

Weight two has an additive correction under the full modular group.
At integral weights at least three the usual homogeneous law holds.
-/

open Complex Real ModularForm EisensteinSeries SlashInvariantForm
open UpperHalfPlane hiding I
open scoped UpperHalfPlane MatrixGroups Topology
namespace AnalyticNumberTheory.ModularAndPartitions

/-- Reflection at an integral weight. -/
theorem eisensteinReflection_nat (k : ℕ) : eisensteinReflection k=(-1:ℂ)^k := by
  rw [eisensteinReflection,mul_comm _ (k:ℂ),Complex.exp_nat_mul,Complex.exp_pi_mul_I]

/-- The continued family at weight two coincides with the classical
Eisenstein-ordered series `G₂`. -/
theorem eisensteinG_two (z : ℍ) : eisensteinG z 2=G2 z := by
  have he : eisensteinReflection 2=1 := by simpa using eisensteinReflection_nat 2
  have hLam := eisensteinLambert_nat_succ (norm_eisensteinNome_lt_one z.im_pos) 1
  norm_num only [Nat.cast_one,one_add_one_eq_two] at hLam
  have hGamma : Complex.Gamma 2=1 := by simpa using Complex.Gamma_nat_eq_factorial 1
  rw [eisensteinG,eisensteinConstant,Function.update_of_ne (by norm_num : (2:ℂ)≠1),
    he,hLam,G2_eq_tsum_cexp,hGamma,inv_one,mul_one]
  rw [show (-2*(π:ℂ)*I)^(2:ℂ)=(-2*(π:ℂ)*I)^2 by simp]
  change _=2*riemannZeta 2-8*(π:ℂ)^2*∑' n : ℕ+,(ArithmeticFunction.sigma 1 (n:ℕ):ℂ)*eisensteinNome z^(n:ℕ)
  rw [mul_pow,Complex.I_sq]; ring

/-- The weight-two correction for all unimodular substitutions. -/
theorem eisensteinG_two_modular (γ : SL(2,ℤ)) (z : ℍ) :
    eisensteinG ((γ • z : ℍ):ℂ) 2 =
      (denom γ z)^2*eisensteinG z 2-2*π*I*(γ 1 0:ℂ)*(denom γ z) := by
  rw [eisensteinG_two,eisensteinG_two]
  have H := congrFun (G2_slash_action γ) z
  rw [SL_slash_apply,Pi.sub_apply,D2] at H
  have hden := denom_ne_zero (γ : GL (Fin 2) ℝ) z
  norm_num only [zpow_neg,zpow_ofNat] at H
  field_simp [hden] at H
  linear_combination H

/-- Every integer weight at least three agrees with the normalized
level-one Eisenstein modular form after restoring its constant factor. -/
theorem eisensteinG_nat_eq_modularForm {k : ℕ} (hk : 3≤k) (z : ℍ) :
    eisensteinG z k=2*riemannZeta k*ModularForm.E hk z := by
  rw [eisensteinG_eq_latticeSum z (by exact_mod_cast (show 2<k by omega)),eisensteinLatticeSum]
  have hterm (v : Fin 2→ℤ) :
      eisensteinLatticeTerm z k (v 0) (v 1)=eisSummand k v z := by
    let w : ℂ := (v 0:ℂ)*z+(v 1:ℤ)
    have hne : k≠0 := by omega
    rw [eisensteinLatticeTerm,eisensteinReflection_nat]
    change (if v 0=0 ∧ v 1=0 then 0 else if _ then w^(-(k:ℂ)) else (-1:ℂ)^k*(-w)^(-(k:ℂ)))=w^(-(k:ℤ))
    simp only [Complex.cpow_neg,Complex.cpow_natCast,zpow_neg,zpow_natCast]
    split_ifs with h h
    · simp [w,h.1,h.2,hne]
    · rfl
    · rw [←neg_one_mul w,mul_pow,mul_inv_rev]
      have hsign : (-1:ℂ)^k≠0 := pow_ne_zero _ (by norm_num)
      field_simp
  have HE := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
  rw [←(finTwoArrowEquiv ℤ).tsum_eq (f:=fun v : ℤ×ℤ => eisensteinLatticeTerm z k v.1 v.2)]
  change (∑' v : Fin 2→ℤ,eisensteinLatticeTerm z k (v 0) (v 1))=_
  simp_rw [hterm]
  rw [HE]
  change _=2*riemannZeta k*((1/2:ℂ)*eisensteinSeries (N:=1) 0 k z)
  ring

/-- Homogeneous transformation law at every integer weight `k ≥ 3`. -/
theorem eisensteinG_nat_modular {k : ℕ} (hk : 3≤k) (γ : SL(2,ℤ)) (z : ℍ) :
    eisensteinG ((γ • z : ℍ):ℂ) k=(denom γ z)^k*eisensteinG z k := by
  rw [eisensteinG_nat_eq_modularForm hk,eisensteinG_nat_eq_modularForm hk]
  have H := slash_action_eqn'' (ModularForm.E hk) (γ:=(γ:GL (Fin 2) ℝ)) (show _∈(Matrix.SpecialLinearGroup.mapGL ℝ).range from ⟨γ,rfl⟩) z
  change (ModularForm.E hk) (γ • z)=(denom γ z)^(k:ℤ)*(ModularForm.E hk) z at H
  rw [H,zpow_natCast]; ring

/-- Translation is periodic at every complex weight. -/
theorem eisensteinG_add_one (z s : ℂ) : eisensteinG (z+1) s=eisensteinG z s := by
  have he : eisensteinNome (z+1)=eisensteinNome z := by
    rw [eisensteinNome,eisensteinNome,mul_add,mul_one,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  simp only [eisensteinG,he]

end AnalyticNumberTheory.ModularAndPartitions
