import AnalyticNumberTheory.ModularAndPartitions.PartitionInversion

/-!
# Modular transformation of the partition product

The exponential prefactor turns the partition generating function into
the reciprocal of Dedekind eta, giving a transformation under every
unimodular substitution.
-/

open Complex Real
open scoped UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

/-- Euler's product identifies the normalized partition generating function
in the upper half-plane with the reciprocal of Dedekind eta. -/
theorem partitionGenFun_normalized_eq_eta_inv (τ : ℍ) :
    Complex.exp (-(π:ℂ)*I*(τ:ℂ)/12)*partitionGenFun (Complex.exp (2*(π:ℂ)*I*(τ:ℂ)))=
      (dedekindEta τ)⁻¹ := by
  have hz : 0<(-(I:ℂ)*(τ:ℂ)).re := by simpa using τ.im_pos
  have H := eta_mul_partitionGenFun_nome hz
  have he : I*(-I*(τ:ℂ))=(τ:ℂ) := by rw [←mul_assoc,mul_neg,Complex.I_mul_I,neg_neg,one_mul]
  rw [he,partitionNome] at H
  rw [show -2*(π:ℂ)*(-I*(τ:ℂ))=2*(π:ℂ)*I*(τ:ℂ) by ring] at H
  have hη := eta_ne_zero_of_im_pos τ.im_pos
  change _=(ModularForm.eta (τ:ℂ))⁻¹
  apply mul_left_cancel₀ hη
  rw [mul_inv_cancel₀ hη,mul_left_comm,H,←Complex.exp_add]
  convert Complex.exp_zero using 2; ring

/-- The full modular transformation of the partition generating function,
with the eta multiplier and its chosen square root. -/
theorem partitionGenFun_SL2Z (γ : SL(2,ℤ)) (τ : ℍ) :
    Complex.exp (-(π:ℂ)*I*(τ:ℂ)/12)*partitionGenFun (Complex.exp (2*(π:ℂ)*I*(τ:ℂ))) =
      etaMultiplier γ * etaAutomorphyFactor γ τ *
        (Complex.exp (-(π:ℂ)*I*((γ • τ : ℍ):ℂ)/12)*
          partitionGenFun (Complex.exp (2*(π:ℂ)*I*((γ • τ : ℍ):ℂ)))) := by
  rw [partitionGenFun_normalized_eq_eta_inv,partitionGenFun_normalized_eq_eta_inv]
  have he := dedekindEta_SL2Z_factor γ τ
  have hn : dedekindEta (γ • τ)≠0 := eta_ne_zero_of_im_pos (γ • τ).im_pos
  have hd : dedekindEta τ≠0 := eta_ne_zero_of_im_pos τ.im_pos
  field_simp [hn,hd]
  rw [he]; ring

end AnalyticNumberTheory.ModularAndPartitions
