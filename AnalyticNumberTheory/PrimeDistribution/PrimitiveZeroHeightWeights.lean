import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyZeroWeights
import AnalyticNumberTheory.PrimeDistribution.ZeroHeightSummation

/-! # Reciprocal-ordinate weights in the primitive zero family -/
noncomputable section
open Finset Real Complex
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- The linear contribution in the power sum acquires one height logarithm,
whereas its cube-root contribution is summable over dyadic height blocks. -/
theorem primitive_zero_reciprocal_height_of_power_sum {Q : ℕ} {x T C : ℝ}
    (hQ : 1≤Q) (hx : 2≤x) (hT : 1≤T) (hC : 0<C)
    (H : ∀ u : ℝ,2≤u → primitiveFamilyZeroWeight Q u (fun z => x^z.re) ≤
      C*(Real.sqrt x*((Q:ℝ)^2*u)+x*((Q:ℝ)^2*u)^(1/3:ℝ))*Real.log x*(Real.log ((Q:ℝ)*u))^8) :
    primitiveFamilyZeroWeight Q T (fun z => x^z.re/(1+|z.im|)) ≤
      (6*C)*(Real.sqrt x*(Q:ℝ)^2*(1+Real.log (T+1))+x*(Q:ℝ)^(2/3:ℝ))*
        Real.log x*(1+Real.log ((Q:ℝ)*(T+1)))^8 := by
  let S := primitiveFamilyZeros Q T
  let L := 1+Real.log ((Q:ℝ)*(T+1))
  let D := C*Real.log x*L^8
  let A := D*Real.sqrt x*(Q:ℝ)^2
  let B := D*x*(Q:ℝ)^(2/3:ℝ)
  let w (i : (p : PrimitiveCharacterIndex) × ℂ) := (characterZeroMultiplicity i.1.2 i.2:ℝ)*x^i.2.re
  let v (i : (p : PrimitiveCharacterIndex) × ℂ) := |i.2.im|
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hq₀ := zero_lt_one.trans_le hr
  have hlog := Real.log_nonneg (by linarith : 1≤x)
  have hp := one_le_mul_of_one_le_of_one_le hr (show 1≤T+1 by linarith)
  have hL : 0≤L := by dsimp [L];linarith [Real.log_nonneg hp]
  have hD : 0≤D := by dsimp [D];positivity
  have hA : 0≤A := by dsimp [A];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have hw (i) : 0≤w i := by dsimp only [w];positivity
  have hv (i) (hi : i∈S) : 0≤v i ∧ v i≤T := by
    obtain ⟨hp,hs⟩ := mem_sigma.mp hi
    letI : NeZero i.1.1 := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus hp).1⟩
    obtain ⟨_,_,h₁,h₂,_⟩ := (mem_characterStripZeros i.1.2).mp hs
    exact ⟨abs_nonneg _,abs_le.mpr ⟨h₁,h₂⟩⟩
  have hc (u : ℝ) (hu : 2≤u) (hu' : u≤2*(T+1)) :
      (∑i∈S with v i≤u,w i)≤A*u+B*Real.sqrt u := by
    have hsub : (S.filter fun i => v i≤u) ⊆ primitiveFamilyZeros Q u := by
      intro i hi
      obtain ⟨hi,ht⟩ := mem_filter.mp hi
      obtain ⟨hp,hs⟩ := mem_sigma.mp hi
      letI : NeZero i.1.1 := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus hp).1⟩
      obtain ⟨h₁,h₂,_,_,hz⟩ := (mem_characterStripZeros i.1.2).mp hs
      exact mem_sigma.mpr ⟨hp,(mem_characterStripZeros i.1.2).mpr ⟨h₁,h₂,(abs_le.mp ht).1,(abs_le.mp ht).2,hz⟩⟩
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hw i)).trans (le_trans (H u hu) ?_)
    have hu₀ : 0<u := by linarith
    have hl := Real.log_le_log (mul_pos hq₀ hu₀) (mul_le_mul_of_nonneg_left hu' hq₀.le)
    rw [show (Q:ℝ)*(2*(T+1))=2*((Q:ℝ)*(T+1)) by ring,
      Real.log_mul (by norm_num) (by linarith : (Q:ℝ)*(T+1)≠0)] at hl
    have hlogu : 0≤Real.log ((Q:ℝ)*u) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hr (by linarith))
    have hpow := pow_le_pow_left₀ hlogu (show Real.log ((Q:ℝ)*u)≤L by
      dsimp only [L];linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]) 8
    have ht : u^(1/3:ℝ)≤Real.sqrt u := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hqr : ((Q:ℝ)^2)^(1/3:ℝ)=(Q:ℝ)^(2/3:ℝ) := by
      rw [←Real.rpow_two,←Real.rpow_mul hq₀.le];norm_num
    have hb : ((Q:ℝ)^2*u)^(1/3:ℝ)≤(Q:ℝ)^(2/3:ℝ)*Real.sqrt u := by
      rw [Real.mul_rpow (sq_nonneg _) hu₀.le,hqr];gcongr
    apply (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left hb (by linarith : 0≤x)) _) hC.le) hlog)
      hpow (by positivity) (by positivity)).trans_eq
    dsimp only [A,B,D];ring
  have hh := reciprocal_height_sum_le S v w hA hB hT hv (fun i _ => hw i) hc
  simp only [primitiveFamilyZeroWeight,←mul_div_assoc]
  exact hh.trans_eq (by dsimp only [A,B,D,L];ring)

end AnalyticNumberTheory.PrimeDistribution
