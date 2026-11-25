import AnalyticNumberTheory.AnalyticTools.SquareMeanLimits
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A vanishing square mean for vertical truncation errors

For a cutoff just above the height, a pole term of size
`N^(1−σ)/t` has negligible normalized square integral when `σ > 1/2`.
-/

open Real Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- An approximation with a pole term and a uniform remainder has vanishing
mean-square error on a vertical line in the right half of the critical strip. -/
theorem tendsto_squareMean_of_vertical_error (E : ℕ → ℝ → ℂ) {σ A B : ℝ}
    (hσ : 1/2<σ) (hσ' : σ≤1)
    (hcont : ∀ N T, ContinuousOn (E N) (Set.Icc 1 T))
    (hbound : ∀ {N : ℕ}, 0<N → ∀ t : ℝ, 1≤t → t≤N →
      ‖E N t‖≤A*((N:ℝ)+1)^(1-σ)/t+B*(N:ℝ)^(-σ)) :
    Tendsto (fun T : ℝ => intervalSquareMean 1 T T (E (⌊T⌋₊+1))) atTop (𝓝 0) := by
  let γ := 2*(1-σ)
  have hγ : 0≤γ := by dsimp [γ]; linarith
  have hγ' : γ<1 := by dsimp [γ]; linarith
  have h₁ := (tendsto_rpow_neg_atTop (by linarith : 0<1-γ)).const_mul (2*A^2*(3:ℝ)^γ)
  have h₂ := (tendsto_rpow_neg_atTop (by linarith : 0<2*σ)).const_mul (2*B^2)
  have hsum := h₁.add h₂
  simp only [mul_zero,add_zero] at hsum
  apply squeeze_zero' _ _ hsum
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    exact div_nonneg (intervalIntegral.integral_nonneg ht fun _ _ => sq_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    let N := ⌊T⌋₊+1
    have ht0 : 0<T := by linarith
    have hN : 0 < N := Nat.succ_pos _
    have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
    have hTN : T≤(N:ℝ) := by simpa [N] using (Nat.lt_floor_add_one T).le
    have hNT : (N:ℝ)+1≤3*T := by dsimp [N]; push_cast; linarith [Nat.floor_le ht0.le]
    let U := A*(((N:ℝ)+1)^(1-σ))
    let V := B*(N:ℝ)^(-σ)
    have hU : U^2 ≤ A^2*((3:ℝ)^γ*T^γ) := by
      dsimp only [U]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (by positivity),← Real.mul_rpow (by norm_num : (0:ℝ)≤3) ht0.le]
      push_cast
      rw [show (1-σ)*(2:ℝ)=γ by dsimp [γ]; ring]
      exact Real.rpow_le_rpow (by positivity) hNT hγ
    have hV : V^2 ≤ B^2*T^(-(2*σ)) := by
      dsimp only [V]; rw [mul_pow,← Real.rpow_natCast ((N:ℝ)^(-σ)) 2,← Real.rpow_mul hNr.le]
      push_cast
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [show -σ*(2:ℝ)= -(2*σ) by ring]
      exact Real.rpow_le_rpow_of_nonpos ht0 hTN (by linarith)
    have hp (t : ℝ) (hm : t∈Set.Icc (1:ℝ) T) : ‖E N t‖^2 ≤ 2*U^2*t^(-2:ℝ)+2*V^2 := by
      have htp : 0<t := by linarith [hm.1]
      have h := hbound hN t hm.1 (hm.2.trans hTN)
      change ‖E N t‖ ≤ U/t+V at h
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      have htinv : t^(-2:ℝ) = (t^2)⁻¹ := by rw [Real.rpow_neg htp.le,Real.rpow_two]
      rw [htinv]
      have he : (U/t)^2=U^2*(t^2)⁻¹ := by rw [div_pow,div_eq_mul_inv]
      nlinarith only [hs,sq_nonneg (U/t-V),he]
    have hc := (hcont N T).norm.pow 2
    have hi : IntervalIntegrable (fun t : ℝ => 2*U^2*t^(-2:ℝ)) volume 1 T :=
      (continuousOn_const.mul (continuousOn_id.rpow_const fun t hm => Or.inl (by dsimp; linarith [hm.1]))).intervalIntegrable_of_Icc ht
    have hh := intervalIntegral.integral_mono_on ht (hc.intervalIntegrable_of_Icc ht) (hi.add intervalIntegrable_const) hp
    have heval : (∫ t in (1:ℝ)..T, t^(-2:ℝ)) = 1-T⁻¹ := by
      rw [integral_rpow (Or.inr ⟨by norm_num,fun h => by rw [Set.uIcc_of_le ht] at h; linarith [h.1]⟩)]
      simp only [show (-2:ℝ)+1= -1 by norm_num,Real.rpow_neg_one]; ring
    rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const_mul,heval,
      intervalIntegral.integral_const,smul_eq_mul] at hh
    change (∫ t in (1:ℝ)..T, ‖E N t‖^2)/T ≤ _
    apply (div_le_iff₀ ht0).mpr
    have hpow : T^(-(1-γ))*T = T^γ := by
      rw [←Real.rpow_add_one ht0.ne']; congr 1; ring
    have husa := mul_le_mul_of_nonneg_left (sub_le_self 1 (inv_nonneg.mpr ht0.le)) (show 0≤2*U^2 by positivity)
    have hvsa := mul_le_mul_of_nonneg_left (sub_le_self T zero_le_one) (show 0≤2*V^2 by positivity)
    change (∫ t in (1:ℝ)..T, ‖E N t‖^2) ≤ (2*A^2*(3:ℝ)^γ*T^(-(1-γ))+2*B^2*T^(-(2*σ)))*T
    change (∫ t in (1:ℝ)..T, ‖E N t‖^2) ≤ 2*U^2*(1-T⁻¹)+(T-1)*(2*V^2) at hh
    nlinarith only [hh,husa,hvsa,hU,mul_le_mul_of_nonneg_right hV ht0.le,
      congrArg (fun y : ℝ => 2*A^2*(3:ℝ)^γ*y) hpow]

end AnalyticNumberTheory.AnalyticTools
