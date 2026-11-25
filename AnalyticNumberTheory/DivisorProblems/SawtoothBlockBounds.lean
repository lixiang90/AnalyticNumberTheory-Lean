import AnalyticNumberTheory.DivisorProblems.DivisorCubeRoot

/-!
# Transfer of partial exponential-sum bounds to sawtooth sums
-/

open Real Finset
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

/-- Exponential-sum estimates may grow linearly above the smoothing
frequency `K`. The finite Fourier sum then costs a single logarithm. -/
theorem sawtooth_sum_le_of_frequency_bound {ι : Type*} (s : Finset ι) (f : ι→ℝ)
    {K : ℕ} (hK : 2≤K) {U : ℝ} (hU : 0≤U)
    (hF : ∀ n∈Icc 1 (K^2),‖∑ i∈s,e (n*f i)‖≤U*max 1 ((n:ℝ)/K)) :
    |∑ i∈s,sawtooth (f i)|≤2*(s.card:ℝ)/K+U*(1+2*Real.log K) := by
  have hK' : (1:ℝ)<K := by exact_mod_cast hK
  have hK0 : 0<(K:ℝ) := by linarith
  have H := abs_sum_sawtooth_le_exponential_sums s f (H:=K^2) (by nlinarith)
    (inv_pos.mpr hK0) (inv_lt_one_of_one_lt₀ hK')
  have hweights (n : ℕ) (hn : n∈Icc 1 (K^2)) :
      K*‖e ((n:ℝ)*(K:ℝ)⁻¹)-1‖*max 1 ((n:ℝ)/K)≤2*Real.pi*n := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    let t := (n:ℝ)*(K:ℝ)⁻¹
    have ht : 0≤t := by dsimp [t]; positivity
    have h₁ : ‖e t-1‖≤2*Real.pi*t := by
      rw [norm_sub_rev,norm_one_sub_e]
      have hd : distToInt t≤t := by simpa [abs_of_nonneg ht] using distToInt_le_abs_sub_int t 0
      calc _ ≤ 2*(Real.pi*distToInt t) := by gcongr; exact Real.sin_le (mul_nonneg Real.pi_pos.le (distToInt_nonneg _))
           _ ≤ 2*(Real.pi*t) := by gcongr
           _ = _ := by ring
    have h₂ : ‖e t-1‖≤2 := (norm_sub_le _ _).trans_eq (by rw [norm_e,norm_one]; norm_num)
    by_cases h : (n:ℝ)≤K
    · rw [max_eq_left ((div_le_one hK0).mpr h),mul_one]
      calc _ ≤ K*(2*Real.pi*t) := mul_le_mul_of_nonneg_left h₁ hK0.le
           _ = _ := by dsimp [t]; field_simp
    · rw [max_eq_right ((one_le_div hK0).mpr (not_le.mp h).le)]
      calc _ ≤ (K:ℝ)*2*((n:ℝ)/K) := by gcongr
           _ = 2*n := by field_simp
           _ ≤ _ := by nlinarith only [mul_nonneg hn0.le (sub_nonneg.mpr Real.pi_gt_three.le)]
  have hsum : (K:ℝ)*(∑ n∈Icc 1 (K^2), ‖e ((n:ℝ)*(K:ℝ)⁻¹)-1‖*
      ‖∑ i∈s,e ((n:ℝ)*f i)‖/(n:ℝ)^2)≤2*Real.pi*U*(1+2*Real.log K) := by
    rw [mul_sum]
    calc _ ≤ ∑ n∈Icc 1 (K^2),(2*Real.pi*U)*(n:ℝ)⁻¹ := by
           apply sum_le_sum; intro n hn
           have hp : 0<(n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
           calc
             _ ≤ (K:ℝ)*(‖e ((n:ℝ)*(K:ℝ)⁻¹)-1‖*(U*max 1 ((n:ℝ)/K))/(n:ℝ)^2) := by gcongr; exact hF n hn
             _ = ((K:ℝ)*‖e ((n:ℝ)*(K:ℝ)⁻¹)-1‖*max 1 ((n:ℝ)/K))*U/(n:ℝ)^2 := by ring
             _ ≤ (2*Real.pi*n)*U/(n:ℝ)^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hweights n hn) hU) (sq_nonneg _)
             _ = _ := by field_simp
         _ ≤ _ := by
           rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity)
           have hh := harmonic_le_one_add_log (K^2)
           rw [harmonic_eq_sum_Icc,Rat.cast_sum,Nat.cast_pow,Real.log_pow] at hh
           simpa only [Rat.cast_inv,Rat.cast_natCast,Nat.cast_ofNat] using hh
  have hp : 0<2*Real.pi^2 := by positivity
  have hlog := Real.log_nonneg (by linarith : 1≤(K:ℝ))
  have hπ := Real.pi_gt_three
  have hcoeff : 1/Real.pi^2+1/2≤2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (show 1≤Real.pi^2 by nlinarith)
    linarith
  have hsum' := div_le_div_of_nonneg_right hsum hp.le
  have hsp : 2*Real.pi*U*(1+2*Real.log K)/(2*Real.pi^2)≤U*(1+2*Real.log K) := by
    apply (div_le_iff₀ hp).mpr
    have h := mul_nonneg (show 0≤U*(1+2*Real.log K) by positivity)
      (show 0≤2*Real.pi^2-2*Real.pi by nlinarith)
    linarith only [h]
  have H' := mul_le_mul_of_nonneg_left H hK0.le
  rw [←mul_assoc,mul_inv_cancel₀ hK0.ne',one_mul,mul_add,mul_div_assoc'] at H'
  apply H'.trans
  apply add_le_add _ (hsum'.trans hsp)
  rw [Nat.cast_pow,show (K:ℝ)*((s.card:ℝ)*(((K:ℝ)^2)⁻¹/Real.pi^2+(K:ℝ)⁻¹^2/2))=
    (s.card:ℝ)/K*(1/Real.pi^2+1/2) by field_simp]
  calc _ ≤ (s.card:ℝ)/K*2 := by gcongr
       _ = _ := by ring

end AnalyticNumberTheory.DivisorProblems
