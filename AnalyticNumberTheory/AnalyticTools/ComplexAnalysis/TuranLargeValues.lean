import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.TuranPowerSums
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Stable Turán detection from a square-mass bound

Only points of norm at least `1/256` enter Turán's lemma. The square mass controls
the remaining power sums and the length of the interval of admissible exponents.
-/

noncomputable section

open Finset Complex
open scoped Classical

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- A point of norm at least one half forces a large high power sum even when
the sums are known only up to a geometrically decreasing error. -/
theorem turan_detection_of_square_mass {ι : Type*} (S : Finset ι) (b : ι → ℕ) (v : ι → ℂ)
    {i₀ : ι} (hi₀ : i₀ ∈ S) (hb₀ : 1 ≤ b i₀) (hv₀ : 1/2 ≤ ‖v i₀‖)
    {H : ℝ} (hH : 0 ≤ H) (henergy : ∑ i ∈ S, (b i:ℝ)*‖v i‖^2 ≤ H)
    {M : ℕ} (hM : 16*256^2*(H+1) ≤ (M:ℝ)) (A : ℕ → ℂ)
    (herror : ∀ k : ℕ, 1 ≤ k → ‖A k - ∑ i ∈ S, (b i:ℂ)*v i^k‖ ≤ H*(1/256:ℝ)^(k-1)) :
    ∃ k ∈ Ioc M (2*M), (1/64:ℝ)^k ≤ ‖A k‖ := by
  let U := S.filter fun i => 0 < b i ∧ (1/256:ℝ) ≤ ‖v i‖
  have hU₀ : i₀ ∈ U := mem_filter.mpr ⟨hi₀,hb₀,by linarith⟩
  have hcard : (U.card:ℝ) ≤ 256^2*H := by
    have hsingle (i : ι) (hi : i ∈ U) : (1/256:ℝ)^2 ≤ (b i:ℝ)*‖v i‖^2 := by
      obtain ⟨_,hb,hv⟩ := mem_filter.mp hi
      exact (pow_le_pow_left₀ (by norm_num) hv 2).trans (le_mul_of_one_le_left (sq_nonneg _) (by exact_mod_cast hb))
    have hsum := (sum_le_sum hsingle).trans
      ((sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)).trans henergy)
    simp only [sum_const,nsmul_eq_mul] at hsum; linarith
  obtain ⟨i,hi,himax⟩ := U.exists_max_image (fun i => ‖v i‖) ⟨i₀,hU₀⟩
  have hvi : 1/2 ≤ ‖v i‖ := hv₀.trans (himax i₀ hU₀)
  obtain ⟨k,hk,hpower⟩ := turan_high_power_sum_scaled U b v hi (mem_filter.mp hi).2.1 himax (by linarith) M
  have hM₁ : 2 ≤ M := by exact_mod_cast (show (2:ℝ) ≤ M by linarith)
  have hU : U.card ≤ M := by exact_mod_cast (show (U.card:ℝ) ≤ M by linarith)
  obtain ⟨hmk,hkn⟩ := mem_Ioc.mp hk
  have hk₂ : 2 ≤ k := by omega
  have hkR : (M:ℝ) ≤ k := by exact_mod_cast hmk.le
  have hkexp : M+10*(U.card:ℝ)+2 ≤ 2*k := by linarith
  have hexp : (1/16:ℝ)^k ≤ Real.exp (-(M+10*(U.card:ℝ)+2)) := by
    have he : (1/16:ℝ) ≤ Real.exp (-2) := by
      rw [Real.exp_neg,one_div,inv_le_inv₀ (by norm_num) (Real.exp_pos _)]
      rw [show (2:ℝ) = 1+1 by norm_num,Real.exp_add]
      nlinarith [mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three.le]
    apply (pow_le_pow_left₀ (by norm_num) he k).trans
    rw [← Real.exp_nat_mul,Real.exp_le_exp]
    linarith
  have hlarge : (1/32:ℝ)^k ≤ ‖∑ j ∈ U, (b j:ℂ)*v j^k‖ := by
    apply le_trans _ hpower
    rw [show (1/32:ℝ) = (1/16)*(1/2) by norm_num,mul_pow]
    exact mul_le_mul hexp (pow_le_pow_left₀ (by norm_num) hvi _) (by positivity) (Real.exp_pos _).le
  have htail : ‖∑ j ∈ S \ U, (b j:ℂ)*v j^k‖ ≤ H*(1/256:ℝ)^(k-2) := by
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ j ∈ S \ U, ((b j:ℝ)*‖v j‖^2)*(1/256:ℝ)^(k-2) := by
        refine sum_le_sum fun j hj => ?_
        rw [norm_mul,Complex.norm_natCast,norm_pow]
        by_cases hb : b j = 0
        · simp [hb]
        have hv : ‖v j‖ ≤ 1/256 := le_of_not_ge fun h =>
          (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨(mem_sdiff.mp hj).1,Nat.pos_of_ne_zero hb,h⟩)
        nth_rw 1 [show k = 2+(k-2) by omega,pow_add]
        rw [←mul_assoc]
        gcongr
      _ ≤ _ := by
        rw [←sum_mul]
        exact mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg sdiff_subset
          (fun _ _ _ => by positivity)).trans henergy) (by positivity)
  have hsmall (e : ℕ) (he : e ≤ 2) : H*(1/256:ℝ)^(k-e) ≤ (1/128:ℝ)^k := by
    have hkpow : (M:ℝ) ≤ (2:ℝ)^k := by
      exact_mod_cast (hmk.le.trans (Nat.lt_two_pow_self (n:=k)).le)
    have hcap : H*(256:ℝ)^e ≤ (2:ℝ)^k := by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤256) he) hH
      linarith
    calc
      _ = (H*256^e)*(1/256:ℝ)^k := by
        nth_rw 2 [show k = e+(k-e) by omega]
        rw [pow_add,←mul_assoc,mul_assoc H,←mul_pow]; norm_num
      _ ≤ (2:ℝ)^k*(1/256:ℝ)^k := mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = _ := by rw [←mul_pow]; norm_num
  have hs := htail.trans (hsmall 2 le_rfl)
  have he := (herror k (by omega)).trans (hsmall 1 (by decide))
  let Z := ∑ j ∈ S, (b j:ℂ)*v j^k
  let Z₀ := ∑ j ∈ U, (b j:ℂ)*v j^k
  let Z₁ := ∑ j ∈ S \ U, (b j:ℂ)*v j^k
  have hsplit : Z₀ + Z₁ = Z := (add_comm ..).trans (sum_sdiff (filter_subset ..))
  have htriangle : ‖Z₀‖ ≤ ‖A k‖ + (‖A k-Z‖ + ‖Z₁‖) := by
    have h := norm_sub_le Z Z₁
    have hz := norm_sub_le (A k) (A k-Z)
    rw [sub_sub_cancel] at hz
    rw [←hsplit,add_sub_cancel_right,hsplit] at h
    linarith
  have hratio : 2*(1/128:ℝ)^k+(1/64:ℝ)^k ≤ (1/32:ℝ)^k := by
    have h2 : (2:ℝ) ≤ (2:ℝ)^k := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 1 ≤ k by omega)
    have h1 (x : ℝ) (hx : 0≤x) : 2*x^k ≤ (2*x)^k := by rw [mul_pow]; gcongr
    have h3 := h1 (1/128) (by norm_num)
    have h4 := h1 (1/64) (by norm_num)
    norm_num only [show (2:ℝ)*(1/128)=1/64 by norm_num,show (2:ℝ)*(1/64)=1/32 by norm_num] at h3 h4
    linarith
  change _ ≤ ‖Z₀‖ at hlarge
  change ‖Z₁‖ ≤ _ at hs
  change ‖A k-Z‖ ≤ _ at he
  exact ⟨k,mem_Ioc.mpr ⟨hmk,by omega⟩,by linarith⟩

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
