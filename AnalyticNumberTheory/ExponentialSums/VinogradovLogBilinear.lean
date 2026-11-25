import AnalyticNumberTheory.ExponentialSums.VinogradovBilinearBounds
import AnalyticNumberTheory.ExponentialSums.VinogradovLogCoefficients
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Estimating bilinear sums with logarithmic Taylor coefficients

A positive proportion of the degrees gives cancellation. For a
Vinogradov mean value with defect at most `K exp(-20)`, these savings
dominate the residual power of the length.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem window_card {l r : ℕ} (hr : 4*l≤r) :
    (univ.filter (fun j : Fin r => 3*l≤j.val ∧ j.val<4*l)).card = l := by
  apply Eq.trans _ (card_range l)
  apply card_bij (fun j _ => j.val-3*l)
  · intro j hj; simp only [mem_filter,mem_univ,true_and] at hj
    apply mem_range.mpr; omega
  · intro x hx y hy he
    simp only [mem_filter,mem_univ,true_and] at hx hy
    apply Fin.ext; omega
  · intro i hi; have hi' := mem_range.mp hi
    refine ⟨⟨3*l+i,by omega⟩,by simp; omega,by simp⟩

private theorem logMoment_defect : Real.exp (-20) ≤ 1/1000000 := by
  rw [Real.exp_neg,inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have h := pow_le_pow_left₀ (by norm_num : 0≤(2:ℝ)) Real.exp_one_gt_two.le 20
  rw [←Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith only [h]

private theorem logMoment_root_bound {C X A T l r s δ : ℝ} (hC : 0≤C) (hX : 0≤X)
    (hA : 0≤A) (hAX : A≤X) (hl : 1≤l) (hr : l≤r) (hr' : r≤32*l)
    (hs : s=21*r^2) (hT : 2*l*X≤T) (hδ : δ≤r*(r+1)/2*Real.exp (-20)) :
    (2*(C*r^4)+2*δ*A+2*r*Real.log (3*s)-l*(T/20-Real.log 5840))/(4*s^2) ≤
      (2*C+6000) - X/(1000000000000*l^2) := by
  have hl0 : 0<l := by linarith
  have hr1 : 1≤r := hl.trans hr
  have hr0 : 0<r := by linarith
  have hs0 : 0<s := by rw [hs]; positivity
  have hr4 := pow_le_pow_left₀ hr0.le hr' 4
  have hr2 := pow_le_pow_left₀ hr0.le hr' 2
  have hd₀ := mul_le_mul_of_nonneg_left logMoment_defect (show 0≤r*(r+1)/2 by positivity)
  have hδ' : 2*δ≤l^2/50 := by
    nlinarith only [hδ,hd₀,hr2,mul_le_mul_of_nonneg_left hr1 hr0.le,sq_nonneg l]
  have hd' : 2*δ*A≤l*T/40 := by
    calc _ ≤ l^2/50*A := mul_le_mul_of_nonneg_right hδ' hA
         _ ≤ l^2/50*X := mul_le_mul_of_nonneg_left hAX (by positivity)
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hT hl0.le,mul_nonneg (sq_nonneg l) hX]
  have h34 : r^3≤r^4 := by simpa only [←pow_succ,mul_one] using mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0.le 3)
  have h14 : r≤r^4 := by simpa only [pow_one] using pow_le_pow_right₀ hr1 (by norm_num : 1≤4)
  have hlogs : 2*r*Real.log (3*s)+l*Real.log 5840 ≤ 6000*r^4 := by
    have h1 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (show 0<3*s by positivity)) hr0.le
    have h2 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (show 0<(5840:ℝ) by norm_num)) hl0.le
    rw [hs] at h1 ⊢
    nlinarith only [h1,h2,hr,h34,h14,hr0.le,hl0.le]
  have hrat : X/(1000000000000*l^2) ≤ l*T/(70560*r^4) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hr4 hX,
      mul_le_mul_of_nonneg_left hT (show 0≤l^3 by positivity),mul_nonneg (pow_nonneg hl0.le 4) hX]
  calc _ ≤ ((2*C+6000)*r^4-l*T/40)/(4*s^2) := by
             apply div_le_div_of_nonneg_right _ (by positivity)
             linarith only [hd',hlogs]
       _ = (2*C+6000)/1764 - l*T/(70560*r^4) := by rw [hs]; field_simp; ring
       _ ≤ _ := by linarith only [hrat,hC]

/-- Bilinear bound for the logarithmic Taylor coefficients. The constant
`C` enters only through a degree-uniform `exp(C r^4)` mean-value estimate. -/
theorem logTaylor_bilinear_saving {r s l a : ℕ} {N n t C δ : ℝ}
    (hN : 0<N) (hX : 100≤Real.log N) (hn : N≤n) (hn' : n≤2*N)
    (ht : 0<t) (hl : 8≤l) (hlT : 2*l*Real.log N≤Real.log t)
    (hTl : Real.log t≤(2*l+2)*Real.log N)
    (hr : 4*l≤r) (hr' : r≤32*l) (hs : s=21*r^2) (ha : 0<a)
    (haN : Real.log N/3≤Real.log a) (haN' : Real.log a≤Real.log N)
    (hC : 0≤C) (hδ : δ≤(r:ℝ)*(r+1)/2*Real.exp (-20))
    (hJ : vinogradovJ s r a ≤ Real.exp (C*(r:ℝ)^4+
      (2*(s:ℝ)-(r:ℝ)*(r+1)/2+δ)*Real.log a)) :
    ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) (logTaylorCoefficients r t n)‖ ≤
      (a:ℝ)^2*Real.exp ((2*C+6000)-Real.log N/(1000000000000*(l:ℝ)^2)) := by
  classical
  let S := univ.filter (fun j : Fin r => 3*l≤j.val ∧ j.val<4*l)
  have hr0 : 0<r := by omega
  have hs0 : 0<s := by rw [hs]; positivity
  have hs' : (s:ℝ)=21*(r:ℝ)^2 := by exact_mod_cast hs
  have hc : S.card=l := window_card hr
  let U := Real.log t/20-Real.log 5840
  have hK (j : Fin r) (hj : j∈S) :
      vinogradovLinearKernel (s*a^(j.val+1)) (logTaylorCoefficients r t n j) ≤
        (2*(s*a^(j.val+1):ℕ)+1:ℝ)^2 * Real.exp (-U) := by
    have hi : 3*l≤j.val ∧ j.val<4*l := (mem_filter.mp hj).2
    have H := logTaylor_kernel_window j hN hX hn hn' ht (by exact_mod_cast hl : (8:ℝ)≤l)
      hlT hTl (by exact_mod_cast (show 3*l≤j.val+1 by omega))
      (by exact_mod_cast (show j.val+1≤4*l by omega)) hs0 ha haN
    apply H.trans_eq
    dsimp only [U]; rw [neg_sub,Real.exp_sub,Real.exp_log (by norm_num),Real.rpow_def_of_pos ht]
    rw [show Real.log t*(-(1/20):ℝ)= -(Real.log t/20) by ring,Real.exp_neg]
    ring
  apply (vinogradovBilinearSum_of_kernel_savings hs0 ha _ S _ δ U hJ hK).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (sq_nonneg _)
  rw [hc]
  exact logMoment_root_bound hC (by linarith) (Real.log_nonneg (by exact_mod_cast ha)) haN'
    (by exact_mod_cast (show 1≤l by omega)) (by exact_mod_cast (show l≤r by omega))
    (by exact_mod_cast hr') hs' hlT hδ

end AnalyticNumberTheory.ExponentialSums
