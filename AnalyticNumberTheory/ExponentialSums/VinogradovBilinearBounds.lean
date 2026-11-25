import AnalyticNumberTheory.ExponentialSums.VinogradovLinearKernels

/-!
# Combining the one-dimensional bilinear estimates

Taking the final moment root converts a bound for the mean value and
bounds for the individual kernels into an explicit estimate for the
bilinear sum itself.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- Apply a logarithmic majorant to the mean value and each frequency kernel. -/
theorem vinogradovBilinearSum_exp_bound {s k a : ℕ} (hs : 0<s) (ha : 0<a)
    (α : Fin k → ℝ) (B : ℝ) (h : Fin k → ℝ) (hJ : vinogradovJ s k a ≤ Real.exp B)
    (hK : ∀ j, vinogradovLinearKernel (s*a^(j.val+1)) (α j) ≤ Real.exp (h j)) :
    ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) α‖ ≤
      Real.exp (((8*(s:ℝ)^2-4*s)*Real.log a + 2*B + ∑ j,h j)/(4*(s:ℝ)^2)) := by
  let d := 4*s^2
  have hd : 0<d := by dsimp [d]; positivity
  have ha0 : (0:ℝ)<a := by positivity
  have hsn : 4*s ≤ 8*s^2 := by nlinarith [Nat.mul_le_mul_left s hs]
  have hJ0 := vinogradovJ_nonneg s k a
  have hprod : (∏ j, vinogradovLinearKernel (s*a^(j.val+1)) (α j)) ≤ Real.exp (∑ j,h j) := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ (fun j _ => sum_nonneg (fun _ _ => norm_nonneg _)) (fun j _ => hK j)
  apply le_of_pow_le_pow_left₀ hd.ne' (Real.exp_pos _).le
  apply (vinogradovBilinearSum_interval_le hs a α).trans
  calc _ ≤ (a:ℝ)^(8*s^2-4*s) * (Real.exp B)^2 * Real.exp (∑ j,h j) := by
             gcongr
             exact prod_nonneg (fun j _ => sum_nonneg (fun _ _ => norm_nonneg _))
       _ = _ := by
             rw [←Real.exp_nat_mul,←Real.exp_nat_mul]
             conv_lhs => rw [←Real.exp_log ha0,←Real.exp_nat_mul]
             rw [←Real.exp_add,←Real.exp_add]
             apply congrArg Real.exp
             dsimp [d]; push_cast [Nat.cast_sub hsn]; field_simp

/-- The elementary frequency-box contribution, expressed additively in the
degree so it can be summed over the full Taylor polynomial. -/
theorem vinogradovLinearKernel_log_bound {s a : ℕ} (hs : 0<s) (ha : 0<a) (m : ℕ) :
    Real.log (2*(s*a^m:ℕ)+1:ℝ) ≤ Real.log (3*(s:ℝ))+m*Real.log (a:ℝ) := by
  have hA : 0<(a:ℝ) := by positivity
  have hS : 0<(s:ℝ) := by positivity
  have h1 : (1:ℝ)≤(s*a^m:ℕ) := by exact_mod_cast Nat.mul_pos hs (pow_pos ha m)
  rw [←Real.log_pow,←Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  push_cast at h1 ⊢
  linarith only [h1]

private theorem twice_sum_degrees (k : ℕ) :
    2*(∑ j : Fin k, ((j.val:ℝ)+1))=(k:ℝ)*((k:ℝ)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    linarith only [ih]

/-- Given a mean-value estimate with exponent defect `δ`, every selected degree
saves `U` in the logarithm before taking the final moment root. -/
theorem vinogradovBilinearSum_of_kernel_savings {s k a : ℕ} (hs : 0<s) (ha : 0<a)
    (α : Fin k → ℝ) (S : Finset (Fin k)) (C δ U : ℝ)
    (hJ : vinogradovJ s k a ≤ Real.exp (C+(2*(s:ℝ)-(k:ℝ)*(k+1)/2+δ)*Real.log a))
    (hK : ∀ j∈S, vinogradovLinearKernel (s*a^(j.val+1)) (α j) ≤
      (2*(s*a^(j.val+1):ℕ)+1:ℝ)^2 * Real.exp (-U)) :
    ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) α‖ ≤
      (a:ℝ)^2*Real.exp ((2*C+2*δ*Real.log a + 2*k*Real.log (3*(s:ℝ))-S.card*U)/(4*(s:ℝ)^2)) := by
  classical
  let A := Real.log (a:ℝ)
  let V := Real.log (3*(s:ℝ))
  let B := C+(2*(s:ℝ)-(k:ℝ)*(k+1)/2+δ)*A
  let h (j : Fin k) := 2*V+2*((j.val:ℝ)+1)*A-(if j∈S then U else 0)
  have ha0 : 0<(a:ℝ) := by positivity
  have hK' (j : Fin k) : vinogradovLinearKernel (s*a^(j.val+1)) (α j) ≤ Real.exp (h j) := by
    let L := (2*(s*a^(j.val+1):ℕ)+1:ℝ)
    have hL : 0<L := by dsimp [L]; positivity
    have hv : Real.log L ≤ V+((j.val:ℝ)+1)*A := by
      simpa only [Nat.cast_add,Nat.cast_one] using vinogradovLinearKernel_log_bound hs ha (j.val+1)
    have hp : L^2 ≤ Real.exp (2*V+2*((j.val:ℝ)+1)*A) := by
      have h := Real.exp_le_exp.mpr (show 2*Real.log L≤2*V+2*((j.val:ℝ)+1)*A by linarith only [hv])
      simpa only [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hL] using h
    by_cases hj : j∈S
    · apply (hK j hj).trans
      dsimp only [h]; simp only [hj,ite_true]; rw [sub_eq_add_neg,Real.exp_add]
      exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    · apply (vinogradovLinearKernel_le_sq _ _).trans
      simpa only [h,hj,ite_false,sub_zero] using hp
  have hsum : (∑ j,h j) = 2*k*V + ((k:ℝ)*(k+1))*A - S.card*U := by
    simp only [h,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,←sum_mul,←mul_sum,sum_ite_mem,univ_inter]
    have H := twice_sum_degrees k
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at H
    linear_combination A*H
  have H := vinogradovBilinearSum_exp_bound hs ha α B h hJ hK'
  apply H.trans_eq
  rw [hsum,←Real.exp_log ha0,←Real.exp_nat_mul,←Real.exp_add,Real.log_exp]
  apply congrArg Real.exp
  dsimp only [A,V,B]
  field_simp
  ring

end AnalyticNumberTheory.ExponentialSums
