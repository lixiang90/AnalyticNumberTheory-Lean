import AnalyticNumberTheory.AdditiveNumberTheory.WaringDiminishingScales

/-!
# Parameters for the logarithmic Waring basis bound

With four full variables per degree, eight times the degree times its
logarithm many short ranges suffice for the minor-arc saving.
-/

open Real Filter Finset
open scoped Topology
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Number of diminishing ranges in each of the two short-variable groups. -/
noncomputable def waringDiminishingOrder (k : ℕ) : ℕ := ⌈8*(k:ℝ)*Real.log k⌉₊

/-- The number of variables in the logarithmic Waring bound. -/
theorem waringDiminishingOrder_total_le (k : ℕ) :
    ((4*k+2*waringDiminishingOrder k:ℕ):ℝ) ≤ 16*k*Real.log k+4*k+2 := by
  by_cases h : k=0
  · simp [h,waringDiminishingOrder]
  have h₁ : (1:ℝ)≤k := by exact_mod_cast (by omega : 1≤k)
  have H := Nat.ceil_lt_add_one (show 0≤8*(k:ℝ)*Real.log k by positivity [Real.log_nonneg h₁])
  unfold waringDiminishingOrder
  push_cast
  linarith

/-- Choice of the number of boxes makes the lost fraction at most the inverse eighth power. -/
theorem waringDiminishingOrder_decay {k : ℕ} (hk : 3≤k) :
    (1-1/(k:ℝ))^(waringDiminishingOrder k) ≤ ((k:ℝ)^8)⁻¹ := by
  let m := waringDiminishingOrder k
  have hk' : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
  have hk0 : (0:ℝ)<k := by linarith
  have hr : 0≤1-1/(k:ℝ) := sub_nonneg.mpr ((div_le_one hk0).mpr hk'.le)
  have hbase : 1-1/(k:ℝ) ≤ exp (-(1/(k:ℝ))) := by linarith [Real.add_one_le_exp (-(1/(k:ℝ)))]
  have hm : 8*(k:ℝ)*log k≤m := Nat.le_ceil _
  calc
    _ ≤ (exp (-(1/(k:ℝ))))^m := pow_le_pow_left₀ hr hbase m
    _ = exp ((m:ℝ)*(-(1/(k:ℝ)))) := (Real.exp_nat_mul _ _).symm
    _ ≤ exp (-(8*log k)) := by apply Real.exp_le_exp.mpr; field_simp; nlinarith
    _ = _ := by rw [Real.exp_neg, show (8:ℝ)=((8:ℕ):ℝ) by norm_num, Real.exp_nat_mul,Real.exp_log hk0]

/-- The exponent in the mean-square minor-arc bound is strictly below the major-arc exponent. -/
theorem waringDiminishingOrder_saving {k : ℕ} (hk : 3≤k) :
    (4*k:ℝ)*(1-1/(1600*(k:ℝ)^2*log k)) <
      ((4*k-k:ℕ):ℝ)+(k:ℝ)*(1-(1-1/(k:ℝ))^(waringDiminishingOrder k)) := by
  have hk' : (3:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have hlog : 0<log k := Real.log_pos (by linarith)
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hk0)
  rw [Real.log_sqrt hk0.le] at hl
  have hl' : log k≤(k:ℝ)/2 := by nlinarith [sq_nonneg (Real.sqrt k-2), Real.sq_sqrt hk0.le]
  have hk5 : (3:ℝ)^5 ≤ (k:ℝ)^5 := pow_le_pow_left₀ (by norm_num) hk' _
  have hx : 400*log k < (k:ℝ)^6 := by
    nlinarith [mul_le_mul_of_nonneg_right hk5 hk0.le]
  have hdec := waringDiminishingOrder_decay hk
  have hpow : (1-1/(k:ℝ))^(waringDiminishingOrder k) < 1/(400*(k:ℝ)^2*log k) := by
    apply hdec.trans_lt
    rw [inv_eq_one_div]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [mul_lt_mul_of_pos_right hx (sq_pos_of_pos hk0)]
  rw [Nat.cast_sub (by omega : k≤4*k), Nat.cast_mul, Nat.cast_ofNat]
  have he : 4*(k:ℝ)*(1-1/(1600*(k:ℝ)^2*log k)) =
      4*(k:ℝ)-(k:ℝ)*(1/(400*(k:ℝ)^2*log k)) := by field_simp; ring
  rw [he]
  nlinarith only [mul_lt_mul_of_pos_left hpow hk0]

end AnalyticNumberTheory.AdditiveNumberTheory
