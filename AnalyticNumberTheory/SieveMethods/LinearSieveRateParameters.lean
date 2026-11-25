import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Parameters for a quantitative linear sieve

Writing log log y as the twentieth power of v allows the cutoff estimates
to use integer powers. The chosen number of recursive prime pairs is the
integer part of 20 log v.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

private theorem log_three_rate : log 3 ≤ 11/10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3)).2
  have H := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤11/10) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at H
  linarith

private theorem log_contraction_rate : log (74/100) ≤ -3/10 := by
  have he : exp (3:ℝ) ≤ (2.72:ℝ)^3 := by
    rw [show (3:ℝ)=(3:ℕ)*1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  have h : (74/100:ℝ)^10 ≤ exp (-3) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (exp_pos 3)]
    exact he.trans (by norm_num)
  have hh := Real.log_le_log (by norm_num : 0<(74/100:ℝ)^10) h
  rw [Real.log_pow, Real.log_exp] at hh
  norm_num at hh
  linarith

/-- Quantitative decay and retained level after floor(20 log v) pairs. -/
theorem linearSieve_rate_depth {v : ℝ} (hv : 1≤v) :
    let m := ⌊20*log v⌋₊
    (m:ℝ)≤20*v ∧ (3:ℝ)^m≤v^22 ∧ (74/100:ℝ)^m≤2/v^6 := by
  intro m
  have vp : 0<v := by linarith
  have hl := Real.log_nonneg hv
  have hm : (m:ℝ)≤20*log v := Nat.floor_le (by positivity)
  have hm' : 20*log v ≤ (m:ℝ)+1 := (Nat.lt_floor_add_one _).le
  refine ⟨hm.trans (mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos vp]) (by norm_num)), ?_, ?_⟩
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).1
    rw [Real.log_pow,Real.log_pow]
    have h := mul_le_mul hm log_three_rate (Real.log_nonneg (by norm_num)) (by positivity)
    push_cast
    linarith
  · apply (le_div_iff₀ (by positivity : 0<v^6)).2
    have h1 : (74/100:ℝ)^m*v^6*(74/100) ≤ 1 := by
      apply (Real.log_le_log_iff (by positivity) (by norm_num)).1
      rw [Real.log_mul (by positivity) (by norm_num),Real.log_mul (by positivity) (by positivity),
        Real.log_pow,Real.log_pow,Real.log_one]
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left log_contraction_rate (Nat.cast_nonneg (α:=ℝ) m),
        log_contraction_rate,hm']
    linarith

/-- A polynomial times the short-branch exponential is bounded by the
sixth inverse power of v. The fixed coefficient is allowed to be large. -/
theorem linearSieve_rate_short {K v u r : ℝ} (hK : 0≤K) (hv : 1≤v)
    (hr : 0≤r) (hr' : r≤v^23) (hur : v^23≤u*r) :
    let m := ⌊20*log v⌋₊
    ((2*m : ℕ):ℝ)*(K*r)^2*exp (-(u*r/3^m)) ≤ (40*K^2*(Nat.factorial 53:ℝ))/v^6 := by
  intro m
  obtain ⟨hm,h3,_⟩ := linearSieve_rate_depth hv
  have vp : 0<v := by linarith
  have hcut : v≤u*r/3^m := by
    apply (le_div_iff₀ (by positivity)).2
    apply (mul_le_mul_of_nonneg_left h3 vp.le).trans
    exact (show v*v^22=v^23 by ring).le.trans hur
  have hp := Real.pow_div_factorial_le_exp v vp.le 53
  have hdec : v^53*exp (-v) ≤ (Nat.factorial 53:ℝ) := by
    rw [Real.exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    exact (div_le_iff₀ (by positivity)).mp hp |>.trans_eq (mul_comm ..)
  calc _ ≤ (40*v)*(K*v^23)^2*exp (-v) := by
          gcongr
          · push_cast; linarith
       _ ≤ _ := by
          apply (le_div_iff₀ (by positivity)).2
          convert mul_le_mul_of_nonneg_left hdec (show 0≤40*K^2 by positivity) using 1 <;> ring

end AnalyticNumberTheory.SieveMethods
