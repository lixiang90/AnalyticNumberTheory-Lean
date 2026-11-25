import AnalyticNumberTheory.AnalyticTools.DyadicIntegralMajorants
import Mathlib.Analysis.Complex.Basic

/-! # Summation of vertical means with the reciprocal-height weight -/
open Real MeasureTheory Set
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- For a nonnegative density whose mass on [0,u] is at most Bu, weighting
by 1/(1+t) accumulates at most one factor of log T. Only heights up to 2T
and at least two are needed in the hypothesis. -/
theorem integral_div_one_add_of_linear_mean {f : ℝ → ℝ} (hf : Continuous f)
    (hf₀ : ∀ t, 0 ≤ f t) {T B : ℝ} (hT : 2 ≤ T) (hB : 0 ≤ B)
    (hmean : ∀ u : ℝ, 2 ≤ u → u ≤ 2*T → (∫ t in (0:ℝ)..u, f t) ≤ B*u) :
    (∫ t in (0:ℝ)..T, f t/(1+|t|)) ≤ 2*B*(2 + Real.log T / Real.log 2) := by
  let F (t : ℝ) := f t/(1+|t|)
  have cF : Continuous F := hf.div (continuous_const.add continuous_abs) (fun t => by positivity)
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near (by linarith : 1≤T) (by norm_num : (1:ℝ)<2)
  have hsum (j : ℕ) (hj : j≤k+1) : (∫t in (0:ℝ)..(2:ℝ)^j,F t) ≤ 2*B*(j+1) := by
    induction j with
    | zero =>
      simp only [pow_zero,Nat.cast_zero,zero_add,mul_one]
      have hsmall := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ)≤1)
        (cF.intervalIntegrable ..) (hf.intervalIntegrable ..)
        (fun t ht => div_le_self (hf₀ t) (by linarith [abs_nonneg t] : 1≤1+|t|))
      have hm := intervalIntegral.integral_mono_interval (μ:=volume) (a:=(0:ℝ)) le_rfl (by norm_num : (0:ℝ)≤1)
        (by norm_num : (1:ℝ)≤2) (Filter.Eventually.of_forall hf₀) (hf.intervalIntegrable ..)
      exact (hsmall.trans (hm.trans (hmean 2 le_rfl (by linarith)))).trans_eq (mul_comm ..)
    | succ j ih =>
      let u := (2:ℝ)^j
      have hu : 1≤u := one_le_pow₀ (by norm_num)
      have hu₀ : 0<u := by linarith
      have huT : u≤T := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j≤k by omega)).trans hk
      have hu₂ : u≤2*u := by linarith
      have h₂ : (2:ℝ)^(j+1)=2*u := by dsimp [u];ring
      have hblock := intervalIntegral.integral_mono_on (μ:=volume) hu₂ (cF.intervalIntegrable ..)
        ((hf.div_const u).intervalIntegrable ..)
        (fun t ht => div_le_div_of_nonneg_left (hf₀ t) hu₀ (by linarith [ht.1,le_abs_self t] : u≤1+|t|))
      change (∫t in u..2*u,F t) ≤ ∫t in u..2*u,f t/u at hblock
      rw [intervalIntegral.integral_div] at hblock
      have hbound := intervalIntegral.integral_mono_interval (μ:=volume) (c:=(0:ℝ)) (a:=u) hu₀.le hu₂ le_rfl
        (Filter.Eventually.of_forall hf₀) (hf.intervalIntegrable ..)
      have hfin : (∫t in u..2*u,F t)≤2*B := hblock.trans ((div_le_iff₀ hu₀).mpr
        ((hbound.trans (hmean (2*u) (by linarith) (by linarith))).trans_eq (by ring)))
      rw [h₂,←intervalIntegral.integral_add_adjacent_intervals (a:=0) (b:=u) (c:=2*u)
        (cF.intervalIntegrable ..) (cF.intervalIntegrable ..)]
      push_cast
      linarith only [ih (by omega),hfin]
  have hh : (∫t in (0:ℝ)..T,F t) ≤ ∫t in (0:ℝ)..(2:ℝ)^(k+1),F t :=
    intervalIntegral.integral_mono_interval (μ:=volume) (a:=(0:ℝ)) le_rfl (by linarith) hk'.le
      (Filter.Eventually.of_forall (fun t => div_nonneg (hf₀ t) (by positivity))) (cF.intervalIntegrable ..)
  have hj := Real.log_le_log (by positivity) hk
  rw [Real.log_pow] at hj
  have hkl := (le_div_iff₀ (Real.log_pos one_lt_two)).mpr hj
  apply (hh.trans (hsum _ le_rfl)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  push_cast
  linarith


/-- Folding both signs of the height onto a single interval. -/
theorem integral_symmetric_fold (f : ℝ → ℝ) (hf : Continuous f) (u : ℝ) :
    (∫ t in (0:ℝ)..u, f t + f (-t)) = ∫ t in -u..u, f t := by
  have hneg : Continuous (fun t => f (-t)) := hf.comp continuous_neg
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..)
    (hneg.intervalIntegrable ..),intervalIntegral.integral_comp_neg,
    neg_zero,add_comm,intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)]

/-- A symmetric vertical mean of size Bu gives a reciprocal-height integral
on the critical line of size B(1+log T). The weight is the actual Perron denominator. -/
theorem critical_perron_integral_of_linear_mean {f : ℝ → ℝ} (hf : Continuous f)
    (hf₀ : ∀ t, 0 ≤ f t) {T B : ℝ} (hT : 2≤T) (hB : 0≤B)
    (hmean : ∀ u : ℝ, 2≤u → u≤2*T → (∫ t in -u..u, f t) ≤ B*u) :
    (∫ t in -T..T, f t/‖(1/2:ℂ)+(t:ℂ)*Complex.I‖) ≤ 6*B*(2+Real.log T/Real.log 2) := by
  let d (t : ℝ) := ‖(1/2:ℂ)+(t:ℂ)*Complex.I‖
  have hd (t) : 1/2 ≤ d t := by
    have h := Complex.abs_re_le_norm ((1/2:ℂ)+(t:ℂ)*Complex.I)
    simpa [d] using h
  have ht (t) : |t| ≤ d t := by
    simpa [d] using Complex.abs_im_le_norm ((1/2:ℂ)+(t:ℂ)*Complex.I)
  have hden : Continuous d := by dsimp [d];fun_prop
  have hF : Continuous (fun t => f t/(1+|t|)) :=
    hf.div (continuous_const.add continuous_abs) (fun t => by positivity)
  have H := integral_div_one_add_of_linear_mean (f:=fun t => f t + f (-t)) (hf.add (hf.comp continuous_neg))
    (fun t => add_nonneg (hf₀ _) (hf₀ _)) hT hB (fun u hu huT => by
      rw [integral_symmetric_fold f hf]; exact hmean u hu huT)
  have heq : (∫t in (0:ℝ)..T,(f t+f (-t))/(1+|t|)) = ∫t in -T..T, f t/(1+|t|) := by
    rw [←integral_symmetric_fold _ hF]
    simp only [abs_neg,add_div]
  change (∫t in (0:ℝ)..T,(f t+f (-t))/(1+|t|)) ≤ _ at H
  rw [heq] at H
  have hp (t : ℝ) : f t/d t ≤ 3*(f t/(1+|t|)) := by
    have hpos : 0<d t := by linarith [hd t]
    have hsum : 1+|t| ≤ 3*d t := by linarith [ht t,hd t]
    rw [mul_div_assoc',div_le_div_iff₀ hpos (by positivity)]
    exact (mul_le_mul_of_nonneg_left hsum (hf₀ t)).trans_eq (by ring)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (by linarith : -T≤T)
    ((hf.div hden (fun t => by linarith [hd t])).intervalIntegrable ..)
    ((continuous_const.mul hF).intervalIntegrable ..) (fun t _ => hp t)
  change (∫t in -T..T,f t/d t) ≤ ∫t in -T..T,3*(f t/(1+|t|)) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq (by ring))

end AnalyticNumberTheory.AnalyticTools
