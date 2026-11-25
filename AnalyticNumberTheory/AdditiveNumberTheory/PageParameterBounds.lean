import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Numerical parameters for the effective Page major arcs

The elementary estimates here keep every coefficient in terms of the chosen
logarithmic power, the supplied analytic bounds, and factorials.
-/

noncomputable section

open Real

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- For a polylogarithmic major-arc cutoff the exceptional arithmetic weight
saves two fifths of a logarithm, with an explicit coefficient. -/
theorem page_log_weight_saving {L : ℝ} (hL : 1≤L) {M : ℕ} (hM : 1≤M)
    (B : ℕ) (hMB : (M:ℝ)≤L^B) :
    (1+log M)^2*log ((M:ℝ)+2)^3/sqrt (L/2) ≤
      2*(2+50*(B:ℝ))^5/L^(2/5:ℝ) := by
  have hL0 : 0<L := by linarith
  have hmr : (1:ℝ)≤M := by exact_mod_cast hM
  have hml : 0≤log M := log_nonneg hmr
  let u := L^(1/50:ℝ)
  have hu : 1≤u := Real.one_le_rpow hL (by norm_num)
  have hlogL : log L≤50*u := by
    linarith [Real.log_le_rpow_div hL0.le (by norm_num : 0<(1/50:ℝ))]
  have hl := log_le_log (by linarith : 0<(M:ℝ)) hMB
  rw [Real.log_pow] at hl
  have hlogM : log M≤(B:ℝ)*(50*u) := hl.trans (mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg _))
  let V := (2+50*(B:ℝ))*u
  have hu₁ : 1+log M≤V := by dsimp [V]; linarith
  have hu₂ : log ((M:ℝ)+2)≤V := by
    have h := log_le_log (by positivity : 0<(M:ℝ)+2) (by linarith : (M:ℝ)+2≤3*M)
    rw [log_mul (by norm_num) (by linarith : (M:ℝ)≠0)] at h
    dsimp [V]
    linarith [log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))]
  have hmul := mul_le_mul (pow_le_pow_left₀ (by linarith : 0≤1+log M) hu₁ 2)
    (pow_le_pow_left₀ (log_nonneg (by linarith : 1≤(M:ℝ)+2)) hu₂ 3)
    (pow_nonneg (log_nonneg (by linarith)) 3) (sq_nonneg V)
  have hV : V^2*V^3=(2+50*(B:ℝ))^5*L^(1/10:ℝ) := by
    rw [←pow_add,mul_pow]
    dsimp only [u]
    rw [←Real.rpow_mul_natCast hL0.le]
    norm_num
  have hs : sqrt L≤2*sqrt (L/2) := by
    nlinarith [Real.sq_sqrt hL0.le,Real.sq_sqrt (show 0≤L/2 by linarith),Real.sqrt_nonneg L,Real.sqrt_nonneg (L/2)]
  have hpow : L^(1/10:ℝ)*L^(2/5:ℝ)=sqrt L := by
    rw [←Real.rpow_add hL0,Real.sqrt_eq_rpow]; norm_num
  apply (div_le_div_iff₀ (sqrt_pos.mpr (by linarith)) (rpow_pos_of_pos hL0 _)).2
  calc _ ≤ (V^2*V^3)*L^(2/5:ℝ) := mul_le_mul_of_nonneg_right hmul (by positivity)
       _ = (2+50*(B:ℝ))^5*sqrt L := by rw [hV,mul_assoc,hpow]
       _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hs (show 0≤(2+50*(B:ℝ))^5 by positivity)]

/-- An elementary quantitative bound for the exponential tail, from the
`k`-th term of the power series for the exponential. -/
theorem pow_mul_exp_neg_le_factorial {u b : ℝ} (hu : 0≤u) (hb : 0<b) (k : ℕ) :
    u^k*exp (-(b*u))≤(k.factorial:ℝ)/b^k := by
  have hf : 0<(k.factorial:ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (b*u) (mul_nonneg hb.le hu) k)
  rw [mul_pow] at h
  rw [Real.exp_neg,←div_eq_mul_inv,div_le_div_iff₀ (Real.exp_pos _) (pow_pos hb _)]
  linarith only [h,mul_comm (b^k) (u^k),mul_comm (exp (b*u)) (k.factorial:ℝ)]

/-- Any prescribed logarithmic power is absorbed by the Page exponential,
with explicit dependence on the exponential decay rate. -/
theorem page_sqrt_exponential_saving {L b : ℝ} (hL : 0≤L) (hb : 0<b) (k : ℕ) :
    L^k*exp (-(b*sqrt (L/2)))≤2^k*((2*k).factorial:ℝ)/b^(2*k) := by
  have h := pow_mul_exp_neg_le_factorial (sqrt_nonneg (L/2)) hb (2*k)
  have he : L^k=2^k*sqrt (L/2)^(2*k) := by
    rw [pow_mul,Real.sq_sqrt (by linarith),←mul_pow]; congr 1; ring
  rw [he,mul_assoc]
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0≤(2:ℝ)^k)).trans_eq (by ring)

/-- Explicit coefficient for the maximum of the elementary small-cutoff
term and the Page exponential error. -/
def pageLogSavingConstant (A b : ℝ) (k : ℕ) : ℝ :=
  max (7*(2:ℝ)^k*k.factorial) (A*2^k*((2*k).factorial:ℝ)/b^(2*k))

/-- At the choice `Y = √x`, both partial-sum errors save any prescribed
logarithmic power with the stated coefficient. -/
theorem page_partial_error_log_saving {x A b : ℝ} (hx : 1≤x) (hA : 0≤A) (hb : 0<b) (k : ℕ) :
    max (7*sqrt x) (A*x*exp (-b*sqrt (log (sqrt x))))*(log x)^k ≤
      pageLogSavingConstant A b k*x := by
  have hx0 : 0<x := by linarith
  have hL := log_nonneg hx
  have hs := sqrt_pos.mpr hx0
  have he : exp (-(1/2*log x))=1/sqrt x := by
    rw [show 1/2*log x=log (sqrt x) by rw [Real.log_sqrt hx0.le]; ring,Real.exp_neg,Real.exp_log hs,one_div]
  have hsmall := pow_mul_exp_neg_le_factorial hL (by norm_num : 0<(1/2:ℝ)) k
  rw [he] at hsmall
  have hs' : (7*sqrt x)*(log x)^k≤(7*2^k*k.factorial)*x := by
    rw [div_pow,one_pow,div_div_eq_mul_div,div_one] at hsmall
    have hh := mul_le_mul_of_nonneg_right hsmall hx0.le
    have hr : (1/sqrt x)*x=sqrt x := by field_simp [hs.ne']; nlinarith [Real.sq_sqrt hx0.le]
    rw [mul_assoc,hr] at hh
    nlinarith only [hh]
  have hlarge := page_sqrt_exponential_saving hL hb k
  rw [Real.log_sqrt hx0.le,show log x/(2:ℝ)=log x/2 by rfl]
  rw [max_mul_of_nonneg _ _ (pow_nonneg hL k)]
  apply max_le
  · exact hs'.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hx0.le)
  · apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) hx0.le)
    calc _ = (A*x)*((log x)^k*exp (-(b*sqrt (log x/2)))) := by ring
         _ ≤ (A*x)*(2^k*((2*k).factorial:ℝ)/b^(2*k)) :=
            mul_le_mul_of_nonneg_left hlarge (mul_nonneg hA hx0.le)
         _ = _ := by ring

/-- Coefficient for an arc error saving `J` logarithms with denominators
up to `(log x)^B`. -/
def pageMajorArcLogConstant (A b : ℝ) (B J : ℕ) : ℝ :=
  9*(2*pageLogSavingConstant A b (2*B+J)+4*((2*B+J+1).factorial:ℝ))

theorem pageMajorArcLogConstant_pos (A b : ℝ) (B J : ℕ) :
    0<pageMajorArcLogConstant A b B J := by
  have h : 0<pageLogSavingConstant A b (2*B+J) :=
    (by positivity : 0<7*(2:ℝ)^(2*B+J)*(2*B+J).factorial).trans_le (le_max_left ..)
  unfold pageMajorArcLogConstant
  positivity

/-- The shared elementary polynomial bound for the pointwise arc errors
has any required logarithmic saving, without an unspecified threshold. -/
theorem page_majorArc_log_saving {x m A b : ℝ} (hx : 1≤x) (hL : 1≤log x)
    (hm : 0≤m) (hA : 0≤A) (hb : 0<b) (B J : ℕ) (hmB : m≤(log x)^B) :
    let U := max (7*sqrt x) (A*x*exp (-b*sqrt (log (sqrt x))))
    9*m^2*(2*U+4*log x)≤pageMajorArcLogConstant A b B J*x/(log x)^J := by
  intro U
  let L := log x
  let k := 2*B+J
  have hx0 : 0<x := by linarith
  have hL0 : 0<L := by dsimp [L]; linarith
  have hU : 0≤U := le_trans (by positivity) (le_max_left ..)
  have he : L^(k+1)≤(k+1).factorial*x := by
    have hh := (div_le_iff₀ (by positivity : 0<((k+1).factorial:ℝ))).mp
      (Real.pow_div_factorial_le_exp L hL0.le (k+1))
    rw [Real.exp_log hx0] at hh
    linarith only [hh,mul_comm x ((k+1).factorial:ℝ)]
  have hpartial := page_partial_error_log_saving hx hA hb k
  change U*L^k≤pageLogSavingConstant A b k*x at hpartial
  have hpow : m^2*L^J≤L^k := by
    dsimp only [k]
    rw [pow_add,mul_comm 2 B,pow_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm hmB 2) (pow_nonneg hL0.le _)
  apply (le_div_iff₀ (pow_pos hL0 J)).2
  change 9*m^2*(2*U+4*L)*L^J≤_
  calc _ = 9*((m^2*L^J)*(2*U+4*L)) := by ring
       _ ≤ 9*(L^k*(2*U+4*L)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (by positivity)) (by norm_num)
       _ = 9*(2*(U*L^k)+4*L^(k+1)) := by rw [pow_succ]; ring
       _ ≤ 9*(2*(pageLogSavingConstant A b k*x)+4*((k+1).factorial*x)) := by gcongr
       _ = _ := by dsimp [pageMajorArcLogConstant,k]; ring

end AnalyticNumberTheory.AdditiveNumberTheory
