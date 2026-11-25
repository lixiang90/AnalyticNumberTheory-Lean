import AnalyticNumberTheory.DirichletSeries.RieszKernelBounds
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalLineShift
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Shifting the Riesz kernel past a zero of an entire function -/
noncomputable section
open Complex Real Filter Finset MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletSeries

private def trailingFactors (w : ℂ) := ∏ j ∈ range 6, (w+(j+1:ℕ))
private theorem factor_denom (w : ℂ) : rieszDenom 6 w=w*trailingFactors w := by
  rw [rieszDenom,Finset.prod_range_succ',trailingFactors]
  simp only [Nat.cast_zero,add_zero,mul_comm]

private theorem tail_bound {G : ℂ → ℂ} {a Y C U : ℝ}
    (hY : 1≤Y) (hC : 0≤C)
    (hbound : ∀ x ∈ Set.Icc a 2, ∀ t : ℝ, U≤|t| → ‖G ((x:ℂ)+t*I)‖ ≤ C*|t|^2)
    (x : ℝ) (hx : x∈Set.Icc a 2) (t : ℝ) (ht : max 1 U≤|t|) :
      ‖G ((x:ℂ)+t*I)*(Y:ℂ)^((x:ℂ)+t*I)/rieszDenom 6 ((x:ℂ)+t*I)‖ ≤ (2*C*Y^2)/(1+t^2) := by
    have hY₀ := zero_lt_one.trans_le hY
    let w : ℂ := (x:ℂ)+t*I
    have ht₁ := (le_max_left 1 U).trans ht
    have ht₀ : 0 < |t| := lt_of_lt_of_le zero_lt_one ht₁
    have him : w.im=t := by simp [w]
    have hr : w.re=x := by simp [w]
    have hpow : ‖(Y:ℂ)^w‖ ≤ Y^2 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY₀,hr,←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hY (by simpa using hx.2)
    have hden := im_pow_le_rieszDenom_norm 6 w
    rw [him] at hden
    have hg := hbound x hx t ((le_max_right 1 U).trans ht)
    change ‖G w‖ ≤ _ at hg
    change ‖G w*(Y:ℂ)^w/rieszDenom 6 w‖ ≤ _
    rw [norm_div,norm_mul]
    calc _ ≤ (C*|t|^2*Y^2)/|t|^7 :=
               div_le_div₀ (by positivity) (mul_le_mul hg hpow (norm_nonneg _) (by positivity))
                 (pow_pos ht₀ _) hden
         _ = C*Y^2*(|t|^2/|t|^7) := by ring
         _ ≤ C*Y^2*(2/(1+|t|^2)) := by
               apply mul_le_mul_of_nonneg_left _ (by positivity)
               rw [div_le_div_iff₀ (pow_pos ht₀ _) (by positivity)]
               nlinarith only [pow_le_pow_right₀ ht₁ (show 2≤7 by decide),
                 pow_le_pow_right₀ ht₁ (show 4≤7 by decide)]
         _ = _ := by rw [sq_abs];ring

set_option maxHeartbeats 650000 in
/-- At a zero of an entire function the pole at the origin is removable.
Quadratic growth in the strip suffices to shift the sixth-order Riesz kernel
from real part two to any line strictly between minus one half and zero. -/
theorem riesz_six_shift_at_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G) (h₀ : G 0=0)
    {a Y C U : ℝ} (ha : -(1/2:ℝ)<a) (ha' : a<0) (hY : 1≤Y) (hC : 0≤C)
    (hbound : ∀ x ∈ Set.Icc a 2, ∀ t : ℝ, U≤|t| →
      ‖G ((x:ℂ)+t*I)‖ ≤ C*|t|^2) :
    let F := fun w : ℂ => G w*(Y:ℂ)^w/rieszDenom 6 w
    (∫ t : ℝ, F (2+t*I)) = ∫ t : ℝ, F ((a:ℂ)+t*I) := by
  intro F
  let R := fun w : ℂ => dslope G 0 w*(Y:ℂ)^w/trailingFactors w
  have hY₀ : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hYc : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY₀.ne'
  have hRF (w : ℂ) (hw : w≠0) : R w=F w := by
    have he := sub_smul_dslope G 0 w
    rw [sub_zero,smul_eq_mul,h₀,sub_zero] at he
    dsimp only [R,F]
    rw [factor_denom,←he]
    by_cases hd : trailingFactors w=0
    · simp [hd]
    · field_simp
  have hdiff : DifferentiableOn ℂ R {w : ℂ | w.re∈Set.Icc a 2} := by
    intro w hw
    have hden : trailingFactors w≠0 := by
      apply prod_ne_zero_iff.mpr
      intro j _ he
      have h := congrArg Complex.re he
      simp only [add_re,natCast_re,Nat.cast_add,Nat.cast_one,one_re,zero_re] at h
      linarith only [hw.1,ha,h,Nat.cast_nonneg (α:=ℝ) j]
    have hd : DifferentiableAt ℂ trailingFactors w := by unfold trailingFactors;fun_prop
    have hpow := (differentiableAt_id (x:=w)).const_cpow (Or.inl hYc)
    exact ((((hG.analyticAt w).dslope 0).differentiableAt.mul hpow).div hd hden).differentiableWithinAt
  have htail (x : ℝ) (hx : x∈Set.Icc a 2) (t : ℝ) (ht : max 1 U≤|t|) :
      ‖R ((x:ℂ)+t*I)‖ ≤ (2*C*Y^2)/(1+t^2) := by
    have hw : (x:ℂ)+t*I≠0 := by
      intro he
      have ht' : t=0 := by simpa using congrArg Complex.im he
      rw [ht',abs_zero] at ht
      linarith only [ht,le_max_left 1 U]
    rw [hRF _ hw]
    exact tail_bound hY hC hbound x hx t ht
  have shift := integral_verticalLine_eq_of_strip_tail (F:=R) (a:=a) (b:=2) (T:=max 1 U) (by linarith : a≤2) hdiff
    (by positivity : 0≤2*C*Y^2) htail
  have hline (x : ℝ) (hx : x≠0) :
      (∫ t : ℝ, R ((x:ℂ)+t*I)) = ∫ t : ℝ, F ((x:ℂ)+t*I) := by
    apply integral_congr_ae
    filter_upwards with t
    exact hRF _ (fun he => hx (by simpa using congrArg Complex.re he))
  have h2 := hline 2 (by norm_num)
  have h := h2.symm.trans (shift.symm.trans (hline a ha'.ne))
  simpa only [Complex.ofReal_ofNat] using h

end AnalyticNumberTheory.DirichletSeries
