import AnalyticNumberTheory.AnalyticTools.FamilyIntegralMoments
import AnalyticNumberTheory.RiemannZeta.FourthMomentLog
import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Critical-line moment estimates for Ingham's density theorem

The fourth moment of zeta and second moment of a finite Möbius polynomial are
used on a common symmetric ordinate interval. A weighted form of Hölder's
inequality keeps the mass of the zero-detecting kernels in the estimate.
-/

noncomputable section
open Complex Real Finset MeasureTheory
open scoped ArithmeticFunction.Moebius ComplexConjugate
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Weighted Hölder with exponents 4, 2, 4, in a form without fractional powers. -/
theorem weighted_interval_fourth_second {a b : ℝ} (hab : a ≤ b) {w f g : ℝ → ℝ}
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g) (hw0 : ∀ t, 0 ≤ w t) :
    (∫ t in a..b, w t*f t*g t)^4 ≤ (∫ t in a..b, w t) *
      (∫ t in a..b, w t*(f t)^4)*(∫ t in a..b, w t*(g t)^2)^2 := by
  have h₁ := AnalyticTools.weighted_interval_cauchy hab hw hf hg hw0
  have h₂ := AnalyticTools.weighted_interval_cauchy hab hw (continuous_const (y:=(1:ℝ))) (hf.pow 2) hw0
  simp only [mul_one,one_pow,Pi.pow_apply,← pow_mul] at h₂
  have h₃ := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
  rw [mul_pow, ←pow_mul] at h₃
  exact h₃.trans (mul_le_mul_of_nonneg_right h₂ (sq_nonneg _))

/-- Fourth moment on both sides of the critical line, for the ordinate window
needed after translating a zero detector at height between `X` and `2X`. -/
theorem ingham_zeta_fourth_mean :
    ∃ C > (0:ℝ), ∀ X : ℕ, 1 ≤ X →
      (∫ t in (-(6*(X:ℝ)))..6*X, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) ≤
        C*X*(1+Real.log X)^4 := by
  obtain ⟨D,hD,hd⟩ := fourthMoment_riemannZeta_log_le
  let f (t : ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖^4
  have hf : Continuous f := continuous_riemannZeta_half.norm.pow 4
  let B := ∫ t in (0:ℝ)..1, f t
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => pow_nonneg (norm_nonneg _) _)
  refine ⟨2*(B+6*6^4*D),by positivity,?_⟩
  intro X hX
  let T := 6*(X:ℝ)
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0:ℝ)<X := by linarith
  have hT : 1 ≤ T := by dsimp [T]; linarith
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hXr]
  have hlog : 1+Real.log T ≤ 6*(1+Real.log X) := by
    dsimp [T]; rw [Real.log_mul (by norm_num) hX0.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<6)]
  have h₁ := (hd T hT).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (by linarith [Real.log_nonneg hT]) hlog 4) (by positivity))
  have hs := intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable («μ»:=volume) 0 1) (hf.intervalIntegrable («μ»:=volume) 1 T)
  have hs' := intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable («μ»:=volume) (-T) 0) (hf.intervalIntegrable («μ»:=volume) 0 T)
  have he (t : ℝ) : f (-t) = f t := by
    have hid : (1/2:ℂ)+((-t:ℝ):ℂ)*I=conj ((1/2:ℂ)+(t:ℂ)*I) := by push_cast; simp [map_ofNat]
    dsimp only [f]; rw [hid,riemannZeta_conj,Complex.norm_conj]
  have hr := intervalIntegral.integral_comp_neg (a:=(0:ℝ)) (b:=T) f
  simp only [he,neg_zero] at hr
  have hUB : B ≤ B*((X:ℝ)*(1+Real.log X)^4) :=
    le_mul_of_one_le_right hB (one_le_mul_of_one_le_of_one_le hXr (one_le_pow₀ hL))
  change (∫ t in (1:ℝ)..T, f t) ≤ _ at h₁
  change (∫ t in -T..T, f t) ≤ _
  change B+(∫ t in (1:ℝ)..T, f t) = _ at hs
  dsimp only [T] at *
  linarith only [h₁,hs,hs',hr,hUB]

/-- The length-`X` Möbius polynomial has second moment `O(X log X)` on the same window. -/
theorem ingham_mobius_second_mean (X : ℕ) :
    (∫ t in (-(6*(X:ℝ)))..6*X, ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖^2) ≤
      (12+2*π)*X*(1+Real.log X) := by
  have h := dirichletPoly_mean_sq_symm_le (fun n => (μ n:ℂ)) X (1/2) (T:=6*(X:ℝ)) (by positivity)
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] at h
  apply h.trans
  have he : ∑ n ∈ Icc 1 X, ‖(μ n:ℂ)‖^2*(n:ℝ)^(-2*(1/2:ℝ)) ≤ 1+Real.log X := by
    apply le_trans (b:=∑ n ∈ Icc 1 X, (n:ℝ)⁻¹)
    · refine sum_le_sum fun n _ => ?_
      norm_num only [show -2*(1/2:ℝ) = -1 by norm_num, Real.rpow_neg_one]
      exact mul_le_of_le_one_left (by positivity) ((pow_le_pow_left₀ (norm_nonneg _) (norm_moebius_complex_le n) 2).trans_eq (one_pow _))
    · simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log X
  exact (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*(6*(X:ℝ))+2*Real.pi*X)).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
