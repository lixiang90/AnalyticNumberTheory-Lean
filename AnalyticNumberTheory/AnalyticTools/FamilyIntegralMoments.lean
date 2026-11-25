import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-! # Weighted Hölder inequalities for finite families of interval integrals -/
noncomputable section
open Finset MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools

theorem weighted_interval_cauchy {a b : ℝ} (hab : a ≤ b) {w f g : ℝ → ℝ}
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g) (hw0 : ∀ t, 0 ≤ w t) :
    (∫ t in a..b, w t*f t*g t)^2 ≤
      (∫ t in a..b, w t*(f t)^2)*(∫ t in a..b, w t*(g t)^2) := by
  let A := ∫ t in a..b, w t*(f t)^2
  let B := ∫ t in a..b, w t*f t*g t
  let C := ∫ t in a..b, w t*(g t)^2
  have h (u : ℝ) : 0 ≤ A*(u*u)+(2*B)*u+C := by
    have hn : 0 ≤ ∫ t in a..b, w t*(u*f t+g t)^2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => mul_nonneg (hw0 t) (sq_nonneg _))
    have he (t : ℝ) : w t*(u*f t+g t)^2 =
        (u*u)*(w t*(f t)^2) + (2*u)*(w t*f t*g t) + w t*(g t)^2 := by ring
    simp_rw [he] at hn
    have h₁ : Continuous fun t => (u*u)*(w t*(f t)^2) := continuous_const.mul (hw.mul (hf.pow 2))
    have h₂ : Continuous fun t => (2*u)*(w t*f t*g t) := continuous_const.mul ((hw.mul hf).mul hg)
    have h₃ : Continuous fun t => w t*(g t)^2 := hw.mul (hg.pow 2)
    rw [intervalIntegral.integral_add (f:=fun t => (u*u)*(w t*(f t)^2) + (2*u)*(w t*f t*g t)) (g:=fun t => w t*(g t)^2) ((h₁.add h₂).intervalIntegrable ..) (h₃.intervalIntegrable ..),
      intervalIntegral.integral_add (h₁.intervalIntegrable ..) (h₂.intervalIntegrable ..),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hn
    change 0 ≤ (u*u)*A + (2*u)*B + C at hn
    linarith only [hn]
  have hd := discrim_le_zero h
  unfold discrim at hd
  change B^2 ≤ A*C
  nlinarith only [hd]

/-- Cauchy–Schwarz for the sum of weighted interval integrals of a finite family. -/
theorem family_weighted_interval_cauchy {ι : Type*} (S : Finset ι) {a b : ℝ} (hab : a≤b)
    {w f g : ι → ℝ → ℝ} (hw : ∀ i∈S,Continuous (w i))
    (hf : ∀ i∈S,Continuous (f i)) (hg : ∀ i∈S,Continuous (g i))
    (hw₀ : ∀ i∈S,∀ t,0≤w i t) :
    (∑ i∈S,∫ t in a..b,w i t*f i t*g i t)^2 ≤
      (∑ i∈S,∫ t in a..b,w i t*(f i t)^2)*(∑ i∈S,∫ t in a..b,w i t*(g i t)^2) :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i hi => intervalIntegral.integral_nonneg hab (fun t _ => mul_nonneg (hw₀ i hi t) (sq_nonneg _)))
    (fun i hi => intervalIntegral.integral_nonneg hab (fun t _ => mul_nonneg (hw₀ i hi t) (sq_nonneg _)))
    (fun i hi => weighted_interval_cauchy hab (hw i hi) (hf i hi) (hg i hi) (hw₀ i hi))

/-- Weighted Hölder with exponents four, two and four over a family and an interval. -/
theorem family_weighted_interval_fourth_second {ι : Type*} (S : Finset ι) {a b : ℝ} (hab : a≤b)
    {w f g : ι → ℝ → ℝ} (hw : ∀ i∈S,Continuous (w i))
    (hf : ∀ i∈S,Continuous (f i)) (hg : ∀ i∈S,Continuous (g i))
    (hw₀ : ∀ i∈S,∀ t,0≤w i t) :
    (∑ i∈S,∫ t in a..b,w i t*f i t*g i t)^4 ≤
      (∑ i∈S,∫ t in a..b,w i t)*(∑ i∈S,∫ t in a..b,w i t*(f i t)^4)*
        (∑ i∈S,∫ t in a..b,w i t*(g i t)^2)^2 := by
  have h₁ := family_weighted_interval_cauchy S hab hw hf hg hw₀
  have h₂ := family_weighted_interval_cauchy S hab hw (f:=fun _ _ => (1:ℝ))
    (fun _ _ => continuous_const) (fun i hi => (hf i hi).pow 2) hw₀
  simp only [mul_one,one_pow,Pi.pow_apply,←pow_mul] at h₂
  have h₃ := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
  rw [mul_pow,←pow_mul] at h₃
  exact h₃.trans (mul_le_mul_of_nonneg_right h₂ (sq_nonneg _))

end AnalyticNumberTheory.AnalyticTools
