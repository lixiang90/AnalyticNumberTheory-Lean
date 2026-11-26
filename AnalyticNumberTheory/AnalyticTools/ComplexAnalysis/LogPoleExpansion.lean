import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalPoleIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Horizontal integrals of finite logarithmic pole expansions -/

noncomputable section

open Complex Set Finset MeasureTheory

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Integrating a uniform error in a finite pole expansion costs the length of
the segment. The endpoint logarithms use the principal branch on the slit plane. -/
theorem norm_integral_sub_horizontal_log_increments_le {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    {a b t M : ℝ} (hab : a ≤ b)
    (hcut : ∀ n ∈ S, ∀ x ∈ Icc a b, (x : ℂ)+(t : ℂ)*I-ρ n ∈ slitPlane)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b))
    (hM : ∀ x ∈ Icc a b, ‖f x-∑ n ∈ S, 1/((x : ℂ)+(t : ℂ)*I-ρ n)‖ ≤ M) :
    ‖(∫ x in a..b, f x) - ((∑ n ∈ S, Complex.log ((b : ℂ)+(t : ℂ)*I-ρ n)) -
      ∑ n ∈ S, Complex.log ((a : ℂ)+(t : ℂ)*I-ρ n))‖ ≤ M*(b-a) := by
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let A (x : ℝ) := ∑ n ∈ S, 1/(p x-ρ n)
  let Q (x : ℝ) := ∑ n ∈ S, Complex.log (p x-ρ n)
  have hc : ContinuousOn A (Icc a b) := by
    apply continuousOn_finsetSum
    intro n hn
    apply continuousOn_const.div ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
    exact fun x hx => slitPlane_ne_zero (hcut n hn x hx)
  have hd (x : ℝ) (hx : x ∈ uIcc a b) : HasDerivAt Q (A x) x := by
    rw [uIcc_of_le hab] at hx
    apply HasDerivAt.fun_sum
    intro n hn
    have hh := (((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ)*I)).sub_const (ρ n)).clog (hcut n hn x hx)
    exact hh.comp_ofReal.congr_deriv (by simp [p])
  have hi : IntervalIntegrable A volume a b := hc.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := M)
    (f := fun x => f x-A x) (fun x hx => by
      rw [uIoc_of_le hab] at hx
      exact hM x (Ioc_subset_Icc_self hx))
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc hab) hi,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

/-- A principal logarithm in the annulus 1/L ≤ |z| ≤ 3 has norm at most
(2+π) log L for log L ≥ 1. -/
theorem norm_log_le_of_inv_le_norm_le_three {z : ℂ} {L : ℝ} (hL : 0 < L)
    (hlog : 1 ≤ Real.log L) (hlo : L⁻¹ ≤ ‖z‖) (hhi : ‖z‖ ≤ 3) :
    ‖Complex.log z‖ ≤ (2+Real.pi)*Real.log L := by
  have hz := (inv_pos.mpr hL).trans_le hlo
  have hl := Real.log_le_log (inv_pos.mpr hL) hlo
  rw [Real.log_inv] at hl
  have hu := Real.log_le_sub_one_of_pos hz
  have hre : |(Complex.log z).re| ≤ 2*Real.log L := by
    rw [Complex.log_re]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have him : |(Complex.log z).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact abs_le.mpr ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  linarith only [hre, him, le_mul_of_one_le_right Real.pi_pos.le hlog]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
