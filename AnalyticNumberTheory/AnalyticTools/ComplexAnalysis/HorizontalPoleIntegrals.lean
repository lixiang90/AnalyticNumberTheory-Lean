import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Integrating a finite sum of simple poles along a horizontal segment -/

noncomputable section

open Complex MeasureTheory Finset Set

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- The horizontal integral of the imaginary part of one simple fraction is an
arctangent difference, including on the ordinate of the pole with totalized division. -/
theorem integral_im_horizontal_pole (ρ : ℂ) (a b t : ℝ) :
    (∫ x in a..b, ((1 : ℂ) / ((x : ℂ) + (t : ℂ)*I - ρ)).im) =
      Real.arctan ((a-ρ.re)/(t-ρ.im)) - Real.arctan ((b-ρ.re)/(t-ρ.im)) := by
  let f (x : ℝ) := (t-ρ.im)/((t-ρ.im)^2 + x^2)
  have he (x : ℝ) : ((1 : ℂ) / ((x : ℂ) + (t : ℂ)*I - ρ)).im = -f (x-ρ.re) := by
    rw [one_div, Complex.inv_im, Complex.normSq_apply]
    simp [f]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_right]
  unfold f
  rw [integral_div_sq_add_sq]
  ring

/-- Each pole contributes at most π to the argument variation along a horizontal
segment. The bound is uniform in its distance from the segment. -/
theorem abs_integral_im_horizontal_pole_le (ρ : ℂ) (a b t : ℝ) :
    |∫ x in a..b, ((1 : ℂ) / ((x : ℂ) + (t : ℂ)*I - ρ)).im| ≤ Real.pi := by
  rw [integral_im_horizontal_pole]
  exact (abs_sub ..).trans ((add_le_add
    (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)
    (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)).trans_eq (by ring))

/-- A simple fraction is continuous on a horizontal line missing its pole. -/
theorem continuous_horizontal_pole (ρ : ℂ) (t : ℝ) (h : t ≠ ρ.im) :
    Continuous (fun x : ℝ => (1 : ℂ)/((x : ℂ)+(t : ℂ)*I-ρ)) := by
  have hd : Continuous (fun x : ℝ => (x : ℂ)+(t : ℂ)*I-ρ) :=
    (Complex.continuous_ofReal.add continuous_const).sub continuous_const
  apply continuous_const.div hd
  intro x hx
  apply h
  exact sub_eq_zero.mp (by simpa using congrArg Complex.im hx)

/-- On a horizontal line avoiding the ordinates, any finite sum of simple fractions
has total signed argument contribution at most π times the number of terms. -/
theorem abs_integral_im_horizontal_poles_le {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    (a b t : ℝ) (h : ∀ n ∈ S, t ≠ (ρ n).im) :
    |∫ x in a..b, (∑ n ∈ S, 1/((x : ℂ) + (t : ℂ)*I - ρ n)).im| ≤ Real.pi * S.card := by
  have hi (n : ι) (hn : n ∈ S) : Continuous (fun x : ℝ => ((1 : ℂ) / ((x : ℂ)+(t : ℂ)*I-ρ n)).im) :=
    Complex.continuous_im.comp (continuous_horizontal_pole (ρ n) t (h n hn))
  simp_rw [Complex.im_sum]
  rw [intervalIntegral.integral_finsetSum (fun n hn => (hi n hn).intervalIntegrable a b)]
  calc
    _ ≤ ∑ n ∈ S, |∫ x in a..b, ((1 : ℂ) / ((x : ℂ)+(t : ℂ)*I-ρ n)).im| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _n ∈ S, Real.pi := sum_le_sum (fun n _ => abs_integral_im_horizontal_pole_le (ρ n) a b t)
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]

/-- Multiplication by the horizontal displacement bounds the real part of a single
pole by one, including at the totalized value of the fraction at the pole. -/
theorem abs_displacement_mul_re_horizontal_pole_le (ρ : ℂ) (x t : ℝ) :
    |(x-ρ.re) * ((1 : ℂ) / ((x : ℂ) + (t : ℂ)*I - ρ)).re| ≤ 1 := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  have hr : ((x : ℂ)+(t : ℂ)*I-ρ).re = x-ρ.re := by simp
  have hi : ((x : ℂ)+(t : ℂ)*I-ρ).im = t-ρ.im := by simp
  rw [hr, hi, ← mul_div_assoc, ← sq, ← sq]
  have ha : 0 ≤ (x-ρ.re)^2 + (t-ρ.im)^2 := by positivity
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) ha)]
  rcases ha.eq_or_lt with he | he
  · rw [← he, div_zero]; norm_num
  · exact (div_le_one he).mpr (by linarith [sq_nonneg (t-ρ.im)])

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
