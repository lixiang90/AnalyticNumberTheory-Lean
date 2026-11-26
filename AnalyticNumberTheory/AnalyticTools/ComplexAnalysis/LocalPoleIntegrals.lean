import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalPoleIntegrals

/-! # Integrating a local pole expansion from a line of zeros -/

noncomputable section

open Complex Finset Set MeasureTheory
open scoped Interval

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- If a complex function is within M of a finite pole sum from the line Re(ρ)=c,
its argument integral costs at most π per pole. Its real-part integral, weighted
by x−c, costs at most b−c per pole. -/
theorem local_pole_integral_bounds {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    {c b t M : ℝ} (hcb : c ≤ b) (hc : ∀ n ∈ S, (ρ n).re = c) (ht : ∀ n ∈ S, t ≠ (ρ n).im)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc c b))
    (hM : ∀ x ∈ Icc c b, ‖f x - ∑ n ∈ S, 1/((x : ℂ)+(t : ℂ)*I-ρ n)‖ ≤ M) :
    |∫ x in c..b, (f x).im| ≤ M*(b-c) + Real.pi*S.card ∧
      |∫ x in c..b, (x-c)*(f x).re| ≤ ((b-c)*M+S.card)*(b-c) := by
  let P (x : ℝ) := ∑ n ∈ S, 1/((x : ℂ)+(t : ℂ)*I-ρ n)
  have hp : Continuous P := continuous_finsetSum _ (fun n hn => continuous_horizontal_pole (ρ n) t (ht n hn))
  have hδ := sub_nonneg.mpr hcb
  have hi : |∫ x in c..b, (f x).im - (P x).im| ≤ M*(b-c) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := b)
      (C := M) (f := fun x => (f x).im - (P x).im) (fun x hx => by
        rw [uIoc_of_le hcb] at hx
        change |(f x-P x).im| ≤ M
        exact (Complex.abs_im_le_norm _).trans (hM x (Ioc_subset_Icc_self hx)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hδ] using h
  have hfi : IntervalIntegrable (fun x => (f x).im) volume c b :=
    (Complex.continuous_im.comp_continuousOn hf).intervalIntegrable_of_Icc hcb
  have hpi : IntervalIntegrable (fun x => (P x).im) volume c b :=
    (Complex.continuous_im.comp hp).intervalIntegrable c b
  rw [intervalIntegral.integral_sub hfi hpi] at hi
  constructor
  · have hP := abs_integral_im_horizontal_poles_le S ρ c b t ht
    change |∫ x in c..b, (P x).im| ≤ _ at hP
    have htri := abs_add_le ((∫ x in c..b, (f x).im) - ∫ x in c..b, (P x).im) (∫ x in c..b, (P x).im)
    rw [sub_add_cancel] at htri
    linarith
  · have hbound (x : ℝ) (hx : x ∈ Icc c b) : |(x-c)*(f x).re| ≤ (b-c)*M+S.card := by
      have hx₀ := sub_nonneg.mpr hx.1
      have hres : |(x-c)*(f x-P x).re| ≤ (b-c)*M := by
        rw [abs_mul, abs_of_nonneg hx₀]
        exact mul_le_mul (sub_le_sub_right hx.2 _) ((Complex.abs_re_le_norm _).trans (hM x hx))
          (abs_nonneg _) hδ
      have hpol : |(x-c)*(P x).re| ≤ S.card := by
        dsimp only [P]
        rw [Complex.re_sum, mul_sum]
        refine (Finset.abs_sum_le_sum_abs ..).trans ?_
        calc
          _ ≤ ∑ _n ∈ S, (1 : ℝ) := sum_le_sum (fun n hn => by
            simpa only [hc n hn] using abs_displacement_mul_re_horizontal_pole_le (ρ n) x t)
          _ = _ := by simp
      rw [show (x-c)*(f x).re = (x-c)*(f x-P x).re + (x-c)*(P x).re by rw [Complex.sub_re]; ring]
      exact (abs_add_le ..).trans (add_le_add hres hpol)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := b)
      (C := (b-c)*M+S.card) (f := fun x => (x-c)*(f x).re) (fun x hx => by
        rw [uIoc_of_le hcb] at hx
        exact hbound x (Ioc_subset_Icc_self hx))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hδ] using h

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
