import AnalyticNumberTheory.RiemannZeta.HorizontalLogMeanIdentity
import AnalyticNumberTheory.RiemannZeta.LogarithmUnderRH

/-! # The Euler-normalized logarithm along a regular horizontal segment -/

noncomputable section

open Complex Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.RiemannZeta

/-- Continuation of the Euler logarithm from 2+it along a horizontal segment.
The logarithm has a well-defined value even at a regular endpoint on the critical line. -/
def horizontalLogZeta (σ t : ℝ) : ℂ :=
  logZeta ((2 : ℂ)+(t : ℂ)*I) - ∫ x in σ..2,
    deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) / riemannZeta ((x : ℂ)+(t : ℂ)*I)

/-- At the right endpoint the horizontal logarithm equals the Euler logarithm. -/
theorem horizontalLogZeta_two (t : ℝ) :
    horizontalLogZeta 2 t = logZeta ((2 : ℂ)+(t : ℂ)*I) := by simp [horizontalLogZeta]

/-- The change of the horizontal branch on a regular subsegment equals the integral of ζ′/ζ. -/
theorem horizontalLogZeta_sub {a b t : ℝ} (hab : a ≤ b) (hb : b ≤ 2) (ht : t ≠ 0)
    (hz : ∀ x ∈ Icc a 2, riemannZeta ((x : ℂ)+(t : ℂ)*I) ≠ 0) :
    horizontalLogZeta b t - horizontalLogZeta a t =
      ∫ x in a..b, deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) / riemannZeta ((x : ℂ)+(t : ℂ)*I) := by
  have h : ContinuousOn (fun x : ℝ => deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) /
      riemannZeta ((x : ℂ)+(t : ℂ)*I)) (Icc a 2) :=
    fun x hx => (continuousAt_horizontal_zeta_logDeriv ht (hz x hx)).continuousWithinAt
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((h.mono (Icc_subset_Icc_right hb)).intervalIntegrable_of_Icc hab)
    ((h.mono (Icc_subset_Icc_left hab)).intervalIntegrable_of_Icc hb)
  unfold horizontalLogZeta
  rw [← hadd]
  abel

/-- Exponentiation of the horizontally continued logarithm recovers zeta on every
nonvanishing segment of nonzero height, including both endpoints. -/
theorem exp_horizontalLogZeta {a t : ℝ} (ha : a ≤ 2) (ht : t ≠ 0)
    (hz : ∀ x ∈ Icc a 2, riemannZeta ((x : ℂ)+(t : ℂ)*I) ≠ 0) :
    Complex.exp (horizontalLogZeta a t) = riemannZeta ((a : ℂ)+(t : ℂ)*I) := by
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let g (x : ℝ) := riemannZeta (p x)
  let D (x : ℝ) := deriv riemannZeta (p x)/g x
  let G (x : ℝ) := ∫ y in a..x, D y
  have hp : Continuous p := Complex.continuous_ofReal.add continuous_const
  have hne (x : ℝ) : p x ≠ 1 := fun he => ht (by simpa [p] using congrArg Complex.im he)
  have hA (x : ℝ) : AnalyticAt ℂ riemannZeta (p x) :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) _ (hne x)
  have hmeas : StronglyMeasurable D := by
    have h₁ : Continuous (fun x => deriv riemannZeta (p x)) :=
      continuous_iff_continuousAt.mpr (fun x => (hA x).deriv.continuousAt.comp hp.continuousAt)
    have h₂ : Continuous g :=
      continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt.comp hp.continuousAt)
    exact (h₁.measurable.div h₂.measurable).stronglyMeasurable
  have hD : ContinuousOn D (Icc a 2) :=
    fun x hx => (continuousAt_horizontal_zeta_logDeriv ht (hz x hx)).continuousWithinAt
  have hconst (x : ℝ) (hx : x ∈ uIcc a 2) :
      HasDerivAt (fun y => Complex.exp (-G y)*g y) 0 x := by
    rw [uIcc_of_le ha] at hx
    have hi : HasDerivAt G (D x) x := intervalIntegral.integral_hasDerivAt_right
      ((hD.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1)
      hmeas.stronglyMeasurableAtFilter (continuousAt_horizontal_zeta_logDeriv ht (hz x hx))
    have hg : HasDerivAt g (deriv riemannZeta (p x)) x := by
      have hh := (differentiableAt_riemannZeta (hne x)).hasDerivAt.comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ)*I))
      exact hh.comp_ofReal.congr_deriv (by simp [p])
    apply (hi.neg.cexp.mul hg).congr_deriv
    dsimp only [D]
    field_simp [show g x ≠ 0 from hz x hx]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hconst intervalIntegrable_const
  have hzero : G a = 0 := intervalIntegral.integral_same
  rw [intervalIntegral.integral_zero, hzero, neg_zero, Complex.exp_zero, one_mul] at h
  have he := sub_eq_zero.mp h.symm
  rw [horizontalLogZeta, sub_eq_add_neg, Complex.exp_add, exp_logZeta (by simp)]
  exact (mul_comm _ _).trans he

/-- Under RH the horizontal continuation agrees with the holomorphic Euler branch
at nonreal points strictly to the right of the critical line. -/
theorem horizontalLogZeta_eq_slitLogZeta (hRH : RiemannHypothesisProp) {a t : ℝ}
    (ha : 1/2 < a) (ha₂ : a ≤ 2) (ht : t ≠ 0) :
    horizontalLogZeta a t = slitLogZeta hRH ((a : ℂ)+(t : ℂ)*I) := by
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let D (x : ℝ) := deriv riemannZeta (p x)/riemannZeta (p x)
  have hD : ContinuousOn D (Icc a 2) := by
    intro x hx
    apply (continuousAt_horizontal_zeta_logDeriv ht _).continuousWithinAt
    exact riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH _ (by simpa using ha.trans_le hx.1)
  have hd (x : ℝ) (hx : x ∈ uIcc a 2) : HasDerivAt (fun y => slitLogZeta hRH (p y)) (D x) x := by
    rw [uIcc_of_le ha₂] at hx
    have hcut : p x-1 ∈ slitPlane := mem_slitPlane_iff.mpr (.inr (by simpa [p] using ht))
    have hh := (hasDerivAt_slitLogZeta hRH (by simpa [p] using ha.trans_le hx.1) hcut).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ)*I))
    exact hh.comp_ofReal.congr_deriv (by simp [D, p])
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hD.intervalIntegrable_of_Icc ha₂)
  rw [slitLogZeta_eq_logZeta hRH (by simp [p] : 1 < (p 2).re)] at h
  change logZeta (p 2)-(∫ x in a..2, D x) = slitLogZeta hRH (p a)
  rw [h]
  abel

end AnalyticNumberTheory.RiemannZeta
