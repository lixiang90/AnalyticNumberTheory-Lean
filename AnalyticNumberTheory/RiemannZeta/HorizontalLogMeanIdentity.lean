import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogModulusDerivative
import AnalyticNumberTheory.RiemannZeta.ZetaLogMean
import AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-! # The horizontal log modulus in terms of the first logarithmic derivative moment -/

noncomputable section

open Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

/-- A horizontal line away from zero ordinates has no zeta zeros at positive real part. -/
theorem riemannZeta_ne_zero_on_horizontal_of_no_ordinate {t x : ℝ} (hno : ¬ IsZeroOrdinate t)
    (hx : 0 < x) : riemannZeta ((x : ℂ)+(t : ℂ)*I) ≠ 0 := by
  rcases lt_or_ge x 1 with h | h
  · exact fun he => hno ⟨_, mem_criticalStripZeros.mpr ⟨he, by simpa using hx, by simpa using h⟩, by simp⟩
  · exact riemannZeta_ne_zero_of_one_le_re_bridge (by simpa using h)

/-- The logarithmic derivative is continuous along the horizontal line at each
regular point of nonzero height. -/
theorem continuousAt_horizontal_zeta_logDeriv {t x : ℝ} (ht : t ≠ 0)
    (hz : riemannZeta ((x : ℂ)+(t : ℂ)*I) ≠ 0) :
    ContinuousAt (fun y : ℝ => deriv riemannZeta ((y : ℂ)+(t : ℂ)*I) /
      riemannZeta ((y : ℂ)+(t : ℂ)*I)) x := by
  let z := (x : ℂ)+(t : ℂ)*I
  have hs : z ≠ 1 := fun he => ht (by simpa [z] using congrArg Complex.im he)
  have ha : AnalyticAt ℂ riemannZeta z :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) _ hs
  have hD : ContinuousAt (fun w : ℂ => deriv riemannZeta w / riemannZeta w) z :=
    ha.deriv.continuousAt.div ha.continuousAt hz
  have hp : ContinuousAt (fun y : ℝ => (y : ℂ)+(t : ℂ)*I) x := (Complex.continuous_ofReal.add continuous_const).continuousAt
  exact hD.comp (f := fun y : ℝ => (y : ℂ)+(t : ℂ)*I) hp

/-- At an ordinate away from the nontrivial zeros and the real axis, the logarithmic
derivative is continuous on the horizontal segment from one half to two. -/
theorem continuousOn_horizontal_zeta_logDeriv {t : ℝ} (ht : t ≠ 0) (hno : ¬ IsZeroOrdinate t) :
    ContinuousOn (fun x : ℝ => deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) /
      riemannZeta ((x : ℂ)+(t : ℂ)*I)) (Icc (1/2 : ℝ) 2) := by
  intro x hx
  exact (continuousAt_horizontal_zeta_logDeriv ht
    (riemannZeta_ne_zero_on_horizontal_of_no_ordinate hno (by linarith [hx.1]))).continuousWithinAt

/-- At heights missing all zeros, the horizontal mean of log |ζ| equals the endpoint
log modulus times 3/2 minus the first real-part moment of ζ′/ζ. -/
theorem horizontalLogMean_zeta_eq_real_moment {t : ℝ} (ht : t ≠ 0) (hno : ¬ IsZeroOrdinate t) :
    horizontalLogMean riemannZeta t =
      (3/2)*Real.log ‖riemannZeta ((2 : ℂ)+(t : ℂ)*I)‖ -
      ∫ x in (1/2 : ℝ)..2, (x-1/2)*(deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) /
        riemannZeta ((x : ℂ)+(t : ℂ)*I)).re := by
  let c : ℝ := 1/2
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let g (x : ℝ) := Real.log ‖riemannZeta (p x)‖
  let D (x : ℝ) := (deriv riemannZeta (p x)/riemannZeta (p x)).re
  have hcb : c ≤ 2 := by norm_num [c]
  have hder (x : ℝ) (hx : x ∈ Icc c 2) : HasDerivAt g (D x) x := by
    have hx₀ : 0 < x := by dsimp [c] at hx; linarith [hx.1]
    have hs : p x ≠ 1 := fun he => ht (by simpa [p] using congrArg Complex.im he)
    have h := (differentiableAt_riemannZeta hs).hasDerivAt.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ)*I))
    apply hasDerivAt_real_log_norm _ (riemannZeta_ne_zero_on_horizontal_of_no_ordinate hno hx₀)
    exact h.comp_ofReal.congr_deriv (by simp [p])
  have hg : ContinuousOn g (Icc c 2) := fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hd : ContinuousOn (fun x => (x-c)*D x) (Icc c 2) :=
    (continuous_id.sub continuous_const).continuousOn.mul
      (Complex.continuous_re.comp_continuousOn (continuousOn_horizontal_zeta_logDeriv ht hno))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := c) (b := 2)
    (f := fun x => (x-c)*g x) (f' := fun x => g x+(x-c)*D x) (fun x hx => by
      rw [uIcc_of_le hcb] at hx
      exact (((hasDerivAt_id x).sub_const c).mul (hder x hx)).congr_deriv (by simp))
    ((hg.add hd).intervalIntegrable_of_Icc hcb)
  have hi₁ : IntervalIntegrable g volume c 2 := hg.intervalIntegrable_of_Icc hcb
  have hi₂ : IntervalIntegrable (fun x => (x-c)*D x) volume c 2 := hd.intervalIntegrable_of_Icc hcb
  rw [intervalIntegral.integral_add hi₁ hi₂, sub_self, zero_mul, sub_zero] at H
  change (∫ x in c..2, g x) = 3/2*g 2 - ∫ x in c..2, (x-c)*D x
  rw [← show 2-c = 3/2 by norm_num [c]]
  linarith

end AnalyticNumberTheory.RiemannZeta
