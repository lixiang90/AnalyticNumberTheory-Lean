import AnalyticNumberTheory.AnalyticTools.BromwichKernel
import AnalyticNumberTheory.AnalyticTools.FourierLocalization

/-! # Symmetric cutoffs for Fourier and Laplace inversion -/

noncomputable section
open MeasureTheory Complex Filter Set
open scoped Topology FourierTransform

namespace AnalyticNumberTheory.AnalyticTools

/-- The finite Bromwich integral is an inverse Fourier integral of the damped
zero extension. Angular height T corresponds to Fourier cutoff T/(2π). -/
theorem truncatedBromwich_eq_fourier (f : ℝ → ℂ) (σ x T : ℝ) :
    truncatedBromwich (laplaceTransform f) σ x T =
      Complex.exp ((σ : ℂ) * x) * truncatedFourierInverse (laplaceDamped σ f) x (T / (2 * Real.pi)) := by
  let c : ℝ := 2 * Real.pi
  let G (ξ : ℝ) := Complex.exp (((c * (x*ξ) : ℝ) : ℂ) * I) * 𝓕 (laplaceDamped σ f) ξ
  have hc : 0 < c := by dsimp [c]; positivity
  have ht (t : ℝ) : Complex.exp (((σ : ℂ) + t * I) * x) * laplaceTransform f ((σ : ℂ) + t * I) =
      Complex.exp ((σ : ℂ) * x) * G (t / c) := by
    dsimp only [G]
    rw [fourier_laplaceDamped]
    have hfreq : 2 * Real.pi * (t / c) = t := by
      change c * (t / c) = t
      field_simp
    have hphase : c * (x * (t / c)) = t*x := by field_simp
    rw [hfreq, hphase, ← mul_assoc, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  unfold truncatedBromwich
  simp_rw [ht]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div G hc.ne', neg_div,
    Complex.real_smul, truncatedFourierInverse_eq_integral]
  change (1 / (2 * Real.pi : ℂ)) * (Complex.exp ((σ : ℂ) * x) *
    ((c : ℂ) * ∫ ξ in -(T/c)..T/c, G ξ)) = Complex.exp ((σ : ℂ) * x) * ∫ ξ in -(T/c)..T/c, G ξ
  have hc' : (c : ℂ) = (2 * Real.pi : ℂ) := by simp [c]
  rw [hc']
  field_simp [Real.pi_ne_zero]

/-- For two exponentially integrable inputs that agree near x, the difference
of their truncated Bromwich integrals tends to zero, on any real vertical line. -/
theorem truncatedBromwich_localization {f g : ℝ → ℂ} {σ x : ℝ}
    (hf : Integrable (laplaceDamped σ f)) (hg : Integrable (laplaceDamped σ g)) (he : ∀ᶠ u in 𝓝 x, 0 < u → f u = g u) :
    Tendsto (fun T => truncatedBromwich (laplaceTransform f) σ x T -
        truncatedBromwich (laplaceTransform g) σ x T) atTop (𝓝 0) := by
  have hlocal : laplaceDamped σ f =ᶠ[𝓝 x] laplaceDamped σ g := by
    filter_upwards [he] with u hu
    by_cases h : u ∈ Ioi (0 : ℝ)
    · simp [laplaceDamped, h, hu h]
    · simp [laplaceDamped, h]
  have hcut : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have H := ((truncatedFourierInverse_localization hf hg x hlocal).comp hcut).const_mul
    (Complex.exp ((σ : ℂ) * x))
  rw [mul_zero] at H
  exact H.congr fun T => by simp [truncatedBromwich_eq_fourier, mul_sub]

/-- Exponential damping makes every bounded measurable function on the
positive half-line integrable on a line of positive real part. -/
theorem integrable_laplaceDamped_of_bounded {f : ℝ → ℂ} {σ B : ℝ} (hσ : 0 < σ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hB : ∀ u : ℝ, 0 < u → ‖f u‖ ≤ B) :
    Integrable (laplaceDamped σ f) := by
  have hi := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hσ) 0
  have hc : Continuous (fun u : ℝ => Complex.exp (-(σ : ℂ)*u)) := by fun_prop
  unfold laplaceDamped
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  apply (hi.mul_const B).mono' (hc.aestronglyMeasurable.mul hf)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖Complex.exp (-(σ : ℂ) * u) * f u‖ ≤ Real.exp (-σ * u) * B
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (hB u hu) (Real.exp_pos _).le

/-- On a line of absolute convergence, subtracting two inputs subtracts the
Bromwich integrals at each finite cutoff. -/
theorem truncatedBromwich_laplace_sub {f g : ℝ → ℂ} {σ : ℝ}
    (hf : Integrable (laplaceDamped σ f)) (hg : Integrable (laplaceDamped σ g)) (x T : ℝ) :
    truncatedBromwich (laplaceTransform (f-g)) σ x T =
      truncatedBromwich (laplaceTransform f) σ x T - truncatedBromwich (laplaceTransform g) σ x T := by
  have hd : laplaceDamped σ (f-g) = laplaceDamped σ f - laplaceDamped σ g := by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ) <;> simp [laplaceDamped, hu, mul_sub]
  simp_rw [truncatedBromwich_eq_fourier]
  rw [hd, truncatedFourierInverse_sub hf hg, mul_sub]

end AnalyticNumberTheory.AnalyticTools
