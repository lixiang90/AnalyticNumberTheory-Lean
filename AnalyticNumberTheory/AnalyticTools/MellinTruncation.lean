import AnalyticNumberTheory.AnalyticTools.FourierLocalization
import AnalyticNumberTheory.AnalyticTools.Transforms

/-! # Mellin inversion with finite symmetric height -/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology FourierTransform

namespace AnalyticNumberTheory.AnalyticTools

/-- Logarithmic coordinates for a Mellin transform on the line Re s = σ. -/
def mellinLogPullback {E : Type*} [SMul ℝ E] (σ : ℝ) (f : ℝ → E) (u : ℝ) : E :=
  Real.exp (-σ*u) • f (Real.exp (-u))

/-- The inverse Mellin integral from σ−iT to σ+iT. -/
def truncatedMellinInverse (F : ℂ → ℂ) (σ x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) * ∫ t in -T..T,
    (x : ℂ) ^ (-((σ : ℂ) + t*I)) * F ((σ : ℂ) + t*I)

/-- Absolute Mellin convergence gives ordinary integrability in logarithmic
coordinates, including the Jacobian of the change of variable. -/
theorem integrable_mellinLogPullback {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (mellinLogPullback σ f) := by
  let K (t : ℝ) := (t : ℂ) ^ ((σ : ℂ)-1) * f t
  have hK : IntegrableOn K (Ioi (0 : ℝ)) := by
    simpa only [MellinConvergent, K, smul_eq_mul] using hf
  have H : Integrable (fun u : ℝ => Real.exp u • K (Real.exp u)) :=
    (integrable_comp_exp K).2 hK
  have weight (u : ℝ) : (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ ((σ : ℂ)-1) =
      (Real.exp (σ*u) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  have He : Integrable (fun u : ℝ => (Real.exp (σ*u) : ℂ) * f (Real.exp u)) := by
    apply H.congr
    refine ae_of_all _ fun u => ?_
    change (Real.exp u : ℂ) * ((Real.exp u : ℂ) ^ ((σ : ℂ)-1) * f (Real.exp u)) = _
    rw [← mul_assoc, weight]
  apply He.comp_neg.congr
  refine ae_of_all _ fun u => ?_
  change (Real.exp (σ*(-u)) : ℂ) * f (Real.exp (-u)) = Real.exp (-σ*u) • f (Real.exp (-u))
  rw [Complex.real_smul, mul_neg, neg_mul]

private lemma mellin_phase {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    (x : ℂ) ^ (-((σ : ℂ) + t*I)) =
      (Real.exp (-σ*Real.log x) : ℂ) * Complex.exp (((t*(-Real.log x) : ℝ) : ℂ)*I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The finite inverse Mellin integral equals the finite inverse Fourier
integral of the logarithmic pullback at −log x, times x raised to −σ. -/
theorem truncatedMellinInverse_eq_fourier (f : ℝ → ℂ) (σ : ℝ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    truncatedMellinInverse (mellin f) σ x T =
      (Real.exp (-σ*Real.log x) : ℂ) *
        truncatedFourierInverse (mellinLogPullback σ f) (-Real.log x) (T / (2 * Real.pi)) := by
  let c : ℝ := 2 * Real.pi
  let G (ξ : ℝ) := Complex.exp (((c * ((-Real.log x)*ξ) : ℝ) : ℂ)*I) * 𝓕 (mellinLogPullback σ f) ξ
  have hc : 0 < c := by dsimp [c]; positivity
  have hF (t : ℝ) : mellin f ((σ : ℂ)+t*I) = 𝓕 (mellinLogPullback σ f) (t/c) := by
    change _ = 𝓕 (fun u : ℝ => Real.exp (-σ*u) • f (Real.exp (-u))) (t/(2*Real.pi))
    rw [mellin_eq_fourier]
    simp only [show ((σ : ℂ)+t*I).re = σ by simp, show ((σ : ℂ)+t*I).im = t by simp]
  have ht (t : ℝ) : (x : ℂ) ^ (-((σ : ℂ) + t*I)) * mellin f ((σ : ℂ) + t*I) =
      (Real.exp (-σ*Real.log x) : ℂ) * G (t/c) := by
    rw [mellin_phase hx, hF]
    dsimp only [G]
    rw [show c * ((-Real.log x)*(t/c)) = t*(-Real.log x) by field_simp, mul_assoc]
  unfold truncatedMellinInverse
  simp_rw [ht]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div G hc.ne', neg_div,
    Complex.real_smul, truncatedFourierInverse_eq_integral]
  change (1 / (2 * Real.pi : ℂ)) * ((Real.exp (-σ*Real.log x) : ℂ) *
    ((c : ℂ) * ∫ ξ in -(T/c)..T/c, G ξ)) = (Real.exp (-σ*Real.log x) : ℂ) * ∫ ξ in -(T/c)..T/c, G ξ
  rw [show (c : ℂ) = (2 * Real.pi : ℂ) by simp [c]]
  field_simp [Real.pi_ne_zero]

end AnalyticNumberTheory.AnalyticTools
