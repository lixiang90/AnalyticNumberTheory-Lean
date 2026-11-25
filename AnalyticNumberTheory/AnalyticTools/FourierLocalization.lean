import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Localization of symmetric Fourier inversion

A locally vanishing integrable function contributes zero in the limit of the
symmetric inverse integrals. A primitive of its Fourier transform is obtained
by dividing the translated function by its displacement from the inversion point.
-/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped FourierTransform Topology RealInnerProductSpace

namespace AnalyticNumberTheory.AnalyticTools

/-- The symmetric inverse Fourier integral with frequency cutoff R. Translating
the input puts the inversion point at the origin. -/
def truncatedFourierInverse (f : ℝ → ℂ) (x R : ℝ) : ℂ :=
  ∫ ξ in -R..R, 𝓕 (fun u : ℝ => f (u+x)) ξ

/-- The usual expression with the positive inverse Fourier phase. -/
theorem truncatedFourierInverse_eq_integral (f : ℝ → ℂ) (x R : ℝ) :
    truncatedFourierInverse f x R =
      ∫ ξ in -R..R, Complex.exp (((2 * Real.pi * (x*ξ) : ℝ) : ℂ) * I) * 𝓕 f ξ := by
  apply intervalIntegral.integral_congr
  intro ξ _
  have H := congr_fun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ ℝ) f x) ξ
  change 𝓕 (fun u : ℝ => f (u+x)) ξ = Real.fourierChar (inner ℝ x ξ) • 𝓕 f ξ at H
  rw [H]
  simp [Circle.smul_def, Real.fourierChar_apply, RCLike.inner_apply, mul_comm x ξ]

private lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

private lemma fourier_const_mul (c : ℂ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (c • g) ξ = c * 𝓕 g ξ :=
  congr_fun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) g c) ξ

/-- If the translated function divided by its argument is integrable, symmetric
inversion gives zero at the point. This is the integrable remainder in Dini's test. -/
theorem truncatedFourierInverse_tendsto_zero_of_integrable_div {f : ℝ → ℂ} (hf : Integrable f)
    (x : ℝ) (hd : Integrable (fun u : ℝ => f (u+x) / (u : ℂ))) :
    Tendsto (truncatedFourierInverse f x) atTop (𝓝 0) := by
  let g (u : ℝ) := f (u+x)
  let h (u : ℝ) := g u / (u : ℂ)
  let c : ℂ := -2 * Real.pi * I
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero]
  have hg : Integrable g := (measurePreserving_add_right volume x).integrable_comp_of_integrable hf
  have hzero : ∀ᵐ u : ℝ, u ≠ 0 := by simp [ae_iff]
  have he : (fun u : ℝ => u • h u) =ᵐ[volume] g := by
    filter_upwards [hzero] with u hu
    rw [Complex.real_smul]
    dsimp only [h]
    field_simp [Complex.ofReal_ne_zero.mpr hu]
  have hm : Integrable (fun u : ℝ => u • h u) := hg.congr he.symm
  have hlin : (fun u : ℝ => (c * (u : ℂ)) • h u) =ᵐ[volume] c • g := by
    filter_upwards [he] with u hu
    change c * (u : ℂ) * h u = c * g u
    rw [mul_assoc, ← Complex.real_smul, hu]
  have hderiv (ξ : ℝ) : HasDerivAt (fun t : ℝ => 𝓕 h t / c) (𝓕 g ξ) ξ := by
    have D := (Real.hasDerivAt_fourier (f := h) hd hm ξ).div_const c
    change HasDerivAt _ (𝓕 (fun u : ℝ => (c * (u : ℂ)) • h u) ξ / c) ξ at D
    rwa [Real.fourier_congr_ae hlin ξ, fourier_const_mul, mul_div_cancel_left₀ _ hc] at D
  have heval (R : ℝ) : truncatedFourierInverse f x R = 𝓕 h R / c - 𝓕 h (-R) / c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ _ => hderiv ξ)
      ((continuous_fourier_of_integrable hg).intervalIntegrable ..)
  have H := Real.zero_at_infty_fourier h
  have hp := H.mono_left atTop_le_cocompact
  have hn := (H.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
  have Hlim := (hp.div_const c).sub (hn.div_const c)
  simp only [zero_div, sub_zero] at Hlim
  exact Hlim.congr fun R => (heval R).symm

/-- An integrable function that vanishes on a neighborhood of the inversion
point makes a vanishing contribution to the symmetric inverse integral. -/
theorem truncatedFourierInverse_tendsto_zero_of_eventually_zero {f : ℝ → ℂ} (hf : Integrable f)
    (x : ℝ) (hlocal : f =ᶠ[𝓝 x] 0) :
    Tendsto (truncatedFourierInverse f x) atTop (𝓝 0) := by
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hg : Integrable (fun u : ℝ => f (u+x)) :=
    (measurePreserving_add_right volume x).integrable_comp_of_integrable hf
  apply truncatedFourierInverse_tendsto_zero_of_integrable_div hf
  apply (hg.norm.div_const r).mono'
    (hg.aemeasurable.div Complex.continuous_ofReal.measurable.aemeasurable).aestronglyMeasurable
  refine ae_of_all _ fun u => ?_
  change ‖f (u+x) / (u : ℂ)‖ ≤ ‖f (u+x)‖ / r
  by_cases hu : |u| < r
  · have hv : f (u+x) = 0 := H (by simpa [Real.dist_eq] using hu)
    simp [hv]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hr (le_of_not_gt hu)

/-- Subtracting two integrable inputs commutes with every finite cutoff. -/
theorem truncatedFourierInverse_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (x R : ℝ) : truncatedFourierInverse (f-g) x R =
      truncatedFourierInverse f x R - truncatedFourierInverse g x R := by
  let F (u : ℝ) := f (u+x)
  let G (u : ℝ) := g (u+x)
  have hF : Integrable F := (measurePreserving_add_right volume x).integrable_comp_of_integrable hf
  have hG : Integrable G := (measurePreserving_add_right volume x).integrable_comp_of_integrable hg
  have hsum : 𝓕 ((F-G)+G) = 𝓕 (F-G) + 𝓕 G :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar (innerSL ℝ).continuous₂ (hF.sub hG) hG
  rw [sub_add_cancel] at hsum
  have hsub (ξ : ℝ) : 𝓕 (F-G) ξ = 𝓕 F ξ - 𝓕 G ξ :=
    eq_sub_iff_add_eq.mpr (congr_fun hsum ξ).symm
  change (∫ ξ in -R..R, 𝓕 (F-G) ξ) = (∫ ξ in -R..R, 𝓕 F ξ) - ∫ ξ in -R..R, 𝓕 G ξ
  simp_rw [hsub]
  exact intervalIntegral.integral_sub ((continuous_fourier_of_integrable hF).intervalIntegrable ..)
    ((continuous_fourier_of_integrable hG).intervalIntegrable ..)

/-- Riemann's localization principle for the Fourier transform on the real
line. The difference of the inverse truncations tends to zero whenever the
two integrable functions agree near the inversion point. -/
theorem truncatedFourierInverse_localization {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (x : ℝ) (he : f =ᶠ[𝓝 x] g) :
    Tendsto (fun R => truncatedFourierInverse f x R - truncatedFourierInverse g x R) atTop (𝓝 0) := by
  have hzero : f-g =ᶠ[𝓝 x] 0 := he.mono fun t ht => by simp [ht]
  exact (truncatedFourierInverse_tendsto_zero_of_eventually_zero (hf.sub hg) x hzero).congr
    (fun R => truncatedFourierInverse_sub hf hg x R)

end AnalyticNumberTheory.AnalyticTools
