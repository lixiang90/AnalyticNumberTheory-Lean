import AnalyticNumberTheory.AnalyticTools.GammaLaplace
import Mathlib.Analysis.Fourier.Inversion

/-!
# Laplace and Bromwich transforms for the partition series

The Laplace transform of the gamma density on the right half-plane supplies
the inverse powers occurring in Rademacher's contour integral.
-/

open Complex Real Filter MeasureTheory Set
open scoped Topology FourierTransform

namespace AnalyticNumberTheory.ModularAndPartitions

private noncomputable def gammaKernel (s : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z*t) * (t^(s-1) : ℝ)

private theorem norm_gammaKernel (s : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gammaKernel s z t‖ = t^(s-1) * Real.exp (-z.re*t) := by
  rw [gammaKernel, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  simp [Complex.mul_re, mul_comm]

private theorem integrable_gammaBound {r b : ℝ} (hr : -1 < r) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t^r*Real.exp (-b*t)) (Ioi 0) := by
  simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow hr zero_lt_one hb

private theorem integrable_gammaKernel {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (gammaKernel s z) (Ioi 0) := by
  refine (integrable_gammaBound (by linarith : -1 < s-1) hz).mono' ?_ ?_
  · unfold gammaKernel; fun_prop
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => (norm_gammaKernel s z ht).le

/-- The gamma Laplace integral at a complex parameter with positive real part. -/
theorem integral_gammaKernel_rightHalfPlane {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z*t) * (t^(s-1) : ℝ)) =
      z^(-(s:ℂ)) * (Real.Gamma s : ℝ) := by
  have h := AnalyticTools.integral_gammaLaplaceKernel_rightHalfPlane (s:=(s:ℂ)) hs hz
  rw [←Complex.Gamma_ofReal]
  apply Eq.trans _ h
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Complex.ofReal_cpow ht.le,Complex.ofReal_sub,Complex.ofReal_one]

/-- Absolute integrability of inverse powers on the vertical line through one. -/
theorem integrable_vertical_cpow {s : ℝ} (hs : 2 ≤ s) :
    Integrable (fun t : ℝ => (1+(t:ℂ)*I) ^ (-(s:ℂ))) := by
  let w (t : ℝ) := 1+(t:ℂ)*I
  have hw (t : ℝ) : (w t).re = 1 := by simp [w]
  have hcont : Continuous (fun t => (w t)^(-(s:ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := w) (continuousAt_cpow_const (Or.inl (by rw [hw]; norm_num))) (by dsimp [w]; fun_prop)
  apply integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
  refine ae_of_all _ fun t => ?_
  change ‖(w t)^(-(s:ℂ))‖ ≤ _
  have hn : 1 ≤ ‖w t‖ := (hw t) ▸ Complex.re_le_norm (w t)
  have hn2 : ‖w t‖^2 = 1+t^2 := by rw [Complex.sq_norm, Complex.normSq_apply, hw]; simp [w, sq]
  rw [← Complex.ofReal_neg, Complex.norm_cpow_real, ← hn2, ← Real.rpow_two, ← Real.rpow_neg (norm_nonneg _)]
  exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)

private theorem fourier_gammaKernel {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    𝓕 ((Ioi 0).indicator (gammaKernel s 1)) ξ =
      (1 + ((2*π*ξ:ℝ):ℂ)*I)^(-(s:ℂ)) * (Real.Gamma s : ℝ) := by
  have hz : 0 < (1 + ((2*π*ξ:ℝ):ℂ)*I).re := by simp
  rw [← integral_gammaKernel_rightHalfPlane hs hz, Real.fourier_eq']
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  by_cases ht : t ∈ Ioi (0:ℝ)
  · simp only [Set.indicator_of_mem ht, smul_eq_mul, RCLike.inner_apply, conj_trivial, gammaKernel,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · simp [Set.indicator_of_notMem ht]

/-- The vertical-line Bromwich integral of an inverse real power.
Its Fourier normalization is `2π`, and the line has real part one. -/
theorem integral_vertical_cpow_exp {s b : ℝ} (hs : 2 ≤ s) (hb : 0 < b) :
    (∫ t : ℝ, Complex.exp (I*b*t) * (1+(t:ℂ)*I)^(-(s:ℂ))) =
      ((2*π*Real.exp (-b)*b^(s-1)/Real.Gamma s : ℝ):ℂ) := by
  let f := (Ioi 0).indicator (gammaKernel s 1)
  let F (t : ℝ) := Complex.exp (I*b*t) * (1+(t:ℂ)*I)^(-(s:ℂ))
  have hs0 : 0 < s := by linarith
  have hg0 : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs0
  have hf : Integrable f := (integrable_gammaKernel hs0 (by norm_num : 0 < (1:ℂ).re)).integrable_indicator measurableSet_Ioi
  have hh : Integrable (𝓕 f) := by
    have h := ((integrable_vertical_cpow hs).comp_mul_left' (by positivity : 2*π ≠ 0)).mul_const ((Real.Gamma s:ℝ):ℂ)
    apply h.congr
    exact ae_of_all _ fun ξ => (fourier_gammaKernel hs0 ξ).symm
  have hcont : ContinuousAt f b := by
    apply ContinuousAt.congr (f := gammaKernel s 1)
    · unfold gammaKernel
      fun_prop (disch := positivity)
    · filter_upwards [lt_mem_nhds hb] with t ht
      exact (Set.indicator_of_mem ht _).symm
  have hinv := hf.fourierInv_fourier_eq hh hcont
  rw [Real.fourierInv_eq'] at hinv
  have he (ξ : ℝ) : Complex.exp (((2*π*inner ℝ ξ b : ℝ):ℂ)*I) • 𝓕 f ξ =
      F ((2*π)*ξ) * ((Real.Gamma s:ℝ):ℂ) := by
    rw [show 𝓕 f ξ = _ from fourier_gammaKernel hs0 ξ]
    simp only [F, smul_eq_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring_nf
  simp_rw [he] at hinv
  rw [integral_mul_const, Measure.integral_comp_mul_left F, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*π)),
    Complex.real_smul] at hinv
  change _ = (Ioi 0).indicator (gammaKernel s 1) b at hinv
  rw [Set.indicator_of_mem hb] at hinv
  dsimp only [gammaKernel] at hinv
  rw [neg_one_mul] at hinv
  change (∫ t, F t) = _
  push_cast
  push_cast at hinv
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hgc : (Real.Gamma s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg0.ne'
  field_simp at hinv ⊢
  linear_combination hinv

end AnalyticNumberTheory.ModularAndPartitions
