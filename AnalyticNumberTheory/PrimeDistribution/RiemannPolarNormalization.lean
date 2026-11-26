import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralReal
import AnalyticNumberTheory.PrimeDistribution.Oscillation
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# The pole and logarithmic derivative in Riemann's prime-power formula

Along the positive real shift the two singular terms cancel at one. Their common
primitive uses the entire factor ζ₁ and the entire remainder of Ei. Evaluating it
at zero and at infinity gives the normalization Ei(u) − log 2.
-/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.PrimeDistribution

private theorem zetaOne_eq_product {z : ℂ} (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz)]

/-- The pole-removed factor (s−1)ζ(s) has value 1/2 at zero. -/
theorem riemannZeta₁_zero_eq_half : riemannZeta₁ 0 = 1 / 2 := by
  rw [zetaOne_eq_product (by norm_num), riemannZeta_zero]
  norm_num

/-- The pole-removed zeta function has positive real part on the nonnegative real axis. -/
theorem riemannZeta₁_re_pos_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 < (riemannZeta₁ y).re := by
  rcases hy.eq_or_lt with rfl | hpos
  · norm_num [riemannZeta₁_zero_eq_half]
  rcases lt_trichotomy y 1 with h | rfl | h
  · rw [zetaOne_eq_product (by exact_mod_cast h.ne)]
    simpa [Complex.mul_re] using mul_pos_of_neg_of_neg (sub_neg.mpr h) (riemannZeta_ofReal_neg_on_Ioo hpos h).1
  · simp
  · rw [zetaOne_eq_product (by exact_mod_cast h.ne')]
    simpa [Complex.mul_re] using mul_pos (sub_pos.mpr h) (riemannZeta_re_pos_of_one_lt h)

/-- ζ(y) tends to one along the positive real axis. -/
theorem tendsto_riemannZeta_ofReal_atTop :
    Tendsto (fun y : ℝ => riemannZeta (y : ℂ)) atTop (𝓝 1) := by
  have h := LSeries.tendsto_atTop (f := 1) (by rw [LSeries.abscissaOfAbsConv_one]; exact EReal.coe_lt_top 1)
  apply (by simpa using h : Tendsto (fun y : ℝ => LSeries 1 (y : ℂ)) atTop (𝓝 1)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy using LSeries_one_eq_riemannZeta (by simpa using hy)

private def polarPrimitive (u : ℝ) (z : ℂ) : ℂ :=
  -exponentialIntegralRemainder ((1-z)*u) - Complex.log (riemannZeta₁ z)

private theorem polarPrimitive_analytic (u : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    AnalyticAt ℂ (polarPrimitive u) (y : ℂ) := by
  have hP : Differentiable ℂ exponentialIntegralRemainder :=
    fun z => (hasDerivAt_exponentialIntegralRemainder z).differentiableAt
  exact (((hP.analyticAt _).comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (1-z)*u) (y:ℂ))).neg).sub
    ((differentiable_riemannZeta₁.analyticAt _).clog (Complex.mem_slitPlane_iff.mpr (.inl (riemannZeta₁_re_pos_of_nonneg hy))))

private theorem deriv_polarPrimitive {u y : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (hy₁ : y ≠ 1) :
    deriv (polarPrimitive u) (y : ℂ) =
      Complex.exp ((1-(y : ℂ))*u)/(1-(y : ℂ)) - deriv riemannZeta y / riemannZeta y := by
  have hz : (y : ℂ) ≠ 1 := by exact_mod_cast hy₁
  have hd := sub_ne_zero.mpr hz
  have hd' := sub_ne_zero.mpr hz.symm
  have hu' := Complex.ofReal_ne_zero.mpr hu.ne'
  have hs := Complex.mem_slitPlane_iff.mpr (Or.inl (riemannZeta₁_re_pos_of_nonneg hy))
  have hlin := ((hasDerivAt_id' (y : ℂ)).const_sub (1:ℂ)).mul_const (u:ℂ)
  have hP := (hasDerivAt_exponentialIntegralRemainder_of_ne_zero (mul_ne_zero hd' hu')).comp (y:ℂ) hlin
  have h := hP.neg.sub ((differentiable_riemannZeta₁ (y:ℂ)).hasDerivAt.clog hs)
  change deriv (fun z : ℂ => -exponentialIntegralRemainder ((1-z)*u) - Complex.log (riemannZeta₁ z)) (y : ℂ) = _
  calc
    _ = _ := h.deriv
    _ = _ := by
      rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hz, riemannZeta_eq_inv_sub_mul hz]
      field_simp [hd, hd', hu', Complex.slitPlane_ne_zero hs]
      ring

private theorem polarPrimitive_zero (u : ℝ) :
    polarPrimitive u 0 = -exponentialIntegralRemainder u + (Real.log 2 : ℂ) := by
  have hlog : Complex.log (1/2 : ℂ) = -(Real.log 2 : ℂ) := by
    rw [show (1/2 : ℂ) = ((2:ℝ)⁻¹ : ℝ) by norm_num,
      ←Complex.ofReal_log (by norm_num), Real.log_inv, Complex.ofReal_neg]
  rw [polarPrimitive, riemannZeta₁_zero_eq_half, hlog]
  simp

private theorem polarPrimitive_of_one_lt {u y : ℝ} (hu : 0 < u) (hy : 1 < y) :
    polarPrimitive u (y : ℂ) = (Real.eulerMascheroniConstant : ℂ) + (Real.log u : ℂ) +
      (realEOne ((y-1)*u) : ℂ) - Complex.log (riemannZeta y) := by
  have hpos := sub_pos.mpr hy
  have hne : (y:ℂ) ≠ 1 := by exact_mod_cast hy.ne'
  have hζ := riemannZeta_ne_zero_of_one_le_re (s := (y:ℂ)) (by simpa using hy.le)
  have hE := realEOne_eq_log_remainder (mul_pos hpos hu)
  rw [Real.log_mul hpos.ne' hu.ne', Complex.ofReal_add] at hE
  have he : -(((y-1)*u : ℝ) : ℂ) = (1-(y:ℂ))*u := by push_cast; ring
  rw [he] at hE
  have hf : (y:ℂ) - 1 = ((y-1:ℝ):ℂ) := by push_cast; rfl
  rw [polarPrimitive, zetaOne_eq_product hne, hf, Complex.log_ofReal_mul hpos hζ]
  linear_combination -hE

/-- Integrating the real shift of the polar term and −ζ'/ζ gives Ei(u) − log 2.
The integrand's isolated value at y = 1 is immaterial. -/
theorem tendsto_integral_riemannPolar_sub_logDeriv {u : ℝ} (hu : 0 < u) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..R,
      Complex.exp ((1-(y:ℂ))*u)/(1-(y:ℂ)) - deriv riemannZeta y / riemannZeta y)
      atTop (𝓝 (principalExponentialIntegral (u:ℂ) - (Real.log 2 : ℂ))) := by
  have hζ := (Complex.hasDerivAt_log (by simp : (1:ℂ) ∈ Complex.slitPlane)).continuousAt.tendsto.comp
    tendsto_riemannZeta_ofReal_atTop
  have hE := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_realEOne_atTop.comp ((tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_id).atTop_mul_const hu))
  have htop : Tendsto (fun R : ℝ => polarPrimitive u R) atTop
      (𝓝 ((Real.eulerMascheroniConstant : ℂ)+(Real.log u : ℂ))) := by
    have ht := (tendsto_const_nhds (x := (Real.eulerMascheroniConstant : ℂ)+(Real.log u : ℂ))).add hE |>.sub hζ
    apply (by simpa [Function.comp_def] using ht :
      Tendsto (fun R : ℝ => (Real.eulerMascheroniConstant : ℂ)+(Real.log u : ℂ) +
        (realEOne ((R+ -1)*u) : ℂ) - Complex.log (riemannZeta R)) atTop _).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with R hR using
      (by simpa [sub_eq_add_neg] using (polarPrimitive_of_one_lt hu hR).symm)
  have hlim := htop.sub_const (polarPrimitive u 0)
  rw [polarPrimitive_zero] at hlim
  apply (show Tendsto (fun R : ℝ => polarPrimitive u R - polarPrimitive u 0) atTop
    (𝓝 (principalExponentialIntegral (u:ℂ) - (Real.log 2 : ℂ))) by
      rw [principalExponentialIntegral, ←Complex.ofReal_log hu.le, polarPrimitive_zero]
      convert hlim using 2
      ring).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  symm
  calc
    _ = ∫ y in (0:ℝ)..R, deriv (polarPrimitive u) (y:ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (1:ℝ)] with y hy₁ hy
      exact (deriv_polarPrimitive hu ((uIoc_of_le hR ▸ hy).1.le) hy₁).symm
    _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => (polarPrimitive_analytic u ((uIcc_of_le hR ▸ hy).1)).differentiableAt.hasDerivAt.comp_ofReal)
      (ContinuousOn.intervalIntegrable fun y hy =>
        ((polarPrimitive_analytic u ((uIcc_of_le hR ▸ hy).1)).deriv.continuousAt.comp
          Complex.continuous_ofReal.continuousAt).continuousWithinAt)

end AnalyticNumberTheory.PrimeDistribution
