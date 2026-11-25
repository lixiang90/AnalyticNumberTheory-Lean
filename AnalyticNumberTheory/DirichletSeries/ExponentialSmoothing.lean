import AnalyticNumberTheory.AnalyticTools.Gamma.SmoothingKernel
import AnalyticNumberTheory.DirichletSeries.Convergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exponential smoothing of a Dirichlet series

Mellin inversion of the Gamma function gives the factor `exp (-n / X)`
at each frequency. Absolute convergence on the integration line justifies
the exchange of the infinite series and the integral.
-/

open Complex Real Set MeasureTheory Filter
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletSeries

private theorem continuous_term_on_line (a : ℕ → ℂ) (n : ℕ) {P : ℝ → ℂ} (hP : Continuous P) :
    Continuous (fun t => LSeries.term a (P t) n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero]; exact continuous_const
  · have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp_rw [LSeries.term_of_ne_zero hn,Complex.cpow_def_of_ne_zero hnC]
    exact continuous_const.div (Complex.continuous_exp.comp (continuous_const.mul hP))
      (fun _ => Complex.exp_ne_zero _)

/-- Termwise inverse Mellin transformation on any positive line of absolute convergence. -/
theorem hasSum_exponentiallySmoothed {a : ℕ → ℂ} {F : ℂ → ℂ} (s : ℂ) {c X : ℝ}
    (hc : 0<c) (hX : 0<X)
    (hF : ∀ t : ℝ, LSeriesHasSum a (s+((c:ℂ)+t*I)) (F (s+((c:ℂ)+t*I)))) :
    HasSum (fun n : ℕ => LSeries.term a s n * (Real.exp (-(n:ℝ)/X):ℂ))
      (gammaSmoothingIntegral (fun w => F (s+w)) X c) := by
  let w (t : ℝ) : ℂ := (c:ℂ)+t*I
  let K (t : ℝ) := Complex.Gamma (w t)*(X:ℂ)^(w t)
  let f (n : ℕ) (t : ℝ) := K t * LSeries.term a (s+w t) n
  let b (n : ℕ) := ‖LSeries.term a (s+c) n‖
  let κ : ℂ := (2*(π:ℂ))⁻¹
  have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hG : Integrable (fun t : ℝ => Complex.Gamma (w t)) := verticalIntegrable_Gamma hc
  have hp : Continuous (fun t => (X:ℂ)^(w t)) :=
    (differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp hw
  have hK : Integrable K := by
    apply (hG.norm.mul_const (X^c)).mono' (hG.aestronglyMeasurable.mul hp.aestronglyMeasurable)
    filter_upwards with t
    simp [K,Complex.norm_cpow_eq_rpow_re_of_pos hX,w]
  have hnorm (n : ℕ) (t : ℝ) : ‖f n t‖ = ‖K t‖*b n := by
    simp [f,b,LSeries.norm_term_eq,w]
  have hfi (n : ℕ) : Integrable (f n) := by
    apply (hK.norm.mul_const (b n)).mono'
      (hK.aestronglyMeasurable.mul (continuous_term_on_line a n (continuous_const.add hw)).aestronglyMeasurable)
    exact Eventually.of_forall (fun t => (hnorm n t).le)
  have hsb : Summable b := by simpa [b] using (hF 0).summable.norm
  have hS := (hasSum_integral_of_summable_integral_norm hfi (show Summable (fun n => ∫ t, ‖f n t‖) by
    simp_rw [hnorm,integral_mul_const]; exact hsb.mul_left _)).mul_left κ
  have hterm (n : ℕ) : κ*(∫ t, f n t) = LSeries.term a s n * (Real.exp (-(n:ℝ)/X):ℂ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hnC : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
    have hX' : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
    have hmel := mellinInv_Gamma hc (div_pos hnR hX)
    rw [neg_div,← hmel]
    unfold mellinInv
    rw [Complex.real_smul,Complex.ofReal_div]
    simp only [Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat,one_div,smul_eq_mul]
    change κ*_ = _*(κ*_)
    rw [mul_left_comm (LSeries.term a s n) κ]
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [f,K,w,LSeries.term_of_ne_zero hn,Complex.cpow_add _ _ hnC,Complex.ofReal_div,
      Complex.ofReal_natCast,Complex.cpow_neg]
    rw [show ((n:ℂ)/(X:ℂ))^((c:ℂ)+(t:ℂ)*I) = (n:ℂ)^((c:ℂ)+(t:ℂ)*I)/(X:ℂ)^((c:ℂ)+(t:ℂ)*I)
      from Complex.div_cpow_ofReal_nonneg hnR.le hX.le _]
    simp only [Complex.cpow_add _ _ hnC, inv_div, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hsum (t : ℝ) : (∑' n, f n t) = K t*F (s+w t) := ((hF t).mul_left (K t)).tsum_eq
  simp_rw [hterm,hsum] at hS
  convert hS using 1
  unfold gammaSmoothingIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  dsimp [K,w]
  ring

end AnalyticNumberTheory.DirichletSeries
