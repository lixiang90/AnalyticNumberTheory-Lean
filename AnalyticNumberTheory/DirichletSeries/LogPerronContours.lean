import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalBoundaryShift

/-! # Moving logarithmically smoothed Perron integrals

For a holomorphic numerator of at most linear growth, the squared
denominator gives decay on both horizontal sides of the rectangle.
Absolute integrability is only required on the two vertical boundaries.
-/

noncomputable section
open Complex Real Set MeasureTheory Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletSeries

/-- The vertical integrand at physical cutoff x and abscissa σ. -/
def logPerronTrace (F : ℂ → ℂ) (σ x t : ℝ) : ℂ :=
  F ((σ : ℂ)+t*I) * logPerronKernel σ (Real.log x) t

/-- The first logarithmic Perron integral, normalized with respect to the ordinate. -/
def logPerronIntegral (F : ℂ → ℂ) (σ x : ℝ) : ℂ :=
  (∫ t : ℝ, logPerronTrace F σ x t)/(2*Real.pi)

theorem logPerronTrace_eq_cpow (F : ℂ → ℂ) (σ : ℝ) {x : ℝ} (hx : 0<x) (t : ℝ) :
    logPerronTrace F σ x t =
      F ((σ : ℂ)+t*I)*(x : ℂ)^((σ : ℂ)+t*I)/(((σ : ℂ)+t*I)^2) := by
  rw [logPerronTrace, logPerronKernel, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, mul_comm ((σ : ℂ)+t*I), mul_div_assoc]

/-- The ordinary absolute-line formula in terms of the normalized integral. -/
theorem logWeightedSum_eq_logPerronIntegral {a : ℕ → ℂ} {x σ : ℝ} (hx : 0<x) (hσ : 0<σ)
    (h : LSeriesSummable a (σ : ℂ)) : logWeightedSum a x = logPerronIntegral (LSeries a) σ x := by
  rw [logWeightedSum_eq_perron hx hσ h, logPerronIntegral]
  simp_rw [logPerronTrace_eq_cpow _ _ hx]

/-- Absolute convergence of the series on a positive line gives absolute
integrability of the logarithmic Perron trace. -/
theorem integrable_logPerronTrace_LSeries {a : ℕ → ℂ} {σ : ℝ} (hσ : 0<σ)
    (h : LSeriesSummable a (σ : ℂ)) (x : ℝ) : Integrable (logPerronTrace (LSeries a) σ x) := by
  have H := DirichletFrequency.logarithmic.integrable_sum_logPerron (fun n => a (n+1)) hσ
    ((DirichletFrequency.logarithmic_absConvergesAt a _).mpr h) (Real.log x)
  apply H.congr (ae_of_all _ fun t => ?_)
  change DirichletFrequency.logarithmic.sum (fun n => a (n+1)) ((σ : ℂ)+t*I) * _ = _
  rw [DirichletFrequency.logarithmic_sum a, logPerronTrace,
    (h.of_re_le_re (by simp : (σ : ℂ).re ≤ ((σ : ℂ)+t*I).re)).dirichletSum_eq_LSeries]

/-- The modulus of the vertical trace factors into the cutoff power and
the boundary norm divided by the squared distance from zero. -/
theorem norm_logPerronTrace (F : ℂ → ℂ) (σ x t : ℝ) :
    ‖logPerronTrace F σ x t‖ = Real.exp (σ*Real.log x) * (‖F ((σ : ℂ)+t*I)‖ / ‖(σ : ℂ)+t*I‖^2) := by
  have hre : (((σ : ℂ)+t*I)*(Real.log x : ℝ)).re = σ*Real.log x := by simp [Complex.mul_re]
  rw [logPerronTrace, logPerronKernel, norm_mul, norm_div, norm_pow, Complex.norm_exp, hre]
  ring

/-- A boundary norm integrable against `dt/|s|²` yields an integrable
Perron trace for every positive cutoff. -/
theorem integrable_logPerronTrace_of_norm {F : ℂ → ℂ} {σ : ℝ} (hσ : 0<σ)
    (hc : Continuous fun t : ℝ => F ((σ : ℂ)+t*I))
    (hi : Integrable fun t : ℝ => ‖F ((σ : ℂ)+t*I)‖ / ‖(σ : ℂ)+t*I‖^2)
    (x : ℝ) : Integrable (logPerronTrace F σ x) := by
  have hm : AEStronglyMeasurable (logPerronTrace F σ x) volume :=
    (hc.mul (continuous_logPerronKernel hσ (Real.log x))).aestronglyMeasurable
  exact (hi.const_mul (Real.exp (σ*Real.log x))).mono' hm
    (ae_of_all _ fun t => (norm_logPerronTrace F σ x t).le)

/-- A numerator of at most linear growth on the strip has equal normalized
Perron integrals on its two positive, integrable boundary lines. -/
theorem logPerronIntegral_shift {F : ℂ → ℂ} {a b x C : ℝ} (ha : 0<a) (hab : a≤b)
    (hf : DifferentiableOn ℂ F {z : ℂ | z.re ∈ Icc a b}) (hC : 0≤C)
    (growth : ∀ z : ℂ, z.re ∈ Icc a b → ‖F z‖ ≤ C*(1+‖z‖))
    (left : Integrable (logPerronTrace F a x)) (right : Integrable (logPerronTrace F b x)) :
    logPerronIntegral F a x = logPerronIntegral F b x := by
  let u := Real.log x
  let G (z : ℂ) := F z * (Complex.exp (z*u) / z^2)
  let K := C*(b+2)*Real.exp (b*|u|)
  have hg : DifferentiableOn ℂ G {z : ℂ | z.re ∈ Icc a b} := by
    have he : Differentiable ℂ (fun z : ℂ => Complex.exp (z*(u : ℂ))) := by fun_prop
    have hpow : Differentiable ℂ (fun z : ℂ => z^2) := differentiable_id.pow 2
    exact hf.mul (he.differentiableOn.div hpow.differentiableOn (fun z hz =>
      pow_ne_zero _ fun h => (ha.trans_le hz.1).ne' (by rw [h]; rfl)))
  have li : Integrable (fun t : ℝ => G ((a : ℂ)+t*I)) := left
  have ri : Integrable (fun t : ℝ => G ((b : ℂ)+t*I)) := right
  have H := integral_verticalLine_eq_of_boundary_decay (F := G) hab hg li ri
    (w := fun T : ℝ => K/T) (tendsto_const_nhds.div_atTop tendsto_id) (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      intro v hv y hy
      have hy' : |y|=T := by rcases hy with h|h <;> simp_all [abs_of_nonneg (by linarith : 0≤T)]
      let z := (v : ℂ)+y*I
      have hv₀ := ha.le.trans hv.1
      have hT₀ := zero_lt_one.trans_le hT
      have hn : ‖z‖ ≤ v+T := (norm_add_le ..).trans_eq (by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv₀, hy'])
      have hlin : 1+‖z‖ ≤ (b+2)*T := by
        nlinarith only [hn, hv.2, hT, mul_nonneg ((ha.le.trans hab)) (sub_nonneg.mpr hT)]
      have hE : Real.exp (v*u) ≤ Real.exp (b*|u|) :=
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self u) hv₀)).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hv.2 (abs_nonneg u)))
      have hnorm : T ≤ ‖z‖ := by simpa [z, hy'] using Complex.abs_im_le_norm z
      have hden := pow_le_pow_left₀ hT₀.le hnorm 2
      change ‖F z * (Complex.exp (z*u)/z^2)‖ ≤ _
      rw [norm_mul, norm_div, norm_pow, Complex.norm_exp, ← mul_div_assoc]
      have hre : (z*(u : ℂ)).re = v*u := by simp [z, Complex.mul_re]
      rw [hre]
      calc
        _ ≤ (C*((b+2)*T)*Real.exp (b*|u|)) / T^2 := by
          exact div_le_div₀ (by positivity [ha.le.trans hab])
            (mul_le_mul ((growth z (by simpa [z] using hv)).trans (mul_le_mul_of_nonneg_left hlin hC)) hE
              (Real.exp_pos _).le (by positivity [ha.le.trans hab])) (sq_pos_of_pos hT₀) hden
        _ = K/T := by dsimp only [K]; field_simp)
  exact congrArg (fun v : ℂ => v/(2*Real.pi)) H

/-- Recover a logarithmically weighted coefficient sum on a positive line
to the left of absolute convergence, given an analytic continuation with
linear strip growth and an integrable left trace. -/
theorem logWeightedSum_eq_of_logPerronContinuation {c : ℕ → ℂ} {F : ℂ → ℂ} {a b x C : ℝ}
    (hx : 0<x) (ha : 0<a) (hab : a≤b) (h : LSeriesSummable c (b : ℂ))
    (hf : DifferentiableOn ℂ F {z : ℂ | z.re ∈ Icc a b}) (hC : 0≤C)
    (growth : ∀ z : ℂ, z.re ∈ Icc a b → ‖F z‖ ≤ C*(1+‖z‖))
    (right : ∀ t : ℝ, F ((b : ℂ)+t*I) = LSeries c ((b : ℂ)+t*I))
    (left : Integrable (logPerronTrace F a x)) :
    logWeightedSum c x = logPerronIntegral F a x := by
  have hb := ha.trans_le hab
  have eq : logPerronTrace F b x = logPerronTrace (LSeries c) b x :=
    funext fun t => by simp only [logPerronTrace, right]
  have hi := integrable_logPerronTrace_LSeries hb h x
  have shift := logPerronIntegral_shift ha hab hf hC growth left (eq ▸ hi)
  rw [shift, logWeightedSum_eq_logPerronIntegral hx hb h, logPerronIntegral, logPerronIntegral, eq]

end AnalyticNumberTheory.DirichletSeries
