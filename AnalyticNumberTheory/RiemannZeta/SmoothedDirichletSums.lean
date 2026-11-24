import AnalyticNumberTheory.RiemannZeta.SmoothedFunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.DirichletSeries.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Two smoothed Dirichlet sums for powers of zeta

On a right-hand vertical line we may expand the zeta function into its
absolutely convergent Dirichlet series. Integrating each frequency produces
a smooth weight depending on the center and its completed gamma factor.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-- Factor relating the entire completion `ξ(s)` and the Riemann zeta function. -/
noncomputable def xiCompletionFactor (s : ℂ) : ℂ := (1/2:ℂ)*s*(s-1)*Gammaℝ s

theorem xi_eq_completionFactor_mul {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xi s = xiCompletionFactor s * riemannZeta s := by
  rw [xi_eq_formula_of_re_pos hs h1]
  unfold xiCompletionFactor Gammaℝ
  ring

/-- The completed Mellin kernel in the Dirichlet weights before division by `n^w`. -/
noncomputable def xiGaussianKernel (s : ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  xiCompletionFactor (s+w)^k * Complex.exp (w^2)/w

/-- Gaussian-smoothed coefficient weight on the right vertical line. -/
noncomputable def xiDirichletWeight (s : ℂ) (k : ℕ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ, let w := (c:ℂ)+t*I
           xiGaussianKernel s k w / (n:ℂ)^w

/-- Absolute integrability of the Gaussian kernel on a line of Dirichlet convergence. -/
theorem integrable_xiGaussianKernel (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0 < c) (hσ : 1 < s.re+c) :
    Integrable (fun t : ℝ => xiGaussianKernel s k ((c:ℂ)+t*I)) := by
  let σ := s.re+c
  let w (t : ℝ) := (c:ℂ)+t*I
  let g (t : ℝ) := riemannZeta (s+w t)
  have hσ0 : 0 < σ := by dsimp [σ]; linarith
  have hwre (t : ℝ) : (s+w t).re = σ := by simp [w,σ]
  have hr (t : ℝ) : 1 < (s+w t).re := by rw [hwre]; exact hσ
  have hne (t : ℝ) : s+w t ≠ 1 := by intro hh; simpa [hh] using hr t
  have hg (t : ℝ) : g t ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (hr t)
  have hwc : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hh (t : ℝ) : xiGaussianKernel s k (w t) =
      xi (s+w t)^k * Complex.exp ((w t)^2) * (g t)⁻¹^k / w t := by
    rw [xi_eq_completionFactor_mul (by linarith [hr t]) (hne t),mul_pow,xiGaussianKernel]
    change _ = xiCompletionFactor (s+w t)^k*(g t)^k*Complex.exp ((w t)^2)*(g t)⁻¹^k / w t
    rw [inv_pow]
    field_simp [hg t]
  have hcw (t : ℝ) : c ≤ ‖w t‖ := by simpa [w] using Complex.re_le_norm (w t)
  have hw (t : ℝ) : w t ≠ 0 := norm_pos_iff.mp (hc.trans_le (hcw t))
  have hcont : Continuous g := continuous_iff_continuousAt.mpr (fun t =>
    ContinuousAt.comp (f := fun u : ℝ => s+w u) (differentiableAt_riemannZeta (hne t)).continuousAt
      ((continuous_const.add hwc).continuousAt))
  have hkcont : Continuous (fun t : ℝ => xiGaussianKernel s k (w t)) := by
    simp_rw [hh]
    exact ((((differentiable_xi.continuous.comp (continuous_const.add hwc)).pow k).mul
      (Complex.continuous_exp.comp (hwc.pow 2))).mul ((hcont.inv₀ hg).pow k)).div hwc hw
  obtain ⟨D,hD,hb⟩ := xi_pow_gaussian_strip_bound s k hc
  let A := σ/(σ-1)
  have hA : 0 ≤ A := by dsimp [A]; exact div_nonneg hσ0.le (sub_pos.mpr hσ).le
  have hgi (t : ℝ) : ‖(g t)⁻¹‖ ≤ A := by
    rw [norm_inv]
    have H := inv_norm_riemannZeta_le_of_one_lt_re hσ (s+w t).im
    have heq : ((s.re+c:ℝ):ℂ) + ((s+w t).im:ℂ)*I = s+w t := by
      rw [show s.re+c = (s+w t).re from (hwre t).symm, Complex.re_add_im]
    rw [heq] at H
    exact H
  apply (integrable_inv_one_add_sq.const_mul (D*A^k/c)).mono' hkcont.aestronglyMeasurable
  filter_upwards with t
  rw [hh,norm_div,norm_mul,norm_pow]
  have h₁ := hb c ⟨by linarith,le_rfl⟩ t
  change ‖xi (s+w t)^k*Complex.exp ((w t)^2)‖ ≤ _ at h₁
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (hgi t) k
  calc _ ≤ (D/(1+t^2)*A^k)/c := div_le_div₀ (by positivity) (mul_le_mul h₁ h₂ (by positivity) (by positivity)) hc (hcw t)
       _ = _ := by ring

private theorem term_sigma_continuous (a : ℕ → ℂ) (n : ℕ) {P : ℝ → ℂ} (hP : Continuous P) :
    Continuous (fun t => LSeries.term a (P t) n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero]; exact continuous_const
  · have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp_rw [LSeries.term_of_ne_zero hn,Complex.cpow_def_of_ne_zero hnC]
    exact continuous_const.div (Complex.continuous_exp.comp (continuous_const.mul hP)) (fun _ => Complex.exp_ne_zero _)

/-- Term-by-term expansion on the right vertical line. The coefficients may be any sequence
whose absolutely convergent Dirichlet series equals the indicated power of zeta. -/
theorem hasSum_xiDirichletWeight {a : ℕ → ℂ} (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0 < c)
    (hσ : 1 < s.re+c) (hcoeff : ∀ z : ℂ, 1 < z.re → LSeriesHasSum a z (riemannZeta z^k)) :
    HasSum (fun n : ℕ => LSeries.term a s n * xiDirichletWeight s k c n) (xiGaussianIntegral s k c) := by
  let w (t : ℝ) := (c:ℂ)+t*I
  let G (t : ℝ) := xiGaussianKernel s k (w t)
  let f (n : ℕ) (t : ℝ) := G t * LSeries.term a (s+w t) n
  let b (n : ℕ) := ‖LSeries.term a ((s.re+c:ℝ):ℂ) n‖
  have hwc : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hnorm (n : ℕ) (t : ℝ) : ‖f n t‖ = ‖G t‖* b n := by simp only [f,b,norm_mul,LSeries.norm_term_eq]; simp [w]
  have hG : Integrable G := integrable_xiGaussianKernel s k hc hσ
  have hfi (n : ℕ) : Integrable (f n) := by
    apply (hG.norm.mul_const (b n)).mono'
      (hG.aestronglyMeasurable.mul (term_sigma_continuous a n (continuous_const.add hwc)).aestronglyMeasurable)
    exact Eventually.of_forall (fun t => (hnorm n t).le)
  have hsb : Summable b := ((hcoeff ((s.re+c:ℝ):ℂ) (by simpa using hσ)).summable).norm
  have hS := hasSum_integral_of_summable_integral_norm hfi (show Summable (fun n => ∫ t, ‖f n t‖) by
    simp_rw [hnorm,integral_mul_const]
    exact hsb.mul_left _)
  have hterm (n : ℕ) : (∫ t, f n t) = LSeries.term a s n * xiDirichletWeight s k c n := by
    rw [xiDirichletWeight,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    by_cases hn : n = 0
    · subst n; simp [f]
    · have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp only [f,G,w,LSeries.term_of_ne_zero hn,Complex.cpow_add _ _ hnC]
      ring
  have hsum (t : ℝ) : (∑' n, f n t) = xi (s+w t)^k * Complex.exp ((w t)^2) / w t := by
    have hr : 1 < (s+w t).re := by simpa [w] using hσ
    have hne : s+w t ≠ 1 := by intro hh; simp [hh] at hr
    have he := ((hcoeff (s+w t) hr).mul_left (G t)).tsum_eq
    change (∑' n, f n t) = G t*(riemannZeta (s+w t)^k) at he
    rw [he,xi_eq_completionFactor_mul (by linarith) hne, mul_pow]
    dsimp [G,xiGaussianKernel]
    ring
  simp_rw [hsum,hterm] at hS
  exact hS


/-- For fixed center and displacement the Gaussian weight decays like `n^(-c)`. -/
theorem norm_xiDirichletWeight_le (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0 < c) (hσ : 1 < s.re+c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 0 < n → ‖xiDirichletWeight s k c n‖ ≤ M/(n:ℝ)^c := by
  let w (t : ℝ) := (c:ℂ)+t*I
  let G (t : ℝ) := xiGaussianKernel s k (w t)
  refine ⟨∫ t, ‖G t‖, integral_nonneg (fun _ => norm_nonneg _),?_⟩
  intro n hn
  have hterm (t : ℝ) : ‖G t/(n:ℂ)^(w t)‖ = ‖G t‖/(n:ℝ)^c := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hn]
    simp [w]
  have hg : Integrable G := integrable_xiGaussianKernel s k hc hσ
  have H := norm_integral_le_of_norm_le (hg.norm.div_const ((n:ℝ)^c)) (Eventually.of_forall (fun t => (hterm t).le))
  exact H.trans_eq (by rw [integral_div])

/-- Symmetric smoothed approximate functional equation as an absolutely convergent sum.
The multiplier of each half is the corresponding Gaussian integral weight. -/
theorem hasSum_completed_twoPiece {a : ℕ → ℂ} (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0 < c)
    (hr : 1 < s.re+c) (hl : 1 < (1-s).re+c)
    (hcoeff : ∀ z : ℂ, 1 < z.re → LSeriesHasSum a z (riemannZeta z^k)) :
    HasSum (fun n : ℕ => LSeries.term a s n * xiDirichletWeight s k c n +
        LSeries.term a (1-s) n * xiDirichletWeight (1-s) k c n) (2*π*xi s^k) := by
  rw [← xi_pow_gaussian_functional_equation s k hc]
  exact (hasSum_xiDirichletWeight s k hc hr hcoeff).add (hasSum_xiDirichletWeight (1-s) k hc hl hcoeff)

/-- The smoothed two-piece Dirichlet expansion of `ζ(s)^2` in the critical strip. The
coefficient of each smoothed frequency is the number of divisors of the integer. -/
theorem riemannZeta_sq_smoothed_functional_equation {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    {c : ℝ} (hr : 1 < s.re+c) (hl : 1 < (1-s).re+c) :
    let a := fun n : ℕ => (n.divisors.card:ℂ)
    HasSum (fun n : ℕ =>
      (LSeries.term a s n * xiDirichletWeight s 2 c n +
        LSeries.term a (1-s) n * xiDirichletWeight (1-s) 2 c n) /
        (2*π*xiCompletionFactor s^2))
      (riemannZeta s^2) := by
  let a := fun n : ℕ => (n.divisors.card:ℂ)
  have ha (z : ℂ) (hz : 1 < z.re) : LSeriesHasSum a z (riemannZeta z^2) := by
    rw [← LSeries_card_divisors_eq hz]
    apply LSeriesSummable.LSeriesHasSum
    exact (LSeriesSummable_congr z (f := fun n => (((ArithmeticFunction.sigma 0 n):ℕ):ℂ)) (g := a)
      (fun {n} _ => by simp [a,ArithmeticFunction.sigma_zero_apply])).mp (LSeriesSummable_sigma_zero_iff.mpr hz)
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  have hne0 : s ≠ 0 := by intro h; simp [h] at hs
  have hφ : xiCompletionFactor s ≠ 0 := by
    unfold xiCompletionFactor
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hne0) (sub_ne_zero.mpr hne)) (Gammaℝ_ne_zero_of_re_pos hs)
  have H := (hasSum_completed_twoPiece s 2 (by linarith) hr hl ha).div_const (2*π*xiCompletionFactor s^2)
  rw [xi_eq_completionFactor_mul hs hne,mul_pow] at H
  convert H using 1
  field_simp

/-- The corresponding linear approximate functional equation has coefficient one. -/
theorem riemannZeta_smoothed_functional_equation {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    {c : ℝ} (hr : 1 < s.re+c) (hl : 1 < (1-s).re+c) :
    HasSum (fun n : ℕ =>
      (LSeries.term 1 s n * xiDirichletWeight s 1 c n +
        LSeries.term 1 (1-s) n * xiDirichletWeight (1-s) 1 c n) /
        (2*π*xiCompletionFactor s))
      (riemannZeta s) := by
  have ha (z : ℂ) (hz : 1 < z.re) : LSeriesHasSum 1 z (riemannZeta z^1) := by
    rw [pow_one,← LSeries_one_eq_riemannZeta hz]
    exact (LSeriesSummable_one_iff.mpr hz).LSeriesHasSum
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  have hne0 : s ≠ 0 := by intro h; simp [h] at hs
  have hφ : xiCompletionFactor s ≠ 0 := by
    unfold xiCompletionFactor
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hne0) (sub_ne_zero.mpr hne)) (Gammaℝ_ne_zero_of_re_pos hs)
  have H := (hasSum_completed_twoPiece s 1 (by linarith) hr hl ha).div_const (2*π*xiCompletionFactor s)
  rw [pow_one,xi_eq_completionFactor_mul hs hne] at H
  convert H using 1
  field_simp

end AnalyticNumberTheory.RiemannZeta
