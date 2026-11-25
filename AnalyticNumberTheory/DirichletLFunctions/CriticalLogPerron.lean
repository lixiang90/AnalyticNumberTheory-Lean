import AnalyticNumberTheory.DirichletSeries.LogPerronContours
import AnalyticNumberTheory.DirichletLFunctions.CriticalPointwiseIntegrals
import AnalyticNumberTheory.DirichletLFunctions.HalfPlaneLinearGrowth

/-! # Logarithmic Perron inversion on the critical line for nonprincipal characters -/

open Complex Real Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem integrable_member_critical_trace {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (G : DirichletCharacter ℂ q → ℂ → ℂ) (hc : Continuous (G χ))
    (hI : Integrable fun t : ℝ => nonprincipalCriticalNorm G t / ‖(1/2 : ℂ)+t*I‖^2)
    (x : ℝ) : Integrable (logPerronTrace (G χ) (1/2) x) := by
  let z (t : ℝ) := (1/2 : ℂ)+t*I
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hne (t : ℝ) : z t ≠ 0 := by intro he; have := congrArg Complex.re he; norm_num [z] at this
  have hw : Continuous (fun t : ℝ => ‖G χ (z t)‖/‖z t‖^2) :=
    (hc.comp hz).norm.div (hz.norm.pow 2) fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne t))
  apply integrable_logPerronTrace_of_norm (by norm_num) (hc.comp (by fun_prop)) _ x
  rw [show ((1/2 : ℝ) : ℂ) = 1/2 by norm_num]
  apply hI.mono' hw.aestronglyMeasurable
  apply ae_of_all _
  intro t
  change ‖‖G χ (z t)‖ / ‖z t‖^2‖ ≤ nonprincipalCriticalNorm G t / ‖z t‖^2
  rw [Real.norm_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Real.le_sqrt_of_sq_le
  exact single_le_sum (f := fun ψ : DirichletCharacter ℂ q => ‖G ψ (z t)‖^2)
    (fun _ _ => sq_nonneg _) (mem_filter.mpr ⟨mem_univ χ,hχ⟩)

/-- Both the value and the negative derivative have an absolutely integrable
Perron trace on the critical line, including imprimitive nonprincipal characters. -/
theorem integrable_nonprincipal_critical_logPerron {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (x : ℝ) :
    Integrable (logPerronTrace χ.LFunction (1/2) x) ∧
      Integrable (logPerronTrace (fun z => -deriv χ.LFunction z) (1/2) x) := by
  obtain ⟨_,_,H⟩ := nonprincipal_critical_perron_means
  have hi := H (q := q) hq
  have hc := differentiable_LFunction_of_ne_one hχ
  have hd : Differentiable ℂ (deriv χ.LFunction) := hc.deriv
  refine ⟨integrable_member_critical_trace hχ (fun ψ => ψ.LFunction) hc.continuous hi.1 x, ?_⟩
  have hder := (integrable_member_critical_trace hχ (fun ψ => deriv ψ.LFunction) hd.continuous hi.2.1 x).neg
  have he : logPerronTrace (fun z => -deriv χ.LFunction z) (1/2) x = -logPerronTrace (deriv χ.LFunction) (1/2) x := by
    funext t
    simp only [logPerronTrace, neg_mul, Pi.neg_apply]
  rw [he]
  exact hder

/-- On the critical line the normalized integrals of L and −L′ invert the
finite logarithmic sums with coefficients χ(n) and χ(n)log n, respectively.
The cutoff can be any positive real number. -/
theorem nonprincipal_critical_logPerron_inversion {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ} (hx : 0<x) :
    logWeightedSum (fun n : ℕ => χ n) x = logPerronIntegral χ.LFunction (1/2) x ∧
      logWeightedSum (LSeries.logMul (fun n : ℕ => χ n)) x =
        logPerronIntegral (fun z => -deriv χ.LFunction z) (1/2) x := by
  have hi := integrable_nonprincipal_critical_logPerron hq hχ x
  have hc := differentiable_LFunction_of_ne_one hχ
  let C := 64*Real.sqrt q*Real.log q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hσ {z : ℂ} (hz : z.re=2) :
      LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < (z.re : EReal) := by
    rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne q) χ, hz]
    exact_mod_cast (by norm_num : (1 : ℝ)<2)
  constructor
  · apply logWeightedSum_eq_of_logPerronContinuation hx (by norm_num) (b := 2) (by norm_num)
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ (by norm_num)) hc.differentiableOn hC
      (fun z hz => (norm_LFunction_deriv_halfPlane_linear hq hχ hz.1).1) _ hi.1
    intro t
    exact DirichletCharacter.LFunction_eq_LSeries χ (by simp)
  · apply logWeightedSum_eq_of_logPerronContinuation hx (by norm_num) (b := 2) (by norm_num)
      (LSeriesSummable_logMul_of_lt_re (hσ (by norm_num))) hc.deriv.neg.differentiableOn hC
      (fun z hz => by simpa only [Pi.neg_apply, norm_neg, C] using (norm_LFunction_deriv_halfPlane_linear hq hχ hz.1).2) _ hi.2
    intro t
    simp only [Pi.neg_apply]
    rw [show ((2 : ℝ) : ℂ)=2 by norm_num, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ (s := (2 : ℂ)+t*I) (by norm_num),
      LSeries_deriv (hσ (z := (2 : ℂ)+t*I) (by norm_num)), neg_neg]

end AnalyticNumberTheory.DirichletLFunctions
