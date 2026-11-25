import AnalyticNumberTheory.RiemannZeta.FourthMomentMainTerms
import AnalyticNumberTheory.RiemannZeta.RiemannDualGamma

/-!
# Reflection in the fourth moment

The zeta functional-equation multiplier is holomorphic away from the real
axis. Its size on a fixed strip allows the reflected main term to be
continued from the critical line to a vertical contour on the right.
-/

open Real Complex Set
open scoped ComplexConjugate
namespace AnalyticNumberTheory.RiemannZeta

/-- The functional-equation multiplier is analytic at every nonreal point. -/
theorem analyticAt_riemannDualGamma {s : ℂ} (hs : s.im≠0) :
    AnalyticAt ℂ riemannDualGamma s := by
  let U := {z : ℂ | z.im≠0}
  have hU : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const
  apply DifferentiableOn.analyticOnNhd (s:=U) _ hU s hs
  intro z hz
  have hg := Complex.differentiableAt_Gamma (1-z) (by
    intro m he
    have hi := congrArg Complex.im he
    exact hz (by simpa using hi))
  have hπ : (2*(Real.pi:ℂ))≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
  rw [show riemannDualGamma = (fun w : ℂ => 2*(2*(Real.pi:ℂ))^(-(1-w))*Complex.Gamma (1-w)*Complex.cos (Real.pi*(1-w)/2)) from funext fun w => riemannDualGamma_eq_gamma_cos w]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · apply DifferentiableAt.const_mul
      exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -(1-w)) z).const_cpow (Or.inl hπ)
    · exact hg.comp z (by fun_prop)
  · fun_prop

/-- The sharp power of the height on the contour from the critical line to
real part two. -/
theorem norm_riemannDualGamma_fourthMoment_strip :
    ∃ C : ℝ,0<C ∧ ∀ {s : ℂ}, 1/2≤s.re → s.re≤2 → 2≤s.im →
      ‖riemannDualGamma s‖≤C*s.im^(1/2-s.re) := by
  obtain ⟨C,hC,H⟩ := norm_riemannDualGamma_on_strip (1/2) 2
  refine ⟨C,hC,?_⟩
  intro s hs hs' ht
  have hpos : 0≤s.im := by linarith
  simpa only [abs_of_nonneg hpos] using H s ⟨hs,hs'⟩ (by rw [abs_of_nonneg hpos]; linarith)

/-- The gamma-factor ratio on the critical line, including height zero. -/
theorem riemannDualGamma_critical_eq_ratio {s : ℂ} (hs : s.re=1/2) :
    riemannDualGamma s=Gammaℝ (1-s)/Gammaℝ s := by
  rw [riemannDualGamma_eq_gamma_cos,←Gammaℝ_div_Gammaℝ_one_sub]
  · simp
  · intro n he
    have hr := congrArg Complex.re he
    simp [Complex.mul_re,hs] at hr
    linarith [show (0:ℝ)≤n by positivity]

private theorem one_sub_eq_conj_of_critical {s : ℂ} (hs : s.re=1/2) : 1-s=conj s := by
  apply Complex.ext <;> simp [hs] ; ring

/-- The reflection phase is a unit in modulus at every height on the critical line. -/
theorem norm_riemannDualGamma_critical {s : ℂ} (hs : s.re=1/2) :
    ‖riemannDualGamma s‖=1 := by
  rw [riemannDualGamma_critical_eq_ratio hs,one_sub_eq_conj_of_critical hs,
    Complex.Gammaℝ_conj,norm_div,Complex.norm_conj,div_self]
  exact norm_ne_zero_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num))

/-- Reflection and conjugation for the square of zeta on the critical line. -/
theorem riemannDualGamma_sq_mul_conj_zeta_sq {s : ℂ} (hs : s.re=1/2) :
    riemannDualGamma s^2*conj (riemannZeta s^2)=riemannZeta s^2 := by
  have hne : s≠0 := fun he => by norm_num [he] at hs
  have hre : (1-s).re=1/2 := by simp [hs]; ring
  have hne' : 1-s≠0 := fun he => by norm_num [he] at hre
  have hg := Gammaℝ_ne_zero_of_re_pos (show 0<(1-s).re by rw [hre]; norm_num)
  have h : riemannDualGamma s*riemannZeta (1-s)=riemannZeta s := by
    rw [riemannDualGamma_critical_eq_ratio hs,riemannZeta_def_of_ne_zero hne,
      riemannZeta_def_of_ne_zero hne',completedRiemannZeta_one_sub]
    field_simp [hg]
  rw [one_sub_eq_conj_of_critical hs,riemannZeta_conj] at h
  rw [map_pow,←mul_pow,h]

/-- The ratio of xi-completion factors agrees with the reflection multiplier. -/
theorem xiCompletionFactor_reflection_critical {s : ℂ} (hs : s.re=1/2) :
    xiCompletionFactor (1-s)/xiCompletionFactor s=riemannDualGamma s := by
  have h₀ : s≠0 := fun he => by norm_num [he] at hs
  have h₁ : s≠1 := fun he => by norm_num [he] at hs
  rw [riemannDualGamma_critical_eq_ratio hs,xiCompletionFactor,xiCompletionFactor]
  field_simp [h₀,sub_ne_zero.mpr h₁]; ring

/-- Exact reflected divisor polynomial in the unweighted fourth-moment approximation. -/
theorem fourthMomentMainTerm_true_eq_reflected (N : ℕ) (t : ℝ) :
    let s := (1/2:ℂ)+t*I
    fourthMomentMainTerm N true t=riemannDualGamma s^2*divisorPolynomial N (1-s) := by
  let s := (1/2:ℂ)+t*I
  have hs : s.re=1/2 := by simp [s]
  have href : (1/2:ℂ)+((-t:ℝ):ℂ)*I=1-s := by dsimp [s]; push_cast; ring
  change (xiCompletionFactor _^2/xiCompletionFactor s^2)*divisorPolynomial N _=_
  simp only [ite_true]
  rw [href,←div_pow,xiCompletionFactor_reflection_critical hs]

/-- The first main term is the ordinary divisor polynomial. -/
theorem fourthMomentMainTerm_false_eq_polynomial (N : ℕ) (t : ℝ) :
    fourthMomentMainTerm N false t=divisorPolynomial N ((1/2:ℂ)+t*I) := by
  let s := (1/2:ℂ)+t*I
  have hs : s.re=1/2 := by simp [s]
  have h₀ : s≠0 := fun he => by norm_num [he] at hs
  have h₁ : s≠1 := fun he => by norm_num [he] at hs
  have hne : xiCompletionFactor s≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num : (1/2:ℂ)≠0) h₀) (sub_ne_zero.mpr h₁))
    (Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num))
  change (xiCompletionFactor s^2/xiCompletionFactor s^2)*divisorPolynomial N s=_
  rw [div_self (pow_ne_zero 2 hne),one_mul]

/-- Conjugation followed by the squared reflection phase interchanges the
two main terms on the critical line. -/
theorem fourthMomentMainTerm_true_eq_mul_conj (N : ℕ) (t : ℝ) :
    fourthMomentMainTerm N true t=riemannDualGamma ((1/2:ℂ)+t*I)^2*
      conj (fourthMomentMainTerm N false t) := by
  rw [fourthMomentMainTerm_true_eq_reflected,fourthMomentMainTerm_false_eq_polynomial,
    one_sub_eq_conj_of_critical (by simp : ((1/2:ℂ)+t*I).re=1/2),divisorPolynomial_conj]

end AnalyticNumberTheory.RiemannZeta
