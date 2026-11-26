import AnalyticNumberTheory.AdditiveNumberTheory.LinearPhaseIntegral
import AnalyticNumberTheory.AnalyticTools.Summation.Abel

/-! # Fourier transforms of sequences with a differentiable main term -/

noncomputable section

open Finset Real Complex MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A uniform approximation to all partial sums transfers to every real
Fourier frequency. Its differentiable main term contributes the Fourier
integral of its derivative. Both the cutoff and the frequency can be real. -/
theorem norm_expSum_sub_integral_of_partial_sums {x E : ℝ} (hx : 1 ≤ x)
    (a : ℕ → ℂ) (F F' : ℝ → ℂ) (h₁ : F 1 = 0)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t) (hc : ContinuousOn F' (Set.Icc 1 x))
    (hP : ∀ t ∈ Set.Icc 1 x, ‖(∑ n ∈ Icc 1 ⌊t⌋₊, a n) - F t‖ ≤ E) (z : ℝ) :
    ‖expSum a (Icc 1 ⌊x⌋₊) z - ∫ t in (1 : ℝ)..x, F' t*e (z*t)‖ ≤
      E*(1+2*Real.pi*x*|z|) := by
  let P (t : ℝ) := ∑ n ∈ Icc 1 ⌊t⌋₊, a n
  let f (t : ℝ) := e (z*t)
  let c : ℂ := 2*Real.pi*z*Complex.I
  let f' (t : ℝ) := c*f t
  have hE := (norm_nonneg _).trans (hP x ⟨hx, le_rfl⟩)
  have hdiff (t : ℝ) : HasDerivAt f (f' t) t := hasDerivAt_e_linear z t
  have hfc : Continuous f := continuous_e.comp (continuous_const.mul continuous_id)
  have hfc' : Continuous f' := continuous_const.mul hfc
  have hnorm (t : ℝ) : ‖f' t‖ = 2*Real.pi*|z| := by
    rw [←(hdiff t).deriv]
    exact norm_deriv_e_linear z t
  have hin (t : ℝ) (ht : t ∈ Set.uIcc 1 x) : t ∈ Set.Icc 1 x := by
    simpa only [Set.uIcc_of_le hx] using ht
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hd t (hin t ht)) (fun t _ => hdiff t)
    (hc.intervalIntegrable_of_Icc hx) (hfc'.intervalIntegrable 1 x)
  rw [h₁, zero_mul, sub_zero] at hparts
  have hab := abel_summation_Icc_one_hasDerivAt a hx (fun t _ => hdiff t) hfc'.continuousOn
  change expSum a (Icc 1 ⌊x⌋₊) z = P x*f x - ∫ t in (1 : ℝ)..x, P t*f' t at hab
  have hiP : IntervalIntegrable (fun t => P t*f' t) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    simpa only [P, mul_comm] using integrableOn_mul_sum_Icc a (m:=1) zero_le_one hfc'.continuousOn.integrableOn_Icc
  have hFc : ContinuousOn F (Set.Icc 1 x) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hiF : IntervalIntegrable (fun t => F t*f' t) volume 1 x :=
    (hFc.mul hfc'.continuousOn).intervalIntegrable_of_Icc hx
  have he : expSum a (Icc 1 ⌊x⌋₊) z - (∫ t in (1 : ℝ)..x, F' t*f t) =
      (P x-F x)*f x - ∫ t in (1 : ℝ)..x, (P t-F t)*f' t := by
    simp_rw [sub_mul]
    rw [hab, intervalIntegral.integral_sub hiP hiF, hparts]
    ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t => (P t-F t)*f' t) (a:=1) (b:=x) (C:=E*(2*Real.pi*|z|)) (fun t ht => by
      rw [Set.uIoc_of_le hx] at ht
      rw [norm_mul, hnorm]
      exact mul_le_mul_of_nonneg_right (hP t ⟨ht.1.le,ht.2⟩) (by positivity))
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hi
  have hend : ‖(P x-F x)*f x‖ ≤ E := by
    simpa only [f, norm_mul, norm_e, mul_one] using (hP x ⟨hx, le_rfl⟩)
  change ‖expSum a (Icc 1 ⌊x⌋₊) z - (∫ t in (1 : ℝ)..x, F' t*f t)‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans ((add_le_add hend hi).trans ?_)
  nlinarith only [mul_nonneg hE (mul_nonneg (by positivity : 0 ≤ 2*Real.pi) (abs_nonneg z))]

/-- An arithmetic main term λ(t^β−1)/β transfers with its sign and
coefficient intact. The possible exceptional zero corresponds to λ = −1,
and the linear principal term to λ = β = 1. -/
theorem norm_expSum_sub_powerWeightFourierIntegral {x E β : ℝ} (hx : 1 ≤ x) (hβ : 0 < β)
    (a : ℕ → ℂ) (v : ℂ)
    (hP : ∀ t ∈ Set.Icc 1 x, ‖(∑ n ∈ Icc 1 ⌊t⌋₊, a n) - v*(((t^β-1)/β : ℝ) : ℂ)‖ ≤ E)
    (z : ℝ) :
    ‖expSum a (Icc 1 ⌊x⌋₊) z - v*powerWeightFourierIntegral β x z‖ ≤
      E*(1+2*Real.pi*x*|z|) := by
  let F (t : ℝ) := v*(((t^β-1)/β : ℝ) : ℂ)
  let F' (t : ℝ) := v*((t^(β-1) : ℝ) : ℂ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) : HasDerivAt F (F' t) t := by
    have h := ((Real.hasDerivAt_rpow_const (p:=β) (Or.inl (zero_lt_one.trans_le ht.1).ne')).sub_const 1).div_const β
    have hd' : HasDerivAt (fun u : ℝ => (u^β-1)/β) (t^(β-1)) t := by
      convert h using 1
      field_simp
    exact hd'.ofReal_comp.const_mul v
  have hc : ContinuousOn F' (Set.Icc 1 x) := continuousOn_const.mul
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.rpow_const
      (fun t (ht : t ∈ Set.Icc 1 x) => Or.inl (zero_lt_one.trans_le ht.1).ne')))
  have h := norm_expSum_sub_integral_of_partial_sums hx a F F' (by simp [F]) hd hc hP z
  have he : (∫ t in (1 : ℝ)..x, F' t*e (z*t)) = v*powerWeightFourierIntegral β x z := by
    unfold powerWeightFourierIntegral
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => mul_assoc _ _ _)
  rwa [he] at h

end AnalyticNumberTheory.AdditiveNumberTheory
