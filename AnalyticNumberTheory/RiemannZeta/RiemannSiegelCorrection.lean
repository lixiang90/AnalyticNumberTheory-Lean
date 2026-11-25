import AnalyticNumberTheory.AnalyticTools.MordellEvaluation
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The first Riemann–Siegel coefficient

The integral definition extends the elementary cosine quotient continuously
through its two removable singularities on the interval [0,2].
-/
noncomputable section
open Real Complex Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private def phaseFactor (c : ℝ) : ℂ := 2*Real.pi*Complex.exp (((Real.pi*(c^2/2-5/8):ℝ):ℂ)*I)
private theorem phaseFactor_ne (c : ℝ) : phaseFactor c≠0 := by unfold phaseFactor;apply mul_ne_zero _ (Complex.exp_ne_zero _);norm_num [Real.pi_ne_zero]

/-- The real Riemann–Siegel coefficient in the variable c=2{√(t/(2π))}
for the ordinary zeta function. -/
def riemannSiegelCorrection (c : ℝ) : ℝ := (mordellIntegral c Real.pi/phaseFactor c).re

theorem continuous_riemannSiegelCorrection : Continuous riemannSiegelCorrection := by
  apply Complex.continuous_re.comp
  exact continuous_mordellIntegral_upper.div (by unfold phaseFactor;fun_prop) phaseFactor_ne

theorem cos_mul_riemannSiegelCorrection (c : ℝ) :
    Real.cos (Real.pi*c)*riemannSiegelCorrection c=Real.cos (Real.pi*(c^2/2-c-1/8)) := by
  have he : ((Real.cos (Real.pi*c):ℝ):ℂ)*(mordellIntegral c Real.pi/phaseFactor c)=
      ((Real.cos (Real.pi*(c^2/2-c-1/8)):ℝ):ℂ) := by
    rw [←mul_div_assoc,cos_mul_mordellIntegral]
    change phaseFactor c*_ / phaseFactor c=_
    field_simp [phaseFactor_ne c]
  simpa only [Complex.re_ofReal_mul,Complex.ofReal_re,riemannSiegelCorrection] using congrArg Complex.re he

/-- The integral coefficient is the elementary cosine quotient away from its removable singularities. -/
theorem riemannSiegelCorrection_eq_cos_quotient {c : ℝ} (hc : Real.cos (Real.pi*c)≠0) :
    riemannSiegelCorrection c=Real.cos (Real.pi*(c^2/2-c-1/8))/Real.cos (Real.pi*c) := by
  apply (eq_div_iff hc).mpr
  rw [mul_comm,cos_mul_riemannSiegelCorrection]

/-- The Gaussian integral equals its unit phase times the real coefficient,
including at every half-integral parameter. -/
theorem mordellIntegral_eq_riemannSiegelCorrection (c : ℝ) :
    mordellIntegral c Real.pi =
      2*Real.pi*Complex.exp (((Real.pi*(c^2/2-5/8):ℝ):ℂ)*I)*(riemannSiegelCorrection c:ℂ) := by
  have hd : Dense (Set.range (fun n : ℤ => (2*(n:ℝ)+1)/2))ᶜ := (Set.countable_range _).dense_compl ℝ
  have he : (fun u : ℝ => mordellIntegral u Real.pi)=fun u : ℝ => phaseFactor u*(riemannSiegelCorrection u:ℂ) := by
    apply Continuous.ext_on hd continuous_mordellIntegral_upper
      ((show Continuous phaseFactor by unfold phaseFactor;fun_prop).mul (Complex.continuous_ofReal.comp continuous_riemannSiegelCorrection))
    intro u hu
    have hne : Real.cos (Real.pi*u)≠0 := by
      intro hh;obtain ⟨n,hn⟩ := Real.cos_eq_zero_iff.mp hh
      apply hu;refine ⟨n,?_⟩
      apply mul_left_cancel₀ Real.pi_ne_zero
      linarith
    change mordellIntegral u Real.pi=phaseFactor u*(riemannSiegelCorrection u:ℂ)
    rw [mordellIntegral_eq_cos_quotient hne,riemannSiegelCorrection_eq_cos_quotient hne];rfl
  exact congrFun he c

private theorem removable_product_deriv {f g u : ℝ → ℝ} {c f' g' : ℝ}
    (hf : HasDerivAt f f' c) (hg : HasDerivAt g g' c) (h0 : f c=0)
    (hu : ContinuousAt u c) (he : ∀ x, f x*u x=g x) : f'*u c=g' := by
  have hg0 : g c=0 := by rw [←he,h0,zero_mul]
  have H := hf.tendsto_slope.mul (hu.tendsto.mono_left nhdsWithin_le_nhds)
  apply tendsto_nhds_unique H (hg.tendsto_slope.congr' _)
  filter_upwards with x
  rw [slope_def_field,slope_def_field,h0,hg0,sub_zero,sub_zero,←he]
  ring

private theorem correction_at_cos_zero (c : ℝ) (h : Real.cos (Real.pi*c)=0)
    (hA : Real.sin (Real.pi*(c^2/2-c-1/8))= -1) :
    -Real.sin (Real.pi*c)*riemannSiegelCorrection c = c-1 := by
  have hf := ((hasDerivAt_id c).const_mul Real.pi).cos
  have hpoly : HasDerivAt (fun x : ℝ => Real.pi*(x^2/2-x-1/8)) (Real.pi*(c-1)) c := by
    convert (((((hasDerivAt_pow 2 c).div_const 2).sub (hasDerivAt_id c)).sub_const (1/8)).const_mul Real.pi) using 1
    · funext x;rfl
    · norm_num
  have H := removable_product_deriv hf hpoly.cos h continuous_riemannSiegelCorrection.continuousAt cos_mul_riemannSiegelCorrection
  simp only [id_eq,mul_one,hA,neg_neg,one_mul] at H
  apply mul_left_cancel₀ Real.pi_ne_zero
  linear_combination H

/-- The first removable value of the cosine quotient. -/
@[simp] theorem riemannSiegelCorrection_one_half : riemannSiegelCorrection (1/2)=1/2 := by
  have H := correction_at_cos_zero (1/2) (by rw [show Real.pi*(1/2)=Real.pi/2 by ring,Real.cos_pi_div_two])
    (by rw [show Real.pi*((1/2)^2/2-1/2-1/8)=-(Real.pi/2) by ring,Real.sin_neg,Real.sin_pi_div_two])
  rw [show Real.pi*(1/2)=Real.pi/2 by ring,Real.sin_pi_div_two] at H
  linarith

/-- The second removable value of the cosine quotient. -/
@[simp] theorem riemannSiegelCorrection_three_halves : riemannSiegelCorrection (3/2)=1/2 := by
  have he : Real.pi*(3/2)=Real.pi/2+Real.pi := by ring
  have H := correction_at_cos_zero (3/2) (by rw [he,Real.cos_add_pi,Real.cos_pi_div_two,neg_zero])
    (by rw [show Real.pi*((3/2)^2/2-3/2-1/8)=-(Real.pi/2) by ring,Real.sin_neg,Real.sin_pi_div_two])
  rw [he,Real.sin_add_pi,Real.sin_pi_div_two] at H
  linarith

end AnalyticNumberTheory.RiemannZeta
