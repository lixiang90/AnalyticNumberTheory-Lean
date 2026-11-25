import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The entire Perron weight and reflected zero pairs

Subtracting the numerator at the origin removes the pole of the Perron
weight. Pairing a small zero with its reflection gives a uniform bound in
terms of the usual zero weights without dividing by a zero close to zero.
-/

noncomputable section

open Complex MeasureTheory Finset
open scoped ComplexConjugate

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Entire regularization of the Mellin weight `(x^s-1)/s`. -/
def perronDifferenceWeight (x : ℝ) : ℂ → ℂ :=
  dslope (fun s : ℂ => Complex.exp (Real.log x*s)) 0

/-- Value of the regularized weight at the origin. -/
@[simp] theorem perronDifferenceWeight_zero (x : ℝ) : perronDifferenceWeight x 0=(Real.log x:ℂ) := by
  rw [perronDifferenceWeight,dslope_same]
  have h := ((hasDerivAt_id (0:ℂ)).const_mul (Real.log x:ℂ)).cexp
  simpa using h.deriv

theorem differentiable_perronDifferenceWeight (x : ℝ) : Differentiable ℂ (perronDifferenceWeight x) := by
  intro z
  have ha : AnalyticAt ℂ (fun s : ℂ => Complex.exp (Real.log x*s)) z := by fun_prop
  exact (ha.dslope 0).differentiableAt

theorem perronDifferenceWeight_eq {x : ℝ} (hx : 0<x) {z : ℂ} (hz : z≠0) :
    perronDifferenceWeight x z = ((x:ℂ)^z-1)/z := by
  have h := sub_smul_dslope (fun s : ℂ => Complex.exp (Real.log x*s)) 0 z
  simp only [sub_zero,smul_eq_mul,mul_zero,Complex.exp_zero] at h
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),←Complex.ofReal_log hx.le]
  apply (eq_div_iff hz).mpr
  simpa [perronDifferenceWeight,mul_comm] using h

theorem perronDifferenceWeight_eq_integral {x : ℝ} (hx : 0<x) {z : ℂ} (hz : z≠0) :
    perronDifferenceWeight x z = ∫ u : ℝ in 0..Real.log x, Complex.exp (z*u) := by
  rw [perronDifferenceWeight_eq hx hz,integral_exp_mul_complex hz,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),←Complex.ofReal_log hx.le]
  simp [mul_comm]

/-- The bounded continuation of the weight near a small zero. -/
theorem norm_perronDifferenceWeight_le_log {x : ℝ} (hx : 1≤x) {z : ℂ} (hz : 0<z.re) :
    ‖perronDifferenceWeight x z‖ ≤ Real.log x*x^z.re := by
  have hxp : 0<x := by linarith
  have hzn : z≠0 := by intro h; simp [h] at hz
  have hlog := Real.log_nonneg hx
  rw [perronDifferenceWeight_eq_integral hxp hzn]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=Real.log x)
    (f:=fun u : ℝ => Complex.exp (z*u)) (C:=x^z.re) (by
      intro u hu
      rw [Set.uIoc_of_le hlog] at hu
      rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
        Real.rpow_def_of_pos hxp]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hu.2 hz.le]))
  simpa only [sub_zero,abs_of_nonneg hlog,mul_comm] using h

/-- Each individual regularized weight is bounded by the weights of its zero
and its functional-equation reflection, with an absolute constant. -/
theorem norm_perronDifferenceWeight_le_reflected {x : ℝ} (hx : 1≤x) {z : ℂ}
    (hz : 0<z.re) :
    ‖perronDifferenceWeight x z‖ ≤ 16*(x^z.re+x^(1-z.re))/(1+|z.im|) := by
  have hxp : 0<x := by linarith
  have hn : z≠0 := by intro h; simp [h] at hz
  have him := Complex.abs_im_le_norm z
  have hre := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have hpow : 1≤x^z.re := Real.one_le_rpow hx hz.le
  have href := Real.rpow_pos_of_pos hxp (1-z.re)
  have hden : 0<1+|z.im| := by positivity
  by_cases h : 1/4≤‖z‖
  · have ha : ‖perronDifferenceWeight x z‖ ≤ 2*x^z.re/‖z‖ := by
      rw [perronDifferenceWeight_eq hxp hn,norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      have h1 := norm_sub_le ((x:ℂ)^z) 1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp,norm_one] at h1
      linarith
    apply ha.trans
    rw [div_le_div_iff₀ (norm_pos_iff.mpr hn) hden]
    have hle : 1+|z.im|≤8*‖z‖ := by linarith [abs_nonneg z.im]
    nlinarith [mul_le_mul_of_nonneg_left hle (le_trans zero_le_one hpow),mul_nonneg href.le (norm_nonneg z)]
  · have hb := norm_perronDifferenceWeight_le_log hx hz
    have hlog := Real.log_le_rpow_div hxp.le (by norm_num : (0:ℝ)<1/4)
    have hp : x^z.re*x^(1/4:ℝ)≤x^(1-z.re) := by
      rw [←Real.rpow_add hxp]
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hb' : ‖perronDifferenceWeight x z‖ ≤ 4*x^(1-z.re) := by
      nlinarith [mul_le_mul_of_nonneg_right hlog (le_trans zero_le_one hpow)]
    apply hb'.trans
    rw [le_div_iff₀ hden]
    have hle : 1+|z.im|≤2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hle href.le]

/-- Summation with multiplicity converts both reflected weights to a single
zero sum for a primitive character. The estimate includes real zeros. -/
theorem sum_norm_perronDifferenceWeight_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) {x : ℝ} (hx : 1≤x) (a b : ℝ) :
    ∑z∈criticalStripZeroFinset χ a b,
      (analyticOrderNatAt χ.LFunction z:ℝ)*‖perronDifferenceWeight x z‖ ≤
    32*∑z∈criticalStripZeroFinset χ a b,
      (analyticOrderNatAt χ.LFunction z:ℝ)*(x^z.re/(1+|z.im|)) := by
  classical
  let Z := criticalStripZeroFinset χ a b
  let m (z : ℂ) : ℝ := analyticOrderNatAt χ.LFunction z
  let w (z : ℂ) := m z * (x^z.re/(1+|z.im|))
  let r (z : ℂ) := 1-conj z
  have hr (z : ℂ) (hz : z∈Z) : r z∈Z := by
    obtain ⟨hl,hu,ht,ht',hf⟩ := (mem_criticalStripZeroFinset χ).mp hz
    obtain ⟨hl',hu',hf'⟩ := (criticalStripZerosL_one_sub_conj_iff hχ hq z).mpr ⟨hl,hu,hf⟩
    apply (mem_criticalStripZeroFinset χ).mpr
    exact ⟨hl',hu',by simpa [r] using ht,by simpa [r] using ht',hf'⟩
  have hi (z : ℂ) : r (r z)=z := by simp [r]
  have hs : ∑z∈Z,w (r z) = ∑z∈Z,w z := by
    apply sum_bij (fun z _ => r z) hr
    · intro z hz v hv e
      simpa only [hi] using congrArg r e
    · intro z hz
      exact ⟨r z,hr z hz,hi z⟩
    · intro z hz; rfl
  calc
    _ ≤ ∑z∈Z,16*(w z+w (r z)) := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hl,hu,_,_,_⟩ := (mem_criticalStripZeroFinset χ).mp hz
      have hm : m (r z)=m z := by
        dsimp [m,r]; rw [analyticOrderNatAt_LFunction_one_sub_conj hχ hq hl hu]
      have h := mul_le_mul_of_nonneg_left (norm_perronDifferenceWeight_le_reflected hx hl)
        (show 0≤m z by dsimp [m]; positivity)
      change m z*‖perronDifferenceWeight x z‖≤_
      dsimp only [w]
      rw [hm,show (r z).re=1-z.re by simp [r],show (r z).im=z.im by simp [r]]
      exact h.trans_eq (by ring)
    _ = _ := by rw [←mul_sum,sum_add_distrib,hs]; dsimp [Z,w,m]; ring

end AnalyticNumberTheory.DirichletLFunctions
