import AnalyticNumberTheory.RiemannZeta.HadamardProduct
import Mathlib.NumberTheory.ZetaValues

/-!
# A bounded primitive of the argument of zeta on the line of real part two

Dividing the logarithmic Dirichlet coefficients by an additional logarithm
gives an absolutely convergent primitive. Its real part along a vertical
line integrates the imaginary part of the Euler-product logarithm.
On the line of real part two this is the principal argument.
-/

open Real Complex Set Filter MeasureTheory
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.RiemannZeta

/-- A bounded-coefficient Dirichlet series on the line of real part two. -/
theorem norm_LSeries_two_le {a : ℕ→ℂ} {M : ℝ} (hM : 0≤M) (ha : ∀ n,‖a n‖≤M)
    {s : ℂ} (hs : s.re=2) : ‖LSeries a s‖≤M*(π^2/6) := by
  have H (n : ℕ) : ‖LSeries.term a s n‖≤M*(1/(n:ℝ)^2) := by
    rcases Nat.eq_zero_or_pos n with rfl|hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne',norm_div,Complex.norm_natCast_cpow_of_pos hn,hs,Real.rpow_two,mul_one_div]
      exact div_le_div_of_nonneg_right (ha n) (sq_nonneg _)
  have hb := hasSum_zeta_two.summable.mul_left M
  have hsum := hb.of_nonneg_of_le (fun n => norm_nonneg _) H
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply (hsum.tsum_le_tsum H hb).trans_eq
  rw [tsum_mul_left,hasSum_zeta_two.tsum_eq]

/-- The logarithm defined by the Euler product gives the principal argument
at every point of the line `Re s = 2`. -/
theorem logZeta_im_two {s : ℂ} (hs : s.re=2) : (logZeta s).im=(riemannZeta s).arg := by
  have hσ : 1<s.re := by linarith
  have h := norm_LSeries_two_le zero_le_one norm_logZetaCoeff_le_one hs
  rw [←logZeta_eq_LSeries hσ,one_mul] at h
  have hpi := mul_le_mul_of_nonneg_left Real.pi_le_four Real.pi_pos.le
  have hp : π^2/6<π := by nlinarith only [Real.pi_pos,hpi]
  have him := (Complex.abs_im_le_norm (logZeta s)).trans_lt (h.trans_lt hp)
  have hz := Complex.log_exp (abs_lt.mp him).1 (abs_lt.mp him).2.le
  rw [exp_logZeta hσ] at hz
  simpa only [Complex.log_im] using (congrArg Complex.im hz).symm

private noncomputable def primitiveCoeff (n : ℕ) : ℂ := -logZetaCoeff n/(Real.log n:ℂ)

private theorem norm_primitiveCoeff_le (n : ℕ) : ‖primitiveCoeff n‖≤1/Real.log 2 := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt n 1 with hn|hn
  · interval_cases n <;> simp [primitiveCoeff,h₂.le]
  · have hlog : Real.log 2≤Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    rw [primitiveCoeff,norm_div,norm_neg,Complex.norm_real,Real.norm_of_nonneg (h₂.trans_le hlog).le]
    exact div_le_div₀ zero_le_one (norm_logZetaCoeff_le_one n) h₂ hlog

/-- A holomorphic primitive of the Euler-product logarithm in its half-plane
of absolute convergence. -/
noncomputable def logZetaPrimitive (s : ℂ) := LSeries primitiveCoeff s

theorem hasDerivAt_logZetaPrimitive {s : ℂ} (hs : 1<s.re) :
    HasDerivAt logZetaPrimitive (logZeta s) s := by
  have hab : LSeries.abscissaOfAbsConv primitiveCoeff≤(1:EReal) := by
    have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f:=primitiveCoeff) (x:=0)
      ⟨1/Real.log 2,fun n _ => by simpa using norm_primitiveCoeff_le n⟩
    simpa using h
  have H := hasDerivAt_LSeries (f:=primitiveCoeff) (s:=s) (hab.trans_lt (EReal.coe_lt_coe_iff.mpr hs))
  apply H.congr_deriv
  rw [logZeta_eq_LSeries hs]
  apply LSeries_congr _ s
  intro n hn
  by_cases h : n=1
  · simp [h,primitiveCoeff,logZetaCoeff]
  · have hnat : 2≤n := by omega
    have hL : 0<Real.log n := Real.log_pos (by exact_mod_cast hnat)
    have he : Complex.log (n:ℂ)=(Real.log n:ℂ) := by rw [←Complex.ofReal_natCast,Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [primitiveCoeff,he]
    have hn₀ := Complex.ofReal_ne_zero.mpr hL.ne'
    calc _ = ((Real.log n:ℂ)*logZetaCoeff n)/(Real.log n:ℂ) := by ring
         _ = _ := mul_div_cancel_left₀ _ hn₀

/-- A bounded real primitive of the principal argument along `2+it`. -/
noncomputable def argZetaPrimitive (t : ℝ) := -(logZetaPrimitive (2+t*I)).re

theorem hasDerivAt_argZetaPrimitive (t : ℝ) :
    HasDerivAt argZetaPrimitive (riemannZeta (2+t*I)).arg t := by
  let s := (2:ℂ)+t*I
  have hs : s.re=2 := by simp [s]
  have hh := hasDerivAt_logZetaPrimitive (by linarith : 1<s.re)
  have hlin : HasDerivAt (fun w : ℂ => (2:ℂ)+w*I) I (t:ℂ) := by
    simpa using (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (2:ℂ))
  have H := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hh.comp (t:ℂ) hlin).comp_ofReal)
  apply H.neg.congr_deriv
  simp only [Complex.reCLM_apply,Complex.mul_I_re,neg_neg]; exact logZeta_im_two hs

theorem abs_argZetaPrimitive_le (t : ℝ) : |argZetaPrimitive t|≤π^2/(6*Real.log 2) := by
  have hh := norm_LSeries_two_le (one_div_nonneg.mpr (Real.log_nonneg (by norm_num))) norm_primitiveCoeff_le
    (s:=(2:ℂ)+t*I) (by simp)
  rw [argZetaPrimitive,abs_neg]
  exact (Complex.abs_re_le_norm _).trans (hh.trans_eq (by ring))

/-- The principal argument of zeta is continuous on the entire vertical line of real part two. -/
theorem continuous_arg_riemannZeta_two : Continuous (fun t : ℝ => (riemannZeta (2+t*I)).arg) := by
  have he (t : ℝ) : (riemannZeta (2+t*I)).arg=(logZeta (2+t*I)).im := (logZeta_im_two (by simp)).symm
  simp_rw [he]; apply Complex.continuous_im.comp
  apply continuous_iff_continuousAt.mpr; intro t
  exact ContinuousAt.comp (f:=fun t : ℝ => (2:ℂ)+t*I)
    (hasDerivAt_logZeta (by simp : 1<((2:ℂ)+t*I).re)).continuousAt (by fun_prop)

/-- The argument integral on any oriented interval is exactly a difference
of values of a bounded primitive. -/
theorem integral_arg_riemannZeta_two (a b : ℝ) :
    (∫ t in a..b,(riemannZeta (2+t*I)).arg)=argZetaPrimitive b-argZetaPrimitive a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_argZetaPrimitive t)
    (continuous_arg_riemannZeta_two.intervalIntegrable a b)

/-- Absolute endpoint-independent bound for the principal-argument integral. -/
theorem abs_integral_arg_riemannZeta_two_le (a b : ℝ) :
    |∫ t in a..b,(riemannZeta (2+t*I)).arg|≤π^2/(3*Real.log 2) := by
  rw [integral_arg_riemannZeta_two]
  exact (abs_sub ..).trans ((add_le_add (abs_argZetaPrimitive_le b) (abs_argZetaPrimitive_le a)).trans_eq (by ring))

end AnalyticNumberTheory.RiemannZeta
