import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalCauchyShift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Higher Cauchy formulas on rectangular and infinite vertical contours

Integration by parts along the four sides reduces each higher Cauchy kernel
to the first kernel applied to a derivative. The antiderivative terms cancel
at the corners of the rectangle.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private theorem cauchy_line_parts {f : ℂ → ℂ} (p u d : ℂ) (k : ℕ) (a b : ℝ)
    (ha : ∀ t∈uIcc a b, AnalyticAt ℂ f (u+d*(t:ℂ)))
    (hn : ∀ t∈uIcc a b, u+d*(t:ℂ) ≠ p) :
    d*(∫ t in a..b, deriv f (u+d*(t:ℂ))/(u+d*(t:ℂ)-p)^(k+1)) -
      (k+1:ℂ)*(d*(∫ t in a..b, f (u+d*(t:ℂ))/(u+d*(t:ℂ)-p)^(k+2))) =
      f (u+d*(b:ℂ))/(u+d*(b:ℂ)-p)^(k+1) -
      f (u+d*(a:ℂ))/(u+d*(a:ℂ)-p)^(k+1) := by
  let P (t : ℝ) := u+d*(t:ℂ)
  let g (v : ℂ) := f v / (v-p)^(k+1)
  let f₁ (v : ℂ) := deriv f v/(v-p)^(k+1)
  let f₂ (v : ℂ) := f v/(v-p)^(k+2)
  have hdz (z : ℂ) (hz : AnalyticAt ℂ f z) (hne : z-p≠0) :
      HasDerivAt g (f₁ z-(k+1:ℂ)*f₂ z) z := by
    have hb := ((hasDerivAt_id z).sub_const p).pow (k+1)
    apply (hz.differentiableAt.hasDerivAt.div hb (pow_ne_zero _ hne)).congr_deriv
    simp only [f₁,f₂, Pi.pow_apply, Pi.sub_apply, Pi.sub_def, Function.comp_apply, id_eq,Nat.cast_add_one,Nat.add_sub_cancel,mul_one]
    rw [show k+2=k+1+1 by omega,pow_succ (z-p) (k+1)]
    field_simp [hne]
    ring
  have hd (t : ℝ) (ht : t∈uIcc a b) :
      HasDerivAt (fun x => g (P x)) (d*f₁ (P t)-(k+1:ℂ)*(d*f₂ (P t))) t := by
    have hP := (((hasDerivAt_id (t:ℂ)).const_mul d).const_add u)
    apply (((hdz (P t) (ha t ht) (sub_ne_zero.mpr (hn t ht))).comp (t:ℂ) hP).comp_ofReal).congr_deriv
    simp only [mul_one]
    ring
  have hc : Continuous P := by dsimp [P]; fun_prop
  have h₁ : ContinuousOn (fun t => f₁ (P t)) (uIcc a b) := by
    intro t ht
    have hf : ContinuousAt f₁ (P t) := (ha t ht).deriv.continuousAt.div
      ((continuousAt_id.sub continuousAt_const).pow _) (pow_ne_zero _ (sub_ne_zero.mpr (hn t ht)))
    exact (hf.comp hc.continuousAt).continuousWithinAt
  have h₂ : ContinuousOn (fun t => f₂ (P t)) (uIcc a b) := by
    intro t ht
    have hf : ContinuousAt f₂ (P t) := (ha t ht).continuousAt.div
      ((continuousAt_id.sub continuousAt_const).pow _) (pow_ne_zero _ (sub_ne_zero.mpr (hn t ht)))
    exact (hf.comp hc.continuousAt).continuousWithinAt
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_const.mul h₁).sub (continuousOn_const.mul (continuousOn_const.mul h₂))).intervalIntegrable
  have hi₁ : IntervalIntegrable (fun t => d*f₁ (P t)) volume a b := (continuousOn_const.mul h₁).intervalIntegrable
  have hi₂ : IntervalIntegrable (fun t => (k+1:ℂ)*(d*f₂ (P t))) volume a b :=
    (continuousOn_const.mul (continuousOn_const.mul h₂)).intervalIntegrable
  rw [intervalIntegral.integral_sub hi₁ hi₂] at hI
  simp only [intervalIntegral.integral_const_mul] at hI
  exact hI

/-- Higher-order Cauchy formula for an analytic function on a closed vertical strip. -/
theorem rectangleBoundary_cauchy_pow {f : ℂ → ℂ} {p z w : ℂ} (k : ℕ)
    (hf : ∀ u : ℂ, u.re∈Icc z.re w.re → AnalyticAt ℂ f u)
    (hz : z.re<p.re) (hw : p.re<w.re) (hy : z.im<p.im) (ht : p.im<w.im) :
    rectangleBoundary (fun u => f u/(u-p)^(k+1)) z w =
      2*π*I*(iteratedDeriv k f p)/(k.factorial:ℂ) := by
  induction k generalizing f with
  | zero => simpa using rectangleBoundary_cauchy_on_strip hf hz hw hy ht
  | succ k ih =>
    have hab := (hz.trans hw).le
    have H (v : ℝ) (hv : v≠p.im) :=
      cauchy_line_parts (f:=f) p ((v:ℂ)*I) 1 k z.re w.re
        (fun t h => hf _ (by simpa [uIcc_of_le hab] using h))
        (fun t _ he => hv (by simpa using congrArg Complex.im he))
    have V (v : ℝ) (hv : v≠p.re) (hs : v∈Icc z.re w.re) :=
      cauchy_line_parts (f:=f) p (v:ℂ) I k z.im w.im
        (fun t _ => hf _ (by simpa using hs))
        (fun t _ he => hv (by simpa using congrArg Complex.re he))
    have h₁ := H z.im hy.ne
    have h₂ := H w.im ht.ne'
    have h₃ := V w.re hw.ne' ⟨hab,le_rfl⟩
    have h₄ := V z.re hz.ne ⟨le_rfl,hab⟩
    simp only [one_mul,add_comm (_*I) ((_:ℝ):ℂ),mul_comm I ((_:ℝ):ℂ)] at h₁ h₂ h₃ h₄
    have hrec : (k+1:ℂ)*rectangleBoundary (fun u => f u/(u-p)^(k+2)) z w =
        rectangleBoundary (fun u => deriv f u/(u-p)^(k+1)) z w := by
      unfold rectangleBoundary
      linear_combination -h₁ + h₂ - h₃ + h₄
    rw [ih (fun u hu => (hf u hu).deriv),← iteratedDeriv_succ'] at hrec
    have hn : (k+1:ℂ)≠0 := by exact_mod_cast (Nat.succ_ne_zero k)
    have hfact : (k.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]
    field_simp [hn,hfact] at hrec ⊢
    linear_combination hrec

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
