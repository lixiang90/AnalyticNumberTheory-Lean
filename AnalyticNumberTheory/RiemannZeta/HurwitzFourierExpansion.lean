import AnalyticNumberTheory.RiemannZeta.HurwitzSharpCutoff
import AnalyticNumberTheory.RiemannZeta.HurwitzFourierTails

/-!
# Fourier expansion at the sharp Hurwitz cutoff

Pairing opposite nonzero frequencies gives an absolutely summable series.
The endpoint correction in each mode is the first integration-by-parts term
of its oscillatory tail.
-/
noncomputable section
open Real Complex Filter Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- The positive Fourier frequency indexed starting at zero. -/
def hurwitzOmega (m : ℕ) : ℝ := 2*Real.pi*((m:ℝ)+1)

/-- Translation factor for a progression shifted by a. -/
def hurwitzShift (a ω : ℝ) : ℂ := Complex.exp ((-ω*a:ℝ)*I)

@[simp] theorem norm_hurwitzShift (a ω : ℝ) : ‖hurwitzShift a ω‖=1 := by
  rw [hurwitzShift,Complex.norm_exp]; simp

theorem hurwitzOmega_pos (m : ℕ) : 0<hurwitzOmega m := by dsimp [hurwitzOmega]; positivity

/-- A translated Fourier tail with its boundary term removed. -/
def hurwitzCorrectedMode (a x : ℝ) (s : ℂ) (ω : ℝ) : ℂ :=
  hurwitzShift a ω*(hurwitzTail s ω x-hurwitzMode s ω x/hurwitzFrequency ω)

theorem hurwitzMode_integrable_tail {s : ℂ} (hs : 1<s.re) (ω : ℝ) {x : ℝ} (hx : 0<x) :
    IntegrableOn (hurwitzMode s ω) (Ioi x) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) hx).mono'
  · unfold hurwitzMode; fun_prop
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun u hu => (norm_hurwitzMode s ω (hx.trans hu)).le

theorem hurwitzShift_mul_mode (a ω u : ℝ) (s : ℂ) :
    hurwitzShift a ω*hurwitzMode s ω u = Complex.exp ((ω*(u-a):ℝ)*I)*(u:ℂ)^(-s) := by
  rw [hurwitzShift,hurwitzMode,←mul_assoc,←Complex.exp_add]
  push_cast; congr 2; ring

private lemma freq_sq (ω : ℝ) : hurwitzFrequency ω^2= -(ω:ℂ)^2 := by
  rw [hurwitzFrequency,mul_pow,Complex.I_sq]; ring

theorem hurwitzCorrectedMode_eq {a x ω : ℝ} {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1)
    (hw : ω≠0) (hx : 0<x) :
    hurwitzCorrectedMode a x s ω =
      1/(ω:ℂ)^2 * (s*Complex.exp ((ω*(x-a):ℝ)*I)*(x:ℂ)^(-s-1)-
      s*(s+1)*(hurwitzShift a ω*∫ u in Ioi x,hurwitzMode (s+2) ω u)) := by
  rw [hurwitzCorrectedMode,hurwitzTail_second_order hσ hσ' hw hx,freq_sq]
  rw [show -s-1= -(s+1) by ring,mul_assoc s,←hurwitzShift_mul_mode]
  ring

private theorem translated_integral (a x : ℝ) (f : ℝ → ℂ) :
    ∫ u in Ioi (x-a),f u = ∫ v in Ioi x,f (v-a) := by
  have h := (measurePreserving_sub_right (μ:=volume) a).setIntegral_preimage_emb
    (measurableEmbedding_subRight a) f (Ioi (x-a))
  have he : (fun v : ℝ => v-a) ⁻¹' Ioi (x-a) = Ioi x := by ext v; simp
  rw [he] at h
  exact h.symm

private lemma bernoulli_mode_shift {s : ℂ} (hs : 0<s.re) (a : ℝ) {x : ℝ} (hx : 0<x) (m : ℕ) :
    ∫ v in Ioi (x-a),hurwitzBernoulliMode a s m v =
    (1/(hurwitzOmega m:ℂ)^2)*
      (hurwitzShift a (hurwitzOmega m)*(∫ u in Ioi x,hurwitzMode (s+2) (hurwitzOmega m) u)+
       hurwitzShift a (-hurwitzOmega m)*(∫ u in Ioi x,hurwitzMode (s+2) (-hurwitzOmega m) u)) := by
  rw [translated_integral a x,←integral_const_mul,←integral_const_mul,
    ←integral_add ((hurwitzMode_integrable_tail (s:=s+2) (by simp; linarith) _ hx).const_mul _)
      ((hurwitzMode_integrable_tail (s:=s+2) (by simp; linarith) _ hx).const_mul _),
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [hurwitzShift_mul_mode,hurwitzBernoulliMode,sub_add_cancel,hurwitzOmega]
  push_cast
  rw [show -(s+2)= -s-2 by ring]
  congr 1
  · ring
  · rw [neg_mul]; ring

/-- Absolutely convergent Fourier expansion of the sharp-cutoff remainder. -/
theorem hurwitzZeta_hasSum_correctedModes {a x : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : a≤x)
    {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) :
    HasSum (fun m : ℕ => hurwitzCorrectedMode a x s (hurwitzOmega m)+
      hurwitzCorrectedMode a x s (-hurwitzOmega m))
      (HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s+
        (x:ℂ)^(1-s)/(1-s)-(sawtooth (x-a):ℂ)*(x:ℂ)^(-s)) := by
  have hs : s≠1 := fun he => by simp [he] at hσ'
  have H := hurwitzZeta_eq_real_cutoff ha hx (by linarith : -1<s.re) hs
  have hb := (hasSum_bernoulliKernel_two_exp (x-a)).mul_right (s*(x:ℂ)^(-s-1))
  have hi := hasSum_hurwitzBernoulliMode ha.1 hσ (t:=s.im) (N:=x-a) (sub_nonneg.mpr hx)
  dsimp only at hi
  rw [Complex.re_add_im] at hi
  convert (hb.sub (hi.mul_left (s*(s+1)))) using 1
  · funext m
    have hw := (hurwitzOmega_pos m).ne'
    try dsimp only [Pi.sub_apply]
    rw [hurwitzCorrectedMode_eq hσ hσ' hw (ha.1.trans_le hx),
      hurwitzCorrectedMode_eq hσ hσ' (neg_ne_zero.mpr hw) (ha.1.trans_le hx),bernoulli_mode_shift hσ a (ha.1.trans_le hx)]
    simp only [Complex.ofReal_neg,neg_sq,neg_mul]
    dsimp only [hurwitzOmega]
    push_cast
    ring
  · linear_combination H

end AnalyticNumberTheory.RiemannZeta
