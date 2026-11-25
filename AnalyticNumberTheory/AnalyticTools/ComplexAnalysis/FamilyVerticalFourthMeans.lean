import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.NearLineInterpolation
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PairedVerticalIntegrals
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Interpolation of fourth means for finite holomorphic families

Pairing a function with its conjugate reflection recovers its fourth
power on a real base point without any reality condition on coefficients.
The sharper input is a single summed moment at the central abscissa.
-/

open Complex Real Set Finset MeasureTheory
open scoped ComplexConjugate
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- The paired integral for the fourth moment of an analytic function. -/
noncomputable def verticalFourthPair (f : ℂ→ℂ) (T : ℝ) :=
  pairedVerticalIntegral (fun z => f z^2) (fun z => conj (f (conj z))^2) (-T) T

theorem verticalFourthPair_real (f : ℂ→ℂ) (T σ : ℝ) :
    verticalFourthPair f T σ=((∫ t in -T..T,‖f ((σ:ℂ)+t*I)‖^4:ℝ):ℂ) := by
  rw [←intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  have h : conj ((σ:ℂ)-t*I)=(σ:ℂ)+t*I := by simp
  change f _^2*conj (f _)^2=_
  rw [h,←mul_pow,Complex.mul_conj,←Complex.sq_norm]
  push_cast;ring

theorem differentiableAt_verticalFourthPair {f : ℂ→ℂ} {l u : ℝ}
    (hf : ∀ z : ℂ,z.re∈Ioo l u → AnalyticAt ℂ f z) (T : ℝ) {z : ℂ} (hz : z.re∈Ioo l u) :
    DifferentiableAt ℂ (verticalFourthPair f T) z := by
  let U := Complex.re ⁻¹' Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  apply differentiableAt_pairedVerticalIntegral (l:=l) (u:=u) (fun w hw => (hf w hw).pow 2) _ _ _ hz
  intro w hw
  have hd : DifferentiableOn ℂ (conj ∘ f ∘ conj) U := fun v hv =>
    (differentiableAt_conj_conj_iff.mpr (hf (conj v) (by simpa [U] using hv)).differentiableAt).differentiableWithinAt
  exact (hd.analyticOnNhd hU w hw).pow 2

/-- At a central vertical translate each paired integral is dominated by
the same function's fourth moment on the doubled height interval. -/
theorem norm_verticalFourthPair_on_line {f : ℂ→ℂ} {c T : ℝ} (hT : 0≤T)
    (hf : Continuous (fun t : ℝ => f ((c:ℂ)+t*I))) {z : ℂ} (hc : z.re=c) (ht : |z.im|≤T) :
    ‖verticalFourthPair f T z‖≤2*(∫ t in -(2*T)..2*T,‖f ((c:ℂ)+t*I)‖^4) := by
  let v := z.im
  let g (t : ℝ) := ‖f ((c:ℂ)+t*I)‖^4
  have hg : Continuous g := hf.norm.pow 4
  have hv : -T≤v ∧ v≤T := abs_le.mp ht
  have hp (t : ℝ) : z+t*I=(c:ℂ)+((v+t:ℝ):ℂ)*I := by rw [←Complex.re_add_im z];simp [hc,v];ring
  have hm (t : ℝ) : conj (z-t*I)=(c:ℂ)+((t-v:ℝ):ℂ)*I := by
    rw [←Complex.re_add_im z];simp [hc,v];ring
  have hi (a b : ℝ) (ha : -(2*T)≤a) (hab : a≤b) (hb : b≤2*T) :
      (∫ t in a..b,g t)≤∫ t in -(2*T)..2*T,g t :=
    intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) (hg.intervalIntegrable ..)
  have h₁ := (intervalIntegral.integral_comp_add_left (a:=-T) (b:=T) g v).trans_le (hi _ _ (by linarith [hv.1]) (by linarith) (by linarith [hv.2]))
  have h₂ := (intervalIntegral.integral_comp_sub_right (a:=-T) (b:=T) g v).trans_le (hi _ _ (by linarith [hv.2]) (by linarith) (by linarith [hv.1]))
  have hci : Continuous (fun t : ℝ => f (z+t*I)^2*conj (f (conj (z-t*I)))^2) := by
    simp_rw [hp,hm]
    exact ((hf.comp (f:=fun t : ℝ => v+t) (by fun_prop)).pow 2).mul
      ((Complex.continuous_conj.comp (hf.comp (f:=fun t : ℝ => t-v) (by fun_prop))).pow 2)
  have hp' : Continuous (fun t : ℝ => g (v+t)) := hg.comp (f:=fun t : ℝ => v+t) (by fun_prop)
  have hm' : Continuous (fun t : ℝ => g (t-v)) := hg.comp (f:=fun t : ℝ => t-v) (by fun_prop)
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith : -T≤T)).trans
  apply (intervalIntegral.integral_mono_on (g:=fun t => g (v+t)+g (t-v)) (by linarith : -T≤T)
    (hci.norm.intervalIntegrable ..) ((hp'.add hm').intervalIntegrable ..) ?_).trans
  · rw [intervalIntegral.integral_add (hp'.intervalIntegrable ..) (hm'.intervalIntegrable ..)]
    change _≤2*(∫ t in -(2*T)..2*T,g t)
    linarith only [h₁,h₂]
  · intro t _
    change ‖f (z+t*I)^2*conj (f (conj (z-t*I)))^2‖≤g (v+t)+g (t-v)
    simp only [norm_mul,norm_pow,Complex.norm_conj,hp,hm,g]
    generalize ‖f ((c:ℂ)+((v+t:ℝ):ℂ)*I)‖=a
    generalize ‖f ((c:ℂ)+((t-v:ℝ):ℂ)*I)‖=b
    nlinarith only [sq_nonneg (a^2-b^2),sq_nonneg (a*b)]

/-- Fourth-mean interpolation for any finite family, with an independent
height and a separate conductor-height scale `X`. -/
theorem family_fourthMoment_interpolation {ι : Type*} (S : Finset ι) (f : ι→ℂ→ℂ)
    {l u c w T X K M : ℝ} (m : ℕ) (hw : 0<w) (hwT : w≤T) (hX : 1≤X)
    (hK : 0≤K) (hM : 0≤M) (hl : l<c-w) (hu : c+w<u)
    (hf : ∀ i∈S,∀ z : ℂ,z.re∈Ioo l u → AnalyticAt ℂ (f i) z)
    (hcenter : (∑i∈S,∫ t in -(2*T)..2*T,‖f i ((c:ℂ)+t*I)‖^4)≤M)
    (hrect : ∀ i∈S,∀ z : ℂ,|z.re-c|≤w → |z.im|≤2*T → ‖f i z‖≤K)
    (hscale : (S.card:ℝ)*T*K^4≤M*X^m)
    {σ : ℝ} (hσ : |σ-c|≤w) :
    (∑i∈S,∫ t in -T..T,‖f i ((σ:ℂ)+t*I)‖^4)≤
      2*M*Real.exp ((2*m/w)*|σ-c| *Real.log X) := by
  let F (z : ℂ) := ∑ i∈S,verticalFourthPair (f i) T z
  have hT := hw.trans_le hwT
  have hc : c∈Ioo l u := ⟨by linarith,by linarith⟩
  have hd : DifferentiableOn ℂ F (Icc (c-w) (c+w) ×ℂ Icc (-T) T) := by
    intro z hz;apply DifferentiableAt.differentiableWithinAt
    exact DifferentiableAt.fun_sum (fun i hi => differentiableAt_verticalFourthPair (hf i hi) T ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩)
  have hV (z : ℂ) (hz : z.re=c) (ht : |z.im|≤T) : ‖F z‖≤2*M := by
    apply (norm_sum_le ..).trans
    apply (Finset.sum_le_sum (fun i hi => norm_verticalFourthPair_on_line hT.le
      (continuous_iff_continuousAt.mpr (fun t : ℝ => ((hf i hi _ (by simpa using hc)).continuousAt.comp
        (f:=fun t : ℝ => (c:ℂ)+t*I) (by fun_prop)))) hz ht)).trans
    rw [←mul_sum];linarith only [hcenter]
  have hH (z : ℂ) (hz : |z.re-c|≤w) (ht : |z.im|≤T) : ‖F z‖≤2*M*X^m := by
    apply (norm_sum_le ..).trans
    have hp (i : ι) (hi : i∈S) : ‖verticalFourthPair (f i) T z‖≤K^4*(2*T) := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=-T) (b:=T) (C:=K^4)
        (f:=fun t : ℝ => f i (z+t*I)^2*conj (f i (conj (z-t*I)))^2) (by
          intro t hmem
          have ht' : t∈Ioc (-T) T := (uIoc_of_le (by linarith : -T≤T)) ▸ hmem
          have habs : |t|≤T := abs_le.mpr ⟨ht'.1.le,ht'.2⟩
          have hp := hrect i hi (z+t*I) (by simpa using hz) (by simp;linarith only [abs_add_le z.im t,ht,habs])
          have hm := hrect i hi (conj (z-t*I)) (by simpa using hz) (by simp;linarith only [abs_add_le (-z.im) t,show |-z.im|≤T by simpa using ht,habs])
          simp only [norm_mul,norm_pow,Complex.norm_conj]
          exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp 2) (pow_le_pow_left₀ (norm_nonneg _) hm 2)
            (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring))
      simpa only [verticalFourthPair,pairedVerticalIntegral,sub_neg_eq_add,←two_mul,abs_of_nonneg (show 0≤2*T by linarith)] using hh
    apply (Finset.sum_le_sum hp).trans
    simp only [sum_const,nsmul_eq_mul]
    nlinarith only [hscale]
  have H := norm_le_near_vertical_line_of_power_bound m hw hwT hX (by positivity : 0≤2*M) hd hV hH hσ
  dsimp only [F] at H
  simp_rw [verticalFourthPair_real] at H
  rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_of_nonneg] at H
  · exact H
  · exact Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (by linarith) (fun t _ => pow_nonneg (norm_nonneg _) _)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
