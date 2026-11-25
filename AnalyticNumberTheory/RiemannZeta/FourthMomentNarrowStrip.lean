import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.NearLineInterpolation
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PairedVerticalIntegrals
import AnalyticNumberTheory.RiemannZeta.FourthMomentLog
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-!
# Zeta's fourth moment in a logarithmically narrow strip

A paired vertical integral is holomorphic in its base point, and equals
the real fourth moment when the base point is real. Finite-rectangle
interpolation transfers the critical-line bound to nearby vertical lines.
-/

open Real Complex Set MeasureTheory
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

private theorem zeta_quarter_strip_linear :
    ∃ A : ℝ,0<A ∧ ∀ z : ℂ,z.re∈Icc (1/4:ℝ) (3/4) → ‖riemannZeta z‖≤A*(1+|z.im|) := by
  obtain ⟨B,hB,H⟩ := norm_riemannZeta_critical_strip_le_of_two_le (ε:=1/2) (by norm_num)
  let U := Icc (1/4:ℝ) (3/4) ×ℂ Icc (-2:ℝ) 2
  have hc : IsCompact U := isCompact_Icc.reProdIm isCompact_Icc
  have hf : ContinuousOn (fun z : ℂ => ‖riemannZeta z‖) U := by
    intro z hz
    have h := hz.1.2
    exact (differentiableAt_riemannZeta (by intro he;norm_num [he] at h)).continuousAt.norm.continuousWithinAt
  obtain ⟨D,hD⟩ := hc.bddAbove_image hf
  let A := 1+B+|D|
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro z hz
  by_cases ht : 2≤|z.im|
  · have hh := H (σ:=z.re) (t:=z.im) ⟨by linarith [hz.1],by linarith [hz.2]⟩ ht
    rw [Complex.re_add_im] at hh
    have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤|z.im|)
      (by linarith [hz.1] : (1-z.re)/2+1/2≤1)
    rw [Real.rpow_one] at hpow
    apply hh.trans
    exact mul_le_mul (by dsimp [A]; linarith [abs_nonneg D]) (by linarith only [hpow]) (by positivity) hA.le
  · have hh := hD (show ‖riemannZeta z‖∈(fun z : ℂ => ‖riemannZeta z‖) '' U from ⟨z,⟨hz,abs_le.mp (le_of_not_ge ht)⟩,rfl⟩)
    apply hh.trans
    exact (show D≤A by dsimp [A]; linarith [le_abs_self D]).trans (by nlinarith [mul_nonneg hA.le (abs_nonneg z.im)])

private noncomputable def fourthMomentPair (T : ℝ) :=
  pairedVerticalIntegral (fun w : ℂ => riemannZeta w^2) (fun w : ℂ => riemannZeta w^2) 0 T

private theorem analytic_zeta_sq_off_one {z : ℂ} (hz : z≠1) : AnalyticAt ℂ (fun w => riemannZeta w^2) z :=
  ((DifferentiableOn.analyticOnNhd (s:={(1:ℂ)}ᶜ) (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
      isOpen_compl_singleton z hz).pow 2)

private theorem fourthMomentPair_differentiable (T : ℝ) {z : ℂ} (hz : z.re∈Ioo (0:ℝ) 1) :
    DifferentiableAt ℂ (fourthMomentPair T) z :=
  differentiableAt_pairedVerticalIntegral (l:=0) (u:=1)
    (fun w hw => analytic_zeta_sq_off_one (by intro he; have := hw.2; simp [he] at this))
    (fun w hw => analytic_zeta_sq_off_one (by intro he; have := hw.2; simp [he] at this)) 0 T hz

private theorem fourthMomentPair_real (T σ : ℝ) :
    fourthMomentPair T σ=((∫ t in (0:ℝ)..T, ‖riemannZeta ((σ:ℂ)+t*I)‖^4:ℝ):ℂ) := by
  rw [←intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  have hconj : (σ:ℂ)-t*I=conj ((σ:ℂ)+t*I) := by simp;ring
  change riemannZeta _^2*riemannZeta _^2=_
  rw [hconj,riemannZeta_conj,←mul_pow,Complex.mul_conj]
  push_cast
  rw [←Complex.sq_norm]
  push_cast
  ring

/-- The critical-line fourth moment on a symmetric interval, with arbitrary real upper endpoint. -/
theorem fourthMoment_riemannZeta_symmetric_log_le :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ}, 1≤T →
      (∫ t in -T..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^4) ≤ C*T*(1+Real.log T)^4 := by
  obtain ⟨D,hD,H⟩ := fourthMoment_riemannZeta_log_le
  let f (t : ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖^4
  have hf : Continuous f := continuous_riemannZeta_half.norm.pow 4
  let A := ∫ t in (0:ℝ)..1, f t
  have hA : 0≤A := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => pow_nonneg (norm_nonneg _) _)
  refine ⟨2*(A+D),by positivity,?_⟩
  intro T hT
  have hs := intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable («μ»:=volume) 0 1) (hf.intervalIntegrable («μ»:=volume) 1 T)
  have ht := intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable («μ»:=volume) (-T) 0) (hf.intervalIntegrable («μ»:=volume) 0 T)
  have hr := intervalIntegral.integral_comp_neg (a:=(0:ℝ)) (b:=T) f
  have he (t : ℝ) : f (-t)=f t := by
    have he : (1/2:ℂ)+((-t:ℝ):ℂ)*I=conj ((1/2:ℂ)+t*I) := by push_cast; simp [map_ofNat]
    dsimp only [f]; rw [he,riemannZeta_conj,Complex.norm_conj]
  simp only [he,neg_zero] at hr
  have ha := le_mul_of_one_le_right hA (one_le_mul_of_one_le_of_one_le hT (one_le_pow₀ (by linarith [Real.log_nonneg hT] : 1≤1+Real.log T) (n:=4)))
  change (∫ t in -T..T,f t)≤_
  change A+(∫ t in (1:ℝ)..T,f t)=_ at hs
  have hh : (∫ t in (1:ℝ)..T,f t)≤_ := H T hT
  linarith only [hs,ht,hr,ha,hh]

set_option maxHeartbeats 500000 in
private theorem fourthMomentPair_central :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ} {z : ℂ},1≤T → z.re=1/2 → |z.im|≤T →
      ‖fourthMomentPair T z‖≤C*T*(1+Real.log T)^4 := by
  obtain ⟨A,hA,H⟩ := fourthMoment_riemannZeta_symmetric_log_le
  refine ⟨64*A,by positivity,?_⟩
  intro T z hT hz ht
  let f (t : ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖^4
  have hf : Continuous f := continuous_riemannZeta_half.norm.pow 4
  let v := z.im
  have hv : -T≤v ∧ v≤T := abs_le.mp ht
  have hp (t : ℝ) : z+t*I=(1/2:ℂ)+((v+t:ℝ):ℂ)*I := by rw [←Complex.re_add_im z]; simp [hz,v];ring
  have hm (t : ℝ) : z-t*I=(1/2:ℂ)+((v-t:ℝ):ℂ)*I := by rw [←Complex.re_add_im z];simp [hz,v];ring
  have hi (a b : ℝ) (ha : -(2*T)≤a) (hab : a≤b) (hb : b≤2*T) :
      (∫ t in a..b, f t) ≤ ∫ t in -(2*T)..2*T, f t :=
    intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) (hf.intervalIntegrable ..)
  have H' := H (T:=2*T) (by linarith)
  have hlog : 1+Real.log (2*T)≤2*(1+Real.log T) := by
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),Real.log_nonneg hT]
  have h₀ : (∫ t in -(2*T)..2*T,f t)≤32*A*T*(1+Real.log T)^4 := by
    apply H'.trans
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : 1≤2*T)]) hlog 4) (by positivity)).trans_eq (by ring)
  have h₁ := (intervalIntegral.integral_comp_add_left (a:=(0:ℝ)) (b:=T) f v).trans_le (hi _ _ (by linarith only [hv.1,hT]) (by linarith only [hT]) (by linarith only [hv.2]))
  have h₂ := (intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=T) f v).trans_le (hi _ _ (by linarith only [hv.1]) (by linarith only [hT]) (by linarith only [hv.2,hT]))
  have hci : Continuous (fun t : ℝ => riemannZeta (z+t*I)^2*riemannZeta (z-t*I)^2) := by
    simp_rw [hp,hm]
    exact ((continuous_riemannZeta_half.comp (f:=fun t : ℝ => v+t) (by fun_prop)).pow 2).mul
      ((continuous_riemannZeta_half.comp (f:=fun t : ℝ => v-t) (by fun_prop)).pow 2)
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith : (0:ℝ)≤T)).trans
  have hp' : Continuous (fun t : ℝ => f (v+t)) := hf.comp (continuous_const.add (continuous_id (X:=ℝ)) : Continuous fun t : ℝ => v+t)
  have hm' : Continuous (fun t : ℝ => f (v-t)) := hf.comp (continuous_const.sub (continuous_id (X:=ℝ)) : Continuous fun t : ℝ => v-t)
  apply (intervalIntegral.integral_mono_on (g:=fun t => f (v+t)+f (v-t)) (by linarith : (0:ℝ)≤T) (hci.norm.intervalIntegrable ..) ((hp'.add hm').intervalIntegrable ..) ?_).trans
  · rw [intervalIntegral.integral_add (hp'.intervalIntegrable ..) (hm'.intervalIntegrable ..)]
    linarith only [h₀,h₁,h₂]
  · intro t _
    change ‖riemannZeta (z+t*I)^2*riemannZeta (z-t*I)^2‖≤f (v+t)+f (v-t)
    simp only [norm_mul,norm_pow,hp,hm,f]
    generalize ‖riemannZeta ((1/2:ℂ)+((v+t:ℝ):ℂ)*I)‖=a
    generalize ‖riemannZeta ((1/2:ℂ)+((v-t:ℝ):ℂ)*I)‖=b
    nlinarith only [sq_nonneg (a^2-b^2),sq_nonneg (a*b)]

private theorem fourthMomentPair_rectangle :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ} {z : ℂ},1≤T → |z.re-1/2|≤1/4 → |z.im|≤T →
      ‖fourthMomentPair T z‖≤C*T^5 := by
  obtain ⟨A,hA,H⟩ := zeta_quarter_strip_linear
  refine ⟨(3*A)^4,by positivity,?_⟩
  intro T z hT hr hi
  have hp (r : ℝ) (hr' : |r|≤T) : ‖riemannZeta (z+r*I)‖≤3*A*T := by
    apply (H _ (by simp; constructor <;> linarith [(abs_le.mp hr).1,(abs_le.mp hr).2])).trans
    have ht : |(z+r*I).im|≤2*T := by simp; linarith only [abs_add_le z.im r,hi,hr']
    nlinarith only [mul_le_mul_of_nonneg_left (by linarith : 1+|(z+r*I).im|≤3*T) hA.le]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=T)
    (f:=fun t : ℝ => riemannZeta (z+t*I)^2*riemannZeta (z-t*I)^2) (C:=(3*A*T)^4) (by
      intro t ht
      have ht' : t∈Ioc (0:ℝ) T := (uIoc_of_le (by linarith : (0:ℝ)≤T)) ▸ ht
      have hr' : |t|≤T := by rw [abs_of_nonneg ht'.1.le];exact ht'.2
      have hm := hp (-t) (by simpa using hr')
      rw [Complex.ofReal_neg,neg_mul,←sub_eq_add_neg] at hm
      rw [norm_mul,norm_pow,norm_pow]
      exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hp t hr') 2) (pow_le_pow_left₀ (norm_nonneg _) hm 2) (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring))
  change ‖fourthMomentPair T z‖≤_
  rw [sub_zero,abs_of_nonneg (by linarith : 0≤T)] at hh
  exact hh.trans_eq (by ring)

/-- In the fixed strip of half-width one quarter the fourth moment loses
at most `exp (16 |σ−1/2| log T)` relative to the critical-line bound. -/
theorem fourthMoment_riemannZeta_interpolated :
    ∃ C : ℝ,0<C ∧ ∀ {T σ : ℝ}, 1≤T → |σ-1/2|≤1/4 →
      (∫ t in (0:ℝ)..T,‖riemannZeta ((σ:ℂ)+t*I)‖^4) ≤ C*T*(1+Real.log T)^4*
        Real.exp (16*|σ-1/2| *Real.log T) := by
  obtain ⟨A,hA,HA⟩ := fourthMomentPair_central
  obtain ⟨B,hB,HB⟩ := fourthMomentPair_rectangle
  let K := A+B
  refine ⟨K*(1+(1/4:ℝ))^4,by dsimp [K];positivity,?_⟩
  intro T σ hT hσ
  let M := K*T*(1+Real.log T)^4
  have hK : 0<K := by dsimp [K];positivity
  have hM : 0≤M := by dsimp [M];positivity
  have hL : 1≤(1+Real.log T)^4 := one_le_pow₀ (by linarith [Real.log_nonneg hT])
  have H := norm_le_near_vertical_line (f:=fourthMomentPair T) (c:=1/2) (w:=1/4) (T:=T) (M:=M) 4 (by norm_num) hT hM (fun z hz =>
    (fourthMomentPair_differentiable T (by constructor <;> linarith [hz.1.1,hz.1.2])).differentiableWithinAt) (fun z hz ht =>
    (HA hT hz ht).trans (by dsimp [M,K];gcongr <;> linarith)) (fun z hz ht => (HB hT hz ht).trans (by
      have hcoeff : B≤K*(1+Real.log T)^4 := (show B≤K by dsimp [K];linarith).trans (le_mul_of_one_le_right hK.le hL)
      have hh := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0≤T^5)
      convert hh using 1 <;> dsimp [M] <;> ring)) hσ
  rw [fourthMomentPair_real,Complex.norm_real,Real.norm_of_nonneg (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity))] at H
  apply H.trans_eq
  dsimp [M]; norm_num;ring

/-- Uniform fourth moment in the strip of width `1/(200 log T)` at every real height `T≥2`. -/
theorem fourthMoment_riemannZeta_narrow_strip :
    ∃ C : ℝ,0<C ∧ ∀ {T σ : ℝ}, 2≤T → |σ-1/2|≤1/(200*Real.log T) →
      (∫ t in (0:ℝ)..T,‖riemannZeta ((σ:ℂ)+t*I)‖^4) ≤ C*T*(Real.log T)^4 := by
  obtain ⟨A,hA,H⟩ := fourthMoment_riemannZeta_interpolated
  refine ⟨A*3^4*Real.exp 1,by positivity,?_⟩
  intro T σ hT hσ
  have hlog : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have ht : 0<Real.log T := by linarith
  have hgap := (le_div_iff₀ (by positivity : 0<200*Real.log T)).mp hσ
  have hsmall : |σ-1/2|≤1/4 := hσ.trans ((div_le_iff₀ (by positivity : 0<200*Real.log T)).mpr (by linarith))
  have hh := H (by linarith : 1≤T) hsmall
  have hl := pow_le_pow_left₀ (by linarith : 0≤1+Real.log T) (by linarith : 1+Real.log T≤3*Real.log T) 4
  rw [mul_pow] at hl
  apply hh.trans
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity : 0≤A*T))
    (Real.exp_le_exp.mpr (by linarith only [hgap] : 16*|σ-1/2| *Real.log T≤1)) (Real.exp_pos _).le (by positivity)).trans_eq (by ring)

end AnalyticNumberTheory.RiemannZeta
