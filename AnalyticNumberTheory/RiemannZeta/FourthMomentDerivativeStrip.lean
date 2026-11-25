import AnalyticNumberTheory.RiemannZeta.FourthMomentNarrowStrip
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.CauchyFourthMeans

/-!
# Fourth mean of the derivative of zeta near the critical line

A circle of radius `1/(400 log T)` fits inside the wider strip for the
function. Its vertical displacement costs only a factor of two in height.
-/

open Complex Real Metric Set MeasureTheory
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

private theorem zeta_analytic_on_left {z : ℂ} (h : z.re<1) : AnalyticAt ℂ riemannZeta z :=
  DifferentiableOn.analyticOnNhd (s:={(1:ℂ)}ᶜ) (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
      isOpen_compl_singleton z (show z≠1 by intro he;simp [he] at h)

private theorem zeta_line_continuous {σ : ℝ} (hσ : σ<1) :
    Continuous (fun t : ℝ => riemannZeta ((σ:ℂ)+t*I)) := continuous_iff_continuousAt.mpr (fun _ =>
  (zeta_analytic_on_left (by simpa using hσ)).continuousAt.comp (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop))

/-- The fourth moment in a doubled symmetric height window, uniform in a
logarithmic strip measured using the original height. -/
theorem fourthMoment_riemannZeta_narrow_symmetric_window :
    ∃ C : ℝ,0<C ∧ ∀ {T σ : ℝ}, 2≤T → |σ-1/2|≤1/(200*Real.log T) →
      (∫ t in -(2*T)..2*T,‖riemannZeta ((σ:ℂ)+t*I)‖^4)≤C*T*(Real.log T)^4 := by
  obtain ⟨A,hA,H⟩ := fourthMoment_riemannZeta_interpolated
  refine ⟨4*4^4*A*Real.exp 1,by positivity,?_⟩
  intro T σ hT hs
  have hlog : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have hpos : 0<Real.log T := by linarith
  have hsmall : |σ-1/2|≤1/4 := hs.trans ((div_le_iff₀ (by positivity : 0<200*Real.log T)).mpr (by linarith))
  have hwidth := (le_div_iff₀ (by positivity : 0<200*Real.log T)).mp hs
  have h₂ : 1≤2*T := by linarith
  have h₂log : Real.log (2*T)≤2*Real.log T := by
    rw [Real.log_mul (by norm_num) (by linarith)];linarith [Real.log_le_log (by norm_num) hT]
  have hh := H h₂ hsmall
  let f (t : ℝ) := ‖riemannZeta ((σ:ℂ)+t*I)‖^4
  have hf : Continuous f := (zeta_line_continuous (by linarith [(abs_le.mp hsmall).2])).norm.pow 4
  have he (t : ℝ) : f (-t)=f t := by
    have he : (σ:ℂ)+((-t:ℝ):ℂ)*I=conj ((σ:ℂ)+t*I) := by simp
    dsimp only [f];rw [he,riemannZeta_conj,Complex.norm_conj]
  have ha := intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable («μ»:=volume) (-(2*T)) 0) (hf.intervalIntegrable («μ»:=volume) 0 (2*T))
  have hb := intervalIntegral.integral_comp_neg (a:=(0:ℝ)) (b:=2*T) f
  simp only [he,neg_zero] at hb
  have hl := pow_le_pow_left₀ (by linarith [Real.log_nonneg h₂] : 0≤1+Real.log (2*T)) (by linarith : 1+Real.log (2*T)≤4*Real.log T) 4
  rw [mul_pow] at hl
  have hExp := Real.exp_le_exp.mpr (show 16*|σ-1/2| *Real.log (2*T)≤1 by
    nlinarith only [mul_le_mul_of_nonneg_left h₂log (abs_nonneg (σ-1/2)),hwidth])
  have hfull := hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity : 0≤A*(2*T))) hExp (Real.exp_pos _).le (by positivity))
  change (∫ t in (0:ℝ)..2*T,f t)≤_ at hfull
  change (∫ t in -(2*T)..2*T,f t)≤_
  linarith only [hfull,ha,hb]

/-- The fourth mean of the zeta derivative throughout the strip of width
`1/(400 log T)`, in the symmetric height interval. -/
theorem fourthMoment_deriv_riemannZeta_narrow_symmetric :
    ∃ C : ℝ,0<C ∧ ∀ {T σ : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log T) →
      (∫ t in -T..T,‖deriv riemannZeta ((σ:ℂ)+t*I)‖^4)≤C*T*(Real.log T)^8 := by
  obtain ⟨A,hA,H⟩ := fourthMoment_riemannZeta_narrow_symmetric_window
  refine ⟨400^4*A,by positivity,?_⟩
  intro T σ hT hσ
  have hlog : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have hpos : 0<Real.log T := by linarith
  let r := 1/(400*Real.log T)
  have hr : 0<r := by dsimp [r];positivity
  have hr₁ : r≤1/8 := (div_le_iff₀ (by positivity : 0<400*Real.log T)).mpr (by linarith)
  have hrσ : σ+r<1 := by linarith [(abs_le.mp hσ).2,show r=1/(400*Real.log T) from rfl]
  have hball (t : ℝ) {z : ℂ} (hz : z∈closedBall ((σ:ℂ)+t*I) r) : z.re<1 := by
    have hh := (Complex.abs_re_le_norm (z-((σ:ℂ)+t*I))).trans (by simpa [Complex.dist_eq] using hz)
    simp only [Complex.sub_re,Complex.add_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero,Complex.ofReal_re] at hh
    linarith [(abs_le.mp hh).2]
  let P (x : ℝ×ℝ) := circleMap ((σ:ℂ)+x.1*I) r x.2
  have hP : Continuous P := by dsimp [P,circleMap];fun_prop
  have hPa (x : ℝ×ℝ) := zeta_analytic_on_left (z:=P x) (hball x.1 (sphere_subset_closedBall (circleMap_mem_sphere _ hr.le _)))
  have hDiff (t : ℝ) : DifferentiableOn ℂ riemannZeta (closedBall ((σ:ℂ)+t*I) r) :=
    fun z hz => (zeta_analytic_on_left (hball t hz)).differentiableAt.differentiableWithinAt
  have hDer : Continuous (fun t : ℝ => deriv riemannZeta ((σ:ℂ)+t*I)) := continuous_iff_continuousAt.mpr (fun t =>
    (zeta_analytic_on_left (z:=(σ:ℂ)+t*I) (by simp;linarith)).deriv.continuousAt.comp (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop))
  have hCircle : Continuous (fun x : ℝ×ℝ => ‖riemannZeta (P x)‖^4) :=
    (continuous_iff_continuousAt.mpr (fun x => (hPa x).continuousAt.comp hP.continuousAt)).norm.pow 4
  have hRow (θ : ℝ) : (∫ t in -T..T, ‖riemannZeta (P (t,θ))‖^4)≤A*T*(Real.log T)^4 := by
    let v := circleMap 0 r θ
    have hnorm : ‖v‖=r := by dsimp [v];rw [norm_circleMap_zero,abs_of_pos hr]
    have hre := (Complex.abs_re_le_norm v).trans_eq hnorm
    have him := (Complex.abs_im_le_norm v).trans_eq hnorm
    have hshift : |σ+v.re-1/2|≤1/(200*Real.log T) := by
      calc |σ+v.re-1/2| = |σ-1/2+v.re| := by ring_nf
           _ ≤ |σ-1/2|+|v.re| := abs_add_le ..
           _ ≤ r+r := add_le_add hσ hre
           _ = _ := by dsimp [r];ring
    have he (t : ℝ) : P (t,θ)=((σ+v.re:ℝ):ℂ)+((t+v.im:ℝ):ℂ)*I := by
      have hh := circleMap_sub_center ((σ:ℂ)+t*I) r θ
      change P (t,θ)-_=v at hh
      rw [←Complex.re_add_im v] at hh;push_cast;linear_combination hh
    let g (t : ℝ) := ‖riemannZeta (((σ+v.re:ℝ):ℂ)+t*I)‖^4
    have hg : Continuous g := (zeta_line_continuous (by linarith [(abs_le.mp hre).2])).norm.pow 4
    simp_rw [he]
    change (∫ t in -T..T,g (t+v.im))≤_
    rw [intervalIntegral.integral_comp_add_right]
    apply (intervalIntegral.integral_mono_interval (c:=-(2*T)) (d:=2*T) (by linarith [(abs_le.mp him).1])
      (by linarith) (by linarith [(abs_le.mp him).2]) (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) (hg.intervalIntegrable ..)).trans
    exact H hT hshift
  have hh := family_deriv_fourth_le_of_circle_means (σ:=σ) ({()}:Finset Unit) (fun _ => riemannZeta) hr
    (by linarith : -T≤T) (fun _ _ t _ => hDiff t) (fun _ _ => hDer) (fun _ _ => hCircle) (fun θ _ => by simpa using hRow θ)
  simp only [Finset.sum_singleton] at hh
  exact hh.trans_eq (by dsimp [r];field_simp)

/-- The derivative fourth-moment estimate from height zero to any `T≥2`. -/
theorem fourthMoment_deriv_riemannZeta_narrow_strip :
    ∃ C : ℝ,0<C ∧ ∀ {T σ : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log T) →
      (∫ t in (0:ℝ)..T,‖deriv riemannZeta ((σ:ℂ)+t*I)‖^4)≤C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,H⟩ := fourthMoment_deriv_riemannZeta_narrow_symmetric
  refine ⟨C,hC,?_⟩
  intro T σ hT hs
  have hl : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have hσ : σ<1 := by
    have hw : 1/(400*Real.log T)≤1/4 := (div_le_iff₀ (by linarith : 0<400*Real.log T)).mpr (by linarith)
    linarith [(abs_le.mp hs).2]
  have hd : Continuous (fun t : ℝ => deriv riemannZeta ((σ:ℂ)+t*I)) := continuous_iff_continuousAt.mpr (fun t =>
    (zeta_analytic_on_left (z:=(σ:ℂ)+t*I) (by simpa using hσ)).deriv.continuousAt.comp (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop))
  exact (intervalIntegral.integral_mono_interval (a:=0) (b:=T) (c:=-T) (d:=T) (by linarith) (by linarith) le_rfl
    (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) ((hd.norm.pow 4).intervalIntegrable ..)).trans (H hT hs)

end AnalyticNumberTheory.RiemannZeta
