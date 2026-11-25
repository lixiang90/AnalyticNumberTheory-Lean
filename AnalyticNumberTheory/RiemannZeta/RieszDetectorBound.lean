import AnalyticNumberTheory.RiemannZeta.RieszCriticalKernel
import AnalyticNumberTheory.RiemannZeta.RieszDetectorKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Truncating the mollified Riesz detector on the critical line

The part with `|v| ≤ 4X` is controlled by a fourth-power weight. Outside
that range the linear bound for zeta and the trivial mollifier bound leave
an integrable Cauchy kernel with coefficient `O(1/X)`.
-/

open Real Complex MeasureTheory Filter Finset Set
open AnalyticNumberTheory.DirichletSeries
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem norm_mobiusPoly_le_length (X : ℕ) {s : ℂ} (hs : 0≤s.re) :
    ‖rieszMobiusPolynomial X s‖ ≤ X := by
  apply (norm_rieszMobiusPolynomial_le X hs).trans
  calc _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1:ℝ) := by
            apply sum_le_sum
            intro n _
            rw [Complex.norm_intCast]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=n)
       _ = _ := by simp [Nat.card_Icc]

private noncomputable def critArg (ρ : ℂ) (v : ℝ) : ℂ := (1/2:ℂ)+(ρ.im+v)*I
private noncomputable def shiftArg (ρ : ℂ) (v : ℝ) : ℂ := ((1/2-ρ.re:ℝ):ℂ)+v*I

private theorem add_shiftArg (ρ : ℂ) (v : ℝ) : ρ+shiftArg ρ v=critArg ρ v := by
  apply Complex.ext <;> simp [shiftArg,critArg]

private theorem norm_detector_critical_le {ρ : ℂ} (hβ : 1/2 ≤ ρ.re) (hβ' : ρ.re ≤ 1) (hγ : 1 ≤ ρ.im)
    {Y : ℝ} (hY : 0<Y) (X : ℕ) (v : ℝ) {d : ℝ} (hd : 0<d) (hdw : d≤‖shiftArg ρ v‖) :
    ‖rieszDetectorIntegrand X ρ Y (shiftArg ρ v)‖ ≤
      1458/d*Y^(1/2-ρ.re)*‖riemannZeta (critArg ρ v)‖*‖rieszMobiusPolynomial X (critArg ρ v)‖/(1+|v|)^5 := by
  let w := shiftArg ρ v
  have hr : w.re=1/2-ρ.re := by simp [w,shiftArg]
  have hi : w.im=v := by simp [w,shiftArg]
  have h := riesz_six_critical_kernel_le (ρ:=ρ) (w:=w) hγ (by linarith) (by linarith) hd hdw
  rw [hi] at h
  have hy := Complex.norm_cpow_eq_rpow_re_of_pos (y:=w) hY
  rw [hr] at hy
  rw [rieszDetectorIntegrand,norm_div,norm_mul,norm_mul,norm_mul,add_shiftArg]
  change _*_*‖1+w/(ρ-1)‖*‖(Y:ℂ)^w‖/‖rieszDenom 6 w‖ ≤ _
  rw [hy]
  apply (le_of_eq _).trans ((mul_le_mul_of_nonneg_left h (show 0 ≤
    (Y^(1/2-ρ.re)*‖riemannZeta (critArg ρ v)‖*‖rieszMobiusPolynomial X (critArg ρ v)‖) by positivity)).trans_eq _)
  all_goals simp only [div_eq_mul_inv,mul_inv_rev]; ring

private theorem continuous_detector_majorant (X : ℕ) (ρ : ℂ) :
    Continuous (fun v : ℝ => 1/(1+|v|)^4*‖riemannZeta (critArg ρ v)‖*‖rieszMobiusPolynomial X (critArg ρ v)‖) := by
  have harg : Continuous (critArg ρ) := by unfold critArg; fun_prop
  have hz : Continuous (fun v => riemannZeta (critArg ρ v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have h : critArg ρ v ≠ 1 := by intro he; have hh := congrArg Complex.re he; norm_num [critArg] at hh
    exact (differentiableAt_riemannZeta h).continuousAt.comp harg.continuousAt
  apply Continuous.mul _ ((differentiable_rieszMobiusPolynomial X).continuous.comp harg).norm
  exact (continuous_const.div ((continuous_const.add continuous_abs).pow 4) (fun v => by change (1+|v|)^4 ≠ 0; positivity)).mul hz.norm

/-- Uniform critical-line detector bound, retaining only heights `|v| ≤ 4X` in the moment term. -/
theorem rieszDetector_critical_truncation_of_length_le :
    ∃ C > (0:ℝ), ∀ᶠ T : ℕ in atTop, ∀ {X : ℕ} {Y : ℝ} {ρ : ℂ},
      X ≤ T → 1 ≤ Y → 1/Real.log T ≤ ρ.re-1/2 → ρ.re < 1 → (T:ℝ) ≤ ρ.im → ρ.im ≤ 2*T →
      ‖((Nat.factorial 6:ℂ)/(2*π))*(∫ v : ℝ, rieszDetectorIntegrand X ρ Y (((1/2-ρ.re:ℝ):ℂ)+v*I))‖ ≤
        1/16+C*(1+Real.log T)*Y^(1/2-ρ.re)*(∫ v in -(4*(T:ℝ))..4*(T:ℝ),
          (1/(1+|v|)^4)*‖riemannZeta ((1/2:ℂ)+(ρ.im+v)*I)‖*
            ‖dirichletPoly (fun n : ℕ => (ArithmeticFunction.moebius n:ℂ)) X ((1/2:ℂ)+(ρ.im+v)*I)‖) := by
  obtain ⟨B,hB,HB⟩ := riemannZeta_halfplane_linear_bound
  let A := ‖(Nat.factorial 6:ℂ)/(2*π)‖
  let D := 1458*4*B
  have hA : 0≤A := norm_nonneg _
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨1458*(A+1),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (16*A*D*π))] with T hX hlarge
  intro X Y ρ hXT hY hδ hβ hγ hγ'
  have hx : (2:ℝ) ≤ T := by exact_mod_cast hX
  have hx0 : 0 < (T:ℝ) := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hβ' : 1/2≤ρ.re := by linarith [one_div_pos.mpr hl]
  let q (v : ℝ) := 1+|v|
  let F (v : ℝ) := 1/(q v)^4*‖riemannZeta (critArg ρ v)‖*‖rieszMobiusPolynomial X (critArg ρ v)‖
  let U := 1458*(1+Real.log T)*Y^(1/2-ρ.re)
  let E := Ioc (-(4*(T:ℝ))) (4*(T:ℝ))
  have hF := continuous_detector_majorant X ρ
  have hF0 (v : ℝ) : 0≤F v := by dsimp [F,q]; positivity
  have hU : 0≤U := by dsimp [U]; positivity
  have hpow : Y^(1/2-ρ.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY (by linarith)
  have hcentral (v : ℝ) : ‖rieszDetectorIntegrand X ρ Y (shiftArg ρ v)‖ ≤ U*F v := by
    have hgap := Complex.abs_re_le_norm (shiftArg ρ v)
    have hre : (shiftArg ρ v).re=1/2-ρ.re := by simp [shiftArg]
    rw [hre,abs_of_nonpos (by linarith)] at hgap
    have h := norm_detector_critical_le hβ' hβ.le (by linarith) (by linarith : 0<Y) X v
      (one_div_pos.mpr hl) (hδ.trans (by linarith))
    have hq : 1≤q v := by dsimp [q]; linarith [abs_nonneg v]
    have hq0 : 0<q v := by linarith
    have hd := pow_le_pow_right₀ hq (show 4≤5 by decide)
    have hcoef : 1458/(1/Real.log (T:ℝ)) ≤ 1458*(1+Real.log T) := by rw [div_div_eq_mul_div]; ring_nf; linarith
    apply h.trans
    change _ / (q v)^5 ≤ _
    have hnum := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (show 0≤Y by linarith) (1/2-ρ.re)))
      (norm_nonneg (riemannZeta (critArg ρ v)))) (norm_nonneg (rieszMobiusPolynomial X (critArg ρ v)))
    apply (div_le_div₀ (by positivity) hnum (pow_pos hq0 4) hd).trans_eq
    dsimp only [U,F]; ring
  have htail (v : ℝ) (hv : 4*(T:ℝ)≤|v|) :
      ‖rieszDetectorIntegrand X ρ Y (shiftArg ρ v)‖ ≤ (D/T)*(1+v^2)⁻¹ := by
    have hq : 1≤q v := by dsimp [q]; linarith [abs_nonneg v]
    have hq0 : 0<q v := by linarith
    have hxq : (T:ℝ)≤q v := by dsimp [q]; linarith
    have hi : (shiftArg ρ v).im=v := by simp [shiftArg]
    have hw := Complex.abs_im_le_norm (shiftArg ρ v)
    rw [hi] at hw
    have h := norm_detector_critical_le hβ' hβ.le (by linarith) (by linarith : 0<Y) X v zero_lt_one
      (show 1≤‖shiftArg ρ v‖ by linarith)
    have hcim : (critArg ρ v).im=ρ.im+v := by simp [critArg]
    have hcre : (critArg ρ v).re=1/2 := by simp [critArg]
    have habs : |ρ.im|=ρ.im := abs_of_nonneg (by linarith)
    have hi' := abs_sub (ρ.im+v) ρ.im
    rw [add_sub_cancel_left,habs] at hi'
    have hip : 2≤|(critArg ρ v).im| := by rw [hcim]; linarith
    have hiz : |(critArg ρ v).im|+2 ≤ 4*q v := by
      rw [hcim]; dsimp [q]; linarith [abs_add_le ρ.im v]
    have hz := (HB (by rw [hcre]) hip).trans (mul_le_mul_of_nonneg_left hiz hB)
    have hm := (norm_mobiusPoly_le_length X (by rw [hcre]; norm_num)).trans (Nat.cast_le.mpr hXT : (X:ℝ) ≤ T)
    have hqv : 1+v^2 ≤ (q v)^2 := by dsimp [q]; nlinarith only [sq_abs v,abs_nonneg v]
    have hv2 := mul_le_mul (pow_le_pow_left₀ hx0.le hxq 2) hqv (by positivity) (sq_nonneg _)
    apply h.trans
    change _/(q v)^5 ≤ _
    calc _ ≤ (1458*1*(B*(4*q v))*T)/(q v)^5 := by gcongr <;> first | exact hpow | exact hz | exact hm | norm_num
         _ = D*T/(q v)^4 := by dsimp only [D]; field_simp [hq0.ne']
         _ ≤ _ := by
           rw [← div_eq_mul_inv,div_div]
           apply (div_le_div_iff₀ (pow_pos hq0 4) (mul_pos hx0 (by positivity))).mpr
           nlinarith only [mul_le_mul_of_nonneg_left hv2 hD]

  have hab : -(4*(T:ℝ))≤4*(T:ℝ) := by linarith
  have hfi : Integrable (E.indicator (fun v => U*F v)) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact (continuous_const.mul hF).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgi := integrable_inv_one_add_sq.const_mul (D/(T:ℝ))
  have hmajor := hfi.add hgi
  have hh : (∫ v : ℝ, ‖rieszDetectorIntegrand X ρ Y (shiftArg ρ v)‖) ≤
      ∫ v : ℝ, (E.indicator (fun w => U*F w) v + D/T*(1+v^2)⁻¹) := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hmajor
    apply Eventually.of_forall
    intro v
    simp only [Pi.add_apply]
    by_cases hv : v∈E
    · rw [indicator_of_mem hv]; exact (hcentral v).trans (le_add_of_nonneg_right (by positivity))
    · rw [indicator_of_notMem hv,zero_add]
      apply htail
      simp only [E,Set.mem_Ioc,not_and_or,not_lt,not_le] at hv
      rcases hv with h | h
      · have := neg_le_abs v; linarith
      · linarith [le_abs_self v]
  rw [integral_add hfi hgi,integral_indicator measurableSet_Ioc,integral_const_mul,integral_const_mul,
    integral_univ_inv_one_add_sq] at hh
  have hI : 0≤∫ v in -(4*(T:ℝ))..4*(T:ℝ), F v := intervalIntegral.integral_nonneg hab fun v _ => hF0 v
  have he : ∫ v in E, F v = ∫ v in -(4*(T:ℝ))..4*(T:ℝ), F v := (intervalIntegral.integral_of_le hab).symm
  rw [he] at hh
  have H := (norm_integral_le_integral_norm (fun v : ℝ => rieszDetectorIntegrand X ρ Y (shiftArg ρ v))).trans hh
  have htail' : A*(D/(T:ℝ)*π) ≤ 1/16 := by
    change 16*A*D*π≤(T:ℝ) at hlarge
    rw [show A*(D/(T:ℝ)*π)=(A*D*π)/(T:ℝ) by ring]
    apply (div_le_iff₀ hx0).mpr; linarith
  rw [norm_mul]
  change A*‖∫ v : ℝ, rieszDetectorIntegrand X ρ Y (shiftArg ρ v)‖ ≤
    1/16+(1458*(A+1))*(1+Real.log T)*Y^(1/2-ρ.re)*(∫ v in -(4*(T:ℝ))..4*(T:ℝ), F v)
  apply (mul_le_mul_of_nonneg_left H hA).trans
  have hcoef := mul_le_mul_of_nonneg_right (show A*1458≤1458*(A+1) by linarith) (show 0≤(1+Real.log T)*Y^(1/2-ρ.re) by positivity)
  dsimp only [U]
  nlinarith only [htail',mul_le_mul_of_nonneg_right hcoef hI]

/-- Uniform critical-line detector bound, retaining only heights `|v| ≤ 4X` in the moment term. -/
theorem rieszDetector_critical_truncation :
    ∃ C > (0:ℝ), ∀ᶠ X : ℕ in atTop, ∀ {Y : ℝ} {ρ : ℂ},
      1 ≤ Y → 1/Real.log X ≤ ρ.re-1/2 → ρ.re < 1 → (X:ℝ) ≤ ρ.im → ρ.im ≤ 2*X →
      ‖((Nat.factorial 6:ℂ)/(2*π))*(∫ v : ℝ, rieszDetectorIntegrand X ρ Y (((1/2-ρ.re:ℝ):ℂ)+v*I))‖ ≤
        1/16+C*(1+Real.log X)*Y^(1/2-ρ.re)*(∫ v in -(4*(X:ℝ))..4*(X:ℝ),
          (1/(1+|v|)^4)*‖riemannZeta ((1/2:ℂ)+(ρ.im+v)*I)‖*
            ‖dirichletPoly (fun n : ℕ => (ArithmeticFunction.moebius n:ℂ)) X ((1/2:ℂ)+(ρ.im+v)*I)‖) := by
  obtain ⟨C,hC,H⟩ := rieszDetector_critical_truncation_of_length_le
  exact ⟨C,hC,H.mono fun X hX Y ρ hY hδ hβ hγ hγ' => hX le_rfl hY hδ hβ hγ hγ'⟩

end AnalyticNumberTheory.RiemannZeta
