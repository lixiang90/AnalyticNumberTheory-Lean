import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleDecay
import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleExpansion

/-!
# Gaussian majorants on the balanced Hurwitz contour

Both the original saddle kernel and its quadratic model have a common
Gaussian bound near the saddle and a common exponential bound outside.
-/
noncomputable section
open Real Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem norm_exact_kernel_le {s : ℂ} {x b q v C : ℝ} (hx : 0<x)
    (hb : x/2≤b) (hv : -b/2≤v) (hσ : s.re=1/2) (ht : s.im=2*Real.pi*x^2)
    (hC : ‖(Complex.exp (hurwitzSaddleVariable v)-1)⁻¹‖≤C) :
    ‖hurwitzSaddleKernel s b q v‖≤2*C*x^(-(1/2:ℝ))*Real.exp (hurwitzSaddleHeight x b q v) := by
  let z := hurwitzRay b 1 v
  have hr : x/4≤z.re := by rw [hurwitzRay_re];linarith
  have hz : z≠0 := by intro he;rw [he,zero_re] at hr;linarith
  have hpow : ‖z‖^(-(1/2:ℝ))≤2*x^(-(1/2:ℝ)) := by
    apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0<x/4) (hr.trans (Complex.re_le_norm _)) (by norm_num : -(1/2:ℝ)≤0)).trans_eq
    rw [Real.div_rpow hx.le (by norm_num)]
    have h4 : (4:ℝ)^(-(1/2:ℝ))=1/2 := by rw [Real.rpow_neg (by norm_num),←Real.sqrt_eq_rpow];norm_num
    rw [h4];ring
  unfold hurwitzSaddleKernel;rw [div_eq_mul_inv,norm_mul,norm_mul,norm_saddle_carrier,Complex.norm_cpow_of_ne_zero hz,neg_re,neg_im,hσ,ht,mul_neg,Real.exp_neg,div_inv_eq_mul]
  change (‖z‖^(-(1/2:ℝ))*Real.exp (z.arg*(2*Real.pi*x^2))*Real.exp (-2*Real.pi*q*v))*_ ≤ _
  rw [mul_assoc (‖z‖^(-(1/2:ℝ))) (Real.exp (z.arg*(2*Real.pi*x^2))) (Real.exp (-2*Real.pi*q*v)),←Real.exp_add,show z.arg*(2*Real.pi*x^2)+ -2*Real.pi*q*v=hurwitzSaddleHeight x b q v by unfold hurwitzSaddleHeight;dsimp [z];ring]
  calc _ ≤ (2*x^(-(1/2:ℝ))*Real.exp (hurwitzSaddleHeight x b q v))*C :=
            mul_le_mul (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) hC (norm_nonneg _) (by positivity)
       _ = _ := by ring

private theorem model_height (x l q v : ℝ) :
    (-2*Real.pi*I*x*hurwitzSaddleOffset l v+Real.pi*I*(hurwitzSaddleOffset l v)^2).re -2*Real.pi*q*v =
      2*Real.pi*(x-q-(1/2-l))*v-2*Real.pi*v^2 := by
  simp [hurwitzSaddleOffset,mul_re,mul_im,pow_two,div_re];ring

private theorem norm_model_le {s : ℂ} {x l q v C : ℝ} (hx : 0<x) (hσ : s.re=1/2)
    (hl : l∈Icc (0:ℝ) 1) (hq : x-1≤q) (hq' : q≤x)
    (hC : ‖(Complex.exp (hurwitzSaddleVariable v)-1)⁻¹‖≤C) :
    ‖(x:ℂ)^(-s)*hurwitzSaddleModel x l q v‖ ≤ C*x^(-(1/2:ℝ))*Real.exp (32-v^2) := by
  have hA : |x-q-(1/2-l)|≤3/2 := abs_le.mpr ⟨by linarith [hl.1],by linarith [hl.2]⟩
  have hmul : (x-q-(1/2-l))*v ≤ (3/2)*|v| := (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_right hA (abs_nonneg _))
  have hE : 2*Real.pi*(x-q-(1/2-l))*v-2*Real.pi*v^2≤32-v^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hmul (show 0≤2*Real.pi by positivity),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (abs_nonneg v),
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg v),sq_nonneg (|v|-2),sq_abs v]
  unfold hurwitzSaddleModel
  rw [div_eq_mul_inv,norm_mul,norm_mul,norm_mul,norm_saddle_carrier,Complex.norm_exp,Complex.norm_cpow_eq_rpow_re_of_pos hx,neg_re,hσ,←Real.exp_add]
  rw [show _+(-2*Real.pi*q*v)=2*Real.pi*(x-q-(1/2-l))*v-2*Real.pi*v^2 by simpa only [sub_eq_add_neg,neg_mul] using model_height x l q v]
  calc _ ≤ x^(-(1/2:ℝ))*(Real.exp (32-v^2)*C) := mul_le_mul_of_nonneg_left (mul_le_mul (Real.exp_le_exp.mpr hE) hC (norm_nonneg _) (Real.exp_nonneg _)) (Real.rpow_nonneg hx.le _)
       _ = _ := by ring

/-- The difference after extending the exact truncated contour by zero.
The two integrable majorants isolate the cubic Taylor error and the
outer tails of width 1/b. -/
theorem hurwitzSaddle_pointwise_majorant : ∃ D : ℝ,0<D ∧ ∀ {s : ℂ} {x l b q : ℝ},
    1024≤x → l∈Icc (0:ℝ) 1 → b=x-l+1/2 → x-1≤q → q≤x →
    s.re=1/2 → s.im=2*Real.pi*x^2 → ∀ v : ℝ,
    ‖(Ioi (-b/2)).indicator (hurwitzSaddleKernel s b q) v -
      (x:ℂ)^(-s)*hurwitzSaddleModel x l q v‖≤
      D*(x^(-(1/2:ℝ))/x)*((1+v^4)*Real.exp (-v^2/16))+
      D*x^(-(1/2:ℝ))*Real.exp (-(b/64)*|v|) := by
  obtain ⟨C,hC,hden⟩ := saddleVariable_inv_bound
  let E := Real.exp 1024
  refine ⟨300*C*E,by dsimp [E];positivity,?_⟩
  intro s x l b q hx hl hb hq hq' hσ ht v
  have hx' : 0<x := by linarith
  have hb' : 0<b := by linarith [hl.2]
  have hb0 : |b-x|≤1/2 := abs_le.mpr ⟨by linarith [hl.2],by linarith [hl.1]⟩
  have hbx : x/2≤b := by linarith [hl.2]
  let P := x^(-(1/2:ℝ))
  have hP : 0≤P := Real.rpow_nonneg hx'.le _
  have hm := norm_model_le (s:=s) (v:=v) hx' hσ hl hq hq' (hden v)
  have he := norm_exact_kernel_le (s:=s) (q:=q) (v:=v) hx' hbx (hσ:=hσ) (ht:=ht) (hC:=hden v)
  have hE : 0<E := Real.exp_pos _
  by_cases hv : |v|≤b/4
  · have hv' : -b/2<v := by linarith [(abs_le.mp hv).1]
    rw [indicator_of_mem (mem_Ioi.mpr hv')]
    have hc := norm_hurwitzSaddleKernel_sub_model_central (q:=q) (by linarith) hl hb hσ ht hv
    have hH := hurwitzSaddleHeight_central hx hb0 hq hq' hv
    have hg : Real.exp (hurwitzSaddleHeight x b q v)≤E*Real.exp (-v^2/16) := by rw [←Real.exp_add];apply Real.exp_le_exp.mpr;linarith
    have hm' : Real.exp (32-v^2)≤E*Real.exp (-v^2/16) := by rw [←Real.exp_add];apply Real.exp_le_exp.mpr;nlinarith [sq_nonneg v]
    apply hc.trans
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    change 100*(1+v^4)/x*(_+_)≤_
    calc _ ≤ 100*(1+v^4)/x*(2*C*P*(E*Real.exp (-v^2/16))+C*P*(E*Real.exp (-v^2/16))) := by
              gcongr
              · exact (he hv'.le).trans (mul_le_mul_of_nonneg_left hg (by positivity))
              · exact hm.trans (mul_le_mul_of_nonneg_left hm' (by positivity))
         _ = _ := by dsimp [P];ring
  · have hv' : b/4≤|v| := (not_le.mp hv).le
    have htail : Real.exp (32-v^2)≤E*Real.exp (-(b/64)*|v|) := by
      rw [←Real.exp_add];apply Real.exp_le_exp.mpr;nlinarith [mul_nonneg (sub_nonneg.mpr hv') (abs_nonneg v),sq_abs v]
    have hm' := hm.trans (mul_le_mul_of_nonneg_left htail (show 0≤C*P by positivity))
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply (norm_sub_le _ _).trans
    have haux : ‖(Ioi (-b/2)).indicator (hurwitzSaddleKernel s b q) v‖≤2*C*P*(E*Real.exp (-(b/64)*|v|)) := by
      by_cases hh : -b/2<v
      · rw [indicator_of_mem (mem_Ioi.mpr hh)]
        apply (he hh.le).trans (mul_le_mul_of_nonneg_left _ (by positivity))
        rw [←Real.exp_add];apply Real.exp_le_exp.mpr
        have H := hurwitzSaddleHeight_outer hx hb0 hq hq' hh.le hv'
        nlinarith [mul_nonneg hb'.le (sub_nonneg.mpr hv')]
      · rw [indicator_of_notMem (show v∉Ioi (-b/2) by exact hh),norm_zero];positivity
    apply (add_le_add haux hm').trans
    change _≤300*C*E*P*_
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC.le hE.le) hP) (Real.exp_nonneg (-(b/64)*|v|))]

end AnalyticNumberTheory.RiemannZeta
