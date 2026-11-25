import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleMajorants
import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleDecomposition
import AnalyticNumberTheory.AnalyticTools.IntegratedGaussianError

/-!
# Integrated error in the Hurwitz saddle approximation

Combining both parts of the exact saddle contour and evaluating the
complete quadratic model gives the first Riemann–Siegel coefficient.
-/
noncomputable section
open Real Complex Set MeasureTheory Filter
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- The balanced saddle integral, with its first coefficient and an error
of order x^(-3/2), where the ordinate is 2πx². -/
theorem hurwitz_saddle_integral_first_correction : ∃ C : ℝ,0<C ∧ ∀ {s : ℂ} {x l b : ℝ} {q : ℕ},
    1024≤x → l∈Icc (0:ℝ) 1 → b=x-l+1/2 → x-1≤q → (q:ℝ)≤x →
    s.re=1/2 → s.im=2*Real.pi*x^2 →
    ‖hurwitzGeometricTail s b 1 q+hurwitzLowerGeometric s b q -
      (x:ℂ)^(-s)*Complex.exp (((Real.pi*(2*x*l+l^2-(x+l-q)^2/2-7/8):ℝ):ℂ)*I)*
        (riemannSiegelCorrection (x+l-q):ℂ)‖ ≤ C*x^(-(3/2:ℝ)) := by
  obtain ⟨D,hD,hd⟩ := hurwitzSaddle_pointwise_majorant
  obtain ⟨C,hC,h⟩ := norm_integral_sub_le_of_gaussian_error hD
  refine ⟨2*C,by positivity,?_⟩
  intro s x l b q hx hl hb hq hq' hσ ht
  have hx' : 0<x := by linarith
  have hb' : 0<b := by linarith [hl.2]
  let K := hurwitzSaddleKernel s b q
  let S := Ioi (-b/2)
  have hc : ContinuousOn K S := by
    change ContinuousOn (fun v : ℝ => hurwitzSaddleKernel s b q v) S
    simp_rw [hurwitzSaddleKernel_eq_geometric]
    have hr : Continuous (hurwitzRayRatio 1) := by unfold hurwitzRayRatio;fun_prop
    apply ContinuousOn.div _ (continuous_const.sub hr).continuousOn (fun v _ => sub_ne_zero.mpr (hurwitzRayRatio_ne_one _ _).symm)
    apply ContinuousOn.mul _ (hr.pow _).continuousOn
    apply ContinuousOn.cpow_const (by unfold hurwitzRay;fun_prop)
    intro v hv;left;rw [hurwitzRay_re];have hh : -b/2<v := hv;linarith
  have hm : AEStronglyMeasurable (S.indicator K) := by
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact hc.aestronglyMeasurable measurableSet_Ioi
  obtain ⟨hiF,H⟩ := h hx' (by linarith [hl.2] : x/2≤b) (Real.rpow_nonneg hx'.le (-(1/2:ℝ))) hm
    ((integrable_hurwitzSaddleModel x l q).const_mul ((x:ℂ)^(-s))) (hd hx hl hb hq hq' hσ ht)
  have hi : IntegrableOn K S := (integrable_indicator_iff measurableSet_Ioi).mp hiF
  have hi' : IntegrableOn K (Ioi 0) := hi.mono_set (Ioi_subset_Ioi (by linarith : -b/2≤0))
  rw [integral_indicator measurableSet_Ioi,integral_const_mul] at H
  have he := intervalIntegral.integral_interval_add_Ioi hi hi'
  have hs : hurwitzGeometricTail s b 1 q+hurwitzLowerGeometric s b q=(1+I)*∫ v in S,K v := by
    unfold hurwitzGeometricTail hurwitzLowerGeometric
    simp only [ofReal_one,one_mul]
    rw [←mul_add,add_comm,←he]
    congr 1;dsimp only [K];simp_rw [hurwitzSaddleKernel_eq_geometric];exact add_comm _ _
  have hmodel := integral_hurwitzSaddleModel x l q
  have hxpow : x^(-(1/2:ℝ))/x=x^(-(3/2:ℝ)) := by rw [←Real.rpow_sub_one hx'.ne'];norm_num
  have hfactor : ‖(1:ℂ)+I‖≤2 := (norm_add_le _ _).trans (by norm_num)
  calc
    _ = ‖(1+I)*((∫ v in S,K v)-(x:ℂ)^(-s)*(∫ v : ℝ,hurwitzSaddleModel x l q v))‖ := by
      rw [hs,mul_assoc ((x:ℂ)^(-s)),←hmodel];congr 1;ring
    _ ≤ 2*(C*(x^(-(1/2:ℝ))/x)) := by rw [norm_mul];exact mul_le_mul hfactor H (norm_nonneg _) (by norm_num)
    _ = _ := by rw [hxpow];ring
end AnalyticNumberTheory.RiemannZeta
