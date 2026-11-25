import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleKernel
import AnalyticNumberTheory.AnalyticTools.QuadraticPowerApproximation

/-!
# Local comparison of the Hurwitz saddle and the quadratic model

The logarithm is expanded before taking absolute values. The estimate keeps
both endpoint moduli, which permits direct use of Gaussian decay.
-/
noncomputable section
open Real Complex MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem norm_one_add_I_le : ‖(1:ℂ)+I‖≤3/2 := by
  have H : ‖(1:ℂ)+I‖^2=2 := by rw [←Complex.normSq_eq_norm_sq];norm_num [Complex.normSq_apply]
  nlinarith [norm_nonneg ((1:ℂ)+I)]

theorem saddleOffset_norm_le {l : ℝ} (hl : l∈Icc (0:ℝ) 1) (v : ℝ) :
    ‖hurwitzSaddleOffset l v‖≤1/2+(3/2)*|v| := by
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,show (1/2-(l:ℂ))=((1/2-l:ℝ):ℂ) by push_cast;rfl,Complex.norm_real,Real.norm_eq_abs]
  exact add_le_add (abs_le.mpr ⟨by linarith [hl.2],by linarith [hl.1]⟩) (mul_le_mul_of_nonneg_right norm_one_add_I_le (abs_nonneg _))

private theorem saddleOffset_polynomial {l : ℝ} (hl : l∈Icc (0:ℝ) 1) (v : ℝ) :
    ‖hurwitzSaddleOffset l v‖+2*Real.pi*‖hurwitzSaddleOffset l v‖^3≤100*(1+v^4) := by
  let z := hurwitzSaddleOffset l v
  have h := saddleOffset_norm_le hl v
  have hp := Real.pi_lt_four
  by_cases hv : |v|≤1
  · have hz : ‖z‖≤2 := by dsimp [z];linarith
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hz 3
    change ‖z‖+_≤_;nlinarith [mul_le_mul_of_nonneg_left h3 (show 0≤2*Real.pi by positivity),sq_nonneg (v^2)]
  · have h1 : 1≤|v| := (not_le.mp hv).le
    have hz : ‖z‖≤2*|v| := by dsimp [z];linarith
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hz 3
    have h4 : |v|^4=v^4 := by rw [show 4=2*2 by decide,pow_mul,pow_mul,sq_abs]
    have ha : |v|≤|v|^4 := by simpa using pow_le_pow_right₀ h1 (show 1≤4 by decide)
    have ha' : |v|^3≤|v|^4 := pow_le_pow_right₀ h1 (by decide)
    change ‖z‖+_≤_
    nlinarith [mul_le_mul_of_nonneg_left h3 (show 0≤2*Real.pi by positivity),
      mul_le_mul_of_nonneg_right hp.le (show 0≤|v|^3 by positivity)]

/-- Pointwise relative error in the central quarter of the contour. -/
theorem norm_hurwitzSaddleKernel_sub_model_central {s : ℂ} {x l b q v : ℝ}
    (hx : 8≤x) (hl : l∈Icc (0:ℝ) 1) (hb : b=x-l+1/2)
    (hσ : s.re=1/2) (ht : s.im=2*Real.pi*x^2) (hv : |v|≤b/4) :
    ‖hurwitzSaddleKernel s b q v-(x:ℂ)^(-s)*hurwitzSaddleModel x l q v‖≤
      (100*(1+v^4)/x)*(‖hurwitzSaddleKernel s b q v‖+‖(x:ℂ)^(-s)*hurwitzSaddleModel x l q v‖) := by
  have hx' : 0<x := by linarith
  have hxc : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx'.ne'
  let Z := hurwitzSaddleOffset l v
  let u := Z/(x:ℂ)
  let W := Complex.exp (-(q:ℂ)*hurwitzSaddleVariable v)/(Complex.exp (hurwitzSaddleVariable v)-1)
  let G := (x:ℂ)^(-s)*Complex.exp (-(s.im:ℂ)*I*(u-u^2/2))
  have hnorm : ‖u‖=‖Z‖/x := by rw [show u=Z/(x:ℂ) by rfl,norm_div,Complex.norm_of_nonneg hx'.le]
  have hu : ‖u‖≤1/2 := by
    rw [hnorm,div_le_iff₀ hx'];dsimp only [Z];linarith [saddleOffset_norm_le hl v,hl.1]
  have hz : (x:ℂ)*(1+u)=hurwitzRay b 1 v := by
    dsimp [u,Z,hurwitzSaddleOffset,hurwitzRay];rw [hb];push_cast;field_simp;ring
  have hE : -(s.im:ℂ)*I*(u-u^2/2)= -2*Real.pi*I*x*Z+Real.pi*I*Z^2 := by
    rw [ht];dsimp only [u];push_cast;field_simp;ring
  have hG : G*W=(x:ℂ)^(-s)*hurwitzSaddleModel x l q v := by dsimp only [G,W,hurwitzSaddleModel];rw [hE];dsimp only [Z];ring
  have hK : (hurwitzRay b 1 v)^(-s)*W=hurwitzSaddleKernel s b q v := by dsimp [W,hurwitzSaddleKernel];ring
  have H := norm_cpow_sub_quadratic_le hx' (s:=s) (by linarith) hu
  change ‖_ -G‖≤_*(‖_‖+‖G‖) at H
  rw [hz] at H
  have hP : 2*s.re*‖u‖+|s.im| *‖u‖^3 ≤100*(1+v^4)/x := by
    rw [hσ,ht,abs_of_nonneg (by positivity),hnorm]
    calc _ = (‖Z‖+2*Real.pi*‖Z‖^3)/x := by field_simp
         _ ≤ _ := div_le_div_of_nonneg_right (saddleOffset_polynomial hl v) hx'.le
  rw [←hG,←hK,←sub_mul,norm_mul,norm_mul,norm_mul]
  apply (mul_le_mul_of_nonneg_right (H.trans (mul_le_mul_of_nonneg_right hP (by positivity))) (norm_nonneg W)).trans_eq
  ring

end AnalyticNumberTheory.RiemannZeta
