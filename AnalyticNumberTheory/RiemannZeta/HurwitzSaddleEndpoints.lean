import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleDecomposition
import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleKernel
import AnalyticNumberTheory.RiemannZeta.HurwitzNonstationaryContour

/-!
# The nonstationary endpoint terms in the balanced Hurwitz formula

The lower diagonal endpoint decays on scale b/t, while the radial heads
and the negative complete gamma modes have exponential decay in the height.
-/
noncomputable section
open Real Complex MeasureTheory Filter Set Finset
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem lower_diagonal_arg {b v : ℝ} (hb : 0<b) (hv : v∈Set.Ioc (-b/2) 0) :
    (hurwitzRay b 1 v).arg≤v/b := by
  let z := hurwitzRay b 1 v
  have hi : z.im=v := by simp [z]
  have hr : z.re=b+v := by simp [z]
  have hpos : 0<b+v := by linarith [hv.1]
  have hn : 0<‖z‖ := (hr ▸ hpos).trans_le (Complex.re_le_norm z)
  have hn' : ‖z‖≤b := (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [hr,hi,abs_of_pos hpos,abs_of_nonpos hv.2];linarith)
  rcases lt_or_eq_of_le hv.2 with h|h
  · have harg := Complex.arg_neg_iff.mpr (hi ▸ h)
    have H := Real.sin_le (neg_nonneg.mpr harg.le)
    rw [Real.sin_neg,Complex.sin_arg,hi] at H
    apply (by linarith : z.arg≤v/‖z‖).trans
    apply (div_le_div_iff₀ hn hb).mpr
    exact mul_le_mul_of_nonpos_left hn' hv.2
  · rw [h];simp [hurwitzRay,Complex.arg_ofReal_of_nonneg hb.le]

/-- The lower diagonal endpoint on the complementary side of the geometric
summation has the same saving b/t as the negative-frequency contour. -/
theorem norm_hurwitzLowerGeometric_zero : ∃ C : ℝ,0<C ∧ ∀ {s : ℂ} {b : ℝ},
    0≤s.re → 0<s.im → 0<b →
    ‖hurwitzLowerGeometric s b 0‖≤C*(b/2)^(-s.re)*b/s.im := by
  obtain ⟨C,hC,hden⟩ := saddleVariable_inv_bound
  refine ⟨2*C,by positivity,?_⟩
  intro s b hσ ht hb
  let K := hurwitzSaddleKernel s b 0
  let A := C*(b/2)^(-s.re)
  have hpoint (v : ℝ) (hv : v∈Set.Ioc (-b/2) 0) : ‖K v‖≤A*Real.exp ((s.im/b)*v) := by
    let z := hurwitzRay b 1 v
    have hr : b/2≤z.re := by dsimp only [z];rw [hurwitzRay_re];linarith [hv.1]
    have hp : 0<z.re := (by positivity : 0<b/2).trans_le hr
    have hz : z≠0 := by intro he;simpa [he] using hp
    dsimp only [K,hurwitzSaddleKernel];simp only [ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,mul_one]
    rw [div_eq_mul_inv,norm_mul,Complex.norm_cpow_of_ne_zero hz,neg_re,neg_im,mul_neg,Real.exp_neg,div_inv_eq_mul]
    have hI := Real.rpow_le_rpow_of_nonpos (by positivity : 0<b/2) (hr.trans (Complex.re_le_norm _)) (neg_nonpos.mpr hσ)
    have he : Real.exp (z.arg*s.im)≤Real.exp ((s.im/b)*v) := Real.exp_le_exp.mpr (by
      have H := mul_le_mul_of_nonneg_right (lower_diagonal_arg hb hv) ht.le
      change z.arg*s.im≤_;convert H using 1;ring)
    calc _ ≤ ((b/2)^(-s.re)*Real.exp ((s.im/b)*v))*C := mul_le_mul (mul_le_mul hI he (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) _)) (hden v) (norm_nonneg _) (by positivity)
         _ = _ := by dsimp [A];ring
  have hg : IntegrableOn (fun v : ℝ => A*Real.exp ((s.im/b)*v)) (Iic 0) := (integrableOn_exp_mul_Iic (div_pos ht hb) 0).const_mul _
  have hmeas : AEStronglyMeasurable K (volume.restrict (Set.Ioc (-b/2) 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    change ContinuousOn (fun v => hurwitzSaddleKernel s b (0:ℕ) v) _
    simp_rw [hurwitzSaddleKernel_eq_geometric]
    have hr : Continuous (hurwitzRayRatio 1) := by unfold hurwitzRayRatio;fun_prop
    apply ContinuousOn.div _ (continuous_const.sub hr).continuousOn (fun v _ => sub_ne_zero.mpr (hurwitzRayRatio_ne_one _ _).symm)
    apply ContinuousOn.mul _ (hr.pow _).continuousOn
    apply ContinuousOn.cpow_const (by unfold hurwitzRay;fun_prop)
    intro v hv;left;rw [hurwitzRay_re];linarith [hv.1]
  have hsubset : Set.Ioc (-b/2) 0⊆Iic 0 := fun _ h => h.2
  have hB := (setIntegral_mono_on (((hg.mono_set hsubset).mono' hmeas ((ae_restrict_mem measurableSet_Ioc).mono hpoint)).norm)
    (hg.mono_set hsubset) measurableSet_Ioc hpoint).trans (setIntegral_mono_set hg (by filter_upwards with v;dsimp [A];positivity) (Filter.Eventually.of_forall hsubset))
  rw [integral_const_mul,integral_exp_mul_Iic (div_pos ht hb),mul_zero,Real.exp_zero] at hB
  have hK : hurwitzLowerGeometric s b 0=(1+I)*∫ v in Set.Ioc (-b/2) 0,K v := by
    rw [hurwitzLowerGeometric,intervalIntegral.integral_of_le (by linarith)]
    congr 1;apply integral_congr_ae;filter_upwards with v;exact (hurwitzSaddleKernel_eq_geometric s b 0 v).symm
  rw [hK,norm_mul]
  apply (mul_le_mul (show ‖(1:ℂ)+I‖≤2 from (norm_add_le _ _).trans (by norm_num)) ((norm_integral_le_integral_norm _).trans hB) (norm_nonneg _) (by norm_num)).trans_eq
  dsimp [A];simp only [one_div,inv_div];ring

private theorem norm_Gamma_half_le {z : ℂ} (hz : z.re=1/2) : ‖Complex.Gamma z‖≤Real.Gamma (1/2) := by
  rw [←hz,Complex.Gamma_eq_integral (by linarith),Complex.GammaIntegral,Real.Gamma_eq_integral (by linarith)]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,Complex.norm_cpow_eq_rpow_re_of_pos hu];simp

/-- The negative-frequency gamma polynomial is exponentially small at
positive height. -/
theorem norm_hurwitzNegativeDual_critical {s : ℂ} (hσ : s.re=1/2) (a : ℝ) (q : ℕ) :
    ‖hurwitzNegativeDual s a q‖ ≤ (q:ℝ)*Real.Gamma (1/2)*Real.exp (-(Real.pi/2)*s.im) := by
  unfold hurwitzNegativeDual
  apply (norm_sum_le _ _).trans
  have hΓ := norm_Gamma_half_le (z:=1-s) (by rw [sub_re,one_re,hσ];norm_num)
  calc _ ≤ ∑ _j∈range q,Real.Gamma (1/2)*Real.exp (-(Real.pi/2)*s.im) := by
            apply sum_le_sum;intro j _
            rw [norm_mul,norm_hurwitzShift,one_mul,hurwitzDualMode,norm_mul]
            have hω : 1≤hurwitzOmega j := by unfold hurwitzOmega;nlinarith [Real.pi_gt_three,Nat.cast_nonneg (α:=ℝ) j,mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α:=ℝ) j)]
            have hf : hurwitzFrequency (-hurwitzOmega j)=(hurwitzOmega j:ℂ)*I := by unfold hurwitzFrequency;push_cast;ring
            rw [hf,Complex.norm_cpow_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (hurwitzOmega_pos j).ne') I_ne_zero),
              Complex.arg_real_mul _ (hurwitzOmega_pos j),Complex.arg_I,norm_mul,Complex.norm_I,mul_one,
              Complex.norm_of_nonneg (hurwitzOmega_pos j).le,sub_re,sub_im,one_re,one_im,sub_zero,hσ,div_eq_mul_inv,←Real.exp_neg,neg_mul]
            have hw := Real.rpow_le_one_of_one_le_of_nonpos hω (by norm_num : 1/2-1≤(0:ℝ))
            let E := Real.exp (-(Real.pi/2*s.im))
            change hurwitzOmega j^(1/2-1:ℝ)*E*‖Complex.Gamma (1-s)‖≤Real.Gamma (1/2)*E
            calc _ ≤ (1*E)*Real.Gamma (1/2) :=
                         mul_le_mul (mul_le_mul_of_nonneg_right hw (Real.exp_nonneg _)) hΓ (norm_nonneg _) (by dsimp [E];positivity)
                 _ = _ := by ring
       _ = _ := by simp;ring
end AnalyticNumberTheory.RiemannZeta
