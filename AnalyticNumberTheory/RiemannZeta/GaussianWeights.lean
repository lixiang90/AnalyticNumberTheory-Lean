import AnalyticNumberTheory.RiemannZeta.SmoothedDirichletSums
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling

/-!
# Uniform bounds for the Gaussian weights

The ratio of the completed archimedean factors on the critical line and on
a fixed displaced vertical line costs a power of the height. The remaining
growth in the integration variable is absorbed by a Gaussian.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.RiemannZeta

set_option maxHeartbeats 800000

theorem differentiableAt_xiCompletionFactor {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ xiCompletionFactor z := by
  have hG : DifferentiableAt ℂ Gammaℝ z := by
    have hh := (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
    change DifferentiableAt ℂ (fun u => (Gammaℝ u)⁻¹⁻¹) z at hh
    simpa only [inv_inv] using hh
  unfold xiCompletionFactor
  exact ((((differentiableAt_const (1/2:ℂ)).mul differentiableAt_id).mul (differentiableAt_id.sub_const 1))).mul hG

private noncomputable def archEnvelope (σ t : ℝ) : ℝ :=
  Real.exp (-(π/4)*|t|) * |t|^(σ/2+3/2)

/-- Large-height comparison of the entire archimedean factor with its Stirling envelope. -/
private theorem completionFactor_vertical_bounds (σ : ℝ) (hσ : 0 < σ) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ {t : ℝ}, 2 ≤ |t| →
      b*archEnvelope σ t ≤ ‖xiCompletionFactor ((σ:ℂ)+t*I)‖ ∧
      ‖xiCompletionFactor ((σ:ℂ)+t*I)‖ ≤ B*archEnvelope σ t := by
  obtain ⟨b,B,hb,hbB,hG⟩ := norm_complex_gamma_strip_bounds (σ/2) (σ/2)
  let e := σ/2-1/2
  let a := (1/2:ℝ)*π^(-σ/2:ℝ)/(2:ℝ)^e
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a*b,a*B*(σ+1)*(|σ-1|+1), by positivity, by have := hb.trans_le hbB; positivity,?_⟩
  intro t ht
  let z := (σ:ℂ)+t*I
  have ht0 : 0 < |t| := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have hhalf : z/2 = ((σ/2:ℝ):ℂ)+(t/2:ℝ)*I := by dsimp [z]; push_cast; ring
  have hp : ‖(π:ℂ)^(-z/2)‖ = π^(-σ/2) := by rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]; simp [z]
  have hg := hG (σ := σ/2) (t := t/2) ⟨le_rfl,le_rfl⟩ (by rw [abs_div]; norm_num; linarith)
  have he : Real.exp (-(π/2)*|t/2|) = Real.exp (-(π/4)*|t|) := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; congr 1; ring
  have hpow : |t/2|^e = |t|^e / (2:ℝ)^e := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),Real.div_rpow (abs_nonneg _) (by norm_num)]
  change _*Real.exp (-(π/2)*|t/2|)*|t/2|^e ≤ _ ∧ _ ≤ _*Real.exp (-(π/2)*|t/2|)*|t/2|^e at hg
  rw [he,hpow,← hhalf] at hg
  have him : z.im = t := by simp [z]
  have hlz : |t| ≤ ‖z‖ := him ▸ Complex.abs_im_le_norm z
  have hlm : |t| ≤ ‖z-1‖ := by simpa [z] using Complex.abs_im_le_norm (z-1)
  have huz : ‖z‖ ≤ (σ+1)*|t| := by
    have h := norm_add_le (σ:ℂ) ((t:ℂ)*I)
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ] at h
    nlinarith [mul_nonneg hσ.le (sub_nonneg.mpr ht1)]
  have hum : ‖z-1‖ ≤ (|σ-1|+1)*|t| := by
    have hh : z-1 = ((σ-1:ℝ):ℂ)+t*I := by dsimp [z]; push_cast; ring
    rw [hh]
    have h := norm_add_le ((σ-1:ℝ):ℂ) ((t:ℂ)*I)
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at h
    nlinarith [mul_nonneg (abs_nonneg (σ-1)) (sub_nonneg.mpr ht1)]
  have henv : archEnvelope σ t = Real.exp (-(π/4)*|t|)*|t|^e*|t|^2 := by
    unfold archEnvelope
    rw [show σ/2+3/2=e+2 by dsimp [e]; ring, Real.rpow_add ht0, Real.rpow_two]
    ring
  change _ ≤ ‖xiCompletionFactor z‖ ∧ ‖xiCompletionFactor z‖ ≤ _
  unfold xiCompletionFactor Gammaℝ
  simp only [norm_mul,hp,norm_div,norm_one,Complex.norm_ofNat]
  rw [henv]
  obtain ⟨hgl,hgu⟩ := hg
  have hb' := mul_le_mul (mul_le_mul hlz hlm (abs_nonneg _) (norm_nonneg _)) hgl
    (by positivity) (by positivity)
  have hB' := mul_le_mul (mul_le_mul huz hum (norm_nonneg _) (by positivity)) hgu
    (norm_nonneg _) (by positivity)
  dsimp [a]
  constructor
  · have h := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ (1/2:ℝ)*π^(-σ/2:ℝ))
    convert h using 1 <;> ring
  · have h := mul_le_mul_of_nonneg_left hB' (by positivity : 0 ≤ (1/2:ℝ)*π^(-σ/2:ℝ))
    convert h using 1 <;> ring

/-- A global vertical upper bound, including bounded imaginary parts. -/
private theorem completionFactor_vertical_upper (σ : ℝ) (hσ : 0 < σ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖xiCompletionFactor ((σ:ℂ)+t*I)‖ ≤
      B*(Real.exp (-(π/4)*|t|)*(1+|t|)^(σ/2+3/2)) := by
  obtain ⟨b,B,hb,hB,hbounds⟩ := completionFactor_vertical_bounds σ hσ
  let E (t : ℝ) := Real.exp (-(π/4)*|t|)*(1+|t|)^(σ/2+3/2)
  have hE (t : ℝ) : 0 < E t := by dsimp [E]; positivity
  have hce : Continuous E := by dsimp [E]; fun_prop (disch := positivity)
  let g (t : ℝ) := xiCompletionFactor ((σ:ℂ)+t*I)
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun t =>
    ContinuousAt.comp (f := fun u : ℝ => (σ:ℂ)+u*I)
      (differentiableAt_xiCompletionFactor (by simpa using hσ : 0 < ((σ:ℂ)+t*I).re)).continuousAt (by fun_prop)
  obtain ⟨v,hv,hm⟩ := isCompact_Icc.exists_isMaxOn (f := fun t => ‖g t‖/E t)
    (nonempty_Icc.mpr (by norm_num : (-2:ℝ)≤2)) (hc.norm.div hce (fun t => (hE t).ne')).continuousOn
  refine ⟨max B (‖g v‖/E v), lt_of_lt_of_le hB (le_max_left ..),?_⟩
  intro t
  change ‖g t‖ ≤ _*E t
  by_cases ht : 2 ≤ |t|
  · have hu := (hbounds ht).2
    have he : archEnvelope σ t ≤ E t := by
      dsimp only [archEnvelope,E]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (abs_nonneg t) (by linarith) (by linarith)
    exact hu.trans (mul_le_mul (le_max_left ..) he (by dsimp [archEnvelope]; positivity) (by positivity))
  · have H := hm (abs_le.mp (le_of_lt (not_le.mp ht)))
    exact (div_le_iff₀ (hE t)).mp (H.trans (le_max_right ..))


private theorem completionFactor_ratio {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, 2 ≤ t → ∀ u v : ℝ, |u| = t →
      ‖xiCompletionFactor (((1/2+c:ℝ):ℂ)+(u+v:ℝ)*I)‖ /
        ‖xiCompletionFactor ((1/2:ℂ)+t*I)‖ ≤
      C * t^(c/2) * ((1+|v|)^(7/4+c/2) * Real.exp ((π/4)*|v|)) := by
  obtain ⟨b,B₀,hb,hB₀,hden⟩ := completionFactor_vertical_bounds (1/2) (by norm_num)
  obtain ⟨B,hB,hnum⟩ := completionFactor_vertical_upper (1/2+c) (by linarith)
  let e := 7/4+c/2
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  refine ⟨B/b*(2:ℝ)^e,by positivity,?_⟩
  intro t ht u v hu
  have ht0 : 0 < t := by linarith
  have hn := hnum (u+v)
  have hd := (hden (t := t) (by simpa [abs_of_pos ht0] using ht)).1
  change _ ≤ ‖xiCompletionFactor (((1/2:ℝ):ℂ)+t*I)‖ at hd
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hd
  rw [archEnvelope,abs_of_pos ht0,show (1/2:ℝ)/2+3/2=7/4 by norm_num] at hd
  rw [show (1/2+c)/2+3/2=e by dsimp [e]; ring] at hn
  have habs : 1+|u+v| ≤ (2*t)*(1+|v|) := by
    have h := abs_add_le u v
    rw [hu] at h
    nlinarith [abs_nonneg v,mul_nonneg (by linarith : 0 ≤ 2*t-1) (abs_nonneg v)]
  have hpow := Real.rpow_le_rpow (by positivity) habs he0
  rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) ht0.le] at hpow
  have hphase : Real.exp (-(π/4)*|u+v|) ≤ Real.exp (-(π/4)*t)*Real.exp (π/4*|v|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h := abs_add_le (u+v) (-v)
    rw [add_neg_cancel_right,abs_neg,hu] at h
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h)]
  apply (div_le_iff₀ (lt_of_lt_of_le (by positivity) hd)).mpr
  have hcomp := mul_le_mul_of_nonneg_left hd (show 0 ≤ (B/b*2^e)*t^(c/2)*((1+|v|)^e*Real.exp (π/4*|v|)) by positivity)
  apply hn.trans
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hphase hpow (by positivity) (by positivity)) hB.le)
  apply hcomp.trans_eq'
  rw [show t^e = t^(7/4:ℝ)*t^(c/2) by dsimp only [e]; rw [Real.rpow_add ht0]]
  field_simp

/-- Gaussian domination uniform in the entire height interval and in both signs of the
critical height. The right shift `c` costs the factor `T^c` for the square of zeta. -/
theorem norm_normalized_xiGaussianKernel_sq_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ {T t : ℝ}, 2 ≤ T → t ∈ Icc T (2*T) → ∀ u v : ℝ, |u|=t →
      ‖xiGaussianKernel ((1/2:ℂ)+u*I) 2 ((c:ℂ)+v*I) /
        (2*π*xiCompletionFactor ((1/2:ℂ)+t*I)^2)‖ ≤ K*T^c*Real.exp (-v^2/2) := by
  obtain ⟨C,hC,h⟩ := completionFactor_ratio hc
  let e := 7/4+c/2
  let A := 2*e+π/2
  let K := C^2*(2:ℝ)^c*Real.exp (c^2+A^2/2)/(2*π*c)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro T t hT ht u v hu
  have hT0 : 0 < T := by linarith
  have ht2 := hT.trans ht.1
  have ht0 : 0 < t := by linarith
  let s := (1/2:ℂ)+u*I
  let z := (1/2:ℂ)+t*I
  let w := (c:ℂ)+v*I
  have hre : s+w = ((1/2+c:ℝ):ℂ)+(u+v:ℝ)*I := by dsimp [s,w]; push_cast; ring
  have hrat := h ht2 u v hu
  rw [← hre] at hrat
  have hpow : (1+|v|)^e ≤ Real.exp (e*|v|) := by
    rw [Real.rpow_def_of_pos (by positivity),Real.exp_le_exp]
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+|v|)
    dsimp [e]
    nlinarith [mul_nonneg (show 0 ≤ 7/4+c/2 by linarith) (show 0 ≤ |v|-Real.log (1+|v|) by linarith)]
  have hd : ‖xiCompletionFactor (s+w)‖ / ‖xiCompletionFactor z‖ ≤
      C * t^(c/2) * Real.exp ((e+π/4)*|v|) := by
    apply hrat.trans
    rw [add_mul,Real.exp_add]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
  have hw : c ≤ ‖w‖ := by simpa [w] using Complex.re_le_norm w
  have he : (w^2).re = c^2-v^2 := by simp [w,pow_two]
  have htP : (t^(c/2))^2 ≤ (2:ℝ)^c*T^c := by
    rw [← Real.rpow_mul_natCast ht0.le,show c/2*(2:ℕ)=c by push_cast; ring,← Real.mul_rpow (by norm_num) hT0.le]
    exact Real.rpow_le_rpow ht0.le ht.2 hc.le
  have hE : (Real.exp ((e+π/4)*|v|))^2 * Real.exp (w^2).re ≤
      Real.exp (c^2+A^2/2)*Real.exp (-v^2/2) := by
    rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,Real.exp_le_exp,he]
    dsimp [A]
    nlinarith [sq_nonneg (|v|-(2*e+π/2)),sq_abs v]
  change ‖xiGaussianKernel s 2 w / (2*π*xiCompletionFactor z^2)‖ ≤ _
  simp only [xiGaussianKernel,norm_div,norm_mul,norm_pow,Complex.norm_exp,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [show ‖xiCompletionFactor (s+w)‖^2*Real.exp (w^2).re / ‖w‖ /(2*π*‖xiCompletionFactor z‖^2) =
      ((‖xiCompletionFactor (s+w)‖/‖xiCompletionFactor z‖)^2 * Real.exp (w^2).re)/(2*π*‖w‖) by ring]
  have hsq := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) hd 2
  rw [mul_pow,mul_pow] at hsq
  calc _ ≤ ((C^2*(t^(c/2))^2*(Real.exp ((e+π/4)*|v|))^2)*Real.exp (w^2).re)/(2*π*c) :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hsq (by positivity)) (by positivity)
              (mul_le_mul_of_nonneg_left hw (by positivity))
       _ ≤ _ := by
           dsimp only [K]
           have H := mul_le_mul (mul_le_mul_of_nonneg_left htP (sq_nonneg C)) hE (by positivity) (by positivity)
           calc _ ≤ (C^2*(2^c*T^c)*(Real.exp (c^2+A^2/2)*Real.exp (-v^2/2)))/(2*π*c) := by
                  apply div_le_div_of_nonneg_right _ (by positivity)
                  convert H using 1; ring
                _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
