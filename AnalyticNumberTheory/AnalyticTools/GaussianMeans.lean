import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Gaussian weighted second moments

A kernel dominated by a Gaussian in the integration variable preserves
a uniform bound for the second moment on a finite interval. The kernel
may vary with the point in the interval.
-/

open Real Set MeasureTheory Filter
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private noncomputable def gaussWeight (v : ℝ) := Real.exp (-(1/2:ℝ)*v^2)
private theorem weight_integrable : Integrable gaussWeight :=
  integrable_exp_neg_mul_sq (by norm_num : 0<(1/2:ℝ))
private theorem weight_pos (v : ℝ) : 0 < gaussWeight v := Real.exp_pos _
private theorem weight_continuous : Continuous gaussWeight := by unfold gaussWeight; fun_prop
private theorem weight_mass : (∫ v, gaussWeight v) = √(2*π) := by
  unfold gaussWeight
  rw [integral_gaussian]; congr 1; ring

private theorem weighted_integral_sq {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (h0 : ∀ v, 0 ≤ f v) (hb : ∀ v, f v ≤ M) :
    (∫ v, gaussWeight v*f v)^2 ≤ √(2*π)*(∫ v, gaussWeight v*(f v)^2) := by
  have h1 : Integrable (fun v => gaussWeight v*f v) := by
    apply (weight_integrable.mul_const M).mono' (weight_continuous.mul hf).aestronglyMeasurable
    filter_upwards [] with v
    change ‖gaussWeight v*f v‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (weight_pos v).le (h0 v))]
    exact mul_le_mul_of_nonneg_left (hb v) (weight_pos v).le
  have h2 : Integrable (fun v => gaussWeight v*(f v)^2) := by
    apply (weight_integrable.mul_const (M^2)).mono' (weight_continuous.mul (hf.pow 2)).aestronglyMeasurable
    filter_upwards [] with v
    change ‖gaussWeight v*(f v)^2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (weight_pos v).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h0 v) (hb v) 2) (weight_pos v).le
  let m := (∫ v, gaussWeight v*f v)/√(2*π)
  have he (v : ℝ) : gaussWeight v*(f v-m)^2 =
      gaussWeight v*(f v)^2-(gaussWeight v*f v)*(2*m)+gaussWeight v*m^2 := by ring
  have h := integral_nonneg (μ:=volume) (fun v : ℝ => mul_nonneg (weight_pos v).le (sq_nonneg (f v-m)))
  simp_rw [he] at h
  have hd : Integrable (fun v => gaussWeight v*(f v)^2-gaussWeight v*f v*(2*m)) := h2.sub (h1.mul_const _)
  rw [integral_add hd (weight_integrable.mul_const (m^2)),
    integral_sub h2 (h1.mul_const _),integral_mul_const,integral_mul_const,weight_mass] at h
  have hs : 0 < √(2*π) := by positivity
  dsimp [m] at h
  field_simp at h
  nlinarith only [h,hs]

/-- An interval second-moment bound survives integration against a kernel
bounded in norm by `K exp(-v²/2)`, at the cost of the factor `2πK²`. -/
theorem gaussian_weighted_mean_bound {a b K E : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (F P : ℝ → ℝ → ℂ) (hc : Continuous (Function.uncurry P))
    (hbounded : ∃ M : ℝ, ∀ t v, ‖P t v‖ ≤ M)
    (hF : ∀ t ∈ Ioc a b, ∀ v, ‖F t v‖ ≤ K*Real.exp (-(1/2:ℝ)*v^2))
    (hE : ∀ v, (∫ t in a..b, ‖P t v‖^2) ≤ E) :
    (∫ t in a..b, ‖∫ v, F t v*P t v‖^2) ≤ 2*π*K^2*E := by
  obtain ⟨M,hM⟩ := hbounded
  let μ := volume.restrict (Ioc a b)
  let H := fun t v => gaussWeight v*‖P t v‖^2
  have hp : Integrable (Function.uncurry H) (μ.prod volume) := by
    have hi := (integrable_const (μ:=μ) (M^2)).mul_prod weight_integrable
    apply hi.mono' ((weight_continuous.comp continuous_snd).mul (hc.norm.pow 2)).aestronglyMeasurable
    filter_upwards [] with p
    change ‖gaussWeight p.2*‖P p.1 p.2‖^2‖ ≤ M^2*gaussWeight p.2
    rw [Real.norm_of_nonneg (mul_nonneg (weight_pos _).le (sq_nonneg _)),mul_comm (M^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hM ..) 2) (weight_pos _).le
  have hpoint (t : ℝ) (ht : t ∈ Ioc a b) :
      ‖∫ v, F t v*P t v‖^2 ≤ (K^2*√(2*π))*(∫ v, H t v) := by
    have hct : Continuous (P t) := hc.comp (continuous_const.prodMk continuous_id)
    have hg : Integrable (fun v => gaussWeight v*‖P t v‖) := by
      apply (weight_integrable.mul_const M).mono' (weight_continuous.mul hct.norm).aestronglyMeasurable
      filter_upwards [] with v
      change ‖gaussWeight v*‖P t v‖‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (weight_pos _).le (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hM t v) (weight_pos v).le
    have hi := norm_integral_le_of_norm_le (hg.const_mul K) (f:=fun v => F t v*P t v)
      (Eventually.of_forall fun v => by
        rw [norm_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_right (hF t ht v) (norm_nonneg _))
    rw [integral_const_mul] at hi
    have hh := pow_le_pow_left₀ (norm_nonneg _) hi 2
    rw [mul_pow] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (weighted_integral_sq hct.norm (fun _ => norm_nonneg _) (hM t)) (sq_nonneg _)).trans_eq (by ring))
  rw [intervalIntegral.integral_of_le hab]
  have hint := integral_mono_of_nonneg (μ:=μ) (Eventually.of_forall fun t => sq_nonneg ‖∫ v, F t v*P t v‖)
    (hp.integral_prod_left.const_mul (K^2*√(2*π)))
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hpoint t ht)
  rw [integral_const_mul] at hint
  simp only [Function.uncurry_apply_pair] at hint
  rw [integral_integral_swap hp] at hint
  have hlast : (∫ v, ∫ t, H t v ∂μ) ≤ (∫ v, gaussWeight v*E) := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun v => integral_nonneg fun t => mul_nonneg (weight_pos _).le (sq_nonneg _))
      (weight_integrable.mul_const E)
    filter_upwards [] with v
    change (∫ t, gaussWeight v*‖P t v‖^2 ∂μ) ≤ _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [intervalIntegral.integral_of_le hab,μ] using hE v) (weight_pos v).le
  rw [integral_mul_const,weight_mass] at hlast
  apply hint.trans ((mul_le_mul_of_nonneg_left hlast (by positivity)).trans_eq _)
  nlinarith only [Real.sq_sqrt (by positivity : 0 ≤ 2*π),
    congrArg (fun z : ℝ => K^2*z*E) (Real.sq_sqrt (by positivity : 0 ≤ 2*π))]

/-- The Gaussian estimate for translated or reflected samples of a
bounded continuous function, using a bound on every interval of length `T`. -/
theorem gaussian_shifted_dyadic_mean {T K E : ℝ} (hT : 0≤T) (hK : 0≤K)
    (p : ℝ → ℂ) (hp : Continuous p) (hb : ∃ M : ℝ, ∀ u, ‖p u‖≤M)
    (hE : ∀ a b : ℝ, b-a=T → (∫ u in a..b, ‖p u‖^2) ≤ E)
    (negative : Bool) (F : ℝ → ℝ → ℂ)
    (hF : ∀ t ∈ Ioc T (2*T), ∀ v, ‖F t v‖ ≤ K*Real.exp (-(1/2:ℝ)*v^2)) :
    (∫ t in T..2*T, ‖∫ v, F t v*p (if negative then v-t else v+t)‖^2) ≤ 2*π*K^2*E := by
  let P := fun t v : ℝ => p (if negative then v-t else v+t)
  have hc : Continuous (Function.uncurry P) := by
    cases negative <;> apply hp.comp <;> first | exact continuous_snd.add continuous_fst | exact continuous_snd.sub continuous_fst
  obtain ⟨M,hM⟩ := hb
  apply gaussian_weighted_mean_bound (by linarith) hK F P hc ⟨M,fun t v => hM _⟩ hF
  intro v
  cases negative
  · change (∫ t in T..2*T, (fun u => ‖p u‖^2) (v+t)) ≤ _
    rw [intervalIntegral.integral_comp_add_left (fun u : ℝ => ‖p u‖^2) v]
    exact hE _ _ (by ring)
  · change (∫ t in T..2*T, (fun u => ‖p u‖^2) (v-t)) ≤ _
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => ‖p u‖^2) v]
    exact hE _ _ (by ring)

end AnalyticNumberTheory.AnalyticTools
