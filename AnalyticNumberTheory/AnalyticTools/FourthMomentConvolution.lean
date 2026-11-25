import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Convolution estimates for fourth moments

A positive integrable majorant transfers bounds on all translated height
intervals to a convolution, uniformly over a finite family.
-/
noncomputable section
open Real Finset Set MeasureTheory Filter
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- Fourth-power Jensen inequality for a positive, possibly unnormalized
weight. The additional unit in the mass permits the zero measure as well. -/
theorem weighted_integral_fourth_le {w f : ℝ→ℝ} (hw : ∀v,0≤w v) (hf : ∀v,0≤f v)
    (hi : Integrable w) (h₁ : Integrable (fun v=>w v*f v))
    (h₄ : Integrable (fun v=>w v*f v^4)) :
    (∫v,w v*f v)^4 ≤ (1+∫v,w v)^3*∫v,w v*f v^4 := by
  let W := 1+∫v,w v
  let x := (∫v,w v*f v)/W
  have hw₀ := integral_nonneg (μ:=volume) hw
  have hW : 0<W := by dsimp [W];linarith
  have hx : 0≤x := div_nonneg (integral_nonneg fun v=>mul_nonneg (hw v) (hf v)) hW.le
  have hid : (∫v,w v*f v)=W*x := by dsimp [x];field_simp
  have hpoint (v : ℝ) : (4*x^3)*(w v*f v)-(3*x^4)*w v ≤ w v*f v^4 := by
    have h := mul_nonneg (hw v) (mul_nonneg (sq_nonneg (f v-x))
      (show 0≤f v^2+2*x*f v+3*x^2 by positivity [hf v]))
    nlinarith only [h]
  have hh := integral_mono ((h₁.const_mul (4*x^3)).sub (hi.const_mul (3*x^4))) h₄ hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (h₁.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul,hid] at hh
  have hmass : (∫v,w v)=W-1 := by dsimp [W];ring
  rw [hmass] at hh
  change _≤W^3*_
  rw [hid]
  nlinarith only [mul_le_mul_of_nonneg_left hh (pow_nonneg hW.le 3),
    mul_nonneg (pow_nonneg hW.le 3) (pow_nonneg hx 4)]

/-- Bound a fourth moment across a finite family for a convolution with
a common nonnegative majorant. The input fourth-moment bound may be used
on all translates of the prescribed interval. -/
theorem family_fourth_convolution_le {ι : Type*} (S : Finset ι)
    (F f : ι→ℝ→ℝ) (w : ℝ→ℝ) {a b K M R : ℝ} (hab : a≤b) (hK : 0≤K)
    (hw : ∀v,0≤w v) (cw : Continuous w) (hi : Integrable w)
    (cf : ∀i∈S,Continuous (f i)) (hf : ∀i∈S,∀t,0≤f i t ∧ f i t≤M)
    (hF : ∀i∈S,∀t∈Set.Icc a b,0≤F i t ∧ F i t≤K*∫v,w v*f i (t+v))
    (hR : ∀v, (∑i∈S,∫t in (a+v)..(b+v),f i t^4)≤R) :
    (∑i∈S,∫t in a..b,F i t^4)≤K^4*(1+∫v,w v)^4*R := by
  let μ := volume.restrict (Set.Ioc a b)
  let W := 1+∫v,w v
  have hW : 0<W := by dsimp [W];linarith [integral_nonneg (μ:=volume) hw]
  let D := K^4*W^3
  have hD : 0≤D := by dsimp [D];positivity
  have hμ : IsFiniteMeasure μ := by dsimp [μ];infer_instance
  let g (i : ι) (t v : ℝ) := w v*f i (t+v)^4
  have hi₄ (i) (hι : i∈S) : Integrable (Function.uncurry (g i)) (μ.prod volume) := by
    have h₀ : Integrable (fun _:ℝ=>M^4) μ := integrable_const _
    apply (h₀.mul_prod hi).mono' (by dsimp [g,Function.uncurry];fun_prop (disch:=exact cf i hι))
    filter_upwards with p
    change ‖w p.2*f i (p.1+p.2)^4‖≤M^4*w p.2
    rw [Real.norm_of_nonneg (mul_nonneg (hw _) (by positivity))]
    simpa only [mul_comm (M^4)] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hf i hι _).1 (hf i hι _).2 4) (hw _)
  have hrow (i) (hι : i∈S) :
      (∫t in a..b,F i t^4) ≤ D*∫v,w v*(∫t in (a+v)..(b+v),f i t^4) := by
    have hpoint (t : ℝ) (ht : t∈Set.Ioc a b) : F i t^4≤D*∫v,g i t v := by
      have hj (k : ℕ) : Integrable (fun v=>w v*f i (t+v)^k) := by
        apply (hi.mul_const (M^k)).mono' (by fun_prop (disch:=exact cf i hι))
        filter_upwards with v
        rw [Real.norm_of_nonneg (mul_nonneg (hw _) (pow_nonneg (hf i hι _).1 _))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hf i hι _).1 (hf i hι _).2 k) (hw _)
      have h := weighted_integral_fourth_le hw (fun v=>(hf i hι (t+v)).1) hi
        (by simpa only [pow_one] using hj 1) (hj 4)
      have hp := hF i hι t ⟨ht.1.le,ht.2⟩
      apply (pow_le_pow_left₀ hp.1 hp.2 4).trans
      rw [mul_pow]
      exact (mul_le_mul_of_nonneg_left h (pow_nonneg hK 4)).trans_eq (by dsimp [D,W,g];ring)
    rw [intervalIntegral.integral_of_le hab]
    have hle : (∫t,F i t^4 ∂μ)≤∫t,D*(∫v,g i t v) ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun t=>by positivity)) (((hi₄ i hι).integral_prod_left).const_mul D)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hpoint t ht
    apply hle.trans_eq
    rw [integral_const_mul,integral_integral_swap (hi₄ i hι)]
    congr 1;apply integral_congr_ae;filter_upwards with v
    rw [←intervalIntegral.integral_comp_add_right (f:=fun t=>f i t^4),intervalIntegral.integral_of_le hab]
    exact integral_const_mul (μ:=μ) (w v) (fun t=>f i (t+v)^4)
  have hirow (i) (hι : i∈S) : Integrable (fun v=>w v*(∫t in (a+v)..(b+v),f i t^4)) := by
    apply ((hi₄ i hι).integral_prod_right).congr
    filter_upwards with v
    rw [←intervalIntegral.integral_comp_add_right (f:=fun t=>f i t^4),intervalIntegral.integral_of_le hab]
    exact integral_const_mul (μ:=μ) (w v) (fun t=>f i (t+v)^4)
  apply (sum_le_sum hrow).trans
  rw [←mul_sum,←integral_finsetSum S hirow]
  have hlast : (∫v,∑i∈S,w v*(∫t in (a+v)..(b+v),f i t^4)) ≤ (∫v,w v)*R := by
    rw [←integral_mul_const]
    apply integral_mono (integrable_finsetSum S hirow) (hi.mul_const R)
    intro v;dsimp only;rw [←mul_sum];exact mul_le_mul_of_nonneg_left (hR v) (hw v)
  have hr : 0≤R := le_trans (Finset.sum_nonneg (fun i _=>intervalIntegral.integral_nonneg (by linarith) (fun _ _=>by positivity))) (hR 0)
  apply (mul_le_mul_of_nonneg_left hlast hD).trans
  have hmass : (∫v,w v)=W-1 := by dsimp [W];ring
  change D*(_*R)≤K^4*W^4*R
  rw [hmass];dsimp only [D];nlinarith only [mul_nonneg hD hr]

/-- Translates of a bounded continuous input against a continuous integrable
positive weight depend continuously on the translation. -/
theorem continuous_positive_convolution {w f : ℝ→ℝ} (cw : Continuous w) (hi : Integrable w)
    (hw : ∀t,0≤w t) (cf : Continuous f) {M : ℝ} (hf : ∀t,0≤f t ∧ f t≤M) :
    Continuous (fun t=>∫v,w v*f (t+v)) := by
  apply continuous_of_dominated (bound:=fun v=>w v*M)
  · intro t;exact (cw.mul (cf.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro t;apply ae_of_all;intro v
    rw [Real.norm_of_nonneg (mul_nonneg (hw v) (hf _).1)];exact mul_le_mul_of_nonneg_left (hf _).2 (hw v)
  · exact hi.mul_const M
  · exact ae_of_all _ (fun v=>continuous_const.mul (cf.comp (continuous_id.add continuous_const)))

/-- Transfer three nonnegative majorants to a finite family fourth moment.
The factor 64 follows by applying the two-term power inequality twice. -/
theorem family_three_fourth_le {ι : Type*} (S : Finset ι) (F f g h : ι→ℝ→ℝ)
    {a b A B C : ℝ} (hab : a≤b) (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (hc : ∀ i∈S,Continuous (f i) ∧ Continuous (g i) ∧ Continuous (h i))
    (hn : ∀ i∈S,∀t∈Set.Icc a b,0≤f i t ∧ 0≤g i t ∧ 0≤h i t)
    (hF : ∀ i∈S,∀t∈Set.Icc a b,0≤F i t ∧ F i t≤A*f i t+B*g i t+C*h i t) :
    (∑ i∈S,∫t in a..b,F i t^4)≤64*(A^4*(∑i∈S,∫t in a..b,f i t^4)+
      B^4*(∑i∈S,∫t in a..b,g i t^4)+C^4*(∑i∈S,∫t in a..b,h i t^4)) := by
  have hrow (i : ι) (hι : i∈S) : (∫t in a..b,F i t^4)≤
      64*(A^4*(∫t in a..b,f i t^4)+B^4*(∫t in a..b,g i t^4)+C^4*(∫t in a..b,h i t^4)) := by
    obtain ⟨cf,cg,ch⟩ := hc i hι
    have c₁ : Continuous (fun t=>A^4*f i t^4) := continuous_const.mul (cf.pow 4)
    have c₂ : Continuous (fun t=>B^4*g i t^4) := continuous_const.mul (cg.pow 4)
    have c₃ : Continuous (fun t=>C^4*h i t^4) := continuous_const.mul (ch.pow 4)
    have c₁₂ : Continuous (fun t=>A^4*f i t^4+B^4*g i t^4) := c₁.add c₂
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_add (c₁.intervalIntegrable ..) (c₂.intervalIntegrable ..),
      ←intervalIntegral.integral_add (c₁₂.intervalIntegrable ..) (c₃.intervalIntegrable ..),
      ←intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
    apply integral_mono_of_nonneg (ae_of_all _ (fun t=>by positivity)) ((continuous_const.mul ((c₁.add c₂).add c₃)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp only [Pi.mul_apply,Pi.add_apply] at *
    have ht' : t∈Set.Icc a b := ⟨ht.1.le,ht.2⟩
    obtain ⟨hf,hg,hh⟩ := hn i hι t ht'
    obtain ⟨hF₀,hF₁⟩ := hF i hι t ht'
    apply (pow_le_pow_left₀ hF₀ hF₁ 4).trans
    have h₁ := add_pow_le (mul_nonneg hA hf) (mul_nonneg hB hg) 4
    have h₂ := add_pow_le (add_nonneg (mul_nonneg hA hf) (mul_nonneg hB hg)) (mul_nonneg hC hh) 4
    norm_num only [Nat.reduceSub, Nat.reducePow, Nat.cast_ofNat] at h₁ h₂
    nlinarith only [h₁,h₂,pow_nonneg (mul_nonneg hC hh) 4]
  apply (sum_le_sum hrow).trans_eq
  rw [←mul_sum, sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,←mul_sum]

end AnalyticNumberTheory.AnalyticTools
