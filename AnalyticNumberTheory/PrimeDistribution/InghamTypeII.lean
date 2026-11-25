import AnalyticNumberTheory.PrimeDistribution.InghamMomentBounds
import AnalyticNumberTheory.PrimeDistribution.InghamKernel

/-!
# The integral alternative in Ingham's zero detector

After translating the detecting integrals to the critical line, their weights
have bounded overlap. Weighted Hölder uses the fourth moment of zeta and the
second moment of the length-`X` Möbius polynomial.
-/

noncomputable section
open Finset Complex Real Filter MeasureTheory
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private def weight (z : ℂ) (t : ℝ) := 1/(1+|t-z.im|)^4
private lemma continuous_weight (z : ℂ) : Continuous (weight z) :=
  continuous_const.div (g:=fun t : ℝ => (1+|t-z.im|)^4) ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 4)
    (fun t => by positivity)
private lemma weight_nonneg (z : ℂ) (t : ℝ) : 0 ≤ weight z t := by unfold weight; positivity

private theorem translated_detector_le {X : ℕ} {z : ℂ} (hz : 0 ≤ z.im ∧ z.im ≤ 2*X)
    {F : ℝ → ℝ} (hF : Continuous F) (hpos : ∀ t, 0 ≤ F t) :
    (∫ v in -(4*(X:ℝ))..4*X, (1/(1+|v|)^4)*F (z.im+v)) ≤
      ∫ t in -(6*(X:ℝ))..6*X, weight z t*F t := by
  let g (t : ℝ) := weight z t*F t
  have htrans := intervalIntegral.integral_comp_add_left (a:=-(4*(X:ℝ))) (b:=4*X) g z.im
  have hi (v : ℝ) : g (z.im+v) = (1/(1+|v|)^4)*F (z.im+v) := by simp [g,weight]
  simp_rw [hi] at htrans
  apply htrans.le.trans
  have hX : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
  apply intervalIntegral.integral_mono_interval (by linarith [hz.1]) (by linarith) (by linarith [hz.2])
  · exact Eventually.of_forall fun t => mul_nonneg (weight_nonneg ..) (hpos t)
  · exact ((continuous_weight z).mul hF).intervalIntegrable ..

/-- Translate a finite family of detector integrals to a common window and
sum their translated weights. -/
theorem ingham_sum_translated_detectors_le {X : ℕ} {S : Finset ℂ} {V : ℝ}
    (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im ≤ 2*X) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hdet : ∀ z ∈ S, V ≤ ∫ v in -(4*(X:ℝ))..4*X, (1/(1+|v|)^4)*(f (z.im+v)*g (z.im+v))) :
    (S.card:ℝ)*V ≤ ∫ t in -(6*(X:ℝ))..6*X, (∑ z ∈ S,1/(1+|t-z.im|)^4)*f t*g t := by
  let T := 6*(X:ℝ)
  let w (t : ℝ) := ∑ z ∈ S, weight z t
  have hfi (z : ℂ) : Continuous fun t => weight z t*(f t*g t) := (continuous_weight z).mul (hf.mul hg)
  calc
    (S.card:ℝ)*V = ∑ _z ∈ S, V := by simp
    _ ≤ ∑ z ∈ S, ∫ t in -T..T, weight z t*(f t*g t) := by
      refine sum_le_sum fun z hz => (hdet z hz).trans ?_
      exact translated_detector_le (F:=fun t => f t*g t) (him z hz) (hf.mul hg)
        (fun t => mul_nonneg (hf0 t) (hg0 t))
    _ = ∫ t in -T..T, ∑ z ∈ S, weight z t*(f t*g t) :=
      (intervalIntegral.integral_finsetSum (fun z _ => (hfi z).intervalIntegrable ..)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change ∑ z ∈ S, weight z t*(f t*g t) = w t*f t*g t
      rw [←sum_mul,mul_assoc]

set_option maxHeartbeats 900000 in
/-- A large convolution at each ordinate implies a cubic bound on their number.
The two kernel estimates are stated explicitly so that the argument also accepts
a sharper point-density or mass bound on an individual finite set. -/
theorem ingham_integral_large_values {X : ℕ} {S : Finset ℂ} {A B V : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V) (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im ≤ 2*X)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hdet : ∀ z ∈ S, V ≤ ∫ v in -(4*(X:ℝ))..4*X, (1/(1+|v|)^4)*(f (z.im+v)*g (z.im+v)))
    (hpeak : ∀ t, (∑ z ∈ S, 1/(1+|t-z.im|)^4) ≤ A)
    (hmass : (∫ t in -(6*(X:ℝ))..6*X, ∑ z ∈ S, 1/(1+|t-z.im|)^4) ≤ B*S.card) :
    (S.card:ℝ)^3*V^4 ≤ B*A^3*(∫ t in -(6*(X:ℝ))..6*X, (f t)^4)*
      (∫ t in -(6*(X:ℝ))..6*X, (g t)^2)^2 := by
  let T := 6*(X:ℝ)
  have hT : -T ≤ T := by dsimp [T]; linarith [Nat.cast_nonneg (α:=ℝ) X]
  let w (t : ℝ) := ∑ z ∈ S, weight z t
  have hw : Continuous w := continuous_finsetSum _ fun z _ => continuous_weight z
  have hw0 (t : ℝ) : 0 ≤ w t := sum_nonneg (fun z _ => weight_nonneg z t)
  have hd := ingham_sum_translated_detectors_le him hf hg hf0 hg0 hdet
  change (S.card:ℝ)*V ≤ ∫ t in -T..T,w t*f t*g t at hd
  have hp := (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hV) hd 4).trans
    (weighted_interval_fourth_second hT hw hf hg hw0)
  have hdom (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t) :
      (∫ t in -T..T, w t*F t) ≤ A*∫ t in -T..T, F t := by
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hT ((hw.mul hF).intervalIntegrable ..)
      ((continuous_const.mul hF).intervalIntegrable ..) (fun t _ => mul_le_mul_of_nonneg_right (hpeak t) (hF0 t))
  have h₄ := hdom (fun t => (f t)^4) (hf.pow 4) (fun _ => by positivity)
  have h₂ := hdom (fun t => (g t)^2) (hg.pow 2) (fun _ => by positivity)
  have h₄' : 0 ≤ ∫ t in -T..T, w t*(f t)^4 := intervalIntegral.integral_nonneg hT (fun t _ => mul_nonneg (hw0 t) (by positivity))
  have h₂' : 0 ≤ ∫ t in -T..T, w t*(g t)^2 := intervalIntegral.integral_nonneg hT (fun t _ => mul_nonneg (hw0 t) (by positivity))
  have hw' : 0 ≤ ∫ t in -T..T, w t := intervalIntegral.integral_nonneg hT (fun t _ => hw0 t)
  have hm : (∫ t in -T..T, w t) ≤ B*(S.card:ℝ) := hmass
  have hb := (hp.trans (mul_le_mul (mul_le_mul hm h₄ h₄' (hw'.trans hm)) (pow_le_pow_left₀ h₂' h₂ 2)
    (sq_nonneg _) (mul_nonneg (hw'.trans hm) (h₄'.trans h₄))))
  let F := ∫ t in -T..T, (f t)^4
  let G := ∫ t in -T..T, (g t)^2
  change ((S.card:ℝ)*V)^4 ≤ B*(S.card:ℝ)*(A*F)*(A*G)^2 at hb
  change (S.card:ℝ)^3*V^4 ≤ B*A^3*F*G^2
  by_cases hS : S.Nonempty
  · have hcard : 0 < (S.card:ℝ) := by exact_mod_cast card_pos.mpr hS
    apply le_of_mul_le_mul_left (a:=(S.card:ℝ)) _ hcard
    convert hb using 1 <;> ring
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp only [card_empty,Nat.cast_zero,zero_pow (by decide : 3≠0),zero_mul]
    have h₄'' : 0 ≤ F :=
      intervalIntegral.integral_nonneg hT (fun t _ => pow_nonneg (hf0 t) 4)
    positivity

/-- Type II count in its cubic form. The detection threshold `V` may depend on
the cutoff and the lower edge of the strip but is uniform over `S`. -/
theorem ingham_typeII_count :
    ∃ C > (0:ℝ), ∀ {X : ℕ}, 1 ≤ X → ∀ {S : Finset ℂ} {K V : ℝ}, 0 ≤ K → 0 ≤ V →
      (∀ z ∈ S, 0 ≤ z.im ∧ z.im ≤ 2*X) →
      (∀ j < 2*X+1, ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K) →
      (∀ z ∈ S, V ≤ ∫ v in -(4*(X:ℝ))..4*X,
        (1/(1+|v|)^4)*(‖riemannZeta ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖*
          ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖)) →
      (S.card:ℝ)^3*V^4 ≤ C*K^3*(X:ℝ)^3*(1+Real.log X)^6 := by
  obtain ⟨D,hD,hd⟩ := ingham_zeta_fourth_mean
  refine ⟨π*(2*π)^3*D*(12+2*π)^2,by positivity,?_⟩
  intro X hX S K V hK hV him hcount hdet
  let f (t : ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖
  let g (t : ℝ) := ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖
  have hf : Continuous f := continuous_riemannZeta_half.norm
  have hg : Continuous g := by
    apply Continuous.norm
    unfold dirichletPoly
    apply continuous_finsetSum
    intro n hn
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    simp_rw [Complex.cpow_def_of_ne_zero hn0]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg))
  have hL : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < (2*X+1:ℕ) := by
    intro z hz
    obtain ⟨h₀,h₁⟩ := him z hz
    exact ⟨h₀,by push_cast; linarith⟩
  have hT : -(6*(X:ℝ)) ≤ 6*X := by linarith [Nat.cast_nonneg (α:=ℝ) X]
  have h := ingham_integral_large_values (by positivity : 0 ≤ 2*π*K) pi_pos.le hV him hf hg
    (fun t => norm_nonneg _) (fun t => norm_nonneg _) hdet (ingham_kernel_sum_le S hK hL hcount)
    (ingham_kernel_integral_le S hT)
  have h₄ := hd X hX
  have h₂ := ingham_mobius_second_mean X
  have hg0 : 0 ≤ ∫ t in -(6*(X:ℝ))..6*X, (g t)^2 := intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
  have hf0 : 0 ≤ ∫ t in -(6*(X:ℝ))..6*X, (f t)^4 := intervalIntegral.integral_nonneg hT (fun t _ => pow_nonneg (norm_nonneg _) _)
  have hk : 0 ≤ π*(2*π*K)^3 := by positivity
  exact (h.trans (mul_le_mul (mul_le_mul_of_nonneg_left h₄ hk) (pow_le_pow_left₀ hg0 h₂ 2)
    (sq_nonneg _) (mul_nonneg hk (hf0.trans h₄)))).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
