import AnalyticNumberTheory.RiemannZeta.FourthMomentContourIntegrand

/-! # Bounding the analytic fourth-moment cross term on the line of absolute convergence -/
noncomputable section
open Complex Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem right_cross_majorant :
    ∃ D : ℝ, 0<D ∧ ∀ {T t : ℝ} (N : ℕ), 4≤T → T/2≤t →
      let s := (2:ℂ)+(t:ℂ)*I
      let P := ‖divisorPolynomial N (1-s)‖
      let E := ‖riemannZeta s^2-divisorPolynomial N s‖
      ‖fourthMomentCrossTerm N s‖ ≤ E*P+(D/T^3)*P^2 := by
  obtain ⟨C,hC,HC⟩ := norm_riemannDualGamma_on_strip 2 2
  refine ⟨8*C^2,by positivity,?_⟩
  intro T t N hT ht s P E
  have ht₀ : 2≤t := by linarith
  have hT₀ : 0<T := by linarith
  have hsre : s.re=2 := by simp [s]
  have hsim : s.im=t := by simp [s]
  have H := HC s ⟨hsre.ge,hsre.le⟩ (by rw [hsim,abs_of_nonneg (by linarith)];linarith)
  rw [hsim,hsre,abs_of_nonneg (by linarith)] at H
  have hp : (t^(1/2-(2:ℝ)))^2 = 1/t^3 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith)]
    norm_num [Real.rpow_neg (by linarith : 0≤t),one_div]
  have hgt : ‖riemannDualGamma s‖^2 ≤ C^2/t^3 := by
    simpa only [mul_pow,hp,mul_one_div] using pow_le_pow_left₀ (norm_nonneg _) H 2
  have htg : C^2/t^3 ≤ 8*C^2/T^3 := by
    rw [div_le_div_iff₀ (pow_pos (by linarith) 3) (pow_pos hT₀ 3)]
    have hcube := pow_le_pow_left₀ hT₀.le (by linarith : T≤2*t) 3
    nlinarith only [mul_le_mul_of_nonneg_left hcube (sq_nonneg C)]
  have hra := norm_sub_le (riemannZeta s^2-divisorPolynomial N s)
    (riemannDualGamma s^2*divisorPolynomial N (1-s))
  rw [norm_mul,norm_pow] at hra
  have hP : 0≤P := norm_nonneg _
  have hR : ‖fourthMomentError N s‖ ≤ E+(8*C^2/T^3)*P :=
    hra.trans (add_le_add (le_refl E) (mul_le_mul_of_nonneg_right (hgt.trans htg) hP))
  rw [fourthMomentCrossTerm,norm_mul]
  exact (mul_le_mul_of_nonneg_right hR hP).trans_eq (by ring)

/-- Pointwise transfer of polynomial and tail bounds to the right edge of the contour. -/
theorem fourthMomentCrossTerm_right_of_pointwise {B : ℝ} (hB : 0<B) :
    ∃ C : ℝ,0<C ∧ ∀ {T t : ℝ} {N : ℕ}, 4≤T → T/2≤t →
      let s := (2:ℂ)+(t:ℂ)*I
      ‖divisorPolynomial N (1-s)‖ ≤ B*T^2*(1+Real.log T) →
      ‖riemannZeta s^2-divisorPolynomial N s‖ ≤ B/T*(1+Real.log T) →
      ‖fourthMomentCrossTerm N s‖ ≤ C*T*(1+Real.log T)^3 := by
  obtain ⟨D,hD,HD⟩ := right_cross_majorant
  refine ⟨B^2*(1+D),by positivity,?_⟩
  intro T t N hT ht s hP hE
  let L := 1+Real.log T
  have hT₀ : 0<T := by linarith
  have hL : 1≤L := by dsimp [L];linarith [Real.log_nonneg (by linarith : 1≤T)]
  have H := HD N hT ht
  apply H.trans
  calc
    _ ≤ (B/T*L)*(B*T^2*L)+(D/T^3)*(B*T^2*L)^2 := by
      apply add_le_add (mul_le_mul hE hP (norm_nonneg _) (by positivity))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hP 2) (by positivity)
    _ = (B^2*(1+D)*T)*L^2 := by field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 2≤3)) (by positivity)

/-- Right-edge integral estimate, using the two mean squares on the line of real part two. -/
theorem fourthMomentCrossTerm_right_integral_of_means {B : ℝ} (hB : 0<B) :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ} {N : ℕ}, 4≤T →
      let s := fun t : ℝ => (2:ℂ)+(t:ℂ)*I
      let L := (1+Real.log T)^3
      (∫ t in T..2*T, ‖divisorPolynomial N (1-s t)‖^2) ≤ B*T^4*L →
      (∫ t in T..2*T, ‖riemannZeta (s t)^2-divisorPolynomial N (s t)‖^2) ≤ B/T^2*L →
      ‖∫ t in T..2*T, fourthMomentCrossTerm N (s t)‖ ≤ C*T*L := by
  obtain ⟨D,hD,HD⟩ := right_cross_majorant
  refine ⟨B*(2+D),by positivity,?_⟩
  intro T N hT s L hp he
  let P (t : ℝ) := ‖divisorPolynomial N (1-s t)‖
  let E (t : ℝ) := ‖riemannZeta (s t)^2-divisorPolynomial N (s t)‖
  have hs : Continuous s := by dsimp [s];fun_prop
  have hζ : Continuous (fun t => riemannZeta (s t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f:=s) (differentiableAt_riemannZeta (by
      intro h; have := congrArg Complex.re h; norm_num [s] at this)).continuousAt hs.continuousAt
  have hpol := (differentiable_divisorPolynomial N).continuous
  have hP : Continuous P := (hpol.comp (continuous_const.sub hs)).norm
  have hE : Continuous E := ((hζ.pow 2).sub (hpol.comp hs)).norm
  have hT₀ : 0<T := by linarith
  have tiE : IntervalIntegrable (fun t => (E t)^2) volume T (2*T) := (hE.pow 2).intervalIntegrable (μ:=volume) T (2*T)
  have tiP : IntervalIntegrable (fun t => (P t)^2) volume T (2*T) := (hP.pow 2).intervalIntegrable (μ:=volume) T (2*T)
  have hm (t : ℝ) (ht : t∈Ioc T (2*T)) :
      ‖fourthMomentCrossTerm N (s t)‖≤ T^3*(E t)^2+((1+D)/T^3)*(P t)^2 := by
    have hh := HD (T:=T) (t:=t) N hT (by linarith [ht.1])
    change ‖fourthMomentCrossTerm N (s t)‖ ≤ E t*P t+(D/T^3)*(P t)^2 at hh
    apply hh.trans
    field_simp [hT₀.ne']
    nlinarith only [sq_nonneg (T^3*E t-P t),sq_nonneg (P t),sq_nonneg (T^3*E t)]
  have H := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) (by linarith : T≤2*T)
    (ae_of_all _ hm) ((tiE.const_mul (T^3)).add (tiP.const_mul ((1+D)/T^3)))
  rw [intervalIntegral.integral_add (tiE.const_mul _) (tiP.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at H
  apply H.trans
  calc
    _ ≤ T^3*(B/T^2*L) + ((1+D)/T^3)*(B*T^4*L) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by positivity)) (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by field_simp <;> ring

end AnalyticNumberTheory.RiemannZeta
