import AnalyticNumberTheory.PrimeDistribution.CharacterMellinDetector

/-! # Positive finite-window bounds for the character Mellin detector -/
noncomputable section
open Complex Real Finset Filter MeasureTheory
open scoped ArithmeticFunction.Moebius Topology
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

private def critical (t : ℝ) : ℂ := (1/2:ℂ)+t*I

/-- On the critical line the kernel retains six powers of vertical decay.
The factor `1/d` measures the horizontal distance to the pole at zero. -/
theorem norm_characterRieszKernel_critical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℕ) {Y d : ℝ} (hY : 0<Y) {ρ : ℂ} (hβ : ρ.re≤1) (hd : 0<d) (hgap : d≤ρ.re-1/2)
    (t : ℝ) :
    let s := (1/2:ℂ)+t*I
    ‖characterRieszKernel χ X 6 ρ Y (((1/2-ρ.re:ℝ):ℂ)+((t-ρ.im:ℝ):ℂ)*I)‖ ≤
      (729/d*Y^(1/2-ρ.re))*(1/(1+|t-ρ.im|)^6*‖χ.LFunction s‖*‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X s‖) := by
  intro s
  let w : ℂ := ((1/2-ρ.re:ℝ):ℂ)+((t-ρ.im:ℝ):ℂ)*I
  have hr : w.re=1/2-ρ.re := by simp [w]
  have hi : w.im=t-ρ.im := by simp [w]
  have hs : ρ+w=s := by apply Complex.ext <;> simp [s,w] <;> ring
  have hw : d≤‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [hr,abs_of_nonpos (by linarith)] at h;linarith
  have hD := rieszDenom_norm_lower 6 (w:=w) (by rw [hr];linarith) hd.le hw
  rw [hi] at hD
  change ‖characterRieszKernel χ X 6 ρ Y w‖≤_
  rw [characterRieszKernel,mollifiedLFunction,hs,norm_div,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hY,hr]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hD).trans_eq
  field_simp;ring

set_option maxHeartbeats 500000 in
/-- Every zero yielding the integral alternative has a positive detector on
each sufficiently large symmetric height window. A finite family of zeros can
therefore be treated on a common window even when its moduli exceed its height. -/
theorem character_detector_window {q X : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hX : 1≤X) {Y d : ℝ} (hY : 16≤Y)
    {ρ : ℂ} (hd : 0<d) (hgap : d≤ρ.re-1/2) (hβ : ρ.re<1) (hz : χ.LFunction ρ=0) :
    1/4≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ n*(n:ℂ)^(-ρ)‖ ∨
    ∀ᶠ R : ℝ in atTop, 1/8 ≤ (729*‖(720/(2*π):ℂ)‖/d*Y^(1/2-ρ.re))*
      (∫ t in -R..R, (1/(1+|t-ρ.im|)^6)*‖χ.LFunction ((1/2:ℂ)+t*I)‖*
        ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+t*I)‖) := by
  rcases character_mellin_dichotomy hχ hX hY (by linarith) hβ hz with h|h
  · exact Or.inl h
  right
  let c := (720/(2*π):ℂ)
  let F (v : ℝ) := characterRieszKernel χ X 6 ρ Y (((1/2-ρ.re:ℝ):ℂ)+v*I)
  let G (t : ℝ) := c*F (t-ρ.im)
  let P (t : ℝ) := 1/(1+|t-ρ.im|)^6*‖χ.LFunction (critical t)‖*
    ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X (critical t)‖
  let A := 729*‖c‖/d*Y^(1/2-ρ.re)
  have hnorm (t : ℝ) : ‖G t‖ ≤ A*P t := by
    have hb := norm_characterRieszKernel_critical χ X (by linarith : 0<Y) hβ.le hd hgap t
    change ‖c*F (t-ρ.im)‖ ≤ _
    rw [norm_mul]
    change ‖F (t-ρ.im)‖ ≤ (729/d*Y^(1/2-ρ.re))*P t at hb
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by dsimp only [A];ring)
  have hG : 1/4≤‖∫ t : ℝ,G t‖ := by
    dsimp only [G]
    rw [integral_const_mul,integral_sub_right_eq_self F ρ.im]
    exact h
  have hi : Integrable G := by
    by_contra hn
    rw [integral_undef hn,norm_zero] at hG
    norm_num at hG
  have hP : Continuous P := by
    have hc : Continuous critical := by unfold critical; fun_prop
    have hL := (DirichletCharacter.differentiable_LFunction hχ).continuous.comp hc
    have hp := (differentiable_dirichletPoly (fun n => (μ n:ℂ)*χ n) X).continuous.comp hc
    exact ((continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 6)
      (fun t => by change (1+|t-ρ.im|)^6≠0;positivity)).mul hL.norm).mul hp.norm
  have ht := intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  filter_upwards [ht.norm.eventually_const_lt (show (1/8:ℝ)<‖∫ t,G t‖ by linarith),eventually_ge_atTop (0:ℝ)] with R hR hR₀
  change 1/8 ≤ A*∫ t in -R..R,P t
  rw [←intervalIntegral.integral_const_mul]
  exact hR.le.trans ((intervalIntegral.norm_integral_le_integral_norm (by linarith : -R≤R)).trans
    (intervalIntegral.integral_mono_on (by linarith) (hi.intervalIntegrable.norm)
      ((hP.const_mul A).intervalIntegrable ..) (fun t _ => hnorm t)))

end AnalyticNumberTheory.PrimeDistribution
