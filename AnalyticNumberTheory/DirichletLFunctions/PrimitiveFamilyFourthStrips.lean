import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthSampling
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveFamilyCriticalFourth

/-!
# Fourth means of primitive characters in logarithmically narrow strips

The constants in all estimates are absolute. A single modulus is fixed
inside each sum and may vary across estimates. This includes modulus one.
-/

open Real Complex Set Finset MeasureTheory
open scoped Classical Interval
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem primitive_critical_fourth_input :
    ∃ D : ℝ,0<D ∧ ∀{q : ℕ} [NeZero q],CharacterFamilyCriticalFourthBound
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)) D := by
  obtain ⟨D,hD,H⟩ := primitive_family_critical_fourth_moment
  refine ⟨D,hD,?_⟩
  intro q _ T hT
  exact H hT

/-- Uniform primitive-character fourth moment in a doubled symmetric window,
valid in the band of width `1/(200 log(qT))`. -/
theorem primitive_family_fourth_narrow_window :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫ t in -(2*T)..2*T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨D,hD,hS⟩ := primitive_critical_fourth_input
  obtain ⟨C,hC,H⟩ := character_family_fourth_narrow_window hD.le
  refine ⟨C,hC,?_⟩
  intro q _ T σ hT hσ
  exact H _ (hS (q:=q)) hT hσ

/-- Fourth moment of the primitive family on the symmetric interval `[-T,T]`. -/
theorem primitive_family_fourth_narrow_symmetric :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫ t in -T..T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨C,hC,H⟩ := primitive_family_fourth_narrow_window
  refine ⟨C,hC,?_⟩
  intro q _ T σ hT hσ
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hX : 2≤(q:ℝ)*T := hT.trans (by simpa using mul_le_mul_of_nonneg_right hq (show 0≤T by linarith))
  have hlog : 1/2≤Real.log ((q:ℝ)*T) := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hX)
  have hwidth : 1/(200*Real.log ((q:ℝ)*T))≤1/4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hs : σ<1 := by linarith [(abs_le.mp hσ).2]
  apply (Finset.sum_le_sum (fun χ hi => ?_)).trans (H hT hσ)
  have hc : Continuous (fun t : ℝ => χ.LFunction ((σ:ℂ)+t*I)) :=
    continuous_iff_continuousAt.mpr fun t => (analyticAt_LFunction_re_lt_one χ (z:=(σ:ℂ)+t*I) (by simpa using hs)).continuousAt.comp
      (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop)
  exact intervalIntegral.integral_mono_interval (by linarith : -(2*T)≤ -T) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) ((hc.norm.pow 4).intervalIntegrable ..)

/-- The fourth-power integral from height zero to `T`, summed over primitive
characters and uniform jointly in `q,T,σ`. -/
theorem primitive_family_fourth_narrow_strip :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫ t in (0:ℝ)..T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨D,hD,hS⟩ := primitive_critical_fourth_input
  obtain ⟨C,hC,H⟩ := character_family_fourth_narrow_strip hD.le
  refine ⟨C,hC,?_⟩
  intro q _ T σ hT hσ
  exact H _ (hS (q:=q)) hT hσ

/-- Fourth-power integral of primitive derivatives on `[-T,T]`, in the strip
of width `1/(400 log(qT))`. -/
theorem primitive_family_deriv_fourth_narrow_symmetric :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫ t in -T..T,‖deriv χ.LFunction ((σ:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(Real.log (q*T))^8 := by
  obtain ⟨D,hD,hS⟩ := primitive_critical_fourth_input
  obtain ⟨C,hC,H⟩ := character_family_deriv_fourth_narrow_symmetric hD.le
  refine ⟨C,hC,?_⟩
  intro q _ T σ hT hσ
  exact H _ (hS (q:=q)) hT hσ

/-- Fourth-power integral of primitive derivatives on `[0,T]`, uniform in
the modulus and height. -/
theorem primitive_family_deriv_fourth_narrow_strip :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫ t in (0:ℝ)..T,‖deriv χ.LFunction ((σ:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(Real.log (q*T))^8 := by
  obtain ⟨D,hD,hS⟩ := primitive_critical_fourth_input
  obtain ⟨C,hC,H⟩ := character_family_deriv_fourth_narrow_strip hD.le
  refine ⟨C,hC,?_⟩
  intro q _ T σ hT hσ
  exact H _ (hS (q:=q)) hT hσ

/-- Fourth powers at separated ordinates on the critical line, with an
independent sampling set for every primitive character. -/
theorem primitive_family_fourth_separated :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T δ : ℝ},2≤T → 0<δ →
      ∀ E : DirichletCharacter ℂ q → Finset ℝ,
      (∀ χ : DirichletCharacter ℂ q,χ.IsPrimitive → ∀ t∈E χ,|t|≤T) →
      (∀ χ : DirichletCharacter ℂ q,χ.IsPrimitive → ∀ t∈E χ,∀ u∈E χ,t≠u → δ≤|t-u|) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∑ t∈E χ,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤
        C*(δ⁻¹+Real.log (q*T))*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨D,hD,hS⟩ := primitive_critical_fourth_input
  obtain ⟨C,hC,H⟩ := character_family_fourth_separated hD.le
  refine ⟨C,hC,?_⟩
  intro q _ T δ hT hδ E hE hsep
  exact H _ (hS (q:=q)) hT hδ E (fun χ hχ => hE χ (Finset.mem_filter.mp hχ).2)
    (fun χ hχ => hsep χ (Finset.mem_filter.mp hχ).2)

end AnalyticNumberTheory.DirichletLFunctions
