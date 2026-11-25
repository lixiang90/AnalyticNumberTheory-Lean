import AnalyticNumberTheory.DirichletLFunctions.FullFamilyFourthStrips
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogarithmicFourthMeans

/-!
# Derivative moments and separated values over all characters

The same estimates hold for the inducing primitive functions and for
the actual Dirichlet functions with their imprimitive Euler factors.
-/

open Real Complex Set Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

private noncomputable def sampledLFunction {q : ℕ} [NeZero q] (b : Bool)
    (χ : DirichletCharacter ℂ q) : ℂ→ℂ :=
  if b then inducingLFunction χ else χ.LFunction

private theorem sampledLFunction_analytic {q : ℕ} [NeZero q] (b : Bool)
    (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : z.re<1) : AnalyticAt ℂ (sampledLFunction b χ) z := by
  cases b
  · exact analyticAt_LFunction_re_lt_one χ hz
  · letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    exact analyticAt_LFunction_re_lt_one χ.primitiveCharacter hz

private theorem sampledLFunction_window :
    ∃ A : ℝ,0<A ∧ ∀{q : ℕ} [NeZero q] (b : Bool) {σ T : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q,∫t in -(2*T)..2*T,‖sampledLFunction b χ ((σ:ℂ)+t*I)‖^4)≤A*q*T*(Real.log (q*T))^4 := by
  obtain ⟨A,hA,H⟩ := full_character_fourth_narrow_window
  refine ⟨A,hA,?_⟩
  intro q _ b σ T hT hσ
  cases b
  · exact (H hT hσ).2
  · exact (H hT hσ).1

private theorem log_modulus_height_ge {q : ℕ} [NeZero q] {T : ℝ} (hT : 2≤T) : Real.log 2≤Real.log ((q:ℝ)*T) := by
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  exact Real.log_le_log (by norm_num) (hT.trans (by simpa using mul_le_mul_of_nonneg_right hq (show 0≤T by linarith)))

private theorem sampledLFunction_deriv_strip :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (b : Bool) {σ T : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q,∫t in -T..T,‖deriv (sampledLFunction b χ) ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^8 := by
  obtain ⟨A,hA,H⟩ := sampledLFunction_window
  refine ⟨400^4*A,by positivity,?_⟩
  intro q _ b σ T hT hσ
  have hh := family_deriv_fourth_logarithmic_strip Finset.univ (sampledLFunction (q:=q) b)
    (by linarith [log_modulus_height_ge (q:=q) hT,Real.log_two_gt_d9]) hT hσ
    (fun χ _ _ hz => sampledLFunction_analytic b χ hz) (fun u hu => H b hT hu)
  exact hh.trans_eq (by ring)

/-- A joint fourth moment for the derivatives of the inducing functions and
of the actual functions, in the strip of width `1/(400 log(qT))`. -/
theorem full_character_deriv_fourth_narrow_symmetric :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log (q*T)) →
      ((∑χ : DirichletCharacter ℂ q,∫t in -T..T,‖deriv (inducingLFunction χ) ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^8) ∧
      ((∑χ : DirichletCharacter ℂ q,∫t in -T..T,‖deriv χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^8) := by
  obtain ⟨C,hC,H⟩ := sampledLFunction_deriv_strip
  exact ⟨C,hC,fun hT hσ => ⟨H true hT hσ,H false hT hσ⟩⟩

private theorem sampledLFunction_separated :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (b : Bool) {T δ : ℝ},2≤T → 0<δ →
      ∀ E : DirichletCharacter ℂ q→Finset ℝ,(∀ χ,∀ t∈E χ,|t|≤T) →
      (∀ χ,∀ t∈E χ,∀ u∈E χ,t≠u → δ≤|t-u|) →
      (∑χ : DirichletCharacter ℂ q,∑t∈E χ,‖sampledLFunction b χ ((1/2:ℂ)+t*I)‖^4)≤C*(δ⁻¹+Real.log (q*T))*q*T*(Real.log (q*T))^4 := by
  obtain ⟨A,hA,HA⟩ := sampledLFunction_window
  obtain ⟨B,hB,HB⟩ := sampledLFunction_deriv_strip
  refine ⟨5*A+512*B,by positivity,?_⟩
  intro q _ b T δ hT hδ E hE hsep
  let L := Real.log ((q:ℝ)*T)
  have hl₂ := log_modulus_height_ge (q:=q) hT
  have hL : 1/2≤L := by dsimp [L];linarith [Real.log_two_gt_d9]
  have h2T : 2≤2*T := by linarith
  have hp₂ := log_modulus_height_ge (q:=q) h2T
  have hg : 0<Real.log ((q:ℝ)*(2*T)) := by linarith [Real.log_two_gt_d9]
  have hscale : Real.log ((q:ℝ)*(2*T))≤2*L := by
    rw [show (q:ℝ)*(2*T)=2*((q:ℝ)*T) by ring,Real.log_mul (by norm_num) (mul_pos (by exact_mod_cast NeZero.pos q) (by linarith)).ne']
    change Real.log 2+L≤2*L;linarith only [hl₂]
  have hval := HA (q:=q) b (σ:=1/2) hT (by simp;positivity [show 0<Real.log ((q:ℝ)*T) by linarith [Real.log_two_gt_d9]])
  have hder := HB (q:=q) b (σ:=1/2) h2T (by simp;positivity)
  push_cast at hval hder
  have hpow := pow_le_pow_left₀ hg.le hscale 8
  have hB' := hder.trans (mul_le_mul_of_nonneg_left hpow (by positivity : 0≤B*q*(2*T)))
  have hh := family_fourth_separated_of_means Finset.univ (sampledLFunction (q:=q) b) E hL hT hδ
    (by positivity : 0≤A*q*T) (by positivity : 0≤512*B*q*T)
    (fun χ _ t => sampledLFunction_analytic b χ (by simp;norm_num))
    (fun χ _ => hE χ) (fun χ _ => hsep χ) hval (hB'.trans_eq (by ring))
  exact hh.trans_eq (by dsimp [L];ring)

/-- Fourth powers on independently chosen separated ordinate sets for every
character of a fixed modulus. The same constant bounds the actual functions
and their inducing primitive functions. -/
theorem full_character_fourth_separated :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T δ : ℝ},2≤T → 0<δ →
      ∀ E : DirichletCharacter ℂ q→Finset ℝ,(∀ χ,∀ t∈E χ,|t|≤T) →
      (∀ χ,∀ t∈E χ,∀ u∈E χ,t≠u → δ≤|t-u|) →
      ((∑χ : DirichletCharacter ℂ q,∑t∈E χ,‖inducingLFunction χ ((1/2:ℂ)+t*I)‖^4)≤C*(δ⁻¹+Real.log (q*T))*q*T*(Real.log (q*T))^4) ∧
      ((∑χ : DirichletCharacter ℂ q,∑t∈E χ,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤C*(δ⁻¹+Real.log (q*T))*q*T*(Real.log (q*T))^4) := by
  obtain ⟨C,hC,H⟩ := sampledLFunction_separated
  exact ⟨C,hC,fun hT hδ E hE hsep => ⟨H true hT hδ E hE hsep,H false hT hδ E hE hsep⟩⟩

end AnalyticNumberTheory.DirichletLFunctions
