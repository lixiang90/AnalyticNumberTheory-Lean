import AnalyticNumberTheory.DirichletLFunctions.PrimitiveFamilyFourthStrips
import AnalyticNumberTheory.DirichletLFunctions.ConductorMomentStrips

/-!
# Fourth moments in narrow strips for all characters

For a fixed modulus the estimate holds both for the inducing primitive
functions and for the functions with their actual Euler factors. Summing
primitive families through a varying conductor gives the quadratic bound.
-/

open Real Complex Set Finset MeasureTheory
open scoped Classical Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Simultaneous fourth moments on the doubled height window, for all
characters and for their inducing primitive functions. -/
theorem full_character_fourth_narrow_window :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      ((∑χ : DirichletCharacter ℂ q,∫t in -(2*T)..2*T,‖inducingLFunction χ ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^4) ∧
      ((∑χ : DirichletCharacter ℂ q,∫t in -(2*T)..2*T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^4) := by
  obtain ⟨D,hD,H⟩ := primitive_family_fourth_narrow_window
  exact full_character_fourth_narrow_of_primitive hD (by norm_num : (0:ℝ)≤2) (fun hT hσ => H hT hσ)

/-- The full character family and its inducing primitive functions both
have a fourth moment bounded by a constant times `q T log⁴(qT)`. -/
theorem full_character_fourth_narrow_symmetric :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      ((∑χ : DirichletCharacter ℂ q,∫t in -T..T,‖inducingLFunction χ ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^4) ∧
      ((∑χ : DirichletCharacter ℂ q,∫t in -T..T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^4) := by
  obtain ⟨D,hD,H⟩ := primitive_family_fourth_narrow_symmetric
  simpa only [one_mul] using full_character_fourth_narrow_of_primitive hD zero_le_one
    (fun hT hσ => by simpa only [one_mul] using H hT hσ)

/-- Summing the primitive fourth moments over all conductors up to `Q` gives
a uniform `Q² T log⁴(QT)` bound on the same narrow strip. -/
theorem primitive_conductors_fourth_narrow_strip :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ} {σ T : ℝ},1≤Q → 2≤T → |σ-1/2|≤1/(200*Real.log (Q*T)) →
      (∑p∈PrimeDistribution.primitiveCharacterFamily Q,∫t in -T..T,‖familyLFunction p ((σ:ℂ)+t*I)‖^4)≤
        C*(Q:ℝ)^2*T*(Real.log (Q*T))^4 := by
  obtain ⟨D,hD,H⟩ := primitive_family_fourth_narrow_symmetric
  exact ⟨D,hD,fun hQ hT hσ => primitive_conductors_fourth_narrow_of_fixed hD (fun hT hσ => H hT hσ) hQ hT hσ⟩

end AnalyticNumberTheory.DirichletLFunctions
