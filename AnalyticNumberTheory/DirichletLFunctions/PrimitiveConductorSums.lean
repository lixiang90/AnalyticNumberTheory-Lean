import AnalyticNumberTheory.DirichletLFunctions.Characters

/-! # Sums over characters classified by their primitive conductors -/
noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Reindex an arbitrary sum over the character group by primitive conductors.
The attached divisor supplies the proof of divisibility needed to lift a character. -/
theorem sum_by_primitive_conductor {q : ℕ} [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : DirichletCharacter ℂ q → A) :
    ∑ χ, f χ = ∑ d∈q.divisors.attach,
      ∑ ψ∈univ.filter (fun ψ : DirichletCharacter ℂ d.val => ψ.IsPrimitive),
        f (ψ.changeLevel (Nat.dvd_of_mem_divisors d.property)) := by
  let W (d : ℕ) := ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ.conductor=d), f χ
  have hfib : ∑ χ,f χ = ∑ d∈q.divisors,W d := (sum_fiberwise_of_maps_to
    (fun χ (_ : χ∈univ) => Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,NeZero.ne q⟩) f).symm
  rw [hfib,←sum_attach q.divisors W]
  refine sum_congr rfl fun d _ => ?_
  let hd := Nat.dvd_of_mem_divisors d.property
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  symm
  apply sum_bij (fun ψ _ => DirichletCharacter.changeLevel hd ψ)
  · intro ψ hψ
    exact mem_filter.mpr ⟨mem_univ _,conductor_changeLevel_of_isPrimitive hd (mem_filter.mp hψ).2⟩
  · intro ψ _ ξ _ h
    exact DirichletCharacter.changeLevel_injective hd h
  · intro χ hχ
    have hc := (mem_filter.mp hχ).2
    let ψ := χ.primitiveCharacter.changeLevel (dvd_of_eq hc)
    have hp : ψ.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_changeLevel]
      exact χ.primitiveCharacter_isPrimitive.trans hc
    refine ⟨ψ,mem_filter.mpr ⟨mem_univ _,hp⟩,?_⟩
    dsimp [ψ]
    rw [←DirichletCharacter.changeLevel_trans,χ.changeLevel_primitiveCharacter]
  · intro ψ _;rfl

end AnalyticNumberTheory.DirichletLFunctions
