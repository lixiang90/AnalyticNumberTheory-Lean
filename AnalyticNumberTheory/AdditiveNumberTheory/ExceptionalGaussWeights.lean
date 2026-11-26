import AnalyticNumberTheory.AdditiveNumberTheory.GaussCoefficientBounds

/-! # The two possible main terms in a finite character expansion -/

noncomputable section

open Finset
open scoped Classical

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- At a fixed level a primitive inducing pair determines its character. -/
theorem character_inducingPair_injective (q : ℕ) :
    Function.Injective (fun χ : DirichletCharacter ℂ q =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m)) := by
  intro χ ψ he
  exact (eq_changeLevel_of_inducingPair_eq ψ.conductor_dvd_level he).trans ψ.changeLevel_primitiveCharacter

/-- In a finite character expansion only the principal character and the
one induced by a selected primitive pair can use the larger bound E+M.
Their extra contributions each cost at most B M, independently of φ(q). -/
theorem norm_sum_rationalCharacterCoefficient_exceptional {q : ℕ} [NeZero q] (a : ℕ)
    (e₀ : Σ m : ℕ, DirichletCharacter ℂ m) (f : DirichletCharacter ℂ q → ℂ)
    {B E M : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hcoeff : ∀ χ : DirichletCharacter ℂ q, ‖rationalCharacterCoefficient χ a‖ ≤ B)
    (hall : ∀ χ, ‖f χ‖ ≤ E+M)
    (hgood : ∀ χ, χ ≠ 1 →
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) ≠ e₀ → ‖f χ‖ ≤ E) :
    ‖∑ χ : DirichletCharacter ℂ q, rationalCharacterCoefficient χ a*f χ‖ ≤
      (q.totient : ℝ)*E + 2*B*M := by
  let D := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ =>
    (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) = e₀)
  let W := insert 1 D
  have hD : D.card ≤ 1 := card_le_one.mpr (fun χ hχ ψ hψ =>
    character_inducingPair_injective q (((mem_filter.mp hχ).2).trans (mem_filter.mp hψ).2.symm))
  have hW : W.card ≤ 2 := (card_insert_le _ _).trans (by omega)
  have hterm (χ : DirichletCharacter ℂ q) :
      ‖rationalCharacterCoefficient χ a*f χ‖ ≤ E + (if χ ∈ W then B*M else 0) := by
    let G := ‖rationalCharacterCoefficient χ a‖
    have hG : 0 ≤ G := norm_nonneg _
    have hG₁ : G ≤ 1 := norm_rationalCharacterCoefficient_le_one χ a
    rw [norm_mul]
    change G * ‖f χ‖ ≤ _
    by_cases hh : χ ∈ W
    · rw [ite_eq_left hh]
      calc _ ≤ G*(E+M) := mul_le_mul_of_nonneg_left (hall χ) hG
           _ = G*E + G*M := mul_add ..
           _ ≤ E+B*M := add_le_add (mul_le_of_le_one_left hE hG₁)
             (mul_le_mul_of_nonneg_right (hcoeff χ) hM)
    · rw [ite_eq_right hh, add_zero]
      have hn : χ ≠ 1 := fun e => hh (e ▸ mem_insert_self _ _)
      have hne : (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) ≠ e₀ :=
        fun e => hh (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, e⟩))
      exact (mul_le_of_le_one_left (norm_nonneg _) hG₁).trans (hgood χ hn hne)
  calc _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖rationalCharacterCoefficient χ a*f χ‖ := norm_sum_le _ _
       _ ≤ ∑ χ : DirichletCharacter ℂ q, (E + if χ ∈ W then B*M else 0) := sum_le_sum (fun χ _ => hterm χ)
       _ = (q.totient : ℝ)*E + W.card*(B*M) := by
         rw [sum_add_distrib, sum_ite_mem, univ_inter]
         simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_eq_nat_card,
           DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
       _ ≤ _ := by
         have hh := mul_le_mul_of_nonneg_right (show (W.card : ℝ) ≤ 2 by exact_mod_cast hW) (mul_nonneg hB hM)
         linarith only [hh]

end AnalyticNumberTheory.AdditiveNumberTheory
