import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear
import AnalyticNumberTheory.DirichletLFunctions.Characters

/-!
# Products of characters in a sparse family

For a fixed modulus a product stays at that modulus. For a primitive
family of levels at most Q the product has a representative of level at
most Q². In both situations the principal product can occur only on the
diagonal of the family.
-/
open Finset Complex DirichletCharacter
open scoped Classical ComplexConjugate
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- Common-level representatives for all pointwise correlations of a character family. -/
def CharacterCorrelationFamily {ι : Type*} (F : Finset ι) (f : ι→ℕ→ℂ) (D : ℕ) : Prop :=
  ∀i∈F,∀j∈F,∃q : ℕ,0<q ∧ q≤D ∧ ∃ ψ : DirichletCharacter ℂ q,
    (∀n : ℕ,ψ n=f i n*conj (f j n)) ∧ (ψ=1 → i=j)

/-- All characters modulo q form a family with correlation level q. -/
theorem fixed_modulus_correlation_family (q : ℕ) [NeZero q] :
    CharacterCorrelationFamily (univ : Finset (DirichletCharacter ℂ q)) (fun χ n => χ n) q := by
  intro χ _ ψ _
  refine ⟨q,NeZero.pos q,le_rfl,χ*ψ⁻¹,fun n => ?_,fun h => ?_⟩
  · rw [MulChar.mul_apply,conj_char_apply]
  · exact mul_inv_eq_one.mp h

private theorem char_nat_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (h : ¬n.Coprime q) :
    χ n=0 := MulChar.map_nonunit χ (fun hu => h ((ZMod.isUnit_iff_coprime n q).mp hu))

private theorem lifted_agrees {q d : ℕ} (χ : DirichletCharacter ℂ q) (h : q∣d)
    {n : ℕ} (hn : n.Coprime d) : χ.changeLevel h n=χ n := by
  simpa only [Int.cast_natCast] using changeLevel_eq_cast_of_dvd' χ h (Nat.isCoprime_iff_coprime.mpr hn)

/-- All primitive characters with level at most Q have correlation level at most Q². -/
theorem primitive_correlation_family (Q : ℕ) :
    CharacterCorrelationFamily (primitiveCharacterFamily Q) (fun p n => p.2 n) (Q^2) := by
  rintro ⟨q,χ⟩ hχ ⟨r,ψ⟩ hψ
  obtain ⟨hq,hχ⟩ := mem_sigma.mp hχ
  obtain ⟨hr,hψ⟩ := mem_sigma.mp hψ
  obtain ⟨hq₀,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₀,hrQ⟩ := mem_Icc.mp hr
  have hp := (mem_filter.mp hχ).2
  have hp' := (mem_filter.mp hψ).2
  change 1≤q at hq₀
  change 1≤r at hr₀
  letI : NeZero q := ⟨Nat.ne_of_gt hq₀⟩
  letI : NeZero r := ⟨by omega⟩
  let c := χ.changeLevel (dvd_mul_right q r)
  let e := ψ.changeLevel (dvd_mul_left r q)
  refine ⟨q*r,Nat.mul_pos hq₀ hr₀,(Nat.mul_le_mul hqQ hrQ).trans_eq (sq Q).symm,c*e⁻¹,?_,?_⟩
  · intro n
    change (c*e⁻¹) n=χ n*conj (ψ n)
    rw [MulChar.mul_apply,←conj_char_apply]
    by_cases hn : n.Coprime (q*r)
    · rw [show c n=χ n from lifted_agrees χ _ hn,show e n=ψ n from lifted_agrees ψ _ hn]
    · rw [char_nat_zero c hn,zero_mul]
      rcases not_and_or.mp (mt Nat.coprime_mul_iff_right.mpr hn) with h|h
      · rw [char_nat_zero χ h,zero_mul]
      · rw [char_nat_zero ψ h,map_zero,mul_zero]
  · intro h
    have he := mul_inv_eq_one.mp h
    have hqr := congrArg (fun θ : DirichletCharacter ℂ (q*r) => θ.conductor) he
    simp only [c,e,conductor_changeLevel] at hqr
    have hqr' : q=r := hp.symm.trans (hqr.trans hp')
    subst r
    have hχψ := DirichletCharacter.changeLevel_injective (dvd_mul_right q q) he
    subst ψ;rfl

end AnalyticNumberTheory.SieveMethods
