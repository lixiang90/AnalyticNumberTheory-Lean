import AnalyticNumberTheory.SieveMethods.CharacterCorrelationFamilies

/-!
# Least common multiples as correlation conductors

A product of characters of conductors q and r can be evaluated at
their least common multiple. For a family whose conductors share a
factor b this saves that factor in the correlation level.
-/
noncomputable section
open Finset Complex DirichletCharacter
open scoped Classical ComplexConjugate
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- Primitive characters of conductor at most Q divisible by b. -/
def primitiveConductorMultiples (Q b : ℕ) :=
  (primitiveCharacterFamily Q).filter (fun p => b∣p.1)

/-- The maximum pairwise least common multiple of the conductors is an
admissible common correlation bound on any primitive subfamily. -/
theorem primitive_lcm_correlation_family {Q D : ℕ} {F : Finset (Σ q : ℕ,DirichletCharacter ℂ q)}
    (hF : F⊆primitiveCharacterFamily Q) (hD : ∀i∈F,∀j∈F,Nat.lcm i.1 j.1≤D) :
    CharacterCorrelationFamily F (fun p n => p.2 n) D := by
  rintro ⟨q,χ⟩ hi ⟨r,ψ⟩ hj
  obtain ⟨hq,hχ⟩ := mem_sigma.mp (hF hi)
  obtain ⟨hr,hψ⟩ := mem_sigma.mp (hF hj)
  have hq₀ : 0<q := (mem_Icc.mp hq).1
  have hr₀ : 0<r := (mem_Icc.mp hr).1
  have hp := (mem_filter.mp hχ).2
  have hp' := (mem_filter.mp hψ).2
  let d := q.lcm r
  have hd : 0<d := Nat.lcm_pos hq₀ hr₀
  letI : NeZero d := ⟨hd.ne'⟩
  letI : NeZero q := ⟨hq₀.ne'⟩
  letI : NeZero r := ⟨hr₀.ne'⟩
  let c := χ.changeLevel (Nat.dvd_lcm_left q r)
  let e := ψ.changeLevel (Nat.dvd_lcm_right q r)
  refine ⟨d,hd,hD _ hi _ hj,c*e⁻¹,?_,?_⟩
  · intro n
    change (c*e⁻¹) n=χ n*conj (ψ n)
    rw [MulChar.mul_apply,←conj_char_apply]
    by_cases hn : n.Coprime d
    · have hz := Nat.isCoprime_iff_coprime.mpr hn
      have h₁ : c n=χ n := by simpa only [Int.cast_natCast] using changeLevel_eq_cast_of_dvd' χ (Nat.dvd_lcm_left q r) hz
      have h₂ : e n=ψ n := by simpa only [Int.cast_natCast] using changeLevel_eq_cast_of_dvd' ψ (Nat.dvd_lcm_right q r) hz
      rw [h₁,h₂]
    · have hz {l : ℕ} (θ : DirichletCharacter ℂ l) (h : ¬n.Coprime l) : θ n=0 :=
        MulChar.map_nonunit θ (fun hu => h ((ZMod.isUnit_iff_coprime n l).mp hu))
      rw [hz c hn,zero_mul]
      have hh : ¬ n.Coprime (q*r) := fun h => hn (h.of_dvd_right (Nat.lcm_dvd_mul q r))
      rcases not_and_or.mp (mt Nat.coprime_mul_iff_right.mpr hh) with h|h
      · rw [hz χ h,zero_mul]
      · rw [hz ψ h,map_zero,mul_zero]
  · intro h
    have he := mul_inv_eq_one.mp h
    have he' := congrArg (fun θ : DirichletCharacter ℂ d => θ.conductor) he
    simp only [c,e,conductor_changeLevel] at he'
    have heq : q=r := hp.symm.trans (he'.trans hp')
    subst r
    have hχψ := DirichletCharacter.changeLevel_injective (Nat.dvd_lcm_left q q) he
    subst ψ;rfl

/-- Common divisibility of the conductors divides the correlation parameter
Q² by that common divisor. -/
theorem primitive_multiple_correlation_family (Q : ℕ) {b : ℕ} (hb : 1≤b) :
    CharacterCorrelationFamily (primitiveConductorMultiples Q b) (fun p n => p.2 n) (Q^2/b) := by
  apply primitive_lcm_correlation_family (filter_subset ..)
  intro i hi j hj
  obtain ⟨hi,hbi⟩ := mem_filter.mp hi
  obtain ⟨hj,hbj⟩ := mem_filter.mp hj
  have hqi := mem_Icc.mp (mem_sigma.mp hi).1
  have hqj := mem_Icc.mp (mem_sigma.mp hj).1
  have hg := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left j.1 hqi.1) (Nat.dvd_gcd hbi hbj)
  apply (Nat.le_div_iff_mul_le hb).mpr
  calc i.1.lcm j.1*b ≤ i.1.lcm j.1*(i.1.gcd j.1) := Nat.mul_le_mul_left _ hg
       _ = i.1*j.1 := (Nat.mul_comm ..).trans (Nat.gcd_mul_lcm ..)
       _ ≤ Q*Q := Nat.mul_le_mul hqi.2 hqj.2
       _ = Q^2 := (sq Q).symm

end AnalyticNumberTheory.SieveMethods
