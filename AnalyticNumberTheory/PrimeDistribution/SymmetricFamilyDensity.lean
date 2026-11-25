import AnalyticNumberTheory.PrimeDistribution.DirichletZeroCountDensity
import AnalyticNumberTheory.DirichletLFunctions.FamilyDensityCounts

/-! # Passing from upper-half estimates to symmetric density counts -/
noncomputable section
open Finset Complex Real
open scoped Classical ComplexConjugate
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Conjugate negative ordinates and permute the family. Real ordinates are
assigned to the nonnegative half, so each distinct zero is used once. -/
theorem symmetric_family_count_of_upper {ι : Type*} (F : Finset ι) (c : ι→ι)
    (hinv : Function.Involutive c) (hc : ∀ i∈F,c i∈F) {P : ι→ℂ→Prop}
    (hconj : ∀ i∈F,∀ z,P (c i) z → P i (conj z)) {L B : ℝ}
    (hupper : ∀ S : ι→Finset ℂ, (∀ i∈F,∀ z∈S i,P i z ∧ 0≤z.im ∧ z.im<L) →
      (∑ i∈F,((S i).card:ℝ))≤B) (S : ι→Finset ℂ)
    (hS : ∀ i∈F,∀ z∈S i,P i z ∧ |z.im|<L) :
    (∑ i∈F,((S i).card:ℝ))≤2*B := by
  let U (i : ι) := (S i).filter (fun z => 0≤z.im)
  let N (i : ι) := (S i).filter (fun z => ¬0≤z.im)
  let V (i : ι) := (N (c i)).image (starRingEnd ℂ)
  have hu := hupper U (by
    intro i hi z hz
    obtain ⟨hs,ht⟩ := mem_filter.mp hz
    exact ⟨(hS i hi z hs).1,ht,(abs_lt.mp (hS i hi z hs).2).2⟩)
  have hv := hupper V (by
    intro i hi z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    obtain ⟨hs,ht⟩ := mem_filter.mp hw
    obtain ⟨hp,ha⟩ := hS (c i) (hc i hi) w hs
    exact ⟨hconj i hi w hp,by simp;linarith,by simp;linarith [(abs_lt.mp ha).1]⟩)
  have he (i : ι) : (V i).card=(N (c i)).card := card_image_of_injective _ (starRingEnd ℂ).injective
  simp only [he] at hv
  have hsum : (∑ i∈F,((N (c i)).card:ℝ))=∑ i∈F,((N i).card:ℝ) := by
    refine sum_bij (fun i _ => c i) hc (fun i _ j _ h => hinv.injective h) ?_ (fun _ _ => rfl)
    exact fun i hi => ⟨c i,hc i hi,hinv i⟩
  rw [hsum] at hv
  have hsplit (i : ι) : ((S i).card:ℝ) = (U i).card+(N i).card := by
    exact_mod_cast (card_filter_add_card_filter_not (s:=S i) (fun z => 0≤z.im)).symm
  simp_rw [hsplit];rw [sum_add_distrib];linarith

/-- Separate the principal contribution from the nonprincipal multiplicities. -/
theorem characterDensityCount_split_principal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ T : ℝ) :
    characterDensityCount χ σ T = (if χ=1 then characterDensityCount (1 : DirichletCharacter ℂ q) σ T else 0) +
      ∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z := by
  by_cases he : χ=1
  · subst χ;simp [nonprincipalDensityFinset,NeZero.ne q]
  · simp [he,characterDensityCount,nonprincipalDensityFinset,characterZeroMultiplicity,NeZero.ne q]

/-- The local Jensen bound costs one logarithm when converting a family of
distinct nonprincipal zeros to its total analytic multiplicity. -/
theorem nonprincipal_family_multiplicity_le {ι : Type*} (F : Finset ι) (q : ι→ℕ)
    [∀ i,NeZero (q i)] (χ : (i : ι) → DirichletCharacter ℂ (q i)) {σ T X : ℝ}
    (hX : 0<X) (hq : ∀ i∈F,(q i:ℝ)*(T+3)≤2*X) :
    (∑ i∈F, ∑ z∈nonprincipalDensityFinset (χ i) σ T,(characterZeroMultiplicity (χ i) z:ℝ)) ≤
      (∑ i∈F,((nonprincipalDensityFinset (χ i) σ T).card:ℝ))*
        (jensenUnitZeroDensityConst*(1+Real.log X)) := by
  have hloc (i) (hi : i∈F) (z : ℂ) (hz : z∈nonprincipalDensityFinset (χ i) σ T) :
      (characterZeroMultiplicity (χ i) z:ℝ) ≤ jensenUnitZeroDensityConst*(1+Real.log X) := by
    obtain ⟨hn,he,hr,_,hr',ht⟩ := (mem_nonprincipalDensityFinset _).mp hz
    apply (characterZeroMultiplicity_le_log hn he hr hr').trans
    apply mul_le_mul_of_nonneg_left _ jensenUnitZeroDensityConst_pos.le
    have hq' : 0<(q i:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have h := Real.log_le_log (mul_pos hq' (by positivity : 0 < |z.im|+3)) ((mul_le_mul_of_nonneg_left
      (add_le_add ht (le_refl 3)) hq'.le).trans (hq i hi))
    rw [Real.log_mul (by norm_num) hX.ne'] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  rw [sum_mul]
  exact sum_le_sum fun i hi => (sum_le_sum (hloc i hi)).trans_eq (by simp)

end AnalyticNumberTheory.PrimeDistribution
