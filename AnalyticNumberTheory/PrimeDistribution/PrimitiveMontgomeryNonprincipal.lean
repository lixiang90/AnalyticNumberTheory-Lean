import AnalyticNumberTheory.PrimeDistribution.PrimitiveMontgomeryBounds
import AnalyticNumberTheory.PrimeDistribution.CharacterMontgomerySymmetric
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityScale

/-! # Montgomery's zero-density estimate for nonprincipal primitive characters -/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- Montgomery's count of nonprincipal primitive zeros in the right-hand
range, summed over conductors up to Q with analytic multiplicity. -/
theorem primitiveFamilyZeroCount_montgomery_log_twelve :
    ∃ A : ℝ,0<A ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (4/5:ℝ) 1 → 2≤T →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤
        A*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^12 := by
  obtain ⟨C,hC,HC⟩ := primitive_sparse_mean_attach
  obtain ⟨B,hB,HB⟩ := primitive_fourth_dyadic_at_scale
  obtain ⟨D,hD,HD⟩ := character_montgomery_symmetric_weighted hB hC
  refine ⟨D*(100*24^12),by positivity,?_⟩;intro Q σ T hQ hσ hT
  let L := ⌊T⌋₊+16
  let X := Q^2*(L+2)
  let F := primitiveCharacterFamily Q
  let q (i : F) := i.val.1
  let χ (i : F) := i.val.2
  letI (i : F) : NeZero (q i) := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus i.property).1⟩
  let c (i : F) : F := ⟨primitiveStarIndex i.val,primitiveStarIndex_mem i.property⟩
  have hL : 16≤L := by dsimp [L];omega
  have hQ₂ : 1≤Q^2 := Nat.one_le_pow _ _ hQ
  have hQq : Q≤Q^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right Q hQ
  have hLX : Q^2*L≤X := Nat.mul_le_mul_left _ (Nat.le_add_right L 2)
  have hX : 16≤X := hL.trans ((Nat.le_mul_of_pos_left L hQ₂).trans hLX)
  have hTL : T<(L:ℝ) := by dsimp only [L];push_cast;linarith [Nat.lt_floor_add_one T]
  have hscale : (X:ℝ)=(Q:ℝ)^2*((L:ℝ)+2) := by simp [X]
  have hm : SparseCharacterBound F.attach (fun i n => χ i n) L (X:ℝ) C := by
    rw [hscale];exact HC Q L hQ
  have hfun (i : F) (s : ℂ) : familyLFunction i.val s=(χ i).LFunction s := by
    simp only [familyLFunction,dite_eq_right (Nat.ne_of_gt (primitiveCharacterFamily_modulus i.property).1),χ]
  have hmoment (j : ℕ) : (∑i∈F.attach,∫t in -(2^j*(L:ℝ))..2^j*L,‖(χ i).LFunction ((1/2:ℂ)+t*I)‖^4)≤
      B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4 := by
    simp_rw [←hfun]
    exact HB hQ (by omega) hLX j
  have hz := HD F.attach q χ c (X:=X) (L:=L) (σ:=σ) (T:=T)
    (fun i => Subtype.ext (primitiveStarIndex_involutive _)) (fun i _ => mem_attach _ _)
    (fun i _ => nonprincipal_star_conjugate (χ i)) hX (by omega) hTL hσ
    (by simpa only [card_attach,F] using (Nat.mul_le_mul_right L (card_primitiveFamily_le Q)).trans hLX)
    (fun i _ => (Nat.mul_le_mul_right L ((primitiveCharacterFamily_modulus i.property).2.trans hQq)).trans hLX)
    hm hmoment
  have hh : (primitiveFamilyZeroCount Q σ T:ℝ) ≤ D*(1+Real.log X)^12*(X:ℝ)^(montgomeryExponent σ) := by
    simp only [primitiveFamilyZeroCount,Nat.cast_sum]
    exact (sum_attach F _).symm.le.trans hz
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hQT := hT.trans (le_mul_of_one_le_left (by linarith : 0≤T) hr)
  have hLbound : (L:ℝ)+2≤10*T := by
    dsimp only [L];push_cast;linarith [Nat.floor_le (by linarith : 0≤T)]
  have hs := montgomery_scale_log_twelve (by exact_mod_cast (by omega : 1≤X) : (1:ℝ)≤X)
    (by positivity : 0≤(Q:ℝ)^2*T) hQT
    (by rw [hscale];nlinarith only [mul_le_mul_of_nonneg_left hLbound (sq_nonneg (Q:ℝ))])
    (by nlinarith only [mul_nonneg (sq_nonneg (Q:ℝ)) (show 0≤T^2-T by nlinarith only [hT,sq_nonneg (T-1)])])
    ⟨by linarith [hσ.1],hσ.2⟩
  exact hh.trans ((le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left hs hD.le).trans_eq (by ring)))

/-- Montgomery's count of nonprincipal primitive zeros in the right-hand
range, summed over conductors up to Q with analytic multiplicity. -/
theorem primitiveFamilyZeroCount_montgomery :
    ∃ A : ℝ,0<A ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (4/5:ℝ) 1 → 2≤T →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤
        A*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^13 := by
  obtain ⟨D,hD,H⟩ := primitiveFamilyZeroCount_montgomery_log_twelve
  refine ⟨2*D,by positivity,?_⟩;intro Q σ T hQ hσ hT
  have hy := hT.trans (le_mul_of_one_le_left (show 0≤T by linarith) (by exact_mod_cast hQ : (1:ℝ)≤Q))
  apply (H hQ hσ hT).trans
  exact (mul_le_mul_of_nonneg_left (log_pow_le_twice_log_succ 12 hy)
    (show 0≤D*((Q:ℝ)^2*T)^(montgomeryExponent σ) by positivity)).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
