import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaDetector
import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaInputs
import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaCountTransfer
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDetectorCounts
import AnalyticNumberTheory.PrimeDistribution.PrincipalCharacterDensity
import AnalyticNumberTheory.SieveMethods.SparseCharacterSampling

/-!
# Montgomery density for the zeta and principal-character zeros

Applying the sparse mean with modulus one detects the high zeros; the
explicit contribution from the pole covers the complementary low range.
All the final counts include analytic multiplicities.
-/

open Real Complex Finset Set MeasureTheory Filter
open scoped Classical Topology ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- Montgomery's distinct high-zero estimate at the adaptive mollifier
length determined by the actual sample size. -/
theorem montgomery_zeta_high_count : ∃D : ℝ,0<D ∧ MontgomeryHighZetaCount D := by
  obtain ⟨C,hC,HS,_⟩ := sparse_character_family_mean
  obtain ⟨B,hB,HB⟩ := zeta_density_dyadic_fourth_input
  obtain ⟨A,hA,HA⟩ := montgomery_zeta_zero_detector
  obtain ⟨K,hK,HK⟩ := zeta_density_sample_count_inputs
  obtain ⟨D,hD,HD⟩ := montgomery_count_of_alternatives.{0} hC hB hA hK
  refine ⟨D,hD,?_⟩
  intro L σ hL hσ S hS
  let F : Finset (DirichletCharacter ℂ 1) := Finset.univ
  let H := (L:ℝ)+2
  let Y := montgomeryCutoff H σ
  let X := montgomeryMollifierLength (S.card:ℝ) H
  let f (t : ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖
  have hHH : 16≤H := by dsimp [H];linarith [show (16:ℝ)≤L by exact_mod_cast hL]
  have hH₁ : 1≤H := by linarith
  have hss : σ∈Icc (1/2:ℝ) 1 := ⟨by linarith [hσ.1],hσ.2⟩
  have hY : 16≤Y := hHH.trans (montgomeryCutoff_bounds hH₁ hss).1
  have hfc : F.card=1 := by change Fintype.card (DirichletCharacter ℂ 1)=1;rw [card_dirichletCharacter_eq_totient];decide
  have hch : (fun (χ : DirichletCharacter ℂ 1) (n : ℕ) => χ n)=(fun _ _ => (1:ℂ)) := by
    funext χ n
    rw [show (n:ZMod 1)=1 from Subsingleton.elim ..,map_one]
  have hsparse := HS 1 L
  rw [hch] at hsparse
  have hs0 : SparseCharacterBound F (fun _ _ => (1:ℂ)) L H C := by simpa [F,H] using hsparse
  obtain ⟨hcell,hcard⟩ := HK L S (fun z hz => by
    obtain ⟨h₁,h₂,h₃,h₄,h₅,_⟩ := hS z hz
    exact ⟨h₁,by linarith [hσ.1],h₃,h₄,h₅⟩)
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he,Finset.card_empty,Nat.cast_zero]
    positivity [Real.log_nonneg (by dsimp [H] at hH₁;exact hH₁)]
  have hx' := (montgomeryMollifierLength_bounds (by exact_mod_cast hne.card_pos : (1:ℝ)≤S.card) hH₁).1
  have hX : 1≤X := by
    have hsc : 0<(S.card:ℝ) := by exact_mod_cast hne.card_pos
    have hp : (0:ℝ)<X := (mul_pos hsc (Real.sqrt_pos.mpr (zero_lt_one.trans_le hH₁))).trans_le hx'
    exact_mod_cast hp
  have hcount : (∑_χ∈F,(S.card:ℝ))=(S.card:ℝ) := by simp [hfc]
  have h₄ (j : ℕ) : (∑_χ∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,(f t)^4)≤(B*H*(1+Real.log H)^4)*2^j*((j:ℝ)+1)^4 := by
    rw [sum_const,hfc,one_nsmul];exact HB (by omega : 1≤L) j
  have hlen := HD F (fun _ _ => (1:ℂ)) (fun _ => S) (fun _ => f) hH₁ (by omega : 1≤L) hss hs0
    (fun _ _ => continuous_riemannZeta_half.norm)
    (fun _ _ z hz => ⟨(hS z hz).2.1,(hS z hz).2.2.1.le⟩)
    (fun _ _ z hz => ⟨(hS z hz).2.2.2.1.le,(hS z hz).2.2.2.2.1⟩)
    (fun _ _ j hj => hcell j hj) (hcount.le.trans hcard)
    h₄
  simp only [hcount] at hlen
  apply hlen (inghamRieszCoeff X Y) (norm_inghamRieszCoeff (by linarith : 0<Y) X)
  intro χ _ z hz
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hS z hz
  simpa only [mul_one,criticalMollifierNorm,f] using HA hX hY (by linarith [hσ.1]) h₂ h₃ h₆ h₁

/-- Montgomery's zeta density estimate with multiplicities on the full
positive height interval. The integral detector yields twelve logarithms. -/
theorem montgomery_zeta_density_log_twelve :
    ∃C : ℝ,0<C ∧ ∀{T σ : ℝ},2≤T → σ∈Icc (4/5:ℝ) 1 →
      (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤C*T^(montgomeryExponent σ)*(Real.log T)^12 := by
  obtain ⟨D,hD,H⟩ := montgomery_zeta_high_count
  exact montgomery_zeta_weighted_of_high hD H

/-- Montgomery's conventional thirteenth-log density bound for zeta zeros,
counting all multiplicities. -/
theorem montgomery_zeta_density_with_multiplicity :
    ∃C : ℝ,0<C ∧ ∀{T σ : ℝ},2≤T → σ∈Icc (4/5:ℝ) 1 →
      (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤C*T^(montgomeryExponent σ)*(Real.log T)^13 := by
  obtain ⟨C,hC,H⟩ := montgomery_zeta_density_log_twelve
  refine ⟨2*C,by positivity,?_⟩
  intro T σ hT hσ
  have hl : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have hb := mul_le_mul_of_nonneg_left (by linarith : 1≤2*Real.log T)
    (by positivity : 0≤C*T^(montgomeryExponent σ)*(Real.log T)^12)
  exact (H hT hσ).trans (by linarith only [hb])

/-- The twelfth-logarithmic form for the principal character of every modulus. -/
theorem principal_character_montgomery_log_twelve :
    ∃C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → σ∈Icc (4/5:ℝ) 1 →
      (characterDensityCount (1:DirichletCharacter ℂ q) σ T:ℝ)≤C*T^(montgomeryExponent σ)*(Real.log T)^12 := by
  obtain ⟨C,hC,H⟩ := montgomery_zeta_density_log_twelve
  refine ⟨2*C,by positivity,?_⟩
  intro q _ T σ hT hσ
  rw [characterDensityCount_principal_eq_twice (by linarith [hσ.1])]
  push_cast
  exact (mul_le_mul_of_nonneg_left (H hT hσ) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

/-- The principal character of any modulus has the same symmetric strip
zeros as zeta, including their orders of vanishing. -/
theorem principal_character_montgomery_density :
    ∃C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T σ : ℝ},2≤T → σ∈Icc (4/5:ℝ) 1 →
      (characterDensityCount (1:DirichletCharacter ℂ q) σ T:ℝ)≤C*T^(montgomeryExponent σ)*(Real.log T)^13 := by
  obtain ⟨C,hC,H⟩ := montgomery_zeta_density_with_multiplicity
  refine ⟨2*C,by positivity,?_⟩
  intro q _ T σ hT hσ
  rw [characterDensityCount_principal_eq_twice (by linarith [hσ.1])]
  push_cast
  exact (mul_le_mul_of_nonneg_left (H hT hσ) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

/-- On the entire closed right half-strip the Ingham and Montgomery estimates
hold simultaneously, keeping the logarithmic power of each method. -/
theorem zeta_density_ingham_montgomery_min :
    ∃ C : ℝ,0<C ∧ ∀{T σ : ℝ},2≤T → σ∈Icc (1/2:ℝ) 1 →
      (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤
        C*min (T^(inghamExponent σ)*(Real.log T)^8) (T^(montgomeryExponent σ)*(Real.log T)^12) := by
  obtain ⟨A,hA,HA⟩ := ingham_zeroDensity_with_multiplicity_log_eight
  obtain ⟨B,hB,HB⟩ := montgomery_zeta_density_log_twelve
  let C := 16*A+B
  have hCA : A≤C := by dsimp [C];linarith
  have hCB : B≤C := by dsimp [C];linarith
  have hC : 0<C := hA.trans_le hCA
  refine ⟨C,hC,?_⟩
  intro T σ hT hσ
  have hl : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  rw [mul_min_of_nonneg _ _ hC.le]
  apply le_min
  · apply (HA σ hσ T hT).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCA (by positivity : 0≤T^(inghamExponent σ)*(Real.log T)^8)
  · by_cases hs : 4/5≤σ
    · apply (HB hT ⟨hs,hσ.2⟩).trans
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCB (by positivity : 0≤T^(montgomeryExponent σ)*(Real.log T)^12)
    · have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤T)
          (inghamExponent_le_montgomeryExponent (by linarith [hσ.1]) (le_of_not_ge hs))
      have h₄ := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hl 4
      norm_num at h₄
      have hlog := mul_le_mul_of_nonneg_right (by linarith : 1≤16*(Real.log T)^4) (pow_nonneg (by linarith : 0≤Real.log T) 8)
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hp hA.le) hlog (by positivity) (by positivity)
      apply (HA σ hσ T hT).trans
      calc _ ≤ 16*A*(T^(montgomeryExponent σ)*(Real.log T)^12) := by linarith only [h]
           _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (by positivity)

end AnalyticNumberTheory.PrimeDistribution
