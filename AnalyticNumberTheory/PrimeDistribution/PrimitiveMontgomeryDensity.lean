import AnalyticNumberTheory.PrimeDistribution.PrimitiveMontgomeryNonprincipal
import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaDensity

/-!
# Montgomery's density exponent for the full primitive family

Both signs of the ordinate and analytic multiplicity are included. The
conductor-one character is accounted for by the separate Riemann zeta estimate.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Montgomery's density theorem for all primitive characters of conductor
at most Q. Its exponent is 2(1−σ)/σ, with twelve logarithms. -/
theorem primitive_conductors_montgomery_log_twelve :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^12 := by
  apply primitive_conductors_montgomery_join 12 (by decide) primitiveFamilyZeroCount_montgomery_log_twelve
  obtain ⟨C,hC,H⟩ := principal_character_montgomery_log_twelve
  refine ⟨C,hC,?_⟩
  intro σ T hσ hT
  exact H (q:=1) hT hσ

/-- Montgomery's density theorem for all primitive characters of conductor
at most Q. Its exponent is 2(1−σ)/σ, with thirteen logarithms. -/
theorem primitive_conductors_montgomery_density :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^13 := by
  obtain ⟨D,hD,H⟩ := primitive_conductors_montgomery_log_twelve
  refine ⟨2*D,by positivity,?_⟩;intro Q σ T hQ hσ hT
  have hy := hT.trans (le_mul_of_one_le_left (show 0≤T by linarith) (by exact_mod_cast hQ : (1:ℝ)≤Q))
  apply (H hQ hσ hT).trans
  exact (mul_le_mul_of_nonneg_left (log_pow_le_twice_log_succ 12 hy)
    (show 0≤D*((Q:ℝ)^2*T)^(montgomeryExponent σ) by positivity)).trans_eq (by ring)

/-- Montgomery's bound includes all ordinates at height zero and in bounded
windows after replacing T by T+2. -/
theorem primitive_conductors_montgomery_all_heights_log_twelve :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 0≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*(T+2))^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*(T+2)))^12 := by
  obtain ⟨C,hC,H⟩ := primitive_conductors_montgomery_log_twelve
  refine ⟨C,hC,?_⟩;intro Q σ T hQ hσ hT
  apply le_trans _ (H hQ hσ (show 2≤T+2 by linarith))
  apply sum_le_sum
  intro q hq
  exact_mod_cast sum_le_sum (s:=univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
    (fun (χ : DirichletCharacter ℂ q) _ => characterDensityCount_mono_height χ σ (show T≤T+2 by linarith))

/-- Montgomery's bound includes all ordinates at height zero and in bounded
windows after replacing T by T+2. -/
theorem primitive_conductors_montgomery_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 0≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*(T+2))^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*(T+2)))^13 := by
  obtain ⟨D,hD,H⟩ := primitive_conductors_montgomery_all_heights_log_twelve
  refine ⟨2*D,by positivity,?_⟩;intro Q σ T hQ hσ hT
  have hy : 2≤(Q:ℝ)*(T+2) := (show 2≤T+2 by linarith).trans
    (le_mul_of_one_le_left (by linarith) (by exact_mod_cast hQ : (1:ℝ)≤Q))
  apply (H hQ hσ hT).trans
  exact (mul_le_mul_of_nonneg_left (log_pow_le_twice_log_succ 12 hy)
    (show 0≤D*((Q:ℝ)^2*(T+2))^(montgomeryExponent σ) by positivity)).trans_eq (by ring)

/-- Taking the better of the Ingham and Montgomery bounds retains the
respective logarithmic powers on either side of their crossover. -/
theorem primitive_conductors_density_min :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ)) ≤ C*min
        (((Q:ℝ)^2*T)^(inghamExponent σ)*(Real.log ((Q:ℝ)*T))^8)
        (((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^12) := by
  obtain ⟨B,hB,HI⟩ := primitive_conductors_ingham_log_eight
  obtain ⟨D,hD,HM⟩ := primitive_conductors_montgomery_log_twelve
  refine ⟨max B D,hB.trans_le (le_max_left _ _),?_⟩;intro Q σ T hQ hσ hT
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hY : 1≤(Q:ℝ)*T := one_le_mul_of_one_le_of_one_le hr (by linarith)
  rw [mul_min_of_nonneg _ _ (hB.le.trans (le_max_left _ _))]
  apply le_min
  · apply (HI hQ hσ hT).trans
    rw [mul_assoc B]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · apply (HM hQ hσ hT).trans
    rw [mul_assoc D]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity [Real.log_nonneg hY])

/-- Uniform linear density exponent for all primitive characters up to Q.
The coefficient five halves is attained by both exponents at σ = 4/5. -/
theorem primitive_conductors_density_five_halves :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^((5/2:ℝ)*(1-σ))*(Real.log ((Q:ℝ)*T))^12 := by
  obtain ⟨D,hD,HD⟩ := primitive_conductors_density_min
  refine ⟨16*D,by positivity,?_⟩
  intro Q σ T hQ hσ hT
  let H := (Q:ℝ)^2*T
  let Y := (Q:ℝ)*T
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) (by linarith)
  have hY : 2≤Y := hT.trans (le_mul_of_one_le_left (by linarith) hr)
  have hy : 0≤Real.log Y := Real.log_nonneg (by linarith)
  have h₀ : 0≤1-σ := sub_nonneg.mpr hσ.2
  apply (HD hQ hσ hT).trans
  change D*min (H^(inghamExponent σ)*(Real.log Y)^8) (H^(montgomeryExponent σ)*(Real.log Y)^12) ≤ _
  by_cases h : σ≤4/5
  · have he : inghamExponent σ≤(5/2:ℝ)*(1-σ) := by
      unfold inghamExponent
      apply (div_le_iff₀ (by linarith [hσ.2])).mpr
      nlinarith only [mul_nonneg h₀ (show 0≤4-5*σ by linarith)]
    apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hD.le).trans
    have hm := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hH he) (log_pow_le_scaled_log_pow (by decide : 8≤12) hY)
      (pow_nonneg hy _) (Real.rpow_nonneg (zero_le_one.trans hH) _)
    exact (mul_le_mul_of_nonneg_left hm hD.le).trans_eq (by dsimp [H,Y];ring)
  · have he : montgomeryExponent σ≤(5/2:ℝ)*(1-σ) := by
      unfold montgomeryExponent
      apply (div_le_iff₀ (by linarith [hσ.1])).mpr
      nlinarith only [mul_nonneg h₀ (show 0≤5*σ-4 by linarith)]
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hD.le).trans
    have hm := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hH he) (pow_nonneg hy 12)
    change _≤16*D*H^((5/2:ℝ)*(1-σ))*(Real.log Y)^12
    nlinarith only [mul_le_mul_of_nonneg_left hm hD.le,mul_nonneg hD.le
      (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hH) ((5/2:ℝ)*(1-σ))) (pow_nonneg hy 12))]

end AnalyticNumberTheory.PrimeDistribution
