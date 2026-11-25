import AnalyticNumberTheory.PrimeDistribution.CharacterInghamSymmetric
import AnalyticNumberTheory.PrimeDistribution.PrincipalCharacterDensity
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthMoment

/-! # Ingham's zero-density estimate for the full character group of one modulus -/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- The nonprincipal zeros of a fixed modulus at the natural integral cutoff
q times the rounded height. This form retains seven logarithmic factors. -/
theorem fixed_nonprincipal_ingham_at_cutoff :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
    let X := q*(⌊T⌋₊+16)
    (∑ χ : DirichletCharacter ℂ q,∑ z∈nonprincipalDensityFinset χ σ T,(characterZeroMultiplicity χ z:ℝ))
      ≤ C*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨B,hB,HB⟩ := full_character_critical_fourth_moments
  obtain ⟨D,hD,H⟩ := character_ingham_symmetric_weighted hB
  refine ⟨D,hD,?_⟩
  intro q _ σ T hσ hT
  let L := ⌊T⌋₊+16
  let X := q*L
  have hq := NeZero.pos q
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
  have hL : 16≤L := by dsimp [L];omega
  have hX : 16≤X := hL.trans (Nat.le_mul_of_pos_left L hq)
  have hTL : T<(L:ℝ) := by dsimp [L];push_cast;linarith [Nat.lt_floor_add_one T]
  have hXL : (X:ℝ)=(q:ℝ)*L := by dsimp [X];push_cast;rfl
  have hh := H (univ : Finset (DirichletCharacter ℂ q)) (fun _ => q) id star (X:=X) (L:=L)
    (T:=T) (σ:=σ) (fun χ => star_star χ) (fun _ _ => mem_univ _)
    (fun χ _ => nonprincipal_star_conjugate χ) hX (by omega) hTL hσ (by
      rw [card_univ,card_dirichletCharacter_eq_totient]
      exact Nat.mul_le_mul_right _ (Nat.totient_le _)) (fun _ _ => le_rfl) (by
      intro m _
      have he : (q:ℝ)*((m*L:ℕ):ℝ)=(m:ℝ)*X := by rw [hXL];push_cast;ring
      simpa only [he, id_eq] using fixed_modulus_family_hybrid_mean q (m*L)) (by
      intro j
      let U := (2:ℝ)^j*L
      have hU : 1≤U := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
        (by exact_mod_cast (by omega : 1≤L))
      have he : (q:ℝ)*U=2^j*X := by rw [hXL];dsimp [U];ring
      have h := (HB (q:=q) hU).2
      rw [mul_assoc B,he] at h
      exact h)
  exact hh

private theorem fixed_nonprincipal_ingham :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
    (∑ χ : DirichletCharacter ℂ q,∑ z∈nonprincipalDensityFinset χ σ T,(characterZeroMultiplicity χ z:ℝ))
      ≤ C*((q:ℝ)*T)^(inghamExponent σ)*(Real.log ((q:ℝ)*T))^9 := by
  obtain ⟨D,hD,H⟩ := fixed_nonprincipal_ingham_at_cutoff
  refine ⟨D*(9*20^9),by positivity,?_⟩
  intro q _ σ T hσ hT
  let L := ⌊T⌋₊+16
  let X := q*L
  have hq := NeZero.pos q
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
  have hL : 16≤L := by dsimp [L];omega
  have hX : 16≤X := hL.trans (Nat.le_mul_of_pos_left L hq)
  have hXL : (X:ℝ)=(q:ℝ)*L := by dsimp [X];push_cast;rfl
  have hh := H (q:=q) hσ hT
  have hLX : (L:ℝ)≤9*T := by dsimp [L];push_cast;linarith [Nat.floor_le (by linarith : 0≤T)]
  have hQT : 2≤(q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) hq₁)
  have hX' : (1:ℝ)≤X := by exact_mod_cast (by omega : 1≤X)
  have h9 : (X:ℝ)≤9*(q*T) := by rw [hXL];nlinarith only [mul_le_mul_of_nonneg_left hLX (Nat.cast_nonneg (α:=ℝ) q)]
  have hscale := ingham_scale_bound (Y:=(q:ℝ)*T) hX' (by linarith : 0≤(q:ℝ)*T) hQT h9
    (by nlinarith [sq_nonneg ((q:ℝ)*T-1)]) hσ
  have h := hh.trans ((show D*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ) =
    D*((1+Real.log X)^7*(X:ℝ)^(inghamExponent σ)) by ring).le.trans (mul_le_mul_of_nonneg_left hscale hD.le))
  exact h.trans_eq (by ring)

/-- Ingham's exponent for all Dirichlet characters modulo q, counting both signs
of height and every analytic multiplicity, including the principal character. -/
theorem modulusDensityCount_ingham :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (modulusDensityCount q σ T:ℝ) ≤ C*((q:ℝ)*T)^(inghamExponent σ)*(Real.log ((q:ℝ)*T))^9 := by
  obtain ⟨C,hC,HC⟩ := fixed_nonprincipal_ingham
  obtain ⟨D,hD,HD⟩ := principal_character_ingham_density_log_nine
  refine ⟨C+D,by positivity,?_⟩
  intro q _ σ T hσ hT
  let N := characterDensityCount (1:DirichletCharacter ℂ q) σ T
  let M := ∑ χ : DirichletCharacter ℂ q,∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z
  have he : modulusDensityCount q σ T=N+M := by
    unfold modulusDensityCount
    calc _ = ∑ χ : DirichletCharacter ℂ q, ((if χ=1 then N else 0)+
             ∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z) :=
               sum_congr rfl (fun χ _ => characterDensityCount_split_principal χ σ T)
         _ = _ := by rw [sum_add_distrib];simp [M]
  have he' : (modulusDensityCount q σ T:ℝ)=(N:ℝ)+(M:ℝ) := by exact_mod_cast he
  have hP := HD (q:=q) hσ hT
  have hN := HC (q:=q) hσ hT
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have ht : T≤(q:ℝ)*T := le_mul_of_one_le_left (by linarith) hq₁
  have hl := Real.log_le_log (by linarith : 0<T) ht
  have he₀ : 0 ≤ inghamExponent σ := by unfold inghamExponent;apply div_nonneg <;> linarith [hσ.2]
  have hh := hP.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ht he₀) hD.le)
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hl 9) (by positivity [Real.log_nonneg (by linarith : 1≤T)])
    (by positivity : 0≤D*((q:ℝ)*T)^(inghamExponent σ)))
  change (N:ℝ)≤_ at hh
  simp only [M,Nat.cast_sum] at he'
  linarith only [he',hh,hN]

end AnalyticNumberTheory.PrimeDistribution
