import AnalyticNumberTheory.PrimeDistribution.CharacterMontgomerySymmetric
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityInputs
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityScale
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthMoment

/-! # Montgomery's density estimate for nonprincipal characters of a fixed modulus -/
noncomputable section
open Finset Real Complex MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- The nonprincipal contribution for a fixed modulus above real part four fifths. -/
theorem fixed_nonprincipal_montgomery :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (4/5:ℝ) 1 → 2≤T →
    (∑ χ : DirichletCharacter ℂ q,∑ z∈nonprincipalDensityFinset χ σ T,(characterZeroMultiplicity χ z:ℝ))
      ≤ C*((q:ℝ)*T)^(montgomeryExponent σ)*(Real.log ((q:ℝ)*T))^12 := by
  obtain ⟨B,hB,HB⟩ := full_character_critical_fourth_moments
  obtain ⟨C,hC,HC,_⟩ := sparse_character_family_mean
  obtain ⟨D,hD,HD⟩ := character_montgomery_symmetric_weighted hB hC
  refine ⟨D*(100*24^12),by positivity,?_⟩
  intro q _ σ T hσ hT
  let L := ⌊T⌋₊+16
  let X := q*(L+2)
  have hq := NeZero.pos q
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
  have hL : 16≤L := by dsimp [L];omega
  have hqL : q*L≤X := Nat.mul_le_mul_left _ (by omega)
  have hX : 16≤X := (hL.trans (Nat.le_mul_of_pos_left L hq)).trans hqL
  have hTL : T<(L:ℝ) := by dsimp [L];push_cast;linarith [Nat.lt_floor_add_one T]
  have hXL : (X:ℝ)=(q:ℝ)*((L:ℝ)+2) := by dsimp [X];push_cast;rfl
  have hqL' : (q:ℝ)*L≤X := by exact_mod_cast hqL
  have hh := HD (univ : Finset (DirichletCharacter ℂ q)) (fun _ => q) id star (X:=X) (L:=L)
    (T:=T) (σ:=σ) (fun χ => star_star χ) (fun _ _ => mem_univ _)
    (fun χ _ => nonprincipal_star_conjugate χ) hX (by omega) hTL hσ (by
      rw [card_univ,card_dirichletCharacter_eq_totient]
      exact (Nat.mul_le_mul_right _ (Nat.totient_le _)).trans hqL) (fun _ _ => hqL)
    (by simpa only [hXL,id_eq] using HC q L) (by
      intro j
      let U := (2:ℝ)^j*L
      have hU : 1≤U := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
        (by exact_mod_cast (by omega : 1≤L))
      have hqU : 1≤(q:ℝ)*U := one_le_mul_of_one_le_of_one_le hq₁ hU
      have he : (q:ℝ)*U≤2^j*X := by
        dsimp only [U];calc _ = 2^j*((q:ℝ)*L) := by ring
                            _ ≤ _ := mul_le_mul_of_nonneg_left hqL' (by positivity)
      have h := (HB (q:=q) hU).2
      rw [mul_assoc B] at h
      exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left he hB.le)
        (pow_le_pow_left₀ (by linarith [Real.log_nonneg hqU]) (by linarith only [Real.log_le_log (zero_lt_one.trans_le hqU) he]) 4)
        (by positivity) (by positivity)))
  have hLX : (L:ℝ)+2≤10*T := by dsimp [L];push_cast;linarith [Nat.floor_le (by linarith : 0≤T)]
  have hQT : 2≤(q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) hq₁)
  have hX' : (1:ℝ)≤X := by exact_mod_cast (by omega : 1≤X)
  have h10 : (X:ℝ)≤10*(q*T) := by rw [hXL];linarith only [mul_le_mul_of_nonneg_left hLX (Nat.cast_nonneg (α:=ℝ) q)]
  have hscale := montgomery_scale_log_twelve (Y:=(q:ℝ)*T) hX' (by linarith : 0≤(q:ℝ)*T) hQT h10
    (by nlinarith [sq_nonneg ((q:ℝ)*T-1)]) ⟨by linarith [hσ.1],hσ.2⟩
  exact hh.trans ((show D*(1+Real.log X)^12*(X:ℝ)^(montgomeryExponent σ) =
    D*((1+Real.log X)^12*(X:ℝ)^(montgomeryExponent σ)) by ring).le.trans
    ((mul_le_mul_of_nonneg_left hscale hD.le).trans_eq (by ring)))

end AnalyticNumberTheory.PrimeDistribution
