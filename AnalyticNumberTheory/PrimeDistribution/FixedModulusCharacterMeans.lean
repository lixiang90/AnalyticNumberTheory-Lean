import AnalyticNumberTheory.PrimeDistribution.FixedModulusHeightWeights
import AnalyticNumberTheory.PrimeDistribution.CharacterTruncatedExplicitFormula

/-! # Fixed-modulus mean estimate for twisted Chebyshev sums -/

noncomputable section

open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- At one modulus, sum the maximal twisted Chebyshev sums over the full
character group. Each character may attain its maximum at a different endpoint
in `[0,x]`. The proof uses the truncated explicit formula and Ingham density. -/
theorem fixed_modulus_maximal_psi_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {x : ℝ}, 4 ≤ x → (q : ℝ) ≤ x →
      (∑ χ : DirichletCharacter ℂ q, maximalPsiCharNorm x χ) ≤
        C * (Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x) *
          (1 + Real.log x) ^ 10 := by
  obtain ⟨D, hD, hExplicit⟩ := nonprincipal_psi_truncated_explicit_bound
  obtain ⟨K, hK, density⟩ := fixed_modulus_zero_weight_sqrt
  let B := Real.log 4 + 4
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B + D * (4 + K), by positivity, ?_⟩
  intro q _ x hx hqx
  let w := fun z : ℂ => x ^ z.re / (1 + |z.im|)
  let Z := fun χ : DirichletCharacter ℂ q => characterZeroWeight χ (Real.sqrt x) w
  let U := Real.sqrt x * (1 + Real.log ((q : ℝ) * x)) ^ 2
  let M := Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x
  let L := 1 + Real.log x
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hx₁]
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hz (χ) : 0 ≤ Z χ := sum_nonneg fun z _ =>
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Real.rpow_nonneg hx₀.le _) (by positivity))
  have hχ (χ : DirichletCharacter ℂ q) :
      maximalPsiCharNorm x χ ≤ (if χ = 1 then B * x else 0) + D * (U + Z χ) := by
    apply csSup_le
    · exact ⟨_, 0, ⟨le_rfl, hx₀.le⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    by_cases h : χ = 1
    · rw [ite_eq_left h]
      exact ((norm_psiChar_le_const_mul_self hy.1 χ).trans
        (mul_le_mul_of_nonneg_left hy.2 hB.le)).trans
          (le_add_of_nonneg_right (mul_nonneg hD.le (add_nonneg hU (hz χ))))
    · simpa only [ite_eq_right h, zero_add] using hExplicit h hx hy.1 hy.2
  have hsum : (∑ χ : DirichletCharacter ℂ q, maximalPsiCharNorm x χ) ≤
      B * x + D * ((q.totient : ℝ) * U + modulusZeroWeight q (Real.sqrt x) w) := by
    apply (sum_le_sum (fun χ _ => hχ χ)).trans_eq
    rw [sum_add_distrib, ← mul_sum, sum_add_distrib, modulusZeroWeight_eq_sum_characters]
    simp [Z, card_dirichletCharacter_eq_totient]
  have hqxlog := Real.log_le_log hq₀ hqx
  have hl : 1 + Real.log ((q : ℝ) * x) ≤ 2 * L := by
    rw [Real.log_mul hq₀.ne' hx₀.ne']
    dsimp only [L]
    linarith
  have hl₀ := add_nonneg zero_le_one (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq hx₁))
  have hsq : (1 + Real.log ((q : ℝ) * x)) ^ 2 ≤ 4 * L ^ 10 := by
    calc
      _ ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hl₀ hl 2
      _ = 4 * L ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 2 ≤ 10)) (by norm_num)
  have hmiddle := mul_nonneg (Real.rpow_nonneg hx₀.le (4/5)) (Real.rpow_nonneg hq₀.le (3/5))
  have hfirst := mul_nonneg (Real.sqrt_nonneg x) hq₀.le
  have hfirstM : Real.sqrt x * q ≤ M := by dsimp only [M]; linarith
  have hxM : x ≤ M := by dsimp only [M]; linarith
  have hmain : (q.totient : ℝ) * U ≤ 4 * (M * L ^ 10) := by
    calc
      _ ≤ (q : ℝ) * U := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) hU
      _ ≤ (q : ℝ) * (Real.sqrt x * (4 * L ^ 10)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg x)) hq₀.le
      _ = 4 * ((Real.sqrt x * q) * L ^ 10) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfirstM (by positivity)) (by norm_num)
  have hxML := hxM.trans (le_mul_of_one_le_right (hx₀.le.trans hxM) (one_le_pow₀ hL (n := 10)))
  have hzero : modulusZeroWeight q (Real.sqrt x) w ≤ K * (M * L ^ 10) := by
    simpa only [mul_assoc] using density hx hqx
  apply hsum.trans ((add_le_add (mul_le_mul_of_nonneg_left hxML hB.le)
    (mul_le_mul_of_nonneg_left (add_le_add hmain hzero) hD.le)).trans_eq ?_)
  dsimp only [M, L]
  ring

end AnalyticNumberTheory.PrimeDistribution
