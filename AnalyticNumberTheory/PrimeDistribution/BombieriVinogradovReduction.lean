import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovSmallConductors
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik

/-!
# Reduction of Bombieri–Vinogradov to a large-cutoff character mean

The ordinary prime number theorem supplies the principal character contribution.
Elementary estimates handle the bounded range where the logarithm of the
cutoff is smaller than one.
-/

noncomputable section

open Finset
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

private theorem log_rpow_le_on_initial_interval (A : ℝ) {x : ℝ} (hx : 2 ≤ x) (hl : Real.log x ≤ 1) :
    Real.log x ^ A ≤ max 1 (Real.log 2 ^ A) := by
  have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  by_cases hA : 0 ≤ A
  · apply le_trans _ (le_max_left ..)
    simpa using Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hl hA
  · apply le_trans _ (le_max_right ..)
    exact Real.rpow_le_rpow_of_nonpos (Real.log_pos one_lt_two) hl2 (le_of_not_ge hA)

/-- The ordinary prime number theorem saves any fixed real power of `log x`. -/
theorem abs_psi_sub_id_le_log_power (A : ℝ) :
    ∃ C > 0, ∀ {x : ℝ}, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x / Real.log x ^ A := by
  obtain ⟨C, hC, γ, hγ, hpnt⟩ := abs_psi_sub_id_le_exp
  obtain ⟨K, hK, hsave⟩ := log_rpow_mul_exp_neg_sqrt_log_le A hγ
  let M := max K (max 1 (Real.log 2 ^ A))
  have hM : 0 < M := hK.trans_le (le_max_left ..)
  refine ⟨C*M, by positivity, fun {x} hx => ?_⟩
  let z := Real.exp (-γ * Real.sqrt (Real.log x))
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hpow : Real.log x ^ A * z ≤ M := by
    by_cases hlog : 1 ≤ Real.log x
    · exact (hsave hlog).trans (le_max_left ..)
    · have hz1 : z ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))
      exact ((mul_le_of_le_one_right (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _) hz1).trans
        (log_rpow_le_on_initial_interval A hx (le_of_not_ge hlog))).trans (le_max_right ..)
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hl _)]
  calc _ ≤ (C*x*z) * Real.log x ^ A := mul_le_mul_of_nonneg_right (hpnt x hx) (Real.rpow_nonneg hl.le _)
       _ = (C*x) * (Real.log x ^ A * z) := by ring
       _ ≤ (C*x) * M := mul_le_mul_of_nonneg_left hpow (by positivity)
       _ = _ := by ring

private theorem primitive_char_mean_trivial {x Q : ℝ} (hx : 0 ≤ x) (hQ : 0 ≤ Q) :
    ∑ d ∈ Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive),
        ‖psiChar x χ‖ ≤ Q * ((Real.log 4 + 4) * x) := by
  let E := (Real.log 4 + 4) * x
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hd (d : ℕ) (hd : d ∈ Icc 2 ⌊Q⌋₊) :
      (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive),
          ‖psiChar x χ‖ ≤ E := by
    have h2 := (mem_Icc.mp hd).1
    have : NeZero d := ⟨by omega⟩
    rw [inv_mul_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega)))]
    apply le_trans (b := ∑ _χ : DirichletCharacter ℂ d, E)
    · calc _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive), E :=
             sum_le_sum fun χ _ => norm_psiChar_le_const_mul_self hx χ
           _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => hE)
    · simp only [sum_const, card_univ, nsmul_eq_mul]
      rw [Fintype.card_eq_nat_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  calc _ ≤ ∑ _d ∈ Icc 2 ⌊Q⌋₊, E := sum_le_sum hd
       _ ≤ Q * E := by
         simp only [sum_const, nsmul_eq_mul]
         refine mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr ?_).trans (Nat.floor_le hQ)) hE
         simp [Nat.card_Icc]

/-- The primitive character mean at `log x ≥ 1` suffices for the full
Bombieri–Vinogradov estimate. -/
theorem bombieriVinogradov_of_large_x_primitive_mean
    (hprim : ∀ A : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ {x Q : ℝ},
      2 ≤ x → 1 ≤ Real.log x → 1 ≤ Q → Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B →
      ∑ d ∈ Icc 2 ⌊Q⌋₊, (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive),
          ‖psiChar x χ‖ ≤ C * x / Real.log x ^ A) : BombieriVinogradovStatement := by
  apply bombieriVinogradov_of_primitive_char_bound abs_psi_sub_id_le_log_power
  intro A
  obtain ⟨B, hB, C, hC, hmean⟩ := hprim A
  let R := (Real.exp 1) ^ (1 / 2 : ℝ) / Real.log 2 ^ B
  let L := max 1 (Real.log 2 ^ A)
  let K := R * (Real.log 4 + 4) * L
  refine ⟨B, max C K, hC.trans_le (le_max_left ..), fun {x Q} hx hQ hcut => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow := Real.rpow_pos_of_pos hlog A
  by_cases hl : 1 ≤ Real.log x
  · apply (hmean hx hl hQ hcut).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (by linarith)) hpow.le
  have hxe : x ≤ Real.exp 1 := (Real.log_le_iff_le_exp (by linarith)).mp (le_of_not_ge hl)
  have hQR : Q ≤ R := hcut.trans (div_le_div₀ (by positivity)
    (Real.rpow_le_rpow (by linarith) hxe (by norm_num)) (Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _)
    (Real.rpow_le_rpow (Real.log_pos one_lt_two).le (Real.log_le_log (by norm_num) hx) hB))
  have hpL := log_rpow_le_on_initial_interval A hx (le_of_not_ge hl)
  apply (primitive_char_mean_trivial (by linarith : 0 ≤ x) (by linarith : 0 ≤ Q)).trans
  rw [le_div_iff₀ hpow]
  calc _ ≤ R * ((Real.log 4 + 4) * x) * L := by
             exact mul_le_mul (mul_le_mul_of_nonneg_right hQR (by positivity)) hpL hpow.le (by dsimp [R]; positivity)
       _ = K * x := by dsimp [K]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (by linarith)

end AnalyticNumberTheory.PrimeDistribution
