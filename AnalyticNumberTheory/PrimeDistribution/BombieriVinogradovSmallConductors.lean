import AnalyticNumberTheory.PrimeDistribution.SiegelWalfisz

/-!
# Small conductors in the Bombieri–Vinogradov mean

The reciprocal totient in the primitive-character mean cancels the size of
the character group. For a polylogarithmic range of conductors, the remaining
sum is controlled by the uniform Siegel–Walfisz character estimate.
-/

noncomputable section

open Finset
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

/-- An exponential saving in the square root of a logarithm absorbs an
arbitrary fixed real power of the logarithm. -/
theorem log_rpow_mul_exp_neg_sqrt_log_le (A : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ K > 0, ∀ {x : ℝ}, 1 ≤ Real.log x →
      Real.log x ^ A * Real.exp (-γ * Real.sqrt (Real.log x)) ≤ K := by
  let m := ⌈2 * A⌉₊
  refine ⟨(m.factorial : ℝ) / γ ^ m, by positivity, fun {x} hx => ?_⟩
  let y := Real.sqrt (Real.log x)
  have hy : 1 ≤ y := Real.one_le_sqrt.mpr hx
  have hs : y ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hpow : Real.log x ^ A ≤ y ^ m := by
    rw [← hs, ← Real.rpow_two, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hy (Nat.le_ceil _)
  have hf := Real.pow_div_factorial_le_exp (γ * y) (mul_nonneg hγ.le (by linarith : 0 ≤ y)) m
  rw [mul_pow, div_le_iff₀ (by positivity)] at hf
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _),
    div_mul_eq_mul_div, le_div_iff₀ (pow_pos hγ m)]
  exact (mul_le_mul_of_nonneg_right hpow (pow_nonneg hγ.le _)).trans (by linarith only [hf])

/-- Small-conductor part of the primitive-character mean, including the
factor `1/φ(d)` required by the Bombieri–Vinogradov reduction. -/
theorem sum_smallConductor_psiChar_le (A : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Real.log x →
      ∑ d ∈ Icc 2 ⌊min Q (Real.log x ^ L)⌋₊, (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
          (fun χ => χ.IsPrimitive), ‖psiChar x χ‖ ≤ C * x / Real.log x ^ A := by
  obtain ⟨C, hC, γ, hγ, hχ⟩ := norm_psiChar_siegelWalfisz L hL
  obtain ⟨K, hK, hsave⟩ := log_rpow_mul_exp_neg_sqrt_log_le (L + A) hγ
  refine ⟨C * K, by positivity, fun {x Q} hx hlog => ?_⟩
  let R := Real.log x ^ L
  let S := Icc 2 ⌊min Q R⌋₊
  let E := C * x * Real.exp (-γ * Real.sqrt (Real.log x))
  have hR : 0 ≤ R := Real.rpow_nonneg (by linarith) _
  have hfloor : ⌊min Q R⌋₊ ≤ ⌊R⌋₊ := Nat.floor_mono (min_le_right ..)
  have he (d : ℕ) (hd : d ∈ S) : (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive),
          ‖psiChar x χ‖ ≤ E := by
    have hd' := mem_Icc.mp hd
    have : NeZero d := ⟨by omega⟩
    have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr (hd'.2.trans hfloor)).trans (Nat.floor_le hR)
    let F := (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive)
    have hsum : ∑ χ ∈ F, ‖psiChar x χ‖ ≤ ∑ _χ ∈ F, E := by
      apply sum_le_sum
      intro χ hmem
      have hprim := (mem_filter.mp hmem).2
      have hne : χ ≠ 1 := by
        intro h1
        have hc : χ.conductor = d := hprim
        rw [h1, DirichletCharacter.conductor_one] at hc
        omega
      exact hχ x d χ hx (by omega) hdR hne
    have hcard : F.card ≤ d.totient := by
      have hh := card_le_univ F
      rwa [Fintype.card_eq_nat_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity] at hh
    have htot : 0 < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    change (d.totient : ℝ)⁻¹ * (∑ χ ∈ F, ‖psiChar x χ‖) ≤ E
    rw [inv_mul_le_iff₀ htot]
    refine hsum.trans ?_
    simp only [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by dsimp [E]; positivity)
  have hlen : (S.card : ℝ) ≤ R := by
    have hh : S.card ≤ ⌊min Q R⌋₊ := by simp [S, Nat.card_Icc]
    exact (Nat.cast_le.mpr (hh.trans hfloor)).trans (Nat.floor_le hR)
  have hmajor := hsave hlog
  have hlog0 : 0 < Real.log x := by linarith
  rw [Real.rpow_add hlog0] at hmajor
  calc _ ≤ ∑ _d ∈ S, E := sum_le_sum he
       _ ≤ R * E := by
         simp only [sum_const, nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right hlen (by dsimp [E]; positivity)
       _ ≤ _ := by
         rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog0 _)]
         dsimp [R, E]
         calc _ = (C * x) * ((Real.log x ^ L * Real.log x ^ A) *
                  Real.exp (-γ * Real.sqrt (Real.log x))) := by ring
              _ ≤ (C * x) * K := mul_le_mul_of_nonneg_left hmajor (by positivity)
              _ = _ := by ring

end AnalyticNumberTheory.PrimeDistribution
