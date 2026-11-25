import AnalyticNumberTheory.PrimeDistribution.FixedModulusCharacterMeans
import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterExpansion

/-! # Rational prime exponential sums from fixed-modulus zero density -/

noncomputable section

open Complex Finset Real
open scoped Classical ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

/-- Reversing the frequency conjugates the prime exponential sum. -/
theorem star_primeExpSum (x α : ℝ) : star (primeExpSum x α) = primeExpSum x (-α) := by
  unfold primeExpSum
  rw [star_expSum]
  simp only [Complex.star_def, Complex.conj_ofReal, expSum]

private lemma norm_primeExpSum_abs (x α : ℝ) : ‖primeExpSum x |α|‖ = ‖primeExpSum x α‖ := by
  rcases le_or_gt 0 α with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, ← star_primeExpSum, norm_star]

/-- Transfer a maximum over characters to any reduced rational frequency.
The discarded prime powers have the explicit logarithmic error from the
character expansion. -/
theorem norm_primeExpSum_le_character_mean {q : ℕ} [NeZero q] {a : ℕ}
    (ha : a.Coprime q) {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    ‖primeExpSum y ((a : ℝ) / q)‖ ≤ Real.log q / Real.log 2 * Real.log y +
      (Real.sqrt q / q.totient) * ∑ χ : DirichletCharacter ℂ q, maximalPsiCharNorm x χ := by
  let S := ∑ χ : DirichletCharacter ℂ q, rationalCharacterCoefficient χ a * psiChar y χ
  have hsum : ‖S‖ ≤ (Real.sqrt q / q.totient) * ∑ χ : DirichletCharacter ℂ q, maximalPsiCharNorm x χ := by
    rw [mul_sum]
    apply (norm_sum_le ..).trans (sum_le_sum ?_)
    intro χ _
    rw [norm_mul]
    have hdq : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    have hcoef := (norm_rationalCharacterCoefficient_le_conductor χ ha).trans
      (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hdq) (Nat.cast_nonneg _))
    exact mul_le_mul hcoef (norm_psiChar_le_maximalPsiCharNorm χ (zero_le_one.trans hy) hyx)
      (norm_nonneg _) (by positivity)
  exact (norm_le_norm_sub_add _ S).trans (add_le_add (norm_primeExpSum_sub_character_expansion hy a) hsum)

/-- The zero-density estimate for the linear von Mangoldt sum at a reduced
rational frequency. The cutoff can vary up to `x` and the numerator may be any
integer. The middle term is `x^(4/5) q^(1/10)`. -/
theorem primeExpSum_rational_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x y : ℝ},
      a.natAbs.Coprime q → 4 ≤ x → (q : ℝ) ≤ x → 0 ≤ y → y ≤ x →
      ‖primeExpSum y ((a : ℝ) / q)‖ ≤
        C * (x / Real.sqrt q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (1/10 : ℝ) + Real.sqrt (x*q)) *
          (1 + Real.log x) ^ 11 := by
  obtain ⟨C, hC, mean⟩ := fixed_modulus_maximal_psi_mean
  let D := 1 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D + 6 * C, by positivity, ?_⟩
  intro q _ a x y ha hx hqx hy hyx
  let L := 1 + Real.log x
  let V := x / Real.sqrt q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (1/10 : ℝ) + Real.sqrt (x*q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hs := Real.sqrt_pos.mpr hq₀
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hx₁]
  have hV : 1 ≤ V := by
    have hh := Real.one_le_sqrt.mpr (one_le_mul_of_one_le_of_one_le hx₁ hq)
    dsimp only [V]
    linarith only [hh, div_nonneg hx₀.le hs.le,
      mul_nonneg (Real.rpow_nonneg hx₀.le (4/5)) (Real.rpow_nonneg hq₀.le (1/10))]
  change ‖primeExpSum y ((a : ℝ) / q)‖ ≤ (D + 6 * C) * V * L ^ 11
  by_cases hy₁ : 1 ≤ y
  swap
  · have hf : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hy₁)
    simp only [primeExpSum, expSum, hf, Icc_eq_empty_of_lt (by decide : 0 < 1), sum_empty, norm_zero]
    positivity
  have habs : (a.natAbs : ℝ) / q = |(a : ℝ) / q| := by
    rw [abs_div, abs_of_nonneg hq₀.le]
    apply congrArg (fun t : ℝ => t / q)
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun n : ℤ => (n : ℝ)) (Int.natCast_natAbs a)
  have hr := norm_primeExpSum_le_character_mean ha hy₁ hyx
  rw [habs, norm_primeExpSum_abs] at hr
  have hlogq := Real.log_le_log hq₀ hqx
  have hlogy := Real.log_le_log (zero_lt_one.trans_le hy₁) hyx
  have herr : Real.log q / Real.log 2 * Real.log y ≤ D * (V * L ^ 11) := by
    have hprod := mul_le_mul (show Real.log q ≤ L by dsimp [L]; linarith)
      (show Real.log y ≤ L by dsimp [L]; linarith) (Real.log_nonneg hy₁) (zero_le_one.trans hL)
    have hp : L ^ 2 ≤ L ^ 11 := pow_le_pow_right₀ hL (by decide)
    have he := (show Real.log q * Real.log y ≤ L ^ 2 by simpa only [sq] using hprod).trans
      (hp.trans (le_mul_of_one_le_left (by positivity) hV))
    calc
      _ = D * (Real.log q * Real.log y) := by dsimp [D]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he hD.le
  have hpow : (q : ℝ) ^ (3/5 : ℝ) = Real.sqrt q * (q : ℝ) ^ (1/10 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq₀]
    norm_num
  have hscale : Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x = Real.sqrt q * V := by
    dsimp only [V]
    rw [hpow, Real.sqrt_mul hx₀.le, mul_add, mul_add, mul_div_cancel₀ _ hs.ne']
    nlinarith only [congrArg (fun z : ℝ => Real.sqrt x * z) (Real.sq_sqrt hq₀.le)]
  have hratio := (div_totient_le_six_mul_log (NeZero.pos q)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hlogq 1) (by norm_num))
  have hz := mean hx hqx
  rw [hscale] at hz
  have hmean : Real.sqrt q / q.totient * (∑ χ : DirichletCharacter ℂ q, maximalPsiCharNorm x χ) ≤
      (6*C) * (V * L ^ 11) := by
    apply (mul_le_mul_of_nonneg_left hz (div_nonneg hs.le hφ.le)).trans
    calc
      _ = ((q : ℝ) / q.totient) * (C * V * L ^ 10) := by
        dsimp only [L]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith only [congrArg (fun z : ℝ => (q.totient : ℝ)⁻¹ * C * V * (1+Real.log x)^10 * z)
          (Real.sq_sqrt hq₀.le)]
      _ ≤ (6 * L) * (C * V * L ^ 10) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  exact hr.trans ((add_le_add herr hmean).trans_eq (by ring))

end AnalyticNumberTheory.ExponentialSums
