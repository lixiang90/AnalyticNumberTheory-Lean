import AnalyticNumberTheory.PrimeDistribution.LeastPrime
import AnalyticNumberTheory.PrimeDistribution.SiegelWalfisz

/-!
# Subexponential bounds for the least prime in a reduced class

The Siegel–Walfisz theorem controls relative errors uniformly in every
polylogarithmic range. Inverting the relation between modulus and cutoff gives
a bound for the least prime of the form `exp (Cε q^ε)` for every `ε > 0`.
-/

open Filter
open scoped Topology

namespace AnalyticNumberTheory.PrimeDistribution

/-- For every polylogarithmic range of moduli, the relative error in the
first Chebyshev function tends to zero uniformly over reduced residue classes. -/
theorem eventually_thetaAP_relative_error_le {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (q a : ℕ), 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → a.Coprime q →
      |thetaAP x q a - x / q.totient| ≤ ε * x / q.totient := by
  obtain ⟨C, hC, c, hc, herr⟩ := siegelWalfisz_thetaAP siegelWalfisz A hA
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*A) c hc).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop (2 : ℝ), ht.eventually_lt_const (div_pos hε hC)] with x hx hsmall
  intro q a hq hqlog ha
  let y := Real.sqrt (Real.log x)
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have heq : y ^ (2 * A) = Real.log x ^ A := by
    rw [Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt hlog.le]
  change y ^ (2*A) * Real.exp (-c*y) < ε / C at hsmall
  rw [heq, lt_div_iff₀ hC] at hsmall
  have hφ : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hφlog : (q.totient : ℝ) ≤ Real.log x ^ A := (Nat.cast_le.mpr (Nat.totient_le q)).trans hqlog
  apply (herr x q a hx hq hqlog ha).trans
  rw [le_div_iff₀ hφ]
  calc _ = x * C * Real.exp (-c*y) * q.totient := by ring
       _ ≤ x * C * Real.exp (-c*y) * (Real.log x ^ A) :=
           mul_le_mul_of_nonneg_left hφlog (by positivity)
       _ = (Real.log x ^ A * Real.exp (-c*y) * C) * x := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le (by linarith)

/-- For every positive `ε`, some constant `C` bounds the least prime in every
reduced residue class modulo `q` by `exp (C q^ε)`. -/
theorem leastPrimeAP_le_exp_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q),
      (leastPrimeAP hq ha : ℝ) ≤ Real.exp (C * (q : ℝ)^ε) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (eventually_thetaAP_relative_error_le (A := 1 / ε) (one_div_pos.mpr hε).le (ε := 1/2) (by norm_num))
  let C := max 1 (Real.log (max 2 X))
  have hC : 1 ≤ C := le_max_left ..
  refine ⟨C, by linarith, fun {q a} hq ha => ?_⟩
  let x := Real.exp (C * (q : ℝ)^ε)
  have hq1 := Nat.pos_of_ne_zero hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hp : 1 ≤ (q : ℝ)^ε := Real.one_le_rpow hqR hε.le
  have hXx : X ≤ x := by
    calc X ≤ max 2 X := le_max_right ..
         _ = Real.exp (Real.log (max 2 X)) := (Real.exp_log (lt_of_lt_of_le zero_lt_two (le_max_left ..))).symm
         _ ≤ _ := Real.exp_le_exp.mpr ((le_max_right ..).trans (le_mul_of_one_le_right (by linarith) hp))
  have hqlog : (q : ℝ) ≤ Real.log x ^ (1/ε) := by
    dsimp [x]; rw [Real.log_exp]
    calc (q : ℝ) = ((q : ℝ)^ε)^(1/ε) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hε.ne', Real.rpow_one]
         _ ≤ _ := Real.rpow_le_rpow (by positivity) (le_mul_of_one_le_left (by positivity) hC) (one_div_pos.mpr hε).le
  have he := hX x hXx q a hq1 hqlog ha
  apply (leastPrimeAP_le_iff_thetaAP_pos hq ha x).mpr
  have hmain : 0 < x / q.totient := div_pos (Real.exp_pos _) (Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1))
  have hb := (abs_le.mp he).1
  rw [mul_div_assoc] at hb
  linarith

end AnalyticNumberTheory.PrimeDistribution
