import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Chebyshev Functions and Mertens' Theorems

This file develops the classical elementary theory of prime distribution around the Chebyshev
functions `Chebyshev.psi` (`ψ`), `Chebyshev.theta` (`θ`), and the real-valued prime counting
function `primePi` (`π`):

- Unified API around `Nat.primeCounting`, `Chebyshev.theta`, and `Chebyshev.psi`, including
  monotonicity, positivity, and summation formulas over `Finset.Icc 1 ⌊x⌋₊` and `Nat.primesLE`.
- Quantitative Abel-summation equivalence identities relating `primePi`, `theta`, and `psi`,
  including the logarithmic-integral error transfer identity and explicit `O(√x)` / `O(x / log² x)`
  remainder bounds.
- Explicit Chebyshev upper and lower bounds for `psi`, `theta`, and `primePi`.
- Rigorous proofs of all three Mertens' theorems (with explicit remainder constants and asymptotic
  forms):
  1. `mertens_first_theorem`: `∑_{p ≤ x} log p / p = log x + O(1)`.
  2. `mertens_second_theorem`: `∑_{p ≤ x} 1 / p = log (log x) + M + O(1 / log x)`, defining the
     Meissel–Mertens constant `meisselMertensConstant`.
  3. `mertens_third_theorem`: `∏_{p ≤ x} (1 - 1 / p) = exp(-γ) / log x * (1 + O(1 / log x))`,
     deduced via `meisselMertensConstant - ∑' p, (log(1 - 1/p) + 1/p) = γ`.
-/

noncomputable section

open Nat hiding log
open Finset MeasureTheory Set Filter Asymptotics
open scoped Topology Nat.Prime ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.PrimeDistribution

/-! ### Unified API for `primePi`, `theta`, and `psi` -/

/-- The real-valued prime counting function `π(x)` counting primes `p ≤ x`. -/
def primePi (x : ℝ) : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- At a natural number `n`, `primePi n` equals `(Nat.primeCounting n : ℝ)`. -/
@[simp]
theorem primePi_natCast (n : ℕ) : primePi (n : ℝ) = (Nat.primeCounting n : ℝ) := by
  simp [primePi]

/-- `primePi x` is always nonnegative. -/
theorem primePi_nonneg (x : ℝ) : 0 ≤ primePi x :=
  Nat.cast_nonneg _

/-- `primePi` is monotone nondecreasing on `ℝ`. -/
@[gcongr]
theorem primePi_mono : Monotone primePi := fun _ _ hxy =>
  Nat.cast_le.mpr (Nat.monotone_primeCounting (Nat.floor_mono hxy))

/-- `primePi x` vanishes for `x < 2`. -/
theorem primePi_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : primePi x = 0 := by
  unfold primePi
  have hfl : ⌊x⌋₊ ≤ 1 := by
    by_cases hx0 : x < 0
    · simp [Nat.floor_of_nonpos hx0.le]
    · have h2 : ⌊x⌋₊ < 2 := (Nat.floor_lt (not_lt.mp hx0)).mpr (by exact_mod_cast hx)
      omega
  rw [Nat.primeCounting_eq_zero_iff.mpr hfl, Nat.cast_zero]

/-- `primePi x` is strictly positive for `2 ≤ x`. -/
theorem primePi_pos {x : ℝ} (hx : 2 ≤ x) : 0 < primePi x := by
  have h2 : (1 : ℝ) ≤ primePi 2 := by
    unfold primePi
    rw [Nat.floor_ofNat]
    exact_mod_cast (by decide : 1 ≤ Nat.primeCounting 2)
  exact lt_of_lt_of_le zero_lt_one (h2.trans (primePi_mono hx))

/-- `primePi x` equals the cardinality of `Nat.primesLE ⌊x⌋₊`. -/
theorem primePi_eq_card_primesLE (x : ℝ) : primePi x = ((Nat.primesLE ⌊x⌋₊).card : ℝ) := by
  simp [primePi, Nat.primesLE_card_eq_primeCounting]

/-- `primePi x` expressed as the sum of `1` over primes `p ≤ x`. -/
theorem primePi_eq_sum (x : ℝ) : primePi x = ∑ _p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) := by
  simp [primePi_eq_card_primesLE]

/-- `Chebyshev.psi x` expressed as a sum over `Finset.Icc 1 ⌊x⌋₊`. -/
theorem psi_eq_sum_Icc (x : ℝ) : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
  rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- `Chebyshev.theta x` expressed as a sum over `Nat.primesLE ⌊x⌋₊`. -/
theorem theta_eq_sum_primesLE (x : ℝ) :
    Chebyshev.theta x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p :=
  Chebyshev.theta_eq_sum_primesLE x

/-- `Chebyshev.theta x` expressed as a filtered sum over `Finset.Icc 1 ⌊x⌋₊`. -/
theorem theta_eq_sum_Icc (x : ℝ) :
    Chebyshev.theta x = ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Real.log p := by
  rw [Chebyshev.theta, Finset.sum_filter, Finset.sum_filter, ← Finset.Icc_add_one_left_eq_Ioc,
    zero_add]

/-- Basic comparison `θ(x) ≤ ψ(x)` for all `x : ℝ`. -/
theorem theta_le_psi (x : ℝ) : Chebyshev.theta x ≤ Chebyshev.psi x :=
  Chebyshev.theta_le_psi x

/-- Basic comparison `θ(x) ≤ π(x) * log x` for all `x : ℝ`. -/
theorem theta_le_primePi_mul_log (x : ℝ) : Chebyshev.theta x ≤ primePi x * Real.log x := by
  simpa [primePi] using Chebyshev.theta_le_pi_mul_log' x

/-- Basic comparison `ψ(x) ≤ π(x) * log x` for all `x : ℝ`. -/
theorem psi_le_primePi_mul_log (x : ℝ) : Chebyshev.psi x ≤ primePi x * Real.log x := by
  simpa [primePi] using Chebyshev.psi_le_primeCounting_mul_log' x

/-! ### Quantitative Abel-Summation Equivalence Lemmas -/

private theorem intervalIntegrable_inv_log (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 x := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hx]
  have hlog : ContinuousOn Real.log (Set.Icc (2 : ℝ) x) :=
    Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le zero_lt_two ht.1).ne'
  exact hlog.inv₀ fun t ht => (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'

private theorem intervalIntegrable_inv_log_sq (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
  Chebyshev.intervalIntegrable_one_div_log_sq one_lt_two (lt_of_lt_of_le one_lt_two hx)

private theorem intervalIntegrable_log_div_mul_log_sq (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Real.log t / (t * Real.log t ^ 2)) volume 2 x := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hx]
  have hlog : ContinuousOn Real.log (Set.Icc (2 : ℝ) x) :=
    Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le zero_lt_two ht.1).ne'
  refine hlog.div (continuousOn_id.mul (hlog.pow 2)) fun t ht =>
    mul_ne_zero (lt_of_lt_of_le zero_lt_two ht.1).ne'
      (pow_ne_zero 2 (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne')

/-- Expresses `primePi x` in terms of `Chebyshev.theta` for `2 ≤ x` via Abel summation. -/
theorem primePi_eq_theta_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    primePi x = Chebyshev.theta x / Real.log x +
      ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2) := by
  simpa [primePi] using Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-- Expresses `Chebyshev.theta x` in terms of `primePi` for `2 ≤ x` via Abel summation. -/
theorem theta_eq_primePi_mul_log_sub_integral {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.theta x = primePi x * Real.log x - ∫ t in (2 : ℝ)..x, primePi t / t := by
  simpa [primePi] using Chebyshev.theta_eq_primeCounting_mul_log_sub_integral hx

private theorem integral_inv_log_eq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hint_sub :
      ∫ t in (2 : ℝ)..x, ((Real.log t)⁻¹ - 1 / Real.log t ^ 2) =
        x / Real.log x - 2 / Real.log 2 := by
    have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun u : ℝ => u / Real.log u) ((Real.log t)⁻¹ - 1 / Real.log t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_two ht.1).ne'
      have hlog : Real.log t ≠ 0 := (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'
      have h := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hlog
      refine h.congr_deriv ?_
      field_simp [ht0, hlog]
    have hint : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹ - 1 / Real.log t ^ 2) volume 2 x :=
      (intervalIntegrable_inv_log x hx).sub (intervalIntegrable_inv_log_sq x hx)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_inv_log x hx)
    (intervalIntegrable_inv_log_sq x hx)] at hint_sub
  linarith

private theorem intervalIntegrable_theta_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x

/-- Exact Abel-summation error-transfer identity comparing `primePi x - ∫_2^x (log t)⁻¹ dt` to
`θ(x) - x` for `2 ≤ x`. -/
theorem primePi_sub_li_eq_theta_sub_id_abel {x : ℝ} (hx : 2 ≤ x) :
    primePi x - ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ =
      (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  have hpi := primePi_eq_theta_div_log_add_integral hx
  have hli := integral_inv_log_eq hx
  have h1 : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x :=
    intervalIntegrable_theta_div_mul_log_sq hx
  have h2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    intervalIntegrable_inv_log_sq x hx
  have hcongr :
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2) =
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_two ht.1).ne'
    have hlog : Real.log t ≠ 0 := (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'
    field_simp [ht0, hlog]
  rw [hpi, hli]
  have hsub := intervalIntegral.integral_sub h1 h2
  rw [hcongr] at hsub
  linarith [show Chebyshev.theta x / Real.log x - x / Real.log x =
    (Chebyshev.theta x - x) / Real.log x by ring]

/-- Explicit `O(√x log x)` bound for `|ψ(x) - θ(x)|` valid for `1 ≤ x`. -/
theorem abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx

/-- Explicit `O(√x)` bound for `|ψ(x) - θ(x)|` valid for all `x : ℝ`, with constant
`3 * (log 4 + 4)`. -/
theorem abs_psi_sub_theta_le_mul_sqrt (x : ℝ) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ (Real.log 4 + 4) * 3 * Real.sqrt x := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
  rcases le_total x 1 with hx | hx
  · rw [Chebyshev.theta_eq_zero_of_le_one hx, Chebyshev.psi_eq_zero_of_le_one hx, sub_self]
    positivity
  · have hpow (n : ℕ) (hn : 2 ≤ n) :
        Chebyshev.psi (x ^ (n : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      have hr : 0 ≤ x ^ (n : ℝ)⁻¹ := Real.rpow_nonneg (zero_le_one.trans hx) _
      refine (Chebyshev.psi_le_const_mul_self hr).trans ?_
      rw [Real.sqrt_eq_rpow, one_div]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx
          (inv_anti₀ (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn : (2 : ℝ) ≤ n)))
        (by positivity)
    have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    have h2 : Chebyshev.psi (x ^ (2 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      simpa using hpow 2 le_rfl
    have h3 : Chebyshev.psi (x ^ (3 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      simpa using hpow 3 (by omega)
    have h5 : Chebyshev.psi (x ^ (5 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      simpa using hpow 5 (by omega)
    linarith

/-- Asymptotic `O(√x)` bound `ψ(x) - θ(x) = O(√x)` as `x → ∞`. -/
theorem psi_sub_theta_isBigO_sqrt :
    (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x) =O[atTop] Real.sqrt :=
  Chebyshev.isBigO_psi_sub_theta_sqrt

/-- Asymptotic `O(x / (log x)²)` bound `π(x) - θ(x) / log x = O(x / (log x)²)` as `x → ∞`. -/
theorem primePi_sub_theta_div_log_isBigO :
    (fun x : ℝ => primePi x - Chebyshev.theta x / Real.log x) =O[atTop]
      (fun x : ℝ => x / Real.log x ^ 2) := by
  simpa [primePi] using Chebyshev.primeCounting_sub_theta_div_log_isBigO

private theorem integral_one_div_log_sq_le_of_le {a b : ℝ} (hab : a ≤ b) (ha : 1 < a) :
    ∫ t in a..b, 1 / Real.log t ^ 2 ≤ (b - a) / Real.log a ^ 2 := by
  have hint := Chebyshev.intervalIntegrable_one_div_log_sq ha (ha.trans_le hab)
  have hmono : ∫ t in a..b, 1 / Real.log t ^ 2 ≤ ∫ _t in a..b, 1 / Real.log a ^ 2 := by
    refine intervalIntegral.integral_mono_on hab hint (by simp) fun t ht => ?_
    have hlog_pos : 0 < Real.log a := Real.log_pos ha
    have hlog_le : Real.log a ≤ Real.log t := Real.log_le_log (zero_lt_one.trans ha) ht.1
    exact one_div_le_one_div_of_le (sq_pos_of_pos hlog_pos) (pow_le_pow_left₀ hlog_pos.le hlog_le 2)
  refine hmono.trans_eq ?_
  simp [div_eq_mul_inv]

/-- Explicit bound on `|π(x) - θ(x) / log x|` for `4 ≤ x`. -/
theorem abs_primePi_sub_theta_div_log_le {x : ℝ} (hx : 4 ≤ x) :
    |primePi x - Chebyshev.theta x / Real.log x| ≤
      Real.log 4 * (4 * x / Real.log x ^ 2 + Real.sqrt x / Real.log 2 ^ 2) := by
  have hx2 : 2 ≤ x := by linarith
  have hsqrt2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hsqrtx : Real.sqrt x ≤ x := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  rw [primePi_eq_theta_div_log_add_integral hx2, add_sub_cancel_left]
  have hnorm : |∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)| ≤
      ∫ t in (2 : ℝ)..x, ‖Chebyshev.theta t / (t * Real.log t ^ 2)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hx2
  have hmono : ∫ t in (2 : ℝ)..x, ‖Chebyshev.theta t / (t * Real.log t ^ 2)‖ ≤
      ∫ t in (2 : ℝ)..x, Real.log 4 * (1 / Real.log t ^ 2) := by
    refine intervalIntegral.integral_mono_on hx2 (intervalIntegrable_theta_div_mul_log_sq hx2).norm
      ((intervalIntegrable_inv_log_sq x hx2).const_mul _) fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ht.1
    have hlogt : Real.log t ≠ 0 := (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Chebyshev.theta_nonneg t) (by positivity))]
    calc Chebyshev.theta t / (t * Real.log t ^ 2)
        ≤ (Real.log 4 * t) / (t * Real.log t ^ 2) := by
          gcongr
          exact Chebyshev.theta_le_log4_mul_x ht0.le
      _ = Real.log 4 * (1 / Real.log t ^ 2) := by field_simp [ht0.ne', hlogt]
  have heval : ∫ t in (2 : ℝ)..x, Real.log 4 * (1 / Real.log t ^ 2) =
      Real.log 4 * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have hsplit : ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 =
      (∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ^ 2) +
        ∫ t in Real.sqrt x..x, 1 / Real.log t ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Chebyshev.intervalIntegrable_one_div_log_sq one_lt_two (by linarith))
      (Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith))).symm
  have hleft : ∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ^ 2 ≤ Real.sqrt x / Real.log 2 ^ 2 := by
    refine (integral_one_div_log_sq_le_of_le hsqrt2 one_lt_two).trans ?_
    gcongr
    linarith
  have hright : ∫ t in Real.sqrt x..x, 1 / Real.log t ^ 2 ≤ 4 * x / Real.log x ^ 2 := by
    refine (integral_one_div_log_sq_le_of_le hsqrtx (by linarith)).trans ?_
    rw [Real.log_sqrt (by linarith), div_pow, div_div_eq_mul_div]
    have hle : x - Real.sqrt x ≤ x := by linarith [Real.sqrt_nonneg x]
    have hlogx_pos : 0 < Real.log x ^ 2 := sq_pos_of_pos (Real.log_pos (by linarith))
    calc (x - Real.sqrt x) * (2 : ℝ) ^ 2 / Real.log x ^ 2
        ≤ x * (2 : ℝ) ^ 2 / Real.log x ^ 2 := by gcongr
      _ = 4 * x / Real.log x ^ 2 := by ring
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc |∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)|
      ≤ Real.log 4 * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := hnorm.trans (hmono.trans_eq heval)
    _ ≤ Real.log 4 * (4 * x / Real.log x ^ 2 + Real.sqrt x / Real.log 2 ^ 2) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left (by linarith) hlog4_nn

/-- Equivalence of PNT limit statements for `θ(x)/x` and `ψ(x)/x`. -/
theorem tendsto_theta_div_iff_tendsto_psi_div (c : ℝ) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 c) ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 c) := by
  have hdiff : Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) :=
    Chebyshev.isLittleO_psi_sub_theta_id.tendsto_div_nhds_zero
  constructor
  · intro h
    simpa using (h.add hdiff).congr' (by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [field])
  · intro h
    simpa using (h.sub hdiff).congr' (by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [field])

/-- Equivalence of PNT limit statements for `π(x) * log x / x` and `θ(x) / x`. -/
theorem tendsto_primePi_mul_log_div_iff_tendsto_theta_div (c : ℝ) :
    Tendsto (fun x : ℝ => primePi x * Real.log x / x) atTop (𝓝 c) ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 c) := by
  have hdiff : Tendsto (fun x : ℝ => (primePi x * Real.log x - Chebyshev.theta x) / x)
      atTop (𝓝 0) := by
    simpa [primePi] using Chebyshev.isLittleO_primeCounting_mul_log_sub_theta.tendsto_div_nhds_zero
  constructor
  · intro h
    simpa using (h.sub hdiff).congr' (by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [field])
  · intro h
    simpa using (h.add hdiff).congr' (by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [field])

/-! ### Explicit Chebyshev Bounds -/

/-- Chebyshev's upper bound `θ(x) ≤ (log 4) * x` for `0 ≤ x`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) : Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

/-- Chebyshev's upper bound `ψ(x) ≤ (log 4 + 4) * x` for `0 ≤ x`. -/
theorem psi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/-- Explicit Chebyshev lower bound `(log 2 / 3) * x ≤ ψ(x)` valid for all `x ≥ 2`. -/
theorem psi_ge_explicit {x : ℝ} (hx : 2 ≤ x) : (Real.log 2 / 3) * x ≤ Chebyshev.psi x := by
  have hfl2 : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hx
  have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Chebyshev.psi_eq_psi_coe_floor]
  by_cases h7 : 7 ≤ ⌊x⌋₊
  · have h3 : x ≤ 3 * (⌊x⌋₊ : ℝ) := by
      have : (7 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h7
      linarith
    calc (Real.log 2 / 3) * x
        ≤ (Real.log 2 / 3) * (3 * (⌊x⌋₊ : ℝ)) := by gcongr
      _ = (⌊x⌋₊ : ℝ) * Real.log 2 := by ring
      _ ≤ Chebyshev.psi (⌊x⌋₊ : ℝ) := Chebyshev.psi_ge_of_seven_le h7
  · have hlt7 : ⌊x⌋₊ < 7 := not_le.mp h7
    have hn_bound : (((⌊x⌋₊ + 1 : ℕ) : ℝ)) * Real.log 2 / 3 ≤ Chebyshev.psi (⌊x⌋₊ : ℝ) := by
      have hpow_le : (2 : ℕ) ^ (⌊x⌋₊ + 1) ≤ (Nat.lcmUpto ⌊x⌋₊) ^ 3 := by
        interval_cases h : ⌊x⌋₊ <;> decide
      have hlog_le : Real.log ((2 : ℝ) ^ (⌊x⌋₊ + 1)) ≤ Real.log ((Nat.lcmUpto ⌊x⌋₊ : ℝ) ^ 3) := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast hpow_le
      rw [Real.log_pow, Real.log_pow, ← Chebyshev.psi_eq_log_lcmUpto] at hlog_le
      push_cast at hlog_le ⊢
      linarith
    calc (Real.log 2 / 3) * x
        ≤ (Real.log 2 / 3) * ((⌊x⌋₊ : ℝ) + 1) := by gcongr
      _ = (((⌊x⌋₊ + 1 : ℕ) : ℝ)) * Real.log 2 / 3 := by push_cast; ring
      _ ≤ Chebyshev.psi (⌊x⌋₊ : ℝ) := hn_bound

/-- Explicit Chebyshev lower bound `(log 2 / 4) * x ≤ θ(x)` valid for `x ≥ 3600`. -/
theorem theta_ge_explicit {x : ℝ} (hx : 3600 ≤ x) : (Real.log 2 / 4) * x ≤ Chebyshev.theta x := by
  have hx7 : 7 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by norm_num; linarith)
  have hpsi : (⌊x⌋₊ : ℝ) * Real.log 2 ≤ Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_psi_coe_floor]
    exact Chebyshev.psi_ge_of_seven_le hx7
  have hx_floor : (6 / 7 : ℝ) * x ≤ (⌊x⌋₊ : ℝ) := by
    have hlt : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
    linarith
  have hdiff : Chebyshev.psi x - Chebyshev.theta x ≤ (Real.log 4 + 4) * 3 * Real.sqrt x := by
    have h := abs_psi_sub_theta_le_mul_sqrt x
    rwa [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))] at h
  have hlog4_lt : Real.log 4 < 2 := by
    have h4_lt : (4 : ℝ) < Real.exp 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
      nlinarith
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    exact h4_lt
  have hhalf_lt_log2 : (1 / 2 : ℝ) < Real.log 2 := by
    rw [show (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) by simp]
    have hexp_lt : Real.exp (1 / 2 : ℝ) < 2 := by
      have hsq : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp (1 / 2 : ℝ) = Real.sqrt (Real.exp 1) := by
            rw [Real.sqrt_eq_rpow, Real.exp_one_rpow]
        _ < Real.sqrt 4 := Real.sqrt_lt_sqrt (Real.exp_pos 1).le hsq
        _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    exact Real.log_lt_log (Real.exp_pos _) hexp_lt
  have hsqrt_le : 60 * Real.sqrt x ≤ x := by
    have hsq : (60 * Real.sqrt x) ^ 2 ≤ x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      nlinarith
    nlinarith [Real.sqrt_nonneg x]
  have hC_lt : (Real.log 4 + 4) * 3 * Real.sqrt x ≤ (3 / 10 : ℝ) * x := by
    have h1 : (Real.log 4 + 4) * 3 < 18 := by linarith
    have h2 : (Real.log 4 + 4) * 3 * Real.sqrt x ≤ 18 * Real.sqrt x := by
      gcongr
    linarith
  have hmain : (6 / 7 - 1 / 4 : ℝ) * Real.log 2 * x ≥ (3 / 10 : ℝ) * x := by
    nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpsi_low : (6 / 7 : ℝ) * Real.log 2 * x ≤ Chebyshev.psi x := by
    have hmul : (6 / 7 : ℝ) * x * Real.log 2 ≤ (⌊x⌋₊ : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hx_floor hlog2_pos.le
    linarith
  linarith

/-- Explicit Chebyshev upper bound `π(x) ≤ (2 * log 4 + 2) * (x / log x)` for `x > 1`. -/
theorem primePi_le_explicit {x : ℝ} (hx : 1 < x) :
    primePi x ≤ (2 * Real.log 4 + 2) * (x / Real.log x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hsqrt1 : 1 < Real.sqrt x := Real.lt_sqrt_of_sq_lt (by simpa using hx)
  have hlog_sqrt : Real.log (Real.sqrt x) = Real.log x / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hx0]
    ring
  have hlog_sqrt_pos : 0 < Real.log (Real.sqrt x) := Real.log_pos hsqrt1
  have hlog_sqrt_le : Real.log (Real.sqrt x) ≤ Real.sqrt x :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans hsqrt1)).trans (by linarith)
  have hsqrt_le : Real.sqrt x ≤ 2 * x / Real.log x := by
    have h1 : Real.sqrt x * Real.log x ≤ 2 * x := by
      have hmul : Real.log x ≤ 2 * Real.sqrt x := by linarith
      calc Real.sqrt x * Real.log x
          ≤ Real.sqrt x * (2 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg x)
        _ = 2 * (Real.sqrt x) ^ 2 := by ring
        _ = 2 * x := by rw [Real.sq_sqrt hx0.le]
    exact (le_div_iff₀ hlogx).mpr h1
  have hpi := Chebyshev.pi_le_log4_mul_div hx
  change primePi x ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x at hpi
  rw [hlog_sqrt] at hpi
  have hdiv : Real.log 4 * x / (Real.log x / 2) = (2 * Real.log 4) * (x / Real.log x) := by
    field_simp [hlogx.ne']
  rw [hdiv] at hpi
  linarith [show 2 * x / Real.log x = 2 * (x / Real.log x) by ring]

/-- Explicit Chebyshev lower bound `(log 2 / 4) * (x / log x) ≤ π(x)` for all `x ≥ 2`. -/
theorem primePi_ge_explicit {x : ℝ} (hx : 2 ≤ x) :
    (Real.log 2 / 4) * (x / Real.log x) ≤ primePi x := by
  have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  by_cases hx4 : 4 ≤ x
  · have hfl4 : 4 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hx4
    have hfl_pos : (1 : ℝ) < ⌊x⌋₊ := by
      have : (4 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfl4
      linarith
    have hlog_fl_pos : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos hfl_pos
    have hlog_fl_le : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
    have hx_le : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have : (4 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfl4
      linarith
    have hpi4 : (⌊x⌋₊ : ℝ) * Real.log 2 / Real.log (⌊x⌋₊ : ℝ) ≤ primePi x := by
      simpa [primePi] using Chebyshev.pi_ge_of_four_le hfl4
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc (Real.log 2 / 4) * (x / Real.log x)
        ≤ (Real.log 2 / 4) * ((2 * (⌊x⌋₊ : ℝ)) / Real.log (⌊x⌋₊ : ℝ)) := by
          gcongr
      _ = ((⌊x⌋₊ : ℝ) * Real.log 2 / Real.log (⌊x⌋₊ : ℝ)) / 2 := by ring
      _ ≤ (⌊x⌋₊ : ℝ) * Real.log 2 / Real.log (⌊x⌋₊ : ℝ) := by
          have hnn : 0 ≤ (⌊x⌋₊ : ℝ) * Real.log 2 / Real.log (⌊x⌋₊ : ℝ) := by positivity
          linarith
      _ ≤ primePi x := hpi4
  · have hx_lt4 : x < 4 := not_le.mp hx4
    have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h1 : (Real.log 2 / 4) * (x / Real.log x) ≤ 1 := by
      calc (Real.log 2 / 4) * (x / Real.log x)
          ≤ (Real.log 2 / 4) * (4 / Real.log 2) := by
            gcongr
        _ = 1 := by field_simp [hlog2_pos.ne']
    have hpi1 : 1 ≤ primePi x := by
      have h2 : (1 : ℝ) ≤ primePi 2 := by
        unfold primePi
        rw [Nat.floor_ofNat]
        exact_mod_cast (by decide : 1 ≤ Nat.primeCounting 2)
      exact h2.trans (primePi_mono hx)
    exact h1.trans hpi1

/-! ### Mertens' First Theorem -/

/-- Exact identity `∑_{1 ≤ n ≤ N} Λ(n) * ⌊N / n⌋ = log(N!)` relating `Λ` and factorials. -/
theorem sum_vonMangoldt_mul_floor_div (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ) = Real.log (N ! : ℝ) := by
  rw [← sum_log_eq_log_factorial N]
  have hlog : ∀ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) = ∑ d ∈ m.divisors, Λ d :=
    fun m _ => (ArithmeticFunction.vonMangoldt_sum (n := m)).symm
  rw [Finset.sum_congr rfl hlog]
  have hdiv : ∀ m ∈ Finset.Icc 1 N,
      ∑ d ∈ m.divisors, Λ d = ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then Λ d else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.mp hm).1
      omega
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, ne_eq, hm0, not_false_eq_true,
      and_true]
    constructor
    · intro hd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm0),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd).trans (Finset.mem_Icc.mp hm).2⟩, hd⟩
    · exact fun hd => hd.2
  rw [Finset.sum_congr rfl hdiv, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_mem := Finset.mem_Icc.mp hd
  have hd_pos : 0 < d := hd_mem.1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hcard : #{m ∈ Finset.Icc 1 N | d ∣ m} = N / d := by
    have hbij : Finset.image (fun k : ℕ => d * k) (Finset.Icc 1 (N / d)) =
        (Finset.Icc 1 N).filter (fun m => d ∣ m) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨k, ⟨hk1, hkd⟩, rfl⟩
        exact ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos hd_pos hk1),
            (Nat.mul_le_mul_left d hkd).trans (Nat.mul_div_le N d)⟩,
          dvd_mul_right d k⟩
      · rintro ⟨⟨hm1, hmN⟩, k, rfl⟩
        refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hd_pos).mpr (by simpa [mul_comm] using hmN)⟩, rfl⟩
        by_contra hk0
        have hk : k = 0 := by omega
        subst hk
        omega
    rw [← hbij, Finset.card_image_of_injective _ (mul_right_injective₀ hd_pos.ne')]
    simp
  rw [hcard]

/-- Explicit `O(1)` bound for `∑_{1 ≤ n ≤ x} Λ(n) / n - log x` valid for `1 ≤ x`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n - Real.log x| ≤ Real.log 4 + 8 := by
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN1
  have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN1
  have hfac := sum_vonMangoldt_mul_floor_div N
  rw [← sum_log_eq_log_factorial N] at hfac
  have hstirl := abs_sum_log_sub_le hN1
  have hlogN_le : Real.log (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have hle : Real.log (N : ℝ) ≤ (N : ℝ) - 1 := Real.log_le_sub_one_of_pos hN_pos
    linarith
  have hdiff_nn :
      0 ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n -
        ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hdiv_le : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr hn_pos)]
      exact_mod_cast Nat.div_mul_le_self N n
    have hmul_eq : (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
    rw [hmul_eq, ← mul_sub]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr hdiv_le)
  have hdiff_le :
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n -
          ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ) ≤
        Chebyshev.psi N := by
    rw [psi_eq_sum_Icc, Nat.floor_natCast, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hlt : (N : ℝ) / n < ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (Nat.cast_pos.mpr hn_pos)]
      have : N < (N / n + 1) * n := by
        have hlt_nat := Nat.lt_div_mul_add hn_pos (a := N)
        linarith [show (N / n + 1) * n = N / n * n + n by ring]
      exact_mod_cast this
    have hmul_eq : (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
    rw [hmul_eq, ← mul_sub]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (by linarith)
  have hpsiN : Chebyshev.psi (N : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) :=
    Chebyshev.psi_le_const_mul_self hN_pos.le
  have hN_bound : |∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N| ≤ Real.log 4 + 7 := by
    have hmain : |((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n) - ((N : ℝ) * Real.log N - N)| ≤
        (Real.log 4 + 6) * (N : ℝ) := by
      have h1 : |(∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ)) - ((N : ℝ) * Real.log N - N)| ≤
          2 * (N : ℝ) := by
        rw [hfac]
        exact hstirl.trans hlogN_le
      have h2 : |(N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n -
          ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ)| ≤ (Real.log 4 + 4) * (N : ℝ) := by
        rw [abs_of_nonneg hdiff_nn]
        exact hdiff_le.trans hpsiN
      calc |(N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n - ((N : ℝ) * Real.log N - N)|
          ≤ |(N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n -
              ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ)| +
            |∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ) - ((N : ℝ) * Real.log N - N)| :=
            abs_sub_le _ _ _
        _ ≤ (Real.log 4 + 4) * (N : ℝ) + 2 * (N : ℝ) := add_le_add h2 h1
        _ = (Real.log 4 + 6) * (N : ℝ) := by ring
    have hdivN : |∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N + 1| ≤ Real.log 4 + 6 := by
      have hmul_abs : |(N : ℝ) * (∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N + 1)| ≤
          (N : ℝ) * (Real.log 4 + 6) := by
        have heq : (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N + 1) =
            (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, Λ n / n - ((N : ℝ) * Real.log N - N) := by ring
        rw [heq]
        exact hmain.trans_eq (by ring)
      rw [abs_mul, abs_of_pos hN_pos] at hmul_abs
      exact (mul_le_mul_iff_right₀ hN_pos).mp hmul_abs
    calc |∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N|
        ≤ |∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N + 1| + 1 := by
          have := abs_sub (∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N + 1) 1
          simpa using this
      _ ≤ (Real.log 4 + 6) + 1 := add_le_add hdivN le_rfl
      _ = Real.log 4 + 7 := by ring
  have hlog_diff : |Real.log x - Real.log N| ≤ 1 := by
    have hx_le : x ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h0 : 0 ≤ Real.log x - Real.log N := sub_nonneg.mpr (Real.log_le_log hN_pos hNx)
    have hle : Real.log x - Real.log N ≤ 1 := by
      rw [← Real.log_div (by linarith) hN_pos.ne']
      calc Real.log (x / N) ≤ x / N - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) hN_pos)
        _ ≤ (N + 1) / N - 1 := by gcongr
        _ = (N : ℝ)⁻¹ := by field_simp [hN_pos.ne']; ring
        _ ≤ 1 := inv_le_one_of_one_le₀ h1N
    rwa [abs_of_nonneg h0]
  calc |∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log x|
      ≤ |∑ n ∈ Finset.Icc 1 N, Λ n / n - Real.log N| + |Real.log x - Real.log N| := by
        rw [abs_sub_comm (Real.log x)]
        exact abs_sub_le _ _ _
    _ ≤ (Real.log 4 + 7) + 1 := add_le_add hN_bound hlog_diff
    _ = Real.log 4 + 8 := by ring

/-- Big-O form of Mertens' first theorem for `Λ`: `∑_{n ≤ x} Λ(n) / n - log x = O(1)`. -/
theorem sum_vonMangoldt_div_sub_log_isBigO_one :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n - Real.log x) =O[atTop]
      (fun _ : ℝ => (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨Real.log 4 + 8, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, norm_one, mul_one]
  exact abs_sum_vonMangoldt_div_sub_log_le hx

/-- Uniform bound on the higher prime-power contribution `∑_{n ≤ x, ¬n.Prime} Λ(n) / n`. -/
theorem sum_not_prime_vonMangoldt_div_le (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, Λ n / n ≤ 2 * ((Real.log 4 + 4) * 3) := by
  let C₀ : ℝ := (Real.log 4 + 4) * 3
  rcases lt_or_ge x 1 with hx | hx
  · have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
    simp [hfl]
    positivity
  · let c : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n
    have hsum_eq : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, Λ n / n =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n * (n : ℝ)⁻¹ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hp : n.Prime <;> simp [c, hp, div_eq_mul_inv]
    have hc_partial : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k = Chebyshev.psi t - Chebyshev.theta t := by
      intro t
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter,
        ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : k.Prime <;> simp [c, hp]
    have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt (fun u : ℝ => u⁻¹) (-t ^ (-2 : ℝ)) t := by
      intro t ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_one ht.1).ne'
      convert hasDerivAt_inv ht0 using 1
      rw [Real.rpow_neg (lt_of_lt_of_le zero_lt_one ht.1).le, Real.rpow_two]
    have hcont : ContinuousOn (fun t : ℝ => -t ^ (-2 : ℝ)) (Set.Icc (1 : ℝ) x) := by
      refine ContinuousOn.neg (continuousOn_of_forall_continuousAt fun t ht => ?_)
      exact Real.continuousAt_rpow_const t (-2) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
    have hAbel := abel_summation_Icc_one_hasDerivAt c hx hderiv hcont
    rw [hsum_eq, hAbel, hc_partial x]
    have hcongr_int : ∫ t in (1 : ℝ)..x, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (-t ^ (-2 : ℝ)) =
        -∫ t in (1 : ℝ)..x, (Chebyshev.psi t - Chebyshev.theta t) * t ^ (-2 : ℝ) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      rw [hc_partial t]
      ring
    rw [hcongr_int, sub_neg_eq_add]
    have hR_bound : ∀ t : ℝ, Chebyshev.psi t - Chebyshev.theta t ≤ C₀ * Real.sqrt t := by
      intro t
      have h := abs_psi_sub_theta_le_mul_sqrt t
      rwa [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))] at h
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hterm1 : (Chebyshev.psi x - Chebyshev.theta x) * x⁻¹ ≤ C₀ * x ^ (-1 / 2 : ℝ) := by
      calc (Chebyshev.psi x - Chebyshev.theta x) * x⁻¹
          ≤ (C₀ * Real.sqrt x) * x⁻¹ := by
            exact mul_le_mul_of_nonneg_right (hR_bound x) (inv_nonneg.mpr hx0.le)
        _ = C₀ * (x ^ (1 / 2 : ℝ) * x ^ (-1 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg_one]
            ring
        _ = C₀ * x ^ (-1 / 2 : ℝ) := by
            rw [← Real.rpow_add hx0]
            norm_num
    have hrpow_cont : ContinuousOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Icc (1 : ℝ) x) :=
      continuousOn_of_forall_continuousAt fun t ht =>
        Real.continuousAt_rpow_const t (-3 / 2 : ℝ) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
    have hbound : IntegrableOn (fun t : ℝ => C₀ * t ^ (-3 / 2 : ℝ)) (Set.Icc 1 x) :=
      hrpow_cont.integrableOn_Icc.const_mul C₀
    have h_psi_int : IntervalIntegrable
        (fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) * t ^ (-2 : ℝ)) volume 1 x := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      have hmono : Monotone fun t : ℝ => Chebyshev.psi t - Chebyshev.theta t := by
        intro a b hab
        dsimp only
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.psi_sub_theta_eq_sum_not_prime]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hab)))
          fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      have hmeas : Measurable fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) * t ^ (-2 : ℝ) :=
        hmono.measurable.mul (measurable_id.pow_const (-2 : ℝ))
      refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      have hR_nn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t :=
        sub_nonneg.mpr (Chebyshev.theta_le_psi t)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR_nn (Real.rpow_nonneg ht0.le _))]
      calc (Chebyshev.psi t - Chebyshev.theta t) * t ^ (-2 : ℝ)
          ≤ (C₀ * Real.sqrt t) * t ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (hR_bound t) (Real.rpow_nonneg ht0.le _)
        _ = C₀ * (t ^ (1 / 2 : ℝ) * t ^ (-2 : ℝ)) := by rw [Real.sqrt_eq_rpow]; ring
        _ = C₀ * t ^ (-3 / 2 : ℝ) := by rw [← Real.rpow_add ht0]; norm_num
    have hrhs_int : IntervalIntegrable (fun t : ℝ => C₀ * t ^ (-3 / 2 : ℝ)) volume 1 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hbound
    have hmono_int : ∫ t in (1 : ℝ)..x, (Chebyshev.psi t - Chebyshev.theta t) * t ^ (-2 : ℝ) ≤
        ∫ t in (1 : ℝ)..x, C₀ * t ^ (-3 / 2 : ℝ) := by
      refine intervalIntegral.integral_mono_on hx h_psi_int hrhs_int fun t ht => ?_
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      have hle : (Chebyshev.psi t - Chebyshev.theta t) * t ^ (-2 : ℝ) ≤
          (C₀ * Real.sqrt t) * t ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hR_bound t) (Real.rpow_nonneg ht0.le _)
      refine hle.trans_eq ?_
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht0]
      norm_num
    have heval_int : ∫ t in (1 : ℝ)..x, C₀ * t ^ (-3 / 2 : ℝ) =
        2 * C₀ * (1 - x ^ (-1 / 2 : ℝ)) := by
      have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) x := by
        rw [Set.uIcc_of_le hx]
        exact fun h => lt_irrefl (0 : ℝ) (lt_of_lt_of_le zero_lt_one h.1)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      have hexp : (-3 / 2 : ℝ) + 1 = (-1 / 2 : ℝ) := by norm_num
      rw [hexp, Real.one_rpow]
      ring
    have hx_neg_half_nn : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hC₀_nn : 0 ≤ C₀ := by positivity
    linarith [hterm1, hmono_int, heval_int, mul_nonneg hC₀_nn hx_neg_half_nn]

/-- Uniform error bound constant in Mertens' first theorem. -/
def mertensOneBound : ℝ := (Real.log 4 + 8) + 2 * ((Real.log 4 + 4) * 3)

/-- `mertensOneBound` is strictly positive. -/
theorem mertensOneBound_pos : 0 < mertensOneBound := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold mertensOneBound
  linarith

/-- Explicit `O(1)` bound for Mertens' first theorem:
`|∑_{p ≤ x} log p / p - log x| ≤ mertensOneBound` for all `1 ≤ x`. -/
theorem abs_mertens_one_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertensOneBound := by
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n -
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, Λ n / n := by
    have hprime : ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p =
        ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Λ p / p := by
      rw [Nat.primesLE_eq_filter_Icc_one]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    rw [hprime, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) Nat.Prime]
    ring
  have h1 := abs_sum_vonMangoldt_div_sub_log_le hx
  have h2 := sum_not_prime_vonMangoldt_div_le x
  have h2_nn : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, Λ n / n :=
    Finset.sum_nonneg fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have h2_abs : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n - ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p| ≤
      2 * ((Real.log 4 + 4) * 3) := by
    rw [hsplit, abs_of_nonneg h2_nn]
    exact h2
  calc |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x|
      ≤ |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n| +
          |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n - Real.log x| := abs_sub_le _ _ _
    _ = |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n - ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p| +
          |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n - Real.log x| := by rw [abs_sub_comm]
    _ ≤ 2 * ((Real.log 4 + 4) * 3) + (Real.log 4 + 8) := add_le_add h2_abs h1
    _ = mertensOneBound := by rw [mertensOneBound]; ring

/-- **Mertens' first theorem** (Big-O form): `∑_{p ≤ x} log p / p - log x = O(1)` as `x → ∞`. -/
theorem mertens_first_theorem :
    (fun x : ℝ => ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) =O[atTop]
      (fun _ : ℝ => (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨mertensOneBound, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, norm_one, mul_one]
  exact abs_mertens_one_sub_log_le hx

/-- **Mertens' first theorem** (asymptotic ratio form):
`(∑_{p ≤ x} log p / p) / log x → 1` as `x → ∞`. -/
theorem mertens_first_theorem_tendsto :
    Tendsto (fun x : ℝ => (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) / Real.log x)
      atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) / Real.log x) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul mertensOneBound)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog_pos, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_mertens_one_sub_log_le (by linarith))
      (inv_nonneg.mpr hlog_pos.le)
  have h1 : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) / Real.log x + 1)
      atTop (𝓝 (0 + 1)) := h0.add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp [hlog]
  ring

/-! ### Mertens' Second Theorem and the Meissel–Mertens Constant -/

private def mertensOneSum (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log p / p

/-- The `O(1)` remainder `∑_{p ≤ t} log p / p - log t` in Mertens' first theorem. -/
def mertensOneRem (t : ℝ) : ℝ :=
  (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log p / p) - Real.log t

private lemma mertensOneSum_mono : Monotone mertensOneSum := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hab))
    fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

private lemma measurable_mertensOneRem : Measurable mertensOneRem :=
  mertensOneSum_mono.measurable.sub Real.measurable_log

/-- Pointwise bound on `mertensOneRem t` for `1 ≤ t`. -/
theorem abs_mertensOneRem_le {t : ℝ} (ht : 1 ≤ t) : |mertensOneRem t| ≤ mertensOneBound :=
  abs_mertens_one_sub_log_le ht

private lemma integrableOn_inv_mul_log_sq_Ioi {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Ioi x) ∧
      ∫ t in Set.Ioi x, (t * Real.log t ^ 2)⁻¹ = (Real.log x)⁻¹ := by
  have hderiv : ∀ t ∈ Set.Ici x,
      HasDerivAt (fun u : ℝ => -(Real.log u)⁻¹) ((t * Real.log t ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le one_lt_two (hx.trans ht)
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    convert ((Real.hasDerivAt_log ht0).inv hlog).neg using 1
    field_simp [ht0, hlog]
  have hpos : ∀ t ∈ Set.Ioi x, 0 ≤ (t * Real.log t ^ 2)⁻¹ := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two (hx.trans ht.le)
    positivity
  have hlim : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa only [neg_zero] using hinv.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim

/-- Integrability of `t ↦ mertensOneRem t / (t * (log t)²)` on `(2, ∞)`. -/
theorem integrableOn_mertensOneRem_div :
    IntegrableOn (fun t : ℝ => mertensOneRem t / (t * Real.log t ^ 2)) (Set.Ioi (2 : ℝ)) := by
  have hbase := (integrableOn_inv_mul_log_sq_Ioi (le_rfl : (2 : ℝ) ≤ 2)).1.const_mul mertensOneBound
  refine Integrable.mono' hbase ?_ ?_
  · exact (measurable_mertensOneRem.div
      (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := one_lt_two.trans ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hlog_pos : 0 < Real.log t := Real.log_pos ht1
    have hden_pos : 0 < t * Real.log t ^ 2 := mul_pos ht0 (sq_pos_of_pos hlog_pos)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_mertensOneRem_le (by linarith))
      (inv_nonneg.mpr hden_pos.le)

/-- The **Meissel–Mertens constant**
`M = 1 - log (log 2) + ∫_{2}^∞ (∑_{p ≤ t} log p / p - log t) / (t * (log t)²) dt`. -/
def meisselMertensConstant : ℝ :=
  1 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2 : ℝ), mertensOneRem t / (t * Real.log t ^ 2)

/-- Exact Abel-summation identity for `∑_{p ≤ x} 1 / p` (`2 ≤ x`):
`∑_{p ≤ x} 1 / p = log (log x) + M + R₁(x) / log x - ∫_{x}^∞ R₁(t) / (t * (log t)²) dt`. -/
theorem sum_inv_primes_eq_abel {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ =
      Real.log (Real.log x) + meisselMertensConstant + mertensOneRem x / Real.log x -
        ∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2) := by
  have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p / p else 0
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(t * Real.log t ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le one_lt_two ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    convert (Real.hasDerivAt_log ht0).inv hlogt using 1
    field_simp [ht0, hlogt]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hcont : ContinuousOn (deriv (fun u : ℝ => (Real.log u)⁻¹)) (Set.Icc (2 : ℝ) x) := by
    have hEq : Set.EqOn (deriv (fun u : ℝ => (Real.log u)⁻¹))
        (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc (2 : ℝ) x) :=
      fun t ht => (hderiv t ht).deriv
    refine ContinuousOn.congr ?_ hEq
    have hlog_cc : ContinuousOn Real.log (Set.Icc (2 : ℝ) x) :=
      Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le zero_lt_two ht.1).ne'
    refine (continuousOn_id.mul (hlog_cc.pow 2)).inv₀ (fun t ht => ?_) |>.neg
    exact mul_ne_zero (lt_of_lt_of_le zero_lt_two ht.1).ne'
      (pow_ne_zero 2 (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne')
  have hAbel := abel_summation_Ioc_one c zero_le_two hx hdiff hcont
  have hc_sum : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k = mertensOneSum t := by
    intro t
    unfold mertensOneSum
    rw [Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
  have hLHS : ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ =
      (2 : ℝ)⁻¹ + ∑ k ∈ Finset.Ioc ⌊(2 : ℝ)⌋₊ ⌊x⌋₊, c k * (Real.log k)⁻¹ := by
    have hfl2 : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
    have hfl_x : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr hx
    have hIcc : Finset.Icc 2 ⌊x⌋₊ = insert 2 (Finset.Ioc 2 ⌊x⌋₊) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hprime_sum : ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ =
        ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, c k * (Real.log k)⁻¹ := by
      rw [Nat.primesLE_eq_filter_Icc_two, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hp : k.Prime
      · have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hlogk : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < k))).ne'
        simp only [c, hp, ↓reduceIte]
        field_simp [hlogk]
      · simp [c, hp]
    rw [hfl2, hprime_sum, hIcc, Finset.sum_insert (by simp)]
    have h2val : c 2 * (Real.log ((2 : ℕ) : ℝ))⁻¹ = (2 : ℝ)⁻¹ := by
      simp only [c, Nat.prime_two, ↓reduceIte, Nat.cast_ofNat]
      field_simp [hlog2.ne']
    rw [h2val]
  have h2_term : mertensOneSum 2 * (Real.log 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [mertensOneSum, Nat.floor_ofNat]
    have hpl : Nat.primesLE 2 = {2} := by decide
    rw [hpl, Finset.sum_singleton]
    push_cast
    field_simp [hlog2.ne']
  have hAbel' : ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ =
      mertensOneSum x / Real.log x +
        ∫ t in (2 : ℝ)..x, mertensOneSum t / (t * Real.log t ^ 2) := by
    rw [hLHS, hAbel, hc_sum, hc_sum, h2_term]
    have hint_congr :
        ∫ t in (2 : ℝ)..x, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) *
            deriv (fun u : ℝ => (Real.log u)⁻¹) t =
          -∫ t in (2 : ℝ)..x, mertensOneSum t / (t * Real.log t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      rw [hc_sum, (hderiv t ht).deriv]
      ring
    rw [hint_congr]
    ring
  have hint_log : ∫ t in (2 : ℝ)..x, Real.log t / (t * Real.log t ^ 2) =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
    have hd : ∀ t ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun u : ℝ => Real.log (Real.log u)) (Real.log t / (t * Real.log t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht1 : 1 < t := lt_of_lt_of_le one_lt_two ht.1
      have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
      have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
      have hc := (Real.hasDerivAt_log hlogt).comp t (Real.hasDerivAt_log ht0)
      refine hc.congr_deriv ?_
      field_simp [ht0, hlogt]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (intervalIntegrable_log_div_mul_log_sq x hx)
  have hint_rem : IntervalIntegrable (fun t : ℝ => mertensOneRem t / (t * Real.log t ^ 2))
      volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact integrableOn_mertensOneRem_div.mono_set Set.Ioc_subset_Ioi_self
  have hint_log_int := intervalIntegrable_log_div_mul_log_sq x hx
  have hsum_split : ∫ t in (2 : ℝ)..x, mertensOneSum t / (t * Real.log t ^ 2) =
      (∫ t in (2 : ℝ)..x, Real.log t / (t * Real.log t ^ 2)) +
        ∫ t in (2 : ℝ)..x, mertensOneRem t / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_add hint_log_int hint_rem]
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [mertensOneRem, mertensOneSum]
    ring
  have hIoi_split : ∫ t in Set.Ioi (2 : ℝ), mertensOneRem t / (t * Real.log t ^ 2) =
      (∫ t in (2 : ℝ)..x, mertensOneRem t / (t * Real.log t ^ 2)) +
        ∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2) := by
    have h1 : IntegrableOn (fun t : ℝ => mertensOneRem t / (t * Real.log t ^ 2)) (Set.Ioc 2 x) :=
      integrableOn_mertensOneRem_div.mono_set Set.Ioc_subset_Ioi_self
    have h2 : IntegrableOn (fun t : ℝ => mertensOneRem t / (t * Real.log t ^ 2)) (Set.Ioi x) :=
      integrableOn_mertensOneRem_div.mono_set (Set.Ioi_subset_Ioi hx)
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2,
      intervalIntegral.integral_of_le hx]
  have hx_split : mertensOneSum x / Real.log x = 1 + mertensOneRem x / Real.log x := by
    dsimp only [mertensOneRem, mertensOneSum]
    field_simp [hlogx.ne']
    ring
  rw [hAbel', hx_split, hsum_split, hint_log, meisselMertensConstant, hIoi_split]
  ring

/-- Explicit `O(1 / log x)` error bound for Mertens' second theorem (`2 ≤ x`):
`|∑_{p ≤ x} 1 / p - (log (log x) + M)| ≤ (2 * mertensOneBound) / log x`. -/
theorem abs_mertens_two_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - (Real.log (Real.log x) + meisselMertensConstant)| ≤
      (2 * mertensOneBound) / Real.log x := by
  have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hdiff : ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ -
        (Real.log (Real.log x) + meisselMertensConstant) =
      mertensOneRem x / Real.log x - ∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2) := by
    rw [sum_inv_primes_eq_abel hx]
    ring
  have h1 : |mertensOneRem x / Real.log x| ≤ mertensOneBound / Real.log x := by
    rw [abs_div, abs_of_pos hlogx]
    exact div_le_div_of_nonneg_right (abs_mertensOneRem_le (by linarith)) hlogx.le
  have htail := integrableOn_inv_mul_log_sq_Ioi hx
  have h_int : IntegrableOn (fun t : ℝ => mertensOneRem t / (t * Real.log t ^ 2)) (Set.Ioi x) :=
    integrableOn_mertensOneRem_div.mono_set (Set.Ioi_subset_Ioi hx)
  have h2 : |∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2)| ≤
      mertensOneBound / Real.log x := by
    have hnorm : ‖∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2)‖ ≤
        ∫ t in Set.Ioi x, ‖mertensOneRem t / (t * Real.log t ^ 2)‖ :=
      norm_integral_le_integral_norm _
    have hmono : ∫ t in Set.Ioi x, ‖mertensOneRem t / (t * Real.log t ^ 2)‖ ≤
        ∫ t in Set.Ioi x, mertensOneBound * (t * Real.log t ^ 2)⁻¹ := by
      refine setIntegral_mono_on h_int.norm (htail.1.const_mul mertensOneBound) measurableSet_Ioi
        fun t ht => ?_
      have ht1 : 1 < t := hx1.trans ht
      have hden_pos : 0 < t * Real.log t ^ 2 :=
        mul_pos (zero_lt_one.trans ht1) (sq_pos_of_pos (Real.log_pos ht1))
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (abs_mertensOneRem_le (by linarith))
        (inv_nonneg.mpr hden_pos.le)
    have heval : ∫ t in Set.Ioi x, mertensOneBound * (t * Real.log t ^ 2)⁻¹ =
        mertensOneBound / Real.log x := by
      rw [integral_const_mul, htail.2, div_eq_mul_inv]
    rw [← Real.norm_eq_abs]
    exact hnorm.trans (hmono.trans_eq heval)
  rw [hdiff]
  calc |mertensOneRem x / Real.log x - ∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2)|
      ≤ |mertensOneRem x / Real.log x| +
          |∫ t in Set.Ioi x, mertensOneRem t / (t * Real.log t ^ 2)| := abs_sub _ _
    _ ≤ mertensOneBound / Real.log x + mertensOneBound / Real.log x := add_le_add h1 h2
    _ = (2 * mertensOneBound) / Real.log x := by ring

/-- **Mertens' second theorem** (Big-O form):
`∑_{p ≤ x} 1 / p - (log (log x) + M) = O(1 / log x)` as `x → ∞`. -/
theorem mertens_second_theorem :
    (fun x : ℝ => ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ -
        (Real.log (Real.log x) + meisselMertensConstant)) =O[atTop]
      (fun x : ℝ => (Real.log x)⁻¹) := by
  refine isBigO_iff.mpr ⟨2 * mertensOneBound, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le one_lt_two hx)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr hlogx.le), ← div_eq_mul_inv]
  exact abs_mertens_two_sub_le hx

/-- **Mertens' second theorem** (asymptotic equivalence form):
`∑_{p ≤ x} 1 / p ~ log (log x)` as `x → ∞`. -/
theorem mertens_second_theorem_isEquivalent :
    (fun x : ℝ => ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) ~[atTop]
      (fun x : ℝ => Real.log (Real.log x)) := by
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hrem_tendsto : Tendsto (fun x : ℝ =>
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - Real.log (Real.log x))
      atTop (𝓝 meisselMertensConstant) := by
    have h0 : Tendsto (fun x : ℝ => ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ -
        (Real.log (Real.log x) + meisselMertensConstant)) atTop (𝓝 0) :=
      mertens_second_theorem.trans_tendsto Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa [← sub_sub, sub_add_cancel] using h0.add_const meisselMertensConstant
  have hdiv : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - Real.log (Real.log x)) / Real.log (Real.log x))
      atTop (𝓝 0) :=
    hrem_tendsto.div_atTop hloglog
  have hdiv1 : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - Real.log (Real.log x)) / Real.log (Real.log x) + 1)
      atTop (𝓝 1) := by
    simpa using hdiv.add_const 1
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · refine hdiv1.congr' ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlog : 1 < Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith))
    have hll : Real.log (Real.log x) ≠ 0 := (Real.log_pos hlog).ne'
    simp only [Pi.div_apply]
    field_simp [hll]
    ring
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlog : 1 < Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith))
    exact (Real.log_pos hlog).ne'

/-! ### Mertens' Constant Identity and Mertens' Third Theorem -/

private lemma neg_log_one_sub_sub_nonneg {u : ℝ} (hu : u < 1) : 0 ≤ -Real.log (1 - u) - u := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hu)
  linarith

private lemma neg_log_one_sub_sub_le_sq {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    -Real.log (1 - u) - u ≤ u ^ 2 := by
  let h : ℝ → ℝ := fun t => t ^ 2 + t + Real.log (1 - t)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      HasDerivAt h (2 * t + 1 - (1 - t)⁻¹) t := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2]
    have hd1 : HasDerivAt (fun x : ℝ => x ^ 2 + x) (2 * t + 1) t := by
      convert (hasDerivAt_pow 2 t).add (hasDerivAt_id' t) using 1
      norm_num
    have hd2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((1 - t)⁻¹ * (-1)) t := by
      have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
        convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t) using 1
        simp
      exact (Real.hasDerivAt_log h1t).comp t hsub
    convert hd1.add hd2 using 1
    ring
  have hmono : MonotoneOn h (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
    · have h1sub_cont : ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) (1 / 2)) :=
        continuousOn_const.sub continuousOn_id
      have hlog_cont : ContinuousOn (fun t : ℝ => Real.log (1 - t)) (Set.Icc (0 : ℝ) (1 / 2)) :=
        Real.continuousOn_log.comp h1sub_cont fun t ht => (by linarith [ht.2] : 1 - t ≠ 0)
      exact (continuousOn_pow 2 |>.add continuousOn_id).add hlog_cont
    · intro t ht
      have hmem : t ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset ht
      exact (hderiv t hmem).differentiableAt.differentiableWithinAt
    · intro t ht
      have hmem : t ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset ht
      rw [(hderiv t hmem).deriv]
      have h1t : 0 < 1 - t := by linarith [hmem.2]
      have hnum : 0 ≤ t * (1 - 2 * t) := mul_nonneg hmem.1 (by linarith [hmem.2])
      have heq : 2 * t + 1 - (1 - t)⁻¹ = t * (1 - 2 * t) / (1 - t) := by
        field_simp [h1t.ne']
        ring
      rw [heq]
      exact div_nonneg hnum h1t.le
  have hval := hmono (Set.left_mem_Icc.mpr (by norm_num)) ⟨hu0, hu⟩ hu0
  have h0 : h 0 = 0 := by simp [h]
  rw [h0] at hval
  dsimp [h] at hval
  linarith

private lemma neg_log_one_sub_rpow_bounds {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    0 ≤ -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) ∧
      -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-2 : ℝ) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hp_two : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hpow_le : (p : ℝ) ^ (-s) ≤ 1 / 2 := by
    rw [Real.rpow_neg hp_pos.le]
    refine inv_le_of_inv_le₀ (by norm_num) ?_
    calc ((1 / 2 : ℝ)⁻¹) = (2 : ℝ) := by norm_num
      _ ≤ (p : ℝ) ^ (1 : ℝ) := by simpa using hp_two
      _ ≤ (p : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have h_nn := neg_log_one_sub_sub_nonneg (lt_of_le_of_lt hpow_le (by norm_num))
  have h_le := neg_log_one_sub_sub_le_sq (Real.rpow_nonneg hp_pos.le _) hpow_le
  have h_p2 : ((p : ℝ) ^ (-s)) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  exact ⟨h_nn, h_le.trans h_p2⟩

private lemma summable_neg_log_one_sub_rpow_sub {s : ℝ} (hs : 1 ≤ s) :
    Summable fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) := by
  have hp2 : Summable fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  exact hp2.of_nonneg_of_le (fun p => (neg_log_one_sub_rpow_bounds hs p).1)
    (fun p => (neg_log_one_sub_rpow_bounds hs p).2)

/-- Summability of `log (1 - 1/p) + 1/p` over all primes `p`. -/
theorem summable_prime_log_one_sub_add_inv :
    Summable fun p : Nat.Primes => Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹ := by
  rw [← summable_neg_iff]
  refine (summable_neg_log_one_sub_rpow_sub (s := 1) le_rfl).congr fun p => ?_
  rw [Real.rpow_neg_one]
  ring

private lemma real_log_riemannZeta_eq_tsum {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re =
      ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have heuler := riemannZeta_eulerProduct_exp_log hsC
  have him : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
  have hlog_eq : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) =
        ((-Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
    intro p
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have hpow_lt1 : (p : ℝ) ^ (-s) < 1 := by
      rw [Real.rpow_neg hp_pos.le]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp_gt1 (by linarith))
    have h1sub_pos : 0 < 1 - (p : ℝ) ^ (-s) := sub_pos.mpr hpow_lt1
    have hcp : (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hp_pos.le]
    rw [hcp, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log h1sub_pos.le,
      Complex.ofReal_neg]
  have htsum_C : ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) =
      ((∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
    rw [tsum_congr hlog_eq, Complex.ofReal_tsum]
  rw [htsum_C, ← Complex.ofReal_exp] at heuler
  have hz_eq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hz_eq, Complex.ofReal_inj] at heuler
  rw [← heuler, Real.log_exp]

private lemma integrableOn_prime_inv_sum_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ => (∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹) * t ^ (-s))
      (Set.Ioi (2 : ℝ)) := by
  let S : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹
  have hmono : Monotone S := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hab))
      fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hmeas : Measurable fun t : ℝ => S t * t ^ (-s) :=
    hmono.measurable.mul (measurable_id.pow_const (-s))
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-s)) (Set.Ioi (2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_two
  have h2 : IntegrableOn (fun t : ℝ => (2 / (s - 1)) * t ^ (-(s + 1) / 2)) (Set.Ioi (2 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_two).const_mul _
  refine Integrable.mono' (h1.add h2) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := by linarith [show (2 : ℝ) < t from ht]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hS_nn : 0 ≤ S t := Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hS_le : S t ≤ 1 + Real.log t := by
    calc S t = ∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹ := rfl
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (n : ℝ)⁻¹ := by
          rw [Nat.primesLE_eq_filter_Icc_one]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ 1 + Real.log t := sum_inv_le_one_add_log ht1
  have hlog_le : Real.log t ≤ (2 / (s - 1)) * t ^ ((s - 1) / 2) := by
    have h := Real.log_le_rpow_div ht0.le (by linarith : (0 : ℝ) < (s - 1) / 2)
    refine h.trans_eq ?_
    field_simp [(sub_pos.mpr hs).ne']
  have hrhs : (1 + (2 / (s - 1)) * t ^ ((s - 1) / 2)) * t ^ (-s) =
      t ^ (-s) + (2 / (s - 1)) * t ^ (-(s + 1) / 2) := by
    rw [add_mul, one_mul, mul_assoc, ← Real.rpow_add ht0]
    congr 2
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hS_nn (Real.rpow_nonneg ht0.le _)),
    Pi.add_apply, ← hrhs]
  exact mul_le_mul_of_nonneg_right (hS_le.trans (by linarith)) (Real.rpow_nonneg ht0.le _)

private lemma tsum_prime_rpow_eq_abel_integral {s : ℝ} (hs : 1 < s) :
    ∑' p : Nat.Primes, (p : ℝ) ^ (-s) =
      (s - 1) * ∫ t in Set.Ioi (2 : ℝ),
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹) * t ^ (-s) := by
  let S : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹
  let c : ℕ → ℝ := fun n => if n.Prime then (n : ℝ)⁻¹ else 0
  have hS_eq : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k = S t := by
    intro t
    dsimp [S]
    rw [Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
  have hs1 : 0 < s - 1 := sub_pos.mpr hs
  have hS_bound : ∀ t : ℝ, 1 ≤ t → S t ≤ 1 + Real.log t := by
    intro t ht
    calc S t = ∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹ := rfl
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (n : ℝ)⁻¹ := by
          rw [Nat.primesLE_eq_filter_Icc_one]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ 1 + Real.log t := sum_inv_le_one_add_log ht
  have hS_int : IntegrableOn (fun t : ℝ => S t * t ^ (-s)) (Set.Ioi (2 : ℝ)) :=
    integrableOn_prime_inv_sum_mul_rpow hs
  have hAbel_N : ∀ N : ℕ, 2 ≤ N →
      ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-s) =
        S N * (N : ℝ) ^ (-(s - 1)) + (s - 1) * ∫ t in (2 : ℝ)..N, S t * t ^ (-s) := by
    intro N hN
    have h1N : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) N,
        HasDerivAt (fun u : ℝ => u ^ (-(s - 1))) (-(s - 1) * t ^ (-s)) t := by
      intro t ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_one ht.1).ne'
      convert (Real.hasDerivAt_rpow_const (p := -(s - 1)) (Or.inl ht0)) using 1
      ring_nf
    have hcont : ContinuousOn (fun t : ℝ => -(s - 1) * t ^ (-s)) (Set.Icc (1 : ℝ) N) := by
      refine ContinuousOn.const_mul (continuousOn_of_forall_continuousAt fun t ht => ?_) _
      exact Real.continuousAt_rpow_const t (-s) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
    have hAbel := abel_summation_Icc_one_hasDerivAt c h1N hderiv hcont
    rw [Nat.floor_natCast] at hAbel
    have hLHS : ∑ k ∈ Finset.Icc 1 N, c k * (k : ℝ) ^ (-(s - 1)) =
        ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-s) := by
      rw [Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      by_cases hp : k.Prime
      · simp only [c, hp, ↓reduceIte]
        rw [← Real.rpow_neg_one, ← Real.rpow_add hk0]
        congr 1
        ring
      · simp [c, hp]
    have hint_12 : ∫ t in (1 : ℝ)..2, S t * t ^ (-s) = 0 := by
      rw [intervalIntegral.integral_of_le one_le_two, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      have hfl : ⌊t⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith [ht.1])]
        exact ⟨by exact_mod_cast ht.1.le, by norm_num; exact ht.2⟩
      simp [S, hfl]
    have hint_split : ∫ t in (1 : ℝ)..N, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (-(s - 1) * t ^ (-s)) =
        -(s - 1) * ∫ t in (2 : ℝ)..N, S t * t ^ (-s) := by
      have hcongr : ∫ t in (1 : ℝ)..N, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (-(s - 1) * t ^ (-s)) =
          -(s - 1) * ∫ t in (1 : ℝ)..N, S t * t ^ (-s) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [hS_eq t]
        ring
      have hi12 : IntervalIntegrable (fun t : ℝ => S t * t ^ (-s)) volume 1 2 := by
        refine (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo fun t ht => ?_
        rw [Set.uIoo_of_le one_le_two] at ht
        have hfl : ⌊t⌋₊ = 1 := by
          rw [Nat.floor_eq_iff (by linarith [ht.1])]
          exact ⟨by exact_mod_cast ht.1.le, by norm_num; exact ht.2⟩
        simp [S, hfl]
      have hi2N : IntervalIntegrable (fun t : ℝ => S t * t ^ (-s)) volume 2 N := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2N]
        exact hS_int.mono_set Set.Ioc_subset_Ioi_self
      rw [hcongr, ← intervalIntegral.integral_add_adjacent_intervals hi12 hi2N, hint_12, zero_add]
    have hSN : ∑ k ∈ Finset.Icc 1 N, c k = S N := by
      simpa [Nat.floor_natCast] using hS_eq N
    rw [hLHS, hint_split, hSN] at hAbel
    linarith
  have hlim_LHS : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-s))
      atTop (𝓝 (∑' p : Nat.Primes, (p : ℝ) ^ (-s))) := by
    have hsum_nat : Summable fun k : ℕ => if k.Prime then (k : ℝ) ^ (-s) else 0 :=
      (Nat.Primes.summable_iff_summable_ite _).mp (Nat.Primes.summable_rpow.mpr (by linarith))
    have ht_eq : ∑' k : ℕ, (if k.Prime then (k : ℝ) ^ (-s) else 0) =
        ∑' p : Nat.Primes, (p : ℝ) ^ (-s) :=
      (Nat.Primes.tsum_eq_tsum_ite (fun p : ℕ => (p : ℝ) ^ (-s))).symm
    have hlim_range : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
          if k.Prime then (k : ℝ) ^ (-s) else 0)
        atTop (𝓝 (∑' p : Nat.Primes, (p : ℝ) ^ (-s))) := by
      rw [← ht_eq]
      exact (hsum_nat.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine hlim_range.congr fun N => ?_
    rw [Nat.primesLE_eq_filter_range, Finset.sum_filter]
  have hlim_RHS : Tendsto (fun N : ℕ =>
        S N * (N : ℝ) ^ (-(s - 1)) + (s - 1) * ∫ t in (2 : ℝ)..N, S t * t ^ (-s))
      atTop (𝓝 ((s - 1) * ∫ t in Set.Ioi (2 : ℝ), S t * t ^ (-s))) := by
    have htail_0 : Tendsto (fun N : ℕ => S N * (N : ℝ) ^ (-(s - 1))) atTop (𝓝 0) := by
      have hlog_0 : Tendsto (fun N : ℕ => (1 + Real.log N) * (N : ℝ) ^ (-(s - 1))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(s - 1))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop hs1).comp tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (s - 1)) atTop (𝓝 0) :=
          (isLittleO_log_rpow_atTop hs1).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
        have h12 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(s - 1)) + Real.log N / (N : ℝ) ^ (s - 1))
            atTop (𝓝 0) := by
          simpa using h1.add h2
        refine h12.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
        rw [Real.rpow_neg hN_pos.le]
        ring
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog_0 ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with N _
        exact mul_nonneg (Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      · filter_upwards [eventually_ge_atTop 1] with N hN
        exact mul_le_mul_of_nonneg_right (hS_bound N (by exact_mod_cast hN))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    have hint_lim : Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, S t * t ^ (-s)) atTop
        (𝓝 (∫ t in Set.Ioi (2 : ℝ), S t * t ^ (-s))) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 2 hS_int tendsto_natCast_atTop_atTop
    simpa using htail_0.add (hint_lim.const_mul (s - 1))
  have hcongr : (fun N : ℕ => ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-s)) =ᶠ[atTop]
      (fun N : ℕ => S N * (N : ℝ) ^ (-(s - 1)) + (s - 1) * ∫ t in (2 : ℝ)..N, S t * t ^ (-s)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact hAbel_N N hN
  exact tendsto_nhds_unique hlim_LHS (hlim_RHS.congr' hcongr.symm)

private lemma integrableOn_log_log_Ioc_one_two :
    IntegrableOn (fun t : ℝ => Real.log (Real.log t)) (Set.Ioc (1 : ℝ) 2) := by
  have hbase : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-2 : ℝ))
      (Set.Ioc (1 : ℝ) 2) :=
    (Real.integrableOn_log_log_mul_rpow (s := 2) one_lt_two).mono_set Set.Ioc_subset_Ioi_self
  have hbdd : ContinuousOn (fun t : ℝ => t ^ (2 : ℝ)) (Set.Icc (1 : ℝ) 2) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (zero_lt_one.trans_le ht.1).ne')
  have hmul := hbase.mul_continuousOn_of_subset hbdd measurableSet_Ioc isCompact_Icc
    Set.Ioc_subset_Icc_self
  refine hmul.congr_fun (fun t ht => ?_) measurableSet_Ioc
  have ht0 : 0 < t := zero_lt_one.trans ht.1
  dsimp only
  rw [mul_assoc, ← Real.rpow_add ht0]
  norm_num

/-- **Mertens' constant identity**:
`meisselMertensConstant - ∑' p : Nat.Primes, (log (1 - 1 / p) + 1 / p) = γ`. -/
theorem meisselMertensConstant_sub_tsum_eq_eulerMascheroni :
    meisselMertensConstant -
      ∑' p : Nat.Primes, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) =
        Real.eulerMascheroniConstant := by
  let S : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, (p : ℝ)⁻¹
  let E : ℝ → ℝ := fun t => S t - (Real.log (Real.log t) + meisselMertensConstant)
  have hE_bound : ∀ t : ℝ, 2 ≤ t → |E t| ≤ (2 * mertensOneBound) / Real.log t :=
    fun _ ht => abs_mertens_two_sub_le ht
  have h_sum_lim :
      Tendsto (fun s : ℝ => (∑' p : Nat.Primes, (p : ℝ) ^ (-s)) + Real.log (s - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 (meisselMertensConstant - Real.eulerMascheroniConstant)) := by
    have hev : (fun s : ℝ => (∑' p : Nat.Primes, (p : ℝ) ^ (-s)) + Real.log (s - 1)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun s : ℝ => (meisselMertensConstant * (2 : ℝ) ^ (1 - s) - Real.eulerMascheroniConstant) -
          (s - 1) * (∫ t in Set.Ioc (1 : ℝ) 2, Real.log (Real.log t) * t ^ (-s)) +
          (s - 1) * (∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s))) := by
      filter_upwards [eventually_mem_nhdsWithin] with s (hs : 1 < s)
      have hs1 : 0 < s - 1 := sub_pos.mpr hs
      have h_ll_1 : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-s)) (Set.Ioc 1 2) :=
        (Real.integrableOn_log_log_mul_rpow hs).mono_set (fun _ ht => ht.1)
      have h_ll_2 : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-s)) (Set.Ioi 2) :=
        (Real.integrableOn_log_log_mul_rpow hs).mono_set (Set.Ioi_subset_Ioi one_le_two)
      have h_ll_split : ∫ t in Set.Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-s) =
          (∫ t in Set.Ioc (1 : ℝ) 2, Real.log (Real.log t) * t ^ (-s)) +
            ∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-s) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi one_le_two,
          setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h_ll_1 h_ll_2]
      have h_M_int : IntegrableOn (fun t : ℝ => meisselMertensConstant * t ^ (-s)) (Set.Ioi 2) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_two).const_mul _
      have h_M_eval : (s - 1) * ∫ t in Set.Ioi (2 : ℝ), meisselMertensConstant * t ^ (-s) =
          meisselMertensConstant * (2 : ℝ) ^ (1 - s) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_two]
        have hexp : (-s + 1 : ℝ) = 1 - s := by ring
        rw [hexp]
        field_simp [(by linarith : 1 - s ≠ 0)]
        ring
      have hS_int : IntegrableOn (fun t : ℝ => S t * t ^ (-s)) (Set.Ioi 2) :=
        integrableOn_prime_inv_sum_mul_rpow hs
      have hE_eq : (fun t : ℝ => E t * t ^ (-s)) =
          fun t : ℝ => S t * t ^ (-s) - (Real.log (Real.log t) * t ^ (-s) +
            meisselMertensConstant * t ^ (-s)) := by
        ext t
        dsimp [E]
        ring
      have h_S_split : ∫ t in Set.Ioi (2 : ℝ), S t * t ^ (-s) =
          (∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-s)) +
            (∫ t in Set.Ioi (2 : ℝ), meisselMertensConstant * t ^ (-s)) +
            ∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s) := by
        have hE_int : IntegrableOn (fun t : ℝ => E t * t ^ (-s)) (Set.Ioi 2) := by
          rw [hE_eq]
          exact hS_int.sub (h_ll_2.add h_M_int)
        have hint12 : ∫ t in Set.Ioi (2 : ℝ),
            (Real.log (Real.log t) * t ^ (-s) + meisselMertensConstant * t ^ (-s)) =
            (∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-s)) +
              ∫ t in Set.Ioi (2 : ℝ), meisselMertensConstant * t ^ (-s) :=
          integral_add h_ll_2 h_M_int
        have h1 : (fun t : ℝ => S t * t ^ (-s)) =
            (fun t : ℝ => Real.log (Real.log t) * t ^ (-s) + meisselMertensConstant * t ^ (-s)) +
              fun t : ℝ => E t * t ^ (-s) := by
          ext t
          dsimp [E]
          ring
        have hint123 := integral_add (h_ll_2.add h_M_int) hE_int
        have heq1 : (∫ t in Set.Ioi (2 : ℝ), S t * t ^ (-s)) =
            (∫ t in Set.Ioi (2 : ℝ),
              (Real.log (Real.log t) * t ^ (-s) + meisselMertensConstant * t ^ (-s))) +
              ∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s) := by
          rw [h1]
          exact hint123
        rw [heq1, hint12]
      have hgam := Real.eulerMascheroniConstant_eq_neg_integral_log_log hs
      rw [h_ll_split, mul_add] at hgam
      have htsum := tsum_prime_rpow_eq_abel_integral hs
      change ∑' p : Nat.Primes, (p : ℝ) ^ (-s) = (s - 1) * ∫ t in Set.Ioi (2 : ℝ), S t * t ^ (-s)
        at htsum
      rw [htsum, h_S_split]
      have hgam' : (s - 1) * (∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-s)) +
            Real.log (s - 1) =
          -Real.eulerMascheroniConstant -
            (s - 1) * (∫ t in Set.Ioc (1 : ℝ) 2, Real.log (Real.log t) * t ^ (-s)) := by
        linarith
      linarith [hgam', h_M_eval]
    have h_lim1 : Tendsto (fun s : ℝ =>
        meisselMertensConstant * (2 : ℝ) ^ (1 - s) - Real.eulerMascheroniConstant)
        (𝓝[>] (1 : ℝ)) (𝓝 (meisselMertensConstant - Real.eulerMascheroniConstant)) := by
      have hc : ContinuousAt (fun s : ℝ =>
          meisselMertensConstant * (2 : ℝ) ^ (1 - s) - Real.eulerMascheroniConstant) 1 := by
        fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h_lim2 : Tendsto (fun s : ℝ =>
        (s - 1) * ∫ t in Set.Ioc (1 : ℝ) 2, Real.log (Real.log t) * t ^ (-s))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      let B : ℝ := ∫ t in Set.Ioc (1 : ℝ) 2, ‖Real.log (Real.log t)‖
      have hB_nn : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
      have h_upper : Tendsto (fun s : ℝ => (s - 1) * B) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
        have hc : ContinuousAt (fun s : ℝ => (s - 1) * B) 1 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
        (Eventually.of_forall fun _ => norm_nonneg _) ?_
      filter_upwards [eventually_mem_nhdsWithin] with s (hs : 1 < s)
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hs)]
      refine mul_le_mul_of_nonneg_left ?_ (sub_pos.mpr hs).le
      have h_int : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-s)) (Set.Ioc 1 2) :=
        (Real.integrableOn_log_log_mul_rpow hs).mono_set (fun _ ht => ht.1)
      have hnorm : ‖∫ t in Set.Ioc (1 : ℝ) 2, Real.log (Real.log t) * t ^ (-s)‖ ≤
          ∫ t in Set.Ioc (1 : ℝ) 2, ‖Real.log (Real.log t) * t ^ (-s)‖ :=
        norm_integral_le_integral_norm _
      refine hnorm.trans ?_
      refine setIntegral_mono_on h_int.norm integrableOn_log_log_Ioc_one_two.norm measurableSet_Ioc
        fun t ht => ?_
      have ht1 : 1 ≤ t := ht.1.le
      have hpow_le : ‖t ^ (-s)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht1) _),
          Real.rpow_neg (zero_le_one.trans ht1)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow ht1 (by linarith))
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hpow_le
    have h_lim3 : Tendsto (fun s : ℝ => (s - 1) * ∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      let C₂ : ℝ := 2 * mertensOneBound
      have hC₂_pos : 0 < C₂ := mul_pos two_pos mertensOneBound_pos
      let M₀ : ℝ := max 2 (Real.exp (2 * C₂ / ε))
      have hM₀_2 : 2 ≤ M₀ := le_max_left _ _
      have hM₀_1 : 1 < M₀ := lt_of_lt_of_le one_lt_two hM₀_2
      have hM₀_exp : Real.exp (2 * C₂ / ε) ≤ M₀ := le_max_right _ _
      have hM₀_log : 2 * C₂ / ε ≤ Real.log M₀ := by
        rw [← Real.log_exp (2 * C₂ / ε)]
        exact Real.log_le_log (Real.exp_pos _) hM₀_exp
      have htail_bound : C₂ / Real.log M₀ ≤ ε / 2 := by
        have hlogM_pos : 0 < Real.log M₀ := Real.log_pos hM₀_1
        rw [div_le_iff₀ hlogM_pos]
        have h1 : 2 * C₂ ≤ Real.log M₀ * ε := (div_le_iff₀ hε).mp hM₀_log
        linarith
      have hE_meas : Measurable E := by
        have hmono : Monotone S := fun _ _ hab =>
          Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hab))
            fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
        exact hmono.measurable.sub ((Real.measurable_log.comp Real.measurable_log).add measurable_const)
      let K : ℝ := (C₂ / Real.log 2) * (M₀ - 2) + 1
      have hK_pos : 0 < K := by
        have h1 : 0 ≤ (C₂ / Real.log 2) * (M₀ - 2) :=
          mul_nonneg (div_nonneg hC₂_pos.le (Real.log_pos one_lt_two).le) (by linarith)
        linarith
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [div_pos hε (mul_pos two_pos hK_pos)] :
          (1 : ℝ) < 1 + ε / (2 * K)))] with s (hs : 1 < s) (hs_ub : s < 1 + ε / (2 * K))
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (sub_pos.mpr hs)]
      have hE_int : IntegrableOn (fun t : ℝ => E t * t ^ (-s)) (Set.Ioi 2) := by
        have hdom := (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_two).const_mul
          (C₂ / Real.log 2)
        refine Integrable.mono' hdom
          (hE_meas.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht2 : 2 ≤ t := le_of_lt ht
        have ht0 : 0 < t := zero_lt_two.trans_le ht2
        have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht2
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        have hEt : |E t| ≤ C₂ / Real.log 2 := (hE_bound t ht2).trans (by gcongr)
        exact mul_le_mul_of_nonneg_right hEt (Real.rpow_nonneg ht0.le _)
      have h1 : IntegrableOn (fun t : ℝ => E t * t ^ (-s)) (Set.Ioc 2 M₀) :=
        hE_int.mono_set Set.Ioc_subset_Ioi_self
      have h2 : IntegrableOn (fun t : ℝ => E t * t ^ (-s)) (Set.Ioi M₀) :=
        hE_int.mono_set (Set.Ioi_subset_Ioi hM₀_2)
      have hsplit : ∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s) =
          (∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)) +
            ∫ t in Set.Ioi M₀, E t * t ^ (-s) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi hM₀_2,
          setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]
      have h_left : |∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)| ≤ (C₂ / Real.log 2) * (M₀ - 2) := by
        have hnorm : ‖∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)‖ ≤
            ∫ t in Set.Ioc (2 : ℝ) M₀, ‖E t * t ^ (-s)‖ :=
          norm_integral_le_integral_norm _
        have hconst : IntegrableOn (fun _ : ℝ => C₂ / Real.log 2) (Set.Ioc 2 M₀) := by
          simp
        have hmono : ∫ t in Set.Ioc (2 : ℝ) M₀, ‖E t * t ^ (-s)‖ ≤
            ∫ _t in Set.Ioc (2 : ℝ) M₀, C₂ / Real.log 2 := by
          refine setIntegral_mono_on h1.norm hconst measurableSet_Ioc fun t ht => ?_
          have ht2 : 2 ≤ t := ht.1.le
          have ht1 : 1 ≤ t := by linarith
          have ht0 : 0 < t := zero_lt_two.trans_le ht2
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
          have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht2
          have hEt : |E t| ≤ C₂ / Real.log 2 := (hE_bound t ht2).trans (by gcongr)
          have hpow : t ^ (-s) ≤ 1 := by
            rw [Real.rpow_neg ht0.le]
            exact inv_le_one_of_one_le₀ (Real.one_le_rpow ht1 (by linarith))
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
          exact (mul_le_mul_of_nonneg_right hEt (Real.rpow_nonneg ht0.le _)).trans
            (mul_le_of_le_one_right (div_nonneg hC₂_pos.le hlog2_pos.le) hpow)
        have heval : ∫ _t in Set.Ioc (2 : ℝ) M₀, C₂ / Real.log 2 = (C₂ / Real.log 2) * (M₀ - 2) := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hM₀_2, mul_comm]
        rw [← Real.norm_eq_abs]
        exact hnorm.trans (hmono.trans_eq heval)
      have h_right : (s - 1) * |∫ t in Set.Ioi M₀, E t * t ^ (-s)| ≤ ε / 2 := by
        have hnorm : ‖∫ t in Set.Ioi M₀, E t * t ^ (-s)‖ ≤
            ∫ t in Set.Ioi M₀, ‖E t * t ^ (-s)‖ :=
          norm_integral_le_integral_norm _
        have hdom : IntegrableOn (fun t : ℝ => (C₂ / Real.log M₀) * t ^ (-s)) (Set.Ioi M₀) :=
          (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (zero_lt_one.trans hM₀_1)).const_mul _
        have hmono : ∫ t in Set.Ioi M₀, ‖E t * t ^ (-s)‖ ≤
            ∫ t in Set.Ioi M₀, (C₂ / Real.log M₀) * t ^ (-s) := by
          refine setIntegral_mono_on h2.norm hdom measurableSet_Ioi fun t ht => ?_
          have htM : M₀ ≤ t := le_of_lt ht
          have ht2 : 2 ≤ t := hM₀_2.trans htM
          have ht0 : 0 < t := zero_lt_two.trans_le ht2
          have hlogM_pos : 0 < Real.log M₀ := Real.log_pos hM₀_1
          have hlog_le : Real.log M₀ ≤ Real.log t := Real.log_le_log (zero_lt_one.trans hM₀_1) htM
          have hEt : |E t| ≤ C₂ / Real.log M₀ := (hE_bound t ht2).trans (by gcongr)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
          exact mul_le_mul_of_nonneg_right hEt (Real.rpow_nonneg ht0.le _)
        have heval : ∫ t in Set.Ioi M₀, (C₂ / Real.log M₀) * t ^ (-s) =
            (C₂ / Real.log M₀) * (M₀ ^ (1 - s) / (s - 1)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (zero_lt_one.trans hM₀_1)]
          have hexp : (-s + 1 : ℝ) = 1 - s := by ring
          rw [hexp]
          field_simp [(by linarith : 1 - s ≠ 0), (sub_pos.mpr hs).ne']
          ring
        have hM_pow : M₀ ^ (1 - s) ≤ 1 := by
          rw [show (1 - s : ℝ) = -(s - 1) by ring, Real.rpow_neg (zero_lt_one.trans hM₀_1).le]
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow hM₀_1.le (sub_pos.mpr hs).le)
        have h_abs : |∫ t in Set.Ioi M₀, E t * t ^ (-s)| ≤
            (C₂ / Real.log M₀) * (M₀ ^ (1 - s) / (s - 1)) := by
          rw [← Real.norm_eq_abs]
          exact hnorm.trans (hmono.trans_eq heval)
        calc (s - 1) * |∫ t in Set.Ioi M₀, E t * t ^ (-s)|
            ≤ (s - 1) * ((C₂ / Real.log M₀) * (M₀ ^ (1 - s) / (s - 1))) :=
              mul_le_mul_of_nonneg_left h_abs (sub_pos.mpr hs).le
          _ = (C₂ / Real.log M₀) * M₀ ^ (1 - s) := by
              field_simp [(sub_pos.mpr hs).ne']
          _ ≤ (C₂ / Real.log M₀) * 1 :=
              mul_le_mul_of_nonneg_left hM_pow (div_nonneg hC₂_pos.le (Real.log_pos hM₀_1).le)
          _ ≤ ε / 2 := by linarith
      have h_abs_split : |∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s)| ≤
          |∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)| +
            |∫ t in Set.Ioi M₀, E t * t ^ (-s)| := by
        rw [hsplit]
        exact abs_add_le _ _
      have hs_lt_K : (s - 1) * K < ε / 2 := by
        have h1 : s - 1 < ε / (2 * K) := by linarith
        calc (s - 1) * K < (ε / (2 * K)) * K := mul_lt_mul_of_pos_right h1 hK_pos
          _ = ε / 2 := by field_simp [hK_pos.ne']
      have h_left_mul : (s - 1) * |∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)| < ε / 2 := by
        calc (s - 1) * |∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)|
            ≤ (s - 1) * ((C₂ / Real.log 2) * (M₀ - 2)) :=
              mul_le_mul_of_nonneg_left h_left (sub_pos.mpr hs).le
          _ ≤ (s - 1) * K := by
              refine mul_le_mul_of_nonneg_left (by simp [K]) (sub_pos.mpr hs).le
          _ < ε / 2 := hs_lt_K
      calc (s - 1) * |∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s)|
          ≤ (s - 1) * (|∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)| +
              |∫ t in Set.Ioi M₀, E t * t ^ (-s)|) :=
            mul_le_mul_of_nonneg_left h_abs_split (sub_pos.mpr hs).le
        _ = (s - 1) * |∫ t in Set.Ioc (2 : ℝ) M₀, E t * t ^ (-s)| +
              (s - 1) * |∫ t in Set.Ioi M₀, E t * t ^ (-s)| := by ring
        _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h_left_mul h_right
        _ = ε := by ring
    have hsum_lim : Tendsto (fun s : ℝ =>
        meisselMertensConstant * (2 : ℝ) ^ (1 - s) - Real.eulerMascheroniConstant -
          (s - 1) * (∫ t in Set.Ioc (1 : ℝ) 2, Real.log (Real.log t) * t ^ (-s)) +
          (s - 1) * (∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s)))
        (𝓝[>] (1 : ℝ)) (𝓝 (meisselMertensConstant - Real.eulerMascheroniConstant)) := by
      simpa using (h_lim1.sub h_lim2).add h_lim3
    exact hsum_lim.congr' (by simpa using hev.symm)
  have h_tail_lim :
      Tendsto (fun s : ℝ =>
          ∑' p : Nat.Primes, (-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)))
        (𝓝[>] (1 : ℝ))
        (𝓝 (∑' p : Nat.Primes, (-Real.log (1 - (p : ℝ)⁻¹) - (p : ℝ)⁻¹))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ))
      (Nat.Primes.summable_rpow.mpr (by norm_num)) ?_ ?_
    · intro p
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
      have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      have h1sub : 1 - (p : ℝ)⁻¹ ≠ 0 := by
        have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt1
        linarith
      have hc : ContinuousAt (fun s : ℝ => -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)) 1 := by
        have hr1 : ContinuousAt (fun s : ℝ => (p : ℝ) ^ (-s)) 1 :=
          (continuousAt_const.rpow continuousAt_id.neg (Or.inl hp_pos.ne'))
        have hr2 : ContinuousAt (fun s : ℝ => 1 - (p : ℝ) ^ (-s)) 1 :=
          continuousAt_const.sub hr1
        have h1val : 1 - (p : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by
          simpa [Real.rpow_neg_one] using h1sub
        have hlog_at : ContinuousAt (fun s : ℝ => Real.log (1 - (p : ℝ) ^ (-s))) 1 :=
          hr2.log h1val
        exact hlog_at.neg.sub hr1
      simpa [Real.rpow_neg_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) p
      have hb := neg_log_one_sub_rpow_bounds hs.le p
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
  have h_zeta_lim :
      Tendsto (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    log_riemannZeta_add_log_sub_isLittleO_ofReal.tendsto_div_nhds_zero.congr (fun _ => by simp)
  have h_zeta_eq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun s : ℝ => ((∑' p : Nat.Primes, (p : ℝ) ^ (-s)) + Real.log (s - 1)) +
          ∑' p : Nat.Primes, (-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s))) := by
    filter_upwards [eventually_mem_nhdsWithin] with s (hs : 1 < s)
    rw [real_log_riemannZeta_eq_tsum hs]
    have hp_s : Summable fun p : Nat.Primes => (p : ℝ) ^ (-s) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    have h_tail_sum : Summable fun p : Nat.Primes =>
        -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) :=
      summable_neg_log_one_sub_rpow_sub hs.le
    have hadd := hp_s.tsum_add h_tail_sum
    have hfun : (fun p : Nat.Primes => (p : ℝ) ^ (-s) + (-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s))) =
        fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-s)) := by
      ext p; ring
    rw [hfun] at hadd
    rw [hadd]
    ring
  have h_sum_total := h_sum_lim.add h_tail_lim
  have h_eq_lim := tendsto_nhds_unique h_zeta_lim (h_sum_total.congr' h_zeta_eq.symm)
  have hneg : ∑' p : Nat.Primes, (-Real.log (1 - (p : ℝ)⁻¹) - (p : ℝ)⁻¹) =
      -∑' p : Nat.Primes, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
    rw [← tsum_neg]
    refine tsum_congr fun p => by ring
  rw [hneg] at h_eq_lim
  linarith

private lemma tail_prime_log_one_sub_add_inv_le {x : ℝ} (hx : 2 ≤ x) :
    ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)},
        -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) ≤
      (⌊x⌋₊ : ℝ)⁻¹ := by
  let N : ℕ := ⌊x⌋₊
  have hN2 : 2 ≤ N := (Nat.le_floor_iff (by linarith)).mpr hx
  let g : ℕ → ℝ := fun k => (N + k : ℝ)⁻¹ - (N + k + 1 : ℝ)⁻¹
  have hg_tel : HasSum g (N : ℝ)⁻¹ := by
    have hlim : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, g k) atTop (𝓝 (N : ℝ)⁻¹) := by
      have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, g k = (N : ℝ)⁻¹ - (N + m : ℝ)⁻¹ := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          dsimp [g]
          push_cast
          ring
      simp_rw [hsum]
      have h0 : Tendsto (fun m : ℕ => (N + m : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (N : ℝ) tendsto_natCast_atTop_atTop)
      simpa using tendsto_const_nhds.sub h0
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · exact hlim
    · intro k
      dsimp [g]
      have hk_pos : (0 : ℝ) < N + k := by exact_mod_cast (by omega : 0 < N + k)
      have hle : (N + k : ℝ) ≤ N + k + 1 := by linarith
      exact sub_nonneg.mpr (inv_anti₀ hk_pos hle)
  have hg_sum : Summable g := hg_tel.summable
  let ι : {p : Nat.Primes // N < (p : ℕ)} → ℕ := fun p => (p.1 : ℕ) - (N + 1)
  have hι_inj : Function.Injective ι := by
    intro p q hpq
    have hp1 : N + 1 ≤ (p.1 : ℕ) := p.2
    have hq1 : N + 1 ≤ (q.1 : ℕ) := q.2
    have hval : (p.1 : ℕ) = (q.1 : ℕ) := by
      dsimp [ι] at hpq
      omega
    exact Subtype.ext (Subtype.ext hval)
  have h_le_g : ∀ p : {p : Nat.Primes // N < (p : ℕ)},
      -(Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) ≤ g (ι p) := by
    intro p
    have hp_pos : (0 : ℝ) < p.1 := by exact_mod_cast p.1.prop.pos
    have hp_two : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.1.prop.two_le
    have hinv_half : (p.1 : ℝ)⁻¹ ≤ 1 / 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
    have hle := neg_log_one_sub_sub_le_sq (inv_nonneg.mpr hp_pos.le) hinv_half
    have hp_cast : (p.1 : ℝ) = (N + (ι p : ℕ) + 1 : ℝ) := by
      have hp1 : N + 1 ≤ (p.1 : ℕ) := p.2
      dsimp [ι]
      exact_mod_cast (by omega : (p.1 : ℕ) = N + ((p.1 : ℕ) - (N + 1)) + 1)
    have hN_k_pos : (0 : ℝ) < N + (ι p : ℕ) := by exact_mod_cast (by omega : 0 < N + ι p)
    have hg_eq : g (ι p) = ((N + (ι p : ℕ) : ℝ) * (N + (ι p : ℕ) + 1 : ℝ))⁻¹ := by
      dsimp [g]
      field_simp [hN_k_pos.ne', (by linarith : (N + (ι p : ℕ) + 1 : ℝ) ≠ 0)]
      ring
    have hsq_le : ((p.1 : ℝ)⁻¹) ^ 2 ≤ g (ι p) := by
      rw [hg_eq, inv_pow, hp_cast]
      refine inv_anti₀ (mul_pos hN_k_pos (by linarith)) ?_
      rw [sq]
      nlinarith
    have h_neg_eq : -(Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) =
        -Real.log (1 - (p.1 : ℝ)⁻¹) - (p.1 : ℝ)⁻¹ := by ring
    rw [h_neg_eq]
    exact hle.trans hsq_le
  have h_sub_sum : Summable fun p : {p : Nat.Primes // N < (p : ℕ)} =>
      -(Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) :=
    (summable_prime_log_one_sub_add_inv.neg).subtype _
  calc ∑' p : {p : Nat.Primes // N < (p : ℕ)}, -(Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹)
      ≤ ∑' p : {p : Nat.Primes // N < (p : ℕ)}, g (ι p) :=
        h_sub_sum.tsum_le_tsum h_le_g (hg_sum.comp_injective hι_inj)
    _ ≤ ∑' k : ℕ, g k :=
        (hg_sum.comp_injective hι_inj).tsum_le_tsum_of_inj ι hι_inj
          (fun _ _ => sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith))) (fun _ => le_rfl)
          hg_sum
    _ = (N : ℝ)⁻¹ := hg_tel.tsum_eq

/-- Explicit `O(1 / log x)` error bound for the logarithm of Mertens' third product (`2 ≤ x`). -/
theorem abs_log_mertens_three_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
        (-Real.log (Real.log x) - Real.eulerMascheroniConstant)| ≤
      (2 * mertensOneBound + 1) / Real.log x := by
  have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hprod_log :
      Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - (p : ℝ)⁻¹) := by
    refine Real.log_prod fun p hp => ?_
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    have hp_inv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt1
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - (p : ℝ)⁻¹) =
      -(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) +
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  let T : Finset Nat.Primes :=
    (Nat.primesLE ⌊x⌋₊).attach.map
      ⟨fun p : {n : ℕ // n ∈ Nat.primesLE ⌊x⌋₊} => (⟨p.1, Nat.prime_of_mem_primesLE p.2⟩ : Nat.Primes),
        fun p q h => Subtype.ext (congrArg (fun r : Nat.Primes => (r : ℕ)) h)⟩
  have hfin_eq : ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) =
      ∑ p ∈ T, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
    rw [Finset.sum_map]
    exact (Finset.sum_attach (Nat.primesLE ⌊x⌋₊)
      (fun p : ℕ => Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)).symm
  have hT_iff : ∀ p : Nat.Primes, p ∈ T ↔ (p : ℕ) ≤ ⌊x⌋₊ := by
    intro p
    simp only [T, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Nat.mem_primesLE]
    constructor
    · rintro ⟨n, ⟨hn, _⟩, rfl⟩
      exact hn
    · intro hle
      exact ⟨p.1, ⟨hle, p.prop⟩, Subtype.ext rfl⟩
  have htsum_split :=
    (summable_prime_log_one_sub_add_inv.sum_add_tsum_compl (s := T))
  have hcompl_eq :
      ∑' p : (Tᶜ : Set Nat.Primes), (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) =
        ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)},
          (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
    let e : (Tᶜ : Set Nat.Primes) ≃ {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)} :=
      { toFun := fun p => ⟨p.1, Nat.lt_of_not_ge fun h => p.2 ((hT_iff p.1).mpr h)⟩
        invFun := fun p => ⟨p.1, fun h => Nat.not_lt_of_ge ((hT_iff p.1).mp h) p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.tsum_eq fun p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)} =>
      Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹
  rw [hcompl_eq] at htsum_split
  have hdiff :
      Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
          (-Real.log (Real.log x) - Real.eulerMascheroniConstant) =
        -(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - (Real.log (Real.log x) + meisselMertensConstant)) +
          ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)},
            -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
    rw [hprod_log, hsplit, hfin_eq, ← meisselMertensConstant_sub_tsum_eq_eulerMascheroni,
      ← htsum_split, tsum_neg]
    ring
  have h1 := abs_mertens_two_sub_le hx
  have htail_nn : 0 ≤ ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)},
      -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
    refine tsum_nonneg fun p => ?_
    have hp_lt : (p.1 : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast p.1.prop.one_lt)
    have hnn := neg_log_one_sub_sub_nonneg hp_lt
    linarith
  have htail_le : ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)},
      -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) ≤ 1 / Real.log x := by
    refine (tail_prime_log_one_sub_add_inv_le hx).trans ?_
    have hlog_le : Real.log x ≤ (⌊x⌋₊ : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
      have h2 : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
      linarith
    rw [one_div]
    exact inv_anti₀ hlogx hlog_le
  rw [hdiff]
  calc |-(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - (Real.log (Real.log x) + meisselMertensConstant)) +
          ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)}, -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)|
      ≤ |-(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - (Real.log (Real.log x) + meisselMertensConstant))| +
          |∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)}, -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)| :=
        abs_add_le _ _
    _ = |∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - (Real.log (Real.log x) + meisselMertensConstant)| +
          ∑' p : {p : Nat.Primes // ⌊x⌋₊ < (p : ℕ)}, -(Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
        rw [abs_neg, abs_of_nonneg htail_nn]
    _ ≤ (2 * mertensOneBound) / Real.log x + 1 / Real.log x := add_le_add h1 htail_le
    _ = (2 * mertensOneBound + 1) / Real.log x := by ring

private lemma abs_exp_sub_one_le_of_abs_le {u B : ℝ} (hu : |u| ≤ B) :
    |Real.exp u - 1| ≤ Real.exp B * |u| := by
  rcases le_total 0 u with hu0 | hu0
  · have h1 : 0 ≤ Real.exp u - 1 := sub_nonneg.mpr (Real.one_le_exp hu0)
    have h2 : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
    have h3 : Real.exp u - 1 = Real.exp u * (1 - Real.exp (-u)) := by
      rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [abs_of_nonneg h1, abs_of_nonneg hu0, h3]
    calc Real.exp u * (1 - Real.exp (-u))
        ≤ Real.exp u * u := mul_le_mul_of_nonneg_left h2 (Real.exp_pos u).le
      _ ≤ Real.exp B * u := by
          gcongr
          exact (le_abs_self u).trans hu
  · have h1 : Real.exp u - 1 ≤ 0 := sub_nonpos.mpr (Real.exp_le_one_iff.mpr hu0)
    have h2 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    rw [abs_of_nonpos h1, abs_of_nonpos hu0]
    have h3 : -(Real.exp u - 1) ≤ -u := by linarith
    have hB0 : 0 ≤ B := (abs_nonneg u).trans hu
    have hexpB : 1 ≤ Real.exp B := Real.one_le_exp hB0
    calc -(Real.exp u - 1) ≤ -u := h3
      _ ≤ Real.exp B * (-u) := le_mul_of_one_le_left (by linarith) hexpB

/-- Constant appearing in the explicit `O(1 / (log x)²)` error bound for Mertens' third theorem. -/
def mertensThreeBound : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) *
    Real.exp ((2 * mertensOneBound + 1) / Real.log 2) * (2 * mertensOneBound + 1)

/-- Explicit `O(1 / (log x)²)` error bound for **Mertens' third theorem** (`2 ≤ x`):
`|∏_{p ≤ x} (1 - 1 / p) - exp(-γ) / log x| ≤ mertensThreeBound / (log x)²`. -/
theorem abs_mertens_three_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) -
        Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤
      mertensThreeBound / Real.log x ^ 2 := by
  have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  have hP_pos : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp_gt1)
  let u : ℝ := Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
    (-Real.log (Real.log x) - Real.eulerMascheroniConstant)
  have hu_le : |u| ≤ (2 * mertensOneBound + 1) / Real.log x :=
    abs_log_mertens_three_sub_le hx
  have hu_B : |u| ≤ (2 * mertensOneBound + 1) / Real.log 2 := by
    refine hu_le.trans ?_
    have hnum_nn : 0 ≤ 2 * mertensOneBound + 1 := by linarith [mertensOneBound_pos]
    gcongr
  have hexp_u : ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) =
      (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) * Real.exp u := by
    have hlog_eq : Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) =
        (-Real.log (Real.log x) - Real.eulerMascheroniConstant) + u := by
      dsimp [u]; ring
    calc ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)
        = Real.exp (Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹))) := (Real.exp_log hP_pos).symm
      _ = Real.exp ((-Real.log (Real.log x) - Real.eulerMascheroniConstant) + u) := by rw [hlog_eq]
      _ = Real.exp (-Real.log (Real.log x)) * Real.exp (-Real.eulerMascheroniConstant) *
            Real.exp u := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
      _ = (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) * Real.exp u := by
          rw [Real.exp_neg, Real.exp_log hlogx]
          ring
  have hdiff_eq : ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) -
        Real.exp (-Real.eulerMascheroniConstant) / Real.log x =
      (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) * (Real.exp u - 1) := by
    rw [hexp_u]
    ring
  rw [hdiff_eq, abs_mul, abs_of_nonneg (div_nonneg (Real.exp_pos _).le hlogx.le)]
  have hexp_sub := abs_exp_sub_one_le_of_abs_le hu_B
  calc (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) * |Real.exp u - 1|
      ≤ (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) *
          (Real.exp ((2 * mertensOneBound + 1) / Real.log 2) * |u|) :=
        mul_le_mul_of_nonneg_left hexp_sub (div_nonneg (Real.exp_pos _).le hlogx.le)
    _ ≤ (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) *
          (Real.exp ((2 * mertensOneBound + 1) / Real.log 2) *
            ((2 * mertensOneBound + 1) / Real.log x)) := by
        gcongr
    _ = mertensThreeBound / Real.log x ^ 2 := by
        rw [mertensThreeBound]
        ring

/-- **Mertens' third theorem** (Big-O remainder form):
`∏_{p ≤ x} (1 - 1 / p) - exp(-γ) / log x = O((log x)⁻²)` as `x → ∞`. -/
theorem mertens_third_theorem_isBigO :
    (fun x : ℝ => ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) -
        Real.exp (-Real.eulerMascheroniConstant) / Real.log x) =O[atTop]
      (fun x : ℝ => (Real.log x ^ 2)⁻¹) := by
  refine isBigO_iff.mpr ⟨mertensThreeBound, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), ← div_eq_mul_inv]
  exact abs_mertens_three_sub_le hx

/-- **Mertens' third theorem** (asymptotic equivalence form):
`∏_{p ≤ x} (1 - 1 / p) ~ exp(-γ) / log x` as `x → ∞`. -/
theorem mertens_third_theorem :
    (fun x : ℝ => ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) ~[atTop]
      (fun x : ℝ => Real.exp (-Real.eulerMascheroniConstant) / Real.log x) := by
  have h_err : (fun x : ℝ => ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) -
      Real.exp (-Real.eulerMascheroniConstant) / Real.log x) =o[atTop]
      (fun x : ℝ => Real.exp (-Real.eulerMascheroniConstant) / Real.log x) := by
    refine mertens_third_theorem_isBigO.trans_isLittleO ?_
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have h0 : Tendsto (fun x : ℝ =>
          (Real.log x)⁻¹ / Real.exp (-Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
        simpa using Real.tendsto_log_atTop.inv_tendsto_atTop.div_const
          (Real.exp (-Real.eulerMascheroniConstant))
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      field_simp [hlog, (Real.exp_pos (-Real.eulerMascheroniConstant)).ne']
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hzero
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      exact absurd hzero (div_ne_zero (Real.exp_pos _).ne' hlog)
  exact Asymptotics.IsLittleO.isEquivalent h_err

/-- **Mertens' third theorem** (limit form):
`log x * ∏_{p ≤ x} (1 - 1 / p) → exp(-γ)` as `x → ∞`. -/
theorem mertens_third_theorem_tendsto :
    Tendsto (fun x : ℝ => Real.log x * ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := (Asymptotics.isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (Real.exp_pos _).ne' (Real.log_pos hx).ne')).mp mertens_third_theorem
  have hmul := h.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  simp only [Pi.div_apply]
  field_simp [hlog, (Real.exp_pos (-Real.eulerMascheroniConstant)).ne']

end AnalyticNumberTheory.PrimeDistribution
