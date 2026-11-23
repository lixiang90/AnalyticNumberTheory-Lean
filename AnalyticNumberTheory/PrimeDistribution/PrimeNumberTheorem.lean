import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-!
# The Prime Number Theorem

This file establishes the unified Prime Number Theorem API and the unconditional
de la Vallée Poussin Prime Number Theorem with explicit exponential error terms:

- Weak / asymptotic PNT bridges from Mathlib (`Chebyshev.psi x ~ x`, `Chebyshev.theta x ~ x`,
  `primePi x ~ x / Real.log x`, `Nat.nth Nat.Prime n ~ n * Real.log n`).
- The classical `3 + 4 cos θ + cos(2θ) ≥ 0` trigonometric inequality and its `-Re (ζ'/ζ)` form
  for `Re s > 1`.
- Unconditional de la Vallée Poussin zero-free region for `riemannZeta` (via `3-4-1` and
  Borel–Carathéodory / Landau's logarithmic-derivative lemma) together with the logarithmic
  derivative upper bound `‖-ζ'(s) / ζ(s)‖ ≪ (log(|Im s| + 3))²` inside the zero-free region.
- Clean Perron + Cauchy-rectangle contour shift proving the unconditional de la Vallée Poussin
  error terms for `Chebyshev.psi x - x`, `Chebyshev.theta x - x`, and `primePi x - logIntegral x`.
-/

noncomputable section

open Finset MeasureTheory Set Filter Asymptotics Complex
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-! ### Weak / Asymptotic Prime Number Theorem Bridges -/

/-- The Chebyshev `ψ` function satisfies `ψ(x) / x → 1` as `x → ∞`. -/
theorem tendsto_psi_div_atTop :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  Chebyshev.tendsto_psi_div_atTop

/-- The Chebyshev `ψ` function is asymptotically equivalent to `id`: `ψ(x) ~ x`. -/
theorem isEquivalent_psi_id : Chebyshev.psi ~[atTop] id :=
  Chebyshev.isEquivalent_psi_id

/-- The Chebyshev `θ` function satisfies `θ(x) / x → 1` as `x → ∞`. -/
theorem tendsto_theta_div_atTop :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  Chebyshev.tendsto_theta_div_atTop

/-- The Chebyshev `θ` function is asymptotically equivalent to `id`: `θ(x) ~ x`. -/
theorem isEquivalent_theta_id : Chebyshev.theta ~[atTop] id :=
  Chebyshev.isEquivalent_theta_id

/-- The prime counting function satisfies `π(x) * Real.log x / x → 1` as `x → ∞`. -/
theorem tendsto_primePi_mul_log_div_atTop :
    Tendsto (fun x : ℝ => primePi x * Real.log x / x) atTop (𝓝 1) :=
  (tendsto_primePi_mul_log_div_iff_tendsto_theta_div 1).mpr tendsto_theta_div_atTop

/-- **Prime Number Theorem** for `primePi`: `π(x) ~ x / Real.log x` as `x → ∞`. -/
theorem isEquivalent_primePi :
    primePi ~[atTop] fun x : ℝ => x / Real.log x := by
  refine (Nat.isEquivalent_primeCounting).congr' (Eventually.of_forall fun x => rfl) .rfl

/-- Successive primes are asymptotically equal: `p_{n+1} ~ p_n`. -/
theorem isEquivalent_nth_prime_succ :
    (fun n : ℕ => (Nat.nth Nat.Prime (n + 1) : ℝ)) ~[atTop]
      fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) :=
  Nat.isEquivalent_nth_prime_succ

/-- **Prime Number Theorem for the `n`-th prime**: `p_n ~ n * Real.log n` as `n → ∞`. -/
theorem isEquivalent_nth_prime :
    (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) * Real.log n := by
  let p : ℕ → ℕ := Nat.nth Nat.Prime
  have hp_mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp_top : Tendsto (fun n : ℕ => (p n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp_mono.tendsto_atTop
  have hp_ge2_nat : ∀ n : ℕ, 2 ≤ p n := fun n =>
    le_trans (Nat.le_add_left 2 n) (Nat.add_two_le_nth_prime n)
  have hcount : ∀ n : ℕ, Nat.primeCounting (p n) = n + 1 := by
    intro n
    rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting',
      Nat.count_succ_eq_succ_count_iff.mpr (Nat.prime_nth_prime n)]
    exact congrArg Nat.succ (Nat.primeCounting'_nth_eq n)
  have hp_ratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log (p n) / (p n : ℝ))
      atTop (𝓝 1) := by
    refine (tendsto_primePi_mul_log_div_atTop.comp hp_top).congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply, primePi, Nat.floor_natCast, hcount n, Nat.cast_add,
      Nat.cast_one]
  have h_ev_le : ∀ᶠ n : ℕ in atTop,
      (p n : ℝ) ≤ 2 * ((n : ℝ) + 1) * Real.log (p n) := by
    have hhalf : ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) < ((n : ℝ) + 1) * Real.log (p n) / (p n : ℝ) :=
      hp_ratio.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [hhalf] with n hn
    have hp_pos : (0 : ℝ) < p n := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) (hp_ge2_nat n)
    rw [lt_div_iff₀ hp_pos] at hn
    linarith
  have h_ev_poly : ∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ 16 * ((n : ℝ) + 1) ^ 2 := by
    filter_upwards [h_ev_le] with n hn
    have hp_pos : (0 : ℝ) < p n := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) (hp_ge2_nat n)
    have hlog_sqrt : Real.log (p n) ≤ 2 * Real.sqrt (p n) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp_pos)
      rw [Real.sqrt_eq_rpow, Real.log_rpow hp_pos, ← Real.sqrt_eq_rpow] at h1
      linarith
    have hsqrt_le : Real.sqrt (p n) ≤ 4 * ((n : ℝ) + 1) := by
      have hsq : Real.sqrt (p n) * Real.sqrt (p n) ≤ 4 * ((n : ℝ) + 1) * Real.sqrt (p n) := by
        calc Real.sqrt (p n) * Real.sqrt (p n) = p n := Real.mul_self_sqrt hp_pos.le
          _ ≤ 2 * ((n : ℝ) + 1) * (2 * Real.sqrt (p n)) :=
            hn.trans (mul_le_mul_of_nonneg_left hlog_sqrt (by positivity))
          _ = 4 * ((n : ℝ) + 1) * Real.sqrt (p n) := by ring
      exact le_of_mul_le_mul_right hsq (Real.sqrt_pos.mpr hp_pos)
    calc (p n : ℝ) = Real.sqrt (p n) ^ 2 := (Real.sq_sqrt hp_pos.le).symm
      _ ≤ (4 * ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
      _ = 16 * ((n : ℝ) + 1) ^ 2 := by ring
  have hlog_nat_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_succ : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / Real.log n) atTop (𝓝 1) := by
    have hlim : Tendsto (fun n : ℕ => 1 + Real.log 2 / Real.log (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlog_nat_top)
    rw [add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hlogn_pos : 0 < Real.log n := Real.log_pos hn1
      exact (one_le_div hlogn_pos).mpr (Real.log_le_log (by linarith) (by linarith))
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hlogn_pos : 0 < Real.log n := Real.log_pos hn1
      have hlog_le : Real.log ((n : ℝ) + 1) ≤ Real.log n + Real.log 2 := by
        calc Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
              Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) (by linarith)
          _ = Real.log n + Real.log 2 := add_comm _ _
      calc Real.log ((n : ℝ) + 1) / Real.log n
          ≤ (Real.log n + Real.log 2) / Real.log n :=
            div_le_div_of_nonneg_right hlog_le hlogn_pos.le
        _ = 1 + Real.log 2 / Real.log n := by field_simp [hlogn_pos.ne']
  have hloglog : Tendsto (fun n : ℕ =>
      Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) / Real.log n) atTop (𝓝 0) := by
    have hsqrt_inv : Tendsto (fun n : ℕ => 6 / Real.sqrt (Real.log n)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n : ℕ => Real.sqrt (Real.log n)) atTop atTop :=
        tendsto_atTop_atTop.mpr fun b => by
          obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hlog_nat_top ((max b 0) ^ 2)
          exact ⟨N, fun n hn => by
            have := Real.sqrt_le_sqrt (hN n hn)
            rw [Real.sqrt_sq (le_max_right _ _)] at this
            exact (le_max_left b 0).trans this⟩
      simpa [div_eq_mul_inv] using hsq.inv_tendsto_atTop.const_mul 6
    refine squeeze_zero' ?_ ?_ hsqrt_inv
    · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hlogn_pos : 0 < Real.log n := Real.log_pos hn1
      have hge1 : 1 ≤ Real.log 16 + 2 * Real.log ((n : ℝ) + 1) := by
        have h16 : (1 : ℝ) ≤ Real.log 16 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          exact Real.exp_one_lt_d9.le.trans (by norm_num)
        have hpos : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
        linarith
      exact div_nonneg (Real.log_nonneg hge1) hlogn_pos.le
    · filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
      have hlogn_pos : 0 < Real.log n := Real.log_pos (by linarith)
      have hle_poly : Real.log 16 + 2 * Real.log ((n : ℝ) + 1) ≤ 9 * Real.log n := by
        have h1 : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) hn16
        have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
          Real.log_le_log (by positivity) (by linarith)
        have h3 : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
          Real.log_mul (by norm_num) hn_pos.ne'
        have h4 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have harg_pos : 0 < Real.log 16 + 2 * Real.log ((n : ℝ) + 1) := by
        have h16p : 0 < Real.log 16 := Real.log_pos (by norm_num)
        have hnp : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
        linarith
      have hlog_sq : Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) ≤
          2 * Real.sqrt (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr harg_pos)
        rw [Real.sqrt_eq_rpow, Real.log_rpow harg_pos, ← Real.sqrt_eq_rpow] at h1
        linarith
      have hsq2 : 2 * Real.sqrt (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) ≤
          6 * Real.sqrt (Real.log n) := by
        calc 2 * Real.sqrt (Real.log 16 + 2 * Real.log ((n : ℝ) + 1))
            ≤ 2 * Real.sqrt (9 * Real.log n) := by gcongr
          _ = 2 * (Real.sqrt 9 * Real.sqrt (Real.log n)) := by rw [Real.sqrt_mul (by norm_num)]
          _ = 6 * Real.sqrt (Real.log n) := by
              rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; ring
      calc Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) / Real.log n
          ≤ (6 * Real.sqrt (Real.log n)) / Real.log n :=
            div_le_div_of_nonneg_right (hlog_sq.trans hsq2) hlogn_pos.le
        _ = 6 / Real.sqrt (Real.log n) := by
            rw [div_eq_div_iff hlogn_pos.ne' (Real.sqrt_pos.mpr hlogn_pos).ne']
            linear_combination 6 * (Real.mul_self_sqrt hlogn_pos.le)
  have hlog_ratio : Tendsto (fun n : ℕ => Real.log (p n) / Real.log n) atTop (𝓝 1) := by
    have hupper_tendsto : Tendsto (fun n : ℕ =>
        Real.log 2 / Real.log n + Real.log ((n : ℝ) + 1) / Real.log n +
          Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) / Real.log n) atTop (𝓝 (0 + 1 + 0)) :=
      ((tendsto_const_nhds.div_atTop hlog_nat_top).add hlog_succ).add hloglog
    rw [zero_add, add_zero] at hupper_tendsto
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tendsto ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hlogn_pos : 0 < Real.log n := Real.log_pos hn1
      have hnp : (n : ℝ) ≤ p n := by
        exact_mod_cast le_trans (Nat.le_add_right n 2) (Nat.add_two_le_nth_prime n)
      exact (one_le_div hlogn_pos).mpr (Real.log_le_log (by linarith) hnp)
    · filter_upwards [h_ev_le, h_ev_poly, eventually_ge_atTop (3 : ℕ)] with n hn hpoly hn3
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hlogn_pos : 0 < Real.log n := Real.log_pos hn1
      have hp_ge2 : (2 : ℝ) ≤ p n := by exact_mod_cast hp_ge2_nat n
      have hlogp_poly : Real.log (p n) ≤ Real.log 16 + 2 * Real.log ((n : ℝ) + 1) := by
        calc Real.log (p n) ≤ Real.log (16 * ((n : ℝ) + 1) ^ 2) :=
              Real.log_le_log (by linarith) hpoly
          _ = Real.log 16 + Real.log (((n : ℝ) + 1) ^ 2) :=
              Real.log_mul (by norm_num) (by positivity)
          _ = Real.log 16 + 2 * Real.log ((n : ℝ) + 1) := by rw [Real.log_pow]; ring
      have hpoly_pos : 0 < Real.log 16 + 2 * Real.log ((n : ℝ) + 1) := by
        have : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
        have : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
        linarith
      have hmul : (p n : ℝ) ≤ 2 * ((n : ℝ) + 1) * (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) :=
        hn.trans (mul_le_mul_of_nonneg_left hlogp_poly (by positivity))
      have hlogp_tight : Real.log (p n) ≤
          Real.log 2 + Real.log ((n : ℝ) + 1) +
            Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) := by
        calc Real.log (p n)
            ≤ Real.log (2 * ((n : ℝ) + 1) * (Real.log 16 + 2 * Real.log ((n : ℝ) + 1))) :=
              Real.log_le_log (by linarith) hmul
          _ = Real.log (2 * ((n : ℝ) + 1)) +
                Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) :=
              Real.log_mul (by positivity) hpoly_pos.ne'
          _ = Real.log 2 + Real.log ((n : ℝ) + 1) +
                Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) := by
              rw [Real.log_mul (by norm_num) (by positivity)]
      calc Real.log (p n) / Real.log n
          ≤ (Real.log 2 + Real.log ((n : ℝ) + 1) +
              Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1))) / Real.log n :=
            div_le_div_of_nonneg_right hlogp_tight hlogn_pos.le
        _ = Real.log 2 / Real.log n + Real.log ((n : ℝ) + 1) / Real.log n +
              Real.log (Real.log 16 + 2 * Real.log ((n : ℝ) + 1)) / Real.log n := by ring
  have hinv_ratio : Tendsto (fun n : ℕ => (p n : ℝ) / (((n : ℝ) + 1) * Real.log (p n)))
      atTop (𝓝 1) := by
    have h1 := hp_ratio.inv₀ (by norm_num)
    rw [inv_one] at h1
    refine h1.congr' (Eventually.of_forall fun n => ?_)
    rw [inv_div]
  have hsucc_div : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + (n : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn0]
  rw [isEquivalent_iff_tendsto_one]
  · have hprod := (hinv_ratio.mul hsucc_div).mul hlog_ratio
    rw [one_mul, one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hp_ge2 : (2 : ℝ) ≤ p n := by exact_mod_cast hp_ge2_nat n
    have hlogp_pos : 0 < Real.log (p n) := Real.log_pos (by linarith)
    have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    simp only [Pi.div_apply]
    field_simp [hn_pos.ne', hlogp_pos.ne', hlogn_pos.ne',
      show (n : ℝ) + 1 ≠ 0 by positivity]
    ring
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hlogn0 : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
    exact mul_ne_zero hn0 hlogn0

/-! ### Trigonometric `3-4-1` Inequality and `-Re(ζ'/ζ)` on `Re s > 1` -/

/-- Classical `3 + 4 cos θ + cos(2θ) = 2 (1 + cos θ)² ≥ 0` inequality. -/
theorem three_four_one_cos (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (1 + Real.cos θ)]

private lemma summable_vonMangoldt_rpow_cos {σ t : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hs : 1 < ((σ : ℂ) + (t : ℂ) * I).re := by simp [hσ]
  have hsum : LSeriesSummable (fun n : ℕ => (Λ n : ℂ)) ((σ : ℂ) + (t : ℂ) * I) :=
    LSeriesSummable_vonMangoldt_iff.mpr hs
  refine (Complex.reCLM.hasSum hsum.hasSum).summable.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    split_ifs with h0
    · exact absurd h0 hn
    · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hlogC : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
      have hcpow : (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
          ((n : ℝ) ^ (-σ) : ℝ) * Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) := by
        rw [Complex.cpow_def_of_ne_zero hnC, hlogC, Real.rpow_def_of_pos hn_pos,
          Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast; ring
      rw [div_eq_mul_inv, ← Complex.cpow_neg, hcpow]
      have hre : (Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I)).re = Real.cos (t * Real.log n) := by
        rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      have hmul : (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) *
            Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I)) =
          ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
            Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) := by
        push_cast; ring
      rw [hmul, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hre]

/-- Exact cosine Dirichlet series expansion of `-Re (ζ'/ζ)(σ + i t)` for `σ > 1`. -/
theorem neg_re_logDeriv_riemannZeta_eq_tsum {σ t : ℝ} (hσ : 1 < σ) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s, hσ]
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum : LSeriesSummable (fun n : ℕ => (Λ n : ℂ)) s :=
    LSeriesSummable_vonMangoldt_iff.mpr hs
  have hneg : -(logDeriv riemannZeta s).re = (LSeries (fun n : ℕ => (Λ n : ℂ)) s).re := by
    rw [logDeriv_apply, ← Complex.neg_re, ← neg_div, ← hL]
  rw [hneg, LSeries, Complex.re_tsum hsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    split_ifs with h0
    · exact absurd h0 hn
    · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hlogC : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
      have hcpow : (n : ℂ) ^ (-s) =
          ((n : ℝ) ^ (-σ) : ℝ) * Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) := by
        rw [Complex.cpow_def_of_ne_zero hnC, hlogC, Real.rpow_def_of_pos hn_pos,
          Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        dsimp [s]; push_cast; ring
      rw [div_eq_mul_inv, ← Complex.cpow_neg, hcpow]
      have hre : (Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I)).re = Real.cos (t * Real.log n) := by
        rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      have hmul : (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) *
            Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I)) =
          ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
            Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) := by
        push_cast; ring
      rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]

/-- **Mertens' `3-4-1` zeta inequality**: for `σ > 1` and any real `t`,
`0 ≤ 3 * (-Re(ζ'/ζ)(σ)) + 4 * (-Re(ζ'/ζ)(σ + it)) + (-Re(ζ'/ζ)(σ + 2it))`. -/
theorem three_four_one_zeta_ineq {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-(logDeriv riemannZeta (σ : ℂ)).re) +
      4 * (-(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re) +
      (-(logDeriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re) := by
  have h0 := neg_re_logDeriv_riemannZeta_eq_tsum (t := 0) hσ
  have h1 := neg_re_logDeriv_riemannZeta_eq_tsum (t := t) hσ
  have h2 := neg_re_logDeriv_riemannZeta_eq_tsum (t := 2 * t) hσ
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, mul_one] at h0
  have hs0 : Summable fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-σ) := by
    simpa using summable_vonMangoldt_rpow_cos (t := 0) hσ
  have hs1 := summable_vonMangoldt_rpow_cos (t := t) hσ
  have hs2 := summable_vonMangoldt_rpow_cos (t := 2 * t) hσ
  rw [h0, h1, h2, ← tsum_mul_left, ← tsum_mul_left, ← (hs0.mul_left 3).tsum_add (hs1.mul_left 4),
    ← ((hs0.mul_left 3).add (hs1.mul_left 4)).tsum_add hs2]
  refine tsum_nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · split_ifs with h0
    · exact absurd h0 hn
    · have hcoeff : 0 ≤ Λ n * (n : ℝ) ^ (-σ) :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      have htrig := three_four_one_cos (t * Real.log n)
      calc 0 ≤ (Λ n * (n : ℝ) ^ (-σ)) *
            (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n))) :=
          mul_nonneg hcoeff htrig
        _ = 3 * (Λ n * (n : ℝ) ^ (-σ)) + 4 * (Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)) +
              Λ n * (n : ℝ) ^ (-σ) * Real.cos (2 * t * Real.log n) := by ring

/-! ### de la Vallée Poussin Zero-Free Region and Logarithmic Derivative Bounds -/

/-- Bundle packaging a de la Vallée Poussin zero-free constant `c > 0` and logarithmic derivative
upper bound constant `C > 0` for `riemannZeta`. -/
structure ZetaZeroFreeData where
  /-- Zero-free region width constant `c` (`0 < c ≤ 1 / 8`). -/
  c : ℝ
  /-- Positivity of `c`. -/
  hc_pos : 0 < c
  /-- Upper normalization `c ≤ 1 / 8`. -/
  hc_le : c ≤ 1 / 8
  /-- Logarithmic derivative constant `C`. -/
  C : ℝ
  /-- Positivity of `C`. -/
  hC_pos : 0 < C
  /-- `riemannZeta₁ s ≠ 0` inside `1 - c / Real.log (|s.im| + 3) ≤ s.re`. -/
  zeroFree_zetaOne : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta₁ s ≠ 0
  /-- `‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * (Real.log (|s.im| + 3))²` for `3 ≤ |s.im|`. -/
  norm_logDeriv_large : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → 3 ≤ |s.im| →
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * (Real.log (|s.im| + 3)) ^ 2
  /-- `‖-deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹‖ ≤ C` for `|s.im| ≤ 3`, `s ≠ 1`. -/
  norm_logDeriv_small : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → |s.im| ≤ 3 → s ≠ 1 →
    ‖-deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹‖ ≤ C

private lemma logDeriv_riemannZeta_eq_sub {s : ℂ} (hs : s ≠ 1) (h1 : riemannZeta₁ s ≠ 0) :
    logDeriv riemannZeta s = logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
  have hz : riemannZeta s ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs)) h1
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs,
    riemannZeta_eq_inv_sub_mul hs]
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hs', h1]
  ring

/-- Upper bound for `-(logDeriv riemannZeta σ).re` on the real interval `σ ∈ (1, 2]`:
`-(logDeriv riemannZeta σ).re ≤ 1 / (σ - 1) + C₀`. -/
theorem neg_re_logDeriv_riemannZeta_real_le :
    ∃ C₀ > 0, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C₀ := by
  have hne : ∀ σ ∈ Set.Icc (1 : ℝ) 2, riemannZeta₁ (σ : ℂ) ≠ 0 := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ.1 with rfl | hgt
    · simp
    · have hne1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hgt.ne'
      have hz : riemannZeta (σ : ℂ) ≠ 0 := RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simpa using hgt)
      intro h0
      apply hz
      rw [riemannZeta_eq_inv_sub_mul hne1, h0, mul_zero]
  have hcont : ContinuousOn (fun σ : ℝ => ‖logDeriv riemannZeta₁ (σ : ℂ)‖) (Set.Icc 1 2) := by
    have hdiff : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁_bridge
    have hcd : Continuous fun σ : ℝ => deriv riemannZeta₁ (σ : ℂ) :=
      (hdiff.contDiff.continuous_deriv le_rfl).comp Complex.continuous_ofReal
    have hcf : Continuous fun σ : ℝ => riemannZeta₁ (σ : ℂ) :=
      hdiff.continuous.comp Complex.continuous_ofReal
    refine (hcd.continuousOn.div hcf.continuousOn hne).norm.congr fun σ _ => ?_
    simp [logDeriv_apply]
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcont
  let C₀ : ℝ := max M 1
  refine ⟨C₀, by positivity, fun σ h1 h2 => ?_⟩
  have hmem : σ ∈ Set.Icc (1 : ℝ) 2 := ⟨h1.le, h2⟩
  have hle_M : ‖logDeriv riemannZeta₁ (σ : ℂ)‖ ≤ M := hM ⟨σ, hmem, rfl⟩
  have hle_C₀ : -(logDeriv riemannZeta₁ (σ : ℂ)).re ≤ C₀ := by
    have h1' : -(logDeriv riemannZeta₁ (σ : ℂ)).re ≤ ‖logDeriv riemannZeta₁ (σ : ℂ)‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    exact h1'.trans (hle_M.trans (le_max_left _ _))
  have hne1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne'
  rw [logDeriv_riemannZeta_eq_sub hne1 (hne σ hmem), Complex.sub_re, neg_sub]
  have hinv_re : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re,
      one_div]
  rw [hinv_re]
  linarith

/-- Compact-rectangle zero-freeness and logarithmic derivative bound for `riemannZeta₁` on
`|s.im| ≤ 3`. -/
theorem zeta_small_im_zeroFree_and_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧ ∃ C_sm > 0,
      (∀ s : ℂ, 1 - ε₀ ≤ s.re → |s.im| ≤ 3 → riemannZeta₁ s ≠ 0) ∧
      (∀ s : ℂ, 1 - ε₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 3 → ‖logDeriv riemannZeta₁ s‖ ≤ C_sm) := by
  let K₁ : Set ℂ := Set.Icc (1 : ℝ) 2 ×ℂ Set.Icc (-3 : ℝ) 3
  let K₂ : Set ℂ := Set.Icc (1 / 2 : ℝ) 2 ×ℂ Set.Icc (-3 : ℝ) 3
  have hK₁_comp : IsCompact K₁ := isCompact_Icc.reProdIm isCompact_Icc
  have hK₂_comp : IsCompact K₂ := isCompact_Icc.reProdIm isCompact_Icc
  have hK₁_ne : K₁.Nonempty := ⟨(1 : ℂ), ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hcont_z1 : Continuous riemannZeta₁ := differentiable_riemannZeta₁_bridge.continuous
  obtain ⟨s₀, hs₀K, hs₀_min⟩ :=
    hK₁_comp.exists_isMinOn hK₁_ne hcont_z1.norm.continuousOn
  have hs₀_ne : riemannZeta₁ s₀ ≠ 0 := by
    rcases eq_or_ne s₀ 1 with rfl | hs1
    · simp
    · have hz := riemannZeta_ne_zero_of_one_le_re hs₀K.1.1
      intro h0
      apply hz
      rw [riemannZeta_eq_inv_sub_mul hs1, h0, mul_zero]
  let m : ℝ := ‖riemannZeta₁ s₀‖
  have hm_pos : 0 < m := norm_pos_iff.mpr hs₀_ne
  have huc := hK₂_comp.uniformContinuousOn_of_continuous hcont_z1.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := huc (m / 2) (half_pos hm_pos)
  let ε₀ : ℝ := min (1 / 4) (δ₁ / 2)
  have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (half_pos hδ₁_pos)
  have hε₀_le : ε₀ ≤ 1 / 4 := min_le_left _ _
  have hε₀_lt : ε₀ < δ₁ := (min_le_right _ _).trans_lt (half_lt_self hδ₁_pos)
  have h_nozero : ∀ s : ℂ, 1 - ε₀ ≤ s.re → |s.im| ≤ 3 → riemannZeta₁ s ≠ 0 := by
    intro s hs_re hs_im
    by_cases hre1 : 1 ≤ s.re
    · rcases eq_or_ne s 1 with rfl | hs1
      · simp
      · have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1
        intro h0
        apply hz
        rw [riemannZeta_eq_inv_sub_mul hs1, h0, mul_zero]
    · have hs_lt1 : s.re < 1 := not_le.mp hre1
      have him_mem : s.im ∈ Set.Icc (-3 : ℝ) 3 := abs_le.mp hs_im
      have hs_K₂ : s ∈ K₂ := ⟨⟨by linarith, by linarith⟩, him_mem⟩
      let s' : ℂ := (1 : ℂ) + (s.im : ℂ) * I
      have hs'_K₁ : s' ∈ K₁ := ⟨⟨by simp [s'], by simp [s']⟩, by simpa [s'] using him_mem⟩
      have hs'_K₂ : s' ∈ K₂ := ⟨⟨by simp [s']; norm_num, by simp [s']⟩, by simpa [s'] using him_mem⟩
      have hdist : dist s s' < δ₁ := by
        rw [dist_eq_norm]
        have hdiff : s - s' = ((s.re - 1 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [s']
        rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hs_lt1)]
        linarith
      have hclose := hδ₁ s hs_K₂ s' hs'_K₂ hdist
      rw [dist_eq_norm] at hclose
      have hm_le : m ≤ ‖riemannZeta₁ s'‖ := hs₀_min hs'_K₁
      have hnorm_pos : 0 < ‖riemannZeta₁ s‖ := by
        have htri : ‖riemannZeta₁ s'‖ ≤ ‖riemannZeta₁ s‖ + ‖riemannZeta₁ s - riemannZeta₁ s'‖ := by
          calc ‖riemannZeta₁ s'‖ = ‖riemannZeta₁ s - (riemannZeta₁ s - riemannZeta₁ s')‖ := by ring_nf
            _ ≤ ‖riemannZeta₁ s‖ + ‖riemannZeta₁ s - riemannZeta₁ s'‖ := norm_sub_le _ _
        linarith
      exact norm_ne_zero_iff.mp hnorm_pos.ne'
  let K₃ : Set ℂ := Set.Icc (1 - ε₀) 2 ×ℂ Set.Icc (-3 : ℝ) 3
  have hK₃_comp : IsCompact K₃ := isCompact_Icc.reProdIm isCompact_Icc
  have hcont_ld : ContinuousOn (fun s : ℂ => ‖logDeriv riemannZeta₁ s‖) K₃ := by
    have hdiff := differentiable_riemannZeta₁_bridge
    refine ((hdiff.contDiff.continuous_deriv le_rfl).continuousOn.div
      hdiff.continuous.continuousOn fun s (hs : s ∈ Set.Icc (1 - ε₀) 2 ×ℂ Set.Icc (-3 : ℝ) 3) =>
        h_nozero s hs.1.1 (abs_le.mpr hs.2)).norm.congr fun s _ => ?_
    simp [logDeriv_apply]
  obtain ⟨M, hM⟩ := hK₃_comp.bddAbove_image hcont_ld
  refine ⟨ε₀, hε₀_pos, hε₀_le, max M 1, by positivity, h_nozero, fun s hs1 hs2 hs3 => ?_⟩
  have hs_K₃ : s ∈ K₃ := ⟨⟨hs1, hs2⟩, abs_le.mp hs3⟩
  exact (hM ⟨s, hs_K₃, rfl⟩).trans (le_max_left _ _)

private lemma riemannZeta_analyticOnNhd_closedBall_of_large_im {σ t R : ℝ}
    (ht : R + 1 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall ((σ : ℂ) + (t : ℂ) * I) R) := by
  have hsub : Metric.closedBall ((σ : ℂ) + (t : ℂ) * I) R ⊆ ({1}ᶜ : Set ℂ) := by
    intro w hw h1
    rw [Set.mem_singleton_iff] at h1
    rw [h1, Metric.mem_closedBall, dist_eq_norm] at hw
    have him : |t| ≤ ‖(1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)‖ := by
      have h1' : ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).im = -t := by simp
      calc |t| = |-t| := (abs_neg t).symm
        _ = |((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).im| := by rw [h1']
        _ ≤ ‖(1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)‖ := Complex.abs_im_le_norm _
    linarith
  have hdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun w hw =>
    (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hw)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton).mono hsub

/-- Landau's logarithmic-derivative upper bound on `-(logDeriv riemannZeta (σ + i t)).re`
for `|t| ≥ 3` and `1 < σ ≤ 2`. -/
theorem neg_re_logDeriv_riemannZeta_disk_le {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (ht : 3 ≤ |t|) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re ≤
      8 * Real.log (4 * (|t| + 3) / (σ - 1)) := by
  let z₀ : ℂ := (σ : ℂ) + (t : ℂ) * I
  let M : ℝ := 4 * (|t| + 3) / (σ - 1)
  have hf_an : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ (1 / 2)) :=
    riemannZeta_analyticOnNhd_closedBall_of_large_im (by linarith)
  have hz₀_ne : riemannZeta z₀ ≠ 0 := RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simp [z₀, hσ1])
  have hbound : ∀ w ∈ Metric.sphere z₀ (1 / 2), ‖riemannZeta w / riemannZeta z₀‖ ≤ M := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hw_re : 1 / 2 ≤ w.re := by
      have h1 : |w.re - z₀.re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm (w - z₀)
      have hzre : z₀.re = σ := by simp [z₀]
      linarith [(abs_le.mp (h1.trans hw.le)).1]
    have hw_norm_ge : 2 ≤ ‖w‖ := by
      have h1 : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm (w - z₀)
      have hzim : z₀.im = t := by simp [z₀]
      have hw_im : 5 / 2 ≤ |w.im| := by
        rcases le_or_gt 0 t with ht0 | ht0
        · rw [abs_of_nonneg ht0] at ht
          have := (abs_le.mp (h1.trans hw.le)).1
          have h2 : 5 / 2 ≤ w.im := by linarith
          exact h2.trans (le_abs_self _)
        · rw [abs_of_neg ht0] at ht
          have := (abs_le.mp (h1.trans hw.le)).2
          have h2 : 5 / 2 ≤ -w.im := by linarith
          exact h2.trans (neg_le_abs _)
      exact (by norm_num : (2 : ℝ) ≤ 5 / 2).trans (hw_im.trans (Complex.abs_im_le_norm w))
    have hnum : ‖riemannZeta w‖ ≤ 2 * (|t| + 3) := by
      have h1 := norm_riemannZeta_re_ge_half_le hw_re hw_norm_ge
      have hw_norm_le : ‖w‖ ≤ |t| + 3 := by
        have hz₀_le : ‖z₀‖ ≤ σ + |t| := by
          calc ‖z₀‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
            _ = |σ| + |t| := by simp [Complex.norm_real, Complex.norm_I]
            _ = σ + |t| := by rw [abs_of_pos (by linarith)]
        calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ 1 / 2 + (σ + |t|) := add_le_add hw.le hz₀_le
          _ ≤ |t| + 3 := by linarith
      linarith
    have hden : (σ - 1) / 2 ≤ ‖riemannZeta z₀‖ := by
      have h1 := norm_riemannZeta_ge_of_one_lt_re hσ1 t
      have h2 : (σ - 1) / 2 ≤ (σ - 1) / σ := div_le_div_of_nonneg_left (by linarith) (by linarith) hσ2
      exact h2.trans h1
    rw [norm_div]
    calc ‖riemannZeta w‖ / ‖riemannZeta z₀‖
        ≤ (2 * (|t| + 3)) / ((σ - 1) / 2) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = M := by dsimp [M]; field_simp [show σ - 1 ≠ 0 by linarith]; ring
  have hzeros : ∀ ρ ∈ Metric.closedBall z₀ (1 / 2 / 2), riemannZeta ρ = 0 → ρ.re ≤ z₀.re := by
    intro ρ hρ hz
    have hρ_lt1 : ρ.re < 1 := (nontrivial_zero_re_mem_Ioo hz fun ⟨n, hn⟩ => by
      have hre : ρ.re = -2 * (n + 1 : ℝ) := by rw [hn]; simp
      rw [Metric.mem_closedBall, dist_eq_norm] at hρ
      have h1 : |ρ.re - z₀.re| ≤ ‖ρ - z₀‖ := Complex.abs_re_le_norm _
      have hzre : z₀.re = σ := by simp [z₀]
      have hρ_pos : 0 < ρ.re := by linarith [(abs_le.mp (h1.trans hρ)).1]
      linarith [show (0 : ℝ) ≤ n by positivity]).2
    have hzre : z₀.re = σ := by simp [z₀]
    linarith
  have hres := landau_neg_re_logDeriv_center_le (R := 1 / 2) (by norm_num) hf_an hz₀_ne hbound hzeros
  refine hres.trans_eq ?_
  norm_num [M]

/-- Single-zero extraction form of `neg_re_logDeriv_riemannZeta_disk_le` when `β + i t` is a
zero of `riemannZeta` with `|t| ≥ 3`, `1 - 1 / 8 ≤ β < 1`, and `1 < σ ≤ 9 / 8`. -/
theorem neg_re_logDeriv_riemannZeta_disk_sub_zero {σ t β : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 9 / 8)
    (ht : 3 ≤ |t|) (hβ1 : 1 - 1 / 8 ≤ β) (hβ2 : β < 1)
    (hzero : riemannZeta ((β : ℂ) + (t : ℂ) * I) = 0) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re ≤
      8 * Real.log (4 * (|t| + 3) / (σ - 1)) - 1 / (σ - β) := by
  let z₀ : ℂ := (σ : ℂ) + (t : ℂ) * I
  let ρ₀ : ℂ := (β : ℂ) + (t : ℂ) * I
  let M : ℝ := 4 * (|t| + 3) / (σ - 1)
  have hf_an : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ (1 / 2)) :=
    riemannZeta_analyticOnNhd_closedBall_of_large_im (by linarith)
  have hz₀_ne : riemannZeta z₀ ≠ 0 := RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simp [z₀, hσ1])
  have hbound : ∀ w ∈ Metric.sphere z₀ (1 / 2), ‖riemannZeta w / riemannZeta z₀‖ ≤ M := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hw_re : 1 / 2 ≤ w.re := by
      have h1 : |w.re - z₀.re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm (w - z₀)
      have hzre : z₀.re = σ := by simp [z₀]
      linarith [(abs_le.mp (h1.trans hw.le)).1]
    have hw_norm_ge : 2 ≤ ‖w‖ := by
      have h1 : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm (w - z₀)
      have hzim : z₀.im = t := by simp [z₀]
      have hw_im : 5 / 2 ≤ |w.im| := by
        rcases le_or_gt 0 t with ht0 | ht0
        · rw [abs_of_nonneg ht0] at ht
          have := (abs_le.mp (h1.trans hw.le)).1
          have h2 : 5 / 2 ≤ w.im := by linarith
          exact h2.trans (le_abs_self _)
        · rw [abs_of_neg ht0] at ht
          have := (abs_le.mp (h1.trans hw.le)).2
          have h2 : 5 / 2 ≤ -w.im := by linarith
          exact h2.trans (neg_le_abs _)
      exact (by norm_num : (2 : ℝ) ≤ 5 / 2).trans (hw_im.trans (Complex.abs_im_le_norm w))
    have hnum : ‖riemannZeta w‖ ≤ 2 * (|t| + 3) := by
      have h1 := norm_riemannZeta_re_ge_half_le hw_re hw_norm_ge
      have hw_norm_le : ‖w‖ ≤ |t| + 3 := by
        have hz₀_le : ‖z₀‖ ≤ σ + |t| := by
          calc ‖z₀‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
            _ = |σ| + |t| := by simp [Complex.norm_real, Complex.norm_I]
            _ = σ + |t| := by rw [abs_of_pos (by linarith)]
        calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ 1 / 2 + (σ + |t|) := add_le_add hw.le hz₀_le
          _ ≤ |t| + 3 := by linarith
      linarith
    have hden : (σ - 1) / 2 ≤ ‖riemannZeta z₀‖ := by
      have h1 := norm_riemannZeta_ge_of_one_lt_re hσ1 t
      have h2 : (σ - 1) / 2 ≤ (σ - 1) / σ :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
      exact h2.trans h1
    rw [norm_div]
    calc ‖riemannZeta w‖ / ‖riemannZeta z₀‖
        ≤ (2 * (|t| + 3)) / ((σ - 1) / 2) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = M := by dsimp [M]; field_simp [show σ - 1 ≠ 0 by linarith]; ring
  have hzeros : ∀ ρ ∈ Metric.closedBall z₀ (1 / 2 / 2), riemannZeta ρ = 0 → ρ.re ≤ z₀.re := by
    intro ρ hρ hz
    have hρ_lt1 : ρ.re < 1 := (nontrivial_zero_re_mem_Ioo hz fun ⟨n, hn⟩ => by
      have hre : ρ.re = -2 * (n + 1 : ℝ) := by rw [hn]; simp
      rw [Metric.mem_closedBall, dist_eq_norm] at hρ
      have h1 : |ρ.re - z₀.re| ≤ ‖ρ - z₀‖ := Complex.abs_re_le_norm _
      have hzre : z₀.re = σ := by simp [z₀]
      have hρ_pos : 0 < ρ.re := by linarith [(abs_le.mp (h1.trans hρ)).1]
      linarith [show (0 : ℝ) ≤ n by positivity]).2
    have hzre : z₀.re = σ := by simp [z₀]
    linarith
  have hρ₀_mem : ρ₀ ∈ Metric.closedBall z₀ (1 / 2 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : ρ₀ - z₀ = ((β - σ : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [ρ₀, z₀]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hres := landau_neg_re_logDeriv_center_le_sub_zero (R := 1 / 2) (by norm_num)
    hf_an hz₀_ne hbound hzeros hρ₀_mem hzero
  have hinv_re : ((z₀ - ρ₀)⁻¹).re = 1 / (σ - β) := by
    have hdiff : z₀ - ρ₀ = ((σ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z₀, ρ₀]
    rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hinv_re] at hres
  refine hres.trans_eq ?_
  norm_num [M]

/-- **de la Vallée Poussin zero-free region for `|s.im| ≥ 3`**: there exists `c_lg > 0` (`c_lg ≤ 1 / 8`)
such that `riemannZeta s ≠ 0` whenever `3 ≤ |s.im|` and `1 - c_lg / Real.log (|s.im| + 3) ≤ s.re`. -/
theorem riemannZeta_zeroFree_large_im :
    ∃ c_lg : ℝ, 0 < c_lg ∧ c_lg ≤ 1 / 8 ∧
      ∀ s : ℂ, 3 ≤ |s.im| → 1 - c_lg / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨C₀, hC₀_pos, hreal⟩ := neg_re_logDeriv_riemannZeta_real_le
  let A₁ : ℝ := 3 * C₀ + 40 * Real.log 8 + 80
  have hA₁_pos : 0 < A₁ := by
    have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    positivity
  let u₀ : ℝ := min (1 / 4) (min (1 / (4 * A₁)) (1 / 320))
  have hu₀_pos : 0 < u₀ := lt_min (by norm_num) (lt_min (by positivity) (by norm_num))
  let δ : ℝ := u₀ ^ 2
  have hδ_pos : 0 < δ := sq_pos_of_pos hu₀_pos
  have hδ_le_eighth : δ ≤ 1 / 8 := by
    have hu : u₀ ≤ 1 / 4 := min_le_left _ _
    nlinarith [hu₀_pos]
  let c_lg : ℝ := δ / 8
  have hc_pos : 0 < c_lg := by positivity
  have hc_le : c_lg ≤ 1 / 8 := by dsimp [c_lg]; linarith
  refine ⟨c_lg, hc_pos, hc_le, fun s ht hs_re hzero => ?_⟩
  by_cases hs1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hs1 hzero
  have hβ_lt1 : s.re < 1 := not_le.mp hs1
  let t : ℝ := s.im
  let β : ℝ := s.re
  have hL_ge1 : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL_pos : 0 < Real.log (|t| + 3) := by linarith
  have hβ_ge : 1 - 1 / 8 ≤ β := by
    have h1 : c_lg / Real.log (|t| + 3) ≤ 1 / 8 :=
      (div_le_self hc_pos.le hL_ge1).trans hc_le
    linarith
  let L : ℝ := Real.log (|t| + 3)
  let σ : ℝ := 1 + δ / L
  have hσ1 : 1 < σ := by dsimp [σ]; linarith [div_pos hδ_pos hL_pos]
  have hσ2 : σ ≤ 9 / 8 := by
    have h1 : δ / L ≤ 1 / 8 := (div_le_self hδ_pos.le hL_ge1).trans hδ_le_eighth
    dsimp [σ]; linarith
  have hs_eq : (β : ℂ) + (t : ℂ) * I = s := Complex.re_add_im s
  have hzero' : riemannZeta ((β : ℂ) + (t : ℂ) * I) = 0 := by rwa [hs_eq]
  have h0_bd := hreal σ hσ1 (by linarith)
  have h1_bd : -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re ≤
      8 * Real.log (4 * (|t| + 3) / (σ - 1)) - 1 / (σ - β) :=
    neg_re_logDeriv_riemannZeta_disk_sub_zero hσ1 hσ2 ht hβ_ge hβ_lt1 hzero'
  have h2t_ge : 3 ≤ |2 * t| := by
    rw [abs_mul, abs_of_pos zero_lt_two]
    linarith
  have h2_bd := neg_re_logDeriv_riemannZeta_disk_le hσ1 (by linarith) h2t_ge
  have hineq := three_four_one_zeta_ineq hσ1 t
  have h_inv_σ : 1 / (σ - 1) = L / δ := by
    dsimp [σ]; rw [add_sub_cancel_left, one_div_div]
  have h_log_t : Real.log (4 * (|t| + 3) / (σ - 1)) ≤ 2 * L + Real.log 8 + Real.log (1 / δ) := by
    have harg : 4 * (|t| + 3) / (σ - 1) = (4 / δ) * ((|t| + 3) * L) := by
      rw [show σ - 1 = δ / L by dsimp [σ]; ring]
      field_simp [hδ_pos.ne', hL_pos.ne']
    have hL_le : L ≤ |t| + 3 := by
      have h1 := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 3)
      linarith
    have h1 : 4 * (|t| + 3) / (σ - 1) ≤ (8 / δ) * (|t| + 3) ^ 2 := by
      rw [harg]
      calc (4 / δ) * ((|t| + 3) * L)
          ≤ (4 / δ) * ((|t| + 3) * (|t| + 3)) := by gcongr
        _ = (4 / δ) * (|t| + 3) ^ 2 := by ring
        _ ≤ (8 / δ) * (|t| + 3) ^ 2 := by gcongr; norm_num
    calc Real.log (4 * (|t| + 3) / (σ - 1))
        ≤ Real.log ((8 / δ) * (|t| + 3) ^ 2) :=
          Real.log_le_log (div_pos (by positivity) (by linarith)) h1
      _ = Real.log (8 * (1 / δ)) + Real.log ((|t| + 3) ^ 2) := by
          rw [show (8 / δ) = 8 * (1 / δ) by ring, Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 8 + Real.log (1 / δ) + 2 * L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          simp [L]
      _ = 2 * L + Real.log 8 + Real.log (1 / δ) := by ring
  have h_log_2t : Real.log (4 * (|2 * t| + 3) / (σ - 1)) ≤ 2 * L + Real.log 8 + Real.log (1 / δ) := by
    have h2t_le : |2 * t| + 3 ≤ 2 * (|t| + 3) := by
      rw [abs_mul, abs_of_pos zero_lt_two]; linarith
    have hL_le : L ≤ |t| + 3 := by
      have h1 := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 3)
      linarith
    have h1 : 4 * (|2 * t| + 3) / (σ - 1) ≤ (8 / δ) * (|t| + 3) ^ 2 := by
      have harg : 4 * (|2 * t| + 3) / (σ - 1) = (4 / δ) * ((|2 * t| + 3) * L) := by
        rw [show σ - 1 = δ / L by dsimp [σ]; ring]
        field_simp [hδ_pos.ne', hL_pos.ne']
      rw [harg]
      calc (4 / δ) * ((|2 * t| + 3) * L)
          ≤ (4 / δ) * (2 * (|t| + 3) * (|t| + 3)) := by gcongr
        _ = (8 / δ) * (|t| + 3) ^ 2 := by ring
    calc Real.log (4 * (|2 * t| + 3) / (σ - 1))
        ≤ Real.log ((8 / δ) * (|t| + 3) ^ 2) :=
          Real.log_le_log (div_pos (by positivity) (by linarith)) h1
      _ = Real.log 8 + Real.log (1 / δ) + 2 * L := by
          rw [show (8 / δ) = 8 * (1 / δ) by ring, Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          simp [L]
      _ = 2 * L + Real.log 8 + Real.log (1 / δ) := by ring
  have h_log_inv_δ : Real.log (1 / δ) ≤ 2 / u₀ := by
    have h1 : Real.log (1 / u₀) ≤ 1 / u₀ := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / u₀)
      linarith
    have heq : 1 / δ = (1 / u₀) ^ 2 := by dsimp [δ]; ring
    calc Real.log (1 / δ) = Real.log ((1 / u₀) ^ 2) := by rw [heq]
      _ = 2 * Real.log (1 / u₀) := by rw [Real.log_pow, Nat.cast_ofNat]
      _ ≤ 2 * (1 / u₀) := by linarith
      _ = 2 / u₀ := by ring
  have h_comb : 4 / (σ - β) ≤ 3 * (L / δ) + 3 * C₀ + 40 * (2 * L + Real.log 8 + 2 / u₀) := by
    have h1_sum : 4 * (8 * Real.log (4 * (|t| + 3) / (σ - 1)) - 1 / (σ - β)) =
        32 * Real.log (4 * (|t| + 3) / (σ - 1)) - 4 / (σ - β) := by ring
    have hsum : 4 / (σ - β) ≤ 3 * (1 / (σ - 1) + C₀) +
        32 * Real.log (4 * (|t| + 3) / (σ - 1)) +
        8 * Real.log (4 * (|2 * t| + 3) / (σ - 1)) := by
      linarith [hineq, h0_bd, h1_bd, h2_bd, h1_sum]
    rw [h_inv_σ] at hsum
    calc 4 / (σ - β)
        ≤ 3 * (L / δ + C₀) + 32 * (2 * L + Real.log 8 + 2 / u₀) +
            8 * (2 * L + Real.log 8 + 2 / u₀) := by
          linarith [hsum, h_log_t, h_log_2t, h_log_inv_δ]
      _ = 3 * (L / δ) + 3 * C₀ + 40 * (2 * L + Real.log 8 + 2 / u₀) := by ring
  have h_tail : 3 * C₀ + 40 * (2 * L + Real.log 8 + 2 / u₀) ≤ (1 / (2 * δ)) * L := by
    have hA_δ : A₁ ≤ 1 / (4 * δ) := by
      have hu1 : u₀ ≤ 1 / 4 := min_le_left _ _
      have hu2 : u₀ ≤ 1 / (4 * A₁) := (min_le_right _ _).trans (min_le_left _ _)
      have hsq : u₀ ^ 2 ≤ 1 / (4 * A₁) := by
        calc u₀ ^ 2 = u₀ * u₀ := by ring
          _ ≤ 1 * (1 / (4 * A₁)) := mul_le_mul (by linarith) hu2 hu₀_pos.le zero_le_one
          _ = 1 / (4 * A₁) := one_mul _
      rw [show A₁ = 1 / (4 * (1 / (4 * A₁))) by field_simp [hA₁_pos.ne']]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by dsimp [δ]; linarith)
    have h80_u : 80 / u₀ ≤ (1 / (4 * δ)) * L := by
      have hu3 : u₀ ≤ 1 / 320 := (min_le_right _ _).trans (min_le_right _ _)
      have h1 : 80 / u₀ ≤ 1 / (4 * δ) := by
        dsimp [δ]
        rw [div_le_div_iff₀ hu₀_pos (by positivity)]
        have : 320 * u₀ ≤ 1 := by
          rw [← le_div_iff₀' (by norm_num : (0 : ℝ) < 320)]
          exact hu3
        nlinarith [hu₀_pos]
      exact h1.trans (le_mul_of_one_le_right (by positivity) hL_ge1)
    have hsplit : 3 * C₀ + 40 * (2 * L + Real.log 8 + 2 / u₀) =
        (3 * C₀ + 40 * Real.log 8 + 80) + 80 * (L - 1) + 80 / u₀ := by ring
    have hpart1 : (3 * C₀ + 40 * Real.log 8 + 80) + 80 * (L - 1) ≤ A₁ * L := by
      have hA_def : A₁ = 3 * C₀ + 40 * Real.log 8 + 80 := rfl
      have hC₀_nn : 0 ≤ 3 * C₀ + 40 * Real.log 8 := by
        have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
        positivity
      rw [hA_def]
      nlinarith [hL_ge1]
    have hA_L : A₁ * L ≤ (1 / (4 * δ)) * L := mul_le_mul_of_nonneg_right hA_δ hL_pos.le
    calc 3 * C₀ + 40 * (2 * L + Real.log 8 + 2 / u₀)
        = (3 * C₀ + 40 * Real.log 8 + 80) + 80 * (L - 1) + 80 / u₀ := hsplit
      _ ≤ A₁ * L + (1 / (4 * δ)) * L := add_le_add hpart1 h80_u
      _ ≤ (1 / (4 * δ)) * L + (1 / (4 * δ)) * L := add_le_add hA_L le_rfl
      _ = (1 / (2 * δ)) * L := by ring
  have h4_bd : 4 / (σ - β) ≤ (7 / (2 * δ)) * L := by
    calc 4 / (σ - β)
        ≤ 3 * (L / δ) + (3 * C₀ + 40 * (2 * L + Real.log 8 + 2 / u₀)) := by
          linarith [h_comb]
      _ ≤ 3 * (L / δ) + (1 / (2 * δ)) * L := add_le_add le_rfl h_tail
      _ = (7 / (2 * δ)) * L := by ring
  have hσβ_pos : 0 < σ - β := by linarith
  have h_lower : (8 * δ) / (7 * L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity)]
    have h4' : 4 ≤ (7 / (2 * δ)) * L * (σ - β) := (div_le_iff₀ hσβ_pos).mp h4_bd
    calc 8 * δ ≤ (7 * L) * (σ - β) := by
          have hpos_2δ : 0 ≤ 2 * δ := by positivity
          calc 8 * δ = (2 * δ) * 4 := by ring
            _ ≤ (2 * δ) * ((7 / (2 * δ)) * L * (σ - β)) := mul_le_mul_of_nonneg_left h4' hpos_2δ
            _ = (7 * L) * (σ - β) := by field_simp [hδ_pos.ne']
      _ = (σ - β) * (7 * L) := mul_comm _ _
  have hs_re' : 1 - c_lg / L ≤ β := hs_re
  have h_upper : σ - β ≤ (9 * δ) / (8 * L) := by
    have hc_eq : c_lg / L = δ / (8 * L) := by dsimp [c_lg]; ring
    have h_sum_frac : δ / L + δ / (8 * L) = (9 * δ) / (8 * L) := by
      field_simp [hL_pos.ne']; ring
    dsimp [σ]
    linarith [hs_re', hc_eq, h_sum_frac]
  have h_contra : (8 * δ) / (7 * L) ≤ (9 * δ) / (8 * L) := h_lower.trans h_upper
  have h_num : (9 * δ) / (8 * L) < (8 * δ) / (7 * L) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hδ_pos, hL_pos]
  linarith

/-- **Unified de la Vallée Poussin zero-free region** for `riemannZeta₁` (and hence `riemannZeta`
away from `s = 1`): there exists `c_zf > 0` (`c_zf ≤ 1 / 8`) such that `riemannZeta₁ s ≠ 0`
whenever `1 - c_zf / Real.log (|s.im| + 3) ≤ s.re`. -/
theorem riemannZeta_zeroFree_region :
    ∃ c_zf : ℝ, 0 < c_zf ∧ c_zf ≤ 1 / 8 ∧
      ∀ s : ℂ, 1 - c_zf / Real.log (|s.im| + 3) ≤ s.re → riemannZeta₁ s ≠ 0 := by
  obtain ⟨ε₀, hε₀_pos, hε₀_le, _, _, hsm_nozero, _⟩ := zeta_small_im_zeroFree_and_bound
  obtain ⟨c_lg, hclg_pos, hclg_le, hlg_nozero⟩ := riemannZeta_zeroFree_large_im
  let c_zf : ℝ := min (ε₀ * Real.log 3) c_lg
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hczf_pos : 0 < c_zf := lt_min (mul_pos hε₀_pos hlog3_pos) hclg_pos
  have hczf_le : c_zf ≤ 1 / 8 := (min_le_right _ _).trans hclg_le
  refine ⟨c_zf, hczf_pos, hczf_le, fun s hs_re => ?_⟩
  by_cases him : |s.im| ≤ 3
  · have hlog_ge : Real.log 3 ≤ Real.log (|s.im| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have h_div_le : c_zf / Real.log (|s.im| + 3) ≤ ε₀ := by
      rw [div_le_iff₀ (Real.log_pos (by linarith [abs_nonneg s.im]))]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlog_ge hε₀_pos.le)
    exact hsm_nozero s (by linarith) him
  · have him3 : 3 ≤ |s.im| := (not_le.mp him).le
    have h_div_le : c_zf / Real.log (|s.im| + 3) ≤ c_lg / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_right (min_le_right _ _) (Real.log_nonneg (by linarith [abs_nonneg s.im]))
    have hz : riemannZeta s ≠ 0 := hlg_nozero s him3 (by linarith)
    have hs1 : s ≠ 1 := by
      intro h; subst h; simp at him3; norm_num at him3
    intro h0
    apply hz
    rw [riemannZeta_eq_inv_sub_mul hs1, h0, mul_zero]

private lemma norm_neg_logDeriv_riemannZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤ -(logDeriv riemannZeta (s.re : ℂ)).re := by
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum : LSeriesSummable (fun n : ℕ => (Λ n : ℂ)) s :=
    LSeriesSummable_vonMangoldt_iff.mpr hs
  have hreal_eq := neg_re_logDeriv_riemannZeta_eq_tsum (σ := s.re) (t := 0) hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, mul_one] at hreal_eq
  have hsumm_r : Summable fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-s.re) := by
    simpa using summable_vonMangoldt_rpow_cos (σ := s.re) (t := 0) hs
  rw [← hL, LSeries]
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  rw [hreal_eq]
  refine hsum.norm.tsum_le_tsum (fun n => ?_) hsumm_r
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    split_ifs with h0
    · exact absurd h0 hn
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), div_eq_mul_inv,
        ← Real.rpow_neg (Nat.cast_nonneg n)]

private lemma norm_neg_logDeriv_riemannZeta_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤ -(logDeriv riemannZeta (2 : ℂ)).re := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  have h1 := norm_neg_logDeriv_riemannZeta_of_one_lt_re hs1
  have hreal_s := neg_re_logDeriv_riemannZeta_eq_tsum (σ := s.re) (t := 0) hs1
  have hreal_2 := neg_re_logDeriv_riemannZeta_eq_tsum (σ := 2) (t := 0) (by norm_num)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, mul_one] at hreal_s hreal_2
  have hreal_2' : -(logDeriv riemannZeta (2 : ℂ)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-2 : ℝ) := by
    simpa using hreal_2
  have hss : Summable fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-s.re) := by
    simpa using summable_vonMangoldt_rpow_cos (σ := s.re) (t := 0) hs1
  have hs2 : Summable fun n : ℕ => if n = 0 then (0 : ℝ) else Λ n * (n : ℝ) ^ (-2 : ℝ) := by
    simpa using summable_vonMangoldt_rpow_cos (σ := 2) (t := 0) (by norm_num)
  have hle : -(logDeriv riemannZeta (s.re : ℂ)).re ≤ -(logDeriv riemannZeta (2 : ℂ)).re := by
    rw [hreal_s, hreal_2']
    refine hss.tsum_le_tsum (fun n => ?_) hs2
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · split_ifs with h0
      · exact absurd h0 hn
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        exact mul_le_mul_of_nonneg_left hpow ArithmeticFunction.vonMangoldt_nonneg
  exact h1.trans hle

private lemma norm_neg_logDeriv_riemannZeta_band_le
    {c_zf c₁ : ℝ} (hczf_pos : 0 < c_zf) (hczf_le : c_zf ≤ 1 / 8)
    (hc₁_zf16 : c₁ ≤ c_zf / 16)
    (hzf : ∀ s : ℂ, 1 - c_zf / Real.log (|s.im| + 3) ≤ s.re → riemannZeta₁ s ≠ 0)
    {s : ℂ} (hs_re : 1 - c₁ / Real.log (|s.im| + 3) ≤ s.re) (him3 : 3 ≤ |s.im|)
    (hband : s.re ≤ 1 + (c_zf / (2 * Real.log (2 * |s.im| + 4))) / 4) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤
      ((224 / c_zf) * (2 * Real.log (16 / c_zf) + 12)) * (Real.log (|s.im| + 3)) ^ 2 := by
  let t : ℝ := s.im
  let σ : ℝ := s.re
  have hs_eq : (σ : ℂ) + (t : ℂ) * I = s := Complex.re_add_im s
  have hL3_ge1 : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL2_ge2 : 2 ≤ Real.log (2 * |t| + 4) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    have hexp2 : Real.exp 2 < 10 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    linarith
  have hL2_le : Real.log (2 * |t| + 4) ≤ 2 * Real.log (|t| + 3) := by
    have h1 : 2 * |t| + 4 ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
    calc Real.log (2 * |t| + 4) ≤ Real.log ((|t| + 3) ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; ring
  let R₀ : ℝ := c_zf / (2 * Real.log (2 * |t| + 4))
  have hR₀_pos : 0 < R₀ := by positivity
  have hR₀_le : R₀ ≤ 1 / 32 := by
    have h1 : c_zf / (2 * Real.log (2 * |t| + 4)) ≤ (1 / 8) / (2 * 2) :=
      div_le_div₀ (by norm_num) hczf_le (by norm_num) (by linarith)
    linarith
  let z₀ : ℂ := ((1 + R₀ / 2 : ℝ) : ℂ) + (t : ℂ) * I
  let r : ℝ := (3 / 4) * R₀
  have hr_nn : 0 ≤ r := by positivity
  have hrR : r < R₀ := by dsimp [r]; linarith
  have hball_diff : DifferentiableOn ℂ riemannZeta (Metric.ball z₀ R₀) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw1 : w ≠ 1 := by
      intro h1
      have him : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have hwim : w.im = 0 := by rw [h1]; simp
      have hzim : z₀.im = t := by simp [z₀]
      rw [hwim, hzim, zero_sub, abs_neg] at him
      linarith [hw.le]
    exact (differentiableAt_riemannZeta hw1).differentiableWithinAt
  have hball_ne : ∀ w ∈ Metric.ball z₀ R₀, riemannZeta w ≠ 0 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw1 : w ≠ 1 := by
      intro h1
      have him : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have hwim : w.im = 0 := by rw [h1]; simp
      have hzim : z₀.im = t := by simp [z₀]
      rw [hwim, hzim, zero_sub, abs_neg] at him
      linarith [hw.le]
    have hw_im_le : |w.im| + 3 ≤ 2 * |t| + 4 := by
      have him : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have hzim : z₀.im = t := by simp [z₀]
      have habs : |w.im| ≤ |t| + R₀ := by
        have hup := (abs_le.mp (him.trans hw.le)).2
        have hlo := (abs_le.mp (him.trans hw.le)).1
        rw [abs_le]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
      linarith
    have hlog_w : Real.log (|w.im| + 3) ≤ Real.log (2 * |t| + 4) :=
      Real.log_le_log (by linarith [abs_nonneg w.im]) hw_im_le
    have h_zf_w : 1 - c_zf / Real.log (|w.im| + 3) ≤ w.re := by
      have hre : |w.re - z₀.re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
      have hzre : z₀.re = 1 + R₀ / 2 := by simp [z₀]
      have hre_lt : |w.re - z₀.re| < R₀ := hre.trans_lt hw
      have hwre_gt : 1 - R₀ / 2 < w.re := by
        linarith [(abs_lt.mp hre_lt).1]
      have hc1 : c_zf / Real.log (2 * |t| + 4) ≤ c_zf / Real.log (|w.im| + 3) :=
        div_le_div_of_nonneg_left hczf_pos.le (Real.log_pos (by linarith [abs_nonneg w.im])) hlog_w
      have hc_quarter : c_zf / (4 * Real.log (2 * |t| + 4)) ≤ c_zf / Real.log (|w.im| + 3) := by
        have h4 : Real.log (2 * |t| + 4) ≤ 4 * Real.log (2 * |t| + 4) := by linarith [hL2_ge2]
        exact (div_le_div_of_nonneg_left hczf_pos.le (by linarith [hL2_ge2]) h4).trans hc1
      have hR_half : R₀ / 2 = c_zf / (4 * Real.log (2 * |t| + 4)) := by
        dsimp [R₀]; ring
      linarith
    have hz1 := hzf w h_zf_w
    intro h0
    apply hz1
    have heq : (w - 1) * riemannZeta w = riemannZeta₁ w := by
      rw [riemannZeta_eq_inv_sub_mul hw1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hw1), one_mul]
    rw [← heq, h0, mul_zero]
  let M : ℝ := 8 * (|t| + 3) / R₀
  have hM_bound : ∀ w ∈ Metric.ball z₀ R₀, ‖riemannZeta w / riemannZeta z₀‖ ≤ M := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_re : 1 / 2 ≤ w.re := by
      have hre : |w.re - z₀.re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
      have hzre : z₀.re = 1 + R₀ / 2 := by simp [z₀]
      linarith [(abs_le.mp (hre.trans hw.le)).1]
    have hw_norm_ge : 2 ≤ ‖w‖ := by
      have him : |w.im - z₀.im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have hzim : z₀.im = t := by simp [z₀]
      have hw_im : 2 ≤ |w.im| := by
        rcases le_or_gt 0 t with ht0 | ht0
        · rw [abs_of_nonneg ht0] at him3
          have := (abs_le.mp (him.trans hw.le)).1
          exact (by linarith : 2 ≤ w.im).trans (le_abs_self _)
        · rw [abs_of_neg ht0] at him3
          have := (abs_le.mp (him.trans hw.le)).2
          exact (by linarith : 2 ≤ -w.im).trans (neg_le_abs _)
      exact hw_im.trans (Complex.abs_im_le_norm w)
    have hnum : ‖riemannZeta w‖ ≤ 2 * (|t| + 3) := by
      have h1 := norm_riemannZeta_re_ge_half_le hw_re hw_norm_ge
      have hw_norm_le : ‖w‖ ≤ |t| + 3 := by
        have hz₀_le : ‖z₀‖ ≤ (1 + R₀ / 2) + |t| := by
          calc ‖z₀‖ ≤ ‖((1 + R₀ / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
            _ = |1 + R₀ / 2| + |t| := by
                rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
                  Real.norm_eq_abs, Complex.norm_I, mul_one]
            _ = (1 + R₀ / 2) + |t| := by rw [abs_of_pos (by linarith)]
        calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ R₀ + ((1 + R₀ / 2) + |t|) := add_le_add hw.le hz₀_le
          _ ≤ |t| + 3 := by linarith
      linarith
    have hden : R₀ / 4 ≤ ‖riemannZeta z₀‖ := by
      have h1 := norm_riemannZeta_ge_of_one_lt_re (show 1 < 1 + R₀ / 2 by linarith) t
      have h2 : R₀ / 4 ≤ ((1 + R₀ / 2 : ℝ) - 1) / (1 + R₀ / 2 : ℝ) := by
        rw [show (1 + R₀ / 2 : ℝ) - 1 = R₀ / 2 by ring, show R₀ / 4 = (R₀ / 2) / 2 by ring]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      exact h2.trans h1
    rw [norm_div]
    calc ‖riemannZeta w‖ / ‖riemannZeta z₀‖
        ≤ (2 * (|t| + 3)) / (R₀ / 4) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = M := by dsimp [M]; field_simp [hR₀_pos.ne']; ring
  have hs_mem : s ∈ Metric.closedBall z₀ r := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← hs_eq]
    have hdiff : ((σ : ℂ) + (t : ℂ) * I) - z₀ = ((σ - (1 + R₀ / 2) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z₀]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hc₁_div : c₁ / Real.log (|t| + 3) ≤ R₀ / 4 := by
      dsimp [R₀]
      have h1 : c₁ / Real.log (|t| + 3) ≤ (c_zf / 16) / Real.log (|t| + 3) :=
        div_le_div_of_nonneg_right hc₁_zf16 (by linarith)
      have h2 : (c_zf / 16) / Real.log (|t| + 3) ≤ c_zf / (8 * Real.log (2 * |t| + 4)) := by
        rw [show (c_zf / 16) / Real.log (|t| + 3) = c_zf / (16 * Real.log (|t| + 3)) by ring]
        exact div_le_div_of_nonneg_left hczf_pos.le (by positivity) (by linarith)
      exact h1.trans (h2.trans_eq (by ring))
    constructor <;> dsimp [r] <;> linarith
  have hld := landau_logDeriv_le_of_ne_zero hr_nn hrR hball_diff hball_ne hM_bound hs_mem
  have hnorm_eq : ‖-deriv riemannZeta s / riemannZeta s‖ = ‖logDeriv riemannZeta s‖ := by
    rw [logDeriv_apply, neg_div, norm_neg]
  have hcoeff : 2 * (R₀ + r) / (R₀ - r) ^ 2 = 56 / R₀ := by
    dsimp [r]; field_simp [hR₀_pos.ne']; ring
  have hlogM_bd : Real.log M ≤ (2 * Real.log (16 / c_zf) + 12) * Real.log (|t| + 3) := by
    have harg : M = 16 * (|t| + 3) * Real.log (2 * |t| + 4) / c_zf := by
      dsimp [M, R₀]; field_simp [hczf_pos.ne', (by linarith : Real.log (2 * |t| + 4) ≠ 0)]; ring
    have hL2_le_t : Real.log (2 * |t| + 4) ≤ 2 * (|t| + 3) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * |t| + 4)
      linarith
    have hM_le : M ≤ (32 / c_zf) * (|t| + 3) ^ 2 := by
      rw [harg]
      calc 16 * (|t| + 3) * Real.log (2 * |t| + 4) / c_zf
          ≤ 16 * (|t| + 3) * (2 * (|t| + 3)) / c_zf := by gcongr
        _ = (32 / c_zf) * (|t| + 3) ^ 2 := by ring
    calc Real.log M ≤ Real.log ((32 / c_zf) * (|t| + 3) ^ 2) :=
          Real.log_le_log (by dsimp [M]; positivity) hM_le
      _ = Real.log (2 * (16 / c_zf)) + Real.log ((|t| + 3) ^ 2) := by
          rw [show (32 / c_zf) = 2 * (16 / c_zf) by ring,
            Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 2 + Real.log (16 / c_zf) + 2 * Real.log (|t| + 3) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          ring
      _ ≤ (2 * Real.log (16 / c_zf) + 12) * Real.log (|t| + 3) := by
          have hlog2_lt : Real.log 2 ≤ 1 := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            exact Real.exp_one_gt_d9.le.trans' (by norm_num)
          have h16_nn : 0 ≤ Real.log (16 / c_zf) := Real.log_nonneg (by
            rw [le_div_iff₀ hczf_pos]; linarith)
          nlinarith [hL3_ge1]
  have h56 : 56 / R₀ = (112 / c_zf) * Real.log (2 * |t| + 4) := by
    dsimp [R₀]; field_simp [hczf_pos.ne']; ring
  have h56_le : 56 / R₀ ≤ (224 / c_zf) * Real.log (|t| + 3) := by
    calc 56 / R₀ = (112 / c_zf) * Real.log (2 * |t| + 4) := h56
      _ ≤ (112 / c_zf) * (2 * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hL2_le (by positivity)
      _ = (224 / c_zf) * Real.log (|t| + 3) := by ring
  have hM_ge1 : 1 ≤ M := by
    dsimp [M]; rw [le_div_iff₀ hR₀_pos]; linarith [abs_nonneg t]
  have hmul := mul_le_mul h56_le hlogM_bd (Real.log_nonneg hM_ge1) (by positivity)
  rw [hnorm_eq]
  rw [hcoeff] at hld
  calc ‖logDeriv riemannZeta s‖ ≤ (56 / R₀) * Real.log M := hld
    _ ≤ ((224 / c_zf) * Real.log (|t| + 3)) *
          ((2 * Real.log (16 / c_zf) + 12) * Real.log (|t| + 3)) := hmul
    _ = ((224 / c_zf) * (2 * Real.log (16 / c_zf) + 12)) * (Real.log (|t| + 3)) ^ 2 := by ring

private lemma norm_neg_logDeriv_riemannZeta_large_im_le
    {c_zf c₁ C₀ C_dir2 C₁ : ℝ} (hczf_pos : 0 < c_zf) (hczf_le : c_zf ≤ 1 / 8)
    (hc₁_zf16 : c₁ ≤ c_zf / 16) (hC₀_pos : 0 < C₀) (hC₁_pos : 0 < C₁)
    (hC_dir2_pos : 0 < C_dir2)
    (hC_ld_le : (224 / c_zf) * (2 * Real.log (16 / c_zf) + 12) + (16 / c_zf + C₀) + C_dir2 ≤ C₁)
    (hC_dir2_le : C_dir2 ≤ C₁)
    (hC_dir2_eq : -(logDeriv riemannZeta (2 : ℂ)).re ≤ C_dir2)
    (hzf : ∀ s : ℂ, 1 - c_zf / Real.log (|s.im| + 3) ≤ s.re → riemannZeta₁ s ≠ 0)
    (hreal : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C₀)
    {s : ℂ} (hs_re : 1 - c₁ / Real.log (|s.im| + 3) ≤ s.re) (him3 : 3 ≤ |s.im|) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C₁ * (Real.log (|s.im| + 3)) ^ 2 := by
  let t : ℝ := s.im
  let σ : ℝ := s.re
  have hL3_ge1 : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL2_ge2 : 2 ≤ Real.log (2 * |t| + 4) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    have hexp2 : Real.exp 2 < 10 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    linarith
  have hL2_le : Real.log (2 * |t| + 4) ≤ 2 * Real.log (|t| + 3) := by
    have h1 : 2 * |t| + 4 ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
    calc Real.log (2 * |t| + 4) ≤ Real.log ((|t| + 3) ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; ring
  let R₀ : ℝ := c_zf / (2 * Real.log (2 * |t| + 4))
  have hR₀_pos : 0 < R₀ := by positivity
  by_cases hband : σ ≤ 1 + R₀ / 4
  · have hbd := norm_neg_logDeriv_riemannZeta_band_le hczf_pos hczf_le hc₁_zf16 hzf hs_re him3 hband
    have hrem : 0 ≤ (16 / c_zf + C₀) + C_dir2 := by positivity
    have hC_le : (224 / c_zf) * (2 * Real.log (16 / c_zf) + 12) ≤ C₁ := by linarith
    exact hbd.trans (mul_le_mul_of_nonneg_right hC_le (sq_nonneg _))
  · have hσ_gt : 1 + R₀ / 4 < σ := not_le.mp hband
    have hσ1 : 1 < s.re := by change 1 < σ; linarith
    have h1 := norm_neg_logDeriv_riemannZeta_of_one_lt_re hσ1
    by_cases hσ2 : σ ≤ 2
    · have hr := hreal σ hσ1 hσ2
      have hinv_le : 1 / (σ - 1) ≤ (16 / c_zf) * Real.log (|t| + 3) := by
        have h_sub : R₀ / 4 < σ - 1 := by linarith
        have hinv1 : 1 / (σ - 1) ≤ 4 / R₀ := by
          rw [div_le_div_iff₀ (by linarith) hR₀_pos]
          linarith
        have h4R : 4 / R₀ = (8 / c_zf) * Real.log (2 * |t| + 4) := by
          dsimp [R₀]; field_simp [hczf_pos.ne']; ring
        have h4R_le : 4 / R₀ ≤ (16 / c_zf) * Real.log (|t| + 3) := by
          calc 4 / R₀ = (8 / c_zf) * Real.log (2 * |t| + 4) := h4R
            _ ≤ (8 / c_zf) * (2 * Real.log (|t| + 3)) :=
                mul_le_mul_of_nonneg_left hL2_le (by positivity)
            _ = (16 / c_zf) * Real.log (|t| + 3) := by ring
        exact hinv1.trans h4R_le
      have h16_nn : 0 ≤ Real.log (16 / c_zf) := Real.log_nonneg (by
        rw [le_div_iff₀ hczf_pos]; linarith)
      have hp1 : 0 ≤ (224 / c_zf) * (2 * Real.log (16 / c_zf) + 12) := by positivity
      have hC_ge : 16 / c_zf + C₀ ≤ C₁ := by linarith
      have h_log_sq : Real.log (|t| + 3) ≤ (Real.log (|t| + 3)) ^ 2 := by
        nlinarith [hL3_ge1]
      calc ‖-deriv riemannZeta s / riemannZeta s‖
          ≤ -(logDeriv riemannZeta (σ : ℂ)).re := h1
        _ ≤ 1 / (σ - 1) + C₀ := hr
        _ ≤ (16 / c_zf) * Real.log (|t| + 3) + C₀ := by linarith
        _ ≤ (16 / c_zf + C₀) * Real.log (|t| + 3) := by nlinarith [hL3_ge1, hC₀_pos]
        _ ≤ C₁ * (Real.log (|t| + 3)) ^ 2 := by nlinarith [hC_ge, h_log_sq]
    · have hσ2' : 2 ≤ s.re := by change 2 ≤ σ; linarith
      have h2 := norm_neg_logDeriv_riemannZeta_of_two_le_re hσ2'
      have hsq : 1 ≤ (Real.log (|t| + 3)) ^ 2 := by nlinarith [hL3_ge1]
      calc ‖-deriv riemannZeta s / riemannZeta s‖
          ≤ -(logDeriv riemannZeta (2 : ℂ)).re := h2
        _ ≤ C_dir2 := hC_dir2_eq
        _ ≤ C₁ := hC_dir2_le
        _ ≤ C₁ * (Real.log (|t| + 3)) ^ 2 := le_mul_of_one_le_right hC₁_pos.le hsq

/-- **Logarithmic derivative upper bound inside the de la Vallée Poussin zero-free region**:
provides explicit constants `0 < c₁ ≤ 1 / 8` and `C₁ > 0` witnessing `ZetaZeroFreeData`. -/
theorem norm_neg_logDeriv_riemannZeta_le :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 8 ∧ ∃ C₁ > 0,
      (∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 3) ≤ s.re → riemannZeta₁ s ≠ 0) ∧
      (∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 3) ≤ s.re → 3 ≤ |s.im| →
        ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C₁ * (Real.log (|s.im| + 3)) ^ 2) ∧
      (∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 3) ≤ s.re → |s.im| ≤ 3 → s ≠ 1 →
        ‖-deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹‖ ≤ C₁) := by
  obtain ⟨c_zf, hczf_pos, hczf_le, hzf⟩ := riemannZeta_zeroFree_region
  obtain ⟨ε₀, hε₀_pos, hε₀_le, C_sm, hC_sm_pos, hsm_nozero, hsm_bd⟩ := zeta_small_im_zeroFree_and_bound
  obtain ⟨C₀, hC₀_pos, hreal⟩ := neg_re_logDeriv_riemannZeta_real_le
  let c₁ : ℝ := min (c_zf / 16) (ε₀ * Real.log 3)
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc₁_pos : 0 < c₁ := lt_min (by positivity) (mul_pos hε₀_pos hlog3_pos)
  have hc₁_le : c₁ ≤ 1 / 8 := (min_le_left _ _).trans (by linarith)
  have hc₁_zf : c₁ ≤ c_zf := (min_le_left _ _).trans (by linarith)
  have hc₁_zf16 : c₁ ≤ c_zf / 16 := min_le_left _ _
  have hc₁_sm : c₁ ≤ ε₀ * Real.log 3 := min_le_right _ _
  let C_dir2 : ℝ := -(logDeriv riemannZeta (2 : ℂ)).re + 1
  have hC_dir2_pos : 0 < C_dir2 := by
    have h0 := neg_re_logDeriv_riemannZeta_eq_tsum (σ := 2) (t := 0) (by norm_num)
    simp only [Complex.ofReal_ofNat, Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero,
      mul_one] at h0
    have hnn : 0 ≤ -(logDeriv riemannZeta (2 : ℂ)).re := by
      rw [h0]
      exact tsum_nonneg fun n => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    linarith
  let C_ld : ℝ := (224 / c_zf) * (2 * Real.log (16 / c_zf) + 12) + (16 / c_zf + C₀) + C_dir2
  let C₁ : ℝ := max C_sm (max C_ld C_dir2)
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hC_sm_pos (le_max_left _ _)
  have hC_ld_le : C_ld ≤ C₁ := (le_max_left C_ld C_dir2).trans (le_max_right _ _)
  have hC_sm_le : C_sm ≤ C₁ := le_max_left _ _
  have hC_dir2_le : C_dir2 ≤ C₁ := (le_max_right C_ld C_dir2).trans (le_max_right _ _)
  refine ⟨c₁, hc₁_pos, hc₁_le, C₁, hC₁_pos, ?_, ?_, ?_⟩
  · intro s hs_re
    have h1 : c₁ / Real.log (|s.im| + 3) ≤ c_zf / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_right hc₁_zf (Real.log_nonneg (by linarith [abs_nonneg s.im]))
    exact hzf s (by linarith)
  · exact fun s hs_re him3 => norm_neg_logDeriv_riemannZeta_large_im_le hczf_pos hczf_le hc₁_zf16
      hC₀_pos hC₁_pos hC_dir2_pos hC_ld_le hC_dir2_le (by dsimp [C_dir2]; linarith) hzf hreal hs_re him3
  · intro s hs_re him3 hs1
    by_cases hs2 : s.re ≤ 2
    · have hlog_ge : Real.log 3 ≤ Real.log (|s.im| + 3) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
      have hc_le_ε : c₁ / Real.log (|s.im| + 3) ≤ ε₀ := by
        rw [div_le_iff₀ (Real.log_pos (by linarith [abs_nonneg s.im]))]
        exact hc₁_sm.trans (mul_le_mul_of_nonneg_left hlog_ge hε₀_pos.le)
      have hs_ge : 1 - ε₀ ≤ s.re := by linarith
      have hz1 : riemannZeta₁ s ≠ 0 := hsm_nozero s hs_ge him3
      have heq_ld : -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹ = -logDeriv riemannZeta₁ s := by
        have hsub := logDeriv_riemannZeta_eq_sub hs1 hz1
        rw [logDeriv_apply] at hsub
        rw [neg_div, hsub]
        ring
      rw [heq_ld, norm_neg]
      exact (hsm_bd s hs_ge hs2 him3).trans hC_sm_le
    · have hs2' : 2 ≤ s.re := (not_le.mp hs2).le
      have hinv_le : ‖(s - 1)⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        have hre : 1 ≤ (s - 1).re := by simp; linarith
        exact inv_le_one_of_one_le₀ (hre.trans (Complex.re_le_norm (s - 1)))
      have htri : ‖-deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹‖ ≤
          ‖-deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
      exact (htri.trans (add_le_add (norm_neg_logDeriv_riemannZeta_of_two_le_re hs2') hinv_le)).trans
        hC_dir2_le

/-- Unconditional witness of `ZetaZeroFreeData` for `riemannZeta`. -/
@[irreducible] def unconditionalZetaZeroFreeData : ZetaZeroFreeData :=
  let h := norm_neg_logDeriv_riemannZeta_le
  { c := h.choose
    hc_pos := h.choose_spec.1
    hc_le := h.choose_spec.2.1
    C := h.choose_spec.2.2.choose
    hC_pos := h.choose_spec.2.2.choose_spec.1
    zeroFree_zetaOne := h.choose_spec.2.2.choose_spec.2.1
    norm_logDeriv_large := h.choose_spec.2.2.choose_spec.2.2.1
    norm_logDeriv_small := h.choose_spec.2.2.choose_spec.2.2.2 }

/-! ### Unconditional de la Vallée Poussin Prime Number Theorem Error Terms -/

private lemma LFunctionTrivChar₁_one_eq_riemannZeta₁ (s : ℂ) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = riemannZeta₁ s := by
  by_cases hs : s = 1
  · subst hs; simp [DirichletCharacter.LFunctionTrivChar₁]
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs, Nat.primeFactors_one,
      Finset.prod_empty, one_mul, riemannZeta_eq_inv_sub_mul hs, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

private lemma LFunction_one_eq_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  change DirichletCharacter.LFunctionTrivChar 1 s = riemannZeta s
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs, Nat.primeFactors_one,
    Finset.prod_empty, one_mul]

private lemma neg_logDeriv_LFunction_one_eq {s : ℂ} (hs : s ≠ 1) :
    -deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s =
      -deriv riemannZeta s / riemannZeta s := by
  have hev : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact LFunction_one_eq_riemannZeta_of_ne_one (Set.mem_compl_singleton_iff.mp hw)
  rw [hev.deriv_eq, LFunction_one_eq_riemannZeta_of_ne_one hs]

private lemma sum_inv_abs_halfInteger_le (N : ℕ) (hN : 2 ≤ N) :
    let x : ℝ := (N : ℝ) + 1 / 2
    ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ ≤ 4 * (1 + Real.log ((N : ℝ) + 1)) := by
  intro x
  have hsplit : Finset.Icc 1 (2 * N + 1) =
      Finset.Icc 1 N ∪ Finset.Icc (N + 1) (2 * N + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (2 * N + 1)) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ n ∈ Finset.Icc 1 N, |x - (n : ℝ)|⁻¹ ≤ 2 * (1 + Real.log N) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, |x - (n : ℝ)|⁻¹ ≤
        ∑ n ∈ Finset.Icc 1 N, 2 * ((N + 1 - n : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := Finset.mem_Icc.mp hn
      have hpos : (0 : ℝ) < ((N + 1 - n : ℕ) : ℝ) / 2 := by
        have : 1 ≤ N + 1 - n := by omega
        positivity
      have hge : ((N + 1 - n : ℕ) : ℝ) / 2 ≤ |x - (n : ℝ)| := by
        have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn'.2
        have hcast : ((N + 1 - n : ℕ) : ℝ) = (N : ℝ) + 1 - (n : ℝ) := by
          have : n ≤ N + 1 := by omega
          rw [Nat.cast_sub this]; push_cast; ring
        rw [abs_of_pos (by dsimp [x]; linarith), hcast]
        dsimp [x]; linarith
      calc |x - (n : ℝ)|⁻¹ ≤ (((N + 1 - n : ℕ) : ℝ) / 2)⁻¹ :=
            inv_anti₀ hpos hge
        _ = 2 * ((N + 1 - n : ℕ) : ℝ)⁻¹ := by ring
    have hbij : ∑ n ∈ Finset.Icc 1 N, ((N + 1 - n : ℕ) : ℝ)⁻¹ =
        ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
      refine Finset.sum_bij (fun n _ => N + 1 - n) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
      · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Icc] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        exact ⟨N + 1 - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n _; rfl
    have hharm : ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ ≤ 1 + Real.log N := by
      simpa [Nat.floor_natCast] using sum_inv_le_one_add_log (x := (N : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N))
    rw [← Finset.mul_sum, hbij] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hharm zero_le_two)
  have hright : ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), |x - (n : ℝ)|⁻¹ ≤
      2 * (1 + Real.log ((N : ℝ) + 1)) := by
    have h1 : ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), |x - (n : ℝ)|⁻¹ ≤
        ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), 2 * ((n - N : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := Finset.mem_Icc.mp hn
      have hpos : (0 : ℝ) < ((n - N : ℕ) : ℝ) / 2 := by
        have : 1 ≤ n - N := by omega
        positivity
      have hge : ((n - N : ℕ) : ℝ) / 2 ≤ |x - (n : ℝ)| := by
        have hnR : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn'.1
        have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        rw [abs_of_neg (by dsimp [x]; linarith), hcast]
        dsimp [x]; linarith
      calc |x - (n : ℝ)|⁻¹ ≤ (((n - N : ℕ) : ℝ) / 2)⁻¹ :=
            inv_anti₀ hpos hge
        _ = 2 * ((n - N : ℕ) : ℝ)⁻¹ := by ring
    have hbij : ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), ((n - N : ℕ) : ℝ)⁻¹ =
        ∑ k ∈ Finset.Icc 1 (N + 1), (k : ℝ)⁻¹ := by
      refine Finset.sum_bij (fun n _ => n - N) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
      · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Icc] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        exact ⟨N + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n _; rfl
    have hharm : ∑ k ∈ Finset.Icc 1 (N + 1), (k : ℝ)⁻¹ ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have h1 := sum_inv_le_one_add_log (x := ((N + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N + 1))
      rw [Nat.floor_natCast, Nat.cast_add, Nat.cast_one] at h1
      exact h1
    rw [← Finset.mul_sum, hbij] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hharm zero_le_two)
  have hlog_le : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by linarith)
  linarith

private lemma perron_vonMangoldt_halfInteger_error_le {N : ℕ} (hN : 2 ≤ N)
    {c T : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (hT : 2 ≤ T) :
    let x : ℝ := (N : ℝ) + 1 / 2
    ‖dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x c T - (Chebyshev.psi x : ℂ)‖ ≤
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) +
        (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T) := by
  intro x
  have hx_pos : 0 < x := by positivity
  have hc_pos : 0 < c := by linarith
  have hT_pos : 0 < T := by linarith
  have ha : LSeriesSummable (fun n : ℕ => (Λ n : ℂ)) (c : ℂ) :=
    LSeriesSummable_vonMangoldt_iff.mpr (by simpa using hc1)
  have hex := perron_truncated_explicit hx_pos hc_pos hT_pos ha
  have hfl : ⌊x⌋₊ = N := by
    rw [Nat.floor_eq_iff hx_pos.le]
    exact ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hfl2 : ⌊2 * x⌋₊ = 2 * N + 1 := by
    have h2x : 2 * x = ((2 * N + 1 : ℕ) : ℝ) := by dsimp [x]; push_cast; ring
    rw [h2x, Nat.floor_natCast]
  have hpsi : (Chebyshev.psi x : ℂ) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) := by
    rw [psi_eq_sum_Icc]
    push_cast; rfl
  have hx_nonint : ∀ n : ℕ, (n : ℝ) ≠ x := by
    intro n hn
    rcases le_or_gt n N with hle | hgt
    · have : (n : ℝ) ≤ N := by exact_mod_cast hle
      dsimp [x] at hn; linarith
    · have : (N + 1 : ℝ) ≤ n := by exact_mod_cast hgt
      dsimp [x] at hn; linarith
  have hhit0 : (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if (n : ℝ) = x then ‖(Λ n : ℂ)‖ * (1 / 2 + c / (Real.pi * T)) else 0) = 0 :=
    Finset.sum_eq_zero fun n _ => ite_eq_right (hx_nonint n)
  have htsum_bd : ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => (Λ k : ℂ)) (c : ℂ) n‖ ≤ 4 / (c - 1) ^ 2 := by
    have h1 := tsum_norm_LSeries_term_twist_le (1 : DirichletCharacter ℂ 1) hc1
    refine (le_of_eq ?_).trans h1
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp
  have hnear_bd : (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
        ‖(Λ n : ℂ)‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
      else 0) ≤ (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T) := by
    rw [hfl2]
    have hlog2x_ge1 : 1 ≤ Real.log (2 * x) := by
      have h5 : (5 : ℝ) ≤ 2 * x := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        dsimp [x]; linarith
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    have hterm_le : ∑ n ∈ Finset.Icc 1 (2 * N + 1),
        (if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
          ‖(Λ n : ℂ)‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
        else 0) ≤
        (Real.log (2 * x) * (8 * x / (Real.pi * T))) *
          ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn_mem := Finset.mem_Icc.mp hn
      split_ifs with hcond
      · have hnorm_Λ : ‖(Λ n : ℂ)‖ ≤ Real.log (2 * x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          have hle_log : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_mem.1
          have hn_le2x : (n : ℝ) ≤ 2 * x := by
            have h2N : ((2 * N + 1 : ℕ) : ℝ) = 2 * x := by dsimp [x]; push_cast; ring
            rw [← h2N]; exact_mod_cast hn_mem.2
          exact hle_log.trans (Real.log_le_log hn_pos hn_le2x)
        have h2c : (2 : ℝ) ^ c ≤ 4 := by
          calc (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hc2
            _ = 4 := by norm_num
        have hmul_eq : 2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|) =
            (2 ^ c * (2 * x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹ := by ring
        rw [hmul_eq]
        have hpos_x : 0 ≤ 2 * x / (Real.pi * T) := by positivity
        have hpow_le : 2 ^ c * (2 * x) / (Real.pi * T) ≤ 8 * x / (Real.pi * T) := by
          calc 2 ^ c * (2 * x) / (Real.pi * T)
              ≤ 4 * (2 * x) / (Real.pi * T) := by gcongr
            _ = 8 * x / (Real.pi * T) := by ring
        calc ‖(Λ n : ℂ)‖ * ((2 ^ c * (2 * x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹)
            ≤ Real.log (2 * x) * ((8 * x / (Real.pi * T)) * |x - (n : ℝ)|⁻¹) := by gcongr
          _ = (Real.log (2 * x) * (8 * x / (Real.pi * T))) * |x - (n : ℝ)|⁻¹ := by ring
      · positivity
    have hsum_inv := sum_inv_abs_halfInteger_le N hN
    have h_N1_le : (N : ℝ) + 1 ≤ 2 * x := by dsimp [x]; linarith
    have h4_le : 4 * (1 + Real.log ((N : ℝ) + 1)) ≤ 8 * Real.log (2 * x) := by
      have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x) :=
        Real.log_le_log (by positivity) h_N1_le
      linarith [hlog2x_ge1]
    calc (∑ n ∈ Finset.Icc 1 (2 * N + 1),
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖(Λ n : ℂ)‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
          else 0)
        ≤ (Real.log (2 * x) * (8 * x / (Real.pi * T))) *
            ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ := hterm_le
      _ ≤ (Real.log (2 * x) * (8 * x / (Real.pi * T))) * (8 * Real.log (2 * x)) := by
          dsimp only at hsum_inv
          exact mul_le_mul_of_nonneg_left (hsum_inv.trans h4_le) (by positivity)
      _ = (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T) := by ring
  have hterm1 : (x ^ c / (Real.pi * T * Real.log 2)) *
        ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => (Λ k : ℂ)) (c : ℂ) n‖ ≤
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc (x ^ c / (Real.pi * T * Real.log 2)) *
          ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => (Λ k : ℂ)) (c : ℂ) n‖
        ≤ (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) := by gcongr
      _ = (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) := by
          have hc0 : c - 1 ≠ 0 := sub_ne_zero.mpr hc1.ne'
          field_simp [hT_pos.ne', hlog2_pos.ne', hc0]
  rw [← hpsi] at hex
  linarith [hex, hhit0, hnear_bd, hterm1]

private lemma rpow_sqrt_log_mul_exp_neg_le {m : ℕ} {γ u : ℝ} (hγ : 0 < γ) (_hu : 1 ≤ u) :
    (Real.sqrt (Real.log u)) ^ m * Real.exp (-2 * γ * Real.sqrt (Real.log u)) ≤
      ((m.factorial : ℝ) / γ ^ m) * Real.exp (-γ * Real.sqrt (Real.log u)) := by
  let y : ℝ := Real.sqrt (Real.log u)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hpow : (γ * y) ^ m / (m.factorial : ℝ) ≤ Real.exp (γ * y) := by
    have hexp := Real.sum_le_exp_of_nonneg (mul_nonneg hγ.le hy) (m + 1)
    have hsingle : (γ * y) ^ m / (m.factorial : ℝ) ≤
        ∑ k ∈ Finset.range (m + 1), (γ * y) ^ k / (k.factorial : ℝ) :=
      Finset.single_le_sum (fun k _ => div_nonneg (pow_nonneg (mul_nonneg hγ.le hy) k)
        (Nat.cast_nonneg _)) (Finset.mem_range.mpr (Nat.lt_succ_self m))
    exact hsingle.trans hexp
  have hy_bd : y ^ m ≤ ((m.factorial : ℝ) / γ ^ m) * Real.exp (γ * y) := by
    rw [mul_pow] at hpow
    rw [div_le_iff₀ (by positivity)] at hpow
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hγ m)]
    linarith
  calc y ^ m * Real.exp (-2 * γ * y)
      ≤ (((m.factorial : ℝ) / γ ^ m) * Real.exp (γ * y)) * Real.exp (-2 * γ * y) :=
        mul_le_mul_of_nonneg_right hy_bd (Real.exp_pos _).le
    _ = ((m.factorial : ℝ) / γ ^ m) * (Real.exp (γ * y) * Real.exp (-2 * γ * y)) := by ring
    _ = ((m.factorial : ℝ) / γ ^ m) * Real.exp (-γ * y) := by
        rw [← Real.exp_add]; congr 2; ring

private lemma LFunctionTrivChar_one_nonzero_rect (Z : ZetaZeroFreeData)
    {T c_line : ℝ} :
    let L_T : ℝ := Real.log (T + 3)
    let σ₀ : ℝ := 1 - Z.c / L_T
    ∀ s ∈ Set.Icc σ₀ c_line ×ℂ Set.Icc (-T) T,
      DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0 := by
  intro L_T σ₀ s hs
  rw [LFunctionTrivChar₁_one_eq_riemannZeta₁]
  refine Z.zeroFree_zetaOne s ?_
  have him_le : |s.im| ≤ T := abs_le.mpr hs.2
  have hlog_le : Real.log (|s.im| + 3) ≤ L_T :=
    Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith)
  have hdiv_le : Z.c / L_T ≤ Z.c / Real.log (|s.im| + 3) :=
    div_le_div_of_nonneg_left Z.hc_pos.le (Real.log_pos (by linarith [abs_nonneg s.im])) hlog_le
  have hre_ge : σ₀ ≤ s.re := hs.1.1
  dsimp [σ₀] at hre_ge
  linarith

private lemma LFunctionTrivChar_one_logDeriv_edge_bd (Z : ZetaZeroFreeData)
    {T : ℝ} (hLT_ge1 : 1 ≤ Real.log (T + 3)) :
    let L_T : ℝ := Real.log (T + 3)
    let σ₀ : ℝ := 1 - Z.c / L_T
    let B_bound : ℝ := (9 * Z.C + 1 / Z.c) * L_T ^ 2
    ∀ s : ℂ, σ₀ ≤ s.re → |s.im| ≤ T → Z.c / L_T ≤ ‖s - 1‖ ∨ 3 ≤ |s.im| →
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) s /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s‖ ≤ B_bound := by
  intro L_T σ₀ B_bound s hsre _hsim hfar
  have hcZ_pos := Z.hc_pos
  have hCZ_pos := Z.hC_pos
  have hlog_le : Real.log (|s.im| + 3) ≤ L_T :=
    Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith)
  have hzf_re : 1 - Z.c / Real.log (|s.im| + 3) ≤ s.re := by
    have hdiv : Z.c / L_T ≤ Z.c / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_left hcZ_pos.le (Real.log_pos (by linarith [abs_nonneg s.im])) hlog_le
    dsimp [σ₀] at hsre
    linarith
  by_cases him3 : 3 ≤ |s.im|
  · have hs1 : s ≠ 1 := by
      intro h; subst h; simp at him3; norm_num at him3
    rw [neg_logDeriv_LFunction_one_eq hs1]
    have h1 := Z.norm_logDeriv_large s hzf_re him3
    have hlog_nn : 0 ≤ Real.log (|s.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg s.im])
    have hsq_le : Real.log (|s.im| + 3) ^ 2 ≤ L_T ^ 2 :=
      pow_le_pow_left₀ hlog_nn hlog_le 2
    calc ‖-deriv riemannZeta s / riemannZeta s‖
        ≤ Z.C * Real.log (|s.im| + 3) ^ 2 := h1
      _ ≤ Z.C * L_T ^ 2 := mul_le_mul_of_nonneg_left hsq_le hCZ_pos.le
      _ ≤ (9 * Z.C + 1 / Z.c) * L_T ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith [show 0 ≤ 1 / Z.c by positivity]) (sq_nonneg _)
  · have hfar1 : Z.c / L_T ≤ ‖s - 1‖ := hfar.resolve_right him3
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hfar1
      have : 0 < Z.c / L_T := by positivity
      linarith
    rw [neg_logDeriv_LFunction_one_eq hs1]
    have him_le3 : |s.im| ≤ 3 := le_of_not_ge him3
    have h1 := Z.norm_logDeriv_small s hzf_re him_le3 hs1
    have htri : ‖-deriv riemannZeta s / riemannZeta s‖ ≤
        ‖-deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹‖ + ‖(s - 1)⁻¹‖ := by
      calc ‖-deriv riemannZeta s / riemannZeta s‖
          = ‖(-deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹) + (s - 1)⁻¹‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have hinv_le : ‖(s - 1)⁻¹‖ ≤ (1 / Z.c) * L_T := by
      rw [norm_inv]
      calc ‖s - 1‖⁻¹ ≤ (Z.c / L_T)⁻¹ := inv_anti₀ (by positivity) hfar1
        _ = (1 / Z.c) * L_T := by rw [inv_div]; ring
    have hL_sq : L_T ≤ L_T ^ 2 := by nlinarith [hLT_ge1]
    have h1_lt : 1 ≤ L_T ^ 2 := by nlinarith [hLT_ge1]
    calc ‖-deriv riemannZeta s / riemannZeta s‖
        ≤ Z.C + (1 / Z.c) * L_T := htri.trans (add_le_add h1 hinv_le)
      _ ≤ Z.C * L_T ^ 2 + (1 / Z.c) * L_T ^ 2 :=
          add_le_add (le_mul_of_one_le_right hCZ_pos.le h1_lt)
            (mul_le_mul_of_nonneg_left hL_sq (by positivity))
      _ = (Z.C + 1 / Z.c) * L_T ^ 2 := by ring
      _ ≤ (9 * Z.C + 1 / Z.c) * L_T ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

private lemma abs_psi_sub_id_halfInteger_le_exp (Z : ZetaZeroFreeData) :
    ∃ C₁ > 0, ∀ N : ℕ, Real.exp 16 ≤ (N : ℝ) + 1 / 2 →
      let x' : ℝ := (N : ℝ) + 1 / 2
      |Chebyshev.psi x' - x'| ≤ C₁ * x' * Real.exp (-(Z.c / 16) * Real.sqrt (Real.log x')) := by
  have hcZ_pos := Z.hc_pos
  have hcZ_le := Z.hc_le
  have hCZ_pos := Z.hC_pos
  let c_pnt : ℝ := Z.c / 16
  have hc_pnt_pos : 0 < c_pnt := by positivity
  have hc_pnt_le : c_pnt ≤ 1 / 128 := by dsimp [c_pnt]; linarith
  let X₀ : ℝ := Real.exp 16
  have hX₀_ge : 4 ≤ X₀ := by
    have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    exact hexp2.trans (Real.exp_le_exp.mpr (by norm_num))
  let C_vert_k : ℝ := 9 * Z.C + 1 / Z.c
  have hCv_pos : 0 < C_vert_k := by positivity
  let M₁ : ℝ := (Real.sqrt 2 / Real.pi) * (C_vert_k * 8) * ((Nat.factorial 3 : ℝ) / c_pnt ^ 3)
  let M₂ : ℝ := ((2 : ℝ) / Real.pi) * (C_vert_k * 4) * Real.exp 1 * ((Nat.factorial 2 : ℝ) / c_pnt ^ 2)
  let M₃ : ℝ := (4 / (Real.pi * Real.log 2)) * Real.exp 1 * ((Nat.factorial 4 : ℝ) / c_pnt ^ 4)
  let M₄ : ℝ := (64 / Real.pi) * 4 * ((Nat.factorial 4 : ℝ) / c_pnt ^ 4)
  refine ⟨M₁ + M₂ + M₃ + M₄ + 1, by positivity, fun N hN_ge => ?_⟩
  intro x'
  have hx'_ge4 : 4 ≤ x' := hX₀_ge.trans hN_ge
  have hx'_pos : 0 < x' := by linarith
  have hN2 : 2 ≤ N := by
    by_contra hlt
    have : (N : ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
    dsimp [x'] at hx'_ge4
    linarith
  have hlog_ge16 : 16 ≤ Real.log x' := by
    rw [Real.le_log_iff_exp_le hx'_pos]
    exact hN_ge
  have hsqrt_ge4 : 4 ≤ Real.sqrt (Real.log x') := by
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  let sL : ℝ := Real.sqrt (Real.log x')
  have hsL_ge4 : 4 ≤ sL := hsqrt_ge4
  have hlog_eq_sq : Real.log x' = sL ^ 2 := (Real.sq_sqrt (by linarith)).symm
  let T : ℝ := Real.exp sL
  have hT_ge3 : 3 ≤ T := by
    have h1 : Real.exp 2 ≤ T := Real.exp_le_exp.mpr (by linarith)
    have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    linarith
  have hT_pos : 0 < T := Real.exp_pos sL
  let c_line : ℝ := 1 + 1 / Real.log x'
  have hc1 : 1 < c_line := by
    dsimp [c_line]; linarith [one_div_pos.mpr (by linarith : 0 < Real.log x')]
  have hc2 : c_line ≤ 2 := by
    dsimp [c_line]
    have : 1 / Real.log x' ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    linarith
  let L_T : ℝ := Real.log (T + 3)
  have hLT_le : L_T ≤ 2 * sL := by
    have hT3 : T + 3 ≤ 2 * T := by linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
    calc L_T ≤ Real.log (2 * T) := Real.log_le_log (by positivity) hT3
      _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) hT_pos.ne'
      _ = Real.log 2 + sL := by dsimp [T]; rw [Real.log_exp]
      _ ≤ 2 * sL := by linarith
  have hLT_ge1 : 1 ≤ L_T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  let σ₀ : ℝ := 1 - Z.c / L_T
  have hσ0_ge : 1 / 2 ≤ σ₀ := by
    have h1 : Z.c / L_T ≤ 1 / 8 := (div_le_self hcZ_pos.le hLT_ge1).trans hcZ_le
    dsimp [σ₀]; linarith
  have hσ0_pos : 0 < σ₀ := by linarith
  have hσ0_lt1 : σ₀ < 1 := by dsimp [σ₀]; linarith [div_pos hcZ_pos (by linarith : 0 < L_T)]
  let B_bound : ℝ := C_vert_k * L_T ^ 2
  have hB_nn : 0 ≤ B_bound := by positivity
  have hnonzero := LFunctionTrivChar_one_nonzero_rect Z (T := T) (c_line := c_line)
  have h_edge_bd := LFunctionTrivChar_one_logDeriv_edge_bd Z (T := T) hLT_ge1
  have hvert : ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ((σ₀ : ℂ) + (t : ℂ) * I) /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
        B_bound := by
    intro t ht
    have hre : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
    refine h_edge_bd _ (by rw [hre]) (by simpa using abs_le.mpr ht) (Or.inl ?_)
    have h1 : |(((σ₀ : ℂ) + (t : ℂ) * I) - 1).re| ≤ ‖((σ₀ : ℂ) + (t : ℂ) * I) - 1‖ :=
      Complex.abs_re_le_norm _
    have h2 : (((σ₀ : ℂ) + (t : ℂ) * I) - 1).re = -(Z.c / L_T) := by simp [σ₀]
    rw [h2, abs_neg, abs_of_nonneg (by positivity)] at h1
    exact h1
  have htop : ∀ u ∈ Set.Icc σ₀ c_line,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ((u : ℂ) + (T : ℂ) * I) /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B_bound := fun u hu => by
    have hre : ((u : ℂ) + (T : ℂ) * I).re = u := by simp
    exact h_edge_bd _ (by rw [hre]; exact hu.1) (by simp [abs_of_pos hT_pos])
      (Or.inr (by simp [abs_of_pos hT_pos, hT_ge3]))
  have hbot : ∀ u ∈ Set.Icc σ₀ c_line,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ((u : ℂ) + ((-T : ℝ) : ℂ) * I) /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        B_bound := fun u hu => by
    have hre : ((u : ℂ) + ((-T : ℝ) : ℂ) * I).re = u := by simp
    exact h_edge_bd _ (by rw [hre]; exact hu.1) (by simp [abs_of_pos hT_pos])
      (Or.inr (by simp [abs_of_pos hT_pos, hT_ge3]))
  have hshift := norm_dirichletContourIntegral_trivChar_sub_le 1 (by linarith : 1 ≤ x')
    hσ0_pos hσ0_lt1 hc1 hT_pos hB_nn hB_nn hnonzero hvert htop hbot
  have hperr := perron_vonMangoldt_halfInteger_error_le hN2 hc1 hc2 (by linarith : 2 ≤ T)
  dsimp only at hperr
  have h_contour_eq : dirichletContourIntegral (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n * (Λ n : ℂ))
        x' c_line T =
      dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T := by
    congr 1; funext n
    simp
  rw [h_contour_eq] at hshift
  have h_psi_norm : |Chebyshev.psi x' - x'| ≤
      ‖dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T - (x' : ℂ)‖ +
        ‖dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T - (Chebyshev.psi x' : ℂ)‖ := by
    have h1 : |Chebyshev.psi x' - x'| = ‖(Chebyshev.psi x' : ℂ) - (x' : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    have hid : (Chebyshev.psi x' : ℂ) - (x' : ℂ) =
        (dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T - (x' : ℂ)) -
          (dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T - (Chebyshev.psi x' : ℂ)) := by ring
    rw [hid]
    exact norm_sub_le _ _
  have h_xc : x' ^ c_line = Real.exp 1 * x' := by
    dsimp [c_line]
    rw [Real.rpow_add hx'_pos, Real.rpow_one, Real.rpow_def_of_pos hx'_pos,
      mul_div_cancel₀ 1 (by linarith : Real.log x' ≠ 0)]
    ring
  have h_inv_T : T⁻¹ ≤ Real.exp (-2 * c_pnt * sL) := by
    dsimp [T]
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by nlinarith only [hc_pnt_le, hsL_ge4])
  have hB_le : B_bound ≤ 4 * C_vert_k * sL ^ 2 := by
    have hsq : L_T ^ 2 ≤ (2 * sL) ^ 2 := pow_le_pow_left₀ (by linarith) hLT_le 2
    calc B_bound = C_vert_k * L_T ^ 2 := rfl
      _ ≤ C_vert_k * (2 * sL) ^ 2 := mul_le_mul_of_nonneg_left hsq hCv_pos.le
      _ = 4 * C_vert_k * sL ^ 2 := by ring
  have h_term1 : (Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀) ≤
      M₁ * x' * Real.exp (-c_pnt * sL) := by
    have hlog_T : Real.log (1 + T / σ₀) ≤ 2 * sL := by
      have h1 : 1 + T / σ₀ ≤ 4 * T := by
        have hdiv : T / σ₀ ≤ 2 * T := by
          rw [div_le_iff₀ hσ0_pos]
          calc T = T * 1 := (mul_one T).symm
            _ ≤ T * (2 * σ₀) := mul_le_mul_of_nonneg_left (by linarith [hσ0_ge]) hT_pos.le
            _ = 2 * T * σ₀ := by ring
        linarith
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have hlog2 : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
        norm_num; linarith
      calc Real.log (1 + T / σ₀) ≤ Real.log (4 * T) := Real.log_le_log (by positivity) h1
        _ = Real.log 4 + Real.log T := Real.log_mul (by norm_num) hT_pos.ne'
        _ = Real.log 4 + sL := by dsimp [T]; rw [Real.log_exp]
        _ ≤ 2 * sL := by linarith
    have hxσ : x' ^ σ₀ ≤ x' * Real.exp (-2 * c_pnt * sL) := by
      rw [Real.rpow_def_of_pos hx'_pos]
      have heq : Real.log x' * σ₀ = Real.log x' - (Z.c / L_T) * Real.log x' := by
        dsimp [σ₀]; ring
      rw [heq, Real.exp_sub, Real.exp_log hx'_pos, div_eq_mul_inv, ← Real.exp_neg]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx'_pos.le
      have hdiv : 2 * c_pnt * sL ≤ (Z.c / L_T) * Real.log x' := by
        rw [hlog_eq_sq, div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < L_T)]
        have h8 : 2 * c_pnt * (2 * sL) ≤ Z.c * sL := by
          calc 2 * c_pnt * (2 * sL) = (1 / 4 : ℝ) * (Z.c * sL) := by dsimp [c_pnt]; ring
            _ ≤ 1 * (Z.c * sL) := mul_le_mul_of_nonneg_right (by norm_num)
                (mul_nonneg hcZ_pos.le (by linarith))
            _ = Z.c * sL := one_mul _
        calc 2 * c_pnt * sL * L_T ≤ 2 * c_pnt * sL * (2 * sL) :=
              mul_le_mul_of_nonneg_left hLT_le (by positivity)
          _ = (2 * c_pnt * (2 * sL)) * sL := by ring
          _ ≤ (Z.c * sL) * sL := mul_le_mul_of_nonneg_right h8 (by linarith)
          _ = Z.c * sL ^ 2 := by ring
      linarith
    have hrpow : sL ^ 3 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 3 : ℝ) / c_pnt ^ 3) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 3) hc_pnt_pos (by linarith : 1 ≤ x')
    have hlog_T_nn : 0 ≤ Real.log (1 + T / σ₀) :=
      Real.log_nonneg (by linarith [div_pos hT_pos hσ0_pos])
    have hfac1 : (Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ ≤
        (Real.sqrt 2 / Real.pi) * (4 * C_vert_k * sL ^ 2) * (x' * Real.exp (-2 * c_pnt * sL)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB_le (by positivity)) hxσ (by positivity) (by positivity)
    calc (Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀)
        ≤ ((Real.sqrt 2 / Real.pi) * (4 * C_vert_k * sL ^ 2) *
            (x' * Real.exp (-2 * c_pnt * sL))) * (2 * sL) :=
          mul_le_mul hfac1 hlog_T hlog_T_nn (by positivity)
      _ = (Real.sqrt 2 / Real.pi) * (C_vert_k * 8) * x' * (sL ^ 3 * Real.exp (-2 * c_pnt * sL)) := by ring
      _ ≤ (Real.sqrt 2 / Real.pi) * (C_vert_k * 8) * x' *
            (((Nat.factorial 3 : ℝ) / c_pnt ^ 3) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = M₁ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₁]; ring
  have h_term2 : ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line ≤
      M₂ * x' * Real.exp (-c_pnt * sL) := by
    have hc_diff : c_line - σ₀ ≤ 2 := by
      have h1 : 1 / Real.log x' ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      have h2 : Z.c / L_T ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      dsimp [c_line, σ₀]; linarith
    have hrpow : sL ^ 2 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 2 : ℝ) / c_pnt ^ 2) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 2) hc_pnt_pos (by linarith : 1 ≤ x')
    have h_prefix : (c_line - σ₀) / Real.pi * B_bound ≤ 2 / Real.pi * (4 * C_vert_k * sL ^ 2) :=
      mul_le_mul (div_le_div_of_nonneg_right hc_diff Real.pi_pos.le) hB_le hB_nn (by positivity)
    calc ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line
        = (c_line - σ₀) / Real.pi * B_bound * (Real.exp 1 * x') * T⁻¹ := by rw [h_xc]; ring
      _ ≤ 2 / Real.pi * (4 * C_vert_k * sL ^ 2) * (Real.exp 1 * x') * Real.exp (-2 * c_pnt * sL) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h_prefix (by positivity)) h_inv_T (by positivity) (by positivity)
      _ = (2 / Real.pi) * (C_vert_k * 4) * Real.exp 1 * x' * (sL ^ 2 * Real.exp (-2 * c_pnt * sL)) := by ring
      _ ≤ (2 / Real.pi) * (C_vert_k * 4) * Real.exp 1 * x' *
            (((Nat.factorial 2 : ℝ) / c_pnt ^ 2) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = M₂ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₂]; ring
  have h_term3 : (4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2)) ≤
      M₃ * x' * Real.exp (-c_pnt * sL) := by
    have hc_sq : (c_line - 1) ^ 2 = (sL ^ 4)⁻¹ := by
      dsimp [c_line]; rw [add_sub_cancel_left, one_div, hlog_eq_sq, inv_pow, ← pow_mul]
    have hrpow : sL ^ 4 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 4) hc_pnt_pos (by linarith : 1 ≤ x')
    have h_eq : x' ^ c_line / (T * (c_line - 1) ^ 2) = Real.exp 1 * x' * sL ^ 4 * T⁻¹ := by
      rw [h_xc, hc_sq, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hcoeff3 : 0 ≤ (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' := by positivity
    calc (4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2))
        = (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' * (sL ^ 4 * T⁻¹) := by rw [h_eq]; ring
      _ ≤ (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' * (sL ^ 4 * Real.exp (-2 * c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_inv_T (by positivity)) hcoeff3
      _ ≤ (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' *
            (((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow hcoeff3
      _ = M₃ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₃]; ring
  have h_term4 : (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T) ≤
      M₄ * x' * Real.exp (-c_pnt * sL) := by
    have hlog2x_le : Real.log (2 * x') ≤ 2 * sL ^ 2 := by
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; linarith only [Real.exp_one_gt_d9]
      have h1_sL : 1 ≤ sL ^ 2 := by nlinarith only [hsL_ge4]
      rw [Real.log_mul (by norm_num) hx'_pos.ne', hlog_eq_sq]
      linarith only [hlog2, h1_sL]
    have hsq2x : (Real.log (2 * x')) ^ 2 ≤ 4 * sL ^ 4 := by
      calc (Real.log (2 * x')) ^ 2 ≤ (2 * sL ^ 2) ^ 2 :=
            pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hx'_ge4])) hlog2x_le 2
        _ = 4 * sL ^ 4 := by ring
    have hrpow : sL ^ 4 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 4) hc_pnt_pos (by linarith : 1 ≤ x')
    have h_eq : x' * (Real.log (2 * x')) ^ 2 / T = x' * (Real.log (2 * x')) ^ 2 * T⁻¹ := by ring
    calc (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T)
        ≤ (64 / Real.pi) * (x' * (4 * sL ^ 4) * Real.exp (-2 * c_pnt * sL)) := by
          rw [h_eq]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_left hsq2x hx'_pos.le) h_inv_T (by positivity) (by positivity))
            (by positivity)
      _ = (64 / Real.pi) * 4 * x' * (sL ^ 4 * Real.exp (-2 * c_pnt * sL)) := by ring
      _ ≤ (64 / Real.pi) * 4 * x' * (((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = M₄ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₄]; ring
  calc |Chebyshev.psi x' - x'|
      ≤ ‖dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T - (x' : ℂ)‖ +
          ‖dirichletContourIntegral (fun n : ℕ => (Λ n : ℂ)) x' c_line T - (Chebyshev.psi x' : ℂ)‖ :=
        h_psi_norm
    _ ≤ ((Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀) +
            ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line) +
          ((4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2)) +
            (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T)) := add_le_add hshift hperr
    _ ≤ (M₁ * x' * Real.exp (-c_pnt * sL) + M₂ * x' * Real.exp (-c_pnt * sL)) +
          (M₃ * x' * Real.exp (-c_pnt * sL) + M₄ * x' * Real.exp (-c_pnt * sL)) :=
        add_le_add (add_le_add h_term1 h_term2) (add_le_add h_term3 h_term4)
    _ = (M₁ + M₂ + M₃ + M₄) * (x' * Real.exp (-c_pnt * sL)) := by ring
    _ ≤ (M₁ + M₂ + M₃ + M₄ + 1) * (x' * Real.exp (-c_pnt * sL)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
    _ = (M₁ + M₂ + M₃ + M₄ + 1) * x' * Real.exp (-c_pnt * sL) := by ring

/-- Unconditional **de la Vallée Poussin Prime Number Theorem** with explicit exponential
error term for `Chebyshev.psi`:
`∃ C > 0, ∃ c > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * x * exp(-c * √(log x))`. -/
theorem abs_psi_sub_id_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  let Z := unconditionalZetaZeroFreeData
  have hcZ_pos : 0 < Z.c := Z.hc_pos
  have hcZ_le : Z.c ≤ 1 / 8 := Z.hc_le
  have hCZ_pos : 0 < Z.C := Z.hC_pos
  let c_pnt : ℝ := Z.c / 16
  have hc_pnt_pos : 0 < c_pnt := by positivity
  have hc_pnt_le : c_pnt ≤ 1 / 128 := by dsimp [c_pnt]; linarith
  let X₀ : ℝ := Real.exp 16
  have hX₀_ge : 4 ≤ X₀ := by
    dsimp [X₀]
    have h1 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : (16 : ℝ) ≤ Real.exp 4 := by
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
      have h2' : (4 : ℝ) ≤ Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_pos 1]
      nlinarith
    have h4 : Real.exp 4 ≤ Real.exp 16 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  obtain ⟨C₁, hC₁_pos, h_half_bd⟩ := abs_psi_sub_id_halfInteger_le_exp Z
  let C_small : ℝ := (Real.log 4 + 5) * Real.exp (c_pnt * Real.sqrt (Real.log (X₀ + 1)))
  let C_large : ℝ := (3 / 2 : ℝ) * C₁ * Real.exp c_pnt + 1
  refine ⟨max C_small C_large, by positivity, c_pnt, hc_pnt_pos, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  by_cases hx_small : x ≤ X₀ + 1
  · have hpsi_bd : |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x := by
      have h1 : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
      have h2 : Chebyshev.psi x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx0.le
      rw [abs_le]
      constructor <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have hexp_ge : 1 ≤ Real.exp (c_pnt * Real.sqrt (Real.log (X₀ + 1))) *
        Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have hle : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (X₀ + 1)) :=
        Real.sqrt_le_sqrt (Real.log_le_log hx0 hx_small)
      nlinarith [hc_pnt_pos]
    calc |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x := hpsi_bd
      _ ≤ (Real.log 4 + 5) * x * (Real.exp (c_pnt * Real.sqrt (Real.log (X₀ + 1))) *
            Real.exp (-c_pnt * Real.sqrt (Real.log x))) :=
          le_mul_of_one_le_right (by positivity) hexp_ge
      _ = C_small * x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by dsimp [C_small]; ring
      _ ≤ max C_small C_large * x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_left _ _
  · have hx_gt : X₀ + 1 < x := not_le.mp hx_small
    let N : ℕ := ⌊x⌋₊
    let x' : ℝ := (N : ℝ) + 1 / 2
    have hNx1 : x - 1 < N := Nat.sub_one_lt_floor x
    have hNx2 : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    have hx'_ge : X₀ ≤ x' := by dsimp [x']; linarith
    have hx'_half : x / 2 ≤ x' := by
      have : 4 ≤ x := by linarith [hX₀_ge]
      dsimp [x']; linarith
    have hfl : ⌊x'⌋₊ = N := by
      rw [Nat.floor_eq_iff (by positivity)]
      exact ⟨by dsimp [x']; linarith, by dsimp [x']; linarith⟩
    have hpsi_eq : Chebyshev.psi x = Chebyshev.psi x' := by
      rw [psi_eq_sum_Icc, psi_eq_sum_Icc, hfl]
    have h_diff_half : |Chebyshev.psi x' - x'| ≤ C₁ * x' * Real.exp (-c_pnt * Real.sqrt (Real.log x')) :=
      h_half_bd N hx'_ge
    have hexp_cmp : Real.exp (-c_pnt * Real.sqrt (Real.log x')) ≤
        Real.exp c_pnt * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hx'_ge4 : 4 ≤ x' := hX₀_ge.trans hx'_ge
      have hlogx'_ge1 : 1 ≤ Real.log x' := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        exact Real.exp_one_lt_d9.le.trans (by linarith)
      have hlog_diff : Real.log x ≤ Real.log x' + 1 := by
        have h1 : x ≤ 2 * x' := by linarith
        have hlog2 : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
        calc Real.log x ≤ Real.log (2 * x') := Real.log_le_log hx0 h1
          _ = Real.log 2 + Real.log x' := Real.log_mul (by norm_num) (by linarith)
          _ ≤ Real.log x' + 1 := by linarith
      have hsqrt_diff : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log x') + 1 := by
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        have hsq : (Real.sqrt (Real.log x') + 1) ^ 2 =
            Real.log x' + 2 * Real.sqrt (Real.log x') + 1 := by
          rw [add_sq, Real.sq_sqrt (by linarith)]; ring
        rw [hsq]
        nlinarith [Real.sqrt_nonneg (Real.log x')]
      nlinarith [hc_pnt_pos]
    have hx_sub_bd : |x' - x| ≤ x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by
      have hx_sub : |x' - x| ≤ 1 := by
        rw [abs_le]; dsimp [x']; constructor <;> linarith
      have hsqrt_le : c_pnt * Real.sqrt (Real.log x) ≤ Real.log x / 2 := by
        have hlog_ge4 : 4 ≤ Real.log x := by
          rw [Real.le_log_iff_exp_le hx0]
          exact (Real.exp_le_exp.mpr (by norm_num : (4 : ℝ) ≤ 16)).trans (by linarith)
        have hs_ge2 : 2 ≤ Real.sqrt (Real.log x) := by
          rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by linarith)
        have hsq : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
        nlinarith [hc_pnt_le]
      have hhalf_bd : 1 ≤ x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by
        have hexp_le : Real.exp (c_pnt * Real.sqrt (Real.log x)) ≤ Real.sqrt x := by
          conv_rhs => rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
          exact Real.exp_le_exp.mpr (by linarith)
        have hsqx : 2 ≤ Real.sqrt x := by
          rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by linarith [hX₀_ge])
        rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, one_le_div (Real.exp_pos _)]
        calc Real.exp (c_pnt * Real.sqrt (Real.log x)) ≤ Real.sqrt x := hexp_le
          _ ≤ Real.sqrt x * Real.sqrt x := le_mul_of_one_le_right (Real.sqrt_nonneg _) (by linarith)
          _ = x := Real.mul_self_sqrt hx0.le
      exact hx_sub.trans hhalf_bd
    have htri : |Chebyshev.psi x - x| ≤ |Chebyshev.psi x' - x'| + |x' - x| := by
      rw [hpsi_eq]
      calc |Chebyshev.psi x' - x| = |(Chebyshev.psi x' - x') + (x' - x)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hx'_le15 : x' ≤ (3 / 2 : ℝ) * x := by
      have : 4 ≤ x := by linarith [hX₀_ge]
      dsimp [x']; linarith
    calc |Chebyshev.psi x - x|
        ≤ |Chebyshev.psi x' - x'| + |x' - x| := htri
      _ ≤ C₁ * x' * Real.exp (-c_pnt * Real.sqrt (Real.log x')) +
            x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := add_le_add h_diff_half hx_sub_bd
      _ ≤ C₁ * ((3 / 2 : ℝ) * x) * (Real.exp c_pnt * Real.exp (-c_pnt * Real.sqrt (Real.log x))) +
            x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by gcongr
      _ = C_large * x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by dsimp [C_large]; ring
      _ ≤ max C_small C_large * x * Real.exp (-c_pnt * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_right _ _

private lemma sqrt_le_mul_exp_neg_quarter {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x ≤ x * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_two hx
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    rw [show (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) by simp]
    refine Real.log_lt_log (Real.exp_pos _) ?_
    have hsq : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    calc Real.exp (1 / 2 : ℝ) = Real.sqrt (Real.exp 1) := by
          rw [Real.sqrt_eq_rpow, Real.exp_one_rpow]
      _ < Real.sqrt 4 := Real.sqrt_lt_sqrt (Real.exp_pos 1).le hsq
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hlogx : 1 / 2 < Real.log x := hlog2.trans_le (Real.log_le_log zero_lt_two hx)
  have hsq_le : (1 / 4 : ℝ) * Real.sqrt (Real.log x) ≤ Real.log x / 2 := by
    have hc : (1 / 4 : ℝ) ≤ Real.sqrt (Real.log x) / 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log x) := Real.le_sqrt_of_sq_le (by linarith)
      linarith
    calc (1 / 4 : ℝ) * Real.sqrt (Real.log x)
        ≤ (Real.sqrt (Real.log x) / 2) * Real.sqrt (Real.log x) :=
          mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
      _ = Real.sqrt (Real.log x) ^ 2 / 2 := by ring
      _ = Real.log x / 2 := by rw [Real.sq_sqrt (by linarith)]
  have hexp : Real.exp ((1 / 4 : ℝ) * Real.sqrt (Real.log x)) ≤ Real.sqrt x := by
    conv_rhs => rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have heq : x * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x)) =
      x / Real.exp ((1 / 4 : ℝ) * Real.sqrt (Real.log x)) := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  rw [heq, le_div_iff₀ (Real.exp_pos _)]
  calc Real.sqrt x * Real.exp ((1 / 4 : ℝ) * Real.sqrt (Real.log x))
      ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
    _ = x := Real.mul_self_sqrt hx0.le

/-- Unconditional **de la Vallée Poussin Prime Number Theorem** with explicit exponential
error term for `Chebyshev.theta`:
`∃ C > 0, ∃ c > 0, ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * x * exp(-c * √(log x))`. -/
theorem abs_theta_sub_id_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨C, hC, c, hc, hpsi⟩ := abs_psi_sub_id_le_exp
  let C' : ℝ := C + 18
  let c' : ℝ := min c (1 / 4)
  refine ⟨C', by positivity, c', lt_min hc (by norm_num), fun x hx => ?_⟩
  have h1 := hpsi x hx
  have h2 : |Chebyshev.psi x - Chebyshev.theta x| ≤ 18 * Real.sqrt x := by
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
      norm_num; linarith
    exact (abs_psi_sub_theta_le_mul_sqrt x).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg x))
  have h3 := sqrt_le_mul_exp_neg_quarter hx
  have hx0 : 0 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hexp1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤
      Real.exp (-c' * Real.sqrt (Real.log x)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [min_le_left c (1 / 4 : ℝ)]
  have hexp2 : Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x)) ≤
      Real.exp (-c' * Real.sqrt (Real.log x)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [min_le_right c (1 / 4 : ℝ)]
  calc |Chebyshev.theta x - x|
      ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - x| := abs_sub_le _ _ _
    _ = |Chebyshev.psi x - Chebyshev.theta x| + |Chebyshev.psi x - x| := by rw [abs_sub_comm]
    _ ≤ 18 * (x * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x))) +
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        refine add_le_add (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) h1
    _ ≤ 18 * (x * Real.exp (-c' * Real.sqrt (Real.log x))) +
          C * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by gcongr
    _ = C' * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by dsimp [C']; ring

/-- Unconditional **de la Vallée Poussin Prime Number Theorem** for `primePi - logIntegral`:
`∃ C > 0, ∃ c > 0, ∀ x ≥ 2, |primePi x - logIntegral x| ≤ C * x * exp(-c * √(log x))`. -/
theorem abs_primePi_sub_logIntegral_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 2 ≤ x → |primePi x - logIntegral x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨Cθ, hCθ, cθ, hcθ, hθ⟩ := abs_theta_sub_id_le_exp
  let c' : ℝ := min (cθ / Real.sqrt 2) (1 / 4)
  have hc' : 0 < c' := lt_min (div_pos hcθ (Real.sqrt_pos.mpr zero_lt_two)) (by norm_num)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let C_small : ℝ := (Real.log 4 + 3 + 2 / Real.log 2) * Real.exp (c' * Real.sqrt (Real.log 4))
  let C_large : ℝ := Cθ / Real.log 2 + 2 / Real.log 2 + (Real.log 4 + 1) / Real.log 2 ^ 2 +
    Cθ / Real.log 2 ^ 2
  refine ⟨max C_small C_large, by positivity, c', hc', fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_two hx
  have hlogx_pos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le one_lt_two hx)
  have hlogx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  by_cases hx4 : x ≤ 4
  · have hpi_bd : primePi x ≤ x := by
      have hle4 : primePi x ≤ primePi 4 := primePi_mono hx4
      have h4 : primePi 4 ≤ 2 := by
        unfold primePi
        rw [Nat.floor_ofNat]
        exact_mod_cast (by decide : Nat.primeCounting 4 ≤ 2)
      linarith
    have hli_bd : logIntegral x ≤ x / Real.log 2 := by
      have hnonneg : ∀ t ∈ Set.uIcc (2 : ℝ) x, (Real.log t)⁻¹ ≤ (Real.log 2)⁻¹ := by
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht.1
        exact inv_anti₀ hlog2_pos hlt
      have hint : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 x := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hx]
        have hlog_c : ContinuousOn Real.log (Set.Icc 2 x) :=
          Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le zero_lt_two ht.1).ne'
        exact hlog_c.inv₀ fun t ht => (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'
      calc logIntegral x = ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ := rfl
        _ ≤ ∫ _t in (2 : ℝ)..x, (Real.log 2)⁻¹ :=
            intervalIntegral.integral_mono_on hx hint (by simp) fun t ht =>
              hnonneg t (by rwa [Set.uIcc_of_le hx])
        _ = (x - 2) * (Real.log 2)⁻¹ := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ x / Real.log 2 := by
            rw [← div_eq_mul_inv]
            exact div_le_div_of_nonneg_right (by linarith) hlog2_pos.le
    have hli_nn : 0 ≤ logIntegral x := by
      refine intervalIntegral.integral_nonneg hx fun t ht => ?_
      exact inv_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
    have h1 : |primePi x - logIntegral x| ≤ (Real.log 4 + 3 + 2 / Real.log 2) * x := by
      rw [abs_le]
      have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by
        rw [show (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) by simp]
        refine Real.log_lt_log (Real.exp_pos _) ?_
        calc Real.exp (1 / 2 : ℝ) = Real.sqrt (Real.exp 1) := by
              rw [Real.sqrt_eq_rpow, Real.exp_one_rpow]
          _ < Real.sqrt 4 := Real.sqrt_lt_sqrt (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9])
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h_inv_log2 : (Real.log 2)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ hlog2_pos]; linarith
      have h_li_2x : logIntegral x ≤ 2 * x := hli_bd.trans (by
        rw [div_eq_mul_inv]; exact (mul_le_mul_of_nonneg_left h_inv_log2 hx0.le).trans_eq (mul_comm _ _))
      have h_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      constructor
      · have : -((Real.log 4 + 3 + 2 / Real.log 2) * x) ≤ -logIntegral x := by
          nlinarith [hx0, hlog2_pos, div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog2_pos.le]
        linarith [primePi_nonneg x]
      · have : primePi x ≤ (Real.log 4 + 3 + 2 / Real.log 2) * x := by
          have : 0 ≤ 2 / Real.log 2 := by positivity
          nlinarith [hx0]
        linarith [hli_nn]
    have hexp_ge : 1 ≤ Real.exp (c' * Real.sqrt (Real.log 4)) *
        Real.exp (-c' * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have hle : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log 4) :=
        Real.sqrt_le_sqrt (Real.log_le_log hx0 hx4)
      nlinarith [hc']
    calc |primePi x - logIntegral x|
        ≤ (Real.log 4 + 3 + 2 / Real.log 2) * x := h1
      _ ≤ (Real.log 4 + 3 + 2 / Real.log 2) * x *
            (Real.exp (c' * Real.sqrt (Real.log 4)) * Real.exp (-c' * Real.sqrt (Real.log x))) :=
          le_mul_of_one_le_right (by positivity) hexp_ge
      _ = C_small * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by dsimp [C_small]; ring
      _ ≤ max C_small C_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_left _ _
  · have hx_gt4 : 4 < x := not_le.mp hx4
    have hsqrt2 : 2 ≤ Real.sqrt x := by
      rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsqrtx : Real.sqrt x ≤ x := by
      calc Real.sqrt x ≤ Real.sqrt x * 2 := le_mul_of_one_le_right (Real.sqrt_nonneg _) one_le_two
        _ ≤ Real.sqrt x * Real.sqrt x := by gcongr
        _ = x := Real.mul_self_sqrt hx0.le
    have h_id : primePi x - logIntegral x =
        (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
          ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) :=
      primePi_sub_li_eq_theta_sub_id_abel hx
    have hint_diff : IntervalIntegrable
        (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) volume 2 x := by
      have hcont : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc 2 x) := by
        have hlog_c : ContinuousOn Real.log (Set.Icc 2 x) :=
          Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le zero_lt_two ht.1).ne'
        refine (continuousOn_id.mul (hlog_c.pow 2)).inv₀ fun t ht => ?_
        have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_two ht.1).ne'
        have hlt0 : Real.log t ≠ 0 := (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'
        exact mul_ne_zero ht0 (pow_ne_zero 2 hlt0)
      have h_th_int : IntervalIntegrable
          (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
      have h_id_int : IntervalIntegrable
          (fun t : ℝ => t / (t * Real.log t ^ 2)) volume 2 x := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hx]
        exact continuousOn_id.mul hcont
      simpa only [sub_div] using h_th_int.sub h_id_int
    have hmem_uIcc : Real.sqrt x ∈ Set.uIcc (2 : ℝ) x := by
      rw [Set.uIcc_of_le hx]; exact ⟨hsqrt2, hsqrtx⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint_diff.mono_set (Set.uIcc_subset_uIcc_left hmem_uIcc))
      (hint_diff.mono_set (Set.uIcc_subset_uIcc_right hmem_uIcc))
    have hleft_int : |∫ t in (2 : ℝ)..Real.sqrt x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        ((Real.log 4 + 1) / Real.log 2 ^ 2) * Real.sqrt x := by
      have hnorm := intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) hsqrt2
      have hint_sub : IntervalIntegrable
          (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
          volume 2 (Real.sqrt x) :=
        hint_diff.mono_set (Set.uIcc_subset_uIcc_left hmem_uIcc)
      have hmono : ∫ t in (2 : ℝ)..Real.sqrt x,
          ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤
          ∫ _t in (2 : ℝ)..Real.sqrt x, (Real.log 4 + 1) / Real.log 2 ^ 2 := by
        refine intervalIntegral.integral_mono_on hsqrt2 hint_sub.norm (by simp) fun t ht => ?_
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ht.1
        have hlogt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht.1
        have hnum : |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := by
          rw [abs_le]
          have hth : Chebyshev.theta t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
          have hth0 : 0 ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
          constructor <;> linarith [ht0.le, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos (by linarith)))]
        calc |Chebyshev.theta t - t| / (t * Real.log t ^ 2)
            ≤ ((Real.log 4 + 1) * t) / (t * Real.log 2 ^ 2) := by gcongr
          _ = (Real.log 4 + 1) / Real.log 2 ^ 2 := by field_simp [ht0.ne']
      refine (hnorm.trans hmono).trans ?_
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hnn : 0 ≤ (Real.log 4 + 1) / Real.log 2 ^ 2 := by positivity
      nlinarith
    have hright_int : |∫ t in Real.sqrt x..x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        (Cθ / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      have hnorm := intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) hsqrtx
      have hint_sub : IntervalIntegrable
          (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
          volume (Real.sqrt x) x :=
        hint_diff.mono_set (Set.uIcc_subset_uIcc_right hmem_uIcc)
      have hmono : ∫ t in Real.sqrt x..x,
          ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤
          ∫ _t in Real.sqrt x..x, (Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)) := by
        refine intervalIntegral.integral_mono_on hsqrtx hint_sub.norm (by simp) fun t ht => ?_
        have ht2 : 2 ≤ t := hsqrt2.trans ht.1
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ht2
        have hlogt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht2
        have hlogt_pos : 0 < Real.log t := lt_of_lt_of_le hlog2_pos hlogt_ge
        have hlogt_sqrt : Real.log x / 2 ≤ Real.log t := by
          have := Real.log_le_log (Real.sqrt_pos.mpr hx0) ht.1
          rw [Real.log_sqrt hx0.le] at this
          linarith
        have hθ_t := hθ t ht2
        have hsqrt_logt : Real.sqrt (Real.log x) / Real.sqrt 2 ≤ Real.sqrt (Real.log t) := by
          rw [← Real.sqrt_div hlogx_pos.le]
          exact Real.sqrt_le_sqrt hlogt_sqrt
        have hexp_t : Real.exp (-cθ * Real.sqrt (Real.log t)) ≤
            Real.exp (-c' * Real.sqrt (Real.log x)) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : c' ≤ cθ / Real.sqrt 2 := min_le_left _ _
          have h2 : c' * Real.sqrt (Real.log x) ≤ (cθ / Real.sqrt 2) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
          have h3 : (cθ / Real.sqrt 2) * Real.sqrt (Real.log x) =
              cθ * (Real.sqrt (Real.log x) / Real.sqrt 2) := by ring
          have h4 : cθ * (Real.sqrt (Real.log x) / Real.sqrt 2) ≤ cθ * Real.sqrt (Real.log t) :=
            mul_le_mul_of_nonneg_left hsqrt_logt hcθ.le
          linarith
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlogt_pos))]
        calc |Chebyshev.theta t - t| / (t * Real.log t ^ 2)
            ≤ (Cθ * t * Real.exp (-cθ * Real.sqrt (Real.log t))) / (t * Real.log 2 ^ 2) := by gcongr
          _ = (Cθ / Real.log 2 ^ 2) * Real.exp (-cθ * Real.sqrt (Real.log t)) := by
              field_simp [ht0.ne']
          _ ≤ (Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)) := by gcongr
      refine (hnorm.trans hmono).trans ?_
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hnn : 0 ≤ (Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)) := by positivity
      have hlen : x - Real.sqrt x ≤ x := by linarith [Real.sqrt_nonneg x]
      calc (x - Real.sqrt x) * ((Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)))
          ≤ x * ((Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x))) := by gcongr
        _ = (Cθ / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have hθ_x := hθ x hx
    have hexp_x1 : Real.exp (-cθ * Real.sqrt (Real.log x)) ≤
        Real.exp (-c' * Real.sqrt (Real.log x)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : c' ≤ cθ / Real.sqrt 2 := min_le_left _ _
      have h2 : cθ / Real.sqrt 2 ≤ cθ := div_le_self hcθ.le (Real.one_le_sqrt.mpr (by norm_num))
      nlinarith [Real.sqrt_nonneg (Real.log x)]
    have h_sqrt_x : Real.sqrt x ≤ x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      refine (sqrt_le_mul_exp_neg_quarter hx).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx0.le
      nlinarith [min_le_right (cθ / Real.sqrt 2) (1 / 4 : ℝ), Real.sqrt_nonneg (Real.log x)]
    have h_one_le_x : 1 ≤ x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt x := by linarith
      exact h1.trans h_sqrt_x
    have h_term1 : |(Chebyshev.theta x - x) / Real.log x| ≤
        (Cθ / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      rw [abs_div, abs_of_pos hlogx_pos]
      calc |Chebyshev.theta x - x| / Real.log x
          ≤ (Cθ * x * Real.exp (-cθ * Real.sqrt (Real.log x))) / Real.log 2 := by gcongr
        _ ≤ (Cθ * x * Real.exp (-c' * Real.sqrt (Real.log x))) / Real.log 2 := by gcongr
        _ = (Cθ / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have h_term2 : |2 / Real.log 2| ≤
        (2 / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      rw [abs_of_pos (by positivity)]
      calc 2 / Real.log 2 = (2 / Real.log 2) * 1 := (mul_one _).symm
        _ ≤ (2 / Real.log 2) * (x * Real.exp (-c' * Real.sqrt (Real.log x))) := by gcongr
        _ = (2 / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have h_term3 : |∫ t in (2 : ℝ)..Real.sqrt x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        ((Real.log 4 + 1) / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      refine hleft_int.trans ?_
      calc ((Real.log 4 + 1) / Real.log 2 ^ 2) * Real.sqrt x
          ≤ ((Real.log 4 + 1) / Real.log 2 ^ 2) * (x * Real.exp (-c' * Real.sqrt (Real.log x))) := by
            gcongr
        _ = ((Real.log 4 + 1) / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have h_int_sum : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        |∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| +
          |∫ t in Real.sqrt x..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| := by
      rw [← hsplit]; exact abs_add_le _ _
    have h_all : |primePi x - logIntegral x| ≤
        |(Chebyshev.theta x - x) / Real.log x| + |2 / Real.log 2| +
          |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| := by
      rw [h_id]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    calc |primePi x - logIntegral x|
        ≤ (Cθ / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) +
            (2 / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) +
            (((Real.log 4 + 1) / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) +
              (Cθ / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x))) := by linarith
      _ = C_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by dsimp [C_large]; ring
      _ ≤ max C_small C_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_right _ _

/-- `Asymptotics.IsBigO` formulation of the de la Vallée Poussin error term for `Chebyshev.psi`. -/
theorem psi_sub_id_isBigO_exp :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] fun x : ℝ =>
        x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨C, hC, c, hc, hbd⟩ := abs_psi_sub_id_le_exp
  refine ⟨c, hc, (Asymptotics.isBigO_iff).mpr ⟨C, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hpos : 0 ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    have : 0 ≤ x := by linarith
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (by linarith : 0 ≤ x), mul_assoc] using hbd x hx

/-- `Asymptotics.IsBigO` formulation of the de la Vallée Poussin error term for `Chebyshev.theta`. -/
theorem theta_sub_id_isBigO_exp :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] fun x : ℝ =>
        x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨C, hC, c, hc, hbd⟩ := abs_theta_sub_id_le_exp
  refine ⟨c, hc, (Asymptotics.isBigO_iff).mpr ⟨C, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hpos : 0 ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    have : 0 ≤ x := by linarith
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (by linarith : 0 ≤ x), mul_assoc] using hbd x hx

/-- `Asymptotics.IsBigO` formulation of the de la Vallée Poussin error term for `primePi - logIntegral`. -/
theorem primePi_sub_li_isBigO_exp :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => primePi x - logIntegral x) =O[atTop] fun x : ℝ =>
        x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨C, hC, c, hc, hbd⟩ := abs_primePi_sub_logIntegral_le_exp
  refine ⟨c, hc, (Asymptotics.isBigO_iff).mpr ⟨C, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hpos : 0 ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    have : 0 ≤ x := by linarith
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (by linarith : 0 ≤ x), mul_assoc] using hbd x hx

end AnalyticNumberTheory.PrimeDistribution
