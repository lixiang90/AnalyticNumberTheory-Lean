import AnalyticNumberTheory.AnalyticTools.Summation.DivisorSums
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Riemann's prime-power counting function

A real parameter sets the weight of an exact endpoint. Taking this weight to be one counts
inclusively, zero counts strictly, and one half gives the midpoint convention used in Riemann
explicit formulas. Both finite root transforms preserve this parameter.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.PrimeDistribution

/-- Weight of a summand already known to lie below or at the cutoff `x`. -/
def endpointWeight (c x : ℝ) (n : ℕ) : ℝ := if (n : ℝ) = x then c else 1

/-- Count primes up to `x`, giving a prime at the endpoint weight `c`. -/
def primePiWithEndpoint (c x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, endpointWeight c x p

/-- Riemann's weighted prime-power count. A power `pᵏ` has mass `1/k`, multiplied by
`c` when `pᵏ = x`. At `c = 1/2` this is the midpoint counting function. -/
def riemannPrimeCounting (c x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, endpointWeight c x n * (Λ n / Real.log n)

/-- Full endpoint weight recovers the usual inclusive prime counting function. -/
theorem primePiWithEndpoint_one (x : ℝ) : primePiWithEndpoint 1 x = primePi x := by
  simp [primePiWithEndpoint, endpointWeight, primePi_eq_card_primesLE]

/-- With full endpoint weight, Riemann's counting function sums `Λ(n)/log n` up to `x`. -/
theorem riemannPrimeCounting_one (x : ℝ) :
    riemannPrimeCounting 1 x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.log n := by
  simp [riemannPrimeCounting, endpointWeight]

private theorem sum_endpointWeight_succ (a : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    ∑ m ∈ Ioc 0 (n + 1), endpointWeight c (↑(n + 1 : ℕ)) m * a m =
      (∑ m ∈ Ioc 0 n, a m) + c * a (n + 1) := by
  rw [sum_Ioc_succ_top (Nat.zero_le n)]
  congr 1
  · refine sum_congr rfl fun m hm => ?_
    have h : (m : ℝ) ≠ ↑(n + 1 : ℕ) := by
      exact_mod_cast (Nat.ne_of_lt (Nat.lt_succ_of_le (mem_Ioc.mp hm).2))
    simp only [endpointWeight, ite_eq_right h, one_mul]
  · simp [endpointWeight]

/-- A prime-power jump at the positive integer `n+1` has mass `Λ(n+1)/log(n+1)`. -/
theorem riemannPrimeCounting_succ (c : ℝ) (n : ℕ) :
    riemannPrimeCounting c (↑(n + 1 : ℕ)) = riemannPrimeCounting 1 n +
      c * (Λ (n+1) / Real.log (↑(n+1 : ℕ))) := by
  rw [riemannPrimeCounting_one, riemannPrimeCounting, Nat.floor_natCast, Nat.floor_natCast]
  exact sum_endpointWeight_succ _ c n

private theorem primePiWithEndpoint_eq_sum_Ioc (c x : ℝ) :
    primePiWithEndpoint c x = ∑ p ∈ Ioc 0 ⌊x⌋₊,
      endpointWeight c x p * (if p.Prime then 1 else 0) := by
  simp [primePiWithEndpoint, Nat.primesLE_eq_filter_Ioc_zero, sum_filter, mul_ite]

/-- At an integer, the prime count changes only if that integer is prime. -/
theorem primePiWithEndpoint_succ (c : ℝ) (n : ℕ) :
    primePiWithEndpoint c (↑(n + 1 : ℕ)) = primePi n +
      c * (if (n+1).Prime then 1 else 0) := by
  rw [← primePiWithEndpoint_one, primePiWithEndpoint_eq_sum_Ioc,
    primePiWithEndpoint_eq_sum_Ioc, Nat.floor_natCast, Nat.floor_natCast,
    sum_endpointWeight_succ]
  simp [endpointWeight]

/-- At a positive integer, half weight gives the arithmetic mean of the inclusive Riemann
counts immediately before and at its jump. -/
theorem riemannPrimeCounting_half_succ (n : ℕ) :
    riemannPrimeCounting (1/2) (↑(n+1 : ℕ)) =
      (riemannPrimeCounting 1 n + riemannPrimeCounting 1 (↑(n+1 : ℕ))) / 2 := by
  rw [riemannPrimeCounting_succ, riemannPrimeCounting_succ 1]
  ring

/-- At a positive integer, the midpoint prime count averages the two consecutive values of
the ordinary prime counting function. -/
theorem primePiWithEndpoint_half_succ (n : ℕ) :
    primePiWithEndpoint (1/2) (↑(n+1 : ℕ)) = (primePi n + primePi (↑(n+1 : ℕ))) / 2 := by
  rw [primePiWithEndpoint_succ, ← primePiWithEndpoint_one (↑(n+1 : ℕ)),
    primePiWithEndpoint_succ]
  ring

private theorem endpointWeight_pow (c : ℝ) {x : ℝ} (hx : 0 ≤ x) (p : ℕ)
    {k : ℕ} (hk : 0 < k) :
    endpointWeight c x (p ^ k) = endpointWeight c (x ^ ((1 : ℝ) / k)) p := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hroot (y : ℝ) (hy : 0 ≤ y) : (y ^ k) ^ ((1 : ℝ) / k) = y := by
    rw [← Real.rpow_natCast_mul hy, mul_one_div_cancel hk', Real.rpow_one]
  have hpow : (x ^ ((1 : ℝ) / k)) ^ k = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel hk', Real.rpow_one]
  have hiff : ((p ^ k : ℕ) : ℝ) = x ↔ (p : ℝ) = x ^ ((1 : ℝ) / k) := by
    rw [Nat.cast_pow]
    exact ⟨fun h => h ▸ (hroot p (Nat.cast_nonneg p)).symm, fun h => h ▸ hpow⟩
  simp only [endpointWeight, hiff]

/-- Decompose Riemann's count by the exponent of each prime power, keeping the same endpoint
weight after taking roots. Any larger finite exponent cutoff gives the same sum. -/
theorem riemannPrimeCounting_eq_sum_primePiWithEndpoint (c : ℝ) {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    riemannPrimeCounting c x = ∑ k ∈ Icc 1 N,
      primePiWithEndpoint c (x ^ ((1 : ℝ) / k)) / k := by
  let f (n : ℕ) := endpointWeight c x n * (Λ n / Real.log n)
  change ∑ n ∈ Ioc 0 ⌊x⌋₊, f n = _
  have hfilter : ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, f n := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : IsPrimePow n
    · simp [hn]
    · simp [hn, f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  rw [← hfilter, Chebyshev.sum_PrimePow_eq_sum_sum' f hx hN]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  rw [primePiWithEndpoint, Nat.primesLE_eq_filter_Ioc_zero, sum_div]
  refine sum_congr rfl fun p hp => ?_
  have hp' := (mem_filter.mp hp).2
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp'.one_lt)).ne'
  simp only [f, endpointWeight_pow c hx p hk0, ArithmeticFunction.vonMangoldt_apply_pow hk0.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp', Nat.cast_pow, Real.log_pow]
  field_simp [hl, Nat.cast_ne_zero.mpr hk0.ne']

private theorem exponentCutoff_root {x : ℝ} (hx : 0 < x) (d : ℕ) :
    ⌊Real.log (x ^ ((1 : ℝ) / d)) / Real.log 2⌋₊ =
      ⌊Real.log x / Real.log 2⌋₊ / d := by
  rw [Real.log_rpow hx, ← Nat.floor_div_natCast]
  congr 1
  ring

/-- Finite Möbius inversion recovers the prime counting function from Riemann's prime-power
count for every endpoint weight, including points which are exact prime powers. -/
theorem primePiWithEndpoint_eq_sum_moebius_riemannPrimeCounting (c : ℝ) {x : ℝ}
    (hx : 0 < x) {N : ℕ} (hNpos : 1 ≤ N) (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    primePiWithEndpoint c x = ∑ d ∈ Icc 1 N,
      ((μ d : ℝ) / d) * riemannPrimeCounting c (x ^ ((1 : ℝ) / d)) := by
  let F (n : ℕ) := primePiWithEndpoint c (x ^ ((1 : ℝ) / n)) / n
  calc
    primePiWithEndpoint c x = F 1 := by simp [F]
    _ = _ := (sum_moebius_mul_sum_multiples hNpos F).symm
    _ = _ := by
      refine sum_congr rfl fun d hd => ?_
      rw [riemannPrimeCounting_eq_sum_primePiWithEndpoint c (Real.rpow_nonneg hx.le _)
        (N := N / d) (by rw [exponentCutoff_root hx]; exact Nat.div_le_div_right hN)]
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hroot : (x ^ ((1 : ℝ) / d)) ^ ((1 : ℝ) / j) = x ^ ((1 : ℝ) / (d*j : ℕ)) := by
        rw [← Real.rpow_mul hx.le, Nat.cast_mul]
        congr 1
        simp [one_div, mul_comm]
      rw [hroot]
      dsimp [F]
      push_cast
      ring

/-- The usual inclusive prime-power identity with its natural exponent cutoff. -/
theorem riemannPrimeCounting_eq_sum_primePi {x : ℝ} (hx : 0 ≤ x) :
    riemannPrimeCounting 1 x = ∑ k ∈ Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      primePi (x ^ ((1 : ℝ) / k)) / k := by
  simpa only [primePiWithEndpoint_one] using
    riemannPrimeCounting_eq_sum_primePiWithEndpoint 1 hx le_rfl

/-- Riemann's finite inversion of the usual inclusive count for `x ≥ 2`. -/
theorem primePi_eq_sum_moebius_riemannPrimeCounting {x : ℝ} (hx : 2 ≤ x) :
    primePi x = ∑ d ∈ Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      ((μ d : ℝ) / d) * riemannPrimeCounting 1 (x ^ ((1 : ℝ) / d)) := by
  have hl : 1 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)), one_mul]
    exact Real.log_le_log (by norm_num) hx
  simpa only [primePiWithEndpoint_one] using
    primePiWithEndpoint_eq_sum_moebius_riemannPrimeCounting 1 (by linarith : 0 < x) hl le_rfl

end AnalyticNumberTheory.PrimeDistribution
