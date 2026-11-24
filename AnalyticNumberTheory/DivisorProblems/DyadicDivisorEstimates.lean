import AnalyticNumberTheory.DivisorProblems.SawtoothErrors
import AnalyticNumberTheory.DivisorProblems.SawtoothApproximation
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.VanDerCorput

/-!
# Dyadic estimates for the divisor problem

Split the short sawtooth sum in the divisor error into dyadic intervals. On any
subinterval of `[D,2D]`, the second derivative of the reciprocal phase `A/t`
varies by at most a factor of eight. This yields a uniform bound on its exponential
sums, including the final incomplete interval.
-/

open Finset
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.DivisorProblems

/-- The integer points in `(2^j, 2^(j+1)]` up to the cutoff `N`. -/
def dyadicBlock (N j : ℕ) : Finset ℕ :=
  Ioc (2 ^ j) (min N (2 ^ (j + 1)))

/-- Split a sum over positive integers into the first summand and half-open dyadic blocks.
The last block can be incomplete, and blocks above the cutoff are empty. -/
theorem sum_Icc_eq_dyadic_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {N K : ℕ} (hN : 1 ≤ N) (hK : N ≤ 2 ^ K) :
    ∑ n ∈ Icc 1 N, f n = f 1 + ∑ j ∈ range K, ∑ n ∈ dyadicBlock N j, f n := by
  have hsplit (k : ℕ) :
      ∑ n ∈ Ioc 0 (min N (2 ^ k)), f n =
        f 1 + ∑ j ∈ range k, ∑ n ∈ dyadicBlock N j, f n := by
    induction k with
    | zero => simp [min_eq_right hN, Nat.Ioc_succ_singleton]
    | succ k ih =>
      rw [sum_range_succ, ← add_assoc, ← ih]
      by_cases hk : 2 ^ k ≤ N
      · rw [dyadicBlock, min_eq_right hk]
        exact (sum_Ioc_consecutive f (Nat.zero_le _)
          (le_min hk (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ k)))).symm
      · have hle : N ≤ 2 ^ k := by omega
        have hle' : N ≤ 2 ^ (k + 1) := hle.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))
        simp [dyadicBlock, min_eq_left hle, min_eq_left hle', Ioc_eq_empty_of_le hle]
  simpa only [min_eq_left hK, ← Icc_add_one_left_eq_Ioc, zero_add] using hsplit K

/-- Bound the divisor error by the absolute sawtooth sums on the dyadic blocks below `√x`. -/
theorem abs_divisorError_le_dyadic_sawtooth {x : ℝ} (hx : 1 ≤ x) {K : ℕ}
    (hK : ⌊Real.sqrt x⌋₊ ≤ 2 ^ K) :
    |divisorError x| ≤ 9 + 2 * ∑ j ∈ range K,
      |∑ n ∈ dyadicBlock ⌊Real.sqrt x⌋₊ j, sawtooth (x / n)| := by
  let S := ∑ n ∈ Icc 1 ⌊Real.sqrt x⌋₊, sawtooth (x / n)
  have hsplit := sum_Icc_eq_dyadic_blocks (fun n : ℕ => sawtooth (x / n))
    (Nat.floor_pos.mpr (Real.one_le_sqrt.mpr hx)) hK
  have hS : |S| ≤ 1 / 2 + ∑ j ∈ range K,
      |∑ n ∈ dyadicBlock ⌊Real.sqrt x⌋₊ j, sawtooth (x / n)| := by
    dsimp only [S]
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add (sawtooth_abs_le _) (Finset.abs_sum_le_sum_abs _ _))
  have hrem : |divisorError x + 2 * S| ≤ 8 := abs_divisorError_add_two_sum_sawtooth_le hx
  have htri := abs_sub (divisorError x + 2 * S) (2 * S)
  rw [add_sub_cancel_right, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
  linarith only [htri, hrem, hS]

/-- The reciprocal-phase exponential sum on any integer interval `(a,b] ⊆ (D,2D]`.
Here `A` can in particular be `h*x` for any positive Fourier frequency `h`. -/
theorem norm_sum_reciprocal_phase_le {A : ℝ} (hA : 0 < A) {D a b : ℕ}
    (hD : 0 < D) (hDa : D ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * D) :
    ‖∑ n ∈ Ioc a b, e (A / n)‖ ≤
      180 * (((b : ℝ) - a) * Real.sqrt (A / (4 * (D : ℝ) ^ 3)) +
        (Real.sqrt (A / (4 * (D : ℝ) ^ 3)))⁻¹) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
    positivity
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hpos {t : ℝ} (ht : t ∈ Set.Icc (a : ℝ) b) : 0 < t :=
    hD'.trans_le ((Nat.cast_le.mpr hDa).trans ht.1)
  let lam := A / (4 * (D : ℝ) ^ 3)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have h := vanDerCorput_second_deriv (f := fun t => A / t)
    (f' := fun t => -A / t ^ 2) (f'' := fun t => 2 * A / t ^ 3)
    hab hlam (by norm_num : (1 : ℝ) ≤ 8)
    (fun t ht => by
      simpa only [id_eq, zero_mul, mul_one, zero_sub] using
        (hasDerivAt_const t A).fun_div (hasDerivAt_id t) (hpos ht).ne')
    (fun t ht => by
      convert (hasDerivAt_const t (-A)).fun_div (hasDerivAt_pow 2 t) (pow_ne_zero _ (hpos ht).ne') using 1
      field_simp [(hpos ht).ne']
      ring)
    (continuousOn_const.div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero _ (hpos ht).ne'))
    (fun t ht => by
      have hlow : (D : ℝ) ≤ t := (Nat.cast_le.mpr hDa).trans ht.1
      have hhigh : t ≤ 2 * (D : ℝ) := ht.2.trans (by exact_mod_cast hb)
      have ht0 := hpos ht
      rw [abs_of_pos (by positivity)]
      constructor
      · apply (div_le_div_iff₀ (by positivity : 0 < 4 * (D : ℝ) ^ 3) (by positivity)).2
        calc A * t ^ 3 ≤ A * (2 * (D : ℝ)) ^ 3 := by gcongr
             _ = 2 * A * (4 * (D : ℝ) ^ 3) := by ring
      · calc 2 * A / t ^ 3 ≤ 2 * A / (D : ℝ) ^ 3 := by gcongr
             _ = 8 * lam := by dsimp [lam]; ring)
  simpa only [e, Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow,
    show (20 : ℝ) * 8 + 20 = 180 by norm_num, lam] using h

/-- An explicit bound for the sawtooth sum on a possibly incomplete dyadic interval.
The Fourier cutoff and the smoothing step are free parameters. -/
theorem abs_sum_reciprocal_sawtooth_dyadic_le {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (h1 : h < 1) {D a b H : ℕ} (hD : 0 < D) (hDa : D ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * D) (hH : 1 ≤ H) :
    h * |∑ d ∈ Ioc a b, sawtooth (x / d)| ≤
      (b - a : ℕ) * ((H : ℝ)⁻¹ / Real.pi ^ 2 + h ^ 2 / 2) +
        (∑ n ∈ Icc 1 H, min 2 (2 * Real.pi * n * h) *
          (180 * (((b : ℝ) - a) * Real.sqrt (n * x / (4 * (D : ℝ) ^ 3)) +
            (Real.sqrt (n * x / (4 * (D : ℝ) ^ 3)))⁻¹)) / (n : ℝ) ^ 2) /
          (2 * Real.pi ^ 2) := by
  have hsum := abs_sum_sawtooth_le_exponential_sums (Ioc a b) (fun d : ℕ => x / d) hH hh h1
  rw [Nat.card_Ioc] at hsum
  apply hsum.trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine sum_le_sum fun n hn => div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  have hweight : ‖e (n * h) - 1‖ ≤ min 2 (2 * Real.pi * n * h) := by
    rw [norm_sub_rev, norm_one_sub_e]
    have hd : distToInt (n * h) ≤ n * h := by
      simpa [abs_of_nonneg (mul_nonneg hn0.le hh.le)] using distToInt_le_abs_sub_int (n * h) 0
    refine le_min (by linarith only [Real.sin_le_one (Real.pi * distToInt (n * h))]) ?_
    calc 2 * Real.sin (Real.pi * distToInt (n * h)) ≤ 2 * (Real.pi * distToInt (n * h)) := by
           gcongr
           exact Real.sin_le (mul_nonneg Real.pi_pos.le (distToInt_nonneg _))
         _ ≤ 2 * (Real.pi * (n * h)) := by gcongr
         _ = _ := by ring
  apply mul_le_mul hweight _ (norm_nonneg _) ((norm_nonneg _).trans hweight)
  simpa only [mul_div_assoc] using norm_sum_reciprocal_phase_le (mul_pos hn0 hx) hD hDa hab hb

end AnalyticNumberTheory.DivisorProblems
