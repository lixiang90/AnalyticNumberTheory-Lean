import AnalyticNumberTheory.DirichletLFunctions.FixedModulusPolynomialEnergy
import AnalyticNumberTheory.DirichletSeries.VerticalOrder
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Finite coefficient energy on the critical line -/

noncomputable section

open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- On the critical line the squared modulus of `n⁻ˢ` is exactly `1/n`.
This gives the finite character mean with explicit harmonic weights. -/
theorem critical_polynomial_energy {q : ℕ} [NeZero q] (a : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : s.re = 1/2) :
    (∑ χ : DirichletCharacter ℂ q, ‖dirichletPoly (fun n => a n * χ n) N s‖^2) ≤
      q.totient * (1 + (N : ℝ)/q) * ∑ n ∈ Icc 1 N, ‖a n‖^2/(n : ℝ) := by
  have H := fixed_modulus_polynomial_energy (q := q) (fun n => a n * (n : ℂ)^(-s)) 0 N
  rw [zero_add, ← Icc_add_one_left_eq_Ioc, zero_add] at H
  have he (χ : DirichletCharacter ℂ q) :
      dirichletPoly (fun n => a n * χ n) N s = ∑ n ∈ Icc 1 N, χ n * (a n * (n : ℂ)^(-s)) :=
    sum_congr rfl fun n _ => by ring
  simp_rw [he]
  apply H.trans_eq
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := (mem_Icc.mp hn).1
  rw [norm_mul, mul_pow, Complex.norm_natCast_cpow_of_pos hn₀, Complex.neg_re, hs,
    Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    div_eq_mul_inv]

/-- A bounded coefficient sequence costs at most the harmonic sum through `N`
in the critical-line mean. -/
theorem critical_polynomial_energy_of_bound {q : ℕ} [NeZero q] (a : ℕ → ℂ)
    {N : ℕ} {B : ℝ} (ha : ∀ n ∈ Icc 1 N, ‖a n‖ ≤ B) {s : ℂ} (hs : s.re = 1/2) :
    (∑ χ : DirichletCharacter ℂ q, ‖dirichletPoly (fun n => a n * χ n) N s‖^2) ≤
      q.totient * (1 + (N : ℝ)/q) * (B^2 * (1+Real.log N)) := by
  apply (critical_polynomial_energy a N hs).trans (mul_le_mul_of_nonneg_left _ (by positivity))
  have hh : (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹) ≤ 1+Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log N
  apply le_trans _ (mul_le_mul_of_nonneg_left hh (sq_nonneg B))
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2) (by positivity)

/-- Convert a uniform error for the nonprincipal characters and a polynomial
mean over all characters into a mean for the original values. -/
theorem nonprincipal_square_sum_le_of_approx {q : ℕ} [NeZero q]
    (F P : DirichletCharacter ℂ q → ℂ) {B E : ℝ}
    (hB : ∀ χ, χ ≠ 1 → ‖F χ - P χ‖ ≤ B) (hE : (∑ χ, ‖P χ‖^2) ≤ E) :
    (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖F χ‖^2) ≤ 2*E + 2*q.totient*B^2 := by
  let S := (univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1)
  have h (χ) (hχ : χ ∈ S) : ‖F χ‖^2 ≤ 2*‖P χ‖^2 + 2*B^2 := by
    have hf := (norm_le_norm_sub_add (F χ) (P χ)).trans (add_le_add (hB χ (mem_filter.mp hχ).2) le_rfl)
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hf 2, sq_nonneg (B - ‖P χ‖)]
  have hsum := sum_le_sum h
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hsum
  have hcard : (S.card : ℝ) ≤ q.totient := by
    exact_mod_cast (card_le_univ S).trans_eq (card_dirichletCharacter_eq_totient (q := q))
  have hp := (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun χ _ _ => sq_nonneg ‖P χ‖)).trans hE
  change (∑ χ ∈ S, ‖F χ‖^2) ≤ _
  nlinarith only [hsum, hp, mul_le_mul_of_nonneg_right hcard (sq_nonneg B)]

end AnalyticNumberTheory.DirichletLFunctions
