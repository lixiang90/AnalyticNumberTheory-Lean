import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-!
# Linear Exponential Sums and Weyl's Inequality

This file develops the basic theory of additive exponential sums `e(α) = exp(2πi α)` and Weyl
differencing:

- The additive character `e (α : ℝ) : ℂ`, periodicity, unit modulus, and exact geometric series
  evaluation over intervals.
- Distance to the nearest integer `distToInt (α : ℝ) = |α - round α|`, triangle inequalities,
  and the sharp linear exponential sum bound `min N (1 / (2 * distToInt α))`.
- The linear reciprocal-distance divisor sum bound
  `∑_{1 ≤ n ≤ X} min Y (1 / (2 * distToInt (α * n))) ≪ (X + q) log(2q) + XY/q`
  for `|α - a/q| ≤ 1/q²`, together with the elementary divisor bound `d(n) ≪_ε n^ε`.
- Forward difference and polynomial difference operators, Weyl's squaring inequality, and
  Weyl's inequality for degree-`k` real polynomials.
-/

noncomputable section

open Complex Finset Polynomial
open scoped BigOperators

namespace AnalyticNumberTheory.ExponentialSums

section AdditiveCharacterAndDistance

/-- The standard additive character `e(α) = exp(2πi α)` on `ℝ`. -/
def e (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * (α : ℂ) * Complex.I)

/-- `e 0 = 1`. -/
@[simp]
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- Multiplicativity of the additive character: `e (α + β) = e α * e β`. -/
theorem e_add (α β : ℝ) : e (α + β) = e α * e β := by
  simp only [e, Complex.ofReal_add]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Negation of the additive character: `e (-α) = (e α)⁻¹`. -/
theorem e_neg (α : ℝ) : e (-α) = (e α)⁻¹ := by
  simp only [e, Complex.ofReal_neg]
  rw [← Complex.exp_neg]
  congr 1
  ring

/-- Subtraction law for the additive character: `e (α - β) = e α * (e β)⁻¹`. -/
theorem e_sub (α β : ℝ) : e (α - β) = e α * (e β)⁻¹ := by
  rw [sub_eq_add_neg, e_add, e_neg]

/-- Conjugation / star law for the additive character: `star (e α) = e (-α)`. -/
theorem star_e (α : ℝ) : star (e α) = e (-α) := by
  simp only [e, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- `e` evaluates to `1` at every integer. -/
@[simp]
theorem e_intCast (n : ℤ) : e (n : ℝ) = 1 := by
  simp only [e, Complex.ofReal_intCast]
  have h : 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- `e` evaluates to `1` at every natural number. -/
@[simp]
theorem e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  simpa only [Int.cast_natCast] using e_intCast (n : ℤ)

/-- `1`-periodicity of `e`: `e (α + 1) = e α`. -/
@[simp]
theorem e_add_one (α : ℝ) : e (α + 1) = e α := by
  rw [e_add, show (1 : ℝ) = ((1 : ℤ) : ℝ) by norm_num, e_intCast, mul_one]

/-- Integer shift invariance of `e`: `e (α + n) = e α`. -/
@[simp]
theorem e_add_int (α : ℝ) (n : ℤ) : e (α + n) = e α := by
  rw [e_add, e_intCast, mul_one]

/-- `e` is `1`-periodic. -/
theorem e_periodic : Function.Periodic e 1 :=
  e_add_one

/-- `e α` always lies on the unit circle: `‖e α‖ = 1`. -/
@[simp]
theorem norm_e (α : ℝ) : ‖e α‖ = 1 := by
  have h : 2 * (Real.pi : ℂ) * (α : ℂ) * Complex.I = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, h, Complex.norm_exp_ofReal_mul_I]

/-- Natural-number power identity `e (n * α) = e α ^ n`. -/
theorem e_nsmul (n : ℕ) (α : ℝ) : e ((n : ℝ) * α) = e α ^ n := by
  simp only [e, Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Integer power identity `e (n * α) = e α ^ n`. -/
theorem e_zsmul (n : ℤ) (α : ℝ) : e ((n : ℝ) * α) = e α ^ n := by
  simp only [e, Complex.ofReal_mul, Complex.ofReal_intCast, ← Complex.exp_int_mul]
  congr 1
  ring

/-- Distance from `α : ℝ` to the nearest integer: `‖α‖ = |α - round α|`. -/
def distToInt (α : ℝ) : ℝ :=
  |α - round α|

/-- `distToInt α` is nonnegative. -/
theorem distToInt_nonneg (α : ℝ) : 0 ≤ distToInt α :=
  abs_nonneg _

/-- `distToInt α` is at most `1 / 2`. -/
theorem distToInt_le_half (α : ℝ) : distToInt α ≤ 1 / 2 :=
  abs_sub_round α

/-- Formula `distToInt α = min (Int.fract α) (1 - Int.fract α)`. -/
theorem distToInt_eq_min (α : ℝ) : distToInt α = min (Int.fract α) (1 - Int.fract α) :=
  abs_sub_round_eq_min α

/-- `distToInt α ≤ |α - n|` for every integer `n`. -/
theorem distToInt_le_abs_sub_int (α : ℝ) (n : ℤ) : distToInt α ≤ |α - n| :=
  round_le α n

/-- Integer shift invariance of `distToInt`. -/
@[simp]
theorem distToInt_add_int (α : ℝ) (n : ℤ) : distToInt (α + n) = distToInt α := by
  simp only [distToInt, round_add_intCast, Int.cast_add]
  ring_nf

/-- Unit shift invariance of `distToInt`. -/
@[simp]
theorem distToInt_add_one (α : ℝ) : distToInt (α + 1) = distToInt α := by
  simpa only [Int.cast_one] using distToInt_add_int α 1

/-- `distToInt` is `1`-periodic. -/
theorem distToInt_periodic : Function.Periodic distToInt 1 :=
  distToInt_add_one

/-- `distToInt` is even: `distToInt (-α) = distToInt α`. -/
@[simp]
theorem distToInt_neg (α : ℝ) : distToInt (-α) = distToInt α := by
  apply le_antisymm
  · calc distToInt (-α) ≤ |-α - (-round α : ℤ)| := distToInt_le_abs_sub_int (-α) (-round α)
      _ = |-(α - round α)| := by push_cast; ring_nf
      _ = distToInt α := abs_neg _
  · calc distToInt α ≤ |α - (-round (-α) : ℤ)| := distToInt_le_abs_sub_int α (-round (-α))
      _ = |-(-α - round (-α))| := by push_cast; ring_nf
      _ = distToInt (-α) := abs_neg _

/-- Triangle inequality for `distToInt`: `distToInt (α + β) ≤ distToInt α + distToInt β`. -/
theorem distToInt_add_le (α β : ℝ) : distToInt (α + β) ≤ distToInt α + distToInt β := by
  calc distToInt (α + β) ≤ |(α + β) - ((round α + round β : ℤ) : ℝ)| :=
        distToInt_le_abs_sub_int (α + β) (round α + round β)
    _ = |(α - round α) + (β - round β)| := by push_cast; ring_nf
    _ ≤ |α - round α| + |β - round β| := abs_add_le _ _

/-- Reverse triangle inequality for `distToInt`: `distToInt α - |β| ≤ distToInt (α + β)`. -/
theorem distToInt_sub_abs_le_add (α β : ℝ) : distToInt α - |β| ≤ distToInt (α + β) := by
  have h1 := distToInt_add_le (α + β) (-β)
  rw [show α + β + -β = α by ring] at h1
  have h2 : distToInt (-β) ≤ |β| := by
    rw [distToInt_neg]
    exact (distToInt_le_abs_sub_int β 0).trans_eq (by simp)
  linarith

/-- `distToInt α = 0` if and only if `α` is an integer. -/
theorem distToInt_eq_zero_iff (α : ℝ) : distToInt α = 0 ↔ ∃ n : ℤ, α = n := by
  constructor
  · intro h
    refine ⟨round α, ?_⟩
    exact sub_eq_zero.mp (abs_eq_zero.mp h)
  · rintro ⟨n, rfl⟩
    simp [distToInt]

/-- `0 < distToInt α` if and only if `α` is not an integer. -/
theorem distToInt_pos_iff (α : ℝ) : 0 < distToInt α ↔ ∀ n : ℤ, α ≠ n := by
  rw [lt_iff_le_and_ne, and_iff_right (distToInt_nonneg α), ne_comm, ne_eq, distToInt_eq_zero_iff]
  push Not
  rfl

/-- Exact formula for `distToInt (m / q)` for `m, q : ℕ`. -/
theorem distToInt_div_natCast (m q : ℕ) :
    distToInt ((m : ℝ) / q) = ((min (m % q) (q - m % q) : ℕ) : ℝ) / q := by
  unfold distToInt
  exact abs_sub_round_div_natCast_eq (α := ℝ) (m := m) (n := q)

/-- Relation between `|sin(π α)|` and `sin(π distToInt α)`. -/
theorem abs_sin_pi_mul_eq_sin_pi_distToInt (α : ℝ) :
    |Real.sin (Real.pi * α)| = Real.sin (Real.pi * distToInt α) := by
  have hsplit : Real.pi * α = Real.pi * (α - round α) + (round α : ℤ) * Real.pi := by ring
  rw [hsplit, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hbd : |Real.pi * (α - round α)| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc Real.pi * |α - round α| ≤ Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left (distToInt_le_half α) Real.pi_pos.le
      _ ≤ Real.pi := by linarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hbd, abs_mul, abs_of_pos Real.pi_pos]
  rfl

/-- Exact norm of `1 - e α`: equals `2 * sin (π * distToInt α)`. -/
theorem norm_one_sub_e (α : ℝ) : ‖1 - e α‖ = 2 * Real.sin (Real.pi * distToInt α) := by
  have hsq : ‖1 - e α‖ ^ 2 = (2 * |Real.sin (Real.pi * α)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hexp : e α = Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
      simp only [e]; congr 1; push_cast; ring
    rw [hexp]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_sub]
    have hcos : Real.cos (2 * Real.pi * α) = 1 - 2 * Real.sin (Real.pi * α) ^ 2 := by
      have h := Real.cos_two_mul (Real.pi * α)
      rw [show 2 * (Real.pi * α) = 2 * Real.pi * α by ring] at h
      have hsc := Real.sin_sq_add_cos_sq (Real.pi * α)
      linarith
    have hsc0 := Real.sin_sq_add_cos_sq (2 * Real.pi * α)
    calc (1 - Real.cos (2 * Real.pi * α)) * (1 - Real.cos (2 * Real.pi * α)) +
          -Real.sin (2 * Real.pi * α) * -Real.sin (2 * Real.pi * α)
        = 2 - 2 * Real.cos (2 * Real.pi * α) := by linarith [hsc0]
      _ = 4 * Real.sin (Real.pi * α) ^ 2 := by rw [hcos]; ring
      _ = (2 * |Real.sin (Real.pi * α)|) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have h1 : 0 ≤ ‖1 - e α‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * α)| := by positivity
  have hnorm : ‖1 - e α‖ = 2 * |Real.sin (Real.pi * α)| := by nlinarith
  rw [hnorm, abs_sin_pi_mul_eq_sin_pi_distToInt]

/-- Jordan lower bound `4 * distToInt α ≤ ‖1 - e α‖`. -/
theorem four_mul_distToInt_le_norm_one_sub_e (α : ℝ) : 4 * distToInt α ≤ ‖1 - e α‖ := by
  rw [norm_one_sub_e]
  have h0 : 0 ≤ Real.pi * distToInt α := mul_nonneg Real.pi_pos.le (distToInt_nonneg α)
  have h1 : Real.pi * distToInt α ≤ Real.pi / 2 := by
    calc Real.pi * distToInt α ≤ Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left (distToInt_le_half α) Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hsin := Real.mul_le_sin h0 h1
  have h2 : 2 / Real.pi * (Real.pi * distToInt α) = 2 * distToInt α := by
    field_simp [Real.pi_ne_zero]
  rw [h2] at hsin
  linarith

/-- `e α ≠ 1` if and only if `α` is not an integer. -/
theorem e_ne_one_iff (α : ℝ) : e α ≠ 1 ↔ ∀ n : ℤ, α ≠ n := by
  rw [← distToInt_pos_iff]
  constructor
  · intro hne
    by_contra hle
    have h0 : distToInt α = 0 := le_antisymm (not_lt.mp hle) (distToInt_nonneg α)
    have hnorm : ‖1 - e α‖ = 0 := by rw [norm_one_sub_e, h0]; simp
    have h1 : 1 - e α = 0 := norm_eq_zero.mp hnorm
    exact hne (sub_eq_zero.mp h1).symm
  · intro hpos heq
    have hnorm : ‖1 - e α‖ = 0 := by rw [heq, sub_self, norm_zero]
    linarith [four_mul_distToInt_le_norm_one_sub_e α]

end AdditiveCharacterAndDistance

section LinearExponentialSums

/-- Exact geometric series evaluation of `∑ n ∈ Finset.Ioc M (M + N), e (α * n)` when `α ∉ ℤ`. -/
theorem sum_Ioc_e_eq (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (M N : ℕ) :
    ∑ n ∈ Finset.Ioc M (M + N), e (α * n) =
      e (α * ((M + 1 : ℕ) : ℝ)) * (e (α * (N : ℝ)) - 1) / (e α - 1) := by
  have he_ne : e α ≠ 1 := (e_ne_one_iff α).mpr hα
  have hbij :
      ∑ n ∈ Finset.Ioc M (M + N), e (α * n) =
        ∑ k ∈ Finset.range N, e (α * ((M + 1 + k : ℕ) : ℝ)) := by
    refine Finset.sum_bij (fun n _ => n - (M + 1)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp only [Finset.mem_range]
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Ioc] at hn₁ hn₂
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      refine ⟨M + 1 + k, ?_, by omega⟩
      simp only [Finset.mem_Ioc]
      omega
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      congr 2
      have h1 : M + 1 + (n - (M + 1)) = n := by omega
      exact_mod_cast h1.symm
  rw [hbij]
  have hfac :
      ∑ k ∈ Finset.range N, e (α * ((M + 1 + k : ℕ) : ℝ)) =
        e (α * ((M + 1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range N, e α ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_add, mul_add, e_add, mul_comm α (k : ℝ), e_nsmul]
  rw [hfac, geom_sum_eq he_ne, ← e_nsmul N α, mul_comm (N : ℝ) α, mul_div_assoc]

/-- Exact geometric series evaluation of `∑ n ∈ Finset.Icc 1 N, e (α * n)` when `α ∉ ℤ`. -/
theorem sum_Icc_one_e_eq (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, e (α * n) = e α * (e (α * (N : ℝ)) - 1) / (e α - 1) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  simpa [← hIoc] using sum_Ioc_e_eq α hα 0 N

/-- Sharp inverse-sine bound on a linear exponential sum when `α ∉ ℤ`. -/
theorem norm_sum_Ioc_e_le_inv_sin (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), e (α * n)‖ ≤ (Real.sin (Real.pi * distToInt α))⁻¹ := by
  rw [sum_Ioc_e_eq α hα M N, norm_div, norm_mul, norm_e, one_mul, norm_sub_rev (e α) 1,
    norm_one_sub_e]
  have hpos : 0 < distToInt α := (distToInt_pos_iff α).mpr hα
  have hpi_le : Real.pi * distToInt α < Real.pi := by
    calc Real.pi * distToInt α ≤ Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left (distToInt_le_half α) Real.pi_pos.le
      _ < Real.pi := by linarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin (Real.pi * distToInt α) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hpos) hpi_le
  have hnum : ‖e (α * (N : ℝ)) - 1‖ ≤ 2 := by
    calc ‖e (α * (N : ℝ)) - 1‖ ≤ ‖e (α * (N : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_e, norm_one]; norm_num
  calc ‖e (α * (N : ℝ)) - 1‖ / (2 * Real.sin (Real.pi * distToInt α))
      ≤ 2 / (2 * Real.sin (Real.pi * distToInt α)) := by gcongr
    _ = (Real.sin (Real.pi * distToInt α))⁻¹ := by
          rw [← div_div, div_self two_ne_zero, one_div]

/-- Inverse linear distance bound `1 / (2 * distToInt α)` on a linear exponential sum (`α ∉ ℤ`). -/
theorem norm_sum_Ioc_e_le_inv_two_dist (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), e (α * n)‖ ≤ 1 / (2 * distToInt α) := by
  rw [sum_Ioc_e_eq α hα M N, norm_div, norm_mul, norm_e, one_mul, norm_sub_rev (e α) 1]
  have hpos : 0 < distToInt α := (distToInt_pos_iff α).mpr hα
  have hden : 4 * distToInt α ≤ ‖1 - e α‖ := four_mul_distToInt_le_norm_one_sub_e α
  have hnum : ‖e (α * (N : ℝ)) - 1‖ ≤ 2 := by
    calc ‖e (α * (N : ℝ)) - 1‖ ≤ ‖e (α * (N : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_e, norm_one]; norm_num
  calc ‖e (α * (N : ℝ)) - 1‖ / ‖1 - e α‖
      ≤ 2 / (4 * distToInt α) := div_le_div₀ zero_le_two hnum (by positivity) hden
    _ = 1 / (2 * distToInt α) := by ring

/-- Trivial triangle-inequality bound `N` on `∑_{n ∈ Ioc M (M + N)} e (α * n)`. -/
theorem norm_sum_Ioc_e_le_length (α : ℝ) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), e (α * n)‖ ≤ (N : ℝ) := by
  calc ‖∑ n ∈ Finset.Ioc M (M + N), e (α * n)‖
      ≤ ∑ n ∈ Finset.Ioc M (M + N), ‖e (α * n)‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Ioc M (M + N), (1 : ℝ) := by simp [norm_e]
    _ = (N : ℝ) := by simp [Nat.card_Ioc]

/-- Sharp combined linear exponential sum bound: `min N (1 / (2 * distToInt α))` for `α ∉ ℤ`. -/
theorem norm_sum_Ioc_e_le_min (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), e (α * n)‖ ≤ min (N : ℝ) (1 / (2 * distToInt α)) :=
  le_min (norm_sum_Ioc_e_le_length α M N) (norm_sum_Ioc_e_le_inv_two_dist α hα M N)

/-- Sharp combined linear exponential sum bound over `Finset.Icc 1 N` (`α ∉ ℤ`). -/
theorem norm_sum_Icc_one_e_le_min (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, e (α * n)‖ ≤ min (N : ℝ) (1 / (2 * distToInt α)) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  simpa [← hIoc] using norm_sum_Ioc_e_le_min α hα 0 N

/-- Sharp bound on an arbitrary integer interval `Finset.Ioc A B` (`A ≤ B : ℤ`) when `α ∉ ℤ`. -/
theorem norm_sum_Ioc_int_e_le_min (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) {A B : ℤ} (hAB : A ≤ B) :
    ‖∑ n ∈ Finset.Ioc A B, e (α * (n : ℝ))‖ ≤
      min ((B - A : ℤ) : ℝ) (1 / (2 * distToInt α)) := by
  let N : ℕ := (B - A).toNat
  have hBN : B = A + (N : ℤ) := by
    dsimp only [N]; omega
  have hbij :
      ∑ n ∈ Finset.Ioc A B, e (α * (n : ℝ)) =
        e (α * (A : ℝ)) * ∑ k ∈ Finset.Ioc 0 N, e (α * (k : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => (n - A).toNat) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ioc] at hn ⊢
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Ioc] at hn₁ hn₂
      omega
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      refine ⟨A + (k : ℤ), ?_, by omega⟩
      simp only [Finset.mem_Ioc]
      omega
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      have hcast : ((n - A).toNat : ℝ) = (n : ℝ) - (A : ℝ) := by
        have : ((n - A).toNat : ℤ) = n - A := by omega
        exact_mod_cast this
      rw [hcast, ← e_add]
      congr 1
      ring
  rw [hbij, norm_mul, norm_e, one_mul]
  have hN : (N : ℝ) = ((B - A : ℤ) : ℝ) := by exact_mod_cast (by omega : (N : ℤ) = B - A)
  rw [← hN]
  simpa only [zero_add] using norm_sum_Ioc_e_le_min α hα 0 N

/-- Unconditional upper bound function `linearExpBound Y θ` equal to `Y` when `θ ∈ ℤ` and
`min Y (1 / (2 * distToInt θ))` otherwise. -/
def linearExpBound (Y θ : ℝ) : ℝ :=
  if distToInt θ = 0 then Y else min Y (1 / (2 * distToInt θ))

/-- Nonnegativity of `linearExpBound Y θ` when `0 ≤ Y`. -/
theorem linearExpBound_nonneg {Y : ℝ} (hY : 0 ≤ Y) (θ : ℝ) : 0 ≤ linearExpBound Y θ := by
  unfold linearExpBound
  split_ifs
  · exact hY
  · exact le_min hY (by positivity [distToInt_nonneg θ])

/-- `linearExpBound Y θ ≤ Y`. -/
theorem linearExpBound_le_left (Y θ : ℝ) : linearExpBound Y θ ≤ Y := by
  unfold linearExpBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- `linearExpBound Y θ = linearExpBound Y (-θ)`. -/
@[simp]
theorem linearExpBound_neg (Y θ : ℝ) : linearExpBound Y (-θ) = linearExpBound Y θ := by
  simp [linearExpBound, distToInt_neg]

/-- Unconditional bound on `‖∑ n ∈ Finset.Ioc A B, e (α * n)‖` by `linearExpBound N α`
whenever `B - A ≤ N`. -/
theorem norm_sum_Ioc_int_e_le_linearExpBound (α : ℝ) {A B : ℤ} (hAB : A ≤ B) {N : ℕ}
    (hN : B - A ≤ (N : ℤ)) :
    ‖∑ n ∈ Finset.Ioc A B, e (α * (n : ℝ))‖ ≤ linearExpBound (N : ℝ) α := by
  by_cases h0 : distToInt α = 0
  · simp only [linearExpBound, h0, ↓reduceIte]
    calc ‖∑ n ∈ Finset.Ioc A B, e (α * (n : ℝ))‖
        ≤ ∑ _n ∈ Finset.Ioc A B, (1 : ℝ) := by
          refine (norm_sum_le _ _).trans_eq ?_
          simp [norm_e]
      _ = ((B - A : ℤ) : ℝ) := by
          simp only [Finset.sum_const, Int.card_Ioc, nsmul_eq_mul, mul_one]
          have : (((B - A).toNat : ℤ) : ℝ) = ((B - A : ℤ) : ℝ) := by
            congr 1; omega
          exact this
      _ ≤ (N : ℝ) := by exact_mod_cast hN
  · simp only [linearExpBound, h0, ↓reduceIte]
    have hα : ∀ n : ℤ, α ≠ n := (distToInt_pos_iff α).mp
      (lt_of_le_of_ne (distToInt_nonneg α) (Ne.symm h0))
    refine (norm_sum_Ioc_int_e_le_min α hα hAB).trans ?_
    exact min_le_min (by exact_mod_cast hN) le_rfl

end LinearExponentialSums

section DivisorBounds

private theorem sum_Icc_inv_le_one_add_log :
    ∀ m : ℕ, 1 ≤ m → ∑ j ∈ Finset.Icc 1 m, (j : ℝ)⁻¹ ≤ 1 + Real.log (m : ℝ)
  | 0, hm => by omega
  | 1, _ => by simp
  | m + 2, _ => by
    have hm1 : 1 ≤ m + 1 := Nat.succ_pos m
    have ih := sum_Icc_inv_le_one_add_log (m + 1) hm1
    have hm1_pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hm2_pos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    have hlog_step : ((m + 2 : ℕ) : ℝ)⁻¹ ≤
        Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
      have hratio_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) := by positivity
      have h1 := Real.log_le_sub_one_of_pos hratio_pos
      rw [Real.log_div hm1_pos.ne' hm2_pos.ne'] at h1
      have hdiff : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 = -((m + 2 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp [hm2_pos.ne']
        ring
      linarith
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 2)]
    linarith

private theorem one_add_log_half_le_log_two_mul {q : ℕ} (hq : 2 ≤ q) :
    1 + Real.log ((q / 2 : ℕ) : ℝ) ≤ Real.log (2 * (q : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hm_pos : 1 ≤ q / 2 := by omega
  have hm_posR : (0 : ℝ) < ((q / 2 : ℕ) : ℝ) := by exact_mod_cast hm_pos
  have hm_le : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
    have : 2 * (q / 2) ≤ q := by omega
    have : (2 : ℝ) * ((q / 2 : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    linarith
  have hlog_le : Real.log ((q / 2 : ℕ) : ℝ) ≤ Real.log (q : ℝ) - Real.log 2 := by
    calc Real.log ((q / 2 : ℕ) : ℝ) ≤ Real.log ((q : ℝ) / 2) := Real.log_le_log hm_posR hm_le
      _ = Real.log (q : ℝ) - Real.log 2 := Real.log_div hq0.ne' two_ne_zero
  have hlog2_gt : 1 / 2 < Real.log 2 := by
    have hhalf : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
      have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
      linarith
    have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
      rw [show (1 / 2 : ℝ) = -(-(1 / 2 : ℝ)) by ring, Real.exp_neg]
      rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    have hexp : Real.exp 1 < 4 := by
      have hsq : Real.exp 1 = Real.exp (1 / 2 : ℝ) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1; norm_num
      rw [hsq]
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have hlog4 : 1 < Real.log 4 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) hexp
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlog2q : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
    Real.log_mul two_ne_zero hq0.ne'
  linarith

private theorem sum_Ico_inv_min_le {q : ℕ} (hq : 2 ≤ q) :
    ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) ≤
      2 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by positivity
  let m := q / 2
  have hm_pos : 1 ≤ m := by omega
  have hsplit : Finset.Ico 1 q = Finset.Icc 1 m ∪ Finset.Ioc m (q - 1) := by
    ext s; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioc m (q - 1)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hs1 hs2
    omega
  have h1 : ∑ s ∈ Finset.Icc 1 m, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) =
      (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [Finset.mem_Icc] at hs
    have hmin : min s (q - s) = s := min_eq_left (by omega)
    rw [hmin, div_eq_mul_inv]
  have h2 : ∑ s ∈ Finset.Ioc m (q - 1), (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) ≤
      (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ := by
    have hbij :
        ∑ s ∈ Finset.Ioc m (q - 1), (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) =
          ∑ b ∈ Finset.Ico 1 (q - m), (q : ℝ) / (b : ℝ) := by
      refine Finset.sum_bij (fun s _ => q - s) ?_ ?_ ?_ ?_
      · intro s hs; simp only [Finset.mem_Ioc] at hs; simp only [Finset.mem_Ico]; omega
      · intro s₁ hs₁ s₂ hs₂ h; simp only [Finset.mem_Ioc] at hs₁ hs₂; omega
      · intro b hb
        simp only [Finset.mem_Ico] at hb
        refine ⟨q - b, ?_, by omega⟩
        simp only [Finset.mem_Ioc]; omega
      · intro s hs
        simp only [Finset.mem_Ioc] at hs
        have hmin : min s (q - s) = q - s := min_eq_right (by omega)
        rw [hmin]
    have hsub : Finset.Ico 1 (q - m) ⊆ Finset.Icc 1 m := by
      intro b hb; simp only [Finset.mem_Ico] at hb; simp only [Finset.mem_Icc]; omega
    rw [hbij]
    calc ∑ b ∈ Finset.Ico 1 (q - m), (q : ℝ) / (b : ℝ)
        ≤ ∑ b ∈ Finset.Icc 1 m, (q : ℝ) / (b : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => by positivity
      _ = (q : ℝ) * ∑ b ∈ Finset.Icc 1 m, (b : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [div_eq_mul_inv]
  have hharm := (sum_Icc_inv_le_one_add_log m hm_pos).trans (one_add_log_half_le_log_two_mul hq)
  rw [hsplit, Finset.sum_union hdisj]
  calc ∑ s ∈ Finset.Icc 1 m, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) +
        ∑ s ∈ Finset.Ioc m (q - 1), (q : ℝ) / ((min s (q - s) : ℕ) : ℝ)
      ≤ (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ +
          (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ := add_le_add h1.le h2
    _ = 2 * ((q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹) := by ring
    _ ≤ 2 * ((q : ℝ) * Real.log (2 * (q : ℝ))) := by gcongr
    _ = 2 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by ring

private lemma distToInt_intCast_div_natCast {z : ℤ} {q : ℕ} (hq : 0 < q) :
    distToInt ((z : ℝ) / (q : ℝ)) =
      ((min (Int.natMod z q) (q - Int.natMod z q) : ℕ) : ℝ) / (q : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmod : z = (z / (q : ℤ)) * (q : ℤ) + ((Int.natMod z q : ℕ) : ℤ) := by
    have hz : (Int.natMod z q : ℤ) = z % (q : ℤ) := by
      have h0 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg z (by exact_mod_cast hq.ne')
      rw [Int.natMod, Int.toNat_of_nonneg h0]
    rw [hz, Int.emod_def]
    ring
  have hsplit : (z : ℝ) / (q : ℝ) = ((Int.natMod z q : ℕ) : ℝ) / (q : ℝ) + ((z / (q : ℤ)) : ℤ) := by
    have hz : (z : ℝ) = ((z / (q : ℤ)) : ℤ) * (q : ℝ) + ((Int.natMod z q : ℕ) : ℝ) := by
      exact_mod_cast hmod
    rw [hz]
    field_simp [hq0]
    ring
  rw [hsplit, distToInt_add_int, distToInt_div_natCast]
  have hlt : Int.natMod z q < q := by
    dsimp only [Int.natMod]
    have h0 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg z (by exact_mod_cast hq.ne')
    have hq_lt : z % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos z (by exact_mod_cast hq)
    omega
  rw [Nat.mod_eq_of_lt hlt]

private lemma natMod_linear_bij {q : ℕ} (hq : 0 < q) {a u : ℤ}
    (hcop : Nat.Coprime a.natAbs q) :
    Function.Bijective (fun r : Fin q =>
      (⟨Int.natMod (a * (r : ℤ) + u) q, by
        dsimp only [Int.natMod]
        have h0 : 0 ≤ (a * (r : ℤ) + u) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
        have hlt : (a * (r : ℤ) + u) % (q : ℤ) < (q : ℤ) :=
          Int.emod_lt_of_pos _ (by exact_mod_cast hq)
        omega⟩ : Fin q)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun r₁ r₂ h => ?_, rfl⟩
  have heq : Int.natMod (a * (r₁ : ℤ) + u) q = Int.natMod (a * (r₂ : ℤ) + u) q :=
    congrArg Fin.val h
  have hmod : (a * (r₁ : ℤ) + u) % (q : ℤ) = (a * (r₂ : ℤ) + u) % (q : ℤ) := by
    dsimp only [Int.natMod] at heq
    have h1 : 0 ≤ (a * (r₁ : ℤ) + u) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    have h2 : 0 ≤ (a * (r₂ : ℤ) + u) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    omega
  have hdvd : (q : ℤ) ∣ a * ((r₁ : ℤ) - (r₂ : ℤ)) := by
    have hd1 : (q : ℤ) ∣ (a * (r₁ : ℤ) + u) - (a * (r₂ : ℤ) + u) :=
      Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod, sub_self, Int.zero_emod])
    simpa [mul_sub, sub_add_sub_cancel] using hd1
  have hdvdN : q ∣ a.natAbs * ((r₁ : ℤ) - (r₂ : ℤ)).natAbs := by
    have := Int.natCast_dvd.mp hdvd
    simpa [Int.natAbs_mul] using this
  have hdvd_diff : q ∣ ((r₁ : ℤ) - (r₂ : ℤ)).natAbs := hcop.symm.dvd_of_dvd_mul_left hdvdN
  have hdiff_lt : ((r₁ : ℤ) - (r₂ : ℤ)).natAbs < q := by
    have hr1 : (r₁ : ℕ) < q := r₁.2
    have hr2 : (r₂ : ℕ) < q := r₂.2
    omega
  have hz0 : ((r₁ : ℤ) - (r₂ : ℤ)).natAbs = 0 := by
    by_contra hne
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd_diff) (not_le.mpr hdiff_lt)
  exact Fin.ext (by omega)

/-- Divisor-type reciprocal distance bound for linear exponential sums:
when `|α - a/q| ≤ 1/q²` with `gcd(a, q) = 1`, `q ≥ 1`, and `Y ≥ 0`,
`∑_{1 ≤ n ≤ X} linearExpBound Y (α * n) ≤ 9 * ((X + q) * log(2q) + X * Y / q)`. -/
theorem sum_Icc_linearExpBound_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n) ≤
      9 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hlog_pos : 0 < Real.log (2 * (q : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hrhs_nonneg : 0 ≤ ((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q := by
    positivity
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp; positivity
  rcases eq_or_lt_of_le hq with rfl | hq2
  · calc ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n)
        ≤ ∑ _n ∈ Finset.Icc 1 X, Y :=
          Finset.sum_le_sum fun n _ => linearExpBound_le_left Y (α * n)
      _ = (X : ℝ) * Y := by simp
      _ ≤ 9 * (((X : ℝ) + (1 : ℕ)) * Real.log (2 * ((1 : ℕ) : ℝ)) + (X : ℝ) * Y / (1 : ℕ)) := by
          have h1 : (0 : ℝ) ≤ ((X : ℝ) + 1) * Real.log 2 := by positivity
          simp only [Nat.cast_one, mul_one, div_one]
          linarith
  have hq2' : 2 ≤ q := hq2
  let θ : ℝ := α - (a : ℝ) / q
  have hθ : |θ| ≤ 1 / (q : ℝ) ^ 2 := hα
  by_cases hsmall : 2 * X < q
  · have hbound_term : ∀ n ∈ Finset.Icc 1 X,
        linearExpBound Y (α * n) ≤
          (q : ℝ) / ((min (Int.natMod (a * (n : ℤ)) q) (q - Int.natMod (a * (n : ℤ)) q) : ℕ) : ℝ) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn_lt : n < q := by omega
      have hndiv : ¬ (q : ℤ) ∣ a * (n : ℤ) := by
        intro hdvd
        have hdvd' : q ∣ a.natAbs * n := by
          have h1 := Int.natCast_dvd.mp hdvd
          simpa [Int.natAbs_mul] using h1
        have hqn : q ∣ n := hcop.symm.dvd_of_dvd_mul_left hdvd'
        exact absurd (Nat.le_of_dvd hn.1 hqn) (not_le.mpr hn_lt)
      let s := Int.natMod (a * (n : ℤ)) q
      have hs_pos : 1 ≤ s := by
        by_contra hs0
        have h0 : Int.natMod (a * (n : ℤ)) q = 0 := by omega
        have heq0 : (a * (n : ℤ)) % (q : ℤ) = 0 := by
          dsimp only [Int.natMod] at h0
          have hnn : 0 ≤ (a * (n : ℤ)) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
          omega
        exact hndiv (Int.dvd_of_emod_eq_zero heq0)
      have hs_lt : s < q := by
        dsimp only [s, Int.natMod]
        have hnn : 0 ≤ (a * (n : ℤ)) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
        have hlt : (a * (n : ℤ)) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq0)
        omega
      let m := min s (q - s)
      have hm_pos : 1 ≤ m := le_min hs_pos (by omega)
      have hsplit_an : α * (n : ℝ) = ((a * (n : ℤ) : ℤ) : ℝ) / q + θ * n := by
        simp only [θ]; push_cast; ring
      have hdist_base : distToInt (((a * (n : ℤ) : ℤ) : ℝ) / q) = (m : ℝ) / q := by
        exact distToInt_intCast_div_natCast (z := a * (n : ℤ)) (by omega : 0 < q)
      have herr_bd : |θ * (n : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (a := (n : ℝ)) (Nat.cast_nonneg n)]
        have hn_half : (n : ℝ) ≤ (q : ℝ) / 2 := by
          have : (2 : ℝ) * n ≤ q := by exact_mod_cast (by omega : 2 * n ≤ q)
          linarith
        calc |θ| * (n : ℝ) ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) :=
              mul_le_mul hθ hn_half (Nat.cast_nonneg n) (by positivity)
          _ = 1 / (2 * (q : ℝ)) := by field_simp [hq0.ne']
      have hdist_lb : (m : ℝ) / (2 * (q : ℝ)) ≤ distToInt (α * n) := by
        rw [hsplit_an]
        have h1 := distToInt_sub_abs_le_add (((a * (n : ℤ) : ℤ) : ℝ) / q) (θ * n)
        rw [hdist_base] at h1
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
        calc (m : ℝ) / (2 * (q : ℝ))
            = (m : ℝ) / q - (m : ℝ) / (2 * q) := by ring
          _ ≤ (m : ℝ) / q - 1 / (2 * q) := by gcongr
          _ ≤ (m : ℝ) / q - |θ * n| := by gcongr
          _ ≤ distToInt (((a * (n : ℤ) : ℤ) : ℝ) / q + θ * n) := h1
      have hdist_pos : 0 < distToInt (α * n) :=
        lt_of_lt_of_le (by positivity) hdist_lb
      simp only [linearExpBound, hdist_pos.ne', ↓reduceIte]
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hm_pos)]
      have h2 : 1 * (m : ℝ) ≤ (q : ℝ) * (2 * distToInt (α * n)) := by
        have hm_mul : (m : ℝ) ≤ 2 * (q : ℝ) * distToInt (α * n) := by
          have := mul_le_mul_of_nonneg_left hdist_lb (by positivity : (0 : ℝ) ≤ 2 * q)
          rw [mul_div_cancel₀ _ (by positivity)] at this
          exact this
        linarith
      linarith
    have hinj : ∀ n₁ ∈ Finset.Icc 1 X, ∀ n₂ ∈ Finset.Icc 1 X,
        Int.natMod (a * (n₁ : ℤ)) q = Int.natMod (a * (n₂ : ℤ)) q → n₁ = n₂ := by
      intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Icc] at hn₁ hn₂
      have h1 : n₁ < q := by omega
      have h2 : n₂ < q := by omega
      have hbij := (natMod_linear_bij (by omega : 0 < q) (a := a) (u := 0) hcop).1
      have hfin : (⟨n₁, h1⟩ : Fin q) = ⟨n₂, h2⟩ := hbij (Fin.ext (by simpa using h))
      exact congrArg Fin.val hfin
    have hmap_sum :
        ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n) ≤
          ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
      calc ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n)
          ≤ ∑ n ∈ Finset.Icc 1 X,
              (q : ℝ) / ((min (Int.natMod (a * (n : ℤ)) q) (q - Int.natMod (a * (n : ℤ)) q) : ℕ) : ℝ) :=
            Finset.sum_le_sum hbound_term
        _ = ∑ s ∈ (Finset.Icc 1 X).image (fun n : ℕ => Int.natMod (a * (n : ℤ)) q),
              (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
            symm
            refine Finset.sum_image (fun n₁ hn₁ n₂ hn₂ h => hinj n₁ hn₁ n₂ hn₂ h)
        _ ≤ ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro s hs
            rcases Finset.mem_image.mp hs with ⟨n, hn, rfl⟩
            simp only [Finset.mem_Icc] at hn
            have hn_lt : n < q := by omega
            have hndiv : ¬ (q : ℤ) ∣ a * (n : ℤ) := by
              intro hdvd
              have hdvd' : q ∣ a.natAbs * n := by
                have h1 := Int.natCast_dvd.mp hdvd
                simpa [Int.natAbs_mul] using h1
              exact absurd (Nat.le_of_dvd hn.1 (hcop.symm.dvd_of_dvd_mul_left hdvd')) (not_le.mpr hn_lt)
            have hs_pos : 1 ≤ Int.natMod (a * (n : ℤ)) q := by
              by_contra h0
              have : (a * (n : ℤ)) % (q : ℤ) = 0 := by
                dsimp only [Int.natMod] at h0
                have hnn : 0 ≤ (a * (n : ℤ)) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
                omega
              exact hndiv (Int.dvd_of_emod_eq_zero this)
            have hs_lt : Int.natMod (a * (n : ℤ)) q < q := by
              dsimp only [Int.natMod]
              have hnn : 0 ≤ (a * (n : ℤ)) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
              have hlt : (a * (n : ℤ)) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq0)
              omega
            exact Finset.mem_Ico.mpr ⟨hs_pos, hs_lt⟩
    calc ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n)
        ≤ 2 * (q : ℝ) * Real.log (2 * (q : ℝ)) := hmap_sum.trans (sum_Ico_inv_min_le hq2')
      _ ≤ 9 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q) := by
          have h1 : (q : ℝ) ≤ (X : ℝ) + q := by linarith [Nat.cast_nonneg (α := ℝ) X]
          have h2 : 0 ≤ (X : ℝ) * Y / q := by positivity
          nlinarith
  · have hq_le_2X : (q : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast (not_lt.mp hsmall)
    let K : ℕ := X / q + 1
    have hsub : Finset.Icc 1 X ⊆ (Finset.range K ×ˢ Finset.range q).image (fun p => p.1 * q + p.2) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      refine Finset.mem_image.mpr ⟨(n / q, n % q), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · simp only [Finset.mem_range, K]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.2)
      · exact Finset.mem_range.mpr (Nat.mod_lt n (by omega))
      · dsimp only
        linarith [Nat.div_add_mod n q]
    have hsum_sub :
        ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n) ≤
          ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range q, linearExpBound Y (α * ((k * q + r : ℕ) : ℝ)) := by
      calc ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n)
          ≤ ∑ n ∈ (Finset.range K ×ˢ Finset.range q).image (fun p => p.1 * q + p.2),
              linearExpBound Y (α * n) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => linearExpBound_nonneg hY _
        _ ≤ ∑ p ∈ Finset.range K ×ˢ Finset.range q, linearExpBound Y (α * ((p.1 * q + p.2 : ℕ) : ℝ)) :=
            Finset.sum_image_le_of_nonneg fun _ _ => linearExpBound_nonneg hY _
        _ = ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range q,
              linearExpBound Y (α * ((k * q + r : ℕ) : ℝ)) := by rw [Finset.sum_product]
    have hblock : ∀ k : ℕ,
        ∑ r ∈ Finset.range q, linearExpBound Y (α * ((k * q + r : ℕ) : ℝ)) ≤
          3 * Y + 4 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
      intro k
      let u : ℤ := round ((q : ℝ) * (θ * (k : ℝ) * (q : ℝ)))
      let sFun : Fin q → ℕ := fun r => Int.natMod (a * (r : ℤ) + u) q
      have hs_lt : ∀ r : Fin q, sFun r < q := fun r => by
        dsimp only [sFun, Int.natMod]
        have hnn : 0 ≤ (a * (r : ℤ) + u) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
        have hlt : (a * (r : ℤ) + u) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq0)
        omega
      let sFin : Fin q → Fin q := fun r => ⟨sFun r, hs_lt r⟩
      have hsBij : Function.Bijective sFin := natMod_linear_bij (by omega : 0 < q) hcop
      have hterm_le : ∀ r : Fin q,
          linearExpBound Y (α * ((k * q + r : ℕ) : ℝ)) ≤
            if min (sFun r) (q - sFun r) ≤ 1 then Y
            else 2 * (q : ℝ) / ((min (sFun r) (q - sFun r) : ℕ) : ℝ) := by
        intro r
        split_ifs with hm1
        · exact linearExpBound_le_left Y _
        · have hm2 : 2 ≤ min (sFun r) (q - sFun r) := by omega
          let m := min (sFun r) (q - sFun r)
          let η : ℝ := θ * (k : ℝ) * (q : ℝ) - (u : ℝ) / (q : ℝ)
          let εr : ℝ := η + θ * (r : ℝ)
          have hsplit : α * ((k * q + r : ℕ) : ℝ) =
              (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ) + εr) + ((a * (k : ℤ) : ℤ) : ℝ) := by
            simp only [θ, εr, η]
            push_cast
            field_simp [hq0.ne']
            ring
          have hη_bd : |η| ≤ 1 / (2 * (q : ℝ)) := by
            have h1 : |η| = |(q : ℝ) * (θ * (k : ℝ) * (q : ℝ)) - u| / (q : ℝ) := by
              rw [show η = ((q : ℝ) * (θ * (k : ℝ) * (q : ℝ)) - u) / (q : ℝ) by
                dsimp only [η]; field_simp [hq0.ne'], abs_div, abs_of_pos hq0]
            rw [h1, div_le_div_iff₀ hq0 (by positivity)]
            have h2 := abs_sub_round ((q : ℝ) * (θ * (k : ℝ) * (q : ℝ)))
            change |(q : ℝ) * (θ * (k : ℝ) * (q : ℝ)) - u| ≤ 1 / 2 at h2
            nlinarith [hq0]
          have hθr_bd : |θ * (r : ℝ)| ≤ 1 / (q : ℝ) := by
            rw [abs_mul, abs_of_nonneg (a := ((r : ℕ) : ℝ)) (Nat.cast_nonneg (r : ℕ))]
            have hr_le : ((r : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast r.2.le
            calc |θ| * ((r : ℕ) : ℝ) ≤ (1 / (q : ℝ) ^ 2) * (q : ℝ) :=
                  mul_le_mul hθ hr_le (Nat.cast_nonneg _) (by positivity)
              _ = 1 / (q : ℝ) := by field_simp [hq0.ne']
          have hε_bd : |εr| ≤ 3 / (2 * (q : ℝ)) := by
            calc |εr| ≤ |η| + |θ * (r : ℝ)| := abs_add_le _ _
              _ ≤ 1 / (2 * (q : ℝ)) + 1 / (q : ℝ) := add_le_add hη_bd hθr_bd
              _ = 3 / (2 * (q : ℝ)) := by ring
          have hdist_base : distToInt (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ)) = (m : ℝ) / (q : ℝ) := by
            exact distToInt_intCast_div_natCast (z := a * (r : ℤ) + u) (by omega : 0 < q)
          have hdist_lb : (m : ℝ) / (4 * (q : ℝ)) ≤ distToInt (α * ((k * q + r : ℕ) : ℝ)) := by
            rw [hsplit, distToInt_add_int]
            have h1 := distToInt_sub_abs_le_add (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ)) εr
            rw [hdist_base] at h1
            have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
            calc (m : ℝ) / (4 * (q : ℝ))
                ≤ (m : ℝ) / (q : ℝ) - 3 / (2 * (q : ℝ)) := by
                  rw [le_sub_iff_add_le]
                  have hdiv : (m : ℝ) / (4 * q) + 3 / (2 * q) = ((m : ℝ) + 6) / (4 * q) := by
                    field_simp [hq0.ne']; ring
                  rw [hdiv, div_le_div_iff₀ (by positivity) hq0]
                  nlinarith [hq0, hm2R]
              _ ≤ (m : ℝ) / (q : ℝ) - |εr| := by gcongr
              _ ≤ distToInt (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ) + εr) := h1
          have hdist_pos : 0 < distToInt (α * ((k * q + r : ℕ) : ℝ)) :=
            lt_of_lt_of_le (by positivity) hdist_lb
          simp only [linearExpBound, hdist_pos.ne', ↓reduceIte]
          refine (min_le_right _ _).trans ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hmul : (m : ℝ) ≤ 4 * (q : ℝ) * distToInt (α * ((k * q + r : ℕ) : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hdist_lb (by positivity : (0 : ℝ) ≤ 4 * q)
            rw [mul_div_cancel₀ _ (by positivity)] at this
            exact this
          linarith
      calc ∑ r ∈ Finset.range q, linearExpBound Y (α * ((k * q + r : ℕ) : ℝ))
          = ∑ r : Fin q, linearExpBound Y (α * ((k * q + r : ℕ) : ℝ)) := (Fin.sum_univ_eq_sum_range _ q).symm
        _ ≤ ∑ r : Fin q,
              (if min (sFun r) (q - sFun r) ≤ 1 then Y
               else 2 * (q : ℝ) / ((min (sFun r) (q - sFun r) : ℕ) : ℝ)) :=
            Finset.sum_le_sum fun r _ => hterm_le r
        _ = ∑ s : Fin q,
              (if min (s : ℕ) (q - s) ≤ 1 then Y
               else 2 * (q : ℝ) / ((min (s : ℕ) (q - s) : ℕ) : ℝ)) :=
            Fintype.sum_bijective sFin hsBij _ _ fun _ => rfl
        _ = ∑ s ∈ Finset.range q,
              (if min s (q - s) ≤ 1 then Y
               else 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ)) :=
            Fin.sum_univ_eq_sum_range
              (fun s => if min s (q - s) ≤ 1 then Y else 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ)) q
        _ ≤ ∑ s ∈ Finset.range q, (if min s (q - s) ≤ 1 then Y else 0) +
              ∑ s ∈ Finset.Ico 1 q, 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
            have hsplit_ico : Finset.range q = insert 0 (Finset.Ico 1 q) := by
              ext s; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
            have h0_not : (0 : ℕ) ∉ Finset.Ico 1 q := by simp
            rw [hsplit_ico, Finset.sum_insert h0_not, Finset.sum_insert h0_not]
            have h0_val : (if min (0 : ℕ) (q - 0) ≤ 1 then Y else 2 * (q : ℝ) / ((min 0 (q - 0) : ℕ) : ℝ)) = Y := by
              simp
            have h0_val' : (if min (0 : ℕ) (q - 0) ≤ 1 then Y else 0) = Y := by simp
            rw [h0_val, h0_val', add_assoc]
            refine add_le_add le_rfl ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun s _ => ?_
            split_ifs
            · exact le_add_of_nonneg_right (by positivity)
            · rw [zero_add]
        _ ≤ 3 * Y + 4 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
            have hcount :
                ∑ s ∈ Finset.range q, (if min s (q - s) ≤ 1 then Y else 0) ≤ 3 * Y := by
              have hsub_bad :
                  (Finset.range q).filter (fun s => min s (q - s) ≤ 1) ⊆ ({0, 1, q - 1} : Finset ℕ) := by
                intro s hs
                simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
                  Finset.mem_singleton] at hs ⊢
                omega
              calc ∑ s ∈ Finset.range q, (if min s (q - s) ≤ 1 then Y else 0)
                  = ∑ _s ∈ (Finset.range q).filter (fun s => min s (q - s) ≤ 1), Y := by
                    rw [Finset.sum_filter]
                _ = (((Finset.range q).filter (fun s => min s (q - s) ≤ 1)).card : ℝ) * Y := by
                    simp
                _ ≤ (({0, 1, q - 1} : Finset ℕ).card : ℝ) * Y := by
                    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub_bad) hY
                _ ≤ 3 * Y := by
                    gcongr
                    norm_cast
                    exact Finset.card_le_three
            have hrec :
                ∑ s ∈ Finset.Ico 1 q, 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) ≤
                  4 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
              have hrewrite :
                  ∑ s ∈ Finset.Ico 1 q, 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) =
                    2 * ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun s _ => by ring
              rw [hrewrite]
              linarith [sum_Ico_inv_min_le hq2']
            exact add_le_add hcount hrec
    have hK_le : (K : ℝ) ≤ (X : ℝ) / q + 1 := by
      have hdiv : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := Nat.cast_div_le
      simp only [K, Nat.cast_add, Nat.cast_one]
      linarith
    have hK_le_three : (K : ℝ) ≤ 3 * ((X : ℝ) / q) := by
      have h1 : (1 : ℝ) ≤ 2 * ((X : ℝ) / q) := by
        rw [← mul_div_assoc, le_div_iff₀ hq0]
        linarith
      linarith
    calc ∑ n ∈ Finset.Icc 1 X, linearExpBound Y (α * n)
        ≤ ∑ _k ∈ Finset.range K, (3 * Y + 4 * (q : ℝ) * Real.log (2 * (q : ℝ))) :=
          hsum_sub.trans (Finset.sum_le_sum fun k _ => hblock k)
      _ = (K : ℝ) * (3 * Y) + (K : ℝ) * (4 * (q : ℝ) * Real.log (2 * (q : ℝ))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ (3 * ((X : ℝ) / q)) * (3 * Y) +
            ((X : ℝ) / q + 1) * (4 * (q : ℝ) * Real.log (2 * (q : ℝ))) := by
          gcongr
      _ = 9 * ((X : ℝ) * Y / q) + 4 * ((X : ℝ) + q) * Real.log (2 * (q : ℝ)) := by
          field_simp [hq0.ne']
          ring
      _ ≤ 9 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q) := by
          have : 0 ≤ ((X : ℝ) + q) * Real.log (2 * (q : ℝ)) := by positivity
          linarith

/-- Divisor-type bound on `∑_{1 ≤ n ≤ X} min Y (1 / (2 * distToInt (α * n)))`
when `|α - a/q| ≤ 1/q²`, `gcd(a, q) = 1`, `q ≥ 1`, and `Y ≥ 0`. -/
theorem sum_Icc_min_inv_two_distToInt_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 X, min Y (1 / (2 * distToInt (α * n))) ≤
      9 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q) := by
  refine (Finset.sum_le_sum fun n _ => ?_).trans (sum_Icc_linearExpBound_le hq hcop hα X hY)
  unfold linearExpBound
  split_ifs with h0
  · rw [h0]; simp [hY]
  · exact le_rfl

/-- Elementary divisor bound: for every `ε > 0`, there exists `C > 0` such that
`#n.divisors ≤ C * n ^ ε` for all `n ≥ 1`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let L : ℝ := 1 + 1 / (ε * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : 1 ≤ L := by
    have : 0 < 1 / (ε * Real.log 2) := by positivity
    linarith
  let K : ℕ := ⌊(2 : ℝ) ^ (1 / ε)⌋₊
  let C : ℝ := L ^ K
  refine ⟨C, pow_pos (lt_of_lt_of_le zero_lt_one hL) K, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    push_cast
    rfl
  have hn_prod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    have h1 := Nat.prod_factorization_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at h1
    conv_lhs => rw [← h1]
    simp [Nat.cast_prod]
  have hrpow : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ ε := by
    rw [hn_prod]
    induction n.primeFactors using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Finset.prod_insert hps, Real.mul_rpow (by positivity)
        (Finset.prod_nonneg fun _ _ => by positivity), ih]
  have hfactor : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) / ((p : ℝ) ^ (n.factorization p)) ^ ε ≤
        if p ≤ K then L else 1 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
    let a := n.factorization p
    have hpow_ge : (2 : ℝ) ^ ((a : ℝ) * ε) ≤ ((p : ℝ) ^ a) ^ ε := by
      rw [← Real.rpow_natCast (p : ℝ) a, ← Real.rpow_mul (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hp2 (by positivity)
    split_ifs with hpK
    · have h2exp : (a : ℝ) * ε * Real.log 2 ≤ (2 : ℝ) ^ ((a : ℝ) * ε) := by
        have hlin := Real.add_one_le_exp ((a : ℝ) * ε * Real.log 2)
        have hdef : (2 : ℝ) ^ ((a : ℝ) * ε) = Real.exp (((a : ℝ) * ε) * Real.log 2) := by
          rw [Real.rpow_def_of_pos two_pos]
          ring_nf
        rw [hdef]
        linarith
      have h1_le : 1 ≤ (2 : ℝ) ^ ((a : ℝ) * ε) :=
        Real.one_le_rpow one_le_two (by positivity)
      have hnum : (a : ℝ) + 1 ≤ L * (2 : ℝ) ^ ((a : ℝ) * ε) := by
        have ha_le : (a : ℝ) ≤ (1 / (ε * Real.log 2)) * (2 : ℝ) ^ ((a : ℝ) * ε) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hε hlog2)]
          linarith
        dsimp only [L]
        nlinarith [h1_le, ha_le]
      rw [div_le_iff₀ (by positivity)]
      calc (a : ℝ) + 1 ≤ L * (2 : ℝ) ^ ((a : ℝ) * ε) := hnum
        _ ≤ L * ((p : ℝ) ^ a) ^ ε := mul_le_mul_of_nonneg_left hpow_ge (by positivity)
    · have hp_gt : (2 : ℝ) ^ (1 / ε) < (p : ℝ) := by
        by_contra hle
        exact hpK (Nat.le_floor (not_lt.mp hle))
      have hp_rpow : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul two_pos.le, one_div_mul_cancel hε.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hp_gt.le hε.le
      have hp_pow : (2 : ℝ) ^ a ≤ ((p : ℝ) ^ a) ^ ε := by
        rw [← Real.rpow_natCast (p : ℝ) a, ← Real.rpow_mul (by positivity),
          mul_comm (a : ℝ) ε, Real.rpow_mul (by positivity), Real.rpow_natCast]
        exact pow_le_pow_left₀ zero_le_two hp_rpow a
      have ha2 : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := by
        exact_mod_cast (by
          clear * - a
          induction a with
          | zero => simp
          | succ m ih =>
            rcases eq_or_ne m 0 with rfl | hm
            · simp
            · have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
              have : m + 1 + 1 ≤ 2 ^ m + 2 ^ m := by omega
              simpa [pow_succ, mul_two] using this : a + 1 ≤ 2 ^ a)
      rw [div_le_one (by positivity)]
      exact ha2.trans hp_pow
  have hprod_div :
      (n.divisors.card : ℝ) / (n : ℝ) ^ ε ≤
        ∏ p ∈ n.primeFactors, (if p ≤ K then L else 1) := by
    rw [hcard, hrpow, ← Finset.prod_div_distrib]
    exact Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => hfactor p hp)
  have hprod_bound :
      ∏ p ∈ n.primeFactors, (if p ≤ K then L else 1) ≤ C := by
    have hsplit :
        ∏ p ∈ n.primeFactors, (if p ≤ K then L else 1) =
          ∏ _p ∈ n.primeFactors.filter (· ≤ K), L := by
      rw [Finset.prod_filter]
    rw [hsplit, Finset.prod_const]
    have hcard_le : (n.primeFactors.filter (· ≤ K)).card ≤ K := by
      have hsub : n.primeFactors.filter (· ≤ K) ⊆ Finset.Icc 1 K := by
        intro p hp
        simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.1.pos, hp.2⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    exact pow_le_pow_right₀ hL hcard_le
  rw [div_le_iff₀ (by positivity)] at hprod_div
  exact hprod_div.trans (mul_le_mul_of_nonneg_right hprod_bound (by positivity))

/-- Upper bound on the number of `m`-tuples `(h₁, ..., h_m)` of positive integers `1 ≤ h_i`
whose product equals `r` (`1 ≤ m`, `1 ≤ r`): bounded by `(r.divisors.card) ^ (m - 1)`. -/
theorem card_pos_tuples_prod_eq_le :
    ∀ (m : ℕ) (r : ℕ), 1 ≤ m → 1 ≤ r →
      ((Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 r)).filter
        (fun h => ∏ i, h i = r)).card ≤ r.divisors.card ^ (m - 1)
  | 0, _, hm, _ => by omega
  | 1, r, _, hr => by
    simp only [Nat.sub_self, pow_zero]
    refine Finset.card_le_one.mpr fun h₁ hh₁ h₂ hh₂ => ?_
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, Fin.prod_univ_one] at hh₁ hh₂
    ext i
    rw [Fin.eq_zero i]
    exact hh₁.2.trans hh₂.2.symm
  | m + 2, r, _, hr => by
    have ih := card_pos_tuples_prod_eq_le (m + 1)
    let S := (Fintype.piFinset (fun _ : Fin (m + 2) => Finset.Icc 1 r)).filter
      (fun h => ∏ i, h i = r)
    let proj : (Fin (m + 2) → ℕ) → (_ : ℕ) × (Fin (m + 1) → ℕ) :=
      fun h => ⟨h 0, fun i => h i.succ⟩
    have hinj : ∀ h₁ ∈ S, ∀ h₂ ∈ S, proj h₁ = proj h₂ → h₁ = h₂ := by
      intro h₁ _ h₂ _ heq
      ext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact congrArg Sigma.fst heq
      · exact congrFun (congrArg Sigma.snd heq) j
    have hcard_eq : S.card = (S.image proj).card := (Finset.card_image_of_injOn hinj).symm
    let T := r.divisors.sigma fun d =>
      (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 (r / d))).filter
        (fun h => ∏ i, h i = r / d)
    have himg : S.image proj ⊆ T := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨h, hh, rfl⟩
      simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hh
      have hprod_split : ∏ i : Fin (m + 2), h i = h 0 * ∏ i : Fin (m + 1), h i.succ :=
        Fin.prod_univ_succ h
      have hprod_eq : h 0 * ∏ i : Fin (m + 1), h i.succ = r := hprod_split.symm.trans hh.2
      have hdvd : h 0 ∣ r := ⟨∏ i : Fin (m + 1), h i.succ, hprod_eq.symm⟩
      have hd_mem : h 0 ∈ r.divisors := Nat.mem_divisors.mpr ⟨hdvd, by omega⟩
      have hd_pos : 0 < h 0 := (hh.1 0).1
      have hprod_tail : ∏ i : Fin (m + 1), h i.succ = r / h 0 := by
        rw [← hprod_eq, mul_comm, Nat.mul_div_cancel _ hd_pos]
      refine Finset.mem_sigma.mpr ⟨hd_mem, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i : Fin (m + 1) =>
        Finset.mem_Icc.mpr ⟨(hh.1 i.succ).1, ?_⟩, hprod_tail⟩⟩
      calc h i.succ ≤ ∏ j : Fin (m + 1), h j.succ :=
            Finset.single_le_prod (fun j _ => (hh.1 j.succ).1) (Finset.mem_univ i)
        _ = r / h 0 := hprod_tail
    have hT_card : T.card ≤ r.divisors.card ^ (m + 1) := by
      rw [Finset.card_sigma]
      calc ∑ d ∈ r.divisors,
            ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 (r / d))).filter
              (fun h => ∏ i, h i = r / d)).card
          ≤ ∑ d ∈ r.divisors, (r / d).divisors.card ^ m := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd_dvd : d ∣ r := Nat.dvd_of_mem_divisors hd
            have hrd_pos : 1 ≤ r / d := Nat.div_pos (Nat.le_of_dvd hr hd_dvd)
              (Nat.pos_of_dvd_of_pos hd_dvd hr)
            simpa using ih (r / d) (by omega) hrd_pos
        _ ≤ ∑ _d ∈ r.divisors, r.divisors.card ^ m := by
            refine Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left ?_ m
            refine Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega)
              (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
        _ = r.divisors.card * r.divisors.card ^ m := by simp
        _ = r.divisors.card ^ (m + 1) := by ring
    rw [show m + 2 - 1 = m + 1 by rfl, hcard_eq]
    exact (Finset.card_le_card himg).trans hT_card

/-- Upper bound on the number of `m`-tuples `(h₁, ..., h_m)` of integers with `|h_i| ≤ N`
and `∏ |h_i| = r` (`1 ≤ m`, `1 ≤ r`): bounded by `2^m * (r.divisors.card) ^ (m - 1)`. -/
theorem card_int_tuples_prod_natAbs_eq_le (m N r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    ((Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(N : ℤ)) N)).filter
      (fun h => ∏ i, (h i).natAbs = r)).card ≤ 2 ^ m * r.divisors.card ^ (m - 1) := by
  let S := (Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(N : ℤ)) N)).filter
    (fun h => ∏ i, (h i).natAbs = r)
  let f : (Fin m → ℤ) → (Fin m → Bool) × (Fin m → ℕ) :=
    fun h => (fun i => decide (0 ≤ h i), fun i => (h i).natAbs)
  have hinj : ∀ h₁ ∈ S, ∀ h₂ ∈ S, f h₁ = f h₂ → h₁ = h₂ := by
    intro h₁ _ h₂ _ heq
    ext i
    have hb : decide (0 ≤ h₁ i) = decide (0 ≤ h₂ i) := congrFun (congrArg Prod.fst heq) i
    have ha : (h₁ i).natAbs = (h₂ i).natAbs := congrFun (congrArg Prod.snd heq) i
    by_cases h1 : 0 ≤ h₁ i
    · have h2 : 0 ≤ h₂ i := by simpa [h1] using hb
      omega
    · have h2 : ¬ 0 ≤ h₂ i := by simpa [h1] using hb
      omega
  have hcard_eq : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  let B := Fintype.piFinset (fun _ : Fin m => ({false, true} : Finset Bool))
  let P := (Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 r)).filter (fun h => ∏ i, h i = r)
  have himg : S.image f ⊆ B ×ˢ P := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨h, hh, rfl⟩
    simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hh
    have hj_pos : ∀ j : Fin m, 1 ≤ (h j).natAbs := fun j => by
      have hne : (h j).natAbs ≠ 0 := fun hz => by
        have h0 : ∏ k, (h k).natAbs = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hz
        linarith [hh.2, hr]
      exact Nat.pos_of_ne_zero hne
    refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => by simp, ?_⟩
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨hj_pos i, ?_⟩, hh.2⟩
    calc (h i).natAbs ≤ ∏ j, (h j).natAbs :=
          Finset.single_le_prod (fun j _ => hj_pos j) (Finset.mem_univ i)
      _ = r := hh.2
  have hB_card : B.card ≤ 2 ^ m := by
    dsimp only [B]
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left (by simp) m
  have hP_card : P.card ≤ r.divisors.card ^ (m - 1) := card_pos_tuples_prod_eq_le m r hm hr
  calc S.card = (S.image f).card := hcard_eq
    _ ≤ (B ×ˢ P).card := Finset.card_le_card himg
    _ = B.card * P.card := Finset.card_product _ _
    _ ≤ 2 ^ m * r.divisors.card ^ (m - 1) := Nat.mul_le_mul hB_card hP_card

end DivisorBounds

section WeylDifferencing

/-- Forward difference operator `forwardDiff h f x = f (x + h) - f x`. -/
def forwardDiff (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (x + h) - f x

/-- Iterated forward difference operator over a tuple `h : Fin k → ℝ`. -/
def iterForwardDiff : ∀ {k : ℕ}, (Fin k → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, _, f => f
  | _ + 1, h, f => forwardDiff (h 0) (iterForwardDiff (fun i => h i.succ) f)

/-- Polynomial forward difference operator `polyDiff h P = P(X + h) - P(X)`. -/
def polyDiff (h : ℝ) (P : ℝ[X]) : ℝ[X] :=
  P.comp (Polynomial.X + Polynomial.C h) - P

/-- Iterated polynomial difference operator over `h : Fin k → ℝ`. -/
def iterPolyDiff : ∀ {k : ℕ}, (Fin k → ℝ) → ℝ[X] → ℝ[X]
  | 0, _, P => P
  | _ + 1, h, P => polyDiff (h 0) (iterPolyDiff (fun i => h i.succ) P)

/-- Evaluation compatibility: `(polyDiff h P).eval x = forwardDiff h (fun t => P.eval t) x`. -/
@[simp]
theorem eval_polyDiff (h : ℝ) (P : ℝ[X]) (x : ℝ) :
    (polyDiff h P).eval x = forwardDiff h (fun t => P.eval t) x := by
  simp [polyDiff, forwardDiff, Polynomial.eval_comp]

/-- Evaluation compatibility for iterated differences. -/
@[simp]
theorem eval_iterPolyDiff : ∀ {k : ℕ} (h : Fin k → ℝ) (P : ℝ[X]) (x : ℝ),
    (iterPolyDiff h P).eval x = iterForwardDiff h (fun t => P.eval t) x
  | 0, _, P, x => rfl
  | k + 1, h, P, x => by
    simp only [iterPolyDiff, iterForwardDiff, eval_polyDiff, forwardDiff]
    rw [eval_iterPolyDiff (fun i => h i.succ) P (x + h 0),
      eval_iterPolyDiff (fun i => h i.succ) P x]

private lemma polyDiff_X_pow (h : ℝ) (n : ℕ) :
    (polyDiff h (Polynomial.X ^ n)).natDegree ≤ n - 1 ∧
      (1 ≤ n → (polyDiff h (Polynomial.X ^ n)).coeff (n - 1) = (n : ℝ) * h) := by
  have hcomp : (Polynomial.X ^ n : ℝ[X]).comp (Polynomial.X + Polynomial.C h) =
      (Polynomial.X + Polynomial.C h) ^ n := by simp
  rw [polyDiff, hcomp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · constructor
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases eq_or_ne m n with rfl | hne
      · simp [Polynomial.coeff_X_add_C_pow]
      · simp only [hne, ↓reduceIte, sub_zero, Polynomial.coeff_X_add_C_pow]
        rw [Nat.choose_eq_zero_of_lt (by omega : n < m)]
        simp
    · intro _
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      simp only [show n - 1 ≠ n by omega, ↓reduceIte, sub_zero, Polynomial.coeff_X_add_C_pow]
      have hch : n.choose (n - 1) = n := by
        rw [← Nat.choose_symm (by omega : n - 1 ≤ n), show n - (n - 1) = 1 by omega,
          Nat.choose_one_right]
      have hpow : h ^ (n - (n - 1)) = h := by rw [show n - (n - 1) = 1 by omega, pow_one]
      rw [hch, hpow]
      ring

/-- Degree bound and leading coefficient drop for `polyDiff h P`. -/
theorem polyDiff_natDegree_and_coeff (h : ℝ) (P : ℝ[X]) {m : ℕ} (hm : P.natDegree ≤ m + 1) :
    (polyDiff h P).natDegree ≤ m ∧
      (polyDiff h P).coeff m = ((m + 1 : ℕ) : ℝ) * h * P.coeff (m + 1) := by
  have hlin : ∀ (c : ℝ) (A B : ℝ[X]),
      polyDiff h (Polynomial.C c * A + B) =
        Polynomial.C c * polyDiff h A + polyDiff h B := by
    intro c A B
    simp only [polyDiff, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp]
    ring
  let c := P.coeff (m + 1)
  let Q := P - Polynomial.C c * Polynomial.X ^ (m + 1)
  have hQ_deg : Q.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne j (m + 1) with rfl | hne
    · simp [c]
    · simp only [hne, ↓reduceIte, mul_zero, sub_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hP_eq : P = Polynomial.C c * Polynomial.X ^ (m + 1) + Q := by
    dsimp only [Q]; ring
  have hdiff_Q : (polyDiff h Q).natDegree ≤ m - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rcases eq_or_ne m 0 with rfl | hm0
    · have hQ0 : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hQ_deg
      rw [hQ0]
      simp [polyDiff]
    · have hj1 : m - 1 < j := by omega
      have hQsum : Q = ∑ i ∈ Finset.range (m + 1), Polynomial.C (Q.coeff i) * Polynomial.X ^ i := by
        have h0 := Polynomial.as_sum_range' Q (m + 1) (by omega)
        simp only [← Polynomial.C_mul_X_pow_eq_monomial] at h0
        exact h0
      have hQdiff : polyDiff h Q =
          ∑ i ∈ Finset.range (m + 1), Polynomial.C (Q.coeff i) * polyDiff h (Polynomial.X ^ i) := by
        conv_lhs => rw [hQsum]
        simp only [polyDiff, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hQdiff, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi_deg := (polyDiff_X_pow h i).1
      rw [Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := polyDiff h (Polynomial.X ^ i)) (by omega),
        mul_zero]
  have hpow := polyDiff_X_pow h (m + 1)
  have hpow_deg : (polyDiff h (Polynomial.X ^ (m + 1))).natDegree ≤ m := by
    simpa using hpow.1
  have hpow_coeff : (polyDiff h (Polynomial.X ^ (m + 1))).coeff m = ((m + 1 : ℕ) : ℝ) * h := by
    simpa using hpow.2 (Nat.succ_pos m)
  rw [hP_eq, hlin]
  constructor
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (hdiff_Q.trans (Nat.sub_le m 1)))
    exact (Polynomial.natDegree_C_mul_le c _).trans hpow_deg
  · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, hpow_coeff]
    have hQc : (polyDiff h Q).coeff m = 0 := by
      rcases eq_or_ne m 0 with rfl | hm0
      · have hQ0 : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hQ_deg
        rw [hQ0]
        simp [polyDiff]
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hQc, add_zero]
    have hPcoeff : (Polynomial.C c * Polynomial.X ^ (m + 1) + Q).coeff (m + 1) = c := by
      rw [← hP_eq]
    rw [hPcoeff]
    ring

/-- Degree bound and leading coefficient formula for `iterPolyDiff` of order `k`. -/
theorem iterPolyDiff_natDegree_and_coeff :
    ∀ {k : ℕ} (h : Fin k → ℝ) (P : ℝ[X]) (m : ℕ), P.natDegree ≤ m + k →
      (iterPolyDiff h P).natDegree ≤ m ∧
        (iterPolyDiff h P).coeff m =
          ((m + k).descFactorial k : ℝ) * (∏ i, h i) * P.coeff (m + k)
  | 0, _, P, m, hdeg => by simpa [iterPolyDiff] using hdeg
  | k + 1, h, P, m, hdeg => by
    have ih := iterPolyDiff_natDegree_and_coeff (fun i => h i.succ) P (m + 1) (by omega)
    have hstep := polyDiff_natDegree_and_coeff (h 0) (iterPolyDiff (fun i => h i.succ) P) ih.1
    refine ⟨hstep.1, ?_⟩
    have ih2 := ih.2
    have hP_idx : m + 1 + k = m + (k + 1) := by omega
    rw [iterPolyDiff, hstep.2, ih2, Fin.prod_univ_succ]
    have hdesc : (m + 1 + k).descFactorial k * (m + 1) = (m + (k + 1)).descFactorial (k + 1) := by
      rw [show m + (k + 1) = m + 1 + k by ring, Nat.descFactorial_succ]
      have hsub : m + 1 + k - k = m + 1 := by omega
      rw [hsub, mul_comm]
    have hdescR : ((m + 1 + k).descFactorial k : ℝ) * ((m + 1 : ℕ) : ℝ) =
        ((m + (k + 1)).descFactorial (k + 1) : ℝ) := by exact_mod_cast hdesc
    calc ((m + 1 : ℕ) : ℝ) * h 0 *
          (((m + 1 + k).descFactorial k : ℝ) * (∏ i : Fin k, h i.succ) * P.coeff (m + 1 + k))
        = (((m + 1 + k).descFactorial k : ℝ) * ((m + 1 : ℕ) : ℝ)) *
            (h 0 * ∏ i : Fin k, h i.succ) * P.coeff (m + 1 + k) := by ring
      _ = ((m + (k + 1)).descFactorial (k + 1) : ℝ) * (h 0 * ∏ i : Fin k, h i.succ) *
            P.coeff (m + (k + 1)) := by rw [hdescR, hP_idx]

/-- Integer interval maintained during Weyl differencing. -/
def weylInterval (A B : ℤ) : ∀ {k : ℕ}, (Fin k → ℤ) → Finset ℤ
  | 0, _ => Finset.Ioc A B
  | _ + 1, h =>
    (weylInterval A B (fun i => h i.succ)).filter (fun n => n + h 0 ∈ weylInterval A B (fun i => h i.succ))

private lemma weylInterval_eq_Ioc :
    ∀ {k : ℕ} (A B : ℤ) (h : Fin k → ℤ),
      ∃ A' B' : ℤ, weylInterval A B h = Finset.Ioc A' B' ∧ B' - A' ≤ max 0 (B - A)
  | 0, A, B, _ => ⟨A, B, rfl, le_max_right _ _⟩
  | k + 1, A, B, h => by
    rcases weylInterval_eq_Ioc A B (fun i => h i.succ) with ⟨A', B', hEq, hlen⟩
    refine ⟨max A' (A' - h 0), min B' (B' - h 0), ?_, ?_⟩
    · rw [weylInterval, hEq]
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc, max_lt_iff, le_min_iff]
      omega
    · have hle : min B' (B' - h 0) - max A' (A' - h 0) ≤ B' - A' := by omega
      exact hle.trans hlen

private lemma add_one_le_two_pow : ∀ {n : ℕ}, 1 ≤ n → n + 1 ≤ 2 ^ n
  | 0, h => by omega
  | 1, _ => by simp
  | n + 2, _ => by
    have ih := add_one_le_two_pow (n := n + 1) (by omega)
    calc n + 2 + 1 ≤ n + 2 + (n + 2) := by omega
      _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := add_le_add ih ih
      _ = 2 ^ (n + 2) := by ring

private lemma weyl_step_one (f : ℝ → ℝ) {A B : ℤ} {N : ℕ} (hAB : B - A ≤ (N : ℤ)) :
    ‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ 2 ≤
      ∑ h ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
        ‖∑ n ∈ (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B),
          e (forwardDiff (h : ℝ) f (n : ℝ))‖ := by
  have hnormSq :
      ‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ 2 =
        (∑ n₁ ∈ Finset.Ioc A B, ∑ n₂ ∈ Finset.Ioc A B,
          e (f (n₁ : ℝ) - f (n₂ : ℝ))).re := by
    have hns : ((‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ 2 : ℝ) : ℂ) =
        starRingEnd ℂ (∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))) *
          ∑ n ∈ Finset.Ioc A B, e (f (n : ℝ)) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    have hre1 : ‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ 2 =
        (starRingEnd ℂ (∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))) *
          ∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))).re := by
      rw [← hns, Complex.ofReal_re]
    rw [hre1, map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, ← Complex.star_def, star_e]
    have hconj : ∑ n₁ ∈ Finset.Ioc A B, ∑ n₂ ∈ Finset.Ioc A B,
        e (-f (n₁ : ℝ)) * e (f (n₂ : ℝ)) =
        starRingEnd ℂ (∑ n₁ ∈ Finset.Ioc A B, ∑ n₂ ∈ Finset.Ioc A B,
          e (f (n₁ : ℝ) - f (n₂ : ℝ))) := by
      simp only [map_sum, ← Complex.star_def, star_e]
      refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
      rw [← e_add]
      congr 1
      ring
    rw [hconj, Complex.conj_re]
  have hgroup :
      ∑ n₁ ∈ Finset.Ioc A B, ∑ n₂ ∈ Finset.Ioc A B, e (f (n₁ : ℝ) - f (n₂ : ℝ)) =
        ∑ h ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          ∑ n ∈ (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B),
            e (forwardDiff (h : ℝ) f (n : ℝ)) := by
    rw [← Finset.sum_product']
    symm
    rw [Finset.sum_sigma' (s := Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1))
      (t := fun h => (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B))
      (f := fun h n => e (forwardDiff (h : ℝ) f (n : ℝ)))]
    symm
    refine Finset.sum_bij (fun p _ => ⟨p.1 - p.2, p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_Ioc] at hp
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hp.2, Finset.mem_Ioc.mpr (by dsimp only; omega)⟩⟩
    · intro p₁ _ p₂ _ heq
      have h1 : p₁.1 - p₁.2 = p₂.1 - p₂.2 := congrArg Sigma.fst heq
      have h2 : p₁.2 = p₂.2 := congrArg Sigma.snd heq
      exact Prod.ext (by omega) h2
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc] at hq
      refine ⟨(q.2 + q.1, q.2), Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr hq.2.2,
        Finset.mem_Ioc.mpr hq.2.1⟩, ?_⟩
      ext <;> simp
    · intro p _
      simp only [forwardDiff]
      congr 2
      have hcast : ((p.1 - p.2 : ℤ) : ℝ) = (p.1 : ℝ) - (p.2 : ℝ) := by push_cast; ring
      rw [hcast]
      ring_nf
  rw [hnormSq, hgroup]
  calc (∑ h ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          ∑ n ∈ (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B),
            e (forwardDiff (h : ℝ) f (n : ℝ))).re
      ≤ ‖∑ h ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          ∑ n ∈ (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B),
            e (forwardDiff (h : ℝ) f (n : ℝ))‖ := Complex.re_le_norm _
    _ ≤ ∑ h ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          ‖∑ n ∈ (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B),
            e (forwardDiff (h : ℝ) f (n : ℝ))‖ := norm_sum_le _ _

private lemma weyl_squaring_inner :
    ∀ (k : ℕ) (f : ℝ → ℝ) (A B : ℤ) (N : ℕ), 1 ≤ N → B - A ≤ (N : ℤ) →
      ‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ (2 ^ k) ≤
        (2 * (N : ℝ)) ^ (2 ^ k - k - 1) *
          ∑ h ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)),
            ‖∑ n ∈ weylInterval A B h, e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖
  | 0, f, A, B, N, _, _ => by
    simp [weylInterval, iterForwardDiff]
  | k + 1, f, A, B, N, hN, hAB => by
    rcases eq_or_lt_of_le (Nat.zero_le k) with h0 | hk
    · have hk0 : k = 0 := h0.symm
      subst hk0
      simp only [Nat.zero_add, pow_one, Nat.sub_self, pow_zero, one_mul]
      have h1 := weyl_step_one f hAB
      have hbij :
          ∑ h ∈ Fintype.piFinset (fun _ : Fin 1 => Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)),
            ‖∑ n ∈ weylInterval A B h,
              e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ =
          ∑ h ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
            ‖∑ n ∈ (Finset.Ioc A B).filter (fun n => n + h ∈ Finset.Ioc A B),
              e (forwardDiff (h : ℝ) f (n : ℝ))‖ := by
        refine Finset.sum_bij (fun h _ => h 0) ?_ ?_ ?_ ?_
        · intro h hh; exact (Fintype.mem_piFinset.mp hh) 0
        · intro h₁ _ h₂ _ heq; ext i; rw [Fin.eq_zero i]; exact heq
        · intro h hh
          refine ⟨fun _ => h, Fintype.mem_piFinset.mpr fun _ => hh, rfl⟩
        · intro h _
          simp [weylInterval, iterForwardDiff]
      rw [hbij]
      exact h1
    · have ih := weyl_squaring_inner k f A B N hN hAB
      let H := Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1))
      have hsq :
          (‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ (2 ^ k)) ^ 2 ≤
            ((2 * (N : ℝ)) ^ (2 ^ k - k - 1)) ^ 2 *
              (∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
                e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖) ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) ih 2
      have hcs :
          (∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
              e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖) ^ 2 ≤
            (H.card : ℝ) * ∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
              e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := H)
          (f := fun h => ‖∑ n ∈ weylInterval A B h,
            e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖)
      have hH_card : (H.card : ℝ) ≤ (2 * (N : ℝ)) ^ k := by
        dsimp only [H]
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        have hIcc : (Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)).card ≤ 2 * N := by
          rw [Int.card_Icc]
          omega
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hIcc) k
      have hstep_inner : ∀ h ∈ H,
          ‖∑ n ∈ weylInterval A B h,
              e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ ^ 2 ≤
            ∑ h₀ ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
              ‖∑ n ∈ (weylInterval A B h).filter (fun n => n + h₀ ∈ weylInterval A B h),
                e (forwardDiff (h₀ : ℝ) (iterForwardDiff (fun i => (h i : ℝ)) f) (n : ℝ))‖ := by
        intro h _
        rcases weylInterval_eq_Ioc A B h with ⟨A', B', hEq, hlen⟩
        rw [hEq]
        have hlen' : B' - A' ≤ (N : ℤ) := hlen.trans (max_le (by omega) hAB)
        exact weyl_step_one (iterForwardDiff (fun i => (h i : ℝ)) f) hlen'
      have hprod_sum :
          ∑ h ∈ H, ∑ h₀ ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
            ‖∑ n ∈ (weylInterval A B h).filter (fun n => n + h₀ ∈ weylInterval A B h),
              e (forwardDiff (h₀ : ℝ) (iterForwardDiff (fun i => (h i : ℝ)) f) (n : ℝ))‖ =
          ∑ h' ∈ Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)),
            ‖∑ n ∈ weylInterval A B h', e (iterForwardDiff (fun i => (h' i : ℝ)) f (n : ℝ))‖ := by
        rw [← Finset.sum_product']
        refine Finset.sum_bij (fun p _ => Fin.cons p.2 p.1) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_product, H, Fintype.mem_piFinset] at hp ⊢
          intro i
          refine Fin.cases hp.2 (fun j => hp.1 j) i
        · intro p₁ _ p₂ _ heq
          ext1
          · ext j
            have := congrFun heq j.succ
            simpa using this
          · have := congrFun heq 0
            simpa using this
        · intro h' hh'
          refine ⟨(fun j => h' j.succ, h' 0), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · exact Fintype.mem_piFinset.mpr fun j => (Fintype.mem_piFinset.mp hh') j.succ
          · exact (Fintype.mem_piFinset.mp hh') 0
          · ext i; refine Fin.cases rfl (fun j => rfl) i
        · intro p _
          simp [weylInterval, iterForwardDiff]
      have hexp_eq : (2 ^ k - k - 1) * 2 + k = 2 ^ (k + 1) - (k + 1) - 1 := by
        have hk1 : k + 1 ≤ 2 ^ k := add_one_le_two_pow hk
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [hpow]
        omega
      have hpow_combine :
          ((2 * (N : ℝ)) ^ (2 ^ k - k - 1)) ^ 2 * (2 * (N : ℝ)) ^ k =
            (2 * (N : ℝ)) ^ (2 ^ (k + 1) - (k + 1) - 1) := by
        rw [← pow_mul, ← pow_add, hexp_eq]
      calc ‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ (2 ^ (k + 1))
          = (‖∑ n ∈ Finset.Ioc A B, e (f (n : ℝ))‖ ^ (2 ^ k)) ^ 2 := by
            rw [← pow_mul, show 2 ^ k * 2 = 2 ^ (k + 1) by ring]
        _ ≤ ((2 * (N : ℝ)) ^ (2 ^ k - k - 1)) ^ 2 *
              (∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
                e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖) ^ 2 := hsq
        _ ≤ ((2 * (N : ℝ)) ^ (2 ^ k - k - 1)) ^ 2 *
              ((H.card : ℝ) * ∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
                e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ ^ 2) := by
            gcongr
        _ ≤ ((2 * (N : ℝ)) ^ (2 ^ k - k - 1)) ^ 2 *
              ((2 * (N : ℝ)) ^ k * ∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
                e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ ^ 2) := by
            gcongr
        _ = (2 * (N : ℝ)) ^ (2 ^ (k + 1) - (k + 1) - 1) *
              ∑ h ∈ H, ‖∑ n ∈ weylInterval A B h,
                e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ ^ 2 := by
            rw [← mul_assoc, hpow_combine]
        _ ≤ (2 * (N : ℝ)) ^ (2 ^ (k + 1) - (k + 1) - 1) *
              ∑ h ∈ H, ∑ h₀ ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
                ‖∑ n ∈ (weylInterval A B h).filter (fun n => n + h₀ ∈ weylInterval A B h),
                  e (forwardDiff (h₀ : ℝ) (iterForwardDiff (fun i => (h i : ℝ)) f) (n : ℝ))‖ := by
            gcongr with h hh
            exact hstep_inner h hh
        _ = (2 * (N : ℝ)) ^ (2 ^ (k + 1) - (k + 1) - 1) *
              ∑ h' ∈ Fintype.piFinset
                (fun _ : Fin (k + 1) => Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)),
                ‖∑ n ∈ weylInterval A B h',
                  e (iterForwardDiff (fun i => (h' i : ℝ)) f (n : ℝ))‖ := by
            rw [hprod_sum]

/-- **Weyl's squaring inequality** on `Finset.Ioc M (M + N)` for `1 ≤ N` and any `k : ℕ`. -/
theorem weyl_squaring_ineq (k : ℕ) (f : ℝ → ℝ) (M N : ℕ) (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Ioc M (M + N), e (f (n : ℝ))‖ ^ (2 ^ k) ≤
      (2 * (N : ℝ)) ^ (2 ^ k - k - 1) *
        ∑ h ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ)) N),
          ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
            e (iterForwardDiff (fun i => (h i : ℝ)) f (n : ℝ))‖ := by
  have hcast_sum :
      ∑ n ∈ Finset.Ioc M (M + N), e (f (n : ℝ)) =
        ∑ n ∈ Finset.Ioc (M : ℤ) ((M + N : ℕ) : ℤ), e (f (n : ℝ)) := by
    refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_Ioc] at hn ⊢; omega
    · intro n₁ _ n₂ _ h; exact Int.ofNat.inj h
    · intro z hz
      simp only [Finset.mem_Ioc] at hz
      refine ⟨z.toNat, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n _; rfl
  rw [hcast_sum]
  have hAB : ((M + N : ℕ) : ℤ) - (M : ℤ) ≤ (N : ℤ) := by omega
  have h0 := weyl_squaring_inner k f (M : ℤ) ((M + N : ℕ) : ℤ) N hN hAB
  refine h0.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro h hh
  simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hh ⊢
  intro i
  have hi := hh i
  omega

end WeylDifferencing

section WeylInequality

private lemma card_tuples_prod_zero_le :
    ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ((Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(N : ℤ)) N)).filter
        (fun h => ∏ i, h i = 0)).card ≤ m * (3 * N) ^ (m - 1)
  | 0, _, hm, _ => by omega
  | m + 1, N, _, hN => by
    let S := (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc (-(N : ℤ)) N)).filter
      (fun h => ∏ i, h i = 0)
    have hsub : S ⊆ Finset.biUnion Finset.univ fun i : Fin (m + 1) =>
        (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc (-(N : ℤ)) N)).filter
          (fun h => h i = 0) := by
      intro h hh
      simp only [S, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and] at hh ⊢
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hh.2
      exact ⟨i, hh.1, hi⟩
    have hfiber : ∀ i : Fin (m + 1),
        ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc (-(N : ℤ)) N)).filter
          (fun h => h i = 0)).card ≤ (3 * N) ^ m := by
      intro i
      let Fi := (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc (-(N : ℤ)) N)).filter
        (fun h => h i = 0)
      let T := Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(N : ℤ)) N)
      have hcard : Fi.card ≤ T.card := by
        refine Finset.card_le_card_of_injOn (fun h => fun j => h (i.succAbove j))
          (fun h hh => Fintype.mem_piFinset.mpr fun j =>
            (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hh).1) (i.succAbove j)) ?_
        intro h₁ hh₁ h₂ hh₂ heq
        have hz1 : h₁ i = 0 := (Finset.mem_filter.mp hh₁).2
        have hz2 : h₂ i = 0 := (Finset.mem_filter.mp hh₂).2
        ext k
        rcases eq_or_ne k i with rfl | hk
        · exact hz1.trans hz2.symm
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
          exact congrFun heq j
      have hT : T.card ≤ (3 * N) ^ m := by
        dsimp only [T]
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hIcc : (Finset.Icc (-(N : ℤ)) N).card ≤ 3 * N := by
          rw [Int.card_Icc]; omega
        exact Nat.pow_le_pow_left hIcc m
      exact hcard.trans hT
    calc S.card ≤ ∑ i : Fin (m + 1),
          ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc (-(N : ℤ)) N)).filter
            (fun h => h i = 0)).card := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin (m + 1), (3 * N) ^ m := Finset.sum_le_sum fun i _ => hfiber i
      _ = (m + 1) * (3 * N) ^ m := by simp

private theorem weyl_inequality_k_ge_two {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : ℝ[X]), P.natDegree ≤ k → ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Nat.Coprime a.natAbs q →
        |P.coeff k - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ (M N : ℕ), 1 ≤ N →
          ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ ≤
            C * (N : ℝ) ^ (1 + ε) *
              ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) ^ ((2 : ℝ) ^ (1 - (k : ℤ))) := by
  let m : ℕ := k - 1
  have hm : 1 ≤ m := by omega
  have hmk : m + 1 = k := by omega
  let δ : ℝ := (2 ^ m : ℝ) * ε / ((m * (m - 1) + 1 : ℕ) : ℝ)
  have hδ : 0 < δ := by positivity
  obtain ⟨Cdiv, hCdiv_pos, hCdiv⟩ := card_divisors_le_rpow hδ
  have hlog_bd : ∃ Clog : ℝ, 0 < Clog ∧ ∀ x : ℝ, 2 ≤ x → Real.log x ≤ Clog * x ^ δ := by
    refine ⟨(1 : ℝ) / δ, by positivity, fun x hx => ?_⟩
    have hx_pos : 0 < x := by linarith
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos δ)
    rw [Real.log_rpow hx_pos] at h1
    rw [one_div_mul_eq_div, le_div_iff₀ hδ]
    linarith
  obtain ⟨Clog, hClog_pos, hClog⟩ := hlog_bd
  let K0 : ℝ := (2 : ℝ) ^ (2 ^ m - m - 1)
  let K1 : ℝ := (m : ℝ) * 3 ^ (m - 1)
  let K2 : ℝ := 2 ^ m * Cdiv ^ (m - 1) * 9 * ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1)
  let Cpow : ℝ := K0 * (K1 + K2)
  have hCpow_pos : 0 < Cpow := by positivity
  let C : ℝ := max 1 (Cpow ^ ((2 : ℝ) ^ (1 - (k : ℤ))))
  refine ⟨C, by positivity, fun P hPdeg a q hq hcop hα M N hN => ?_⟩
  have hN_pos : (0 : ℝ) < N := by positivity
  have hq_pos : (0 : ℝ) < q := by positivity
  have hbase_pos : 0 < (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)) := by positivity
  by_cases hN1 : N = 1
  · subst hN1
    have hge1 : 1 ≤ (q : ℝ)⁻¹ + ((1 : ℕ) : ℝ)⁻¹ + (q : ℝ) * ((1 : ℕ) : ℝ) ^ (-(k : ℝ)) := by
      simp only [Nat.cast_one, inv_one, Real.one_rpow, mul_one]
      have : 0 ≤ (q : ℝ)⁻¹ + (q : ℝ) := by positivity
      linarith
    have hrpow1 : 1 ≤ ((q : ℝ)⁻¹ + ((1 : ℕ) : ℝ)⁻¹ + (q : ℝ) * ((1 : ℕ) : ℝ) ^ (-(k : ℝ))) ^
        ((2 : ℝ) ^ (1 - (k : ℤ))) :=
      Real.one_le_rpow hge1 (by positivity)
    calc ‖∑ n ∈ Finset.Ioc M (M + 1), e (P.eval (n : ℝ))‖
        ≤ 1 := (norm_sum_le _ _).trans_eq (by simp [norm_e])
      _ ≤ C * ((1 : ℕ) : ℝ) ^ (1 + ε) *
            ((q : ℝ)⁻¹ + ((1 : ℕ) : ℝ)⁻¹ + (q : ℝ) * ((1 : ℕ) : ℝ) ^ (-(k : ℝ))) ^
              ((2 : ℝ) ^ (1 - (k : ℤ))) := by
          simp only [Nat.cast_one, Real.one_rpow, mul_one]
          have hC1 : 1 ≤ C := le_max_left _ _
          exact le_trans (one_mul 1).symm.le (mul_le_mul hC1 (by simpa using hrpow1) zero_le_one (by positivity))
  have hN2 : 2 ≤ N := by omega
  by_cases hq_big : (N : ℝ) ^ k < (q : ℝ)
  · have hge1 : 1 ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)) := by
      have h1 : 1 ≤ (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)) := by
        rw [Real.rpow_neg hN_pos.le, Real.rpow_natCast, ← div_eq_mul_inv, one_le_div (by positivity)]
        exact hq_big.le
      have h2 : 0 ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ := by positivity
      linarith
    have hrpow1 : 1 ≤ ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) ^
        ((2 : ℝ) ^ (1 - (k : ℤ))) :=
      Real.one_le_rpow hge1 (by positivity)
    have hNle : (N : ℝ) ≤ C * (N : ℝ) ^ (1 + ε) := by
      have hC1 : 1 ≤ C := le_max_left _ _
      have hNr : (N : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
        conv_lhs => rw [← Real.rpow_one (N : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
      nlinarith [Real.rpow_pos_of_pos hN_pos (1 + ε)]
    calc ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖
        ≤ (N : ℝ) := by
          refine (norm_sum_le _ _).trans_eq ?_
          simp [norm_e, Nat.card_Ioc]
      _ ≤ (C * (N : ℝ) ^ (1 + ε)) * 1 := by linarith
      _ ≤ C * (N : ℝ) ^ (1 + ε) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) ^
              ((2 : ℝ) ^ (1 - (k : ℤ))) := by
          gcongr
  have hq_le : (q : ℝ) ≤ (N : ℝ) ^ k := not_lt.mp hq_big
  have hsq := weyl_squaring_ineq m (fun t => P.eval t) M N hN
  let Hbox := Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(N : ℤ)) N)
  let H0 := Hbox.filter (fun h => ∏ i, h i = 0)
  let H1 := Hbox.filter (fun h => ∏ i, h i ≠ 0)
  have hsplit_box :
      ∑ h ∈ Hbox, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
          e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ =
        ∑ h ∈ H0, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
            e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ +
          ∑ h ∈ H1, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
            e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not Hbox (fun h => ∏ i, h i = 0)]
  have hlen_weyl : ∀ h : Fin m → ℤ,
      ∃ A' B' : ℤ, weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h = Finset.Ioc A' B' ∧
        B' - A' ≤ (N : ℤ) := by
    intro h
    rcases weylInterval_eq_Ioc (M : ℤ) ((M + N : ℕ) : ℤ) h with ⟨A', B', hEq, hlen⟩
    refine ⟨A', B', hEq, hlen.trans ?_⟩
    exact max_le (by positivity) (by omega)
  have hpart0 :
      ∑ h ∈ H0, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
          e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ ≤
        K1 * (N : ℝ) ^ k * (N : ℝ)⁻¹ := by
    have hterm : ∀ h ∈ H0,
        ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
          e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ ≤ (N : ℝ) := by
      intro h _
      rcases hlen_weyl h with ⟨A', B', hEq, hlen⟩
      rw [hEq]
      calc ‖∑ n ∈ Finset.Ioc A' B', _‖
          ≤ ∑ _n ∈ Finset.Ioc A' B', (1 : ℝ) := (norm_sum_le _ _).trans_eq (by simp [norm_e])
        _ = (((B' - A').toNat : ℕ) : ℝ) := by simp [Int.card_Ioc]
        _ ≤ (N : ℝ) := by exact_mod_cast (by omega : ((B' - A').toNat : ℤ) ≤ N)
    have hcard0 : (H0.card : ℝ) ≤ (m : ℝ) * (3 * (N : ℝ)) ^ (m - 1) := by
      exact_mod_cast card_tuples_prod_zero_le m N hm hN
    calc ∑ h ∈ H0, _ ≤ ∑ _h ∈ H0, (N : ℝ) := Finset.sum_le_sum hterm
      _ = (H0.card : ℝ) * (N : ℝ) := by simp
      _ ≤ (m : ℝ) * (3 * (N : ℝ)) ^ (m - 1) * (N : ℝ) := by gcongr
      _ = K1 * (N : ℝ) ^ m := by
          dsimp only [K1]
          have hm1 : (N : ℝ) ^ (m - 1) * (N : ℝ) = (N : ℝ) ^ m := by
            conv_rhs => rw [← Nat.sub_add_cancel hm, pow_add, pow_one]
          rw [mul_pow]
          calc (m : ℝ) * ((3 : ℝ) ^ (m - 1) * (N : ℝ) ^ (m - 1)) * (N : ℝ)
              = (m : ℝ) * (3 : ℝ) ^ (m - 1) * ((N : ℝ) ^ (m - 1) * (N : ℝ)) := by ring
            _ = (m : ℝ) * (3 : ℝ) ^ (m - 1) * (N : ℝ) ^ m := by rw [hm1]
      _ = K1 * (N : ℝ) ^ k * (N : ℝ)⁻¹ := by
          rw [← hmk, pow_succ]
          field_simp [hN_pos.ne']
  have hpart1 :
      ∑ h ∈ H1, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
          e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ ≤
        K2 * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
    have hterm1 : ∀ h ∈ H1,
        ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
          e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ ≤
          linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i).natAbs : ℕ) : ℝ)) := by
      intro h hh
      let hr : Fin m → ℝ := fun i => (h i : ℝ)
      have hdeg_poly := iterPolyDiff_natDegree_and_coeff hr P 1 (by omega : P.natDegree ≤ 1 + m)
      let Q := iterPolyDiff hr P
      have hQ_eq : ∀ t : ℝ, Q.eval t = Q.coeff 1 * t + Q.coeff 0 := fun t => by
        have hQdeg : Q.natDegree ≤ 1 := hdeg_poly.1
        have hsum := Polynomial.as_sum_range' Q 2 (Nat.lt_succ_of_le hQdeg)
        conv_lhs => rw [hsum]
        simp [Finset.sum_range_succ, add_comm]
      have hQ1 : Q.coeff 1 = (k.factorial : ℝ) * (∏ i, hr i) * P.coeff k := by
        have h2 := hdeg_poly.2
        have hdesc_fac : (1 + m).descFactorial m = k.factorial := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, ← Nat.choose_symm (by omega : m ≤ 1 + m),
            show 1 + m - m = 1 by omega, Nat.choose_one_right, mul_comm,
            show 1 + m = k by omega, ← hmk, Nat.factorial_succ]
        rw [hdesc_fac, show 1 + m = k by omega] at h2
        exact h2
      rcases hlen_weyl h with ⟨A', B', hEq, hlen⟩
      rw [hEq]
      by_cases hAB' : A' ≤ B'
      · have hnorm_eq :
            ‖∑ n ∈ Finset.Ioc A' B', e (iterForwardDiff hr (fun t => P.eval t) (n : ℝ))‖ =
              ‖∑ n ∈ Finset.Ioc A' B', e (Q.coeff 1 * (n : ℝ))‖ := by
          have hsum_eq :
              ∑ n ∈ Finset.Ioc A' B', e (iterForwardDiff hr (fun t => P.eval t) (n : ℝ)) =
                e (Q.coeff 0) * ∑ n ∈ Finset.Ioc A' B', e (Q.coeff 1 * (n : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [← eval_iterPolyDiff hr P (n : ℝ)]
            change e (Q.eval (n : ℝ)) = e (Q.coeff 0) * e (Q.coeff 1 * (n : ℝ))
            rw [hQ_eq, add_comm, e_add]
          rw [hsum_eq, norm_mul, norm_e, one_mul]
        rw [hnorm_eq]
        have hlin := norm_sum_Ioc_int_e_le_linearExpBound (Q.coeff 1) hAB' hlen
        have hprod_abs :
            linearExpBound (N : ℝ) (Q.coeff 1) =
              linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i).natAbs : ℕ) : ℝ)) := by
          have h1 : Q.coeff 1 = P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i : ℝ))) := by
            rw [hQ1]; ring
          have h2 : |∏ i, (h i : ℝ)| = ((∏ i, (h i).natAbs : ℕ) : ℝ) := by
            rw [Finset.abs_prod]
            push_cast
            refine Finset.prod_congr rfl fun i _ => ?_
            simp only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          rcases abs_cases (∏ i, (h i : ℝ)) with ⟨habs, _⟩ | ⟨habs, _⟩
          · rw [h1, ← habs, h2]
          · rw [h1, show ∏ i, (h i : ℝ) = -((∏ i, (h i).natAbs : ℕ) : ℝ) by linarith [habs, h2]]
            have : P.coeff k * ((k.factorial : ℕ) * -((∏ i, (h i).natAbs : ℕ) : ℝ)) =
                -(P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i).natAbs : ℕ) : ℝ)) := by ring
            rw [this, linearExpBound_neg]
        rwa [← hprod_abs]
      · have hempty : Finset.Ioc A' B' = ∅ := Finset.Ioc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, norm_zero]
        exact linearExpBound_nonneg (Nat.cast_nonneg N) _
    let R_up := N ^ m
    have hmap_r : ∀ h ∈ H1, ∏ i, (h i).natAbs ∈ Finset.Icc 1 R_up := by
      intro h hh
      simp only [H1, Finset.mem_filter, Hbox, Fintype.mem_piFinset, Finset.mem_Icc] at hh
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · have hne : ∏ i, (h i).natAbs ≠ 0 := by
          intro hz
          obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
          exact hh.2 (Finset.prod_eq_zero (Finset.mem_univ i) (Int.natAbs_eq_zero.mp hi))
        omega
      · calc ∏ i, (h i).natAbs ≤ ∏ _i ∈ (Finset.univ : Finset (Fin m)), N :=
              Finset.prod_le_prod fun i _ => by have := hh.1 i; omega
          _ = N ^ m := by simp
    have hgroup_r :
        ∑ h ∈ H1, linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i).natAbs : ℕ) : ℝ)) ≤
          ∑ r ∈ Finset.Icc 1 R_up,
            ((2 ^ m * r.divisors.card ^ (m - 1) : ℕ) : ℝ) *
              linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) := by
      rw [← Finset.sum_fiberwise_of_maps_to hmap_r]
      refine Finset.sum_le_sum fun r hr => ?_
      have hconst :
          ∑ h ∈ H1 with ∏ i, (h i).natAbs = r,
              linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i).natAbs : ℕ) : ℝ)) =
            ((H1.filter (fun h => ∏ i, (h i).natAbs = r)).card : ℝ) *
              linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) := by
        rw [Finset.sum_congr rfl fun h hh => by rw [(Finset.mem_filter.mp hh).2]]
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      refine mul_le_mul_of_nonneg_right ?_ (linearExpBound_nonneg (Nat.cast_nonneg N) _)
      have hsub_H : H1.filter (fun h => ∏ i, (h i).natAbs = r) ⊆
          Hbox.filter (fun h => ∏ i, (h i).natAbs = r) :=
        Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      exact_mod_cast (Finset.card_le_card hsub_H).trans
        (card_int_tuples_prod_natAbs_eq_le m N r hm (Finset.mem_Icc.mp hr).1)
    have hdiv_r : ∀ r ∈ Finset.Icc 1 R_up,
        ((2 ^ m * r.divisors.card ^ (m - 1) : ℕ) : ℝ) ≤
          2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hdr := hCdiv r hr.1
      have hr_le : (r : ℝ) ^ δ ≤ (N : ℝ) ^ (m * δ) := by
        have hrm : (r : ℝ) ≤ (N : ℝ) ^ m := by exact_mod_cast hr.2
        calc (r : ℝ) ^ δ ≤ ((N : ℝ) ^ m) ^ δ := Real.rpow_le_rpow (by positivity) hrm hδ.le
          _ = (N : ℝ) ^ (m * δ) := by
            rw [← Real.rpow_natCast (N : ℝ) m, ← Real.rpow_mul hN_pos.le]
      have hpow_le : (r.divisors.card : ℝ) ^ (m - 1) ≤
          (Cdiv * (N : ℝ) ^ (m * δ)) ^ (m - 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdr.trans (mul_le_mul_of_nonneg_left hr_le hCdiv_pos.le)) _
      have hpow_eq : (Cdiv * (N : ℝ) ^ (m * δ)) ^ (m - 1) =
          Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) := by
        rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (m * δ)) (m - 1),
          ← Real.rpow_mul hN_pos.le]
        congr 2
        push_cast
        ring
      rw [hpow_eq] at hpow_le
      push_cast
      calc (2 : ℝ) ^ m * (r.divisors.card : ℝ) ^ (m - 1)
          ≤ (2 : ℝ) ^ m * (Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ)) :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ = 2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * δ) := by
            rw [Nat.cast_mul]; ring
    have hsum_kfac :
        ∑ r ∈ Finset.Icc 1 R_up, linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) ≤
          ∑ s ∈ Finset.Icc 1 (k.factorial * R_up), linearExpBound (N : ℝ) (P.coeff k * (s : ℝ)) := by
      have himg_eq :
          ∑ r ∈ Finset.Icc 1 R_up, linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) =
            ∑ s ∈ (Finset.Icc 1 R_up).image (fun r => k.factorial * r),
              linearExpBound (N : ℝ) (P.coeff k * (s : ℝ)) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun r _ => by push_cast; rfl
        · intro r₁ _ r₂ _ heq
          exact Nat.mul_left_cancel (Nat.factorial_pos k) heq
      rw [himg_eq]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => linearExpBound_nonneg (Nat.cast_nonneg N) _)
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨r, hr, rfl⟩
      simp only [Finset.mem_Icc] at hr ⊢
      exact ⟨Nat.mul_pos (Nat.factorial_pos k) hr.1, Nat.mul_le_mul_left _ hr.2⟩
    have hlin_sum := sum_Icc_linearExpBound_le hq hcop hα (k.factorial * R_up) (Nat.cast_nonneg N)
    have hlog_q : Real.log (2 * (q : ℝ)) ≤ (k : ℝ) * Clog * (2 : ℝ) ^ δ * (N : ℝ) ^ δ := by
      have h2q : 2 * (q : ℝ) ≤ (2 * (N : ℝ)) ^ k := by
        have : (2 : ℝ) ≤ 2 ^ k := by
          have : (2 : ℕ) ≤ 2 ^ k := by
            calc 2 = 2 ^ 1 := by simp
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          exact_mod_cast this
        calc 2 * (q : ℝ) ≤ 2 * (N : ℝ) ^ k := by gcongr
          _ ≤ 2 ^ k * (N : ℝ) ^ k := by gcongr
          _ = (2 * (N : ℝ)) ^ k := by rw [mul_pow]
      have hlog1 : Real.log (2 * (q : ℝ)) ≤ Real.log ((2 * (N : ℝ)) ^ k) :=
        Real.log_le_log (by positivity) h2q
      have hlog2 : Real.log ((2 * (N : ℝ)) ^ k) = (k : ℝ) * Real.log (2 * (N : ℝ)) := by
        rw [Real.log_pow]
      have hlog3 : Real.log (2 * (N : ℝ)) ≤ Clog * (2 * (N : ℝ)) ^ δ :=
        hClog (2 * (N : ℝ)) (by exact_mod_cast (by omega : 2 ≤ 2 * N))
      have hrpow_mul : (2 * (N : ℝ)) ^ δ = (2 : ℝ) ^ δ * (N : ℝ) ^ δ :=
        Real.mul_rpow two_pos.le hN_pos.le
      calc Real.log (2 * (q : ℝ)) ≤ (k : ℝ) * Real.log (2 * (N : ℝ)) := hlog1.trans_eq hlog2
        _ ≤ (k : ℝ) * (Clog * ((2 : ℝ) ^ δ * (N : ℝ) ^ δ)) := by gcongr; rwa [hrpow_mul] at hlog3
        _ = (k : ℝ) * Clog * (2 : ℝ) ^ δ * (N : ℝ) ^ δ := by ring
    have hmain_sum :
        9 * ((((k.factorial * R_up : ℕ) : ℝ) + q) * Real.log (2 * (q : ℝ)) +
            ((k.factorial * R_up : ℕ) : ℝ) * (N : ℝ) / q) ≤
          9 * ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) *
            (N : ℝ) ^ (k + δ) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
      have hR_eq : ((k.factorial * R_up : ℕ) : ℝ) = (k.factorial : ℝ) * (N : ℝ) ^ m := by
        simp [R_up]
      have h1 : ((k.factorial : ℝ) * (N : ℝ) ^ m + q) * Real.log (2 * (q : ℝ)) ≤
          ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) *
            ((N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
        have hsum_bd : (k.factorial : ℝ) * (N : ℝ) ^ m + q ≤
            ((k.factorial : ℝ) + 1) * (N : ℝ) ^ k * ((N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
          have hA : (N : ℝ) ^ k * (N : ℝ)⁻¹ = (N : ℝ) ^ m := by
            rw [← hmk, pow_succ]; field_simp [hN_pos.ne']
          have hB : (N : ℝ) ^ k * ((q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) = (q : ℝ) := by
            rw [Real.rpow_neg hN_pos.le, Real.rpow_natCast]; field_simp [hN_pos.ne']
          have hpos_m : (0 : ℝ) ≤ (N : ℝ) ^ m := by positivity
          have hpos_k : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
          calc (k.factorial : ℝ) * (N : ℝ) ^ m + q
              ≤ ((k.factorial : ℝ) + 1) * (N : ℝ) ^ m + ((k.factorial : ℝ) + 1) * (q : ℝ) := by nlinarith [hq_pos]
            _ = ((k.factorial : ℝ) + 1) * ((N : ℝ) ^ k * (N : ℝ)⁻¹ + (N : ℝ) ^ k * ((q : ℝ) * (N : ℝ) ^ (-(k : ℝ)))) := by
                rw [hA, hB]; ring
            _ = ((k.factorial : ℝ) + 1) * (N : ℝ) ^ k * ((N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by ring
        have hrpow_split : (N : ℝ) ^ (k + δ) = (N : ℝ) ^ k * (N : ℝ) ^ δ := by
          rw [← Real.rpow_natCast (N : ℝ) k, Real.rpow_add hN_pos]
        have hlog_le' : Real.log (2 * (q : ℝ)) ≤
            ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ δ := by
          have : 0 ≤ (N : ℝ) ^ δ := by positivity
          linarith [hlog_q]
        calc ((k.factorial : ℝ) * (N : ℝ) ^ m + q) * Real.log (2 * (q : ℝ))
            ≤ (((k.factorial : ℝ) + 1) * (N : ℝ) ^ k * ((N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)))) *
                (((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ δ) :=
              mul_le_mul hsum_bd hlog_le'
                (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * q))) (by positivity)
          _ = ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) *
                ((N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
              rw [hrpow_split]; ring
      have h2 : (k.factorial : ℝ) * (N : ℝ) ^ m * (N : ℝ) / q ≤
          ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) * (q : ℝ)⁻¹ := by
        have hmN : (N : ℝ) ^ m * (N : ℝ) = (N : ℝ) ^ k := by rw [← hmk, pow_succ]
        have hNk_le : (N : ℝ) ^ k ≤ (N : ℝ) ^ (k + δ) := by
          rw [← Real.rpow_natCast (N : ℝ) k]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
        have hfac1 : (k.factorial : ℝ) ≤ (k.factorial : ℝ) + 1 := by linarith
        have hfac2 : (1 : ℝ) ≤ (k : ℝ) * Clog * (2 : ℝ) ^ δ + 1 := by
          have : 0 ≤ (k : ℝ) * Clog * (2 : ℝ) ^ δ := by positivity
          linarith
        calc (k.factorial : ℝ) * (N : ℝ) ^ m * (N : ℝ) / q
            = (k.factorial : ℝ) * (N : ℝ) ^ k * (q : ℝ)⁻¹ := by rw [mul_assoc, hmN, div_eq_mul_inv]
          _ ≤ ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) * (q : ℝ)⁻¹ := by
              have : (k.factorial : ℝ) * (N : ℝ) ^ k ≤
                  ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) := by
                calc (k.factorial : ℝ) * (N : ℝ) ^ k
                    ≤ ((k.factorial : ℝ) + 1) * (N : ℝ) ^ (k + δ) := mul_le_mul hfac1 hNk_le (by positivity) (by positivity)
                  _ = ((k.factorial : ℝ) + 1) * 1 * (N : ℝ) ^ (k + δ) := by ring
                  _ ≤ ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) := by gcongr
              exact mul_le_mul_of_nonneg_right this (by positivity)
      rw [hR_eq]
      calc 9 * (((k.factorial : ℝ) * (N : ℝ) ^ m + q) * Real.log (2 * (q : ℝ)) +
              (k.factorial : ℝ) * (N : ℝ) ^ m * (N : ℝ) / q)
          ≤ 9 * (((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) *
                ((N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) +
              ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) * (N : ℝ) ^ (k + δ) *
                (q : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
        _ = 9 * ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) *
              (N : ℝ) ^ (k + δ) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by ring
    have hcomb1 :
        ∑ r ∈ Finset.Icc 1 R_up, ((2 ^ m * r.divisors.card ^ (m - 1) : ℕ) : ℝ) *
            linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) ≤
          2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) *
            ∑ r ∈ Finset.Icc 1 R_up, linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      exact mul_le_mul_of_nonneg_right (hdiv_r r hr) (linearExpBound_nonneg (Nat.cast_nonneg N) _)
    have hrpow_prod :
        (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) * (N : ℝ) ^ ((k : ℝ) + δ) =
          (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) := by
      rw [← Real.rpow_add hN_pos]
      congr 1
      push_cast
      ring
    calc ∑ h ∈ H1, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
            e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖
        ≤ ∑ h ∈ H1, linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (∏ i, (h i).natAbs : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm1
      _ ≤ ∑ r ∈ Finset.Icc 1 R_up, ((2 ^ m * r.divisors.card ^ (m - 1) : ℕ) : ℝ) *
            linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) := hgroup_r
      _ ≤ 2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) *
            ∑ r ∈ Finset.Icc 1 R_up, linearExpBound (N : ℝ) (P.coeff k * ((k.factorial : ℕ) * (r : ℝ))) := hcomb1
      _ ≤ 2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) *
            ∑ s ∈ Finset.Icc 1 (k.factorial * R_up), linearExpBound (N : ℝ) (P.coeff k * (s : ℝ)) := by gcongr
      _ ≤ 2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) *
            (9 * ((((k.factorial * R_up : ℕ) : ℝ) + q) * Real.log (2 * (q : ℝ)) +
              ((k.factorial * R_up : ℕ) : ℝ) * (N : ℝ) / q)) := by gcongr
      _ ≤ 2 ^ m * Cdiv ^ (m - 1) * (N : ℝ) ^ ((m * (m - 1) : ℕ) * δ) *
            (9 * ((k.factorial : ℝ) + 1) * ((k : ℝ) * Clog * (2 : ℝ) ^ δ + 1) *
              (N : ℝ) ^ ((k : ℝ) + δ) *
              ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)))) := by gcongr
      _ = K2 * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
          dsimp only [K2]
          rw [← hrpow_prod]
          ring
  have hN_pow_compare :
      (N : ℝ) ^ k ≤ (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) := by
    rw [← Real.rpow_natCast (N : ℝ) k]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [show 0 ≤ ((m * (m - 1) + 1 : ℕ) : ℝ) * δ by positivity])
  have hpart0' :
      K1 * (N : ℝ) ^ k * (N : ℝ)⁻¹ ≤
        K1 * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
    have hinv_le : (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)) := by
      have : 0 ≤ (q : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)) := by positivity
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN_pow_compare (by positivity)) hinv_le
      (by positivity) (by positivity)
  have hbox_le :
      ∑ h ∈ Hbox, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
          e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ ≤
        (K1 + K2) * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
    rw [hsplit_box]
    linarith [hpart0, hpart0', hpart1]
  have hpow_pref :
      (2 * (N : ℝ)) ^ (2 ^ m - m - 1) *
          ((K1 + K2) * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)))) =
        Cpow * (N : ℝ) ^ ((2 ^ m : ℝ) * (1 + ε)) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
    have h2N : (2 * (N : ℝ)) ^ (2 ^ m - m - 1) =
        K0 * (N : ℝ) ^ ((2 ^ m - m - 1 : ℕ) : ℝ) := by
      dsimp only [K0]
      rw [mul_pow, Real.rpow_natCast]
    have hexp_total : ((2 ^ m - m - 1 : ℕ) : ℝ) + ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) =
        (2 ^ m : ℝ) * (1 + ε) := by
      have hm1 : m + 1 ≤ 2 ^ m := add_one_le_two_pow hm
      have hsub_cast : ((2 ^ m - m - 1 : ℕ) : ℝ) = (2 ^ m : ℝ) - m - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ m - m), Nat.cast_sub (by omega : m ≤ 2 ^ m)]
        push_cast
        ring
      have hk_cast : (k : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hmk.symm
      have hδ_cancel : ((m * (m - 1) + 1 : ℕ) : ℝ) * δ = (2 ^ m : ℝ) * ε := by
        dsimp only [δ]
        have hne : ((m * (m - 1) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hne]
      rw [hsub_cast, hk_cast, hδ_cancel]
      ring
    rw [h2N]
    calc K0 * (N : ℝ) ^ ((2 ^ m - m - 1 : ℕ) : ℝ) *
          ((K1 + K2) * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))))
        = (K0 * (K1 + K2)) *
            ((N : ℝ) ^ ((2 ^ m - m - 1 : ℕ) : ℝ) *
              (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ)) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by ring
      _ = Cpow * (N : ℝ) ^ ((2 ^ m : ℝ) * (1 + ε)) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
          rw [← Real.rpow_add hN_pos, hexp_total]
  have hfinal_pow :
      ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ ^ (2 ^ m) ≤
        Cpow * (N : ℝ) ^ ((2 ^ m : ℝ) * (1 + ε)) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := by
    calc ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ ^ (2 ^ m)
        ≤ (2 * (N : ℝ)) ^ (2 ^ m - m - 1) *
            ∑ h ∈ Hbox, ‖∑ n ∈ weylInterval (M : ℤ) ((M + N : ℕ) : ℤ) h,
              e (iterForwardDiff (fun i => (h i : ℝ)) (fun t => P.eval t) (n : ℝ))‖ := hsq
      _ ≤ (2 * (N : ℝ)) ^ (2 ^ m - m - 1) *
            ((K1 + K2) * (N : ℝ) ^ ((k : ℝ) + ((m * (m - 1) + 1 : ℕ) : ℝ) * δ) *
              ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)))) := by
          gcongr
      _ = Cpow * (N : ℝ) ^ ((2 ^ m : ℝ) * (1 + ε)) *
            ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) := hpow_pref
  let invExp : ℝ := (2 : ℝ) ^ (1 - (k : ℤ))
  have hinvExp_eq : invExp = ((2 ^ m : ℝ))⁻¹ := by
    dsimp only [invExp]
    have h1k : (1 - (k : ℤ)) = -(m : ℤ) := by omega
    rw [h1k, zpow_neg, zpow_natCast]
  have hroot := Real.rpow_le_rpow (by positivity) hfinal_pow (by positivity : 0 ≤ invExp)
  have hlhs_root :
      (‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ ^ (2 ^ m)) ^ invExp =
        ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ := by
    rw [hinvExp_eq, ← Real.rpow_natCast _ (2 ^ m), ← Real.rpow_mul (norm_nonneg _),
      Nat.cast_pow, Nat.cast_ofNat, mul_inv_cancel₀ (by positivity), Real.rpow_one]
  have hrhs_root :
      (Cpow * (N : ℝ) ^ ((2 ^ m : ℝ) * (1 + ε)) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ)))) ^ invExp =
        Cpow ^ invExp * (N : ℝ) ^ (1 + ε) *
          ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) ^ invExp := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), hinvExp_eq,
      ← Real.rpow_mul hN_pos.le, mul_assoc (2 ^ m : ℝ) (1 + ε), mul_comm (1 + ε) ((2 ^ m : ℝ)⁻¹),
      ← mul_assoc (2 ^ m : ℝ), mul_inv_cancel₀ (by positivity), one_mul]
  rw [hlhs_root, hrhs_root] at hroot
  refine hroot.trans ?_
  have hC_le : Cpow ^ invExp ≤ C := le_max_right _ _
  gcongr

/-- **Weyl's inequality** for degree-`k` real polynomials (`k ≥ 1`):
if `|P.coeff k - a/q| ≤ 1/q²` with `gcd(a, q) = 1` and `1 ≤ q`, then for any `ε > 0`,
`‖∑_{n ∈ Ioc M (M + N)} e(P(n))‖ ≤ C * N^(1 + ε) * (q⁻¹ + N⁻¹ + q N^(-k))^(2^(1 - k))`. -/
theorem weyl_inequality {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : ℝ[X]), P.natDegree ≤ k → ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Nat.Coprime a.natAbs q →
        |P.coeff k - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ (M N : ℕ), 1 ≤ N →
          ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ ≤
            C * (N : ℝ) ^ (1 + ε) *
              ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(k : ℝ))) ^ ((2 : ℝ) ^ (1 - (k : ℤ))) := by
  rcases eq_or_lt_of_le hk with rfl | hk2
  · refine ⟨1, zero_lt_one, fun P hPdeg a q hq hcop hα M N hN => ?_⟩
    have hN_pos : (0 : ℝ) < N := by positivity
    have hq_pos : (0 : ℝ) < q := by positivity
    have hP_eq : ∀ t : ℝ, P.eval t = P.coeff 1 * t + P.coeff 0 := fun t => by
      have hsum := Polynomial.as_sum_range' P 2 (by omega : P.natDegree < 2)
      conv_lhs => rw [hsum]
      simp [Finset.sum_range_succ, add_comm]
    have hnorm_eq :
        ‖∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ))‖ =
          ‖∑ n ∈ Finset.Ioc M (M + N), e (P.coeff 1 * (n : ℝ))‖ := by
      have hsum_eq :
          ∑ n ∈ Finset.Ioc M (M + N), e (P.eval (n : ℝ)) =
            e (P.coeff 0) * ∑ n ∈ Finset.Ioc M (M + N), e (P.coeff 1 * (n : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hP_eq, add_comm, e_add]
      rw [hsum_eq, norm_mul, norm_e, one_mul]
    have hN_rpow : (N : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
      conv_lhs => rw [← Real.rpow_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
    have hexp1 : ((2 : ℝ) ^ (1 - ((1 : ℕ) : ℤ))) = 1 := by simp
    have hNneg1 : (N : ℝ) ^ (-((1 : ℕ) : ℝ)) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
    rw [one_mul, hexp1, hNneg1, Real.rpow_one, hnorm_eq]
    by_cases hq1 : q = 1
    · subst hq1
      have h1 : 1 ≤ ((1 : ℕ) : ℝ)⁻¹ + (N : ℝ)⁻¹ + ((1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
        simp only [Nat.cast_one, inv_one, one_mul]
        have : 0 ≤ (N : ℝ)⁻¹ + (N : ℝ)⁻¹ := by positivity
        linarith
      calc ‖∑ n ∈ Finset.Ioc M (M + N), e (P.coeff 1 * (n : ℝ))‖
          ≤ (N : ℝ) := norm_sum_Ioc_e_le_length _ M N
        _ ≤ (N : ℝ) ^ (1 + ε) * 1 := by linarith
        _ ≤ (N : ℝ) ^ (1 + ε) * (((1 : ℕ) : ℝ)⁻¹ + (N : ℝ)⁻¹ + ((1 : ℕ) : ℝ) * (N : ℝ)⁻¹) := by
            gcongr
    · have hq2 : 2 ≤ q := by omega
      by_cases hqN : N ≤ q
      · have h1 : 1 ≤ (q : ℝ) * (N : ℝ)⁻¹ := by
          rw [← div_eq_mul_inv, one_le_div hN_pos]
          exact_mod_cast hqN
        have h2 : 1 ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ)⁻¹ := by
          have : 0 ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ := by positivity
          linarith
        calc ‖∑ n ∈ Finset.Ioc M (M + N), e (P.coeff 1 * (n : ℝ))‖
            ≤ (N : ℝ) := norm_sum_Ioc_e_le_length _ M N
          _ ≤ (N : ℝ) ^ (1 + ε) * 1 := by linarith
          _ ≤ (N : ℝ) ^ (1 + ε) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ)⁻¹) := by gcongr
      · have hq_lt_N : q < N := by omega
        have hndiv : ¬ (q : ℤ) ∣ a := by
          intro hdvd
          have hd : q ∣ a.natAbs := Int.natCast_dvd.mp hdvd
          have hq_dvd_gcd : q ∣ Nat.gcd a.natAbs q := Nat.dvd_gcd hd dvd_rfl
          rw [hcop] at hq_dvd_gcd
          have hq_eq1 : q = 1 := Nat.dvd_one.mp hq_dvd_gcd
          omega
        have hbase : 1 / (q : ℝ) ≤ distToInt ((a : ℝ) / q) := by
          rw [distToInt_intCast_div_natCast (by omega : 0 < q)]
          have hs_pos : 1 ≤ Int.natMod a q := by
            by_contra h0
            have : a % (q : ℤ) = 0 := by
              dsimp only [Int.natMod] at h0
              have hnn : 0 ≤ a % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq_pos.ne')
              omega
            exact hndiv (Int.dvd_of_emod_eq_zero this)
          have hs_lt : Int.natMod a q < q := by
            dsimp only [Int.natMod]
            have hnn : 0 ≤ a % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq_pos.ne')
            have hlt : a % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq_pos)
            omega
          have hm1 : (1 : ℝ) ≤ ((min (Int.natMod a q) (q - Int.natMod a q) : ℕ) : ℝ) := by
            exact_mod_cast le_min hs_pos (by omega)
          exact div_le_div_of_nonneg_right hm1 hq_pos.le
        have hdist_lb : 1 / (2 * (q : ℝ)) ≤ distToInt (P.coeff 1) := by
          have h1 := distToInt_sub_abs_le_add ((a : ℝ) / q) (P.coeff 1 - (a : ℝ) / q)
          rw [show (a : ℝ) / q + (P.coeff 1 - (a : ℝ) / q) = P.coeff 1 by ring] at h1
          have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq2
          have hq_sq : 1 / (q : ℝ) ^ 2 ≤ 1 / (2 * (q : ℝ)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hq_pos, hq2R]
          have hsub_le : 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 / (2 * (q : ℝ)) := by ring
          linarith [hα, h1, hbase, hq_sq, hsub_le]
        have hdist_pos : 0 < distToInt (P.coeff 1) := lt_of_lt_of_le (by positivity) hdist_lb
        have hnotint : ∀ n : ℤ, P.coeff 1 ≠ n := (distToInt_pos_iff _).mp hdist_pos
        have hbd := norm_sum_Ioc_e_le_inv_two_dist (P.coeff 1) hnotint M N
        have hinv_le : 1 / (2 * distToInt (P.coeff 1)) ≤ (q : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          have hmul := mul_le_mul_of_nonneg_left hdist_lb (by positivity : (0 : ℝ) ≤ 2 * q)
          rw [mul_div_cancel₀ _ (by positivity)] at hmul
          linarith
        have hq_rhs : (q : ℝ) ≤ (N : ℝ) ^ (1 + ε) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ)⁻¹) := by
          have h1 : (q : ℝ) = (N : ℝ) * ((q : ℝ) * (N : ℝ)⁻¹) := by
            field_simp [hN_pos.ne']
          have h2 : (q : ℝ) * (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ)⁻¹ := by
            have : 0 ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ := by positivity
            linarith
          calc (q : ℝ) = (N : ℝ) * ((q : ℝ) * (N : ℝ)⁻¹) := h1
            _ ≤ (N : ℝ) ^ (1 + ε) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ)⁻¹) :=
                mul_le_mul hN_rpow h2 (by positivity) (by positivity)
        exact (hbd.trans hinv_le).trans hq_rhs
  · exact weyl_inequality_k_ge_two hk2 hε

end WeylInequality

end AnalyticNumberTheory.ExponentialSums

