import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Divisors

/-!
# Vaughan's Identity and Vinogradov's Linear Prime Exponential Sum Bound

This file develops Vaughan's decomposition for the von Mangoldt function `Λ`, bilinear Type I and
Type II exponential sum bounds, and Vinogradov's linear prime exponential sum estimate:

- Exact algebraic Vaughan identity in `ArithmeticFunction ℝ`, pointwise over divisors, and for
  weighted partial sums `∑_{1 ≤ n ≤ x} Λ(n) f(n)` decomposing into a finite prefix, a
  logarithmic Type I sum, an unweighted Type I' sum, and a Type II bilinear sum.
- Elementary divisor second-moment bound `∑_{1 ≤ m ≤ Y} d(m)^2 ≤ Y (1 + log Y)^3`.
- Bilinear Type I bound `∑_{1 ≤ m ≤ M} ‖∑_{1 ≤ n ≤ x/m} e(α m n)‖` and Cauchy–Schwarz Type II
  bilinear bound `‖∑_{M < m ≤ 2M} ∑_{N < n ≤ x/m} a_m b_n e(α m n)‖` under Diophantine
  approximation `|α - a/q| ≤ 1/q²` (`gcd(a, q) = 1`).
- Vinogradov's linear prime exponential sum bound
  `‖∑_{1 ≤ n ≤ x} Λ(n) e(α n)‖ ≤ C * (x * q^(-1/2) + x^(4/5) + x^(1/2) * q^(1/2)) * (log x)^4`.
-/

noncomputable section

open Complex Finset
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
  ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

section VaughanAlgebraicIdentity

/-- Truncation of the Möbius function `μ(n)` to `n ≤ U`. -/
def moebiusTrunc (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then (μ n : ℝ) else 0, by simp⟩

/-- Tail of the Möbius function `μ(n)` supported on `U < n`. -/
def moebiusTail (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then (μ n : ℝ) else 0, by simp⟩

/-- Truncation of the von Mangoldt function `Λ(n)` to `n ≤ V`. -/
def vonMangoldtTrunc (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ V then Λ n else 0, by simp⟩

/-- Tail of the von Mangoldt function `Λ(n)` supported on `V < n`. -/
def vonMangoldtTail (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if V < n then Λ n else 0, by simp⟩

/-- Evaluation of `moebiusTrunc U`. -/
@[simp]
theorem moebiusTrunc_apply (U n : ℕ) :
    moebiusTrunc U n = if n ≤ U then (μ n : ℝ) else 0 := rfl

/-- Evaluation of `moebiusTail U`. -/
@[simp]
theorem moebiusTail_apply (U n : ℕ) :
    moebiusTail U n = if U < n then (μ n : ℝ) else 0 := rfl

/-- Evaluation of `vonMangoldtTrunc V`. -/
@[simp]
theorem vonMangoldtTrunc_apply (V n : ℕ) :
    vonMangoldtTrunc V n = if n ≤ V then Λ n else 0 := rfl

/-- Evaluation of `vonMangoldtTail V`. -/
@[simp]
theorem vonMangoldtTail_apply (V n : ℕ) :
    vonMangoldtTail V n = if V < n then Λ n else 0 := rfl

/-- Splitting `(μ : ArithmeticFunction ℝ) = moebiusTrunc U + moebiusTail U`. -/
theorem moebiusTrunc_add_tail (U : ℕ) :
    moebiusTrunc U + moebiusTail U = (μ : ArithmeticFunction ℝ) := by
  ext n
  simp only [add_apply, moebiusTrunc_apply, moebiusTail_apply,
    ArithmeticFunction.intCoe_apply]
  by_cases hn : n ≤ U
  · have hn' : ¬ U < n := by omega
    simp [hn, hn']
  · have hn' : U < n := by omega
    simp [hn, hn']

/-- Splitting `Λ = vonMangoldtTrunc V + vonMangoldtTail V`. -/
theorem vonMangoldtTrunc_add_tail (V : ℕ) :
    vonMangoldtTrunc V + vonMangoldtTail V = Λ := by
  ext n
  simp only [add_apply, vonMangoldtTrunc_apply, vonMangoldtTail_apply]
  by_cases hn : n ≤ V
  · have hn' : ¬ V < n := by omega
    simp [hn, hn']
  · have hn' : V < n := by omega
    simp [hn, hn']

/-- Type I' Dirichlet convolution coefficient `(moebiusTrunc U * vonMangoldtTrunc V)(d)`
arising in Vaughan's identity. -/
def vaughanTypeICoeff (U V : ℕ) : ArithmeticFunction ℝ :=
  moebiusTrunc U * vonMangoldtTrunc V

/-- Type II Dirichlet convolution coefficient `(moebiusTail U * ζ)(m)` arising in
Vaughan's identity. -/
def vaughanTypeIICoeff (U : ℕ) : ArithmeticFunction ℝ :=
  moebiusTail U * ζ

/-- Exact algebraic Vaughan identity in `ArithmeticFunction ℝ`:
`Λ = vonMangoldtTrunc V + moebiusTrunc U * log - vaughanTypeICoeff U V * ζ +
vaughanTypeIICoeff U * vonMangoldtTail V`. -/
theorem vaughan_arithmetic_identity (U V : ℕ) :
    Λ = vonMangoldtTrunc V + moebiusTrunc U * ArithmeticFunction.log -
      vaughanTypeICoeff U V * (ζ : ArithmeticFunction ℝ) +
      vaughanTypeIICoeff U * vonMangoldtTail V := by
  have hL : vonMangoldtTrunc V + vonMangoldtTail V = Λ := vonMangoldtTrunc_add_tail V
  have hM : moebiusTrunc U + moebiusTail U = (μ : ArithmeticFunction ℝ) :=
    moebiusTrunc_add_tail U
  have hzeta_lam : (ζ : ArithmeticFunction ℝ) * Λ = ArithmeticFunction.log :=
    ArithmeticFunction.zeta_mul_vonMangoldt
  have hmu_zeta : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  calc Λ
      = vonMangoldtTrunc V + 1 * vonMangoldtTail V := by rw [one_mul, hL]
    _ = vonMangoldtTrunc V + ((moebiusTrunc U + moebiusTail U) * (ζ : ArithmeticFunction ℝ)) *
          vonMangoldtTail V := by rw [hM, hmu_zeta]
    _ = vonMangoldtTrunc V + moebiusTrunc U * ((ζ : ArithmeticFunction ℝ) * (Λ - vonMangoldtTrunc V)) +
          (moebiusTail U * (ζ : ArithmeticFunction ℝ)) * vonMangoldtTail V := by
        have htail : vonMangoldtTail V = Λ - vonMangoldtTrunc V := by
          rw [← hL]; ring
        rw [htail]; ring
    _ = vonMangoldtTrunc V + moebiusTrunc U * ArithmeticFunction.log -
          (moebiusTrunc U * vonMangoldtTrunc V) * (ζ : ArithmeticFunction ℝ) +
          (moebiusTail U * (ζ : ArithmeticFunction ℝ)) * vonMangoldtTail V := by
        rw [mul_sub, mul_sub, hzeta_lam]; ring

/-- `vaughanTypeICoeff U V d` vanishes for `U * V < d`. -/
theorem vaughanTypeICoeff_eq_zero_of_gt {U V d : ℕ} (hd : U * V < d) :
    vaughanTypeICoeff U V d = 0 := by
  simp only [vaughanTypeICoeff, ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  simp only [moebiusTrunc_apply, vonMangoldtTrunc_apply]
  split_ifs with h1 h2
  · have hmul : p.1 * p.2 ≤ U * V := Nat.mul_le_mul h1 h2
    omega
  · ring
  · ring
  · ring

/-- Divisor bound `|vaughanTypeICoeff U V d| ≤ Real.log d` for all `U, V, d : ℕ`. -/
theorem abs_vaughanTypeICoeff_le_log (U V d : ℕ) :
    |vaughanTypeICoeff U V d| ≤ Real.log d := by
  simp only [vaughanTypeICoeff, ArithmeticFunction.mul_apply]
  calc |∑ p ∈ Nat.divisorsAntidiagonal d, moebiusTrunc U p.1 * vonMangoldtTrunc V p.2|
      ≤ ∑ p ∈ Nat.divisorsAntidiagonal d, |moebiusTrunc U p.1 * vonMangoldtTrunc V p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.divisorsAntidiagonal d, Λ p.2 := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [abs_mul, moebiusTrunc_apply, vonMangoldtTrunc_apply]
        have hmu : |if p.1 ≤ U then (μ p.1 : ℝ) else 0| ≤ 1 := by
          split_ifs
          · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := p.1))
          · norm_num
        have hlam : |if p.2 ≤ V then Λ p.2 else 0| ≤ Λ p.2 := by
          split_ifs
          · exact le_of_eq (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg)
          · rw [abs_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
        calc |if p.1 ≤ U then (μ p.1 : ℝ) else 0| * |if p.2 ≤ V then Λ p.2 else 0|
            ≤ 1 * Λ p.2 := mul_le_mul hmu hlam (abs_nonneg _) zero_le_one
          _ = Λ p.2 := one_mul _
    _ = ∑ i ∈ d.divisors, Λ i := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ i => Λ i)]
    _ = Real.log d := ArithmeticFunction.vonMangoldt_sum

/-- `vaughanTypeIICoeff U m` vanishes for `m ≤ U`. -/
theorem vaughanTypeIICoeff_eq_zero_of_le {U m : ℕ} (hm : m ≤ U) :
    vaughanTypeIICoeff U m = 0 := by
  simp only [vaughanTypeIICoeff, ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  rcases eq_or_ne m 0 with rfl | hm0
  · exact absurd rfl hp.2
  · have hp1 : p.1 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) ⟨p.2, hp.1.symm⟩
    have hnot : ¬ U < p.1 := by omega
    simp [hnot]

/-- Divisor bound `|vaughanTypeIICoeff U m| ≤ (Nat.divisors m).card` for all `U, m : ℕ`. -/
theorem abs_vaughanTypeIICoeff_le_divisors (U m : ℕ) :
    |vaughanTypeIICoeff U m| ≤ ((Nat.divisors m).card : ℝ) := by
  simp only [vaughanTypeIICoeff, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y => moebiusTail U x * (ζ : ArithmeticFunction ℝ) y)]
  calc |∑ d ∈ m.divisors, moebiusTail U d * (ζ : ArithmeticFunction ℝ) (m / d)|
      ≤ ∑ d ∈ m.divisors, |moebiusTail U d * (ζ : ArithmeticFunction ℝ) (m / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ m.divisors, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rcases Nat.mem_divisors.mp hd with ⟨hd_dvd, hm0⟩
        have hd_pos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd_dvd)
          (Nat.pos_of_dvd_of_pos hd_dvd (Nat.pos_of_ne_zero hm0))
        rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hd_pos.ne',
          Nat.cast_one, mul_one, moebiusTail_apply]
        split_ifs
        · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        · norm_num
    _ = ((Nat.divisors m).card : ℝ) := by simp

/-- Pointwise Vaughan identity decomposing `Λ n` into finite prefix, Type I log term, Type I'
term, and Type II bilinear convolution term. -/
theorem vaughan_identity_pointwise (U V n : ℕ) :
    Λ n =
      (if n ≤ V then Λ n else 0) +
      (∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log (n / d : ℕ)) -
      (∑ d ∈ n.divisors with d ≤ U * V, vaughanTypeICoeff U V d) +
      ∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
        vaughanTypeIICoeff U p.1 * Λ p.2 := by
  have hid := congrFun (congrArg DFunLike.coe (vaughan_arithmetic_identity U V)) n
  simp only [sub_apply, add_apply] at hid
  have hlog : (moebiusTrunc U * ArithmeticFunction.log) n =
      ∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log (n / d : ℕ) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (f := fun d q => moebiusTrunc U d * ArithmeticFunction.log q),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [moebiusTrunc_apply, ArithmeticFunction.log_apply]
  have hzeta : (vaughanTypeICoeff U V * (ζ : ArithmeticFunction ℝ)) n =
      ∑ d ∈ n.divisors with d ≤ U * V, vaughanTypeICoeff U V d := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (f := fun d q => vaughanTypeICoeff U V d * (ζ : ArithmeticFunction ℝ) q),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hd
    · have hnd_pos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd))
          (Nat.pos_of_mem_divisors hd)
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hnd_pos.ne',
        Nat.cast_one, mul_one]
      split_ifs with hle
      · rfl
      · exact vaughanTypeICoeff_eq_zero_of_gt (not_le.mp hle)
  have hII : (vaughanTypeIICoeff U * vonMangoldtTail V) n =
      ∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
        vaughanTypeIICoeff U p.1 * Λ p.2 := by
    rw [ArithmeticFunction.mul_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [vonMangoldtTail_apply]
    by_cases h1 : U < p.1
    · by_cases h2 : V < p.2
      · simp [h1, h2]
      · simp [h1, h2]
    · have hp1 : vaughanTypeIICoeff U p.1 = 0 := vaughanTypeIICoeff_eq_zero_of_le (not_lt.mp h1)
      simp [h1, hp1]
  calc Λ n
      = (vonMangoldtTrunc V) n + (moebiusTrunc U * ArithmeticFunction.log) n -
          (vaughanTypeICoeff U V * (ζ : ArithmeticFunction ℝ)) n +
          (vaughanTypeIICoeff U * vonMangoldtTail V) n := hid
    _ = (if n ≤ V then Λ n else 0) +
          (∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log (n / d : ℕ)) -
          (∑ d ∈ n.divisors with d ≤ U * V, vaughanTypeICoeff U V d) +
          ∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
            vaughanTypeIICoeff U p.1 * Λ p.2 := by rw [vonMangoldtTrunc_apply, hlog, hzeta, hII]

/-- Pointwise Vaughan identity for `V < n`, where the finite truncation term vanishes. -/
theorem vaughan_identity_pointwise_of_gt {U V n : ℕ} (hn : V < n) :
    Λ n =
      (∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log (n / d : ℕ)) -
      (∑ d ∈ n.divisors with d ≤ U * V, vaughanTypeICoeff U V d) +
      ∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
        vaughanTypeIICoeff U p.1 * Λ p.2 := by
  have h := vaughan_identity_pointwise U V n
  simp only [not_le.mpr hn, ↓reduceIte, zero_add] at h
  exact h

private theorem sum_Icc_divisors_mul (N M : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors with d ≤ M, g d (n / d) =
      ∑ d ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 (N / d), g d m := by
  rw [Finset.sum_sigma' (Finset.Icc 1 N) (fun n => n.divisors.filter (· ≤ M))
    (fun n d => g d (n / d)),
    Finset.sum_sigma' (Finset.Icc 1 M) (fun d => Finset.Icc 1 (N / d)) (fun d m => g d m)]
  refine Finset.sum_bij (fun p _ => (⟨p.2, p.1 / p.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hp
    have hn_pos : 0 < n := hp.1.1
    have hd_dvd : d ∣ n := hp.2.1.1
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hn_pos
    have hd_le_n : d ≤ n := Nat.le_of_dvd hn_pos hd_dvd
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hp.2.2⟩,
      Finset.mem_Icc.mpr ⟨Nat.div_pos hd_le_n hd_pos, Nat.div_le_div_right hp.1.2⟩⟩
  · intro ⟨n₁, d₁⟩ hp₁ ⟨n₂, d₂⟩ hp₂ heq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hp₁ hp₂
    have hd : d₁ = d₂ := congrArg Sigma.fst heq
    have hq : n₁ / d₁ = n₂ / d₂ := congrArg Sigma.snd heq
    have hn : n₁ = n₂ := by
      calc n₁ = d₁ * (n₁ / d₁) := (Nat.mul_div_cancel' hp₁.2.1.1).symm
        _ = d₂ * (n₂ / d₂) := by rw [hq, hd]
        _ = n₂ := Nat.mul_div_cancel' hp₂.2.1.1
    cases hn; cases hd; rfl
  · intro ⟨d, m⟩ hdm
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hdm
    have hd_pos : 0 < d := hdm.1.1
    have hm_pos : 0 < m := hdm.2.1
    have hdm_le : d * m ≤ N := (Nat.mul_le_mul_left d hdm.2.2).trans (Nat.mul_div_le N d)
    refine ⟨⟨d * m, d⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd_pos hm_pos, hdm_le⟩,
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right d m, (Nat.mul_pos hd_pos hm_pos).ne'⟩,
        hdm.1.2⟩⟩, ?_⟩
    dsimp only
    rw [Nat.mul_div_cancel_left m hd_pos]
  · intro _ _
    rfl

/-- Exact Vaughan sum identity in `ℂ` for any `x : ℝ`, parameters `U, V : ℕ` (`1 ≤ V`), and
arbitrary weight function `f : ℕ → ℂ`. -/
theorem vaughan_identity_sum (x : ℝ) {U V : ℕ} (hV : 1 ≤ V) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * f n =
      (∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), (Λ n : ℂ) * f n) +
      (∑ d ∈ Finset.Icc 1 U, (μ d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), (Real.log m : ℂ) * f (d * m)) -
      (∑ d ∈ Finset.Icc 1 (U * V), (vaughanTypeICoeff U V d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), f (d * m)) +
      (∑ m ∈ Finset.Ioc U (⌊x⌋₊ / V), (vaughanTypeIICoeff U m : ℂ) *
        ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) * f (m * k)) := by
  let N := ⌊x⌋₊
  have hpt : ∀ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * f n =
      ((if n ≤ V then (Λ n : ℂ) else 0) * f n) +
      ((∑ d ∈ n.divisors with d ≤ U, (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ)) * f n) -
      ((∑ d ∈ n.divisors with d ≤ U * V, (vaughanTypeICoeff U V d : ℂ)) * f n) +
      ((∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
        (vaughanTypeIICoeff U p.1 : ℂ) * (Λ p.2 : ℂ)) * f n) := by
    intro n _
    have hp : (Λ n : ℂ) =
        ((if n ≤ V then (Λ n : ℂ) else 0) +
          (∑ d ∈ n.divisors with d ≤ U, (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ)) -
          (∑ d ∈ n.divisors with d ≤ U * V, (vaughanTypeICoeff U V d : ℂ)) +
          (∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
            (vaughanTypeIICoeff U p.1 : ℂ) * (Λ p.2 : ℂ))) := by
      have hpR := congrArg Complex.ofReal (vaughan_identity_pointwise U V n)
      push_cast at hpR
      convert hpR using 2
      split_ifs <;> simp
    conv_lhs => rw [hp]
    ring
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hterm0 : ∑ n ∈ Finset.Icc 1 N, (if n ≤ V then (Λ n : ℂ) else 0) * f n =
      ∑ n ∈ Finset.Icc 1 (min N V), (Λ n : ℂ) * f n := by
    have hfilter : Finset.Icc 1 (min N V) = (Finset.Icc 1 N).filter (fun n => n ≤ V) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [hfilter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hterm1 : ∑ n ∈ Finset.Icc 1 N,
        (∑ d ∈ n.divisors with d ≤ U, (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ)) * f n =
      ∑ d ∈ Finset.Icc 1 U, (μ d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / d), (Real.log m : ℂ) * f (d * m) := by
    have hmul : ∑ n ∈ Finset.Icc 1 N,
          (∑ d ∈ n.divisors with d ≤ U, (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ)) * f n =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors with d ≤ U, (μ d : ℂ) * ((Real.log (n / d : ℕ) : ℂ) * f (d * (n / d))) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mul_div_cancel' hd.1.1]
      ring
    rw [hmul, sum_Icc_divisors_mul N U (fun d m => (μ d : ℂ) * ((Real.log m : ℂ) * f (d * m)))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
  have hterm2 : ∑ n ∈ Finset.Icc 1 N,
        (∑ d ∈ n.divisors with d ≤ U * V, (vaughanTypeICoeff U V d : ℂ)) * f n =
      ∑ d ∈ Finset.Icc 1 (U * V), (vaughanTypeICoeff U V d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / d), f (d * m) := by
    have hmul : ∑ n ∈ Finset.Icc 1 N,
          (∑ d ∈ n.divisors with d ≤ U * V, (vaughanTypeICoeff U V d : ℂ)) * f n =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors with d ≤ U * V, (vaughanTypeICoeff U V d : ℂ) * f (d * (n / d)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mul_div_cancel' hd.1.1]
    rw [hmul, sum_Icc_divisors_mul N (U * V) (fun d m => (vaughanTypeICoeff U V d : ℂ) * f (d * m))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
  have hterm3 : ∑ n ∈ Finset.Icc 1 N,
        (∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
          (vaughanTypeIICoeff U p.1 : ℂ) * (Λ p.2 : ℂ)) * f n =
      ∑ m ∈ Finset.Ioc U (N / V), (vaughanTypeIICoeff U m : ℂ) *
        ∑ k ∈ Finset.Ioc V (N / m), (Λ k : ℂ) * f (m * k) := by
    let gII : ℕ → ℕ → ℂ := fun m k =>
      if U < m ∧ V < k then (vaughanTypeIICoeff U m : ℂ) * (Λ k : ℂ) * f (m * k) else 0
    have hmul : ∑ n ∈ Finset.Icc 1 N,
          (∑ p ∈ Nat.divisorsAntidiagonal n with U < p.1 ∧ V < p.2,
            (vaughanTypeIICoeff U p.1 : ℂ) * (Λ p.2 : ℂ)) * f n =
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.divisors with m ≤ N / V, gII m (n / m) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_Icc] at hn
      rw [Finset.sum_mul, Finset.sum_filter,
        Nat.sum_divisorsAntidiagonal (f := fun m k =>
          if U < m ∧ V < k then (vaughanTypeIICoeff U m : ℂ) * (Λ k : ℂ) * f n else 0),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_dvd : m ∣ n := (Nat.mem_divisors.mp hm).1
      have hmn : m * (n / m) = n := Nat.mul_div_cancel' hm_dvd
      by_cases hcond : U < m ∧ V < n / m
      · have hm_le : m ≤ N / V := by
          refine (Nat.le_div_iff_mul_le hV).mpr ?_
          have h1 : m * V ≤ m * (n / m) := Nat.mul_le_mul_left m hcond.2.le
          rw [hmn] at h1
          exact h1.trans hn.2
        simp [gII, hm_le, hcond, hmn]
      · simp [gII, hcond]
    rw [hmul, sum_Icc_divisors_mul N (N / V) gII]
    have hfilter_m : Finset.Ioc U (N / V) = (Finset.Icc 1 (N / V)).filter (fun m => U < m) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hfilter_m, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hmU : U < m
    · simp only [hmU, ↓reduceIte]
      have hfilter_k : Finset.Ioc V (N / m) = (Finset.Icc 1 (N / m)).filter (fun k => V < k) := by
        ext k; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hfilter_k, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkV : V < k
      · simp only [gII, hmU, hkV, and_self, ↓reduceIte, mul_assoc]
      · simp [gII, hkV]
    · simp [gII, hmU]
  rw [hterm0, hterm1, hterm2, hterm3]

end VaughanAlgebraicIdentity

section DivisorSecondMomentAndLinearBounds

private def vaughanE (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * (α : ℂ) * Complex.I)

private lemma vaughanE_add (α β : ℝ) :
    vaughanE (α + β) = vaughanE α * vaughanE β := by
  simp only [vaughanE, Complex.ofReal_add, mul_add, add_mul, Complex.exp_add]

private lemma vaughanE_intCast (n : ℤ) : vaughanE (n : ℝ) = 1 := by
  simp only [vaughanE]
  have h : 2 * (Real.pi : ℂ) * (((n : ℤ) : ℝ) : ℂ) * Complex.I = (n : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

private lemma vaughanE_add_int (α : ℝ) (n : ℤ) : vaughanE (α + n) = vaughanE α := by
  rw [vaughanE_add, vaughanE_intCast, mul_one]

private lemma norm_vaughanE (α : ℝ) : ‖vaughanE α‖ = 1 := by
  have h : 2 * (Real.pi : ℂ) * (α : ℂ) * Complex.I = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [vaughanE, h, Complex.norm_exp_ofReal_mul_I]

private lemma vaughanE_nsmul (n : ℕ) (α : ℝ) : vaughanE ((n : ℝ) * α) = vaughanE α ^ n := by
  simp only [vaughanE, Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1; ring

private lemma star_vaughanE (α : ℝ) : star (vaughanE α) = vaughanE (-α) := by
  have h1 : 2 * (Real.pi : ℂ) * (α : ℂ) * Complex.I = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : 2 * (Real.pi : ℂ) * ((-α : ℝ) : ℂ) * Complex.I =
      ((-2 * Real.pi * α : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [vaughanE, vaughanE, h1, h2, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1; push_cast; ring

private def vDist (α : ℝ) : ℝ := |α - round α|

private lemma vDist_nonneg (α : ℝ) : 0 ≤ vDist α := abs_nonneg _

private lemma vDist_le_half (α : ℝ) : vDist α ≤ 1 / 2 := abs_sub_round α

private lemma vDist_le_abs_sub_int (α : ℝ) (n : ℤ) : vDist α ≤ |α - n| := round_le α n

private lemma vDist_add_int (α : ℝ) (n : ℤ) : vDist (α + n) = vDist α := by
  simp only [vDist, round_add_intCast, Int.cast_add]; ring_nf

private lemma vDist_neg (α : ℝ) : vDist (-α) = vDist α := by
  apply le_antisymm
  · calc vDist (-α) ≤ |-α - (-round α : ℤ)| := vDist_le_abs_sub_int (-α) (-round α)
      _ = |-(α - round α)| := by push_cast; ring_nf
      _ = vDist α := abs_neg _
  · calc vDist α ≤ |α - (-round (-α) : ℤ)| := vDist_le_abs_sub_int α (-round (-α))
      _ = |-(-α - round (-α))| := by push_cast; ring_nf
      _ = vDist (-α) := abs_neg _

private lemma vDist_add_le (α β : ℝ) : vDist (α + β) ≤ vDist α + vDist β := by
  calc vDist (α + β) ≤ |(α + β) - ((round α + round β : ℤ) : ℝ)| :=
        vDist_le_abs_sub_int (α + β) (round α + round β)
    _ = |(α - round α) + (β - round β)| := by push_cast; ring_nf
    _ ≤ |α - round α| + |β - round β| := abs_add_le _ _

private lemma vDist_sub_abs_le_add (α β : ℝ) : vDist α - |β| ≤ vDist (α + β) := by
  have h1 := vDist_add_le (α + β) (-β)
  rw [show α + β + -β = α by ring] at h1
  have h2 : vDist (-β) ≤ |β| := by
    rw [vDist_neg]
    exact (vDist_le_abs_sub_int β 0).trans_eq (by simp)
  linarith

private lemma vDist_eq_zero_iff (α : ℝ) : vDist α = 0 ↔ ∃ n : ℤ, α = n := by
  constructor
  · intro h; exact ⟨round α, sub_eq_zero.mp (abs_eq_zero.mp h)⟩
  · rintro ⟨n, rfl⟩; simp [vDist]

private lemma vDist_pos_iff (α : ℝ) : 0 < vDist α ↔ ∀ n : ℤ, α ≠ n := by
  rw [lt_iff_le_and_ne, and_iff_right (vDist_nonneg α), ne_comm, ne_eq, vDist_eq_zero_iff]
  push Not; rfl

private lemma vDist_intCast_div_natCast {z : ℤ} {q : ℕ} (hq : 0 < q) :
    vDist ((z : ℝ) / (q : ℝ)) =
      ((min (Int.natMod z q) (q - Int.natMod z q) : ℕ) : ℝ) / (q : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmod : z = (z / (q : ℤ)) * (q : ℤ) + ((Int.natMod z q : ℕ) : ℤ) := by
    have hz : (Int.natMod z q : ℤ) = z % (q : ℤ) := by
      have h0 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg z (by exact_mod_cast hq.ne')
      rw [Int.natMod, Int.toNat_of_nonneg h0]
    rw [hz, Int.emod_def]; ring
  have hsplit : (z : ℝ) / (q : ℝ) = ((Int.natMod z q : ℕ) : ℝ) / (q : ℝ) + ((z / (q : ℤ)) : ℤ) := by
    have hz : (z : ℝ) = ((z / (q : ℤ)) : ℤ) * (q : ℝ) + ((Int.natMod z q : ℕ) : ℝ) := by
      exact_mod_cast hmod
    rw [hz]; field_simp [hq0]; ring
  rw [hsplit, vDist_add_int, vDist, abs_sub_round_div_natCast_eq (α := ℝ)]
  have hlt : Int.natMod z q < q := by
    dsimp only [Int.natMod]
    have h0 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg z (by exact_mod_cast hq.ne')
    have hq_lt : z % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos z (by exact_mod_cast hq)
    omega
  rw [Nat.mod_eq_of_lt hlt]

private lemma norm_one_sub_vaughanE (α : ℝ) :
    ‖1 - vaughanE α‖ = 2 * Real.sin (Real.pi * vDist α) := by
  have habs_sin : |Real.sin (Real.pi * α)| = Real.sin (Real.pi * vDist α) := by
    have hsplit : Real.pi * α = Real.pi * (α - round α) + (round α : ℤ) * Real.pi := by ring
    rw [hsplit, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    have hbd : |Real.pi * (α - round α)| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      calc Real.pi * |α - round α| ≤ Real.pi * (1 / 2) :=
            mul_le_mul_of_nonneg_left (vDist_le_half α) Real.pi_pos.le
        _ ≤ Real.pi := by linarith [Real.pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hbd, abs_mul, abs_of_pos Real.pi_pos]
    rfl
  have hsq : ‖1 - vaughanE α‖ ^ 2 = (2 * |Real.sin (Real.pi * α)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hexp : vaughanE α = Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
      simp only [vaughanE]; congr 1; push_cast; ring
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
  have h1 : 0 ≤ ‖1 - vaughanE α‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * α)| := by positivity
  have hnorm : ‖1 - vaughanE α‖ = 2 * |Real.sin (Real.pi * α)| := by nlinarith
  rw [hnorm, habs_sin]

private lemma four_mul_vDist_le_norm_one_sub_vaughanE (α : ℝ) :
    4 * vDist α ≤ ‖1 - vaughanE α‖ := by
  rw [norm_one_sub_vaughanE]
  have h0 : 0 ≤ Real.pi * vDist α := mul_nonneg Real.pi_pos.le (vDist_nonneg α)
  have h1 : Real.pi * vDist α ≤ Real.pi / 2 := by
    calc Real.pi * vDist α ≤ Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left (vDist_le_half α) Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hsin := Real.mul_le_sin h0 h1
  have h2 : 2 / Real.pi * (Real.pi * vDist α) = 2 * vDist α := by
    field_simp [Real.pi_ne_zero]
  rw [h2] at hsin
  linarith

private lemma vaughanE_ne_one_iff (α : ℝ) : vaughanE α ≠ 1 ↔ ∀ n : ℤ, α ≠ n := by
  rw [← vDist_pos_iff]
  constructor
  · intro hne
    by_contra hle
    have h0 : vDist α = 0 := le_antisymm (not_lt.mp hle) (vDist_nonneg α)
    have hnorm : ‖1 - vaughanE α‖ = 0 := by rw [norm_one_sub_vaughanE, h0]; simp
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm
  · intro hpos heq
    have hnorm : ‖1 - vaughanE α‖ = 0 := by rw [heq, sub_self, norm_zero]
    linarith [four_mul_vDist_le_norm_one_sub_vaughanE α]

private def vLinBound (Y θ : ℝ) : ℝ :=
  if vDist θ = 0 then Y else min Y (1 / (2 * vDist θ))

private lemma vLinBound_nonneg {Y : ℝ} (hY : 0 ≤ Y) (θ : ℝ) : 0 ≤ vLinBound Y θ := by
  unfold vLinBound
  split_ifs
  · exact hY
  · exact le_min hY (by positivity [vDist_nonneg θ])

private lemma vLinBound_le_left (Y θ : ℝ) : vLinBound Y θ ≤ Y := by
  unfold vLinBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private lemma vLinBound_mono_left {Y₁ Y₂ : ℝ} (hY : Y₁ ≤ Y₂) (θ : ℝ) :
    vLinBound Y₁ θ ≤ vLinBound Y₂ θ := by
  unfold vLinBound
  split_ifs
  · exact hY
  · exact min_le_min hY le_rfl

private lemma vLinBound_neg (Y θ : ℝ) : vLinBound Y (-θ) = vLinBound Y θ := by
  simp [vLinBound, vDist_neg]

private lemma norm_sum_Ioc_vaughanE_le_vLinBound (α : ℝ) {A B : ℕ} {Y : ℝ}
    (hY : ((B - A : ℕ) : ℝ) ≤ Y) :
    ‖∑ n ∈ Finset.Ioc A B, vaughanE (α * n)‖ ≤ vLinBound Y α := by
  rcases le_or_gt B A with hBA | hAB
  · have hmt : Finset.Ioc A B = ∅ := Finset.Ioc_eq_empty (not_lt.mpr hBA)
    rw [hmt, Finset.sum_empty, norm_zero]
    have hY0 : 0 ≤ Y := (Nat.cast_nonneg (B - A)).trans hY
    exact vLinBound_nonneg hY0 α
  · have htriv : ‖∑ n ∈ Finset.Ioc A B, vaughanE (α * n)‖ ≤ Y := by
      calc ‖∑ n ∈ Finset.Ioc A B, vaughanE (α * n)‖
          ≤ ∑ n ∈ Finset.Ioc A B, ‖vaughanE (α * n)‖ := norm_sum_le _ _
        _ = ((Finset.Ioc A B).card : ℝ) := by simp [norm_vaughanE]
        _ = ((B - A : ℕ) : ℝ) := by rw [Nat.card_Ioc]
        _ ≤ Y := hY
    by_cases h0 : vDist α = 0
    · simpa [vLinBound, h0] using htriv
    · have hα : ∀ n : ℤ, α ≠ n := (vDist_pos_iff α).mp
        (lt_of_le_of_ne (vDist_nonneg α) (Ne.symm h0))
      have he_ne : vaughanE α ≠ 1 := (vaughanE_ne_one_iff α).mpr hα
      let N := B - A
      have hB_eq : B = A + N := by omega
      have hbij : ∑ n ∈ Finset.Ioc A B, vaughanE (α * n) =
          vaughanE (α * ((A + 1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range N, vaughanE α ^ k := by
        calc ∑ n ∈ Finset.Ioc A B, vaughanE (α * n)
            = ∑ k ∈ Finset.range N, vaughanE (α * ((A + 1 + k : ℕ) : ℝ)) := by
              refine Finset.sum_bij (fun n _ => n - (A + 1)) ?_ ?_ ?_ ?_
              · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_range]; omega
              · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ioc] at hn₁ hn₂; omega
              · intro k hk
                simp only [Finset.mem_range] at hk
                refine ⟨A + 1 + k, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro n hn
                simp only [Finset.mem_Ioc] at hn
                congr 2; exact_mod_cast (by omega : A + 1 + (n - (A + 1)) = n).symm
          _ = vaughanE (α * ((A + 1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range N, vaughanE α ^ k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Nat.cast_add, mul_add, vaughanE_add, mul_comm α (k : ℝ), vaughanE_nsmul]
      have hsum_eq : ∑ n ∈ Finset.Ioc A B, vaughanE (α * n) =
          vaughanE (α * ((A + 1 : ℕ) : ℝ)) * (vaughanE α ^ N - 1) / (vaughanE α - 1) := by
        rw [hbij, geom_sum_eq he_ne, mul_div_assoc]
      have hdist_pos : 0 < vDist α := lt_of_le_of_ne (vDist_nonneg α) (Ne.symm h0)
      have hden : 4 * vDist α ≤ ‖1 - vaughanE α‖ := four_mul_vDist_le_norm_one_sub_vaughanE α
      have hinv_bd : ‖∑ n ∈ Finset.Ioc A B, vaughanE (α * n)‖ ≤ 1 / (2 * vDist α) := by
        rw [hsum_eq, norm_div, norm_mul, norm_vaughanE, one_mul, norm_sub_rev (vaughanE α) 1]
        have hnum : ‖vaughanE α ^ N - 1‖ ≤ 2 := by
          calc ‖vaughanE α ^ N - 1‖ ≤ ‖vaughanE α ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_pow, norm_vaughanE, one_pow, norm_one]; norm_num
        calc ‖vaughanE α ^ N - 1‖ / ‖1 - vaughanE α‖
            ≤ 2 / (4 * vDist α) := div_le_div₀ zero_le_two hnum (by positivity) hden
          _ = 1 / (2 * vDist α) := by ring
      simp only [vLinBound, h0, ↓reduceIte]
      exact le_min htriv hinv_bd

private lemma norm_sum_Icc_one_vaughanE_le_vLinBound (α : ℝ) (N : ℕ) {Y : ℝ}
    (hY : (N : ℝ) ≤ Y) :
    ‖∑ n ∈ Finset.Icc 1 N, vaughanE (α * n)‖ ≤ vLinBound Y α := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [← hIoc]
  exact norm_sum_Ioc_vaughanE_le_vLinBound α (by simpa using hY)

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

private lemma one_add_log_half_le_log_two_mul {q : ℕ} (hq : 2 ≤ q) :
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
      rw [show (1 / 2 : ℝ) = -(-(1 / 2 : ℝ)) by ring, Real.exp_neg,
        inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    have hexp : Real.exp 1 < 4 := by
      have hsq : Real.exp 1 = Real.exp (1 / 2 : ℝ) ^ 2 := by
        rw [sq, ← Real.exp_add]; congr 1; norm_num
      rw [hsq]; nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have hlog4 : 1 < Real.log 4 := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hexp
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlog2q : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
    Real.log_mul two_ne_zero hq0.ne'
  linarith

private lemma sum_Ico_inv_min_le {q : ℕ} (hq : 2 ≤ q) :
    ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) ≤
      2 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  let m := q / 2
  have hm_pos : 1 ≤ m := by omega
  have hsplit : Finset.Ico 1 q = Finset.Icc 1 m ∪ Finset.Ioc m (q - 1) := by
    ext s; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioc m (q - 1)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hs1 hs2; omega
  have h1 : ∑ s ∈ Finset.Icc 1 m, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) =
      (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [Finset.mem_Icc] at hs
    rw [min_eq_left (by omega), div_eq_mul_inv]
  have h2 : ∑ s ∈ Finset.Ioc m (q - 1), (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) ≤
      (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ := by
    have hbij : ∑ s ∈ Finset.Ioc m (q - 1), (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) =
        ∑ b ∈ Finset.Ico 1 (q - m), (q : ℝ) / (b : ℝ) := by
      refine Finset.sum_bij (fun s _ => q - s) ?_ ?_ ?_ ?_
      · intro s hs; simp only [Finset.mem_Ioc] at hs; simp only [Finset.mem_Ico]; omega
      · intro s₁ hs₁ s₂ hs₂ h; simp only [Finset.mem_Ioc] at hs₁ hs₂; omega
      · intro b hb; simp only [Finset.mem_Ico] at hb; exact ⟨q - b, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro s hs; simp only [Finset.mem_Ioc] at hs; rw [min_eq_right (by omega)]
    have hsub : Finset.Ico 1 (q - m) ⊆ Finset.Icc 1 m := by
      intro b hb; simp only [Finset.mem_Ico] at hb; simp only [Finset.mem_Icc]; omega
    rw [hbij]
    calc ∑ b ∈ Finset.Ico 1 (q - m), (q : ℝ) / (b : ℝ)
        ≤ ∑ b ∈ Finset.Icc 1 m, (q : ℝ) / (b : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (q : ℝ) * ∑ b ∈ Finset.Icc 1 m, (b : ℝ)⁻¹ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => div_eq_mul_inv _ _
  have hm_R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
  have hharm0 := sum_inv_le_one_add_log hm_R
  rw [Nat.floor_natCast] at hharm0
  have hharm := hharm0.trans (one_add_log_half_le_log_two_mul hq)
  rw [hsplit, Finset.sum_union hdisj]
  calc ∑ s ∈ Finset.Icc 1 m, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) +
        ∑ s ∈ Finset.Ioc m (q - 1), (q : ℝ) / ((min s (q - s) : ℕ) : ℝ)
      ≤ (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ +
          (q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹ := add_le_add h1.le h2
    _ = 2 * ((q : ℝ) * ∑ s ∈ Finset.Icc 1 m, (s : ℝ)⁻¹) := by ring
    _ ≤ 2 * ((q : ℝ) * Real.log (2 * (q : ℝ))) := by gcongr
    _ = 2 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by ring

private lemma sum_Icc_vLinBound_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n) ≤
      9 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hlog_pos : 0 < Real.log (2 * (q : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp; positivity
  rcases eq_or_lt_of_le hq with rfl | hq2
  · calc ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n)
        ≤ ∑ _n ∈ Finset.Icc 1 X, Y :=
          Finset.sum_le_sum fun n _ => vLinBound_le_left Y (α * n)
      _ = (X : ℝ) * Y := by simp
      _ ≤ 9 * (((X : ℝ) + (1 : ℕ)) * Real.log (2 * ((1 : ℕ) : ℝ)) + (X : ℝ) * Y / (1 : ℕ)) := by
          have h1 : (0 : ℝ) ≤ ((X : ℝ) + 1) * Real.log 2 := by positivity
          have h2 : (0 : ℝ) ≤ (X : ℝ) * Y := mul_nonneg (Nat.cast_nonneg X) hY
          simp only [Nat.cast_one, mul_one, div_one]
          linarith
  have hq2' : 2 ≤ q := hq2
  let θ : ℝ := α - (a : ℝ) / q
  have hθ : |θ| ≤ 1 / (q : ℝ) ^ 2 := hα
  by_cases hsmall : 2 * X < q
  · have hbound_term : ∀ n ∈ Finset.Icc 1 X,
        vLinBound Y (α * n) ≤
          (q : ℝ) / ((min (Int.natMod (a * (n : ℤ)) q) (q - Int.natMod (a * (n : ℤ)) q) : ℕ) : ℝ) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn_lt : n < q := by omega
      have hndiv : ¬ (q : ℤ) ∣ a * (n : ℤ) := by
        intro hdvd
        have hdvd' : q ∣ a.natAbs * n := by
          have h1 := Int.natCast_dvd.mp hdvd
          simpa [Int.natAbs_mul] using h1
        exact absurd (Nat.le_of_dvd hn.1 (hcop.symm.dvd_of_dvd_mul_left hdvd')) (not_le.mpr hn_lt)
      let s := Int.natMod (a * (n : ℤ)) q
      have hs_pos : 1 ≤ s := by
        by_contra hs0
        have heq0 : (a * (n : ℤ)) % (q : ℤ) = 0 := by
          have hnn : 0 ≤ (a * (n : ℤ)) % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq0.ne')
          dsimp only [s, Int.natMod] at hs0; omega
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
      have hdist_base : vDist (((a * (n : ℤ) : ℤ) : ℝ) / q) = (m : ℝ) / q :=
        vDist_intCast_div_natCast (z := a * (n : ℤ)) (by omega : 0 < q)
      have herr_bd : |θ * (n : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
        have hn_half : (n : ℝ) ≤ (q : ℝ) / 2 := by
          have : (2 : ℝ) * n ≤ q := by exact_mod_cast (by omega : 2 * n ≤ q)
          linarith
        calc |θ| * (n : ℝ) ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) :=
              mul_le_mul hθ hn_half (Nat.cast_nonneg n) (by positivity)
          _ = 1 / (2 * (q : ℝ)) := by field_simp [hq0.ne']
      have hdist_lb : (m : ℝ) / (2 * (q : ℝ)) ≤ vDist (α * n) := by
        rw [hsplit_an]
        have h1 := vDist_sub_abs_le_add (((a * (n : ℤ) : ℤ) : ℝ) / q) (θ * n)
        rw [hdist_base] at h1
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
        calc (m : ℝ) / (2 * (q : ℝ))
            = (m : ℝ) / q - (m : ℝ) / (2 * q) := by ring
          _ ≤ (m : ℝ) / q - 1 / (2 * q) := by gcongr
          _ ≤ (m : ℝ) / q - |θ * n| := by gcongr
          _ ≤ vDist (((a * (n : ℤ) : ℤ) : ℝ) / q + θ * n) := h1
      have hdist_pos : 0 < vDist (α * n) := lt_of_lt_of_le (by positivity) hdist_lb
      simp only [vLinBound, hdist_pos.ne', ↓reduceIte]
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hm_pos)]
      have hmul : (m : ℝ) ≤ 2 * (q : ℝ) * vDist (α * n) := by
        have := mul_le_mul_of_nonneg_left hdist_lb (by positivity : (0 : ℝ) ≤ 2 * q)
        rw [mul_div_cancel₀ _ (by positivity)] at this
        exact this
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
        ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n) ≤
          ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
      calc ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n)
          ≤ ∑ n ∈ Finset.Icc 1 X,
              (q : ℝ) / ((min (Int.natMod (a * (n : ℤ)) q) (q - Int.natMod (a * (n : ℤ)) q) : ℕ) : ℝ) :=
            Finset.sum_le_sum hbound_term
        _ = ∑ s ∈ (Finset.Icc 1 X).image (fun n : ℕ => Int.natMod (a * (n : ℤ)) q),
              (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
            symm; exact Finset.sum_image (fun n₁ hn₁ n₂ hn₂ h => hinj n₁ hn₁ n₂ hn₂ h)
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
    calc ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n)
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
      · simp only [Finset.mem_range, K]; exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.2)
      · exact Finset.mem_range.mpr (Nat.mod_lt n (by omega))
      · dsimp only; linarith [Nat.div_add_mod n q]
    have hsum_sub :
        ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n) ≤
          ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range q, vLinBound Y (α * ((k * q + r : ℕ) : ℝ)) := by
      calc ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n)
          ≤ ∑ n ∈ (Finset.range K ×ˢ Finset.range q).image (fun p => p.1 * q + p.2),
              vLinBound Y (α * n) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vLinBound_nonneg hY _
        _ ≤ ∑ p ∈ Finset.range K ×ˢ Finset.range q, vLinBound Y (α * ((p.1 * q + p.2 : ℕ) : ℝ)) :=
            Finset.sum_image_le_of_nonneg fun _ _ => vLinBound_nonneg hY _
        _ = ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range q,
              vLinBound Y (α * ((k * q + r : ℕ) : ℝ)) := by rw [Finset.sum_product]
    have hblock : ∀ k : ℕ,
        ∑ r ∈ Finset.range q, vLinBound Y (α * ((k * q + r : ℕ) : ℝ)) ≤
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
          vLinBound Y (α * ((k * q + r : ℕ) : ℝ)) ≤
            if min (sFun r) (q - sFun r) ≤ 1 then Y
            else 2 * (q : ℝ) / ((min (sFun r) (q - sFun r) : ℕ) : ℝ) := by
        intro r
        split_ifs with hm1
        · exact vLinBound_le_left Y _
        · have hm2 : 2 ≤ min (sFun r) (q - sFun r) := by omega
          let m := min (sFun r) (q - sFun r)
          let η : ℝ := θ * (k : ℝ) * (q : ℝ) - (u : ℝ) / (q : ℝ)
          let εr : ℝ := η + θ * (r : ℝ)
          have hsplit : α * ((k * q + r : ℕ) : ℝ) =
              (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ) + εr) + ((a * (k : ℤ) : ℤ) : ℝ) := by
            simp only [θ, εr, η]; push_cast; field_simp [hq0.ne']; ring
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
          have hdist_base : vDist (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ)) = (m : ℝ) / (q : ℝ) :=
            vDist_intCast_div_natCast (z := a * (r : ℤ) + u) (by omega : 0 < q)
          have hdist_lb : (m : ℝ) / (4 * (q : ℝ)) ≤ vDist (α * ((k * q + r : ℕ) : ℝ)) := by
            rw [hsplit, vDist_add_int]
            have h1 := vDist_sub_abs_le_add (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ)) εr
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
              _ ≤ vDist (((a * (r : ℤ) + u : ℤ) : ℝ) / (q : ℝ) + εr) := h1
          have hdist_pos : 0 < vDist (α * ((k * q + r : ℕ) : ℝ)) :=
            lt_of_lt_of_le (by positivity) hdist_lb
          simp only [vLinBound, hdist_pos.ne', ↓reduceIte]
          refine (min_le_right _ _).trans ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hmul : (m : ℝ) ≤ 4 * (q : ℝ) * vDist (α * ((k * q + r : ℕ) : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hdist_lb (by positivity : (0 : ℝ) ≤ 4 * q)
            rw [mul_div_cancel₀ _ (by positivity)] at this
            exact this
          linarith
      calc ∑ r ∈ Finset.range q, vLinBound Y (α * ((k * q + r : ℕ) : ℝ))
          = ∑ r : Fin q, vLinBound Y (α * ((k * q + r : ℕ) : ℝ)) := (Fin.sum_univ_eq_sum_range _ q).symm
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
            have h0_val : (if min (0 : ℕ) (q - 0) ≤ 1 then Y else 2 * (q : ℝ) / ((min 0 (q - 0) : ℕ) : ℝ)) = Y := by simp
            have h0_val' : (if min (0 : ℕ) (q - 0) ≤ 1 then Y else 0) = Y := by simp
            rw [h0_val, h0_val', add_assoc]
            refine add_le_add le_rfl ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun s _ => ?_
            split_ifs
            · exact le_add_of_nonneg_right (by positivity)
            · rw [zero_add]
        _ ≤ 3 * Y + 4 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
            have hcount : ∑ s ∈ Finset.range q, (if min s (q - s) ≤ 1 then Y else 0) ≤ 3 * Y := by
              have hsub_bad :
                  (Finset.range q).filter (fun s => min s (q - s) ≤ 1) ⊆ ({0, 1, q - 1} : Finset ℕ) := by
                intro s hs
                simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
                  Finset.mem_singleton] at hs ⊢; omega
              calc ∑ s ∈ Finset.range q, (if min s (q - s) ≤ 1 then Y else 0)
                  = ∑ _s ∈ (Finset.range q).filter (fun s => min s (q - s) ≤ 1), Y := by
                    rw [Finset.sum_filter]
                _ = (((Finset.range q).filter (fun s => min s (q - s) ≤ 1)).card : ℝ) * Y := by simp
                _ ≤ (({0, 1, q - 1} : Finset ℕ).card : ℝ) * Y :=
                    mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub_bad) hY
                _ ≤ 3 * Y := by gcongr; norm_cast; exact Finset.card_le_three
            have hrec : ∑ s ∈ Finset.Ico 1 q, 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) ≤
                4 * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
              have hrewrite : ∑ s ∈ Finset.Ico 1 q, 2 * (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) =
                  2 * ∑ s ∈ Finset.Ico 1 q, (q : ℝ) / ((min s (q - s) : ℕ) : ℝ) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
              rw [hrewrite]; linarith [sum_Ico_inv_min_le hq2']
            exact add_le_add hcount hrec
    have hK_le : (K : ℝ) ≤ (X : ℝ) / q + 1 := by
      have hdiv : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := Nat.cast_div_le
      simp only [K, Nat.cast_add, Nat.cast_one]; linarith
    have hK_le_three : (K : ℝ) ≤ 3 * ((X : ℝ) / q) := by
      have h1 : (1 : ℝ) ≤ 2 * ((X : ℝ) / q) := by
        rw [← mul_div_assoc, le_div_iff₀ hq0]; linarith
      linarith
    calc ∑ n ∈ Finset.Icc 1 X, vLinBound Y (α * n)
        ≤ ∑ _k ∈ Finset.range K, (3 * Y + 4 * (q : ℝ) * Real.log (2 * (q : ℝ))) :=
          hsum_sub.trans (Finset.sum_le_sum fun k _ => hblock k)
      _ = (K : ℝ) * (3 * Y) + (K : ℝ) * (4 * (q : ℝ) * Real.log (2 * (q : ℝ))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ (3 * ((X : ℝ) / q)) * (3 * Y) +
            ((X : ℝ) / q + 1) * (4 * (q : ℝ) * Real.log (2 * (q : ℝ))) :=
          add_le_add
            (mul_le_mul_of_nonneg_right hK_le_three (by positivity))
            (mul_le_mul_of_nonneg_right hK_le (by positivity))
      _ = 4 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ))) + 9 * ((X : ℝ) * Y / q) := by
          field_simp [hq0.ne']; ring
      _ ≤ 9 * (((X : ℝ) + q) * Real.log (2 * (q : ℝ)) + (X : ℝ) * Y / q) := by
          have h1 : 0 ≤ ((X : ℝ) + q) * Real.log (2 * (q : ℝ)) := by positivity
          have h2 : 0 ≤ (X : ℝ) * Y / q := by positivity
          linarith

/-- Elementary second-moment bound for the divisor function `d(m) = (Nat.divisors m).card`:
`∑_{1 ≤ m ≤ Y} d(m)^2 ≤ Y * (1 + log (max Y 1))^3`. -/
theorem sum_Icc_card_divisors_sq_le (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, ((Nat.divisors m).card : ℝ) ^ 2 ≤
      (Y : ℝ) * (1 + Real.log (max Y 1 : ℕ)) ^ 3 := by
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp
  · have hmax : max Y 1 = Y := max_eq_left hY
    rw [hmax]
    let B := Finset.Icc 1 Y
    have hsq : ∀ m ∈ B, ((Nat.divisors m).card : ℝ) ^ 2 =
        ∑ p ∈ m.divisors ×ˢ m.divisors, (1 : ℝ) := by
      intro m _
      simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul, mul_one, Nat.cast_mul, sq]
    have hswap : ∑ m ∈ B, ((Nat.divisors m).card : ℝ) ^ 2 =
        ∑ p ∈ B ×ˢ B, (((B.filter (fun m => Nat.lcm p.1 p.2 ∣ m)).card : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl hsq]
      have hcomm :
          ∑ m ∈ B, ∑ p ∈ m.divisors ×ˢ m.divisors, (1 : ℝ) =
            ∑ m ∈ B, ∑ p ∈ B ×ˢ B, if Nat.lcm p.1 p.2 ∣ m then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hm_le : m ≤ Y := (Finset.mem_Icc.mp hm).2
        have hsub : m.divisors ×ˢ m.divisors ⊆ B ×ˢ B := by
          intro p hp
          simp only [Finset.mem_product, Nat.mem_divisors] at hp
          refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hp.1.1 hm_pos,
            (Nat.le_of_dvd hm_pos hp.1.1).trans hm_le⟩,
            Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hp.2.1 hm_pos,
              (Nat.le_of_dvd hm_pos hp.2.1).trans hm_le⟩⟩
        have hfilt : (B ×ˢ B).filter (fun p => Nat.lcm p.1 p.2 ∣ m) = m.divisors ×ˢ m.divisors := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hlcm⟩
            exact ⟨⟨(Nat.dvd_lcm_left p.1 p.2).trans hlcm, hm_pos.ne'⟩,
              ⟨(Nat.dvd_lcm_right p.1 p.2).trans hlcm, hm_pos.ne'⟩⟩
          · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
            exact ⟨⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos h1 hm_pos, (Nat.le_of_dvd hm_pos h1).trans hm_le⟩,
              Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos h2 hm_pos, (Nat.le_of_dvd hm_pos h2).trans hm_le⟩⟩,
              Nat.lcm_dvd h1 h2⟩
        rw [← hfilt, Finset.sum_filter]
      rw [hcomm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard_le : ∀ p ∈ B ×ˢ B,
        (((B.filter (fun m => Nat.lcm p.1 p.2 ∣ m)).card : ℕ) : ℝ) ≤
          (Y : ℝ) / (Nat.lcm p.1 p.2 : ℝ) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_Icc, B] at hp
      let L := Nat.lcm p.1 p.2
      have hL_pos : 0 < L := Nat.lcm_pos hp.1.1 hp.2.1
      have hinj : Finset.card (B.filter (fun m => L ∣ m)) ≤ (Finset.Icc 1 (Y / L)).card := by
        refine Finset.card_le_card_of_injOn (fun m => m / L) ?_ ?_
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, B] at hm
          exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm.1.1 hm.2) hL_pos,
            Nat.div_le_div_right hm.1.2⟩
        · intro m₁ hm₁ m₂ hm₂ h
          dsimp only at h
          simp only [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
          calc m₁ = L * (m₁ / L) := (Nat.mul_div_cancel' hm₁.2).symm
            _ = L * (m₂ / L) := by rw [h]
            _ = m₂ := Nat.mul_div_cancel' hm₂.2
      rw [Nat.card_Icc, Nat.add_sub_cancel] at hinj
      have hinjR : ((B.filter (fun m => L ∣ m)).card : ℝ) ≤ ((Y / L : ℕ) : ℝ) := by
        exact_mod_cast hinj
      exact hinjR.trans (Nat.cast_div_le (m := Y) (n := L))
    let φ : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun p => (Nat.gcd p.1 p.2, (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2))
    have hφ_inj : ∀ p₁ ∈ B ×ˢ B, ∀ p₂ ∈ B ×ˢ B, φ p₁ = φ p₂ → p₁ = p₂ := by
      intro p₁ _ p₂ _ heq
      have hg : Nat.gcd p₁.1 p₁.2 = Nat.gcd p₂.1 p₂.2 := congrArg Prod.fst heq
      have hu : p₁.1 / Nat.gcd p₁.1 p₁.2 = p₂.1 / Nat.gcd p₂.1 p₂.2 :=
        congrArg (fun x => x.2.1) heq
      have hv : p₁.2 / Nat.gcd p₁.1 p₁.2 = p₂.2 / Nat.gcd p₂.1 p₂.2 :=
        congrArg (fun x => x.2.2) heq
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = Nat.gcd p₁.1 p₁.2 * (p₁.1 / Nat.gcd p₁.1 p₁.2) :=
              (Nat.mul_div_cancel' (Nat.gcd_dvd_left p₁.1 p₁.2)).symm
          _ = Nat.gcd p₂.1 p₂.2 * (p₂.1 / Nat.gcd p₂.1 p₂.2) := by rw [hu, hg]
          _ = p₂.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left p₂.1 p₂.2)
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = Nat.gcd p₁.1 p₁.2 * (p₁.2 / Nat.gcd p₁.1 p₁.2) :=
              (Nat.mul_div_cancel' (Nat.gcd_dvd_right p₁.1 p₁.2)).symm
          _ = Nat.gcd p₂.1 p₂.2 * (p₂.2 / Nat.gcd p₂.1 p₂.2) := by rw [hv, hg]
          _ = p₂.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right p₂.1 p₂.2)
      exact Prod.ext h1 h2
    have hφ_mem : (B ×ˢ B).image φ ⊆ B ×ˢ (B ×ˢ B) := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨p, hp, rfl⟩
      simp only [Finset.mem_product, Finset.mem_Icc, B] at hp ⊢
      have hg_pos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hp.1.1
      have hg_le : Nat.gcd p.1 p.2 ≤ Y :=
        (Nat.le_of_dvd hp.1.1 (Nat.gcd_dvd_left p.1 p.2)).trans hp.1.2
      exact ⟨⟨hg_pos, hg_le⟩,
        ⟨⟨Nat.div_pos (Nat.le_of_dvd hp.1.1 (Nat.gcd_dvd_left p.1 p.2)) hg_pos,
          (Nat.div_le_self p.1 _).trans hp.1.2⟩,
        ⟨Nat.div_pos (Nat.le_of_dvd hp.2.1 (Nat.gcd_dvd_right p.1 p.2)) hg_pos,
          (Nat.div_le_self p.2 _).trans hp.2.2⟩⟩⟩
    have hlcm_eq : ∀ p ∈ B ×ˢ B,
        (Nat.lcm p.1 p.2 : ℝ) = ((φ p).1 : ℝ) * ((φ p).2.1 : ℝ) * ((φ p).2.2 : ℝ) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_Icc, B] at hp
      have hg_lcm := Nat.gcd_mul_lcm p.1 p.2
      have h1 : p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
      have h2 : p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
      have hmul : Nat.gcd p.1 p.2 * Nat.lcm p.1 p.2 =
          Nat.gcd p.1 p.2 * (Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) * (p.2 / Nat.gcd p.1 p.2)) := by
        calc Nat.gcd p.1 p.2 * Nat.lcm p.1 p.2 = p.1 * p.2 := hg_lcm
          _ = (Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2)) *
                (Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2)) := by rw [← h1, ← h2]
          _ = Nat.gcd p.1 p.2 * (Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) * (p.2 / Nat.gcd p.1 p.2)) := by ring
      have hg_pos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hp.1.1
      exact_mod_cast Nat.eq_of_mul_eq_mul_left hg_pos hmul
    have hY_R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hharm := sum_inv_le_one_add_log hY_R
    rw [Nat.floor_natCast] at hharm
    have hharm_nn : 0 ≤ ∑ n ∈ B, (n : ℝ)⁻¹ :=
      Finset.sum_nonneg fun _ _ => by positivity
    calc ∑ m ∈ B, ((Nat.divisors m).card : ℝ) ^ 2
        = ∑ p ∈ B ×ˢ B, (((B.filter (fun m => Nat.lcm p.1 p.2 ∣ m)).card : ℕ) : ℝ) := hswap
      _ ≤ ∑ p ∈ B ×ˢ B, (Y : ℝ) / (Nat.lcm p.1 p.2 : ℝ) := Finset.sum_le_sum hcard_le
      _ = ∑ p ∈ B ×ˢ B, (Y : ℝ) / (((φ p).1 : ℝ) * ((φ p).2.1 : ℝ) * ((φ p).2.2 : ℝ)) := by
          refine Finset.sum_congr rfl fun p hp => ?_; rw [hlcm_eq p hp]
      _ = ∑ t ∈ (B ×ˢ B).image φ, (Y : ℝ) / ((t.1 : ℝ) * (t.2.1 : ℝ) * (t.2.2 : ℝ)) := by
          symm; exact Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hφ_inj p₁ hp₁ p₂ hp₂ h)
      _ ≤ ∑ t ∈ B ×ˢ (B ×ˢ B), (Y : ℝ) / ((t.1 : ℝ) * (t.2.1 : ℝ) * (t.2.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hφ_mem fun _ _ _ => by positivity
      _ = (Y : ℝ) * (∑ n ∈ B, (n : ℝ)⁻¹) ^ 3 := by
          rw [Finset.sum_product]
          simp_rw [Finset.sum_product]
          simp only [div_eq_mul_inv, mul_inv, mul_assoc]
          have hliftY :
              ∑ g ∈ B, ∑ u ∈ B, ∑ v ∈ B, (Y : ℝ) * ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹)) =
                (Y : ℝ) * ∑ g ∈ B, ∑ u ∈ B, ∑ v ∈ B, (g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹) := by
            calc ∑ g ∈ B, ∑ u ∈ B, ∑ v ∈ B, (Y : ℝ) * ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹))
                = ∑ g ∈ B, ∑ u ∈ B, (Y : ℝ) * ∑ v ∈ B, (g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹) := by
                    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun u _ => ?_
                    rw [← Finset.mul_sum]
              _ = ∑ g ∈ B, (Y : ℝ) * ∑ u ∈ B, ∑ v ∈ B, (g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹) := by
                    refine Finset.sum_congr rfl fun g _ => by rw [← Finset.mul_sum]
              _ = (Y : ℝ) * ∑ g ∈ B, ∑ u ∈ B, ∑ v ∈ B, (g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹) := by
                    rw [← Finset.mul_sum]
          rw [hliftY]
          congr 1
          rw [pow_three]
          calc ∑ g ∈ B, ∑ u ∈ B, ∑ v ∈ B, (g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * (v : ℝ)⁻¹)
              = ∑ g ∈ B, ∑ u ∈ B, (g : ℝ)⁻¹ * ((u : ℝ)⁻¹ * ∑ v ∈ B, (v : ℝ)⁻¹) := by
                  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun u _ => ?_
                  simp only [← mul_assoc]; rw [← Finset.mul_sum]
            _ = ∑ g ∈ B, (g : ℝ)⁻¹ * ((∑ u ∈ B, (u : ℝ)⁻¹) * ∑ v ∈ B, (v : ℝ)⁻¹) := by
                  refine Finset.sum_congr rfl fun g _ => ?_
                  rw [← Finset.mul_sum]
                  congr 1
                  rw [← Finset.sum_mul]
            _ = (∑ g ∈ B, (g : ℝ)⁻¹) * ((∑ u ∈ B, (u : ℝ)⁻¹) * ∑ v ∈ B, (v : ℝ)⁻¹) := by
                  rw [← Finset.sum_mul]
      _ ≤ (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 3 := by
          gcongr

end DivisorSecondMomentAndLinearBounds

section BilinearTypeIAndTypeII

private lemma sum_biUnion_le_sum_of_nonneg' {α β : Type*} [DecidableEq α]
    (s : Finset β) (t : β → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ b ∈ s, ∑ a ∈ t b, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hb]
    have hunion : ∑ a ∈ t b ∪ s.biUnion t, f a ≤
        ∑ a ∈ t b, f a + ∑ a ∈ s.biUnion t, f a := by
      have h := Finset.sum_union_inter (s₁ := t b) (s₂ := s.biUnion t) (f := f)
      have hinter : 0 ≤ ∑ a ∈ t b ∩ s.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
      linarith
    exact hunion.trans (add_le_add le_rfl ih)

private lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have hhalf : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [show (1 / 2 : ℝ) = -(-(1 / 2 : ℝ)) by ring, Real.exp_neg,
      inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hexp : Real.exp 1 < 4 := by
    have hsq : Real.exp 1 = Real.exp (1 / 2 : ℝ) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; norm_num
    rw [hsq]; nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlog4 : 1 < Real.log 4 := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hexp
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

private lemma sum_Icc_dyadic_vLinBound_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (D : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ d ∈ Finset.Icc 1 D, vLinBound (x / d) (α * d) ≤
      36 * (1 + Real.log (max D 1 : ℕ)) * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hlog_pos : 0 < Real.log (2 * (q : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp; positivity
  · rw [max_eq_left hD]
    let J := Nat.log 2 D + 1
    let block : ℕ → Finset ℕ := fun j => Finset.Icc (2 ^ j) (min D (2 ^ (j + 1)))
    have hcover : Finset.Icc 1 D ⊆ (Finset.range J).biUnion block := by
      intro d hd
      simp only [Finset.mem_Icc] at hd
      have hd_pos : 0 < d := hd.1
      let j := Nat.log 2 d
      have hj_lt : j < J := by
        dsimp only [J]
        exact Nat.lt_succ_of_le (Nat.log_mono_right hd.2)
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
      · exact Nat.pow_log_le_self 2 hd_pos.ne'
      · exact le_min hd.2 (Nat.lt_pow_succ_log_self one_lt_two d).le
    have hblock_bd : ∀ j : ℕ,
        ∑ d ∈ block j, vLinBound (x / d) (α * d) ≤
          18 * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by
      intro j
      let Xj := min D (2 ^ (j + 1))
      let Yj := x / (2 ^ j : ℝ)
      have hYj : 0 ≤ Yj := by positivity
      calc ∑ d ∈ block j, vLinBound (x / d) (α * d)
          ≤ ∑ d ∈ block j, vLinBound Yj (α * d) := by
            refine Finset.sum_le_sum fun d hd => vLinBound_mono_left ?_ _
            simp only [block, Finset.mem_Icc] at hd
            have h2j_pos : (0 : ℝ) < (2 ^ j : ℝ) := by positivity
            have hd_ge : (2 ^ j : ℝ) ≤ d := by exact_mod_cast hd.1
            exact div_le_div_of_nonneg_left hx h2j_pos hd_ge
        _ ≤ ∑ d ∈ Finset.Icc 1 Xj, vLinBound Yj (α * d) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => vLinBound_nonneg hYj _)
            intro d hd
            simp only [block, Finset.mem_Icc] at hd
            exact Finset.mem_Icc.mpr ⟨(Nat.one_le_two_pow).trans hd.1, hd.2⟩
        _ ≤ 9 * (((Xj : ℝ) + q) * Real.log (2 * (q : ℝ)) + (Xj : ℝ) * Yj / q) :=
            sum_Icc_vLinBound_le hq hcop hα Xj hYj
        _ ≤ 18 * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by
            have hXj_le_D : (Xj : ℝ) ≤ D := by exact_mod_cast min_le_left D (2 ^ (j + 1))
            have hXj_le_pow : (Xj : ℝ) ≤ 2 * (2 ^ j : ℝ) := by
              have hle : Xj ≤ 2 ^ (j + 1) := min_le_right D (2 ^ (j + 1))
              have hleR : (Xj : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hle
              simpa [pow_succ'] using hleR
            have hprod : (Xj : ℝ) * Yj ≤ 2 * x := by
              have hpow_ne : (2 ^ j : ℝ) ≠ 0 := by positivity
              calc (Xj : ℝ) * Yj ≤ (2 * (2 ^ j : ℝ)) * (x / (2 ^ j : ℝ)) :=
                    mul_le_mul_of_nonneg_right hXj_le_pow hYj
                _ = 2 * x := by field_simp [hpow_ne]
            have htermA : ((Xj : ℝ) + q) * Real.log (2 * (q : ℝ)) ≤
                ((D : ℝ) + q) * Real.log (2 * (q : ℝ)) := by gcongr
            have htermB : (Xj : ℝ) * Yj / q ≤ 2 * (x / q) := by
              calc (Xj : ℝ) * Yj / q ≤ (2 * x) / q := div_le_div_of_nonneg_right hprod hq0.le
                _ = 2 * (x / q) := by ring
            have h0A : 0 ≤ ((D : ℝ) + q) * Real.log (2 * (q : ℝ)) := by positivity
            have h0B : 0 ≤ x / q := by positivity
            linarith
    have hJ_le : (J : ℝ) ≤ 2 * (1 + Real.log (D : ℝ)) := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 D) ≤ D := by
        exact_mod_cast Nat.pow_log_le_self 2 hD.ne'
      have hlog_pow : (Nat.log 2 D : ℝ) * Real.log 2 ≤ Real.log (D : ℝ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hpow
      have hJ_R : (J : ℝ) = (Nat.log 2 D : ℝ) + 1 := by simp [J]
      nlinarith [log_two_gt_half]
    calc ∑ d ∈ Finset.Icc 1 D, vLinBound (x / d) (α * d)
        ≤ ∑ d ∈ (Finset.range J).biUnion block, vLinBound (x / d) (α * d) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun d hd _ =>
            vLinBound_nonneg (by positivity) _
      _ ≤ ∑ j ∈ Finset.range J, ∑ d ∈ block j, vLinBound (x / d) (α * d) :=
          sum_biUnion_le_sum_of_nonneg' (Finset.range J) block _ fun _ => vLinBound_nonneg (by positivity) _
      _ ≤ ∑ _j ∈ Finset.range J, 18 * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) :=
          Finset.sum_le_sum fun j _ => hblock_bd j
      _ = (J : ℝ) * (18 * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (1 + Real.log (D : ℝ))) * (18 * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q)) :=
          mul_le_mul_of_nonneg_right hJ_le (by positivity)
      _ = 36 * (1 + Real.log (D : ℝ)) * (((D : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by ring

/-- Bilinear Type I exponential sum bound under Diophantine approximation `|α - a/q| ≤ 1/q²`
(`gcd(a, q) = 1`, `q ≥ 1`):
`∑_{1 ≤ m ≤ M} ‖∑_{1 ≤ n ≤ ⌊x⌋₊ / m} exp(2πi α m n)‖ ≤
36 * (1 + log(max M 1)) * ((M + q) log(2q) + x / q)`. -/
theorem typeI_bilinear_exp_sum_bound {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ m ∈ Finset.Icc 1 M,
      ‖∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / m),
        Complex.exp (2 * Real.pi * ((α * (m * n : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
      36 * (1 + Real.log (max M 1 : ℕ)) * (((M : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / m),
        Complex.exp (2 * Real.pi * ((α * (m * n : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
      vLinBound (x / m) (α * m) := by
    intro m hm
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm_posR : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hdiv_le : ((⌊x⌋₊ / m : ℕ) : ℝ) ≤ x / m := by
      have h1 : (⌊x⌋₊ / m : ℕ) * m ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ m
      have h2 : ((⌊x⌋₊ / m : ℕ) : ℝ) * m ≤ ⌊x⌋₊ := by exact_mod_cast h1
      have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
      rw [le_div_iff₀ hm_posR]
      exact h2.trans h3
    have hrew : ∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / m),
          Complex.exp (2 * Real.pi * ((α * (m * n : ℕ) : ℝ) : ℂ) * Complex.I) =
        ∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / m), vaughanE ((α * m) * n) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [vaughanE, Nat.cast_mul, Complex.ofReal_mul]
      congr 1; ring
    rw [hrew]
    exact norm_sum_Icc_one_vaughanE_le_vLinBound (α * m) (⌊x⌋₊ / m) hdiv_le
  exact (Finset.sum_le_sum hterm).trans (sum_Icc_dyadic_vLinBound_le hq hcop hα M hx)

private lemma typeII_offdiag_half_bound (I : Finset ℕ) (K M : ℕ) (α : ℝ)
    (hI_sub : ∀ n ∈ I, 1 ≤ n ∧ n ≤ K) (hI_card : (I.card : ℝ) ≤ K)
    {P : Finset (ℕ × ℕ)} (hP : ∀ p ∈ P, p ∈ I ×ˢ I ∧ p.2 < p.1) :
    ∑ p ∈ P, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
      (K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h) := by
  have hstep : ∑ p ∈ P, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
      ∑ h ∈ Finset.Icc 1 K, ∑ _n ∈ I, vLinBound (M : ℝ) (α * h) := by
    have hinj : P ⊆ (Finset.Icc 1 K ×ˢ I).image (fun q : ℕ × ℕ => (q.2 + q.1, q.2)) := by
      intro p hp
      rcases hP p hp with ⟨hpI, hlt⟩
      simp only [Finset.mem_product] at hpI
      have hp1 := hI_sub p.1 hpI.1
      have hp2 := hI_sub p.2 hpI.2
      refine Finset.mem_image.mpr ⟨(p.1 - p.2, p.2), Finset.mem_product.mpr ⟨?_, hpI.2⟩, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · exact Prod.ext (by omega) rfl
    calc ∑ p ∈ P, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))
        ≤ ∑ p ∈ (Finset.Icc 1 K ×ˢ I).image (fun q : ℕ × ℕ => (q.2 + q.1, q.2)),
            vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hinj fun _ _ _ =>
            vLinBound_nonneg (Nat.cast_nonneg M) _
      _ ≤ ∑ q ∈ Finset.Icc 1 K ×ˢ I,
            vLinBound (M : ℝ) (α * ((((q.2 + q.1 : ℕ) : ℝ)) - (q.2 : ℝ))) :=
          Finset.sum_image_le_of_nonneg fun _ _ => vLinBound_nonneg (Nat.cast_nonneg M) _
      _ = ∑ h ∈ Finset.Icc 1 K, ∑ _n ∈ I, vLinBound (M : ℝ) (α * h) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun _n _ => ?_
          rw [Nat.cast_add]; congr 1; ring
  calc ∑ p ∈ P, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))
      ≤ ∑ h ∈ Finset.Icc 1 K, (I.card : ℝ) * vLinBound (M : ℝ) (α * h) := by
        refine hstep.trans_eq (Finset.sum_congr rfl fun h _ => ?_)
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ h ∈ Finset.Icc 1 K, (K : ℝ) * vLinBound (M : ℝ) (α * h) := by
        refine Finset.sum_le_sum fun h _ =>
          mul_le_mul_of_nonneg_right hI_card (vLinBound_nonneg (Nat.cast_nonneg M) _)
    _ = (K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h) := by
        rw [Finset.mul_sum]

/-- Cauchy–Schwarz Type II bilinear exponential sum bound:
for any sequences `a, b : ℕ → ℂ` with `∑_{M < m ≤ M'} ‖a m‖^2 ≤ A2` (`M' ≤ 2M`) and
`‖b n‖ ≤ B_inf` on `N < n ≤ ⌊x⌋₊ / M`, and `|α - a₀/q| ≤ 1/q²` (`gcd(a₀, q) = 1`, `q ≥ 1`),
`‖∑_{M < m ≤ M'} a m ∑_{N < n ≤ ⌊x⌋₊ / m} b n exp(2πi α m n)‖^2 ≤
A2 * B_inf^2 * (K * M + 18 * K * ((K + q) log(2q) + K * M / q))` where `K = ⌊x⌋₊ / M`. -/
theorem typeII_bilinear_exp_sum_bound {α : ℝ} {a₀ : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a₀.natAbs q) (hα : |α - (a₀ : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (a b : ℕ → ℂ) {M M' N : ℕ} (hM : 1 ≤ M) (hM' : M' ≤ 2 * M) {x : ℝ}
    {A2 B_inf : ℝ} (hA2_nn : 0 ≤ A2) (hB_nn : 0 ≤ B_inf)
    (hA2 : ∑ m ∈ Finset.Ioc M M', ‖a m‖ ^ 2 ≤ A2)
    (hB : ∀ n ∈ Finset.Ioc N (⌊x⌋₊ / M), ‖b n‖ ≤ B_inf) :
    ‖∑ m ∈ Finset.Ioc M M', a m *
        ∑ n ∈ Finset.Ioc N (⌊x⌋₊ / m), b n *
          Complex.exp (2 * Real.pi * ((α * (m * n : ℕ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      A2 * B_inf ^ 2 *
        (((⌊x⌋₊ / M : ℕ) : ℝ) * M +
          18 * ((⌊x⌋₊ / M : ℕ) : ℝ) *
            ((((⌊x⌋₊ / M : ℕ) : ℝ) + q) * Real.log (2 * (q : ℝ)) +
              ((⌊x⌋₊ / M : ℕ) : ℝ) * M / q)) := by
  let K := ⌊x⌋₊ / M
  let S := Finset.Ioc M M'
  let inner : ℕ → ℂ := fun m =>
    ∑ n ∈ Finset.Ioc N (⌊x⌋₊ / m), b n * vaughanE (α * (m * n : ℕ))
  have hrew_sum :
      ∑ m ∈ S, a m *
          ∑ n ∈ Finset.Ioc N (⌊x⌋₊ / m), b n *
            Complex.exp (2 * Real.pi * ((α * (m * n : ℕ) : ℝ) : ℂ) * Complex.I) =
        ∑ m ∈ S, a m * inner m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
  rw [hrew_sum]
  have hcs : ‖∑ m ∈ S, a m * inner m‖ ^ 2 ≤
      (∑ m ∈ S, ‖a m‖ ^ 2) * ∑ m ∈ S, ‖inner m‖ ^ 2 := by
    calc ‖∑ m ∈ S, a m * inner m‖ ^ 2
        ≤ (∑ m ∈ S, ‖a m‖ * ‖inner m‖) ^ 2 := by
          have h1 : ‖∑ m ∈ S, a m * inner m‖ ≤ ∑ m ∈ S, ‖a m‖ * ‖inner m‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => (norm_mul _ _).le)
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ m ∈ S, ‖a m‖ ^ 2) * ∑ m ∈ S, ‖inner m‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq S (fun m => ‖a m‖) (fun m => ‖inner m‖)
  let I := Finset.Ioc N K
  let c : ℕ → ℕ → ℂ := fun m n =>
    if n ≤ ⌊x⌋₊ / m then b n * vaughanE (α * (m * n : ℕ)) else 0
  have hinner_eq : ∀ m ∈ S, inner m = ∑ n ∈ I, c m n := by
    intro m hm
    have hm_gt : M < m := (Finset.mem_Ioc.mp hm).1
    have hdiv_le : ⌊x⌋₊ / m ≤ K := Nat.div_le_div_left hm_gt.le hM
    have hfilt : Finset.Ioc N (⌊x⌋₊ / m) = I.filter (fun n => n ≤ ⌊x⌋₊ / m) := by
      ext n; simp only [I, Finset.mem_Ioc, Finset.mem_filter]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hdiv_le⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    rw [← Finset.sum_filter, ← hfilt]
  have hexpand : ∑ m ∈ S, ‖inner m‖ ^ 2 =
      ∑ p ∈ I ×ˢ I,
        ((∑ m ∈ S, c m p.1 * star (c m p.2))).re := by
    have hterm : ∀ m ∈ S, ‖inner m‖ ^ 2 =
        ∑ p ∈ I ×ˢ I, (c m p.1 * star (c m p.2)).re := by
      intro m hm
      rw [hinner_eq m hm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre : (∑ n ∈ I, c m n).re * (∑ n ∈ I, c m n).re +
          (∑ n ∈ I, c m n).im * (∑ n ∈ I, c m n).im =
          (∑ n₁ ∈ I, c m n₁ * star (∑ n₂ ∈ I, c m n₂)).re := by
        rw [← Finset.sum_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
        ring
      rw [hre, star_sum]
      simp only [Finset.mul_sum, Complex.re_sum]
      rw [Finset.sum_product]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.re_sum]
  have hp_bd : ∀ p ∈ I ×ˢ I,
      (∑ m ∈ S, c m p.1 * star (c m p.2)).re ≤
        B_inf ^ 2 * vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) := by
    intro p hp
    simp only [Finset.mem_product, I, Finset.mem_Ioc] at hp
    have hp1_pos : 0 < p.1 := Nat.pos_of_ne_zero (by omega)
    have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (by omega)
    let Mtop := min M' (⌊x⌋₊ / max p.1 p.2)
    have hsplit_c : ∑ m ∈ S, c m p.1 * star (c m p.2) =
        b p.1 * star (b p.2) * ∑ m ∈ Finset.Ioc M Mtop, vaughanE ((α * ((p.1 : ℝ) - (p.2 : ℝ))) * m) := by
      have hfilt : Finset.Ioc M Mtop = S.filter (fun m => p.1 ≤ ⌊x⌋₊ / m ∧ p.2 ≤ ⌊x⌋₊ / m) := by
        ext m
        simp only [S, Mtop, Finset.mem_Ioc, Finset.mem_filter]
        constructor
        · rintro ⟨hm1, hm2⟩
          have hm_pos : 0 < m := le_trans hM hm1.le
          have hle_max : m ≤ ⌊x⌋₊ / max p.1 p.2 := le_trans hm2 (min_le_right _ _)
          have hmax_pos : 0 < max p.1 p.2 := lt_of_lt_of_le hp1_pos (le_max_left _ _)
          have hmul : max p.1 p.2 * m ≤ ⌊x⌋₊ :=
            (Nat.mul_le_mul_left (max p.1 p.2) hle_max).trans (Nat.mul_div_le ⌊x⌋₊ _)
          have h1 : p.1 ≤ ⌊x⌋₊ / m := (Nat.le_div_iff_mul_le hm_pos).mpr
            ((Nat.mul_le_mul_right m (le_max_left p.1 p.2)).trans hmul)
          have h2 : p.2 ≤ ⌊x⌋₊ / m := (Nat.le_div_iff_mul_le hm_pos).mpr
            ((Nat.mul_le_mul_right m (le_max_right p.1 p.2)).trans hmul)
          exact ⟨⟨hm1, hm2.trans (min_le_left _ _)⟩, h1, h2⟩
        · rintro ⟨⟨hm1, hm2⟩, h1, h2⟩
          have hm_pos : 0 < m := le_trans hM hm1.le
          have hmul1 : p.1 * m ≤ ⌊x⌋₊ := (Nat.le_div_iff_mul_le hm_pos).mp h1
          have hmul2 : p.2 * m ≤ ⌊x⌋₊ := (Nat.le_div_iff_mul_le hm_pos).mp h2
          have hmul : max p.1 p.2 * m ≤ ⌊x⌋₊ := max_le_iff.mpr ⟨hmul1, hmul2⟩ |> fun h => by
            rcases le_total p.1 p.2 with hp12 | hp21
            · rw [max_eq_right hp12]; exact hmul2
            · rw [max_eq_left hp21]; exact hmul1
          have hmax_pos : 0 < max p.1 p.2 := lt_of_lt_of_le hp1_pos (le_max_left _ _)
          exact ⟨hm1, le_min hm2 ((Nat.le_div_iff_mul_le hmax_pos).mpr (by simpa [mul_comm] using hmul))⟩
      rw [hfilt, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only [c]
      by_cases hp1 : p.1 ≤ ⌊x⌋₊ / m; swap; · simp [hp1]
      by_cases hp2 : p.2 ≤ ⌊x⌋₊ / m; swap; · simp [hp2]
      simp only [hp1, hp2, and_self, ↓reduceIte]
      have he : vaughanE (α * (m * p.1 : ℕ)) * star (vaughanE (α * (m * p.2 : ℕ))) =
          vaughanE (α * ((p.1 : ℝ) - (p.2 : ℝ)) * (m : ℝ)) := by
        rw [star_vaughanE, ← vaughanE_add]
        congr 1
        push_cast
        ring
      calc b p.1 * vaughanE (α * (m * p.1 : ℕ)) * star (b p.2 * vaughanE (α * (m * p.2 : ℕ)))
          = b p.1 * star (b p.2) *
              (vaughanE (α * (m * p.1 : ℕ)) * star (vaughanE (α * (m * p.2 : ℕ)))) := by
              rw [star_mul]; ring
        _ = b p.1 * star (b p.2) * vaughanE (α * ((p.1 : ℝ) - (p.2 : ℝ)) * (m : ℝ)) := by rw [he]
    calc (∑ m ∈ S, c m p.1 * star (c m p.2)).re
        ≤ ‖∑ m ∈ S, c m p.1 * star (c m p.2)‖ := Complex.re_le_norm _
      _ = ‖b p.1‖ * ‖b p.2‖ *
            ‖∑ m ∈ Finset.Ioc M Mtop, vaughanE ((α * ((p.1 : ℝ) - (p.2 : ℝ))) * m)‖ := by
          rw [hsplit_c, norm_mul, norm_mul, norm_star]
      _ ≤ B_inf ^ 2 * vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) := by
          have hb1 : ‖b p.1‖ ≤ B_inf := hB p.1 (Finset.mem_Ioc.mpr hp.1)
          have hb2 : ‖b p.2‖ ≤ B_inf := hB p.2 (Finset.mem_Ioc.mpr hp.2)
          have hlen : ((Mtop - M : ℕ) : ℝ) ≤ (M : ℝ) := by
            have hle : Mtop ≤ 2 * M := (min_le_left _ _).trans hM'
            have hsub : Mtop - M ≤ M := by calc Mtop - M ≤ 2 * M - M := Nat.sub_le_sub_right hle M
              _ = M := by omega
            exact_mod_cast hsub
          have hsum_bd := norm_sum_Ioc_vaughanE_le_vLinBound (α * ((p.1 : ℝ) - (p.2 : ℝ))) hlen
          have hbb : ‖b p.1‖ * ‖b p.2‖ ≤ B_inf ^ 2 := by
            rw [sq]; exact mul_le_mul hb1 hb2 (norm_nonneg _) hB_nn
          exact mul_le_mul hbb hsum_bd (norm_nonneg _) (sq_nonneg B_inf)
  have hI_card : (I.card : ℝ) ≤ K := by
    have hcard : I.card ≤ K := by
      dsimp only [I]
      rw [Nat.card_Ioc]
      exact Nat.sub_le K N
    exact_mod_cast hcard
  have hdiag_le : ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 = p.2),
      vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤ (K : ℝ) * M := by
    calc ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 = p.2), vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))
        ≤ ∑ _p ∈ (I ×ˢ I).filter (fun p => p.1 = p.2), (M : ℝ) :=
          Finset.sum_le_sum fun p _ => vLinBound_le_left _ _
      _ = (((I ×ˢ I).filter (fun p => p.1 = p.2)).card : ℝ) * M := by simp
      _ ≤ (I.card : ℝ) * M := by
          have hle : ((I ×ˢ I).filter (fun p => p.1 = p.2)).card ≤ I.card := by
            refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
            · intro p hp
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
              exact hp.1.1
            · intro p₁ hp₁ p₂ hp₂ h
              simp only [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
              exact Prod.ext h (by rw [← hp₁.2, h, hp₂.2])
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg M)
      _ ≤ (K : ℝ) * M := mul_le_mul_of_nonneg_right hI_card (Nat.cast_nonneg M)
  have hgt_le : ∑ p ∈ (I ×ˢ I).filter (fun p => p.2 < p.1),
      vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
      (K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h) :=
    typeII_offdiag_half_bound I K M α
      (fun n hn => by simp only [I, Finset.mem_Ioc] at hn; omega) hI_card
      (fun p hp => by simp only [Finset.mem_filter] at hp; exact hp)
  have hlt_le : ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 < p.2),
      vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
      (K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h) := by
    let Q := (I ×ˢ I).filter (fun p => p.2 < p.1)
    have hbij : ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 < p.2),
          vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) =
        ∑ p ∈ Q, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) := by
      refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Q] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq; simp only [Finset.mem_filter, Finset.mem_product, Q] at hq
        exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq.1.2, hq.1.1⟩, hq.2⟩,
          Prod.ext rfl rfl⟩
      · intro p _
        dsimp only
        rw [show α * ((p.2 : ℝ) - (p.1 : ℝ)) = -(α * ((p.1 : ℝ) - (p.2 : ℝ))) by ring, vLinBound_neg]
    rw [hbij]; exact hgt_le
  have hpart : I ×ˢ I = (I ×ˢ I).filter (fun p => p.1 = p.2) ∪
      ((I ×ˢ I).filter (fun p => p.2 < p.1) ∪ (I ×ˢ I).filter (fun p => p.1 < p.2)) := by
    ext p; simp only [Finset.mem_union, Finset.mem_filter]; constructor
    · intro hp; rcases lt_trichotomy p.1 p.2 with h1 | h1 | h1
      · exact Or.inr (Or.inr ⟨hp, h1⟩)
      · exact Or.inl ⟨hp, h1⟩
      · exact Or.inr (Or.inl ⟨hp, h1⟩)
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hd1 : Disjoint ((I ×ˢ I).filter (fun p => p.1 = p.2))
      ((I ×ˢ I).filter (fun p => p.2 < p.1) ∪ (I ×ˢ I).filter (fun p => p.1 < p.2)) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h2 with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
  have hd2 : Disjoint ((I ×ˢ I).filter (fun p => p.2 < p.1))
      ((I ×ˢ I).filter (fun p => p.1 < p.2)) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2; omega
  have hlin_K := sum_Icc_vLinBound_le hq hcop hα K (Nat.cast_nonneg M)
  have hsum_v : ∑ p ∈ I ×ˢ I, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
      (K : ℝ) * M + 18 * (K : ℝ) * (((K : ℝ) + q) * Real.log (2 * (q : ℝ)) + (K : ℝ) * M / q) := by
    calc ∑ p ∈ I ×ˢ I, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))
        = ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 = p.2), vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) +
          (∑ p ∈ (I ×ˢ I).filter (fun p => p.2 < p.1), vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) +
          ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 < p.2), vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))) := by
          conv_lhs => rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
      _ ≤ (K : ℝ) * M + ((K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h) +
            (K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h)) :=
          add_le_add hdiag_le (add_le_add hgt_le hlt_le)
      _ = (K : ℝ) * M + 2 * (K : ℝ) * ∑ h ∈ Finset.Icc 1 K, vLinBound (M : ℝ) (α * h) := by ring
      _ ≤ (K : ℝ) * M + 2 * (K : ℝ) * (9 * (((K : ℝ) + q) * Real.log (2 * (q : ℝ)) + (K : ℝ) * M / q)) := by
          gcongr
      _ = (K : ℝ) * M + 18 * (K : ℝ) * (((K : ℝ) + q) * Real.log (2 * (q : ℝ)) + (K : ℝ) * M / q) := by ring
  have hS_sq_nn : 0 ≤ ∑ m ∈ S, ‖inner m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinner_bd : ∑ m ∈ S, ‖inner m‖ ^ 2 ≤
      B_inf ^ 2 * ((K : ℝ) * M + 18 * (K : ℝ) * (((K : ℝ) + q) * Real.log (2 * (q : ℝ)) + (K : ℝ) * M / q)) := by
    calc ∑ m ∈ S, ‖inner m‖ ^ 2
        = ∑ p ∈ I ×ˢ I, (∑ m ∈ S, c m p.1 * star (c m p.2)).re := hexpand
      _ ≤ ∑ p ∈ I ×ˢ I, B_inf ^ 2 * vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) :=
          Finset.sum_le_sum hp_bd
      _ = B_inf ^ 2 * ∑ p ∈ I ×ˢ I, vLinBound (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) := by
          rw [← Finset.mul_sum]
      _ ≤ B_inf ^ 2 * ((K : ℝ) * M + 18 * (K : ℝ) * (((K : ℝ) + q) * Real.log (2 * (q : ℝ)) + (K : ℝ) * M / q)) :=
          mul_le_mul_of_nonneg_left hsum_v (sq_nonneg B_inf)
  exact hcs.trans ((mul_le_mul hA2 hinner_bd hS_sq_nn hA2_nn).trans_eq (by ring))

end BilinearTypeIAndTypeII

section VinogradovPrimeExpSum

private lemma real_log_two_mul_le_two_mul_log {x : ℝ} {q : ℕ} (hx : 2 ≤ x) (hq1 : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) :
    Real.log (2 * (q : ℝ)) ≤ 2 * Real.log x := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hx0 : 0 < x := by linarith
  have h2qx : 2 * (q : ℝ) ≤ x ^ 2 := by nlinarith
  calc Real.log (2 * (q : ℝ)) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) h2qx
    _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num

private lemma one_add_log_le_three_mul_log {x y : ℝ} (hx : 2 ≤ x) (hy1 : 1 ≤ y) (hyx : y ≤ x) :
    1 + Real.log y ≤ 3 * Real.log x := by
  have h1 : 1 ≤ 2 * Real.log 2 := by linarith [log_two_gt_half]
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  have h3 : Real.log y ≤ Real.log x := Real.log_le_log (by positivity) hyx
  linarith

private lemma sum_Ico_log_sub (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.Ico 1 K, (Real.log (k + 1 : ℕ) - Real.log k) = Real.log K := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    ring

private lemma typeI_log_sum_bound {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    ‖∑ d ∈ Finset.Icc 1 U, (μ d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), (Real.log m : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
      72 * Real.log x * (1 + Real.log (max U 1 : ℕ)) *
        (((U : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by
  have hx0 : 0 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hterm : ∀ d ∈ Finset.Icc 1 U,
      ‖(μ d : ℂ) * ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), (Real.log m : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * Real.log x * vLinBound (x / d) (α * d) := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hd_posR : (0 : ℝ) < d := by exact_mod_cast hd_pos
    let K := ⌊x⌋₊ / d
    have hK_le : (K : ℝ) ≤ x / d := by
      have h1 : K * d ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ d
      have h2 : (K : ℝ) * d ≤ ⌊x⌋₊ := by exact_mod_cast h1
      rw [le_div_iff₀ hd_posR]; exact h2.trans (Nat.floor_le hx0)
    have hmu : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    have hrew : ∑ m ∈ Finset.Icc 1 K, (Real.log m : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I) =
        ∑ m ∈ Finset.Icc 1 K, vaughanE ((α * d) * m) * (Real.log m : ℂ) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [vaughanE, Nat.cast_mul, Complex.ofReal_mul]
      rw [mul_comm (Real.log m : ℂ)]; congr 2; ring
    rw [norm_mul, hrew]
    have habel := abel_discrete_Icc_one (fun m => vaughanE ((α * d) * m))
      (fun m => (Real.log m : ℂ)) K
    rw [habel]
    have hps_bd : ∀ t ≤ K, ‖∑ i ∈ Finset.Icc 1 t, vaughanE ((α * d) * i)‖ ≤
        vLinBound (x / d) (α * d) := fun t ht =>
      norm_sum_Icc_one_vaughanE_le_vLinBound (α * d) t
        ((Nat.cast_le.mpr ht).trans hK_le)
    rcases Nat.eq_zero_or_pos K with hK0 | hK_pos
    · rw [hK0]
      have hIcc0 : Finset.Icc 1 0 = ∅ := by ext; simp
      have hIco0 : Finset.Ico 1 0 = ∅ := by ext; simp
      rw [hIcc0, hIco0, Finset.sum_empty, Finset.sum_empty, zero_mul, sub_zero, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg zero_le_two hlogx_nn)
        (vLinBound_nonneg (div_nonneg hx0 (Nat.cast_nonneg d)) (α * (d : ℝ)))
    · have hK_le_x : (K : ℝ) ≤ x := hK_le.trans (div_le_self hx0 (by exact_mod_cast hd_pos))
      have hlogK_le : Real.log K ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast hK_pos) hK_le_x
      have hlogK_nn : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK_pos)
      have ht1 : ‖(∑ i ∈ Finset.Icc 1 K, vaughanE ((α * d) * i)) * (Real.log K : ℂ)‖ ≤
          Real.log x * vLinBound (x / d) (α * d) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogK_nn]
        exact (mul_le_mul (hps_bd K le_rfl) hlogK_le hlogK_nn
          (vLinBound_nonneg (by positivity) _)).trans_eq (mul_comm _ _)
      have ht2 : ‖∑ k ∈ Finset.Ico 1 K,
          (∑ i ∈ Finset.Icc 1 k, vaughanE ((α * d) * i)) *
            ((Real.log (k + 1 : ℕ) : ℂ) - (Real.log k : ℂ))‖ ≤
          Real.log x * vLinBound (x / d) (α * d) := by
        calc ‖∑ k ∈ Finset.Ico 1 K, _‖
            ≤ ∑ k ∈ Finset.Ico 1 K,
                ‖∑ i ∈ Finset.Icc 1 k, vaughanE ((α * d) * i)‖ *
                  ‖(Real.log (k + 1 : ℕ) : ℂ) - (Real.log k : ℂ)‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
          _ ≤ ∑ k ∈ Finset.Ico 1 K,
                vLinBound (x / d) (α * d) * (Real.log (k + 1 : ℕ) - Real.log k) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk_ge : 1 ≤ k := (Finset.mem_Ico.mp hk).1
              have hk_lt : k < K := (Finset.mem_Ico.mp hk).2
              have hdiff_nn : 0 ≤ Real.log (k + 1 : ℕ) - Real.log k :=
                sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hk_ge) (by norm_cast; omega))
              have hnorm_d : ‖(Real.log (k + 1 : ℕ) : ℂ) - (Real.log k : ℂ)‖ =
                  Real.log (k + 1 : ℕ) - Real.log k := by
                rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiff_nn]
              rw [hnorm_d]
              exact mul_le_mul_of_nonneg_right (hps_bd k hk_lt.le) hdiff_nn
          _ = vLinBound (x / d) (α * d) *
                ∑ k ∈ Finset.Ico 1 K, (Real.log (k + 1 : ℕ) - Real.log k) := by
              rw [← Finset.mul_sum]
          _ = vLinBound (x / d) (α * d) * Real.log K := by
              rw [sum_Ico_log_sub K hK_pos]
          _ ≤ Real.log x * vLinBound (x / d) (α * d) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hlogK_le (vLinBound_nonneg (by positivity) _)
      have hinner : ‖(∑ i ∈ Finset.Icc 1 K, vaughanE ((α * d) * i)) * (Real.log K : ℂ) -
            ∑ k ∈ Finset.Ico 1 K,
              (∑ i ∈ Finset.Icc 1 k, vaughanE ((α * d) * i)) *
                ((Real.log (k + 1 : ℕ) : ℂ) - (Real.log k : ℂ))‖ ≤
          2 * Real.log x * vLinBound (x / d) (α * d) := by
        calc _ ≤ ‖_‖ + ‖_‖ := norm_sub_le _ _
          _ ≤ Real.log x * vLinBound (x / d) (α * d) +
                Real.log x * vLinBound (x / d) (α * d) := add_le_add ht1 ht2
          _ = 2 * Real.log x * vLinBound (x / d) (α * d) := by ring
      calc ‖(μ d : ℂ)‖ * ‖_‖ ≤ 1 * (2 * Real.log x * vLinBound (x / d) (α * d)) :=
            mul_le_mul hmu hinner (norm_nonneg _) zero_le_one
        _ = 2 * Real.log x * vLinBound (x / d) (α * d) := one_mul _
  calc ‖∑ d ∈ Finset.Icc 1 U, (μ d : ℂ) * _‖
      ≤ ∑ d ∈ Finset.Icc 1 U, ‖(μ d : ℂ) * _‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U, 2 * Real.log x * vLinBound (x / d) (α * d) :=
        Finset.sum_le_sum hterm
    _ = 2 * Real.log x * ∑ d ∈ Finset.Icc 1 U, vLinBound (x / d) (α * d) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * Real.log x *
          (36 * (1 + Real.log (max U 1 : ℕ)) * (((U : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_dyadic_vLinBound_le hq hcop hα U hx0) (by positivity)
    _ = 72 * Real.log x * (1 + Real.log (max U 1 : ℕ)) *
          (((U : ℝ) + q) * Real.log (2 * (q : ℝ)) + x / q) := by ring

private lemma typeII_dyadic_sum_bound {α : ℝ} {a₀ : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a₀.natAbs q) (hα : |α - (a₀ : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) {x : ℝ} (hx : 2 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hUV_x : U ≤ ⌊x⌋₊ / V) (_hU_le_x : (U : ℝ) ≤ x) (_hV_le_x : (V : ℝ) ≤ x) :
    ‖∑ m ∈ Finset.Ioc U (⌊x⌋₊ / V), (vaughanTypeIICoeff U m : ℂ) *
        ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
      408 * (Real.log x) ^ 4 *
        (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
          x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let W := ⌊x⌋₊ / V
  have hx0 : 0 ≤ x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2q : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log x := real_log_two_mul_le_two_mul_log hx hq hqx
  have hlog_x1 : 1 + Real.log x ≤ 3 * Real.log x :=
    one_add_log_le_three_mul_log hx (by linarith) le_rfl
  let j₀ := Nat.log 2 U
  let j₁ := Nat.log 2 W
  let block : ℕ → Finset ℕ := fun j =>
    if j = j₀ then Finset.Ioc U (min W (2 ^ (j₀ + 1)))
    else Finset.Ioc (2 ^ j) (min W (2 ^ (j + 1)))
  have hcover : Finset.Ioc U W ⊆ (Finset.Icc j₀ j₁).biUnion block := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    by_cases hm_small : m ≤ 2 ^ (j₀ + 1)
    · refine Finset.mem_biUnion.mpr ⟨j₀, Finset.mem_Icc.mpr ⟨le_rfl, Nat.log_mono_right hUV_x⟩, ?_⟩
      simp only [block, ↓reduceIte, Finset.mem_Ioc]
      exact ⟨hm.1, le_min hm.2 hm_small⟩
    · have hm_gt : 2 ^ (j₀ + 1) < m := not_le.mp hm_small
      have hm_pos : 0 < m := hU.trans hm.1.le
      let jm := Nat.log 2 m
      have hjm_ge : j₀ + 1 ≤ jm := by
        dsimp only [jm]
        exact Nat.le_log_of_pow_le one_lt_two hm_gt.le
      by_cases hpow : m = 2 ^ jm
      · let j := jm - 1
        have hj_ge : j₀ + 1 ≤ j + 1 := by omega
        have hj_not : j ≠ j₀ := by
          have : 2 ^ (j₀ + 1) < 2 ^ jm := by rw [← hpow]; exact hm_gt
          have : j₀ + 1 < jm := Nat.pow_lt_pow_iff_right one_lt_two |>.mp this
          omega
        have hj_lo : j₀ ≤ j := by omega
        have hj_hi : j ≤ j₁ := by
          have : 2 ^ j ≤ W := by
            have hle : 2 ^ j ≤ 2 ^ jm := Nat.pow_le_pow_right (by norm_num) (by omega)
            rw [← hpow] at hle; exact hle.trans hm.2
          exact Nat.le_log_of_pow_le one_lt_two this
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj_lo, hj_hi⟩, ?_⟩
        simp only [block, hj_not, ↓reduceIte, Finset.mem_Ioc]
        have hlt : 2 ^ j < m := by
          rw [hpow]; exact Nat.pow_lt_pow_right one_lt_two (by omega)
        have hle : m ≤ 2 ^ (j + 1) := by rw [hpow, show j + 1 = jm by omega]
        exact ⟨hlt, le_min hm.2 hle⟩
      · have hjm_gt : 2 ^ jm < m :=
          lt_of_le_of_ne (Nat.pow_log_le_self 2 hm_pos.ne') (Ne.symm hpow)
        have hj_not : jm ≠ j₀ := by omega
        have hj_hi : jm ≤ j₁ := Nat.log_mono_right hm.2
        refine Finset.mem_biUnion.mpr ⟨jm, Finset.mem_Icc.mpr ⟨by omega, hj_hi⟩, ?_⟩
        simp only [block, hj_not, ↓reduceIte, Finset.mem_Ioc]
        exact ⟨hjm_gt, le_min hm.2 (Nat.lt_pow_succ_log_self one_lt_two m).le⟩
  have hdisj : ∀ j ∈ Finset.Icc j₀ j₁,
      block j ⊆ Finset.Ioc U W := fun j hj m hm => by
    simp only [Finset.mem_Icc] at hj
    dsimp only [block] at hm
    split_ifs at hm with hjj
    · simp only [Finset.mem_Ioc] at hm
      exact Finset.mem_Ioc.mpr ⟨hm.1, hm.2.trans (min_le_left _ _)⟩
    · simp only [Finset.mem_Ioc] at hm
      have hj_gt : j₀ < j := by omega
      have hU_lt : U < 2 ^ j :=
        (Nat.lt_pow_succ_log_self one_lt_two U).trans_le (Nat.pow_le_pow_right (by norm_num) hj_gt)
      exact Finset.mem_Ioc.mpr ⟨hU_lt.trans hm.1, hm.2.trans (min_le_left _ _)⟩
  have hsum_split :
      ‖∑ m ∈ Finset.Ioc U W, (vaughanTypeIICoeff U m : ℂ) *
          ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
        ∑ j ∈ Finset.Icc j₀ j₁,
          ‖∑ m ∈ block j, (vaughanTypeIICoeff U m : ℂ) *
            ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ := by
    have hdisj_pw : Set.PairwiseDisjoint (Finset.Icc j₀ j₁ : Set ℕ) block := by
      intro i hi j hj hij
      rw [Function.onFun, Finset.disjoint_left]
      intro m hmi hmj
      simp only [Finset.mem_coe, Finset.mem_Icc] at hi hj
      rcases lt_or_gt_of_ne hij with hilt | hjlt
      · simp only [block] at hmi hmj
        have hle : m ≤ 2 ^ (i + 1) := by
          split_ifs at hmi with hii
          · subst hii; exact (Finset.mem_Ioc.mp hmi).2.trans (min_le_right _ _)
          · exact (Finset.mem_Ioc.mp hmi).2.trans (min_le_right _ _)
        have hgt : 2 ^ j < m := by
          split_ifs at hmj with hjj
          · omega
          · exact (Finset.mem_Ioc.mp hmj).1
        have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hilt
        omega
      · simp only [block] at hmi hmj
        have hle : m ≤ 2 ^ (j + 1) := by
          split_ifs at hmj with hjj
          · subst hjj; exact (Finset.mem_Ioc.mp hmj).2.trans (min_le_right _ _)
          · exact (Finset.mem_Ioc.mp hmj).2.trans (min_le_right _ _)
        have hgt : 2 ^ i < m := by
          split_ifs at hmi with hii
          · omega
          · exact (Finset.mem_Ioc.mp hmi).1
        have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hjlt
        omega
    have heq_set : Finset.Ioc U W = (Finset.Icc j₀ j₁).biUnion block := by
      refine Finset.Subset.antisymm hcover ?_
      rw [Finset.biUnion_subset]
      exact hdisj
    rw [heq_set, Finset.sum_biUnion hdisj_pw]
    exact norm_sum_le _ _
  have hblock_norm : ∀ j ∈ Finset.Icc j₀ j₁,
      ‖∑ m ∈ block j, (vaughanTypeIICoeff U m : ℂ) *
          ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
        68 * (Real.log x) ^ 3 *
          (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
            x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    let M : ℕ := if j = j₀ then U else 2 ^ j
    let M' : ℕ := min W (2 ^ (j + 1))
    have hblock_eq : block j = Finset.Ioc M M' := by
      dsimp only [block, M, M']
      split_ifs with hjj
      · subst hjj; rfl
      · rfl
    have hM_ge_U : U ≤ M := by
      dsimp only [M]
      split_ifs with hjj
      · exact le_rfl
      · have hj_gt : j₀ < j := by omega
        exact (Nat.lt_pow_succ_log_self one_lt_two U).le.trans
          (Nat.pow_le_pow_right (by norm_num) hj_gt)
    have hM_pos : 1 ≤ M := hU.trans hM_ge_U
    have hM_le_W : M ≤ W := by
      dsimp only [M]
      split_ifs
      · exact hUV_x
      · exact (Nat.pow_le_pow_right (by norm_num) hj.2).trans (Nat.pow_log_le_self 2 (by
          have : 1 ≤ W := hU.trans hUV_x; omega))
    have hM'_le : M' ≤ 2 * M := by
      dsimp only [M', M]
      split_ifs with hjj
      · subst hjj
        have h1 : 2 ^ (j₀ + 1) ≤ 2 * U := by
          have hpow : 2 ^ Nat.log 2 U ≤ U := Nat.pow_log_le_self 2 (by omega)
          change 2 ^ (Nat.log 2 U + 1) ≤ 2 * U
          rw [pow_succ']
          omega
        exact (min_le_right _ _).trans h1
      · rw [pow_succ']
        exact min_le_right _ _
    have h2M_le : 2 * M ≤ 2 * ⌊x⌋₊ := by
      have hW_le : W ≤ ⌊x⌋₊ := Nat.div_le_self ⌊x⌋₊ V
      omega
    let A2 : ℝ := (2 * (M : ℝ)) * (4 * Real.log x) ^ 3
    have hA2_nn : 0 ≤ A2 := by positivity
    have hA2 : ∑ m ∈ Finset.Ioc M M', ‖(vaughanTypeIICoeff U m : ℂ)‖ ^ 2 ≤ A2 := by
      have hsub : Finset.Ioc M M' ⊆ Finset.Icc 1 (2 * M) := fun m hm => by
        simp only [Finset.mem_Ioc] at hm
        exact Finset.mem_Icc.mpr ⟨hM_pos.trans hm.1.le, hm.2.trans hM'_le⟩
      have hdiv_sum : ∑ m ∈ Finset.Ioc M M', ‖(vaughanTypeIICoeff U m : ℂ)‖ ^ 2 ≤
          ∑ m ∈ Finset.Icc 1 (2 * M), ((Nat.divisors m).card : ℝ) ^ 2 := by
        calc ∑ m ∈ Finset.Ioc M M', ‖(vaughanTypeIICoeff U m : ℂ)‖ ^ 2
            ≤ ∑ m ∈ Finset.Ioc M M', ((Nat.divisors m).card : ℝ) ^ 2 := by
              refine Finset.sum_le_sum fun m _ => ?_
              rw [Complex.norm_real, Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (abs_vaughanTypeIICoeff_le_divisors U m) 2
          _ ≤ ∑ m ∈ Finset.Icc 1 (2 * M), ((Nat.divisors m).card : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      have hmax : max (2 * M) 1 = 2 * M := max_eq_left (by omega)
      have h2M_le_x : ((2 * M : ℕ) : ℝ) ≤ 2 * x := by
        have h1 : (2 * M : ℕ) ≤ 2 * ⌊x⌋₊ := h2M_le
        have h2 : ((2 * M : ℕ) : ℝ) ≤ 2 * (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
        exact h2.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx0) zero_le_two)
      have hlog_2M : 1 + Real.log (2 * (M : ℝ)) ≤ 4 * Real.log x := by
        have h12 : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * x) :=
          Real.log_le_log (by positivity) (by push_cast at h2M_le_x; exact h2M_le_x)
        have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul two_ne_zero (by linarith)
        have h2x : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
        have h1l : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [log_two_gt_half]
        linarith
      have hlog_2M_nn : 0 ≤ 1 + Real.log (2 * (M : ℝ)) := by
        have h1 : (1 : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * M)
        linarith [Real.log_nonneg h1]
      calc ∑ m ∈ Finset.Ioc M M', ‖(vaughanTypeIICoeff U m : ℂ)‖ ^ 2
          ≤ ((2 * M : ℕ) : ℝ) * (1 + Real.log ((max (2 * M) 1 : ℕ) : ℝ)) ^ 3 :=
            hdiv_sum.trans (sum_Icc_card_divisors_sq_le (2 * M))
        _ = (2 * (M : ℝ)) * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
            rw [hmax]; push_cast; rfl
        _ ≤ (2 * (M : ℝ)) * (4 * Real.log x) ^ 3 := by gcongr
    have hB : ∀ k ∈ Finset.Ioc V (⌊x⌋₊ / M), ‖(Λ k : ℂ)‖ ≤ Real.log x := by
      intro k hk
      simp only [Finset.mem_Ioc] at hk
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hk_pos : 1 ≤ k := hV.trans hk.1.le
      have hk_le_x : (k : ℝ) ≤ x := by
        have h1 : k ≤ ⌊x⌋₊ := hk.2.trans (Nat.div_le_self ⌊x⌋₊ M)
        exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hx0)
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hk_pos) hk_le_x)
    have hII := typeII_bilinear_exp_sum_bound hq hcop hα
      (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun k => (Λ k : ℂ))
      hM_pos hM'_le (x := x) hA2_nn hlog_pos.le hA2 hB
    rw [← hblock_eq] at hII
    let K := ⌊x⌋₊ / M
    have hM_posR : (0 : ℝ) < M := by exact_mod_cast hM_pos
    have hK_le : (K : ℝ) ≤ x / (M : ℝ) := by
      have h1 : K * M ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ M
      have h2 : (K : ℝ) * (M : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
      rw [le_div_iff₀ hM_posR]; exact h2.trans (Nat.floor_le hx0)
    have hKM_le : (K : ℝ) * (M : ℝ) ≤ x := by
      have := mul_le_mul_of_nonneg_right hK_le hM_posR.le
      rwa [div_mul_cancel₀ _ hM_posR.ne'] at this
    have hU_posR : (0 : ℝ) < U := by exact_mod_cast hU
    have hV_posR : (0 : ℝ) < V := by exact_mod_cast hV
    have hq_posR : (0 : ℝ) < q := by positivity
    have hM_ge_UR : (U : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_U
    have hM_le_xV : (M : ℝ) ≤ x / (V : ℝ) := by
      have h1 : M * V ≤ ⌊x⌋₊ := (Nat.mul_le_mul_right V hM_le_W).trans (Nat.div_mul_le_self ⌊x⌋₊ V)
      have h2 : (M : ℝ) * (V : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
      rw [le_div_iff₀ hV_posR]; exact h2.trans (Nat.floor_le hx0)
    have hterm1 : (M : ℝ) * ((K : ℝ) * (M : ℝ)) ≤ x ^ 2 / (V : ℝ) := by
      calc (M : ℝ) * ((K : ℝ) * (M : ℝ)) ≤ (x / (V : ℝ)) * x :=
            mul_le_mul hM_le_xV hKM_le (by positivity) (by positivity)
        _ = x ^ 2 / (V : ℝ) := by ring
    have hlog2q_nn : 0 ≤ Real.log (2 * (q : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have hterm2 : (M : ℝ) * ((K : ℝ) * ((K : ℝ) * Real.log (2 * (q : ℝ)))) ≤
        (x ^ 2 / (U : ℝ)) * (2 * Real.log x) := by
      calc (M : ℝ) * ((K : ℝ) * ((K : ℝ) * Real.log (2 * (q : ℝ))))
          ≤ (M : ℝ) * ((x / (M : ℝ)) * ((x / (M : ℝ)) * (2 * Real.log x))) := by gcongr
        _ = (x ^ 2 / (M : ℝ)) * (2 * Real.log x) := by field_simp [hM_posR.ne']
        _ ≤ (x ^ 2 / (U : ℝ)) * (2 * Real.log x) := by gcongr
    have hterm3 : (M : ℝ) * ((K : ℝ) * ((q : ℝ) * Real.log (2 * (q : ℝ)))) ≤
        (x * (q : ℝ)) * (2 * Real.log x) := by
      calc (M : ℝ) * ((K : ℝ) * ((q : ℝ) * Real.log (2 * (q : ℝ))))
          = ((K : ℝ) * (M : ℝ)) * ((q : ℝ) * Real.log (2 * (q : ℝ))) := by ring
        _ ≤ x * ((q : ℝ) * (2 * Real.log x)) := by gcongr
        _ = (x * (q : ℝ)) * (2 * Real.log x) := by ring
    have hterm4 : (M : ℝ) * ((K : ℝ) * ((K : ℝ) * (M : ℝ) / (q : ℝ))) ≤ x ^ 2 / (q : ℝ) := by
      calc (M : ℝ) * ((K : ℝ) * ((K : ℝ) * (M : ℝ) / (q : ℝ)))
          = ((K : ℝ) * (M : ℝ)) * ((K : ℝ) * (M : ℝ)) / (q : ℝ) := by ring
        _ ≤ x * x / (q : ℝ) := by gcongr
        _ = x ^ 2 / (q : ℝ) := by ring
    have hlogx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
    have h1_le_2logx : 1 ≤ 2 * Real.log x := by linarith [log_two_gt_half]
    have hinner_sq :
        (2 * (M : ℝ)) * ((K : ℝ) * (M : ℝ) + 18 * (K : ℝ) *
          (((K : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + (K : ℝ) * (M : ℝ) / (q : ℝ))) ≤
        72 * Real.log x *
          (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := by
      have hexp :
          (2 * (M : ℝ)) * ((K : ℝ) * (M : ℝ) + 18 * (K : ℝ) *
            (((K : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + (K : ℝ) * (M : ℝ) / (q : ℝ))) =
          2 * ((M : ℝ) * ((K : ℝ) * (M : ℝ))) +
            36 * ((M : ℝ) * ((K : ℝ) * ((K : ℝ) * Real.log (2 * (q : ℝ))))) +
            36 * ((M : ℝ) * ((K : ℝ) * ((q : ℝ) * Real.log (2 * (q : ℝ))))) +
            36 * ((M : ℝ) * ((K : ℝ) * ((K : ℝ) * (M : ℝ) / (q : ℝ)))) := by ring
      rw [hexp]
      have h1' : 2 * ((M : ℝ) * ((K : ℝ) * (M : ℝ))) ≤ 72 * Real.log x * (x ^ 2 / (V : ℝ)) := by
        have hv0 : 0 ≤ x ^ 2 / (V : ℝ) := by positivity
        calc 2 * ((M : ℝ) * ((K : ℝ) * (M : ℝ))) ≤ 2 * (x ^ 2 / (V : ℝ)) := by linarith [hterm1]
          _ ≤ 2 * ((2 * Real.log x) * (x ^ 2 / (V : ℝ))) :=
              mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hv0 h1_le_2logx) zero_le_two
          _ = 4 * Real.log x * (x ^ 2 / (V : ℝ)) := by ring
          _ ≤ 72 * Real.log x * (x ^ 2 / (V : ℝ)) := by
              have : 0 ≤ Real.log x * (x ^ 2 / (V : ℝ)) := mul_nonneg hlog_pos.le hv0
              linarith
      have h2' : 36 * ((M : ℝ) * ((K : ℝ) * ((K : ℝ) * Real.log (2 * (q : ℝ))))) ≤
          72 * Real.log x * (x ^ 2 / (U : ℝ)) := by
        calc 36 * ((M : ℝ) * ((K : ℝ) * ((K : ℝ) * Real.log (2 * (q : ℝ)))))
            ≤ 36 * ((x ^ 2 / (U : ℝ)) * (2 * Real.log x)) := by linarith [hterm2]
          _ = 72 * Real.log x * (x ^ 2 / (U : ℝ)) := by ring
      have h3' : 36 * ((M : ℝ) * ((K : ℝ) * ((q : ℝ) * Real.log (2 * (q : ℝ))))) ≤
          72 * Real.log x * (x * (q : ℝ)) := by
        calc 36 * ((M : ℝ) * ((K : ℝ) * ((q : ℝ) * Real.log (2 * (q : ℝ)))))
            ≤ 36 * ((x * (q : ℝ)) * (2 * Real.log x)) := by linarith [hterm3]
          _ = 72 * Real.log x * (x * (q : ℝ)) := by ring
      have h4' : 36 * ((M : ℝ) * ((K : ℝ) * ((K : ℝ) * (M : ℝ) / (q : ℝ)))) ≤
          72 * Real.log x * (x ^ 2 / (q : ℝ)) := by
        have hq0' : 0 ≤ x ^ 2 / (q : ℝ) := by positivity
        calc 36 * ((M : ℝ) * ((K : ℝ) * ((K : ℝ) * (M : ℝ) / (q : ℝ))))
            ≤ 36 * (x ^ 2 / (q : ℝ)) := by linarith [hterm4]
          _ ≤ 36 * ((2 * Real.log x) * (x ^ 2 / (q : ℝ))) :=
              mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hq0' h1_le_2logx) (by norm_num)
          _ = 72 * Real.log x * (x ^ 2 / (q : ℝ)) := by ring
      linarith
    have hsq_full :
        ‖∑ m ∈ block j, (vaughanTypeIICoeff U m : ℂ) *
            ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
          4624 * (Real.log x) ^ 6 *
            (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := by
      have hnonneg : 0 ≤ (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := by
        positivity
      calc _ ≤ A2 * (Real.log x) ^ 2 * _ := hII
        _ = 64 * (Real.log x) ^ 5 *
              ((2 * (M : ℝ)) * ((K : ℝ) * (M : ℝ) + 18 * (K : ℝ) *
                (((K : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + (K : ℝ) * (M : ℝ) / (q : ℝ)))) := by
              dsimp only [A2]; ring
        _ ≤ 64 * (Real.log x) ^ 5 *
              (72 * Real.log x * (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ))) := by
              gcongr
        _ = 4608 * (Real.log x) ^ 6 *
              (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := by ring
        _ ≤ 4624 * (Real.log x) ^ 6 *
              (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := by
              have hnn : 0 ≤ (Real.log x) ^ 6 *
                  (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := by positivity
              linarith only [hnn]
    have hsqrt_le := Real.sqrt_le_sqrt hsq_full
    have hleft_sq : Real.sqrt (‖∑ m ∈ block j, (vaughanTypeIICoeff U m : ℂ) *
        ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
        ‖∑ m ∈ block j, (vaughanTypeIICoeff U m : ℂ) *
          ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ :=
      Real.sqrt_sq (norm_nonneg _)
    rw [hleft_sq] at hsqrt_le
    have h68_sq : (4624 : ℝ) * (Real.log x) ^ 6 = (68 * (Real.log x) ^ 3) ^ 2 := by ring
    have h68_nn : 0 ≤ 68 * (Real.log x) ^ 3 := by positivity
    have hsum_sqrt :
        Real.sqrt (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) ≤
          Real.sqrt (x ^ 2 / (U : ℝ)) + Real.sqrt (x ^ 2 / (V : ℝ)) +
            Real.sqrt (x * (q : ℝ)) + Real.sqrt (x ^ 2 / (q : ℝ)) := by
      let r1 := Real.sqrt (x ^ 2 / (U : ℝ))
      let r2 := Real.sqrt (x ^ 2 / (V : ℝ))
      let r3 := Real.sqrt (x * (q : ℝ))
      let r4 := Real.sqrt (x ^ 2 / (q : ℝ))
      have hr_nn : 0 ≤ r1 + r2 + r3 + r4 := by positivity
      rw [← Real.sqrt_sq hr_nn]
      refine Real.sqrt_le_sqrt ?_
      have hsq1 : r1 ^ 2 = x ^ 2 / (U : ℝ) := Real.sq_sqrt (div_nonneg (sq_nonneg x) hU_posR.le)
      have hsq2 : r2 ^ 2 = x ^ 2 / (V : ℝ) := Real.sq_sqrt (div_nonneg (sq_nonneg x) hV_posR.le)
      have hsq3 : r3 ^ 2 = x * (q : ℝ) := Real.sq_sqrt (mul_nonneg hx0 hq_posR.le)
      have hsq4 : r4 ^ 2 = x ^ 2 / (q : ℝ) := Real.sq_sqrt (div_nonneg (sq_nonneg x) hq_posR.le)
      have hc12 : 0 ≤ r1 * r2 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hc13 : 0 ≤ r1 * r3 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hc14 : 0 ≤ r1 * r4 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hc23 : 0 ≤ r2 * r3 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hc24 : 0 ≤ r2 * r4 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hc34 : 0 ≤ r3 * r4 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hexp_sq : (r1 + r2 + r3 + r4) ^ 2 = r1 ^ 2 + r2 ^ 2 + r3 ^ 2 + r4 ^ 2 +
          2 * (r1 * r2 + r1 * r3 + r1 * r4 + r2 * r3 + r2 * r4 + r3 * r4) := by ring
      linarith only [hsq1, hsq2, hsq3, hsq4, hc12, hc13, hc14, hc23, hc24, hc34, hexp_sq]
    have hr1_eq : Real.sqrt (x ^ 2 / (U : ℝ)) = x * (U : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx0, div_eq_mul_inv, Real.sqrt_eq_rpow,
        Real.rpow_neg hU_posR.le]
    have hr2_eq : Real.sqrt (x ^ 2 / (V : ℝ)) = x * (V : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx0, div_eq_mul_inv, Real.sqrt_eq_rpow,
        Real.rpow_neg hV_posR.le]
    have hr3_eq : Real.sqrt (x * (q : ℝ)) = x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul hx0, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hr4_eq : Real.sqrt (x ^ 2 / (q : ℝ)) = x * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx0, div_eq_mul_inv, Real.sqrt_eq_rpow,
        Real.rpow_neg hq_posR.le]
    rw [Real.sqrt_mul (by positivity), h68_sq, Real.sqrt_sq h68_nn] at hsqrt_le
    calc _ ≤ 68 * (Real.log x) ^ 3 *
            Real.sqrt (x ^ 2 / (U : ℝ) + x ^ 2 / (V : ℝ) + x * (q : ℝ) + x ^ 2 / (q : ℝ)) := hsqrt_le
      _ ≤ 68 * (Real.log x) ^ 3 *
            (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
              x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
            rw [hr1_eq, hr2_eq, hr3_eq, hr4_eq] at hsum_sqrt
            exact mul_le_mul_of_nonneg_left hsum_sqrt h68_nn
  have hcard_blocks : ((Finset.Icc j₀ j₁).card : ℝ) ≤ 6 * Real.log x := by
    have hW_pos : 1 ≤ W := hU.trans hUV_x
    have hW_le_x : (W : ℝ) ≤ x := by
      have h1 : W ≤ ⌊x⌋₊ := Nat.div_le_self ⌊x⌋₊ V
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hx0)
    have hpow : (2 : ℝ) ^ j₁ ≤ (W : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog_pow : (j₁ : ℝ) * Real.log 2 ≤ Real.log (W : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow
    have hlog_W : Real.log (W : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast hW_pos) hW_le_x
    have hcard_le : (Finset.Icc j₀ j₁).card ≤ j₁ + 1 := by
      rw [Nat.card_Icc]; omega
    have hcard_R : ((Finset.Icc j₀ j₁).card : ℝ) ≤ (j₁ : ℝ) + 1 := by exact_mod_cast hcard_le
    nlinarith [log_two_gt_half, hlog_x1]
  have hrhs_nn : 0 ≤ x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
      x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc ‖∑ m ∈ Finset.Ioc U W, (vaughanTypeIICoeff U m : ℂ) *
        ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ j ∈ Finset.Icc j₀ j₁,
          ‖∑ m ∈ block j, (vaughanTypeIICoeff U m : ℂ) *
            ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ := hsum_split
    _ ≤ ∑ _j ∈ Finset.Icc j₀ j₁,
          68 * (Real.log x) ^ 3 *
            (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
              x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ))) :=
        Finset.sum_le_sum hblock_norm
    _ = ((Finset.Icc j₀ j₁).card : ℝ) *
          (68 * (Real.log x) ^ 3 *
            (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
              x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ)))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (6 * Real.log x) *
          (68 * (Real.log x) ^ 3 *
            (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
              x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcard_blocks (by positivity)
    _ = 408 * (Real.log x) ^ 4 *
          (x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
            x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring

/-- **Vinogradov's linear prime exponential sum bound**:
whenever `|α - a / q| ≤ 1 / q^2` with `gcd(a, q) = 1`, `1 ≤ q`, and `2 ≤ x`,
`‖∑_{1 ≤ n ≤ x} Λ(n) exp(2πi α n)‖ ≤
10000 * (x * q^(-1/2) + x^(4/5) + x^(1/2) * q^(1/2)) * (log x)^4`. -/
theorem vinogradov_prime_exp_sum_bound {α : ℝ} {a : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {x : ℝ} (hx : 2 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) *
        Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      10000 * (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
        x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1_R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcheb :
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) *
          Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 6 * x := by
    have hlog4 : Real.log 4 < 2 := by
      have hexp1 : (2 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
        linarith
      have hexp2 : (4 : ℝ) < Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith
      rw [← Real.log_exp 2]
      exact Real.log_lt_log (by norm_num) hexp2
    calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(Λ n : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            show Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
              vaughanE (α * n) from rfl, norm_vaughanE, mul_one]
      _ = Chebyshev.psi x := (psi_eq_sum_Icc x).symm
      _ ≤ (Real.log 4 + 4) * x := psi_le_const_mul_self hx0
      _ ≤ 6 * x := mul_le_mul_of_nonneg_right (by linarith) hx0
  by_cases hx32 : x < 32
  · have hx_split : x = x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_add hx_pos]; norm_num
    have hx15 : x ^ (1 / 5 : ℝ) ≤ 2 := by
      have h32 : x ^ (1 / 5 : ℝ) ≤ (32 : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hx0 hx32.le (by norm_num)
      have h32eq : (32 : ℝ) ^ (1 / 5 : ℝ) = 2 := by
        rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 5,
          ← Real.rpow_mul zero_le_two]
        norm_num
      linarith
    have hx45_nn : 0 ≤ x ^ (4 / 5 : ℝ) := Real.rpow_nonneg hx0 _
    have hlog4_lb : (1 / 16 : ℝ) ≤ (Real.log x) ^ 4 := by
      have hlog_ge : 1 / 2 ≤ Real.log x :=
        (log_two_gt_half.le).trans (Real.log_le_log zero_lt_two hx)
      calc (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.log x) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog_ge 4
    have hmain : 6 * x ≤ 192 * x ^ (4 / 5 : ℝ) * (Real.log x) ^ 4 := by
      calc 6 * x = 6 * (x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ)) := by rw [← hx_split]
        _ ≤ 6 * (2 * x ^ (4 / 5 : ℝ)) := by gcongr
        _ = 12 * x ^ (4 / 5 : ℝ) := by ring
        _ = 192 * x ^ (4 / 5 : ℝ) * (1 / 16 : ℝ) := by ring
        _ ≤ 192 * x ^ (4 / 5 : ℝ) * (Real.log x) ^ 4 := by gcongr
    have hsum_ge : x ^ (4 / 5 : ℝ) ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
        x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
      have ha : 0 ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
      have hb : 0 ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
      linarith
    calc _ ≤ 6 * x := hcheb
      _ ≤ 192 * x ^ (4 / 5 : ℝ) * (Real.log x) ^ 4 := hmain
      _ ≤ 10000 * (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
            x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by
          have hlog4_nn : 0 ≤ (Real.log x) ^ 4 := by positivity
          calc 192 * x ^ (4 / 5 : ℝ) * (Real.log x) ^ 4
              ≤ 10000 * x ^ (4 / 5 : ℝ) * (Real.log x) ^ 4 := by nlinarith
            _ ≤ 10000 * (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
                  x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by gcongr
  have hx32' : 32 ≤ x := not_lt.mp hx32
  by_cases hqx : (q : ℝ) ≤ x
  · let U : ℕ := ⌊x ^ (2 / 5 : ℝ)⌋₊
    let V : ℕ := U
    have hx25_ge4 : 4 ≤ x ^ (2 / 5 : ℝ) := by
      have h32_25 : (32 : ℝ) ^ (2 / 5 : ℝ) = 4 := by
        rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 5,
          ← Real.rpow_mul zero_le_two]
        norm_num
      rw [← h32_25]
      exact Real.rpow_le_rpow (by norm_num) hx32' (by norm_num)
    have hU4 : 4 ≤ U := (Nat.le_floor_iff (by positivity)).mpr hx25_ge4
    have hU1 : 1 ≤ U := by omega
    have hU_le : (U : ℝ) ≤ x ^ (2 / 5 : ℝ) := Nat.floor_le (by positivity)
    have hU_ge_half : x ^ (2 / 5 : ℝ) / 2 ≤ (U : ℝ) := by
      have hlt : x ^ (2 / 5 : ℝ) < (U : ℝ) + 1 := Nat.lt_floor_add_one _
      have hU4R : (4 : ℝ) ≤ U := by exact_mod_cast hU4
      linarith
    have hx15_ge2 : 2 ≤ x ^ (1 / 5 : ℝ) := by
      have h32_15 : (32 : ℝ) ^ (1 / 5 : ℝ) = 2 := by
        rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 5,
          ← Real.rpow_mul zero_le_two]
        norm_num
      rw [← h32_15]
      exact Real.rpow_le_rpow (by norm_num) hx32' (by norm_num)
    have hx45_le_x : x ^ (4 / 5 : ℝ) ≤ x := by
      calc x ^ (4 / 5 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = x := Real.rpow_one x
    have hx25_le_x : x ^ (2 / 5 : ℝ) ≤ x := by
      calc x ^ (2 / 5 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = x := Real.rpow_one x
    have hUV_le_45 : ((U * V : ℕ) : ℝ) ≤ x ^ (4 / 5 : ℝ) := by
      have hmul : (U : ℝ) * (V : ℝ) ≤ x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) :=
        mul_le_mul hU_le hU_le (by positivity) (by positivity)
      have hexp : x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) = x ^ (4 / 5 : ℝ) := by
        rw [← Real.rpow_add hx_pos]; norm_num
      push_cast; linarith
    have hUV_le_x : ((U * V : ℕ) : ℝ) ≤ x := hUV_le_45.trans hx45_le_x
    have hU_le_x : (U : ℝ) ≤ x := hU_le.trans hx25_le_x
    have hUV_div : U ≤ ⌊x⌋₊ / V := by
      refine (Nat.le_div_iff_mul_le hU1).mpr ?_
      exact (Nat.le_floor_iff hx0).mpr hUV_le_x
    have hvaughan := @vaughan_identity_sum x U U hU1
      (fun n => Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I))
    have hlog2q : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log x := real_log_two_mul_le_two_mul_log hx hq hqx
    have h1_le_2logx : 1 ≤ 2 * Real.log x := by
      have := Real.log_le_log zero_lt_two hx
      linarith [log_two_gt_half]
    have hq_sqrt : (q : ℝ) ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
      have h1 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hq0.le hqx (by norm_num)
      have h2 : (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hq0]; norm_num
      calc (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := h2
        _ ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by gcongr
    have hq_neg : x / (q : ℝ) ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (q : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ hx0
      exact Real.rpow_le_rpow_of_exponent_le hq1_R (by norm_num)
    let M : ℝ := x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
      x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)
    have hM_nn : 0 ≤ M := by positivity
    have hT0 :
        ‖∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), (Λ n : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
          96 * M * (Real.log x) ^ 4 := by
      have hlog4 : Real.log 4 < 2 := by
        have hexp1 : (2 : ℝ) < Real.exp 1 := by
          have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0); linarith
        have hexp2 : (4 : ℝ) < Real.exp 2 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
        rw [← Real.log_exp 2]; exact Real.log_lt_log (by norm_num) hexp2
      have hsub : Finset.Icc 1 (min ⌊x⌋₊ V) ⊆ Finset.Icc 1 ⌊(U : ℝ)⌋₊ := by
        intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        rw [Nat.floor_natCast]
        exact ⟨hn.1, hn.2.trans (min_le_right _ _)⟩
      have hle_psi :
          ‖∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), (Λ n : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 6 * x ^ (4 / 5 : ℝ) := by
        calc _ ≤ ∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V),
                ‖(Λ n : ℂ) * Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
              norm_sum_le _ _
          _ = ∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), Λ n := by
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
                show Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
                  vaughanE (α * n) from rfl, norm_vaughanE, mul_one]
          _ ≤ ∑ n ∈ Finset.Icc 1 ⌊(U : ℝ)⌋₊, Λ n :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
                ArithmeticFunction.vonMangoldt_nonneg
          _ = Chebyshev.psi (U : ℝ) := (psi_eq_sum_Icc (U : ℝ)).symm
          _ ≤ (Real.log 4 + 4) * (U : ℝ) := psi_le_const_mul_self (Nat.cast_nonneg U)
          _ ≤ 6 * x ^ (4 / 5 : ℝ) := by
              calc (Real.log 4 + 4) * (U : ℝ) ≤ 6 * (U : ℝ) :=
                    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg U)
                _ ≤ 6 * x ^ (2 / 5 : ℝ) := mul_le_mul_of_nonneg_left hU_le (by norm_num)
                _ ≤ 6 * x ^ (4 / 5 : ℝ) :=
                    mul_le_mul_of_nonneg_left
                      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
      have h16_log4 : 1 ≤ 16 * (Real.log x) ^ 4 := by
        have h1 : 1 / 2 ≤ Real.log x :=
          log_two_gt_half.le.trans (Real.log_le_log zero_lt_two hx)
        calc (1 : ℝ) = 16 * (1 / 2 : ℝ) ^ 4 := by norm_num
          _ ≤ 16 * (Real.log x) ^ 4 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h1 4) (by norm_num)
      calc _ ≤ 6 * x ^ (4 / 5 : ℝ) := hle_psi
        _ ≤ 6 * M := mul_le_mul_of_nonneg_left (by dsimp only [M]; linarith [show 0 ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) by positivity]) (by norm_num)
        _ ≤ (6 * M) * (16 * (Real.log x) ^ 4) := le_mul_of_one_le_right (by positivity) h16_log4
        _ = 96 * M * (Real.log x) ^ 4 := by ring
    have hlog2q_nn : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith [hq1_R])
    have hT1 :
        ‖∑ d ∈ Finset.Icc 1 U, (μ d : ℂ) *
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), (Real.log m : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
          864 * M * (Real.log x) ^ 4 := by
      have h1 := typeI_log_sum_bound hq hcop hα U hx
      have hmaxU : max U 1 = U := max_eq_left hU1
      have hlogU : 1 + Real.log ((max U 1 : ℕ) : ℝ) ≤ 3 * Real.log x := by
        rw [hmaxU]
        exact one_add_log_le_three_mul_log hx (by exact_mod_cast hU1) hU_le_x
      have hlogU_nn : 0 ≤ 1 + Real.log ((max U 1 : ℕ) : ℝ) := by positivity
      have hUx45 : (U : ℝ) ≤ x ^ (4 / 5 : ℝ) := hU_le.trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
      have hbr : ((U : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ) ≤
          2 * Real.log x * M := by
        have ha : ((U : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) ≤
            (x ^ (4 / 5 : ℝ) + x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (2 * Real.log x) :=
          mul_le_mul (add_le_add hUx45 hq_sqrt) hlog2q hlog2q_nn (by positivity)
        have hb : x / (q : ℝ) ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.log x) :=
          hq_neg.trans (le_mul_of_one_le_right (by positivity) h1_le_2logx)
        calc ((U : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ)
            ≤ (x ^ (4 / 5 : ℝ) + x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (2 * Real.log x) +
                x * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.log x) := add_le_add ha hb
          _ = 2 * Real.log x * M := by dsimp only [M]; ring
      have hbr_nn : 0 ≤ ((U : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ) :=
        add_nonneg (mul_nonneg (by positivity) hlog2q_nn) (by positivity)
      calc _ ≤ 72 * Real.log x * (1 + Real.log ((max U 1 : ℕ) : ℝ)) *
              (((U : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ)) := by
            simpa using h1
        _ ≤ 72 * Real.log x * (3 * Real.log x) * (2 * Real.log x * M) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hlogU (by positivity))
              hbr hbr_nn (by positivity)
        _ = 432 * M * (Real.log x) ^ 3 := by ring
        _ ≤ 432 * M * (Real.log x) ^ 3 * (2 * Real.log x) :=
            le_mul_of_one_le_right (by positivity) h1_le_2logx
        _ = 864 * M * (Real.log x) ^ 4 := by ring
    have hT2 :
        ‖∑ d ∈ Finset.Icc 1 (U * V), (vaughanTypeICoeff U V d : ℂ) *
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d),
              Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
          432 * M * (Real.log x) ^ 4 := by
      have hterm : ∀ d ∈ Finset.Icc 1 (U * V),
          ‖(vaughanTypeICoeff U V d : ℂ) *
              ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d),
                Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
            Real.log x * vLinBound (x / d) (α * d) := by
        intro d hd
        have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
        have hd_posR : (0 : ℝ) < d := by exact_mod_cast hd_pos
        have hd_le_x : (d : ℝ) ≤ x :=
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hd).2).trans hUV_le_x
        have hcoeff : ‖(vaughanTypeICoeff U V d : ℂ)‖ ≤ Real.log x := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (abs_vaughanTypeICoeff_le_log U V d).trans (Real.log_le_log hd_posR hd_le_x)
        have hdiv_le : ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ x / d := by
          have h1 : (⌊x⌋₊ / d : ℕ) * d ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ d
          have h2 : ((⌊x⌋₊ / d : ℕ) : ℝ) * d ≤ ⌊x⌋₊ := by exact_mod_cast h1
          rw [le_div_iff₀ hd_posR]; exact h2.trans (Nat.floor_le hx0)
        have hrew : ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d),
              Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I) =
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), vaughanE ((α * d) * m) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [vaughanE, Nat.cast_mul, Complex.ofReal_mul]; congr 1; ring
        rw [norm_mul, hrew]
        exact mul_le_mul hcoeff (norm_sum_Icc_one_vaughanE_le_vLinBound (α * d) (⌊x⌋₊ / d) hdiv_le)
          (norm_nonneg _) hlogx_pos.le
      have hUV1 : 1 ≤ U * V := Nat.mul_pos hU1 hU1
      have hmaxUV : max (U * V) 1 = U * V := max_eq_left hUV1
      have hlogUV : 1 + Real.log ((max (U * V) 1 : ℕ) : ℝ) ≤ 3 * Real.log x := by
        rw [hmaxUV]; exact one_add_log_le_three_mul_log hx (by exact_mod_cast hUV1) hUV_le_x
      have hbr : (((U * V : ℕ) : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ) ≤
          2 * Real.log x * M := by
        have ha : (((U * V : ℕ) : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) ≤
            (x ^ (4 / 5 : ℝ) + x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (2 * Real.log x) :=
          mul_le_mul (add_le_add hUV_le_45 hq_sqrt) hlog2q hlog2q_nn (by positivity)
        have hb : x / (q : ℝ) ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.log x) :=
          hq_neg.trans (le_mul_of_one_le_right (by positivity) h1_le_2logx)
        calc (((U * V : ℕ) : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ)
            ≤ (x ^ (4 / 5 : ℝ) + x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (2 * Real.log x) +
                x * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.log x) := add_le_add ha hb
          _ = 2 * Real.log x * M := by dsimp only [M]; ring
      have hbr_nn : 0 ≤ (((U * V : ℕ) : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ) :=
        add_nonneg (mul_nonneg (by positivity) hlog2q_nn) (by positivity)
      calc ‖∑ d ∈ Finset.Icc 1 (U * V), _‖
          ≤ ∑ d ∈ Finset.Icc 1 (U * V), ‖(vaughanTypeICoeff U V d : ℂ) * _‖ := norm_sum_le _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (U * V), Real.log x * vLinBound (x / d) (α * d) :=
            Finset.sum_le_sum hterm
        _ = Real.log x * ∑ d ∈ Finset.Icc 1 (U * V), vLinBound (x / d) (α * d) := by
            rw [← Finset.mul_sum]
        _ ≤ Real.log x * (36 * (1 + Real.log ((max (U * V) 1 : ℕ) : ℝ)) *
              ((((U * V : ℕ) : ℝ) + (q : ℝ)) * Real.log (2 * (q : ℝ)) + x / (q : ℝ))) := by
            gcongr; exact sum_Icc_dyadic_vLinBound_le hq hcop hα (U * V) hx0
        _ ≤ Real.log x * (36 * (3 * Real.log x) * (2 * Real.log x * M)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul_of_nonneg_left hlogUV (by norm_num)) hbr hbr_nn (by positivity))
              hlogx_pos.le
        _ = 216 * M * (Real.log x) ^ 3 := by ring
        _ ≤ 216 * M * (Real.log x) ^ 3 * (2 * Real.log x) :=
            le_mul_of_one_le_right (by positivity) h1_le_2logx
        _ = 432 * M * (Real.log x) ^ 4 := by ring
    have hT3 :
        ‖∑ m ∈ Finset.Ioc U (⌊x⌋₊ / V), (vaughanTypeIICoeff U m : ℂ) *
            ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ ≤
          1632 * M * (Real.log x) ^ 4 := by
      have hII := typeII_dyadic_sum_bound hq hcop hα U V hU1 hU1 hx hqx hUV_div hU_le_x hU_le_x
      have hU_neg : x * (U : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * x ^ (4 / 5 : ℝ) := by
        have h2 : (U : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * x ^ (-(1 / 5 : ℝ)) := by
          have hinv : ((U : ℝ) ^ (1 / 2 : ℝ))⁻¹ = (U : ℝ) ^ (-(1 / 2 : ℝ)) :=
            (Real.rpow_neg (by positivity) _).symm
          have hposU : 0 < (U : ℝ) := by exact_mod_cast hU1
          have hsq_half : (x ^ (2 / 5 : ℝ) / 2) ^ (1 / 2 : ℝ) ≤ (U : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hU_ge_half (by norm_num)
          have hmul_eq : x ^ (1 / 5 : ℝ) / 2 ≤ (x ^ (2 / 5 : ℝ) / 2) ^ (1 / 2 : ℝ) := by
            rw [Real.div_rpow (by positivity) zero_le_two, ← Real.rpow_mul hx0,
              show (2 / 5 : ℝ) * (1 / 2) = 1 / 5 by norm_num]
            have hsq2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
              have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
              simpa using h1
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq2
          have hlb : x ^ (1 / 5 : ℝ) / 2 ≤ (U : ℝ) ^ (1 / 2 : ℝ) := hmul_eq.trans hsq_half
          rw [← hinv, Real.rpow_neg hx0]
          calc ((U : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ (x ^ (1 / 5 : ℝ) / 2)⁻¹ :=
                (inv_anti₀ (by positivity) hlb)
            _ = 2 * (x ^ (1 / 5 : ℝ))⁻¹ := by ring
        calc x * (U : ℝ) ^ (-(1 / 2 : ℝ)) ≤ x * (2 * x ^ (-(1 / 5 : ℝ))) :=
              mul_le_mul_of_nonneg_left h2 hx0
          _ = 2 * (x ^ (1 : ℝ) * x ^ (-(1 / 5 : ℝ))) := by rw [Real.rpow_one]; ring
          _ = 2 * x ^ (4 / 5 : ℝ) := by rw [← Real.rpow_add hx_pos]; norm_num
      have hbr_le : x * (U : ℝ) ^ (-(1 / 2 : ℝ)) + x * (V : ℝ) ^ (-(1 / 2 : ℝ)) +
          x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 4 * M := by
        dsimp only [M, V] at *
        have hqp : 0 ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        have hxqp : 0 ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
        linarith
      calc _ ≤ 408 * (Real.log x) ^ 4 * _ := hII
        _ ≤ 408 * (Real.log x) ^ 4 * (4 * M) := by gcongr
        _ = 1632 * M * (Real.log x) ^ 4 := by ring
    have htri :
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) *
            Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
          ‖∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), (Λ n : ℂ) *
              Complex.exp (2 * Real.pi * ((α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ +
          ‖∑ d ∈ Finset.Icc 1 U, (μ d : ℂ) *
              ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), (Real.log m : ℂ) *
                Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ +
          ‖∑ d ∈ Finset.Icc 1 (U * V), (vaughanTypeICoeff U V d : ℂ) *
              ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d),
                Complex.exp (2 * Real.pi * ((α * (d * m : ℕ) : ℝ) : ℂ) * Complex.I)‖ +
          ‖∑ m ∈ Finset.Ioc U (⌊x⌋₊ / V), (vaughanTypeIICoeff U m : ℂ) *
              ∑ k ∈ Finset.Ioc V (⌊x⌋₊ / m), (Λ k : ℂ) *
                Complex.exp (2 * Real.pi * ((α * (m * k : ℕ) : ℝ) : ℂ) * Complex.I)‖ := by
      rw [hvaughan]
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    calc _ ≤ 96 * M * (Real.log x) ^ 4 + 864 * M * (Real.log x) ^ 4 +
            432 * M * (Real.log x) ^ 4 + 1632 * M * (Real.log x) ^ 4 :=
          htri.trans (add_le_add (add_le_add (add_le_add hT0 hT1) hT2) hT3)
      _ = 3024 * M * (Real.log x) ^ 4 := by ring
      _ ≤ 10000 * M * (Real.log x) ^ 4 := by
          have hnn : 0 ≤ M * (Real.log x) ^ 4 := by positivity
          linarith
  · have hxq : x < (q : ℝ) := not_le.mp hqx
    have hlog32 : 2 ≤ Real.log x := by
      have hexp : Real.exp 2 < 32 := by
        have h1 : Real.exp 1 < 4 := by
          have hhalf : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
            have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num); linarith
          have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
            rw [show (1 / 2 : ℝ) = -(-(1 / 2 : ℝ)) by ring, Real.exp_neg,
              inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
            linarith
          have hsq : Real.exp 1 = Real.exp (1 / 2 : ℝ) ^ 2 := by
            rw [sq, ← Real.exp_add]; congr 1; norm_num
          rw [hsq]; nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        have hsq2 : Real.exp 2 = Real.exp 1 ^ 2 := by
          rw [sq, ← Real.exp_add]; congr 1; norm_num
        rw [hsq2]; nlinarith [Real.exp_pos 1]
      calc 2 = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 2) (hexp.le.trans hx32')
    have hx_split : x ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
      have h1 : x ^ (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hx0 hxq.le (by norm_num)
      have h2 : x = x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hx_pos]; norm_num
      calc x = x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := h2
        _ ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by gcongr
    have hlog4_ge1 : 1 ≤ (Real.log x) ^ 4 := by
      calc (1 : ℝ) = (1 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.log x) ^ 4 := pow_le_pow_left₀ zero_le_one (by linarith) 4
    have hsum_ge : x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) ≤
        x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
          x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
      have : 0 ≤ x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) := by positivity
      linarith
    calc _ ≤ 6 * x := hcheb
      _ ≤ 6 * (x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) := by linarith
      _ ≤ 6 * (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
            x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by
          have h1 : 6 * (x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) ≤
              6 * (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
                x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) := by gcongr
          exact h1.trans (le_mul_of_one_le_right (by positivity) hlog4_ge1)
      _ ≤ 10000 * (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
            x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by
          have hnn : 0 ≤ (x * (q : ℝ) ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
              x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by positivity
          linarith

end VinogradovPrimeExpSum

end AnalyticNumberTheory.ExponentialSums

