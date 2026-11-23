import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Operations on Dirichlet Series and Classical Identities

This file provides algebraic operations on Dirichlet series (Dirichlet convolution, products,
powers, shifts `s ↦ s - a`, and dilations `s ↦ 2 * s`) together with a complete catalog of
classical Dirichlet series identities in their half-planes of absolute convergence:

- `1 / ζ(s) = ∑ μ(n) n^{-s}` (`Re s > 1`)
- `-ζ'(s) / ζ(s) = ∑ Λ(n) n^{-s}` (`Re s > 1`)
- `ζ(s)^2 = ∑ d(n) n^{-s}` (`Re s > 1`)
- `ζ(s) * ζ(s - a) = ∑ σ_a(n) n^{-s}` (`Re s > max 1 (1 + Re a)`)
- `ζ(s - 1) / ζ(s) = ∑ φ(n) n^{-s}` (`Re s > 2`)
- `ζ(2s) / ζ(s) = ∑ λ(n) n^{-s}` (`Re s > 1`)
- `ζ(s) / ζ(2s) = ∑ |μ(n)| n^{-s}` (`Re s > 1`)
- `ζ(s)^2 / ζ(2s) = ∑ 2^{ω(n)} n^{-s}` (`Re s > 1`)
-/

open Complex Filter
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.sigma
  ArithmeticFunction.omega ArithmeticFunction.vonMangoldt LSeries.notation

namespace AnalyticNumberTheory.DirichletSeries

/-! ### Helper Lemmas -/

private theorem LSeriesSummable_of_norm_le_of_ne_zero {f g : ℕ → ℂ} {s : ℂ}
    (hg : LSeriesSummable g s) (h : ∀ n ≠ 0, ‖f n‖ ≤ ‖g n‖) : LSeriesSummable f s := by
  rw [LSeriesSummable, ← summable_norm_iff] at hg ⊢
  refine hg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact LSeries.norm_term_le s (h n hn)

private theorem LSeriesSummable_zetaC_iff {s : ℂ} :
    LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s ↔ 1 < s.re := by
  simpa [ArithmeticFunction.natCoe_apply] using
    (ArithmeticFunction.LSeriesSummable_zeta_iff (s := s))

private theorem LSeries_zetaC_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(ζ : ArithmeticFunction ℂ) s = riemannZeta s := by
  simpa [ArithmeticFunction.natCoe_apply] using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

private theorem not_summable_prime_ite_div_rpow {c x : ℝ} (hc : 0 < c) (hx : x ≤ 1) :
    ¬ Summable (fun n : ℕ ↦ if n.Prime then c / (n : ℝ) ^ x else 0) := by
  intro h
  apply not_summable_one_div_on_primes
  have h1 : Summable (fun n : ℕ ↦ if n.Prime then (1 : ℝ) / n else 0) := by
    refine (h.div_const c).of_nonneg_of_le
      (fun n ↦ by split_ifs <;> positivity) (fun n ↦ ?_)
    split_ifs with hp
    · rw [div_div_cancel_left₀ hc.ne']
      have hpow : (n : ℝ) ^ x ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (mod_cast hp.one_lt.le) hx
      rw [Real.rpow_one] at hpow
      rw [← one_div]
      exact div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos (mod_cast hp.pos) _) hpow
    · simp
  refine h1.congr fun n ↦ ?_
  by_cases hp : n.Prime <;> simp [hp]

/-! ### General Dirichlet Convolution and Product Theorems -/

/-- Dirichlet convolution of sequences over a commutative semiring is commutative. -/
theorem convolution_comm {R : Type*} [CommSemiring R] (f g : ℕ → R) : f ⍟ g = g ⍟ f := by
  simp [LSeries.convolution, mul_comm]

/-- Dirichlet convolution of sequences over a semiring is associative. -/
theorem convolution_assoc {R : Type*} [Semiring R] (f g h : ℕ → R) :
    (f ⍟ g) ⍟ h = f ⍟ (g ⍟ h) := by
  simp [LSeries.convolution, mul_assoc]

/-- Convolving a sequence `f` (vanishing at `0`) on the right with `δ` yields `f`. -/
theorem convolution_delta {f : ℕ → ℂ} (hf : f 0 = 0) : f ⍟ δ = f := by
  have h1 : toArithmeticFunction δ = (1 : ArithmeticFunction ℂ) := by
    ext n
    by_cases hn : n = 0 <;> simp [toArithmeticFunction, LSeries.delta, ArithmeticFunction.one_apply, hn]
  ext n
  have h2 : toArithmeticFunction f n = f n := by
    by_cases hn : n = 0 <;> simp [toArithmeticFunction, hn, hf]
  simp [LSeries.convolution, h1, h2]

/-- Convolving `δ` on the left with a sequence `f` (vanishing at `0`) yields `f`. -/
theorem delta_convolution {f : ℕ → ℂ} (hf : f 0 = 0) : δ ⍟ f = f := by
  rw [convolution_comm, convolution_delta hf]

/-- The L-series of the Dirichlet convolution of two sequences equals the product of their
L-series when both converge absolutely at `s`. -/
theorem LSeries_convolution_eq {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) : LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution' hf hg

/-- The L-series of a power `f ^ k` in the Dirichlet ring converges absolutely at `s` whenever
`LSeriesSummable ↗f s`. -/
theorem LSeriesSummable_pow {f : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (k : ℕ) : LSeriesSummable ↗(f ^ k) s := by
  induction k with
  | zero =>
    rw [pow_zero]
    change LSeriesSummable ↗(1 : ArithmeticFunction ℂ) s
    rw [ArithmeticFunction.one_eq_delta]
    refine summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
    rw [Finset.mem_singleton] at hn
    simp [LSeries.term_delta, hn]
  | succ k ih =>
    rw [pow_succ]
    exact ArithmeticFunction.LSeriesSummable_mul ih hf

/-- The L-series of the `k`-th convolution power `f ^ k` equals `(LSeries ↗f s) ^ k` whenever
`LSeriesSummable ↗f s`. -/
theorem LSeries_pow {f : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s) (k : ℕ) :
    LSeries ↗(f ^ k) s = LSeries ↗f s ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    change LSeries ↗(1 : ArithmeticFunction ℂ) s = 1
    rw [ArithmeticFunction.one_eq_delta, LSeries_delta, Pi.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, ArithmeticFunction.LSeries_mul' (LSeriesSummable_pow hf k) hf, ih]

/-- If `f * g = 1` in `ArithmeticFunction ℂ` and both L-series converge absolutely at `s`, then
`LSeries ↗f s ≠ 0` and `LSeries ↗g s = (LSeries ↗f s)⁻¹`. -/
theorem LSeries_eq_inv_of_mul_eq_one {f g : ArithmeticFunction ℂ} (hfg : f * g = 1) {s : ℂ}
    (hf : LSeriesSummable ↗f s) (hg : LSeriesSummable ↗g s) :
    LSeries ↗f s ≠ 0 ∧ LSeries ↗g s = (LSeries ↗f s)⁻¹ := by
  have hprod : LSeries ↗f s * LSeries ↗g s = 1 := by
    rw [← ArithmeticFunction.LSeries_mul' hf hg, hfg, ArithmeticFunction.one_eq_delta,
      LSeries_delta, Pi.one_apply]
  have hne : LSeries ↗f s ≠ 0 := fun h ↦ by simp [h] at hprod
  exact ⟨hne, eq_inv_of_mul_eq_one_right hprod⟩

/-! ### Shifts (`s ↦ s - a`) and Dilations (`s ↦ 2 * s`) -/

/-- Pointwise twist of `f : ℕ → ℂ` by `n ↦ n ^ a` (vanishing at `0`). -/
noncomputable def powMul (a : ℂ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if n = 0 then 0 else (n : ℂ) ^ a * f n

/-- Each L-series term of `powMul a f` at `s` equals the corresponding term of `f` at `s - a`. -/
theorem term_powMul (a : ℂ) (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (powMul a f) s n = LSeries.term f (s - a) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, powMul, ite_eq_right hn]
    rw [cpow_sub _ _ hnC]
    field_simp

/-- The L-series of `powMul a f` converges absolutely at `s` if and only if the L-series of `f`
converges absolutely at `s - a`. -/
theorem LSeriesSummable_powMul_iff (a : ℂ) (f : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (powMul a f) s ↔ LSeriesSummable f (s - a) := by
  rw [LSeriesSummable, LSeriesSummable]
  exact summable_congr (term_powMul a f s)

/-- Shifting the Dirichlet series variable by `a`: `LSeries (powMul a f) s = LSeries f (s - a)`. -/
theorem LSeries_powMul (a : ℂ) (f : ℕ → ℂ) (s : ℂ) :
    LSeries (powMul a f) s = LSeries f (s - a) := by
  simp only [LSeries, term_powMul]

/-- The sequence supported on positive square integers sending `m ^ 2` to `f m`. -/
noncomputable def sqDilate (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if n ≠ 0 ∧ IsSquare n then f (Nat.sqrt n) else 0

private theorem term_sqDilate_sq (f : ℕ → ℂ) (s : ℂ) (m : ℕ) :
    LSeries.term (sqDilate f) s (m ^ 2) = LSeries.term f (2 * s) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hsq : IsSquare (m ^ 2) := ⟨m, sq m⟩
    have hsqrt : Nat.sqrt (m ^ 2) = m := by rw [sq, Nat.sqrt_eq m]
    rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm, sqDilate,
      ite_eq_left ⟨hm2, hsq⟩, hsqrt]
    congr 1
    rw [sq, Nat.cast_mul, ← Complex.ofReal_natCast,
      Complex.mul_cpow_ofReal_nonneg m.cast_nonneg m.cast_nonneg, Complex.ofReal_natCast,
      ← cpow_add _ _ hmC, two_mul]

private theorem term_sqDilate_eq_zero_of_not_range (f : ℕ → ℂ) (s : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ ↦ m ^ 2)) : LSeries.term (sqDilate f) s n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hnsq : ¬ IsSquare n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, by ring⟩
    simp [LSeries.term_of_ne_zero hn0, sqDilate, hnsq]

/-- The L-series of `sqDilate f` converges absolutely at `s` if and only if that of `f` converges
absolutely at `2 * s`. -/
theorem LSeriesSummable_sqDilate_iff (f : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (sqDilate f) s ↔ LSeriesSummable f (2 * s) := by
  have hinj : Function.Injective (fun m : ℕ ↦ m ^ 2) := Nat.pow_left_injective two_ne_zero
  rw [LSeriesSummable, LSeriesSummable,
    ← hinj.summable_iff (f := LSeries.term (sqDilate f) s)
      (fun n hn ↦ term_sqDilate_eq_zero_of_not_range f s hn)]
  exact summable_congr fun m ↦ term_sqDilate_sq f s m

/-- Dilation of the variable by `2`: `LSeries (sqDilate f) s = LSeries f (2 * s)`. -/
theorem LSeries_sqDilate (f : ℕ → ℂ) (s : ℂ) :
    LSeries (sqDilate f) s = LSeries f (2 * s) := by
  have hinj : Function.Injective (fun m : ℕ ↦ m ^ 2) := Nat.pow_left_injective two_ne_zero
  have hsupp : Function.support (LSeries.term (sqDilate f) s) ⊆ Set.range (fun m : ℕ ↦ m ^ 2) := by
    intro n hn
    by_contra h
    exact hn (term_sqDilate_eq_zero_of_not_range f s h)
  rw [LSeries, LSeries, ← hinj.tsum_eq hsupp]
  exact tsum_congr fun m ↦ term_sqDilate_sq f s m

/-! ### Arithmetic Functions and Classical Convolution Identities -/

/-- Euler's totient function `φ` bundled as an `ArithmeticFunction ℕ`. -/
def totientAF : ArithmeticFunction ℕ where
  toFun := Nat.totient
  map_zero' := Nat.totient_zero

/-- Evaluation of `totientAF` at `n`. -/
@[simp]
theorem totientAF_apply (n : ℕ) : totientAF n = n.totient := rfl

/-- `totientAF` is multiplicative. -/
theorem isMultiplicative_totientAF : totientAF.IsMultiplicative :=
  ⟨Nat.totient_one, fun {_ _} h ↦ Nat.totient_mul h⟩

/-- The complex-valued arithmetic function `n ↦ n ^ a` (vanishing at `0`). -/
noncomputable def powC (a : ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else (n : ℂ) ^ a
  map_zero' := rfl

/-- Evaluation of `powC a` at positive integers `n ≠ 0`. -/
@[simp]
theorem powC_apply_ne {a : ℂ} {n : ℕ} (hn : n ≠ 0) : powC a n = (n : ℂ) ^ a :=
  ite_eq_right hn

/-- Complex divisor-power sum function `σ_a(n) = ∑_{d ∣ n} d^a`. -/
noncomputable def sigmaC (a : ℂ) : ArithmeticFunction ℂ where
  toFun n := ∑ d ∈ n.divisors, (d : ℂ) ^ a
  map_zero' := by simp

/-- Evaluation of `sigmaC a` at `n`. -/
@[simp]
theorem sigmaC_apply (a : ℂ) (n : ℕ) : sigmaC a n = ∑ d ∈ n.divisors, (d : ℂ) ^ a := rfl

/-- For a natural number `k`, `sigmaC k` agrees with the coercion of `ArithmeticFunction.sigma k`. -/
theorem sigmaC_natCast (k n : ℕ) : sigmaC k n = (σ k n : ℂ) := by
  simp [sigmaC, ArithmeticFunction.sigma_apply]

private theorem isSquare_mul_iff_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) : IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  rw [Nat.isSquare_iff_even_factorization, Nat.isSquare_iff_even_factorization,
    Nat.isSquare_iff_even_factorization]
  constructor
  · intro h
    constructor <;> intro p hp
    · by_cases hpm : p ∣ m
      · have hpn : ¬ p ∣ n := fun hpn ↦ hp.ne_one (Nat.dvd_one.mp (hmn ▸ Nat.dvd_gcd hpm hpn))
        have hfac := h p hp
        rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpn, add_zero] at hfac
        exact hfac
      · rw [Nat.factorization_eq_zero_of_not_dvd hpm]
        exact Even.zero
    · by_cases hpn : p ∣ n
      · have hpm : ¬ p ∣ m := fun hpm ↦ hp.ne_one (Nat.dvd_one.mp (hmn ▸ Nat.dvd_gcd hpm hpn))
        have hfac := h p hp
        rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpm, zero_add] at hfac
        exact hfac
      · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
        exact Even.zero
  · rintro ⟨hm_sq, hn_sq⟩ p hp
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
    exact (hm_sq p hp).add (hn_sq p hp)

private theorem isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) :
    IsSquare (p ^ k) ↔ Even k := by
  rw [Nat.isSquare_iff_even_factorization]
  constructor
  · intro h
    have := h p hp
    simpa [hp.factorization_self] using this
  · intro hk q hq
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact hk.mul_right _

/-- Indicator arithmetic function of positive square integers. -/
def sqIndicatorAF : ArithmeticFunction ℤ where
  toFun n := if n ≠ 0 ∧ IsSquare n then 1 else 0
  map_zero' := by simp

/-- Evaluation of `sqIndicatorAF` at `n`. -/
@[simp]
theorem sqIndicatorAF_apply (n : ℕ) :
    sqIndicatorAF n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := rfl

/-- `sqIndicatorAF` is multiplicative. -/
theorem isMultiplicative_sqIndicatorAF : sqIndicatorAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {m n} hm hn hmn ↦ ?_⟩
  simp only [sqIndicatorAF_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true,
    true_and, isSquare_mul_iff_of_coprime hm hn hmn]
  by_cases h1 : IsSquare m <;> by_cases h2 : IsSquare n <;> simp [h1, h2]

/-- Arithmetic function supported on positive squares taking value `μ(√n)`. -/
def moebiusSqAF : ArithmeticFunction ℤ where
  toFun n := if n ≠ 0 ∧ IsSquare n then μ (Nat.sqrt n) else 0
  map_zero' := by simp

/-- Evaluation of `moebiusSqAF` at `n`. -/
@[simp]
theorem moebiusSqAF_apply (n : ℕ) :
    moebiusSqAF n = if n ≠ 0 ∧ IsSquare n then μ (Nat.sqrt n) else 0 := rfl

/-- `moebiusSqAF` is multiplicative. -/
theorem isMultiplicative_moebiusSqAF : moebiusSqAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {m n} hm hn hmn ↦ ?_⟩
  simp only [moebiusSqAF_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    isSquare_mul_iff_of_coprime hm hn hmn]
  by_cases h1 : IsSquare m <;> by_cases h2 : IsSquare n <;> simp [h1, h2]
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have ha0 : a ≠ 0 := by rintro rfl; simp [ha] at hm
  have hb0 : b ≠ 0 := by rintro rfl; simp [hb] at hn
  have hma : m = a * a := ha
  have hnb : n = b * b := hb
  have hab : a.Coprime b := by
    have hmn' : Nat.Coprime (a * a) (b * b) := hma ▸ hnb ▸ hmn
    exact (Nat.Coprime.coprime_dvd_left (dvd_mul_left a a) hmn').coprime_dvd_right
      (dvd_mul_left b b)
  rw [hma, hnb]
  have hsq : a * a * (b * b) = (a * b) * (a * b) := by ring
  rw [hsq, Nat.sqrt_eq (a * b), Nat.sqrt_eq a, Nat.sqrt_eq b]
  exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab

/-- Indicator arithmetic function of squarefree positive integers (`|μ(n)|`). -/
def absMoebiusAF : ArithmeticFunction ℕ where
  toFun n := if Squarefree n then 1 else 0
  map_zero' := by simp [not_squarefree_zero]

/-- Evaluation of `absMoebiusAF` at `n`. -/
@[simp]
theorem absMoebiusAF_apply (n : ℕ) :
    absMoebiusAF n = if Squarefree n then 1 else 0 := rfl

/-- `absMoebiusAF` equals `|μ(n)|` when coerced to `ℤ`. -/
theorem absMoebiusAF_coe_int (n : ℕ) : (absMoebiusAF n : ℤ) = |μ n| := by
  simp [absMoebiusAF, ArithmeticFunction.abs_moebius]

/-- `absMoebiusAF` is multiplicative. -/
theorem isMultiplicative_absMoebiusAF : absMoebiusAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {m n} _ _ hmn ↦ ?_⟩
  simp only [absMoebiusAF_apply, Nat.squarefree_mul hmn]
  by_cases h1 : Squarefree m <;> by_cases h2 : Squarefree n <;> simp [h1, h2]

/-- The arithmetic function `n ↦ 2 ^ ω(n)` (vanishing at `0`). -/
def twoPowOmegaAF : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else 2 ^ ω n
  map_zero' := rfl

/-- Evaluation of `twoPowOmegaAF` at positive integers `n ≠ 0`. -/
@[simp]
theorem twoPowOmegaAF_apply_ne {n : ℕ} (hn : n ≠ 0) : twoPowOmegaAF n = 2 ^ ω n :=
  ite_eq_right hn

/-- `twoPowOmegaAF` is multiplicative. -/
theorem isMultiplicative_twoPowOmegaAF : twoPowOmegaAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {m n} hm hn hmn ↦ ?_⟩
  simp [twoPowOmegaAF, mul_ne_zero hm hn, hm, hn,
    ArithmeticFunction.cardDistinctFactors_mul hmn, pow_add]

/-- Convolution identity `ζ * powC a = sigmaC a`. -/
theorem zeta_mul_powC_eq_sigmaC (a : ℂ) : (ζ : ArithmeticFunction ℂ) * powC a = sigmaC a := by
  ext n
  rw [ArithmeticFunction.coe_zeta_mul_apply, sigmaC_apply]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [powC_apply_ne hd0]

/-- Convolution identity `ζ * totientAF = ArithmeticFunction.id`. -/
theorem zeta_mul_totientAF_eq_id : ζ * totientAF = ArithmeticFunction.id := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.zeta_mul_apply]
    simp [Nat.sum_totient n]

private theorem sum_range_neg_one_pow (k : ℕ) :
    ∑ x ∈ Finset.range (k + 1), (-1 : ℤ) ^ x = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : Even k
    · have hne : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using hk
      have hodd : Odd (k + 1) := Nat.not_even_iff_odd.mp hne
      simp [hk, hne, hodd.neg_one_pow]
    · have hev : Even (k + 1) := Nat.even_add_one.mpr hk
      simp [hk, hev, hev.neg_one_pow]

/-- Convolution identity `ζ * λ = sqIndicatorAF` in `ArithmeticFunction ℤ`. -/
theorem zeta_mul_liouville_eq_sqIndicator :
    (ζ : ArithmeticFunction ℤ) * ArithmeticFunction.liouville = sqIndicatorAF := by
  have hmul : ((ζ : ArithmeticFunction ℤ) * ArithmeticFunction.liouville).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      ArithmeticFunction.isMultiplicative_liouville
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    isMultiplicative_sqIndicatorAF]
  intro p k hp
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  have hsum : ∑ x ∈ Finset.range (k + 1), ArithmeticFunction.liouville (p ^ x) =
      ∑ x ∈ Finset.range (k + 1), (-1 : ℤ) ^ x := by
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [ArithmeticFunction.liouville_apply (pow_ne_zero x hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp]
  rw [hsum, sum_range_neg_one_pow, sqIndicatorAF_apply]
  have hne : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  simp only [hne, ne_eq, not_false_eq_true, true_and, isSquare_prime_pow_iff hp]

/-- Convolution identity `ζ * moebiusSqAF = absMoebiusAF` in `ArithmeticFunction ℤ`. -/
theorem zeta_mul_moebiusSq_eq_absMoebius :
    (ζ : ArithmeticFunction ℤ) * moebiusSqAF = (absMoebiusAF : ArithmeticFunction ℤ) := by
  have hmul : ((ζ : ArithmeticFunction ℤ) * moebiusSqAF).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul isMultiplicative_moebiusSqAF
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    isMultiplicative_absMoebiusAF.natCast]
  intro p k hp
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp,
    ArithmeticFunction.natCoe_apply, absMoebiusAF_apply]
  have h1 : moebiusSqAF p = 0 := by
    rw [moebiusSqAF_apply, ite_eq_right]
    intro h
    have he := (isSquare_prime_pow_iff hp (k := 1)).mp (by simpa using h.2)
    exact (by decide : ¬ Even 1) he
  rcases k with _ | _ | k
  · simp
  · rw [pow_one, ite_eq_left hp.squarefree, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
      pow_one, moebiusSqAF_apply, ite_eq_left ⟨one_ne_zero, ⟨1, one_mul 1⟩⟩, Nat.sqrt_one,
      ArithmeticFunction.moebius_apply_one, h1, add_zero]
    rfl
  · have hnsq : ¬ Squarefree (p ^ (k + 2)) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      omega
    rw [ite_eq_right hnsq]
    have hzero : ∀ x ∈ Finset.range (k + 3), 3 ≤ x → moebiusSqAF (p ^ x) = 0 := by
      intro x _ hx
      rw [moebiusSqAF_apply]
      split_ifs with h
      · obtain ⟨j, hj⟩ := (isSquare_prime_pow_iff hp).mp h.2
        have hj2 : j ≥ 2 := by omega
        have hsqrt : Nat.sqrt (p ^ x) = p ^ j := by
          rw [hj, ← two_mul, mul_comm 2 j, pow_mul, sq, Nat.sqrt_eq (p ^ j)]
        rw [hsqrt, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show j ≠ 1 by omega]
      · rfl
    have htrunc : ∑ x ∈ Finset.range (k + 3), moebiusSqAF (p ^ x) =
        ∑ x ∈ Finset.range 3, moebiusSqAF (p ^ x) := by
      have hsplit := Finset.sum_range_add_sum_Ico (fun x ↦ moebiusSqAF (p ^ x)) (m := 3)
        (n := k + 3) (by omega)
      rw [← hsplit]
      have htail : ∑ x ∈ Finset.Ico 3 (k + 3), moebiusSqAF (p ^ x) = 0 :=
        Finset.sum_eq_zero fun x hx ↦ hzero x (Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2)
          (Finset.mem_Ico.mp hx).1
      rw [htail, add_zero]
    rw [htrunc, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h2 : moebiusSqAF (p ^ 2) = -1 := by
      rw [moebiusSqAF_apply, ite_eq_left ⟨pow_ne_zero 2 hp.ne_zero, ⟨p, sq p⟩⟩, sq, Nat.sqrt_eq p,
        ArithmeticFunction.moebius_apply_prime hp]
    simp [h1, h2]

/-- Convolution identity `ζ * absMoebiusAF = twoPowOmegaAF` in `ArithmeticFunction ℕ`. -/
theorem zeta_mul_absMoebius_eq_twoPowOmega : ζ * absMoebiusAF = twoPowOmegaAF := by
  have hmul : (ζ * absMoebiusAF).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.mul isMultiplicative_absMoebiusAF
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    isMultiplicative_twoPowOmegaAF]
  intro p k hp
  rw [ArithmeticFunction.zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Finset.sum_range_one, pow_zero, absMoebiusAF_apply, ite_eq_left squarefree_one,
      twoPowOmegaAF_apply_ne one_ne_zero, ArithmeticFunction.cardDistinctFactors_one, pow_zero]
  · rw [twoPowOmegaAF_apply_ne (pow_ne_zero k hp.ne_zero),
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp hk, pow_one]
    have hzero : ∀ x ∈ Finset.range (k + 1), 2 ≤ x → absMoebiusAF (p ^ x) = 0 := by
      intro x _ hx
      rw [absMoebiusAF_apply, ite_eq_right]
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      omega
    have hk2 : 2 ≤ k + 1 := by omega
    have hsplit := Finset.sum_range_add_sum_Ico (fun x ↦ absMoebiusAF (p ^ x)) (m := 2)
      (n := k + 1) hk2
    rw [← hsplit]
    have htail : ∑ x ∈ Finset.Ico 2 (k + 1), absMoebiusAF (p ^ x) = 0 :=
      Finset.sum_eq_zero fun x hx ↦ hzero x (Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2)
        (Finset.mem_Ico.mp hx).1
    rw [htail, add_zero, Finset.sum_range_succ, Finset.sum_range_one]
    simp [absMoebiusAF_apply, hp.squarefree]

/-! ### Classical Dirichlet Series Identities -/

/-- The L-series of the Möbius function converges absolutely at `s` iff `1 < Re s`. -/
theorem LSeriesSummable_moebius_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re :=
  ArithmeticFunction.LSeriesSummable_moebius_iff

/-- `1 / ζ(s) = ∑ μ(n) n^{-s}` for `1 < Re s` (inverse form). -/
theorem LSeries_moebius_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗μ s = (riemannZeta s)⁻¹ := by
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
  exact eq_inv_of_mul_eq_one_right hmul

/-- `1 / ζ(s) = ∑ μ(n) n^{-s}` for `1 < Re s`. -/
theorem LSeries_moebius_eq_one_div_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗μ s = 1 / riemannZeta s := by
  rw [LSeries_moebius_eq_inv_riemannZeta hs, one_div]

private theorem not_LSeriesSummable_vonMangoldt_at_one : ¬ LSeriesSummable ↗Λ 1 := by
  intro h
  refine not_summable_prime_ite_div_rpow (Real.log_pos one_lt_two) le_rfl ?_
  refine (summable_norm_iff.mpr h).of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity) fun n ↦ ?_
  split_ifs with hp
  · have hp2 : (2 : ℝ) ≤ n := mod_cast hp.two_le
    rw [LSeries.norm_term_eq, ite_eq_right hp.ne_zero, one_re, Real.rpow_one,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact div_le_div_of_nonneg_right (Real.log_le_log zero_lt_two hp2) n.cast_nonneg
  · exact norm_nonneg _

/-- The L-series of the von Mangoldt function converges absolutely at `s` iff `1 < Re s`. -/
theorem LSeriesSummable_vonMangoldt_iff {s : ℂ} : LSeriesSummable ↗Λ s ↔ 1 < s.re := by
  refine ⟨fun h ↦ ?_, ArithmeticFunction.LSeriesSummable_vonMangoldt⟩
  by_contra! hs
  exact not_LSeriesSummable_vonMangoldt_at_one (h.of_re_le_re (by simpa using hs))

/-- `-ζ'(s) / ζ(s) = ∑ Λ(n) n^{-s}` for `1 < Re s`. -/
theorem LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗Λ s = -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- The L-series of the divisor-count function `d(n) = σ₀(n)` converges absolutely at `s` iff
`1 < Re s`. -/
theorem LSeriesSummable_sigma_zero_iff {s : ℂ} : LSeriesSummable ↗(σ 0) s ↔ 1 < s.re := by
  constructor
  · intro h
    rw [← LSeriesSummable_one_iff (s := s)]
    refine LSeriesSummable_of_norm_le_of_ne_zero h fun n hn ↦ ?_
    simp only [Pi.one_apply, norm_one, Complex.norm_natCast]
    exact mod_cast ArithmeticFunction.sigma_pos 0 n hn
  · intro hs
    have hmul : (ζ : ArithmeticFunction ℂ) * ζ = (σ 0 : ArithmeticFunction ℂ) := by
      rw [← ArithmeticFunction.natCoe_mul]
      nth_rw 2 [← ArithmeticFunction.pow_zero_eq_zeta]
      rw [ArithmeticFunction.zeta_mul_pow_eq_sigma]
    have hmul_sum := ArithmeticFunction.LSeriesSummable_mul
      (LSeriesSummable_zetaC_iff.mpr hs) (LSeriesSummable_zetaC_iff.mpr hs)
    rw [hmul] at hmul_sum
    simpa [ArithmeticFunction.natCoe_apply] using hmul_sum

/-- `ζ(s)^2 = ∑ d(n) n^{-s}` for `1 < Re s`. -/
theorem LSeries_sigma_zero_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(σ 0) s = riemannZeta s ^ 2 := by
  have hmul : (ζ : ArithmeticFunction ℂ) * ζ = (σ 0 : ArithmeticFunction ℂ) := by
    rw [← ArithmeticFunction.natCoe_mul]
    nth_rw 2 [← ArithmeticFunction.pow_zero_eq_zeta]
    rw [ArithmeticFunction.zeta_mul_pow_eq_sigma]
  have hprod := ArithmeticFunction.LSeries_mul'
    (LSeriesSummable_zetaC_iff.mpr hs) (LSeriesSummable_zetaC_iff.mpr hs)
  rw [hmul, LSeries_zetaC_eq_riemannZeta hs, ← sq] at hprod
  simpa [ArithmeticFunction.natCoe_apply] using hprod

/-- `ζ(s)^2 = ∑ #(divisors n) n^{-s}` for `1 < Re s`. -/
theorem LSeries_card_divisors_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ ((n.divisors.card : ℕ) : ℂ)) s = riemannZeta s ^ 2 := by
  refine (LSeries_congr (fun {n} _ ↦ ?_) s).trans (LSeries_sigma_zero_eq hs)
  simp [ArithmeticFunction.sigma_zero_apply]

/-- The L-series of `σ_a` converges absolutely when `max 1 (1 + Re a) < Re s`. -/
theorem LSeriesSummable_sigmaC {a s : ℂ} (hs : max 1 (1 + a.re) < s.re) :
    LSeriesSummable ↗(sigmaC a) s := by
  have hs1 : 1 < s.re := (le_max_left _ _).trans_lt hs
  have hsa : 1 < (s - a).re := by
    rw [sub_re]
    have h2 := (le_max_right 1 (1 + a.re)).trans_lt hs
    linarith
  have hpow : LSeriesSummable ↗(powC a) s := by
    refine (LSeriesSummable_congr (f := powMul a 1) (g := ↗(powC a)) s ?_).mp ?_
    · intro n hn
      simp [powMul, ite_eq_right hn, powC_apply_ne hn]
    · rw [LSeriesSummable_powMul_iff, LSeriesSummable_one_iff]
      exact hsa
  rw [← zeta_mul_powC_eq_sigmaC]
  exact ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zetaC_iff.mpr hs1) hpow

/-- `ζ(s) * ζ(s - a) = ∑ σ_a(n) n^{-s}` when `max 1 (1 + Re a) < Re s`. -/
theorem LSeries_sigmaC_eq {a s : ℂ} (hs : max 1 (1 + a.re) < s.re) :
    LSeries ↗(sigmaC a) s = riemannZeta s * riemannZeta (s - a) := by
  have hs1 : 1 < s.re := (le_max_left _ _).trans_lt hs
  have hsa : 1 < (s - a).re := by
    rw [sub_re]
    have h2 := (le_max_right 1 (1 + a.re)).trans_lt hs
    linarith
  have hpow_sum : LSeriesSummable ↗(powC a) s := by
    refine (LSeriesSummable_congr (f := powMul a 1) (g := ↗(powC a)) s ?_).mp ?_
    · intro n hn
      simp [powMul, ite_eq_right hn, powC_apply_ne hn]
    · rw [LSeriesSummable_powMul_iff, LSeriesSummable_one_iff]
      exact hsa
  have hpow_eq : LSeries ↗(powC a) s = riemannZeta (s - a) := by
    have hc : LSeries ↗(powC a) s = LSeries (powMul a 1) s :=
      LSeries_congr (fun {n} hn ↦ by simp [powMul, ite_eq_right hn, powC_apply_ne hn]) s
    rw [hc, LSeries_powMul, LSeries_one_eq_riemannZeta hsa]
  rw [← zeta_mul_powC_eq_sigmaC, ArithmeticFunction.LSeries_mul'
    (LSeriesSummable_zetaC_iff.mpr hs1) hpow_sum,
    LSeries_zetaC_eq_riemannZeta hs1, hpow_eq]

/-- For natural `k`, the L-series of `σ_k` converges absolutely at `s` iff `1 + k < Re s`. -/
theorem LSeriesSummable_sigma_iff {k : ℕ} {s : ℂ} :
    LSeriesSummable ↗(σ k) s ↔ 1 + (k : ℝ) < s.re := by
  constructor
  · intro h
    have hpow : LSeriesSummable (powMul k 1) s := by
      refine LSeriesSummable_of_norm_le_of_ne_zero h fun n hn ↦ ?_
      rw [powMul, ite_eq_right hn, Pi.one_apply, mul_one, cpow_natCast,
        Complex.norm_pow, Complex.norm_natCast, Complex.norm_natCast]
      have hd : n ^ k ≤ σ k n := by
        rw [ArithmeticFunction.sigma_apply]
        exact Finset.single_le_sum (f := fun d : ℕ ↦ d ^ k) (fun _ _ ↦ Nat.zero_le _)
          (Nat.mem_divisors_self n hn)
      exact mod_cast hd
    rw [LSeriesSummable_powMul_iff, LSeriesSummable_one_iff, sub_re, natCast_re] at hpow
    linarith
  · intro hs
    have hmax : max 1 (1 + (k : ℂ).re) < s.re := by
      simp only [natCast_re, max_lt_iff]
      exact ⟨by linarith [show (0 : ℝ) ≤ k by positivity], hs⟩
    have hC := LSeriesSummable_sigmaC hmax
    exact (LSeriesSummable_congr s fun {n} _ ↦ sigmaC_natCast k n).mp hC

/-- `ζ(s) * ζ(s - k) = ∑ σ_k(n) n^{-s}` for `k : ℕ` and `1 + k < Re s`. -/
theorem LSeries_sigma_eq {k : ℕ} {s : ℂ} (hs : 1 + (k : ℝ) < s.re) :
    LSeries ↗(σ k) s = riemannZeta s * riemannZeta (s - k) := by
  have hmax : max 1 (1 + (k : ℂ).re) < s.re := by
    simp only [natCast_re, max_lt_iff]
    exact ⟨by linarith [show (0 : ℝ) ≤ k by positivity], hs⟩
  refine (LSeries_congr (fun {n} _ ↦ (sigmaC_natCast k n).symm) s).trans ?_
  exact LSeries_sigmaC_eq hmax

/-- The L-series of Euler's totient function `φ` converges absolutely at `s` iff `2 < Re s`. -/
theorem LSeriesSummable_totient_iff {s : ℂ} :
    LSeriesSummable (fun n : ℕ ↦ (n.totient : ℂ)) s ↔ 2 < s.re := by
  constructor
  · intro h
    by_contra! hs
    refine not_summable_prime_ite_div_rpow (c := 1 / 2) (x := 1) (by norm_num) le_rfl ?_
    refine (summable_norm_iff.mpr h).of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity) fun n ↦ ?_
    split_ifs with hp
    · have hp2 : 2 ≤ n := hp.two_le
      have htot : (1 / 2 : ℝ) * n ≤ n.totient := by
        rw [Nat.totient_prime hp]
        have : (n : ℝ) ≥ 2 := mod_cast hp2
        have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
        linarith
      have hpow : (n : ℝ) ^ s.re ≤ (n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (mod_cast hp.one_lt.le) hs
      have hpow_pos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (mod_cast hp.pos) _
      have h2_pos : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := by positivity
      rw [LSeries.norm_term_eq, ite_eq_right hp.ne_zero, Complex.norm_natCast, Real.rpow_one]
      calc
        (1 / 2 : ℝ) / n = ((1 / 2 : ℝ) * n) / (n : ℝ) ^ (2 : ℝ) := by
          rw [Real.rpow_two]
          field_simp
        _ ≤ (n.totient : ℝ) / (n : ℝ) ^ (2 : ℝ) := by gcongr
        _ ≤ (n.totient : ℝ) / (n : ℝ) ^ s.re := by gcongr
    · exact norm_nonneg _
  · intro hs
    have hid : LSeriesSummable ↗(ArithmeticFunction.id : ArithmeticFunction ℕ) s := by
      refine (LSeriesSummable_congr (f := powMul 1 1)
        (g := ↗(ArithmeticFunction.id : ArithmeticFunction ℕ)) s ?_).mp ?_
      · intro n hn
        simp [powMul, ite_eq_right hn]
      · rw [LSeriesSummable_powMul_iff, LSeriesSummable_one_iff, sub_re, one_re]
        linarith
    refine LSeriesSummable_of_norm_le_of_ne_zero hid fun n _ ↦ ?_
    simp only [ArithmeticFunction.id_apply, Complex.norm_natCast]
    exact mod_cast Nat.totient_le n

/-- `ζ(s - 1) / ζ(s) = ∑ φ(n) n^{-s}` for `2 < Re s`. -/
theorem LSeries_totient_eq {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n : ℕ ↦ (n.totient : ℂ)) s = riemannZeta (s - 1) / riemannZeta s := by
  have hs1 : 1 < s.re := by linarith
  have hs2 : 1 < (s - 1).re := by rw [sub_re, one_re]; linarith
  have htot_sum : LSeriesSummable ↗(totientAF : ArithmeticFunction ℂ) s := by
    simpa [ArithmeticFunction.natCoe_apply] using LSeriesSummable_totient_iff.mpr hs
  have hzeta_sum : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zetaC_iff.mpr hs1
  have hconv : (ζ : ArithmeticFunction ℂ) * (totientAF : ArithmeticFunction ℂ) =
      ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    rw [← ArithmeticFunction.natCoe_mul, zeta_mul_totientAF_eq_id]
  have hid_eq : LSeries ↗((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s =
      riemannZeta (s - 1) := by
    have hc : LSeries ↗((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s =
        LSeries (powMul 1 1) s :=
      LSeries_congr (fun {n} hn ↦ by simp [powMul, ite_eq_right hn]) s
    rw [hc, LSeries_powMul, LSeries_one_eq_riemannZeta hs2]
  have hprod := ArithmeticFunction.LSeries_mul' hzeta_sum htot_sum
  rw [hconv, hid_eq, LSeries_zetaC_eq_riemannZeta hs1] at hprod
  have htot_eq : LSeries (fun n : ℕ ↦ (n.totient : ℂ)) s =
      LSeries ↗(totientAF : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} _ ↦ by simp) s
  rw [htot_eq]
  exact eq_div_of_mul_eq (riemannZeta_ne_zero_of_one_lt_re hs1) (by rw [mul_comm, hprod])

/-- The L-series of the Liouville function `λ` converges absolutely at `s` iff `1 < Re s`. -/
theorem LSeriesSummable_liouville_iff {s : ℂ} :
    LSeriesSummable ↗ArithmeticFunction.liouville s ↔ 1 < s.re := by
  have heq : LSeriesSummable ↗ArithmeticFunction.liouville s ↔ LSeriesSummable (1 : ℕ → ℂ) s := by
    rw [LSeriesSummable, LSeriesSummable,
      ← summable_norm_iff (f := LSeries.term ↗ArithmeticFunction.liouville s),
      ← summable_norm_iff (f := LSeries.term (1 : ℕ → ℂ) s)]
    refine summable_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, ArithmeticFunction.liouville_apply hn]
  exact heq.trans LSeriesSummable_one_iff

/-- `ζ(2s) / ζ(s) = ∑ λ(n) n^{-s}` for `1 < Re s`. -/
theorem LSeries_liouville_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗ArithmeticFunction.liouville s = riemannZeta (2 * s) / riemannZeta s := by
  have hs2 : 1 < (2 * s).re := by
    rw [mul_re]
    simp only [re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hzeta_sum : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zetaC_iff.mpr hs
  have hlio_sum : LSeriesSummable ↗(ArithmeticFunction.liouville : ArithmeticFunction ℂ) s := by
    simpa [ArithmeticFunction.intCoe_apply] using LSeriesSummable_liouville_iff.mpr hs
  have hconv : (ζ : ArithmeticFunction ℂ) * (ArithmeticFunction.liouville : ArithmeticFunction ℂ) =
      (sqIndicatorAF : ArithmeticFunction ℂ) := by
    rw [← ArithmeticFunction.coe_coe (f := ζ), ← ArithmeticFunction.intCoe_mul,
      zeta_mul_liouville_eq_sqIndicator]
  have hsq_eq : LSeries ↗(sqIndicatorAF : ArithmeticFunction ℂ) s = riemannZeta (2 * s) := by
    have hc : LSeries ↗(sqIndicatorAF : ArithmeticFunction ℂ) s = LSeries (sqDilate 1) s :=
      LSeries_congr (fun {n} _ ↦ by
        simp only [ArithmeticFunction.intCoe_apply, sqIndicatorAF_apply, sqDilate, Pi.one_apply]
        split_ifs <;> simp) s
    rw [hc, LSeries_sqDilate, LSeries_one_eq_riemannZeta hs2]
  have hprod := ArithmeticFunction.LSeries_mul' hzeta_sum hlio_sum
  rw [hconv, hsq_eq, LSeries_zetaC_eq_riemannZeta hs] at hprod
  have hlio_eq : LSeries ↗ArithmeticFunction.liouville s =
      LSeries ↗(ArithmeticFunction.liouville : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} _ ↦ by simp) s
  rw [hlio_eq]
  exact eq_div_of_mul_eq (riemannZeta_ne_zero_of_one_lt_re hs) (by rw [mul_comm, hprod])

/-- The L-series of `|μ|` (squarefree indicator) converges absolutely at `s` iff `1 < Re s`. -/
theorem LSeriesSummable_absMoebius_iff {s : ℂ} :
    LSeriesSummable ↗absMoebiusAF s ↔ 1 < s.re := by
  constructor
  · intro h
    by_contra! hs
    refine not_summable_prime_ite_div_rpow (c := 1) (x := s.re) zero_lt_one hs ?_
    refine (summable_norm_iff.mpr h).of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity) fun n ↦ ?_
    split_ifs with hp
    · rw [LSeries.norm_term_eq, ite_eq_right hp.ne_zero, absMoebiusAF_apply,
        ite_eq_left hp.squarefree]
      simp
    · exact norm_nonneg _
  · intro hs
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ ?_) hs
    rw [absMoebiusAF_apply]
    split_ifs <;> simp

/-- `ζ(s) / ζ(2s) = ∑ |μ(n)| n^{-s}` for `1 < Re s`. -/
theorem LSeries_absMoebius_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗absMoebiusAF s = riemannZeta s / riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    rw [mul_re]
    simp only [re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hzeta_sum : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zetaC_iff.mpr hs
  have hmuSq_sum : LSeriesSummable ↗(moebiusSqAF : ArithmeticFunction ℂ) s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ ?_) hs
    rw [ArithmeticFunction.intCoe_apply, moebiusSqAF_apply]
    split_ifs
    · have hle : |μ (Nat.sqrt n)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      simpa using (mod_cast hle : ((|μ (Nat.sqrt n)| : ℤ) : ℝ) ≤ 1)
    · simp
  have hmuSq_eq : LSeries ↗(moebiusSqAF : ArithmeticFunction ℂ) s = (riemannZeta (2 * s))⁻¹ := by
    have hc : LSeries ↗(moebiusSqAF : ArithmeticFunction ℂ) s = LSeries (sqDilate ↗μ) s :=
      LSeries_congr (fun {n} _ ↦ by
        simp only [ArithmeticFunction.intCoe_apply, moebiusSqAF_apply, sqDilate]
        split_ifs <;> simp) s
    rw [hc, LSeries_sqDilate, LSeries_moebius_eq_inv_riemannZeta hs2]
  have hconv : (ζ : ArithmeticFunction ℂ) * (moebiusSqAF : ArithmeticFunction ℂ) =
      (absMoebiusAF : ArithmeticFunction ℂ) := by
    rw [← ArithmeticFunction.coe_coe (f := ζ), ← ArithmeticFunction.intCoe_mul,
      zeta_mul_moebiusSq_eq_absMoebius, ArithmeticFunction.coe_coe]
  have hprod := ArithmeticFunction.LSeries_mul' hzeta_sum hmuSq_sum
  rw [hconv, LSeries_zetaC_eq_riemannZeta hs, hmuSq_eq, ← div_eq_mul_inv] at hprod
  have habs_eq : LSeries ↗absMoebiusAF s = LSeries ↗(absMoebiusAF : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} _ ↦ by simp) s
  rw [habs_eq, hprod]

/-- `ζ(s) / ζ(2s) = ∑ |μ(n)| n^{-s}` expressed directly with `|μ n|` for `1 < Re s`. -/
theorem LSeries_abs_moebius_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ ((|μ n| : ℤ) : ℂ)) s = riemannZeta s / riemannZeta (2 * s) := by
  refine (LSeries_congr (fun {n} _ ↦ ?_) s).trans (LSeries_absMoebius_eq hs)
  rw [← absMoebiusAF_coe_int n]
  simp

/-- The L-series of `n ↦ 2 ^ ω(n)` converges absolutely at `s` iff `1 < Re s`. -/
theorem LSeriesSummable_twoPowOmega_iff {s : ℂ} :
    LSeriesSummable (fun n : ℕ ↦ (2 : ℂ) ^ ω n) s ↔ 1 < s.re := by
  have hcongr : LSeriesSummable (fun n : ℕ ↦ (2 : ℂ) ^ ω n) s ↔
      LSeriesSummable ↗twoPowOmegaAF s :=
    LSeriesSummable_congr s fun {n} hn ↦ by simp [twoPowOmegaAF_apply_ne hn]
  rw [hcongr]
  constructor
  · intro h
    rw [← LSeriesSummable_one_iff (s := s)]
    refine LSeriesSummable_of_norm_le_of_ne_zero h fun n hn ↦ ?_
    rw [Pi.one_apply, norm_one, twoPowOmegaAF_apply_ne hn, Complex.norm_natCast]
    exact mod_cast Nat.one_le_pow (ω n) 2 (by norm_num)
  · intro hs
    have h1 : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s := LSeriesSummable_zetaC_iff.mpr hs
    have h2 : LSeriesSummable ↗(absMoebiusAF : ArithmeticFunction ℂ) s := by
      simpa [ArithmeticFunction.natCoe_apply] using LSeriesSummable_absMoebius_iff.mpr hs
    have hmul := ArithmeticFunction.LSeriesSummable_mul h1 h2
    have hconv : (ζ : ArithmeticFunction ℂ) * (absMoebiusAF : ArithmeticFunction ℂ) =
        (twoPowOmegaAF : ArithmeticFunction ℂ) := by
      rw [← ArithmeticFunction.natCoe_mul, zeta_mul_absMoebius_eq_twoPowOmega]
    rw [hconv] at hmul
    simpa [ArithmeticFunction.natCoe_apply] using hmul

/-- `ζ(s)^2 / ζ(2s) = ∑ 2^{ω(n)} n^{-s}` for `1 < Re s`. -/
theorem LSeries_twoPowOmega_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ (2 : ℂ) ^ ω n) s = riemannZeta s ^ 2 / riemannZeta (2 * s) := by
  have hcongr : LSeries (fun n : ℕ ↦ (2 : ℂ) ^ ω n) s = LSeries ↗twoPowOmegaAF s :=
    LSeries_congr (fun {n} hn ↦ by simp [twoPowOmegaAF_apply_ne hn]) s
  have h1 : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s := LSeriesSummable_zetaC_iff.mpr hs
  have h2 : LSeriesSummable ↗(absMoebiusAF : ArithmeticFunction ℂ) s := by
    simpa [ArithmeticFunction.natCoe_apply] using LSeriesSummable_absMoebius_iff.mpr hs
  have hconv : (ζ : ArithmeticFunction ℂ) * (absMoebiusAF : ArithmeticFunction ℂ) =
      (twoPowOmegaAF : ArithmeticFunction ℂ) := by
    rw [← ArithmeticFunction.natCoe_mul, zeta_mul_absMoebius_eq_twoPowOmega]
  have hmul := ArithmeticFunction.LSeries_mul' h1 h2
  rw [hconv, LSeries_zetaC_eq_riemannZeta hs] at hmul
  have habs_eq : LSeries ↗(absMoebiusAF : ArithmeticFunction ℂ) s =
      riemannZeta s / riemannZeta (2 * s) := by
    simpa [ArithmeticFunction.natCoe_apply] using LSeries_absMoebius_eq hs
  rw [habs_eq] at hmul
  rw [hcongr]
  have htwo_eq : LSeries ↗twoPowOmegaAF s = LSeries ↗(twoPowOmegaAF : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} _ ↦ by simp) s
  rw [htwo_eq, hmul]
  ring

end AnalyticNumberTheory.DirichletSeries
