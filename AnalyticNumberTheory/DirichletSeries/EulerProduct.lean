import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Euler Products for Dirichlet Series

This file develops the Euler product theory for Dirichlet series and L-functions:

- General Euler products for multiplicative functions (`ArithmeticFunction.IsMultiplicative` and
  coprime-multiplicative sequences) in the half-plane of absolute convergence.
- General Euler products for completely multiplicative functions (`ℕ →* ℂ`, `ℕ →*₀ ℂ`, and
  `IsCompletelyMultiplicative`), including non-vanishing on the domain of absolute convergence.
- Euler products for `ζ(s)`, Dirichlet `L(s, χ)`, `1 / ζ(s)`, `1 / L(s, χ)`, and `L(s, λ)`.
- Logarithmic (`log`) and logarithmic-derivative (`deriv`) forms of Euler products for `Re s > 1`
  and for general completely multiplicative functions.
-/

open Complex Filter Nat
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
  LSeries.notation Topology

namespace AnalyticNumberTheory.DirichletSeries

/-! ### Helper Lemmas -/

private theorem cpow_nat_pow_neg (p : ℕ) (s : ℂ) (e : ℕ) :
    ((p ^ e : ℕ) : ℂ) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.cast_mul, Nat.cast_pow, ← Complex.ofReal_natCast p, ← Complex.ofReal_pow,
      Complex.mul_cpow_ofReal_nonneg (pow_nonneg p.cast_nonneg e) p.cast_nonneg,
      Complex.ofReal_pow, Complex.ofReal_natCast, ← Nat.cast_pow, ih, pow_succ]

private theorem term_prime_pow_eq (f : ℕ → ℂ) (s : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    LSeries.term f s (p ^ e) = f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  have hne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  rw [LSeries.term_of_ne_zero hne, div_eq_mul_inv, ← cpow_neg, cpow_nat_pow_neg]

private theorem term_coprime_mul {f : ℕ → ℂ} (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (s : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    LSeries.term f s (m * n) = LSeries.term f s m * LSeries.term f s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  rw [LSeries.term_of_ne_zero hmn0, LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
    hmul hmn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-! ### General Euler Products for Multiplicative Functions -/

/-- General Euler product (`HasProd` form) for a coprime-multiplicative sequence `f : ℕ → ℂ`
whose L-series converges absolutely at `s`. -/
theorem eulerProduct_hasProd_of_coprime_mul {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f s (p ^ e)) (LSeries f s) := by
  have ht1 : LSeries.term f s 1 = 1 := by simp [hf1]
  have htnorm : Summable (fun n ↦ ‖LSeries.term f s n‖) := summable_norm_iff.mpr hsum
  exact EulerProduct.eulerProduct_hasProd ht1 (fun {m n} hmn ↦ term_coprime_mul hmul s hmn)
    htnorm (LSeries.term_zero f s)

/-- General Euler product (`HasProd` form with `f (p ^ e) * p ^ (-e * s)`) for a
coprime-multiplicative sequence `f : ℕ → ℂ` whose L-series converges absolutely at `s`. -/
theorem eulerProduct_hasProd_of_coprime_mul' {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e) (LSeries f s) := by
  have hfun : (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f s (p ^ e)) =
      (fun p : Nat.Primes ↦ ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e) := by
    funext p
    exact tsum_congr fun e ↦ term_prime_pow_eq f s p.prop e
  rw [← hfun]
  exact eulerProduct_hasProd_of_coprime_mul hf1 hmul hsum

/-- General Euler product (`tprod` form) for a coprime-multiplicative sequence `f : ℕ → ℂ`
whose L-series converges absolutely at `s`. -/
theorem eulerProduct_tprod_of_coprime_mul {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    ∏' p : Nat.Primes, ∑' e : ℕ, LSeries.term f s (p ^ e) = LSeries f s :=
  (eulerProduct_hasProd_of_coprime_mul hf1 hmul hsum).tprod_eq

/-- General Euler product (finite partial product convergence form) for a coprime-multiplicative
sequence `f : ℕ → ℂ` whose L-series converges absolutely at `s`. -/
theorem eulerProduct_tendsto_of_coprime_mul {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, ∑' e : ℕ, LSeries.term f s (p ^ e))
      atTop (𝓝 (LSeries f s)) :=
  EulerProduct.eulerProduct (by simp [hf1]) (fun {m n} hmn ↦ term_coprime_mul hmul s hmn)
    (summable_norm_iff.mpr hsum) (LSeries.term_zero f s)

/-- General Euler product (`HasProd` form) for a multiplicative arithmetic function
`f : ArithmeticFunction ℂ` when `LSeriesSummable ↗f s`. -/
theorem eulerProduct_hasProd_of_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {s : ℂ} (hsum : LSeriesSummable ↗f s) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term ↗f s (p ^ e)) (LSeries ↗f s) :=
  eulerProduct_hasProd_of_coprime_mul hf.1 (fun hmn ↦ hf.2 hmn) hsum

/-- General Euler product (`HasProd` form with `f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e`) for a
multiplicative arithmetic function `f : ArithmeticFunction ℂ` when `LSeriesSummable ↗f s`. -/
theorem eulerProduct_hasProd_of_isMultiplicative' {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {s : ℂ} (hsum : LSeriesSummable ↗f s) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e) (LSeries ↗f s) :=
  eulerProduct_hasProd_of_coprime_mul' hf.1 (fun hmn ↦ hf.2 hmn) hsum

/-- General Euler product (`tprod` form) for a multiplicative arithmetic function
`f : ArithmeticFunction ℂ` when `LSeriesSummable ↗f s`. -/
theorem eulerProduct_tprod_of_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {s : ℂ} (hsum : LSeriesSummable ↗f s) :
    ∏' p : Nat.Primes, ∑' e : ℕ, LSeries.term ↗f s (p ^ e) = LSeries ↗f s :=
  (eulerProduct_hasProd_of_isMultiplicative hf hsum).tprod_eq

/-- General Euler product (finite partial product convergence form) for a multiplicative
arithmetic function `f : ArithmeticFunction ℂ` when `LSeriesSummable ↗f s`. -/
theorem eulerProduct_tendsto_of_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {s : ℂ} (hsum : LSeriesSummable ↗f s) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, ∑' e : ℕ, LSeries.term ↗f s (p ^ e))
      atTop (𝓝 (LSeries ↗f s)) :=
  eulerProduct_tendsto_of_coprime_mul hf.1 (fun hmn ↦ hf.2 hmn) hsum

/-- General Euler product (`tprod` form) on the open half-plane of absolute convergence
`abscissaOfAbsConv ↗f < Re s` for a multiplicative arithmetic function `f`. -/
theorem eulerProduct_tprod_of_abscissaOfAbsConv_lt {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {s : ℂ} (hs : LSeries.abscissaOfAbsConv ↗f < s.re) :
    ∏' p : Nat.Primes, ∑' e : ℕ, LSeries.term ↗f s (p ^ e) = LSeries ↗f s :=
  eulerProduct_tprod_of_isMultiplicative hf (LSeriesSummable_of_abscissaOfAbsConv_lt_re hs)

/-! ### Euler Products for Completely Multiplicative Functions -/

/-- A sequence `f : ℕ → ℂ` is completely multiplicative (as a Dirichlet series coefficient
sequence) if `f 0 = 0`, `f 1 = 1`, and `f (m * n) = f m * f n` for all `m, n : ℕ`. -/
def IsCompletelyMultiplicative (f : ℕ → ℂ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

/-- Package a completely multiplicative sequence `f : ℕ → ℂ` as a `MonoidWithZeroHom ℕ ℂ`. -/
def IsCompletelyMultiplicative.toMonoidWithZeroHom {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) : ℕ →*₀ ℂ where
  toFun := f
  map_zero' := hf.1
  map_one' := hf.2.1
  map_mul' := hf.2.2

/-- A completely multiplicative sequence gives a multiplicative `ArithmeticFunction ℂ`. -/
def IsCompletelyMultiplicative.toArithmeticFunction {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) : ArithmeticFunction ℂ where
  toFun := f
  map_zero' := hf.1

/-- `IsCompletelyMultiplicative.toArithmeticFunction` is multiplicative. -/
theorem IsCompletelyMultiplicative.isMultiplicative {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) : hf.toArithmeticFunction.IsMultiplicative :=
  ⟨hf.2.1, fun {m n} _ ↦ hf.2.2 m n⟩

/-- The completely multiplicative `MonoidWithZeroHom` `n ↦ LSeries.term f s n` associated to a
sequence `f` satisfying `f 1 = 1` and `f (m * n) = f m * f n` for positive `m, n`. -/
noncomputable def lseriesTermHom (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n) (s : ℂ) : ℕ →*₀ ℂ where
  toFun := LSeries.term f s
  map_zero' := LSeries.term_zero f s
  map_one' := by simp [hf1]
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    rw [LSeries.term_of_ne_zero hmn, LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
      hmul m n hm hn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring

private theorem lseriesTermHom_prime (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    lseriesTermHom f hf1 hmul s p = f p * (p : ℂ) ^ (-s) := by
  simp [lseriesTermHom, LSeries.term_of_ne_zero hp.ne_zero, div_eq_mul_inv, cpow_neg]

private theorem lseriesTermHom_tsum (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n) (s : ℂ) :
    ∑' n : ℕ, lseriesTermHom f hf1 hmul s n = LSeries f s := rfl

private theorem lseriesTermHom_summable_norm {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    Summable (fun n ↦ ‖lseriesTermHom f hf1 hmul s n‖) :=
  summable_norm_iff.mpr hsum

/-- If `f : ℕ →*₀ ℂ` is L-series summable at `s`, then `‖f p * p ^ (-s)‖ < 1` for every prime `p`. -/
theorem norm_prime_term_lt_one_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) {p : ℕ} (hp : p.Prime) :
    ‖f p * (p : ℂ) ^ (-s)‖ < 1 := by
  let g := lseriesTermHom f f.map_one (fun m n _ _ ↦ f.map_mul m n) s
  have hg : Summable (g : ℕ → ℂ) := hsum
  have hlt := hg.norm_lt_one (f := g.toMonoidHom) hp.one_lt
  simpa [g, lseriesTermHom_prime f f.map_one (fun m n _ _ ↦ f.map_mul m n) s hp] using hlt

/-- Euler product (`HasProd` form) for a completely multiplicative function `f : ℕ →*₀ ℂ`. -/
theorem eulerProduct_hasProd_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    HasProd (fun p : Nat.Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) (LSeries f s) := by
  let g := lseriesTermHom f f.map_one (fun m n _ _ ↦ f.map_mul m n) s
  have hg : Summable (fun n ↦ ‖g n‖) := lseriesTermHom_summable_norm _ _ hsum
  have hprod := EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := g) hg
  rw [lseriesTermHom_tsum] at hprod
  have hfun : (fun p : Nat.Primes ↦ (1 - g p)⁻¹) =
      (fun p : Nat.Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) := by
    funext p
    rw [lseriesTermHom_prime _ _ _ _ p.prop]
  rwa [← hfun]

/-- Euler product (`tprod` form) for a completely multiplicative function `f : ℕ →*₀ ℂ`. -/
theorem eulerProduct_tprod_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    ∏' p : Nat.Primes, (1 - f p * (p : ℂ) ^ (-s))⁻¹ = LSeries f s :=
  (eulerProduct_hasProd_of_monoidWithZeroHom f hsum).tprod_eq

/-- Euler product (partial products form) for a completely multiplicative function `f : ℕ →*₀ ℂ`. -/
theorem eulerProduct_tendsto_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - f p * (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (LSeries f s)) := by
  let g := lseriesTermHom f f.map_one (fun m n _ _ ↦ f.map_mul m n) s
  have hg : Summable (fun n ↦ ‖g n‖) := lseriesTermHom_summable_norm _ _ hsum
  have ht := EulerProduct.eulerProduct_completely_multiplicative (f := g) hg
  rw [lseriesTermHom_tsum] at ht
  refine ht.congr fun N ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  rw [lseriesTermHom_prime _ _ _ _ (Nat.prime_of_mem_primesBelow hp)]

/-- Euler product (`HasProd` form) for a monoid homomorphism `f : ℕ →* ℂ`. -/
theorem eulerProduct_hasProd_of_monoidHom (f : ℕ →* ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    HasProd (fun p : Nat.Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) (LSeries f s) := by
  let f₀ : ℕ →*₀ ℂ :=
    { toFun := fun n ↦ if n = 0 then 0 else f n
      map_zero' := rfl
      map_one' := by simp [f.map_one]
      map_mul' := fun m n ↦ by
        by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn, f.map_mul] }
  have hsum₀ : LSeriesSummable f₀ s :=
    (LSeriesSummable_congr s (fun {n} hn ↦ by simp [f₀, hn])).mpr hsum
  have hL : LSeries f₀ s = LSeries f s :=
    LSeries_congr (fun {n} hn ↦ by simp [f₀, hn]) s
  have hp := eulerProduct_hasProd_of_monoidWithZeroHom f₀ hsum₀
  rw [hL] at hp
  have hfun : (fun p : Nat.Primes ↦ (1 - f₀ p * (p : ℂ) ^ (-s))⁻¹) =
      (fun p : Nat.Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) := by
    funext p
    simp [f₀, p.prop.ne_zero]
  rwa [← hfun]

/-- Euler product (`tprod` form) for a monoid homomorphism `f : ℕ →* ℂ`. -/
theorem eulerProduct_tprod_of_monoidHom (f : ℕ →* ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    ∏' p : Nat.Primes, (1 - f p * (p : ℂ) ^ (-s))⁻¹ = LSeries f s :=
  (eulerProduct_hasProd_of_monoidHom f hsum).tprod_eq

/-- Euler product (partial products form) for a monoid homomorphism `f : ℕ →* ℂ`. -/
theorem eulerProduct_tendsto_of_monoidHom (f : ℕ →* ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - f p * (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (LSeries f s)) := by
  let f₀ : ℕ →*₀ ℂ :=
    { toFun := fun n ↦ if n = 0 then 0 else f n
      map_zero' := rfl
      map_one' := by simp [f.map_one]
      map_mul' := fun m n ↦ by
        by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn, f.map_mul] }
  have hsum₀ : LSeriesSummable f₀ s :=
    (LSeriesSummable_congr s (fun {n} hn ↦ by simp [f₀, hn])).mpr hsum
  have hL : LSeries f₀ s = LSeries f s :=
    LSeries_congr (fun {n} hn ↦ by simp [f₀, hn]) s
  have ht := eulerProduct_tendsto_of_monoidWithZeroHom f₀ hsum₀
  rw [hL] at ht
  refine ht.congr fun N ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  simp [f₀, (Nat.prime_of_mem_primesBelow hp).ne_zero]

/-- Euler product (`HasProd` form) for a completely multiplicative sequence `f : ℕ → ℂ`. -/
theorem eulerProduct_hasProd_of_completelyMultiplicative {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) {s : ℂ} (hsum : LSeriesSummable f s) :
    HasProd (fun p : Nat.Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) (LSeries f s) :=
  eulerProduct_hasProd_of_monoidWithZeroHom hf.toMonoidWithZeroHom hsum

/-- Euler product (`tprod` form) for a completely multiplicative sequence `f : ℕ → ℂ`. -/
theorem eulerProduct_tprod_of_completelyMultiplicative {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) {s : ℂ} (hsum : LSeriesSummable f s) :
    ∏' p : Nat.Primes, (1 - f p * (p : ℂ) ^ (-s))⁻¹ = LSeries f s :=
  (eulerProduct_hasProd_of_completelyMultiplicative hf hsum).tprod_eq

/-- Euler product (partial products form) for a completely multiplicative sequence `f : ℕ → ℂ`. -/
theorem eulerProduct_tendsto_of_completelyMultiplicative {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) {s : ℂ} (hsum : LSeriesSummable f s) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - f p * (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (LSeries f s)) :=
  eulerProduct_tendsto_of_monoidWithZeroHom hf.toMonoidWithZeroHom hsum

/-! ### Exponential-Logarithm Euler Product and Non-Vanishing -/

/-- Logarithmic-exponential form of the Euler product for any completely multiplicative
`f : ℕ →*₀ ℂ` that is L-series summable at `s`. -/
theorem eulerProduct_exp_log_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - f p * (p : ℂ) ^ (-s))) = LSeries f s := by
  let g := lseriesTermHom f f.map_one (fun m n _ _ ↦ f.map_mul m n) s
  have hg : Summable (fun n ↦ ‖g n‖) := lseriesTermHom_summable_norm _ _ hsum
  have hexp := EulerProduct.exp_tsum_primes_log_eq_tsum (f := g) hg
  rw [lseriesTermHom_tsum] at hexp
  rw [← hexp]
  congr 1
  refine tsum_congr fun p ↦ ?_
  rw [lseriesTermHom_prime _ _ _ _ p.prop]

/-- Non-vanishing of any completely multiplicative L-series on its domain of absolute
convergence. -/
theorem LSeries_ne_zero_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) : LSeries f s ≠ 0 := by
  rw [← eulerProduct_exp_log_of_monoidWithZeroHom f hsum]
  exact Complex.exp_ne_zero _

/-- Non-vanishing of a completely multiplicative sequence's L-series when `LSeriesSummable`. -/
theorem LSeries_ne_zero_of_completelyMultiplicative {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicative f) {s : ℂ} (hsum : LSeriesSummable f s) :
    LSeries f s ≠ 0 :=
  LSeries_ne_zero_of_monoidWithZeroHom hf.toMonoidWithZeroHom hsum

/-! ### Classical Euler Products: `ζ(s)`, `L(s, χ)`, `1 / ζ(s)`, `1 / L(s, χ)`, `L(s, λ)` -/

/-- Euler product (`HasProd` form) for the Riemann zeta function `ζ(s)` on `1 < Re s`. -/
theorem riemannZeta_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  _root_.riemannZeta_eulerProduct_hasProd hs

/-- Euler product (`tprod` form) for the Riemann zeta function `ζ(s)` on `1 < Re s`. -/
theorem riemannZeta_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  _root_.riemannZeta_eulerProduct_tprod hs

/-- Euler product (partial products form) for the Riemann zeta function `ζ(s)` on `1 < Re s`. -/
theorem riemannZeta_eulerProduct_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (riemannZeta s)) :=
  _root_.riemannZeta_eulerProduct hs

/-- Euler product (`HasProd` form) for Dirichlet L-series `L(s, χ)` on `1 < Re s`. -/
theorem dirichletLSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (LSeries ↗χ s) :=
  DirichletCharacter.LSeries_eulerProduct_hasProd χ hs

/-- Euler product (`tprod` form) for Dirichlet L-series `L(s, χ)` on `1 < Re s`. -/
theorem dirichletLSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = LSeries ↗χ s :=
  DirichletCharacter.LSeries_eulerProduct_tprod χ hs

/-- Euler product (partial products form) for Dirichlet L-series `L(s, χ)` on `1 < Re s`. -/
theorem dirichletLSeries_eulerProduct_tendsto {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - χ p * (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (LSeries ↗χ s)) :=
  DirichletCharacter.LSeries_eulerProduct χ hs

private theorem moebius_prime_pow_tsum (s : ℂ) (p : Nat.Primes) :
    ∑' e : ℕ, LSeries.term ↗μ s ((p : ℕ) ^ e) = 1 - (p : ℂ) ^ (-s) := by
  have hzero : ∀ e ∉ (Finset.range 2 : Finset ℕ), LSeries.term ↗μ s ((p : ℕ) ^ e) = 0 := by
    intro e he
    rw [Finset.mem_range, not_lt] at he
    rw [LSeries.term_of_ne_zero (pow_ne_zero e p.prop.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow p.prop (by omega),
      ite_eq_right (by omega)]
    simp
  rw [tsum_eq_sum hzero, Finset.sum_range_succ, Finset.sum_range_one]
  simp [LSeries.term_of_ne_zero p.prop.ne_zero, ArithmeticFunction.moebius_apply_prime p.prop,
    div_eq_mul_inv, cpow_neg, sub_eq_add_neg]

private theorem LSeries_moebius_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗μ s = (riemannZeta s)⁻¹ := by
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
  exact eq_inv_of_mul_eq_one_right hmul

/-- Euler product (`HasProd` form) for `1 / ζ(s)` via the Möbius function on `1 < Re s`. -/
theorem inv_riemannZeta_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ 1 - (p : ℂ) ^ (-s)) (riemannZeta s)⁻¹ := by
  have hsum : LSeriesSummable ↗(μ : ArithmeticFunction ℂ) s := by
    simpa [ArithmeticFunction.intCoe_apply] using
      (ArithmeticFunction.LSeriesSummable_moebius_iff (s := s)).mpr hs
  have hp := eulerProduct_hasProd_of_isMultiplicative
    ArithmeticFunction.isMultiplicative_moebius.intCast hsum
  have hL : LSeries ↗(μ : ArithmeticFunction ℂ) s = (riemannZeta s)⁻¹ := by
    simpa [ArithmeticFunction.intCoe_apply] using LSeries_moebius_eq_inv_zeta hs
  rw [hL] at hp
  have hfun : (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term ↗(μ : ArithmeticFunction ℂ) s ((p : ℕ) ^ e)) =
      (fun p : Nat.Primes ↦ 1 - (p : ℂ) ^ (-s)) := by
    funext p
    have hts : ∑' e : ℕ, LSeries.term ↗(μ : ArithmeticFunction ℂ) s ((p : ℕ) ^ e) =
        ∑' e : ℕ, LSeries.term ↗μ s ((p : ℕ) ^ e) := by
      refine tsum_congr fun e ↦ ?_
      simp [ArithmeticFunction.intCoe_apply]
    rw [hts, moebius_prime_pow_tsum]
  rwa [← hfun]

/-- Euler product (`tprod` form) for `1 / ζ(s)` on `1 < Re s`. -/
theorem inv_riemannZeta_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s)) = (riemannZeta s)⁻¹ :=
  (inv_riemannZeta_eulerProduct_hasProd hs).tprod_eq

/-- Euler product (partial products form) for `1 / ζ(s)` on `1 < Re s`. -/
theorem inv_riemannZeta_eulerProduct_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-s)))
      atTop (𝓝 (riemannZeta s)⁻¹) := by
  have hsum : LSeriesSummable ↗(μ : ArithmeticFunction ℂ) s := by
    simpa [ArithmeticFunction.intCoe_apply] using
      (ArithmeticFunction.LSeriesSummable_moebius_iff (s := s)).mpr hs
  have ht := eulerProduct_tendsto_of_isMultiplicative
    ArithmeticFunction.isMultiplicative_moebius.intCast hsum
  have hL : LSeries ↗(μ : ArithmeticFunction ℂ) s = (riemannZeta s)⁻¹ := by
    simpa [ArithmeticFunction.intCoe_apply] using LSeries_moebius_eq_inv_zeta hs
  rw [hL] at ht
  refine ht.congr fun N ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  have hts : ∑' e : ℕ, LSeries.term ↗(μ : ArithmeticFunction ℂ) s (p ^ e) =
      ∑' e : ℕ, LSeries.term ↗μ s (p ^ e) := by
    refine tsum_congr fun e ↦ ?_
    simp [ArithmeticFunction.intCoe_apply]
  rw [hts, moebius_prime_pow_tsum s ⟨p, Nat.prime_of_mem_primesBelow hp⟩]

/-- Euler product (`HasProd` form) for `1 / L(s, χ)` on `1 < Re s`. -/
theorem inv_dirichletLSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ 1 - χ p * (p : ℂ) ^ (-s)) (LSeries ↗χ s)⁻¹ := by
  let g : ℕ → ℂ := ↗χ * ↗μ
  have hg1 : g 1 = 1 := by simp [g]
  have hgmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := by
    intro m n hmn
    simp only [g, Pi.mul_apply, Nat.cast_mul, map_mul,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul]
    ring
  have hsum : LSeriesSummable g s :=
    DirichletCharacter.LSeriesSummable_mul χ
      ((ArithmeticFunction.LSeriesSummable_moebius_iff (s := s)).mpr hs)
  have hp := eulerProduct_hasProd_of_coprime_mul hg1 hgmul hsum
  have hL : LSeries g s = (LSeries ↗χ s)⁻¹ :=
    eq_inv_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ hs)
  rw [hL] at hp
  have hfun : (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term g s ((p : ℕ) ^ e)) =
      (fun p : Nat.Primes ↦ 1 - χ p * (p : ℂ) ^ (-s)) := by
    funext p
    have hzero : ∀ e ∉ (Finset.range 2 : Finset ℕ), LSeries.term g s ((p : ℕ) ^ e) = 0 := by
      intro e he
      rw [Finset.mem_range, not_lt] at he
      dsimp only [g]
      rw [LSeries.term_of_ne_zero (pow_ne_zero e p.prop.ne_zero), Pi.mul_apply,
        ArithmeticFunction.moebius_apply_prime_pow p.prop (by omega), ite_eq_right (by omega)]
      simp
    rw [tsum_eq_sum hzero, Finset.sum_range_succ, Finset.sum_range_one]
    simp [g, LSeries.term_of_ne_zero p.prop.ne_zero, ArithmeticFunction.moebius_apply_prime p.prop,
      div_eq_mul_inv, cpow_neg, sub_eq_add_neg]
  rwa [← hfun]

/-- Euler product (`tprod` form) for `1 / L(s, χ)` on `1 < Re s`. -/
theorem inv_dirichletLSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - χ p * (p : ℂ) ^ (-s)) = (LSeries ↗χ s)⁻¹ :=
  (inv_dirichletLSeries_eulerProduct_hasProd χ hs).tprod_eq

/-- Euler product (partial products form) for `1 / L(s, χ)` on `1 < Re s`. -/
theorem inv_dirichletLSeries_eulerProduct_tendsto {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun K : ℕ ↦ ∏ p ∈ Nat.primesBelow K, (1 - χ p * (p : ℂ) ^ (-s)))
      atTop (𝓝 (LSeries ↗χ s)⁻¹) := by
  let g : ℕ → ℂ := ↗χ * ↗μ
  have hg1 : g 1 = 1 := by simp [g]
  have hgmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := by
    intro m n hmn
    simp only [g, Pi.mul_apply, Nat.cast_mul, map_mul,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul]
    ring
  have hsum : LSeriesSummable g s :=
    DirichletCharacter.LSeriesSummable_mul χ
      ((ArithmeticFunction.LSeriesSummable_moebius_iff (s := s)).mpr hs)
  have ht := eulerProduct_tendsto_of_coprime_mul hg1 hgmul hsum
  have hL : LSeries g s = (LSeries ↗χ s)⁻¹ :=
    eq_inv_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ hs)
  rw [hL] at ht
  refine ht.congr fun K ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hzero : ∀ e ∉ (Finset.range 2 : Finset ℕ), LSeries.term g s (p ^ e) = 0 := by
    intro e he
    rw [Finset.mem_range, not_lt] at he
    dsimp only [g]
    rw [LSeries.term_of_ne_zero (pow_ne_zero e hpp.ne_zero), Pi.mul_apply,
      ArithmeticFunction.moebius_apply_prime_pow hpp (by omega), ite_eq_right (by omega)]
    simp
  rw [tsum_eq_sum hzero, Finset.sum_range_succ, Finset.sum_range_one]
  simp [g, LSeries.term_of_ne_zero hpp.ne_zero, ArithmeticFunction.moebius_apply_prime hpp,
    div_eq_mul_inv, cpow_neg, sub_eq_add_neg]

/-- Euler product (`tprod` form) for the Liouville L-series on `1 < Re s`. -/
theorem liouville_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-s))⁻¹ = LSeries ↗ArithmeticFunction.liouville s := by
  let f₀ : ℕ →*₀ ℂ :=
    { toFun := fun n ↦ (ArithmeticFunction.liouville n : ℂ)
      map_zero' := by simp
      map_one' := by simp [ArithmeticFunction.liouville_apply_one]
      map_mul' := fun m n ↦ by
        simp [ArithmeticFunction.liouville_apply_mul] }
  have hsum : LSeriesSummable f₀ s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ ?_) hs
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f₀]
    · simp [f₀, ArithmeticFunction.liouville_apply hn]
  have ht := eulerProduct_tprod_of_monoidWithZeroHom f₀ hsum
  have heq : LSeries f₀ s = LSeries ↗ArithmeticFunction.liouville s := rfl
  rw [heq] at ht
  rw [← ht]
  refine tprod_congr fun p ↦ ?_
  simp [f₀, ArithmeticFunction.liouville_apply p.prop.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime p.prop, sub_neg_eq_add]

/-! ### Logarithmic and Logarithmic-Derivative Forms of Euler Products -/

/-- Logarithmic Euler product for a general completely multiplicative `f : ℕ →*₀ ℂ`:
`∑' p : Nat.Primes, -log (1 - f p * p ^ (-s)) = LSeries (fun n ↦ f n * Λ n / Real.log n) s`. -/
theorem eulerProduct_log_eq_LSeries_of_monoidWithZeroHom (f : ℕ →*₀ ℂ) {s : ℂ}
    (hsum : LSeriesSummable f s) :
    ∑' p : Nat.Primes, -Complex.log (1 - f p * (p : ℂ) ^ (-s)) =
      LSeries (fun n : ℕ ↦ f n * (Λ n : ℂ) / (Real.log n : ℂ)) s := by
  have hpow (p : Nat.Primes) : ‖f p * (p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_term_lt_one_of_monoidWithZeroHom f hsum p.prop
  let g : ℕ → ℂ := fun n ↦ LSeries.term (fun k ↦ f k * (Λ k : ℂ) / (Real.log k : ℂ)) s n
  have hg_sum : Summable g := by
    rw [← summable_norm_iff]
    refine (summable_norm_iff.mpr hsum).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [g]
    rcases eq_or_ne n 1 with rfl | hn1
    · simp [g]
    have hn1' : 1 < n := by omega
    have hlog_pos : 0 < Real.log n := Real.log_pos (mod_cast hn1')
    change ‖LSeries.term (fun k ↦ f k * (Λ k : ℂ) / (Real.log k : ℂ)) s n‖ ≤ ‖LSeries.term f s n‖
    refine LSeries.norm_term_le s ?_
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog_pos.le,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_div_assoc]
    exact mul_le_of_le_one_right (norm_nonneg _)
      ((div_le_one hlog_pos).mpr ArithmeticFunction.vonMangoldt_le_log)
  have hg_supp : Function.support g ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    apply hn
    simp [g, LSeries.term_def, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp]
  rw [tsum_congr fun p ↦ (Complex.hasSum_taylorSeries_neg_log' (hpow p)).tsum_eq.symm]
  have hts := tsum_eq_tsum_primes_of_support_subset_prime_powers hg_sum hg_supp
  have hgL : ∑' n : ℕ, g n = LSeries (fun n : ℕ ↦ f n * (Λ n : ℂ) / (Real.log n : ℂ)) s := rfl
  rw [← hgL, hts]
  refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
  have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have hpk0 : (p : ℕ) ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) p.prop.ne_zero
  have hlogp : Complex.log p ≠ 0 := by
    rw [← Complex.natCast_log]
    exact Complex.ofReal_ne_zero.mpr p.prop.log_ne_zero
  symm
  dsimp only [g]
  rw [LSeries.term_of_ne_zero hpk0, div_eq_mul_inv, ← cpow_neg, cpow_nat_pow_neg,
    map_pow, ArithmeticFunction.vonMangoldt_apply_pow hk0,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop, Nat.cast_pow, Real.log_pow, mul_pow]
  push_cast
  field_simp [hlogp]

/-- Convolution identity `(f * Λ) ⍟ f = LSeries.logMul f` for any completely multiplicative
`f : ℕ →*₀ ℂ`. -/
theorem mul_vonMangoldt_convolution_self (f : ℕ →*₀ ℂ) :
    (fun n : ℕ ↦ f n * (Λ n : ℂ)) ⍟ f = LSeries.logMul f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.logMul]
  · simp only [LSeries.convolution_def, LSeries.logMul]
    have hsum : ∑ p ∈ n.divisorsAntidiagonal, f p.1 * (Λ p.1 : ℂ) * f p.2 =
        ∑ p ∈ n.divisorsAntidiagonal, f n * (Λ p.1 : ℂ) := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hp' := Nat.mem_divisorsAntidiagonal.mp hp
      calc
        f p.1 * (Λ p.1 : ℂ) * f p.2 = (f p.1 * f p.2) * (Λ p.1 : ℂ) := by ring
        _ = f (p.1 * p.2) * (Λ p.1 : ℂ) := by rw [← f.map_mul]
        _ = f n * (Λ p.1 : ℂ) := by rw [hp'.1]
    rw [hsum, Nat.sum_divisorsAntidiagonal (f := fun x _ ↦ f n * (Λ x : ℂ)), ← Finset.mul_sum,
      ← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum, Complex.natCast_log, mul_comm]

/-- For `f : ℕ →*₀ ℂ` and `abscissaOfAbsConv f < Re s`, the L-series of `f * Λ` converges
absolutely and equals `-deriv (LSeries f) s / LSeries f s`. -/
theorem LSeries_mul_vonMangoldt_eq_neg_logDeriv (f : ℕ →*₀ ℂ) {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv f < s.re) :
    LSeriesSummable (fun n : ℕ ↦ f n * (Λ n : ℂ)) s ∧
      LSeries (fun n : ℕ ↦ f n * (Λ n : ℂ)) s = -deriv (LSeries f) s / LSeries f s := by
  have hlog : LSeriesSummable (LSeries.logMul f) s := LSeriesSummable_logMul_of_lt_re hs
  have hΛ : LSeriesSummable (fun n : ℕ ↦ f n * (Λ n : ℂ)) s := by
    rw [LSeriesSummable, ← summable_norm_iff] at hlog ⊢
    refine hlog.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · refine LSeries.norm_term_le s ?_
      simp only [LSeries.logMul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Complex.natCast_log,
        Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
      rw [mul_comm (Real.log n)]
      exact mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (norm_nonneg _)
  have hsumf : LSeriesSummable f s := LSeriesSummable_of_abscissaOfAbsConv_lt_re hs
  have hne : LSeries f s ≠ 0 := LSeries_ne_zero_of_monoidWithZeroHom f hsumf
  have hconv := LSeries_convolution' hΛ hsumf
  rw [mul_vonMangoldt_convolution_self f, ← neg_neg (LSeries (LSeries.logMul f) s),
    ← LSeries_deriv hs] at hconv
  exact ⟨hΛ, eq_div_of_mul_eq hne hconv.symm⟩

/-- Derivative (`HasSum`) form of the Euler product for any completely multiplicative
`f : ℕ →*₀ ℂ` with `abscissaOfAbsConv f < Re s`. -/
theorem eulerProduct_neg_logDeriv_hasSum (f : ℕ →*₀ ℂ) {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv f < s.re) :
    HasSum
      (fun p : Nat.Primes ↦ Complex.log p * f p * (p : ℂ) ^ (-s) / (1 - f p * (p : ℂ) ^ (-s)))
      (-deriv (LSeries f) s / LSeries f s) := by
  obtain ⟨hΛ, hL⟩ := LSeries_mul_vonMangoldt_eq_neg_logDeriv f hs
  have hsumf : LSeriesSummable f s := LSeriesSummable_of_abscissaOfAbsConv_lt_re hs
  let g : ℕ → ℂ := LSeries.term (fun n ↦ f n * (Λ n : ℂ)) s
  have hg_sum : Summable g := hΛ
  have hg_supp : Function.support g ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    apply hn
    simp [g, LSeries.term_def, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp]
  let e := Nat.Primes.prodNatEquiv
  have hpair : Summable (fun pk : Nat.Primes × ℕ ↦ g (e pk)) :=
    (hg_sum.subtype _).comp_injective e.injective
  have hhas : HasSum (fun p : Nat.Primes ↦ ∑' k : ℕ, g (e (p, k)))
      (∑' (p : Nat.Primes) (k : ℕ), g (e (p, k))) :=
    hpair.prod.hasSum
  have hts := tsum_eq_tsum_primes_of_support_subset_prime_powers hg_sum hg_supp
  have hL' : ∑' (p : Nat.Primes) (k : ℕ), g (e (p, k)) = -deriv (LSeries f) s / LSeries f s := by
    calc
      ∑' (p : Nat.Primes) (k : ℕ), g (e (p, k)) =
          ∑' (p : Nat.Primes) (k : ℕ), g ((p : ℕ) ^ (k + 1)) := by
        refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
        rfl
      _ = ∑' n : ℕ, g n := hts.symm
      _ = -deriv (LSeries f) s / LSeries f s := hL
  rw [hL'] at hhas
  refine hhas.congr_fun fun p ↦ ?_
  have hnorm : ‖f p * (p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_term_lt_one_of_monoidWithZeroHom f hsumf p.prop
  have hterm (k : ℕ) :
      g (e (p, k)) = (Complex.log p * f p * (p : ℂ) ^ (-s)) * (f p * (p : ℂ) ^ (-s)) ^ k := by
    change g ((p : ℕ) ^ (k + 1)) = _
    have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    have hpk0 : (p : ℕ) ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) p.prop.ne_zero
    dsimp only [g]
    rw [LSeries.term_of_ne_zero hpk0, div_eq_mul_inv, ← cpow_neg, cpow_nat_pow_neg,
      map_pow, ArithmeticFunction.vonMangoldt_apply_pow hk0,
      ArithmeticFunction.vonMangoldt_apply_prime p.prop, Complex.natCast_log]
    simp only [pow_succ]
    ring
  simp_rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm, div_eq_mul_inv]

/-- Derivative (`tprod`/`tsum`) form of the Euler product for any completely multiplicative
`f : ℕ →*₀ ℂ` with `abscissaOfAbsConv f < Re s`. -/
theorem eulerProduct_neg_logDeriv_eq_tsum (f : ℕ →*₀ ℂ) {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv f < s.re) :
    -deriv (LSeries f) s / LSeries f s =
      ∑' p : Nat.Primes,
        Complex.log p * f p * (p : ℂ) ^ (-s) / (1 - f p * (p : ℂ) ^ (-s)) :=
  (eulerProduct_neg_logDeriv_hasSum f hs).tsum_eq.symm

/-- Logarithmic Euler product for `ζ(s)` (`exp` form) on `1 < Re s`. -/
theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) = riemannZeta s :=
  _root_.riemannZeta_eulerProduct_exp_log hs

/-- Logarithmic Euler product for `L(s, χ)` (`exp` form) on `1 < Re s`. -/
theorem dirichletLSeries_eulerProduct_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - χ p * (p : ℂ) ^ (-s))) = LSeries ↗χ s :=
  DirichletCharacter.LSeries_eulerProduct_exp_log χ hs

/-- Logarithmic Euler product for `L(s, χ)` (`tsum` form) on `1 < Re s`. -/
theorem dirichletLSeries_eulerProduct_log_eq_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, -Complex.log (1 - χ p * (p : ℂ) ^ (-s)) =
      LSeries (fun n ↦ χ n * Λ n / Real.log n) s :=
  DirichletCharacter.eulerProduct_log_eq_LSeries χ hs

/-- Logarithmic derivative of the Euler product for `ζ(s)` (`HasSum` form) on `1 < Re s`:
`∑' p, log p * p^(-s) / (1 - p^(-s)) = -ζ'(s) / ζ(s)`. -/
theorem riemannZeta_neg_logDeriv_hasSum_primes {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes ↦ Complex.log p * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)))
      (-deriv riemannZeta s / riemannZeta s) := by
  let u : ℕ →*₀ ℂ :=
    { toFun := fun n ↦ if n = 0 then 0 else 1
      map_zero' := rfl
      map_one' := by simp
      map_mul' := fun m n ↦ by
        by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn] }
  have hu_abs : LSeries.abscissaOfAbsConv u < s.re := by
    have hcongr : LSeries.abscissaOfAbsConv u = LSeries.abscissaOfAbsConv 1 :=
      LSeries.abscissaOfAbsConv_congr (fun {n} hn ↦ by simp [u, hn])
    rw [hcongr, LSeries.abscissaOfAbsConv_one]
    exact mod_cast hs
  have heq : LSeries u =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    have hL : LSeries u z = LSeries 1 z := LSeries_congr (fun {n} hn ↦ by simp [u, hn]) z
    rw [hL, LSeries_one_eq_riemannZeta hz]
  have hval : LSeries u s = riemannZeta s := heq.eq_of_nhds
  have hderiv : deriv (LSeries u) s = deriv riemannZeta s := heq.deriv_eq
  have hhas := eulerProduct_neg_logDeriv_hasSum u hu_abs
  rw [hval, hderiv] at hhas
  refine hhas.congr_fun fun p ↦ ?_
  simp [u, p.prop.ne_zero]

/-- Logarithmic derivative of the Euler product for `ζ(s)` (`tsum` form) on `1 < Re s`. -/
theorem riemannZeta_neg_logDeriv_eq_tsum_primes {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      ∑' p : Nat.Primes, Complex.log p * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) :=
  (riemannZeta_neg_logDeriv_hasSum_primes hs).tsum_eq.symm

/-- Alternate form of the logarithmic derivative of the Euler product for `ζ(s)` on `1 < Re s`:
`-ζ'(s) / ζ(s) = ∑' p, log p / (p^s - 1)`. -/
theorem riemannZeta_neg_logDeriv_eq_tsum_primes' {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      ∑' p : Nat.Primes, Complex.log p / ((p : ℂ) ^ s - 1) := by
  rw [riemannZeta_neg_logDeriv_eq_tsum_primes hs]
  refine tsum_congr fun p ↦ ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hmul : (p : ℂ) ^ (-s) * (p : ℂ) ^ s = 1 := by
    rw [← cpow_add _ _ hp0, neg_add_cancel, cpow_zero]
  have hps0 : (p : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp0)
  have h1 : (1 - (p : ℂ) ^ (-s)) * (p : ℂ) ^ s = (p : ℂ) ^ s - 1 := by
    rw [sub_mul, one_mul, hmul]
  rw [← h1]
  field_simp [hps0]
  rw [mul_assoc, hmul, mul_one]

/-- Logarithmic derivative of the Euler product for `L(s, χ)` (`HasSum` form) on `1 < Re s`. -/
theorem dirichletLSeries_neg_logDeriv_hasSum_primes {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun p : Nat.Primes ↦
        Complex.log p * χ p * (p : ℂ) ^ (-s) / (1 - χ p * (p : ℂ) ^ (-s)))
      (-deriv (LSeries ↗χ) s / LSeries ↗χ s) := by
  let u : ℕ →*₀ ℂ :=
    { toFun := fun n ↦ if n = 0 then 0 else χ n
      map_zero' := rfl
      map_one' := by simp
      map_mul' := fun m n ↦ by
        by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn] }
  have hu_abs : LSeries.abscissaOfAbsConv u < s.re := by
    have hcongr : LSeries.abscissaOfAbsConv u = LSeries.abscissaOfAbsConv ↗χ :=
      LSeries.abscissaOfAbsConv_congr (fun {n} hn ↦ by simp [u, hn])
    rw [hcongr]
    rcases eq_or_ne N 0 with rfl | hN
    · have h0 : LSeries.abscissaOfAbsConv (↗(χ : DirichletCharacter ℂ 0)) ≤ 1 :=
        LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ ↦ χ.norm_le_one n⟩
      exact h0.trans_lt (mod_cast hs)
    · rw [DirichletCharacter.abscissaOfAbsConv_eq_one hN]
      exact mod_cast hs
  have heq : LSeries u = LSeries ↗χ := by
    ext z
    exact LSeries_congr (fun {n} hn ↦ by simp [u, hn]) z
  have hhas := eulerProduct_neg_logDeriv_hasSum u hu_abs
  rw [heq] at hhas
  refine hhas.congr_fun fun p ↦ ?_
  simp [u, p.prop.ne_zero]

/-- Logarithmic derivative of the Euler product for `L(s, χ)` (`tsum` form) on `1 < Re s`. -/
theorem dirichletLSeries_neg_logDeriv_eq_tsum_primes {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    -deriv (LSeries ↗χ) s / LSeries ↗χ s =
      ∑' p : Nat.Primes, Complex.log p * χ p * (p : ℂ) ^ (-s) / (1 - χ p * (p : ℂ) ^ (-s)) :=
  (dirichletLSeries_neg_logDeriv_hasSum_primes χ hs).tsum_eq.symm

end AnalyticNumberTheory.DirichletSeries
