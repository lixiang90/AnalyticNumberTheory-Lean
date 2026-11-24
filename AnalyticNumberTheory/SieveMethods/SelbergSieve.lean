import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SelbergSieve

/-!
# The Selberg Sieve

This file bridges and extends `Mathlib.NumberTheory.SelbergSieve` (`BoundingSieve` and
`SelbergSieve`) in the namespace `AnalyticNumberTheory.SieveMethods`:

- Bridges between `(A, P, X, ω)` sieve data (`ν(d) = ω(d) / d`) and Mathlib's `BoundingSieve`,
  together with `selbergEulerProd s = ∏_{p ∣ P} (1 - ν(p))`.
- Explicit optimal Selberg weights `selbergOptW s z d`, the `G_d(z / d) / G(z)` representation,
  `selbergOptW s z 1 = 1`, uniform bound `|selbergOptW s z d| ≤ 1`, and complete diagonalization
  `mainSum (lambdaSquared (selbergOptW s z)) = 1 / G(z)` and double-sum form
  `∑_{d₁, d₂ ≤ z} w_{d₁} w_{d₂} ν([d₁, d₂]) = 1 / G(z)`.
- General Selberg upper-bound sieve theorems (`selberg_upper_bound`, `selberg_upper_bound_simple`,
  `selberg_upper_bound_level`) and comparison inequalities between `1 / G(z)` and `V(P)`.
- Concrete applications:
  * **Primes in intervals**: `π(x + y) - π(x) ≤ (2 + o(1)) y / log y` (plus explicit bound).
  * **Twin primes upper bound**: `π₂(x) ≤ C * x / (log x)^2`.
  * **Binary Goldbach upper bound**:
    `r₂(2N) ≤ C * (N / (log N)^2) * ∏_{p ∣ N, p > 2} (1 + 1 / (p - 2))`.
-/

noncomputable section

open Finset Filter Asymptotics BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Classical
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.SieveMethods

/-! ### Bridge with Mathlib's `BoundingSieve` and `SelbergSieve` -/

section SelbergBridge

/-- The finite set of primes `p ≤ z` represented using `Nat.primesLE`. -/
def selbergPrimeFinset (z : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊z⌋₊

/-- The primorial product `∏_{p ≤ z} p`. -/
def selbergPrimeProd (z : ℝ) : ℕ :=
  primorial ⌊z⌋₊

/-- `selbergPrimeProd z` is strictly positive. -/
theorem selbergPrimeProd_pos (z : ℝ) : 0 < selbergPrimeProd z :=
  primorial_pos _

/-- `selbergPrimeProd z` is nonzero. -/
theorem selbergPrimeProd_ne_zero (z : ℝ) : selbergPrimeProd z ≠ 0 :=
  (selbergPrimeProd_pos z).ne'

/-- `selbergPrimeProd z` is squarefree. -/
theorem selbergPrimeProd_squarefree (z : ℝ) : Squarefree (selbergPrimeProd z) :=
  squarefree_primorial _

/-- The prime factors of `selbergPrimeProd z` are `selbergPrimeFinset z`. -/
theorem primeFactors_selbergPrimeProd (z : ℝ) :
    (selbergPrimeProd z).primeFactors = selbergPrimeFinset z := by
  rw [selbergPrimeProd, primeFactors_primorial, selbergPrimeFinset]

/-- Membership in `selbergPrimeFinset z` characterizes primes `p` with `(p : ℝ) ≤ z`. -/
theorem mem_selbergPrimeFinset_iff {z : ℝ} {p : ℕ} :
    p ∈ selbergPrimeFinset z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  unfold selbergPrimeFinset
  rw [Nat.mem_primesLE]
  constructor
  · rintro ⟨hp_le, hp⟩
    refine ⟨hp, ?_⟩
    have hfl : (⌊z⌋₊ : ℝ) ≤ z := by
      by_cases hz : 0 ≤ z
      · exact Nat.floor_le hz
      · have h0 : ⌊z⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hz)
        exfalso
        exact hp.ne_zero (Nat.le_zero.mp (h0 ▸ hp_le))
    exact (by exact_mod_cast hp_le : (p : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans hfl
  · rintro ⟨hp, hpz⟩
    exact ⟨Nat.le_floor hpz, hp⟩

/-- A prime `p` divides `selbergPrimeProd z` if and only if `(p : ℝ) ≤ z`. -/
theorem prime_dvd_selbergPrimeProd_iff {z : ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ selbergPrimeProd z ↔ (p : ℝ) ≤ z := by
  have hmem : p ∈ selbergPrimeFinset z ↔ (p : ℝ) ≤ z := by
    simp [mem_selbergPrimeFinset_iff, hp]
  rw [← hmem, ← primeFactors_selbergPrimeProd, Nat.mem_primeFactors]
  simp [hp, selbergPrimeProd_ne_zero z]

/-- Every number coprime to `selbergPrimeProd z` has no prime factors `≤ z` and conversely
any prime `p > z` is coprime to `selbergPrimeProd z`. -/
theorem coprime_selbergPrimeProd_of_prime_gt {z : ℝ} {p : ℕ} (hp : p.Prime) (hpz : z < (p : ℝ)) :
    Nat.Coprime (selbergPrimeProd z) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdvd
  have hle : (p : ℝ) ≤ z := (prime_dvd_selbergPrimeProd_iff hp).mp hdvd
  linarith

/-- The Euler product `V(P) = ∏_{p ∣ P} (1 - ν(p))` associated with a `BoundingSieve`. -/
def selbergEulerProd (s : BoundingSieve) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)

/-- Each factor `1 - s.nu p` for a prime `p ∣ s.prodPrimes` is strictly positive. -/
theorem one_sub_nu_pos_of_mem_primeFactors (s : BoundingSieve) {p : ℕ}
    (hp : p ∈ s.prodPrimes.primeFactors) : 0 < 1 - s.nu p := by
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  exact sub_pos.mpr (s.nu_lt_one_of_prime p hp_prime hp_dvd)

/-- `selbergEulerProd s` is strictly positive. -/
theorem selbergEulerProd_pos (s : BoundingSieve) : 0 < selbergEulerProd s :=
  Finset.prod_pos fun _ hp => one_sub_nu_pos_of_mem_primeFactors s hp

/-- `selbergEulerProd s` is at most `1`. -/
theorem selbergEulerProd_le_one (s : BoundingSieve) : selbergEulerProd s ≤ 1 := by
  refine Finset.prod_le_one₀ (fun p hp => (one_sub_nu_pos_of_mem_primeFactors s hp).le)
    (fun p hp => ?_)
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  linarith [s.nu_pos_of_prime p hp_prime hp_dvd]

/-- Given a multiplicative root-counting function `ω`, form the arithmetic density function
`ν(d) = ω(d) / d` (with `ν(0) = 0`). -/
def selbergDensityOmega (ω : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else ω d / (d : ℝ)
  map_zero' := by simp

/-- Value of `selbergDensityOmega ω` at a nonzero natural number `d`. -/
@[simp]
theorem selbergDensityOmega_apply {ω : ArithmeticFunction ℝ} {d : ℕ} (hd : d ≠ 0) :
    selbergDensityOmega ω d = ω d / (d : ℝ) := by
  simp [selbergDensityOmega, hd]

/-- `selbergDensityOmega ω` is multiplicative whenever `ω` is multiplicative. -/
theorem selbergDensityOmega_isMultiplicative {ω : ArithmeticFunction ℝ}
    (hω : ω.IsMultiplicative) : (selbergDensityOmega ω).IsMultiplicative := by
  constructor
  · simp [selbergDensityOmega, hω.1]
  · intro m n hcop
    by_cases hm0 : m = 0
    · subst hm0; simp [selbergDensityOmega]
    by_cases hn0 : n = 0
    · subst hn0; simp [selbergDensityOmega]
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    simp only [selbergDensityOmega, ArithmeticFunction.coe_mk, hmn0, hm0, hn0, ↓reduceIte,
      Nat.cast_mul, hω.2 hcop]
    ring

/-- Construct a `BoundingSieve` with unit weights on a finset `A` from a modulus `P`,
approximation `X`, and multiplicative sieve density `ω(d)` (`0 < ω(p) < p` for primes `p ∣ P`). -/
def mkBoundingSieveOfOmega (A : Finset ℕ) (P : ℕ) (hP : Squarefree P) (X : ℝ)
    (ω : ArithmeticFunction ℝ) (hω_mult : ω.IsMultiplicative)
    (hω_pos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ω p)
    (hω_lt : ∀ p : ℕ, p.Prime → p ∣ P → ω p < (p : ℝ)) : BoundingSieve where
  support := A
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := selbergDensityOmega ω
  nu_mult := selbergDensityOmega_isMultiplicative hω_mult
  nu_pos_of_prime p hp hpP := by
    rw [selbergDensityOmega_apply hp.ne_zero]
    exact div_pos (hω_pos p hp hpP) (Nat.cast_pos.mpr hp.pos)
  nu_lt_one_of_prime p hp hpP := by
    rw [selbergDensityOmega_apply hp.ne_zero, div_lt_one (Nat.cast_pos.mpr hp.pos)]
    exact hω_lt p hp hpP

/-- Construct a `SelbergSieve` with unit weights and level `y ≥ 1` from `(A, P, X, ω)`. -/
def mkSelbergSieveOfOmega (A : Finset ℕ) (P : ℕ) (hP : Squarefree P) (X : ℝ)
    (ω : ArithmeticFunction ℝ) (hω_mult : ω.IsMultiplicative)
    (hω_pos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ω p)
    (hω_lt : ∀ p : ℕ, p.Prime → p ∣ P → ω p < (p : ℝ))
    (y : ℝ) (hy : 1 ≤ y) : SelbergSieve :=
  { mkBoundingSieveOfOmega A P hP X ω hω_mult hω_pos hω_lt with
    level := y
    one_le_level := hy }

/-- When `s.weights = fun _ => 1`, `s.siftedSum` equals the cardinality of
`{n ∈ s.support : Nat.Coprime s.prodPrimes n}`. -/
theorem siftedSum_eq_card_of_weights_one {s : BoundingSieve} (hw : ∀ n, s.weights n = 1) :
    s.siftedSum = ((s.support.filter (fun n => Nat.Coprime s.prodPrimes n)).card : ℝ) := by
  unfold BoundingSieve.siftedSum
  simp_rw [hw, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- When `s.weights = fun _ => 1`, `s.multSum d` equals the cardinality of
`{n ∈ s.support : d ∣ n}`. -/
theorem multSum_eq_card_of_weights_one {s : BoundingSieve} (hw : ∀ n, s.weights n = 1) (d : ℕ) :
    s.multSum d = ((s.support.filter (fun n => d ∣ n)).card : ℝ) := by
  unfold BoundingSieve.multSum
  simp_rw [hw, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end SelbergBridge

/-! ### Optimal Selberg Weights, Diagonalization, and Upper-Bound Theorem -/

section OptimalSelbergSieve

private lemma sum_divisors_moebius_eq_ite {m : ℕ} (hm : m ≠ 0) :
    ∑ r ∈ m.divisors, (μ r : ℝ) = if m = 1 then 1 else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hzeta := congrArg (fun f : ArithmeticFunction ℤ => f m)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hzeta
  have hsum : ∑ x ∈ m.divisorsAntidiagonal,
      (μ x.1 : ℤ) * (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
      ∑ d ∈ m.divisors, (μ d : ℤ) := by
    refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro x hx
      exact Nat.fst_mem_divisors_of_mem_antidiagonal hx
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 := Nat.mem_divisorsAntidiagonal.mp hx₁
      have h2 := Nat.mem_divisorsAntidiagonal.mp hx₂
      have hx1_nz : x₁.1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact hm h1.1.symm
      have hsnd : x₁.2 = x₂.2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx1_nz)
        (h1.1.trans (heq ▸ h2.1.symm))
      exact Prod.ext heq hsnd
    · intro d hd
      have hdm := Nat.dvd_of_mem_divisors hd
      exact ⟨(d, m / d), Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hdm, hm⟩, rfl⟩
    · intro x hx
      have hx2_nz : x.2 ≠ 0 := by
        intro h0
        have h1 := (Nat.mem_divisorsAntidiagonal.mp hx).1
        rw [h0, mul_zero] at h1
        exact hm h1.symm
      have hζ : (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 = 1 := by
        simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hx2_nz]
      rw [hζ, mul_one]
  rw [hsum] at hzeta
  have hcast := congrArg (fun k : ℤ => (k : ℝ)) hzeta
  push_cast at hcast
  exact hcast

/-- The truncated Selberg sum `G(z) = ∑_{d ∣ P, d ≤ z} g(d)`, where
`g(d) = s.selbergTerms d`. -/
def selbergG (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z), s.selbergTerms d

/-- The coprime truncated Selberg sum `G_d(u) = ∑_{m ∣ P, gcd(m, d) = 1, m ≤ u} g(m)`. -/
def selbergGCoprime (s : BoundingSieve) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ s.prodPrimes.divisors.filter (fun m : ℕ => m.Coprime d ∧ (m : ℝ) ≤ u),
    s.selbergTerms m

/-- Every term `s.selbergTerms d` for `d ∣ s.prodPrimes` is nonnegative. -/
theorem selbergTerms_nonneg_of_mem {s : BoundingSieve} {d : ℕ}
    (hd : d ∈ s.prodPrimes.divisors) : 0 ≤ s.selbergTerms d :=
  (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le

/-- `selbergG s z` is always nonnegative. -/
theorem selbergG_nonneg (s : BoundingSieve) (z : ℝ) : 0 ≤ selbergG s z :=
  Finset.sum_nonneg fun _ hd => selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hd).1

/-- `selbergGCoprime s d u` is always nonnegative. -/
theorem selbergGCoprime_nonneg (s : BoundingSieve) (d : ℕ) (u : ℝ) :
    0 ≤ selbergGCoprime s d u :=
  Finset.sum_nonneg fun _ hm => selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hm).1

/-- For `1 ≤ z`, `selbergG s z ≥ 1`. -/
theorem selbergG_ge_one {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) : 1 ≤ selbergG s z := by
  have h1_mem : 1 ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z) := by
    refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero, ?_⟩
    exact_mod_cast hz
  have h1_eq : s.selbergTerms 1 = 1 := s.selbergTerms_isMultiplicative.1
  calc
    (1 : ℝ) = s.selbergTerms 1 := h1_eq.symm
    _ ≤ selbergG s z := Finset.single_le_sum
        (fun d hd => selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hd).1) h1_mem

/-- For `1 ≤ z`, `0 < selbergG s z`. -/
theorem selbergG_pos {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) : 0 < selbergG s z :=
  lt_of_lt_of_le zero_lt_one (selbergG_ge_one hz)

/-- Monotonicity of `selbergG s` in the truncation level `z`. -/
@[gcongr]
theorem selbergG_mono {s : BoundingSieve} {w z : ℝ} (hwz : w ≤ z) :
    selbergG s w ≤ selbergG s z := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d hd _ =>
    selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hd).1)
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd'.1, hd'.2.trans hwz⟩

/-- When `d = 1`, `selbergGCoprime s 1 u` equals `selbergG s u`. -/
@[simp]
theorem selbergGCoprime_one (s : BoundingSieve) (u : ℝ) :
    selbergGCoprime s 1 u = selbergG s u := by
  unfold selbergGCoprime selbergG
  congr 1
  ext m
  simp

/-- Helper identity summing `s.selbergTerms r` over all divisors of `d ∣ s.prodPrimes`:
`∑_{r ∣ d} g(r) = ∏_{p ∣ d} (1 - ν(p))⁻¹`. -/
theorem sum_divisors_selbergTerms_eq_prod (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    ∑ r ∈ d.divisors, s.selbergTerms r = ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
  have hd_nz : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd
  have hsum := s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
  have hflt : s.prodPrimes.divisors.filter (· ∣ d) = d.divisors := by
    rw [Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd]
  rw [← Finset.sum_filter, hflt] at hsum
  rw [hsum, s.selbergTerms_apply d]
  have hnu : s.nu d ≠ 0 := s.nu_ne_zero hd
  field_simp [hnu]

/-- The optimal Selberg sieve vector `w_d` minimizing the diagonalized quadratic form:
`w_d = (μ(d) / (ν(d) * G(z))) * ∑_{k ∣ P, d ∣ k, k ≤ z} g(k)` for `d ∣ P` and `(d : ℝ) ≤ z`,
and `0` otherwise. -/
def selbergOptW (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes ∧ (d : ℝ) ≤ z then
    ((μ d : ℝ) / (s.nu d * selbergG s z)) *
      ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => d ∣ k ∧ (k : ℝ) ≤ z), s.selbergTerms k
  else 0

/-- Outside `{d ∣ s.prodPrimes : (d : ℝ) ≤ z}`, `selbergOptW s z d = 0`. -/
theorem selbergOptW_eq_zero_of_not {s : BoundingSieve} {z : ℝ} {d : ℕ}
    (h : ¬ (d ∣ s.prodPrimes ∧ (d : ℝ) ≤ z)) : selbergOptW s z d = 0 := by
  simp [selbergOptW, h]

/-- Textbook representation of the optimal Selberg weights in terms of `selbergGCoprime`:
for `1 ≤ z`, `d ∣ s.prodPrimes`, and `(d : ℝ) ≤ z`,
`selbergOptW s z d = μ(d) * (∏_{p ∣ d} (1 - ν(p))⁻¹) * G_d(z / d) / G(z)`. -/
theorem selbergOptW_eq_G_coprime {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ s.prodPrimes) (hdz : (d : ℝ) ≤ z) :
    selbergOptW s z d =
      (μ d : ℝ) * (∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹) *
        selbergGCoprime s d (z / d) / selbergG s z := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  have hdR_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hsum_eq :
      ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => d ∣ k ∧ (k : ℝ) ≤ z), s.selbergTerms k =
        s.selbergTerms d * selbergGCoprime s d (z / d) := by
    unfold selbergGCoprime
    rw [Finset.mul_sum]
    refine (Finset.sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_).symm
    · intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmP : m ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hm'.1
      have hdm_dvd : d * m ∣ s.prodPrimes := hm'.2.1.symm.mul_dvd_of_dvd_of_dvd hd hmP
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdm_dvd, s.prodPrimes_ne_zero⟩,
        dvd_mul_right d m, ?_⟩
      push_cast
      rw [← le_div_iff₀' hdR_pos]
      exact hm'.2.2
    · intro m₁ _ m₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left hd_pos heq
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkP : k ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hk'.1
      have hdk : d ∣ k := hk'.2.1
      let m := k / d
      have hdm : d * m = k := Nat.mul_div_cancel' hdk
      have hmP : m ∣ s.prodPrimes := (Nat.div_dvd_of_dvd hdk).trans hkP
      have hcop : d.Coprime m :=
        (Nat.squarefree_mul_iff.mp (hdm.symm ▸ s.squarefree_of_dvd_prodPrimes hkP)).1
      have hm_le : (m : ℝ) ≤ z / (d : ℝ) := by
        rw [le_div_iff₀' hdR_pos]
        have hcast : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; rfl
        rw [← hcast, hdm]
        exact hk'.2.2
      exact ⟨m, Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hmP, s.prodPrimes_ne_zero⟩, hcop.symm, hm_le⟩, hdm⟩
    · intro m hm
      have hcop : d.Coprime m := (Finset.mem_filter.mp hm).2.1.symm
      exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop).symm
  have hcond : d ∣ s.prodPrimes ∧ (d : ℝ) ≤ z := ⟨hd, hdz⟩
  rw [selbergOptW, ite_eq_left_iff.mpr (fun h => (h hcond).elim), hsum_eq, s.selbergTerms_apply d]
  have hnu : s.nu d ≠ 0 := s.nu_ne_zero hd
  have hG : selbergG s z ≠ 0 := (selbergG_pos hz).ne'
  field_simp [hnu, hG]

/-- For `1 ≤ z`, `selbergOptW s z 1 = 1`, so `lambdaSquared (selbergOptW s z)` defines
an upper Möbius weight sequence. -/
theorem selbergOptW_one {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) :
    selbergOptW s z 1 = 1 := by
  have h1_le : ((1 : ℕ) : ℝ) ≤ z := by exact_mod_cast hz
  rw [selbergOptW_eq_G_coprime hz (one_dvd _) h1_le]
  have hG : selbergG s z ≠ 0 := (selbergG_pos hz).ne'
  simp [div_self hG]

/-- Every optimal Selberg weight satisfies `|selbergOptW s z d| ≤ 1`. -/
theorem selbergOptW_abs_le_one {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) (d : ℕ) :
    |selbergOptW s z d| ≤ 1 := by
  by_cases hd : d ∣ s.prodPrimes ∧ (d : ℝ) ≤ z
  · rw [selbergOptW_eq_G_coprime hz hd.1 hd.2]
    have hd_nz : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd.1
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_nz
    have hμ_abs : |(μ d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hprod_nn : 0 ≤ ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
      refine Finset.prod_nonneg fun p hp => inv_nonneg.mpr ?_
      exact (one_sub_nu_pos_of_mem_primeFactors s
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans hd.1, s.prodPrimes_ne_zero⟩)).le
    have hGc_nn : 0 ≤ selbergGCoprime s d (z / d) := selbergGCoprime_nonneg s d (z / d)
    have hG_pos : 0 < selbergG s z := selbergG_pos hz
    have hnum_le :
        (∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹) * selbergGCoprime s d (z / d) ≤ selbergG s z := by
      rw [← sum_divisors_selbergTerms_eq_prod s hd.1]
      unfold selbergGCoprime selbergG
      let T := s.prodPrimes.divisors.filter (fun m : ℕ => m.Coprime d ∧ (m : ℝ) ≤ z / d)
      rw [Finset.sum_mul_sum]
      rw [← Finset.sum_product']
      have himg_inj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ((d.divisors ×ˢ T : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
        intro ⟨r₁, m₁⟩ h₁ ⟨r₂, m₂⟩ h₂ heq
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors, T,
          Finset.mem_filter] at h₁ h₂
        have hr₁d : r₁ ∣ d := h₁.1.1
        have hr₂d : r₂ ∣ d := h₂.1.1
        have hm₁d : m₁.Coprime d := h₁.2.2.1
        have hm₂d : m₂.Coprime d := h₂.2.2.1
        have hgcd1 : Nat.gcd (r₁ * m₁) d = r₁ := by
          have hc : m₁.Coprime (d / r₁) := hm₁d.coprime_dvd_right (Nat.div_dvd_of_dvd hr₁d)
          conv_rhs => rw [← mul_one r₁, ← hc.gcd_eq_one, ← Nat.gcd_mul_left,
            Nat.mul_div_cancel' hr₁d]
        have hgcd2 : Nat.gcd (r₂ * m₂) d = r₂ := by
          have hc : m₂.Coprime (d / r₂) := hm₂d.coprime_dvd_right (Nat.div_dvd_of_dvd hr₂d)
          conv_rhs => rw [← mul_one r₂, ← hc.gcd_eq_one, ← Nat.gcd_mul_left,
            Nat.mul_div_cancel' hr₂d]
        have hr_eq : r₁ = r₂ := hgcd1.symm.trans (congrArg (fun k => Nat.gcd k d) heq |>.trans hgcd2)
        have hr₁_pos : 0 < r₁ := Nat.pos_of_dvd_of_pos hr₁d hd_pos
        have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hr₁_pos (hr_eq ▸ heq)
        exact Prod.ext hr_eq hm_eq
      have hterm_eq : ∀ x ∈ d.divisors ×ˢ T,
          s.selbergTerms x.1 * s.selbergTerms x.2 = s.selbergTerms (x.1 * x.2) := by
        intro ⟨r, m⟩ hx
        have hx' := Finset.mem_product.mp hx
        have hrd : r ∣ d := Nat.dvd_of_mem_divisors hx'.1
        have hmd : m.Coprime d := (Finset.mem_filter.mp hx'.2).2.1
        have hcop : r.Coprime m := (hmd.coprime_dvd_right hrd).symm
        exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop).symm
      have hsub : (d.divisors ×ˢ T).image (fun x : ℕ × ℕ => x.1 * x.2) ⊆
          s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨⟨r, m⟩, hx, rfl⟩
        have hx' := Finset.mem_product.mp hx
        have hrd : r ∣ d := Nat.dvd_of_mem_divisors hx'.1
        have hm' := Finset.mem_filter.mp hx'.2
        have hmP : m ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hm'.1
        have hmd : m.Coprime d := hm'.2.1
        have hcop : r.Coprime m := (hmd.coprime_dvd_right hrd).symm
        have hkP : r * m ∣ s.prodPrimes := hcop.mul_dvd_of_dvd_of_dvd (hrd.trans hd.1) hmP
        have hr_le : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_dvd hd_pos hrd
        have hk_le : ((r * m : ℕ) : ℝ) ≤ z := by
          have hm_le : (m : ℝ) ≤ z / (d : ℝ) := hm'.2.2
          have hdR_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
          have hdm_le : (d : ℝ) * (m : ℝ) ≤ z := (le_div_iff₀' hdR_pos).mp hm_le
          push_cast
          exact (mul_le_mul_of_nonneg_right hr_le (Nat.cast_nonneg _)).trans hdm_le
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hkP, s.prodPrimes_ne_zero⟩, hk_le⟩
      calc
        ∑ x ∈ d.divisors ×ˢ T, s.selbergTerms x.1 * s.selbergTerms x.2
            = ∑ x ∈ d.divisors ×ˢ T, s.selbergTerms (x.1 * x.2) :=
                Finset.sum_congr rfl hterm_eq
        _ = ∑ k ∈ (d.divisors ×ˢ T).image (fun x : ℕ × ℕ => x.1 * x.2), s.selbergTerms k :=
                (Finset.sum_image himg_inj).symm
        _ ≤ ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z), s.selbergTerms k :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun k hk _ => selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hk).1)
    calc
      |(μ d : ℝ) * (∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹) * selbergGCoprime s d (z / d) /
          selbergG s z|
          = |(μ d : ℝ)| * ((∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹) *
              selbergGCoprime s d (z / d)) / selbergG s z := by
              rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hprod_nn, abs_of_nonneg hGc_nn,
                abs_of_pos hG_pos]
              ring
      _ ≤ 1 * selbergG s z / selbergG s z := by
              gcongr
      _ = 1 := by rw [one_mul, div_self hG_pos.ne']
  · rw [selbergOptW_eq_zero_of_not hd, abs_zero]
    exact zero_le_one

private lemma sum_divisors_moebius_filter_dvd {s : BoundingSieve} {l k : ℕ}
    (hl : l ∣ k) (hk : k ∣ s.prodPrimes) :
    ∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ k), (μ d : ℝ) =
      if k = l then (μ l : ℝ) else 0 := by
  have hk_sq : Squarefree k := s.squarefree_of_dvd_prodPrimes hk
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_sq.ne_zero
  have hl_pos : 0 < l := Nat.pos_of_dvd_of_pos hl hk_pos
  let m := k / l
  have hkm : l * m = k := Nat.mul_div_cancel' hl
  have hm_nz : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hkm
    exact hk_pos.ne' hkm.symm
  have hcop_lm : l.Coprime m := (Nat.squarefree_mul_iff.mp (hkm.symm ▸ hk_sq)).1
  have hbij :
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ k), (μ d : ℝ) =
        ∑ r ∈ m.divisors, (μ l : ℝ) * (μ r : ℝ) := by
    refine (Finset.sum_bij (fun r _ => l * r) ?_ ?_ ?_ ?_).symm
    · intro r hr
      have hrm : r ∣ m := Nat.dvd_of_mem_divisors hr
      have hlr_k : l * r ∣ k := hkm ▸ Nat.mul_dvd_mul_left l hrm
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hlr_k.trans hk, s.prodPrimes_ne_zero⟩, dvd_mul_right l r, hlr_k⟩
    · intro r₁ _ r₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left hl_pos heq
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      let r := d / l
      have hdr : l * r = d := Nat.mul_div_cancel' hd'.2.1
      have hrm : r ∣ m := by
        have : l * r ∣ l * m := hdr.symm ▸ hkm.symm ▸ hd'.2.2
        exact Nat.dvd_of_mul_dvd_mul_left hl_pos this
      exact ⟨r, Nat.mem_divisors.mpr ⟨hrm, hm_nz⟩, hdr⟩
    · intro r hr
      have hrm : r ∣ m := Nat.dvd_of_mem_divisors hr
      have hcop_lr : l.Coprime r := hcop_lm.coprime_dvd_right hrm
      have hμ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_lr
      exact_mod_cast hμ.symm
  rw [hbij, ← Finset.mul_sum, sum_divisors_moebius_eq_ite hm_nz]
  have hm_eq_one : m = 1 ↔ k = l := by
    constructor
    · intro hm1; rw [← hkm, hm1, mul_one]
    · intro hkl; apply Nat.eq_of_mul_eq_mul_left hl_pos; rw [hkm, hkl, mul_one]
  simp only [hm_eq_one]
  split_ifs <;> ring

/-- Exact evaluation of the linear form `∑_{l ∣ d} ν(d) w_d` for the optimal Selberg weights:
it equals `μ(l) g(l) / G(z)` when `(l : ℝ) ≤ z`, and `0` otherwise. -/
theorem selbergOptW_sum_divisors_mul_nu {s : BoundingSieve} {z : ℝ} (_hz : 1 ≤ z) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    ∑ d ∈ s.prodPrimes.divisors, (if l ∣ d then s.nu d * selbergOptW s z d else 0) =
      if (l : ℝ) ≤ z then (μ l : ℝ) * s.selbergTerms l / selbergG s z else 0 := by
  have hrewrite :
      ∑ d ∈ s.prodPrimes.divisors, (if l ∣ d then s.nu d * selbergOptW s z d else 0) =
        ∑ d ∈ s.prodPrimes.divisors,
          ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z),
            if l ∣ d ∧ d ∣ k then (μ d : ℝ) * s.selbergTerms k / selbergG s z else 0 := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP)
    by_cases hld : l ∣ d
    · by_cases hdz : (d : ℝ) ≤ z
      · have hnu : s.nu d ≠ 0 := s.nu_ne_zero hdP
        have hcond : d ∣ s.prodPrimes ∧ (d : ℝ) ≤ z := ⟨hdP, hdz⟩
        conv_lhs => simp only [hld, ↓reduceIte, selbergOptW, hcond, and_self]
        have hterm : s.nu d * (((μ d : ℝ) / (s.nu d * selbergG s z)) *
            ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => d ∣ k ∧ (k : ℝ) ≤ z),
              s.selbergTerms k) =
            ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => d ∣ k ∧ (k : ℝ) ≤ z),
              (μ d : ℝ) * s.selbergTerms k / selbergG s z := by
          rw [← mul_assoc, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          field_simp [hnu]
        have hrhs :
            (∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z),
              if l ∣ d ∧ d ∣ k then (μ d : ℝ) * s.selbergTerms k / selbergG s z else 0) =
            ∑ k ∈ (s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z)).filter
              (fun k : ℕ => l ∣ d ∧ d ∣ k), (μ d : ℝ) * s.selbergTerms k / selbergG s z :=
          (Finset.sum_filter _ _).symm
        rw [hterm, hrhs, Finset.filter_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext k
        simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, hld, true_and]
        tauto
      · conv_lhs => simp only [hld, ↓reduceIte]
        rw [selbergOptW_eq_zero_of_not (fun h => hdz h.2), mul_zero]
        symm
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk' := Finset.mem_filter.mp hk
        have hnot : ¬ (l ∣ d ∧ d ∣ k) := by
          rintro ⟨_, hdk⟩
          have hk_pos : 0 < k := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
            (Nat.dvd_of_mem_divisors hk'.1))
          have hdk_le : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_dvd hk_pos hdk
          exact hdz (hdk_le.trans hk'.2)
        rw [ite_eq_right_iff]
        intro h
        exact (hnot h).elim
    · conv_lhs => simp only [hld, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      have hnot : ¬ (l ∣ d ∧ d ∣ k) := fun h => hld h.1
      rw [ite_eq_right_iff]
      intro h
      exact (hnot h).elim
  rw [hrewrite, Finset.sum_comm]
  have hcollapse :
      ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z),
        ∑ d ∈ s.prodPrimes.divisors,
          (if l ∣ d ∧ d ∣ k then (μ d : ℝ) * s.selbergTerms k / selbergG s z else 0) =
      ∑ k ∈ s.prodPrimes.divisors.filter (fun k : ℕ => (k : ℝ) ≤ z),
        (if k = l then (μ l : ℝ) * s.selbergTerms l / selbergG s z else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkP : k ∣ s.prodPrimes := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1
    by_cases hlk : l ∣ k
    · have hinner :
          ∑ d ∈ s.prodPrimes.divisors,
            (if l ∣ d ∧ d ∣ k then (μ d : ℝ) * s.selbergTerms k / selbergG s z else 0) =
          (∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ k), (μ d : ℝ)) *
            (s.selbergTerms k / selbergG s z) := by
        rw [← Finset.sum_filter, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => by ring
      rw [hinner, sum_divisors_moebius_filter_dvd hlk hkP]
      split_ifs with hkl
      · subst hkl; ring
      · simp
    · have hzero :
          ∑ d ∈ s.prodPrimes.divisors,
            (if l ∣ d ∧ d ∣ k then (μ d : ℝ) * s.selbergTerms k / selbergG s z else 0) = 0 := by
        refine Finset.sum_eq_zero fun d _ => ?_
        have hnot : ¬ (l ∣ d ∧ d ∣ k) := fun h => hlk (h.1.trans h.2)
        simp only [eq_false hnot, ↓reduceIte]
      have hne : k ≠ l := fun hkl => hlk (hkl ▸ dvd_rfl)
      simp only [hzero, eq_false hne, ↓reduceIte]
  rw [hcollapse]
  by_cases hlz : (l : ℝ) ≤ z
  · simp only [hlz, ↓reduceIte]
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_filter, Nat.mem_divisors, hl, hlz, s.prodPrimes_ne_zero]
  · simp only [hlz, ↓reduceIte]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hne : k ≠ l := by
      rintro rfl
      exact hlz (Finset.mem_filter.mp hk).2
    simp only [eq_false hne, ↓reduceIte]

/-- Complete Selberg diagonalization identity:
`s.mainSum (lambdaSquared (selbergOptW s z)) = (selbergG s z)⁻¹`. -/
theorem selbergOptW_mainSum_eq_inv_G {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) :
    s.mainSum (lambdaSquared (selbergOptW s z)) = (selbergG s z)⁻¹ := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq (selbergOptW s z)]
  have hG_pos : 0 < selbergG s z := selbergG_pos hz
  have hterm :
      ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergOptW s z d else 0) ^ 2 =
      ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => (l : ℝ) ≤ z),
        s.selbergTerms l / (selbergG s z) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (s.prodPrimes.divisors) (fun l : ℕ => (l : ℝ) ≤ z)]
    have hnot :
        ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => ¬ (l : ℝ) ≤ z), (s.selbergTerms l)⁻¹ *
          (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergOptW s z d else 0) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' := Finset.mem_filter.mp hl
      have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl'.1
      rw [selbergOptW_sum_divisors_mul_nu hz hlP]
      simp only [hl'.2, ↓reduceIte]
      simp
    rw [hnot, add_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_filter.mp hl
    have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl'.1
    have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hlP
    have hμ_sq : ((μ l : ℝ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hl_sq
    have hg : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos hlP).ne'
    rw [selbergOptW_sum_divisors_mul_nu hz hlP]
    simp only [hl'.2, ↓reduceIte]
    calc
      (s.selbergTerms l)⁻¹ * ((μ l : ℝ) * s.selbergTerms l / selbergG s z) ^ 2
          = (μ l : ℝ) ^ 2 * (s.selbergTerms l * (s.selbergTerms l)⁻¹) * s.selbergTerms l /
              (selbergG s z) ^ 2 := by ring
      _ = 1 * 1 * s.selbergTerms l / (selbergG s z) ^ 2 := by
              rw [hμ_sq, mul_inv_cancel₀ hg]
      _ = s.selbergTerms l / (selbergG s z) ^ 2 := by ring
  rw [hterm, ← Finset.sum_div]
  change selbergG s z / (selbergG s z) ^ 2 = (selbergG s z)⁻¹
  field_simp [hG_pos.ne']

/-- Double-sum diagonalization of the optimal Selberg weights:
`∑_{d₁ ≤ z} ∑_{d₂ ≤ z} w_{d₁} w_{d₂} ν([d₁, d₂]) = 1 / G(z)`. -/
theorem selbergOptW_double_sum_diag {s : BoundingSieve} {z : ℝ} (hz : 1 ≤ z) :
    ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
      ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        selbergOptW s z d₁ * selbergOptW s z d₂ * s.nu (d₁.lcm d₂) = (selbergG s z)⁻¹ := by
  have hmain := s.mainSum_lambdaSquared_eq_sum_sum_mul (selbergOptW s z)
  rw [selbergOptW_mainSum_eq_inv_G hz] at hmain
  rw [hmain]
  have hrestrict :
      ∑ d₁ ∈ s.prodPrimes.divisors, ∑ d₂ ∈ s.prodPrimes.divisors,
        s.nu d₁ * selbergOptW s z d₁ * s.nu d₂ * selbergOptW s z d₂ * (s.nu (d₁.gcd d₂))⁻¹ =
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          s.nu d₁ * selbergOptW s z d₁ * s.nu d₂ * selbergOptW s z d₂ * (s.nu (d₁.gcd d₂))⁻¹ := by
    simp_rw [← Finset.sum_filter_add_sum_filter_not s.prodPrimes.divisors (fun d : ℕ => (d : ℝ) ≤ z)]
    have h1 :
        ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
          (∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
            s.nu d₁ * selbergOptW s z d₁ * s.nu d₂ * selbergOptW s z d₂ * (s.nu (d₁.gcd d₂))⁻¹ +
           ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
            s.nu d₁ * selbergOptW s z d₁ * s.nu d₂ * selbergOptW s z d₂ *
              (s.nu (d₁.gcd d₂))⁻¹) = 0 := by
      refine Finset.sum_eq_zero fun d₁ hd₁ => ?_
      have hd₁' := (Finset.mem_filter.mp hd₁).2
      have hw1 : selbergOptW s z d₁ = 0 := selbergOptW_eq_zero_of_not (fun h => hd₁' h.2)
      simp [hw1]
    rw [h1, add_zero]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    have h2 :
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
          s.nu d₁ * selbergOptW s z d₁ * s.nu d₂ * selbergOptW s z d₂ * (s.nu (d₁.gcd d₂))⁻¹ = 0 := by
      refine Finset.sum_eq_zero fun d₂ hd₂ => ?_
      have hd₂' := (Finset.mem_filter.mp hd₂).2
      have hw2 : selbergOptW s z d₂ = 0 := selbergOptW_eq_zero_of_not (fun h => hd₂' h.2)
      simp [hw2]
    rw [h2, add_zero]
  rw [hrestrict]
  refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
  have hd₁P : d₁ ∣ s.prodPrimes := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₁).1
  have hgcd_nz : s.nu (d₁.gcd d₂) ≠ 0 :=
    s.nu_ne_zero ((Nat.gcd_dvd_left d₁ d₂).trans hd₁P)
  rw [s.nu_mult.map_lcm hgcd_nz]
  ring

/-- Error-sum bound for `lambdaSquared` of a sequence `w` supported on `{d ∣ P : (d : ℝ) ≤ z}`. -/
theorem errSum_lambdaSquared_le {s : BoundingSieve} {z : ℝ} (w : ℕ → ℝ)
    (hsupp : ∀ d, ¬ (d ∣ s.prodPrimes ∧ (d : ℝ) ≤ z) → w d = 0) :
    s.errSum (lambdaSquared w) ≤
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          |w d₁| * |w d₂| * |s.rem (d₁.lcm d₂)| := by
  unfold BoundingSieve.errSum lambdaSquared
  calc
    ∑ d ∈ s.prodPrimes.divisors,
        |∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors, if d = d₁.lcm d₂ then w d₁ * w d₂ else 0| *
          |s.rem d|
        ≤ ∑ d ∈ s.prodPrimes.divisors,
            (∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
              if d = d₁.lcm d₂ then |w d₁| * |w d₂| else 0) * |s.rem d| := by
            refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            calc
              |∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors, if d = d₁.lcm d₂ then w d₁ * w d₂ else 0|
                  ≤ ∑ d₁ ∈ d.divisors, |∑ d₂ ∈ d.divisors,
                      if d = d₁.lcm d₂ then w d₁ * w d₂ else 0| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
                      |if d = d₁.lcm d₂ then w d₁ * w d₂ else 0| :=
                    Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
              _ = ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
                      if d = d₁.lcm d₂ then |w d₁| * |w d₂| else 0 := by
                    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
                    split_ifs <;> simp [abs_mul]
    _ = ∑ d ∈ s.prodPrimes.divisors, ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
          if d = d₁.lcm d₂ then |w d₁| * |w d₂| * |s.rem d| else 0 := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d₂ _ => ?_
          split_ifs <;> ring
    _ = ∑ d ∈ s.prodPrimes.divisors, ∑ d₁ ∈ s.prodPrimes.divisors, ∑ d₂ ∈ s.prodPrimes.divisors,
          if d = d₁.lcm d₂ then |w d₁| * |w d₂| * |s.rem d| else 0 := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
          have hsub : ∀ d₁ d₂, (d₁ ∣ d ∧ d₂ ∣ d ∧ d = d₁.lcm d₂) ↔ d = d₁.lcm d₂ := by
            intro d₁ d₂
            constructor
            · exact fun h => h.2.2
            · intro h; refine ⟨?_, ?_, h⟩
              · rw [h]; exact Nat.dvd_lcm_left d₁ d₂
              · rw [h]; exact Nat.dvd_lcm_right d₁ d₂
          simp_rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP, Finset.sum_filter,
            Finset.ite_sum_zero, ← ite_and, hsub]
    _ = ∑ d₁ ∈ s.prodPrimes.divisors, ∑ d₂ ∈ s.prodPrimes.divisors,
          |w d₁| * |w d₂| * |s.rem (d₁.lcm d₂)| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
          have hlcm : d₁.lcm d₂ ∣ s.prodPrimes :=
            Nat.lcm_dvd_iff.mpr ⟨Nat.dvd_of_mem_divisors hd₁, Nat.dvd_of_mem_divisors hd₂⟩
          rw [Finset.sum_ite_eq_of_mem' s.prodPrimes.divisors (d₁.lcm d₂) _
            (Nat.mem_divisors.mpr ⟨hlcm, s.prodPrimes_ne_zero⟩)]
    _ = ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
            |w d₁| * |w d₂| * |s.rem (d₁.lcm d₂)| := by
          simp_rw [← Finset.sum_filter_add_sum_filter_not s.prodPrimes.divisors
            (fun d : ℕ => (d : ℝ) ≤ z)]
          have h1 :
              ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
                (∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
                  |w d₁| * |w d₂| * |s.rem (d₁.lcm d₂)| +
                 ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
                  |w d₁| * |w d₂| * |s.rem (d₁.lcm d₂)|) = 0 := by
            refine Finset.sum_eq_zero fun d₁ hd₁ => ?_
            have hd₁' := (Finset.mem_filter.mp hd₁).2
            rw [hsupp d₁ (fun h => hd₁' h.2)]
            simp
          rw [h1, add_zero]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          have h2 :
              ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
                |w d₁| * |w d₂| * |s.rem (d₁.lcm d₂)| = 0 := by
            refine Finset.sum_eq_zero fun d₂ hd₂ => ?_
            have hd₂' := (Finset.mem_filter.mp hd₂).2
            rw [hsupp d₂ (fun h => hd₂' h.2)]
            simp
          rw [h2, add_zero]

/-- **Selberg Upper-Bound Sieve Theorem** (weighted error form): for any `1 ≤ z`,
`s.siftedSum ≤ s.totalMass / selbergG s z + ∑_{d₁, d₂ ≤ z} |w_{d₁}| |w_{d₂}| |r_{[d₁,d₂]}|`. -/
theorem selberg_upper_bound (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / selbergG s z +
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          |selbergOptW s z d₁| * |selbergOptW s z d₂| * |s.rem (d₁.lcm d₂)| := by
  have hup := s.siftedSum_le_mainSum_errSum_of_upperMoebius (lambdaSquared (selbergOptW s z))
    (upperMoebius_lambdaSquared _ (selbergOptW_one hz))
  rw [selbergOptW_mainSum_eq_inv_G hz, ← div_eq_mul_inv] at hup
  have herr := errSum_lambdaSquared_le (s := s) (z := z) (selbergOptW s z)
    (fun d hd => selbergOptW_eq_zero_of_not hd)
  linarith

/-- **Selberg Upper-Bound Sieve Theorem** (simplified error form using `|selbergOptW s z d| ≤ 1`):
`s.siftedSum ≤ s.totalMass / selbergG s z + ∑_{d₁, d₂ ≤ z} |r_{[d₁,d₂]}|`. -/
theorem selberg_upper_bound_simple (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / selbergG s z +
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          |s.rem (d₁.lcm d₂)| := by
  have h1 := selberg_upper_bound s hz
  have herr :
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          |selbergOptW s z d₁| * |selbergOptW s z d₂| * |s.rem (d₁.lcm d₂)| ≤
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          |s.rem (d₁.lcm d₂)| := by
    refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
    have hw1 := selbergOptW_abs_le_one (s := s) hz d₁
    have hw2 := selbergOptW_abs_le_one (s := s) hz d₂
    have hmul : |selbergOptW s z d₁| * |selbergOptW s z d₂| ≤ 1 := by
      simpa using mul_le_mul hw1 hw2 (abs_nonneg _) zero_le_one
    exact mul_le_of_le_one_left (abs_nonneg _) hmul
  linarith

/-- **Selberg Upper-Bound Sieve Theorem** packaged for Mathlib's `SelbergSieve` at level
`s.level` with `z = Real.sqrt s.level`, so every `d₁.lcm d₂ ≤ s.level`. -/
theorem selberg_upper_bound_level (s : SelbergSieve) :
    s.siftedSum ≤ s.totalMass / selbergG s.toBoundingSieve (Real.sqrt s.level) +
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ s.level),
        |(lambdaSquared (selbergOptW s.toBoundingSieve (Real.sqrt s.level))) d| * |s.rem d| := by
  have hz : 1 ≤ Real.sqrt s.level := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt s.one_le_level
  have hup := s.toBoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (lambdaSquared (selbergOptW s.toBoundingSieve (Real.sqrt s.level)))
    (upperMoebius_lambdaSquared _ (selbergOptW_one hz))
  rw [selbergOptW_mainSum_eq_inv_G hz, ← div_eq_mul_inv] at hup
  have herr_sub :
      s.toBoundingSieve.errSum (lambdaSquared (selbergOptW s.toBoundingSieve (Real.sqrt s.level))) ≤
        ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ s.level),
          |(lambdaSquared (selbergOptW s.toBoundingSieve (Real.sqrt s.level))) d| * |s.rem d| := by
    unfold BoundingSieve.errSum
    rw [← Finset.sum_filter_add_sum_filter_not s.prodPrimes.divisors
      (fun d : ℕ => (d : ℝ) ≤ s.level)]
    have hzero :
        ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ s.level),
          |(lambdaSquared (selbergOptW s.toBoundingSieve (Real.sqrt s.level))) d| *
            |s.rem d| = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      have hd_gt : s.level < (d : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hd).2
      have hlam0 : lambdaSquared (selbergOptW s.toBoundingSieve (Real.sqrt s.level)) d = 0 := by
        unfold lambdaSquared
        refine Finset.sum_eq_zero fun d₁ hd₁ => Finset.sum_eq_zero fun d₂ hd₂ => ?_
        split_ifs with hlcm
        · have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
          have hd₁_pos : 0 < d₁ := Nat.pos_of_ne_zero
              (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero ((Nat.dvd_of_mem_divisors hd₁).trans hdP))
          have hd₂_pos : 0 < d₂ := Nat.pos_of_ne_zero
              (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero ((Nat.dvd_of_mem_divisors hd₂).trans hdP))
          have hle_mul : d ≤ d₁ * d₂ := by
            rw [hlcm]
            exact Nat.le_of_dvd (Nat.mul_pos hd₁_pos hd₂_pos)
              (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
          have hgt : Real.sqrt s.level < (d₁ : ℝ) ∨ Real.sqrt s.level < (d₂ : ℝ) := by
            by_contra hnot
            rw [not_or] at hnot
            have h1 : (d₁ : ℝ) ≤ Real.sqrt s.level := not_lt.mp hnot.1
            have h2 : (d₂ : ℝ) ≤ Real.sqrt s.level := not_lt.mp hnot.2
            have hprod : (d : ℝ) ≤ Real.sqrt s.level * Real.sqrt s.level := by
              calc
                (d : ℝ) ≤ ((d₁ * d₂ : ℕ) : ℝ) := by exact_mod_cast hle_mul
                _ = (d₁ : ℝ) * (d₂ : ℝ) := by push_cast; rfl
                _ ≤ Real.sqrt s.level * Real.sqrt s.level :=
                    mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
            rw [Real.mul_self_sqrt (by linarith [s.one_le_level])] at hprod
            linarith
          rcases hgt with h1 | h2
          · rw [selbergOptW_eq_zero_of_not (fun h => (not_le.mpr h1) h.2), zero_mul]
          · rw [selbergOptW_eq_zero_of_not (fun h => (not_le.mpr h2) h.2), mul_zero]
        · rfl
      rw [hlam0, abs_zero, zero_mul]
    rw [hzero, add_zero]
  linarith

end OptimalSelbergSieve

/-! ### Comparison of `1 / G(z)` with `V(P)` -/

section ComparisonWithEulerProd

/-- Untruncated Selberg sum identity:
`∑_{d ∣ P} g(d) = (selbergEulerProd s)⁻¹`. -/
theorem sum_divisors_selbergTerms_eq_inv_eulerProd (s : BoundingSieve) :
    ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d = (selbergEulerProd s)⁻¹ := by
  rw [sum_divisors_selbergTerms_eq_prod s dvd_rfl, selbergEulerProd, Finset.prod_inv_distrib]

/-- Exact logarithmic identity for `selbergTerms`:
`∑_{d ∣ P} g(d) log d = (selbergEulerProd s)⁻¹ * ∑_{p ∣ P} ν(p) log p`. -/
theorem sum_divisors_selbergTerms_mul_log_eq (s : BoundingSieve) :
    ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d =
      (selbergEulerProd s)⁻¹ * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
  have hlog_eq : ∀ d ∈ s.prodPrimes.divisors,
      Real.log (d : ℝ) = ∑ p ∈ s.prodPrimes.primeFactors, (if p ∣ d then Real.log (p : ℝ) else 0) := by
    intro d hd
    have hd_sq : Squarefree d := s.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd)
    have hprod_d : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      have h1 : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd_sq).symm
      conv_lhs => rw [h1]
      push_cast
      rfl
    rw [hprod_d, Real.log_prod]
    · rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq]
      constructor
      · intro hp
        exact ⟨⟨hp.1, hp.2.1.trans (Nat.dvd_of_mem_divisors hd), s.prodPrimes_ne_zero⟩, hp.2.1⟩
      · rintro ⟨⟨hp_prime, _, _⟩, hpd⟩
        exact ⟨hp_prime, hpd, hd_sq.ne_zero⟩
    · intro p hp
      exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  calc
    ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d
        = ∑ d ∈ s.prodPrimes.divisors,
            ∑ p ∈ s.prodPrimes.primeFactors,
              (if p ∣ d then s.selbergTerms d * Real.log p else 0) := by
            refine Finset.sum_congr rfl fun d hd => ?_
            rw [hlog_eq d hd, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    _ = ∑ p ∈ s.prodPrimes.primeFactors,
          (∑ d ∈ s.prodPrimes.divisors.filter (p ∣ ·), s.selbergTerms d) * Real.log p := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_filter, Finset.sum_mul]
    _ = ∑ p ∈ s.prodPrimes.primeFactors,
          ((selbergEulerProd s)⁻¹ * s.nu p) * Real.log p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp_prime := Nat.prime_of_mem_primeFactors hp
          have hpP := Nat.dvd_of_mem_primeFactors hp
          let m := s.prodPrimes / p
          have hpm : p * m = s.prodPrimes := Nat.mul_div_cancel' hpP
          have hcop : p.Coprime m :=
            (Nat.squarefree_mul_iff.mp (hpm.symm ▸ s.prodPrimes_squarefree)).1
          have hbij :
              ∑ d ∈ s.prodPrimes.divisors.filter (p ∣ ·), s.selbergTerms d =
                s.selbergTerms p * ∑ r ∈ m.divisors, s.selbergTerms r := by
            rw [Finset.mul_sum]
            refine (Finset.sum_bij (fun r _ => p * r) ?_ ?_ ?_ ?_).symm
            · intro r hr
              have hrm := Nat.dvd_of_mem_divisors hr
              exact Finset.mem_filter.mpr
                ⟨Nat.mem_divisors.mpr ⟨hpm ▸ Nat.mul_dvd_mul_left p hrm, s.prodPrimes_ne_zero⟩,
                  dvd_mul_right p r⟩
            · intro r₁ _ r₂ _ heq
              exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq
            · intro d hd
              have hd' := Finset.mem_filter.mp hd
              have hdpP := Nat.dvd_of_mem_divisors hd'.1
              let r := d / p
              have hdr : p * r = d := Nat.mul_div_cancel' hd'.2
              have hrm : r ∣ m := by
                have : p * r ∣ p * m := hdr.symm ▸ hpm.symm ▸ hdpP
                exact Nat.dvd_of_mul_dvd_mul_left hp_prime.pos this
              have hm_nz : m ≠ 0 := by
                intro hm0; rw [hm0, mul_zero] at hpm; exact s.prodPrimes_ne_zero hpm.symm
              exact ⟨r, Nat.mem_divisors.mpr ⟨hrm, hm_nz⟩, hdr⟩
            · intro r hr
              have hrm := Nat.dvd_of_mem_divisors hr
              exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime
                (hcop.coprime_dvd_right hrm)).symm
          have hmP : m ∣ s.prodPrimes := Nat.div_dvd_of_dvd hpP
          have hsum_m : ∑ r ∈ m.divisors, s.selbergTerms r =
              ∏ q ∈ m.primeFactors, (1 - s.nu q)⁻¹ :=
            sum_divisors_selbergTerms_eq_prod s hmP
          have hm_pf : s.prodPrimes.primeFactors = insert p m.primeFactors := by
            rw [← hpm, hcop.primeFactors_mul, hp_prime.primeFactors]
            ext q; simp [Finset.mem_insert]
          have hp_not : p ∉ m.primeFactors := by
            intro hmem
            have hpm_dvd := Nat.dvd_of_mem_primeFactors hmem
            exact hp_prime.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd hpm_dvd dvd_rfl))
          have hinv_prod : (selbergEulerProd s)⁻¹ =
              (1 - s.nu p)⁻¹ * ∏ q ∈ m.primeFactors, (1 - s.nu q)⁻¹ := by
            rw [selbergEulerProd, hm_pf, Finset.prod_insert hp_not, mul_inv, Finset.prod_inv_distrib]
          rw [hbij, hsum_m, s.selbergTerms_apply p, hp_prime.primeFactors, Finset.prod_singleton,
            hinv_prod]
          ring
    _ = (selbergEulerProd s)⁻¹ * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring

/-- Comparison between `(selbergG s z)⁻¹` and `selbergEulerProd s` by first-moment
truncation: whenever `1 < z` and `∑_{p ∣ P} ν(p) log p < log z`,
`(selbergG s z)⁻¹ ≤ (1 - (∑_{p ∣ P} ν(p) log p) / log z)⁻¹ * selbergEulerProd s`. -/
theorem inv_selbergG_le_eulerProd_of_sum_log {s : BoundingSieve} {z : ℝ} (hz : 1 < z)
    (hsum_lt : ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p < Real.log z) :
    (selbergG s z)⁻¹ ≤
      (1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z)⁻¹ *
        selbergEulerProd s := by
  have hz_ge1 : 1 ≤ z := hz.le
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz
  have hV_pos : 0 < selbergEulerProd s := selbergEulerProd_pos s
  have hG_pos : 0 < selbergG s z := selbergG_pos hz_ge1
  have htail_le :
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z), s.selbergTerms d ≤
        (Real.log z)⁻¹ * ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d := by
    calc
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z), s.selbergTerms d
          ≤ ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
              (Real.log z)⁻¹ * (s.selbergTerms d * Real.log d) := by
              refine Finset.sum_le_sum fun d hd => ?_
              have hd' := Finset.mem_filter.mp hd
              have hz_lt_d : z < (d : ℝ) := lt_of_not_ge hd'.2
              have hlog_le : Real.log z ≤ Real.log d := Real.log_le_log (by linarith) hz_lt_d.le
              have hg_nn : 0 ≤ s.selbergTerms d := selbergTerms_nonneg_of_mem hd'.1
              have h1 : 1 ≤ (Real.log z)⁻¹ * Real.log d := by
                rw [inv_mul_eq_div, one_le_div hlogz_pos]
                exact hlog_le
              calc
                s.selbergTerms d = s.selbergTerms d * 1 := (mul_one _).symm
                _ ≤ s.selbergTerms d * ((Real.log z)⁻¹ * Real.log d) :=
                    mul_le_mul_of_nonneg_left h1 hg_nn
                _ = (Real.log z)⁻¹ * (s.selbergTerms d * Real.log d) := by ring
      _ ≤ ∑ d ∈ s.prodPrimes.divisors, (Real.log z)⁻¹ * (s.selbergTerms d * Real.log d) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun d hd _ => ?_)
          have hd_pos : 1 ≤ d :=
            Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hd))
          have hlogd_nn : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd_pos)
          exact mul_nonneg (inv_nonneg.mpr hlogz_pos.le)
            (mul_nonneg (selbergTerms_nonneg_of_mem hd) hlogd_nn)
      _ = (Real.log z)⁻¹ * ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d :=
          (Finset.mul_sum _ _ _).symm
  have hsplit :
      selbergG s z +
        ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z), s.selbergTerms d =
        (selbergEulerProd s)⁻¹ := by
    unfold selbergG
    rw [Finset.sum_filter_add_sum_filter_not, sum_divisors_selbergTerms_eq_inv_eulerProd]
  have hG_ge :
      (1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z) *
          (selbergEulerProd s)⁻¹ ≤ selbergG s z := by
    rw [sum_divisors_selbergTerms_mul_log_eq] at htail_le
    have h_alg :
        (1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z) *
          (selbergEulerProd s)⁻¹ =
        (selbergEulerProd s)⁻¹ -
          (Real.log z)⁻¹ * ((selbergEulerProd s)⁻¹ *
            ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) := by ring
    rw [h_alg]
    linarith
  have hfac_pos :
      0 < 1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z := by
    rw [sub_pos, div_lt_one hlogz_pos]
    exact hsum_lt
  rw [inv_le_iff_one_le_mul₀ hG_pos]
  calc
    1 = ((1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z)⁻¹ *
          selbergEulerProd s) *
        ((1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z) *
          (selbergEulerProd s)⁻¹) := by
        field_simp [hfac_pos.ne', hV_pos.ne']
    _ ≤ ((1 - (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log z)⁻¹ *
          selbergEulerProd s) * selbergG s z := by
        refine mul_le_mul_of_nonneg_left hG_ge (by positivity)

/-- Rankin's trick lower bound for `selbergG`: for any exponent `c > 0`,
`selbergG s z ≥ (1 - z ^ (-c) * selbergEulerProd s * ∏_{p ∣ P} (1 + g(p) * p ^ c)) * (selbergEulerProd s)⁻¹`
whenever the product tail is smaller than `1`. Here we package the simpler positivity identity
for `∏_{p ∣ P} (1 + g(p) * p ^ c) = ∑_{d ∣ P} g(d) * d ^ c`. -/
theorem sum_divisors_selbergTerms_mul_rpow_eq (s : BoundingSieve) (c : ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * (d : ℝ) ^ c =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.selbergTerms p * (p : ℝ) ^ c) := by
  have hprod : ∀ P : ℕ, Squarefree P →
      ∑ d ∈ P.divisors, s.selbergTerms d * (d : ℝ) ^ c =
        ∏ p ∈ P.primeFactors, (1 + s.selbergTerms p * (p : ℝ) ^ c) := by
    intro P
    induction P using Nat.strong_induction_on with | ind P ih =>
    intro hP
    by_cases hP1 : P = 1
    · subst hP1
      simp [s.selbergTerms_isMultiplicative.1]
    · have hP_pos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
      let p := P.minFac
      have hp : p.Prime := Nat.minFac_prime hP1
      have hpP : p ∣ P := Nat.minFac_dvd P
      let m := P / p
      have hpm : p * m = P := Nat.mul_div_cancel' hpP
      have hm_sq : Squarefree m := hP.squarefree_of_dvd (Nat.div_dvd_of_dvd hpP)
      have hm_lt : m < P := Nat.div_lt_self hP_pos hp.one_lt
      have hcop : p.Coprime m := (Nat.squarefree_mul_iff.mp (hpm.symm ▸ hP)).1
      have hpf : P.primeFactors = insert p m.primeFactors := by
        rw [← hpm, hcop.primeFactors_mul, hp.primeFactors]
        ext q; simp [Finset.mem_insert]
      have hp_not : p ∉ m.primeFactors := by
        intro hmem
        exact hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem) dvd_rfl))
      have hsplit_div :
          ∑ d ∈ P.divisors, s.selbergTerms d * (d : ℝ) ^ c =
            (1 + s.selbergTerms p * (p : ℝ) ^ c) *
              ∑ r ∈ m.divisors, s.selbergTerms r * (r : ℝ) ^ c := by
        have hp_not_m : ¬ p ∣ m := fun h =>
          hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd h dvd_rfl))
        have hdisj : Disjoint m.divisors (m.divisors.image (p * ·)) := by
          rw [Finset.disjoint_left]
          intro d hd1 hd2
          rcases Finset.mem_image.mp hd2 with ⟨r, _, rfl⟩
          exact hp_not_m ((dvd_mul_right p r).trans (Nat.dvd_of_mem_divisors hd1))
        have hunion : P.divisors = m.divisors ∪ m.divisors.image (p * ·) := by
          ext d
          simp only [Nat.mem_divisors, ne_eq, hP.ne_zero, hm_sq.ne_zero, not_false_eq_true,
            and_true, Finset.mem_union, Finset.mem_image]
          constructor
          · intro hdP
            by_cases hpd : p ∣ d
            · right
              refine ⟨d / p, ?_, Nat.mul_div_cancel' hpd⟩
              have : p * (d / p) ∣ p * m := by rwa [Nat.mul_div_cancel' hpd, hpm]
              exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
            · left
              have hcop_pd : p.Coprime d := hp.coprime_iff_not_dvd.mpr hpd
              rw [← hpm] at hdP
              exact hcop_pd.symm.dvd_of_dvd_mul_left hdP
          · rintro (hdm | ⟨r, hrm, rfl⟩)
            · exact hdm.trans (hpm ▸ dvd_mul_left m p)
            · exact hpm ▸ Nat.mul_dvd_mul_left p hrm
        rw [hunion, Finset.sum_union hdisj]
        have hinj : Set.InjOn (fun r => p * r) (m.divisors : Set ℕ) :=
          fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq
        rw [Finset.sum_image (fun r₁ _ r₂ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq)]
        have hterm :
            ∑ r ∈ m.divisors, s.selbergTerms (p * r) * ((p * r : ℕ) : ℝ) ^ c =
              (s.selbergTerms p * (p : ℝ) ^ c) *
                ∑ r ∈ m.divisors, s.selbergTerms r * (r : ℝ) ^ c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrm := Nat.dvd_of_mem_divisors hr
          have hcop_pr : p.Coprime r := hcop.coprime_dvd_right hrm
          rw [s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop_pr, Nat.cast_mul,
            Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
          ring
        rw [hterm]
        ring
      rw [hsplit_div, ih m hm_lt hm_sq, hpf, Finset.prod_insert hp_not]
  exact hprod s.prodPrimes s.prodPrimes_squarefree

/-- Monotonicity of `selbergG` when restricting `prodPrimes` from `s` to a divisor `s'`:
if `s'.prodPrimes ∣ s.prodPrimes` and `s'` shares `nu`, then `selbergG s' w ≤ selbergG s z`
for `w ≤ z`. -/
theorem selbergG_le_of_prodPrimes_dvd {s' s : BoundingSieve} {w z : ℝ}
    (hP : s'.prodPrimes ∣ s.prodPrimes) (hnu : s'.nu = s.nu) (hwz : w ≤ z) :
    selbergG s' w ≤ selbergG s z := by
  have hterms : ∀ d, s'.selbergTerms d = s.selbergTerms d := by
    intro d
    simp [BoundingSieve.selbergTerms, hnu]
  unfold selbergG
  simp_rw [hterms]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun d hd _ => selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hd).1)
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  have hdP : d ∣ s.prodPrimes := (Nat.dvd_of_mem_divisors hd'.1).trans hP
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hdP, s.prodPrimes_ne_zero⟩, hd'.2.trans hwz⟩

/-- `selbergPrimeFinset` is monotone in `z`. -/
theorem selbergPrimeFinset_mono {w z : ℝ} (hwz : w ≤ z) :
    selbergPrimeFinset w ⊆ selbergPrimeFinset z := by
  intro p hp
  have hp' := mem_selbergPrimeFinset_iff.mp hp
  exact mem_selbergPrimeFinset_iff.mpr ⟨hp'.1, hp'.2.trans hwz⟩

/-- `selbergPrimeProd w` divides `selbergPrimeProd z` whenever `w ≤ z`. -/
theorem selbergPrimeProd_dvd_selbergPrimeProd {w z : ℝ} (hwz : w ≤ z) :
    selbergPrimeProd w ∣ selbergPrimeProd z := by
  by_cases hw0 : w < 0
  · have hfl : ⌊w⌋₊ = 0 := Nat.floor_of_nonpos hw0.le
    simp [selbergPrimeProd, hfl]
  · have hw : 0 ≤ w := not_lt.mp hw0
    exact primorial_dvd_primorial (Nat.floor_mono hwz)

private lemma neg_log_one_sub_le_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    -Real.log (1 - u) ≤ 2 * u := by
  have hpos : 0 < 1 - u := by linarith
  have hmul : 1 ≤ (1 - u) * (1 + 2 * u) := by
    have hdiff : (1 - u) * (1 + 2 * u) - 1 = u * (1 - 2 * u) := by ring
    have hnn : 0 ≤ u * (1 - 2 * u) := mul_nonneg hu0 (by linarith)
    linarith
  have hinv_le : (1 - u)⁻¹ ≤ 1 + 2 * u := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  have hexp_le : (1 - u)⁻¹ ≤ Real.exp (2 * u) :=
    hinv_le.trans (by linarith [Real.add_one_le_exp (2 * u)])
  rw [← Real.log_inv]
  exact (Real.log_le_log (inv_pos.mpr hpos) hexp_le).trans_eq (Real.log_exp _)

/-- General `κ`-dimensional comparison `1 / G(z) ≤ C * V(z)`:
for any `κ ≥ 1` and `0 < c₀ ≤ 1`, there exists a constant `C > 0` (depending only on `κ, c₀`)
such that for every `z ≥ 2` and every `BoundingSieve` with `prodPrimes = selbergPrimeProd z`,
`s.nu p ≤ κ / p`, and `c₀ ≤ 1 - s.nu p` on primes `p ≤ z`,
`(selbergG s z)⁻¹ ≤ C * selbergEulerProd s`. -/
theorem inv_selbergG_le_mul_eulerProd_of_le_div {κ c₀ : ℝ}
    (hκ : 1 ≤ κ) (hc₀_pos : 0 < c₀) (hc₀_le : c₀ ≤ 1) :
    ∃ C > 0, ∀ (s : BoundingSieve) (z : ℝ), 2 ≤ z → s.prodPrimes = selbergPrimeProd z →
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → s.nu p ≤ κ / (p : ℝ)) →
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → c₀ ≤ 1 - s.nu p) →
        (selbergG s z)⁻¹ ≤ C * selbergEulerProd s := by
  let M₀ : ℝ := max (max 1 (Real.log (2 * κ + 2))) mertensOneBound
  have hM₀_ge1 : 1 ≤ M₀ := (le_max_left 1 _).trans (le_max_left _ _)
  have hM₀_log : Real.log (2 * κ + 2) ≤ M₀ := (le_max_right 1 _).trans (le_max_left _ _)
  have hM₀_mert : mertensOneBound ≤ M₀ := le_max_right _ _
  let L₀ : ℝ := (4 * κ + 4) * M₀
  let Z₀ : ℝ := Real.exp L₀
  let C_sm : ℝ := (c₀⁻¹) ^ ⌊Z₀⌋₊
  let C_lg : ℝ := 2 * Real.exp (2 * κ * (Real.log (4 * κ + 4) + (4 * mertensOneBound) / Real.log 2))
  let C : ℝ := max C_sm C_lg
  have hC_sm_pos : 0 < C_sm := pow_pos (inv_pos.mpr hc₀_pos) _
  have hC_lg_pos : 0 < C_lg := by positivity
  have hC_pos : 0 < C := lt_of_lt_of_le hC_lg_pos (le_max_right _ _)
  refine ⟨C, hC_pos, fun s z hz hP hν_le hc₀_bd => ?_⟩
  by_cases hz_le : z ≤ Z₀
  · have hG_ge1 : 1 ≤ selbergG s z := selbergG_ge_one (by linarith)
    have hinvG_le1 : (selbergG s z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hG_ge1
    have hcard_le : s.prodPrimes.primeFactors.card ≤ ⌊Z₀⌋₊ := by
      rw [hP, primeFactors_selbergPrimeProd]
      have hsub : selbergPrimeFinset z ⊆ Finset.Icc 1 ⌊Z₀⌋₊ := by
        intro p hp
        have hp' := mem_selbergPrimeFinset_iff.mp hp
        exact Finset.mem_Icc.mpr ⟨hp'.1.one_le, Nat.le_floor (hp'.2.trans hz_le)⟩
      calc
        (selbergPrimeFinset z).card ≤ (Finset.Icc 1 ⌊Z₀⌋₊).card := Finset.card_le_card hsub
        _ = ⌊Z₀⌋₊ := by simp
    have hV_ge : c₀ ^ ⌊Z₀⌋₊ ≤ selbergEulerProd s := by
      unfold selbergEulerProd
      have h1 : c₀ ^ ⌊Z₀⌋₊ ≤ c₀ ^ s.prodPrimes.primeFactors.card :=
        pow_le_pow_of_le_one hc₀_pos.le hc₀_le hcard_le
      have h2 : c₀ ^ s.prodPrimes.primeFactors.card ≤
          ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
        rw [← Finset.prod_const]
        refine Finset.prod_le_prod₀ (fun _ _ => hc₀_pos.le) (fun p hp => ?_)
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp_le : (p : ℝ) ≤ z := by
          rw [hP, primeFactors_selbergPrimeProd] at hp
          exact (mem_selbergPrimeFinset_iff.mp hp).2
        exact hc₀_bd p hp_prime hp_le
      exact h1.trans h2
    have hprod_ge1 : 1 ≤ C_sm * selbergEulerProd s := by
      calc
        (1 : ℝ) = (c₀⁻¹) ^ ⌊Z₀⌋₊ * c₀ ^ ⌊Z₀⌋₊ := by
          rw [← mul_pow, inv_mul_cancel₀ hc₀_pos.ne', one_pow]
        _ ≤ C_sm * selbergEulerProd s := by
          dsimp [C_sm]
          exact mul_le_mul_of_nonneg_left hV_ge (pow_nonneg (inv_pos.mpr hc₀_pos).le _)
    have hC_ge : C_sm ≤ C := le_max_left _ _
    have hV_nn : 0 ≤ selbergEulerProd s := (selbergEulerProd_pos s).le
    calc
      (selbergG s z)⁻¹ ≤ 1 := hinvG_le1
      _ ≤ C_sm * selbergEulerProd s := hprod_ge1
      _ ≤ C * selbergEulerProd s := mul_le_mul_of_nonneg_right hC_ge hV_nn
  · have hZ₀_lt : Z₀ < z := lt_of_not_ge hz_le
    have hlogz_gt : L₀ < Real.log z := by
      calc
        L₀ = Real.log Z₀ := (Real.log_exp L₀).symm
        _ < Real.log z := Real.log_lt_log (Real.exp_pos L₀) hZ₀_lt
    have hlogz_pos : 0 < Real.log z := by
      have : 0 < L₀ := mul_pos (by linarith) (lt_of_lt_of_le zero_lt_one hM₀_ge1)
      linarith
    let w : ℝ := Real.exp (Real.log z / (4 * κ + 4))
    have hlogw : Real.log w = Real.log z / (4 * κ + 4) := Real.log_exp _
    have hM₀_lt_logw : M₀ < Real.log w := by
      rw [hlogw, lt_div_iff₀ (by linarith)]
      linarith
    have hw_ge_2k2 : 2 * κ + 2 ≤ w := by
      have h1 : Real.log (2 * κ + 2) ≤ Real.log w := hM₀_log.trans hM₀_lt_logw.le
      calc
        2 * κ + 2 = Real.exp (Real.log (2 * κ + 2)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (Real.log w) := Real.exp_le_exp.mpr h1
        _ = w := Real.exp_log (Real.exp_pos _)
    have hw_ge4 : 4 ≤ w := by linarith
    have hw_ge2 : 2 ≤ w := by linarith
    have hw_le_z : w ≤ z := by
      have h1 : Real.log w ≤ Real.log z := by
        rw [hlogw]
        exact div_le_self hlogz_pos.le (by linarith)
      calc
        w = Real.exp (Real.log w) := (Real.exp_log (Real.exp_pos _)).symm
        _ ≤ Real.exp (Real.log z) := Real.exp_le_exp.mpr h1
        _ = z := Real.exp_log (by linarith)
    have hlogw_pos : 0 < Real.log w := Real.log_pos (by linarith)
    let s' : BoundingSieve :=
      { support := s.support
        prodPrimes := selbergPrimeProd w
        prodPrimes_squarefree := selbergPrimeProd_squarefree w
        weights := s.weights
        weights_nonneg := s.weights_nonneg
        totalMass := s.totalMass
        nu := s.nu
        nu_mult := s.nu_mult
        nu_pos_of_prime := fun p hp hpP =>
          s.nu_pos_of_prime p hp (hpP.trans (hP ▸ selbergPrimeProd_dvd_selbergPrimeProd hw_le_z))
        nu_lt_one_of_prime := fun p hp hpP =>
          s.nu_lt_one_of_prime p hp (hpP.trans (hP ▸ selbergPrimeProd_dvd_selbergPrimeProd hw_le_z)) }
    have hs'_dvd : s'.prodPrimes ∣ s.prodPrimes := by
      change selbergPrimeProd w ∣ s.prodPrimes
      rw [hP]
      exact selbergPrimeProd_dvd_selbergPrimeProd hw_le_z
    have hG_le : selbergG s' z ≤ selbergG s z :=
      selbergG_le_of_prodPrimes_dvd hs'_dvd rfl le_rfl
    have hG'_pos : 0 < selbergG s' z := selbergG_pos (by linarith)
    have hsum_log_lt :
        ∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Real.log p < Real.log z := by
      have hs'_pf : s'.prodPrimes.primeFactors = Nat.primesLE ⌊w⌋₊ := by
        change (selbergPrimeProd w).primeFactors = _
        rw [primeFactors_selbergPrimeProd, selbergPrimeFinset]
      rw [hs'_pf]
      have hterm_le : ∀ p ∈ Nat.primesLE ⌊w⌋₊, s.nu p * Real.log p ≤ κ * (Real.log p / p) := by
        intro p hp
        have hp_prime := Nat.prime_of_mem_primesLE hp
        have hpw : (p : ℝ) ≤ w :=
          (mem_selbergPrimeFinset_iff.mp (by simpa [selbergPrimeFinset] using hp)).2
        have hpz : (p : ℝ) ≤ z := hpw.trans hw_le_z
        have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
        calc
          s.nu p * Real.log p ≤ (κ / (p : ℝ)) * Real.log p :=
              mul_le_mul_of_nonneg_right (hν_le p hp_prime hpz) hlogp_nn
          _ = κ * (Real.log p / p) := by ring
      have hmert1 := abs_mertens_one_sub_log_le (by linarith : 1 ≤ w)
      have hsum_mert1 : ∑ p ∈ Nat.primesLE ⌊w⌋₊, Real.log p / p ≤ 2 * Real.log w := by
        have h1 := (abs_le.mp hmert1).2
        have h2 : mertensOneBound ≤ Real.log w := hM₀_mert.trans hM₀_lt_logw.le
        linarith
      calc
        ∑ p ∈ Nat.primesLE ⌊w⌋₊, s'.nu p * Real.log p
            ≤ ∑ p ∈ Nat.primesLE ⌊w⌋₊, κ * (Real.log p / p) := Finset.sum_le_sum hterm_le
        _ = κ * ∑ p ∈ Nat.primesLE ⌊w⌋₊, Real.log p / p := (Finset.mul_sum _ _ _).symm
        _ ≤ κ * (2 * Real.log w) := mul_le_mul_of_nonneg_left hsum_mert1 (by linarith)
        _ = (2 * κ / (4 * κ + 4)) * Real.log z := by rw [hlogw]; ring
        _ ≤ (1 / 2) * Real.log z := by
              refine mul_le_mul_of_nonneg_right ?_ hlogz_pos.le
              rw [div_le_div_iff₀ (by linarith) (by norm_num)]
              linarith
        _ < Real.log z := by linarith
    have hsum_half :
        1 / 2 ≤ 1 - (∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Real.log p) / Real.log z := by
      have h1 : (∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Real.log p) / Real.log z ≤ 1 / 2 := by
        rw [div_le_iff₀ hlogz_pos]
        -- Repeat the 2κ/(4κ+4) ≤ 1/2 bound directly
        have hs'_pf : s'.prodPrimes.primeFactors = Nat.primesLE ⌊w⌋₊ := by
          change (selbergPrimeProd w).primeFactors = _
          rw [primeFactors_selbergPrimeProd, selbergPrimeFinset]
        rw [hs'_pf]
        have hmert1 := abs_mertens_one_sub_log_le (by linarith : 1 ≤ w)
        have hsum_mert1 : ∑ p ∈ Nat.primesLE ⌊w⌋₊, Real.log p / p ≤ 2 * Real.log w := by
          linarith [(abs_le.mp hmert1).2, hM₀_mert.trans hM₀_lt_logw.le]
        have hsum_le : ∑ p ∈ Nat.primesLE ⌊w⌋₊, s'.nu p * Real.log p ≤ κ * (2 * Real.log w) := by
          calc
            ∑ p ∈ Nat.primesLE ⌊w⌋₊, s'.nu p * Real.log p
                ≤ ∑ p ∈ Nat.primesLE ⌊w⌋₊, κ * (Real.log p / p) := by
                    refine Finset.sum_le_sum fun p hp => ?_
                    have hp_prime := Nat.prime_of_mem_primesLE hp
                    have hpw : (p : ℝ) ≤ w :=
                      (mem_selbergPrimeFinset_iff.mp (by simpa [selbergPrimeFinset] using hp)).2
                    have hlogp_nn : 0 ≤ Real.log p :=
                      Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
                    calc
                      s.nu p * Real.log p ≤ (κ / (p : ℝ)) * Real.log p :=
                          mul_le_mul_of_nonneg_right (hν_le p hp_prime (hpw.trans hw_le_z)) hlogp_nn
                      _ = κ * (Real.log p / p) := by ring
            _ = κ * ∑ p ∈ Nat.primesLE ⌊w⌋₊, Real.log p / p := (Finset.mul_sum _ _ _).symm
            _ ≤ κ * (2 * Real.log w) := mul_le_mul_of_nonneg_left hsum_mert1 (by linarith)
        have h2k : κ * (2 * Real.log w) ≤ (1 / 2) * Real.log z := by
          have : κ * (2 * Real.log w) = (2 * κ / (4 * κ + 4)) * Real.log z := by
            rw [hlogw]; ring
          rw [this]
          refine mul_le_mul_of_nonneg_right ?_ hlogz_pos.le
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
        exact hsum_le.trans h2k
      linarith
    have hinv_s' : (selbergG s' z)⁻¹ ≤ 2 * selbergEulerProd s' := by
      have h1 := inv_selbergG_le_eulerProd_of_sum_log (s := s') (by linarith : 1 < z) hsum_log_lt
      have hfac :
          (1 - (∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Real.log p) / Real.log z)⁻¹ ≤ 2 := by
        calc
          (1 - (∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Real.log p) / Real.log z)⁻¹
              ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hsum_half
          _ = 2 := by norm_num
      exact h1.trans (mul_le_mul_of_nonneg_right hfac (selbergEulerProd_pos s').le)
    have hinvG_le_s' : (selbergG s z)⁻¹ ≤ 2 * selbergEulerProd s' :=
      (inv_anti₀ hG'_pos hG_le).trans hinv_s'
    -- Compare `selbergEulerProd s'` and `selbergEulerProd s`.
    let D := selbergPrimeFinset z \ selbergPrimeFinset w
    have hsub_pf : selbergPrimeFinset w ⊆ selbergPrimeFinset z := selbergPrimeFinset_mono hw_le_z
    have hsplit_V : selbergEulerProd s = selbergEulerProd s' * ∏ p ∈ D, (1 - s.nu p) := by
      unfold selbergEulerProd
      have hp1 : s.prodPrimes.primeFactors = selbergPrimeFinset z := by
        rw [hP, primeFactors_selbergPrimeProd]
      have hp2 : s'.prodPrimes.primeFactors = selbergPrimeFinset w := by
        change (selbergPrimeProd w).primeFactors = _
        rw [primeFactors_selbergPrimeProd]
      rw [hp1, hp2]
      have hunion : selbergPrimeFinset w ∪ D = selbergPrimeFinset z := Finset.union_sdiff_of_subset hsub_pf
      have hdisj : Disjoint (selbergPrimeFinset w) D := Finset.disjoint_sdiff
      rw [← hunion, Finset.prod_union hdisj]
    have hD_pos : ∀ p ∈ D, 0 < 1 - s.nu p := by
      intro p hp
      have hpz : p ∈ selbergPrimeFinset z := (Finset.mem_sdiff.mp hp).1
      exact one_sub_nu_pos_of_mem_primeFactors s (by rw [hP, primeFactors_selbergPrimeProd]; exact hpz)
    have hlog_D :
        Real.log ((∏ p ∈ D, (1 - s.nu p))⁻¹) ≤
          2 * κ * (Real.log (4 * κ + 4) + (4 * mertensOneBound) / Real.log 2) := by
      rw [Real.log_inv, Real.log_prod (fun p hp => (hD_pos p hp).ne'), ← Finset.sum_neg_distrib]
      have hsum_D_le : ∑ p ∈ D, -Real.log (1 - s.nu p) ≤
          2 * κ * ∑ p ∈ D, (p : ℝ)⁻¹ := by
        calc
          ∑ p ∈ D, -Real.log (1 - s.nu p)
              ≤ ∑ p ∈ D, 2 * κ * (p : ℝ)⁻¹ := by
                refine Finset.sum_le_sum fun p hp => ?_
                have hps := Finset.mem_sdiff.mp hp
                have hpz := mem_selbergPrimeFinset_iff.mp hps.1
                have hpw_gt : w < (p : ℝ) := by
                  by_contra hle
                  exact hps.2 (mem_selbergPrimeFinset_iff.mpr ⟨hpz.1, not_lt.mp hle⟩)
                have hp_gt_2k : 2 * κ < (p : ℝ) := by linarith
                have hνp_nn : 0 ≤ s.nu p :=
                  (s.nu_pos_of_prime p hpz.1 (hP ▸ (prime_dvd_selbergPrimeProd_iff hpz.1).mpr hpz.2)).le
                have hνp_le : s.nu p ≤ κ / (p : ℝ) := hν_le p hpz.1 hpz.2
                have hkp_le : κ / (p : ℝ) ≤ 1 / 2 := by
                  rw [div_le_iff₀ (Nat.cast_pos.mpr hpz.1.pos)]
                  linarith
                have hneg := neg_log_one_sub_le_two_mul hνp_nn (hνp_le.trans hkp_le)
                calc
                  -Real.log (1 - s.nu p) ≤ 2 * s.nu p := hneg
                  _ ≤ 2 * (κ / (p : ℝ)) := by linarith
                  _ = 2 * κ * (p : ℝ)⁻¹ := by ring
          _ = 2 * κ * ∑ p ∈ D, (p : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      have hsum_inv_diff :
          ∑ p ∈ D, (p : ℝ)⁻¹ ≤ Real.log (4 * κ + 4) + (4 * mertensOneBound) / Real.log 2 := by
        have hsplit_inv :
            ∑ p ∈ selbergPrimeFinset w, (p : ℝ)⁻¹ + ∑ p ∈ D, (p : ℝ)⁻¹ =
              ∑ p ∈ selbergPrimeFinset z, (p : ℝ)⁻¹ := by
          have hunion : selbergPrimeFinset w ∪ D = selbergPrimeFinset z :=
            Finset.union_sdiff_of_subset hsub_pf
          have hdisj : Disjoint (selbergPrimeFinset w) D := Finset.disjoint_sdiff
          rw [← hunion, Finset.sum_union hdisj]
        have hmert_z := abs_mertens_two_sub_le hz
        have hmert_w := abs_mertens_two_sub_le hw_ge2
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
        have hlogz_ge2 : Real.log 2 ≤ Real.log z := Real.log_le_log zero_lt_two hz
        have hlogw_ge2 : Real.log 2 ≤ Real.log w := Real.log_le_log zero_lt_two hw_ge2
        have hm1_nn : 0 ≤ 2 * mertensOneBound := by linarith [mertensOneBound_pos]
        have hz_err : (2 * mertensOneBound) / Real.log z ≤ (2 * mertensOneBound) / Real.log 2 := by
          gcongr
        have hw_err : (2 * mertensOneBound) / Real.log w ≤ (2 * mertensOneBound) / Real.log 2 := by
          gcongr
        have hz_up : ∑ p ∈ selbergPrimeFinset z, (p : ℝ)⁻¹ ≤
            Real.log (Real.log z) + meisselMertensConstant + (2 * mertensOneBound) / Real.log 2 := by
          change ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ ≤ _
          linarith [(abs_le.mp hmert_z).2]
        have hw_lo : Real.log (Real.log w) + meisselMertensConstant -
            (2 * mertensOneBound) / Real.log 2 ≤ ∑ p ∈ selbergPrimeFinset w, (p : ℝ)⁻¹ := by
          change _ ≤ ∑ p ∈ Nat.primesLE ⌊w⌋₊, (p : ℝ)⁻¹
          linarith [(abs_le.mp hmert_w).1]
        have hlog_ratio : Real.log (Real.log z) - Real.log (Real.log w) = Real.log (4 * κ + 4) := by
          rw [← Real.log_div hlogz_pos.ne' hlogw_pos.ne', hlogw]
          congr 1
          field_simp [hlogz_pos.ne']
        have herr_sum :
            (2 * mertensOneBound) / Real.log 2 + (2 * mertensOneBound) / Real.log 2 =
              (4 * mertensOneBound) / Real.log 2 := by ring
        linarith [hlog_ratio, herr_sum]
      exact hsum_D_le.trans (mul_le_mul_of_nonneg_left hsum_inv_diff (by linarith))
    have hprod_D_pos : 0 < ∏ p ∈ D, (1 - s.nu p) := Finset.prod_pos hD_pos
    have hinv_D_le : (∏ p ∈ D, (1 - s.nu p))⁻¹ ≤
        Real.exp (2 * κ * (Real.log (4 * κ + 4) + (4 * mertensOneBound) / Real.log 2)) := by
      rw [← Real.exp_log (inv_pos.mpr hprod_D_pos)]
      exact Real.exp_le_exp.mpr hlog_D
    have hs'_eq : selbergEulerProd s' = selbergEulerProd s * (∏ p ∈ D, (1 - s.nu p))⁻¹ := by
      rw [hsplit_V]
      field_simp [hprod_D_pos.ne']
    have hC_ge : C_lg ≤ C := le_max_right _ _
    have hV_nn : 0 ≤ selbergEulerProd s := (selbergEulerProd_pos s).le
    calc
      (selbergG s z)⁻¹ ≤ 2 * selbergEulerProd s' := hinvG_le_s'
      _ = 2 * (selbergEulerProd s * (∏ p ∈ D, (1 - s.nu p))⁻¹) := by rw [hs'_eq]
      _ ≤ 2 * (selbergEulerProd s *
            Real.exp (2 * κ * (Real.log (4 * κ + 4) + (4 * mertensOneBound) / Real.log 2))) := by
            gcongr
      _ = C_lg * selbergEulerProd s := by dsimp [C_lg]; ring
      _ ≤ C * selbergEulerProd s := mul_le_mul_of_nonneg_right hC_ge hV_nn

end ComparisonWithEulerProd

/-! ### Concrete Applications of the Selberg Sieve -/

section SelbergApplications

/-! #### 1. Primes in Intervals: `π(x + y) - π(x) ≤ (2 + o(1)) y / log y` -/

private lemma sum_image_inv_le_sum {α : Type*} [DecidableEq α] (A : Finset α) (g : α → ℕ) :
    ∑ k ∈ A.image g, (k : ℝ)⁻¹ ≤ ∑ x ∈ A, (g x : ℝ)⁻¹ := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hmem : g a ∈ s.image g
    · rw [Finset.insert_eq_of_mem hmem]
      exact ih.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _)))
    · rw [Finset.sum_insert hmem]
      exact add_le_add_right ih ((g a : ℝ)⁻¹)

private lemma geom_sum_inv_prime_le (p : ℕ) (hp : p.Prime) (M : ℕ) :
    ∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsub : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hmul : (∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e) * (1 - (p : ℝ)⁻¹) =
      1 - ((p : ℝ)⁻¹) ^ (M + 1) := by
    have h := geom_sum_mul_neg ((p : ℝ)⁻¹) (M + 1)
    linarith [h]
  conv_rhs => rw [inv_eq_one_div]
  rw [le_div_iff₀ hsub, hmul]
  linarith [show (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ (M + 1) by positivity]

private lemma sum_Icc_primeFactors_subset_le (M : ℕ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ s), (k : ℝ)⁻¹ ≤
        ∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹ := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    have hflt : (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ ∅) ⊆ {1} := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk'.1).1
      have hemp : k.primeFactors = ∅ := Finset.subset_empty.mp hk'.2
      have hk_eq : k = 1 := by
        by_contra hne
        have ⟨p, hp⟩ := Nat.exists_prime_and_dvd hne
        have hmem : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, by omega⟩
        rw [hemp] at hmem
        exact Finset.notMem_empty p hmem
      exact Finset.mem_singleton.mpr hk_eq
    calc
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ ∅), (k : ℝ)⁻¹
          ≤ ∑ k ∈ ({1} : Finset ℕ), (k : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hflt (fun _ _ _ => by positivity)
      _ = 1 := by simp
      _ = ∏ p ∈ (∅ : Finset ℕ), (1 - (p : ℝ)⁻¹)⁻¹ := by simp
  | @insert p s hp_not ih =>
    intro hprimes
    have hp_prime : p.Prime := hprimes p (Finset.mem_insert_self p s)
    have hprimes_s : ∀ q ∈ s, q.Prime := fun q hq => hprimes q (Finset.mem_insert_of_mem hq)
    have ih_s := ih hprimes_s
    let S₀ := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ s)
    let T := Finset.range (M + 1) ×ˢ S₀
    let S₁ := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ insert p s)
    have hsub_img : S₁ ⊆ T.image (fun x : ℕ × ℕ => p ^ x.1 * x.2) := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hk_icc := Finset.mem_Icc.mp hk'.1
      have hk_nz : k ≠ 0 := by omega
      let e := k.factorization p
      let k₀ := k / p ^ e
      have hpow_dvd : p ^ e ∣ k := Nat.ordProj_dvd k p
      have hk_eq : p ^ e * k₀ = k := Nat.mul_div_cancel' hpow_dvd
      have hpow_pos : 0 < p ^ e := pow_pos hp_prime.pos e
      have hk₀_pos : 0 < k₀ := by
        rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
        · rw [h0, mul_zero] at hk_eq; omega
        · exact hpos
      have hk₀_le_k : k₀ ≤ k := Nat.div_le_self k (p ^ e)
      have he_lt : e < M + 1 := by
        have hpe_le_k : p ^ e ≤ k := Nat.le_of_dvd hk_icc.1 hpow_dvd
        have h2_le : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp_prime.two_le e
        have he_lt_2 : e < 2 ^ e := Nat.lt_pow_self (by norm_num)
        omega
      have hp_not_dvd : ¬ p ∣ k₀ := Nat.not_dvd_ordCompl hp_prime hk_nz
      have hk₀_pf : k₀.primeFactors ⊆ s := by
        intro q hq
        have hq_prime := Nat.prime_of_mem_primeFactors hq
        have hq_dvd_k₀ := Nat.dvd_of_mem_primeFactors hq
        have hq_dvd_k : q ∣ k := hq_dvd_k₀.trans (hk_eq ▸ dvd_mul_left k₀ (p ^ e))
        have hq_mem : q ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_k, hk_nz⟩
        rcases Finset.mem_insert.mp (hk'.2 hq_mem) with rfl | hqs
        · exact (hp_not_dvd hq_dvd_k₀).elim
        · exact hqs
      have hk₀_mem : k₀ ∈ S₀ := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hk₀_pos, hk₀_le_k.trans hk_icc.2⟩, hk₀_pf⟩
      exact Finset.mem_image.mpr
        ⟨(e, k₀), Finset.mem_product.mpr ⟨Finset.mem_range.mpr he_lt, hk₀_mem⟩, hk_eq⟩
    have hmul_sum :
        ∑ x ∈ T, ((p ^ x.1 * x.2 : ℕ) : ℝ)⁻¹ =
          (∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e) * ∑ k₀ ∈ S₀, (k₀ : ℝ)⁻¹ := by
      dsimp [T]
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k₀ _ => ?_
      push_cast
      rw [mul_inv, inv_pow]
    have hgeom : ∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
      geom_sum_inv_prime_le p hp_prime M
    have hS₀_nn : 0 ≤ ∑ k₀ ∈ S₀, (k₀ : ℝ)⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
    have hinv_pos : 0 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
      exact inv_nonneg.mpr (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hp1).le)
    calc
      ∑ k ∈ S₁, (k : ℝ)⁻¹
          ≤ ∑ k ∈ T.image (fun x : ℕ × ℕ => p ^ x.1 * x.2), (k : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_img (fun _ _ _ => by positivity)
      _ ≤ ∑ x ∈ T, ((p ^ x.1 * x.2 : ℕ) : ℝ)⁻¹ :=
            sum_image_inv_le_sum T (fun x : ℕ × ℕ => p ^ x.1 * x.2)
      _ = (∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e) * ∑ k₀ ∈ S₀, (k₀ : ℝ)⁻¹ := hmul_sum
      _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ * ∏ q ∈ s, (1 - (q : ℝ)⁻¹)⁻¹ :=
            mul_le_mul hgeom ih_s hS₀_nn hinv_pos
      _ = ∏ q ∈ insert p s, (1 - (q : ℝ)⁻¹)⁻¹ := (Finset.prod_insert hp_not).symm

/-- Harmonic sum lower bound: `log (N + 1) ≤ ∑_{m = 1}^N 1 / m`. -/
theorem harmonicSum_ge_log_succ (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hpos1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
    have hstep : Real.log ((N + 2 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ) ≤
        ((N + 1 : ℕ) : ℝ)⁻¹ := by
      have hdiv : ((N + 2 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) = 1 + ((N + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp [hpos1.ne']
        ring
      rw [← Real.log_div hpos2.ne' hpos1.ne', hdiv]
      have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ((N + 1 : ℕ) : ℝ)⁻¹)
      linarith
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have hsucc : (N + 1 + 1 : ℕ) = N + 2 := rfl
    rw [hsucc]
    linarith

/-- Squarefree reciprocal Euler-totient sum lower bound:
`log (N + 1) ≤ ∑_{d ∣ P(N), d ≤ N} (1 / d) * ∏_{p ∣ d} (1 - 1 / p)⁻¹ = ∑_{d ≤ N, sqfree} 1 / φ(d)`. -/
theorem sum_sqfree_inv_totient_ge_log_succ (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤
      ∑ d ∈ (selbergPrimeProd N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (N : ℝ)),
        ((d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
  let rad : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors, p
  let D := (selbergPrimeProd N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (N : ℝ))
  have hmaps : ∀ m ∈ Finset.Icc 1 N, rad m ∈ D := by
    intro m hm
    have hm_icc := Finset.mem_Icc.mp hm
    have hrad_dvd_m : rad m ∣ m := Nat.prod_primeFactors_dvd m
    have hrad_le_m : rad m ≤ m := Nat.le_of_dvd hm_icc.1 hrad_dvd_m
    have hsub_primes : m.primeFactors ⊆ Nat.primesLE N := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_le : p ≤ m := Nat.le_of_dvd hm_icc.1 (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.mem_primesLE.mpr ⟨hp_le.trans hm_icc.2, hp_prime⟩
    have hrad_dvd_P : rad m ∣ selbergPrimeProd N := by
      rw [selbergPrimeProd, Nat.floor_natCast, primorial_eq_prod_primesLE]
      exact Finset.prod_dvd_prod_of_subset _ _ id hsub_primes
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hrad_dvd_P, selbergPrimeProd_ne_zero N⟩,
        by exact_mod_cast hrad_le_m.trans hm_icc.2⟩
  have hfiber :
      ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ =
        ∑ d ∈ D, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m = d), (m : ℝ)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hbound_fiber : ∀ d ∈ D,
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m = d), (m : ℝ)⁻¹ ≤
        (d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdP : d ∣ selbergPrimeProd N := Nat.dvd_of_mem_divisors hd'.1
    have hd_sq : Squarefree d := (selbergPrimeProd_squarefree N).squarefree_of_dvd hdP
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sq.ne_zero
    let K := (Finset.Icc 1 N).filter (fun k => k.primeFactors ⊆ d.primeFactors)
    have himg : ((Finset.Icc 1 N).filter (fun m => rad m = d)).image (fun m => m / d) ⊆ K := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
      have hm' := Finset.mem_filter.mp hm
      have hm_icc := Finset.mem_Icc.mp hm'.1
      have hdm : d ∣ m := hm'.2 ▸ Nat.prod_primeFactors_dvd m
      have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdm
      have hk_pos : 0 < m / d := by
        rcases Nat.eq_zero_or_pos (m / d) with h0 | hpos
        · rw [h0, mul_zero] at hmul; omega
        · exact hpos
      have hk_le : m / d ≤ N := (Nat.div_le_self m d).trans hm_icc.2
      have hk_pf : (m / d).primeFactors ⊆ d.primeFactors := by
        intro q hq
        have hq_prime := Nat.prime_of_mem_primeFactors hq
        have hq_dvd_m : q ∣ m := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hdm)
        have hqm : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_m, by omega⟩
        have hq_dvd_rad : q ∣ rad m := Finset.dvd_prod_of_mem _ hqm
        rw [hm'.2] at hq_dvd_rad
        exact Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_rad, hd_pos.ne'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, hk_pf⟩
    have hinj : Set.InjOn (fun m => m / d) (((Finset.Icc 1 N).filter (fun m => rad m = d)) : Set ℕ) := by
      intro m₁ hm₁ m₂ hm₂ heq
      have h1 : d ∣ m₁ := (Finset.mem_filter.mp hm₁).2 ▸ Nat.prod_primeFactors_dvd m₁
      have h2 : d ∣ m₂ := (Finset.mem_filter.mp hm₂).2 ▸ Nat.prod_primeFactors_dvd m₂
      dsimp only at heq
      calc
        m₁ = d * (m₁ / d) := (Nat.mul_div_cancel' h1).symm
        _ = d * (m₂ / d) := by rw [heq]
        _ = m₂ := Nat.mul_div_cancel' h2
    have hsum_k :
        ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m = d), (m : ℝ)⁻¹ =
          (d : ℝ)⁻¹ * ∑ k ∈ ((Finset.Icc 1 N).filter (fun m => rad m = d)).image (fun m => m / d),
            (k : ℝ)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hdm : d ∣ m := (Finset.mem_filter.mp hm).2 ▸ Nat.prod_primeFactors_dvd m
      have hmul : m = d * (m / d) := (Nat.mul_div_cancel' hdm).symm
      conv_lhs => rw [hmul]
      push_cast
      rw [mul_inv]
    have hd_primes : ∀ p ∈ d.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
    calc
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m = d), (m : ℝ)⁻¹
          = (d : ℝ)⁻¹ * ∑ k ∈ ((Finset.Icc 1 N).filter (fun m => rad m = d)).image (fun m => m / d),
              (k : ℝ)⁻¹ := hsum_k
      _ ≤ (d : ℝ)⁻¹ * ∑ k ∈ K, (k : ℝ)⁻¹ := by
            gcongr
      _ ≤ (d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
            gcongr
            exact sum_Icc_primeFactors_subset_le N d.primeFactors hd_primes
  calc
    Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := harmonicSum_ge_log_succ N
    _ = ∑ d ∈ D, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m = d), (m : ℝ)⁻¹ := hfiber
    _ ≤ ∑ d ∈ D, (d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
        Finset.sum_le_sum hbound_fiber

private def invNatArith : ArithmeticFunction ℝ where
  toFun d := (d : ℝ)⁻¹
  map_zero' := by simp

private lemma invNatArith_isMultiplicative : invNatArith.IsMultiplicative := by
  constructor
  · simp [invNatArith]
  · intro m n _
    simp [invNatArith, Nat.cast_mul]; ring

/-- `BoundingSieve` for counting primes in the interval `(x, x + y]` with primes `p ≤ z`
sifted out, using main mass `y` and density `ν(d) = 1 / d`. -/
def intervalSieve (x y z : ℝ) : BoundingSieve where
  support := Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊
  prodPrimes := selbergPrimeProd z
  prodPrimes_squarefree := selbergPrimeProd_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y
  nu := invNatArith
  nu_mult := invNatArith_isMultiplicative
  nu_pos_of_prime p hp _ := by
    simp [invNatArith, Nat.cast_pos.mpr hp.pos]
  nu_lt_one_of_prime p hp _ := by
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    simpa [invNatArith] using inv_lt_one_of_one_lt₀ hp1

private lemma card_Ioc_filter_dvd (a b d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ioc a b).filter (d ∣ ·)).card = b / d - a / d := by
  have himg : ((Finset.Ioc (a / d) (b / d)).image (fun q => q * d)) =
      (Finset.Ioc a b).filter (d ∣ ·) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_left d q⟩
      · exact (Nat.div_lt_iff_lt_mul hd).mp hq1
      · exact (Nat.le_div_iff_mul_le hd).mp hq2
    · rintro ⟨⟨ha, hb⟩, ⟨q, rfl⟩⟩
      refine ⟨q, ⟨?_, ?_⟩, by ring⟩
      · rw [Nat.div_lt_iff_lt_mul hd]; linarith [mul_comm d q]
      · rw [Nat.le_div_iff_mul_le hd]; linarith [mul_comm d q]
  have hinj : Set.InjOn (fun q => q * d) (Finset.Ioc (a / d) (b / d) : Set ℕ) :=
    fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_right hd heq
  rw [← himg, Finset.card_image_of_injOn hinj]
  simp

/-- Remainder bound for `intervalSieve`: for `0 ≤ x`, `0 ≤ y`, and `1 ≤ d`,
`|(intervalSieve x y z).rem d| ≤ 2`. -/
theorem abs_intervalSieve_rem_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {d : ℕ} (hd : 1 ≤ d) :
    |(intervalSieve x y z).rem d| ≤ 2 := by
  have hdR_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmult : (intervalSieve x y z).multSum d = ((⌊x + y⌋₊ / d - ⌊x⌋₊ / d : ℕ) : ℝ) := by
    rw [multSum_eq_card_of_weights_one (fun _ => rfl)]
    dsimp [intervalSieve]
    rw [card_Ioc_filter_dvd _ _ d hd]
  have hle_ab : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  have hdiv_le : ⌊x⌋₊ / d ≤ ⌊x + y⌋₊ / d := Nat.div_le_div_right hle_ab
  have hnu : (intervalSieve x y z).nu d = (d : ℝ)⁻¹ := rfl
  unfold BoundingSieve.rem
  rw [hmult, hnu, Nat.cast_sub hdiv_le]
  have hfloor_x_lo : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  have hfloor_x_hi : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hfloor_xy_lo : x + y - 1 < (⌊x + y⌋₊ : ℝ) := Nat.sub_one_lt_floor (x + y)
  have hfloor_xy_hi : (⌊x + y⌋₊ : ℝ) ≤ x + y := Nat.floor_le (by linarith)
  have hdiv1_lo : (⌊x⌋₊ : ℝ) / d - 1 < ((⌊x⌋₊ / d : ℕ) : ℝ) := by
    have : ⌊x⌋₊ < (⌊x⌋₊ / d + 1) * d := by
      have hdm := Nat.div_add_mod ⌊x⌋₊ d
      have hmod := Nat.mod_lt ⌊x⌋₊ hd
      nlinarith
    have hR : ((⌊x⌋₊ : ℕ) : ℝ) < (((⌊x⌋₊ / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast this
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdR_pos]
    exact hR
  have hdiv1_hi : ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / d := by
    rw [le_div_iff₀ hdR_pos]
    exact_mod_cast Nat.div_mul_le_self ⌊x⌋₊ d
  have hdiv2_lo : (⌊x + y⌋₊ : ℝ) / d - 1 < ((⌊x + y⌋₊ / d : ℕ) : ℝ) := by
    have : ⌊x + y⌋₊ < (⌊x + y⌋₊ / d + 1) * d := by
      have hdm := Nat.div_add_mod ⌊x + y⌋₊ d
      have hmod := Nat.mod_lt ⌊x + y⌋₊ hd
      nlinarith
    have hR : ((⌊x + y⌋₊ : ℕ) : ℝ) < (((⌊x + y⌋₊ / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast this
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdR_pos]
    exact hR
  have hdiv2_hi : ((⌊x + y⌋₊ / d : ℕ) : ℝ) ≤ (⌊x + y⌋₊ : ℝ) / d := by
    rw [le_div_iff₀ hdR_pos]
    exact_mod_cast Nat.div_mul_le_self ⌊x + y⌋₊ d
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hinv_le1 : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd_ge1
  have hdiff_hi : (⌊x + y⌋₊ : ℝ) / d - (⌊x⌋₊ : ℝ) / d ≤ y / d + 1 / d := by
    have : (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) ≤ y + 1 := by linarith
    calc
      (⌊x + y⌋₊ : ℝ) / d - (⌊x⌋₊ : ℝ) / d = ((⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)) / d := by ring
      _ ≤ (y + 1) / d := div_le_div_of_nonneg_right this hdR_pos.le
      _ = y / d + 1 / d := by ring
  have hdiff_lo : y / d - 1 / d ≤ (⌊x + y⌋₊ : ℝ) / d - (⌊x⌋₊ : ℝ) / d := by
    have : y - 1 ≤ (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by linarith
    calc
      y / d - 1 / d = (y - 1) / d := by ring
      _ ≤ ((⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)) / d := div_le_div_of_nonneg_right this hdR_pos.le
      _ = (⌊x + y⌋₊ : ℝ) / d - (⌊x⌋₊ : ℝ) / d := by ring
  have h1d : 1 / (d : ℝ) ≤ 1 := by rw [one_div]; exact hinv_le1
  have htotal : (intervalSieve x y z).totalMass = y := rfl
  have hy_div : (d : ℝ)⁻¹ * y = y / (d : ℝ) := by ring
  rw [htotal, hy_div, abs_le]
  constructor
  · linarith
  · linarith

/-- Explicit Selberg upper bound for primes in an interval `(x, x + y]`:
for `0 ≤ x`, `0 ≤ y`, and `1 < z`,
`primePi (x + y) - primePi x ≤ z + y / Real.log z + 2 * z ^ 2`. -/
theorem primeInterval_upper_bound_explicit {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 < z) :
    primePi (x + y) - primePi x ≤ z + y / Real.log z + 2 * z ^ 2 := by
  let s := intervalSieve x y z
  have hz_nn : 0 ≤ z := by linarith
  have hpi_le : primePi (x + y) - primePi x ≤ z + s.siftedSum := by
    rw [primePi_eq_card_primesLE, primePi_eq_card_primesLE]
    have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊x + y⌋₊ := by
      intro p hp
      have hp' := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨hp'.1.trans (Nat.floor_mono (by linarith)), hp'.2⟩
    have hdiff_eq :
        ((Nat.primesLE ⌊x + y⌋₊).card : ℝ) - ((Nat.primesLE ⌊x⌋₊).card : ℝ) =
          (((Nat.primesLE ⌊x + y⌋₊ \ Nat.primesLE ⌊x⌋₊).card : ℕ) : ℝ) := by
      rw [← Nat.cast_sub (Finset.card_le_card hsub), Finset.card_sdiff,
        Finset.inter_eq_left.mpr hsub]
    rw [hdiff_eq, siftedSum_eq_card_of_weights_one (fun _ => rfl)]
    let P_all := Nat.primesLE ⌊x + y⌋₊ \ Nat.primesLE ⌊x⌋₊
    let P_sm := P_all.filter (fun p : ℕ => (p : ℝ) ≤ z)
    let P_lg := P_all.filter (fun p : ℕ => z < (p : ℝ))
    have hpart : P_all.card = P_sm.card + P_lg.card := by
      have h := P_all.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ z)
      have hnot : P_all.filter (fun p : ℕ => ¬ (p : ℝ) ≤ z) = P_lg := by
        ext p; simp [P_lg]
      rw [hnot] at h
      exact h.symm
    have hsm_le : (P_sm.card : ℝ) ≤ z := by
      have hsub_icc : P_sm ⊆ Finset.Icc 1 ⌊z⌋₊ := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hp_mem := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp'.1).1
        exact Finset.mem_Icc.mpr ⟨hp_mem.2.one_le, Nat.le_floor hp'.2⟩
      have hle : P_sm.card ≤ ⌊z⌋₊ := (Finset.card_le_card hsub_icc).trans (by simp)
      exact (by exact_mod_cast hle : (P_sm.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz_nn)
    have hlg_le : P_lg.card ≤ (s.support.filter (fun n => Nat.Coprime s.prodPrimes n)).card := by
      refine Finset.card_le_card fun p hp => ?_
      have hp' := Finset.mem_filter.mp hp
      have hp_sdiff := Finset.mem_sdiff.mp hp'.1
      have hp_mem := Nat.mem_primesLE.mp hp_sdiff.1
      have hp_not_x : ¬ p ≤ ⌊x⌋₊ := fun hle => hp_sdiff.2 (Nat.mem_primesLE.mpr ⟨hle, hp_mem.2⟩)
      have hp_ioc : p ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ :=
        Finset.mem_Ioc.mpr ⟨lt_of_not_ge hp_not_x, hp_mem.1⟩
      have hcop : Nat.Coprime (selbergPrimeProd z) p :=
        coprime_selbergPrimeProd_of_prime_gt hp_mem.2 hp'.2
      exact Finset.mem_filter.mpr ⟨hp_ioc, hcop⟩
    rw [hpart, Nat.cast_add]
    have hlgR : (P_lg.card : ℝ) ≤ ((s.support.filter (fun n => Nat.Coprime s.prodPrimes n)).card : ℝ) :=
      by exact_mod_cast hlg_le
    linarith
  have hG_ge : Real.log z ≤ selbergG s z := by
    have hlt_fl : z < ((⌊z⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one z
    have hlog_le : Real.log z ≤ Real.log ((⌊z⌋₊ + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hlt_fl.le
    have htot := sum_sqfree_inv_totient_ge_log_succ ⌊z⌋₊
    have heq_G : selbergG s z =
        ∑ d ∈ (selbergPrimeProd ⌊z⌋₊).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (⌊z⌋₊ : ℝ)),
          ((d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
      unfold selbergG
      have hsP : s.prodPrimes = selbergPrimeProd ⌊z⌋₊ := by
        change selbergPrimeProd z = selbergPrimeProd ⌊z⌋₊
        simp [selbergPrimeProd]
      rw [hsP]
      have hflt :
          (selbergPrimeProd ⌊z⌋₊).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z) =
            (selbergPrimeProd ⌊z⌋₊).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (⌊z⌋₊ : ℝ)) := by
        ext d
        simp only [Finset.mem_filter]
        refine and_congr_right fun _ => ?_
        constructor
        · intro hdz; exact_mod_cast Nat.le_floor hdz
        · intro hd_fl
          have hd_nat : d ≤ ⌊z⌋₊ := by exact_mod_cast hd_fl
          exact (by exact_mod_cast hd_nat : (d : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz_nn)
      rw [hflt]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [s.selbergTerms_apply d]
      rfl
    rw [heq_G]
    exact hlog_le.trans htot
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz
  have hmain_le : s.totalMass / selbergG s z ≤ y / Real.log z := by
    have hs_tot : s.totalMass = y := rfl
    rw [hs_tot]
    exact div_le_div_of_nonneg_left hy hlogz_pos hG_ge
  have herr_le :
      ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
        ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          |s.rem (d₁.lcm d₂)| ≤ 2 * z ^ 2 := by
    let D := s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
    have hD_sub : D ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
        (Nat.dvd_of_mem_divisors hd'.1))
      exact Finset.mem_Icc.mpr ⟨hd_pos, Nat.le_floor hd'.2⟩
    have hD_card : (D.card : ℝ) ≤ z := by
      have h1 : D.card ≤ ⌊z⌋₊ := (Finset.card_le_card hD_sub).trans (by simp)
      exact (by exact_mod_cast h1 : (D.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz_nn)
    have hterm_le : ∀ d₁ ∈ D, ∀ d₂ ∈ D, |s.rem (d₁.lcm d₂)| ≤ 2 := by
      intro d₁ hd₁ d₂ hd₂
      have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (hD_sub hd₁)).1
      have hd₂_pos : 0 < d₂ := (Finset.mem_Icc.mp (hD_sub hd₂)).1
      have hlcm_pos : 1 ≤ d₁.lcm d₂ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')
      exact abs_intervalSieve_rem_le hx hy hlcm_pos
    calc
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, |s.rem (d₁.lcm d₂)|
          ≤ ∑ _d₁ ∈ D, ∑ _d₂ ∈ D, (2 : ℝ) :=
            Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm_le d₁ hd₁ d₂ hd₂
      _ = (D.card : ℝ) ^ 2 * 2 := by simp; ring
      _ ≤ z ^ 2 * 2 := by gcongr
      _ = 2 * z ^ 2 := by ring
  have hup := selberg_upper_bound_simple s hz.le
  linarith

/-- **Brun–Titchmarsh Theorem in Intervals** (asymptotic `(2 + o(1)) y / log y` via the
Selberg sieve): for every `ε > 0`, there exists `Y₀ ≥ 2` such that for all `x ≥ 0` and
`y ≥ Y₀`, `π(x + y) - π(x) ≤ (2 + ε) * y / Real.log y`. -/
theorem primeInterval_upper_bound_asymptotic :
    ∀ ε > 0, ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ x y : ℝ, 0 ≤ x → Y₀ ≤ y →
      primePi (x + y) - primePi x ≤ (2 + ε) * y / Real.log y := by
  intro ε hε
  let δ : ℝ := min (ε / 32) (1 / 8)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ_le8 : δ ≤ 1 / 8 := min_le_right _ _
  have hδ_eps : 16 * δ ≤ ε / 2 := by
    have h1 : δ ≤ ε / 32 := min_le_left _ _
    linarith
  let M₀ : ℝ := max 1 (Real.log (2 / δ))
  let L₀ : ℝ := max 4 (max ((2 / δ) * M₀) (8 / min ε 1))
  let Y₀ : ℝ := Real.exp L₀
  have hL₀_ge4 : 4 ≤ L₀ := le_max_left _ _
  have hY₀_ge2 : 2 ≤ Y₀ := by
    have h1 : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    exact h1.trans (Real.exp_le_exp.mpr hL₀_ge4)
  refine ⟨Y₀, hY₀_ge2, fun x y hx hy => ?_⟩
  have hy_pos : 0 < y := by linarith
  let L : ℝ := Real.log y
  have hL_ge : L₀ ≤ L := by
    calc
      L₀ = Real.log Y₀ := (Real.log_exp L₀).symm
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos _) hy
  have hL_ge4 : 4 ≤ L := hL₀_ge4.trans hL_ge
  have hL_pos : 0 < L := by linarith
  have hL_ge_M : (2 / δ) * M₀ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL_ge
  have hL_ge_eps : 8 / min ε 1 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL_ge
  have hlogL_le : Real.log L ≤ δ * L := by
    let u : ℝ := L * (δ / 2)
    have hu_pos : 0 < u := mul_pos hL_pos (by positivity)
    have h1 : Real.log u ≤ u := by linarith [Real.log_le_sub_one_of_pos hu_pos]
    have h2 : Real.log L = Real.log u + Real.log (2 / δ) := by
      dsimp [u]
      rw [← Real.log_mul hu_pos.ne' (by positivity)]
      congr 1
      dsimp [u]
      field_simp [hδ_pos.ne']
    have h3 : Real.log (2 / δ) ≤ (δ / 2) * L := by
      have hM : Real.log (2 / δ) ≤ M₀ := le_max_right _ _
      have h4 : M₀ ≤ (δ / 2) * L := by
        calc
          M₀ = (δ / 2) * ((2 / δ) * M₀) := by field_simp [hδ_pos.ne']
          _ ≤ (δ / 2) * L := mul_le_mul_of_nonneg_left hL_ge_M (by positivity)
      exact hM.trans h4
    calc
      Real.log L = Real.log u + Real.log (2 / δ) := h2
      _ ≤ L * (δ / 2) + (δ / 2) * L := add_le_add h1 h3
      _ = δ * L := by ring
  let z : ℝ := Real.sqrt y / L ^ 2
  have hz_pos : 0 < z := div_pos (Real.sqrt_pos.mpr hy_pos) (sq_pos_of_pos hL_pos)
  have hlog_sqrt : Real.log (Real.sqrt y) = L / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hy_pos]
    dsimp [L]; ring
  have hlogz_eq : Real.log z = L / 2 - 2 * Real.log L := by
    dsimp [z]
    rw [Real.log_div (Real.sqrt_pos.mpr hy_pos).ne' (sq_pos_of_pos hL_pos).ne',
      hlog_sqrt, Real.log_pow]
    push_cast; rfl
  have hlogz_ge : (1 / 2 - 2 * δ) * L ≤ Real.log z := by
    rw [hlogz_eq]
    linarith
  have h14L_le_logz : L / 4 ≤ Real.log z := by
    have : L / 4 ≤ (1 / 2 - 2 * δ) * L := by nlinarith [hδ_le8, hL_pos]
    exact this.trans hlogz_ge
  have hz_gt1 : 1 < z := by
    have hlogz_ge1 : 1 ≤ Real.log z := by linarith
    have hexp1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc
      (1 : ℝ) < Real.exp 1 := hexp1
      _ ≤ Real.exp (Real.log z) := Real.exp_le_exp.mpr hlogz_ge1
      _ = z := Real.exp_log hz_pos
  have hmain_le : y / Real.log z ≤ (2 + ε / 2) * y / L := by
    have hfac_pos : 0 < 1 - 4 * δ := by linarith [hδ_le8]
    have hinv_le : (1 - 4 * δ)⁻¹ ≤ 1 + 8 * δ := by
      have hmul : 1 ≤ (1 - 4 * δ) * (1 + 8 * δ) := by
        have : (1 - 4 * δ) * (1 + 8 * δ) - 1 = 4 * δ * (1 - 8 * δ) := by ring
        have hnn : 0 ≤ 4 * δ * (1 - 8 * δ) := mul_nonneg (by linarith) (by linarith)
        linarith
      rw [inv_eq_one_div, div_le_iff₀ hfac_pos]
      linarith
    have h2_le : 2 * (1 - 4 * δ)⁻¹ ≤ 2 + ε / 2 := by
      calc
        2 * (1 - 4 * δ)⁻¹ ≤ 2 * (1 + 8 * δ) := by gcongr
        _ = 2 + 16 * δ := by ring
        _ ≤ 2 + ε / 2 := by linarith [hδ_eps]
    have hden_pos : 0 < (1 / 2 - 2 * δ) * L := mul_pos (by linarith) hL_pos
    calc
      y / Real.log z ≤ y / ((1 / 2 - 2 * δ) * L) :=
          div_le_div_of_nonneg_left hy_pos.le hden_pos hlogz_ge
      _ = (2 * (1 - 4 * δ)⁻¹) * y / L := by
          field_simp [hfac_pos.ne', hL_pos.ne']
          ring
      _ ≤ (2 + ε / 2) * y / L := by
          gcongr
  have hmin_le : min ε 1 ≤ ε := min_le_left _ _
  have h8_le : 8 / ε ≤ L := by
    have : 8 / ε ≤ 8 / min ε 1 := div_le_div_of_nonneg_left (by norm_num) (lt_min hε zero_lt_one) hmin_le
    exact this.trans hL_ge_eps
  have hz_le_err : z ≤ (ε / 4) * y / L := by
    have hy_ge1 : 1 ≤ y := by linarith
    have hsqrt_le : Real.sqrt y ≤ y := by
      rw [Real.sqrt_le_left hy_pos.le]
      nlinarith
    have hL_ge_4eps : 4 / ε ≤ L := by
      have : 4 / ε ≤ 8 / ε := by gcongr; norm_num
      exact this.trans h8_le
    have hinvL : L⁻¹ ≤ ε / 4 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hL_pos (by norm_num)]
      have h1 : 4 ≤ L * ε := (div_le_iff₀ hε).mp hL_ge_4eps
      linarith
    calc
      z = Real.sqrt y / L ^ 2 := rfl
      _ ≤ y / L ^ 2 := div_le_div_of_nonneg_right hsqrt_le (sq_nonneg _)
      _ = L⁻¹ * (y / L) := by ring
      _ ≤ (ε / 4) * (y / L) := mul_le_mul_of_nonneg_right hinvL (div_nonneg hy_pos.le hL_pos.le)
      _ = (ε / 4) * y / L := by ring
  have hz2_le_err : 2 * z ^ 2 ≤ (ε / 4) * y / L := by
    have hz2_eq : z ^ 2 = y / L ^ 4 := by
      dsimp [z]
      rw [div_pow, Real.sq_sqrt hy_pos.le]
      ring
    have hL2_le : L ^ 2 ≤ L ^ 4 := by
      have h1_le_L2 : 1 ≤ L ^ 2 := by nlinarith
      nlinarith
    have h2invL : 2 / L ≤ ε / 4 := by
      rw [div_le_div_iff₀ hL_pos (by norm_num)]
      have h1 : 8 ≤ L * ε := (div_le_iff₀ hε).mp h8_le
      linarith
    calc
      2 * z ^ 2 = 2 * (y / L ^ 4) := by rw [hz2_eq]
      _ ≤ 2 * (y / L ^ 2) := by gcongr
      _ = (2 / L) * (y / L) := by ring
      _ ≤ (ε / 4) * (y / L) := mul_le_mul_of_nonneg_right h2invL (div_nonneg hy_pos.le hL_pos.le)
      _ = (ε / 4) * y / L := by ring
  have hexp := primeInterval_upper_bound_explicit hx hy_pos.le hz_gt1
  calc
    primePi (x + y) - primePi x ≤ z + y / Real.log z + 2 * z ^ 2 := hexp
    _ ≤ (ε / 4) * y / L + (2 + ε / 2) * y / L + (ε / 4) * y / L :=
        add_le_add (add_le_add hz_le_err hmain_le) hz2_le_err
    _ = (2 + ε) * y / Real.log y := by dsimp [L]; ring

/-! #### 2. Twin Primes Sharp Upper Bound `π₂(x) ≤ C * x / (log x)^2` -/

/-- Twin prime counting function `π₂(x) = #{p ≤ x : p.Prime ∧ (p + 2).Prime}`. -/
def selbergTwinCount (x : ℝ) : ℝ :=
  (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)).card : ℝ)

/-- `selbergTwinCount x` is always nonnegative. -/
theorem selbergTwinCount_nonneg (x : ℝ) : 0 ≤ selbergTwinCount x :=
  Nat.cast_nonneg _

/-- `selbergTwinCount x ≤ x` for `0 ≤ x`. -/
theorem selbergTwinCount_le_self {x : ℝ} (hx : 0 ≤ x) : selbergTwinCount x ≤ x := by
  unfold selbergTwinCount
  have hcard : ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)).card ≤ ⌊x⌋₊ :=
    (Finset.card_filter_le _ _).trans (by simp)
  exact (by exact_mod_cast hcard : _ ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx)

/-- Multiplicative root-counting function for twin primes (`ω(p) = 1` if `p = 2`, `2` if `p > 2`). -/
def selbergTwinOmega : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else ∏ p ∈ n.primeFactors, (if p = 2 then (1 : ℝ) else 2)
  map_zero' := by simp

/-- At a nonzero natural number `n`, `selbergTwinOmega n = ∏_{p ∣ n} (if p = 2 then 1 else 2)`. -/
theorem selbergTwinOmega_apply_ne_zero {n : ℕ} (hn : n ≠ 0) :
    selbergTwinOmega n = ∏ p ∈ n.primeFactors, (if p = 2 then (1 : ℝ) else 2) := by
  simp [selbergTwinOmega, hn]

/-- At a prime `p`, `selbergTwinOmega p = if p = 2 then 1 else 2`. -/
theorem selbergTwinOmega_prime {p : ℕ} (hp : p.Prime) :
    selbergTwinOmega p = if p = 2 then (1 : ℝ) else 2 := by
  rw [selbergTwinOmega_apply_ne_zero hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

/-- `selbergTwinOmega` is multiplicative. -/
theorem selbergTwinOmega_isMultiplicative : selbergTwinOmega.IsMultiplicative := by
  constructor
  · simp [selbergTwinOmega]
  · intro m n hcop
    by_cases hm0 : m = 0
    · subst hm0; simp [selbergTwinOmega]
    by_cases hn0 : n = 0
    · subst hn0; simp [selbergTwinOmega]
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    rw [selbergTwinOmega_apply_ne_zero hmn0, selbergTwinOmega_apply_ne_zero hm0,
      selbergTwinOmega_apply_ne_zero hn0, hcop.primeFactors_mul,
      Finset.prod_union hcop.disjoint_primeFactors]

/-- For every squarefree `d`, `selbergTwinOmega d ≤ d`. -/
theorem selbergTwinOmega_le_self {d : ℕ} (hd : Squarefree d) :
    selbergTwinOmega d ≤ (d : ℝ) := by
  rw [selbergTwinOmega_apply_ne_zero hd.ne_zero]
  have hd_prod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    have h1 : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd).symm
    conv_lhs => rw [h1]
    push_cast
    rfl
  rw [hd_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => by split_ifs <;> norm_num) (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  split_ifs with h2
  · subst h2; norm_num
  · exact_mod_cast hp2

/-- `BoundingSieve` setup for twin primes `n(n + 2)` with `1 ≤ n ≤ x` and primes `p ≤ z`. -/
def selbergTwinSieve (x z : ℝ) : BoundingSieve :=
  mkBoundingSieveOfOmega ((Finset.Icc 1 ⌊x⌋₊).image (fun n => n * (n + 2)))
    (selbergPrimeProd z) (selbergPrimeProd_squarefree z) (⌊x⌋₊ : ℝ)
    selbergTwinOmega selbergTwinOmega_isMultiplicative
    (fun p hp _ => by rw [selbergTwinOmega_prime hp]; split_ifs <;> norm_num)
    (fun p hp _ => by
      rw [selbergTwinOmega_prime hp]
      have hp2 : 2 ≤ p := hp.two_le
      split_ifs with h2
      · subst h2; norm_num
      · exact_mod_cast (by omega : 2 < p))

private lemma card_Icc_mod_eq_bounds {d : ℕ} (hd : 1 ≤ d) (N r₀ : ℕ) (hr₀ : r₀ < d) :
    ((N / d : ℕ) : ℝ) ≤ (((Finset.Icc 1 N).filter (fun n => n % d = r₀)).card : ℝ) ∧
      (((Finset.Icc 1 N).filter (fun n => n % d = r₀)).card : ℝ) ≤ (N / d : ℕ) + 1 := by
  let F := (Finset.Icc 1 N).filter (fun n => n % d = r₀)
  have hup_nat : F.card ≤ N / d + 1 := by
    have hinj : Set.InjOn (fun n => n / d) (F : Set ℕ) := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      dsimp only at hab
      rw [← Nat.div_add_mod a d, ← Nat.div_add_mod b d, hab, ha'.2, hb'.2]
    have himg : F.image (fun n => n / d) ⊆ Finset.range (N / d + 1) := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
      have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN))
    calc
      F.card = (F.image (fun n => n / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (N / d + 1)).card := Finset.card_le_card himg
      _ = N / d + 1 := Finset.card_range _
  have hlo_nat : N / d ≤ F.card := by
    by_cases hr0 : r₀ = 0
    · subst hr0
      let g : ℕ → ℕ := fun q => q * d
      have hinj : Set.InjOn g (Finset.Icc 1 (N / d) : Set ℕ) :=
        fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_right hd heq
      have himg : (Finset.Icc 1 (N / d)).image g ⊆ F := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
        have hq' := Finset.mem_Icc.mp hq
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hq'.1 hd, ?_⟩, ?_⟩
        · exact (Nat.mul_le_mul_right d hq'.2).trans (Nat.div_mul_le_self N d)
        · simp [g]
      calc
        N / d = (Finset.Icc 1 (N / d)).card := by simp
        _ = ((Finset.Icc 1 (N / d)).image g).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ F.card := Finset.card_le_card himg
    · let g : ℕ → ℕ := fun q => q * d + r₀
      have hinj : Set.InjOn g (Finset.range (N / d) : Set ℕ) := by
        intro q₁ _ q₂ _ heq
        dsimp [g] at heq
        exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel heq)
      have himg : (Finset.range (N / d)).image g ⊆ F := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
        have hq_lt : q < N / d := Finset.mem_range.mp hq
        have hleN : q * d + r₀ ≤ N := by
          have h1 : q * d + r₀ < (q + 1) * d := by
            rw [Nat.add_mul, one_mul]
            exact Nat.add_lt_add_left hr₀ (q * d)
          have h2 : (q + 1) * d ≤ (N / d) * d := Nat.mul_le_mul_right d hq_lt
          exact le_trans h1.le (h2.trans (Nat.div_mul_le_self N d))
        have hge1 : 1 ≤ q * d + r₀ :=
          le_trans (Nat.pos_of_ne_zero hr0) (Nat.le_add_left r₀ (q * d))
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge1, hleN⟩, ?_⟩
        dsimp [g]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr₀]
      calc
        N / d = (Finset.range (N / d)).card := (Finset.card_range _).symm
        _ = ((Finset.range (N / d)).image g).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ F.card := Finset.card_le_card himg
  exact ⟨by exact_mod_cast hlo_nat, by exact_mod_cast hup_nat⟩

private def twinRootsNat (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun r => d ∣ r * (r + 2))

private lemma dvd_mul_add_two_iff_mem_twinRootsNat {d : ℕ} (hd : 0 < d) (n : ℕ) :
    d ∣ n * (n + 2) ↔ n % d ∈ twinRootsNat d := by
  simp only [twinRootsNat, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => ⟨Nat.mod_lt n hd, ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mod_mod, Nat.add_mod, Nat.mod_mod,
      ← Nat.add_mod, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
    exact h
  · rw [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mod_mod, Nat.add_mod, Nat.mod_mod,
      ← Nat.add_mod, ← Nat.mul_mod] at h
    exact h

private lemma card_twinRootsNat_prime {p : ℕ} (hp : p.Prime) :
    (twinRootsNat p).card = if p = 2 then 1 else 2 := by
  by_cases hp2 : p = 2
  · subst hp2
    have htr : twinRootsNat 2 = {0} := by
      ext r
      simp only [twinRootsNat, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hdvd⟩
        interval_cases r <;> simp_all
      · rintro rfl; decide
    simp [htr]
  · simp only [hp2, ↓reduceIte]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have htr : twinRootsNat p = {0, p - 2} := by
      ext r
      simp only [twinRootsNat, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hdvd⟩
        rcases hp.dvd_mul.mp hdvd with h1 | h2
        · left; exact Nat.eq_zero_of_dvd_of_lt h1 hr
        · right
          rcases h2 with ⟨k, hk⟩
          have hk0 : k ≠ 0 := by intro hk0; subst hk0; omega
          have hk2 : k < 2 := by
            by_contra hge
            have hge2 : 2 ≤ k := not_lt.mp hge
            have h1 : p * 2 ≤ p * k := Nat.mul_le_mul_left p hge2
            omega
          have hk1 : k = 1 := by omega
          subst hk1; omega
      · rintro (rfl | rfl)
        · exact ⟨hp.pos, by simp⟩
        · refine ⟨by omega, ?_⟩
          rw [show p - 2 + 2 = p by omega]
          exact dvd_mul_left p _
    rw [htr, Finset.card_pair (by omega)]

private lemma card_twinRootsNat_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    (twinRootsNat (m * n)).card = (twinRootsNat m).card * (twinRootsNat n).card := by
  have hbij : (twinRootsNat (m * n)).card = ((twinRootsNat m) ×ˢ (twinRootsNat n)).card := by
    refine Finset.card_bij (fun r _ => (r % m, r % n)) ?_ ?_ ?_
    · intro r hr
      simp only [twinRootsNat, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt r hm, ?_⟩, ⟨Nat.mod_lt r hn, ?_⟩⟩
      · have hm_dvd : m ∣ r * (r + 2) := dvd_trans (dvd_mul_right m n) hr.2
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mod_mod, Nat.add_mod, Nat.mod_mod,
          ← Nat.add_mod, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
        exact hm_dvd
      · have hn_dvd : n ∣ r * (r + 2) := dvd_trans (dvd_mul_left n m) hr.2
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mod_mod, Nat.add_mod, Nat.mod_mod,
          ← Nat.add_mod, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
        exact hn_dvd
    · intro r₁ hr₁ r₂ hr₂ heq
      have hr₁_lt : r₁ < m * n := Finset.mem_range.mp (Finset.mem_filter.mp hr₁).1
      have hr₂_lt : r₂ < m * n := Finset.mem_range.mp (Finset.mem_filter.mp hr₂).1
      have hpeq := Prod.ext_iff.mp heq
      have hmod : r₁ ≡ r₂ [MOD m * n] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨hpeq.1, hpeq.2⟩
      change r₁ % (m * n) = r₂ % (m * n) at hmod
      rwa [Nat.mod_eq_of_lt hr₁_lt, Nat.mod_eq_of_lt hr₂_lt] at hmod
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_product, twinRootsNat, Finset.mem_filter, Finset.mem_range] at hab
      have : NeZero m := ⟨hm.ne'⟩
      have : NeZero n := ⟨hn.ne'⟩
      have : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
      let e := ZMod.chineseRemainder hmn
      let r : ℕ := (e.symm ((a : ZMod m), (b : ZMod n))).val
      have hr_lt : r < m * n := ZMod.val_lt _
      have hre : e (r : ZMod (m * n)) = ((a : ZMod m), (b : ZMod n)) := by
        dsimp [r]; rw [ZMod.natCast_zmod_val, e.apply_symm_apply]
      have he_nat : e (r : ZMod (m * n)) = ((r : ZMod m), (r : ZMod n)) := by
        rw [map_natCast]; rfl
      rw [he_nat, Prod.ext_iff] at hre
      have hrm : r % m = a := by
        have hmod : r ≡ a [MOD m] := (ZMod.natCast_eq_natCast_iff r a m).mp hre.1
        change r % m = a % m at hmod
        rwa [Nat.mod_eq_of_lt hab.1.1] at hmod
      have hrn : r % n = b := by
        have hmod : r ≡ b [MOD n] := (ZMod.natCast_eq_natCast_iff r b n).mp hre.2
        change r % n = b % n at hmod
        rwa [Nat.mod_eq_of_lt hab.2.1] at hmod
      refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr_lt, ?_⟩, Prod.ext hrm hrn⟩
      refine hmn.mul_dvd_of_dvd_of_dvd ?_ ?_
      · rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, hrm,
          ← Nat.mod_eq_of_lt hab.1.1, ← Nat.add_mod, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
        exact hab.1.2
      · rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, hrn,
          ← Nat.mod_eq_of_lt hab.2.1, ← Nat.add_mod, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
        exact hab.2.2
  rw [hbij, Finset.card_product]

private lemma card_twinRootsNat_eq_omega {d : ℕ} (hd : Squarefree d) :
    ((twinRootsNat d).card : ℝ) = selbergTwinOmega d := by
  have hd_nat : ∀ k : ℕ, Squarefree k →
      (twinRootsNat k).card = ∏ p ∈ k.primeFactors, (if p = 2 then 1 else 2) := by
    intro k
    induction k using Nat.strong_induction_on with | ind k ih =>
    intro hk
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk.ne_zero
    by_cases hk1 : k = 1
    · subst hk1
      have htr : twinRootsNat 1 = {0} := by ext r; simp [twinRootsNat]
      simp [htr]
    · let p := k.minFac
      have hp : p.Prime := Nat.minFac_prime hk1
      have hpk : p ∣ k := Nat.minFac_dvd k
      let m := k / p
      have hkm : p * m = k := Nat.mul_div_cancel' hpk
      have hm_sq : Squarefree m := hk.squarefree_of_dvd (Nat.div_dvd_of_dvd hpk)
      have hm_lt : m < k := Nat.div_lt_self hk_pos hp.one_lt
      have hcop : p.Coprime m := (Nat.squarefree_mul_iff.mp (hkm.symm ▸ hk)).1
      have hpf : k.primeFactors = insert p m.primeFactors := by
        rw [← hkm, Nat.Coprime.primeFactors_mul hcop, Nat.Prime.primeFactors hp]
        ext q; simp [Finset.mem_insert]
      have hp_not : p ∉ m.primeFactors := fun hmem =>
        hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem) dvd_rfl))
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sq.ne_zero
      rw [← hkm, card_twinRootsNat_mul hp.pos hm_pos hcop, card_twinRootsNat_prime hp,
        ih m hm_lt hm_sq, hkm, hpf, Finset.prod_insert hp_not]
  rw [hd_nat d hd, selbergTwinOmega_apply_ne_zero hd.ne_zero]
  push_cast
  rfl

private lemma strictMono_mul_add_two : StrictMono (fun n : ℕ => n * (n + 2)) := by
  intro a b hab; nlinarith

/-- Remainder bound for `selbergTwinSieve`: for any squarefree `d`,
`|(selbergTwinSieve x z).rem d| ≤ selbergTwinOmega d`. -/
theorem abs_selbergTwinSieve_rem_le (x z : ℝ) {d : ℕ} (hd : Squarefree d) :
    |(selbergTwinSieve x z).rem d| ≤ selbergTwinOmega d := by
  have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero hd.ne_zero
  have hdR_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have himg : ((selbergTwinSieve x z).support.filter (d ∣ ·)) =
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => d ∣ n * (n + 2))).image (fun n => n * (n + 2)) := by
    ext m
    dsimp [selbergTwinSieve, mkBoundingSieveOfOmega]
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hdvd⟩; exact ⟨n, ⟨hn, hdvd⟩, rfl⟩
    · rintro ⟨n, ⟨hn, hdvd⟩, rfl⟩; exact ⟨⟨n, hn, rfl⟩, hdvd⟩
  have hmult : (selbergTwinSieve x z).multSum d =
      (((Finset.Icc 1 ⌊x⌋₊).filter (fun n => d ∣ n * (n + 2))).card : ℝ) := by
    rw [multSum_eq_card_of_weights_one (fun _ => rfl), himg,
      Finset.card_image_of_injective _ strictMono_mul_add_two.injective]
  have hnu_tot : (selbergTwinSieve x z).nu d * (selbergTwinSieve x z).totalMass =
      (selbergTwinOmega d / (d : ℝ)) * (⌊x⌋₊ : ℝ) := by
    dsimp [selbergTwinSieve, mkBoundingSieveOfOmega]
    rw [selbergDensityOmega_apply hd.ne_zero]
  unfold BoundingSieve.rem
  rw [hmult, hnu_tot]
  let N := ⌊x⌋₊
  have hpart :
      ((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card =
        ∑ r ∈ twinRootsNat d, ((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card := by
    have hmaps : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
        n % d ∈ twinRootsNat d := fun n hn =>
      (dvd_mul_add_two_iff_mem_twinRootsNat hd_pos n).mp (Finset.mem_filter.mp hn).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun r hr => ?_
    congr 1; ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hn1, hnN⟩, _⟩, hnr⟩; exact ⟨⟨hn1, hnN⟩, hnr⟩
    · rintro ⟨⟨hn1, hnN⟩, hnr⟩
      exact ⟨⟨⟨hn1, hnN⟩, (dvd_mul_add_two_iff_mem_twinRootsNat hd_pos n).mpr (hnr ▸ hr)⟩, hnr⟩
  have hfiber_bd : ∀ r ∈ twinRootsNat d,
      |(((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
    intro r hr
    have hr_lt : r < d := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hbd := card_Icc_mod_eq_bounds hd_pos N r hr_lt
    have hdiv_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdR_pos]; exact_mod_cast Nat.div_mul_le_self N d
    have hlt_div : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdR_pos]
      have hdm := Nat.div_add_mod N d
      have hmod := Nat.mod_lt N hd_pos
      have hnat : N < (N / d + 1) * d := by nlinarith
      exact_mod_cast hnat
    rw [abs_le]; constructor <;> linarith
  have hsum_eq :
      (selbergTwinOmega d / (d : ℝ)) * (N : ℝ) = ∑ _r ∈ twinRootsNat d, (N : ℝ) / (d : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, card_twinRootsNat_eq_omega hd]; ring
  rw [hpart, Nat.cast_sum, hsum_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ twinRootsNat d, ((((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) -
        (N : ℝ) / (d : ℝ))|
        ≤ ∑ r ∈ twinRootsNat d, |(((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) -
            (N : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ twinRootsNat d, (1 : ℝ) := Finset.sum_le_sum fun r hr => hfiber_bd r hr
    _ = selbergTwinOmega d := by simp [card_twinRootsNat_eq_omega hd]

private lemma lcm_mul_left_of_coprime {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    (p * a).lcm b = p * (a.lcm b) := by
  have hcop_a : p.Coprime a := hp.coprime_iff_not_dvd.mpr hpa
  have hcop_b : p.Coprime b := hp.coprime_iff_not_dvd.mpr hpb
  have hcop_ab : p.Coprime (a.lcm b) := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hmul : p ∣ a * b := hdvd.trans (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
    rcases hp.dvd_mul.mp hmul with ha | hb
    · exact hpa ha
    · exact hpb hb
  refine Nat.dvd_antisymm ?_ ?_
  · exact Nat.lcm_dvd (Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b))
      ((Nat.dvd_lcm_right a b).trans (dvd_mul_left _ p))
  · exact hcop_ab.mul_dvd_of_dvd_of_dvd ((dvd_mul_right p a).trans (Nat.dvd_lcm_left _ _))
      (Nat.lcm_dvd ((dvd_mul_left a p).trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _))

private lemma mul_lcm_mul_of_prime {p a b : ℕ} (hp : p.Prime) :
    (p * a).lcm (p * b) = p * (a.lcm b) := by
  refine Nat.dvd_antisymm ?_ ?_
  · exact Nat.lcm_dvd (Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b))
      (Nat.mul_dvd_mul_left p (Nat.dvd_lcm_right a b))
  · by_cases h0 : a = 0 ∨ b = 0
    · rcases h0 with rfl | rfl <;> simp
    have ha0 : a ≠ 0 := fun h => h0 (Or.inl h)
    have hb0 : b ≠ 0 := fun h => h0 (Or.inr h)
    have hlcm_nz : (p * a).lcm (p * b) ≠ 0 :=
      Nat.lcm_ne_zero (mul_ne_zero hp.ne_zero ha0) (mul_ne_zero hp.ne_zero hb0)
    have hp_dvd : p ∣ (p * a).lcm (p * b) := (dvd_mul_right p a).trans (Nat.dvd_lcm_left _ _)
    let q := ((p * a).lcm (p * b)) / p
    have hq : p * q = (p * a).lcm (p * b) := Nat.mul_div_cancel' hp_dvd
    have haq : a ∣ q := by
      have : p * a ∣ p * q := hq.symm ▸ Nat.dvd_lcm_left _ _
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
    have hbq : b ∣ q := by
      have : p * b ∣ p * q := hq.symm ▸ Nat.dvd_lcm_right _ _
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
    rw [← hq]
    exact Nat.mul_dvd_mul_left p (Nat.lcm_dvd haq hbq)

private lemma sum_divisors_lcm_eq_prod (f₁ f₂ : ℕ → ℝ)
    (hf₁_one : f₁ 1 = 1) (hf₂_one : f₂ 1 = 1)
    (hf₁_mul : ∀ {m n : ℕ}, m.Coprime n → f₁ (m * n) = f₁ m * f₁ n)
    (hf₂_mul : ∀ {m n : ℕ}, m.Coprime n → f₂ (m * n) = f₂ m * f₂ n) :
    ∀ d : ℕ, Squarefree d →
      ∑ a ∈ d.divisors, ∑ b ∈ d.divisors, (if a.lcm b = d then f₁ a * f₂ b else 0) =
        ∏ p ∈ d.primeFactors, (f₁ p + f₂ p + f₁ p * f₂ p) := by
  intro d
  induction d using Nat.strong_induction_on with | ind d ih =>
  intro hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  by_cases hd1 : d = 1
  · subst hd1
    simp [hf₁_one, hf₂_one]
  · let p := d.minFac
    have hp : p.Prime := Nat.minFac_prime hd1
    have hpd : p ∣ d := Nat.minFac_dvd d
    let m := d / p
    have hdm : p * m = d := Nat.mul_div_cancel' hpd
    have hm_sq : Squarefree m := hd.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)
    have hm_lt : m < d := Nat.div_lt_self hd_pos hp.one_lt
    have hcop : p.Coprime m := (Nat.squarefree_mul_iff.mp (hdm.symm ▸ hd)).1
    have hp_not_m : ¬ p ∣ m := fun h =>
      hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd h dvd_rfl))
    have hpf : d.primeFactors = insert p m.primeFactors := by
      rw [← hdm, hcop.primeFactors_mul, hp.primeFactors]
      ext q; simp [Finset.mem_insert]
    have hp_not_pf : p ∉ m.primeFactors := fun hmem =>
      hp_not_m (Nat.dvd_of_mem_primeFactors hmem)
    have hdiv_eq : d.divisors = m.divisors ∪ m.divisors.image (p * ·) := by
      ext a
      simp only [Nat.mem_divisors, ne_eq, hd.ne_zero, hm_sq.ne_zero, not_false_eq_true,
        and_true, Finset.mem_union, Finset.mem_image]
      constructor
      · intro ha
        by_cases hpa : p ∣ a
        · right
          refine ⟨a / p, ?_, Nat.mul_div_cancel' hpa⟩
          have : p * (a / p) ∣ p * m := by rwa [Nat.mul_div_cancel' hpa, hdm]
          exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
        · left
          rw [← hdm] at ha
          exact (hp.coprime_iff_not_dvd.mpr hpa).symm.dvd_of_dvd_mul_left ha
      · rintro (ham | ⟨a₀, ha₀, rfl⟩)
        · exact ham.trans (hdm ▸ dvd_mul_left m p)
        · exact hdm ▸ Nat.mul_dvd_mul_left p ha₀
    have hdisj : Disjoint m.divisors (m.divisors.image (p * ·)) := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      rcases Finset.mem_image.mp ha2 with ⟨a₀, _, rfl⟩
      exact hp_not_m ((dvd_mul_right p a₀).trans (Nat.dvd_of_mem_divisors ha1))
    have hinj : Set.InjOn (fun a => p * a) (m.divisors : Set ℕ) :=
      fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq
    have hsplit : ∀ g : ℕ → ℝ,
        ∑ a ∈ d.divisors, g a = (∑ a ∈ m.divisors, g a) + ∑ a ∈ m.divisors, g (p * a) := by
      intro g
      rw [hdiv_eq, Finset.sum_union hdisj, Finset.sum_image hinj]
    rw [hsplit]
    have hS00 :
        ∑ a ∈ m.divisors, ∑ b ∈ d.divisors, (if a.lcm b = d then f₁ a * f₂ b else 0) =
          ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
            (if a.lcm (p * b) = d then f₁ a * f₂ (p * b) else 0) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hsplit]
      have h0 : ∑ b ∈ m.divisors, (if a.lcm b = d then f₁ a * f₂ b else 0) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        have hlcm_m : a.lcm b ∣ m :=
          Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb)
        have hne : a.lcm b ≠ d := by
          intro heq
          rw [heq] at hlcm_m
          exact hp_not_m (hpd.trans hlcm_m)
        simp [hne]
      rw [h0, zero_add]
    have hS10 :
        ∑ a ∈ m.divisors, ∑ b ∈ d.divisors, (if (p * a).lcm b = d then f₁ (p * a) * f₂ b else 0) =
          (∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
            (if (p * a).lcm b = d then f₁ (p * a) * f₂ b else 0)) +
          ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
            (if (p * a).lcm (p * b) = d then f₁ (p * a) * f₂ (p * b) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => hsplit _
    have hT01 :
        ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
          (if a.lcm (p * b) = d then f₁ a * f₂ (p * b) else 0) =
            f₂ p * ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, (if a.lcm b = m then f₁ a * f₂ b else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have ha_ndvd : ¬ p ∣ a := fun h => hp_not_m (h.trans (Nat.dvd_of_mem_divisors ha))
      have hb_ndvd : ¬ p ∣ b := fun h => hp_not_m (h.trans (Nat.dvd_of_mem_divisors hb))
      have hlcm_eq : a.lcm (p * b) = p * (a.lcm b) := by
        rw [Nat.lcm_comm, lcm_mul_left_of_coprime hp hb_ndvd ha_ndvd, Nat.lcm_comm]
      have hcop_pb : p.Coprime b := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hb)
      simp only [hlcm_eq, ← hdm, Nat.mul_right_inj hp.ne_zero, hf₂_mul hcop_pb]
      split_ifs <;> ring
    have hT10 :
        ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
          (if (p * a).lcm b = d then f₁ (p * a) * f₂ b else 0) =
            f₁ p * ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, (if a.lcm b = m then f₁ a * f₂ b else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have ha_ndvd : ¬ p ∣ a := fun h => hp_not_m (h.trans (Nat.dvd_of_mem_divisors ha))
      have hb_ndvd : ¬ p ∣ b := fun h => hp_not_m (h.trans (Nat.dvd_of_mem_divisors hb))
      have hlcm_eq : (p * a).lcm b = p * (a.lcm b) := lcm_mul_left_of_coprime hp ha_ndvd hb_ndvd
      have hcop_pa : p.Coprime a := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors ha)
      simp only [hlcm_eq, ← hdm, Nat.mul_right_inj hp.ne_zero, hf₁_mul hcop_pa]
      split_ifs <;> ring
    have hT11 :
        ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
          (if (p * a).lcm (p * b) = d then f₁ (p * a) * f₂ (p * b) else 0) =
            (f₁ p * f₂ p) *
              ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, (if a.lcm b = m then f₁ a * f₂ b else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hcop_pa : p.Coprime a := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors ha)
      have hcop_pb : p.Coprime b := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hb)
      simp only [mul_lcm_mul_of_prime hp, ← hdm, Nat.mul_right_inj hp.ne_zero, hf₁_mul hcop_pa,
        hf₂_mul hcop_pb]
      split_ifs <;> ring
    rw [hS00, hS10, hT01, hT10, hT11, ih m hm_lt hm_sq, hpf, Finset.prod_insert hp_not_pf]
    ring

private noncomputable def phiInvProd (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, ((p : ℝ) - 1)⁻¹

private lemma phiInvProd_one : phiInvProd 1 = 1 := by simp [phiInvProd]

private lemma phiInvProd_mul_coprime {m n : ℕ} (hcop : m.Coprime n) :
    phiInvProd (m * n) = phiInvProd m * phiInvProd n := by
  unfold phiInvProd
  rw [hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors]

private lemma phiInvProd_nonneg (n : ℕ) : 0 ≤ phiInvProd n := by
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  exact inv_nonneg.mpr (by linarith)

private lemma phiInvProd_two_mul {a : ℕ} (ha : ¬ 2 ∣ a) (_ha0 : a ≠ 0) :
    phiInvProd (2 * a) = phiInvProd a := by
  have hcop : Nat.Coprime 2 a := Nat.prime_two.coprime_iff_not_dvd.mpr ha
  rw [phiInvProd_mul_coprime hcop]
  have h2 : phiInvProd 2 = 1 := by
    unfold phiInvProd
    rw [Nat.Prime.primeFactors Nat.prime_two, Finset.prod_singleton]
    norm_num
  rw [h2, one_mul]

private lemma sum_oddSqfree_phiInvProd_ge (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) / 2 ≤
      ∑ a ∈ (Finset.Icc 1 N).filter (fun a => Squarefree a ∧ ¬ 2 ∣ a), phiInvProd a := by
  let O := (Finset.Icc 1 N).filter (fun a => Squarefree a ∧ ¬ 2 ∣ a)
  let D := (selbergPrimeProd N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (N : ℝ))
  have hD_split :
      ∑ d ∈ D, ((d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) =
        ∑ d ∈ D, phiInvProd d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdP : d ∣ selbergPrimeProd N := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hd_sq : Squarefree d := (selbergPrimeProd_squarefree N).squarefree_of_dvd hdP
    have hprod_d : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      have h1 : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd_sq).symm
      conv_lhs => rw [h1]
      push_cast; rfl
    rw [hprod_d, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    field_simp [hp_pos.ne']
  have hD_sub : D ⊆ O ∪ O.image (2 * ·) := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdP : d ∣ selbergPrimeProd N := Nat.dvd_of_mem_divisors hd'.1
    have hd_sq : Squarefree d := (selbergPrimeProd_squarefree N).squarefree_of_dvd hdP
    have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero hd_sq.ne_zero
    have hd_le : d ≤ N := by exact_mod_cast hd'.2
    by_cases h2d : 2 ∣ d
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d / 2, ?_, Nat.mul_div_cancel' h2d⟩)
      have ha_sq : Squarefree (d / 2) := hd_sq.squarefree_of_dvd (Nat.div_dvd_of_dvd h2d)
      have ha_pos : 1 ≤ d / 2 := Nat.pos_of_ne_zero ha_sq.ne_zero
      have ha_le : d / 2 ≤ N := (Nat.div_le_self d 2).trans hd_le
      have ha_odd : ¬ 2 ∣ d / 2 := by
        intro h2a
        have : 2 * 2 ∣ d := by
          have := Nat.mul_dvd_mul_left 2 h2a
          rwa [Nat.mul_div_cancel' h2d] at this
        exact Nat.squarefree_iff_prime_squarefree.mp hd_sq 2 Nat.prime_two this
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha_pos, ha_le⟩, ha_sq, ha_odd⟩
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le⟩, hd_sq, h2d⟩)
  have hdisj : Disjoint O (O.image (2 * ·)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rcases Finset.mem_image.mp hd2 with ⟨a, _, rfl⟩
    exact (Finset.mem_filter.mp hd1).2.2 (dvd_mul_right 2 a)
  have hinj : Set.InjOn (2 * ·) (O : Set ℕ) :=
    fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left (by norm_num) heq
  have himg_sum : ∑ d ∈ O.image (2 * ·), phiInvProd d = ∑ a ∈ O, phiInvProd a := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_filter.mp ha
    exact phiInvProd_two_mul ha'.2.2 ha'.2.1.ne_zero
  have htot := (sum_sqfree_inv_totient_ge_log_succ N).trans_eq hD_split
  have hle_2 : ∑ d ∈ D, phiInvProd d ≤ 2 * ∑ a ∈ O, phiInvProd a := by
    calc
      ∑ d ∈ D, phiInvProd d
          ≤ ∑ d ∈ O ∪ O.image (2 * ·), phiInvProd d :=
            Finset.sum_le_sum_of_subset_of_nonneg hD_sub (fun d _ _ => phiInvProd_nonneg d)
      _ = (∑ d ∈ O, phiInvProd d) + ∑ d ∈ O.image (2 * ·), phiInvProd d :=
            Finset.sum_union hdisj
      _ = 2 * ∑ a ∈ O, phiInvProd a := by rw [himg_sum]; ring
  linarith

/-- Lower bound for `selbergG (selbergTwinSieve x z) z`: for `4 ≤ z`,
`Real.log (⌊Real.sqrt z⌋₊ + 1) ^ 2 / 4 ≤ selbergG (selbergTwinSieve x z) z`. -/
theorem selbergG_twinSieve_ge_sq_log {x z : ℝ} (hz : 4 ≤ z) :
    (Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ)) ^ 2 / 4 ≤
      selbergG (selbergTwinSieve x z) z := by
  let N := ⌊Real.sqrt z⌋₊
  let O := (Finset.Icc 1 N).filter (fun a => Squarefree a ∧ ¬ 2 ∣ a)
  let s := selbergTwinSieve x z
  let S_odd_z := s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ∧ ¬ 2 ∣ d)
  have hN_ge2 : 2 ≤ N := by
    have hsq : 2 ≤ Real.sqrt z := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    exact Nat.le_floor hsq
  have hlog_ge : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg; norm_cast; omega
  have hhalf := sum_oddSqfree_phiInvProd_ge N
  have hsq_half : (Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 / 4 ≤ (∑ a ∈ O, phiInvProd a) ^ 2 := by
    have : (Real.log ((N + 1 : ℕ) : ℝ) / 2) ^ 2 = (Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 / 4 := by ring
    rw [← this]
    gcongr
  have hmaps : ∀ ab ∈ O ×ˢ O, ab.1.lcm ab.2 ∈ S_odd_z := by
    intro ⟨a, b⟩ hab
    have hab' := Finset.mem_product.mp hab
    have ha' := Finset.mem_filter.mp hab'.1
    have hb' := Finset.mem_filter.mp hab'.2
    have ha_icc := Finset.mem_Icc.mp ha'.1
    have hb_icc := Finset.mem_Icc.mp hb'.1
    have ha_le_sq : (a : ℝ) ≤ Real.sqrt z :=
      (by exact_mod_cast ha_icc.2 : (a : ℝ) ≤ (N : ℝ)).trans (Nat.floor_le (Real.sqrt_nonneg z))
    have hb_le_sq : (b : ℝ) ≤ Real.sqrt z :=
      (by exact_mod_cast hb_icc.2 : (b : ℝ) ≤ (N : ℝ)).trans (Nat.floor_le (Real.sqrt_nonneg z))
    have hlcm_le_mul : a.lcm b ≤ a * b := Nat.le_of_dvd (Nat.mul_pos ha_icc.1 hb_icc.1)
      (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
    have hlcm_le_z : ((a.lcm b : ℕ) : ℝ) ≤ z := by
      calc
        ((a.lcm b : ℕ) : ℝ) ≤ ((a * b : ℕ) : ℝ) := by exact_mod_cast hlcm_le_mul
        _ = (a : ℝ) * (b : ℝ) := by push_cast; rfl
        _ ≤ Real.sqrt z * Real.sqrt z := mul_le_mul ha_le_sq hb_le_sq (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
        _ = z := Real.mul_self_sqrt (by linarith)
    have hlcm_odd : ¬ 2 ∣ a.lcm b := by
      intro hdvd
      have hmul : 2 ∣ a * b := hdvd.trans (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
      rcases Nat.prime_two.dvd_mul.mp hmul with ha2 | hb2
      · exact ha'.2.2 ha2
      · exact hb'.2.2 hb2
    have ha_dvd_P : a ∣ s.prodPrimes := by
      change a ∣ selbergPrimeProd z
      rw [selbergPrimeProd, primorial_eq_prod_primesLE]
      have ha_prod : a = ∏ p ∈ a.primeFactors, p := (Nat.prod_primeFactors_of_squarefree ha'.2.1).symm
      rw [ha_prod]
      refine Finset.prod_dvd_prod_of_subset _ _ id fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_le : p ≤ a := Nat.le_of_dvd ha_icc.1 (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor ((by exact_mod_cast hp_le : (p : ℝ) ≤ a).trans (ha_le_sq.trans (by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith))), hp_prime⟩
    have hb_dvd_P : b ∣ s.prodPrimes := by
      change b ∣ selbergPrimeProd z
      rw [selbergPrimeProd, primorial_eq_prod_primesLE]
      have hb_prod : b = ∏ p ∈ b.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hb'.2.1).symm
      rw [hb_prod]
      refine Finset.prod_dvd_prod_of_subset _ _ id fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_le : p ≤ b := Nat.le_of_dvd hb_icc.1 (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor ((by exact_mod_cast hp_le : (p : ℝ) ≤ b).trans (hb_le_sq.trans (by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith))), hp_prime⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.lcm_dvd ha_dvd_P hb_dvd_P, s.prodPrimes_ne_zero⟩, hlcm_le_z, hlcm_odd⟩
  have hpair_eq :
      (∑ a ∈ O, phiInvProd a) ^ 2 =
        ∑ d ∈ S_odd_z, ∑ ab ∈ (O ×ˢ O).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d),
          phiInvProd ab.1 * phiInvProd ab.2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber_le : ∀ d ∈ S_odd_z,
      ∑ ab ∈ (O ×ˢ O).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d),
        phiInvProd ab.1 * phiInvProd ab.2 ≤ s.selbergTerms d := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd'.1
    have hd_sq : Squarefree d := s.squarefree_of_dvd_prodPrimes hdP
    have hd_odd : ¬ 2 ∣ d := hd'.2.2
    have hsub_prod : (O ×ˢ O).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d) ⊆
        (d.divisors ×ˢ d.divisors).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d) := by
      intro ⟨a, b⟩ hab
      have hab' := Finset.mem_filter.mp hab
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hab'.2⟩
      · exact Nat.mem_divisors.mpr ⟨hab'.2 ▸ Nat.dvd_lcm_left a b, hd_sq.ne_zero⟩
      · exact Nat.mem_divisors.mpr ⟨hab'.2 ▸ Nat.dvd_lcm_right a b, hd_sq.ne_zero⟩
    have h1 :
        ∑ ab ∈ (O ×ˢ O).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d),
            phiInvProd ab.1 * phiInvProd ab.2 ≤
          ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
            (if a.lcm b = d then phiInvProd a * phiInvProd b else 0) := by
      calc
        ∑ ab ∈ (O ×ˢ O).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d),
            phiInvProd ab.1 * phiInvProd ab.2
            ≤ ∑ ab ∈ (d.divisors ×ˢ d.divisors).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d),
                phiInvProd ab.1 * phiInvProd ab.2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_prod
                (fun _ _ _ => mul_nonneg (phiInvProd_nonneg _) (phiInvProd_nonneg _))
        _ = ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
              (if a.lcm b = d then phiInvProd a * phiInvProd b else 0) := by
              rw [Finset.sum_filter, Finset.sum_product]
    have h2 :
        ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
            (if a.lcm b = d then phiInvProd a * phiInvProd b else 0) =
          ∏ p ∈ d.primeFactors, (phiInvProd p + phiInvProd p + phiInvProd p * phiInvProd p) :=
      sum_divisors_lcm_eq_prod phiInvProd phiInvProd phiInvProd_one phiInvProd_one
        (fun h => phiInvProd_mul_coprime h) (fun h => phiInvProd_mul_coprime h) d hd_sq
    have h3 :
        ∏ p ∈ d.primeFactors, (phiInvProd p + phiInvProd p + phiInvProd p * phiInvProd p) ≤
          s.selbergTerms d := by
      have hs_terms : s.selbergTerms d =
          ∏ p ∈ d.primeFactors, (s.nu p * (1 - s.nu p)⁻¹) := by
        rw [s.selbergTerms_apply d, ← s.prod_primeFactors_nu hdP, Finset.prod_mul_distrib]
      rw [hs_terms]
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · exact add_nonneg (add_nonneg (phiInvProd_nonneg p) (phiInvProd_nonneg p))
          (mul_nonneg (phiInvProd_nonneg p) (phiInvProd_nonneg p))
      · have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        have hp_ne2 : p ≠ 2 := fun hp2 => hd_odd (hp2 ▸ hp_dvd)
        have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
        have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        have hphi_p : phiInvProd p = ((p : ℝ) - 1)⁻¹ := by
          unfold phiInvProd
          rw [hp_prime.primeFactors, Finset.prod_singleton]
        have hnu_p : s.nu p = 2 / (p : ℝ) := by
          dsimp [s, selbergTwinSieve, mkBoundingSieveOfOmega]
          rw [selbergDensityOmega_apply hp_prime.ne_zero, selbergTwinOmega_prime hp_prime]
          simp only [eq_false hp_ne2, ↓reduceIte]
        rw [hphi_p, hnu_p]
        have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
        have hp2_pos : 0 < (p : ℝ) - 2 := by linarith
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hdiff :
            (2 / (p : ℝ)) * (1 - 2 / (p : ℝ))⁻¹ -
              (((p : ℝ) - 1)⁻¹ + ((p : ℝ) - 1)⁻¹ + ((p : ℝ) - 1)⁻¹ * ((p : ℝ) - 1)⁻¹) =
            (p : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1) ^ 2) := by
          field_simp [hp_pos.ne', hp1_pos.ne', hp2_pos.ne']
          ring
        have hdiff_nn : 0 ≤ (p : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1) ^ 2) := by positivity
        linarith
    exact h1.trans (h2.trans_le h3)
  have hS_sub : S_odd_z ⊆ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z) := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd'.1, hd'.2.1⟩
  calc
    (Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 / 4 ≤ (∑ a ∈ O, phiInvProd a) ^ 2 := hsq_half
    _ = ∑ d ∈ S_odd_z, ∑ ab ∈ (O ×ˢ O).filter (fun ab : ℕ × ℕ => ab.1.lcm ab.2 = d),
          phiInvProd ab.1 * phiInvProd ab.2 := hpair_eq
    _ ≤ ∑ d ∈ S_odd_z, s.selbergTerms d := Finset.sum_le_sum hfiber_le
    _ ≤ selbergG s z := Finset.sum_le_sum_of_subset_of_nonneg hS_sub
        (fun d hd _ => selbergTerms_nonneg_of_mem (Finset.mem_filter.mp hd).1)

/-- **Twin Primes Sharp Upper Bound via the Selberg Sieve**:
there exists a positive constant `C` such that for all `x ≥ 3`,
`π₂(x) ≤ C * x / (log x)^2`. -/
theorem selberg_twin_primes_bound :
    ∃ C > 0, ∀ x : ℝ, 3 ≤ x → selbergTwinCount x ≤ C * x / (Real.log x) ^ 2 := by
  let x₀ : ℝ := 1024
  have hx₀_gt : 3 ≤ x₀ := by norm_num
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogx₀_pos : 0 < Real.log x₀ := Real.log_pos (by norm_num)
  let C_lg : ℝ := 400 + 200
  let C_sm : ℝ := (Real.log x₀) ^ 2
  let C : ℝ := max C_lg C_sm
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num [C_lg]) (le_max_left _ _)
  refine ⟨C, hC_pos, fun x hx => ?_⟩
  by_cases hbig : x₀ ≤ x
  · have hx_pos : 0 < x := by linarith
    let z : ℝ := x ^ (1 / 5 : ℝ)
    have hz_ge4 : 4 ≤ z := by
      have h4_5 : (1024 : ℝ) = 4 ^ (5 : ℕ) := by norm_num
      have hx_ge : (4 : ℝ) ^ (5 : ℕ) ≤ x := by linarith
      calc
        (4 : ℝ) = ((4 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        _ ≤ x ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) hx_ge (by norm_num)
    have hz_ge1 : 1 ≤ z := by linarith
    let s := selbergTwinSieve x z
    have htwin_le : selbergTwinCount x ≤ z + s.siftedSum := by
      unfold selbergTwinCount
      let P_all := (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)
      let P_sm := P_all.filter (fun p : ℕ => (p : ℝ) ≤ z)
      let P_lg := P_all.filter (fun p : ℕ => z < (p : ℝ))
      have hpart : P_all.card = P_sm.card + P_lg.card := by
        have h := P_all.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ z)
        have hnot : P_all.filter (fun p : ℕ => ¬ (p : ℝ) ≤ z) = P_lg := by ext p; simp [P_lg]
        rw [hnot] at h; exact h.symm
      have hsm_le : (P_sm.card : ℝ) ≤ z := by
        have hsub : P_sm ⊆ Finset.Icc 1 ⌊z⌋₊ := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp'.1).1).1,
            Nat.le_floor hp'.2⟩
        exact (by exact_mod_cast (Finset.card_le_card hsub).trans (by simp) :
          (P_sm.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
      have hlg_le : P_lg.card ≤ (s.support.filter (fun m => Nat.Coprime s.prodPrimes m)).card := by
        have hinj : Set.InjOn (fun p : ℕ => p * (p + 2)) (P_lg : Set ℕ) :=
          fun _ _ _ _ h => strictMono_mul_add_two.injective h
        have himg : P_lg.image (fun p => p * (p + 2)) ⊆
            s.support.filter (fun m => Nat.Coprime s.prodPrimes m) := by
          intro m hm
          rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
          have hp' := Finset.mem_filter.mp hp
          have hp'' := Finset.mem_filter.mp hp'.1
          have hcop : Nat.Coprime (selbergPrimeProd z) (p * (p + 2)) := by
            refine Nat.Coprime.mul_right ?_ ?_
            · exact coprime_selbergPrimeProd_of_prime_gt hp''.2.1 hp'.2
            · exact coprime_selbergPrimeProd_of_prime_gt hp''.2.2 (by push_cast; linarith)
          exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hp''.1, rfl⟩, hcop⟩
        calc
          P_lg.card = (P_lg.image (fun p => p * (p + 2))).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (s.support.filter (fun m => Nat.Coprime s.prodPrimes m)).card :=
              Finset.card_le_card himg
      rw [hpart, Nat.cast_add, siftedSum_eq_card_of_weights_one (fun _ => rfl)]
      have hlgR : (P_lg.card : ℝ) ≤ ((s.support.filter (fun m => Nat.Coprime s.prodPrimes m)).card : ℝ) :=
        by exact_mod_cast hlg_le
      linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hG_ge : (Real.log x) ^ 2 / 400 ≤ selbergG s z := by
      have hG1 := selbergG_twinSieve_ge_sq_log (x := x) hz_ge4
      have hN_gt : Real.sqrt z < ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; exact Nat.lt_floor_add_one _
      have hsqrtz_eq : Real.sqrt z = x ^ (1 / 10 : ℝ) := by
        dsimp [z]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx_pos.le]
        congr 1; norm_num
      have hlog_ge : (1 / 10 : ℝ) * Real.log x ≤ Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ) := by
        have h1 : Real.log (x ^ (1 / 10 : ℝ)) ≤ Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hx_pos _) (hsqrtz_eq ▸ hN_gt.le)
        rwa [Real.log_rpow hx_pos] at h1
      have hsq_ge : ((1 / 10 : ℝ) * Real.log x) ^ 2 / 4 ≤
          (Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ)) ^ 2 / 4 := by
        gcongr
      have heq : ((1 / 10 : ℝ) * Real.log x) ^ 2 / 4 = (Real.log x) ^ 2 / 400 := by ring
      linarith
    have hmain_le : s.totalMass / selbergG s z ≤ 400 * x / (Real.log x) ^ 2 := by
      have hs_tot : s.totalMass ≤ x := Nat.floor_le hx_pos.le
      have hs_tot_nn : 0 ≤ s.totalMass := Nat.cast_nonneg _
      have hG_lb_pos : 0 < (Real.log x) ^ 2 / 400 := by positivity
      calc
        s.totalMass / selbergG s z ≤ x / selbergG s z :=
            div_le_div_of_nonneg_right hs_tot (selbergG_pos hz_ge1).le
        _ ≤ x / ((Real.log x) ^ 2 / 400) := div_le_div_of_nonneg_left hx_pos.le hG_lb_pos hG_ge
        _ = 400 * x / (Real.log x) ^ 2 := by ring
    have herr_le :
        ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
            |s.rem (d₁.lcm d₂)| ≤ z ^ 4 := by
      let D := s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
      have hD_sub : D ⊆ Finset.Icc 1 ⌊z⌋₊ := by
        intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
          (Nat.dvd_of_mem_divisors hd'.1))
        exact Finset.mem_Icc.mpr ⟨hd_pos, Nat.le_floor hd'.2⟩
      have hD_card : (D.card : ℝ) ≤ z :=
        (by exact_mod_cast (Finset.card_le_card hD_sub).trans (by simp) :
          (D.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
      have hterm_le : ∀ d₁ ∈ D, ∀ d₂ ∈ D, |s.rem (d₁.lcm d₂)| ≤ z ^ 2 := by
        intro d₁ hd₁ d₂ hd₂
        have hd₁' := Finset.mem_filter.mp hd₁
        have hd₂' := Finset.mem_filter.mp hd₂
        have hd₁P : d₁ ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd₁'.1
        have hd₂P : d₂ ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd₂'.1
        have hlcmP : d₁.lcm d₂ ∣ s.prodPrimes := Nat.lcm_dvd hd₁P hd₂P
        have hlcm_sq : Squarefree (d₁.lcm d₂) := s.squarefree_of_dvd_prodPrimes hlcmP
        have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (hD_sub hd₁)).1
        have hd₂_pos : 0 < d₂ := (Finset.mem_Icc.mp (hD_sub hd₂)).1
        have hlcm_le : d₁.lcm d₂ ≤ d₁ * d₂ := Nat.le_of_dvd (Nat.mul_pos hd₁_pos hd₂_pos)
          (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
        calc
          |s.rem (d₁.lcm d₂)| ≤ selbergTwinOmega (d₁.lcm d₂) :=
              abs_selbergTwinSieve_rem_le x z hlcm_sq
          _ ≤ ((d₁.lcm d₂ : ℕ) : ℝ) := selbergTwinOmega_le_self hlcm_sq
          _ ≤ ((d₁ * d₂ : ℕ) : ℝ) := by exact_mod_cast hlcm_le
          _ = (d₁ : ℝ) * (d₂ : ℝ) := by push_cast; rfl
          _ ≤ z * z := mul_le_mul hd₁'.2 hd₂'.2 (Nat.cast_nonneg _) (by linarith)
          _ = z ^ 2 := by ring
      calc
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, |s.rem (d₁.lcm d₂)|
            ≤ ∑ _d₁ ∈ D, ∑ _d₂ ∈ D, z ^ 2 :=
              Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm_le d₁ hd₁ d₂ hd₂
        _ = (D.card : ℝ) ^ 2 * z ^ 2 := by simp; ring
        _ ≤ z ^ 2 * z ^ 2 := by gcongr
        _ = z ^ 4 := by ring
    have hz4_eq : z ^ 4 = x ^ (4 / 5 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      congr 1; norm_num
    have hz_le_z4 : z ≤ z ^ 4 := by
      have hz3 : 1 ≤ z ^ 3 := one_le_pow₀ hz_ge1
      calc
        z = z * 1 := (mul_one z).symm
        _ ≤ z * z ^ 3 := mul_le_mul_of_nonneg_left hz3 (by linarith)
        _ = z ^ 4 := by ring
    have hlogx_rpow : (Real.log x) ^ 2 ≤ 100 * x ^ (1 / 5 : ℝ) := by
      have hr_pos : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hx_pos _
      have h1 : Real.log (x ^ (1 / 10 : ℝ)) ≤ x ^ (1 / 10 : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hr_pos]
      rw [Real.log_rpow hx_pos] at h1
      have hlog_le : Real.log x ≤ 10 * x ^ (1 / 10 : ℝ) := by linarith
      have hsq_le : (Real.log x) ^ 2 ≤ (10 * x ^ (1 / 10 : ℝ)) ^ 2 := by gcongr
      have hpow2 : (x ^ (1 / 10 : ℝ)) ^ 2 = x ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
        congr 1; norm_num
      calc
        (Real.log x) ^ 2 ≤ (10 * x ^ (1 / 10 : ℝ)) ^ 2 := hsq_le
        _ = 100 * (x ^ (1 / 10 : ℝ)) ^ 2 := by ring
        _ = 100 * x ^ (1 / 5 : ℝ) := by rw [hpow2]
    have hz4_le_div : z ^ 4 ≤ 100 * x / (Real.log x) ^ 2 := by
      rw [hz4_eq, le_div_iff₀ (sq_pos_of_pos hlogx_pos)]
      have hx_split : x ^ (4 / 5 : ℝ) * x ^ (1 / 5 : ℝ) = x := by
        rw [← Real.rpow_add hx_pos]
        norm_num
      calc
        x ^ (4 / 5 : ℝ) * (Real.log x) ^ 2 ≤ x ^ (4 / 5 : ℝ) * (100 * x ^ (1 / 5 : ℝ)) := by
            gcongr
        _ = 100 * (x ^ (4 / 5 : ℝ) * x ^ (1 / 5 : ℝ)) := by ring
        _ = 100 * x := by rw [hx_split]
    have hup := selberg_upper_bound_simple s hz_ge1
    have htot_le : selbergTwinCount x ≤ C_lg * x / (Real.log x) ^ 2 := by
      calc
        selbergTwinCount x ≤ z + s.siftedSum := htwin_le
        _ ≤ z + (s.totalMass / selbergG s z +
              ∑ d₁ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
                ∑ d₂ ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
                  |s.rem (d₁.lcm d₂)|) := add_le_add_right hup z
        _ ≤ z ^ 4 + (400 * x / (Real.log x) ^ 2 + z ^ 4) :=
            add_le_add hz_le_z4 (add_le_add hmain_le herr_le)
        _ ≤ 100 * x / (Real.log x) ^ 2 +
              (400 * x / (Real.log x) ^ 2 + 100 * x / (Real.log x) ^ 2) :=
            add_le_add hz4_le_div (add_le_add le_rfl hz4_le_div)
        _ = C_lg * x / (Real.log x) ^ 2 := by dsimp [C_lg]; ring
    exact htot_le.trans (by
      have hC_ge : C_lg ≤ C := le_max_left _ _
      gcongr)
  · have hx_lt : x < x₀ := lt_of_not_ge hbig
    have hx0 : 0 ≤ x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx_le : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hx_lt.le
    have h1 : 1 ≤ C_sm / (Real.log x) ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hlogx_pos), one_mul]
      dsimp [C_sm]
      gcongr
    calc
      selbergTwinCount x ≤ x := selbergTwinCount_le_self hx0
      _ = x * 1 := (mul_one x).symm
      _ ≤ x * (C_sm / (Real.log x) ^ 2) := mul_le_mul_of_nonneg_left h1 hx0
      _ = C_sm * x / (Real.log x) ^ 2 := by ring
      _ ≤ C * x / (Real.log x) ^ 2 := by
          have hC_ge : C_sm ≤ C := le_max_right _ _
          gcongr

/-! #### 3. Binary Goldbach Upper Bound -/

/-- The Goldbach representation count `r₂(n) = #{1 ≤ p ≤ n : p.Prime ∧ (n - p).Prime}`. -/
def goldbachRepCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun p => p.Prime ∧ (n - p).Prime)).card

/-- Multiplicative sieve density numerator for Goldbach representations of `2N`:
`ω_{2N}(p) = 1` if `p = 2 ∨ p ∣ N`, and `2` otherwise. -/
def goldbachOmega (N : ℕ) : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else ∏ p ∈ d.primeFactors, (if p = 2 ∨ p ∣ N then (1 : ℝ) else 2)
  map_zero' := by simp

/-- Value of `goldbachOmega N` at a nonzero natural number `d`. -/
theorem goldbachOmega_apply_ne_zero (N : ℕ) {d : ℕ} (hd : d ≠ 0) :
    goldbachOmega N d = ∏ p ∈ d.primeFactors, (if p = 2 ∨ p ∣ N then (1 : ℝ) else 2) := by
  simp [goldbachOmega, hd]

/-- Value of `goldbachOmega N` at a prime `p`. -/
theorem goldbachOmega_prime (N : ℕ) {p : ℕ} (hp : p.Prime) :
    goldbachOmega N p = if p = 2 ∨ p ∣ N then (1 : ℝ) else 2 := by
  rw [goldbachOmega_apply_ne_zero N hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

/-- `goldbachOmega N` is multiplicative. -/
theorem goldbachOmega_isMultiplicative (N : ℕ) : (goldbachOmega N).IsMultiplicative := by
  constructor
  · simp [goldbachOmega]
  · intro m n hcop
    by_cases hm0 : m = 0
    · subst hm0; simp [goldbachOmega]
    by_cases hn0 : n = 0
    · subst hn0; simp [goldbachOmega]
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    rw [goldbachOmega_apply_ne_zero N hmn0, goldbachOmega_apply_ne_zero N hm0,
      goldbachOmega_apply_ne_zero N hn0, hcop.primeFactors_mul,
      Finset.prod_union hcop.disjoint_primeFactors]

/-- For every squarefree `d`, `goldbachOmega N d ≤ d`. -/
theorem goldbachOmega_le_self (N : ℕ) {d : ℕ} (hd : Squarefree d) :
    goldbachOmega N d ≤ (d : ℝ) := by
  rw [goldbachOmega_apply_ne_zero N hd.ne_zero]
  have hd_prod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    have h1 : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd).symm
    conv_lhs => rw [h1]
    push_cast; rfl
  rw [hd_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => by split_ifs <;> norm_num) (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  split_ifs
  · exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hp2)
  · exact_mod_cast hp2

/-- `BoundingSieve` setup for Goldbach pairs `(n, 2N - n)` with `1 ≤ n ≤ N` and primes `p ≤ z`. -/
def goldbachSieve (N : ℕ) (z : ℝ) : BoundingSieve :=
  mkBoundingSieveOfOmega ((Finset.Icc 1 N).image (fun n => n * (2 * N - n)))
    (selbergPrimeProd z) (selbergPrimeProd_squarefree z) (N : ℝ)
    (goldbachOmega N) (goldbachOmega_isMultiplicative N)
    (fun p hp _ => by rw [goldbachOmega_prime N hp]; split_ifs <;> norm_num)
    (fun p hp _ => by
      rw [goldbachOmega_prime N hp]
      have hp2 : 2 ≤ p := hp.two_le
      split_ifs with h
      · exact_mod_cast (by omega : 1 < p)
      · exact_mod_cast (by have : p ≠ 2 := fun h2 => h (Or.inl h2); omega : 2 < p))

private def goldbachRootsNat (N d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun r => (d : ℤ) ∣ (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)))

private lemma dvd_goldbach_iff_mem_roots {N d : ℕ} (hd : 0 < d) {n : ℕ} (hn : n ≤ N) :
    d ∣ n * (2 * N - n) ↔ n % d ∈ goldbachRootsNat N d := by
  have h2N : n ≤ 2 * N := by omega
  have hZ : d ∣ n * (2 * N - n) ↔ (d : ℤ) ∣ (n : ℤ) * (2 * (N : ℤ) - (n : ℤ)) := by
    rw [← Int.natCast_dvd_natCast]
    push_cast [Nat.cast_sub h2N]
    rfl
  rw [hZ]
  simp only [goldbachRootsNat, Finset.mem_filter, Finset.mem_range]
  have hmod : (n : ℤ) ≡ ((n % d : ℕ) : ℤ) [ZMOD d] := by
    rw [Int.ModEq, Int.ofNat_mod_ofNat]
    simp
  have hdvd_diff : (d : ℤ) ∣ (n : ℤ) * (2 * (N : ℤ) - (n : ℤ)) -
      ((n % d : ℕ) : ℤ) * (2 * (N : ℤ) - ((n % d : ℕ) : ℤ)) := by
    have hnd : (d : ℤ) ∣ (n : ℤ) - ((n % d : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hmod.symm
    have hfac : (n : ℤ) * (2 * (N : ℤ) - (n : ℤ)) -
        ((n % d : ℕ) : ℤ) * (2 * (N : ℤ) - ((n % d : ℕ) : ℤ)) =
        ((n : ℤ) - ((n % d : ℕ) : ℤ)) * (2 * (N : ℤ) - (n : ℤ) - ((n % d : ℕ) : ℤ)) := by ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hnd _
  refine ⟨fun h => ⟨Nat.mod_lt n hd, ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · have := dvd_sub h hdvd_diff
    simpa using this
  · have := dvd_add hdvd_diff h
    simpa using this

private lemma card_goldbachRootsNat_prime (N : ℕ) {p : ℕ} (hp : p.Prime) :
    (goldbachRootsNat N p).card = if p = 2 ∨ p ∣ N then 1 else 2 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htr : goldbachRootsNat N p = {0, (2 * N) % p} := by
    ext r
    simp only [goldbachRootsNat, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hdvd⟩
      rcases hpZ.dvd_or_dvd hdvd with h1 | h2
      · left
        have hp_nat : p ∣ r := Int.natCast_dvd_natCast.mp h1
        exact Nat.eq_zero_of_dvd_of_lt hp_nat hr
      · right
        have hmod : (r : ℤ) ≡ (2 * N : ℤ) [ZMOD p] := Int.modEq_iff_dvd.mpr h2
        have hnat : r ≡ 2 * N [MOD p] := Int.natCast_modEq_iff.mp hmod
        change r % p = (2 * N) % p at hnat
        rwa [Nat.mod_eq_of_lt hr] at hnat
    · rintro (rfl | rfl)
      · exact ⟨hp.pos, by simp⟩
      · refine ⟨Nat.mod_lt _ hp.pos, ?_⟩
        have hmod : (((2 * N) % p : ℕ) : ℤ) ≡ 2 * (N : ℤ) [ZMOD p] := by
          rw [Int.ModEq, ← Int.natCast_mod]
          norm_cast
          simp
        have hdvd2 : (p : ℤ) ∣ 2 * (N : ℤ) - (((2 * N) % p : ℕ) : ℤ) :=
          Int.modEq_iff_dvd.mp hmod
        exact dvd_mul_of_dvd_right hdvd2 _
  rw [htr]
  have hdvd_2N : p ∣ 2 * N ↔ p = 2 ∨ p ∣ N := by
    rw [hp.dvd_mul]
    constructor
    · rintro (h | h)
      · left
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h with h1 | h2
        · exact (hp.ne_one h1).elim
        · exact h2
      · right; exact h
    · rintro (rfl | h); exact Or.inl dvd_rfl; exact Or.inr h
  by_cases hcond : p = 2 ∨ p ∣ N
  · have hmod0 : (2 * N) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp (hdvd_2N.mpr hcond)
    simp [hcond, hmod0]
  · have hne : 0 ≠ (2 * N) % p := by
      intro heq
      exact hcond (hdvd_2N.mp (Nat.dvd_iff_mod_eq_zero.mpr heq.symm))
    simp [hcond, Finset.card_pair hne]

private lemma card_goldbachRootsNat_mul (N : ℕ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m.Coprime n) :
    (goldbachRootsNat N (m * n)).card =
      (goldbachRootsNat N m).card * (goldbachRootsNat N n).card := by
  have hbij : (goldbachRootsNat N (m * n)).card =
      ((goldbachRootsNat N m) ×ˢ (goldbachRootsNat N n)).card := by
    refine Finset.card_bij (fun r _ => (r % m, r % n)) ?_ ?_ ?_
    · intro r hr
      simp only [goldbachRootsNat, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hr ⊢
      have hdiv : ∀ d : ℕ, d ∣ m * n →
          (d : ℤ) ∣ ((r % d : ℕ) : ℤ) * (2 * (N : ℤ) - ((r % d : ℕ) : ℤ)) := by
        intro d hdm
        have hdZ : (d : ℤ) ∣ (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)) :=
          dvd_trans (Int.natCast_dvd_natCast.mpr hdm) hr.2
        have hmod : (r : ℤ) ≡ ((r % d : ℕ) : ℤ) [ZMOD d] := by
          rw [Int.ModEq, Int.ofNat_mod_ofNat]; simp
        have hnd : (d : ℤ) ∣ (r : ℤ) - ((r % d : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hmod.symm
        have hfac : (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)) -
            ((r % d : ℕ) : ℤ) * (2 * (N : ℤ) - ((r % d : ℕ) : ℤ)) =
            ((r : ℤ) - ((r % d : ℕ) : ℤ)) * (2 * (N : ℤ) - (r : ℤ) - ((r % d : ℕ) : ℤ)) := by ring
        have hsub := dvd_sub hdZ (hfac ▸ dvd_mul_of_dvd_left hnd _)
        simpa using hsub
      exact ⟨⟨Nat.mod_lt r hm, hdiv m (dvd_mul_right m n)⟩,
        ⟨Nat.mod_lt r hn, hdiv n (dvd_mul_left n m)⟩⟩
    · intro r₁ hr₁ r₂ hr₂ heq
      have hr₁_lt : r₁ < m * n := Finset.mem_range.mp (Finset.mem_filter.mp hr₁).1
      have hr₂_lt : r₂ < m * n := Finset.mem_range.mp (Finset.mem_filter.mp hr₂).1
      have hpeq := Prod.ext_iff.mp heq
      have hmod : r₁ ≡ r₂ [MOD m * n] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨hpeq.1, hpeq.2⟩
      change r₁ % (m * n) = r₂ % (m * n) at hmod
      rwa [Nat.mod_eq_of_lt hr₁_lt, Nat.mod_eq_of_lt hr₂_lt] at hmod
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_product, goldbachRootsNat, Finset.mem_filter, Finset.mem_range] at hab
      have : NeZero m := ⟨hm.ne'⟩
      have : NeZero n := ⟨hn.ne'⟩
      have : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
      let e := ZMod.chineseRemainder hmn
      let r : ℕ := (e.symm ((a : ZMod m), (b : ZMod n))).val
      have hr_lt : r < m * n := ZMod.val_lt _
      have hre : e (r : ZMod (m * n)) = ((a : ZMod m), (b : ZMod n)) := by
        dsimp [r]; rw [ZMod.natCast_zmod_val, e.apply_symm_apply]
      have he_nat : e (r : ZMod (m * n)) = ((r : ZMod m), (r : ZMod n)) := by
        rw [map_natCast]; rfl
      rw [he_nat, Prod.ext_iff] at hre
      have hrm : r % m = a := by
        have hmod : r ≡ a [MOD m] := (ZMod.natCast_eq_natCast_iff r a m).mp hre.1
        change r % m = a % m at hmod
        rwa [Nat.mod_eq_of_lt hab.1.1] at hmod
      have hrn : r % n = b := by
        have hmod : r ≡ b [MOD n] := (ZMod.natCast_eq_natCast_iff r b n).mp hre.2
        change r % n = b % n at hmod
        rwa [Nat.mod_eq_of_lt hab.2.1] at hmod
      refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr_lt, ?_⟩, Prod.ext hrm hrn⟩
      have hdvd_of_mod : ∀ d x : ℕ, x < d → r % d = x →
          (d : ℤ) ∣ (x : ℤ) * (2 * (N : ℤ) - (x : ℤ)) →
          (d : ℤ) ∣ (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)) := by
        intro d x hxd hrx hx_dvd
        have hmod : (r : ℤ) ≡ (x : ℤ) [ZMOD d] := by
          rw [Int.ModEq]
          norm_cast
          rw [hrx, Nat.mod_eq_of_lt hxd]
        have hnd : (d : ℤ) ∣ (r : ℤ) - (x : ℤ) := Int.modEq_iff_dvd.mp hmod.symm
        have hfac : (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)) -
            (x : ℤ) * (2 * (N : ℤ) - (x : ℤ)) =
            ((r : ℤ) - (x : ℤ)) * (2 * (N : ℤ) - (r : ℤ) - (x : ℤ)) := by ring
        have hadd := dvd_add (hfac ▸ dvd_mul_of_dvd_left hnd _) hx_dvd
        simpa using hadd
      have hmZ : (m : ℤ) ∣ (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)) :=
        hdvd_of_mod m a hab.1.1 hrm hab.1.2
      have hnZ : (n : ℤ) ∣ (r : ℤ) * (2 * (N : ℤ) - (r : ℤ)) :=
        hdvd_of_mod n b hab.2.1 hrn hab.2.2
      have hcopZ : IsCoprime (m : ℤ) (n : ℤ) := by
        refine ⟨Int.gcdA m n, Int.gcdB m n, ?_⟩
        have hbez := Int.gcd_eq_gcd_ab (m : ℤ) (n : ℤ)
        have hgcd1 : Int.gcd (m : ℤ) (n : ℤ) = 1 := by
          change m.gcd n = 1
          exact hmn.gcd_eq_one
        rw [hgcd1] at hbez
        push_cast at hbez
        linarith [mul_comm (m : ℤ) (Int.gcdA m n), mul_comm (n : ℤ) (Int.gcdB m n)]
      have hmulZ := hcopZ.mul_dvd hmZ hnZ
      simpa [Nat.cast_mul] using hmulZ
  rw [hbij, Finset.card_product]

private lemma card_goldbachRootsNat_eq_omega (N : ℕ) {d : ℕ} (hd : Squarefree d) :
    ((goldbachRootsNat N d).card : ℝ) = goldbachOmega N d := by
  have hd_nat : ∀ k : ℕ, Squarefree k →
      (goldbachRootsNat N k).card = ∏ p ∈ k.primeFactors, (if p = 2 ∨ p ∣ N then 1 else 2) := by
    intro k
    induction k using Nat.strong_induction_on with | ind k ih =>
    intro hk
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk.ne_zero
    by_cases hk1 : k = 1
    · subst hk1
      have htr : goldbachRootsNat N 1 = {0} := by ext r; simp [goldbachRootsNat]
      simp [htr]
    · let p := k.minFac
      have hp : p.Prime := Nat.minFac_prime hk1
      have hpk : p ∣ k := Nat.minFac_dvd k
      let m := k / p
      have hkm : p * m = k := Nat.mul_div_cancel' hpk
      have hm_sq : Squarefree m := hk.squarefree_of_dvd (Nat.div_dvd_of_dvd hpk)
      have hm_lt : m < k := Nat.div_lt_self hk_pos hp.one_lt
      have hcop : p.Coprime m := (Nat.squarefree_mul_iff.mp (hkm.symm ▸ hk)).1
      have hpf : k.primeFactors = insert p m.primeFactors := by
        rw [← hkm, Nat.Coprime.primeFactors_mul hcop, Nat.Prime.primeFactors hp]
        ext q; simp [Finset.mem_insert]
      have hp_not : p ∉ m.primeFactors := fun hmem =>
        hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem) dvd_rfl))
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sq.ne_zero
      rw [← hkm, card_goldbachRootsNat_mul N hp.pos hm_pos hcop, card_goldbachRootsNat_prime N hp,
        ih m hm_lt hm_sq, hkm, hpf, Finset.prod_insert hp_not]
  rw [hd_nat d hd, goldbachOmega_apply_ne_zero N hd.ne_zero]
  push_cast; rfl

private lemma injOn_goldbachProd (N : ℕ) :
    Set.InjOn (fun n : ℕ => n * (2 * N - n)) (Finset.Icc 1 N : Set ℕ) := by
  have hmono : StrictMonoOn (fun n : ℕ => n * (2 * N - n)) (Finset.Icc 1 N : Set ℕ) := by
    intro a ha b hb hab
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
    have hbN : b ≤ N := (Finset.mem_Icc.mp hb).2
    have ha2N : a ≤ 2 * N := by omega
    have hb2N : b ≤ 2 * N := by omega
    zify [ha2N, hb2N]
    nlinarith
  exact hmono.injOn

/-- Remainder bound for `goldbachSieve`: for any squarefree `d`,
`|(goldbachSieve N z).rem d| ≤ goldbachOmega N d`. -/
theorem abs_goldbachSieve_rem_le (N : ℕ) (z : ℝ) {d : ℕ} (hd : Squarefree d) :
    |(goldbachSieve N z).rem d| ≤ goldbachOmega N d := by
  have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero hd.ne_zero
  have hdR_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have himg : ((goldbachSieve N z).support.filter (d ∣ ·)) =
      ((Finset.Icc 1 N).filter (fun n => d ∣ n * (2 * N - n))).image
        (fun n => n * (2 * N - n)) := by
    ext m
    dsimp [goldbachSieve, mkBoundingSieveOfOmega]
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hdvd⟩; exact ⟨n, ⟨hn, hdvd⟩, rfl⟩
    · rintro ⟨n, ⟨hn, hdvd⟩, rfl⟩; exact ⟨⟨n, hn, rfl⟩, hdvd⟩
  have hinj : Set.InjOn (fun n : ℕ => n * (2 * N - n))
      (((Finset.Icc 1 N).filter (fun n => d ∣ n * (2 * N - n))) : Set ℕ) :=
    (injOn_goldbachProd N).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hmult : (goldbachSieve N z).multSum d =
      (((Finset.Icc 1 N).filter (fun n => d ∣ n * (2 * N - n))).card : ℝ) := by
    rw [multSum_eq_card_of_weights_one (fun _ => rfl), himg, Finset.card_image_of_injOn hinj]
  have hnu_tot : (goldbachSieve N z).nu d * (goldbachSieve N z).totalMass =
      (goldbachOmega N d / (d : ℝ)) * (N : ℝ) := by
    dsimp [goldbachSieve, mkBoundingSieveOfOmega]
    rw [selbergDensityOmega_apply hd.ne_zero]
  unfold BoundingSieve.rem
  rw [hmult, hnu_tot]
  have hpart :
      ((Finset.Icc 1 N).filter (fun n => d ∣ n * (2 * N - n))).card =
        ∑ r ∈ goldbachRootsNat N d, ((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card := by
    have hmaps : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (2 * N - n)),
        n % d ∈ goldbachRootsNat N d := fun n hn =>
      (dvd_goldbach_iff_mem_roots hd_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2).mp
        (Finset.mem_filter.mp hn).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun r hr => ?_
    congr 1; ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hn1, hnN⟩, _⟩, hnr⟩; exact ⟨⟨hn1, hnN⟩, hnr⟩
    · rintro ⟨⟨hn1, hnN⟩, hnr⟩
      exact ⟨⟨⟨hn1, hnN⟩, (dvd_goldbach_iff_mem_roots hd_pos hnN).mpr (hnr ▸ hr)⟩, hnr⟩
  have hfiber_bd : ∀ r ∈ goldbachRootsNat N d,
      |(((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
    intro r hr
    have hr_lt : r < d := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hbd := card_Icc_mod_eq_bounds hd_pos N r hr_lt
    have hdiv_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdR_pos]; exact_mod_cast Nat.div_mul_le_self N d
    have hlt_div : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdR_pos]
      have hdm := Nat.div_add_mod N d
      have hmod := Nat.mod_lt N hd_pos
      have hnat : N < (N / d + 1) * d := by nlinarith
      exact_mod_cast hnat
    rw [abs_le]; constructor <;> linarith
  have hsum_eq :
      (goldbachOmega N d / (d : ℝ)) * (N : ℝ) = ∑ _r ∈ goldbachRootsNat N d, (N : ℝ) / (d : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, card_goldbachRootsNat_eq_omega N hd]; ring
  rw [hpart, Nat.cast_sum, hsum_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ goldbachRootsNat N d, ((((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) -
        (N : ℝ) / (d : ℝ))|
        ≤ ∑ r ∈ goldbachRootsNat N d, |(((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) -
            (N : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ goldbachRootsNat N d, (1 : ℝ) := Finset.sum_le_sum fun r hr => hfiber_bd r hr
    _ = goldbachOmega N d := by simp [card_goldbachRootsNat_eq_omega N hd]

private lemma prod_one_le_of_one_le {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 1 ≤ f a) : 1 ≤ ∏ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact one_le_mul_of_one_le_of_one_le (hf a (Finset.mem_insert_self a s))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

private lemma sum_divisors_eq_prod_one_add (f : ℕ → ℝ) (hf_one : f 1 = 1)
    (hf_mul : ∀ {a b : ℕ}, a.Coprime b → f (a * b) = f a * f b) :
    ∀ P : ℕ, Squarefree P → ∑ t ∈ P.divisors, f t = ∏ p ∈ P.primeFactors, (1 + f p) := by
  intro P
  induction P using Nat.strong_induction_on with | ind P ih =>
  intro hP
  by_cases hP1 : P = 1
  · subst hP1; simp [hf_one]
  · have hP_pos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
    let p := P.minFac
    have hp : p.Prime := Nat.minFac_prime hP1
    have hpP : p ∣ P := Nat.minFac_dvd P
    let m := P / p
    have hpm : p * m = P := Nat.mul_div_cancel' hpP
    have hm_sq : Squarefree m := hP.squarefree_of_dvd (Nat.div_dvd_of_dvd hpP)
    have hm_lt : m < P := Nat.div_lt_self hP_pos hp.one_lt
    have hcop : p.Coprime m := (Nat.squarefree_mul_iff.mp (hpm.symm ▸ hP)).1
    have hp_not_m : ¬ p ∣ m := fun h => hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd h dvd_rfl))
    have hpf : P.primeFactors = insert p m.primeFactors := by
      rw [← hpm, hcop.primeFactors_mul, hp.primeFactors]
      ext q; simp [Finset.mem_insert]
    have hp_not_pf : p ∉ m.primeFactors := fun hmem =>
      hp_not_m (Nat.dvd_of_mem_primeFactors hmem)
    have hdiv_eq : P.divisors = m.divisors ∪ m.divisors.image (p * ·) := by
      ext d
      simp only [Nat.mem_divisors, ne_eq, hP.ne_zero, hm_sq.ne_zero, not_false_eq_true,
        and_true, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hdP
        by_cases hpd : p ∣ d
        · right
          refine ⟨d / p, ?_, Nat.mul_div_cancel' hpd⟩
          have : p * (d / p) ∣ p * m := by rwa [Nat.mul_div_cancel' hpd, hpm]
          exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
        · left
          rw [← hpm] at hdP
          exact (hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left hdP
      · rintro (hdm | ⟨r, hrm, rfl⟩)
        · exact hdm.trans (hpm ▸ dvd_mul_left m p)
        · exact hpm ▸ Nat.mul_dvd_mul_left p hrm
    have hdisj : Disjoint m.divisors (m.divisors.image (p * ·)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rcases Finset.mem_image.mp hd2 with ⟨r, _, rfl⟩
      exact hp_not_m ((dvd_mul_right p r).trans (Nat.dvd_of_mem_divisors hd1))
    have hinj : Set.InjOn (fun r => p * r) (m.divisors : Set ℕ) :=
      fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq
    rw [hdiv_eq, Finset.sum_union hdisj, Finset.sum_image hinj]
    have hterm : ∑ r ∈ m.divisors, f (p * r) = f p * ∑ r ∈ m.divisors, f r := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr =>
        hf_mul (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hr))
    rw [hterm, ih m hm_lt hm_sq, hpf, Finset.prod_insert hp_not_pf]
    ring

private lemma squarefree_and_primeFactors_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) ∧ (∏ p ∈ s, p).primeFactors = s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp_not ih =>
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    rcases ih hs' with ⟨ih_sq, ih_pf⟩
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (hp.coprime_iff_not_dvd).mpr fun hqp => hp_not (by
        rcases (Nat.dvd_prime (hs' q hq)).mp hqp with h1 | rfl
        · exact absurd h1 hp.ne_one
        · exact hq)
    have hp_sq : Squarefree p := by
      rintro d ⟨k, hk⟩
      rcases (Nat.dvd_prime hp).mp ⟨d * k, by rw [hk]; ring⟩ with h1 | hdp
      · exact Nat.isUnit_iff.mpr h1
      · rw [hdp] at hk
        have hk_pos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
          simp [hk0] at hk
          exact hp.ne_zero hk
        have hle : p * p ≤ p := by
          calc
            p * p = p * p * 1 := (mul_one _).symm
            _ ≤ p * p * k := Nat.mul_le_mul_left (p * p) hk_pos
            _ = p := hk.symm
        have hlt : p < p * p := by
          simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
        omega
    rw [Finset.prod_insert hp_not]
    refine ⟨Nat.squarefree_mul_iff.mpr ⟨hcop, hp_sq, ih_sq⟩, ?_⟩
    rw [hcop.primeFactors_mul, hp.primeFactors, ih_pf]
    ext q
    simp [Finset.mem_insert]

private lemma selbergTerms_twin_gcd_decomp (N : ℕ) (hN : N ≠ 0) (z : ℝ)
    (Nz : ℕ) (hNz_sq : Squarefree Nz)
    (hNz_pf : Nz.primeFactors = N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ z))
    (h : ℕ → ℝ) (hh_one : h 1 = 1) (hh_mul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b)
    (hh_prime : ∀ p : ℕ, h p = ∏ q ∈ p.primeFactors, ((q : ℝ) - 2)⁻¹)
    {k : ℕ} (hkP : k ∣ (selbergTwinSieve 1 z).prodPrimes) :
    (selbergTwinSieve 1 z).selbergTerms k =
      ∑ t ∈ (k.gcd Nz).divisors, ∑ a ∈ (k.gcd Nz).divisors,
        if a.lcm t = k.gcd Nz then (goldbachSieve N z).selbergTerms (k / k.gcd Nz * a) * h t else 0 := by
    let st := selbergTwinSieve 1 z
    let sg := goldbachSieve N z
    let r := k.gcd Nz
    let k₀ := k / r
    have hkr : k₀ * r = k := Nat.div_mul_cancel (Nat.gcd_dvd_left k Nz)
    have hr_sq : Squarefree r := (st.squarefree_of_dvd_prodPrimes hkP).squarefree_of_dvd (Nat.gcd_dvd_left k Nz)
    have hcop_k0r : k₀.Coprime r := (Nat.squarefree_mul_iff.mp (hkr.symm ▸ st.squarefree_of_dvd_prodPrimes hkP)).1
    have hst_k : st.selbergTerms k = st.selbergTerms k₀ * st.selbergTerms r := by
      rw [← hkr]; exact st.selbergTerms_isMultiplicative.map_mul_of_coprime hcop_k0r
    have hst_k0 : st.selbergTerms k₀ = sg.selbergTerms k₀ := by
      have hk0_cop : k₀.Coprime Nz := by
        have hk0_nz : k₀ ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hkr
          exact (st.squarefree_of_dvd_prodPrimes hkP).ne_zero hkr.symm
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        have hpos : 0 < k₀.gcd Nz := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hk0_nz)
        let p := (k₀.gcd Nz).minFac
        have hp : p.Prime := Nat.minFac_prime hne
        have hpk0 : p ∣ k₀ := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
        have hpNz : p ∣ Nz := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
        have hpk : p ∣ k := hpk0.trans (hkr ▸ dvd_mul_right k₀ r)
        have hpr : p ∣ r := Nat.dvd_gcd hpk hpNz
        exact hp.ne_one (Nat.dvd_one.mp (hcop_k0r.symm ▸ Nat.dvd_gcd hpr hpk0))
      have hagree : ∀ p ∈ k₀.primeFactors, st.nu p = sg.nu p := by
        intro p hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hpk0 := Nat.dvd_of_mem_primeFactors hp
        have hpP : p ∣ st.prodPrimes := hpk0.trans ((hkr ▸ dvd_mul_right k₀ r).trans hkP)
        have hnot_Nz : ¬ p ∣ Nz := fun hdiv =>
          hp_prime.ne_one (Nat.dvd_one.mp (hk0_cop.symm ▸ Nat.dvd_gcd hdiv hpk0))
        have hle_z : (p : ℝ) ≤ z := (prime_dvd_selbergPrimeProd_iff hp_prime).mp hpP
        have hnot_cond : ¬ (p = 2 ∨ p ∣ N) → ¬ (p = 2 ∨ p ∣ N) := id
        by_cases hp2 : p = 2
        · subst hp2
          dsimp [st, sg, selbergTwinSieve, goldbachSieve, mkBoundingSieveOfOmega]
          rw [selbergDensityOmega_apply (by norm_num), selbergDensityOmega_apply (by norm_num),
            selbergTwinOmega_prime Nat.prime_two, goldbachOmega_prime N Nat.prime_two]
          simp
        · have hp_gt2 : 2 < p := by have := hp_prime.two_le; omega
          have hnot_N : ¬ p ∣ N := fun hpN =>
            hnot_Nz (Nat.dvd_of_mem_primeFactors (by
              rw [hNz_pf]
              exact Finset.mem_filter.mpr
                ⟨Nat.mem_primeFactors.mpr ⟨hp_prime, hpN, hN⟩, hp_gt2, hle_z⟩))
          dsimp [st, sg, selbergTwinSieve, goldbachSieve, mkBoundingSieveOfOmega]
          rw [selbergDensityOmega_apply hp_prime.ne_zero, selbergDensityOmega_apply hp_prime.ne_zero,
            selbergTwinOmega_prime hp_prime, goldbachOmega_prime N hp_prime]
          simp [hp2, hnot_N]
      have hnu_k0 : st.nu k₀ = sg.nu k₀ := by
        have hk0P : k₀ ∣ st.prodPrimes := (hkr ▸ dvd_mul_right k₀ r).trans hkP
        have hk0P' : k₀ ∣ sg.prodPrimes := hk0P
        rw [← st.prod_primeFactors_nu hk0P, ← sg.prod_primeFactors_nu hk0P']
        exact Finset.prod_congr rfl hagree
      rw [st.selbergTerms_apply k₀, sg.selbergTerms_apply k₀, hnu_k0]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hagree p hp]
    -- Expand `st.selbergTerms r` over `(a, t)` with `a.lcm t = r`
    have hsplit_r :
        st.selbergTerms r =
          ∑ a ∈ r.divisors, ∑ t ∈ r.divisors, (if a.lcm t = r then sg.selbergTerms a * h t else 0) := by
      have h1 := sum_divisors_lcm_eq_prod sg.selbergTerms h sg.selbergTerms_isMultiplicative.1 hh_one
        (fun h => sg.selbergTerms_isMultiplicative.map_mul_of_coprime h) (fun h => hh_mul h) r hr_sq
      rw [h1, st.selbergTerms_apply r,
        ← st.prod_primeFactors_nu (show r ∣ st.prodPrimes from (Nat.gcd_dvd_left k Nz).trans hkP),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hpr := Nat.dvd_of_mem_primeFactors hp
      have hpNz : p ∣ Nz := hpr.trans (Nat.gcd_dvd_right k Nz)
      have hp_mem : p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ z) := by
        rw [← hNz_pf]
        exact Nat.mem_primeFactors.mpr ⟨hp_prime, hpNz, hNz_sq.ne_zero⟩
      have hp_gt2 : 2 < p := (Finset.mem_filter.mp hp_mem).2.1
      have hp_N : p ∣ N := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp_mem).1
      have hp_ne2 : p ≠ 2 := by omega
      have hst_nu : st.nu p = 2 / (p : ℝ) := by
        dsimp [st, selbergTwinSieve, mkBoundingSieveOfOmega]
        rw [selbergDensityOmega_apply hp_prime.ne_zero, selbergTwinOmega_prime hp_prime]
        simp [hp_ne2]
      have hsg_nu : sg.nu p = 1 / (p : ℝ) := by
        dsimp [sg, goldbachSieve, mkBoundingSieveOfOmega]
        rw [selbergDensityOmega_apply hp_prime.ne_zero, goldbachOmega_prime N hp_prime]
        simp [hp_N]
      have hsg_term : sg.selbergTerms p = ((p : ℝ) - 1)⁻¹ := by
        rw [sg.selbergTerms_apply p, hp_prime.primeFactors, Finset.prod_singleton, hsg_nu]
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith [show (2 : ℝ) ≤ p from by exact_mod_cast hp_prime.two_le]
        field_simp [hp_pos.ne', hp1]
      have hh_term : h p = ((p : ℝ) - 2)⁻¹ := by
        rw [hh_prime p, hp_prime.primeFactors, Finset.prod_singleton]
      have hst_term : st.nu p * (1 - st.nu p)⁻¹ = 2 / ((p : ℝ) - 2) := by
        rw [hst_nu]
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
        have hp2_pos : (p : ℝ) - 2 ≠ 0 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
        field_simp [hp_pos.ne', hp2_pos]
      rw [hst_term, hsg_term, hh_term]
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
      have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
      field_simp [hp1, hp2]; ring
    rw [hst_k, hst_k0, hsplit_r]
    conv_lhs =>
      rw [Finset.mul_sum]
      arg 2; ext a; rw [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a ha => ?_
    have ha_cop : k₀.Coprime a := hcop_k0r.coprime_dvd_right (Nat.dvd_of_mem_divisors ha)
    have hsg_mul : sg.selbergTerms k₀ * (sg.selbergTerms a * h t) =
        sg.selbergTerms (k₀ * a) * h t := by
      rw [sg.selbergTerms_isMultiplicative.map_mul_of_coprime ha_cop]; ring
    rw [mul_ite, mul_zero, hsg_mul]

private lemma twin_goldbach_gcd_inj_maps (P_z Nz : ℕ) (hPz_sq : Squarefree P_z)
    (hNz_ne : Nz ≠ 0) (z : ℝ) :
    let S_z := P_z.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
    let F : ℕ → Finset (ℕ × ℕ) := fun k =>
      ((k.gcd Nz).divisors ×ˢ (k.gcd Nz).divisors).filter (fun ta => ta.2.lcm ta.1 = k.gcd Nz)
    let T : Finset (Σ _k : ℕ, ℕ × ℕ) := S_z.sigma F
    let φ : (Σ _k : ℕ, ℕ × ℕ) → ℕ × ℕ := fun x => (x.1 / x.1.gcd Nz * x.2.2, x.2.1)
    (∀ x ∈ T, φ x ∈ S_z ×ˢ Nz.divisors) ∧ Set.InjOn φ (T : Set (Σ _k : ℕ, ℕ × ℕ)) := by
  intro S_z F T φ
  have hmaps_T : ∀ x ∈ T, φ x ∈ S_z ×ˢ Nz.divisors := by
    rintro ⟨k, t, a⟩ hx
    rcases Finset.mem_sigma.mp hx with ⟨hk, hta⟩
    have hta' := Finset.mem_filter.mp hta
    have hta_prod := Finset.mem_product.mp hta'.1
    have ht_dvd : t ∣ k.gcd Nz := Nat.dvd_of_mem_divisors hta_prod.1
    have ha_dvd : a ∣ k.gcd Nz := Nat.dvd_of_mem_divisors hta_prod.2
    have hk' := Finset.mem_filter.mp hk
    have hkP : k ∣ P_z := Nat.dvd_of_mem_divisors hk'.1
    have hPz_ne : P_z ≠ 0 := hPz_sq.ne_zero
    have hk_pos : 0 < k := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hPz_ne hkP)
    let m := k / k.gcd Nz * a
    have hm_dvd_k : m ∣ k := by
      have : k / k.gcd Nz * a ∣ k / k.gcd Nz * k.gcd Nz := Nat.mul_dvd_mul_left _ ha_dvd
      rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left k Nz)] at this
    have hm_le_k : m ≤ k := Nat.le_of_dvd hk_pos hm_dvd_k
    have hmP : m ∣ P_z := hm_dvd_k.trans hkP
    have hm_mem : m ∈ S_z := Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hmP, hPz_ne⟩,
        (by exact_mod_cast hm_le_k : (m : ℝ) ≤ (k : ℝ)).trans hk'.2⟩
    have ht_mem : t ∈ Nz.divisors :=
      Nat.mem_divisors.mpr ⟨ht_dvd.trans (Nat.gcd_dvd_right k Nz), hNz_ne⟩
    exact Finset.mem_product.mpr ⟨hm_mem, ht_mem⟩
  have hgcd_rec : ∀ k ∈ S_z, ∀ a : ℕ, a ∣ k.gcd Nz →
      (k / k.gcd Nz * a).gcd Nz = a := by
    intro k hk a ha_dvd
    have hkP : k ∣ P_z := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1
    have hk_sq : Squarefree k := hPz_sq.squarefree_of_dvd hkP
    have hkr : k / k.gcd Nz * k.gcd Nz = k := Nat.div_mul_cancel (Nat.gcd_dvd_left k Nz)
    have hcop_kr : (k / k.gcd Nz).Coprime (k.gcd Nz) :=
      (Nat.squarefree_mul_iff.mp (hkr.symm ▸ hk_sq)).1
    have hk0_cop : (k / k.gcd Nz).Coprime Nz := by
      have hk0_nz : k / k.gcd Nz ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hkr; exact hk_sq.ne_zero hkr.symm
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      let p := ((k / k.gcd Nz).gcd Nz).minFac
      have hp : p.Prime := Nat.minFac_prime hne
      have hpk0 : p ∣ k / k.gcd Nz := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hpNz : p ∣ Nz := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      have hpk : p ∣ k := hpk0.trans ((dvd_mul_right (k / k.gcd Nz) (k.gcd Nz)).trans hkr.dvd)
      have hpr : p ∣ k.gcd Nz := Nat.dvd_gcd hpk hpNz
      exact hp.ne_one (Nat.dvd_one.mp (hcop_kr.symm ▸ Nat.dvd_gcd hpr hpk0))
    have haNz : a ∣ Nz := ha_dvd.trans (Nat.gcd_dvd_right k Nz)
    have hc_cop : (k / k.gcd Nz).Coprime (Nz / a) :=
      hk0_cop.coprime_dvd_right (Nat.div_dvd_of_dvd haNz)
    calc
      (k / k.gcd Nz * a).gcd Nz
          = (a * (k / k.gcd Nz)).gcd (a * (Nz / a)) := by
              rw [mul_comm (k / k.gcd Nz) a, Nat.mul_div_cancel' haNz]
      _ = a * (k / k.gcd Nz).gcd (Nz / a) := Nat.gcd_mul_left _ _ _
      _ = a := by rw [hc_cop.gcd_eq_one, mul_one]
  have hinj_T : Set.InjOn φ (T : Set (Σ _k : ℕ, ℕ × ℕ)) := by
    rintro ⟨k₁, t₁, a₁⟩ h₁ ⟨k₂, t₂, a₂⟩ h₂ heq
    have h₁' := Finset.mem_sigma.mp h₁
    have h₂' := Finset.mem_sigma.mp h₂
    have hta₁ := Finset.mem_filter.mp h₁'.2
    have hta₂ := Finset.mem_filter.mp h₂'.2
    have ha₁_dvd : a₁ ∣ k₁.gcd Nz := Nat.dvd_of_mem_divisors (Finset.mem_product.mp hta₁.1).2
    have ha₂_dvd : a₂ ∣ k₂.gcd Nz := Nat.dvd_of_mem_divisors (Finset.mem_product.mp hta₂.1).2
    have heq' := Prod.ext_iff.mp heq
    have ht_eq : t₁ = t₂ := heq'.2
    have hm_eq : k₁ / k₁.gcd Nz * a₁ = k₂ / k₂.gcd Nz * a₂ := heq'.1
    have ha_eq : a₁ = a₂ := by
      have hg1 := hgcd_rec k₁ h₁'.1 a₁ ha₁_dvd
      have hg2 := hgcd_rec k₂ h₂'.1 a₂ ha₂_dvd
      rw [← hg1, ← hg2, hm_eq]
    have ha₁_pos : 0 < a₁ := Nat.pos_of_ne_zero (by
      intro ha0; rw [ha0] at ha₁_dvd
      have hk1_pos : 0 < k₁.gcd Nz := Nat.gcd_pos_of_pos_right k₁ (Nat.pos_of_ne_zero hNz_ne)
      exact hk1_pos.ne' (Nat.zero_dvd.mp ha₁_dvd))
    have hk0_eq : k₁ / k₁.gcd Nz = k₂ / k₂.gcd Nz :=
      Nat.eq_of_mul_eq_mul_right ha₁_pos (ha_eq ▸ hm_eq)
    have hgcd_eq : k₁.gcd Nz = k₂.gcd Nz := by
      rw [← hta₁.2, ← hta₂.2, ha_eq, ht_eq]
    have hk_eq : k₁ = k₂ := by
      calc
        k₁ = k₁ / k₁.gcd Nz * k₁.gcd Nz := (Nat.div_mul_cancel (Nat.gcd_dvd_left k₁ Nz)).symm
        _ = k₂ / k₂.gcd Nz * k₂.gcd Nz := by rw [hk0_eq, hgcd_eq]
        _ = k₂ := Nat.div_mul_cancel (Nat.gcd_dvd_left k₂ Nz)
    subst hk_eq; subst ht_eq; subst ha_eq
    rfl
  exact ⟨hmaps_T, hinj_T⟩

set_option maxHeartbeats 4000000 in
/-- Relating `selbergG (selbergTwinSieve 1 z) z` to `selbergG (goldbachSieve N z) z` via the
singular series factor `∏_{p ∣ N, p > 2} (1 + 1 / (p - 2))` for nonzero `N`. -/
theorem selbergG_twin_le_goldbach_mul_singular (N : ℕ) (hN : N ≠ 0) {z : ℝ} (_hz : 1 ≤ z) :
    selbergG (selbergTwinSieve 1 z) z ≤
      selbergG (goldbachSieve N z) z *
        ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
  let st := selbergTwinSieve 1 z
  let sg := goldbachSieve N z
  let Nz : ℕ := ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ z), p
  have hNz_aux : Squarefree Nz ∧ Nz.primeFactors = N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ z) :=
    squarefree_and_primeFactors_prod_primes _ fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hNz_sq : Squarefree Nz := hNz_aux.1
  have hNz_pf : Nz.primeFactors = N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ z) :=
    hNz_aux.2
  let h : ℕ → ℝ := fun t => ∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹
  have hh_one : h 1 = 1 := by simp [h]
  have hh_mul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b := by
    intro a b hcop
    simp only [h, hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors]
  let P_z := selbergPrimeProd z
  have hst_P : st.prodPrimes = P_z := rfl
  have hsg_P : sg.prodPrimes = P_z := rfl
  let S_z := P_z.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
  have hst_sum_eq :
      selbergG st z =
        ∑ k ∈ S_z, ∑ t ∈ (k.gcd Nz).divisors,
          ∑ a ∈ (k.gcd Nz).divisors,
            if a.lcm t = k.gcd Nz then sg.selbergTerms (k / k.gcd Nz * a) * h t else 0 := by
    unfold selbergG
    rw [hst_P]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact selbergTerms_twin_gcd_decomp N hN z Nz hNz_sq hNz_pf h hh_one (fun hc => hh_mul hc)
      (fun _ => rfl) (hst_P.symm ▸ Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1)
  let F : ℕ → Finset (ℕ × ℕ) := fun k =>
    ((k.gcd Nz).divisors ×ˢ (k.gcd Nz).divisors).filter (fun ta => ta.2.lcm ta.1 = k.gcd Nz)
  let T : Finset (Σ k : ℕ, ℕ × ℕ) := S_z.sigma F
  have hT_eq :
      selbergG st z =
        ∑ x ∈ T, sg.selbergTerms (x.1 / x.1.gcd Nz * x.2.2) * h x.2.1 := by
    rw [hst_sum_eq, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [F]
    rw [Finset.sum_filter, Finset.sum_product]
  let φ : (Σ _k : ℕ, ℕ × ℕ) → ℕ × ℕ := fun x => (x.1 / x.1.gcd Nz * x.2.2, x.2.1)
  have hgcd_helper := twin_goldbach_gcd_inj_maps P_z Nz (selbergPrimeProd_squarefree z) hNz_sq.ne_zero z
  have hmaps_T : ∀ x ∈ T, φ x ∈ S_z ×ˢ Nz.divisors := hgcd_helper.1
  have hinj_T : Set.InjOn φ (T : Set (Σ _k : ℕ, ℕ × ℕ)) := hgcd_helper.2
  have hprod_sum :
      ∑ y ∈ S_z ×ˢ Nz.divisors, sg.selbergTerms y.1 * h y.2 =
        selbergG sg z * ∑ t ∈ Nz.divisors, h t := by
    rw [Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum]
    unfold selbergG
    rw [hsg_P]
  have hh_div : ∑ t ∈ Nz.divisors, h t =
      ∏ p ∈ Nz.primeFactors, (1 + 1 / ((p : ℝ) - 2)) := by
    rw [sum_divisors_eq_prod_one_add h hh_one (fun hc => hh_mul hc) Nz hNz_sq]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    dsimp [h]
    rw [hp_prime.primeFactors, Finset.prod_singleton, one_div]
  have hsub_pf : Nz.primeFactors ⊆ N.primeFactors.filter (fun p => 2 < p) := by
    rw [hNz_pf]
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
  have hprod_le :
      ∏ p ∈ Nz.primeFactors, (1 + 1 / ((p : ℝ) - 2)) ≤
        ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
    let R := (N.primeFactors.filter (fun p => 2 < p)) \ Nz.primeFactors
    have hunion : Nz.primeFactors ∪ R = N.primeFactors.filter (fun p => 2 < p) :=
      Finset.union_sdiff_of_subset hsub_pf
    have hdisj : Disjoint Nz.primeFactors R := Finset.disjoint_sdiff
    have hR_ge1 : 1 ≤ ∏ p ∈ R, (1 + 1 / ((p : ℝ) - 2)) := by
      refine prod_one_le_of_one_le _ _ fun p hp => ?_
      have hp_gt2 : 2 < p := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
      have : (0 : ℝ) < (p : ℝ) - 2 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
      linarith [div_nonneg zero_le_one this.le]
    have hNz_nn : 0 ≤ ∏ p ∈ Nz.primeFactors, (1 + 1 / ((p : ℝ) - 2)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp_gt2 : 2 < p := (Finset.mem_filter.mp (hsub_pf hp)).2
      have : (0 : ℝ) < (p : ℝ) - 2 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
      positivity
    rw [← hunion, Finset.prod_union hdisj]
    exact le_mul_of_one_le_right hNz_nn hR_ge1
  have hterm_nn : ∀ y ∈ S_z ×ˢ Nz.divisors, 0 ≤ sg.selbergTerms y.1 * h y.2 := by
    rintro ⟨m, t⟩ hy
    have hy' := Finset.mem_product.mp hy
    have hm_nn : 0 ≤ sg.selbergTerms m :=
      selbergTerms_nonneg_of_mem (hsg_P.symm ▸ (Finset.mem_filter.mp hy'.1).1)
    have ht_nn : 0 ≤ h t := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp_dvd : p ∣ Nz := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.dvd_of_mem_divisors hy'.2)
      have hp_mem : p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ z) := by
        rw [← hNz_pf]
        exact Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hp, hp_dvd, hNz_sq.ne_zero⟩
      have hp_gt2 : 2 < p := (Finset.mem_filter.mp hp_mem).2.1
      have : (0 : ℝ) < (p : ℝ) - 2 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
      exact inv_nonneg.mpr this.le
    exact mul_nonneg hm_nn ht_nn
  have hsub_img : T.image φ ⊆ S_z ×ˢ Nz.divisors := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hmaps_T x hx
  calc
    selbergG st z = ∑ x ∈ T, sg.selbergTerms (φ x).1 * h (φ x).2 := hT_eq
    _ = ∑ y ∈ T.image φ, sg.selbergTerms y.1 * h y.2 := by rw [Finset.sum_image hinj_T]
    _ ≤ ∑ y ∈ S_z ×ˢ Nz.divisors, sg.selbergTerms y.1 * h y.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_img (fun y hy _ => hterm_nn y hy)
    _ = selbergG sg z * ∑ t ∈ Nz.divisors, h t := hprod_sum
    _ = selbergG sg z * ∏ p ∈ Nz.primeFactors, (1 + 1 / ((p : ℝ) - 2)) := by rw [hh_div]
    _ ≤ selbergG sg z * ∏ p ∈ N.primeFactors.filter (fun p => 2 < p),
          (1 + 1 / ((p : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left hprod_le (selbergG_nonneg sg z)

/-- **Binary Goldbach Upper Bound via the Selberg Sieve**:
there exists a positive constant `C` such that for every integer `N ≥ 2`,
`r₂(2N) ≤ C * (N / (log N)^2) * ∏_{p ∣ N, p > 2} (1 + 1 / (p - 2))`. -/
theorem selberg_goldbach_upper_bound :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      (goldbachRepCount (2 * N) : ℝ) ≤
        C * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) *
          ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
  let N₀ : ℕ := 1024
  let C_lg : ℝ := 1200
  let C_sm : ℝ := 2 * (Real.log (N₀ : ℝ)) ^ 2
  let C : ℝ := max C_lg C_sm
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num [C_lg]) (le_max_left _ _)
  refine ⟨C, hC_pos, fun N hN => ?_⟩
  let S_N := ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))
  have hS_ge1 : 1 ≤ S_N := by
    refine prod_one_le_of_one_le _ _ fun p hp => ?_
    have hp_gt2 : 2 < p := (Finset.mem_filter.mp hp).2
    have : (0 : ℝ) < (p : ℝ) - 2 := by linarith [show (3 : ℝ) ≤ p from by exact_mod_cast hp_gt2]
    linarith [div_nonneg zero_le_one this.le]
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  by_cases hbig : N₀ ≤ N
  · let x : ℝ := (N : ℝ)
    have hx_ge : (1024 : ℝ) ≤ x := by dsimp [x, N₀] at *; exact_mod_cast (hbig : 1024 ≤ N)
    have hx_pos : 0 < x := by linarith
    let z : ℝ := x ^ (1 / 5 : ℝ)
    have hz_ge4 : 4 ≤ z := by
      have hx_ge45 : (4 : ℝ) ^ (5 : ℕ) ≤ x := by linarith
      calc
        (4 : ℝ) = ((4 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ x ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) hx_ge45 (by norm_num)
    have hz_ge1 : 1 ≤ z := by linarith
    have hz_lt_x : z < x := by
      have h1 : x ^ (1 / 5 : ℝ) < x ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
      simpa [z] using h1
    let sg := goldbachSieve N z
    have hrep_le : (goldbachRepCount (2 * N) : ℝ) ≤ 2 * (z + sg.siftedSum) := by
      unfold goldbachRepCount
      let P_all := (Finset.Icc 1 (2 * N)).filter (fun p => p.Prime ∧ (2 * N - p).Prime)
      let P_lo := (Finset.Icc 1 N).filter (fun p => p.Prime ∧ (2 * N - p).Prime)
      let P_hi := P_all.filter (fun p => N < p)
      have hpart : P_all.card ≤ P_lo.card + P_hi.card := by
        have hsub : P_all ⊆ P_lo ∪ P_hi := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hp_icc := Finset.mem_Icc.mp hp'.1
          by_cases hle : p ≤ N
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨hp_icc.1, hle⟩, hp'.2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, not_le.mp hle⟩)
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hhi_le : P_hi.card ≤ P_lo.card := by
        have hinj : Set.InjOn (fun p => 2 * N - p) (P_hi : Set ℕ) := by
          intro p₁ hp₁ p₂ hp₂ heq
          dsimp only at heq
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).1).2
          have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).1).2
          omega
        have himg : P_hi.image (fun p => 2 * N - p) ⊆ P_lo := by
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
          have hp' := Finset.mem_filter.mp hp
          have hp_all := Finset.mem_filter.mp hp'.1
          have hp_icc := Finset.mem_Icc.mp hp_all.1
          have hq_ge1 : 1 ≤ 2 * N - p := hp_all.2.2.one_le
          have hq_leN : 2 * N - p ≤ N := by have := hp'.2; omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq_ge1, hq_leN⟩, hp_all.2.2,
            by rw [show 2 * N - (2 * N - p) = p by omega]; exact hp_all.2.1⟩
        calc
          P_hi.card = (P_hi.image (fun p => 2 * N - p)).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ P_lo.card := Finset.card_le_card himg
      have hlo_le : (P_lo.card : ℝ) ≤ z + sg.siftedSum := by
        let P_sm := P_lo.filter (fun p : ℕ => (p : ℝ) ≤ z)
        let P_lg := P_lo.filter (fun p : ℕ => z < (p : ℝ))
        have hpart_lo : P_lo.card = P_sm.card + P_lg.card := by
          have h := P_lo.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ z)
          have hnot : P_lo.filter (fun p : ℕ => ¬ (p : ℝ) ≤ z) = P_lg := by ext p; simp [P_lg]
          rw [hnot] at h; exact h.symm
        have hsm_le : (P_sm.card : ℝ) ≤ z := by
          have hsub : P_sm ⊆ Finset.Icc 1 ⌊z⌋₊ := by
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp'.1).1).1,
              Nat.le_floor hp'.2⟩
          exact (by exact_mod_cast (Finset.card_le_card hsub).trans (by simp) :
            (P_sm.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
        have hlg_le : P_lg.card ≤ (sg.support.filter (fun m => Nat.Coprime sg.prodPrimes m)).card := by
          have hinj : Set.InjOn (fun p : ℕ => p * (2 * N - p)) (P_lg : Set ℕ) :=
            (injOn_goldbachProd N).mono (fun p hp =>
              (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
          have himg : P_lg.image (fun p => p * (2 * N - p)) ⊆
              sg.support.filter (fun m => Nat.Coprime sg.prodPrimes m) := by
            intro m hm
            rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
            have hp' := Finset.mem_filter.mp hp
            have hp_lo := Finset.mem_filter.mp hp'.1
            have hp_icc := Finset.mem_Icc.mp hp_lo.1
            have hq_gt : z < ((2 * N - p : ℕ) : ℝ) := by
              have h2Np : N ≤ 2 * N - p := by omega
              exact hz_lt_x.trans_le (by dsimp [x]; exact_mod_cast h2Np)
            have hcop : Nat.Coprime (selbergPrimeProd z) (p * (2 * N - p)) := by
              refine Nat.Coprime.mul_right ?_ ?_
              · exact coprime_selbergPrimeProd_of_prime_gt hp_lo.2.1 hp'.2
              · exact coprime_selbergPrimeProd_of_prime_gt hp_lo.2.2 hq_gt
            exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hp_lo.1, rfl⟩, hcop⟩
          calc
            P_lg.card = (P_lg.image (fun p => p * (2 * N - p))).card :=
                (Finset.card_image_of_injOn hinj).symm
            _ ≤ (sg.support.filter (fun m => Nat.Coprime sg.prodPrimes m)).card :=
                Finset.card_le_card himg
        rw [hpart_lo, Nat.cast_add, siftedSum_eq_card_of_weights_one (fun _ => rfl)]
        have hlgR : (P_lg.card : ℝ) ≤
            ((sg.support.filter (fun m => Nat.Coprime sg.prodPrimes m)).card : ℝ) := by
          exact_mod_cast hlg_le
        linarith
      have hcard_le : (P_all.card : ℝ) ≤ 2 * (P_lo.card : ℝ) := by
        have hnat : P_all.card ≤ 2 * P_lo.card := by omega
        exact_mod_cast hnat
      linarith
    have hGt_ge : (Real.log x) ^ 2 / 400 ≤ selbergG (selbergTwinSieve 1 z) z := by
      have hG1 := selbergG_twinSieve_ge_sq_log (x := 1) hz_ge4
      have hN_gt : Real.sqrt z < ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; exact Nat.lt_floor_add_one _
      have hsqrtz_eq : Real.sqrt z = x ^ (1 / 10 : ℝ) := by
        dsimp [z]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx_pos.le]
        congr 1; norm_num
      have hlog_ge : (1 / 10 : ℝ) * Real.log x ≤ Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ) := by
        have h1 : Real.log (x ^ (1 / 10 : ℝ)) ≤ Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hx_pos _) (hsqrtz_eq ▸ hN_gt.le)
        rwa [Real.log_rpow hx_pos] at h1
      have hsq_ge : ((1 / 10 : ℝ) * Real.log x) ^ 2 / 4 ≤
          (Real.log ((⌊Real.sqrt z⌋₊ + 1 : ℕ) : ℝ)) ^ 2 / 4 := by
        gcongr
      have heq : ((1 / 10 : ℝ) * Real.log x) ^ 2 / 4 = (Real.log x) ^ 2 / 400 := by ring
      linarith
    have hG_comp := selbergG_twin_le_goldbach_mul_singular N (by omega) hz_ge1
    have hinv_sg : (selbergG sg z)⁻¹ ≤ (400 / (Real.log x) ^ 2) * S_N := by
      have hsg_pos : 0 < selbergG sg z := selbergG_pos hz_ge1
      have hGt_pos : 0 < selbergG (selbergTwinSieve 1 z) z := selbergG_pos hz_ge1
      have h1 : (selbergG sg z)⁻¹ ≤ (selbergG (selbergTwinSieve 1 z) z)⁻¹ * S_N := by
        rw [inv_le_iff_one_le_mul₀ hsg_pos]
        calc
          1 = (selbergG (selbergTwinSieve 1 z) z)⁻¹ * selbergG (selbergTwinSieve 1 z) z :=
              (inv_mul_cancel₀ hGt_pos.ne').symm
          _ ≤ (selbergG (selbergTwinSieve 1 z) z)⁻¹ * (selbergG sg z * S_N) :=
              mul_le_mul_of_nonneg_left hG_comp (inv_pos.mpr hGt_pos).le
          _ = ((selbergG (selbergTwinSieve 1 z) z)⁻¹ * S_N) * selbergG sg z := by ring
      have h2 : (selbergG (selbergTwinSieve 1 z) z)⁻¹ ≤ 400 / (Real.log x) ^ 2 := by
        have hpos_lb : 0 < (Real.log x) ^ 2 / 400 := by positivity
        calc
          (selbergG (selbergTwinSieve 1 z) z)⁻¹ ≤ ((Real.log x) ^ 2 / 400)⁻¹ :=
              inv_anti₀ hpos_lb hGt_ge
          _ = 400 / (Real.log x) ^ 2 := by rw [inv_div]
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
    have hmain_le : sg.totalMass / selbergG sg z ≤ 400 * (x / (Real.log x) ^ 2) * S_N := by
      have hs_tot : sg.totalMass = x := rfl
      rw [hs_tot, div_eq_mul_inv]
      calc
        x * (selbergG sg z)⁻¹ ≤ x * ((400 / (Real.log x) ^ 2) * S_N) :=
            mul_le_mul_of_nonneg_left hinv_sg hx_pos.le
        _ = 400 * (x / (Real.log x) ^ 2) * S_N := by ring
    have herr_le :
        ∑ d₁ ∈ sg.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
          ∑ d₂ ∈ sg.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
            |sg.rem (d₁.lcm d₂)| ≤ z ^ 4 := by
      let D := sg.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
      have hD_sub : D ⊆ Finset.Icc 1 ⌊z⌋₊ := by
        intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero sg.prodPrimes_ne_zero
          (Nat.dvd_of_mem_divisors hd'.1))
        exact Finset.mem_Icc.mpr ⟨hd_pos, Nat.le_floor hd'.2⟩
      have hD_card : (D.card : ℝ) ≤ z :=
        (by exact_mod_cast (Finset.card_le_card hD_sub).trans (by simp) :
          (D.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
      have hterm_le : ∀ d₁ ∈ D, ∀ d₂ ∈ D, |sg.rem (d₁.lcm d₂)| ≤ z ^ 2 := by
        intro d₁ hd₁ d₂ hd₂
        have hd₁' := Finset.mem_filter.mp hd₁
        have hd₂' := Finset.mem_filter.mp hd₂
        have hlcmP : d₁.lcm d₂ ∣ sg.prodPrimes :=
          Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd₁'.1) (Nat.dvd_of_mem_divisors hd₂'.1)
        have hlcm_sq : Squarefree (d₁.lcm d₂) := sg.squarefree_of_dvd_prodPrimes hlcmP
        have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (hD_sub hd₁)).1
        have hd₂_pos : 0 < d₂ := (Finset.mem_Icc.mp (hD_sub hd₂)).1
        have hlcm_le : d₁.lcm d₂ ≤ d₁ * d₂ := Nat.le_of_dvd (Nat.mul_pos hd₁_pos hd₂_pos)
          (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
        calc
          |sg.rem (d₁.lcm d₂)| ≤ goldbachOmega N (d₁.lcm d₂) :=
              abs_goldbachSieve_rem_le N z hlcm_sq
          _ ≤ ((d₁.lcm d₂ : ℕ) : ℝ) := goldbachOmega_le_self N hlcm_sq
          _ ≤ ((d₁ * d₂ : ℕ) : ℝ) := by exact_mod_cast hlcm_le
          _ = (d₁ : ℝ) * (d₂ : ℝ) := by push_cast; rfl
          _ ≤ z * z := mul_le_mul hd₁'.2 hd₂'.2 (Nat.cast_nonneg _) (by linarith)
          _ = z ^ 2 := by ring
      calc
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, |sg.rem (d₁.lcm d₂)|
            ≤ ∑ _d₁ ∈ D, ∑ _d₂ ∈ D, z ^ 2 :=
              Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm_le d₁ hd₁ d₂ hd₂
        _ = (D.card : ℝ) ^ 2 * z ^ 2 := by simp; ring
        _ ≤ z ^ 2 * z ^ 2 := by gcongr
        _ = z ^ 4 := by ring
    have hz4_eq : z ^ 4 = x ^ (4 / 5 : ℝ) := by
      dsimp [z]; rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]; congr 1; norm_num
    have hz_le_z4 : z ≤ z ^ 4 := by
      have hz3 : 1 ≤ z ^ 3 := one_le_pow₀ hz_ge1
      calc
        z = z * 1 := (mul_one z).symm
        _ ≤ z * z ^ 3 := mul_le_mul_of_nonneg_left hz3 (by linarith)
        _ = z ^ 4 := by ring
    have hlogx_rpow : (Real.log x) ^ 2 ≤ 100 * x ^ (1 / 5 : ℝ) := by
      have hr_pos : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hx_pos _
      have h1 : Real.log (x ^ (1 / 10 : ℝ)) ≤ x ^ (1 / 10 : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hr_pos]
      rw [Real.log_rpow hx_pos] at h1
      have hlog_le : Real.log x ≤ 10 * x ^ (1 / 10 : ℝ) := by linarith
      have hsq_le : (Real.log x) ^ 2 ≤ (10 * x ^ (1 / 10 : ℝ)) ^ 2 := by gcongr
      have hpow2 : (x ^ (1 / 10 : ℝ)) ^ 2 = x ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]; congr 1; norm_num
      calc
        (Real.log x) ^ 2 ≤ (10 * x ^ (1 / 10 : ℝ)) ^ 2 := hsq_le
        _ = 100 * (x ^ (1 / 10 : ℝ)) ^ 2 := by ring
        _ = 100 * x ^ (1 / 5 : ℝ) := by rw [hpow2]
    have hz4_le_div : z ^ 4 ≤ 100 * (x / (Real.log x) ^ 2) * S_N := by
      have hdiv1 : z ^ 4 ≤ 100 * (x / (Real.log x) ^ 2) := by
        rw [hz4_eq, mul_div_assoc', le_div_iff₀ (sq_pos_of_pos hlogN_pos)]
        have hx_split : x ^ (4 / 5 : ℝ) * x ^ (1 / 5 : ℝ) = x := by
          rw [← Real.rpow_add hx_pos]; norm_num
        calc
          x ^ (4 / 5 : ℝ) * (Real.log x) ^ 2 ≤ x ^ (4 / 5 : ℝ) * (100 * x ^ (1 / 5 : ℝ)) := by
              gcongr
          _ = 100 * (x ^ (4 / 5 : ℝ) * x ^ (1 / 5 : ℝ)) := by ring
          _ = 100 * x := by rw [hx_split]
      exact hdiv1.trans (le_mul_of_one_le_right (by positivity) hS_ge1)
    have hup := selberg_upper_bound_simple sg hz_ge1
    have htot_le : (goldbachRepCount (2 * N) : ℝ) ≤ C_lg * (x / (Real.log x) ^ 2) * S_N := by
      calc
        (goldbachRepCount (2 * N) : ℝ) ≤ 2 * (z + sg.siftedSum) := hrep_le
        _ ≤ 2 * (z + (sg.totalMass / selbergG sg z +
              ∑ d₁ ∈ sg.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
                ∑ d₂ ∈ sg.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
                  |sg.rem (d₁.lcm d₂)|)) := by gcongr
        _ ≤ 2 * (z ^ 4 + (400 * (x / (Real.log x) ^ 2) * S_N + z ^ 4)) := by
            gcongr
        _ ≤ 2 * (100 * (x / (Real.log x) ^ 2) * S_N +
              (400 * (x / (Real.log x) ^ 2) * S_N + 100 * (x / (Real.log x) ^ 2) * S_N)) := by
            gcongr
        _ = C_lg * (x / (Real.log x) ^ 2) * S_N := by dsimp [C_lg]; ring
    exact htot_le.trans (by
      have hC_ge : C_lg ≤ C := le_max_left _ _
      gcongr)
  · have hlt : N < N₀ := not_le.mp hbig
    have hrep_le : (goldbachRepCount (2 * N) : ℝ) ≤ 2 * (N : ℝ) := by
      unfold goldbachRepCount
      have hle : ((Finset.Icc 1 (2 * N)).filter (fun p => p.Prime ∧ (2 * N - p).Prime)).card ≤ 2 * N :=
        (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast hle
    have hlog_le : Real.log (N : ℝ) ≤ Real.log (N₀ : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hlt.le)
    have h1 : 2 ≤ C_sm / (Real.log (N : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hlogN_pos)]
      dsimp [C_sm]
      gcongr
    have h2 : 2 * (N : ℝ) ≤ C_sm * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      calc
        2 * (N : ℝ) ≤ (C_sm / (Real.log (N : ℝ)) ^ 2) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
        _ = C_sm * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
    calc
      (goldbachRepCount (2 * N) : ℝ) ≤ 2 * (N : ℝ) := hrep_le
      _ ≤ C_sm * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := h2
      _ ≤ C_sm * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * S_N :=
          le_mul_of_one_le_right (by positivity) hS_ge1
      _ ≤ C * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * S_N := by
          have hC_ge : C_sm ≤ C := le_max_right _ _
          gcongr

end SelbergApplications

end AnalyticNumberTheory.SieveMethods
