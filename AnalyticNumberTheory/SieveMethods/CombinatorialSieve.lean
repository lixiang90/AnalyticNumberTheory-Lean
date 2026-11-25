import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Primorial

/-!
# Combinatorial Sieve Methods

This file develops the theory of combinatorial sieves and Brun's theorem on twin primes in the
namespace `AnalyticNumberTheory.SieveMethods`:

- General sieve setting (`SieveData`, `primeFinset`, `primeProd`, `primeProdLT`, `sieveMultiple`,
  `siftedCount`, `siftedCountOf`, sieve density `ω(d) / d`, remainder `r_d`, and Euler product
  `V(z)`).
- Exact **Legendre inclusion-exclusion** identity for `siftedCountOf` and `siftedCount`.
- General **upper and lower sieve weights** (`UpperSieveWeights`, `LowerSieveWeights`,
  `UpperSieveWeightsOn`, `LowerSieveWeightsOn`), fundamental sieve inequalities, and the exact
  sieve probability identity `∑_{d|P} λ(d) ν(d) = ∑_{n|P} prob(P, ν, n) ∑_{d|n} λ(d)`.
- **Brun's pure sieve** (Bonferroni truncation at `r` prime factors, with explicit factorial
  main-term bounds in `2m` and `2m + 1` as well as `(e * log V⁻¹ / r)^r` bounds).
- **Buchstab's identity** proved as an exact combinatorial identity for both `primeProdLT`
  (`∏_{p < z} p`) and `primeProd` (`∏_{p ≤ z} p`), as well as general prime finsets.
- **Rosser–Iwaniec combinatorial sieve weights** (`rosserWeightsPlus`, `rosserWeightsMinus`,
  `betaSieveUpper`, `betaSieveLower` with truncation `D_β(p_1 ... p_r) < y`), alternating upper
  and lower sieve bounds, support bounds `d < y`, and Buchstab recurrence.
- **Brun's theorem on twin primes**: `π₂(x) ≤ C * x * (log (log x))^2 / (log x)^2` and
  convergence of the sum of reciprocals of twin primes.
-/

noncomputable section

open Finset Filter Asymptotics
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Classical
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.SieveMethods

/-! ### General Sieve Setting -/

section SieveSetting

/-- The finite set of primes `p ≤ z`. -/
def primeFinset (z : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊z⌋₊

/-- The finite set of primes `p < z`. -/
def primeFinsetLT (z : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊z⌋₊).filter (fun p => (p : ℝ) < z)

/-- Membership in `primeFinset z` characterizes primes `p` with `(p : ℝ) ≤ z`. -/
theorem mem_primeFinset_iff {z : ℝ} {p : ℕ} :
    p ∈ primeFinset z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  unfold primeFinset
  rw [Nat.mem_primesLE]
  constructor
  · rintro ⟨hp_le, hp⟩
    refine ⟨hp, ?_⟩
    by_cases hz : 0 ≤ z
    · exact (Nat.le_floor_iff hz).mp hp_le
    · have hz_lt : z < 0 := lt_of_not_ge hz
      rw [Nat.floor_of_nonpos hz_lt.le] at hp_le
      have hp0 : p = 0 := Nat.le_zero.mp hp_le
      subst hp0
      exact absurd hp Nat.not_prime_zero
  · rintro ⟨hp, hpz⟩
    have hz : 0 ≤ z := le_trans (Nat.cast_nonneg p) hpz
    exact ⟨(Nat.le_floor_iff hz).mpr hpz, hp⟩

/-- Membership in `primeFinsetLT z` characterizes primes `p` with `(p : ℝ) < z`. -/
theorem mem_primeFinsetLT_iff {z : ℝ} {p : ℕ} :
    p ∈ primeFinsetLT z ↔ p.Prime ∧ (p : ℝ) < z := by
  unfold primeFinsetLT
  rw [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, hp⟩, hpz⟩
    exact ⟨hp, hpz⟩
  · rintro ⟨hp, hpz⟩
    have hz : 0 ≤ z := le_trans (Nat.cast_nonneg p) hpz.le
    exact ⟨⟨(Nat.le_floor_iff hz).mpr hpz.le, hp⟩, hpz⟩

/-- Every element of `primeFinset z` is prime. -/
theorem prime_of_mem_primeFinset {z : ℝ} {p : ℕ} (hp : p ∈ primeFinset z) : p.Prime :=
  (mem_primeFinset_iff.mp hp).1

/-- Every element of `primeFinsetLT z` is prime. -/
theorem prime_of_mem_primeFinsetLT {z : ℝ} {p : ℕ} (hp : p ∈ primeFinsetLT z) : p.Prime :=
  (mem_primeFinsetLT_iff.mp hp).1

/-- Monotonicity of `primeFinset`. -/
theorem primeFinset_mono {w z : ℝ} (hwz : w ≤ z) : primeFinset w ⊆ primeFinset z := by
  intro p hp
  rw [mem_primeFinset_iff] at hp ⊢
  exact ⟨hp.1, hp.2.trans hwz⟩

/-- Monotonicity of `primeFinsetLT`. -/
theorem primeFinsetLT_mono {w z : ℝ} (hwz : w ≤ z) : primeFinsetLT w ⊆ primeFinsetLT z := by
  intro p hp
  rw [mem_primeFinsetLT_iff] at hp ⊢
  exact ⟨hp.1, hp.2.trans_le hwz⟩

/-- The product `P(z) = ∏_{p ≤ z} p` of primes up to `z`. -/
def primeProd (z : ℝ) : ℕ :=
  ∏ p ∈ primeFinset z, p

/-- The strict prime product `P_{<}(z) = ∏_{p < z} p` of primes strictly below `z`. -/
def primeProdLT (z : ℝ) : ℕ :=
  ∏ p ∈ primeFinsetLT z, p

/-- `primeProd z` equals `primorial ⌊z⌋₊`. -/
theorem primeProd_eq_primorial (z : ℝ) : primeProd z = primorial ⌊z⌋₊ := by
  rw [primeProd, primeFinset, primorial_eq_prod_primesLE]

/-- `primeProd z` is strictly positive. -/
theorem primeProd_pos (z : ℝ) : 0 < primeProd z := by
  rw [primeProd_eq_primorial]
  exact primorial_pos _

/-- `primeProd z` is nonzero. -/
theorem primeProd_ne_zero (z : ℝ) : primeProd z ≠ 0 :=
  (primeProd_pos z).ne'

/-- `primeProd z` is squarefree. -/
theorem primeProd_squarefree (z : ℝ) : Squarefree (primeProd z) := by
  rw [primeProd_eq_primorial]
  exact squarefree_primorial _

/-- The prime factors of `primeProd z` are `primeFinset z`. -/
theorem primeFactors_primeProd (z : ℝ) : (primeProd z).primeFactors = primeFinset z := by
  rw [primeProd_eq_primorial, primeFactors_primorial, primeFinset]

/-- A prime `p` divides `primeProd z` iff `(p : ℝ) ≤ z`. -/
theorem prime_dvd_primeProd_iff {z : ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ primeProd z ↔ (p : ℝ) ≤ z := by
  constructor
  · intro h
    have hmem : p ∈ (primeProd z).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, h, primeProd_ne_zero z⟩
    rw [primeFactors_primeProd, mem_primeFinset_iff] at hmem
    exact hmem.2
  · intro h
    have hmem : p ∈ (primeProd z).primeFactors := by
      rw [primeFactors_primeProd, mem_primeFinset_iff]
      exact ⟨hp, h⟩
    exact (Nat.mem_primeFactors.mp hmem).2.1

/-- Divisibility monotonicity of `primeProd`. -/
theorem primeProd_dvd_primeProd {w z : ℝ} (hwz : w ≤ z) : primeProd w ∣ primeProd z :=
  Finset.prod_dvd_prod_of_subset _ _ _ (primeFinset_mono hwz)

/-- `primeProdLT z` is strictly positive. -/
theorem primeProdLT_pos (z : ℝ) : 0 < primeProdLT z :=
  Finset.prod_pos fun _ hp => (prime_of_mem_primeFinsetLT hp).pos

/-- `primeProdLT z` is nonzero. -/
theorem primeProdLT_ne_zero (z : ℝ) : primeProdLT z ≠ 0 :=
  (primeProdLT_pos z).ne'

/-- `primeProdLT z` is squarefree. -/
theorem primeProdLT_squarefree (z : ℝ) : Squarefree (primeProdLT z) := by
  unfold primeProdLT
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (prime_of_mem_primeFinsetLT hp).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (prime_of_mem_primeFinsetLT hp)
    (prime_of_mem_primeFinsetLT hq)).mpr hpq

/-- The prime factors of `primeProdLT z` are `primeFinsetLT z`. -/
theorem primeFactors_primeProdLT (z : ℝ) : (primeProdLT z).primeFactors = primeFinsetLT z :=
  Nat.primeFactors_prod fun _ hp => prime_of_mem_primeFinsetLT hp

/-- A prime `p` divides `primeProdLT z` iff `(p : ℝ) < z`. -/
theorem prime_dvd_primeProdLT_iff {z : ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ primeProdLT z ↔ (p : ℝ) < z := by
  constructor
  · intro h
    have hmem : p ∈ (primeProdLT z).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, h, primeProdLT_ne_zero z⟩
    rw [primeFactors_primeProdLT, mem_primeFinsetLT_iff] at hmem
    exact hmem.2
  · intro h
    have hmem : p ∈ (primeProdLT z).primeFactors := by
      rw [primeFactors_primeProdLT, mem_primeFinsetLT_iff]
      exact ⟨hp, h⟩
    exact (Nat.mem_primeFactors.mp hmem).2.1

/-- Divisibility monotonicity of `primeProdLT`. -/
theorem primeProdLT_dvd_primeProdLT {w z : ℝ} (hwz : w ≤ z) :
    primeProdLT w ∣ primeProdLT z :=
  Finset.prod_dvd_prod_of_subset _ _ _ (primeFinsetLT_mono hwz)

/-- At a positive integer `p`, `primeProdLT p = primeProd (p - 1)`. -/
theorem primeProdLT_natCast_eq_primeProd_sub_one {p : ℕ} (hp : 1 ≤ p) :
    primeProdLT (p : ℝ) = primeProd ((p : ℝ) - 1) := by
  unfold primeProdLT primeProd
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext q
  rw [mem_primeFinsetLT_iff, mem_primeFinset_iff]
  constructor
  · rintro ⟨hq, hqp⟩
    refine ⟨hq, ?_⟩
    have hqn : q < p := by exact_mod_cast hqp
    have hq1 : (q : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_pred_of_lt hqn
    rwa [Nat.cast_sub hp, Nat.cast_one] at hq1
  · rintro ⟨hq, hqp⟩
    refine ⟨hq, ?_⟩
    linarith

/-- The subset `A_d = {n ∈ A : d ∣ n}` of multiples of `d` in `A`. -/
def sieveMultiple (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  A.filter (fun n => d ∣ n)

/-- Elements of `sieveMultiple A d` belong to `A` and are divisible by `d`. -/
theorem mem_sieveMultiple_iff {A : Finset ℕ} {d n : ℕ} :
    n ∈ sieveMultiple A d ↔ n ∈ A ∧ d ∣ n :=
  Finset.mem_filter

/-- The sifted count `S(A, P) = #{n ∈ A : Nat.Coprime n P}` against a modulus `P`. -/
def siftedCountOf (A : Finset ℕ) (P : ℕ) : ℕ :=
  (A.filter (fun n => Nat.Coprime n P)).card

/-- The sifted count `S(A, P, z) = #{n ∈ A : Nat.Coprime n (P z)}`. -/
def siftedCount (A : Finset ℕ) (P : ℝ → ℕ) (z : ℝ) : ℕ :=
  siftedCountOf A (P z)

/-- `siftedCountOf A 1` equals `A.card`. -/
@[simp]
theorem siftedCountOf_one (A : Finset ℕ) : siftedCountOf A 1 = A.card := by
  simp [siftedCountOf]

/-- Monotonicity (anti-monotonicity in the sifting modulus): if `P₁ ∣ P₂` then
`siftedCountOf A P₂ ≤ siftedCountOf A P₁`. -/
theorem siftedCountOf_le_of_dvd {A : Finset ℕ} {P₁ P₂ : ℕ} (hP : P₁ ∣ P₂) :
    siftedCountOf A P₂ ≤ siftedCountOf A P₁ := by
  refine Finset.card_le_card fun n hn => ?_
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.coprime_dvd_right hP⟩

/-- Data specifying a combinatorial sieve problem on a finite set `A : Finset ℕ` with sifting
modulus `prodPrimes z`, main-term approximation `X`, and multiplicative sieve density
`ω(d) / d` satisfying `0 ≤ ω(p) < p` for primes `p`. -/
structure SieveData where
  /-- The finite set of integers to be sifted. -/
  A : Finset ℕ
  /-- The squarefree sifting product `P(z)`. -/
  prodPrimes : ℝ → ℕ
  /-- `prodPrimes z` is squarefree for all `z`. -/
  prodPrimes_squarefree : ∀ z : ℝ, Squarefree (prodPrimes z)
  /-- Approximation `X` to `A.card`. -/
  X : ℝ
  /-- Sieve density arithmetic function `ω(d)`. -/
  omega : ArithmeticFunction ℝ
  /-- `ω` is multiplicative. -/
  omega_mult : omega.IsMultiplicative
  /-- Nonnegativity of `ω(p)` at primes. -/
  omega_nonneg_of_prime : ∀ p : ℕ, p.Prime → 0 ≤ omega p
  /-- Strict upper bound `ω(p) < p` at primes. -/
  omega_lt_of_prime : ∀ p : ℕ, p.Prime → omega p < (p : ℝ)

namespace SieveData

/-- `prodPrimes z` is nonzero for every `z`. -/
theorem prodPrimes_ne_zero (s : SieveData) (z : ℝ) : s.prodPrimes z ≠ 0 :=
  (s.prodPrimes_squarefree z).ne_zero

/-- The multiplicative density `ν(d) = ω(d) / d`. -/
def density (s : SieveData) (d : ℕ) : ℝ :=
  s.omega d / (d : ℝ)

/-- `density 0 = 0`. -/
@[simp]
theorem density_zero (s : SieveData) : s.density 0 = 0 := by
  simp [density]

/-- `density 1 = 1`. -/
@[simp]
theorem density_one (s : SieveData) : s.density 1 = 1 := by
  simp [density, s.omega_mult.map_one]

/-- `density` is multiplicative as an arithmetic function. -/
def densityArith (s : SieveData) : ArithmeticFunction ℝ where
  toFun := s.density
  map_zero' := s.density_zero

/-- Evaluation of `densityArith`. -/
@[simp]
theorem densityArith_apply (s : SieveData) (d : ℕ) : s.densityArith d = s.density d :=
  rfl

/-- `densityArith` is multiplicative. -/
theorem densityArith_isMultiplicative (s : SieveData) : s.densityArith.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨s.density_one, fun {m n} hm hn hmn => ?_⟩
  simp only [densityArith_apply, density, Nat.cast_mul]
  rw [s.omega_mult.map_mul_of_coprime hmn]
  ring

/-- `0 ≤ s.density p` for primes `p`. -/
theorem density_nonneg_of_prime (s : SieveData) {p : ℕ} (hp : p.Prime) : 0 ≤ s.density p :=
  div_nonneg (s.omega_nonneg_of_prime p hp) (Nat.cast_nonneg p)

/-- `s.density p < 1` for primes `p`. -/
theorem density_lt_one_of_prime (s : SieveData) {p : ℕ} (hp : p.Prime) : s.density p < 1 := by
  unfold density
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  exact (div_lt_one hp_pos).mpr (s.omega_lt_of_prime p hp)

/-- `0 ≤ s.density d` for every `d` dividing `s.prodPrimes z`. -/
theorem density_nonneg_of_dvd (s : SieveData) {z : ℝ} {d : ℕ} (hd : d ∣ s.prodPrimes z) :
    0 ≤ s.density d := by
  have hsq : Squarefree d := (s.prodPrimes_squarefree z).squarefree_of_dvd hd
  have hprod : s.density d = ∏ p ∈ d.primeFactors, s.density p := by
    calc
      s.density d = s.densityArith d := rfl
      _ = s.densityArith (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hsq]
      _ = ∏ p ∈ d.primeFactors, s.densityArith p :=
          s.densityArith_isMultiplicative.map_prod_of_subset_primeFactors d d.primeFactors subset_rfl
      _ = ∏ p ∈ d.primeFactors, s.density p := rfl
  rw [hprod]
  exact Finset.prod_nonneg fun p hp => s.density_nonneg_of_prime (Nat.prime_of_mem_primeFactors hp)

/-- The remainder term `r_d = |A_d| - (ω(d) / d) * X`. -/
def rem (s : SieveData) (d : ℕ) : ℝ :=
  ((sieveMultiple s.A d).card : ℝ) - s.density d * s.X

/-- Exact decomposition `|A_d| = (ω(d) / d) * X + r_d`. -/
theorem card_sieveMultiple_eq (s : SieveData) (d : ℕ) :
    ((sieveMultiple s.A d).card : ℝ) = s.density d * s.X + s.rem d := by
  unfold rem
  ring

/-- The Euler product `V(z) = ∏_{p ∣ P(z)} (1 - ω(p) / p)`. -/
def eulerProd (s : SieveData) (z : ℝ) : ℝ :=
  ∏ p ∈ (s.prodPrimes z).primeFactors, (1 - s.density p)

/-- `V(z) > 0` for every `z`. -/
theorem eulerProd_pos (s : SieveData) (z : ℝ) : 0 < s.eulerProd z := by
  refine Finset.prod_pos fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  linarith [s.density_lt_one_of_prime hp_prime]

/-- `V(z) ≤ 1` for every `z`. -/
theorem eulerProd_le_one (s : SieveData) (z : ℝ) : s.eulerProd z ≤ 1 := by
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    linarith [s.density_lt_one_of_prime hp_prime]
  · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    linarith [s.density_nonneg_of_prime hp_prime]

/-- Expansion `V(z) = ∑_{d ∣ P(z)} μ(d) * (ω(d) / d)`. -/
theorem eulerProd_eq_sum_divisors (s : SieveData) (z : ℝ) :
    s.eulerProd z = ∑ d ∈ (s.prodPrimes z).divisors, (μ d : ℝ) * s.density d := by
  unfold eulerProd
  have h := s.densityArith_isMultiplicative.prodPrimeFactors_one_sub s.densityArith
    (s.prodPrimes_ne_zero z)
  simpa only [densityArith_apply] using h

end SieveData

end SieveSetting

/-! ### Legendre Inclusion-Exclusion and General Sieve Weights -/

section InclusionExclusionAndWeights

private lemma sum_divisors_moebius_gcd_eq_ite {P : ℕ} (hP : P ≠ 0) (n : ℕ) :
    ∑ d ∈ P.divisors, (if d ∣ n then (μ d : ℤ) else 0) =
      if Nat.Coprime n P then 1 else 0 := by
  let g := Nat.gcd n P
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hP)
  have hg_dvd : g ∣ P := Nat.gcd_dvd_right n P
  have hflt : P.divisors.filter (· ∣ n) = g.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, g, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdP, _⟩, hdn⟩
      exact ⟨⟨hdn, hdP⟩, hg_pos.ne'⟩
    · rintro ⟨⟨hdn, hdP⟩, _⟩
      exact ⟨⟨hdP, hP⟩, hdn⟩
  rw [← Finset.sum_filter, hflt]
  have hzeta := congrArg (fun f : ArithmeticFunction ℤ => f g)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hzeta
  have hsum : ∑ x ∈ g.divisorsAntidiagonal,
      (μ x.1 : ℤ) * (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
      ∑ d ∈ g.divisors, (μ d : ℤ) := by
    refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro x hx
      exact Nat.fst_mem_divisors_of_mem_antidiagonal hx
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 := Nat.mem_divisorsAntidiagonal.mp hx₁
      have h2 := Nat.mem_divisorsAntidiagonal.mp hx₂
      have hx1_nz : x₁.1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact hg_pos.ne' h1.1.symm
      have hsnd : x₁.2 = x₂.2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx1_nz)
        (h1.1.trans (heq ▸ h2.1.symm))
      exact Prod.ext heq hsnd
    · intro d hd
      have hdg := Nat.dvd_of_mem_divisors hd
      exact ⟨(d, g / d), Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hdg, hg_pos.ne'⟩,
        rfl⟩
    · intro x hx
      have hx2_nz : x.2 ≠ 0 := by
        intro h0
        have h1 := (Nat.mem_divisorsAntidiagonal.mp hx).1
        rw [h0, mul_zero] at h1
        exact hg_pos.ne' h1.symm
      have hζ : (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 = 1 := by
        simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hx2_nz]
      rw [hζ, mul_one]
  rw [← hsum, hzeta]

/-- **Legendre exact inclusion-exclusion** over `ℤ`:
for any finite set `A : Finset ℕ` and nonzero `P : ℕ`,
`siftedCountOf A P = ∑_{d ∣ P} μ(d) * |A_d|`. -/
theorem legendre_inclusion_exclusion_int (A : Finset ℕ) {P : ℕ} (hP : P ≠ 0) :
    (siftedCountOf A P : ℤ) =
      ∑ d ∈ P.divisors, (μ d : ℤ) * ((sieveMultiple A d).card : ℤ) := by
  have h1 : (siftedCountOf A P : ℤ) =
      ∑ n ∈ A, (if Nat.Coprime n P then (1 : ℤ) else 0) := by
    unfold siftedCountOf
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  rw [h1]
  calc
    ∑ n ∈ A, (if Nat.Coprime n P then (1 : ℤ) else 0)
        = ∑ n ∈ A, ∑ d ∈ P.divisors, (if d ∣ n then (μ d : ℤ) else 0) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            exact (sum_divisors_moebius_gcd_eq_ite hP n).symm
    _ = ∑ d ∈ P.divisors, ∑ n ∈ A, (if d ∣ n then (μ d : ℤ) else 0) := Finset.sum_comm
    _ = ∑ d ∈ P.divisors, (μ d : ℤ) * ((sieveMultiple A d).card : ℤ) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [sieveMultiple, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul, mul_comm]

/-- **Legendre exact inclusion-exclusion** over `ℝ`:
`siftedCountOf A P = ∑_{d ∣ P} μ(d) * |A_d|`. -/
theorem legendre_inclusion_exclusion (A : Finset ℕ) {P : ℕ} (hP : P ≠ 0) :
    (siftedCountOf A P : ℝ) =
      ∑ d ∈ P.divisors, (μ d : ℝ) * ((sieveMultiple A d).card : ℝ) := by
  have h := congrArg (Int.cast (R := ℝ)) (legendre_inclusion_exclusion_int A hP)
  simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] using h

/-- **Legendre exact inclusion-exclusion** for a threshold product `P z ≠ 0`:
`siftedCount A P z = ∑_{d ∣ P z} μ(d) * |A_d|`. -/
theorem legendre_siftedCount (A : Finset ℕ) (P : ℝ → ℕ) {z : ℝ} (hP : P z ≠ 0) :
    (siftedCount A P z : ℝ) =
      ∑ d ∈ (P z).divisors, (μ d : ℝ) * ((sieveMultiple A d).card : ℝ) :=
  legendre_inclusion_exclusion A hP

/-- Global upper sieve weights: `∑_{d ∣ n} λ⁺_d ≥ 1_{n = 1}` for all `n : ℕ`. -/
def UpperSieveWeights (lam : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ n.divisors, lam d

/-- Global lower sieve weights: `∑_{d ∣ n} λ⁻_d ≤ 1_{n = 1}` for all `n : ℕ`. -/
def LowerSieveWeights (lam : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, lam d ≤ (if n = 1 then (1 : ℝ) else 0)

/-- Upper sieve weights restricted to divisors of `P`:
`∑_{e ∣ d} λ⁺_e ≥ 1_{d = 1}` for all `d ∣ P`. -/
def UpperSieveWeightsOn (P : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, d ∣ P → (if d = 1 then (1 : ℝ) else 0) ≤ ∑ e ∈ d.divisors, lam e

/-- Lower sieve weights restricted to divisors of `P`:
`∑_{e ∣ d} λ⁻_e ≤ 1_{d = 1}` for all `d ∣ P`. -/
def LowerSieveWeightsOn (P : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, d ∣ P → ∑ e ∈ d.divisors, lam e ≤ (if d = 1 then (1 : ℝ) else 0)

/-- Global upper sieve weights satisfy `UpperSieveWeightsOn P` for any `P`. -/
theorem UpperSieveWeights.on {lam : ℕ → ℝ} (h : UpperSieveWeights lam) (P : ℕ) :
    UpperSieveWeightsOn P lam :=
  fun d _ => h d

/-- Global lower sieve weights satisfy `LowerSieveWeightsOn P` for any `P`. -/
theorem LowerSieveWeights.on {lam : ℕ → ℝ} (h : LowerSieveWeights lam) (P : ℕ) :
    LowerSieveWeightsOn P lam :=
  fun d _ => h d

private lemma sum_divisors_mul_card_eq_sum_indicator (A : Finset ℕ) {P : ℕ} (hP : P ≠ 0)
    (lam : ℕ → ℝ) :
    ∑ d ∈ P.divisors, lam d * ((sieveMultiple A d).card : ℝ) =
      ∑ n ∈ A, ∑ d ∈ (Nat.gcd n P).divisors, lam d := by
  calc
    ∑ d ∈ P.divisors, lam d * ((sieveMultiple A d).card : ℝ)
        = ∑ d ∈ P.divisors, ∑ n ∈ A, (if d ∣ n then lam d else 0) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [sieveMultiple, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
              nsmul_eq_mul, mul_comm]
    _ = ∑ n ∈ A, ∑ d ∈ P.divisors, (if d ∣ n then lam d else 0) := Finset.sum_comm
    _ = ∑ n ∈ A, ∑ d ∈ (Nat.gcd n P).divisors, lam d := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          have hg_pos : 0 < Nat.gcd n P := Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hP)
          ext d
          simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Nat.dvd_gcd_iff]
          constructor
          · rintro ⟨⟨hdP, _⟩, hdn⟩
            exact ⟨⟨hdn, hdP⟩, hg_pos.ne'⟩
          · rintro ⟨⟨hdn, hdP⟩, _⟩
            exact ⟨⟨hdP, hP⟩, hdn⟩

/-- **Fundamental upper-bound sieve inequality** (count form): for any `UpperSieveWeightsOn P lam`
with `P ≠ 0`, `siftedCountOf A P ≤ ∑_{d ∣ P} λ⁺_d * |A_d|`. -/
theorem siftedCountOf_le_of_upperSieveWeightsOn (A : Finset ℕ) {P : ℕ} (hP : P ≠ 0)
    {lam : ℕ → ℝ} (hlam : UpperSieveWeightsOn P lam) :
    (siftedCountOf A P : ℝ) ≤ ∑ d ∈ P.divisors, lam d * ((sieveMultiple A d).card : ℝ) := by
  rw [sum_divisors_mul_card_eq_sum_indicator A hP lam]
  have hsift : (siftedCountOf A P : ℝ) = ∑ n ∈ A, (if Nat.Coprime n P then (1 : ℝ) else 0) := by
    unfold siftedCountOf
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsift]
  refine Finset.sum_le_sum fun n _ => ?_
  have h := hlam (Nat.gcd n P) (Nat.gcd_dvd_right n P)
  simpa [Nat.Coprime] using h

/-- **Fundamental lower-bound sieve inequality** (count form): for any `LowerSieveWeightsOn P lam`
with `P ≠ 0`, `∑_{d ∣ P} λ⁻_d * |A_d| ≤ siftedCountOf A P`. -/
theorem sum_le_siftedCountOf_of_lowerSieveWeightsOn (A : Finset ℕ) {P : ℕ} (hP : P ≠ 0)
    {lam : ℕ → ℝ} (hlam : LowerSieveWeightsOn P lam) :
    ∑ d ∈ P.divisors, lam d * ((sieveMultiple A d).card : ℝ) ≤ (siftedCountOf A P : ℝ) := by
  rw [sum_divisors_mul_card_eq_sum_indicator A hP lam]
  have hsift : (siftedCountOf A P : ℝ) = ∑ n ∈ A, (if Nat.Coprime n P then (1 : ℝ) else 0) := by
    unfold siftedCountOf
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsift]
  refine Finset.sum_le_sum fun n _ => ?_
  have h := hlam (Nat.gcd n P) (Nat.gcd_dvd_right n P)
  simpa [Nat.Coprime] using h

/-- **Fundamental upper-bound sieve inequality** (density-remainder form):
`S(A, P, z) ≤ X * (∑_{d ∣ P(z)} λ⁺_d * ω(d) / d) + ∑_{d ∣ P(z)} |λ⁺_d| * |r_d|`. -/
theorem siftedCount_le_sieve_upper (s : SieveData) (z : ℝ) {lam : ℕ → ℝ}
    (hlam : UpperSieveWeightsOn (s.prodPrimes z) lam) :
    (siftedCount s.A s.prodPrimes z : ℝ) ≤
      s.X * (∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d) +
        ∑ d ∈ (s.prodPrimes z).divisors, |lam d| * |s.rem d| := by
  have h1 := siftedCountOf_le_of_upperSieveWeightsOn s.A (s.prodPrimes_ne_zero z) hlam
  have hsplit : ∑ d ∈ (s.prodPrimes z).divisors, lam d * ((sieveMultiple s.A d).card : ℝ) =
      s.X * (∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d) +
        ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.rem d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [s.card_sieveMultiple_eq]
    ring
  have herr : ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.rem d ≤
      ∑ d ∈ (s.prodPrimes z).divisors, |lam d| * |s.rem d| := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← abs_mul]
    exact le_abs_self _
  unfold siftedCount
  linarith

/-- **Fundamental lower-bound sieve inequality** (density-remainder form):
`X * (∑_{d ∣ P(z)} λ⁻_d * ω(d) / d) - ∑_{d ∣ P(z)} |λ⁻_d| * |r_d| ≤ S(A, P, z)`. -/
theorem sieve_lower_le_siftedCount (s : SieveData) (z : ℝ) {lam : ℕ → ℝ}
    (hlam : LowerSieveWeightsOn (s.prodPrimes z) lam) :
    s.X * (∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d) -
        ∑ d ∈ (s.prodPrimes z).divisors, |lam d| * |s.rem d| ≤
      (siftedCount s.A s.prodPrimes z : ℝ) := by
  have h1 := sum_le_siftedCountOf_of_lowerSieveWeightsOn s.A (s.prodPrimes_ne_zero z) hlam
  have hsplit : ∑ d ∈ (s.prodPrimes z).divisors, lam d * ((sieveMultiple s.A d).card : ℝ) =
      s.X * (∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d) +
        ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.rem d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [s.card_sieveMultiple_eq]
    ring
  have herr : -(∑ d ∈ (s.prodPrimes z).divisors, |lam d| * |s.rem d|) ≤
      ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.rem d := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← abs_mul]
    exact neg_abs_le _
  unfold siftedCount
  linarith

/-- Sieve probability weight `prob(P, ν, n) = (∏_{p ∣ n} ν(p)) * (∏_{p ∣ P, p ∤ n} (1 - ν(p)))`
for divisors `n ∣ P` of a squarefree modulus `P`. -/
def sieveProb (P : ℕ) (ν : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ p ∈ n.primeFactors, ν p) * (∏ p ∈ P.primeFactors \ n.primeFactors, (1 - ν p))

/-- Nonnegativity of `sieveProb P ν n` when `0 ≤ ν(p) ≤ 1` on prime factors of `P`. -/
theorem sieveProb_nonneg {P : ℕ} (hP : Squarefree P) {ν : ℕ → ℝ}
    (hν0 : ∀ p ∈ P.primeFactors, 0 ≤ ν p) (hν1 : ∀ p ∈ P.primeFactors, ν p ≤ 1)
    {n : ℕ} (hn : n ∣ P) : 0 ≤ sieveProb P ν n := by
  unfold sieveProb
  have hsub : n.primeFactors ⊆ P.primeFactors := Nat.primeFactors_mono hn hP.ne_zero
  refine mul_nonneg ?_ ?_
  · exact Finset.prod_nonneg fun p hp => hν0 p (hsub hp)
  · exact Finset.prod_nonneg fun p hp => sub_nonneg.mpr (hν1 p (Finset.mem_sdiff.mp hp).1)

/-- `sieveProb P ν 1` equals the Euler product `∏_{p ∣ P} (1 - ν(p))`. -/
theorem sieveProb_one (P : ℕ) (ν : ℕ → ℝ) :
    sieveProb P ν 1 = ∏ p ∈ P.primeFactors, (1 - ν p) := by
  simp [sieveProb]

private lemma sum_powerset_prod_mul_sdiff (S : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ T ∈ S.powerset, (∏ p ∈ T, f p) * (∏ p ∈ S \ T, g p) = ∏ p ∈ S, (f p + g p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.powerset_insert, Finset.sum_union]
      · rw [Finset.sum_image]
        · have h1 : ∑ T ∈ S.powerset, (∏ p ∈ T, f p) * (∏ p ∈ insert a S \ T, g p) =
              g a * ∑ T ∈ S.powerset, (∏ p ∈ T, f p) * (∏ p ∈ S \ T, g p) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun T hT => ?_
            have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
            have hsdiff : insert a S \ T = insert a (S \ T) := Finset.insert_sdiff_of_notMem _ haT
            rw [hsdiff, Finset.prod_insert (fun h => ha (Finset.mem_sdiff.mp h).1)]
            ring
          have h2 : ∑ T ∈ S.powerset, (∏ p ∈ insert a T, f p) * (∏ p ∈ insert a S \ insert a T, g p) =
              f a * ∑ T ∈ S.powerset, (∏ p ∈ T, f p) * (∏ p ∈ S \ T, g p) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun T hT => ?_
            have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
            have hsdiff : insert a S \ insert a T = S \ T := by
              ext x
              simp only [Finset.mem_sdiff, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hxS, hx⟩
                · exact absurd (Or.inl rfl) hx
                · exact ⟨hxS, fun h => hx (Or.inr h)⟩
              · rintro ⟨hxS, hxT⟩
                refine ⟨Or.inr hxS, ?_⟩
                rintro (rfl | hx)
                · exact ha hxS
                · exact hxT hx
            rw [Finset.prod_insert haT, hsdiff]
            ring
          rw [h1, h2, ih, Finset.prod_insert ha]
          ring
        · intro T₁ hT₁ T₂ hT₂ heq
          have ha1 : a ∉ T₁ := fun h => ha (Finset.mem_powerset.mp hT₁ h)
          have ha2 : a ∉ T₂ := fun h => ha (Finset.mem_powerset.mp hT₂ h)
          ext x
          have hmem := Finset.ext_iff.mp heq x
          simp only [Finset.mem_insert] at hmem
          by_cases hxa : x = a
          · subst hxa
            exact ⟨fun h => absurd h ha1, fun h => absurd h ha2⟩
          · simpa [hxa] using hmem
      · rw [Finset.disjoint_left]
        intro T hT himg
        rcases Finset.mem_image.mp himg with ⟨T', _, rfl⟩
        exact ha (Finset.mem_powerset.mp hT (Finset.mem_insert_self a T'))

private lemma divisors_bijective_powerset {ν : ℕ → ℝ} {P : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (fun n => sieveProb P ν n) d =
      ∑ T ∈ P.primeFactors.powerset, (∏ p ∈ T, ν p) * (∏ p ∈ P.primeFactors \ T, (1 - ν p)) := by
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero
  · intro d₁ hd₁ d₂ hd₂ heq
    have hsq1 : Squarefree d₁ := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₁)
    have hsq2 : Squarefree d₂ := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₂)
    rw [← Nat.prod_primeFactors_of_squarefree hsq1, ← Nat.prod_primeFactors_of_squarefree hsq2, heq]
  · intro T hT
    refine ⟨∏ p ∈ T, p, Nat.mem_divisors.mpr ⟨?_, hP.ne_zero⟩, ?_⟩
    · have hsub : T ⊆ P.primeFactors := Finset.mem_powerset.mp hT
      have hprod : ∏ p ∈ T, p ∣ ∏ p ∈ P.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
      rwa [Nat.prod_primeFactors_of_squarefree hP] at hprod
    · exact Nat.primeFactors_prod fun p hp =>
        Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hT hp)
  · intro d _
    rfl

/-- Marginal identity: for squarefree `P` and `d ∣ P` and multiplicative `ν` (`ν.IsMultiplicative`),
`∑_{n ∣ P, d ∣ n} sieveProb P ν n = ν d`. -/
theorem sum_divisors_dvd_sieveProb_eq {P : ℕ} (hP : Squarefree P) {ν : ArithmeticFunction ℝ}
    (hν : ν.IsMultiplicative) {d : ℕ} (hd : d ∣ P) :
    ∑ n ∈ P.divisors with d ∣ n, sieveProb P ν n = ν d := by
  have hd_sq : Squarefree d := hP.squarefree_of_dvd hd
  have hm_sq : Squarefree (P / d) := hP.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)
  have hP_eq : d * (P / d) = P := Nat.mul_div_cancel' hd
  have hcop : d.Coprime (P / d) := (Nat.squarefree_mul_iff.mp (hP_eq.symm ▸ hP)).1
  have hd_prod : ∏ p ∈ d.primeFactors, ν p = ν d := by
    rw [← hν.map_prod_of_subset_primeFactors d d.primeFactors subset_rfl,
      Nat.prod_primeFactors_of_squarefree hd_sq]
  have hbij :
      ∑ n ∈ P.divisors with d ∣ n, sieveProb P ν n =
        ∑ m ∈ (P / d).divisors, sieveProb P ν (d * m) := by
    refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hnP : n ∣ P := Nat.dvd_of_mem_divisors hn'.1
      have hmn : n / d ∣ P / d := by
        rw [← hP_eq, ← Nat.mul_div_cancel' hn'.2] at hnP
        exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hd_sq.ne_zero) hnP
      exact Nat.mem_divisors.mpr ⟨hmn, hm_sq.ne_zero⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      have h1 := (Finset.mem_filter.mp hn₁).2
      have h2 := (Finset.mem_filter.mp hn₂).2
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
    · intro m hm
      have hm_dvd : m ∣ P / d := Nat.dvd_of_mem_divisors hm
      have hdm : d * m ∣ P := by
        rw [← hP_eq]
        exact mul_dvd_mul_left d hm_dvd
      refine ⟨d * m, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdm, hP.ne_zero⟩,
        dvd_mul_right d m⟩, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd_sq.ne_zero)⟩
    · intro n hn
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
  rw [hbij]
  have hterm : ∀ m ∈ (P / d).divisors,
      sieveProb P ν (d * m) = ν d * sieveProb (P / d) ν m := by
    intro m hm
    have hm_dvd : m ∣ P / d := Nat.dvd_of_mem_divisors hm
    have hdm_cop : d.Coprime m := hcop.coprime_dvd_right hm_dvd
    have hpf_dm : (d * m).primeFactors = d.primeFactors ∪ m.primeFactors :=
      Nat.Coprime.primeFactors_mul hdm_cop
    have hdisj_dm : Disjoint d.primeFactors m.primeFactors := hdm_cop.disjoint_primeFactors
    have hpf_P : P.primeFactors = d.primeFactors ∪ (P / d).primeFactors := by
      conv_lhs => rw [← hP_eq]
      exact Nat.Coprime.primeFactors_mul hcop
    have hdisj_P : Disjoint d.primeFactors (P / d).primeFactors := hcop.disjoint_primeFactors
    have hm_sub : m.primeFactors ⊆ (P / d).primeFactors :=
      Nat.primeFactors_mono hm_dvd hm_sq.ne_zero
    have hsdiff_eq : P.primeFactors \ (d * m).primeFactors =
        (P / d).primeFactors \ m.primeFactors := by
      rw [hpf_P, hpf_dm]
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hp1 | hp2, hnot⟩
        · exact absurd (Or.inl hp1) hnot
        · exact ⟨hp2, fun h => hnot (Or.inr h)⟩
      · rintro ⟨hp2, hnot⟩
        refine ⟨Or.inr hp2, ?_⟩
        rintro (hp1 | h)
        · exact Finset.disjoint_left.mp hdisj_P hp1 hp2
        · exact hnot h
    unfold sieveProb
    rw [hsdiff_eq, hpf_dm, Finset.prod_union hdisj_dm, hd_prod, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum_one : ∑ m ∈ (P / d).divisors, sieveProb (P / d) ν m = 1 := by
    rw [divisors_bijective_powerset hm_sq, sum_powerset_prod_mul_sdiff]
    simp
  rw [hsum_one, mul_one]

/-- Total probability identity: `∑_{n ∣ P} sieveProb P ν n = 1` for squarefree `P`. -/
theorem sum_divisors_sieveProb_eq_one {P : ℕ} (hP : Squarefree P) (ν : ℕ → ℝ) :
    ∑ n ∈ P.divisors, sieveProb P ν n = 1 := by
  rw [divisors_bijective_powerset hP, sum_powerset_prod_mul_sdiff]
  simp

/-- **Exact main-term expectation identity**: for any squarefree `P`, multiplicative `ν`,
and sieve weights `lam : ℕ → ℝ`,
`∑_{d ∣ P} lam d * ν d = ∑_{n ∣ P} sieveProb P ν n * ∑_{d ∣ n} lam d`. -/
theorem sum_divisors_mul_density_eq_sum_sieveProb {P : ℕ} (hP : Squarefree P)
    {ν : ArithmeticFunction ℝ} (hν : ν.IsMultiplicative) (lam : ℕ → ℝ) :
    ∑ d ∈ P.divisors, lam d * ν d =
      ∑ n ∈ P.divisors, sieveProb P ν n * ∑ d ∈ n.divisors, lam d := by
  calc
    ∑ d ∈ P.divisors, lam d * ν d
        = ∑ d ∈ P.divisors, lam d * ∑ n ∈ P.divisors with d ∣ n, sieveProb P ν n := by
            refine Finset.sum_congr rfl fun d hd => ?_
            rw [sum_divisors_dvd_sieveProb_eq hP hν (Nat.dvd_of_mem_divisors hd)]
    _ = ∑ d ∈ P.divisors, ∑ n ∈ P.divisors,
          (if d ∣ n then lam d * sieveProb P ν n else 0) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
    _ = ∑ n ∈ P.divisors, ∑ d ∈ P.divisors,
          (if d ∣ n then lam d * sieveProb P ν n else 0) := Finset.sum_comm
    _ = ∑ n ∈ P.divisors, sieveProb P ν n * ∑ d ∈ n.divisors, lam d := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
          have hn_pos : 0 < n := Nat.pos_of_mem_divisors hn
          have hflt : P.divisors.filter (· ∣ n) = n.divisors := by
            ext d
            simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq]
            constructor
            · rintro ⟨⟨_, _⟩, hdn⟩
              exact ⟨hdn, hn_pos.ne'⟩
            · rintro ⟨hdn, _⟩
              exact ⟨⟨hdn.trans (Nat.dvd_of_mem_divisors hn), hP.ne_zero⟩, hdn⟩
          rw [hflt]
          refine Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- For any upper sieve weights `lam`, the main term dominates `V(z)`:
`s.eulerProd z ≤ ∑_{d ∣ P(z)} lam d * s.density d`. -/
theorem eulerProd_le_mainTerm_of_upperSieveWeightsOn (s : SieveData) (z : ℝ) {lam : ℕ → ℝ}
    (hlam : UpperSieveWeightsOn (s.prodPrimes z) lam) :
    s.eulerProd z ≤ ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d := by
  have hP := s.prodPrimes_squarefree z
  have hrew := sum_divisors_mul_density_eq_sum_sieveProb hP s.densityArith_isMultiplicative lam
  have hrew' : ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d =
      ∑ n ∈ (s.prodPrimes z).divisors,
        sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, lam d := hrew
  rw [hrew']
  have h1_mem : 1 ∈ (s.prodPrimes z).divisors := Nat.one_mem_divisors.mpr (s.prodPrimes_ne_zero z)
  have hsplit : ∑ n ∈ (s.prodPrimes z).divisors, sieveProb (s.prodPrimes z) s.density n *
      ∑ d ∈ n.divisors, lam d =
      sieveProb (s.prodPrimes z) s.density 1 * lam 1 +
        ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
          sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, lam d := by
    rw [← Finset.add_sum_erase _ _ h1_mem]
    simp
  have hlam1 : 1 ≤ lam 1 := by
    simpa using hlam 1 (one_dvd _)
  have hprob_nn : ∀ n ∈ (s.prodPrimes z).divisors,
      0 ≤ sieveProb (s.prodPrimes z) s.density n := by
    intro n hn
    exact sieveProb_nonneg hP
      (fun p _ => s.density_nonneg_of_prime (Nat.prime_of_mem_primeFactors ‹_›))
      (fun p _ => (s.density_lt_one_of_prime (Nat.prime_of_mem_primeFactors ‹_›)).le)
      (Nat.dvd_of_mem_divisors hn)
  have hprob1 : sieveProb (s.prodPrimes z) s.density 1 = s.eulerProd z :=
    sieveProb_one (s.prodPrimes z) s.density
  have hrest_nn : 0 ≤ ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
      sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, lam d := by
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_ne : n ≠ 1 := (Finset.mem_erase.mp hn).1
    have hmem : n ∈ (s.prodPrimes z).divisors := (Finset.mem_erase.mp hn).2
    have hsum_nn : 0 ≤ ∑ d ∈ n.divisors, lam d := by
      simpa [hn_ne] using hlam n (Nat.dvd_of_mem_divisors hmem)
    exact mul_nonneg (hprob_nn n hmem) hsum_nn
  rw [hsplit, hprob1]
  have hle1 : s.eulerProd z ≤ s.eulerProd z * lam 1 :=
    le_mul_of_one_le_right (s.eulerProd_pos z).le hlam1
  linarith

/-- For any lower sieve weights `lam`, the main term is bounded above by `V(z)`:
`∑_{d ∣ P(z)} lam d * s.density d ≤ s.eulerProd z`. -/
theorem mainTerm_le_eulerProd_of_lowerSieveWeightsOn (s : SieveData) (z : ℝ) {lam : ℕ → ℝ}
    (hlam : LowerSieveWeightsOn (s.prodPrimes z) lam) :
    ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d ≤ s.eulerProd z := by
  have hP := s.prodPrimes_squarefree z
  have hrew := sum_divisors_mul_density_eq_sum_sieveProb hP s.densityArith_isMultiplicative lam
  have hrew' : ∑ d ∈ (s.prodPrimes z).divisors, lam d * s.density d =
      ∑ n ∈ (s.prodPrimes z).divisors,
        sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, lam d := hrew
  rw [hrew']
  have h1_mem : 1 ∈ (s.prodPrimes z).divisors := Nat.one_mem_divisors.mpr (s.prodPrimes_ne_zero z)
  have hsplit : ∑ n ∈ (s.prodPrimes z).divisors, sieveProb (s.prodPrimes z) s.density n *
      ∑ d ∈ n.divisors, lam d =
      sieveProb (s.prodPrimes z) s.density 1 * lam 1 +
        ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
          sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, lam d := by
    rw [← Finset.add_sum_erase _ _ h1_mem]
    simp
  have hlam1 : lam 1 ≤ 1 := by
    simpa using hlam 1 (one_dvd _)
  have hprob_nn : ∀ n ∈ (s.prodPrimes z).divisors,
      0 ≤ sieveProb (s.prodPrimes z) s.density n := by
    intro n hn
    exact sieveProb_nonneg hP
      (fun p _ => s.density_nonneg_of_prime (Nat.prime_of_mem_primeFactors ‹_›))
      (fun p _ => (s.density_lt_one_of_prime (Nat.prime_of_mem_primeFactors ‹_›)).le)
      (Nat.dvd_of_mem_divisors hn)
  have hprob1 : sieveProb (s.prodPrimes z) s.density 1 = s.eulerProd z :=
    sieveProb_one (s.prodPrimes z) s.density
  have hrest_np : ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
      sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, lam d ≤ 0 := by
    refine Finset.sum_nonpos fun n hn => ?_
    have hn_ne : n ≠ 1 := (Finset.mem_erase.mp hn).1
    have hmem : n ∈ (s.prodPrimes z).divisors := (Finset.mem_erase.mp hn).2
    have hsum_np : ∑ d ∈ n.divisors, lam d ≤ 0 := by
      simpa [hn_ne] using hlam n (Nat.dvd_of_mem_divisors hmem)
    exact mul_nonpos_of_nonneg_of_nonpos (hprob_nn n hmem) hsum_np
  rw [hsplit, hprob1]
  have hle1 : s.eulerProd z * lam 1 ≤ s.eulerProd z :=
    mul_le_of_le_one_right (s.eulerProd_pos z).le hlam1
  linarith

end InclusionExclusionAndWeights

/-! ### Brun's Pure Sieve -/

section BrunsPureSieve

/-- Brun's pure sieve weights truncated at `r` prime factors:
`brunPureWeights r d = μ(d)` if `d.primeFactors.card ≤ r`, and `0` otherwise. -/
def brunPureWeights (r : ℕ) (d : ℕ) : ℝ :=
  if d.primeFactors.card ≤ r then (μ d : ℝ) else 0

/-- At `d = 1`, `brunPureWeights r 1 = 1` for every `r : ℕ`. -/
@[simp]
theorem brunPureWeights_one (r : ℕ) : brunPureWeights r 1 = 1 := by
  simp [brunPureWeights]

/-- `|brunPureWeights r d| ≤ 1` for all `r, d : ℕ`. -/
theorem abs_brunPureWeights_le_one (r d : ℕ) : |brunPureWeights r d| ≤ 1 := by
  unfold brunPureWeights
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  · norm_num

/-- Alternating binomial partial sum identity: for `k ≥ 1` and any `r : ℕ`,
`∑_{j=0}^r (-1)^j C(k, j) = (-1)^r C(k - 1, r)`. -/
theorem sum_neg_one_pow_mul_choose {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) =
      (-1 : ℤ) ^ r * (Nat.choose (k - 1) r : ℤ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_sub_one]
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m r]
      push_cast
      rw [pow_succ]
      ring

private lemma sum_divisors_brunPureWeights_of_squarefree {n : ℕ} (hn : Squarefree n)
    (hn_gt : 1 < n) (r : ℕ) :
    ∑ d ∈ n.divisors, brunPureWeights r d =
      (-1 : ℝ) ^ r * (Nat.choose (n.primeFactors.card - 1) r : ℝ) := by
  let S := n.primeFactors
  have hk : 1 ≤ S.card := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn_gt)
  have hbij :
      ∑ d ∈ n.divisors, brunPureWeights r d =
        ∑ T ∈ S.powerset with T.card ≤ r, (-1 : ℝ) ^ T.card := by
    simp only [brunPureWeights]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd'.1) hn.ne_zero
      · exact hd'.2
    · intro d₁ hd₁ d₂ hd₂ heq
      have hsq1 := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₁).1)
      have hsq2 := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₂).1)
      rw [← Nat.prod_primeFactors_of_squarefree hsq1, ← Nat.prod_primeFactors_of_squarefree hsq2,
        heq]
    · intro T hT
      have hT' := Finset.mem_filter.mp hT
      have hsub : T ⊆ S := Finset.mem_powerset.mp hT'.1
      have hprod_dvd : ∏ p ∈ T, p ∣ n := by
        have h1 : ∏ p ∈ T, p ∣ ∏ p ∈ S, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
        rwa [Nat.prod_primeFactors_of_squarefree hn] at h1
      have hpf : (∏ p ∈ T, p).primeFactors = T :=
        Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
      refine ⟨∏ p ∈ T, p, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hprod_dvd, hn.ne_zero⟩,
        ?_⟩, hpf⟩
      simpa [hpf] using hT'.2
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hsq := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd'.1)
      have hμ_prod : (μ d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
        calc
          (μ d : ℝ) = ((μ : ArithmeticFunction ℝ) d) := rfl
          _ = (μ : ArithmeticFunction ℝ) (∏ p ∈ d.primeFactors, p) := by
              rw [Nat.prod_primeFactors_of_squarefree hsq]
          _ = ∏ p ∈ d.primeFactors, ((μ : ArithmeticFunction ℝ) p) :=
              (ArithmeticFunction.isMultiplicative_moebius.intCast.map_prod_of_subset_primeFactors
                d d.primeFactors subset_rfl)
          _ = ∏ _p ∈ d.primeFactors, (-1 : ℝ) := by
              refine Finset.prod_congr rfl fun p hp => ?_
              simp [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
          _ = (-1 : ℝ) ^ d.primeFactors.card := by simp
      exact hμ_prod
  rw [hbij]
  have hgroup :
      ∑ T ∈ S.powerset with T.card ≤ r, (-1 : ℝ) ^ T.card =
        ∑ j ∈ Finset.range (r + 1), (-1 : ℝ) ^ j * (Nat.choose S.card j : ℝ) := by
    have hmaps : ∀ T ∈ S.powerset.filter (fun T => T.card ≤ r),
        T.card ∈ Finset.range (r + 1) := by
      intro T hT
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hT).2)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hflt_eq : (S.powerset.filter (fun T => T.card ≤ r)).filter (fun T => T.card = j) =
        S.powersetCard j := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hT, _⟩, rfl⟩
        exact ⟨Finset.mem_powerset.mp hT, rfl⟩
      · rintro ⟨hT, rfl⟩
        exact ⟨⟨Finset.mem_powerset.mpr hT, hj_le⟩, rfl⟩
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_filter.mp hT).2]),
      Finset.sum_const, hflt_eq, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
  rw [hgroup]
  have hZ := congrArg (Int.cast (R := ℝ)) (sum_neg_one_pow_mul_choose hk r)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] using hZ

private lemma sum_divisors_brunPureWeights_general (n r : ℕ) :
    ∑ d ∈ n.divisors, brunPureWeights r d =
      if n = 0 then 0
      else if n = 1 then 1
      else (-1 : ℝ) ^ r * (Nat.choose (n.primeFactors.card - 1) r : ℝ) := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hn1 : n = 1
  · subst hn1; simp
  simp only [hn0, hn1, ↓reduceIte]
  let m := ∏ p ∈ n.primeFactors, p
  have hm_sq : Squarefree m := Nat.squarefree_prod_primeFactors n
  have hm_dvd : m ∣ n := Nat.prod_primeFactors_dvd n
  have hm_pf : m.primeFactors = n.primeFactors := Nat.primeFactors_prod_primeFactors n
  have hm_gt : 1 < m := by
    have hne : m ≠ 1 := by
      intro h1
      have hpf : n.primeFactors = ∅ := by
        rw [← hm_pf, h1, Nat.primeFactors_one]
      rw [Nat.primeFactors_eq_empty] at hpf
      rcases hpf with rfl | rfl <;> contradiction
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm_sq.ne_zero, hne⟩
  have hsub : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn0 hm_dvd
  have hsum_eq : ∑ d ∈ n.divisors, brunPureWeights r d =
      ∑ d ∈ m.divisors, brunPureWeights r d := by
    refine (Finset.sum_subset hsub fun d hd hdm => ?_).symm
    have hd_not_sq : ¬ Squarefree d := by
      intro hd_sq
      apply hdm
      refine Nat.mem_divisors.mpr ⟨?_, hm_sq.ne_zero⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn0)
    simp [brunPureWeights, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd_not_sq]
  rw [hsum_eq, sum_divisors_brunPureWeights_of_squarefree hm_sq hm_gt r, hm_pf]

/-- Even Brun pure sieve weights `brunPureWeights (2 * m)` are global `UpperSieveWeights`. -/
theorem brunPureWeights_even_isUpperSieveWeights (m : ℕ) :
    UpperSieveWeights (brunPureWeights (2 * m)) := by
  intro n
  rw [sum_divisors_brunPureWeights_general]
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hn1 : n = 1
  · subst hn1; simp
  simp only [hn0, hn1, ↓reduceIte]
  rw [pow_mul, neg_one_sq, one_pow, one_mul]
  exact Nat.cast_nonneg _

/-- Odd Brun pure sieve weights `brunPureWeights (2 * m + 1)` are global `LowerSieveWeights`. -/
theorem brunPureWeights_odd_isLowerSieveWeights (m : ℕ) :
    LowerSieveWeights (brunPureWeights (2 * m + 1)) := by
  intro n
  rw [sum_divisors_brunPureWeights_general]
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hn1 : n = 1
  · subst hn1; simp
  simp only [hn0, hn1, ↓reduceIte]
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  linarith [show (0 : ℝ) ≤ (Nat.choose (n.primeFactors.card - 1) (2 * m + 1) : ℝ) from
    Nat.cast_nonneg _]

private lemma sum_choose_card_eq_sum_card_eq {P : ℕ} (hP : Squarefree P) (ν : ℕ → ℝ) (r : ℕ) :
    ∑ n ∈ P.divisors, sieveProb P ν n * (Nat.choose n.primeFactors.card r : ℝ) =
      ∑ d ∈ P.divisors with d.primeFactors.card = r,
        ∑ n ∈ P.divisors with d ∣ n, sieveProb P ν n := by
  have h1 : ∀ n ∈ P.divisors,
      (Nat.choose n.primeFactors.card r : ℝ) =
        ∑ d ∈ P.divisors with d.primeFactors.card = r, if d ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    have hsq := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hn)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hflt_eq :
        (P.divisors.filter (fun d => d.primeFactors.card = r)).filter (· ∣ n) =
          ((n.primeFactors.powersetCard r).image (fun T => ∏ p ∈ T, p)) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨⟨hdP, _⟩, hdr⟩, hdn⟩
        have hdsq := hP.squarefree_of_dvd hdP
        refine ⟨d.primeFactors, ⟨Nat.primeFactors_mono hdn (Nat.pos_of_mem_divisors hn).ne', hdr⟩,
          Nat.prod_primeFactors_of_squarefree hdsq⟩
      · rintro ⟨T, ⟨hTn, hTr⟩, rfl⟩
        have hT_prime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTn hp)
        have hpf : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hT_prime
        have hprod_dvd_n : ∏ p ∈ T, p ∣ n := by
          have := Finset.prod_dvd_prod_of_subset T n.primeFactors (fun p => p) hTn
          exact this.trans (Nat.prod_primeFactors_dvd n)
        exact ⟨⟨⟨hprod_dvd_n.trans (Nat.dvd_of_mem_divisors hn), hP.ne_zero⟩, by rw [hpf, hTr]⟩,
          hprod_dvd_n⟩
    rw [hflt_eq, Finset.card_image_of_injOn, Finset.card_powersetCard]
    intro T₁ hT₁ T₂ hT₂ heq
    dsimp only at heq
    have h1' := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT₁)).1
    have h2' := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT₂)).1
    have hpf1 : (∏ p ∈ T₁, p).primeFactors = T₁ :=
      Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (h1' hp)
    have hpf2 : (∏ p ∈ T₂, p).primeFactors = T₂ :=
      Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (h2' hp)
    rw [← hpf1, heq, hpf2]
  calc
    ∑ n ∈ P.divisors, sieveProb P ν n * (Nat.choose n.primeFactors.card r : ℝ)
        = ∑ n ∈ P.divisors, sieveProb P ν n *
            ∑ d ∈ P.divisors with d.primeFactors.card = r, if d ∣ n then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun n hn => by rw [h1 n hn]
    _ = ∑ n ∈ P.divisors, ∑ d ∈ P.divisors with d.primeFactors.card = r,
          (if d ∣ n then sieveProb P ν n else 0) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
    _ = ∑ d ∈ P.divisors with d.primeFactors.card = r, ∑ n ∈ P.divisors,
          (if d ∣ n then sieveProb P ν n else 0) := Finset.sum_comm
    _ = ∑ d ∈ P.divisors with d.primeFactors.card = r,
          ∑ n ∈ P.divisors with d ∣ n, sieveProb P ν n := by
          refine Finset.sum_congr rfl fun d _ => by rw [Finset.sum_filter]

private lemma choose_sub_one_le_choose_succ (k r : ℕ) (hk : 1 ≤ k) :
    Nat.choose (k - 1) r ≤ Nat.choose k (r + 1) := by
  have hmul : Nat.choose k (r + 1) * (r + 1) = k * Nat.choose (k - 1) r := by
    have h := Nat.add_one_mul_choose_eq (k - 1) r
    have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [hk_eq] at h
    exact h.symm
  by_cases hle : r + 1 ≤ k
  · have h1 : (r + 1) * Nat.choose (k - 1) r ≤ k * Nat.choose (k - 1) r :=
      Nat.mul_le_mul_right _ hle
    rw [← hmul, mul_comm (Nat.choose k (r + 1)) (r + 1)] at h1
    exact Nat.le_of_mul_le_mul_left h1 (Nat.succ_pos r)
  · have hlt : k < r + 1 := Nat.lt_of_not_ge hle
    have hk1 : k - 1 < r := by omega
    rw [Nat.choose_eq_zero_of_lt hk1]
    exact Nat.zero_le _

private lemma sum_density_card_eq_le_pow_div_factorial (s : SieveData) (z : ℝ) (k : ℕ) :
    ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card = k, s.density d ≤
      (∑ p ∈ (s.prodPrimes z).primeFactors, s.density p) ^ k / (k.factorial : ℝ) := by
  let P := s.prodPrimes z
  have hP := s.prodPrimes_squarefree z
  have hk_fac : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  rw [le_div_iff₀ hk_fac]
  let D_k := P.divisors.filter (fun d => d.primeFactors.card = k)
  let Φ : (Fin k → ℕ) → ℕ := fun f => ∏ i, f i
  let T_k := (Fintype.piFinset (fun _ : Fin k => P.primeFactors)).filter Function.Injective
  have hsum_pow : (∑ p ∈ P.primeFactors, s.density p) ^ k =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P.primeFactors), ∏ i, s.density (f i) := by
    rw [Finset.sum_pow']
  have hsub_Tk : T_k ⊆ Fintype.piFinset (fun _ : Fin k => P.primeFactors) :=
    Finset.filter_subset _ _
  have hTk_le : ∑ f ∈ T_k, ∏ i, s.density (f i) ≤
      (∑ p ∈ P.primeFactors, s.density p) ^ k := by
    rw [hsum_pow]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub_Tk fun f hf _ => ?_
    refine Finset.prod_nonneg fun i _ => ?_
    have hp := (Fintype.mem_piFinset.mp hf) i
    exact s.density_nonneg_of_prime (Nat.prime_of_mem_primeFactors hp)
  have hfib :
      ∑ f ∈ T_k, ∏ i, s.density (f i) =
        ∑ d ∈ D_k, ∑ f ∈ T_k with Φ f = d, ∏ i, s.density (f i) := by
    refine (Finset.sum_fiberwise_of_maps_to (fun f hf => ?_) _).symm
    have hf' := Finset.mem_filter.mp hf
    have hpi := Fintype.mem_piFinset.mp hf'.1
    have hinj := hf'.2
    have hP_prod : ∏ i, f i ∣ P := by
      have hsub_im : Finset.univ.image f ⊆ P.primeFactors := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
        exact hpi i
      have hprod_im : ∏ i, f i = ∏ p ∈ Finset.univ.image f, p := by
        rw [Finset.prod_image]
        intro a _ b _ hab
        exact hinj hab
      rw [hprod_im]
      have hdvd := Finset.prod_dvd_prod_of_subset (Finset.univ.image f) P.primeFactors
        (fun p => p) hsub_im
      rwa [Nat.prod_primeFactors_of_squarefree hP] at hdvd
    have hpf_prod : (∏ i, f i).primeFactors = Finset.univ.image f := by
      have hprod_im : ∏ i, f i = ∏ p ∈ Finset.univ.image f, p := by
        rw [Finset.prod_image]
        intro a _ b _ hab
        exact hinj hab
      rw [hprod_im]
      exact Nat.primeFactors_prod fun p hp => by
        rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
        exact Nat.prime_of_mem_primeFactors (hpi i)
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hP_prod, hP.ne_zero⟩, ?_⟩
    rw [hpf_prod, Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hfib_eval : ∀ d ∈ D_k,
      ∑ f ∈ T_k with Φ f = d, ∏ i, s.density (f i) =
        (k.factorial : ℝ) * s.density d := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hd_sq := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd'.1)
    have hcard_d : d.primeFactors.card = k := hd'.2
    have hterm_eq : ∀ f ∈ T_k.filter (fun f => Φ f = d),
        ∏ i, s.density (f i) = s.density d := by
      intro f hf
      have hf' := Finset.mem_filter.mp hf
      have hf_Tk := Finset.mem_filter.mp hf'.1
      have hinj := hf_Tk.2
      have hpi := Fintype.mem_piFinset.mp hf_Tk.1
      have him_eq : Finset.univ.image f = d.primeFactors := by
        have h1 : (∏ i, f i).primeFactors = Finset.univ.image f := by
          have hprod_im : ∏ i, f i = ∏ p ∈ Finset.univ.image f, p := by
            rw [Finset.prod_image]
            intro a _ b _ hab
            exact hinj hab
          rw [hprod_im]
          exact Nat.primeFactors_prod fun p hp => by
            rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
            exact Nat.prime_of_mem_primeFactors (hpi i)
        dsimp only [Φ] at hf'
        rw [← h1, hf'.2]
      calc
        ∏ i, s.density (f i)
            = ∏ p ∈ Finset.univ.image f, s.density p := by
                rw [Finset.prod_image]
                intro a _ b _ hab
                exact hinj hab
        _ = ∏ p ∈ d.primeFactors, s.density p := by rw [him_eq]
        _ = ∏ p ∈ d.primeFactors, s.densityArith p := rfl
        _ = s.densityArith (∏ p ∈ d.primeFactors, p) :=
            (s.densityArith_isMultiplicative.map_prod_of_subset_primeFactors d d.primeFactors
              subset_rfl).symm
        _ = s.density d := by rw [Nat.prod_primeFactors_of_squarefree hd_sq]; rfl
    rw [Finset.sum_congr rfl hterm_eq, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hbij_perm : (T_k.filter (fun f => Φ f = d)).card =
        (Fintype.card (Fin k ≃ d.primeFactors)) := by
      refine Finset.card_bij (fun f hf =>
          Equiv.ofBijective (fun i => ⟨f i, by
            have hf' := Finset.mem_filter.mp hf
            have hf_Tk := Finset.mem_filter.mp hf'.1
            have hinj := hf_Tk.2
            have hpi := Fintype.mem_piFinset.mp hf_Tk.1
            have hprod_im : ∏ j, f j = ∏ p ∈ Finset.univ.image f, p := by
              rw [Finset.prod_image]
              intro a _ b _ hab
              exact hinj hab
            have h1 : (∏ j, f j).primeFactors = Finset.univ.image f := by
              rw [hprod_im]
              exact Nat.primeFactors_prod fun p hp => by
                rcases Finset.mem_image.mp hp with ⟨j, _, rfl⟩
                exact Nat.prime_of_mem_primeFactors (hpi j)
            dsimp only [Φ] at hf'
            rw [← hf'.2, h1]
            exact Finset.mem_image_of_mem f (Finset.mem_univ i)⟩)
            ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a b hab => by
              have hf' := Finset.mem_filter.mp hf
              exact (Finset.mem_filter.mp hf'.1).2 (congrArg Subtype.val hab), by
              rw [Fintype.card_coe, hcard_d, Fintype.card_fin]⟩))
        (fun _ _ => Finset.mem_univ _)
        (fun f₁ _ f₂ _ heq => by
          ext i
          exact congrArg Subtype.val (Equiv.ext_iff.mp heq i))
        (fun e _ => ?_)
      · let f : Fin k → ℕ := fun i => (e i : ℕ)
        have hpi : f ∈ Fintype.piFinset (fun _ : Fin k => P.primeFactors) := by
          rw [Fintype.mem_piFinset]
          intro i
          exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd'.1) hP.ne_zero (e i).2
        have hinj : Function.Injective f := fun a b hab =>
          e.injective (Subtype.ext hab)
        have hprod : Φ f = d := by
          dsimp [Φ, f]
          calc
            ∏ i : Fin k, (e i : ℕ) = ∏ p : d.primeFactors, (p : ℕ) :=
              Fintype.prod_equiv e (fun x => (e x : ℕ)) (fun p => (p : ℕ)) (fun _ => rfl)
            _ = ∏ p ∈ d.primeFactors, p := Finset.prod_coe_sort d.primeFactors id
            _ = d := Nat.prod_primeFactors_of_squarefree hd_sq
        refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpi, hinj⟩, hprod⟩, ?_⟩
        ext i
        rfl
    have heqv : Fin k ≃ d.primeFactors :=
      (Fintype.equivFinOfCardEq (by simp [hcard_d] : Fintype.card d.primeFactors = k)).symm
    rw [hbij_perm, Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin k)) heqv.symm),
      Fintype.card_perm, Fintype.card_fin]
  rw [hfib, Finset.sum_congr rfl hfib_eval, ← Finset.mul_sum] at hTk_le
  linarith

private lemma sum_density_le_neg_log_eulerProd (s : SieveData) (z : ℝ) :
    ∑ p ∈ (s.prodPrimes z).primeFactors, s.density p ≤ Real.log ((s.eulerProd z)⁻¹) := by
  have hlog_inv : Real.log ((s.eulerProd z)⁻¹) =
      ∑ p ∈ (s.prodPrimes z).primeFactors, -Real.log (1 - s.density p) := by
    rw [Real.log_inv, SieveData.eulerProd, Real.log_prod]
    · rw [Finset.sum_neg_distrib]
    · intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      linarith [s.density_lt_one_of_prime hp_prime]
  rw [hlog_inv]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < 1 - s.density p := sub_pos.mpr (s.density_lt_one_of_prime hp_prime)
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

private lemma inv_factorial_le_exp_div_pow {r : ℕ} (hr : 1 ≤ r) :
    ((r.factorial : ℝ))⁻¹ ≤ (Real.exp 1 / (r : ℝ)) ^ r := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hfac_pos : (0 : ℝ) < (r.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have hpow_le_exp : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp (r : ℝ) :=
    Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r
  have hexp_r : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp_r] at hpow_le_exp
  have h1 : (r : ℝ) ^ r ≤ (Real.exp 1) ^ r * (r.factorial : ℝ) :=
    (div_le_iff₀ hfac_pos).mp hpow_le_exp
  rw [div_pow, inv_eq_one_div, div_le_div_iff₀ hfac_pos (pow_pos hr_pos r)]
  linarith

/-- Main-term comparison for Brun's pure sieve: for any `r : ℕ`,
`|∑_{d ∣ P(z)} brunPureWeights r d * (ω(d)/d) - V(z)| ≤ (log (V(z)⁻¹))^(r+1) / (r+1)!`. -/
theorem abs_brunPure_mainTerm_sub_eulerProd_le (s : SieveData) (z : ℝ) (r : ℕ) :
    |∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights r d * s.density d - s.eulerProd z| ≤
      (Real.log ((s.eulerProd z)⁻¹)) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
  have hP := s.prodPrimes_squarefree z
  have hrew := sum_divisors_mul_density_eq_sum_sieveProb hP s.densityArith_isMultiplicative
    (brunPureWeights r)
  have hrew' : ∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights r d * s.density d =
      ∑ n ∈ (s.prodPrimes z).divisors,
        sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, brunPureWeights r d := hrew
  rw [hrew']
  have h1_mem : 1 ∈ (s.prodPrimes z).divisors := Nat.one_mem_divisors.mpr (s.prodPrimes_ne_zero z)
  have hsplit : ∑ n ∈ (s.prodPrimes z).divisors, sieveProb (s.prodPrimes z) s.density n *
      ∑ d ∈ n.divisors, brunPureWeights r d =
      s.eulerProd z + ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
        sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, brunPureWeights r d := by
    rw [← Finset.add_sum_erase _ _ h1_mem, sieveProb_one]
    simp [SieveData.eulerProd]
  rw [hsplit, add_sub_cancel_left]
  have hprob_nn : ∀ n ∈ (s.prodPrimes z).divisors,
      0 ≤ sieveProb (s.prodPrimes z) s.density n := by
    intro n hn
    exact sieveProb_nonneg hP
      (fun p hp => s.density_nonneg_of_prime (Nat.prime_of_mem_primeFactors hp))
      (fun p hp => (s.density_lt_one_of_prime (Nat.prime_of_mem_primeFactors hp)).le)
      (Nat.dvd_of_mem_divisors hn)
  have habs_le :
      |∑ n ∈ (s.prodPrimes z).divisors.erase 1,
          sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, brunPureWeights r d| ≤
        ∑ n ∈ (s.prodPrimes z).divisors,
          sieveProb (s.prodPrimes z) s.density n * (Nat.choose n.primeFactors.card (r + 1) : ℝ) := by
    calc
      |∑ n ∈ (s.prodPrimes z).divisors.erase 1,
          sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, brunPureWeights r d|
          ≤ ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
              |sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, brunPureWeights r d| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ (s.prodPrimes z).divisors.erase 1,
            sieveProb (s.prodPrimes z) s.density n *
              (Nat.choose n.primeFactors.card (r + 1) : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : n ≠ 1 := (Finset.mem_erase.mp hn).1
          have hn_mem : n ∈ (s.prodPrimes z).divisors := (Finset.mem_erase.mp hn).2
          have hn_sq := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hn_mem)
          have hn_gt : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn_sq.ne_zero, hn1⟩
          have hk : 1 ≤ n.primeFactors.card :=
            Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn_gt)
          rw [sum_divisors_brunPureWeights_of_squarefree hn_sq hn_gt r, abs_mul,
            abs_of_nonneg (hprob_nn n hn_mem), abs_mul, abs_pow, abs_neg, abs_one, one_pow,
            one_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left
            (by exact_mod_cast choose_sub_one_le_choose_succ n.primeFactors.card r hk)
            (hprob_nn n hn_mem)
      _ ≤ ∑ n ∈ (s.prodPrimes z).divisors,
            sieveProb (s.prodPrimes z) s.density n *
              (Nat.choose n.primeFactors.card (r + 1) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
          intro n hn _
          exact mul_nonneg (hprob_nn n hn) (Nat.cast_nonneg _)
  have hrewrite := sum_choose_card_eq_sum_card_eq hP s.density (r + 1)
  have hsum_dens :
      ∑ n ∈ (s.prodPrimes z).divisors,
          sieveProb (s.prodPrimes z) s.density n * (Nat.choose n.primeFactors.card (r + 1) : ℝ) =
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card = r + 1, s.density d := by
    rw [hrewrite]
    refine Finset.sum_congr rfl fun d hd => ?_
    exact sum_divisors_dvd_sieveProb_eq hP s.densityArith_isMultiplicative
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hpow_le := sum_density_card_eq_le_pow_div_factorial s z (r + 1)
  have hlog_ge := sum_density_le_neg_log_eulerProd s z
  have hsum_nn : 0 ≤ ∑ p ∈ (s.prodPrimes z).primeFactors, s.density p :=
    Finset.sum_nonneg fun p hp => s.density_nonneg_of_prime (Nat.prime_of_mem_primeFactors hp)
  calc
    |∑ n ∈ (s.prodPrimes z).divisors.erase 1,
        sieveProb (s.prodPrimes z) s.density n * ∑ d ∈ n.divisors, brunPureWeights r d|
        ≤ ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card = r + 1, s.density d :=
          habs_le.trans_eq hsum_dens
    _ ≤ (∑ p ∈ (s.prodPrimes z).primeFactors, s.density p) ^ (r + 1) /
          ((r + 1).factorial : ℝ) := hpow_le
    _ ≤ (Real.log ((s.eulerProd z)⁻¹)) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
          gcongr

/-- **Brun's pure sieve upper bound**: truncating at `2 * m` prime factors gives
`S(A, P, z) ≤ X * V(z) + |X| * (log (V(z)⁻¹))^(2m+1) / (2m+1)! + ∑_{d∣P(z), ω(d) ≤ 2m} |r_d|`. -/
theorem brun_pure_upper (s : SieveData) (z : ℝ) (m : ℕ) :
    (siftedCount s.A s.prodPrimes z : ℝ) ≤
      s.X * s.eulerProd z +
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) +
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m, |s.rem d| := by
  have h1 := siftedCount_le_sieve_upper s z ((brunPureWeights_even_isUpperSieveWeights m).on _)
  have hmain := abs_brunPure_mainTerm_sub_eulerProd_le s z (2 * m)
  have hm_le : ∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m) d * s.density d ≤
      s.eulerProd z + (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) := by
    linarith [(abs_le.mp hmain).2]
  have hX_main :
      s.X * (∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m) d * s.density d) ≤
        s.X * s.eulerProd z +
          |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) := by
    have hdiff : s.X * (∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m) d * s.density d -
        s.eulerProd z) ≤
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) := by
      calc
        s.X * (∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m) d * s.density d -
            s.eulerProd z)
            ≤ |s.X * (∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m) d * s.density d -
                s.eulerProd z)| := le_abs_self _
        _ = |s.X| * |∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m) d * s.density d -
              s.eulerProd z| := abs_mul _ _
        _ ≤ |s.X| * ((Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) /
              ((2 * m + 1).factorial : ℝ)) := by
              gcongr
        _ = |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) /
              ((2 * m + 1).factorial : ℝ) := by ring
    linarith
  have hrem_le :
      ∑ d ∈ (s.prodPrimes z).divisors, |brunPureWeights (2 * m) d| * |s.rem d| ≤
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m, |s.rem d| := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases hcard : d.primeFactors.card ≤ 2 * m
    · simp only [hcard, ↓reduceIte]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_brunPureWeights_le_one (2 * m) d)
    · simp [brunPureWeights, hcard]
  linarith

/-- **Brun's pure sieve lower bound**: truncating at `2 * m + 1` prime factors gives
`X * V(z) - |X| * (log (V(z)⁻¹))^(2m+2) / (2m+2)! - ∑_{d∣P(z), ω(d) ≤ 2m+1} |r_d| ≤ S(A, P, z)`. -/
theorem brun_pure_lower (s : SieveData) (z : ℝ) (m : ℕ) :
    s.X * s.eulerProd z -
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ) -
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m + 1, |s.rem d| ≤
      (siftedCount s.A s.prodPrimes z : ℝ) := by
  have h1 := sieve_lower_le_siftedCount s z ((brunPureWeights_odd_isLowerSieveWeights m).on _)
  have hmain := abs_brunPure_mainTerm_sub_eulerProd_le s z (2 * m + 1)
  have hX_main :
      s.X * s.eulerProd z -
          |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ) ≤
        s.X * (∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m + 1) d * s.density d) := by
    have hdiff : s.X * (s.eulerProd z -
        ∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m + 1) d * s.density d) ≤
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ) := by
      calc
        s.X * (s.eulerProd z -
            ∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m + 1) d * s.density d)
            ≤ |s.X * (s.eulerProd z -
                ∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m + 1) d * s.density d)| :=
              le_abs_self _
        _ = |s.X| * |∑ d ∈ (s.prodPrimes z).divisors, brunPureWeights (2 * m + 1) d * s.density d -
              s.eulerProd z| := by rw [abs_mul, abs_sub_comm]
        _ ≤ |s.X| * ((Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 2) /
              ((2 * m + 2).factorial : ℝ)) := by
              gcongr
        _ = |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 2) /
              ((2 * m + 2).factorial : ℝ) := by ring
    linarith
  have hrem_le :
      ∑ d ∈ (s.prodPrimes z).divisors, |brunPureWeights (2 * m + 1) d| * |s.rem d| ≤
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m + 1, |s.rem d| := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases hcard : d.primeFactors.card ≤ 2 * m + 1
    · simp only [hcard, ↓reduceIte]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_brunPureWeights_le_one (2 * m + 1) d)
    · simp [brunPureWeights, hcard]
  linarith

/-- **Brun's pure sieve absolute error estimate** (`r = 2 * m`, `1 ≤ m`):
when `log (V(z)⁻¹) ≤ 2 * m + 1`,
`|S(A, P, z) - X * V(z)| ≤ |X| * (e * log (V(z)⁻¹))^(2m) / (2m)! + ∑_{ω(d) ≤ 2m} |r_d|`,
and in fact with the sharper `|X| * (log (V(z)⁻¹))^(2m) / (2m)!` and explicit `(e * log V⁻¹ / (2m))^(2m)` forms. -/
theorem brun_pure_abs_sub_le (s : SieveData) (z : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (hL : Real.log ((s.eulerProd z)⁻¹) ≤ 2 * m + 1) :
    |(siftedCount s.A s.prodPrimes z : ℝ) - s.X * s.eulerProd z| ≤
      |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m) / ((2 * m).factorial : ℝ) +
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m, |s.rem d| := by
  have hL_nn : 0 ≤ Real.log ((s.eulerProd z)⁻¹) := by
    rw [Real.log_inv]
    have hpos : 0 < s.eulerProd z := s.eulerProd_pos z
    have hle : s.eulerProd z ≤ 1 := s.eulerProd_le_one z
    linarith [Real.log_nonpos hpos.le hle]
  have hratio : (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤
      (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m) / ((2 * m).factorial : ℝ) := by
    have hfac_pos : (0 : ℝ) < ((2 * m).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h2m1_pos : (0 : ℝ) < (2 * m + 1 : ℝ) := by positivity
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    have h1 : (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m) * Real.log ((s.eulerProd z)⁻¹) /
        (((2 : ℝ) * (m : ℝ) + 1) * ((2 * m).factorial : ℝ)) =
        ((Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (Real.log ((s.eulerProd z)⁻¹) / (2 * m + 1 : ℝ)) := by
      field_simp [hfac_pos.ne', h2m1_pos.ne']
    rw [h1]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one h2m1_pos).mpr hL)
  have hup := brun_pure_upper s z m
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hk_odd : 2 * k + 1 = 2 * m - 1 := by omega
  have hlo := brun_pure_lower s z k
  have hk2 : 2 * k + 2 = 2 * m := by omega
  rw [hk2, hk_odd] at hlo
  have hrem_sub :
      ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m - 1, |s.rem d| ≤
        ∑ d ∈ (s.prodPrimes z).divisors with d.primeFactors.card ≤ 2 * m, |s.rem d| := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun _ _ _ => abs_nonneg _)
    simp only [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Nat.sub_le _ _)⟩
  rw [abs_le]
  constructor
  · linarith
  · have hmul : |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) /
        ((2 * m + 1).factorial : ℝ) ≤
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m) / ((2 * m).factorial : ℝ) := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
    linarith

/-- Explicit `(e * log (V(z)⁻¹) / r)^r` and `(e * log (V(z)⁻¹))^r / r!` forms of the Brun pure
sieve main-term error for `1 ≤ r` (`r = 2 * m`). -/
theorem brun_pure_factorial_le_exp_bound (s : SieveData) (z : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ r / (r.factorial : ℝ) ≤
      |s.X| * (Real.exp 1 * Real.log ((s.eulerProd z)⁻¹) / (r : ℝ)) ^ r ∧
    |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ r / (r.factorial : ℝ) ≤
      |s.X| * (Real.exp 1 * Real.log ((s.eulerProd z)⁻¹)) ^ r / (r.factorial : ℝ) := by
  have hL_nn : 0 ≤ Real.log ((s.eulerProd z)⁻¹) := by
    rw [Real.log_inv]
    linarith [Real.log_nonpos (s.eulerProd_pos z).le (s.eulerProd_le_one z)]
  have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  refine ⟨?_, ?_⟩
  · have h1 := inv_factorial_le_exp_div_pow hr
    calc
      |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ r / (r.factorial : ℝ)
          = |s.X| * ((Real.log ((s.eulerProd z)⁻¹)) ^ r * (r.factorial : ℝ)⁻¹) := by ring
      _ ≤ |s.X| * ((Real.log ((s.eulerProd z)⁻¹)) ^ r * (Real.exp 1 / (r : ℝ)) ^ r) := by
            gcongr
      _ = |s.X| * (Real.exp 1 * Real.log ((s.eulerProd z)⁻¹) / (r : ℝ)) ^ r := by
            rw [← mul_pow]
            ring_nf
  · have hpow : (Real.log ((s.eulerProd z)⁻¹)) ^ r ≤
        (Real.exp 1 * Real.log ((s.eulerProd z)⁻¹)) ^ r := by
      gcongr
      exact le_mul_of_one_le_left hL_nn hexp1
    gcongr

end BrunsPureSieve

/-! ### Buchstab's Identity -/

section BuchstabIdentity

/-- **Buchstab's exact combinatorial identity** for arbitrary prime finsets `S_w ⊆ S_z`
that are downward-closed (`∀ p ∈ S_z, ∀ q ∈ S_w, p ≤ q → p ∈ S_w`):
`S(A, ∏_{S_w} p) = S(A, ∏_{S_z} p) + ∑_{p ∈ S_z \ S_w} S(A_p, ∏_{q ∈ S_z, q < p} q)`. -/
theorem buchstab_identity_finset (A : Finset ℕ) {S_w S_z : Finset ℕ}
    (hsub : S_w ⊆ S_z) (hdown : ∀ p ∈ S_z, ∀ q ∈ S_w, p ≤ q → p ∈ S_w)
    (hprimes : ∀ p ∈ S_z, p.Prime) :
    siftedCountOf A (∏ p ∈ S_w, p) =
      siftedCountOf A (∏ p ∈ S_z, p) +
        ∑ p ∈ S_z \ S_w,
          siftedCountOf (sieveMultiple A p) (∏ q ∈ S_z.filter (· < p), q) := by
  let P_w := ∏ p ∈ S_w, p
  let P_z := ∏ p ∈ S_z, p
  let C_w := A.filter (fun n => Nat.Coprime n P_w)
  let C_z := A.filter (fun n => Nat.Coprime n P_z)
  have hCz_sub : C_z ⊆ C_w := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2.coprime_dvd_right
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)⟩
  have hpart : C_w.card = C_z.card + (C_w \ C_z).card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
      Finset.union_sdiff_of_subset hCz_sub]
  have hP_cop_iff : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ n : ℕ,
      Nat.Coprime n (∏ p ∈ S, p) ↔ ∀ p ∈ S, ¬ p ∣ n := by
    intro S hS n
    constructor
    · intro hcop p hp hpn
      have hp_dvd_prod : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem _ hp
      have h1 : p ∣ Nat.gcd n (∏ q ∈ S, q) := Nat.dvd_gcd hpn hp_dvd_prod
      rw [hcop] at h1
      exact (hS p hp).ne_one (Nat.dvd_one.mp h1)
    · intro hnot
      rw [Nat.coprime_comm]
      exact Nat.Coprime.prod_left fun p hp =>
        (Nat.Prime.coprime_iff_not_dvd (hS p hp)).mpr (hnot p hp)
  let B : ℕ → Finset ℕ := fun p =>
    (sieveMultiple A p).filter (fun n => Nat.Coprime n (∏ q ∈ S_z.filter (· < p), q))
  have hdisj : ((S_z \ S_w : Finset ℕ) : Set ℕ).PairwiseDisjoint B := by
    intro p₁ hp₁ p₂ hp₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    have hn1' := Finset.mem_filter.mp hn1
    have hn2' := Finset.mem_filter.mp hn2
    have hp1n : p₁ ∣ n := (mem_sieveMultiple_iff.mp hn1'.1).2
    have hp2n : p₂ ∣ n := (mem_sieveMultiple_iff.mp hn2'.1).2
    have hp1_Sz : p₁ ∈ S_z := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hp₁)).1
    have hp2_Sz : p₂ ∈ S_z := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hp₂)).1
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hcop2 := (hP_cop_iff _ (fun q hq => hprimes q (Finset.mem_filter.mp hq).1) n).mp
        hn2'.2 p₁ (Finset.mem_filter.mpr ⟨hp1_Sz, hlt⟩)
      exact hcop2 hp1n
    · have hcop1 := (hP_cop_iff _ (fun q hq => hprimes q (Finset.mem_filter.mp hq).1) n).mp
        hn1'.2 p₂ (Finset.mem_filter.mpr ⟨hp2_Sz, hlt⟩)
      exact hcop1 hp2n
  have hunion_eq : (S_z \ S_w).biUnion B = C_w \ C_z := by
    ext n
    simp only [C_w, C_z, P_w, P_z, Finset.mem_biUnion, Finset.mem_sdiff, B, Finset.mem_filter,
      mem_sieveMultiple_iff]
    constructor
    · rintro ⟨p, ⟨hpz, hpw⟩, ⟨hnA, hpn⟩, hcop_lt⟩
      refine ⟨⟨hnA, ?_⟩, fun hmem => ?_⟩
      · rw [hP_cop_iff S_w (fun q hq => hprimes q (hsub hq)) n]
        intro q hqw hqn
        have hqz : q ∈ S_z := hsub hqw
        have hlt_qp : q < p := by
          by_contra hle
          exact hpw (hdown p hpz q hqw (not_lt.mp hle))
        exact (hP_cop_iff _ (fun r hr => hprimes r (Finset.mem_filter.mp hr).1) n).mp
          hcop_lt q (Finset.mem_filter.mpr ⟨hqz, hlt_qp⟩) hqn
      · exact (hP_cop_iff S_z hprimes n).mp hmem.2 p hpz hpn
    · rintro ⟨⟨hnA, hcop_w⟩, hnot_z⟩
      have hnot_all : ¬ ∀ p ∈ S_z, ¬ p ∣ n := by
        intro hall
        exact hnot_z ⟨hnA, (hP_cop_iff S_z hprimes n).mpr hall⟩
      push Not at hnot_all
      let D := S_z.filter (fun p => p ∣ n)
      have hD_ne : D.Nonempty := by
        rcases hnot_all with ⟨p, hpz, hpn⟩
        exact ⟨p, Finset.mem_filter.mpr ⟨hpz, hpn⟩⟩
      let p := D.min' hD_ne
      have hpD : p ∈ D := Finset.min'_mem D hD_ne
      have hp_min : ∀ q ∈ D, p ≤ q := fun q hq => Finset.min'_le D q hq
      have hpz : p ∈ S_z := (Finset.mem_filter.mp hpD).1
      have hpn : p ∣ n := (Finset.mem_filter.mp hpD).2
      have hpw : p ∉ S_w := fun hpw =>
        (hP_cop_iff S_w (fun q hq => hprimes q (hsub hq)) n).mp hcop_w p hpw hpn
      refine ⟨p, ⟨hpz, hpw⟩, ⟨hnA, hpn⟩, ?_⟩
      rw [hP_cop_iff _ (fun q hq => hprimes q (Finset.mem_filter.mp hq).1) n]
      intro q hq hqn
      have hq' := Finset.mem_filter.mp hq
      have hle := hp_min q (Finset.mem_filter.mpr ⟨hq'.1, hqn⟩)
      exact absurd hle (not_le.mpr hq'.2)
  have hcard_union : (C_w \ C_z).card = ∑ p ∈ S_z \ S_w, (B p).card := by
    rw [← hunion_eq, Finset.card_biUnion hdisj]
  change C_w.card = C_z.card + ∑ p ∈ S_z \ S_w, (B p).card
  rw [hpart, hcard_union]

/-- **Buchstab's identity** in `ℕ` for `primeProdLT`:
for `w ≤ z`, `S(A, P_{<}, w) = S(A, P_{<}, z) + ∑_{w ≤ p < z} S(A_p, P_{<}, p)`. -/
theorem buchstab_identity_nat (A : Finset ℕ) {w z : ℝ} (hwz : w ≤ z) :
    siftedCount A primeProdLT w =
      siftedCount A primeProdLT z +
        ∑ p ∈ (primeFinsetLT z).filter (fun p : ℕ => w ≤ (p : ℝ)),
          siftedCount (sieveMultiple A p) primeProdLT p := by
  have hsub := primeFinsetLT_mono hwz
  have hdown : ∀ p ∈ primeFinsetLT z, ∀ q ∈ primeFinsetLT w, p ≤ q → p ∈ primeFinsetLT w := by
    intro p hp q hq hpq
    rw [mem_primeFinsetLT_iff] at hp hq ⊢
    exact ⟨hp.1, (by exact_mod_cast hpq : (p : ℝ) ≤ q).trans_lt hq.2⟩
  have hprimes : ∀ p ∈ primeFinsetLT z, p.Prime := fun _ hp => prime_of_mem_primeFinsetLT hp
  have hmain := buchstab_identity_finset A hsub hdown hprimes
  change siftedCountOf A (primeProdLT w) = siftedCountOf A (primeProdLT z) + _
  rw [primeProdLT, primeProdLT, hmain]
  congr 1
  have hsdiff : primeFinsetLT z \ primeFinsetLT w =
      (primeFinsetLT z).filter (fun p : ℕ => w ≤ (p : ℝ)) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, mem_primeFinsetLT_iff]
    constructor
    · rintro ⟨⟨hp, hpz⟩, hnot⟩
      refine ⟨⟨hp, hpz⟩, ?_⟩
      by_contra hlt
      exact hnot ⟨hp, not_le.mp hlt⟩
    · rintro ⟨⟨hp, hpz⟩, hwp⟩
      exact ⟨⟨hp, hpz⟩, fun ⟨_, hpw⟩ => not_le.mpr hpw hwp⟩
  rw [hsdiff]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp_lt : (p : ℝ) < z := (mem_primeFinsetLT_iff.mp (Finset.mem_filter.mp hp).1).2
  have hflt : (primeFinsetLT z).filter (· < p) = primeFinsetLT p := by
    ext q
    simp only [Finset.mem_filter, mem_primeFinsetLT_iff]
    constructor
    · rintro ⟨⟨hq, _⟩, hqp⟩
      exact ⟨hq, by exact_mod_cast hqp⟩
    · rintro ⟨hq, hqp⟩
      have hqp_nat : q < p := by exact_mod_cast hqp
      exact ⟨⟨hq, hqp.trans hp_lt⟩, hqp_nat⟩
  rw [hflt]
  rfl

/-- **Buchstab's identity** in `ℝ` for `primeProdLT`:
for `w ≤ z`, `S(A, P_{<}, z) = S(A, P_{<}, w) - ∑_{w ≤ p < z} S(A_p, P_{<}, p)`. -/
theorem buchstab_identity (A : Finset ℕ) {w z : ℝ} (hwz : w ≤ z) :
    (siftedCount A primeProdLT z : ℝ) =
      (siftedCount A primeProdLT w : ℝ) -
        ∑ p ∈ (primeFinsetLT z).filter (fun p : ℕ => w ≤ (p : ℝ)),
          (siftedCount (sieveMultiple A p) primeProdLT p : ℝ) := by
  have hnat := congrArg (Nat.cast (R := ℝ)) (buchstab_identity_nat A hwz)
  rw [Nat.cast_add, Nat.cast_sum] at hnat
  linarith

/-- **Buchstab's identity** for `primeProd` (`P(z) = ∏_{p ≤ z} p`):
for `w ≤ z`, `S(A, P, z) = S(A, P, w) - ∑_{w < p ≤ z} S(A_p, P, p - 1)`. -/
theorem buchstab_identity_primeProd (A : Finset ℕ) {w z : ℝ} (hwz : w ≤ z) :
    (siftedCount A primeProd z : ℝ) =
      (siftedCount A primeProd w : ℝ) -
        ∑ p ∈ (primeFinset z).filter (fun p : ℕ => w < (p : ℝ)),
          (siftedCount (sieveMultiple A p) primeProd ((p : ℝ) - 1) : ℝ) := by
  have hsub := primeFinset_mono hwz
  have hdown : ∀ p ∈ primeFinset z, ∀ q ∈ primeFinset w, p ≤ q → p ∈ primeFinset w := by
    intro p hp q hq hpq
    rw [mem_primeFinset_iff] at hp hq ⊢
    exact ⟨hp.1, (by exact_mod_cast hpq : (p : ℝ) ≤ q).trans hq.2⟩
  have hprimes : ∀ p ∈ primeFinset z, p.Prime := fun _ hp => prime_of_mem_primeFinset hp
  have hmain := buchstab_identity_finset A hsub hdown hprimes
  have hsdiff : primeFinset z \ primeFinset w =
      (primeFinset z).filter (fun p : ℕ => w < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, mem_primeFinset_iff]
    constructor
    · rintro ⟨⟨hp, hpz⟩, hnot⟩
      refine ⟨⟨hp, hpz⟩, ?_⟩
      by_contra hle
      exact hnot ⟨hp, not_lt.mp hle⟩
    · rintro ⟨⟨hp, hpz⟩, hwp⟩
      exact ⟨⟨hp, hpz⟩, fun ⟨_, hpw⟩ => not_lt.mpr hpw hwp⟩
  have hsum_eq :
      ∑ p ∈ primeFinset z \ primeFinset w,
          siftedCountOf (sieveMultiple A p) (∏ q ∈ (primeFinset z).filter (· < p), q) =
        ∑ p ∈ (primeFinset z).filter (fun p : ℕ => w < (p : ℝ)),
          siftedCount (sieveMultiple A p) primeProd ((p : ℝ) - 1) := by
    rw [hsdiff]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_filter.mp hp
    have hp_prime := prime_of_mem_primeFinset hp'.1
    have hp_le : (p : ℝ) ≤ z := (mem_primeFinset_iff.mp hp'.1).2
    have hflt : (primeFinset z).filter (· < p) = primeFinsetLT (p : ℝ) := by
      ext q
      simp only [Finset.mem_filter, mem_primeFinset_iff, mem_primeFinsetLT_iff]
      constructor
      · rintro ⟨⟨hq, _⟩, hqp⟩
        exact ⟨hq, by exact_mod_cast hqp⟩
      · rintro ⟨hq, hqp⟩
        have hqp_nat : q < p := by exact_mod_cast hqp
        exact ⟨⟨hq, hqp.le.trans hp_le⟩, hqp_nat⟩
    rw [hflt]
    change siftedCountOf (sieveMultiple A p) (primeProdLT (p : ℝ)) =
      siftedCountOf (sieveMultiple A p) (primeProd ((p : ℝ) - 1))
    rw [primeProdLT_natCast_eq_primeProd_sub_one hp_prime.one_le]
  have hnat : siftedCount A primeProd w = siftedCount A primeProd z +
      ∑ p ∈ (primeFinset z).filter (fun p : ℕ => w < (p : ℝ)),
        siftedCount (sieveMultiple A p) primeProd ((p : ℝ) - 1) := by
    rw [← hsum_eq]
    exact hmain
  have hR := congrArg (Nat.cast (R := ℝ)) hnat
  rw [Nat.cast_add, Nat.cast_sum] at hR
  linarith

end BuchstabIdentity

/-! ### Rosser–Iwaniec Combinatorial Sieve Weights (`betaSieve`) -/

section RosserIwaniecSieve

/-- Descending list of prime factors of `d : ℕ`: `[p_1, p_2, ..., p_r]` with `p_1 > ... > p_r`. -/
def descPrimeList (d : ℕ) : List ℕ :=
  (d.primeFactors.sort (· ≤ ·)).reverse

/-- `descPrimeList 1 = []`. -/
@[simp]
theorem descPrimeList_one : descPrimeList 1 = [] := by
  simp [descPrimeList]

/-- Membership in `descPrimeList d` coincides with membership in `d.primeFactors`. -/
theorem mem_descPrimeList_iff {d p : ℕ} : p ∈ descPrimeList d ↔ p ∈ d.primeFactors := by
  simp [descPrimeList, List.mem_reverse, Finset.mem_sort]

/-- Every element of `descPrimeList d` is prime. -/
theorem prime_of_mem_descPrimeList {d p : ℕ} (hp : p ∈ descPrimeList d) : p.Prime :=
  Nat.prime_of_mem_primeFactors (mem_descPrimeList_iff.mp hp)

/-- `descPrimeList d` has no duplicates. -/
theorem descPrimeList_nodup (d : ℕ) : (descPrimeList d).Nodup := by
  unfold descPrimeList
  exact List.nodup_reverse.mpr (Finset.sort_nodup _ _)

/-- `descPrimeList d` is strictly decreasing (`Pairwise (· > ·)`). -/
theorem descPrimeList_pairwise_gt (d : ℕ) : (descPrimeList d).Pairwise (· > ·) := by
  have hsorted : (d.primeFactors.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnodup : (d.primeFactors.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have hlt : (d.primeFactors.sort (· ≤ ·)).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem] at hsorted ⊢
    intro i j hi hj hij
    have hle := hsorted i j hi hj hij
    have hne : (d.primeFactors.sort (· ≤ ·))[i] ≠ (d.primeFactors.sort (· ≤ ·))[j] :=
      hnodup.getElem_inj_iff.ne.mpr (Nat.ne_of_lt hij)
    exact lt_of_le_of_ne hle hne
  simpa [descPrimeList] using List.pairwise_reverse.mpr hlt

/-- For squarefree `d`, `(descPrimeList d).prod = d`. -/
theorem prod_descPrimeList_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (descPrimeList d).prod = d := by
  unfold descPrimeList
  rw [List.prod_reverse, ← Multiset.prod_coe, Finset.sort_eq]
  simpa using Nat.prod_primeFactors_of_squarefree hd

/-- Prepending a prime strictly larger than all elements of `e.primeFactors` gives
`descPrimeList (p * e) = p :: descPrimeList e`. -/
theorem descPrimeList_mul_of_gt {p e : ℕ} (hp : p.Prime) (he : e ≠ 0)
    (hlt : ∀ q ∈ e.primeFactors, q < p) :
    descPrimeList (p * e) = p :: descPrimeList e := by
  have hcop : p.Coprime e := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpe
    have hmem : p ∈ e.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpe, he⟩
    exact (hlt p hmem).false
  have hpf : (p * e).primeFactors = insert p e.primeFactors := by
    rw [Nat.Coprime.primeFactors_mul hcop, Nat.Prime.primeFactors hp]
    ext q
    simp [Finset.mem_insert]
  have hp_not_mem : p ∉ e.primeFactors := fun h => (hlt p h).false
  have hperm : (descPrimeList (p * e)).Perm (p :: descPrimeList e) := by
    rw [List.perm_iff_count]
    intro q
    have hn1 := descPrimeList_nodup (p * e)
    have hn2 : (p :: descPrimeList e).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hp_not_mem (mem_descPrimeList_iff.mp h), descPrimeList_nodup e⟩
    rw [hn1.count, hn2.count]
    by_cases hq : q ∈ descPrimeList (p * e)
    · have hq2 : q ∈ p :: descPrimeList e := by
        rw [mem_descPrimeList_iff, hpf, Finset.mem_insert] at hq
        rw [List.mem_cons, mem_descPrimeList_iff]
        exact hq
      simp [hq, hq2]
    · have hq2 : q ∉ p :: descPrimeList e := by
        rw [mem_descPrimeList_iff, hpf, Finset.mem_insert] at hq
        rw [List.mem_cons, mem_descPrimeList_iff]
        exact hq
      simp [hq, hq2]
  have hp_gt : (p :: descPrimeList e).Pairwise (· > ·) := by
    refine List.pairwise_cons.mpr ⟨fun q hq => ?_, descPrimeList_pairwise_gt e⟩
    exact hlt q (mem_descPrimeList_iff.mp hq)
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => absurd h1 (lt_asymm h2))
    (descPrimeList_pairwise_gt (p * e)) hp_gt

mutual
/-- Mutual recursive upper-sieve truncation condition on a descending prime list `L`:
`rosserCondPlus C [p_1, p_2, ...]` checks `C [p_1]`, `C [p_1, p_2, p_3]`, etc. -/
def rosserCondPlus (C : List ℕ → Prop) : List ℕ → Prop
  | [] => True
  | p :: t => C [p] ∧ rosserCondMinus (fun u => C (p :: u)) t
termination_by L => L.length

/-- Mutual recursive lower-sieve truncation condition on a descending prime list `L`:
`rosserCondMinus C [p_1, p_2, ...]` checks `C [p_1, p_2]`, `C [p_1, p_2, p_3, p_4]`, etc. -/
def rosserCondMinus (C : List ℕ → Prop) : List ℕ → Prop
  | [] => True
  | p :: t => rosserCondPlus (fun u => C (p :: u)) t
termination_by L => L.length
end

/-- Equivalence between `rosserCondPlus C L` and checking `C (L.take j)` at all odd `j ≤ L.length`,
and simultaneously for `rosserCondMinus C L` at all even `2 ≤ j ≤ L.length`. -/
theorem rosserCond_iff_prefixes :
    ∀ (L : List ℕ) (C : List ℕ → Prop),
      (rosserCondPlus C L ↔ ∀ j : ℕ, Odd j → j ≤ L.length → C (L.take j)) ∧
      (rosserCondMinus C L ↔ ∀ j : ℕ, Even j → 2 ≤ j → j ≤ L.length → C (L.take j))
  | [], C => by
      constructor
      · simp only [rosserCondPlus, List.length_nil, true_iff]
        intro j hj hlen
        have hj0 : j = 0 := Nat.le_zero.mp hlen
        subst hj0
        exact absurd hj (by decide)
      · simp only [rosserCondMinus, List.length_nil]
        constructor
        · intro _ j _ h2 hlen
          omega
        · intro _
          trivial
  | p :: t, C => by
      have ih := rosserCond_iff_prefixes t (fun u => C (p :: u))
      refine ⟨?_, ?_⟩
      · simp only [rosserCondPlus, List.length_cons, ih.2]
        constructor
        · rintro ⟨hp, ht⟩ j hj hlen
          rcases j with _ | j
          · exact absurd hj (by decide)
          · rcases j with _ | k
            · simpa using hp
            · have heven : Even (k + 1) := by
                rw [Nat.odd_iff] at hj
                rw [Nat.even_iff]
                omega
              rcases heven with ⟨m, hm⟩
              have hk2 : 2 ≤ k + 1 := by omega
              have hkt : k + 1 ≤ t.length := by omega
              exact ht (k + 1) ⟨m, hm⟩ hk2 hkt
        · intro hall
          refine ⟨by simpa using hall 1 (by decide) (by omega), fun j hev hj2 hjt => ?_⟩
          have hodd : Odd (j + 1) := hev.add_one
          simpa [List.take_succ_cons] using hall (j + 1) hodd (by omega)
      · simp only [rosserCondMinus, List.length_cons, ih.1]
        constructor
        · intro ht j hev hj2 hlen
          rcases j with _ | k
          · omega
          · have hodd : Odd k := by
              rw [Nat.even_iff] at hev
              rw [Nat.odd_iff]
              omega
            simpa [List.take_succ_cons] using ht k hodd (by omega)
        · intro hall j hj hjt
          have hev : Even (j + 1) := hj.add_one
          rcases hj with ⟨m, hm⟩
          have hj2 : 2 ≤ j + 1 := by omega
          simpa [List.take_succ_cons] using hall (j + 1) hev hj2 (by omega)

private lemma sum_map_sublists_cons_aux (p : ℕ) (f : List ℕ → ℝ) :
    ∀ (l : List (List ℕ)),
      ((l.flatMap (fun x => [x, p :: x])).map f).sum =
        (l.map f).sum + (l.map (fun d => f (p :: d))).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons,
        List.sum_cons, sum_map_sublists_cons_aux p f xs]
      ring

/-- Split the sum over sublists according to whether the first entry is selected. -/
theorem sum_sublists_cons (p : ℕ) (L : List ℕ) (f : List ℕ → ℝ) :
    ((p::L).sublists.map f).sum=(L.sublists.map f).sum+(L.sublists.map (fun d => f (p::d))).sum := by
  rw [List.sublists_cons]
  exact sum_map_sublists_cons_aux p f L.sublists

private lemma sum_sublists_rosserCond :
    ∀ (L : List ℕ) (C : List ℕ → Prop), L ≠ [] →
      (0 : ℝ) ≤ (L.sublists.map (fun d =>
          (-1 : ℝ) ^ d.length * (if rosserCondPlus C d then (1 : ℝ) else 0))).sum ∧
      (L.sublists.map (fun d =>
          (-1 : ℝ) ^ d.length * (if rosserCondMinus C d then (1 : ℝ) else 0))).sum ≤ (0 : ℝ)
  | [], _, hne => absurd rfl hne
  | [p], C, _ => by
      have hsub : ([p] : List ℕ).sublists = [[], [p]] := by
        rw [List.sublists_cons, List.sublists_nil]
        rfl
      rw [hsub]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_nil, List.length_cons, pow_zero, one_mul,
        rosserCondPlus, rosserCondMinus, and_true, ↓reduceIte, add_zero]
      refine ⟨?_, by norm_num⟩
      split_ifs <;> norm_num
  | p :: q :: t, C, _ => by
      have htne : q :: t ≠ [] := List.cons_ne_nil _ _
      have ih_self := sum_sublists_rosserCond (q :: t) C htne
      have ih_shift := sum_sublists_rosserCond (q :: t) (fun u => C (p :: u)) htne
      have hsplit : ∀ (f : List ℕ → ℝ),
          ((p :: q :: t).sublists.map f).sum =
            ((q :: t).sublists.map f).sum + ((q :: t).sublists.map (fun d => f (p :: d))).sum := by
        intro f
        rw [List.sublists_cons]
        exact sum_map_sublists_cons_aux p f (q :: t).sublists
      refine ⟨?_, ?_⟩
      · rw [hsplit]
        have h2 : ((q :: t).sublists.map (fun d =>
            (-1 : ℝ) ^ (p :: d).length *
              (if rosserCondPlus C (p :: d) then (1 : ℝ) else 0))).sum =
            -(if C [p] then ((q :: t).sublists.map (fun d =>
              (-1 : ℝ) ^ d.length *
                (if rosserCondMinus (fun u => C (p :: u)) d then (1 : ℝ) else 0))).sum else 0) := by
          by_cases hCp : C [p]
          · simp only [hCp, ↓reduceIte, rosserCondPlus, true_and, List.length_cons, pow_succ]
            clear ih_self ih_shift hsplit
            induction (q :: t).sublists with
            | nil => simp
            | cons d ds ih =>
                simp only [List.map_cons, List.sum_cons] at ih ⊢
                rw [ih]
                ring
          · simp only [hCp, ↓reduceIte, rosserCondPlus, false_and]
            clear ih_self ih_shift hsplit
            induction (q :: t).sublists with
            | nil => simp
            | cons d ds ih =>
                simp only [List.map_cons, List.sum_cons, mul_zero, zero_add] at ih ⊢
                exact ih
        rw [h2]
        by_cases hCp : C [p]
        · simp only [hCp, ↓reduceIte]
          linarith [ih_self.1, ih_shift.2]
        · simp only [hCp, ↓reduceIte, neg_zero, add_zero]
          exact ih_self.1
      · rw [hsplit]
        have h2 : ((q :: t).sublists.map (fun d =>
            (-1 : ℝ) ^ (p :: d).length *
              (if rosserCondMinus C (p :: d) then (1 : ℝ) else 0))).sum =
            -((q :: t).sublists.map (fun d =>
              (-1 : ℝ) ^ d.length *
                (if rosserCondPlus (fun u => C (p :: u)) d then (1 : ℝ) else 0))).sum := by
          simp only [rosserCondMinus, List.length_cons, pow_succ]
          clear ih_self ih_shift hsplit
          induction (q :: t).sublists with
          | nil => simp
          | cons d ds ih =>
              simp only [List.map_cons, List.sum_cons] at ih ⊢
              rw [ih]
              ring
        rw [h2]
        linarith [ih_self.2, ih_shift.1]

/-- Rosser–Iwaniec upper sieve weights associated with a prefix predicate `C : List ℕ → Prop`
applied to the descending prime factorization `descPrimeList d`. -/
def rosserWeightsPlus (C : List ℕ → Prop) (d : ℕ) : ℝ :=
  if Squarefree d ∧ d ≠ 0 ∧ rosserCondPlus C (descPrimeList d) then (μ d : ℝ) else 0

/-- Rosser–Iwaniec lower sieve weights associated with a prefix predicate `C : List ℕ → Prop`
applied to the descending prime factorization `descPrimeList d`. -/
def rosserWeightsMinus (C : List ℕ → Prop) (d : ℕ) : ℝ :=
  if Squarefree d ∧ d ≠ 0 ∧ rosserCondMinus C (descPrimeList d) then (μ d : ℝ) else 0

/-- At `d = 1`, `rosserWeightsPlus C 1 = 1`. -/
@[simp]
theorem rosserWeightsPlus_one (C : List ℕ → Prop) : rosserWeightsPlus C 1 = 1 := by
  simp [rosserWeightsPlus, rosserCondPlus]

/-- At `d = 1`, `rosserWeightsMinus C 1 = 1`. -/
@[simp]
theorem rosserWeightsMinus_one (C : List ℕ → Prop) : rosserWeightsMinus C 1 = 1 := by
  simp [rosserWeightsMinus, rosserCondMinus]

/-- `|rosserWeightsPlus C d| ≤ 1` for all `d : ℕ`. -/
theorem abs_rosserWeightsPlus_le_one (C : List ℕ → Prop) (d : ℕ) :
    |rosserWeightsPlus C d| ≤ 1 := by
  unfold rosserWeightsPlus
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  · norm_num

/-- `|rosserWeightsMinus C d| ≤ 1` for all `d : ℕ`. -/
theorem abs_rosserWeightsMinus_le_one (C : List ℕ → Prop) (d : ℕ) :
    |rosserWeightsMinus C d| ≤ 1 := by
  unfold rosserWeightsMinus
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  · norm_num

private lemma primeFactors_list_prod :
    ∀ {s : List ℕ}, s.Nodup → (∀ p ∈ s, p.Prime) → s.prod.primeFactors = s.toFinset
  | [], _, _ => by simp
  | a :: t, hnd, hp => by
      have ha_prime : a.Prime := hp a (by simp)
      have ha_not : a ∉ t := (List.nodup_cons.mp hnd).1
      have ht_nd : t.Nodup := (List.nodup_cons.mp hnd).2
      have ht_p : ∀ q ∈ t, q.Prime := fun q hq => hp q (by simp [hq])
      have ih := primeFactors_list_prod ht_nd ht_p
      have ht_nz : t.prod ≠ 0 := List.prod_ne_zero fun h0 => (ht_p 0 h0).ne_zero rfl
      have hcop : a.Coprime t.prod := by
        rw [Nat.Prime.coprime_iff_not_dvd ha_prime]
        intro hdvd
        have ha_mem : a ∈ t.prod.primeFactors := Nat.mem_primeFactors.mpr ⟨ha_prime, hdvd, ht_nz⟩
        rw [ih, List.mem_toFinset] at ha_mem
        exact ha_not ha_mem
      rw [List.prod_cons, Nat.Coprime.primeFactors_mul hcop, Nat.Prime.primeFactors ha_prime, ih]
      ext q
      simp [List.mem_toFinset]

/-- Sum over divisors of a squarefree integer by selecting ordered sublists of its prime factors. -/
theorem sum_divisors_eq_sum_sublists_of_squarefree {n : ℕ} (hn : Squarefree n)
    (f : List ℕ → ℝ) (g : ℕ → ℝ) (hfg : ∀ d : ℕ, d ∣ n → g d = f (descPrimeList d)) :
    ∑ d ∈ n.divisors, g d = ((descPrimeList n).sublists.map f).sum := by
  let L := descPrimeList n
  have hL_nodup : L.Nodup := descPrimeList_nodup n
  have hL_prime : ∀ p ∈ L, p.Prime := fun p hp => prime_of_mem_descPrimeList hp
  have hL_gt : L.Pairwise (· > ·) := descPrimeList_pairwise_gt n
  have hsub_nodup : ∀ s ∈ L.sublists, s.Nodup := fun s hs => hL_nodup.sublist (List.mem_sublists.mp hs)
  have hsub_gt : ∀ s ∈ L.sublists, s.Pairwise (· > ·) := fun s hs =>
    hL_gt.sublist (List.mem_sublists.mp hs)
  have hsub_prime : ∀ s ∈ L.sublists, ∀ p ∈ s, p.Prime := fun s hs p hp =>
    hL_prime p ((List.mem_sublists.mp hs).subset hp)
  have hdesc_sub : ∀ s ∈ L.sublists, descPrimeList s.prod = s := by
    intro s hs
    have hsp := hsub_prime s hs
    have hsn := hsub_nodup s hs
    have hsg := hsub_gt s hs
    have hpf : s.prod.primeFactors = s.toFinset := primeFactors_list_prod hsn hsp
    have hperm : (descPrimeList s.prod).Perm s := by
      rw [List.perm_iff_count]
      intro q
      rw [(descPrimeList_nodup s.prod).count, hsn.count]
      simp [mem_descPrimeList_iff, hpf, List.mem_toFinset]
    exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => absurd h1 (lt_asymm h2))
      (descPrimeList_pairwise_gt s.prod) hsg
  have hsum_sub : ((L.sublists.map f).sum) = ∑ s ∈ L.sublists.toFinset, f s := by
    have hnodup_sub : L.sublists.Nodup := List.nodup_sublists.mpr hL_nodup
    rw [← List.sum_toFinset _ hnodup_sub]
  rw [hsum_sub]
  symm
  refine Finset.sum_bij (fun s _ => s.prod) ?_ ?_ ?_ ?_
  · intro s hs
    have hs' := List.mem_toFinset.mp hs
    have hprod_dvd : s.prod ∣ n := by
      rw [← prod_descPrimeList_of_squarefree hn]
      exact (List.mem_sublists.mp hs').prod_dvd_prod
    exact Nat.mem_divisors.mpr ⟨hprod_dvd, hn.ne_zero⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    have hs1' := List.mem_toFinset.mp hs₁
    have hs2' := List.mem_toFinset.mp hs₂
    rw [← hdesc_sub s₁ hs1', heq, hdesc_sub s₂ hs2']
  · intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdsq : Squarefree d := hn.squarefree_of_dvd hdn
    have hsub_pf : d.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hdn hn.ne_zero
    have hsub_list : List.Sublist (descPrimeList d) L := by
      have hsub_asc : List.Sublist (d.primeFactors.sort (· ≤ ·)) (n.primeFactors.sort (· ≤ ·)) := by
        refine List.sublist_of_subperm_of_pairwise (List.subperm_of_subset (Finset.sort_nodup _ _)
          fun p hp => (Finset.mem_sort _).mpr (hsub_pf ((Finset.mem_sort _).mp hp)))
          (Finset.pairwise_sort _ _) (Finset.pairwise_sort _ _)
      exact List.reverse_sublist.mpr hsub_asc
    refine ⟨descPrimeList d, List.mem_toFinset.mpr (List.mem_sublists.mpr hsub_list),
      prod_descPrimeList_of_squarefree hdsq⟩
  · intro s hs
    have hs' := List.mem_toFinset.mp hs
    have hprod_dvd : s.prod ∣ n := by
      rw [← prod_descPrimeList_of_squarefree hn]
      exact (List.mem_sublists.mp hs').prod_dvd_prod
    rw [hfg s.prod hprod_dvd, hdesc_sub s hs']

private lemma sum_divisors_rosserWeights_general (C : List ℕ → Prop) {n : ℕ} (hn0 : n ≠ 0) :
    (∑ d ∈ n.divisors, rosserWeightsPlus C d =
      ∑ d ∈ (∏ p ∈ n.primeFactors, p).divisors, rosserWeightsPlus C d) ∧
    (∑ d ∈ n.divisors, rosserWeightsMinus C d =
      ∑ d ∈ (∏ p ∈ n.primeFactors, p).divisors, rosserWeightsMinus C d) := by
  let m := ∏ p ∈ n.primeFactors, p
  have hm_sq : Squarefree m := Nat.squarefree_prod_primeFactors n
  have hm_dvd : m ∣ n := Nat.prod_primeFactors_dvd n
  have hsub : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn0 hm_dvd
  constructor
  · refine (Finset.sum_subset hsub fun d hd hdm => ?_).symm
    have hd_not_sq : ¬ Squarefree d := by
      intro hd_sq
      apply hdm
      refine Nat.mem_divisors.mpr ⟨?_, hm_sq.ne_zero⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
      exact Finset.prod_dvd_prod_of_subset _ _ _
        (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn0)
    simp [rosserWeightsPlus, hd_not_sq]
  · refine (Finset.sum_subset hsub fun d hd hdm => ?_).symm
    have hd_not_sq : ¬ Squarefree d := by
      intro hd_sq
      apply hdm
      refine Nat.mem_divisors.mpr ⟨?_, hm_sq.ne_zero⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
      exact Finset.prod_dvd_prod_of_subset _ _ _
        (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn0)
    simp [rosserWeightsMinus, hd_not_sq]

/-- General Rosser–Iwaniec weights `rosserWeightsPlus C` are global `UpperSieveWeights`
for any truncation condition `C : List ℕ → Prop`. -/
theorem rosserWeightsPlus_isUpperSieveWeights (C : List ℕ → Prop) :
    UpperSieveWeights (rosserWeightsPlus C) := by
  intro n
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hn1 : n = 1
  · subst hn1; simp
  simp only [hn1, ↓reduceIte]
  rw [(sum_divisors_rosserWeights_general C hn0).1]
  let m := ∏ p ∈ n.primeFactors, p
  have hm_sq : Squarefree m := Nat.squarefree_prod_primeFactors n
  have hm_pf : m.primeFactors = n.primeFactors := Nat.primeFactors_prod_primeFactors n
  have hm_ne1 : m ≠ 1 := by
    intro h1
    have hpf : n.primeFactors = ∅ := by rw [← hm_pf, h1, Nat.primeFactors_one]
    rw [Nat.primeFactors_eq_empty] at hpf
    rcases hpf with rfl | rfl <;> contradiction
  have hL_ne : descPrimeList m ≠ [] := by
    intro hnil
    have h1 : m = 1 := by
      rw [← prod_descPrimeList_of_squarefree hm_sq, hnil, List.prod_nil]
    exact hm_ne1 h1
  have hrew :
      ∑ d ∈ m.divisors, rosserWeightsPlus C d =
        ((descPrimeList m).sublists.map (fun L =>
          (-1 : ℝ) ^ L.length * (if rosserCondPlus C L then (1 : ℝ) else 0))).sum := by
    refine sum_divisors_eq_sum_sublists_of_squarefree hm_sq _ _ fun d hd => ?_
    have hdsq : Squarefree d := hm_sq.squarefree_of_dvd hd
    have hlen : (descPrimeList d).length = d.primeFactors.card := by
      simp [descPrimeList, Finset.length_sort]
    have hμ_prod : (μ d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
      calc
        (μ d : ℝ) = ((μ : ArithmeticFunction ℝ) d) := rfl
        _ = (μ : ArithmeticFunction ℝ) (∏ p ∈ d.primeFactors, p) := by
            rw [Nat.prod_primeFactors_of_squarefree hdsq]
        _ = ∏ p ∈ d.primeFactors, ((μ : ArithmeticFunction ℝ) p) :=
            (ArithmeticFunction.isMultiplicative_moebius.intCast.map_prod_of_subset_primeFactors
              d d.primeFactors subset_rfl)
        _ = ∏ _p ∈ d.primeFactors, (-1 : ℝ) := by
            refine Finset.prod_congr rfl fun p hp => ?_
            simp [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
        _ = (-1 : ℝ) ^ d.primeFactors.card := by simp
    unfold rosserWeightsPlus
    by_cases hc : rosserCondPlus C (descPrimeList d)
    · split_ifs with h
      · simp [hμ_prod, hlen]
      · exact absurd ⟨hdsq, hdsq.ne_zero, hc⟩ h
    · split_ifs with h
      · exact absurd h.2.2 hc
      · simp
  rw [hrew]
  exact (sum_sublists_rosserCond (descPrimeList m) C hL_ne).1

/-- General Rosser–Iwaniec weights `rosserWeightsMinus C` are global `LowerSieveWeights`
for any truncation condition `C : List ℕ → Prop`. -/
theorem rosserWeightsMinus_isLowerSieveWeights (C : List ℕ → Prop) :
    LowerSieveWeights (rosserWeightsMinus C) := by
  intro n
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hn1 : n = 1
  · subst hn1; simp
  simp only [hn1, ↓reduceIte]
  rw [(sum_divisors_rosserWeights_general C hn0).2]
  let m := ∏ p ∈ n.primeFactors, p
  have hm_sq : Squarefree m := Nat.squarefree_prod_primeFactors n
  have hm_pf : m.primeFactors = n.primeFactors := Nat.primeFactors_prod_primeFactors n
  have hm_ne1 : m ≠ 1 := by
    intro h1
    have hpf : n.primeFactors = ∅ := by rw [← hm_pf, h1, Nat.primeFactors_one]
    rw [Nat.primeFactors_eq_empty] at hpf
    rcases hpf with rfl | rfl <;> contradiction
  have hL_ne : descPrimeList m ≠ [] := by
    intro hnil
    have h1 : m = 1 := by
      rw [← prod_descPrimeList_of_squarefree hm_sq, hnil, List.prod_nil]
    exact hm_ne1 h1
  have hrew :
      ∑ d ∈ m.divisors, rosserWeightsMinus C d =
        ((descPrimeList m).sublists.map (fun L =>
          (-1 : ℝ) ^ L.length * (if rosserCondMinus C L then (1 : ℝ) else 0))).sum := by
    refine sum_divisors_eq_sum_sublists_of_squarefree hm_sq _ _ fun d hd => ?_
    have hdsq : Squarefree d := hm_sq.squarefree_of_dvd hd
    have hlen : (descPrimeList d).length = d.primeFactors.card := by
      simp [descPrimeList, Finset.length_sort]
    have hμ_prod : (μ d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
      calc
        (μ d : ℝ) = ((μ : ArithmeticFunction ℝ) d) := rfl
        _ = (μ : ArithmeticFunction ℝ) (∏ p ∈ d.primeFactors, p) := by
            rw [Nat.prod_primeFactors_of_squarefree hdsq]
        _ = ∏ p ∈ d.primeFactors, ((μ : ArithmeticFunction ℝ) p) :=
            (ArithmeticFunction.isMultiplicative_moebius.intCast.map_prod_of_subset_primeFactors
              d d.primeFactors subset_rfl)
        _ = ∏ _p ∈ d.primeFactors, (-1 : ℝ) := by
            refine Finset.prod_congr rfl fun p hp => ?_
            simp [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
        _ = (-1 : ℝ) ^ d.primeFactors.card := by simp
    unfold rosserWeightsMinus
    by_cases hc : rosserCondMinus C (descPrimeList d)
    · split_ifs with h
      · simp [hμ_prod, hlen]
      · exact absurd ⟨hdsq, hdsq.ne_zero, hc⟩ h
    · split_ifs with h
      · exact absurd h.2.2 hc
      · simp
  rw [hrew]
  exact (sum_sublists_rosserCond (descPrimeList m) C hL_ne).2

/-- The Rosser–Iwaniec `β`-sieve truncation factor `D_β([p_1, ..., p_r]) = (p_1 * ... * p_r) * p_r^β`. -/
def rosserTruncationFactor (β : ℝ) (L : List ℕ) : ℝ :=
  (L.prod : ℝ) * ((L.getLastD 1 : ℕ) : ℝ) ^ β

/-- Rosser–Iwaniec upper `β`-sieve weights (`betaSieveUpper β y`) enforcing
`D_β(p_1 ... p_j) < y` at odd prefixes `j` of the descending prime factorization. -/
def betaSieveUpper (β y : ℝ) : ℕ → ℝ :=
  rosserWeightsPlus (fun L => rosserTruncationFactor β L < y)

/-- Rosser–Iwaniec lower `β`-sieve weights (`betaSieveLower β y`) enforcing
`D_β(p_1 ... p_j) < y` at even prefixes `j ≥ 2` of the descending prime factorization. -/
def betaSieveLower (β y : ℝ) : ℕ → ℝ :=
  rosserWeightsMinus (fun L => rosserTruncationFactor β L < y)

/-- `betaSieveUpper β y` is global `UpperSieveWeights`. -/
theorem betaSieveUpper_isUpperSieveWeights (β y : ℝ) :
    UpperSieveWeights (betaSieveUpper β y) :=
  rosserWeightsPlus_isUpperSieveWeights _

/-- `betaSieveLower β y` is global `LowerSieveWeights`. -/
theorem betaSieveLower_isLowerSieveWeights (β y : ℝ) :
    LowerSieveWeights (betaSieveLower β y) :=
  rosserWeightsMinus_isLowerSieveWeights _

private lemma getLastD_eq_getLast' :
    ∀ {L : List ℕ} (h : L ≠ []) (d : ℕ), L.getLastD d = L.getLast h
  | [], h, _ => absurd rfl h
  | [a], _, _ => rfl
  | _ :: b :: t, _, d => by
      simp [List.getLastD, List.getLast]

private lemma descPrimeList_take_last_mul_last {L : List ℕ} (hL : L.Pairwise (· > ·))
    (hlen : 2 ≤ L.length) :
    (L.take (L.length - 1)).prod * L.getLast (List.ne_nil_of_length_pos (by omega)) = L.prod ∧
      L.getLast (List.ne_nil_of_length_pos (by omega)) <
        (L.take (L.length - 1)).getLast (List.ne_nil_of_length_pos (by
          rw [List.length_take]; omega)) := by
  let r := L.length
  have hr2 : 2 ≤ r := hlen
  let p_last := L[r - 1]
  let p_prev := L[r - 2]
  have htake_eq : L.take (r - 1) ++ [p_last] = L := by
    have hdrop : L.drop (r - 1) = [p_last] := by
      rw [List.drop_eq_getElem_cons (by omega)]
      have hdrop_r : L.drop r = [] := List.drop_eq_nil_iff.mpr le_rfl
      rw [show r - 1 + 1 = r by omega, hdrop_r]
    have h := List.take_append_drop (r - 1) L
    rwa [hdrop] at h
  have hprod : (L.take (r - 1)).prod * p_last = L.prod := by
    conv_rhs => rw [← htake_eq, List.prod_append, List.prod_singleton]
  have hlast_L : L.getLast (List.ne_nil_of_length_pos (by omega)) = p_last :=
    List.getLast_eq_getElem _
  have htake_len : (L.take (r - 1)).length = r - 1 := by
    rw [List.length_take]; omega
  have hlast_take :
      (L.take (r - 1)).getLast (List.ne_nil_of_length_pos (by omega)) = p_prev := by
    rw [List.getLast_eq_getElem]
    simp only [htake_len, List.getElem_take]
    rfl
  have hgt : p_last < p_prev := by
    rw [List.pairwise_iff_getElem] at hL
    exact hL (r - 2) (r - 1) (by omega) (by omega) (by omega)
  rw [hlast_L, hlast_take]
  exact ⟨hprod, hgt⟩

/-- Support bound for `betaSieveUpper`: for `1 ≤ β` and `1 < y`, `betaSieveUpper β y d = 0`
whenever `y ≤ (d : ℝ)`. -/
theorem betaSieveUpper_eq_zero_of_le {β y : ℝ} (hβ : 1 ≤ β) (hy : 1 < y) {d : ℕ}
    (hd : y ≤ (d : ℝ)) : betaSieveUpper β y d = 0 := by
  by_contra hne
  have hcond : Squarefree d ∧ d ≠ 0 ∧
      rosserCondPlus (fun L => rosserTruncationFactor β L < y) (descPrimeList d) := by
    unfold betaSieveUpper rosserWeightsPlus at hne
    split_ifs at hne with h
    · exact h
    · exact absurd rfl hne
  let L := descPrimeList d
  have hL_prod : L.prod = d := prod_descPrimeList_of_squarefree hcond.1
  have hL_primes : ∀ p ∈ L, p.Prime := fun p hp => prime_of_mem_descPrimeList hp
  have hL_pos : ∀ p ∈ L, 1 ≤ p := fun p hp => (hL_primes p hp).one_le
  have hL_pref : ∀ j : ℕ, Odd j → j ≤ L.length →
      rosserTruncationFactor β (L.take j) < y :=
    (rosserCond_iff_prefixes L _).1.mp hcond.2.2
  by_cases hlen0 : L.length = 0
  · have hnil : L = [] := List.length_eq_zero_iff.mp hlen0
    have hd1 : d = 1 := by rw [← hL_prod, hnil, List.prod_nil]
    rw [hd1, Nat.cast_one] at hd
    linarith
  rcases Nat.even_or_odd L.length with heven | hodd
  · have hlen2 : 2 ≤ L.length := by
      rcases heven with ⟨k, hk⟩
      omega
    have hodd1 : Odd (L.length - 1) := by
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at heven
      omega
    have htrunc := hL_pref (L.length - 1) hodd1 (Nat.sub_le _ _)
    have hstep := descPrimeList_take_last_mul_last (descPrimeList_pairwise_gt d) hlen2
    have htake_ne : L.take (L.length - 1) ≠ [] := List.ne_nil_of_length_pos (by
      rw [List.length_take]; omega)
    have hL_ne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlast_eq : (L.take (L.length - 1)).getLastD 1 =
        (L.take (L.length - 1)).getLast htake_ne := getLastD_eq_getLast' htake_ne 1
    have hp_last_ge1 : (1 : ℝ) ≤ (L.getLast hL_ne : ℝ) := by
      exact_mod_cast hL_pos _ (List.getLast_mem hL_ne)
    have hp_last_lt : (L.getLast hL_ne : ℝ) < ((L.take (L.length - 1)).getLast htake_ne : ℝ) := by
      exact_mod_cast hstep.2
    have hp_pow_lt : (L.getLast hL_ne : ℝ) <
        ((L.take (L.length - 1)).getLast htake_ne : ℝ) ^ β :=
      lt_of_lt_of_le hp_last_lt (Real.self_le_rpow_of_one_le (le_trans hp_last_ge1 hp_last_lt.le) hβ)
    have hd_lt : (d : ℝ) < rosserTruncationFactor β (L.take (L.length - 1)) := by
      rw [← hL_prod, ← hstep.1, Nat.cast_mul, rosserTruncationFactor, hlast_eq]
      have hprod_pos : (0 : ℝ) < ((L.take (L.length - 1)).prod : ℝ) := by
        exact_mod_cast List.prod_pos fun p hp =>
          hL_pos p ((List.take_subset (L.length - 1) L) hp)
      exact mul_lt_mul_of_pos_left hp_pow_lt hprod_pos
    linarith
  · have htrunc := hL_pref L.length hodd le_rfl
    rw [List.take_length] at htrunc
    have hL_ne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlast_eq : L.getLastD 1 = L.getLast hL_ne := getLastD_eq_getLast' hL_ne 1
    have hp_ge1 : (1 : ℝ) ≤ (L.getLast hL_ne : ℝ) := by
      exact_mod_cast hL_pos _ (List.getLast_mem hL_ne)
    have hpow_ge1 : 1 ≤ (L.getLast hL_ne : ℝ) ^ β := Real.one_le_rpow hp_ge1 (by linarith)
    have hd_le : (d : ℝ) ≤ rosserTruncationFactor β L := by
      rw [← hL_prod, rosserTruncationFactor, hlast_eq]
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) hpow_ge1
    linarith

/-- Support bound for `betaSieveLower`: for `1 ≤ β`, `1 < y`, and any `d` whose prime factors
are all `< y`, `betaSieveLower β y d = 0` whenever `y ≤ (d : ℝ)`. -/
theorem betaSieveLower_eq_zero_of_le {β y : ℝ} (hβ : 1 ≤ β) (hy : 1 < y) {d : ℕ}
    (hd_primes : ∀ p ∈ d.primeFactors, (p : ℝ) < y) (hd : y ≤ (d : ℝ)) :
    betaSieveLower β y d = 0 := by
  by_contra hne
  have hcond : Squarefree d ∧ d ≠ 0 ∧
      rosserCondMinus (fun L => rosserTruncationFactor β L < y) (descPrimeList d) := by
    unfold betaSieveLower rosserWeightsMinus at hne
    split_ifs at hne with h
    · exact h
    · exact absurd rfl hne
  let L := descPrimeList d
  have hL_prod : L.prod = d := prod_descPrimeList_of_squarefree hcond.1
  have hL_primes : ∀ p ∈ L, p.Prime := fun p hp => prime_of_mem_descPrimeList hp
  have hL_pos : ∀ p ∈ L, 1 ≤ p := fun p hp => (hL_primes p hp).one_le
  have hL_pref : ∀ j : ℕ, Even j → 2 ≤ j → j ≤ L.length →
      rosserTruncationFactor β (L.take j) < y :=
    (rosserCond_iff_prefixes L _).2.mp hcond.2.2
  by_cases hlen0 : L.length = 0
  · have hnil : L = [] := List.length_eq_zero_iff.mp hlen0
    have hd1 : d = 1 := by rw [← hL_prod, hnil, List.prod_nil]
    rw [hd1, Nat.cast_one] at hd
    linarith
  by_cases hlen1 : L.length = 1
  · obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlen1
    have hdp : d = p := by rw [← hL_prod, hp, List.prod_singleton]
    have hp_mem : p ∈ d.primeFactors := mem_descPrimeList_iff.mp (by rw [show descPrimeList d = L from rfl, hp]; simp)
    have hpy := hd_primes p hp_mem
    rw [hdp] at hd
    linarith
  rcases Nat.even_or_odd L.length with heven | hodd
  · have hlen2 : 2 ≤ L.length := by omega
    have htrunc := hL_pref L.length heven hlen2 le_rfl
    rw [List.take_length] at htrunc
    have hL_ne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlast_eq : L.getLastD 1 = L.getLast hL_ne := getLastD_eq_getLast' hL_ne 1
    have hp_ge1 : (1 : ℝ) ≤ (L.getLast hL_ne : ℝ) := by
      exact_mod_cast hL_pos _ (List.getLast_mem hL_ne)
    have hpow_ge1 : 1 ≤ (L.getLast hL_ne : ℝ) ^ β := Real.one_le_rpow hp_ge1 (by linarith)
    have hd_le : (d : ℝ) ≤ rosserTruncationFactor β L := by
      rw [← hL_prod, rosserTruncationFactor, hlast_eq]
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) hpow_ge1
    linarith
  · have hlen3 : 3 ≤ L.length := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hlen2 : 2 ≤ L.length := by omega
    have hev1 : Even (L.length - 1) := by
      rw [Nat.even_iff]
      rw [Nat.odd_iff] at hodd
      omega
    have htrunc := hL_pref (L.length - 1) hev1 (by omega) (Nat.sub_le _ _)
    have hstep := descPrimeList_take_last_mul_last (descPrimeList_pairwise_gt d) hlen2
    have htake_ne : L.take (L.length - 1) ≠ [] := List.ne_nil_of_length_pos (by
      rw [List.length_take]; omega)
    have hL_ne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlast_eq : (L.take (L.length - 1)).getLastD 1 =
        (L.take (L.length - 1)).getLast htake_ne := getLastD_eq_getLast' htake_ne 1
    have hp_last_ge1 : (1 : ℝ) ≤ (L.getLast hL_ne : ℝ) := by
      exact_mod_cast hL_pos _ (List.getLast_mem hL_ne)
    have hp_last_lt : (L.getLast hL_ne : ℝ) < ((L.take (L.length - 1)).getLast htake_ne : ℝ) := by
      exact_mod_cast hstep.2
    have hp_pow_lt : (L.getLast hL_ne : ℝ) <
        ((L.take (L.length - 1)).getLast htake_ne : ℝ) ^ β :=
      lt_of_lt_of_le hp_last_lt (Real.self_le_rpow_of_one_le (le_trans hp_last_ge1 hp_last_lt.le) hβ)
    have hd_lt : (d : ℝ) < rosserTruncationFactor β (L.take (L.length - 1)) := by
      rw [← hL_prod, ← hstep.1, Nat.cast_mul, rosserTruncationFactor, hlast_eq]
      have hprod_pos : (0 : ℝ) < ((L.take (L.length - 1)).prod : ℝ) := by
        exact_mod_cast List.prod_pos fun p hp =>
          hL_pos p ((List.take_subset (L.length - 1) L) hp)
      exact mul_lt_mul_of_pos_left hp_pow_lt hprod_pos
    linarith

/-- **Rosser–Iwaniec alternating upper sieve bound**: for `1 ≤ β`, `1 < y`,
`S(A, P, z) ≤ X * V⁺(z, y) + ∑_{d ∣ P(z), d < y} |r_d|`. -/
theorem betaSieve_upper_bound (s : SieveData) (z : ℝ) {β y : ℝ} (hβ : 1 ≤ β) (hy : 1 < y) :
    (siftedCount s.A s.prodPrimes z : ℝ) ≤
      s.X * (∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y),
          betaSieveUpper β y d * s.density d) +
        ∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y), |s.rem d| := by
  have hup := siftedCount_le_sieve_upper s z ((betaSieveUpper_isUpperSieveWeights β y).on _)
  have hmain_eq :
      ∑ d ∈ (s.prodPrimes z).divisors, betaSieveUpper β y d * s.density d =
        ∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y),
          betaSieveUpper β y d * s.density d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hdy : (d : ℝ) < y
    · simp only [hdy, ↓reduceIte]
    · simp only [hdy, ↓reduceIte]
      rw [betaSieveUpper_eq_zero_of_le hβ hy (not_lt.mp hdy), zero_mul]
  have hrem_le :
      ∑ d ∈ (s.prodPrimes z).divisors, |betaSieveUpper β y d| * |s.rem d| ≤
        ∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y), |s.rem d| := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases hdy : (d : ℝ) < y
    · simp only [hdy, ↓reduceIte]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_rosserWeightsPlus_le_one _ d)
    · simp only [hdy, ↓reduceIte]
      rw [betaSieveUpper_eq_zero_of_le hβ hy (not_lt.mp hdy), abs_zero, zero_mul]
  rw [hmain_eq] at hup
  linarith

/-- **Rosser–Iwaniec alternating lower sieve bound**: for `1 ≤ β`, `1 < y`, and `P(z)` whose
prime factors are all `< y`,
`X * V⁻(z, y) - ∑_{d ∣ P(z), d < y} |r_d| ≤ S(A, P, z)`. -/
theorem betaSieve_lower_bound (s : SieveData) (z : ℝ) {β y : ℝ} (hβ : 1 ≤ β) (hy : 1 < y)
    (hPz : ∀ p ∈ (s.prodPrimes z).primeFactors, (p : ℝ) < y) :
    s.X * (∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y),
          betaSieveLower β y d * s.density d) -
        ∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y), |s.rem d| ≤
      (siftedCount s.A s.prodPrimes z : ℝ) := by
  have hlo := sieve_lower_le_siftedCount s z ((betaSieveLower_isLowerSieveWeights β y).on _)
  have hPz_d : ∀ d ∈ (s.prodPrimes z).divisors, ∀ p ∈ d.primeFactors, (p : ℝ) < y := by
    intro d hd p hp
    exact hPz p (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (s.prodPrimes_ne_zero z) hp)
  have hmain_eq :
      ∑ d ∈ (s.prodPrimes z).divisors, betaSieveLower β y d * s.density d =
        ∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y),
          betaSieveLower β y d * s.density d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hdy : (d : ℝ) < y
    · simp only [hdy, ↓reduceIte]
    · simp only [hdy, ↓reduceIte]
      rw [betaSieveLower_eq_zero_of_le hβ hy (hPz_d d hd) (not_lt.mp hdy), zero_mul]
  have hrem_le :
      ∑ d ∈ (s.prodPrimes z).divisors, |betaSieveLower β y d| * |s.rem d| ≤
        ∑ d ∈ (s.prodPrimes z).divisors.filter (fun d : ℕ => (d : ℝ) < y), |s.rem d| := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun d hd => ?_
    by_cases hdy : (d : ℝ) < y
    · simp only [hdy, ↓reduceIte]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_rosserWeightsMinus_le_one _ d)
    · simp only [hdy, ↓reduceIte]
      rw [betaSieveLower_eq_zero_of_le hβ hy (hPz_d d hd) (not_lt.mp hdy), abs_zero, zero_mul]
  rw [hmain_eq] at hlo
  linarith

end RosserIwaniecSieve

/-! ### Brun's Theorem on Twin Primes -/

section BrunsTwinPrimes

/-- Counting function `π₂(x)` for twin primes `p ≤ x` (primes `p` such that `p + 2` is also prime). -/
def twinPrimeCount (x : ℝ) : ℝ :=
  (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)).card : ℝ)

/-- `twinPrimeCount x` is nonnegative. -/
theorem twinPrimeCount_nonneg (x : ℝ) : 0 ≤ twinPrimeCount x :=
  Nat.cast_nonneg _

/-- `twinPrimeCount x ≤ x` for `x ≥ 0`. -/
theorem twinPrimeCount_le_self {x : ℝ} (hx : 0 ≤ x) : twinPrimeCount x ≤ x := by
  unfold twinPrimeCount
  have hle : ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)).card ≤ ⌊x⌋₊ := by
    calc
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)).card
          ≤ (Finset.Icc 1 ⌊x⌋₊).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = ⌊x⌋₊ := by simp
  exact (by exact_mod_cast hle : _ ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx)

/-- Sieve density arithmetic function `ω_twin` for `n(n + 2)`:
`ω_twin(p) = 1` for `p = 2`, `ω_twin(p) = 2` for odd primes `p`, extended multiplicatively
(with `ω_twin(0) = 0`). -/
def twinOmega : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else ∏ p ∈ n.primeFactors, (if p = 2 then (1 : ℝ) else 2)
  map_zero' := by simp

/-- Evaluation of `twinOmega` at `n ≠ 0`. -/
theorem twinOmega_apply_ne_zero {n : ℕ} (hn : n ≠ 0) :
    twinOmega n = ∏ p ∈ n.primeFactors, (if p = 2 then (1 : ℝ) else 2) := by
  simp [twinOmega, hn]

/-- `twinOmega 1 = 1`. -/
@[simp]
theorem twinOmega_one : twinOmega 1 = 1 := by
  simp [twinOmega]

/-- `twinOmega` at a prime `p` equals `1` if `p = 2` and `2` if `p ≠ 2`. -/
theorem twinOmega_prime {p : ℕ} (hp : p.Prime) :
    twinOmega p = if p = 2 then 1 else 2 := by
  rw [twinOmega_apply_ne_zero hp.ne_zero, Nat.Prime.primeFactors hp, Finset.prod_singleton]

/-- `twinOmega` is multiplicative. -/
theorem twinOmega_isMultiplicative : twinOmega.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨twinOmega_one, fun {m n} hm hn hmn => ?_⟩
  rw [twinOmega_apply_ne_zero (mul_ne_zero hm hn), twinOmega_apply_ne_zero hm,
    twinOmega_apply_ne_zero hn, Nat.Coprime.primeFactors_mul hmn,
    Finset.prod_union hmn.disjoint_primeFactors]

/-- `0 ≤ twinOmega p` for all primes `p`. -/
theorem twinOmega_nonneg_of_prime (p : ℕ) (_hp : p.Prime) : 0 ≤ twinOmega p := by
  rw [twinOmega_prime _hp]
  split_ifs <;> norm_num

/-- `twinOmega p < p` for all primes `p`. -/
theorem twinOmega_lt_of_prime (p : ℕ) (hp : p.Prime) : twinOmega p < (p : ℝ) := by
  rw [twinOmega_prime hp]
  by_cases hp2 : p = 2
  · subst hp2; norm_num
  · simp only [hp2, ↓reduceIte]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    exact_mod_cast (by omega : 2 < p)

/-- `twinOmega n ≤ 2 ^ n.primeFactors.card` for all `n : ℕ`. -/
theorem twinOmega_le_two_pow (n : ℕ) : twinOmega n ≤ (2 : ℝ) ^ n.primeFactors.card := by
  by_cases hn0 : n = 0
  · subst hn0; simp [twinOmega]
  rw [twinOmega_apply_ne_zero hn0]
  calc
    ∏ p ∈ n.primeFactors, (if p = 2 then (1 : ℝ) else 2)
        ≤ ∏ _p ∈ n.primeFactors, (2 : ℝ) := by
          refine Finset.prod_le_prod₀ (fun _ _ => by split_ifs <;> norm_num)
            (fun _ _ => by split_ifs <;> norm_num)
    _ = (2 : ℝ) ^ n.primeFactors.card := by simp

private def twinRoots (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun r => d ∣ r * (r + 2))

private lemma dvd_mul_add_two_iff_mem_twinRoots {d : ℕ} (hd : 0 < d) (n : ℕ) :
    d ∣ n * (n + 2) ↔ n % d ∈ twinRoots d := by
  simp only [twinRoots, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => ⟨Nat.mod_lt n hd, ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mod_mod, Nat.add_mod, Nat.mod_mod,
      ← Nat.add_mod, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
    exact h
  · rw [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mod_mod, Nat.add_mod, Nat.mod_mod,
      ← Nat.add_mod, ← Nat.mul_mod] at h
    exact h

private lemma card_twinRoots_prime {p : ℕ} (hp : p.Prime) :
    (twinRoots p).card = if p = 2 then 1 else 2 := by
  by_cases hp2 : p = 2
  · subst hp2
    have htr : twinRoots 2 = {0} := by
      ext r
      simp only [twinRoots, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hdvd⟩
        interval_cases r <;> simp_all
      · rintro rfl
        decide
    simp [htr]
  · simp only [hp2, ↓reduceIte]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have htr : twinRoots p = {0, p - 2} := by
      ext r
      simp only [twinRoots, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hdvd⟩
        rcases hp.dvd_mul.mp hdvd with h1 | h2
        · left; exact Nat.eq_zero_of_dvd_of_lt h1 hr
        · right
          rcases h2 with ⟨k, hk⟩
          have hk0 : k ≠ 0 := by
            intro hk0; subst hk0; omega
          have hk2 : k < 2 := by
            by_contra hge
            have hge2 : 2 ≤ k := not_lt.mp hge
            have h1 : p * 2 ≤ p * k := Nat.mul_le_mul_left p hge2
            omega
          have hk1 : k = 1 := by omega
          subst hk1
          omega
      · rintro (rfl | rfl)
        · exact ⟨hp.pos, by simp⟩
        · refine ⟨by omega, ?_⟩
          rw [show p - 2 + 2 = p by omega]
          exact dvd_mul_left p _
    rw [htr, Finset.card_pair (by omega)]

private lemma card_twinRoots_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    (twinRoots (m * n)).card = (twinRoots m).card * (twinRoots n).card := by
  have hbij : (twinRoots (m * n)).card = ((twinRoots m) ×ˢ (twinRoots n)).card := by
    refine Finset.card_bij (fun r _ => (r % m, r % n)) ?_ ?_ ?_
    · intro r hr
      simp only [twinRoots, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hr ⊢
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
      simp only [Finset.mem_product, twinRoots, Finset.mem_filter, Finset.mem_range] at hab
      have : NeZero m := ⟨hm.ne'⟩
      have : NeZero n := ⟨hn.ne'⟩
      have : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
      let e := ZMod.chineseRemainder hmn
      let r : ℕ := (e.symm ((a : ZMod m), (b : ZMod n))).val
      have hr_lt : r < m * n := ZMod.val_lt _
      have hre : e (r : ZMod (m * n)) = ((a : ZMod m), (b : ZMod n)) := by
        dsimp [r]
        rw [ZMod.natCast_zmod_val, e.apply_symm_apply]
      have he_nat : e (r : ZMod (m * n)) = ((r : ZMod m), (r : ZMod n)) := by
        rw [map_natCast]
        rfl
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

private lemma card_twinRoots_eq_twinOmega {d : ℕ} (hd : Squarefree d) :
    ((twinRoots d).card : ℝ) = twinOmega d := by
  have hd_nat : ∀ k : ℕ, Squarefree k →
      (twinRoots k).card = ∏ p ∈ k.primeFactors, (if p = 2 then 1 else 2) := by
    intro k
    induction k using Nat.strong_induction_on with | ind k ih =>
    intro hk
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk.ne_zero
    by_cases hk1 : k = 1
    · subst hk1
      have htr : twinRoots 1 = {0} := by
        ext r
        simp [twinRoots]
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
        ext q
        simp [Finset.mem_insert]
      have hp_not : p ∉ m.primeFactors := by
        intro hmem
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hmem
        exact hp.ne_one (Nat.dvd_one.mp (hcop.symm ▸ Nat.dvd_gcd hpm dvd_rfl))
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sq.ne_zero
      rw [← hkm, card_twinRoots_mul hp.pos hm_pos hcop, card_twinRoots_prime hp,
        ih m hm_lt hm_sq, hkm, hpf, Finset.prod_insert hp_not]
  rw [hd_nat d hd, twinOmega_apply_ne_zero hd.ne_zero]
  push_cast
  rfl

private lemma card_Icc_filter_mod_eq_bounds {d : ℕ} (hd : 1 ≤ d) (N r₀ : ℕ) (hr₀ : r₀ < d) :
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
      have hinj : Set.InjOn g (Finset.Icc 1 (N / d) : Set ℕ) := by
        intro q₁ _ q₂ _ heq
        exact Nat.eq_of_mul_eq_mul_right hd heq
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
        have h1 : q₁ * d = q₂ * d := Nat.add_right_cancel heq
        exact Nat.eq_of_mul_eq_mul_right hd h1
      have himg : (Finset.range (N / d)).image g ⊆ F := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
        have hq_lt : q < N / d := Finset.mem_range.mp hq
        have hq1 : q + 1 ≤ N / d := hq_lt
        have hleN : q * d + r₀ ≤ N := by
          have h1 : q * d + r₀ < (q + 1) * d := by
            rw [Nat.add_mul, one_mul]
            exact Nat.add_lt_add_left hr₀ (q * d)
          have h2 : (q + 1) * d ≤ (N / d) * d := Nat.mul_le_mul_right d hq1
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

private lemma abs_card_twinMultiple_sub_le {N d : ℕ} (hd : Squarefree d) :
    |(((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card : ℝ) -
        (twinOmega d / (d : ℝ)) * (N : ℝ)| ≤ twinOmega d := by
  have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero hd.ne_zero
  have hdR_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hpart :
      ((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card =
        ∑ r ∈ twinRoots d, ((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card := by
    have hmaps : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
        n % d ∈ twinRoots d := by
      intro n hn
      exact (dvd_mul_add_two_iff_mem_twinRoots hd_pos n).mp (Finset.mem_filter.mp hn).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun r hr => ?_
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hn1, hnN⟩, _⟩, hnr⟩
      exact ⟨⟨hn1, hnN⟩, hnr⟩
    · rintro ⟨⟨hn1, hnN⟩, hnr⟩
      exact ⟨⟨⟨hn1, hnN⟩, (dvd_mul_add_two_iff_mem_twinRoots hd_pos n).mpr (hnr ▸ hr)⟩, hnr⟩
  have hfiber_bd : ∀ r ∈ twinRoots d,
      |(((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
    intro r hr
    have hr_lt : r < d := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hbd := card_Icc_filter_mod_eq_bounds hd_pos N r hr_lt
    have hdiv_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdR_pos]
      exact_mod_cast Nat.div_mul_le_self N d
    have hlt_div : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdR_pos]
      have hdm := Nat.div_add_mod N d
      have hmod := Nat.mod_lt N (Nat.pos_of_ne_zero hd.ne_zero)
      have hnat : N < (N / d + 1) * d := by nlinarith
      exact_mod_cast hnat
    rw [abs_le]
    constructor <;> linarith
  have hsum_eq :
      (twinOmega d / (d : ℝ)) * (N : ℝ) = ∑ _r ∈ twinRoots d, (N : ℝ) / (d : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, card_twinRoots_eq_twinOmega hd]
    ring
  rw [hpart, Nat.cast_sum, hsum_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ twinRoots d, ((((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) -
        (N : ℝ) / (d : ℝ))|
        ≤ ∑ r ∈ twinRoots d, |(((Finset.Icc 1 N).filter (fun n : ℕ => n % d = r)).card : ℝ) -
            (N : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ twinRoots d, (1 : ℝ) := Finset.sum_le_sum fun r hr => hfiber_bd r hr
    _ = twinOmega d := by simp [card_twinRoots_eq_twinOmega hd]

/-- Sieve model for twin primes: `A = {n(n + 2) : 1 ≤ n ≤ ⌊x⌋₊}`, modulus `primeProd z`,
main mass `⌊x⌋₊`, and density `twinOmega`. -/
def twinSieveData (x : ℝ) : SieveData where
  A := (Finset.Icc 1 ⌊x⌋₊).image (fun n => n * (n + 2))
  prodPrimes := primeProd
  prodPrimes_squarefree := primeProd_squarefree
  X := (⌊x⌋₊ : ℝ)
  omega := twinOmega
  omega_mult := twinOmega_isMultiplicative
  omega_nonneg_of_prime := twinOmega_nonneg_of_prime
  omega_lt_of_prime := twinOmega_lt_of_prime

private lemma strictMono_mul_add_two : StrictMono (fun n : ℕ => n * (n + 2)) := by
  intro a b hab
  nlinarith

/-- Remainder bound for `twinSieveData`: for any squarefree `d`,
`|(twinSieveData x).rem d| ≤ (2 : ℝ) ^ d.primeFactors.card`. -/
theorem abs_twinSieveData_rem_le (x : ℝ) {d : ℕ} (hd : Squarefree d) :
    |(twinSieveData x).rem d| ≤ (2 : ℝ) ^ d.primeFactors.card := by
  unfold SieveData.rem SieveData.density twinSieveData
  dsimp only
  have himg : sieveMultiple ((Finset.Icc 1 ⌊x⌋₊).image (fun n => n * (n + 2))) d =
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => d ∣ n * (n + 2))).image (fun n => n * (n + 2)) := by
    ext m
    simp only [sieveMultiple, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hdvd⟩
      exact ⟨n, ⟨hn, hdvd⟩, rfl⟩
    · rintro ⟨n, ⟨hn, hdvd⟩, rfl⟩
      exact ⟨⟨n, hn, rfl⟩, hdvd⟩
  rw [himg, Finset.card_image_of_injective _ strictMono_mul_add_two.injective]
  exact (abs_card_twinMultiple_sub_le hd).trans (twinOmega_le_two_pow d)

/-- Relating `twinPrimeCount x` to `(twinSieveData x)`'s sifted count: for `0 ≤ z`,
`twinPrimeCount x ≤ z + siftedCount (twinSieveData x).A primeProd z`. -/
theorem twinPrimeCount_le_add_siftedCount {x z : ℝ} (hz : 0 ≤ z) :
    twinPrimeCount x ≤ z + (siftedCount (twinSieveData x).A primeProd z : ℝ) := by
  unfold twinPrimeCount
  let P_all := (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime)
  let P_sm := P_all.filter (fun p : ℕ => (p : ℝ) ≤ z)
  let P_lg := P_all.filter (fun p : ℕ => z < (p : ℝ))
  have hpart : P_all.card = P_sm.card + P_lg.card := by
    have h := P_all.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ z)
    have hnot : P_all.filter (fun p : ℕ => ¬ (p : ℝ) ≤ z) = P_lg := by
      ext p; simp [P_lg]
    rw [hnot] at h
    exact h.symm
  have hsm_le : (P_sm.card : ℝ) ≤ z := by
    have hsub : P_sm ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp'' := Finset.mem_filter.mp hp'.1
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp''.1).1, Nat.le_floor hp'.2⟩
    have hle : P_sm.card ≤ ⌊z⌋₊ := by
      calc
        P_sm.card ≤ (Finset.Icc 1 ⌊z⌋₊).card := Finset.card_le_card hsub
        _ = ⌊z⌋₊ := by simp
    exact (by exact_mod_cast hle : (P_sm.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz)
  have hlg_le : P_lg.card ≤ siftedCount (twinSieveData x).A primeProd z := by
    unfold siftedCount siftedCountOf twinSieveData
    dsimp only
    have hinj : Set.InjOn (fun p : ℕ => p * (p + 2)) (P_lg : Set ℕ) :=
      fun _ _ _ _ h => strictMono_mul_add_two.injective h
    have himg : P_lg.image (fun p => p * (p + 2)) ⊆
        ((Finset.Icc 1 ⌊x⌋₊).image (fun n => n * (n + 2))).filter
          (fun m => Nat.Coprime m (primeProd z)) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
      have hp' := Finset.mem_filter.mp hp
      have hp'' := Finset.mem_filter.mp hp'.1
      have hp_prime : p.Prime := hp''.2.1
      have hp2_prime : (p + 2).Prime := hp''.2.2
      have hp_gt_z : z < (p : ℝ) := hp'.2
      have hcop : Nat.Coprime (p * (p + 2)) (primeProd z) := by
        rw [Nat.coprime_comm]
        refine Nat.Coprime.prod_left fun q hq => ?_
        have hq_prime := prime_of_mem_primeFinset hq
        have hqz : (q : ℝ) ≤ z := (mem_primeFinset_iff.mp hq).2
        have hqp : q < p := by exact_mod_cast hqz.trans_lt hp_gt_z
        have hqp2 : q < p + 2 := by omega
        refine Nat.Coprime.mul_right ?_ ?_
        · rw [hq_prime.coprime_iff_not_dvd]
          intro hdiv
          rcases (Nat.dvd_prime hp_prime).mp hdiv with h1 | rfl
          · exact hq_prime.ne_one h1
          · omega
        · rw [hq_prime.coprime_iff_not_dvd]
          intro hdiv
          rcases (Nat.dvd_prime hp2_prime).mp hdiv with h1 | hqeq
          · exact hq_prime.ne_one h1
          · omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hp''.1, rfl⟩, hcop⟩
    calc
      P_lg.card = (P_lg.image (fun p => p * (p + 2))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (((Finset.Icc 1 ⌊x⌋₊).image (fun n => n * (n + 2))).filter
            (fun m => Nat.Coprime m (primeProd z))).card := Finset.card_le_card himg
  rw [hpart, Nat.cast_add]
  have hlgR : (P_lg.card : ℝ) ≤ (siftedCount (twinSieveData x).A primeProd z : ℝ) := by
    exact_mod_cast hlg_le
  linarith

private lemma neg_log_one_sub_le_three_mul {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 / 3) :
    -Real.log (1 - u) ≤ 3 * u := by
  have hpos : 0 < 1 - u := by linarith
  have hmul : 1 ≤ (1 - u) * (1 + 3 * u) := by
    have hdiff : (1 - u) * (1 + 3 * u) - 1 = u * (2 - 3 * u) := by ring
    have hnn : 0 ≤ u * (2 - 3 * u) := mul_nonneg hu0 (by linarith)
    linarith
  have hinv_le : (1 - u)⁻¹ ≤ 1 + 3 * u := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  have hexp_le : (1 - u)⁻¹ ≤ Real.exp (3 * u) :=
    hinv_le.trans (by linarith [Real.add_one_le_exp (3 * u)])
  rw [← Real.log_inv]
  exact (Real.log_le_log (inv_pos.mpr hpos) hexp_le).trans_eq (Real.log_exp _)

private lemma twinSieveData_eulerProd_le (x z : ℝ) :
    (twinSieveData x).eulerProd z ≤
      2 * (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)) ^ 2 := by
  have hprod : (twinSieveData x).eulerProd z =
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (twinSieveData x).density p) := by
    unfold SieveData.eulerProd
    have hp : (twinSieveData x).prodPrimes z = primeProd z := rfl
    rw [hp, primeFactors_primeProd, primeFinset]
  rw [hprod]
  have hsq : (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)) ^ 2 =
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) ^ 2 := by
    rw [Finset.prod_pow]
  rw [hsq]
  by_cases h2 : 2 ∈ Nat.primesLE ⌊z⌋₊
  · rw [← Finset.mul_prod_erase (Nat.primesLE ⌊z⌋₊) (fun p => 1 - (twinSieveData x).density p) h2,
      ← Finset.mul_prod_erase (Nat.primesLE ⌊z⌋₊) (fun p => (1 - (p : ℝ)⁻¹) ^ 2) h2]
    have htwo : 1 - (twinSieveData x).density 2 =
        2 * (1 - ((2 : ℕ) : ℝ)⁻¹) ^ 2 := by
      unfold SieveData.density twinSieveData
      dsimp only
      rw [twinOmega_prime Nat.prime_two]
      norm_num
    rw [htwo, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (by norm_num)
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have hp_prime := Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)
      exact sub_nonneg.mpr ((twinSieveData x).density_lt_one_of_prime hp_prime).le
    · have hp_ne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
      have hp_prime := Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)
      unfold SieveData.density twinSieveData
      dsimp only
      rw [twinOmega_prime hp_prime]
      simp only [hp_ne2, ↓reduceIte]
      have hsq_ge : 1 - 2 / (p : ℝ) ≤ (1 - (p : ℝ)⁻¹) ^ 2 := by
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
        have hdiff : (1 - (p : ℝ)⁻¹) ^ 2 - (1 - 2 / (p : ℝ)) = (p : ℝ)⁻¹ ^ 2 := by
          field_simp [hp_pos.ne']
          ring
        linarith [sq_nonneg (p : ℝ)⁻¹]
      exact hsq_ge
  · have hprod_le :
        ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (twinSieveData x).density p) ≤
          ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) ^ 2 := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · exact sub_nonneg.mpr
          ((twinSieveData x).density_lt_one_of_prime (Nat.prime_of_mem_primesLE hp)).le
      · have hp_ne2 : p ≠ 2 := fun h => h2 (h ▸ hp)
        have hp_prime := Nat.prime_of_mem_primesLE hp
        unfold SieveData.density twinSieveData
        dsimp only
        rw [twinOmega_prime hp_prime]
        simp only [hp_ne2, ↓reduceIte]
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
        have hdiff : (1 - (p : ℝ)⁻¹) ^ 2 - (1 - 2 / (p : ℝ)) = (p : ℝ)⁻¹ ^ 2 := by
          field_simp [hp_pos.ne']
          ring
        linarith [sq_nonneg (p : ℝ)⁻¹]
    have hnn : 0 ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) ^ 2 :=
      Finset.prod_nonneg fun _ _ => sq_nonneg _
    exact hprod_le.trans (le_mul_of_one_le_left hnn (by norm_num))

private lemma log_inv_twinSieveData_eulerProd_le {x z : ℝ} (hz : 2 ≤ z) :
    Real.log (((twinSieveData x).eulerProd z)⁻¹) ≤
      Real.log 2 + 6 * (Real.log (Real.log z) + |meisselMertensConstant| +
        (2 * mertensOneBound) / Real.log 2) := by
  have hlog_eq : Real.log (((twinSieveData x).eulerProd z)⁻¹) =
      ∑ p ∈ Nat.primesLE ⌊z⌋₊, -Real.log (1 - (twinSieveData x).density p) := by
    rw [Real.log_inv, SieveData.eulerProd, twinSieveData]
    dsimp only
    rw [primeFactors_primeProd, primeFinset, Real.log_prod, Finset.sum_neg_distrib]
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    exact (sub_pos.mpr ((twinSieveData x).density_lt_one_of_prime hp_prime)).ne'
  have h2_mem : 2 ∈ Nat.primesLE ⌊z⌋₊ :=
    Nat.mem_primesLE.mpr ⟨Nat.le_floor hz, Nat.prime_two⟩
  rw [hlog_eq, ← Finset.add_sum_erase _ _ h2_mem]
  have h2_term : -Real.log (1 - (twinSieveData x).density 2) = Real.log 2 := by
    unfold SieveData.density twinSieveData
    dsimp only
    rw [twinOmega_prime Nat.prime_two]
    norm_num
    rw [one_div, Real.log_inv, neg_neg]
  have hrest_le :
      ∑ p ∈ (Nat.primesLE ⌊z⌋₊).erase 2, -Real.log (1 - (twinSieveData x).density p) ≤
        6 * ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ := by
    calc
      ∑ p ∈ (Nat.primesLE ⌊z⌋₊).erase 2, -Real.log (1 - (twinSieveData x).density p)
          ≤ ∑ p ∈ (Nat.primesLE ⌊z⌋₊).erase 2, 6 * (p : ℝ)⁻¹ := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_ne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
            have hp_prime := Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)
            have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
            have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
            unfold SieveData.density twinSieveData
            dsimp only
            rw [twinOmega_prime hp_prime]
            simp only [hp_ne2, ↓reduceIte]
            have hu0 : (0 : ℝ) ≤ 2 / (p : ℝ) := by positivity
            have hu : 2 / (p : ℝ) ≤ 2 / 3 := by
              exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3R
            have hle := neg_log_one_sub_le_three_mul hu0 hu
            linarith [show 3 * (2 / (p : ℝ)) = 6 * (p : ℝ)⁻¹ by ring]
      _ ≤ ∑ p ∈ Nat.primesLE ⌊z⌋₊, 6 * (p : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by positivity)
      _ = 6 * ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
  have hmert := abs_mertens_two_sub_le hz
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogz_ge : Real.log 2 ≤ Real.log z := Real.log_le_log zero_lt_two hz
  have hsum_inv_le : ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ ≤
      Real.log (Real.log z) + |meisselMertensConstant| + (2 * mertensOneBound) / Real.log 2 := by
    have h1 := (abs_le.mp hmert).2
    have h2 : (2 * mertensOneBound) / Real.log z ≤ (2 * mertensOneBound) / Real.log 2 := by
      have hm_nn : 0 ≤ 2 * mertensOneBound := by linarith [mertensOneBound_pos]
      gcongr
    have h3 : meisselMertensConstant ≤ |meisselMertensConstant| := le_abs_self _
    linarith
  linarith

private lemma pow_five_div_120_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 5 / 120 ≤ Real.exp u := by
  have h := Real.pow_div_factorial_le_exp u hu 5
  norm_num [Nat.factorial] at h
  exact h

private noncomputable def brunK0 : ℝ :=
  max 20 (Real.log 2 + 6 * (|meisselMertensConstant| + (2 * mertensOneBound) / Real.log 2) + 1)

private noncomputable def brunCmert : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) + mertensThreeBound

private lemma brunK0_ge20 : 20 ≤ brunK0 := le_max_left _ _

private lemma brunK0_ge_const :
    Real.log 2 + 6 * (|meisselMertensConstant| + (2 * mertensOneBound) / Real.log 2) ≤ brunK0 := by
  unfold brunK0
  linarith [le_max_right (20 : ℝ)
    (Real.log 2 + 6 * (|meisselMertensConstant| + (2 * mertensOneBound) / Real.log 2) + 1)]

private lemma brunCmert_pos : 0 < brunCmert := by
  unfold brunCmert mertensThreeBound
  have ha : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have hb : 0 < Real.exp ((2 * mertensOneBound + 1) / Real.log 2) := Real.exp_pos _
  have hc : 0 < 2 * mertensOneBound + 1 := by linarith [mertensOneBound_pos]
  positivity

private lemma brun_twin_primes_large (x : ℝ)
    (hbig : Real.exp (Real.exp brunK0) ≤ x) :
    twinPrimeCount x ≤
      (20000 * brunCmert ^ 2 + Real.exp 2 + 2) * x * (Real.log (Real.log x)) ^ 2 /
        (Real.log x) ^ 2 := by
  let K₀ := brunK0
  let x₀ := Real.exp (Real.exp K₀)
  let C_mert := brunCmert
  let C_lg : ℝ := 20000 * C_mert ^ 2 + Real.exp 2 + 2
  have hK₀_ge20 : 20 ≤ K₀ := brunK0_ge20
  have hK₀_ge_const :
      Real.log 2 + 6 * (|meisselMertensConstant| + (2 * mertensOneBound) / Real.log 2) ≤ K₀ :=
    brunK0_ge_const
  have hexp_1_lt3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hx₀_ge3 : 3 ≤ x₀ := by
    have h2_le_exp : (2 : ℝ) ≤ Real.exp K₀ := by
      have : (2 : ℝ) ≤ K₀ := by linarith
      exact this.trans (by linarith [Real.add_one_le_exp K₀])
    have hexp2 : Real.exp 2 ≤ x₀ := Real.exp_le_exp.mpr h2_le_exp
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hx : 3 ≤ x := hx₀_ge3.trans hbig
  have hCmert_pos : 0 < C_mert := brunCmert_pos
  let L : ℝ := Real.log x
  let LL : ℝ := Real.log L
  have h_goal : twinPrimeCount x ≤ C_lg * x * LL ^ 2 / L ^ 2 := by
    have hLL_ge : K₀ ≤ LL := by
      have hx_log : Real.exp K₀ ≤ L := by
        calc
          Real.exp K₀ = Real.log x₀ := (Real.log_exp _).symm
          _ ≤ Real.log x := Real.log_le_log (by linarith) hbig
      calc
        K₀ = Real.log (Real.exp K₀) := (Real.log_exp _).symm
        _ ≤ Real.log L := Real.log_le_log (Real.exp_pos _) hx_log
    have hLL_ge20 : 20 ≤ LL := hK₀_ge20.trans hLL_ge
    have hLL_pos : 0 < LL := by linarith
    have hL_pos : 0 < L := by
      have hx_log : Real.exp K₀ ≤ L := by
        calc Real.exp K₀ = Real.log x₀ := (Real.log_exp _).symm
          _ ≤ Real.log x := Real.log_le_log (by linarith) hbig
      exact lt_of_lt_of_le (Real.exp_pos _) hx_log
    have hL_eq : L = Real.exp LL := (Real.exp_log hL_pos).symm
    have hL_ge_poly : LL ^ 5 / 120 ≤ L := by
      have h := pow_five_div_120_le_exp hLL_pos.le
      rwa [← hL_eq] at h
    have hL_ge_200LL : 200 * LL ≤ L := by
      have h1 : 200 * LL ≤ LL ^ 5 / 120 := by
        have h4 : (24000 : ℝ) ≤ LL ^ 4 := by
          have : (20 : ℝ) ^ 4 ≤ LL ^ 4 := by gcongr
          linarith
        nlinarith
      exact h1.trans hL_ge_poly
    have hL_ge_44LL : 44 * LL + 2 ≤ L / 2 := by
      have h1 : 44 * LL + 2 ≤ 100 * LL := by linarith
      linarith
    have hL_pos : 0 < L := by linarith
    have hx_pos : 0 < x := by linarith
    let z : ℝ := Real.exp (L / (100 * LL))
    have hlogz : Real.log z = L / (100 * LL) := Real.log_exp _
    have hlogz_ge2 : 2 ≤ Real.log z := by
      rw [hlogz, le_div_iff₀ (by positivity)]
      linarith
    have hz_ge2 : 2 ≤ z := by
      calc
        (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
        _ ≤ z := Real.exp_le_exp.mpr (by rw [← hlogz]; exact hlogz_ge2)
    have hlogz_le_L : Real.log z ≤ L := by
      rw [hlogz]
      exact div_le_self hL_pos.le (by linarith)
    have hz_le_x : z ≤ x := by
      calc
        z = Real.exp (Real.log z) := (Real.exp_log (Real.exp_pos _)).symm
        _ ≤ Real.exp L := Real.exp_le_exp.mpr hlogz_le_L
        _ = x := Real.exp_log hx_pos
    let m : ℕ := ⌊21 * LL⌋₊ + 1
    have hm_ge1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
    have h2m_ge : 42 * LL ≤ (2 * m : ℝ) := by
      have hlt : 21 * LL < (⌊21 * LL⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (21 * LL)
      have hm_cast : (m : ℝ) = (⌊21 * LL⌋₊ : ℝ) + 1 := by simp [m]
      linarith
    have h2m_le : (2 * m : ℝ) ≤ 42 * LL + 2 := by
      have hle : (⌊21 * LL⌋₊ : ℝ) ≤ 21 * LL := Nat.floor_le (by positivity)
      push_cast [m]
      linarith
    let s := twinSieveData x
    have htwin_le := twinPrimeCount_le_add_siftedCount (x := x) (by linarith : 0 ≤ z)
    have hbrun := brun_pure_upper s z m
    have hV_le : s.eulerProd z ≤ 2 * C_mert ^ 2 / (Real.log z) ^ 2 := by
      have hv1 := twinSieveData_eulerProd_le x z
      have hmert3 := abs_mertens_three_sub_le hz_ge2
      have hprod_pos : 0 ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
        exact sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hp_gt1).le
      have hprod_le : ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) ≤ C_mert / Real.log z := by
        have h1 := (abs_le.mp hmert3).2
        have hm3_div : mertensThreeBound / (Real.log z) ^ 2 ≤ mertensThreeBound / Real.log z := by
          have hlogz_ge1 : 1 ≤ Real.log z := by linarith
          have hm3_nn : 0 ≤ mertensThreeBound := by
            unfold mertensThreeBound
            have := mertensOneBound_pos
            positivity
          gcongr
          exact le_self_pow₀ hlogz_ge1 (by norm_num)
        calc
          ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)
              ≤ Real.exp (-Real.eulerMascheroniConstant) / Real.log z +
                  mertensThreeBound / (Real.log z) ^ 2 := by linarith
          _ ≤ Real.exp (-Real.eulerMascheroniConstant) / Real.log z +
                mertensThreeBound / Real.log z := by linarith
          _ = C_mert / Real.log z := by dsimp [C_mert, brunCmert]; ring
      have hsq_le : (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)) ^ 2 ≤
          (C_mert / Real.log z) ^ 2 := by
        gcongr
      calc
        s.eulerProd z ≤ 2 * (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)) ^ 2 := hv1
        _ ≤ 2 * (C_mert / Real.log z) ^ 2 := by gcongr
        _ = 2 * C_mert ^ 2 / (Real.log z) ^ 2 := by ring
    have hmain_term :
        s.X * s.eulerProd z ≤ (20000 * C_mert ^ 2) * x * LL ^ 2 / L ^ 2 := by
      have hsX : s.X ≤ x := Nat.floor_le hx_pos.le
      have hsX_nn : 0 ≤ s.X := Nat.cast_nonneg _
      have hlogz_sq : (Real.log z) ^ 2 = L ^ 2 / (10000 * LL ^ 2) := by
        rw [hlogz]; ring
      have hv_rw : 2 * C_mert ^ 2 / (Real.log z) ^ 2 =
          (20000 * C_mert ^ 2) * LL ^ 2 / L ^ 2 := by
        rw [hlogz_sq]
        field_simp [hL_pos.ne', hLL_pos.ne']
        norm_num
      calc
        s.X * s.eulerProd z ≤ x * (2 * C_mert ^ 2 / (Real.log z) ^ 2) :=
            mul_le_mul hsX hV_le (s.eulerProd_pos z).le hx_pos.le
        _ = (20000 * C_mert ^ 2) * x * LL ^ 2 / L ^ 2 := by rw [hv_rw]; ring
    have hL_V_le : Real.log ((s.eulerProd z)⁻¹) ≤ 7 * LL := by
      have h1 := log_inv_twinSieveData_eulerProd_le (x := x) hz_ge2
      have hlogz_le_L' : Real.log (Real.log z) ≤ LL :=
        Real.log_le_log (by linarith) hlogz_le_L
      linarith
    have hexp_fac_err :
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤
          Real.exp 2 * x / L ^ 2 := by
      have hfac := (brun_pure_factorial_le_exp_bound s z (r := 2 * m + 1) (by omega)).1
      have hV_nn : 0 ≤ Real.log ((s.eulerProd z)⁻¹) := by
        rw [Real.log_inv]
        linarith [Real.log_nonpos (s.eulerProd_pos z).le (s.eulerProd_le_one z)]
      have hratio_le : Real.exp 1 * Real.log ((s.eulerProd z)⁻¹) / ((2 * m + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        have hexp1_lt3' : Real.exp 1 < 3 := hexp_1_lt3
        have hden_pos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
        have hden_ge : 42 * LL ≤ ((2 * m + 1 : ℕ) : ℝ) := by
          push_cast; linarith
        rw [div_le_iff₀ hden_pos]
        calc
          Real.exp 1 * Real.log ((s.eulerProd z)⁻¹)
              ≤ 3 * (7 * LL) := mul_le_mul hexp1_lt3'.le hL_V_le hV_nn (by norm_num)
          _ = (1 / 2) * (42 * LL) := by ring
          _ ≤ (1 / 2) * ((2 * m + 1 : ℕ) : ℝ) := by gcongr
      have hbase_nn : 0 ≤ Real.exp 1 * Real.log ((s.eulerProd z)⁻¹) / ((2 * m + 1 : ℕ) : ℝ) :=
        div_nonneg (mul_nonneg (Real.exp_pos 1).le hV_nn) (Nat.cast_nonneg _)
      have hhalf_pow :
          (Real.exp 1 * Real.log ((s.eulerProd z)⁻¹) / ((2 * m + 1 : ℕ) : ℝ)) ^ (2 * m + 1) ≤
            (1 / 2 : ℝ) ^ (2 * m + 1) := by
        gcongr
      have hpow_le_exp : (1 / 2 : ℝ) ^ (2 * m + 1) ≤ Real.exp 2 / L ^ 2 := by
        let k : ℕ := ⌊LL⌋₊
        have hk_ge : 4 * k ≤ 2 * m + 1 := by
          have hk_le : (k : ℝ) ≤ LL := Nat.floor_le hLL_pos.le
          have hreal : (4 * k : ℝ) ≤ (2 * m + 1 : ℕ) := by push_cast; linarith
          exact_mod_cast hreal
        have h1 : (1 / 2 : ℝ) ^ (2 * m + 1) ≤ (1 / 2 : ℝ) ^ (4 * k) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk_ge
        have h2 : (1 / 2 : ℝ) ^ (4 * k) = (1 / 4 : ℝ) ^ (2 * k) := by
          rw [show 4 * k = 2 * (2 * k) by ring, pow_mul]
          norm_num
        have hinv4 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
          have hexp1_lt4 : Real.exp 1 < 4 := lt_trans hexp_1_lt3 (by norm_num)
          rw [Real.exp_neg, inv_eq_one_div]
          exact div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos 1) hexp1_lt4.le
        have h3 : (1 / 4 : ℝ) ^ (2 * k) ≤ (Real.exp (-1)) ^ (2 * k) := by
          gcongr
        have h4 : (Real.exp (-1)) ^ (2 * k) = Real.exp (-(2 * (k : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1; push_cast; ring
        have h5 : -(2 * (k : ℝ)) ≤ 2 - 2 * LL := by
          have hk_gt : LL - 1 < (k : ℝ) := Nat.sub_one_lt_floor LL
          linarith
        have h6 : Real.exp (2 - 2 * LL) = Real.exp 2 / L ^ 2 := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
          have hexp_2LL : Real.exp (2 * LL) = L ^ 2 := by
            rw [show (2 : ℝ) * LL = (2 : ℕ) * LL by norm_num, Real.exp_nat_mul,
              Real.exp_log hL_pos]
          rw [hexp_2LL, div_eq_mul_inv]
        calc
          (1 / 2 : ℝ) ^ (2 * m + 1) ≤ (1 / 4 : ℝ) ^ (2 * k) := h1.trans_eq h2
          _ ≤ Real.exp (-(2 * (k : ℝ))) := h3.trans_eq h4
          _ ≤ Real.exp (2 - 2 * LL) := Real.exp_le_exp.mpr h5
          _ = Real.exp 2 / L ^ 2 := h6
      have hsX_abs : |s.X| ≤ x := by
        have hnn : 0 ≤ s.X := Nat.cast_nonneg _
        rw [abs_of_nonneg hnn]
        exact Nat.floor_le hx_pos.le
      calc
        |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)
            ≤ |s.X| * (Real.exp 1 * Real.log ((s.eulerProd z)⁻¹) / ((2 * m + 1 : ℕ) : ℝ)) ^ (2 * m + 1) :=
              hfac
        _ ≤ x * (1 / 2 : ℝ) ^ (2 * m + 1) :=
              mul_le_mul hsX_abs hhalf_pow (pow_nonneg hbase_nn _) hx_pos.le
        _ ≤ x * (Real.exp 2 / L ^ 2) := by gcongr
        _ = Real.exp 2 * x / L ^ 2 := by ring
    have hrem_sum_le :
        ∑ d ∈ (primeProd z).divisors.filter (fun d : ℕ => d.primeFactors.card ≤ 2 * m), |s.rem d| ≤
          x / L ^ 2 := by
      let D := (primeProd z).divisors.filter (fun d : ℕ => d.primeFactors.card ≤ 2 * m)
      have hterm_le : ∀ d ∈ D, |s.rem d| ≤ (2 : ℝ) ^ (2 * m) := by
        intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hd_sq : Squarefree d := (primeProd_squarefree z).squarefree_of_dvd
          (Nat.dvd_of_mem_divisors hd'.1)
        exact (abs_twinSieveData_rem_le x hd_sq).trans
          (pow_le_pow_right₀ (by norm_num) hd'.2)
      have hD_card : (D.card : ℝ) ≤ z ^ (2 * m) := by
        have hD_sub : D ⊆ Finset.Icc 1 (⌊z⌋₊ ^ (2 * m)) := by
          intro d hd
          have hd' := Finset.mem_filter.mp hd
          have hd_dvd : d ∣ primeProd z := Nat.dvd_of_mem_divisors hd'.1
          have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_dvd (primeProd_pos z)
          have hd_sq : Squarefree d := (primeProd_squarefree z).squarefree_of_dvd hd_dvd
          have hz_fl_ge1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by norm_num; linarith)
          have hd_le_prod : d ≤ ⌊z⌋₊ ^ d.primeFactors.card := by
            conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
            calc
              ∏ p ∈ d.primeFactors, p
                  ≤ ∏ _p ∈ d.primeFactors, ⌊z⌋₊ := by
                    refine Finset.prod_le_prod fun p hp => ?_
                    have hp_dvd : p ∣ primeProd z :=
                      (Nat.dvd_of_mem_primeFactors hp).trans hd_dvd
                    have hmem : p ∈ primeFinset z := by
                      rw [← primeFactors_primeProd]
                      exact Nat.mem_primeFactors.mpr
                        ⟨Nat.prime_of_mem_primeFactors hp, hp_dvd, primeProd_ne_zero z⟩
                    exact Nat.le_floor (mem_primeFinset_iff.mp hmem).2
              _ = ⌊z⌋₊ ^ d.primeFactors.card := by simp
          exact Finset.mem_Icc.mpr ⟨hd_pos, hd_le_prod.trans (Nat.pow_le_pow_right hz_fl_ge1 hd'.2)⟩
        have hle_nat : D.card ≤ ⌊z⌋₊ ^ (2 * m) := by
          calc D.card ≤ (Finset.Icc 1 (⌊z⌋₊ ^ (2 * m))).card := Finset.card_le_card hD_sub
            _ = ⌊z⌋₊ ^ (2 * m) := by simp
        calc
          (D.card : ℝ) ≤ ((⌊z⌋₊ ^ (2 * m) : ℕ) : ℝ) := by exact_mod_cast hle_nat
          _ = (⌊z⌋₊ : ℝ) ^ (2 * m) := by push_cast; rfl
          _ ≤ z ^ (2 * m) := by
              gcongr
              exact Nat.floor_le (by linarith)
      have hz2m_le : z ^ (2 * m) ≤ Real.exp (L / 2) := by
        have hzm : z ^ (2 * m) = Real.exp ((2 * m : ℝ) * (L / (100 * LL))) := by
          dsimp [z]
          rw [← Real.exp_nat_mul]
          congr 1; push_cast; ring
        rw [hzm]
        refine Real.exp_le_exp.mpr ?_
        have hfrac : (2 * m : ℝ) / (100 * LL) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        calc
          (2 * m : ℝ) * (L / (100 * LL)) = ((2 * m : ℝ) / (100 * LL)) * L := by ring
          _ ≤ (1 / 2) * L := mul_le_mul_of_nonneg_right hfrac hL_pos.le
          _ = L / 2 := by ring
      have h2_2m_le : (2 : ℝ) ^ (2 * m) ≤ Real.exp (42 * LL + 2) := by
        have hlog2_lt1 : Real.log 2 < 1 := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
        have h2pow : (2 : ℝ) ^ (2 * m) = Real.exp ((2 * m : ℝ) * Real.log 2) := by
          conv_lhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          rw [← Real.exp_nat_mul]
          congr 1; push_cast; ring
        rw [h2pow]
        refine Real.exp_le_exp.mpr ?_
        calc
          (2 * m : ℝ) * Real.log 2 ≤ (42 * LL + 2) * 1 :=
              mul_le_mul h2m_le hlog2_lt1.le (Real.log_nonneg (by norm_num)) (by positivity)
          _ = 42 * LL + 2 := by ring
      have hprod_le_x_div : Real.exp (L / 2) * Real.exp (42 * LL + 2) ≤ x / L ^ 2 := by
        have hL2 : L ^ 2 = Real.exp (2 * LL) := by
          rw [show (2 : ℝ) * LL = (2 : ℕ) * LL by norm_num, Real.exp_nat_mul, Real.exp_log hL_pos]
        rw [← Real.exp_add, le_div_iff₀ (sq_pos_of_pos hL_pos), hL2, ← Real.exp_add]
        have hx_exp : x = Real.exp L := (Real.exp_log hx_pos).symm
        conv_rhs => rw [hx_exp]
        refine Real.exp_le_exp.mpr ?_
        linarith
      calc
        ∑ d ∈ D, |s.rem d| ≤ ∑ _d ∈ D, (2 : ℝ) ^ (2 * m) := Finset.sum_le_sum hterm_le
        _ = (D.card : ℝ) * (2 : ℝ) ^ (2 * m) := by simp
        _ ≤ z ^ (2 * m) * (2 : ℝ) ^ (2 * m) := by gcongr
        _ ≤ Real.exp (L / 2) * Real.exp (42 * LL + 2) := mul_le_mul hz2m_le h2_2m_le (by positivity) (by positivity)
        _ ≤ x / L ^ 2 := hprod_le_x_div
    have hz_le_x_div : z ≤ x / L ^ 2 := by
      have hz_le_half : z ≤ Real.exp (L / 2) := by
        dsimp [z]
        refine Real.exp_le_exp.mpr ?_
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hLL_ge20, hL_pos]
      have hhalf_le : Real.exp (L / 2) ≤ x / L ^ 2 := by
        have hL2 : L ^ 2 = Real.exp (2 * LL) := by
          rw [show (2 : ℝ) * LL = (2 : ℕ) * LL by norm_num, Real.exp_nat_mul, Real.exp_log hL_pos]
        rw [le_div_iff₀ (sq_pos_of_pos hL_pos), hL2, ← Real.exp_add]
        have hx_exp : x = Real.exp L := (Real.exp_log hx_pos).symm
        conv_rhs => rw [hx_exp]
        refine Real.exp_le_exp.mpr ?_
        linarith
      exact hz_le_half.trans hhalf_le
    have h1_le_LLsq : 1 ≤ LL ^ 2 := by
      have h1_le_LL : (1 : ℝ) ≤ LL := le_trans (by norm_num) hLL_ge20
      exact one_le_pow₀ h1_le_LL
    have hup : twinPrimeCount x ≤
        z + (s.X * s.eulerProd z +
          |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) +
          ∑ d ∈ (primeProd z).divisors.filter (fun d : ℕ => d.primeFactors.card ≤ 2 * m), |s.rem d|) := by
      dsimp only [s, twinSieveData] at htwin_le hbrun
      exact htwin_le.trans (add_le_add_right hbrun z)
    have h2_le : (Real.exp 2 * x / L ^ 2) + (x / L ^ 2) + (x / L ^ 2) ≤
        (Real.exp 2 + 2) * x * LL ^ 2 / L ^ 2 := by
      have hx_div_nn : 0 ≤ x / L ^ 2 := div_nonneg hx_pos.le (sq_nonneg _)
      have hmul : (Real.exp 2 + 2) * (x / L ^ 2) ≤ (Real.exp 2 + 2) * (x / L ^ 2) * LL ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) hx_div_nn) h1_le_LLsq
      calc
        (Real.exp 2 * x / L ^ 2) + (x / L ^ 2) + (x / L ^ 2)
            = (Real.exp 2 + 2) * (x / L ^ 2) := by ring
        _ ≤ (Real.exp 2 + 2) * (x / L ^ 2) * LL ^ 2 := hmul
        _ = (Real.exp 2 + 2) * x * LL ^ 2 / L ^ 2 := by ring
    calc
      twinPrimeCount x
          ≤ z + (s.X * s.eulerProd z +
              |s.X| * (Real.log ((s.eulerProd z)⁻¹)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) +
              ∑ d ∈ (primeProd z).divisors.filter (fun d : ℕ => d.primeFactors.card ≤ 2 * m),
                |s.rem d|) := hup
      _ ≤ x / L ^ 2 + ((20000 * C_mert ^ 2) * x * LL ^ 2 / L ^ 2 +
            Real.exp 2 * x / L ^ 2 + x / L ^ 2) :=
            add_le_add hz_le_x_div (add_le_add (add_le_add hmain_term hexp_fac_err) hrem_sum_le)
      _ = (20000 * C_mert ^ 2) * x * LL ^ 2 / L ^ 2 +
            (Real.exp 2 * x / L ^ 2 + x / L ^ 2 + x / L ^ 2) := by ring
      _ ≤ (20000 * C_mert ^ 2) * x * LL ^ 2 / L ^ 2 +
            (Real.exp 2 + 2) * x * LL ^ 2 / L ^ 2 := add_le_add le_rfl h2_le
      _ = C_lg * x * LL ^ 2 / L ^ 2 := by dsimp [C_lg]; ring
  exact h_goal

/-- **Brun's Theorem on Twin Primes** (explicit upper bound):
there exists a positive constant `C` such that for all `x ≥ 3`,
`π₂(x) ≤ C * x * (log (log x))^2 / (log x)^2`. -/
theorem brun_twin_primes_bound :
    ∃ C > 0, ∀ x : ℝ, 3 ≤ x →
      twinPrimeCount x ≤ C * x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := by
  let x₀ : ℝ := Real.exp (Real.exp brunK0)
  have hexp_1_lt3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog3_gt1 : 1 < Real.log 3 := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp_1_lt3
  have hloglog3_pos : 0 < Real.log (Real.log 3) := Real.log_pos hlog3_gt1
  have hx₀_ge3 : 3 ≤ x₀ := by
    have h2_le_exp : (2 : ℝ) ≤ Real.exp brunK0 := by
      have : (2 : ℝ) ≤ brunK0 := le_trans (by norm_num) brunK0_ge20
      exact this.trans (by linarith [Real.add_one_le_exp brunK0])
    have hexp2 : Real.exp 2 ≤ x₀ := Real.exp_le_exp.mpr h2_le_exp
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hlogx₀_pos : 0 < Real.log x₀ := Real.log_pos (by linarith)
  let C_lg : ℝ := 20000 * brunCmert ^ 2 + Real.exp 2 + 2
  let C_sm : ℝ := (Real.log x₀) ^ 2 / (Real.log (Real.log 3)) ^ 2
  let C : ℝ := max C_lg C_sm
  have hC_pos : 0 < C := by
    have hClg : 0 < C_lg := by
      have := brunCmert_pos
      positivity
    exact lt_of_lt_of_le hClg (le_max_left _ _)
  refine ⟨C, hC_pos, fun x hx => ?_⟩
  by_cases hbig : x₀ ≤ x
  · calc
      twinPrimeCount x
          ≤ C_lg * x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 :=
            brun_twin_primes_large x hbig
      _ ≤ C * x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := by
            have hC_ge : C_lg ≤ C := le_max_left _ _
            gcongr
  · have hx_lt : x < x₀ := lt_of_not_ge hbig
    have hx0 : 0 ≤ x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx_le : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hx_lt.le
    have hloglog_ge : Real.log (Real.log 3) ≤ Real.log (Real.log x) := by
      refine Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) hx)
    have h1 : 1 ≤ C_sm * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := by
      have hnum : (Real.log (Real.log 3)) ^ 2 ≤ (Real.log (Real.log x)) ^ 2 := by gcongr
      have hden : (Real.log x) ^ 2 ≤ (Real.log x₀) ^ 2 := by gcongr
      calc
        (1 : ℝ) = ((Real.log x₀) ^ 2 / (Real.log (Real.log 3)) ^ 2) *
            (Real.log (Real.log 3)) ^ 2 / (Real.log x₀) ^ 2 := by
              field_simp [hlogx₀_pos.ne', hloglog3_pos.ne']
        _ ≤ C_sm * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := by
              dsimp [C_sm]
              gcongr
    calc
      twinPrimeCount x ≤ x := twinPrimeCount_le_self hx0
      _ = x * 1 := (mul_one _).symm
      _ ≤ x * (C_sm * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hx0
      _ = C_sm * x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := by ring
      _ ≤ C * x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := by
            have hC_ge : C_sm ≤ C := le_max_right _ _
            gcongr

/-- **Brun's Theorem on Twin Primes** (Big-O form):
`π₂(x) = O(x * (log (log x))^2 / (log x)^2)` as `x → ∞`. -/
theorem brun_twin_primes_isBigO :
    twinPrimeCount =O[atTop]
      (fun x : ℝ => x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2) := by
  rcases brun_twin_primes_bound with ⟨C, _, hC⟩
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
  have hx3 : 3 ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hloglogx : 0 ≤ Real.log (Real.log x) := by
    refine Real.log_nonneg ?_
    have hexp1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) (by linarith)
  rw [Real.norm_of_nonneg (twinPrimeCount_nonneg x),
    Real.norm_of_nonneg (by positivity)]
  calc
    twinPrimeCount x ≤ C * x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2 := hC x hx3
    _ = C * (x * (Real.log (Real.log x)) ^ 2 / (Real.log x) ^ 2) := by ring

/-- **Brun's Theorem**: the sum of the reciprocals of all twin primes converges! -/
theorem brun_twin_primes_summable :
    Summable (fun p : ℕ => if p.Prime ∧ (p + 2).Prime then (1 : ℝ) / (p : ℝ) else 0) := by
  let f : ℕ → ℝ := fun p => if p.Prime ∧ (p + 2).Prime then (1 : ℝ) / (p : ℝ) else 0
  have hf_nn : ∀ p : ℕ, 0 ≤ f p := fun p => by
    dsimp [f]; split_ifs <;> positivity
  rcases brun_twin_primes_bound with ⟨C, hC_pos, hC⟩
  let C_dyad : ℝ := 2 * C * 16 * (2 : ℝ) ^ (3 / 2 : ℝ)
  have hblock : ∀ k : ℕ, 2 ≤ k →
      ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p ≤
        C_dyad * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    intro k hk
    have h2k_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hx_ge3 : (3 : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
      have : 8 ≤ 2 ^ (k + 1) := calc
        8 = 2 ^ (2 + 1) := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast (by omega : 3 ≤ 2 ^ (k + 1))
    have hterm : ∀ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        f p ≤ (if p.Prime ∧ (p + 2).Prime then (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) else 0) := by
      intro p hp
      have hp1 : 2 ^ k ≤ p := (Finset.mem_Ico.mp hp).1
      dsimp [f]
      split_ifs
      · exact div_le_div_of_nonneg_left zero_le_one h2k_pos (by exact_mod_cast hp1)
      · rfl
    have hsub :
        (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun p => p.Prime ∧ (p + 2).Prime) ⊆
          (Finset.Icc 1 ⌊((2 ^ (k + 1) : ℕ) : ℝ)⌋₊).filter (fun p => p.Prime ∧ (p + 2).Prime) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp_ico := Finset.mem_Ico.mp hp'.1
      have h1_le : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      rw [Nat.floor_natCast]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1_le.trans hp_ico.1, hp_ico.2.le⟩, hp'.2⟩
    have hsum_le :
        ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p ≤
          twinPrimeCount ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
      calc
        ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p
            ≤ ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
                (if p.Prime ∧ (p + 2).Prime then (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) else 0) :=
              Finset.sum_le_sum hterm
        _ = (((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
              (fun p => p.Prime ∧ (p + 2).Prime)).card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
                mul_one_div]
        _ ≤ twinPrimeCount ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
              gcongr
              unfold twinPrimeCount
              exact_mod_cast Finset.card_le_card hsub
    have hbrun_k := hC ((2 ^ (k + 1) : ℕ) : ℝ) hx_ge3
    let u : ℝ := Real.log ((2 ^ (k + 1) : ℕ) : ℝ)
    have hu_eq : u = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      dsimp [u]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hu_ge1 : 1 ≤ u := by
      rw [hu_eq]
      have hk1 : (3 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 1)
      have hlog2_gt : 1 / 2 < Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      nlinarith
    have hlog_u_le : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
      have hu_pos : 0 < u := by linarith
      have hrpow_pos : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu_pos _
      have h1 : Real.log (u ^ (1 / 4 : ℝ)) ≤ u ^ (1 / 4 : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hrpow_pos]
      rw [Real.log_rpow hu_pos] at h1
      linarith
    have hlog_u_nn : 0 ≤ Real.log u := Real.log_nonneg hu_ge1
    have hratio_u : (Real.log u) ^ 2 / u ^ 2 ≤ 16 * u ^ (-(3 / 2 : ℝ)) := by
      have hu_pos : 0 < u := by linarith
      have hsq : (Real.log u) ^ 2 ≤ 16 * (u ^ (1 / 4 : ℝ)) ^ 2 := by
        calc
          (Real.log u) ^ 2 ≤ (4 * u ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
          _ = 16 * (u ^ (1 / 4 : ℝ)) ^ 2 := by ring
      have hpow2 : (u ^ (1 / 4 : ℝ)) ^ 2 = u ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_pos.le]
        congr 1; norm_num
      have hpow_neg : u ^ (1 / 2 : ℝ) / u ^ 2 = u ^ (-(3 / 2 : ℝ)) := by
        rw [show u ^ 2 = u ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub hu_pos]
        congr 1; norm_num
      calc
        (Real.log u) ^ 2 / u ^ 2 ≤ 16 * (u ^ (1 / 4 : ℝ)) ^ 2 / u ^ 2 := by gcongr
        _ = 16 * (u ^ (1 / 2 : ℝ) / u ^ 2) := by rw [hpow2]; ring
        _ = 16 * u ^ (-(3 / 2 : ℝ)) := by rw [hpow_neg]
    have hu_ge_half : ((k + 1 : ℕ) : ℝ) / 2 ≤ u := by
      rw [hu_eq]
      have hlog2_gt : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith
    have hu_rpow_le : u ^ (-(3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have h1 : (((k + 1 : ℕ) : ℝ) / 2) ^ (3 / 2 : ℝ) ≤ u ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hu_ge_half (by norm_num)
      have h2 : (((k + 1 : ℕ) : ℝ) / 2) ^ (3 / 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) / (2 : ℝ) ^ (3 / 2 : ℝ) :=
        Real.div_rpow hk1_pos.le (by norm_num) _
      rw [h2] at h1
      have hneg : u ^ (-(3 / 2 : ℝ)) = (u ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg (by linarith) _
      rw [hneg]
      have hpos_div : 0 < ((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) / (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
      calc
        (u ^ (3 / 2 : ℝ))⁻¹ ≤ (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) / (2 : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
            inv_anti₀ hpos_div h1
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [inv_div, div_eq_mul_inv]
    have h2k1_div : ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) = 2 := by
      push_cast
      rw [pow_succ]
      field_simp [h2k_pos.ne']
    calc
      ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p
          ≤ twinPrimeCount ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) := hsum_le
      _ ≤ (C * ((2 ^ (k + 1) : ℕ) : ℝ) * (Real.log u) ^ 2 / u ^ 2) / ((2 ^ k : ℕ) : ℝ) := by
            gcongr
      _ = 2 * C * ((Real.log u) ^ 2 / u ^ 2) := by
            rw [← h2k1_div]; ring
      _ ≤ 2 * C * (16 * u ^ (-(3 / 2 : ℝ))) := by gcongr
      _ ≤ 2 * C * (16 * ((2 : ℝ) ^ (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹)) := by
            gcongr
      _ = C_dyad * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by dsimp [C_dyad]; ring
  have hsum_p : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h0
  let B : ℝ := (∑ p ∈ Finset.range 4, f p) +
    C_dyad * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹
  have hbound : ∀ N : ℕ, ∑ p ∈ Finset.range N, f p ≤ B := by
    intro N
    let blocks := Finset.Ico 2 (N + 2)
    have hsub_union : Finset.range N ⊆ Finset.range 4 ∪
        blocks.biUnion (fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
      intro p hp
      have hpN : p < N := Finset.mem_range.mp hp
      by_cases hp4 : p < 4
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr hp4)
      · have hp_ge4 : 4 ≤ p := not_lt.mp hp4
        refine Finset.mem_union_right _ ?_
        rw [Finset.mem_biUnion]
        let k := Nat.log 2 p
        have hk_ge2 : 2 ≤ k := by
          dsimp [k]
          rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
          omega
        have hk_lt : k < N + 2 := by
          have hk_le_p : k ≤ p := Nat.log_le_self 2 p
          omega
        refine ⟨k, Finset.mem_Ico.mpr ⟨hk_ge2, hk_lt⟩, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
        · exact Nat.pow_log_le_self 2 (by omega)
        · exact Nat.lt_pow_succ_log_self (by norm_num) p
    have hpair : (blocks : Set ℕ).PairwiseDisjoint (fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
      intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_Ico] at hp1 hp2
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hpow : 2 ^ (k₁ + 1) ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      · have hpow : 2 ^ (k₂ + 1) ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) hlt
        omega
    have hdisj_four : Disjoint (Finset.range 4)
        (blocks.biUnion (fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1)))) := by
      rw [Finset.disjoint_left]
      intro p hp4 hpbi
      rw [Finset.mem_range] at hp4
      rw [Finset.mem_biUnion] at hpbi
      rcases hpbi with ⟨k, hk, hpk⟩
      have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
      have hpk1 : 2 ^ k ≤ p := (Finset.mem_Ico.mp hpk).1
      have h4 : 4 ≤ 2 ^ k := calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    calc
      ∑ p ∈ Finset.range N, f p
          ≤ ∑ p ∈ Finset.range 4 ∪
              blocks.biUnion (fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1))), f p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_union (fun p _ _ => hf_nn p)
      _ = (∑ p ∈ Finset.range 4, f p) +
            ∑ p ∈ blocks.biUnion (fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1))), f p :=
            Finset.sum_union hdisj_four
      _ = (∑ p ∈ Finset.range 4, f p) +
            ∑ k ∈ blocks, ∑ p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f p := by
            rw [Finset.sum_biUnion hpair]
      _ ≤ (∑ p ∈ Finset.range 4, f p) +
            ∑ k ∈ blocks, C_dyad * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            gcongr with k hk
            exact hblock k (Finset.mem_Ico.mp hk).1
      _ = (∑ p ∈ Finset.range 4, f p) +
            C_dyad * ∑ k ∈ blocks, (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← Finset.mul_sum]
      _ ≤ B := by
            dsimp [B]
            gcongr
            exact Summable.sum_le_tsum _ (fun _ _ => by positivity) hsum_p
  exact summable_of_sum_range_le hf_nn hbound

end BrunsTwinPrimes

end AnalyticNumberTheory.SieveMethods
