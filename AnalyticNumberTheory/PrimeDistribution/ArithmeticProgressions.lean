import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.DirichletSeries.Perron
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.WeakPNT

/-!
# Primes in Arithmetic Progressions

This file develops prime distribution in arithmetic progressions `a (mod q)` in the namespace
`AnalyticNumberTheory.PrimeDistribution`:

- Chebyshev functions in arithmetic progressions: `psiAP`, `thetaAP`, `primeCountingAP`, and `piAP`,
  along with monotonicity, positivity, comparison bounds, `O(√x)` error transfer, and
  Abel-summation equivalence identities relating `piAP` and `thetaAP`.
- Complex-valued character sums `psiChar`, `thetaChar`, `piChar`, together with exact Dirichlet
  character orthogonality decompositions for `Nat.Coprime a q` and an explicit bound on the
  difference between `Chebyshev.psi` and `psiChar · 1`.
- Bridges to Mathlib's Dirichlet theorem (`dirichlet_primesInAP_infinite`, `tendsto_piAP_atTop`)
  and the prime number theorem in arithmetic progressions (`tendsto_psiAP_div`,
  `tendsto_thetaAP_div`, `tendsto_piAP_mul_log_div`, and asymptotic equivalence forms).
- The uniform Siegel–Walfisz predicate `SiegelWalfiszBound`, unconditional deductions of uniform
  `thetaAP` and logarithmic-integral `piAP` bounds from `SiegelWalfiszBound`, unconditional
  reduction of `psiAP x q a - x / φ(q)` to nontrivial character sums `psiChar x χ`, the explicit
  rectangular residue integral `(1 / (2πi)) ∮ (s - 1)⁻¹ ds = 1`, and Perron contour-shift bounds
  for both nontrivial and principal characters from rectangular zero-free regions.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Finset MeasureTheory Set Filter Asymptotics
open Complex (I reProdIm)
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation
open Classical

/-! ### Chebyshev Functions in Arithmetic Progressions -/

/-- Second Chebyshev function in arithmetic progressions:
`ψ(x; q, a) = ∑_{1 ≤ n ≤ x, n ≡ a [MOD q]} Λ(n)`. -/
noncomputable def psiAP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ a [MOD q], Λ n

/-- First Chebyshev function in arithmetic progressions:
`θ(x; q, a) = ∑_{1 ≤ p ≤ x, p prime, p ≡ a [MOD q]} log p`. -/
noncomputable def thetaAP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], Real.log p

/-- Integer-valued prime counting function in arithmetic progressions:
number of primes `p ≤ x` satisfying `p ≡ a [MOD q]`. -/
noncomputable def primeCountingAP (x : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card

/-- Real-valued prime counting function `π(x; q, a)` in arithmetic progressions. -/
noncomputable def piAP (x : ℝ) (q a : ℕ) : ℝ :=
  (primeCountingAP x q a : ℝ)

/-- `psiAP x q a` agrees with the sum starting from `n = 0` because `Λ 0 = 0`. -/
theorem psiAP_eq_sum_Icc0 (x : ℝ) (q a : ℕ) :
    psiAP x q a = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊ with n ≡ a [MOD q], Λ n := by
  unfold psiAP
  have hIcc : Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [Finset.sum_filter, Finset.sum_filter, hIcc, Finset.sum_insert (by simp)]
  simp [ArithmeticFunction.map_zero]

/-- `thetaAP x q a` agrees with the `Finset.Ioc 0 ⌊x⌋₊` sum used in Mathlib. -/
theorem thetaAP_eq_sum_Ioc (x : ℝ) (q a : ℕ) :
    thetaAP x q a = ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], Real.log p := by
  unfold thetaAP
  rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- `primeCountingAP x q a` agrees with the `Finset.Ioc 0 ⌊x⌋₊` cardinality used in Mathlib. -/
theorem primeCountingAP_eq_card_Ioc (x : ℝ) (q a : ℕ) :
    primeCountingAP x q a = ((Finset.Ioc 0 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card := by
  unfold primeCountingAP
  rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- `piAP x q a` expressed as a sum of `1` over primes `p ≤ x` with `p ≡ a [MOD q]`. -/
theorem piAP_eq_sum (x : ℝ) (q a : ℕ) :
    piAP x q a = ∑ _p ∈ Finset.Icc 1 ⌊x⌋₊ with _p.Prime ∧ _p ≡ a [MOD q], (1 : ℝ) := by
  rw [piAP, primeCountingAP]
  simp

/-- `psiAP x q a` is nonnegative for all `x`, `q`, `a`. -/
theorem psiAP_nonneg (x : ℝ) (q a : ℕ) : 0 ≤ psiAP x q a :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- `thetaAP x q a` is nonnegative for all `x`, `q`, `a`. -/
theorem thetaAP_nonneg (x : ℝ) (q a : ℕ) : 0 ≤ thetaAP x q a :=
  Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le)

/-- `piAP x q a` is nonnegative for all `x`, `q`, `a`. -/
theorem piAP_nonneg (x : ℝ) (q a : ℕ) : 0 ≤ piAP x q a :=
  Nat.cast_nonneg _

/-- Monotonicity of `x ↦ psiAP x q a`. -/
theorem psiAP_mono {q a : ℕ} {x y : ℝ} (hxy : x ≤ y) : psiAP x q a ≤ psiAP y q a := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ =>
    ArithmeticFunction.vonMangoldt_nonneg
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono hxy)⟩, hn.2⟩

/-- Monotonicity of `x ↦ thetaAP x q a`. -/
theorem thetaAP_mono {q a : ℕ} {x y : ℝ} (hxy : x ≤ y) : thetaAP x q a ≤ thetaAP y q a := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_
  · simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hxy)⟩, hp.2⟩
  · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le)

/-- Monotonicity of `x ↦ piAP x q a`. -/
theorem piAP_mono {q a : ℕ} {x y : ℝ} (hxy : x ≤ y) : piAP x q a ≤ piAP y q a := by
  unfold piAP primeCountingAP
  exact_mod_cast Finset.card_le_card fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hxy)⟩, hp.2⟩

/-- `psiAP x q a` vanishes whenever `x < 1`. -/
theorem psiAP_eq_zero_of_lt_one {x : ℝ} (hx : x < 1) (q a : ℕ) : psiAP x q a = 0 := by
  have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [psiAP, hfl]

/-- `thetaAP x q a` vanishes whenever `x < 2`. -/
theorem thetaAP_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) (q a : ℕ) : thetaAP x q a = 0 := by
  have hfl : ⌊x⌋₊ < 2 := by
    by_cases hx0 : 0 ≤ x
    · exact (Nat.floor_lt hx0).mpr (by exact_mod_cast hx)
    · simp [Nat.floor_of_nonpos (not_le.mp hx0).le]
  have hempty : (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have := hp.2.1.two_le
    omega
  simp [thetaAP, hempty]

/-- `piAP x q a` vanishes whenever `x < 2`. -/
theorem piAP_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) (q a : ℕ) : piAP x q a = 0 := by
  have hfl : ⌊x⌋₊ < 2 := by
    by_cases hx0 : 0 ≤ x
    · exact (Nat.floor_lt hx0).mpr (by exact_mod_cast hx)
    · simp [Nat.floor_of_nonpos (not_le.mp hx0).le]
  have hempty : (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have := hp.2.1.two_le
    omega
  simp [piAP, primeCountingAP, hempty]

/-- Comparison `θ(x; q, a) ≤ ψ(x; q, a)`. -/
theorem thetaAP_le_psiAP (x : ℝ) (q a : ℕ) : thetaAP x q a ≤ psiAP x q a := by
  have hsub : (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
      (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]) := fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have htheta : thetaAP x q a =
      ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], Λ p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2.1).symm
  rw [htheta]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Comparison `ψ(x; q, a) ≤ ψ(x)` against the full second Chebyshev function. -/
theorem psiAP_le_psi (x : ℝ) (q a : ℕ) : psiAP x q a ≤ Chebyshev.psi x := by
  rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Comparison `θ(x; q, a) ≤ θ(x)` against the full first Chebyshev function. -/
theorem thetaAP_le_theta (x : ℝ) (q a : ℕ) : thetaAP x q a ≤ Chebyshev.theta x := by
  rw [Chebyshev.theta, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_
  · simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)

/-- Comparison `π(x; q, a) ≤ π(x)` against the full prime counting function. -/
theorem piAP_le_primeCounting (x : ℝ) (q a : ℕ) :
    piAP x q a ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
  unfold piAP primeCountingAP
  exact_mod_cast Finset.card_le_card fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩

/-- Upper bound `θ(x; q, a) ≤ π(x; q, a) * log x` valid for all `x : ℝ`. -/
theorem thetaAP_le_piAP_mul_log (x : ℝ) (q a : ℕ) : thetaAP x q a ≤ piAP x q a * Real.log x := by
  rcases lt_or_ge x 2 with hx | hx
  · rw [thetaAP_eq_zero_of_lt_two hx, piAP_eq_zero_of_lt_two hx, zero_mul]
  · have hx0 : 0 < x := lt_of_lt_of_le zero_lt_two hx
    rw [piAP_eq_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos
    have hp_le : (p : ℝ) ≤ x :=
      (by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 : (p : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le hx0.le)
    rw [one_mul]
    exact Real.log_le_log hp_pos hp_le

/-- Upper bound `ψ(x; q, a) ≤ π(x) * log x` valid for all `x : ℝ`. -/
theorem psiAP_le_primeCounting_mul_log (x : ℝ) (q a : ℕ) :
    psiAP x q a ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x :=
  (psiAP_le_psi x q a).trans (Chebyshev.psi_le_primeCounting_mul_log' x)

/-- Upper bound `ψ(x; q, a) - θ(x; q, a) ≤ ψ(x) - θ(x)` by nonnegativity of `Λ`. -/
theorem psiAP_sub_thetaAP_le_psi_sub_theta (x : ℝ) (q a : ℕ) :
    psiAP x q a - thetaAP x q a ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hap : psiAP x q a - thetaAP x q a =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime ∧ n ≡ a [MOD q], Λ n := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q])) Nat.Prime Λ
    have h1 : ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q])).filter Nat.Prime =
        (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
      ext n; simp only [Finset.mem_filter]; tauto
    have h2 : ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q])).filter (fun n => ¬n.Prime) =
        (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬n.Prime ∧ n ≡ a [MOD q]) := by
      ext n; simp only [Finset.mem_filter]; tauto
    have htheta : thetaAP x q a =
        ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], Λ p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2.1).symm
    rw [psiAP, htheta, ← hsplit, h1, h2]
    ring
  have hfull : Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, Λ n := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) Nat.Prime Λ
    have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
      rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    have htheta : Chebyshev.theta x = ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Λ p := by
      rw [Chebyshev.theta, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
      refine Finset.sum_congr rfl fun p hp => ?_
      exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm
    rw [hpsi, htheta, ← hsplit]
    ring
  rw [hap, hfull]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ =>
    ArithmeticFunction.vonMangoldt_nonneg
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

/-- Uniform explicit `O(√x)` bound `|ψ(x; q, a) - θ(x; q, a)| ≤ 3 * (log 4 + 4) * √x`. -/
theorem abs_psiAP_sub_thetaAP_le (x : ℝ) (q a : ℕ) :
    |psiAP x q a - thetaAP x q a| ≤ (Real.log 4 + 4) * 3 * Real.sqrt x := by
  rw [abs_of_nonneg (sub_nonneg.mpr (thetaAP_le_psiAP x q a))]
  refine (psiAP_sub_thetaAP_le_psi_sub_theta x q a).trans ?_
  rcases le_total x 1 with hx | hx
  · rw [Chebyshev.theta_eq_zero_of_le_one hx, Chebyshev.psi_eq_zero_of_le_one hx, sub_self]
    positivity
  · have hpow (n : ℕ) (hn : 2 ≤ n) :
        Chebyshev.psi (x ^ (n : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      have hr : 0 ≤ x ^ (n : ℝ)⁻¹ := Real.rpow_nonneg (zero_le_one.trans hx) _
      refine (Chebyshev.psi_le_const_mul_self hr).trans ?_
      rw [Real.sqrt_eq_rpow, one_div]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx
          (inv_anti₀ (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn : (2 : ℝ) ≤ n)))
        (by positivity)
    have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    have h2 : Chebyshev.psi (x ^ (2 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      simpa using hpow 2 le_rfl
    have h3 : Chebyshev.psi (x ^ (3 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      simpa using hpow 3 (by omega)
    have h5 : Chebyshev.psi (x ^ (5 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      simpa using hpow 5 (by omega)
    linarith

/-- Uniform `O(√x)` error estimate `ψ(x; q, a) - θ(x; q, a) = O(√x)` as `x → ∞`. -/
theorem psiAP_sub_thetaAP_isBigO_sqrt (q a : ℕ) :
    (fun x : ℝ => psiAP x q a - thetaAP x q a) =O[atTop] Real.sqrt :=
  IsBigO.of_bound ((Real.log 4 + 4) * 3) <| Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)] using
      abs_psiAP_sub_thetaAP_le x q a

private theorem continuousOn_log_Icc {a b : ℝ} (ha : 0 < a) :
    ContinuousOn Real.log (Set.Icc a b) :=
  Real.continuousOn_log.mono fun _t ht => (lt_of_lt_of_le ha ht.1).ne'

private theorem intervalIntegrable_thetaAP_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) (q a : ℕ) :
    IntervalIntegrable (fun t : ℝ => thetaAP t q a / (t * Real.log t ^ 2)) volume 2 x := by
  have hmono : Monotone fun t : ℝ => thetaAP t q a := fun _ _ h => thetaAP_mono h
  have h1 : IntervalIntegrable (fun t : ℝ => thetaAP t q a) volume 2 x :=
    (hmono.monotoneOn _).intervalIntegrable
  have h2 : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc (2 : ℝ) x) := by
    refine (continuousOn_id.mul ((continuousOn_log_Icc zero_lt_two).pow 2)).inv₀ fun t ht => ?_
    exact mul_ne_zero (lt_of_lt_of_le zero_lt_two ht.1).ne'
      (pow_ne_zero 2 (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne')
  rw [← Set.uIcc_of_le hx] at h2
  simpa [div_eq_mul_inv] using h1.mul_continuousOn h2

private theorem intervalIntegrable_piAP_div {x : ℝ} (hx : 2 ≤ x) (q a : ℕ) :
    IntervalIntegrable (fun t : ℝ => piAP t q a / t) volume 2 x := by
  have hmono : Monotone fun t : ℝ => piAP t q a := fun _ _ h => piAP_mono h
  have h1 : IntervalIntegrable (fun t : ℝ => piAP t q a) volume 2 x :=
    (hmono.monotoneOn _).intervalIntegrable
  have h2 : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (2 : ℝ) x) :=
    continuousOn_id.inv₀ fun t ht => (lt_of_lt_of_le zero_lt_two ht.1).ne'
  rw [← Set.uIcc_of_le hx] at h2
  simpa [div_eq_mul_inv] using h1.mul_continuousOn h2

/-- Abel-summation identity expressing `π(x; q, a)` in terms of `θ(t; q, a)` for `2 ≤ x`. -/
theorem piAP_eq_thetaAP_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) (q a : ℕ) :
    piAP x q a = thetaAP x q a / Real.log x +
      ∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let c : ℕ → ℝ := fun p => if p.Prime ∧ p ≡ a [MOD q] then Real.log p else 0
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(t * Real.log t ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le one_lt_two ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    convert (Real.hasDerivAt_log ht0).inv hlogt using 1
    field_simp [ht0, hlogt]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hcont : ContinuousOn (deriv (fun u : ℝ => (Real.log u)⁻¹)) (Set.Icc (2 : ℝ) x) := by
    have hEq : Set.EqOn (deriv (fun u : ℝ => (Real.log u)⁻¹))
        (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc (2 : ℝ) x) :=
      fun t ht => (hderiv t ht).deriv
    refine ContinuousOn.congr ?_ hEq
    exact ((continuousOn_id.mul ((continuousOn_log_Icc zero_lt_two).pow 2)).inv₀ fun t ht =>
      mul_ne_zero (lt_of_lt_of_le zero_lt_two ht.1).ne'
        (pow_ne_zero 2 (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne')).neg
  have hAbel := abel_summation_Ioc_one c zero_le_two hx hdiff hcont
  have hc_sum : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k = thetaAP t q a := by
    intro t
    unfold thetaAP
    rw [Finset.sum_filter]
  have hfl2 : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
  have h2_term : thetaAP 2 q a * (Real.log 2)⁻¹ = if 2 ≡ a [MOD q] then 1 else 0 := by
    have hpl : (Finset.Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) =
        if 2 ≡ a [MOD q] then {2} else ∅ := by
      rw [hfl2]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      split_ifs with h2
      · simp only [Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hp1, hp2⟩, hp_pr, _⟩
          have := hp_pr.two_le
          omega
        · rintro rfl
          exact ⟨⟨by omega, le_rfl⟩, Nat.prime_two, h2⟩
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨⟨hp1, hp2⟩, hp_pr, hp_mod⟩
        have := hp_pr.two_le
        have hp_eq : p = 2 := by omega
        exact h2 (hp_eq ▸ hp_mod)
    unfold thetaAP
    rw [hpl]
    split_ifs <;> simp [hlog2.ne']
  have hLHS : piAP x q a =
      (if 2 ≡ a [MOD q] then 1 else 0) + ∑ k ∈ Finset.Ioc ⌊(2 : ℝ)⌋₊ ⌊x⌋₊, c k * (Real.log k)⁻¹ := by
    have hfl_x : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hx
    have hIcc : Finset.Icc 2 ⌊x⌋₊ = insert 2 (Finset.Ioc 2 ⌊x⌋₊) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hpi_sum : piAP x q a = ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, c k * (Real.log k)⁻¹ := by
      rw [piAP_eq_sum, Finset.sum_filter]
      have hIcc12 : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc12, Finset.sum_insert (by simp)]
      simp only [Nat.not_prime_one, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hlogk : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < k))).ne'
      dsimp [c]
      split_ifs with h
      · field_simp [hlogk]
      · simp
    rw [hfl2, hpi_sum, hIcc, Finset.sum_insert (by simp)]
    have hc2 : c 2 * (Real.log ((2 : ℕ) : ℝ))⁻¹ = if 2 ≡ a [MOD q] then 1 else 0 := by
      dsimp [c]
      simp only [Nat.prime_two, true_and]
      split_ifs <;> simp [hlog2.ne']
    rw [hc2]
  have hint_congr :
      ∫ t in (2 : ℝ)..x, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) *
          deriv (fun u : ℝ => (Real.log u)⁻¹) t =
        -∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    rw [hc_sum, (hderiv t ht).deriv]
    ring
  rw [hLHS, hAbel, hc_sum, hc_sum, h2_term, hint_congr]
  ring

/-- Abel-summation identity expressing `θ(x; q, a)` in terms of `π(t; q, a)` for `2 ≤ x`. -/
theorem thetaAP_eq_piAP_mul_log_sub_integral {x : ℝ} (hx : 2 ≤ x) (q a : ℕ) :
    thetaAP x q a = piAP x q a * Real.log x - ∫ t in (2 : ℝ)..x, piAP t q a / t := by
  let c : ℕ → ℝ := fun p => if p.Prime ∧ p ≡ a [MOD q] then 1 else 0
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) x, HasDerivAt Real.log t⁻¹ t := fun t ht =>
    Real.hasDerivAt_log (lt_of_lt_of_le zero_lt_two ht.1).ne'
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ Real.log t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hcont : ContinuousOn (deriv Real.log) (Set.Icc (2 : ℝ) x) := by
    refine ContinuousOn.congr (continuousOn_id.inv₀ fun t ht =>
      (lt_of_lt_of_le zero_lt_two ht.1).ne') fun t ht => (hderiv t ht).deriv
  have hAbel := abel_summation_Ioc_one c zero_le_two hx hdiff hcont
  have hc_sum : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k = piAP t q a := by
    intro t
    rw [piAP_eq_sum, Finset.sum_filter]
  have hfl2 : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
  have hpi2 : piAP 2 q a * Real.log 2 = if 2 ≡ a [MOD q] then Real.log 2 else 0 := by
    rw [piAP_eq_sum, hfl2, Finset.sum_filter]
    have h12 : Finset.Icc 1 2 = {1, 2} := by decide
    rw [h12, Finset.sum_pair (by omega)]
    simp [Nat.not_prime_one, Nat.prime_two]
  have hLHS : thetaAP x q a =
      (if 2 ≡ a [MOD q] then Real.log 2 else 0) +
        ∑ k ∈ Finset.Ioc ⌊(2 : ℝ)⌋₊ ⌊x⌋₊, c k * Real.log k := by
    have hfl_x : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hx
    have hIcc : Finset.Icc 2 ⌊x⌋₊ = insert 2 (Finset.Ioc 2 ⌊x⌋₊) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have htheta_sum : thetaAP x q a = ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, c k * Real.log k := by
      rw [thetaAP, Finset.sum_filter]
      have hIcc12 : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc12, Finset.sum_insert (by simp)]
      simp only [Nat.not_prime_one, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [c]
      split_ifs <;> ring
    rw [hfl2, htheta_sum, hIcc, Finset.sum_insert (by simp)]
    dsimp [c]
    simp only [Nat.prime_two, true_and]
    split_ifs <;> simp
  have hint_congr :
      ∫ t in (2 : ℝ)..x, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * deriv Real.log t =
        ∫ t in (2 : ℝ)..x, piAP t q a / t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    rw [hc_sum, (hderiv t ht).deriv, div_eq_mul_inv]
  rw [hLHS, hAbel, hc_sum, hc_sum, hpi2, hint_congr]
  ring

/-- Uniform explicit error bound `|π(x; q, a) - θ(x; q, a) / log x| = O(x / log² x)` for `4 ≤ x`. -/
theorem abs_piAP_sub_thetaAP_div_log_le {x : ℝ} (hx : 4 ≤ x) (q a : ℕ) :
    |piAP x q a - thetaAP x q a / Real.log x| ≤
      Real.log 4 * (4 * x / Real.log x ^ 2 + Real.sqrt x / Real.log 2 ^ 2) := by
  have hx2 : 2 ≤ x := by linarith
  have hsqrt2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hsqrtx : Real.sqrt x ≤ x := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  rw [piAP_eq_thetaAP_div_log_add_integral hx2, add_sub_cancel_left]
  have hnorm : |∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2)| ≤
      ∫ t in (2 : ℝ)..x, ‖thetaAP t q a / (t * Real.log t ^ 2)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hx2
  have hinv_int {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume u v :=
    Chebyshev.intervalIntegrable_one_div_log_sq hu (hu.trans_le huv)
  have hint_le {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
      ∫ t in u..v, 1 / Real.log t ^ 2 ≤ (v - u) / Real.log u ^ 2 := by
    have hmono : ∫ t in u..v, 1 / Real.log t ^ 2 ≤ ∫ _t in u..v, 1 / Real.log u ^ 2 := by
      refine intervalIntegral.integral_mono_on huv (hinv_int hu huv) (by simp) fun t ht => ?_
      have hlu : 0 < Real.log u := Real.log_pos hu
      exact one_div_le_one_div_of_le (sq_pos_of_pos hlu)
        (pow_le_pow_left₀ hlu.le (Real.log_le_log (zero_lt_one.trans hu) ht.1) 2)
    refine hmono.trans_eq ?_
    simp [div_eq_mul_inv]
  have hmono : ∫ t in (2 : ℝ)..x, ‖thetaAP t q a / (t * Real.log t ^ 2)‖ ≤
      ∫ t in (2 : ℝ)..x, Real.log 4 * (1 / Real.log t ^ 2) := by
    refine intervalIntegral.integral_mono_on hx2
      (intervalIntegrable_thetaAP_div_mul_log_sq hx2 q a).norm
      ((hinv_int one_lt_two hx2).const_mul _) fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ht.1
    have hlogt : Real.log t ≠ 0 := (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (thetaAP_nonneg t q a) (by positivity))]
    calc thetaAP t q a / (t * Real.log t ^ 2)
        ≤ (Real.log 4 * t) / (t * Real.log t ^ 2) := by
          gcongr
          exact (thetaAP_le_theta t q a).trans (Chebyshev.theta_le_log4_mul_x ht0.le)
      _ = Real.log 4 * (1 / Real.log t ^ 2) := by field_simp [ht0.ne', hlogt]
  have hsplit : ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 =
      (∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ^ 2) +
        ∫ t in Real.sqrt x..x, 1 / Real.log t ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hinv_int one_lt_two hsqrt2) (hinv_int (by linarith) hsqrtx)).symm
  have hleft : ∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ^ 2 ≤ Real.sqrt x / Real.log 2 ^ 2 := by
    refine (hint_le one_lt_two hsqrt2).trans ?_
    gcongr
    linarith
  have hright : ∫ t in Real.sqrt x..x, 1 / Real.log t ^ 2 ≤ 4 * x / Real.log x ^ 2 := by
    refine (hint_le (by linarith) hsqrtx).trans ?_
    rw [Real.log_sqrt (by linarith), div_pow, div_div_eq_mul_div]
    have hlogx_pos : 0 < Real.log x ^ 2 := sq_pos_of_pos (Real.log_pos (by linarith))
    have hle : x - Real.sqrt x ≤ x := by linarith [Real.sqrt_nonneg x]
    calc (x - Real.sqrt x) * (2 : ℝ) ^ 2 / Real.log x ^ 2
        ≤ x * (2 : ℝ) ^ 2 / Real.log x ^ 2 := by gcongr
      _ = 4 * x / Real.log x ^ 2 := by ring
  calc |∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2)|
      ≤ Real.log 4 * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
        hnorm.trans (hmono.trans_eq (intervalIntegral.integral_const_mul _ _))
    _ ≤ Real.log 4 * (4 * x / Real.log x ^ 2 + Real.sqrt x / Real.log 2 ^ 2) := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg (by norm_num))

/-- Asymptotic `O(x / log² x)` relation `π(x; q, a) - θ(x; q, a) / log x = O(x / log² x)`. -/
theorem piAP_sub_thetaAP_div_log_isBigO (q a : ℕ) :
    (fun x : ℝ => piAP x q a - thetaAP x q a / Real.log x) =O[atTop]
      (fun x : ℝ => x / Real.log x ^ 2) := by
  have hsqrt : Real.sqrt =o[atTop] fun x : ℝ => x / Real.log x ^ 2 := by
    have h1 : Real.log =o[atTop] fun x : ℝ => x ^ (1 / 4 : ℝ) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have h2 : (fun x : ℝ => Real.log x * Real.log x) =o[atTop]
        fun x : ℝ => x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := h1.mul h1
    refine Asymptotics.isLittleO_iff_tendsto' ?_ |>.mpr ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hzero
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      exact absurd hzero (div_ne_zero (by linarith) (pow_ne_zero 2 hlog))
    · refine h2.tendsto_div_nhds_zero.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      have hpow_eq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = Real.sqrt x := by
        rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
        norm_num
      have hsqrt_eq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
      calc Real.log x * Real.log x / (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ))
          = (Real.sqrt x * Real.log x ^ 2) / (Real.sqrt x * Real.sqrt x) := by
            rw [hpow_eq, pow_two]
            field_simp [(Real.sqrt_pos.mpr hx0).ne']
        _ = Real.sqrt x / (x / Real.log x ^ 2) := by
            rw [hsqrt_eq]
            field_simp [hx0.ne', hlog]
  have hsqrtO : Real.sqrt =O[atTop] fun x : ℝ => x / Real.log x ^ 2 := hsqrt.isBigO
  have hmain : (fun x : ℝ => 4 * x / Real.log x ^ 2 + Real.sqrt x / Real.log 2 ^ 2) =O[atTop]
      (fun x : ℝ => x / Real.log x ^ 2) := by
    have h1 : (fun x : ℝ => 4 * (x / Real.log x ^ 2)) =O[atTop]
        (fun x : ℝ => x / Real.log x ^ 2) :=
      isBigO_refl _ _ |>.const_mul_left 4
    have h2 : (fun x : ℝ => Real.sqrt x * (Real.log 2 ^ 2)⁻¹) =O[atTop]
        (fun x : ℝ => x / Real.log x ^ 2) :=
      (hsqrtO.const_mul_left (Real.log 2 ^ 2)⁻¹).congr_left fun x => by ring
    exact (h1.add h2).congr_left fun x => by ring
  refine Asymptotics.IsBigO.trans ?_ (hmain.const_mul_left (Real.log 4))
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hpos2 : 0 ≤ 4 * x / Real.log x ^ 2 + Real.sqrt x / Real.log 2 ^ 2 := by positivity
  simpa [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)),
    abs_of_nonneg hpos2] using abs_piAP_sub_thetaAP_div_log_le hx q a

/-! ### Character Orthogonality Decomposition -/

/-- Complex-valued second Chebyshev sum twisted by a Dirichlet character `χ`. -/
noncomputable def psiChar (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (Λ n : ℂ)

/-- Complex-valued first Chebyshev sum twisted by a Dirichlet character `χ`. -/
noncomputable def thetaChar (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, χ p * (Real.log p : ℂ)

/-- Complex-valued prime counting sum twisted by a Dirichlet character `χ`. -/
noncomputable def piChar (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, χ p

private lemma dirichletChar_inv_eq_star {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q}
    (ha : IsUnit a) : χ a⁻¹ = star (χ a) := by
  have hnorm : ‖χ a‖ = 1 := by
    simpa [ha.unit_spec] using χ.unit_norm_eq_one ha.unit
  have hmul : χ a⁻¹ * χ a = 1 := by
    rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl, map_one]
  calc χ a⁻¹ = (χ a)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    _ = starRingEnd ℂ (χ a) := Complex.inv_eq_conj hnorm
    _ = star (χ a) := rfl

/-- Exact character orthogonality decomposition for an arbitrary finite sum filtered by
`n ≡ a [MOD q]`, assuming `q ≠ 0` and `Nat.Coprime a q`. -/
theorem sum_filter_modEq_eq_inv_totient_mul_sum_char {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q)
    (S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ S with n ≡ a [MOD q], f n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, star (χ a) * ∑ n ∈ S, χ n * f n := by
  have : NeZero q := ⟨hq⟩
  have htot_pos : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have htot_ne : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr htot_pos.ne'
  have ha_unit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  calc ∑ n ∈ S with n ≡ a [MOD q], f n
      = ∑ n ∈ S, (if n ≡ a [MOD q] then (1 : ℂ) else 0) * f n := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> simp
    _ = (q.totient : ℂ)⁻¹ * ∑ n ∈ S,
          (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ n) * f n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have hsum_orth : ∑ χ : DirichletCharacter ℂ q, star (χ a) * χ n =
            if n ≡ a [MOD q] then (q.totient : ℂ) else 0 := by
          have h1 : ∀ χ : DirichletCharacter ℂ q, star (χ a) = χ (a : ZMod q)⁻¹ := fun χ =>
            (dirichletChar_inv_eq_star χ ha_unit).symm
          simp_rw [h1]
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha_unit (n : ZMod q)]
          have hiff : (a : ZMod q) = (n : ZMod q) ↔ n ≡ a [MOD q] := by
            rw [ZMod.natCast_eq_natCast_iff]
            exact Nat.ModEq.comm
          simp [hiff]
        rw [hsum_orth]
        split_ifs
        · field_simp [htot_ne]
        · simp
    _ = (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, star (χ a) * ∑ n ∈ S, χ n * f n := by
        congr 1
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring

/-- Exact character orthogonality decomposition for `ψ(x; q, a)`. -/
theorem psiAP_eq_inv_totient_mul_sum_psiChar {x : ℝ} {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q) :
    (psiAP x q a : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, star (χ a) * psiChar x χ := by
  unfold psiAP psiChar
  push_cast
  exact sum_filter_modEq_eq_inv_totient_mul_sum_char hq ha (Finset.Icc 1 ⌊x⌋₊) fun n => (Λ n : ℂ)

/-- Exact character orthogonality decomposition for `θ(x; q, a)`. -/
theorem thetaAP_eq_inv_totient_mul_sum_thetaChar {x : ℝ} {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q) :
    (thetaAP x q a : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, star (χ a) * thetaChar x χ := by
  unfold thetaAP thetaChar
  rw [Complex.ofReal_sum]
  have h1 :
      ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], (Real.log p : ℂ) =
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime with p ≡ a [MOD q], (Real.log p : ℂ) := by
    rw [Finset.filter_filter]
  change (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], (Real.log p : ℂ)) =
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, star (χ a) *
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, χ p * (Real.log p : ℂ)
  rw [h1]
  exact sum_filter_modEq_eq_inv_totient_mul_sum_char hq ha
    ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) fun p => (Real.log p : ℂ)

/-- Exact character orthogonality decomposition for `π(x; q, a)`. -/
theorem piAP_eq_inv_totient_mul_sum_piChar {x : ℝ} {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q) :
    (piAP x q a : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, star (χ a) * piChar x χ := by
  rw [piAP_eq_sum]
  unfold piChar
  push_cast
  have h1 :
      ∑ _p ∈ Finset.Icc 1 ⌊x⌋₊ with _p.Prime ∧ _p ≡ a [MOD q], (1 : ℂ) =
        ∑ _p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime with _p ≡ a [MOD q], (1 : ℂ) := by
    rw [Finset.filter_filter]
  have h2 := sum_filter_modEq_eq_inv_totient_mul_sum_char hq ha
    ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) fun _ => (1 : ℂ)
  simpa [h1] using h2

/-- Difference between `Chebyshev.psi x` and the principal-character sum `psiChar x 1`. -/
theorem psiChar_one_eq_psi_sub (x : ℝ) (q : ℕ) :
    (Chebyshev.psi x : ℂ) - psiChar x (1 : DirichletCharacter ℂ q) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, (Λ n : ℂ) := by
  rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add, psiChar]
  push_cast
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊)
    (fun n => n.Coprime q) (fun n => (Λ n : ℂ))
  have hchar : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n.Coprime q, (Λ n : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Coprime q
    · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
      rw [MulChar.one_apply hu, one_mul]
      simp [hn]
    · have hnu : ¬IsUnit (n : ZMod q) := fun hu => hn ((ZMod.isUnit_iff_coprime n q).mp hu)
      rw [MulChar.map_nonunit _ hnu, zero_mul]
      simp [hn]
  rw [hchar, ← hsplit]
  ring

/-- Quantitative bound on `‖Chebyshev.psi x - psiChar x 1‖` in terms of `log q` and `log x`. -/
private lemma minFac_prime_pow_eq {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p ^ k).minFac = p := by
  have hgt : 1 < p ^ k := one_lt_pow₀ hp.one_lt hk.ne'
  have hdvd : (p ^ k).minFac ∣ p ^ k := Nat.minFac_dvd _
  have hmf_pr : (p ^ k).minFac.Prime := Nat.minFac_prime hgt.ne'
  exact (hp.eq_one_or_self_of_dvd _ (hmf_pr.dvd_of_dvd_pow hdvd)).resolve_left hmf_pr.ne_one

/-- Quantitative bound on `‖Chebyshev.psi x - psiChar x 1‖` in terms of `log q` and `log x`. -/
theorem norm_psi_sub_psiChar_one_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    ‖(Chebyshev.psi x : ℂ) - psiChar x (1 : DirichletCharacter ℂ q)‖ ≤
      (Real.log q / Real.log 2) * Real.log x := by
  rw [psiChar_one_eq_psi_sub]
  have hreal : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, Λ n ≤
      (q.primeFactors.card : ℝ) * Real.log x := by
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
    have hcover : (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬n.Coprime q) ⊆
        (q.primeFactors.biUnion fun p =>
          (Finset.Icc 1 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ n.minFac = p)) ∪
        ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => Λ n = 0)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      by_cases hΛ : Λ n = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn.1, hΛ⟩)
      · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ?_)
        have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
        obtain ⟨p, k, hp_pr, hk, rfl⟩ := hpp
        have hp_nat : p.Prime := hp_pr.nat_prime
        have hmin : (p ^ k).minFac = p := minFac_prime_pow_eq hp_nat hk
        have hnotcop : ¬p.Coprime q := by
          intro hc
          exact hn.2 (hc.pow_left k)
        have hpdvd : p ∣ q := hp_nat.dvd_iff_not_coprime.mpr hnotcop
        have hpp_pow : IsPrimePow (p ^ k) := hp_pr.isPrimePow.pow hk.ne'
        refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp_nat, hpdvd, by omega⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn.1, hpp_pow, hmin⟩
    have hsum1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, Λ n ≤
        ∑ p ∈ q.primeFactors,
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n ∧ n.minFac = p, Λ n := by
      have hsub_le : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, Λ n ≤
          ∑ n ∈ (q.primeFactors.biUnion fun p =>
                (Finset.Icc 1 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ n.minFac = p)) ∪
              ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => Λ n = 0)), Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ =>
          ArithmeticFunction.vonMangoldt_nonneg
      have hunion_eq : ∑ n ∈ (q.primeFactors.biUnion fun p =>
                (Finset.Icc 1 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ n.minFac = p)) ∪
              ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => Λ n = 0)), Λ n =
          ∑ n ∈ (q.primeFactors.biUnion fun p =>
                (Finset.Icc 1 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ n.minFac = p)), Λ n := by
        symm
        refine Finset.sum_subset Finset.subset_union_left fun n hn hn_not => ?_
        rcases Finset.mem_union.mp hn with h1 | h2
        · exact absurd h1 hn_not
        · exact (Finset.mem_filter.mp h2).2
      have hdisj : (q.primeFactors : Set ℕ).PairwiseDisjoint fun p =>
          (Finset.Icc 1 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ n.minFac = p) := by
        intro p _ q' _ hpq
        refine Finset.disjoint_left.mpr fun n h1 h2 => ?_
        exact hpq ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
      rw [hunion_eq, Finset.sum_biUnion hdisj] at hsub_le
      exact hsub_le
    refine hsum1.trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp_pr.one_lt)
    let S_p := (Finset.Icc 1 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ n.minFac = p)
    have hbij : Finset.image (Nat.log p) S_p ⊆ Finset.Icc 1 (Nat.log p ⌊x⌋₊) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
      simp only [S_p, Finset.mem_filter, Finset.mem_Icc] at hn
      rcases hn.2.1 with ⟨q₀, m, hq₀, hm, rfl⟩
      have hq₀_pr : q₀.Prime := hq₀.nat_prime
      have hmf : (q₀ ^ m).minFac = q₀ := minFac_prime_pow_eq hq₀_pr hm
      rw [hn.2.2] at hmf
      subst hmf
      rw [Nat.log_pow hp_pr.one_lt]
      refine Finset.mem_Icc.mpr ⟨hm, ?_⟩
      have hn_pos : 0 < ⌊x⌋₊ := by
        have := hn.1.1
        have := hn.1.2
        omega
      exact (Nat.le_log_iff_pow_le hp_pr.one_lt hn_pos.ne').mpr hn.1.2
    have hle_sum : ∑ n ∈ S_p, Λ n ≤ ∑ _k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Real.log p := by
      calc ∑ n ∈ S_p, Λ n
          ≤ ∑ n ∈ S_p, Real.log p := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [S_p, Finset.mem_filter] at hn
            rcases hn.2.1 with ⟨q₀, m, hq₀, hm, rfl⟩
            have hq₀_pr : q₀.Prime := hq₀.nat_prime
            have hmf : (q₀ ^ m).minFac = q₀ := minFac_prime_pow_eq hq₀_pr hm
            rw [hn.2.2] at hmf
            subst hmf
            rw [ArithmeticFunction.vonMangoldt_apply_pow hm.ne',
              ArithmeticFunction.vonMangoldt_apply_prime hp_pr]
        _ = (S_p.card : ℝ) * Real.log p := by simp
        _ ≤ ((Finset.Icc 1 (Nat.log p ⌊x⌋₊)).card : ℝ) * Real.log p := by
            have hinj : Set.InjOn (Nat.log p) S_p := by
              intro n₁ hn₁ n₂ hn₂ heq
              simp only [S_p, Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
              rcases hn₁.2.1 with ⟨q₁, m₁, hq₁, hm₁, rfl⟩
              rcases hn₂.2.1 with ⟨q₂, m₂, hq₂, hm₂, rfl⟩
              have hm1_eq : (q₁ ^ m₁).minFac = q₁ := minFac_prime_pow_eq hq₁.nat_prime hm₁
              have hm2_eq : (q₂ ^ m₂).minFac = q₂ := minFac_prime_pow_eq hq₂.nat_prime hm₂
              rw [hn₁.2.2] at hm1_eq; rw [hn₂.2.2] at hm2_eq
              subst hm1_eq; subst hm2_eq
              rw [Nat.log_pow hp_pr.one_lt, Nat.log_pow hp_pr.one_lt] at heq
              rw [heq]
            have hcard_le : S_p.card ≤ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).card := by
              rw [← Finset.card_image_of_injOn hinj]
              exact Finset.card_le_card hbij
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) hlogp_pos.le
        _ = ∑ _k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Real.log p := by simp
    refine hle_sum.trans ?_
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hpow_le : (p : ℝ) ^ (Nat.log p ⌊x⌋₊) ≤ x := by
      have hfl1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
      have hnat : p ^ Nat.log p ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p (by omega)
      exact (by exact_mod_cast hnat : (p : ℝ) ^ (Nat.log p ⌊x⌋₊) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0)
    have hlog_le : (Nat.log p ⌊x⌋₊ : ℝ) * Real.log p ≤ Real.log x := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos (by exact_mod_cast hp_pr.pos) _) hpow_le
    exact hlog_le
  have hnorm_eq : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, (Λ n : ℂ)‖ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, Λ n := by
    have hsum_cast : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, (Λ n : ℂ)) =
        ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Coprime q, Λ n : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hsum_cast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hcards : (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
    have hpow : 2 ^ q.primeFactors.card ≤ q := by
      have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
        rw [← Finset.prod_const (2 : ℕ)]
        exact Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      exact h1.trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
    have hlog_pow : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).mpr hlog_pow
  rw [hnorm_eq]
  exact hreal.trans (mul_le_mul_of_nonneg_right hcards (Real.log_nonneg hx))

/-! ### Dirichlet's Theorem and PNT in Arithmetic Progressions -/

/-- **Dirichlet's theorem on primes in arithmetic progressions** (infinitude):
there are infinitely many primes `p ≡ a [MOD q]` whenever `q ≠ 0` and `Nat.Coprime a q`. -/
theorem dirichlet_primesInAP_infinite {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  Nat.infinite_setOfPred_prime_and_modEq hq ha

/-- **Dirichlet's theorem** (unboundedness): for every `n : ℕ`, there exists a prime
`p > n` with `p ≡ a [MOD q]`. -/
theorem dirichlet_primesInAP_forall_exists (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] :=
  Nat.forall_exists_prime_gt_and_modEq n hq ha

/-- Divergence of `π(x; q, a)` to `+∞` as `x → ∞` for `q ≠ 0` and `Nat.Coprime a q`. -/
theorem tendsto_piAP_atTop {q a : ℕ} (hq : q ≠ 0) (ha : a.Coprime q) :
    Tendsto (fun x : ℝ => piAP x q a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hNb⟩ := exists_nat_ge b
  obtain ⟨S, hS_sub, hS_card⟩ := (dirichlet_primesInAP_infinite hq ha).exists_subset_card_eq N
  let M : ℕ := max 1 (S.sup id)
  refine ⟨(M : ℝ), fun x hx => ?_⟩
  have hMx : M ≤ ⌊x⌋₊ := (Nat.le_floor_iff (le_trans (by positivity) hx)).mpr (by exact_mod_cast hx)
  have hS_in : S ⊆ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
    intro p hp
    have hmem := hS_sub hp
    simp only [Set.mem_ofPred_eq] at hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmem.1.pos, ?_⟩, hmem⟩
    exact (Finset.le_sup (f := id) hp).trans ((le_max_right 1 _).trans hMx)
  have hcard : N ≤ primeCountingAP x q a := by
    rw [primeCountingAP, ← hS_card]
    exact Finset.card_le_card hS_in
  rw [piAP]
  exact hNb.trans (by exact_mod_cast hcard)

/-- Prime Number Theorem in arithmetic progressions for `ψ(x; q, a)`:
`ψ(x; q, a) / x → 1 / φ(q)` as `x → ∞`. -/
theorem tendsto_psiAP_div {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    Tendsto (fun x : ℝ => psiAP x q a / x) atTop (𝓝 (q.totient : ℝ)⁻¹) := by
  simpa [psiAP_eq_sum_Icc0] using ArithmeticFunction.vonMangoldt.tendsto_sum_modEq_div_atTop ha

/-- Asymptotic equivalence `ψ(x; q, a) ~ x / φ(q)` as `x → ∞`. -/
theorem isEquivalent_psiAP {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    (fun x : ℝ => psiAP x q a) ~[atTop] (fun x : ℝ => x / (q.totient : ℝ)) := by
  have h := tendsto_psiAP_div ha
  have htot : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hm : Tendsto (fun x : ℝ => psiAP x q a / x * (q.totient : ℝ)) atTop (𝓝 1) := by
    simpa [htot] using h.mul_const (q.totient : ℝ)
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Pi.div_apply]
    field_simp [htot, hx.ne']
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx.ne' htot

/-- Prime Number Theorem in arithmetic progressions for `θ(x; q, a)`:
`θ(x; q, a) / x → 1 / φ(q)` as `x → ∞`. -/
theorem tendsto_thetaAP_div {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    Tendsto (fun x : ℝ => thetaAP x q a / x) atTop (𝓝 (q.totient : ℝ)⁻¹) := by
  simpa [thetaAP_eq_sum_Ioc] using Chebyshev.tendsto_sum_log_prime_modEq_div_atTop ha

/-- Asymptotic equivalence `θ(x; q, a) ~ x / φ(q)` as `x → ∞`. -/
theorem isEquivalent_thetaAP {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    (fun x : ℝ => thetaAP x q a) ~[atTop] (fun x : ℝ => x / (q.totient : ℝ)) := by
  have h := tendsto_thetaAP_div ha
  have htot : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hm : Tendsto (fun x : ℝ => thetaAP x q a / x * (q.totient : ℝ)) atTop (𝓝 1) := by
    simpa [htot] using h.mul_const (q.totient : ℝ)
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Pi.div_apply]
    field_simp [htot, hx.ne']
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx.ne' htot

/-- Prime Number Theorem in arithmetic progressions for `π(x; q, a)`:
`π(x; q, a) * log x / x → 1 / φ(q)` as `x → ∞`. -/
theorem tendsto_piAP_mul_log_div {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    Tendsto (fun x : ℝ => piAP x q a * Real.log x / x) atTop (𝓝 (q.totient : ℝ)⁻¹) := by
  simpa [piAP, primeCountingAP_eq_card_Ioc] using Nat.tendsto_card_prime_modEq_mul_log_div_atTop ha

/-- Asymptotic equivalence `π(x; q, a) ~ x / (φ(q) * log x)` as `x → ∞`. -/
theorem isEquivalent_piAP {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    (fun x : ℝ => piAP x q a) ~[atTop] (fun x : ℝ => x / ((q.totient : ℝ) * Real.log x)) := by
  simpa [piAP, primeCountingAP_eq_card_Ioc] using Nat.isEquivalent_card_prime_modEq ha

/-! ### Siegel–Walfisz Uniform Bounds and Perron Contour-Shift Reduction -/

/-- Logarithmic integral `Li(x) = ∫_2^x dt / log t`. -/
noncomputable def logIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

private lemma intervalIntegrable_inv_log (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 x := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hx]
  exact (continuousOn_log_Icc zero_lt_two).inv₀ fun t ht =>
    (Real.log_pos (lt_of_lt_of_le one_lt_two ht.1)).ne'

private lemma intervalIntegrable_inv_log_sq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t ^ 2)⁻¹) volume a b := by
  simpa [one_div] using Chebyshev.intervalIntegrable_one_div_log_sq ha (ha.trans_le hab)

/-- Identity `Li(x) = x / log x - 2 / log 2 + ∫_2^x dt / (log t)²` for `2 ≤ x`. -/
theorem logIntegral_eq_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x = x / Real.log x - 2 / Real.log 2 +
      ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hd : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => u / Real.log u) ((Real.log t)⁻¹ - 1 / Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1 < t := lt_of_lt_of_le one_lt_two ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    convert (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hlogt using 1
    field_simp [ht0, hlogt]
  have hint : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹ - 1 / Real.log t ^ 2) volume 2 x :=
    (intervalIntegrable_inv_log x hx).sub
      (Chebyshev.intervalIntegrable_one_div_log_sq one_lt_two (by linarith))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_inv_log x hx)
    (Chebyshev.intervalIntegrable_one_div_log_sq one_lt_two (by linarith))] at hftc
  unfold logIntegral
  linarith

/-- Uniform Siegel–Walfisz bound predicate for `ψ(x; q, a)`:
for every `A ≥ 0`, there exist constants `C > 0`, `c > 0` such that for all `x ≥ 2`,
`1 ≤ q ≤ (log x)^A`, and `Nat.Coprime a q`,
`|ψ(x; q, a) - x / φ(q)| ≤ C * x * exp(-c * √(log x))`. -/
def SiegelWalfiszBound : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C > 0, ∃ c > 0, ∀ (x : ℝ) (q a : ℕ),
    2 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → a.Coprime q →
    |psiAP x q a - x / q.totient| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

private lemma sqrt_le_mul_exp_neg {x : ℝ} (hx : 2 ≤ x) :
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
      have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log x) := by
        refine Real.le_sqrt_of_sq_le ?_
        linarith
      linarith
    calc (1 / 4 : ℝ) * Real.sqrt (Real.log x)
        ≤ (Real.sqrt (Real.log x) / 2) * Real.sqrt (Real.log x) :=
          mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
      _ = Real.sqrt (Real.log x) ^ 2 / 2 := by ring
      _ = Real.log x / 2 := by rw [Real.sq_sqrt (by linarith)]
  have hexp : Real.exp ((1 / 4 : ℝ) * Real.sqrt (Real.log x)) ≤ Real.sqrt x := by
    conv_rhs => rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have heq : x * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x)) =
      x / Real.exp ((1 / 4 : ℝ) * Real.sqrt (Real.log x)) := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  rw [heq, le_div_iff₀ (Real.exp_pos _)]
  calc Real.sqrt x * Real.exp ((1 / 4 : ℝ) * Real.sqrt (Real.log x))
      ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
    _ = x := Real.mul_self_sqrt hx0.le

/-- Deduction of the uniform Siegel–Walfisz bound for `θ(x; q, a)` from `SiegelWalfiszBound`. -/
theorem siegelWalfisz_thetaAP (hSW : SiegelWalfiszBound) :
    ∀ A : ℝ, 0 ≤ A → ∃ C > 0, ∃ c > 0, ∀ (x : ℝ) (q a : ℕ),
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → a.Coprime q →
      |thetaAP x q a - x / q.totient| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  intro A hA
  obtain ⟨C, hC, c, hc, hbound⟩ := hSW A hA
  let C' : ℝ := C + (Real.log 4 + 4) * 3
  let c' : ℝ := min c (1 / 4)
  refine ⟨C', by positivity, c', lt_min hc (by norm_num), fun x q a hx hq1 hqlog ha => ?_⟩
  have h1 := hbound x q a hx hq1 hqlog ha
  have h2 := abs_psiAP_sub_thetaAP_le x q a
  have h3 := sqrt_le_mul_exp_neg hx
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
  calc |thetaAP x q a - x / q.totient|
      ≤ |thetaAP x q a - psiAP x q a| + |psiAP x q a - x / q.totient| :=
        abs_sub_le _ _ _
    _ = |psiAP x q a - thetaAP x q a| + |psiAP x q a - x / q.totient| := by
        rw [abs_sub_comm]
    _ ≤ (Real.log 4 + 4) * 3 * (x * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x))) +
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        refine add_le_add (h2.trans ?_) h1
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (Real.log 4 + 4) * 3 * (x * Real.exp (-c' * Real.sqrt (Real.log x))) +
          C * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
        gcongr
    _ = C' * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
        dsimp [C']
        ring

/-- Deduction of the uniform Siegel–Walfisz bound for `π(x; q, a) - Li(x) / φ(q)`
from `SiegelWalfiszBound`. -/
theorem siegelWalfisz_piAP_sub_logIntegral (hSW : SiegelWalfiszBound) :
    ∀ A : ℝ, 0 ≤ A → ∃ C > 0, ∃ c > 0, ∀ (x : ℝ) (q a : ℕ),
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → a.Coprime q →
      |piAP x q a - logIntegral x / q.totient| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  intro A hA
  obtain ⟨Cθ, hCθ, cθ, hcθ, hθ⟩ := siegelWalfisz_thetaAP hSW (A + 1) (by linarith)
  let c' : ℝ := min (cθ / Real.sqrt 2) (1 / 4)
  have hc' : 0 < c' := lt_min (div_pos hcθ (Real.sqrt_pos.mpr zero_lt_two)) (by norm_num)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let X₀ : ℝ := max 4 (Real.exp ((2 : ℝ) ^ (A + 1)))
  have hX₀_ge4 : 4 ≤ X₀ := le_max_left _ _
  have hX₀_pos : 0 < X₀ := lt_of_lt_of_le (by norm_num) hX₀_ge4
  let C_small : ℝ := (1 + 1 / Real.log 2) * Real.exp (c' * Real.sqrt (Real.log X₀))
  let C_large : ℝ :=
    Cθ / Real.log 2 + 2 / Real.log 2 + (Real.log 4 + 1) / Real.log 2 ^ 2 + Cθ / Real.log 2 ^ 2
  let C' : ℝ := max C_small C_large
  refine ⟨C', lt_of_lt_of_le (by positivity) (le_max_left _ _), c', hc',
    fun x q a hx hq1 hqlog ha => ?_⟩
  have htot_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have htot1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le one_lt_two hx)
  have hlogx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
  rcases le_or_gt x X₀ with hx_le | hx_gt
  · have hpi_le : piAP x q a ≤ x := by
      unfold piAP primeCountingAP
      have hcard : ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card ≤ ⌊x⌋₊ := by
        calc ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card
            ≤ (Finset.Icc 1 ⌊x⌋₊).card := Finset.card_filter_le _ _
          _ = ⌊x⌋₊ := by simp
      exact (by exact_mod_cast hcard : (primeCountingAP x q a : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le (by linarith))
    have hli_nn : 0 ≤ logIntegral x :=
      intervalIntegral.integral_nonneg hx fun t ht =>
        inv_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
    have hli_le : logIntegral x ≤ x / Real.log 2 := by
      unfold logIntegral
      have h1 : ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ ≤ ∫ _t in (2 : ℝ)..x, (Real.log 2)⁻¹ := by
        refine intervalIntegral.integral_mono_on hx (intervalIntegrable_inv_log x hx)
          (by simp) fun t ht => inv_anti₀ hlog2_pos (Real.log_le_log zero_lt_two ht.1)
      have h2 : ∫ _t in (2 : ℝ)..x, (Real.log 2)⁻¹ = (x - 2) / Real.log 2 := by
        simp [div_eq_mul_inv]
      refine (h1.trans_eq h2).trans ?_
      gcongr
      linarith
    have hdiv_le : logIntegral x / q.totient ≤ x / Real.log 2 :=
      (div_le_self hli_nn htot1).trans hli_le
    have habs : |piAP x q a - logIntegral x / q.totient| ≤ (1 + 1 / Real.log 2) * x := by
      have hsum_eq : (1 + 1 / Real.log 2) * x = x + x / Real.log 2 := by ring
      rw [hsum_eq, abs_le]
      have hpi_nn : 0 ≤ piAP x q a := piAP_nonneg x q a
      have hdiv_nn : 0 ≤ logIntegral x / q.totient := div_nonneg hli_nn htot_pos.le
      constructor <;> linarith
    have hsqrt_le : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log X₀) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hx_le)
    have hexp_le : Real.exp (c' * Real.sqrt (Real.log x)) ≤
        Real.exp (c' * Real.sqrt (Real.log X₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt_le hc'.le)
    have hexp1 : Real.exp (c' * Real.sqrt (Real.log x)) *
        Real.exp (-c' * Real.sqrt (Real.log x)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hC_small_le : (1 + 1 / Real.log 2) * Real.exp (c' * Real.sqrt (Real.log x)) ≤ C_small :=
      mul_le_mul_of_nonneg_left hexp_le (by positivity)
    calc |piAP x q a - logIntegral x / q.totient|
        ≤ (1 + 1 / Real.log 2) * x := habs
      _ = (1 + 1 / Real.log 2) * x *
            (Real.exp (c' * Real.sqrt (Real.log x)) * Real.exp (-c' * Real.sqrt (Real.log x))) := by
          rw [hexp1, mul_one]
      _ = ((1 + 1 / Real.log 2) * Real.exp (c' * Real.sqrt (Real.log x))) *
            x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
      _ ≤ C_small * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
          gcongr
      _ ≤ C' * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
          gcongr
          exact le_max_left _ _
  · have hx4 : 4 ≤ x := hX₀_ge4.trans hx_gt.le
    have h2pow_lt : (2 : ℝ) ^ (A + 1) < Real.log x := by
      have hexp_lt : Real.exp ((2 : ℝ) ^ (A + 1)) < x := (le_max_right 4 _).trans_lt hx_gt
      calc (2 : ℝ) ^ (A + 1) = Real.log (Real.exp ((2 : ℝ) ^ (A + 1))) := by simp
        _ < Real.log x := Real.log_lt_log (Real.exp_pos _) hexp_lt
    have hsqrt2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have hsqrtx : Real.sqrt x ≤ x := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
    have h_id : piAP x q a - logIntegral x / q.totient =
        (thetaAP x q a - x / q.totient) / Real.log x + (2 / Real.log 2) / q.totient +
          ∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2) := by
      rw [piAP_eq_thetaAP_div_log_add_integral hx q a, logIntegral_eq_div_log_add_integral hx]
      have h_int_split :
          ∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2) =
            (∫ t in (2 : ℝ)..x, thetaAP t q a / (t * Real.log t ^ 2)) -
              ∫ t in (2 : ℝ)..x, (t / q.totient) / (t * Real.log t ^ 2) := by
        have h1 := intervalIntegrable_thetaAP_div_mul_log_sq hx q a
        have h2 : IntervalIntegrable (fun t : ℝ => (t / q.totient) / (t * Real.log t ^ 2))
            volume 2 x := by
          refine (Chebyshev.intervalIntegrable_one_div_log_sq one_lt_two (by linarith)
            |>.const_mul (q.totient : ℝ)⁻¹).congr_uIoo fun t ht => ?_
          rw [Set.uIoo_of_le hx] at ht
          have ht0 : t ≠ 0 := (zero_lt_two.trans ht.1).ne'
          field_simp [ht0, htot_pos.ne']
        rw [← intervalIntegral.integral_sub h1 h2]
        refine intervalIntegral.integral_congr fun t _ => by ring
      have h_int_rhs :
          ∫ t in (2 : ℝ)..x, (t / q.totient) / (t * Real.log t ^ 2) =
            (q.totient : ℝ)⁻¹ * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
        rw [← intervalIntegral.integral_const_mul (μ := volume)]
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hx] at ht
        have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_two ht.1).ne'
        field_simp [ht0, htot_pos.ne']
      rw [h_int_split, h_int_rhs]
      ring
    have hint_diff : IntervalIntegrable
        (fun t : ℝ => (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)) volume 2 x := by
      have h1 := intervalIntegrable_thetaAP_div_mul_log_sq hx q a
      have h2 : IntervalIntegrable (fun t : ℝ => (t / q.totient) / (t * Real.log t ^ 2))
          volume 2 x := by
        refine (Chebyshev.intervalIntegrable_one_div_log_sq one_lt_two (by linarith)
          |>.const_mul (q.totient : ℝ)⁻¹).congr_uIoo fun t ht => ?_
        rw [Set.uIoo_of_le hx] at ht
        have ht0 : t ≠ 0 := (zero_lt_two.trans ht.1).ne'
        field_simp [ht0, htot_pos.ne']
      exact (h1.sub h2).congr_uIoo fun t _ => by ring
    have hmem_uIcc : Real.sqrt x ∈ Set.uIcc (2 : ℝ) x := Set.mem_uIcc.mpr (Or.inl ⟨hsqrt2, hsqrtx⟩)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint_diff.mono_set (Set.uIcc_subset_uIcc_left hmem_uIcc))
      (hint_diff.mono_set (Set.uIcc_subset_uIcc_right hmem_uIcc))
    have hleft_int : |∫ t in (2 : ℝ)..Real.sqrt x,
        (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)| ≤
        ((Real.log 4 + 1) / Real.log 2 ^ 2) * Real.sqrt x := by
      have hnorm := intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (f := fun t : ℝ => (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)) hsqrt2
      have hint_sub : IntervalIntegrable
          (fun t : ℝ => (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2))
          volume 2 (Real.sqrt x) :=
        hint_diff.mono_set (Set.uIcc_subset_uIcc_left hmem_uIcc)
      have hmono : ∫ t in (2 : ℝ)..Real.sqrt x,
          ‖(thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)‖ ≤
          ∫ _t in (2 : ℝ)..Real.sqrt x, (Real.log 4 + 1) / Real.log 2 ^ 2 := by
        refine intervalIntegral.integral_mono_on hsqrt2 hint_sub.norm (by simp) fun t ht => ?_
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ht.1
        have hlogt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht.1
        have hnum : |thetaAP t q a - t / q.totient| ≤ (Real.log 4 + 1) * t := by
          rw [abs_le]
          have hth : thetaAP t q a ≤ Real.log 4 * t :=
            (thetaAP_le_theta t q a).trans (Chebyshev.theta_le_log4_mul_x ht0.le)
          have hdiv : t / q.totient ≤ t := div_le_self ht0.le htot1
          constructor <;> linarith [thetaAP_nonneg t q a, ht0.le, div_nonneg ht0.le htot_pos.le]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos (by linarith)))]
        calc |thetaAP t q a - t / q.totient| / (t * Real.log t ^ 2)
            ≤ ((Real.log 4 + 1) * t) / (t * Real.log 2 ^ 2) := by
              gcongr
          _ = (Real.log 4 + 1) / Real.log 2 ^ 2 := by field_simp [ht0.ne']
      refine (hnorm.trans hmono).trans ?_
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hnn : 0 ≤ (Real.log 4 + 1) / Real.log 2 ^ 2 := by positivity
      nlinarith
    have hright_int : |∫ t in Real.sqrt x..x,
        (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)| ≤
        (Cθ / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      have hnorm := intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (f := fun t : ℝ => (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)) hsqrtx
      have hint_sub : IntervalIntegrable
          (fun t : ℝ => (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2))
          volume (Real.sqrt x) x :=
        hint_diff.mono_set (Set.uIcc_subset_uIcc_right hmem_uIcc)
      have hmono : ∫ t in Real.sqrt x..x,
          ‖(thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)‖ ≤
          ∫ _t in Real.sqrt x..x,
            (Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)) := by
        refine intervalIntegral.integral_mono_on hsqrtx hint_sub.norm (by simp) fun t ht => ?_
        have ht2 : 2 ≤ t := hsqrt2.trans ht.1
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ht2
        have hlogt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log zero_lt_two ht2
        have hlogt_pos : 0 < Real.log t := lt_of_lt_of_le hlog2_pos hlogt_ge
        have hlogt_sqrt : Real.log x / 2 ≤ Real.log t := by
          have := Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) ht.1
          rw [Real.log_sqrt (by linarith)] at this
          linarith
        have h2pow_A : (2 : ℝ) ^ A ≤ Real.log t := by
          have h1 : (2 : ℝ) ^ (A + 1) = 2 * (2 : ℝ) ^ A := by
            rw [Real.rpow_add zero_lt_two, Real.rpow_one]
            ring
          linarith
        have hq_le_t : (q : ℝ) ≤ Real.log t ^ (A + 1) := by
          calc (q : ℝ) ≤ Real.log x ^ A := hqlog
            _ ≤ (2 * Real.log t) ^ A :=
                Real.rpow_le_rpow hlogx_pos.le (by linarith) hA
            _ = (2 : ℝ) ^ A * Real.log t ^ A :=
                Real.mul_rpow (by norm_num) hlogt_pos.le
            _ ≤ Real.log t * Real.log t ^ A := by gcongr
            _ = Real.log t ^ (A + 1) := by
                rw [mul_comm, ← Real.rpow_add_one hlogt_pos.ne']
        have hθ_t := hθ t q a ht2 hq1 hq_le_t ha
        have hsqrt_logt : Real.sqrt (Real.log x) / Real.sqrt 2 ≤ Real.sqrt (Real.log t) := by
          rw [← Real.sqrt_div (by linarith)]
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
        calc |thetaAP t q a - t / q.totient| / (t * Real.log t ^ 2)
            ≤ (Cθ * t * Real.exp (-cθ * Real.sqrt (Real.log t))) / (t * Real.log 2 ^ 2) := by
              gcongr
          _ = (Cθ / Real.log 2 ^ 2) * Real.exp (-cθ * Real.sqrt (Real.log t)) := by
              field_simp [ht0.ne']
          _ ≤ (Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)) := by
              gcongr
      refine (hnorm.trans hmono).trans ?_
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hnn : 0 ≤ (Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)) := by
        positivity
      have hlen : x - Real.sqrt x ≤ x := by linarith [Real.sqrt_nonneg x]
      calc (x - Real.sqrt x) * ((Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x)))
          ≤ x * ((Cθ / Real.log 2 ^ 2) * Real.exp (-c' * Real.sqrt (Real.log x))) := by
            gcongr
        _ = (Cθ / Real.log 2 ^ 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have hq_xA1 : (q : ℝ) ≤ Real.log x ^ (A + 1) := by
      have h1lt : 1 ≤ Real.log x := by
        have h1A : (1 : ℝ) ≤ A + 1 := by linarith
        have : (2 : ℝ) ≤ (2 : ℝ) ^ (A + 1) := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1A
        linarith
      exact hqlog.trans (Real.rpow_le_rpow_of_exponent_le h1lt (by linarith))
    have hθ_x := hθ x q a hx hq1 hq_xA1 ha
    have hexp_x1 : Real.exp (-cθ * Real.sqrt (Real.log x)) ≤
        Real.exp (-c' * Real.sqrt (Real.log x)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : c' ≤ cθ / Real.sqrt 2 := min_le_left _ _
      have h2 : cθ / Real.sqrt 2 ≤ cθ := div_le_self hcθ.le (Real.one_le_sqrt.mpr (by norm_num))
      nlinarith [Real.sqrt_nonneg (Real.log x)]
    have hexp_x2 : Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x)) ≤
        Real.exp (-c' * Real.sqrt (Real.log x)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [min_le_right (cθ / Real.sqrt 2) (1 / 4 : ℝ), Real.sqrt_nonneg (Real.log x)]
    have hsqrt_exp := (sqrt_le_mul_exp_neg hx).trans
      (mul_le_mul_of_nonneg_left hexp_x2 (by linarith))
    have h1_exp : (1 : ℝ) ≤ x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      have h21 : (1 : ℝ) ≤ Real.sqrt x := by linarith
      exact h21.trans hsqrt_exp
    have hterm1 : |(thetaAP x q a - x / q.totient) / Real.log x| ≤
        (Cθ / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      rw [abs_div, abs_of_pos hlogx_pos]
      calc |thetaAP x q a - x / q.totient| / Real.log x
          ≤ (Cθ * x * Real.exp (-cθ * Real.sqrt (Real.log x))) / Real.log 2 := by gcongr
        _ ≤ (Cθ * x * Real.exp (-c' * Real.sqrt (Real.log x))) / Real.log 2 := by gcongr
        _ = (Cθ / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have hterm2 : |(2 / Real.log 2) / (q.totient : ℝ)| ≤
        (2 / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      rw [abs_of_nonneg (by positivity)]
      calc (2 / Real.log 2) / (q.totient : ℝ)
          ≤ 2 / Real.log 2 := div_le_self (by positivity) htot1
        _ ≤ (2 / Real.log 2) * (x * Real.exp (-c' * Real.sqrt (Real.log x))) :=
            le_mul_of_one_le_right (by positivity) h1_exp
        _ = (2 / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
    have hterm3 : |∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2)| ≤
        (((Real.log 4 + 1) / Real.log 2 ^ 2) + Cθ / Real.log 2 ^ 2) *
          x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      rw [← hsplit]
      have htri := abs_add_le
        (∫ t in (2 : ℝ)..Real.sqrt x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2))
        (∫ t in Real.sqrt x..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2))
      have hL := hleft_int.trans (mul_le_mul_of_nonneg_left hsqrt_exp (by positivity))
      linarith
    rw [h_id]
    have htri1 := abs_add_le
      ((thetaAP x q a - x / q.totient) / Real.log x + (2 / Real.log 2) / q.totient)
      (∫ t in (2 : ℝ)..x, (thetaAP t q a - t / q.totient) / (t * Real.log t ^ 2))
    have htri2 := abs_add_le ((thetaAP x q a - x / q.totient) / Real.log x)
      ((2 / Real.log 2) / q.totient)
    have hC_le : C_large ≤ C' := le_max_right _ _
    have hsum : C_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) ≤
        C' * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      gcongr
    have hfinal : C_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) =
        (Cθ / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) +
        (2 / Real.log 2) * x * Real.exp (-c' * Real.sqrt (Real.log x)) +
        (((Real.log 4 + 1) / Real.log 2 ^ 2) + Cθ / Real.log 2 ^ 2) *
          x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
      dsimp [C_large]
      ring
    linarith

/-- Unconditional character reduction for `ψ(x; q, a) - x / φ(q)`:
reduces the discrepancy in arithmetic progressions to `|ψ(x) - x|`, `(log q / log 2) * log x`,
and the nontrivial Dirichlet character sums `‖psiChar x χ‖`. -/
theorem abs_psiAP_sub_div_totient_le_sum_chars {x : ℝ} (hx : 1 ≤ x) {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) :
    |psiAP x q a - x / q.totient| ≤
      (q.totient : ℝ)⁻¹ *
        (|Chebyshev.psi x - x| + (Real.log q / Real.log 2) * Real.log x +
          ∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)),
            ‖psiChar x χ‖) := by
  have hq0 : q ≠ 0 := by omega
  have htot_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have ha_unit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have h1a : star ((1 : DirichletCharacter ℂ q) a) = 1 := by
    rw [MulChar.one_apply ha_unit, star_one]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ => star (χ a) * psiChar x χ) (Finset.mem_univ (1 : DirichletCharacter ℂ q))
  have herase : Finset.univ.erase (1 : DirichletCharacter ℂ q) =
      ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)) := by
    ext χ; simp
  rw [herase] at hsplit
  have hdiff : ((psiAP x q a - x / q.totient : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ((psiChar x (1 : DirichletCharacter ℂ q) - x) +
        ∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)),
          star (χ a) * psiChar x χ) := by
    push_cast
    rw [psiAP_eq_inv_totient_mul_sum_psiChar hq0 ha, ← hsplit, h1a, one_mul]
    have htot_ne : (q.totient : ℂ) ≠ 0 := by exact_mod_cast htot_pos.ne'
    field_simp [htot_ne]
    ring
  have hnorm_eq : |psiAP x q a - x / q.totient| =
      ‖((psiAP x q a - x / q.totient : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h1_bound : ‖psiChar x (1 : DirichletCharacter ℂ q) - x‖ ≤
      |Chebyshev.psi x - x| + (Real.log q / Real.log 2) * Real.log x := by
    have htri := norm_add_le (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ))
      ((Chebyshev.psi x : ℂ) - x)
    have hid : psiChar x (1 : DirichletCharacter ℂ q) - x =
        (psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)) +
          ((Chebyshev.psi x : ℂ) - x) := by ring
    have hA : ‖psiChar x (1 : DirichletCharacter ℂ q) - (Chebyshev.psi x : ℂ)‖ ≤
        (Real.log q / Real.log 2) * Real.log x := by
      rw [norm_sub_rev]
      exact norm_psi_sub_psiChar_one_le hx hq
    have hB : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ = |Chebyshev.psi x - x| := by
      have : (Chebyshev.psi x : ℂ) - (x : ℂ) = ((Chebyshev.psi x - x : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [← hid] at htri
    linarith
  have hsum_bound : ‖∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)),
        star (χ a) * psiChar x χ‖ ≤
      ∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)), ‖psiChar x χ‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one (a : ZMod q))
  have hnorm_tot : ‖((q.totient : ℂ)⁻¹)‖ = (q.totient : ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast, Complex.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [hnorm_eq, hdiff, norm_mul, hnorm_tot]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr htot_pos.le)
  exact (norm_add_le _ _).trans (add_le_add h1_bound hsum_bound)

/-- Conditional Siegel–Walfisz deduction: uniform exponential-in-`√(log x)` bounds on
`|ψ(x) - x|` and all nontrivial character sums `‖psiChar x χ‖` for `q ≤ (log x)^A` imply
`SiegelWalfiszBound`. -/
theorem siegelWalfisz_of_character_bounds
    (h1 : ∃ C₀ > 0, ∃ c₀ > 0, ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C₀ * x * Real.exp (-c₀ * Real.sqrt (Real.log x)))
    (hchars : ∀ A : ℝ, 0 ≤ A → ∃ C₁ > 0, ∃ c₁ > 0, ∀ (x : ℝ) (q : ℕ)
      (χ : DirichletCharacter ℂ q), 2 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → χ ≠ 1 →
      ‖psiChar x χ‖ ≤ C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x))) :
    SiegelWalfiszBound := by
  intro A hA
  obtain ⟨C₀, hC₀, c₀, hc₀, hpsi_b⟩ := h1
  obtain ⟨C₁, hC₁, c₁, hc₁, hchar_b⟩ := hchars A hA
  let c : ℝ := min (min c₀ c₁) (1 / 4)
  have hc : 0 < c := lt_min (lt_min hc₀ hc₁) (by norm_num)
  let C : ℝ := C₀ + 16 * A / Real.log 2 + C₁
  refine ⟨C, by positivity, c, hc, fun x q a hx hq1 hqlog ha => ?_⟩
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have htot_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have htot1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have : NeZero q := ⟨by omega⟩
  have hcard : ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)).card ≤
      q.totient := by
    have h1 := Finset.card_le_univ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q))
    rw [Fintype.card_eq_nat_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity] at h1
    exact h1
  have hc0_le : Real.exp (-c₀ * Real.sqrt (Real.log x)) ≤
      Real.exp (-c * Real.sqrt (Real.log x)) := by
    refine Real.exp_le_exp.mpr ?_
    have hc_le : c ≤ c₀ := (min_le_left (min c₀ c₁) (1 / 4 : ℝ)).trans (min_le_left c₀ c₁)
    nlinarith [hc_le, Real.sqrt_nonneg (Real.log x)]
  have hc1_le : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤
      Real.exp (-c * Real.sqrt (Real.log x)) := by
    refine Real.exp_le_exp.mpr ?_
    have hc_le : c ≤ c₁ := (min_le_left (min c₀ c₁) (1 / 4 : ℝ)).trans (min_le_right c₀ c₁)
    nlinarith [hc_le, Real.sqrt_nonneg (Real.log x)]
  have hq_term : (Real.log q / Real.log 2) * Real.log x ≤
      (16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    by_cases hqeq : q = 1
    · subst hqeq
      simp only [Nat.cast_one, Real.log_one, zero_div, zero_mul]
      positivity
    · have hq2 : 2 ≤ q := by omega
      have hq_real2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      have hlogq_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
      have hlogx_gt1 : 1 < Real.log x := by
        by_contra hle
        push Not at hle
        have hlogx_pos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le one_lt_two hx)
        have : Real.log x ^ A ≤ 1 := Real.rpow_le_one hlogx_pos.le hle hA
        linarith
      have hlog_q_le : Real.log q ≤ A * Real.log (Real.log x) := by
        have h1 : Real.log q ≤ Real.log (Real.log x ^ A) := Real.log_le_log (by positivity) hqlog
        rwa [Real.log_rpow (zero_lt_one.trans hlogx_gt1)] at h1
      have hlog_log_le : Real.log (Real.log x) ≤ Real.log x :=
        (Real.log_le_sub_one_of_pos (zero_lt_one.trans hlogx_gt1)).trans (by linarith)
      have hlog_sq : Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
        have hx0 : 0 ≤ x := by linarith
        have h1 : Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
          Real.log_le_rpow_div hx0 (by norm_num)
        have h2 : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by linarith
        have hsq : Real.log x ^ 2 ≤ (4 * x ^ (1 / 4 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith)) h2 2
        have hpow : (4 * x ^ (1 / 4 : ℝ)) ^ 2 = 16 * Real.sqrt x := by
          calc (4 * x ^ (1 / 4 : ℝ)) ^ 2 = 16 * (x ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
                norm_cast; ring
            _ = 16 * Real.sqrt x := by
                rw [← Real.rpow_mul hx0, Real.sqrt_eq_rpow]; norm_num
        linarith
      have hsqrt_exp : Real.sqrt x ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        have hcexp : Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log x)) ≤
            Real.exp (-c * Real.sqrt (Real.log x)) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith [min_le_right (min c₀ c₁) (1 / 4 : ℝ), Real.sqrt_nonneg (Real.log x)]
        exact (sqrt_le_mul_exp_neg hx).trans (mul_le_mul_of_nonneg_left hcexp (by linarith))
      calc (Real.log q / Real.log 2) * Real.log x
          ≤ (A * Real.log x / Real.log 2) * Real.log x := by
            have : Real.log q ≤ A * Real.log x :=
              hlog_q_le.trans (mul_le_mul_of_nonneg_left hlog_log_le hA)
            gcongr
        _ = (A / Real.log 2) * Real.log x ^ 2 := by ring
        _ ≤ (A / Real.log 2) * (16 * Real.sqrt x) := by gcongr
        _ ≤ (A / Real.log 2) * (16 * (x * Real.exp (-c * Real.sqrt (Real.log x)))) := by gcongr
        _ = (16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
  have hsum_char_le :
      ∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)), ‖psiChar x χ‖ ≤
        (q.totient : ℝ) * (C₁ * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
    calc ∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)), ‖psiChar x χ‖
        ≤ ∑ _χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)),
            (C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x))) := by
          refine Finset.sum_le_sum fun χ hχ => hchar_b x q χ hx hq1 hqlog ?_
          simpa using hχ
      _ ≤ ∑ _χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)),
            (C₁ * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
          refine Finset.sum_le_sum fun _ _ => ?_
          gcongr
      _ = (({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)).card : ℝ) *
            (C₁ * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
          simp
      _ ≤ (q.totient : ℝ) * (C₁ * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
          gcongr
  have h1_full : |Chebyshev.psi x - x| + (Real.log q / Real.log 2) * Real.log x ≤
      (C₀ + 16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    have hA : |Chebyshev.psi x - x| ≤ C₀ * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      (hpsi_b x hx).trans (by gcongr)
    linarith
  have hred := abs_psiAP_sub_div_totient_le_sum_chars (x := x) (by linarith) hq1 ha
  refine hred.trans ?_
  calc (q.totient : ℝ)⁻¹ * (|Chebyshev.psi x - x| + (Real.log q / Real.log 2) * Real.log x +
        ∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)), ‖psiChar x χ‖)
      ≤ (q.totient : ℝ)⁻¹ * ((C₀ + 16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) +
          (q.totient : ℝ) * (C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)))) := by gcongr
    _ = (q.totient : ℝ)⁻¹ * ((C₀ + 16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x))) +
          C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        rw [mul_add, inv_mul_cancel_left₀ htot_pos.ne']
    _ ≤ (C₀ + 16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) +
          C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        have hnn : 0 ≤ (C₀ + 16 * A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
          positivity
        have hinv1 : (q.totient : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ htot1
        nlinarith
    _ = C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        dsimp [C]
        ring

private lemma summable_rpow_tail_inv {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => if n < 2 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))) := by
  refine Summable.of_nonneg_of_le
    (fun n => by split_ifs <;> positivity) (fun n => ?_)
    (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + α))
  split_ifs with hn
  · positivity
  · rw [Real.rpow_neg (Nat.cast_nonneg n)]

private lemma tsum_rpow_tail_le {α : ℝ} (hα : 0 < α) :
    ∑' n : ℕ, (if n < 2 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))) ≤ 1 / α := by
  let g : ℕ → ℝ := fun n => if n < 2 then 0 else (n : ℝ) ^ (-(1 + α))
  have hg_sum := summable_rpow_tail_inv hα
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 2), g n ≤ 1 / α := by
    intro N
    have hsum_shift : ∑ n ∈ Finset.range (N + 2), g n =
        ∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ) ^ (-(1 + α)) := by
      induction N with
      | zero =>
          simp [g, Finset.sum_range_succ]
      | succ m ih =>
          rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
          have hge : ¬(m + 2 < 2) := by omega
          simp [g]
    have hint_part : ∀ m : ℕ,
        ∑ k ∈ Finset.range m, ((k + 2 : ℕ) : ℝ) ^ (-(1 + α)) ≤
          ∫ t in (1 : ℝ)..((m + 1 : ℕ) : ℝ), t ^ (-(1 + α)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
          have h1m : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
          have hmm1 : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : m + 1 ≤ m + 2)
          have hint1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + α))) volume 1 (m + 1 : ℕ) :=
            intervalIntegral.intervalIntegrable_rpow (Or.inr fun h0 => by
              rw [Set.uIcc_of_le h1m] at h0; linarith [h0.1])
          have hint2 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + α))) volume (m + 1 : ℕ) (m + 2 : ℕ) :=
            intervalIntegral.intervalIntegrable_rpow (Or.inr fun h0 => by
              rw [Set.uIcc_of_le hmm1] at h0
              have hm0 : (0 : ℝ) < m + 1 := by positivity
              linarith [h0.1])
          have hstep : ((m + 2 : ℕ) : ℝ) ^ (-(1 + α)) ≤
              ∫ t in ((m + 1 : ℕ) : ℝ)..((m + 2 : ℕ) : ℝ), t ^ (-(1 + α)) := by
            have hmono : ∫ _t in ((m + 1 : ℕ) : ℝ)..((m + 2 : ℕ) : ℝ),
                  ((m + 2 : ℕ) : ℝ) ^ (-(1 + α)) ≤
                ∫ t in ((m + 1 : ℕ) : ℝ)..((m + 2 : ℕ) : ℝ), t ^ (-(1 + α)) := by
              refine intervalIntegral.integral_mono_on hmm1 (by simp) hint2 fun t ht => ?_
              have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
              exact Real.rpow_le_rpow_of_nonpos ht0 ht.2 (by linarith)
            refine le_trans ?_ hmono
            rw [intervalIntegral.integral_const, smul_eq_mul,
              show ((m + 2 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) = 1 by push_cast; ring, one_mul]
          rw [Finset.sum_range_succ]
          have hadj := (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
          have h12 : ((m + 1 + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := rfl
          rw [h12, hadj]
          linarith
    have hint_eval : ∫ t in (1 : ℝ)..((N + 1 : ℕ) : ℝ), t ^ (-(1 + α)) ≤ 1 / α := by
      have h1N : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1)
      have hr : -(1 + α) ≠ -1 := by linarith
      rw [integral_rpow (Or.inr ⟨hr, fun h0 => by rw [Set.uIcc_of_le h1N] at h0; linarith [h0.1]⟩)]
      have hexp : -(1 + α) + 1 = -α := by ring
      rw [hexp, Real.one_rpow]
      have hnn : 0 ≤ (((N + 1 : ℕ) : ℝ) ^ (-α)) := Real.rpow_nonneg (by positivity) _
      calc ((((N + 1 : ℕ) : ℝ) ^ (-α)) - 1) / (-α)
          = (1 - ((N + 1 : ℕ) : ℝ) ^ (-α)) / α := by field_simp [hα.ne']; ring
        _ ≤ 1 / α := by gcongr; linarith
    rw [hsum_shift]
    exact (hint_part N).trans hint_eval
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 2), g n) atTop (𝓝 (∑' n : ℕ, g n)) :=
    (hg_sum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 2)
  exact le_of_tendsto htend (Eventually.of_forall hpart)

/-- Absolute convergence `LSeriesSummable` of the twisted von Mangoldt series at `Re s > 1`. -/
theorem LSeriesSummable_twist_vonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) {c : ℝ}
    (hc : 1 < c) : LSeriesSummable (fun n : ℕ => χ n * (Λ n : ℂ)) (c : ℂ) := by
  let α : ℝ := (c - 1) / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hdom : Summable fun n : ℕ =>
      (1 / α) * (if n < 2 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))) :=
    (summable_rpow_tail_inv hα).mul_left (1 / α)
  refine Summable.of_norm_bounded hdom fun n => ?_
  by_cases hn2 : n < 2
  · have hΛ0 : Λ n = 0 := by
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · exact ArithmeticFunction.map_zero
      · exact ArithmeticFunction.vonMangoldt_apply_one
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [hn2]
    · rw [LSeries.term_of_ne_zero hn0, hΛ0]
      simp [hn2]
  · have hn_ge2 : 2 ≤ n := Nat.le_of_not_lt hn2
    have hn_pos : 0 < n := by omega
    have hnr_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [LSeries.term_of_ne_zero hn_pos.ne', norm_div, norm_mul, Complex.norm_real,
      Complex.norm_natCast_cpow_of_pos hn_pos]
    simp only [Complex.ofReal_re]
    have hΛ_le : |Λ n| ≤ Real.log n := by
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log
    have hlog_le : Real.log n ≤ (n : ℝ) ^ α / α := Real.log_le_rpow_div hnr_pos.le hα
    have h1 : ‖χ n‖ * |Λ n| ≤ 1 * ((n : ℝ) ^ α / α) :=
      mul_le_mul (χ.norm_le_one (n : ZMod q)) (hΛ_le.trans hlog_le) (abs_nonneg _) zero_le_one
    simp only [hn2, ↓reduceIte]
    calc ‖χ n‖ * |Λ n| / (n : ℝ) ^ c
        ≤ ((n : ℝ) ^ α / α) / (n : ℝ) ^ c := by
          gcongr
          simpa using h1
      _ = (1 / α) * ((n : ℝ) ^ α * (n : ℝ) ^ (-c)) := by
          rw [Real.rpow_neg hnr_pos.le]
          ring
      _ = (1 / α) * (n : ℝ) ^ (-(1 + α)) := by
          rw [← Real.rpow_add hnr_pos]
          congr 2
          ring

/-- Explicit bound `∑' n, ‖LSeries.term (χ * Λ) c n‖ ≤ 4 / (c - 1) ^ 2` for `1 < c`. -/
theorem tsum_norm_LSeries_term_twist_le {q : ℕ} (χ : DirichletCharacter ℂ q) {c : ℝ}
    (hc : 1 < c) :
    ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ n * (Λ n : ℂ)) (c : ℂ) n‖ ≤ 4 / (c - 1) ^ 2 := by
  let α : ℝ := (c - 1) / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hsum_norm : Summable fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => χ n * (Λ n : ℂ)) (c : ℂ) n‖ :=
    (LSeriesSummable_twist_vonMangoldt χ hc).norm
  have hsum_dom : Summable fun n : ℕ =>
      (1 / α) * (if n < 2 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))) :=
    (summable_rpow_tail_inv hα).mul_left (1 / α)
  calc ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ n * (Λ n : ℂ)) (c : ℂ) n‖
      ≤ ∑' n : ℕ, (1 / α) * (if n < 2 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))) := by
        refine hsum_norm.tsum_le_tsum (fun n => ?_) hsum_dom
        by_cases hn2 : n < 2
        · have hΛ0 : Λ n = 0 := by
            rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
            · exact ArithmeticFunction.map_zero
            · exact ArithmeticFunction.vonMangoldt_apply_one
          rcases eq_or_ne n 0 with rfl | hn0
          · simp [hn2]
          · rw [LSeries.term_of_ne_zero hn0, hΛ0]
            simp [hn2]
        · have hn_ge2 : 2 ≤ n := Nat.le_of_not_lt hn2
          have hn_pos : 0 < n := by omega
          have hnr_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
          rw [LSeries.term_of_ne_zero hn_pos.ne', norm_div, norm_mul, Complex.norm_real,
            Complex.norm_natCast_cpow_of_pos hn_pos]
          simp only [hn2, ↓reduceIte]
          simp only [Complex.ofReal_re]
          have hΛ_le : |Λ n| ≤ Real.log n := by
            rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            exact ArithmeticFunction.vonMangoldt_le_log
          have hlog_le : Real.log n ≤ (n : ℝ) ^ α / α := Real.log_le_rpow_div hnr_pos.le hα
          have h1 : ‖χ n‖ * |Λ n| ≤ (n : ℝ) ^ α / α := by
            calc ‖χ n‖ * |Λ n| ≤ 1 * ((n : ℝ) ^ α / α) :=
                  mul_le_mul (χ.norm_le_one (n : ZMod q)) (hΛ_le.trans hlog_le)
                    (abs_nonneg _) zero_le_one
              _ = (n : ℝ) ^ α / α := one_mul _
          calc ‖χ n‖ * |Λ n| / (n : ℝ) ^ c
              ≤ ((n : ℝ) ^ α / α) / (n : ℝ) ^ c := by gcongr
            _ = (1 / α) * ((n : ℝ) ^ α * (n : ℝ) ^ (-c)) := by
                rw [Real.rpow_neg hnr_pos.le]; ring
            _ = (1 / α) * (n : ℝ) ^ (-(1 + α)) := by
                rw [← Real.rpow_add hnr_pos]; congr 2; ring
    _ = (1 / α) * ∑' n : ℕ, (if n < 2 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))) := tsum_mul_left
    _ ≤ (1 / α) * (1 / α) := mul_le_mul_of_nonneg_left (tsum_rpow_tail_le hα) (by positivity)
    _ = 4 / (c - 1) ^ 2 := by
        dsimp [α]
        field_simp [(by linarith : c - 1 ≠ 0)]
        ring

/-- Analytic identification `LSeries (χ * Λ) s = -L'(s, χ) / L(s, χ)` for `1 < s.re`. -/
theorem LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) s = -deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s := by
  have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs] at h1
  exact h1

private lemma contour_rect_vert_eval (T : ℝ) {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (-T)..T, ((a : ℂ) + (t : ℂ) * I)⁻¹ = ((2 * Real.arctan (T / a) : ℝ) : ℂ) := by
  have hsplit : ∀ t : ℝ, ((a : ℂ) + (t : ℂ) * I)⁻¹ =
      ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) + I * ((-t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro t
    have hden_pos : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
    have hden : (a ^ 2 + t ^ 2 : ℝ) ≠ 0 := hden_pos.ne'
    have hdenC' : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden
    symm
    refine eq_inv_of_mul_eq_one_left ?_
    push_cast
    field_simp [hdenC']
    calc ((a : ℂ) + -((t : ℂ) * I)) * ((a : ℂ) + (t : ℂ) * I)
        = (a : ℂ) ^ 2 - (t : ℂ) ^ 2 * I ^ 2 := by ring
      _ = (a : ℂ) ^ 2 + (t : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
  have hc1 : Continuous fun t : ℝ => (a / (a ^ 2 + t ^ 2) : ℝ) :=
    continuous_const.div (continuous_const.add (continuous_pow 2)) fun t =>
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)).ne'
  have hc2 : Continuous fun t : ℝ => (-t / (a ^ 2 + t ^ 2) : ℝ) :=
    continuous_neg.div (continuous_const.add (continuous_pow 2)) fun t =>
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)).ne'
  have hi1 : IntervalIntegrable (fun t : ℝ => ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) volume (-T) T :=
    (Complex.continuous_ofReal.comp hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => I * ((-t / (a ^ 2 + t ^ 2) : ℝ) : ℂ))
      volume (-T) T :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hc2)).intervalIntegrable _ _
  have h_int1 : ∫ t in (-T)..T, (a / (a ^ 2 + t ^ 2) : ℝ) = 2 * Real.arctan (T / a) := by
    have hd : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt (fun u : ℝ => Real.arctan (u / a)) (a / (a ^ 2 + t ^ 2)) t := by
      intro t _
      have hd1 : HasDerivAt (fun u : ℝ => u / a) (a⁻¹) t :=
        ((hasDerivAt_id' t).div_const a).congr_deriv (by rw [one_div])
      refine ((Real.hasDerivAt_arctan (t / a)).comp t hd1).congr_deriv ?_
      field_simp [ha]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.intervalIntegrable _ _)]
    rw [neg_div, Real.arctan_neg]
    ring
  have h_int2 : ∫ t in (-T)..T, (-t / (a ^ 2 + t ^ 2) : ℝ) = 0 := by
    have hd : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt (fun u : ℝ => -(1 / 2 : ℝ) * Real.log (a ^ 2 + u ^ 2))
          (-t / (a ^ 2 + t ^ 2)) t := by
      intro t _
      have hpos : a ^ 2 + t ^ 2 ≠ 0 :=
        (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)).ne'
      have hsub : HasDerivAt (fun u : ℝ => a ^ 2 + u ^ 2) (2 * t) t := by
        convert (hasDerivAt_pow 2 t).const_add (a ^ 2) using 1
        ring
      refine (((Real.hasDerivAt_log hpos).comp t hsub).const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
      field_simp [hpos]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable _ _)]
    simp only [neg_sq, sub_self]
  calc ∫ t in (-T)..T, ((a : ℂ) + (t : ℂ) * I)⁻¹
      = ∫ t in (-T)..T,
          (((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) + I * ((-t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
        intervalIntegral.integral_congr fun t _ => hsplit t
    _ = (∫ t in (-T)..T, ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) +
          ∫ t in (-T)..T, I * ((-t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) :=
        intervalIntegral.integral_add hi1 hi2
    _ = ((∫ t in (-T)..T, (a / (a ^ 2 + t ^ 2) : ℝ) : ℝ) : ℂ) +
          I * ((∫ t in (-T)..T, (-t / (a ^ 2 + t ^ 2) : ℝ) : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_ofReal]
    _ = ((2 * Real.arctan (T / a) : ℝ) : ℂ) := by
        rw [h_int1, h_int2, Complex.ofReal_zero, mul_zero, add_zero]

private lemma contour_rect_horiz_diff {σ₀ c T : ℝ} (hT : 0 < T) :
    (∫ u in σ₀..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
        (∫ u in σ₀..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) =
      I * ((2 * (Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T)) : ℝ) : ℂ) := by
  have hcont_bot : Continuous fun u : ℝ => ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ :=
    ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀ fun u h0 => by
      have := congrArg Complex.im h0; simp at this; linarith
  have hcont_top : Continuous fun u : ℝ => ((u : ℂ) + (T : ℂ) * I - 1)⁻¹ :=
    ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀ fun u h0 => by
      have := congrArg Complex.im h0; simp at this; linarith
  rw [← intervalIntegral.integral_sub (hcont_bot.intervalIntegrable _ _)
    (hcont_top.intervalIntegrable _ _)]
  have hdiff_pt : ∀ u : ℝ,
      ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ - ((u : ℂ) + (T : ℂ) * I - 1)⁻¹ =
        I * ((2 * T / ((u - 1) ^ 2 + T ^ 2) : ℝ) : ℂ) := by
    intro u
    have hz1 : (u : ℂ) - 1 - (T : ℂ) * I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; simp at this; linarith
    have hz2 : (u : ℂ) - 1 + (T : ℂ) * I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; simp at this; linarith
    have hden : ((u - 1) ^ 2 + T ^ 2 : ℝ) ≠ 0 :=
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hT.ne')).ne'
    have hdenC' : ((u : ℂ) - 1) ^ 2 + (T : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden
    have hprod : ((u : ℂ) - 1 + (T : ℂ) * I) * ((u : ℂ) - 1 - (T : ℂ) * I) =
        ((u : ℂ) - 1) ^ 2 + (T : ℂ) ^ 2 := by
      calc ((u : ℂ) - 1 + (T : ℂ) * I) * ((u : ℂ) - 1 - (T : ℂ) * I)
          = ((u : ℂ) - 1) ^ 2 - (T : ℂ) ^ 2 * I ^ 2 := by ring
        _ = ((u : ℂ) - 1) ^ 2 + (T : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
    push_cast
    rw [show (u : ℂ) + -(T : ℂ) * I - 1 = (u : ℂ) - 1 - (T : ℂ) * I by ring,
      show (u : ℂ) + (T : ℂ) * I - 1 = (u : ℂ) - 1 + (T : ℂ) * I by ring]
    rw [inv_sub_inv hz1 hz2, ← mul_div_assoc, div_eq_div_iff (mul_ne_zero hz1 hz2) hdenC']
    calc ((u : ℂ) - 1 + (T : ℂ) * I - ((u : ℂ) - 1 - (T : ℂ) * I)) * (((u : ℂ) - 1) ^ 2 + (T : ℂ) ^ 2)
        = (2 * (T : ℂ) * I) * (((u : ℂ) - 1 + (T : ℂ) * I) * ((u : ℂ) - 1 - (T : ℂ) * I)) := by
          rw [hprod]; ring
      _ = I * (2 * (T : ℂ)) * (((u : ℂ) - 1 - (T : ℂ) * I) * ((u : ℂ) - 1 + (T : ℂ) * I)) := by ring
  have hc_real : Continuous fun u : ℝ => (T / ((u - 1) ^ 2 + T ^ 2) : ℝ) :=
    continuous_const.div (((continuous_id.sub continuous_const).pow 2).add continuous_const)
      fun u => (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hT.ne')).ne'
  have h_int_u : ∫ u in σ₀..c, (T / ((u - 1) ^ 2 + T ^ 2) : ℝ) =
      Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T) := by
    have hd : ∀ u ∈ Set.uIcc σ₀ c,
        HasDerivAt (fun v : ℝ => Real.arctan ((v - 1) / T)) (T / ((u - 1) ^ 2 + T ^ 2)) u := by
      intro u _
      have hd1 : HasDerivAt (fun v : ℝ => (v - 1) / T) T⁻¹ u :=
        (((hasDerivAt_id' u).sub_const 1).div_const T).congr_deriv (by rw [one_div])
      refine ((Real.hasDerivAt_arctan ((u - 1) / T)).comp u hd1).congr_deriv ?_
      have hpos1 : 1 + ((u - 1) / T) ^ 2 ≠ 0 :=
        (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'
      field_simp [hpos1, hT.ne']
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_real.intervalIntegrable _ _)]
    have heq : (σ₀ - 1) / T = -((1 - σ₀) / T) := by ring
    rw [heq, Real.arctan_neg]
    ring
  calc ∫ u in σ₀..c, (((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ - ((u : ℂ) + (T : ℂ) * I - 1)⁻¹)
      = ∫ u in σ₀..c, I * ((2 : ℂ) * ((T / ((u - 1) ^ 2 + T ^ 2) : ℝ) : ℂ)) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        rw [hdiff_pt u]
        push_cast; ring
    _ = I * ((2 : ℂ) * ((∫ u in σ₀..c, (T / ((u - 1) ^ 2 + T ^ 2) : ℝ) : ℝ) : ℂ)) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_ofReal]
    _ = I * ((2 * (Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T)) : ℝ) : ℂ) := by
        rw [h_int_u]
        push_cast; ring

/-- Exact rectangular contour residue calculation: for `σ₀ < 1 < c` and `0 < T`,
`(1 / (2πi)) ∮_{∂([σ₀, c] × [-T, T])} ds / (s - 1) = 1`. -/
theorem contour_rect_inv_sub_one_eq_one {σ₀ c T : ℝ} (hσ : σ₀ < 1) (hc : 1 < c) (hT : 0 < T) :
    (1 / (2 * Real.pi * I)) *
        ((∫ u in σ₀..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
          (∫ u in σ₀..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) +
          I * (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
          I * (∫ t in (-T)..T, ((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹)) = 1 := by
  have hc_sub : c - 1 ≠ 0 := by linarith
  have hσ_sub : σ₀ - 1 ≠ 0 := by linarith
  have hright : ∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹ =
      ((2 * Real.arctan (T / (c - 1)) : ℝ) : ℂ) := by
    refine (intervalIntegral.integral_congr fun t _ => ?_).trans
      (contour_rect_vert_eval T hc_sub)
    rw [show (c : ℂ) + (t : ℂ) * I - 1 = ((c - 1 : ℝ) : ℂ) + (t : ℂ) * I by push_cast; ring]
  have hleft : ∫ t in (-T)..T, ((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹ =
      ((-2 * Real.arctan (T / (1 - σ₀)) : ℝ) : ℂ) := by
    have hcong : ∫ t in (-T)..T, ((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹ =
        ∫ t in (-T)..T, (((σ₀ - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [show (σ₀ : ℂ) + (t : ℂ) * I - 1 = ((σ₀ - 1 : ℝ) : ℂ) + (t : ℂ) * I by push_cast; ring]
    rw [hcong, contour_rect_vert_eval T hσ_sub]
    have heq : T / (σ₀ - 1) = -(T / (1 - σ₀)) := by
      field_simp [hσ_sub, (by linarith : 1 - σ₀ ≠ 0)]
      ring
    rw [heq, Real.arctan_neg]
    push_cast; ring
  have hhoriz := contour_rect_horiz_diff (σ₀ := σ₀) (c := c) hT
  have hsum_pi :
      Real.arctan ((c - 1) / T) + Real.arctan (T / (c - 1)) = Real.pi / 2 ∧
        Real.arctan ((1 - σ₀) / T) + Real.arctan (T / (1 - σ₀)) = Real.pi / 2 := by
    have h1 : 0 < (c - 1) / T := div_pos (by linarith) hT
    have h2 : 0 < (1 - σ₀) / T := div_pos (by linarith) hT
    have ha1 := Real.arctan_inv_of_pos h1
    have ha2 := Real.arctan_inv_of_pos h2
    rw [inv_div] at ha1 ha2
    exact ⟨by linarith, by linarith⟩
  rw [hhoriz, hright, hleft]
  have hsum_in : I * ((2 * (Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T)) : ℝ) : ℂ) +
        I * ((2 * Real.arctan (T / (c - 1)) : ℝ) : ℂ) -
        I * ((-2 * Real.arctan (T / (1 - σ₀)) : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * I := by
    have hr : (2 * (Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T)) +
        2 * Real.arctan (T / (c - 1)) + 2 * Real.arctan (T / (1 - σ₀))) = 2 * Real.pi := by
      linarith [hsum_pi.1, hsum_pi.2]
    have hc_eq : I * ((2 * (Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T)) : ℝ) : ℂ) +
        I * ((2 * Real.arctan (T / (c - 1)) : ℝ) : ℂ) -
        I * ((-2 * Real.arctan (T / (1 - σ₀)) : ℝ) : ℂ) =
        I * ((2 * (Real.arctan ((c - 1) / T) + Real.arctan ((1 - σ₀) / T)) +
          2 * Real.arctan (T / (c - 1)) + 2 * Real.arctan (T / (1 - σ₀)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc_eq, hr]
    push_cast; ring
  rw [hsum_in]
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero]

private lemma differentiable_ofReal_cpow {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have heq : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => Complex.exp (Complex.log (x : ℂ) * s) := by
    ext s
    exact Complex.cpow_def_of_ne_zero hx0 s
  rw [heq]
  exact Complex.differentiable_exp.comp (differentiable_const _ |>.mul differentiable_id)

private lemma continuous_ofReal_cpow {x : ℝ} (hx : 0 < x) :
    Continuous (fun s : ℂ => (x : ℂ) ^ s) :=
  (differentiable_ofReal_cpow hx).continuous

private lemma integral_inv_sqrt_sq_add_sq_le {σ₀ T : ℝ} (hσ : 0 < σ₀) (hT : 0 < T) :
    ∫ t in (-T)..T, (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ ≤
      2 * Real.sqrt 2 * Real.log (1 + T / σ₀) := by
  have hc_sqrt : Continuous fun t : ℝ => (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ := by
    refine Continuous.inv₀ (Continuous.sqrt (continuous_const.add (continuous_pow 2))) fun t => ?_
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc_abs : Continuous fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|) :=
    continuous_const.div (continuous_const.add continuous_abs) fun t =>
      (add_pos_of_pos_of_nonneg hσ (abs_nonneg t)).ne'
  have hmono : ∫ t in (-T)..T, (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ ≤
      ∫ t in (-T)..T, Real.sqrt 2 / (σ₀ + |t|) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hc_sqrt.intervalIntegrable _ _)
      (hc_abs.intervalIntegrable _ _) fun t _ => ?_
    have hsq_le : (σ₀ + |t|) ^ 2 ≤ 2 * (σ₀ ^ 2 + t ^ 2) := by
      have h1 : 2 * σ₀ * |t| ≤ σ₀ ^ 2 + |t| ^ 2 := by nlinarith [sq_nonneg (σ₀ - |t|)]
      rw [sq_abs] at h1
      nlinarith [sq_abs t]
    have hle : σ₀ + |t| ≤ Real.sqrt 2 * Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
      calc σ₀ + |t| = Real.sqrt ((σ₀ + |t|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (2 * (σ₀ ^ 2 + t ^ 2)) := Real.sqrt_le_sqrt hsq_le
        _ = Real.sqrt 2 * Real.sqrt (σ₀ ^ 2 + t ^ 2) := Real.sqrt_mul zero_le_two _
    have hden_pos : 0 < Real.sqrt (σ₀ ^ 2 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hden2_pos : 0 < σ₀ + |t| := by positivity
    rw [inv_eq_one_div, div_le_div_iff₀ hden_pos hden2_pos]
    linarith
  have heven : ∫ t in (-T)..T, Real.sqrt 2 / (σ₀ + |t|) =
      2 * ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) := by
    have hi_left : IntervalIntegrable (fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|)) volume (-T) 0 :=
      hc_abs.intervalIntegrable _ _
    have hi_right : IntervalIntegrable (fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|)) volume 0 T :=
      hc_abs.intervalIntegrable _ _
    have hadd := (intervalIntegral.integral_add_adjacent_intervals hi_left hi_right).symm
    have hleft : ∫ t in (-T)..0, Real.sqrt 2 / (σ₀ + |t|) =
        ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) := by
      have hcomp := intervalIntegral.integral_comp_neg (fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|))
        (a := 0) (b := T)
      simp only [neg_zero, abs_neg] at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hT.le] at ht
      rw [abs_of_nonneg ht.1]
    have hright : ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + |t|) =
        ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hT.le] at ht
      rw [abs_of_nonneg ht.1]
    rw [hadd, hleft, hright]
    ring
  have heval : ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) = Real.sqrt 2 * Real.log (1 + T / σ₀) := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun u : ℝ => Real.sqrt 2 * Real.log (σ₀ + u)) (Real.sqrt 2 / (σ₀ + t)) t := by
      intro t ht
      rw [Set.uIcc_of_le hT.le] at ht
      have hpos : σ₀ + t ≠ 0 := (add_pos_of_pos_of_nonneg hσ ht.1).ne'
      have hsub : HasDerivAt (fun u : ℝ => σ₀ + u) 1 t := (hasDerivAt_id' t).const_add σ₀
      refine (((Real.hasDerivAt_log hpos).comp t hsub).const_mul (Real.sqrt 2)).congr_deriv ?_
      ring
    have hc_pos : ContinuousOn (fun t : ℝ => Real.sqrt 2 / (σ₀ + t)) (Set.uIcc 0 T) := by
      rw [Set.uIcc_of_le hT.le]
      exact continuousOn_const.div (continuousOn_const.add continuousOn_id) fun t ht =>
        (add_pos_of_pos_of_nonneg hσ ht.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_pos.intervalIntegrable]
    rw [add_zero, ← mul_sub, ← Real.log_div (by linarith) hσ.ne']
    congr 2
    field_simp [hσ.ne']
  exact hmono.trans_eq (by rw [heven, heval]; ring)

private lemma shifted_contour_norm_le {G : ℂ → ℂ} {x σ₀ c T B_vert B_horiz : ℝ}
    (hx : 0 < x) (hσ : 0 < σ₀) (hσc : σ₀ ≤ c) (hT : 0 < T)
    (hB_vert : 0 ≤ B_vert) (_hB_horiz : 0 ≤ B_horiz)
    (hcont_vert : ContinuousOn (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T))
    (hcont_top : ContinuousOn (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) (Set.Icc σ₀ c))
    (hcont_bot : ContinuousOn (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) (Set.Icc σ₀ c))
    (hbound_vert : ∀ t ∈ Set.Icc (-T) T,
      ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert * x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2))
    (hbound_top : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz * x ^ c / T)
    (hbound_bot : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz * x ^ c / T) :
    ‖(1 / (2 * Real.pi * I)) *
        (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)))‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
  have hint_vert : IntervalIntegrable (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le (by linarith)]
  have hint_top : IntervalIntegrable (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) volume σ₀ c := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hσc]
  have hint_bot : IntervalIntegrable (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
      volume σ₀ c := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hσc]
  have hnorm_vert : ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
      2 * Real.sqrt 2 * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (by linarith : -T ≤ T)
    have hsqrt_cont : Continuous fun t : ℝ => B_vert * x ^ σ₀ * (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ :=
      continuous_const.mul ((Continuous.sqrt (continuous_const.add (continuous_pow 2))).inv₀
        fun t => (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos hσ) (sq_nonneg t))).ne')
    have h2 : ∫ t in (-T)..T, ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t in (-T)..T, B_vert * x ^ σ₀ * (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ := by
      refine intervalIntegral.integral_mono_on (by linarith) hint_vert.norm
        (hsqrt_cont.intervalIntegrable _ _) fun t ht => ?_
      simpa [div_eq_mul_inv] using hbound_vert t ht
    rw [intervalIntegral.integral_const_mul (μ := volume) (B_vert * x ^ σ₀) (fun t : ℝ => (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹)] at h2
    calc ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ B_vert * x ^ σ₀ * ∫ t in (-T)..T, (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ := h1.trans h2
      _ ≤ B_vert * x ^ σ₀ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₀)) := by
          gcongr
          exact integral_inv_sqrt_sq_add_sq_le hσ hT
      _ = 2 * Real.sqrt 2 * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) := by ring
  have hnorm_top : ‖∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)‖ ≤ (c - σ₀) * (B_horiz * x ^ c / T) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hσc).trans ?_
    refine (intervalIntegral.integral_mono_on hσc hint_top.norm (by simp) hbound_top).trans_eq ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hnorm_bot : ‖∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
      (c - σ₀) * (B_horiz * x ^ c / T) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hσc).trans ?_
    refine (intervalIntegral.integral_mono_on hσc hint_bot.norm (by simp) hbound_bot).trans_eq ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hnorm_coeff : ‖(1 / (2 * Real.pi * I) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    simp only [one_div, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    norm_num
  have htri : ‖I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
        (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
      ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖ +
        ‖∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)‖ +
        ‖∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
    have hI : ‖I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I))‖ =
        ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have h1 := norm_sub_le
      (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) + ∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I))
      (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
    have h2 := norm_add_le
      (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)))
      (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I))
    linarith
  rw [norm_mul, hnorm_coeff]
  calc (2 * Real.pi)⁻¹ *
        ‖I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖
      ≤ (2 * Real.pi)⁻¹ *
          (2 * Real.sqrt 2 * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
            (c - σ₀) * (B_horiz * x ^ c / T) +
            (c - σ₀) * (B_horiz * x ^ c / T)) := by
        gcongr
        linarith
    _ = (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
          ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
        field_simp [Real.pi_pos.ne', hT.ne']
        ring

/-- Conditional rectangular contour shift for a nontrivial character `χ ≠ 1`:
assuming `LFunction χ` is nonvanishing on `[σ₀, c] × [-T, T]` (`0 < σ₀ < c`, `1 < c`, `0 < T`)
with boundary bounds `B_vert` on `Re s = σ₀` and `B_horiz` on `Im s = ±T` for
`-L'(s, χ) / L(s, χ)`, bounds `‖dirichletContourIntegral (χ * Λ) x c T‖`. -/
theorem norm_dirichletContourIntegral_twist_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1)
    {x σ₀ c T B_vert B_horiz : ℝ} (hx : 1 ≤ x) (hσ : 0 < σ₀) (hσc : σ₀ ≤ c) (hc : 1 < c)
    (hT : 0 < T) (hB_vert : 0 ≤ B_vert) (hB_horiz : 0 ≤ B_horiz)
    (hnonzero : ∀ s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T, DirichletCharacter.LFunction χ s ≠ 0)
    (hvert : ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert)
    (htop : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (T : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz)
    (hbot : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((-T : ℝ) : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz) :
    ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
        (fun n : ℕ => χ n * (Λ n : ℂ)) x c T‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let G : ℂ → ℂ := fun s =>
    (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      (x : ℂ) ^ s / s
  have hdiff_L : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hdiff_dL : Differentiable ℂ (deriv (DirichletCharacter.LFunction χ)) := hdiff_L.deriv
  have hdiff_G : DifferentiableOn ℂ G (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) := by
    intro s hs
    have hs_ne : s ≠ 0 := by
      intro h0
      have hre : s.re = 0 := by rw [h0]; simp
      linarith [hs.1.1]
    have hL_ne : DirichletCharacter.LFunction χ s ≠ 0 := hnonzero s hs
    have h1 : DifferentiableAt ℂ (fun w : ℂ =>
        -deriv (DirichletCharacter.LFunction χ) w / DirichletCharacter.LFunction χ w) s :=
      (hdiff_dL.differentiableAt.neg).div hdiff_L.differentiableAt hL_ne
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ w) s :=
      (differentiable_ofReal_cpow hx_pos).differentiableAt
    exact ((h1.mul h2).div differentiableAt_id hs_ne).differentiableWithinAt
  let z : ℂ := (σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I
  let w : ℂ := (c : ℂ) + (T : ℂ) * I
  have hrect_eq : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) =
      Set.Icc σ₀ c ×ℂ Set.Icc (-T) T := by
    have hzre : z.re = σ₀ := by simp [z]
    have hzim : z.im = -T := by simp [z]
    have hwre : w.re = c := by simp [w]
    have hwim : w.im = T := by simp [w]
    rw [hzre, hzim, hwre, hwim, Set.uIcc_of_le hσc, Set.uIcc_of_le (by linarith)]
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G z w
    (by rwa [hrect_eq])
  simp only [show z.re = σ₀ by simp [z], show z.im = -T by simp [z],
    show w.re = c by simp [w], show w.im = T by simp [w], smul_eq_mul] at hcauchy
  have hright_eq :
      (1 / (2 * Real.pi * I)) * (I * ∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) =
        AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => χ n * (Λ n : ℂ)) x c T := by
    rw [← AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral_eq_div_two_pi_mul_I]
    refine congrArg (fun z : ℂ => (1 / (2 * Real.pi * I)) * (I * z)) ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    dsimp [G]
    rw [LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction χ (by rw [hre]; exact hc)]
  have hshifted_eq :
      AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => χ n * (Λ n : ℂ)) x c T =
        (1 / (2 * Real.pi * I)) *
          (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
            (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
            (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
    have halg : I * (∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) =
        I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
      linear_combination hcauchy
    rw [← hright_eq, halg]
  have hcont_G : ContinuousOn G (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) := hdiff_G.continuousOn
  have hcont_vert : ContinuousOn (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    refine hcont_G.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      fun t ht => ?_
    refine ⟨?_, ?_⟩
    · simp [hσc]
    · simpa using ht
  have hcont_top : ContinuousOn (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) (Set.Icc σ₀ c) := by
    refine hcont_G.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      fun u hu => ?_
    refine ⟨?_, ?_⟩
    · simpa using hu
    · simp [hT.le]
  have hcont_bot : ContinuousOn (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) (Set.Icc σ₀ c) := by
    refine hcont_G.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      fun u hu => ?_
    refine ⟨?_, ?_⟩
    · simpa using hu
    · simp [hT.le]
  have hbound_vert : ∀ t ∈ Set.Icc (-T) T,
      ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert * x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
    intro t ht
    have hnorm_s : ‖(σ₀ : ℂ) + (t : ℂ) * I‖ = Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp [pow_two]
    have hnorm_x : ‖(x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I)‖ = x ^ σ₀ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp
    dsimp [G]
    rw [norm_div, norm_mul, hnorm_s, hnorm_x]
    gcongr
    exact hvert t ht
  have hbound_top : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz * x ^ c / T := by
    intro u hu
    have hnorm_s : T ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := by
      have him : ((u : ℂ) + (T : ℂ) * I).im = T := by simp
      calc T = |((u : ℂ) + (T : ℂ) * I).im| := by rw [him, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hnorm_x : ‖(x : ℂ) ^ ((u : ℂ) + (T : ℂ) * I)‖ ≤ x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hx hu.2
    dsimp [G]
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul (htop u hu) hnorm_x (norm_nonneg _) hB_horiz) hT hnorm_s
  have hbound_bot : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz * x ^ c / T := by
    intro u hu
    have hnorm_s : T ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := by
      have him : ((u : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
      calc T = |((u : ℂ) + ((-T : ℝ) : ℂ) * I).im| := by rw [him, abs_neg, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hnorm_x : ‖(x : ℂ) ^ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hx hu.2
    dsimp [G]
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul (hbot u hu) hnorm_x (norm_nonneg _) hB_horiz) hT hnorm_s
  rw [hshifted_eq]
  exact shifted_contour_norm_le hx_pos hσ hσc hT hB_vert hB_horiz
    hcont_vert hcont_top hcont_bot hbound_vert hbound_top hbound_bot

private lemma sum_norm_twist_Icc_le {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ‖χ n * (Λ n : ℂ)‖ ≤ (Real.log 4 + 4) * M := by
  have h1 : ∑ n ∈ Finset.Icc 1 M, ‖χ n * (Λ n : ℂ)‖ ≤ ∑ n ∈ Finset.Icc 1 M, Λ n := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one (n : ZMod q))
  have h2 : ∑ n ∈ Finset.Icc 1 M, Λ n = Chebyshev.psi M := by
    rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add, Nat.floor_natCast]
  exact h1.trans (h2.symm ▸ Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg M))

/-- Explicit Perron + contour-shift bound for `‖psiChar (N + 1 / 2) χ‖` (`χ ≠ 1`) under a
rectangular zero-free region hypothesis for `LFunction χ`. -/
theorem norm_psiChar_le_of_rect_zeroFree {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) {σ₀ c T B_vert B_horiz : ℝ} (hσ : 0 < σ₀) (hσc : σ₀ ≤ c) (hc : 1 < c)
    (hT : 0 < T) (hB_vert : 0 ≤ B_vert) (hB_horiz : 0 ≤ B_horiz)
    (hnonzero : ∀ s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T, DirichletCharacter.LFunction χ s ≠ 0)
    (hvert : ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert)
    (htop : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (T : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz)
    (hbot : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((-T : ℝ) : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz) :
    let x : ℝ := N + 1 / 2
    ‖psiChar x χ‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c +
        (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) +
        (2 ^ c * (4 * x) / (Real.pi * T)) * ((Real.log 4 + 4) * (2 * x)) := by
  intro x
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [show (1 : ℝ) ≤ N by exact_mod_cast hN]
  have hc_pos : 0 < c := by linarith
  have ha := LSeriesSummable_twist_vonMangoldt χ hc
  have hperron := AnalyticNumberTheory.DirichletSeries.perron_truncated_half_integer
    (a := fun n : ℕ => χ n * (Λ n : ℂ)) (N := N) hc_pos hT ha
  have hfl : ⌊x⌋₊ = N := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hpsi_eq : psiChar x χ = ∑ n ∈ Finset.Icc 1 N, χ n * (Λ n : ℂ) := by
    rw [psiChar, hfl]
  have hshift := norm_dirichletContourIntegral_twist_le hχ hx1 hσ hσc hc hT hB_vert hB_horiz
    hnonzero hvert htop hbot
  have hterm := tsum_norm_LSeries_term_twist_le χ hc
  have htail : ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖χ n * (Λ n : ℂ)‖ ≤
      (Real.log 4 + 4) * (2 * x) := by
    have h2N : ((2 * N + 1 : ℕ) : ℝ) = 2 * x := by dsimp [x]; push_cast; ring
    simpa [h2N] using sum_norm_twist_Icc_le χ (2 * N + 1)
  have htri : ‖psiChar x χ‖ ≤
      ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => χ n * (Λ n : ℂ)) x c T‖ +
        ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => χ n * (Λ n : ℂ)) x c T - psiChar x χ‖ := by
    have hid : psiChar x χ =
        AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => χ n * (Λ n : ℂ)) x c T -
          (AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
            (fun n : ℕ => χ n * (Λ n : ℂ)) x c T - psiChar x χ) := by ring
    calc ‖psiChar x χ‖ =
          ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
              (fun n : ℕ => χ n * (Λ n : ℂ)) x c T -
            (AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
              (fun n : ℕ => χ n * (Λ n : ℂ)) x c T - psiChar x χ)‖ := by rw [← hid]
      _ ≤ _ := norm_sub_le _ _
  rw [hpsi_eq] at htri ⊢
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : (x ^ c / (Real.pi * T * Real.log 2)) *
        ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ n * (Λ n : ℂ)) (c : ℂ) n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) := by
    gcongr
  have h2 : (2 ^ c * (4 * x) / (Real.pi * T)) *
        ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖χ n * (Λ n : ℂ)‖ ≤
      (2 ^ c * (4 * x) / (Real.pi * T)) * ((Real.log 4 + 4) * (2 * x)) := by
    gcongr
  dsimp only at hperron
  linarith

/-- Conditional rectangular contour shift for the principal character `1` mod `q`:
assuming `LFunctionTrivChar₁ q` is nonvanishing on `[σ₀, c] × [-T, T]` (`0 < σ₀ < 1 < c`, `0 < T`)
with boundary bounds `B_vert` on `Re s = σ₀` and `B_horiz` on `Im s = ±T` for
`-L'(s, 1) / L(s, 1)`, extracts the pole residue `x` at `s = 1` and bounds
`‖dirichletContourIntegral (1 * Λ) x c T - x‖`. -/
theorem norm_dirichletContourIntegral_trivChar_sub_le (q : ℕ) [NeZero q]
    {x σ₀ c T B_vert B_horiz : ℝ} (hx : 1 ≤ x) (hσ : 0 < σ₀) (hσ1 : σ₀ < 1) (hc : 1 < c)
    (hT : 0 < T) (hB_vert : 0 ≤ B_vert) (hB_horiz : 0 ≤ B_horiz)
    (hnonzero : ∀ s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T,
      DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0)
    (hvert : ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((σ₀ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert)
    (htop : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((u : ℂ) + (T : ℂ) * I) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz)
    (hbot : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((u : ℂ) + ((-T : ℝ) : ℂ) * I) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz) :
    ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
        (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T - (x : ℂ)‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hσc : σ₀ ≤ c := (hσ1.trans hc).le
  let G : ℂ → ℂ := fun s =>
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) * (x : ℂ) ^ s / s
  let hx_pow : ℂ → ℂ := fun w => (x : ℂ) ^ w / w
  let F₁ : ℂ → ℂ := fun s =>
    (-deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
      DirichletCharacter.LFunctionTrivChar₁ q s) * hx_pow s + dslope hx_pow 1 s
  have hL1_entire : Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ q) :=
    DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  have hL1_deriv_entire : Differentiable ℂ (deriv (DirichletCharacter.LFunctionTrivChar₁ q)) :=
    hL1_entire.deriv
  have h_half_open : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h_hx_diff : DifferentiableOn ℂ hx_pow {s : ℂ | 0 < s.re} := by
    intro s hs
    have hs_ne : s ≠ 0 := by
      intro h0
      have hre : s.re = 0 := by rw [h0]; simp
      linarith [show 0 < s.re from hs]
    exact ((differentiable_ofReal_cpow hx_pos).differentiableAt.div
      differentiableAt_id hs_ne).differentiableWithinAt
  have h_dslope_diff : DifferentiableOn ℂ (dslope hx_pow 1) {s : ℂ | 0 < s.re} :=
    (Complex.differentiableOn_dslope (h_half_open.mem_nhds (by simp))).mpr h_hx_diff
  have hrect_sub : Set.Icc σ₀ c ×ℂ Set.Icc (-T) T ⊆ {s : ℂ | 0 < s.re} := fun _ hs =>
    hσ.trans_le hs.1.1
  have hdiff_F₁ : DifferentiableOn ℂ F₁ (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) := by
    intro s hs
    have hs_half : s ∈ {s : ℂ | 0 < s.re} := hrect_sub hs
    have hL1_ne := hnonzero s hs
    have hd1 : DifferentiableAt ℂ (fun w : ℂ =>
        -deriv (DirichletCharacter.LFunctionTrivChar₁ q) w /
          DirichletCharacter.LFunctionTrivChar₁ q w) s :=
      hL1_deriv_entire.differentiableAt.neg.div hL1_entire.differentiableAt hL1_ne
    have hd2 : DifferentiableAt ℂ hx_pow s :=
      h_hx_diff.differentiableAt (h_half_open.mem_nhds hs_half)
    have hd3 : DifferentiableWithinAt ℂ (dslope hx_pow 1) (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) s :=
      (h_dslope_diff s hs_half).mono hrect_sub
    exact (hd1.mul hd2).differentiableWithinAt.add hd3
  let z : ℂ := (σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I
  let w : ℂ := (c : ℂ) + (T : ℂ) * I
  have hrect_eq : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) =
      Set.Icc σ₀ c ×ℂ Set.Icc (-T) T := by
    have hzre : z.re = σ₀ := by simp [z]
    have hzim : z.im = -T := by simp [z]
    have hwre : w.re = c := by simp [w]
    have hwim : w.im = T := by simp [w]
    rw [hzre, hzim, hwre, hwim, Set.uIcc_of_le hσc, Set.uIcc_of_le (by linarith)]
  have hcauchy_F₁ := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F₁ z w
    (by rwa [hrect_eq])
  simp only [show z.re = σ₀ by simp [z], show z.im = -T by simp [z],
    show w.re = c by simp [w], show w.im = T by simp [w], smul_eq_mul] at hcauchy_F₁
  have h_split_ne1 : ∀ s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T, s ≠ 1 →
      G s = (x : ℂ) * (s - 1)⁻¹ + F₁ s := by
    intro s hs hs1
    have hs_ne : s ≠ 0 := by
      intro h0
      have hre : s.re = 0 := by rw [h0]; simp
      linarith [hs.1.1]
    have hL1_ne := hnonzero s hs
    have hL1_eq : DirichletCharacter.LFunctionTrivChar₁ q s =
        (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s :=
      Function.update_of_ne hs1 _ _
    have hL_ne : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
      intro h0
      apply hL1_ne
      rw [hL1_eq, h0, mul_zero]
    have hderiv1 : deriv (DirichletCharacter.LFunctionTrivChar₁ q) s =
        (s - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s :=
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1
    have hlog_id :
        -deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
            DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
          (s - 1)⁻¹ + (-deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
            DirichletCharacter.LFunctionTrivChar₁ q s) := by
      rw [hderiv1, hL1_eq]
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp [hs1', hL_ne]
      ring
    have hx_one : hx_pow 1 = (x : ℂ) := by
      dsimp [hx_pow]
      simp
    have hdslope_val : dslope hx_pow 1 s = (hx_pow s - (x : ℂ)) * (s - 1)⁻¹ := by
      rw [dslope_of_ne _ hs1, slope_def_module, hx_one, smul_eq_mul, mul_comm]
    have hG_eq : G s =
        (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) * hx_pow s := by
      dsimp [G, hx_pow]
      ring
    rw [hG_eq, hlog_id]
    dsimp [F₁]
    rw [hdslope_val]
    ring
  have hc_rect_1 := contour_rect_inv_sub_one_eq_one hσ1 hc hT
  have hc_rect_x :
      (∫ u in σ₀..c, (x : ℂ) * ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
        (∫ u in σ₀..c, (x : ℂ) * ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) +
        I * (∫ t in (-T)..T, (x : ℂ) * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
        I * (∫ t in (-T)..T, (x : ℂ) * ((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      2 * Real.pi * I * (x : ℂ) := by
    simp_rw [intervalIntegral.integral_const_mul]
    let L : ℂ :=
      (∫ u in σ₀..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
        (∫ u in σ₀..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) +
        I * (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
        I * (∫ t in (-T)..T, ((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹)
    have hne : (2 * Real.pi * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have h2 : L = 2 * Real.pi * I := by
      calc L = (2 * Real.pi * I) * ((1 / (2 * Real.pi * I)) * L) := by field_simp [hne]
        _ = (2 * Real.pi * I) * 1 := by rw [hc_rect_1]
        _ = 2 * Real.pi * I := mul_one _
    calc (x : ℂ) * (∫ u in σ₀..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
          (x : ℂ) * (∫ u in σ₀..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) +
          I * ((x : ℂ) * (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹)) -
          I * ((x : ℂ) * (∫ t in (-T)..T, ((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹))
        = (x : ℂ) * L := by dsimp [L]; ring
      _ = (x : ℂ) * (2 * Real.pi * I) := by rw [h2]
      _ = 2 * Real.pi * I * (x : ℂ) := by ring
  have hcont_F₁ := hdiff_F₁.continuousOn
  have hcont_vert_pair : ∀ (α : ℝ) (hα : α ∈ Set.Icc σ₀ c) (hα1 : α ≠ 1),
      ContinuousOn (fun t : ℝ => (x : ℂ) * ((α : ℂ) + (t : ℂ) * I - 1)⁻¹) (Set.Icc (-T) T) ∧
        ContinuousOn (fun t : ℝ => F₁ ((α : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    intro α hα hα1
    constructor
    · refine Continuous.continuousOn ?_
      refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun t => ?_)
      intro h0
      have hre := congrArg Complex.re h0
      simp at hre
      exact hα1 (sub_eq_zero.mp hre)
    · exact hcont_F₁.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
        fun t ht => ⟨by simpa using hα, by simpa using ht⟩
  have hcont_horiz_pair : ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc (-T) T) (hτ0 : τ ≠ 0),
      ContinuousOn (fun u : ℝ => (x : ℂ) * ((u : ℂ) + (τ : ℂ) * I - 1)⁻¹) (Set.Icc σ₀ c) ∧
        ContinuousOn (fun u : ℝ => F₁ ((u : ℂ) + (τ : ℂ) * I)) (Set.Icc σ₀ c) := by
    intro τ hτ hτ0
    constructor
    · refine Continuous.continuousOn ?_
      refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun u => ?_)
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      exact hτ0 him
    · exact hcont_F₁.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
        fun u hu => ⟨by simpa using hu, by simpa using hτ⟩
  have hsplit_vert : ∀ (α : ℝ) (hα : α ∈ Set.Icc σ₀ c) (hα1 : α ≠ 1),
      ∫ t in (-T)..T, G ((α : ℂ) + (t : ℂ) * I) =
        (∫ t in (-T)..T, (x : ℂ) * ((α : ℂ) + (t : ℂ) * I - 1)⁻¹) +
          ∫ t in (-T)..T, F₁ ((α : ℂ) + (t : ℂ) * I) := by
    intro α hα hα1
    obtain ⟨hc1, hc2⟩ := hcont_vert_pair α hα hα1
    rw [← Set.uIcc_of_le (by linarith : -T ≤ T)] at hc1 hc2
    rw [← intervalIntegral.integral_add hc1.intervalIntegrable hc2.intervalIntegrable]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
    have hs1 : (α : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp at hre
      exact hα1 hre
    exact h_split_ne1 _ ⟨by simpa using hα, by simpa using ht⟩ hs1
  have hsplit_horiz : ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc (-T) T) (hτ0 : τ ≠ 0),
      ∫ u in σ₀..c, G ((u : ℂ) + (τ : ℂ) * I) =
        (∫ u in σ₀..c, (x : ℂ) * ((u : ℂ) + (τ : ℂ) * I - 1)⁻¹) +
          ∫ u in σ₀..c, F₁ ((u : ℂ) + (τ : ℂ) * I) := by
    intro τ hτ hτ0
    obtain ⟨hc1, hc2⟩ := hcont_horiz_pair τ hτ hτ0
    rw [← Set.uIcc_of_le hσc] at hc1 hc2
    rw [← intervalIntegral.integral_add hc1.intervalIntegrable hc2.intervalIntegrable]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hσc] at hu
    have hs1 : (u : ℂ) + (τ : ℂ) * I ≠ 1 := by
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      exact hτ0 him
    exact h_split_ne1 _ ⟨by simpa using hu, by simpa using hτ⟩ hs1
  have hrect_G :
      (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) +
        I * (∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) -
        I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) =
      2 * Real.pi * I * (x : ℂ) := by
    rw [hsplit_horiz (-T) ⟨le_rfl, by linarith⟩ (neg_ne_zero.mpr hT.ne'),
      hsplit_horiz T ⟨by linarith, le_rfl⟩ hT.ne',
      hsplit_vert c ⟨hσc, le_rfl⟩ hc.ne',
      hsplit_vert σ₀ ⟨le_rfl, hσc⟩ hσ1.ne]
    linear_combination hc_rect_x + hcauchy_F₁
  have hright_eq :
      (1 / (2 * Real.pi * I)) * (I * ∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) =
        AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T := by
    rw [← AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral_eq_div_two_pi_mul_I]
    refine congrArg (fun z : ℂ => (1 / (2 * Real.pi * I)) * (I * z)) ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    dsimp [G]
    rw [LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction (1 : DirichletCharacter ℂ q)
      (by rw [hre]; exact hc)]
  have hshifted_sub :
      AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T - (x : ℂ) =
        (1 / (2 * Real.pi * I)) *
          (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
            (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
            (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
    have hne : (2 * Real.pi * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    rw [← hright_eq]
    have halg : I * (∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) - 2 * Real.pi * I * (x : ℂ) =
        I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
      linear_combination hrect_G
    calc (1 / (2 * Real.pi * I)) * (I * ∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) - (x : ℂ)
        = (1 / (2 * Real.pi * I)) *
            (I * (∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) - 2 * Real.pi * I * (x : ℂ)) := by
          field_simp [hne]
      _ = _ := by rw [halg]
  have hG_split : ∀ (s : ℂ) (hs : s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) (hs1 : s ≠ 1),
      G s = (x : ℂ) * (s - 1)⁻¹ + F₁ s := h_split_ne1
  have hcont_vert_G : ContinuousOn (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    obtain ⟨hc1, hc2⟩ := hcont_vert_pair σ₀ ⟨le_rfl, hσc⟩ hσ1.ne
    refine (hc1.add hc2).congr fun t ht => ?_
    have hs1 : (σ₀ : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h0; have hre := congrArg Complex.re h0; simp at hre; exact hσ1.ne hre
    exact hG_split _ ⟨⟨by simp, by simp; linarith⟩, by simpa using ht⟩ hs1
  have hcont_top_G : ContinuousOn (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) (Set.Icc σ₀ c) := by
    obtain ⟨hc1, hc2⟩ := hcont_horiz_pair T ⟨by linarith, le_rfl⟩ hT.ne'
    refine (hc1.add hc2).congr fun u hu => ?_
    have hs1 : (u : ℂ) + (T : ℂ) * I ≠ 1 := by
      intro h0; have him := congrArg Complex.im h0; simp at him; exact hT.ne' him
    exact hG_split _ ⟨by simpa using hu, ⟨by simp; linarith, by simp⟩⟩ hs1
  have hcont_bot_G : ContinuousOn (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) (Set.Icc σ₀ c) := by
    obtain ⟨hc1, hc2⟩ := hcont_horiz_pair (-T) ⟨le_rfl, by linarith⟩ (neg_ne_zero.mpr hT.ne')
    refine (hc1.add hc2).congr fun u hu => ?_
    have hs1 : (u : ℂ) + ((-T : ℝ) : ℂ) * I ≠ 1 := by
      intro h0; have him := congrArg Complex.im h0; simp at him; exact hT.ne' him
    exact hG_split _ ⟨by simpa using hu, ⟨by simp, by simp; linarith⟩⟩ hs1
  have hbound_vert : ∀ t ∈ Set.Icc (-T) T,
      ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert * x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
    intro t ht
    have hnorm_s : ‖(σ₀ : ℂ) + (t : ℂ) * I‖ = Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; simp [pow_two]
    have hnorm_x : ‖(x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I)‖ = x ^ σ₀ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]; simp
    dsimp [G]
    rw [norm_div, norm_mul, hnorm_s, hnorm_x]
    gcongr
    exact hvert t ht
  have hbound_top : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz * x ^ c / T := by
    intro u hu
    have hnorm_s : T ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := by
      have him : ((u : ℂ) + (T : ℂ) * I).im = T := by simp
      calc T = |((u : ℂ) + (T : ℂ) * I).im| := by rw [him, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hnorm_x : ‖(x : ℂ) ^ ((u : ℂ) + (T : ℂ) * I)‖ ≤ x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hx hu.2
    dsimp [G]
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul (htop u hu) hnorm_x (norm_nonneg _) hB_horiz) hT hnorm_s
  have hbound_bot : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz * x ^ c / T := by
    intro u hu
    have hnorm_s : T ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := by
      have him : ((u : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
      calc T = |((u : ℂ) + ((-T : ℝ) : ℂ) * I).im| := by rw [him, abs_neg, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hnorm_x : ‖(x : ℂ) ^ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hx hu.2
    dsimp [G]
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul (hbot u hu) hnorm_x (norm_nonneg _) hB_horiz) hT hnorm_s
  rw [hshifted_sub]
  exact shifted_contour_norm_le hx_pos hσ hσc hT hB_vert hB_horiz
    hcont_vert_G hcont_top_G hcont_bot_G hbound_vert hbound_top hbound_bot

/-- Explicit Perron + contour-shift bound for `‖psiChar (N + 1 / 2) 1 - (N + 1 / 2)‖` under a
rectangular zero-free region hypothesis for `LFunctionTrivChar₁ q`. -/
theorem norm_psiChar_one_sub_le_of_rect_zeroFree (q : ℕ) [NeZero q]
    {N : ℕ} (hN : 1 ≤ N) {σ₀ c T B_vert B_horiz : ℝ} (hσ : 0 < σ₀) (hσ1 : σ₀ < 1) (hc : 1 < c)
    (hT : 0 < T) (hB_vert : 0 ≤ B_vert) (hB_horiz : 0 ≤ B_horiz)
    (hnonzero : ∀ s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T,
      DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0)
    (hvert : ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((σ₀ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert)
    (htop : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((u : ℂ) + (T : ℂ) * I) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz)
    (hbot : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((u : ℂ) + ((-T : ℝ) : ℂ) * I) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz) :
    let x : ℝ := N + 1 / 2
    ‖psiChar x (1 : DirichletCharacter ℂ q) - (x : ℂ)‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c +
        (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) +
        (2 ^ c * (4 * x) / (Real.pi * T)) * ((Real.log 4 + 4) * (2 * x)) := by
  intro x
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [show (1 : ℝ) ≤ N by exact_mod_cast hN]
  have hc_pos : 0 < c := by linarith
  have ha := LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ q) hc
  have hperron := AnalyticNumberTheory.DirichletSeries.perron_truncated_half_integer
    (a := fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (N := N) hc_pos hT ha
  have hfl : ⌊x⌋₊ = N := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hpsi_eq : psiChar x (1 : DirichletCharacter ℂ q) =
      ∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) := by
    rw [psiChar, hfl]
  have hshift := norm_dirichletContourIntegral_trivChar_sub_le q hx1 hσ hσ1 hc hT hB_vert hB_horiz
    hnonzero hvert htop hbot
  have hterm := tsum_norm_LSeries_term_twist_le (1 : DirichletCharacter ℂ q) hc
  have htail : ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖(1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)‖ ≤
      (Real.log 4 + 4) * (2 * x) := by
    have h2N : ((2 * N + 1 : ℕ) : ℝ) = 2 * x := by dsimp [x]; push_cast; ring
    simpa [h2N] using sum_norm_twist_Icc_le (1 : DirichletCharacter ℂ q) (2 * N + 1)
  have htri : ‖psiChar x (1 : DirichletCharacter ℂ q) - (x : ℂ)‖ ≤
      ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T - (x : ℂ)‖ +
        ‖AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
          (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T -
            psiChar x (1 : DirichletCharacter ℂ q)‖ := by
    have hid : psiChar x (1 : DirichletCharacter ℂ q) - (x : ℂ) =
        (AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
            (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T - (x : ℂ)) -
          (AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
            (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T -
              psiChar x (1 : DirichletCharacter ℂ q)) := by ring
    calc ‖psiChar x (1 : DirichletCharacter ℂ q) - (x : ℂ)‖ =
          ‖(AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
              (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T - (x : ℂ)) -
            (AnalyticNumberTheory.DirichletSeries.dirichletContourIntegral
              (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) x c T -
                psiChar x (1 : DirichletCharacter ℂ q))‖ := by rw [← hid]
      _ ≤ _ := norm_sub_le _ _
  rw [hpsi_eq] at htri ⊢
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : (x ^ c / (Real.pi * T * Real.log 2)) *
        ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ))
          (c : ℂ) n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) := by
    gcongr
  have h2 : (2 ^ c * (4 * x) / (Real.pi * T)) *
        ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖(1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)‖ ≤
      (2 ^ c * (4 * x) / (Real.pi * T)) * ((Real.log 4 + 4) * (2 * x)) := by
    gcongr
  dsimp only at hperron
  linarith

end AnalyticNumberTheory.PrimeDistribution