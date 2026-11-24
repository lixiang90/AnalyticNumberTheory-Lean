import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import AnalyticNumberTheory.DirichletSeries.Operations
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Dirichlet Hyperbola Method and Elementary Average Orders

This file develops the Dirichlet hyperbola summation method and derives the classical elementary
asymptotic formulas for arithmetic functions:

- General **Dirichlet hyperbola method identities** (`sum_Icc_convolution_add_rectangle`,
  `dirichlet_hyperbola`, `dirichlet_hyperbola_sqrt`, `dirichlet_hyperbola_self_sqrt`, and
  `ArithmeticFunction` variants) for arbitrary real or natural split parameters `U, V` with
  `U * V = x` and the symmetric specialization `U = V = √x`.
- **Dirichlet's divisor theorem**:
  `divisorSum x := ∑_{1 ≤ n ≤ x} d(n) = x * log x + (2 * γ - 1) * x + Δ(x)`,
  with the explicit remainder bound `|Δ(x)| ≤ 4 * √x` for all `x ≥ 0`, and `Δ =O[atTop] √·`.
- Average order of the sum-of-divisors function:
  `∑_{1 ≤ n ≤ x} σ₁(n) = (π² / 12) * x² + O(x * log x)` with explicit error bound.
- Average order of Euler's totient function (via `φ = μ * id`):
  `∑_{1 ≤ n ≤ x} φ(n) = (3 / π²) * x² + O(x * log x)` with explicit error bound.
- Squarefree counting function (via `μ(n)² = ∑_{d² ∣ n} μ(d)`):
  `∑_{1 ≤ n ≤ x} μ(n)² = (6 / π²) * x + O(√x)` with explicit remainder bound `|E(x)| ≤ 3 * √x`.
-/

noncomputable section

open Finset Filter Asymptotics
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.sigma
  LSeries.notation Topology
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DivisorProblems

/-! ### Partial Sums and the General Dirichlet Hyperbola Method -/

section PartialSumsAndHyperbola

/-- Partial sum of a sequence `f : ℕ → R` over positive integers `1 ≤ n ≤ x`. -/
def partialSum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (x : ℝ) : R :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n

/-- At a natural number `N`, `partialSum f N` is `∑ n ∈ Finset.Icc 1 N, f n`. -/
@[simp]
theorem partialSum_natCast {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    partialSum f (N : ℝ) = ∑ n ∈ Finset.Icc 1 N, f n := by
  simp [partialSum]

/-- `partialSum f x` expressed over `Finset.Ioc 0 ⌊x⌋₊`. -/
theorem partialSum_eq_sum_Ioc {R : Type*} [AddCommMonoid R] (f : ℕ → R) (x : ℝ) :
    partialSum f x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n := by
  rw [partialSum, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- When `f 0 = 0`, `partialSum f x` equals the sum over `Finset.range (⌊x⌋₊ + 1)`. -/
theorem partialSum_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ℕ → R} (hf0 : f 0 = 0)
    (x : ℝ) : partialSum f x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n := by
  rw [partialSum, Finset.range_eq_Ico,
    ← Finset.insert_Ico_add_one_left_eq_Ico (Nat.zero_lt_succ _), Finset.sum_insert (by simp),
    hf0, zero_add, zero_add]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp [Finset.mem_Icc, Finset.mem_Ico]

/-- `partialSum f x` vanishes for `x < 1`. -/
theorem partialSum_of_lt_one {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : x < 1) :
    partialSum f x = 0 := by
  rw [partialSum, Nat.floor_eq_zero.mpr hx]
  simp

/-- `partialSum f x` vanishes for `x ≤ 0`. -/
theorem partialSum_eq_zero_of_nonpos {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ}
    (hx : x ≤ 0) : partialSum f x = 0 :=
  partialSum_of_lt_one f (hx.trans_lt zero_lt_one)

/-- The partial sum of the constant sequence `1` over `1 ≤ n ≤ x` is `⌊x⌋₊`. -/
@[simp]
theorem partialSum_const_one {R : Type*} [AddCommMonoidWithOne R] (x : ℝ) :
    partialSum (fun _ : ℕ => (1 : R)) x = (⌊x⌋₊ : R) := by
  simp [partialSum]

/-- For `0 ≤ x` and `1 ≤ d`, `⌊x / d⌋₊ = ⌊x⌋₊ / d`. -/
theorem nat_floor_div_nat {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 1 ≤ d) :
    ⌊x / (d : ℝ)⌋₊ = ⌊x⌋₊ / d := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hiff : ∀ k : ℕ, k ≤ ⌊x / (d : ℝ)⌋₊ ↔ k ≤ ⌊x⌋₊ / d := fun k => by
    rw [Nat.le_floor_iff (div_nonneg hx hd0.le), le_div_iff₀ hd0, ← Nat.cast_mul,
      ← Nat.le_floor_iff hx, Nat.le_div_iff_mul_le hd]
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

private lemma sum_Icc_convolution_eq_sum_S {R : Type*} [Semiring R] (f g : ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (f ⍟ g) n =
      ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
        f p.1 * g p.2 := by
  let S := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
  have hmaps : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 N := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.1.1.1 hp.1.2.1, hp.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [LSeries.convolution_def]
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨d, m⟩
  simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨hdm, _⟩
    have hd0 : 1 ≤ d := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hdm ▸ hn0))
    have hm0 : 1 ≤ m := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hdm ▸ hn0))
    refine ⟨⟨⟨⟨hd0, ?_⟩, ⟨hm0, ?_⟩⟩, ?_⟩, hdm⟩
    · exact (Nat.le_mul_of_pos_right d hm0).trans (hdm ▸ hnN)
    · exact (Nat.le_mul_of_pos_left m hd0).trans (hdm ▸ hnN)
    · exact hdm ▸ hnN
  · rintro ⟨_, hdm⟩
    exact ⟨hdm, hn0⟩

/-- Single-sum rearrangement for the partial sum of a Dirichlet convolution:
`∑_{1 ≤ n ≤ N} (f ⍟ g)(n) = ∑_{1 ≤ d ≤ N} f(d) * ∑_{1 ≤ m ≤ N / d} g(m)`. -/
theorem sum_Icc_convolution_eq_sum_sum_div {R : Type*} [Semiring R] (f g : ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (f ⍟ g) n =
      ∑ d ∈ Finset.Icc 1 N, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m := by
  rw [sum_Icc_convolution_eq_sum_S]
  have hsigma :
      ∑ d ∈ Finset.Icc 1 N, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m =
        ∑ p ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)), f p.1 * g p.2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_sigma' (Finset.Icc 1 N) (fun d => Finset.Icc 1 (N / d))
      (fun d m => f d * g m)
  rw [hsigma]
  symm
  refine Finset.sum_bij (fun p _ => (p.1, p.2)) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨d, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    have hmul : d * m ≤ N := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hp.1.1).mp hp.2.2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hp.1.1, (Nat.le_mul_of_pos_right d hp.2.1).trans hmul⟩,
      ⟨hp.2.1, (Nat.le_mul_of_pos_left m hp.1.1).trans hmul⟩⟩, hmul⟩
  · rintro ⟨d₁, m₁⟩ _ ⟨d₂, m₂⟩ _ h
    cases h
    rfl
  · rintro ⟨d, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    refine ⟨⟨d, m⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨hp.1.1, hp.1.2.1, (Nat.le_div_iff_mul_le hp.1.1.1).mpr ?_⟩
    simpa only [mul_comm] using hp.2

/-- Real-parameter partial sum rearrangement for a Dirichlet convolution:
`partialSum (f ⍟ g) x = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, f d * partialSum g (x / d)`. -/
theorem partialSum_convolution_eq_sum {R : Type*} [Semiring R] (f g : ℕ → R) (x : ℝ) :
    partialSum (f ⍟ g) x = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, f d * partialSum g (x / d) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [partialSum, sum_Icc_convolution_eq_sum_sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [partialSum, nat_floor_div_nat hx (Finset.mem_Icc.mp hd).1]
  · simp [partialSum, Nat.floor_of_nonpos hx.le]

/-- The two strips below the hyperbola cover all positive lattice points with product at most
`N`. Their overlap is the rectangle `[1,u] × [1,v]`. Counting the rectangle on the left
gives a formula over any semiring, including natural-number weights. -/
theorem sum_Icc_convolution_add_rectangle {R : Type*} [Semiring R] (f g : ℕ → R)
    {u v N : ℕ} (huv : u * v ≤ N) (hN : N < (u + 1) * (v + 1)) :
    (∑ n ∈ Finset.Icc 1 N, (f ⍟ g) n) +
        (∑ d ∈ Finset.Icc 1 u, f d) * (∑ m ∈ Finset.Icc 1 v, g m) =
      (∑ d ∈ Finset.Icc 1 u, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m) +
        (∑ m ∈ Finset.Icc 1 v, (∑ d ∈ Finset.Icc 1 (N / m), f d) * g m) := by
  let S := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
  let A := S.filter (fun p => p.1 ≤ u)
  let B := S.filter (fun p => p.2 ≤ v)
  have hS : ∑ n ∈ Finset.Icc 1 N, (f ⍟ g) n = ∑ p ∈ S, f p.1 * g p.2 :=
    sum_Icc_convolution_eq_sum_S f g N
  have hAB : A ∪ B = S := by
    ext ⟨d, m⟩
    simp only [A, B, S, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hd : d ≤ u
      · exact Or.inl ⟨h, hd⟩
      · right
        refine ⟨h, ?_⟩
        by_contra! hm
        have hd1 : u + 1 ≤ d := Nat.lt_of_not_ge hd
        have hm1 : v + 1 ≤ m := hm
        have hmul : (u + 1) * (v + 1) ≤ d * m := Nat.mul_le_mul hd1 hm1
        omega
  have hAinterB : A ∩ B = Finset.Icc 1 u ×ˢ Finset.Icc 1 v := by
    ext ⟨d, m⟩
    simp only [A, B, S, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨⟨hd1, _⟩, ⟨hm1, _⟩⟩, _⟩, hdu⟩, ⟨_, hmv⟩⟩
      exact ⟨⟨hd1, hdu⟩, ⟨hm1, hmv⟩⟩
    · rintro ⟨⟨hd1, hdu⟩, ⟨hm1, hmv⟩⟩
      have hdm : d * m ≤ N := (Nat.mul_le_mul hdu hmv).trans huv
      have hdN : d ≤ N := (Nat.le_mul_of_pos_right d hm1).trans hdm
      have hmN : m ≤ N := (Nat.le_mul_of_pos_left m hd1).trans hdm
      exact ⟨⟨⟨⟨⟨hd1, hdN⟩, ⟨hm1, hmN⟩⟩, hdm⟩, hdu⟩, ⟨⟨⟨⟨hd1, hdN⟩, ⟨hm1, hmN⟩⟩, hdm⟩, hmv⟩⟩
  have hUI := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun p : ℕ × ℕ => f p.1 * g p.2)
  rw [hAB, hAinterB, ← hS] at hUI
  have hsumA : ∑ p ∈ A, f p.1 * g p.2 =
      ∑ d ∈ Finset.Icc 1 u, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m := by
    have hsigma :
        ∑ d ∈ Finset.Icc 1 u, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m =
          ∑ p ∈ (Finset.Icc 1 u).sigma (fun d => Finset.Icc 1 (N / d)), f p.1 * g p.2 := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_sigma' (Finset.Icc 1 u) (fun d => Finset.Icc 1 (N / d))
        (fun d m => f d * g m)
    rw [hsigma]
    symm
    refine Finset.sum_bij (fun p _ => (p.1, p.2)) ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨d, m⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
      have hmul : d * m ≤ N := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hp.1.1).mp hp.2.2
      simp only [A, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨⟨hp.1.1, (Nat.le_mul_of_pos_right d hp.2.1).trans hmul⟩,
        ⟨hp.2.1, (Nat.le_mul_of_pos_left m hp.1.1).trans hmul⟩⟩, hmul⟩, hp.1.2⟩
    · rintro ⟨d₁, m₁⟩ _ ⟨d₂, m₂⟩ _ h
      cases h
      rfl
    · rintro ⟨d, m⟩ hp
      simp only [A, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      refine ⟨⟨d, m⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_Icc]
      refine ⟨⟨hp.1.1.1.1, hp.2⟩, hp.1.1.2.1, (Nat.le_div_iff_mul_le hp.1.1.1.1).mpr ?_⟩
      simpa only [mul_comm] using hp.1.2
  have hsumB : ∑ p ∈ B, f p.1 * g p.2 =
      ∑ m ∈ Finset.Icc 1 v, (∑ d ∈ Finset.Icc 1 (N / m), f d) * g m := by
    have hsigma :
        ∑ m ∈ Finset.Icc 1 v, (∑ d ∈ Finset.Icc 1 (N / m), f d) * g m =
          ∑ p ∈ (Finset.Icc 1 v).sigma (fun m => Finset.Icc 1 (N / m)), f p.2 * g p.1 := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_sigma' (Finset.Icc 1 v) (fun m => Finset.Icc 1 (N / m))
        (fun m d => f d * g m)
    rw [hsigma]
    symm
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨m, d⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
      have hmul : d * m ≤ N := (Nat.le_div_iff_mul_le hp.1.1).mp hp.2.2
      simp only [B, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨⟨hp.2.1, (Nat.le_mul_of_pos_right d hp.1.1).trans hmul⟩,
        ⟨hp.1.1, (Nat.le_mul_of_pos_left m hp.2.1).trans hmul⟩⟩, hmul⟩, hp.1.2⟩
    · rintro ⟨m₁, d₁⟩ _ ⟨m₂, d₂⟩ _ h
      cases h
      rfl
    · rintro ⟨d, m⟩ hp
      simp only [B, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      refine ⟨⟨m, d⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_Icc]
      refine ⟨⟨hp.1.1.2.1, hp.2⟩, hp.1.1.1.1, (Nat.le_div_iff_mul_le hp.1.1.2.1).mpr ?_⟩
      simpa only [mul_comm] using hp.1.2
  have hsumInter :
      ∑ p ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v, f p.1 * g p.2 =
        (∑ d ∈ Finset.Icc 1 u, f d) * (∑ m ∈ Finset.Icc 1 v, g m) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
  simpa only [hsumA, hsumB, hsumInter] using hUI

/-- The discrete Dirichlet hyperbola identity over a ring. The factors in every summand
have the same order as in the convolution, so multiplication may be noncommutative. -/
theorem sum_Icc_convolution_hyperbola_ring {R : Type*} [Ring R] (f g : ℕ → R)
    {u v N : ℕ} (huv : u * v ≤ N) (hN : N < (u + 1) * (v + 1)) :
    ∑ n ∈ Finset.Icc 1 N, (f ⍟ g) n =
      (∑ d ∈ Finset.Icc 1 u, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m) +
        (∑ m ∈ Finset.Icc 1 v, (∑ d ∈ Finset.Icc 1 (N / m), f d) * g m) -
          (∑ d ∈ Finset.Icc 1 u, f d) * (∑ m ∈ Finset.Icc 1 v, g m) :=
  eq_sub_of_add_eq (sum_Icc_convolution_add_rectangle f g huv hN)

/-- **General discrete Dirichlet hyperbola identity** (`CommRing` version):
for `u * v ≤ N < (u + 1) * (v + 1)`,
`∑_{1 ≤ n ≤ N} (f ⍟ g)(n) = ∑_{d ≤ u} f(d) ∑_{m ≤ N/d} g(m) + ∑_{m ≤ v} g(m) ∑_{d ≤ N/m} f(d) - (∑_{d ≤ u} f(d)) (∑_{m ≤ v} g(m))`. -/
theorem sum_Icc_convolution_hyperbola {R : Type*} [CommRing R] (f g : ℕ → R)
    {u v N : ℕ} (huv : u * v ≤ N) (hN : N < (u + 1) * (v + 1)) :
    ∑ n ∈ Finset.Icc 1 N, (f ⍟ g) n =
      (∑ d ∈ Finset.Icc 1 u, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m) +
        (∑ m ∈ Finset.Icc 1 v, g m * ∑ d ∈ Finset.Icc 1 (N / m), f d) -
          (∑ d ∈ Finset.Icc 1 u, f d) * (∑ m ∈ Finset.Icc 1 v, g m) := by
  have h := sum_Icc_convolution_hyperbola_ring f g huv hN
  simpa only [mul_comm (g _)] using h

/-- **General Dirichlet hyperbola method identity** (`Ring` version) for arbitrary real split
parameters `U, V ≥ 0` with `U * V = x`:
`partialSum (f ⍟ g) x = ∑_{d ≤ U} f(d) G(x/d) + ∑_{m ≤ V} F(x/m) g(m) - F(U) G(V)`. -/
theorem dirichlet_hyperbola_ring {R : Type*} [Ring R] (f g : ℕ → R) {x U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUV : U * V = x) :
    partialSum (f ⍟ g) x =
      (∑ d ∈ Finset.Icc 1 ⌊U⌋₊, f d * partialSum g (x / d)) +
        (∑ m ∈ Finset.Icc 1 ⌊V⌋₊, partialSum f (x / m) * g m) -
          partialSum f U * partialSum g V := by
  have hx : 0 ≤ x := hUV ▸ mul_nonneg hU hV
  have huv : ⌊U⌋₊ * ⌊V⌋₊ ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff hx, Nat.cast_mul, ← hUV]
    exact mul_le_mul (Nat.floor_le hU) (Nat.floor_le hV) (Nat.cast_nonneg _) hU
  have hN : ⌊x⌋₊ < (⌊U⌋₊ + 1) * (⌊V⌋₊ + 1) := by
    have hxlt : x < ((⌊U⌋₊ + 1 : ℕ) : ℝ) * ((⌊V⌋₊ + 1 : ℕ) : ℝ) := by
      rw [← hUV]
      push_cast
      exact mul_lt_mul'' (Nat.lt_floor_add_one U) (Nat.lt_floor_add_one V) hU hV
    exact_mod_cast (Nat.floor_le hx).trans_lt hxlt
  have h := sum_Icc_convolution_hyperbola_ring f g huv hN
  have h1 : ∑ d ∈ Finset.Icc 1 ⌊U⌋₊, f d * ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), g m =
      ∑ d ∈ Finset.Icc 1 ⌊U⌋₊, f d * partialSum g (x / d) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [partialSum, nat_floor_div_nat hx (Finset.mem_Icc.mp hd).1]
  have h2 : ∑ m ∈ Finset.Icc 1 ⌊V⌋₊, (∑ d ∈ Finset.Icc 1 (⌊x⌋₊ / m), f d) * g m =
      ∑ m ∈ Finset.Icc 1 ⌊V⌋₊, partialSum f (x / m) * g m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [partialSum, nat_floor_div_nat hx (Finset.mem_Icc.mp hm).1]
  simp only [partialSum]
  rw [h]
  simp only [partialSum] at h1 h2
  rw [h1, h2]

/-- **General Dirichlet hyperbola method identity** (`CommRing` version) for arbitrary real split
parameters `U, V ≥ 0` with `U * V = x`:
`partialSum (f ⍟ g) x = ∑_{d ≤ U} f(d) G(x/d) + ∑_{m ≤ V} g(m) F(x/m) - F(U) G(V)`. -/
theorem dirichlet_hyperbola {R : Type*} [CommRing R] (f g : ℕ → R) {x U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUV : U * V = x) :
    partialSum (f ⍟ g) x =
      (∑ d ∈ Finset.Icc 1 ⌊U⌋₊, f d * partialSum g (x / d)) +
        (∑ m ∈ Finset.Icc 1 ⌊V⌋₊, g m * partialSum f (x / m)) -
          partialSum f U * partialSum g V := by
  have h := dirichlet_hyperbola_ring f g hU hV hUV
  simpa only [mul_comm (g _)] using h

/-- **Symmetric Dirichlet hyperbola method identity** with split `U = V = √x`:
`partialSum (f ⍟ g) x = ∑_{d ≤ √x} f(d) G(x/d) + ∑_{m ≤ √x} g(m) F(x/m) - F(√x) G(√x)`. -/
theorem dirichlet_hyperbola_sqrt {R : Type*} [CommRing R] (f g : ℕ → R) (x : ℝ) :
    partialSum (f ⍟ g) x =
      (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, f d * partialSum g (x / d)) +
        (∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, g m * partialSum f (x / m)) -
          partialSum f (Real.sqrt x) * partialSum g (Real.sqrt x) := by
  rcases le_or_gt 0 x with hx | hx
  · exact dirichlet_hyperbola f g (Real.sqrt_nonneg x) (Real.sqrt_nonneg x) (Real.mul_self_sqrt hx)
  · simp [partialSum_eq_zero_of_nonpos _ hx.le, Real.sqrt_eq_zero_of_nonpos hx.le,
      partialSum_of_lt_one _ zero_lt_one]

/-- **Symmetric self-convolution Dirichlet hyperbola identity** (`f ⍟ f` with `U = V = √x`):
`partialSum (f ⍟ f) x = 2 * ∑_{d ≤ √x} f(d) F(x/d) - F(√x)²`. -/
theorem dirichlet_hyperbola_self_sqrt {R : Type*} [CommRing R] (f : ℕ → R) (x : ℝ) :
    partialSum (f ⍟ f) x =
      2 * (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, f d * partialSum f (x / d)) -
        partialSum f (Real.sqrt x) ^ 2 := by
  rw [dirichlet_hyperbola_sqrt f f x, two_mul, sq]

/-- **General Dirichlet hyperbola method** for `ArithmeticFunction R` with arbitrary `U, V ≥ 0`
satisfying `U * V = x`. -/
theorem dirichlet_hyperbola_arith {R : Type*} [CommRing R] (f g : ArithmeticFunction R)
    {x U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUV : U * V = x) :
    partialSum (f * g) x =
      (∑ d ∈ Finset.Icc 1 ⌊U⌋₊, f d * partialSum g (x / d)) +
        (∑ m ∈ Finset.Icc 1 ⌊V⌋₊, g m * partialSum f (x / m)) -
          partialSum f U * partialSum g V := by
  simpa only [← ArithmeticFunction.coe_mul] using dirichlet_hyperbola f g hU hV hUV

/-- **Symmetric Dirichlet hyperbola method** for `ArithmeticFunction R` with split `U = V = √x`. -/
theorem dirichlet_hyperbola_arith_sqrt {R : Type*} [CommRing R] (f g : ArithmeticFunction R)
    (x : ℝ) :
    partialSum (f * g) x =
      (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, f d * partialSum g (x / d)) +
        (∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, g m * partialSum f (x / m)) -
          partialSum f (Real.sqrt x) * partialSum g (Real.sqrt x) := by
  simpa only [← ArithmeticFunction.coe_mul] using dirichlet_hyperbola_sqrt f g x

end PartialSumsAndHyperbola

/-! ### Dirichlet's Divisor Theorem -/

section DirichletDivisorTheorem

/-- Counting lattice points with positive coordinates and product at most `N` by the two
strips of width `Nat.sqrt N`. This natural-number formula also holds when `N = 0`. -/
theorem sum_card_divisors_add_sqrt_sq (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, #n.divisors) + N.sqrt ^ 2 =
      2 * ∑ d ∈ Finset.Icc 1 N.sqrt, N / d := by
  have hconv (n : ℕ) :
      ((fun _ : ℕ => (1 : ℕ)) ⍟ (fun _ : ℕ => (1 : ℕ))) n = #n.divisors := by
    rw [LSeries.convolution_def]
    change (∑ _p ∈ n.divisorsAntidiagonal, 1 * 1) = #n.divisors
    rw [← Nat.map_div_right_divisors]
    simp
  simpa [hconv, two_mul, sq] using
    sum_Icc_convolution_add_rectangle (fun _ : ℕ => (1 : ℕ)) (fun _ : ℕ => (1 : ℕ))
      (Nat.sqrt_le N) (Nat.lt_succ_sqrt N)

/-- The divisor-count summatory function `D(x) = ∑_{1 ≤ n ≤ x} d(n)`. -/
def divisorSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((σ 0 n : ℕ) : ℝ)

/-- `divisorSum x` expressed via `Nat.divisors.card`. -/
theorem divisorSum_eq_sum_card_divisors (x : ℝ) :
    divisorSum x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (#n.divisors : ℝ) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ArithmeticFunction.sigma_zero_apply]

/-- `divisorSum x` equals the partial sum of the self-convolution of `1`. -/
theorem divisorSum_eq_partialSum_conv (x : ℝ) :
    divisorSum x = partialSum ((fun _ : ℕ => (1 : ℝ)) ⍟ (fun _ : ℕ => (1 : ℝ))) x := by
  rw [divisorSum, partialSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ArithmeticFunction.sigma_zero_apply, LSeries.convolution_def]
  have hcard : (#n.divisors : ℝ) = ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.card_map ⟨fun d => (d, n / d), fun _ _ => congr_arg Prod.fst⟩,
      Nat.map_div_right_divisors]
  simpa only [one_mul] using hcard

/-- Exact hyperbola identity for the divisor summatory function:
`D(x) = 2 * ∑_{1 ≤ d ≤ √x} ⌊x / d⌋₊ - ⌊√x⌋₊²`. -/
theorem divisorSum_eq_two_sum_floor_sub_sq (x : ℝ) :
    divisorSum x =
      2 * (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / d⌋₊ : ℝ)) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 := by
  rw [divisorSum_eq_partialSum_conv, dirichlet_hyperbola_self_sqrt (fun _ : ℕ => (1 : ℝ)) x]
  simp only [one_mul, partialSum_const_one]

/-- The error term in Dirichlet's divisor theorem:
`Δ(x) = D(x) - x * log x - (2 * γ - 1) * x`. -/
def divisorError (x : ℝ) : ℝ :=
  divisorSum x - x * Real.log x - (2 * Real.eulerMascheroniConstant - 1) * x

private lemma sqrt_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hx

/-- Explicit `O(√x)` error bound for Dirichlet's divisor theorem when `1 ≤ x`:
`|Δ(x)| ≤ 4 * √x`. -/
theorem abs_divisorError_le_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    |divisorError x| ≤ 4 * Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsx1 : 1 ≤ Real.sqrt x := sqrt_one_le hx
  have hsx0 : 0 < Real.sqrt x := zero_lt_one.trans_le hsx1
  have hD := divisorSum_eq_two_sum_floor_sub_sq x
  have hsum_floor :
      ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / d⌋₊ : ℝ) =
        x * (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (d : ℝ)⁻¹) -
          ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d) := by
    have hterm : ∀ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
        (⌊x / d⌋₊ : ℝ) = x * (d : ℝ)⁻¹ - Int.fract (x / d) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
      rw [← Int.cast_natCast, Int.natCast_floor_eq_floor (div_nonneg hx0.le hd0.le)]
      have hf := Int.floor_add_fract (x / d)
      rw [div_eq_mul_inv] at hf ⊢
      linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsqrt_floor :
      (⌊Real.sqrt x⌋₊ : ℝ) = Real.sqrt x - Int.fract (Real.sqrt x) := by
    rw [← Int.cast_natCast, Int.natCast_floor_eq_floor hsx0.le]
    have hf := Int.floor_add_fract (Real.sqrt x)
    linarith
  have hsq :
      (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 =
        x - (2 * Real.sqrt x * Int.fract (Real.sqrt x) - (Int.fract (Real.sqrt x)) ^ 2) := by
    rw [hsqrt_floor]
    have hss : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
    linarith [show (Real.sqrt x - Int.fract (Real.sqrt x)) ^ 2 =
      (Real.sqrt x) ^ 2 - 2 * Real.sqrt x * Int.fract (Real.sqrt x) +
        (Int.fract (Real.sqrt x)) ^ 2 by ring]
  let H := ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (d : ℝ)⁻¹
  let E := H - (Real.log (Real.sqrt x) + Real.eulerMascheroniConstant)
  have hE : |E| ≤ (Real.sqrt x)⁻¹ := abs_sum_inv_sub_log_sub_gamma_le hsx1
  have hH_eq : 2 * x * H =
      x * Real.log x + 2 * Real.eulerMascheroniConstant * x + 2 * x * E := by
    have hlog_sqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
    have hE_eq : H = Real.log x / 2 + Real.eulerMascheroniConstant + E := by
      dsimp only [E]
      linarith [hlog_sqrt]
    rw [hE_eq]
    ring
  have hΔ_eq :
      divisorError x =
        2 * x * E - 2 * (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d)) +
          (2 * Real.sqrt x * Int.fract (Real.sqrt x) - (Int.fract (Real.sqrt x)) ^ 2) := by
    rw [divisorError, hD, hsum_floor, hsq]
    have hmul : 2 * (x * H - ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d)) =
        2 * x * H - 2 * ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d) := by ring
    rw [hmul, hH_eq]
    ring
  have h2xE : |2 * x * E| ≤ 2 * Real.sqrt x := by
    rw [abs_mul, abs_of_pos (mul_pos zero_lt_two hx0)]
    have hxsq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
    calc 2 * x * |E|
        ≤ 2 * x * (Real.sqrt x)⁻¹ := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 2 * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by rw [← hxsq]
      _ = 2 * Real.sqrt x := by field_simp [hsx0.ne']
  have hfract_sum_nonneg :
      0 ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d) :=
    Finset.sum_nonneg fun d _ => Int.fract_nonneg _
  have hfract_sum_le :
      ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d) ≤ Real.sqrt x := by
    calc ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, Int.fract (x / d)
        ≤ ∑ _d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (1 : ℝ) :=
          Finset.sum_le_sum fun d _ => (Int.fract_lt_one _).le
      _ = (⌊Real.sqrt x⌋₊ : ℝ) := by simp
      _ ≤ Real.sqrt x := Nat.floor_le hsx0.le
  have hdiag_nonneg :
      0 ≤ 2 * Real.sqrt x * Int.fract (Real.sqrt x) - (Int.fract (Real.sqrt x)) ^ 2 := by
    have h0 : 0 ≤ Int.fract (Real.sqrt x) := Int.fract_nonneg _
    have h1 : Int.fract (Real.sqrt x) ≤ 2 * Real.sqrt x := by
      linarith [Int.fract_lt_one (Real.sqrt x)]
    nlinarith
  have hdiag_le :
      2 * Real.sqrt x * Int.fract (Real.sqrt x) - (Int.fract (Real.sqrt x)) ^ 2 ≤
        2 * Real.sqrt x := by
    have h0 : 0 ≤ (Int.fract (Real.sqrt x)) ^ 2 := sq_nonneg _
    have h1 : 2 * Real.sqrt x * Int.fract (Real.sqrt x) ≤ 2 * Real.sqrt x * 1 :=
      mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (by positivity)
    linarith
  rw [hΔ_eq, abs_le]
  rw [abs_le] at h2xE
  constructor <;> linarith

/-- Explicit `O(√x)` error bound for Dirichlet's divisor theorem for all `0 ≤ x`:
`|Δ(x)| ≤ 4 * √x`. -/
theorem abs_divisorError_le {x : ℝ} (hx : 0 ≤ x) :
    |divisorError x| ≤ 4 * Real.sqrt x := by
  rcases le_or_gt 1 x with hx1 | hx1
  · exact abs_divisorError_le_of_one_le hx1
  · rcases eq_or_lt_of_le hx with rfl | hx0
    · simp [divisorError, divisorSum]
    · have hsum0 : divisorSum x = 0 := by
        rw [divisorSum, Nat.floor_eq_zero.mpr hx1]
        simp
      have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hsx1 : Real.sqrt x < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt hx0.le hx1
      have hlog_neg_le : -(x * Real.log x) ≤ 2 * Real.sqrt x := by
        have hinv : Real.log ((Real.sqrt x)⁻¹) ≤ (Real.sqrt x)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (inv_pos.mpr hsx0)
        have hmul : Real.sqrt x * (-Real.log (Real.sqrt x)) ≤ 1 := by
          rw [← Real.log_inv]
          calc Real.sqrt x * Real.log ((Real.sqrt x)⁻¹)
              ≤ Real.sqrt x * ((Real.sqrt x)⁻¹ - 1) :=
                mul_le_mul_of_nonneg_left hinv hsx0.le
            _ = 1 - Real.sqrt x := by
                rw [mul_sub, mul_inv_cancel₀ hsx0.ne', mul_one]
            _ ≤ 1 := by linarith
        have hlog_x : Real.log x = 2 * Real.log (Real.sqrt x) := by
          rw [Real.log_sqrt hx0.le]
          ring
        have hxsq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
        have hmain : -(x * Real.log x) =
            2 * Real.sqrt x * (Real.sqrt x * (-Real.log (Real.sqrt x))) := by
          rw [hlog_x]
          nth_rw 1 [hxsq]
          ring
        rw [hmain]
        calc 2 * Real.sqrt x * (Real.sqrt x * (-Real.log (Real.sqrt x)))
            ≤ 2 * Real.sqrt x * 1 := mul_le_mul_of_nonneg_left hmul (by positivity)
          _ = 2 * Real.sqrt x := mul_one _
      have hlog_nonpos : x * Real.log x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hx0.le (Real.log_nonpos hx0.le hx1.le)
      have hgamma_lo : 0 < 2 * Real.eulerMascheroniConstant - 1 := by
        linarith [Real.one_half_lt_eulerMascheroniConstant]
      have hgamma_hi : 2 * Real.eulerMascheroniConstant - 1 < 1 / 3 := by
        linarith [Real.eulerMascheroniConstant_lt_two_thirds]
      have hx_le_sqrt : x ≤ Real.sqrt x := by
        have hxsq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
        conv_lhs => rw [hxsq]
        exact mul_le_of_le_one_right hsx0.le hsx1.le
      have h2_le : (2 * Real.eulerMascheroniConstant - 1) * x ≤ Real.sqrt x := by
        calc (2 * Real.eulerMascheroniConstant - 1) * x
            ≤ 1 * x := mul_le_mul_of_nonneg_right (by linarith) hx0.le
          _ = x := one_mul x
          _ ≤ Real.sqrt x := hx_le_sqrt
      have h2_nonneg : 0 ≤ (2 * Real.eulerMascheroniConstant - 1) * x :=
        mul_nonneg hgamma_lo.le hx0.le
      rw [divisorError, hsum0, zero_sub, abs_le]
      constructor <;> linarith

/-- **Dirichlet's divisor theorem** in Big-O form:
`∑_{1 ≤ n ≤ x} d(n) = x * log x + (2 * γ - 1) * x + O(√x)`. -/
theorem divisorError_isBigO_sqrt :
    divisorError =O[atTop] Real.sqrt := by
  refine isBigO_iff.mpr ⟨4, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  exact abs_divisorError_le hx

/-- **Dirichlet's divisor theorem** with `x^(1/2)` Big-O error term. -/
theorem divisorError_isBigO_rpow_half :
    divisorError =O[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
  refine divisorError_isBigO_sqrt.congr_right ?_
  intro x
  rw [Real.sqrt_eq_rpow]

end DirichletDivisorTheorem

/-! ### Series Helpers for Average Orders -/

section SeriesHelpers

/-- Summability of `1 / n²` over `ℕ`. -/
theorem summable_one_div_sq : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
  hasSum_zeta_two.summable

/-- Exact Basel sum `∑' n : ℕ, 1 / n² = π² / 6`. -/
theorem tsum_one_div_sq : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

/-- Summability of `μ(n) / n²` over `ℕ`. -/
theorem summable_moebius_div_sq : Summable (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ 2) := by
  refine summable_one_div_sq.of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have hmu : (|(μ n : ℤ)| : ℝ) ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  simpa using hmu

/-- Exact evaluation `∑' n : ℕ, μ(n) / n² = 6 / π²` from `1 / ζ(2) = L(2, μ)`. -/
theorem tsum_moebius_div_sq : ∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 = 6 / Real.pi ^ 2 := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hL := LSeries_moebius_eq_one_div_riemannZeta hs
  rw [riemannZeta_two] at hL
  have htsum_eq : LSeries ↗μ 2 = ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_two]
      push_cast
      rfl
  have hdiv : (1 : ℂ) / ((Real.pi : ℂ) ^ 2 / 6) = (((6 / Real.pi ^ 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [htsum_eq, hdiv] at hL
  exact Complex.ofReal_inj.mp hL

/-- Telescoping bound for the tail of `∑ 1 / n²`: for `1 ≤ N`,
`∑' k : ℕ, 1 / (k + N + 1)² ≤ 1 / N`. -/
theorem tail_sum_one_div_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 ≤ (N : ℝ)⁻¹ := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let g : ℕ → ℝ := fun k => ((k + N : ℕ) : ℝ)⁻¹ - ((k + N + 1 : ℕ) : ℝ)⁻¹
  have hg_nonneg : ∀ k : ℕ, 0 ≤ g k := fun k => by
    dsimp only [g]
    have hk0 : (0 : ℝ) < (k + N : ℕ) := Nat.cast_pos.mpr (by omega)
    have hle : ((k + N : ℕ) : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (k + N)
    exact sub_nonneg.mpr (inv_anti₀ hk0 hle)
  have hpart : ∀ K : ℕ, ∑ k ∈ Finset.range K, g k =
      (N : ℝ)⁻¹ - ((K + N : ℕ) : ℝ)⁻¹ := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp only [g]
      have hcast : ((K + 1 + N : ℕ) : ℝ) = ((K + N + 1 : ℕ) : ℝ) := by
        congr 1; omega
      rw [hcast]
      ring
  have htend : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, g k) atTop (𝓝 (N : ℝ)⁻¹) := by
    simp_rw [hpart]
    have h0 : Tendsto (fun K : ℕ => ((K + N : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp ?_
      refine tendsto_natCast_atTop_atTop.comp ?_
      exact tendsto_add_atTop_nat N
    simpa only [sub_zero] using tendsto_const_nhds.sub h0
  have hg_hasSum : HasSum g (N : ℝ)⁻¹ :=
    (hasSum_iff_tendsto_nat_of_nonneg hg_nonneg (N : ℝ)⁻¹).mpr htend
  have htail_sum : Summable (fun k : ℕ => (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (N + 1)).mpr summable_one_div_sq
  calc ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2
      ≤ ∑' k : ℕ, g k := by
        refine htail_sum.tsum_le_tsum (fun k => ?_) hg_hasSum.summable
        have hm0 : (0 : ℝ) < (k + N : ℕ) := Nat.cast_pos.mpr (by omega)
        have hm1 : (0 : ℝ) < (k + N + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
        have hcast : ((k + (N + 1) : ℕ) : ℝ) = ((k + N + 1 : ℕ) : ℝ) := by
          push_cast; ring
        have hsub : ((k + N + 1 : ℕ) : ℝ) = ((k + N : ℕ) : ℝ) + 1 := by
          push_cast; ring
        rw [hcast]
        dsimp only [g]
        have hg_eq : ((k + N : ℕ) : ℝ)⁻¹ - ((k + N + 1 : ℕ) : ℝ)⁻¹ =
            1 / (((k + N : ℕ) : ℝ) * ((k + N + 1 : ℕ) : ℝ)) := by
          field_simp [hm0.ne', hm1.ne']
          linarith
        rw [hg_eq]
        refine one_div_le_one_div_of_le (mul_pos hm0 hm1) ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (by linarith) hm1.le
    _ = (N : ℝ)⁻¹ := hg_hasSum.tsum_eq

/-- Tail bound for a sequence `c : ℕ → ℝ` with `|c n| ≤ 1`: for `1 ≤ N`,
`|∑_{1 ≤ d ≤ N} c d / d² - ∑' n, c n / n²| ≤ 1 / N`. -/
theorem abs_sum_Icc_div_sq_sub_tsum_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1)
    (hs : Summable (fun n : ℕ => c n / (n : ℝ) ^ 2)) {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) ^ 2 - ∑' n : ℕ, c n / (n : ℝ) ^ 2| ≤ (N : ℝ)⁻¹ := by
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  have hrange : ∑ d ∈ Finset.range (N + 1), c d / (d : ℝ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) ^ 2 := by
    have h0 : c 0 / ((0 : ℕ) : ℝ) ^ 2 = 0 := by simp
    rw [Finset.range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (Nat.succ_pos N),
      Finset.sum_insert (by simp), zero_add, h0, zero_add]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hrange] at hsplit
  have hdiff : ∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) ^ 2 - ∑' n : ℕ, c n / (n : ℝ) ^ 2 =
      -∑' k : ℕ, c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 := by
    linarith
  rw [hdiff, abs_neg]
  have htail_sum : Summable (fun k : ℕ => c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (N + 1)).mpr hs
  have htail1 : Summable (fun k : ℕ => (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (N + 1)).mpr summable_one_div_sq
  calc |∑' k : ℕ, c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ) ^ 2|
      ≤ ∑' k : ℕ, ‖c (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ) ^ 2‖ :=
        norm_tsum_le_tsum_norm htail_sum.norm
    _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 := by
        refine htail_sum.norm.tsum_le_tsum (fun k => ?_) htail1
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ((k + (N + 1) : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right (hc _) (sq_nonneg _)
    _ ≤ (N : ℝ)⁻¹ := tail_sum_one_div_sq_le hN

/-- Explicit `1 / N` tail bound for `∑_{1 ≤ d ≤ N} 1 / d² - π² / 6` (`1 ≤ N`). -/
theorem abs_sum_Icc_one_div_sq_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2 - Real.pi ^ 2 / 6| ≤ (N : ℝ)⁻¹ := by
  rw [← tsum_one_div_sq]
  exact abs_sum_Icc_div_sq_sub_tsum_le (fun _ => by norm_num) summable_one_div_sq hN

/-- Explicit `1 / N` tail bound for `∑_{1 ≤ d ≤ N} μ(d) / d² - 6 / π²` (`1 ≤ N`). -/
theorem abs_sum_Icc_moebius_div_sq_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2| ≤ (N : ℝ)⁻¹ := by
  rw [← tsum_moebius_div_sq]
  refine abs_sum_Icc_div_sq_sub_tsum_le (fun n => ?_) summable_moebius_div_sq hN
  have hmu : (|(μ n : ℤ)| : ℝ) ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  simpa using hmu

/-- For `1 ≤ x`, `(⌊x⌋₊ : ℝ)⁻¹ ≤ 2 / x`. -/
theorem inv_floor_le_two_div {x : ℝ} (hx : 1 ≤ x) : ((⌊x⌋₊ : ℝ))⁻¹ ≤ 2 / x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hfloor_pos : (0 : ℝ) < ⌊x⌋₊ := Nat.cast_pos.mpr h1
  have hlt : x < 2 * (⌊x⌋₊ : ℝ) := by
    have h1r : (1 : ℝ) ≤ ⌊x⌋₊ := Nat.one_le_cast.mpr h1
    linarith [Nat.lt_floor_add_one x]
  rw [inv_eq_one_div, div_le_div_iff₀ hfloor_pos hx0]
  linarith

private lemma sum_Icc_one_natCast (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, (m : ℝ) = (K : ℝ) * ((K : ℝ) + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos K), ih]
    push_cast
    ring

private lemma abs_floor_triangle_sub_le {t : ℝ} (ht : 0 ≤ t) :
    |(⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) / 2 - t ^ 2 / 2| ≤ t / 2 + 1 / 2 := by
  rcases lt_or_ge t 1 with ht1 | ht1
  · rw [Nat.floor_eq_zero.mpr ht1]
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, zero_sub, abs_neg]
    have hsq : t ^ 2 ≤ 1 := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    linarith
  · have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
    have hlt : t - 1 < (⌊t⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one t]
    have h0 : 0 ≤ (⌊t⌋₊ : ℝ) := Nat.cast_nonneg _
    have htm1 : 0 ≤ t - 1 := sub_nonneg.mpr ht1
    have hup : (⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) / 2 ≤ t ^ 2 / 2 + t / 2 := by
      have hmul : (⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) ≤ t * (t + 1) :=
        mul_le_mul hle (by linarith) (by positivity) ht
      linarith
    have hlo : t ^ 2 / 2 - t / 2 ≤ (⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) / 2 := by
      have hmul : (t - 1) * t ≤ (⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) :=
        mul_le_mul hlt.le (by linarith) ht (by positivity)
      linarith
    rw [abs_le]
    constructor <;> linarith

private lemma abs_weighted_triangle_sum_sub_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1)
    (hs : Summable (fun n : ℕ => c n / (n : ℝ) ^ 2)) {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2) -
        (x ^ 2 / 2) * (∑' n : ℕ, c n / (n : ℝ) ^ 2)| ≤ x * Real.log x / 2 + 2 * x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  let N := ⌊x⌋₊
  let S1 := ∑ d ∈ Finset.Icc 1 N, c d * ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2)
  let S2 := (x ^ 2 / 2) * ∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) ^ 2
  let S3 := (x ^ 2 / 2) * ∑' n : ℕ, c n / (n : ℝ) ^ 2
  have h12 : |S1 - S2| ≤ x * Real.log x / 2 + x := by
    have hdiff : S1 - S2 =
        ∑ d ∈ Finset.Icc 1 N,
          c d * ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2 - x ^ 2 / (2 * (d : ℝ) ^ 2)) := by
      dsimp only [S1, S2]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [hdiff]
    calc |∑ d ∈ Finset.Icc 1 N,
            c d * ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2 - x ^ 2 / (2 * (d : ℝ) ^ 2))|
        ≤ ∑ d ∈ Finset.Icc 1 N,
            |c d * ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2 - x ^ 2 / (2 * (d : ℝ) ^ 2))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (x / (2 * (d : ℝ)) + 1 / 2) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
          rw [abs_mul]
          have htri := abs_floor_triangle_sub_le (div_nonneg hx0.le hd0.le)
          have hsq_eq : (x / d) ^ 2 / 2 = x ^ 2 / (2 * (d : ℝ) ^ 2) := by ring
          have hdiv_eq : (x / d) / 2 + 1 / 2 = x / (2 * (d : ℝ)) + 1 / 2 := by ring
          rw [hsq_eq, hdiv_eq] at htri
          calc |c d| * |(⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2 - x ^ 2 / (2 * (d : ℝ) ^ 2)|
              ≤ 1 * (x / (2 * (d : ℝ)) + 1 / 2) :=
                mul_le_mul (hc d) htri (abs_nonneg _) zero_le_one
            _ = x / (2 * (d : ℝ)) + 1 / 2 := one_mul _
      _ = (x / 2) * (∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹) + (N : ℝ) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
            nsmul_eq_mul, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun d _ => ?_
            ring
          · ring
      _ ≤ (x / 2) * (1 + Real.log x) + x / 2 := by
          gcongr
          · exact sum_inv_le_one_add_log hx
          · exact Nat.floor_le hx0.le
      _ = x * Real.log x / 2 + x := by ring
  have h23 : |S2 - S3| ≤ x := by
    dsimp only [S2, S3]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have htail := abs_sum_Icc_div_sq_sub_tsum_le hc hs hN1
    have hinv := inv_floor_le_two_div hx
    calc (x ^ 2 / 2) * |∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) ^ 2 - ∑' n : ℕ, c n / (n : ℝ) ^ 2|
        ≤ (x ^ 2 / 2) * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (x ^ 2 / 2) * (2 / x) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = x := by field_simp [hx0.ne']
  calc |S1 - S3|
      = |(S1 - S2) + (S2 - S3)| := by ring_nf
    _ ≤ |S1 - S2| + |S2 - S3| := abs_add_le _ _
    _ ≤ (x * Real.log x / 2 + x) + x := add_le_add h12 h23
    _ = x * Real.log x / 2 + 2 * x := by ring

private lemma isBigO_mul_log_of_bound {E : ℝ → ℝ}
    (hE : ∀ {x : ℝ}, 1 ≤ x → |E x| ≤ x * Real.log x / 2 + 2 * x) :
    E =O[atTop] (fun x : ℝ => x * Real.log x) := by
  refine isBigO_iff.mpr ⟨4, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx2
  have hx1 : 1 ≤ x := one_le_two.trans hx2
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogx : (2 / 3 : ℝ) ≤ Real.log x :=
    hlog2.trans (Real.log_le_log zero_lt_two hx2)
  have hxlog_nonneg : 0 ≤ x * Real.log x := mul_nonneg hx0 (by linarith)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hxlog_nonneg]
  have h2x : 2 * x ≤ 3 * (x * Real.log x) := by
    calc 2 * x = 3 * x * (2 / 3) := by ring
      _ ≤ 3 * x * Real.log x := mul_le_mul_of_nonneg_left hlogx (by positivity)
      _ = 3 * (x * Real.log x) := by ring
  calc |E x|
      ≤ x * Real.log x / 2 + 2 * x := hE hx1
    _ ≤ x * Real.log x / 2 + 3 * (x * Real.log x) := by linarith
    _ ≤ 4 * (x * Real.log x) := by linarith

end SeriesHelpers

/-! ### Average Order of the Sum-of-Divisors Function `σ₁` -/

section SigmaOneAverageOrder

/-- The summatory function of the sum-of-divisors function: `∑_{1 ≤ n ≤ x} σ₁(n)`. -/
def sigmaOneSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((σ 1 n : ℕ) : ℝ)

/-- `sigmaOneSum x` written explicitly as a double sum over divisors `d ∣ n`. -/
theorem sigmaOneSum_eq_sum_divisors (x : ℝ) :
    sigmaOneSum x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [ArithmeticFunction.sigma_one_apply]

/-- `sigmaOneSum x` expressed as the partial sum of the convolution `1 ⍟ id`. -/
theorem sigmaOneSum_eq_partialSum_conv (x : ℝ) :
    sigmaOneSum x = partialSum ((fun _ : ℕ => (1 : ℝ)) ⍟ (fun n : ℕ => (n : ℝ))) x := by
  rw [sigmaOneSum, partialSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hconv : ((fun _ : ℕ => (1 : ℝ)) ⍟ (fun m : ℕ => (m : ℝ))) n =
      ∑ d ∈ n.divisors, (d : ℝ) := by
    rw [LSeries.convolution_def]
    dsimp only
    rw [← Nat.map_div_left_divisors, Finset.sum_map]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [one_mul]
    rfl
  rw [hconv, ArithmeticFunction.sigma_one_apply]
  push_cast
  rfl

/-- Exact triangular-number sum identity for `∑_{1 ≤ n ≤ x} σ₁(n)`:
`sigmaOneSum x = ∑_{1 ≤ d ≤ x} ⌊x / d⌋₊ * (⌊x / d⌋₊ + 1) / 2`. -/
theorem sigmaOneSum_eq_sum_triangle (x : ℝ) :
    sigmaOneSum x =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2) := by
  rw [sigmaOneSum_eq_partialSum_conv, partialSum_convolution_eq_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [one_mul, partialSum, sum_Icc_one_natCast]

/-- The error term in the average order of `σ₁`:
`sigmaOneError x = ∑_{1 ≤ n ≤ x} σ₁(n) - (π² / 12) * x²`. -/
def sigmaOneError (x : ℝ) : ℝ :=
  sigmaOneSum x - Real.pi ^ 2 / 12 * x ^ 2

/-- Explicit `O(x log x)` remainder bound for `∑_{1 ≤ n ≤ x} σ₁(n)` when `1 ≤ x`:
`|sigmaOneError x| ≤ x * log x / 2 + 2 * x`. -/
theorem abs_sigmaOneError_le {x : ℝ} (hx : 1 ≤ x) :
    |sigmaOneError x| ≤ x * Real.log x / 2 + 2 * x := by
  have hmain : (x ^ 2 / 2) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 12 * x ^ 2 := by
    rw [tsum_one_div_sq]
    ring
  rw [sigmaOneError, sigmaOneSum_eq_sum_triangle, ← hmain]
  have hbound := abs_weighted_triangle_sum_sub_le (c := fun _ => (1 : ℝ))
    (fun _ => by norm_num) summable_one_div_sq hx
  simpa only [one_mul] using hbound

/-- **Average order of `σ₁(n)`** in Big-O form:
`∑_{1 ≤ n ≤ x} σ₁(n) = (π² / 12) * x² + O(x * log x)`. -/
theorem sigmaOneError_isBigO_mul_log :
    sigmaOneError =O[atTop] (fun x : ℝ => x * Real.log x) :=
  isBigO_mul_log_of_bound (fun hx => abs_sigmaOneError_le hx)

end SigmaOneAverageOrder

/-! ### Average Order of Euler's Totient Function `φ` -/

section TotientAverageOrder

/-- Convolution identity `φ = μ * id` in `ArithmeticFunction ℤ`. -/
theorem moebius_mul_id_eq_totient :
    (μ : ArithmeticFunction ℤ) * (ArithmeticFunction.id : ArithmeticFunction ℤ) =
      (totientAF : ArithmeticFunction ℤ) := by
  have hzeta : (ζ : ArithmeticFunction ℤ) * (totientAF : ArithmeticFunction ℤ) =
      (ArithmeticFunction.id : ArithmeticFunction ℤ) := by
    rw [← ArithmeticFunction.natCoe_mul, zeta_mul_totientAF_eq_id]
  calc (μ : ArithmeticFunction ℤ) * (ArithmeticFunction.id : ArithmeticFunction ℤ)
      = (μ : ArithmeticFunction ℤ) *
          ((ζ : ArithmeticFunction ℤ) * (totientAF : ArithmeticFunction ℤ)) := by rw [← hzeta]
    _ = ((μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) *
          (totientAF : ArithmeticFunction ℤ) := (mul_assoc _ _ _).symm
    _ = 1 * (totientAF : ArithmeticFunction ℤ) := by rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = (totientAF : ArithmeticFunction ℤ) := one_mul _

/-- Pointwise identity `φ(n) = ∑_{d * m = n} μ(d) * m` in `ℝ`. -/
theorem totient_eq_sum_moebius_mul_div (n : ℕ) :
    (n.totient : ℝ) = ∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * (p.2 : ℝ) := by
  have h := congr_arg (fun f : ArithmeticFunction ℤ => (f n : ℝ)) moebius_mul_id_eq_totient
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply, totientAF_apply,
    ArithmeticFunction.id_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h
  exact h.symm

/-- `φ(n)` expressed as a divisor sum `∑_{d ∣ n} μ(d) * (n / d)`. -/
theorem totient_eq_sum_divisors_moebius_mul_div (n : ℕ) :
    (n.totient : ℝ) = ∑ d ∈ n.divisors, (μ d : ℝ) * ((n / d : ℕ) : ℝ) := by
  rw [totient_eq_sum_moebius_mul_div, ← Nat.map_div_right_divisors, Finset.sum_map]
  rfl

/-- The summatory function of Euler's totient: `Φ(x) = ∑_{1 ≤ n ≤ x} φ(n)`. -/
def totientSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.totient : ℝ)

/-- `totientSum x` expressed as the partial sum of the convolution `μ ⍟ id`. -/
theorem totientSum_eq_partialSum_conv (x : ℝ) :
    totientSum x = partialSum ((fun n : ℕ => (μ n : ℝ)) ⍟ (fun n : ℕ => (n : ℝ))) x := by
  rw [totientSum, partialSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [totient_eq_sum_moebius_mul_div, LSeries.convolution_def]

/-- Exact triangular-number sum identity for `∑_{1 ≤ n ≤ x} φ(n)` via `φ = μ * id`:
`totientSum x = ∑_{1 ≤ d ≤ x} μ(d) * (⌊x / d⌋₊ * (⌊x / d⌋₊ + 1) / 2)`. -/
theorem totientSum_eq_sum_moebius_mul_triangle (x : ℝ) :
    totientSum x =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        (μ d : ℝ) * ((⌊x / d⌋₊ : ℝ) * ((⌊x / d⌋₊ : ℝ) + 1) / 2) := by
  rw [totientSum_eq_partialSum_conv, partialSum_convolution_eq_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [partialSum, sum_Icc_one_natCast]

/-- The error term in the average order of Euler's totient:
`totientError x = ∑_{1 ≤ n ≤ x} φ(n) - (3 / π²) * x²`. -/
def totientError (x : ℝ) : ℝ :=
  totientSum x - 3 / Real.pi ^ 2 * x ^ 2

/-- Explicit `O(x log x)` remainder bound for `∑_{1 ≤ n ≤ x} φ(n)` when `1 ≤ x`:
`|totientError x| ≤ x * log x / 2 + 2 * x`. -/
theorem abs_totientError_le {x : ℝ} (hx : 1 ≤ x) :
    |totientError x| ≤ x * Real.log x / 2 + 2 * x := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmain : (x ^ 2 / 2) * ∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 = 3 / Real.pi ^ 2 * x ^ 2 := by
    rw [tsum_moebius_div_sq]
    field_simp [hpi]
    ring
  rw [totientError, totientSum_eq_sum_moebius_mul_triangle, ← hmain]
  refine abs_weighted_triangle_sum_sub_le (c := fun n => (μ n : ℝ)) (fun n => ?_)
    summable_moebius_div_sq hx
  have hmu : (|(μ n : ℤ)| : ℝ) ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  simpa using hmu

/-- **Average order of Euler's totient function `φ(n)`** in Big-O form:
`∑_{1 ≤ n ≤ x} φ(n) = (3 / π²) * x² + O(x * log x)`. -/
theorem totientError_isBigO_mul_log :
    totientError =O[atTop] (fun x : ℝ => x * Real.log x) :=
  isBigO_mul_log_of_bound (fun hx => abs_totientError_le hx)

end TotientAverageOrder

/-! ### Squarefree Counting Function -/

section SquarefreeCounting

/-- Squarefree indicator identity in `ℤ`: `μ(n)² = ∑_{1 ≤ d ≤ √n, d² ∣ n} μ(d)`. -/
theorem moebius_sq_eq_sum_sq_dvd_int (n : ℕ) :
    μ n ^ 2 = ∑ d ∈ (Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d ^ 2 ∣ n), μ d := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hconv := congr_arg (fun f : ArithmeticFunction ℤ => f n) zeta_mul_moebiusSq_eq_absMoebius
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.natCoe_apply,
      absMoebiusAF_apply] at hconv
    have hsq_eq : ((if Squarefree n then (1 : ℕ) else 0 : ℕ) : ℤ) = μ n ^ 2 := by
      rw [ArithmeticFunction.moebius_sq]
      split_ifs <;> rfl
    rw [hsq_eq] at hconv
    rw [← hconv]
    have hfilt :
        ∑ k ∈ n.divisors, moebiusSqAF k =
          ∑ k ∈ n.divisors.filter (fun k => k ≠ 0 ∧ IsSquare k), moebiusSqAF k := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [moebiusSqAF_apply]
      split_ifs <;> rfl
    rw [hfilt]
    symm
    refine Finset.sum_bij (fun d _ => d ^ 2) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hd.2, hn0⟩, pow_ne_zero 2 (Nat.ne_of_gt hd.1.1), ⟨d, sq d⟩⟩
    · intro d₁ _ d₂ _ h
      exact Nat.pow_left_injective two_ne_zero h
    · intro k hk
      simp only [Finset.mem_filter, Nat.mem_divisors] at hk
      obtain ⟨⟨hkdvd, _⟩, hk0, ⟨d, hd_eq⟩⟩ := hk
      have hsq_eq_d : k = d ^ 2 := by rw [hd_eq, sq]
      have hd1 : 1 ≤ d := by
        by_contra! hd0
        have : d = 0 := by omega
        subst this
        simp at hd_eq
        exact hk0 hd_eq
      have hd_le : d ≤ Nat.sqrt n := by
        rw [Nat.le_sqrt, ← sq, ← hsq_eq_d]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hkdvd
      refine ⟨d, ?_, hsq_eq_d.symm⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd1, hd_le⟩, hsq_eq_d ▸ hkdvd⟩
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      rw [moebiusSqAF_apply, ite_eq_left ⟨pow_ne_zero 2 (Nat.ne_of_gt hd.1.1), ⟨d, sq d⟩⟩,
        sq, Nat.sqrt_eq]

/-- Squarefree indicator identity in `ℝ`: `μ(n)² = ∑_{1 ≤ d ≤ √n, d² ∣ n} μ(d)`. -/
theorem moebius_sq_eq_sum_sq_dvd (n : ℕ) :
    (μ n : ℝ) ^ 2 = ∑ d ∈ (Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d ^ 2 ∣ n), (μ d : ℝ) := by
  have h := congr_arg ((↑) : ℤ → ℝ) (moebius_sq_eq_sum_sq_dvd_int n)
  simpa only [Int.cast_pow, Int.cast_sum] using h

/-- Squarefree indicator identity summed over divisors `d ∈ n.divisors` with `d² ∣ n`. -/
theorem moebius_sq_eq_sum_divisors_sq_dvd (n : ℕ) :
    (μ n : ℝ) ^ 2 = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), (μ d : ℝ) := by
  rw [moebius_sq_eq_sum_sq_dvd]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd1, hdle⟩, hd2n⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [Nat.sqrt_zero] at hdle
      omega
    exact ⟨⟨(dvd_pow_self d (by decide : 2 ≠ 0)).trans hd2n, hn0⟩, hd2n⟩
  · rintro ⟨⟨_, hn0⟩, hd2n⟩
    have hd0 : 1 ≤ d := by
      by_contra! h
      have : d = 0 := by omega
      subst this
      simp at hd2n
      exact hn0 hd2n
    have hd_le : d ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt, ← sq]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd2n
    exact ⟨⟨hd0, hd_le⟩, hd2n⟩

/-- The squarefree counting function `Q(x) = ∑_{1 ≤ n ≤ x} μ(n)²`. -/
def squarefreeCount (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) ^ 2

/-- `squarefreeCount x` equals the cardinality of squarefree integers in `[1, ⌊x⌋₊]`. -/
theorem squarefreeCount_eq_card (x : ℝ) :
    squarefreeCount x = (((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).card : ℝ) := by
  rw [squarefreeCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsq : (μ n : ℝ) ^ 2 = if Squarefree n then (1 : ℝ) else 0 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
    split_ifs <;> simp
  rw [hsq]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private lemma nat_sqrt_floor_eq_floor_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Nat.sqrt ⌊x⌋₊ = ⌊Real.sqrt x⌋₊ := by
  have hiff : ∀ k : ℕ, k ≤ Nat.sqrt ⌊x⌋₊ ↔ k ≤ ⌊Real.sqrt x⌋₊ := fun k => by
    rw [Nat.le_sqrt, ← sq, Nat.le_floor_iff hx, Nat.le_floor_iff (Real.sqrt_nonneg x),
      Nat.cast_pow, Real.le_sqrt (Nat.cast_nonneg k) hx]
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

private lemma card_Icc_filter_dvd (N k : ℕ) (hk : 1 ≤ k) :
    ((Finset.Icc 1 N).filter (fun n => k ∣ n)).card = N / k := by
  have hcard : ((Finset.Icc 1 N).filter (fun n => k ∣ n)).card = (Finset.Icc 1 (N / k)).card := by
    refine Finset.card_bij (fun n _ => n / k) ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn.1.2⟩
      obtain ⟨m, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left _ hk]
      by_contra! hm0
      have : m = 0 := by omega
      subst this
      simp at hn
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn₁ hn₂
      have h1 := Nat.mul_div_cancel' hn₁.2
      have h2 := Nat.mul_div_cancel' hn₂.2
      rw [← h1, ← h2, h]
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      have hmul : k * m ≤ N := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hk).mp hm.2
      refine ⟨k * m, ?_, Nat.mul_div_cancel_left m hk⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.mul_pos hk hm.1, hmul⟩, ⟨m, rfl⟩⟩
  rw [hcard, Nat.card_Icc, Nat.add_sub_cancel]

/-- Exact formula for the squarefree counting function:
`Q(x) = ∑_{1 ≤ d ≤ √x} μ(d) * ⌊x / d²⌋₊`. -/
theorem squarefreeCount_eq_sum_floor_div_sq (x : ℝ) :
    squarefreeCount x =
      ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (μ d : ℝ) * (⌊x / (d : ℝ) ^ 2⌋₊ : ℝ) := by
  rcases lt_or_ge x 0 with hx | hx
  · simp [squarefreeCount, Nat.floor_of_nonpos hx.le, Real.sqrt_eq_zero_of_nonpos hx.le]
  · rw [squarefreeCount]
    have hexpand :
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) ^ 2 =
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, if d ^ 2 ∣ n then (μ d : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [moebius_sq_eq_sum_sq_dvd, Finset.sum_filter]
      have hsub : Finset.Icc 1 (Nat.sqrt n) ⊆ Finset.Icc 1 ⌊Real.sqrt x⌋₊ := by
        refine Finset.Icc_subset_Icc_right ?_
        rw [← nat_sqrt_floor_eq_floor_sqrt hx]
        exact Nat.sqrt_le_sqrt (Finset.mem_Icc.mp hn).2
      refine Finset.sum_subset hsub fun d _ hd_not => ?_
      have hn0 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [ite_eq_right_iff]
      intro hd2n
      exfalso
      apply hd_not
      simp only [Finset.mem_Icc] at *
      have hd_le_n : d ^ 2 ≤ n := Nat.le_of_dvd hn0 hd2n
      have hd1 : 1 ≤ d := by
        by_contra! h0
        have : d = 0 := by omega
        subst this
        simp at hd2n
        omega
      exact ⟨hd1, Nat.le_sqrt.mpr (by rw [← sq]; exact hd_le_n)⟩
    rw [hexpand, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd2 : 1 ≤ d ^ 2 := Nat.one_le_pow 2 d hd1
    have hfilter :
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if d ^ 2 ∣ n then (μ d : ℝ) else 0) =
          (μ d : ℝ) * (((Finset.Icc 1 ⌊x⌋₊).filter (fun n => d ^ 2 ∣ n)).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hfilter, card_Icc_filter_dvd ⌊x⌋₊ (d ^ 2) hd2, ← nat_floor_div_nat hx hd2]
    simp

/-- The error term in the squarefree counting asymptotic:
`squarefreeError x = ∑_{1 ≤ n ≤ x} μ(n)² - (6 / π²) * x`. -/
def squarefreeError (x : ℝ) : ℝ :=
  squarefreeCount x - 6 / Real.pi ^ 2 * x

/-- Explicit `O(√x)` error bound for the squarefree counting function for all `0 ≤ x`:
`|Q(x) - (6 / π²) * x| ≤ 3 * √x`. -/
theorem abs_squarefreeError_le {x : ℝ} (hx : 0 ≤ x) :
    |squarefreeError x| ≤ 3 * Real.sqrt x := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · rcases eq_or_lt_of_le hx with rfl | hx0
    · simp [squarefreeError, squarefreeCount]
    · have hcount0 : squarefreeCount x = 0 := by
        rw [squarefreeCount, Nat.floor_eq_zero.mpr hx1]
        simp
      have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hsx1 : Real.sqrt x ≤ 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hx1.le
      have hx_le_sqrt : x ≤ Real.sqrt x := by
        have hxsq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
        conv_lhs => rw [hxsq]
        exact mul_le_of_le_one_right hsx0 hsx1
      have hpi6 : (6 : ℝ) / Real.pi ^ 2 ≤ 1 := by
        have h1_le_zeta2 : (1 : ℝ) ≤ Real.pi ^ 2 / 6 := by
          rw [← tsum_one_div_sq]
          have hle := summable_one_div_sq.le_tsum 1
            (fun n _ => div_nonneg zero_le_one (sq_nonneg _))
          simpa using hle
        rw [div_le_one (sq_pos_of_pos Real.pi_pos)]
        linarith
      rw [squarefreeError, hcount0, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg (by positivity) hx0.le)]
      calc 6 / Real.pi ^ 2 * x
          ≤ 1 * x := mul_le_mul_of_nonneg_right hpi6 hx0.le
        _ = x := one_mul x
        _ ≤ Real.sqrt x := hx_le_sqrt
        _ ≤ 3 * Real.sqrt x := by linarith
  · have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hsx1 : 1 ≤ Real.sqrt x := sqrt_one_le hx1
    have hsx0 : 0 < Real.sqrt x := zero_lt_one.trans_le hsx1
    have hM1 : 1 ≤ ⌊Real.sqrt x⌋₊ := (Nat.one_le_floor_iff _).mpr hsx1
    let M := ⌊Real.sqrt x⌋₊
    have hsum_floor :
        squarefreeCount x =
          x * (∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) / (d : ℝ) ^ 2) -
            ∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2) := by
      rw [squarefreeCount_eq_sum_floor_div_sq]
      have hterm : ∀ d ∈ Finset.Icc 1 M,
          (μ d : ℝ) * (⌊x / (d : ℝ) ^ 2⌋₊ : ℝ) =
            x * ((μ d : ℝ) / (d : ℝ) ^ 2) - (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2) := by
        intro d hd
        have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
        rw [← Int.cast_natCast, Int.natCast_floor_eq_floor (div_nonneg hx0.le (sq_nonneg _))]
        have hf := Int.floor_add_fract (x / (d : ℝ) ^ 2)
        have hfl : (⌊x / (d : ℝ) ^ 2⌋ : ℝ) = x / (d : ℝ) ^ 2 - Int.fract (x / (d : ℝ) ^ 2) := by
          linarith
        rw [hfl]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hdiff :
        squarefreeError x =
          x * (∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2) -
            ∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2) := by
      rw [squarefreeError, hsum_floor]
      ring
    have htail := abs_sum_Icc_moebius_div_sq_sub_le hM1
    have hinv := inv_floor_le_two_div hsx1
    have h1 :
        |x * (∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤
          2 * Real.sqrt x := by
      rw [abs_mul, abs_of_pos hx0]
      have hxsq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
      calc x * |∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2|
          ≤ x * (M : ℝ)⁻¹ := mul_le_mul_of_nonneg_left htail hx0.le
        _ ≤ x * (2 / Real.sqrt x) := mul_le_mul_of_nonneg_left hinv hx0.le
        _ = (Real.sqrt x * Real.sqrt x) * (2 / Real.sqrt x) := by rw [← hxsq]
        _ = 2 * Real.sqrt x := by field_simp [hsx0.ne']
    have h2 :
        |∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2)| ≤ Real.sqrt x := by
      calc |∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2)|
          ≤ ∑ d ∈ Finset.Icc 1 M, |(μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ Finset.Icc 1 M, (1 : ℝ) := by
            refine Finset.sum_le_sum fun d _ => ?_
            rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (x / (d : ℝ) ^ 2))]
            have hmu : (|(μ d : ℤ)| : ℝ) ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            have hmu' : |(μ d : ℝ)| ≤ 1 := by simpa using hmu
            exact (mul_le_of_le_one_left (Int.fract_nonneg _) hmu').trans (Int.fract_lt_one _).le
        _ = (M : ℝ) := by simp
        _ ≤ Real.sqrt x := Nat.floor_le hsx0.le
    rw [hdiff]
    calc |x * (∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2) -
            ∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2)|
        ≤ |x * (∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| +
            |∑ d ∈ Finset.Icc 1 M, (μ d : ℝ) * Int.fract (x / (d : ℝ) ^ 2)| := abs_sub _ _
      _ ≤ 2 * Real.sqrt x + Real.sqrt x := add_le_add h1 h2
      _ = 3 * Real.sqrt x := by ring

/-- **Squarefree counting asymptotic** in Big-O form:
`∑_{1 ≤ n ≤ x} μ(n)² = (6 / π²) * x + O(√x)`. -/
theorem squarefreeError_isBigO_sqrt :
    squarefreeError =O[atTop] Real.sqrt := by
  refine isBigO_iff.mpr ⟨3, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  exact abs_squarefreeError_le hx

/-- **Squarefree counting asymptotic** with `x^(1/2)` Big-O error term. -/
theorem squarefreeError_isBigO_rpow_half :
    squarefreeError =O[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
  refine squarefreeError_isBigO_sqrt.congr_right ?_
  intro x
  rw [Real.sqrt_eq_rpow]

end SquarefreeCounting

end AnalyticNumberTheory.DivisorProblems
