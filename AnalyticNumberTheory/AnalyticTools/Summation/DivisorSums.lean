module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors

/-!
# Summing over divisors and multiples

A finite hyperbola can be summed by its products or its first coordinate. With Möbius
weights this inverts finite sums over multiples, including root transforms of counting functions.
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- Reindex pairs of positive integers with product at most `N` and first coordinate at most
`M`. The summand may depend jointly on the two coordinates. -/
theorem sum_Icc_divisors_mul {R : Type*} [AddCommMonoid R] (N M : ℕ) (g : ℕ → ℕ → R) :
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

/-- Finite Möbius inversion over multiples. For `N ≥ 1`, the Möbius-weighted sum of
`F(d), F(2d), …, F(⌊N/d⌋d)` over positive `d ≤ N` recovers `F(1)`. -/
theorem sum_moebius_mul_sum_multiples {R : Type*} [Ring R] {N : ℕ} (hN : 1 ≤ N)
    (F : ℕ → R) :
    ∑ d ∈ Icc 1 N, (μ d : R) * (∑ j ∈ Icc 1 (N / d), F (d * j)) = F 1 := by
  simp_rw [mul_sum]
  rw [← sum_Icc_divisors_mul N N (fun d j => (μ d : R) * F (d * j))]
  calc
    _ = ∑ n ∈ Icc 1 N, (if n = 1 then F n else 0) := by
      refine sum_congr rfl fun n hn => ?_
      have hfilter : n.divisors.filter (· ≤ N) = n.divisors := by
        apply filter_eq_self.mpr
        exact fun d hd => (Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.dvd_of_mem_divisors hd)).trans
          (mem_Icc.mp hn).2
      rw [hfilter]
      trans (∑ d ∈ n.divisors, (μ d : R)) * F n
      · rw [sum_mul]
        exact sum_congr rfl fun d hd => by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      · have hsum := congrArg (fun f : ArithmeticFunction R => f n)
            (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := R))
        change ((μ : ArithmeticFunction R) * ζ) n = (1 : ArithmeticFunction R) n at hsum
        rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hsum
        change (∑ d ∈ n.divisors, (μ d : R)) = _ at hsum
        rw [hsum]
        split <;> simp_all
    _ = F 1 := by simp [hN]

end AnalyticNumberTheory.AnalyticTools.Summation
