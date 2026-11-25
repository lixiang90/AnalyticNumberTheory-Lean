import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcs

/-! # Partial summation between nearby prime frequencies -/

noncomputable section
open Complex Finset Real
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- A common bound on initial prime sums transports to a nearby frequency,
at a cost of at most `1+2πx|β|`, also for nonintegral endpoints. -/
theorem norm_primeExpSum_shift_of_bound {x D α : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (H : ∀ t ∈ Set.Icc 0 x, ‖primeExpSum t α‖ ≤ D) (β : ℝ) :
    ‖primeExpSum x (α+β)‖ ≤ D * (1 + 2 * Real.pi * x * |β|) := by
  let N := ⌊x⌋₊
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx
  have step (k : ℕ) (hk : k ∈ Icc 1 N) : ‖primeExpSum k α - (0 : ℂ)*k‖ ≤ D := by
    rw [zero_mul, sub_zero]
    exact H k ⟨Nat.cast_nonneg _, (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans hN⟩
  have h := norm_primeExpSum_shift_sub_main_le (α := α) (β := β) hD step
  have he (t : ℝ) : primeExpSum N t = primeExpSum x t := by simp only [primeExpSum, Nat.floor_natCast, N]
  rw [zero_mul, sub_zero, he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (by positivity)) (abs_nonneg β)) _) hD)

end AnalyticNumberTheory.ExponentialSums
