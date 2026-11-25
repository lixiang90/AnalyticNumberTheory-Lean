import AnalyticNumberTheory.DirichletLFunctions.CharacterPolynomialSquares

/-! # Harmonic mass of a finite Dirichlet convolution -/

open Finset Complex

namespace AnalyticNumberTheory.DirichletLFunctions

/-- In the harmonic first moment of the restricted convolution, grouping
by the product gives at most the square of the original harmonic mass. -/
theorem factorPairWeight_harmonic_mass {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) (a : ℕ → ℂ) :
    (∑ k ∈ Icc 1 (N^2), ‖factorPairWeight S a k‖/(k : ℝ)) ≤
      (∑ n ∈ S, ‖a n‖/(n : ℝ))^2 := by
  let F (p : ℕ × ℕ) := (‖a p.1‖/(p.1 : ℝ)) * (‖a p.2‖/(p.2 : ℝ))
  have maps (p : ℕ × ℕ) (hp : p ∈ S ×ˢ S) : p.1*p.2 ∈ Icc 1 (N^2) := by
    obtain ⟨hu,hv⟩ := mem_product.mp hp
    obtain ⟨hu1,huN⟩ := mem_Icc.mp (hS hu)
    obtain ⟨hv1,hvN⟩ := mem_Icc.mp (hS hv)
    exact mem_Icc.mpr ⟨Nat.mul_pos hu1 hv1, by simpa [sq] using Nat.mul_le_mul huN hvN⟩
  calc
    _ ≤ ∑ k ∈ Icc 1 (N^2), ∑ p ∈ (S ×ˢ S).filter (fun p => p.1*p.2=k), F p := by
      apply sum_le_sum
      intro k hk
      apply (div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg k)).trans_eq
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro p hp
      rw [← (mem_filter.mp hp).2, Nat.cast_mul, norm_mul]
      dsimp only [F]
      ring
    _ = ∑ p ∈ S ×ˢ S, F p := sum_fiberwise_of_maps_to maps _
    _ = _ := by
      rw [sum_product S S F, pow_two, sum_mul]
      simp only [F, mul_sum]

/-- A uniform bound for each convolution coefficient turns its harmonic
first moment into a bound for the diagonal in a fourth-moment estimate. -/
theorem factorPairWeight_harmonic_energy {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N)
    (a : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ k ∈ Icc 1 (N^2), ‖factorPairWeight S a k‖ ≤ B) :
    (∑ k ∈ Icc 1 (N^2), ‖factorPairWeight S a k‖^2/(k : ℝ)) ≤ B*(∑ n ∈ S, ‖a n‖/(n : ℝ))^2 := by
  apply le_trans _ (mul_le_mul_of_nonneg_left (factorPairWeight_harmonic_mass hS a) hB)
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  rw [sq, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hb k hk) (norm_nonneg _)) (Nat.cast_nonneg _)

end AnalyticNumberTheory.DirichletLFunctions
