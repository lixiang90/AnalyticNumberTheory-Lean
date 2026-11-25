import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentOrthogonality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # A weighted fixed-modulus character mean on arbitrary finite samples -/

noncomputable section
open Complex Finset
open scoped Classical

namespace AnalyticNumberTheory.DirichletLFunctions

/-- If the squared coefficient at i is at most w(i)v(i), the second moment
of its character transform costs the maximum total w in a single residue
class times the full sum of v, with the exact Parseval factor φ(q). -/
theorem character_sum_sq_le_of_fiber_weight {ι : Type*} {q : ℕ} [NeZero q] (S : Finset ι)
    (g : ι → ZMod q) (a : ι → ℂ) (w v : ι → ℝ) {K : ℝ}
    (hw : ∀ i ∈ S, 0≤w i) (hv : ∀ i ∈ S, 0≤v i) (ha : ∀ i ∈ S, ‖a i‖^2 ≤ w i*v i)
    (hK : ∀ r : ZMod q, (∑ i ∈ S.filter (fun i => g i=r), w i) ≤ K) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ i ∈ S, χ (g i)*a i‖^2) ≤
      (q.totient : ℝ)*K*∑ i ∈ S, v i := by
  let T (r : ZMod q) := S.filter fun i => g i=r
  let A (r : ZMod q) := ∑ i ∈ T r, a i
  have hm : ∀ i ∈ S, g i ∈ (univ : Finset (ZMod q)) := fun _ _ => mem_univ _
  have split (χ : DirichletCharacter ℂ q) : (∑ i ∈ S, χ (g i)*a i) = ∑ r, χ r*A r := by
    rw [← sum_fiberwise_of_maps_to hm]
    apply sum_congr rfl
    intro r _
    rw [show A r = ∑ i ∈ T r,a i from rfl, mul_sum]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  have hrow (r : ZMod q) : (if IsUnit r then ‖A r‖^2 else 0) ≤ K*∑ i ∈ T r, v i := by
    have inc : T r ⊆ S := filter_subset ..
    have hsum : 0 ≤ ∑ i ∈ T r, v i := sum_nonneg fun i hi => hv i (inc hi)
    by_cases hu : IsUnit r
    · rw [ite_eq_left hu]
      calc
        _ ≤ (∑ i ∈ T r, ‖a i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2
        _ ≤ (∑ i ∈ T r, w i)*∑ i ∈ T r, v i := sum_sq_le_sum_mul_sum_of_sq_le_mul _
              (fun i hi => hw i (inc hi)) (fun i hi => hv i (inc hi)) (fun i hi => ha i (inc hi))
        _ ≤ _ := mul_le_mul_of_nonneg_right (hK r) hsum
    · rw [ite_eq_right hu]
      exact mul_nonneg ((sum_nonneg fun i hi => hw i (inc hi)).trans (hK r)) hsum
  simp_rw [split]
  rw [dirichlet_character_parseval, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (sum_le_sum fun r _ => hrow r).trans_eq
  rw [← mul_sum, sum_fiberwise_of_maps_to hm]

end AnalyticNumberTheory.DirichletLFunctions
