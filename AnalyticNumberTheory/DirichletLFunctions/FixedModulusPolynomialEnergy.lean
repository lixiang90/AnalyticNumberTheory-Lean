import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentOrthogonality
import Mathlib.Algebra.Order.Chebyshev

/-! # Pointwise mean squares of polynomials over characters of one modulus -/

noncomputable section

open Complex Finset
open scoped Classical

namespace AnalyticNumberTheory.DirichletLFunctions

/-- If each residue class occurs at most `K` times, the mean square of its
character transform is at most `φ(q) K` times the coefficient energy. -/
theorem character_sum_sq_le_of_fiber_card {ι : Type*} {q : ℕ} [NeZero q] (S : Finset ι)
    (g : ι → ZMod q) (a : ι → ℂ) {K : ℝ}
    (hK : ∀ r : ZMod q, ((S.filter fun i => g i = r).card : ℝ) ≤ K) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ i ∈ S, χ (g i) * a i‖ ^ 2) ≤
      (q.totient : ℝ) * K * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  let T (r : ZMod q) := S.filter fun i => g i = r
  let A (r : ZMod q) := ∑ i ∈ T r, a i
  have hmap : ∀ i ∈ S, g i ∈ (univ : Finset (ZMod q)) := fun _ _ => mem_univ _
  have split (χ : DirichletCharacter ℂ q) : (∑ i ∈ S, χ (g i) * a i) = ∑ r, χ r * A r := by
    rw [← sum_fiberwise_of_maps_to hmap]
    apply sum_congr rfl
    intro r _
    dsimp only [A]
    rw [mul_sum]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  have hrow (r : ZMod q) : (if IsUnit r then ‖A r‖^2 else 0) ≤ K * ∑ i ∈ T r, ‖a i‖^2 := by
    have hsum : 0 ≤ ∑ i ∈ T r, ‖a i‖^2 := sum_nonneg fun _ _ => sq_nonneg _
    by_cases hu : IsUnit r
    · rw [ite_eq_left hu]
      calc
        _ ≤ (∑ i ∈ T r, ‖a i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) _
        _ ≤ ((T r).card : ℝ) * ∑ i ∈ T r, ‖a i‖^2 := sq_sum_le_card_mul_sum_sq
        _ ≤ _ := mul_le_mul_of_nonneg_right (hK r) hsum
    · rw [ite_eq_right hu]
      exact mul_nonneg ((Nat.cast_nonneg (α := ℝ) _).trans (hK r)) hsum
  simp_rw [split]
  rw [dirichlet_character_parseval, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (sum_le_sum fun r _ => hrow r).trans_eq
  rw [← mul_sum, sum_fiberwise_of_maps_to hmap]

/-- Pointwise second moment over all characters at a fixed modulus on any
shifted interval of `N` consecutive integers. -/
theorem fixed_modulus_polynomial_energy {q : ℕ} [NeZero q] (a : ℕ → ℂ) (M N : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Ioc M (M+N), χ n * a n‖ ^ 2) ≤
      (q.totient : ℝ) * (1 + (N : ℝ)/q) * ∑ n ∈ Ioc M (M+N), ‖a n‖^2 := by
  apply character_sum_sq_le_of_fiber_card (Ioc M (M+N)) (fun n : ℕ => (n : ZMod q)) a
  intro r
  let S := (Ioc M (M+N)).filter fun n : ℕ => (n : ZMod q) = r
  have hcard : S.card ≤ (range (N/q+1)).card := by
    apply card_le_card_of_injOn (fun n : ℕ => (n-M)/q)
    · intro n hn
      have h := mem_Ioc.mp (mem_filter.mp hn).1
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n-M ≤ N)))
    · intro i hi j hj he
      have hi' := mem_Ioc.mp (mem_filter.mp hi).1
      have hj' := mem_Ioc.mp (mem_filter.mp hj).1
      have hres : (i : ZMod q) = (j : ZMod q) := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
      have hdiff : ((i-M : ℕ) : ZMod q) = ((j-M : ℕ) : ZMod q) := by
        rw [Nat.cast_sub hi'.1.le, Nat.cast_sub hj'.1.le, hres]
      have hm := (ZMod.natCast_eq_natCast_iff ..).mp hdiff
      change (i-M) % q = (j-M) % q at hm
      change (i-M)/q = (j-M)/q at he
      have hh : i-M = j-M := by
        calc
          _ = q * ((i-M)/q) + (i-M)%q := (Nat.div_add_mod ..).symm
          _ = q * ((j-M)/q) + (j-M)%q := by rw [he, hm]
          _ = _ := Nat.div_add_mod ..
      omega
  rw [card_range] at hcard
  have hc : (S.card : ℝ) ≤ ((N/q : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  exact hc.trans (by linarith only [Nat.cast_div_le (α := ℝ) (m := N) (n := q)])

end AnalyticNumberTheory.DirichletLFunctions
