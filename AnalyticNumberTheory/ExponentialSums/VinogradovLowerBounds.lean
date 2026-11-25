import AnalyticNumberTheory.ExponentialSums.VinogradovDiagonal
import Mathlib.Algebra.Order.Chebyshev

/-!
# Lower bounds for Vinogradov mean values

The possible vectors of power sums fill a box with side lengths bounded by
`s N^j + 1`. Cauchy–Schwarz applied to their fibers gives the lower bound
from the total number of moments, complementary to the diagonal count.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- A finite system has at least as many equal-value pairs as the
Cauchy–Schwarz inequality for its fibers requires. -/
theorem sq_card_le_box_mul_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (B : Finset β) (f : α → β) (h : (P:Set α).MapsTo f B) :
    P.card^2 ≤ B.card*((P ×ˢ P).filter fun p => f p.1=f p.2).card := by
  classical
  let S := (P ×ˢ P).filter fun p => f p.1=f p.2
  let fiber (b : β) := P.filter (fun a => f a=b)
  have hs : (S:Set (α×α)).MapsTo (fun p => f p.1) B := by
    intro p hp
    exact h (mem_product.mp (mem_filter.mp hp).1).1
  have hf (b : β) : S.filter (fun p => f p.1=b) = fiber b ×ˢ fiber b := by
    ext p
    simp only [S,mem_filter,mem_product,fiber]
    grind
  have hP := card_eq_sum_card_fiberwise h
  have hS := card_eq_sum_card_fiberwise hs
  simp only [hf,card_product,← sq] at hS
  change P.card^2 ≤ B.card*S.card
  rw [hP,hS]
  simpa only [fiber,Nat.cast_id] using (sq_sum_le_card_mul_sum_sq (s:=B) (f:=fun b => (fiber b).card))

private def moments {s : ℕ} (k : ℕ) (x : Fin s → ℕ) (j : Fin k) : ℕ :=
  ∑ i, x i^(j.val+1)

/-- Finite lower bound at every degree and every moment, with the actual
side lengths of the box of power sums. -/
theorem vinogradovSolutionCount_box_lower (s k N : ℕ) :
    N^(2*s) ≤ (∏ j : Fin k, (s*N^(j.val+1)+1))*vinogradovSolutionCount s k N := by
  classical
  let P := Fintype.piFinset (fun _ : Fin s => Icc 1 N)
  let B := Fintype.piFinset (fun j : Fin k => Icc 0 (s*N^(j.val+1)))
  have h : (P:Set (Fin s → ℕ)).MapsTo (moments k) B := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro j
    refine mem_Icc.mpr ⟨Nat.zero_le _,?_⟩
    calc moments k x j ≤ ∑ _i : Fin s,N^(j.val+1) := sum_le_sum fun i _ =>
              Nat.pow_le_pow_left (mem_Icc.mp (Fintype.mem_piFinset.mp hx i)).2 _
         _ = _ := by simp
  have hl := sq_card_le_box_mul_collisions P B (moments k) h
  have he : ((P ×ˢ P).filter fun p => moments k p.1=moments k p.2).card =
      vinogradovSolutionCount s k N := by
    simp only [vinogradovSolutionCount,P]
    congr 1
    ext p
    simp only [mem_filter,moments,funext_iff]
  rw [he] at hl
  simpa [P,B,Fintype.card_piFinset,pow_mul,Nat.mul_comm 2 s] using hl

/-- Volume lower bound for the mean value, independent of any Vinogradov
mean-value upper estimate. -/
theorem vinogradovJ_box_lower (s k N : ℕ) :
    (N:ℝ)^(2*s) ≤ (∏ j : Fin k, ((s:ℝ)*N^(j.val+1)+1))*vinogradovJ s k N := by
  rw [vinogradovJ_eq_card_solutions]
  exact_mod_cast vinogradovSolutionCount_box_lower s k N

end AnalyticNumberTheory.ExponentialSums
