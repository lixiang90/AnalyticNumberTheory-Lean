import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Telescoping products of quadratic Euler factors

The product over all integers from two to a cutoff bounds below every
subproduct. This supplies a numerical lower bound for prime Euler products.
-/

open Finset
namespace AnalyticNumberTheory.AnalyticTools

/-- Telescoping the factors `(n-1)(n+1)/n²` over an initial interval. -/
theorem prod_one_sub_inv_sq_Icc (m : ℕ) :
    ∏ n ∈ Icc 2 (m+1), (1-1/(n:ℝ)^2) = ((m:ℝ)+2)/(2*((m:ℝ)+1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hi : Icc 2 (m+1+1) = insert (m+2) (Icc 2 (m+1)) := by
      ext n
      simp only [mem_Icc,mem_insert]
      omega
    rw [hi,prod_insert (by simp),ih]
    push_cast
    field_simp <;> ring

/-- Any finite set of indices at least two gives a product of quadratic
Euler factors bounded below by one half. -/
theorem half_le_prod_one_sub_inv_sq {S : Finset ℕ} (hS : ∀ n∈S, 2≤n) :
    1/2 ≤ ∏ n ∈ S, (1-1/(n:ℝ)^2) := by
  let m := S.sup id
  have hsub : S ⊆ Icc 2 (m+1) := fun n hn =>
    mem_Icc.mpr ⟨hS n hn,(Finset.le_sup (f:=id) hn).trans (Nat.le_succ m)⟩
  apply le_trans _ (prod_le_prod_of_subset_of_le_one₀ hsub (f:=fun n : ℕ => 1-1/(n:ℝ)^2) ?_ ?_)
  · rw [prod_one_sub_inv_sq_Icc]
    rw [le_div_iff₀ (by positivity)]
    linarith
  · intro n hn
    have hn' : 2≤(n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    have hs : 1≤(n:ℝ)^2 := by nlinarith only [hn',sq_nonneg ((n:ℝ)-1)]
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hs)
  · intro n _ _
    exact sub_le_self _ (by positivity)

end AnalyticNumberTheory.AnalyticTools
