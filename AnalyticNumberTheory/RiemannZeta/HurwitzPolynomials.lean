import AnalyticNumberTheory.RiemannZeta.HurwitzApproximation
import AnalyticNumberTheory.SieveMethods.SeparatedMeanValues

/-!
# Mean values of finite Hurwitz polynomials

The logarithms of `n+a` for `1 ≤ n ≤ N` are separated by at least
`1/(2N)` when `0 < a ≤ 1`. This gives a uniform mean value theorem
for any subset of these indices.
-/

open Complex Real Finset Filter MeasureTheory
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.RiemannZeta

/-- Critical-line Hurwitz polynomial over an arbitrary finite set of indices. -/
noncomputable def hurwitzPolynomial (a : ℝ) (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (((n:ℝ)+a:ℝ):ℂ)^(-((1/2:ℂ)+t*I))

/-- Diagonal contribution from a finite set of positive indices. -/
noncomputable def hurwitzDiagonal (a : ℝ) (S : Finset ℕ) : ℝ := ∑ n ∈ S, ((n:ℝ)+a)⁻¹

theorem continuous_hurwitzPolynomial {a : ℝ} (ha : 0<a) (S : Finset ℕ) :
    Continuous (hurwitzPolynomial a S) := by
  unfold hurwitzPolynomial
  apply continuous_finsetSum
  intro n _
  simp_rw [critical_monomial_eq (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha)]
  fun_prop

/-- Separation of logarithmic frequencies for a real shift of the nonnegative integers. -/
theorem log_shift_gap {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) {p q N : ℕ}
    (hpq : p<q) (hq : q≤N) :
    (2*(N:ℝ))⁻¹ ≤ Real.log ((q:ℝ)+a)-Real.log ((p:ℝ)+a) := by
  have hp' := add_pos_of_nonneg_of_pos (Nat.cast_nonneg p) ha.1
  have hq' := add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) ha.1
  have h := Real.log_le_sub_one_of_pos (div_pos hp' hq')
  rw [Real.log_div hp'.ne' hq'.ne'] at h
  have hqN : (q:ℝ)≤N := by exact_mod_cast hq
  have hdiff : (p:ℝ)+1≤q := by exact_mod_cast hpq
  calc _ ≤ ((q:ℝ)+a)⁻¹ := inv_anti₀ hq' (by linarith only [hqN,hdiff,ha.2,(Nat.cast_nonneg p : 0≤(p:ℝ))])
       _ ≤ ((q:ℝ)-p)/(q+a) := by rw [← one_div]; gcongr; linarith
       _ = 1-((p:ℝ)+a)/(q+a) := by field_simp; ring
       _ ≤ _ := by linarith

/-- The mean square differs from interval length times the diagonal by at
most `4πN` times the diagonal, uniformly in the shift and both endpoints. -/
theorem hurwitzPolynomial_mean_square {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1)
    {N : ℕ} (S : Finset ℕ) (hS : S⊆Icc 1 N) (u v : ℝ) :
    |(∫ t in u..v, ‖hurwitzPolynomial a S t‖^2)-(v-u)*hurwitzDiagonal a S| ≤
      4*π*N*hurwitzDiagonal a S := by
  by_cases hn : N=0
  · subst N
    have he : S=∅ := subset_empty.mp (by simpa using hS)
    simp [he,hurwitzPolynomial,hurwitzDiagonal]
  let x := fun n : ℕ => -Real.log ((n:ℝ)+a)
  let c := fun n : ℕ => (((√((n:ℝ)+a))⁻¹:ℝ):ℂ)
  have hN : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsep (i : ℕ) (hi : i∈S) (j : ℕ) (hj : j∈S) (hne : i≠j) :
      (2*(N:ℝ))⁻¹ ≤ |x i-x j| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := log_shift_gap ha h (mem_Icc.mp (hS hj)).2
      dsimp [x]; rw [neg_sub_neg]; exact hh.trans (le_abs_self _)
    · have hh := log_shift_gap ha h (mem_Icc.mp (hS hi)).2
      rw [abs_sub_comm]; dsimp [x]; rw [neg_sub_neg]; exact hh.trans (le_abs_self _)
  have H := separated_frequency_mean_square S x c (by positivity : 0<(2*(N:ℝ))⁻¹) hsep u v
  have hcoef (n : ℕ) : ‖c n‖^2 = ((n:ℝ)+a)⁻¹ := by
    have hp := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha.1
    simp only [c,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),inv_pow,Real.sq_sqrt hp.le]
  have hpoly (t : ℝ) : hurwitzPolynomial a S t = ∑ n ∈ S,c n*Complex.exp (I*(x n:ℂ)*t) := by
    exact sum_congr rfl fun n _ => critical_monomial_eq (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha.1) t
  simp only [← hpoly,hcoef,inv_inv] at H
  exact H.trans_eq (by unfold hurwitzDiagonal; ring)

end AnalyticNumberTheory.RiemannZeta
