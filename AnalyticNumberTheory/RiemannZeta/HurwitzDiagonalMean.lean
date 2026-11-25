import AnalyticNumberTheory.RiemannZeta.HurwitzVerticalPolynomials
import AnalyticNumberTheory.AnalyticTools.ConvergentDiagonal

/-!
# The diagonal mean of long Hurwitz polynomials

The initial segment through `⌊√T⌋+1` is short enough that separated-frequency
orthogonality extracts its diagonal. The rest of the polynomial has vanishing
normalized square mean by square summability of the coefficients.
-/

open Real Complex Finset MeasureTheory Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem tendsto_hurwitzVerticalEnergy {a σ : ℝ} (ha : 0<a) (hσ : 1/2<σ) :
    Tendsto (fun n : ℕ => hurwitzVerticalEnergy a σ (Icc 0 n)) atTop
      (𝓝 (∑' n : ℕ, ((n:ℝ)+a)^(-2*σ))) := by
  have H := (summable_hurwitzVerticalEnergy ha hσ).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply H.congr
  intro n
  change (∑ k ∈ range (n+1), ((k:ℝ)+a)^(-2*σ)) = _
  rw [show range (n+1) = Icc 0 n by ext k; simp]
  rfl

private theorem Icc_split {E : Type*} [AddCommGroup E] (f : ℕ → E) {M N : ℕ} (h : M≤N) :
    (∑ n ∈ Icc 0 N, f n) - (∑ n ∈ Icc 0 M, f n) = ∑ n ∈ Ioc M N, f n := by
  have h₁ : Disjoint (Icc 0 M) (Ioc M N) := disjoint_left.mpr fun n hn hn' => by
    have := (mem_Icc.mp hn).2; have := (mem_Ioc.mp hn').1; omega
  have h₂ : Icc 0 M ∪ Ioc M N = Icc 0 N := by ext n; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [←h₂,sum_union h₁]; abel

/-- The mean square of the polynomial through `⌊T⌋+1` converges to the full diagonal. -/
theorem tendsto_long_hurwitzPolynomial_squareMean {a σ : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) (hσ : 1/2<σ) :
    Tendsto (fun T : ℝ => intervalSquareMean 1 T T (hurwitzVerticalPolynomial a σ (Icc 0 (⌊T⌋₊+1))))
      atTop (𝓝 (∑' n : ℕ, ((n:ℝ)+a)^(-2*σ))) := by
  let P (n : ℕ) := hurwitzVerticalPolynomial a σ (Icc 0 n)
  let D (n : ℕ) := hurwitzVerticalEnergy a σ (Icc 0 n)
  apply tendsto_squareMean_of_convergent_diagonal P D (K:=4*π) (L:=2)
    (N:=fun T => ⌊T⌋₊+1)
    (fun n => continuous_hurwitzVerticalPolynomial ha.1 σ _)
    (tendsto_hurwitzVerticalEnergy ha.1 hσ) (by positivity) (by norm_num)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    refine ⟨le_rfl,?_⟩
    push_cast; linarith [Nat.floor_le (by linarith : 0≤T)]
  · intro n hn T _
    exact hurwitzVerticalPolynomial_mean_square ha σ hn _ (fun i hi => (mem_Icc.mp hi).2) 1 T
  · intro m n hmn T ht
    have he (t : ℝ) : ‖(P m-P n) t‖ = ‖hurwitzVerticalPolynomial a σ (Ioc m n) t‖ := by
      rw [Pi.sub_apply,norm_sub_rev]; exact congrArg norm (Icc_split _ hmn)
    have he' : D n-D m = hurwitzVerticalEnergy a σ (Ioc m n) := Icc_split _ hmn
    by_cases hn : n=0
    · subst n; have := Nat.eq_zero_of_le_zero hmn; subst m; simp
    rw [he']; simp_rw [he]
    have h := (abs_le.mp (hurwitzVerticalPolynomial_mean_square ha σ (Nat.pos_of_ne_zero hn)
      (Ioc m n) (fun i hi => (mem_Ioc.mp hi).2) 1 T)).2
    linarith only [h,hurwitzVerticalEnergy_nonneg ha.1.le σ (Ioc m n)]
  · intro m n hmn
    apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
    exact fun i _ _ => Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg i) ha.1.le) _

end AnalyticNumberTheory.RiemannZeta
