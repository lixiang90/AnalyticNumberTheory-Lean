import AnalyticNumberTheory.DirichletLFunctions.CharacterPolynomialSquares
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialDiagonals
import AnalyticNumberTheory.AnalyticTools.Summation.LogarithmicTails

/-!
# Diagonals of squared character polynomials

The critical diagonal grows with the fourth power of the logarithm. On
the quarter line it acquires one power of the original polynomial length.
For a tail on the three-halves line the diagonal and its first moment
decay as the inverse fourth and second powers of the cutoff.
-/
noncomputable section
open Real Complex Finset
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.ExponentialSums
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem square_diagonal_le (S : Finset ℕ) (σ : ℝ) (M : ℕ) :
    (∑k∈Icc 1 (M^2),‖characterSquareWeight S σ k‖^2)≤
      ∑k∈Icc 1 (M^2),(k.divisors.card:ℝ)^2*(k:ℝ)^(-2*σ) := by
  apply sum_le_sum;intro k hk
  rw [characterSquareWeight_norm_sq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (by exact_mod_cast factorPairCount_le_divisors S (mem_Icc.mp hk).1) 2) (by positivity)

theorem characterSquareWeight_critical (S : Finset ℕ) {N : ℕ} (hN : 1≤N) :
    (∑k∈Icc 1 (N^2),‖characterSquareWeight S (1/2) k‖^2)≤(1+Real.log (N^2:ℕ))^4 := by
  have H := square_diagonal_le S (1/2) N
  norm_num at H
  exact H.trans (by simpa using divisor_diagonal_critical (N:=N^2) (Nat.one_le_pow _ _ hN))

theorem characterSquareWeight_quarter (S : Finset ℕ) {N : ℕ} (hN : 1≤N) :
    (∑k∈Icc 1 (N^2),‖characterSquareWeight S (1/4) k‖^2)≤2*(N:ℝ)*(1+Real.log (N^2:ℕ))^3 := by
  apply (square_diagonal_le S (1/4) N).trans
  have H := divisor_diagonal_quarter (N:=N^2) (Nat.one_le_pow _ _ hN)
  simpa only [show -2*(1/4:ℝ)=-(1/2) by norm_num,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg (α:=ℝ) N)] using H

private theorem restricted_diagonal_tail {N M : ℕ} {f : ℕ→ℝ}
    (hf : ∀n,0≤f n) :
    (∑j∈Icc 1 (M^2),(factorPairCount (Ioc N M) j:ℝ)^2*f j) ≤
      ∑j∈Ioc (N^2) (M^2),(j.divisors.card:ℝ)^2*f j := by
  have he : (Icc 1 (M^2)).filter (fun j=>N^2<j)=Ioc (N^2) (M^2) := by ext j;simp;omega
  rw [←he,sum_filter]
  apply sum_le_sum;intro j hj
  by_cases hn : N^2<j
  · rw [if_pos hn]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by exact_mod_cast factorPairCount_le_divisors (Ioc N M) (mem_Icc.mp hj).1) 2) (hf j)
  · rw [if_neg hn, factorPairCount_eq_zero (N:=N) (fun n (h : n∈Ioc N M) => (mem_Ioc.mp h).1) (le_of_not_gt hn)];simp

/-- Uniform diagonal and first moment for the three-halves line, including
all finite tail endpoints. -/
theorem characterSquareWeight_tail : ∃ C : ℝ,0<C ∧ ∀ {N : ℕ},1≤N → ∀M : ℕ,
    (∑k∈Icc 1 (M^2),‖characterSquareWeight (Ioc N M) (3/2) k‖^2)≤
      C/(N:ℝ)^4*(1+Real.log (N^2:ℕ))^3 ∧
    (∑k∈Icc 1 (M^2),(k:ℝ)*‖characterSquareWeight (Ioc N M) (3/2) k‖^2)≤
      C/(N:ℝ)^2*(1+Real.log (N^2:ℕ))^3 := by
  let d := fun j : ℕ=>(j.divisors.card:ℝ)^2
  have hd {X : ℕ} (hX : 1≤X) : (∑j∈Icc 1 X,d j)≤1*(X:ℝ)*(1+Real.log X)^3 := by
    simpa only [d,one_mul,max_eq_left hX] using sum_Icc_card_divisors_sq_le X
  obtain ⟨C,hC,H⟩ := logarithmic_power_tail 3 3 (by decide) (f:=d) (fun j=>sq_nonneg _) zero_lt_one hd
  obtain ⟨D,hD,K⟩ := logarithmic_power_tail 3 2 (by decide) (f:=d) (fun j=>sq_nonneg _) zero_lt_one hd
  refine ⟨max C D,hC.trans_le (le_max_left ..),?_⟩
  intro N hN M
  have hNs := Nat.one_le_pow 2 N hN
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hL : 0≤(1+Real.log (N^2:ℕ))^3 := by positivity [Real.log_nonneg (show (1:ℝ)≤(N^2:ℕ) by exact_mod_cast hNs)]
  have he (k : ℕ) : ‖characterSquareWeight (Ioc N M) (3/2) k‖^2 =
        (factorPairCount (Ioc N M) k:ℝ)^2*((k:ℝ)^3)⁻¹ := by
    rw [characterSquareWeight_norm_sq,show -2*(3/2:ℝ)= -(3:ℝ) by norm_num,Real.rpow_neg (Nat.cast_nonneg _)];norm_num
  constructor
  · simp_rw [he]
    apply (restricted_diagonal_tail (N:=N) (M:=M) (f:=fun k=>((k:ℝ)^3)⁻¹) (fun k=>by positivity)).trans
    have hh := H hNs (M^2)
    simp only [d,div_eq_mul_inv] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hL
    push_cast
    calc C*((N:ℝ)^2*(((N:ℝ)^2)^3)⁻¹)=C/(N:ℝ)^4 := by field_simp
         _ ≤ _ := div_le_div_of_nonneg_right (le_max_left ..) (by positivity)
  · have hw (k : ℕ) (hk : k∈Icc 1 (M^2)) :
        (k:ℝ)*‖characterSquareWeight (Ioc N M) (3/2) k‖^2=
        (factorPairCount (Ioc N M) k:ℝ)^2*((k:ℝ)^2)⁻¹ := by
      have hk' : (k:ℝ)≠0 := (Nat.cast_pos.mpr (mem_Icc.mp hk).1).ne'
      rw [he];field_simp
    rw [sum_congr rfl hw]
    apply (restricted_diagonal_tail (N:=N) (M:=M) (f:=fun k=>((k:ℝ)^2)⁻¹) (fun k=>by positivity)).trans
    have hh := K hNs (M^2)
    simp only [d,div_eq_mul_inv] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hL
    push_cast
    calc D*((N:ℝ)^2*(((N:ℝ)^2)^2)⁻¹)=D/(N:ℝ)^2 := by field_simp
         _ ≤ _ := div_le_div_of_nonneg_right (le_max_right ..) (by positivity)

end AnalyticNumberTheory.DirichletLFunctions
