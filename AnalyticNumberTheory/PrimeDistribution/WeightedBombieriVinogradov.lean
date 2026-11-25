import AnalyticNumberTheory.PrimeDistribution.ProgressionCountingBounds
import AnalyticNumberTheory.SieveMethods.SquarefreeDivisorMoments

/-! # A divisor-weighted Bombieri–Vinogradov theorem for prime counts

The maximal error may be weighted by the square of the divisor function on squarefree
moduli while retaining an arbitrary fixed logarithmic saving.
-/
noncomputable section
open Finset Filter Real
open scoped Topology
namespace AnalyticNumberTheory.PrimeDistribution

/-- Maximal prime-counting errors in squarefree moduli, with the Selberg sieve
weight `τ(d)²` and an arbitrary power of logarithmic saving. -/
theorem squarefree_weighted_bombieri_vinogradov (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Icc 1 ⌊√x/(log x)^B⌋₊).filter Squarefree,
        (d.divisors.card : ℝ)^2 * maximalPiAPError x d) ≤ K*x/(log x)^A := by
  obtain ⟨B, hB, C, hC, hBV⟩ := bombieriVinogradov_piAP (2*A+16)
  obtain ⟨D, hD, hmoment⟩ := SieveMethods.squarefree_divisor_fourth_over_totient
  let c : ℝ := 2 + (log 2)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  let K := √(C*c*D)
  have hK : 0 < K := Real.sqrt_pos.2 (by positivity)
  refine ⟨B,hB,K,hK,?_⟩
  filter_upwards [hmoment, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hM hx hlog
  have hx₀ : 0 < x := by linarith
  have hl : 0 < log x := by linarith
  let Q := √x / (log x)^B
  let S := (Icc 1 ⌊Q⌋₊).filter Squarefree
  change (∑ d ∈ S, (d.divisors.card:ℝ)^2 * maximalPiAPError x d) ≤ _
  by_cases hQ : 1 ≤ Q
  · have hQx : Q ≤ x := (div_le_self (sqrt_nonneg _) (Real.one_le_rpow hlog hB)).trans
      ((Real.sqrt_le_iff).2 ⟨hx₀.le, by nlinarith⟩)
    have hd₁ : ∀ d ∈ S, 1 ≤ d := fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1
    have hdQ : ∀ d ∈ S, (d:ℝ) ≤ Q := fun d hd =>
      (Nat.le_floor_iff (by linarith)).mp (mem_Icc.mp (mem_filter.mp hd).1).2
    have hE : ∀ d ∈ S, 0 ≤ maximalPiAPError x d := fun d hd =>
      maximalPiAPError_nonneg hx (hd₁ d hd)
    have hfirst : (∑ d ∈ S, maximalPiAPError x d) ≤ C*x/(log x)^(2*A+16) :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun d hd _ => maximalPiAPError_nonneg hx (mem_Icc.mp hd).1)).trans (hBV hx hQ le_rfl)
    have hsecond : (∑ d ∈ S, (d.divisors.card:ℝ)^4 * maximalPiAPError x d) ≤
        (c*x)*(D*(log x)^16) := by
      calc
        _ ≤ ∑ d ∈ S, (c*x)*((d.divisors.card:ℝ)^4/d.totient) := by
          apply sum_le_sum
          intro d hd
          have H := mul_le_mul_of_nonneg_left
            (maximalPiAPError_le_div_totient hx (hd₁ d hd) ((hdQ d hd).trans hQx))
            (show (0:ℝ) ≤ (d.divisors.card:ℝ)^4 by positivity)
          calc
            _ ≤ _ := H
            _ = _ := by dsimp [c]; ring
        _ = (c*x)*∑ d ∈ S, (d.divisors.card:ℝ)^4/d.totient := by rw [mul_sum]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ hM
          apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
          intro d hd
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd₁ d hd, Nat.le_floor ((hdQ d hd).trans hQx)⟩,
            (mem_filter.mp hd).2⟩
    have H := sum_sq_le_sum_mul_sum_of_sq_le_mul S
      hE (g := fun d => (d.divisors.card:ℝ)^4 * maximalPiAPError x d)
      (fun d hd => mul_nonneg (by positivity) (hE d hd))
      (r := fun d => (d.divisors.card:ℝ)^2 * maximalPiAPError x d)
      (by intros; apply le_of_eq; ring)
    have H' := H.trans (mul_le_mul hfirst hsecond
      (sum_nonneg (fun d hd => mul_nonneg (by positivity) (hE d hd))) (by positivity))
    have hp : (log x)^(2*A+16) = ((log x)^A)^2 * (log x)^16 := by
      rw [Real.rpow_add hl, mul_comm 2 A, Real.rpow_mul hl.le]
      norm_num
    have hKs : K^2 = C*c*D := Real.sq_sqrt (by positivity)
    have hid : (C*x/(log x)^(2*A+16))*((c*x)*(D*(log x)^16)) = (K*x/(log x)^A)^2 := by
      rw [hp, div_pow, mul_pow K x, hKs]
      field_simp [hl.ne', (Real.rpow_pos_of_pos hl A).ne']
      <;> ring
    rw [hid] at H'
    exact le_of_sq_le_sq H' (by positivity)
  · have hempty : Icc 1 ⌊Q⌋₊ = ∅ := Icc_eq_empty_of_lt ((Nat.floor_lt' (by norm_num : (1:ℕ) ≠ 0)).2 (by simpa using lt_of_not_ge hQ))
    simp [S, hempty, show 0 ≤ K*x/(log x)^A by positivity]

end AnalyticNumberTheory.PrimeDistribution
