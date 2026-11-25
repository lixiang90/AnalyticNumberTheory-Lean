import AnalyticNumberTheory.ExponentialSums.PrimeContourApproximation
import AnalyticNumberTheory.ExponentialSums.PrimeWeightTransfer

/-! # Prime weights at real frequencies in the contour method -/

noncomputable section
open Real
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

private theorem sqrt_le_contour_frequency {x q : ℝ} (hx : 1 ≤ x) (hq : 1 ≤ q) :
    Real.sqrt x ≤ primeContourFrequencyScale x q := by
  have hx₀ := zero_le_one.trans hx
  calc
    _ ≤ x^(7/8 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ ≤ x^(7/8 : ℝ)*q^(1/8 : ℝ) := le_mul_of_one_le_right (Real.rpow_nonneg hx₀ _)
      (Real.one_le_rpow hq (by norm_num))
    _ ≤ _ := le_add_of_nonneg_left (by positivity : 0 ≤ x/q^(1/8 : ℝ))

/-- For the sum over primes weighted by log p the contour bound holds
uniformly at every real endpoint y between 1 and x. -/
theorem logPrimeExpSum_contour :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x y : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 1 ≤ y → y ≤ x →
      ‖logPrimeExpSum y α‖ ≤ C*primeContourFrequencyScale x q*(1+Real.log x)^3 := by
  obtain ⟨C,hC,H⟩ := primeExpSum_contour
  refine ⟨C+2, by positivity, ?_⟩
  intro a q α x y hq ha hα hy hyx
  have hx := hy.trans hyx
  exact norm_logPrimeExpSum_le_of_primeExpSum (k := 2) hy hyx
    (sqrt_le_contour_frequency hx (by exact_mod_cast hq)) (H hq ha hα hx (zero_le_one.trans hy) hyx)

/-- Partial summation saves one logarithm for the unweighted prime sum. -/
theorem unweightedPrimeExpSum_contour :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 2 ≤ x →
      ‖unweightedPrimeExpSum x α‖ ≤ C*primeContourFrequencyScale x q*(1+Real.log x)^2 := by
  obtain ⟨C,hC,H⟩ := logPrimeExpSum_contour
  refine ⟨2+12*C, by positivity, ?_⟩
  intro a q α x hq ha hα hx
  exact norm_unweightedPrimeExpSum_le_of_logPrimeExpSum (k := 2) hx hC.le
    (sqrt_le_contour_frequency (by linarith) (by exact_mod_cast hq)) (fun y hy => H hq ha hα hy.1 hy.2)

/-- If Q ≤ q ≤ x/Q, all three prime weights save Q^(1/8) with a single
absolute constant. The unweighted sum has just two powers of the logarithm. -/
theorem prime_sums_contour_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x Q : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 2 ≤ x → 0 < Q → Q ≤ q → (q : ℝ)*Q ≤ x →
      ‖primeExpSum x α‖ ≤ C*(x/Q^(1/8 : ℝ))*(1+Real.log x)^3 ∧
      ‖logPrimeExpSum x α‖ ≤ C*(x/Q^(1/8 : ℝ))*(1+Real.log x)^3 ∧
      ‖unweightedPrimeExpSum x α‖ ≤ C*(x/Q^(1/8 : ℝ))*(1+Real.log x)^2 := by
  obtain ⟨A,hA,HA⟩ := primeExpSum_contour
  obtain ⟨B,hB,HB⟩ := logPrimeExpSum_contour
  obtain ⟨D,hD,HD⟩ := unweightedPrimeExpSum_contour
  let C := A+B+D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨2*C, by positivity, ?_⟩
  intro a q α x Q hq ha hα hx hQ hlo hhi
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hx₀ := zero_lt_one.trans_le hx₁
  have hscale := primeContourFrequencyScale_le_of_denominator_range hx₀ hQ hlo hhi
  have hV := (Real.sqrt_nonneg x).trans (sqrt_le_contour_frequency (q := (q : ℝ)) hx₁ (by exact_mod_cast hq))
  have hL : 0 ≤ 1+Real.log x := by linarith only [Real.log_nonneg hx₁]
  have convert_bound {b t : ℝ} (hb : b ≤ C) (ht : 0 ≤ t) :
      b*primeContourFrequencyScale x q*t ≤ (2*C)*(x/Q^(1/8 : ℝ))*t := by
    apply mul_le_mul_of_nonneg_right _ ht
    exact (mul_le_mul hb hscale hV hC.le).trans_eq (by ring)
  exact ⟨(HA hq ha hα hx₁ hx₀.le le_rfl).trans (convert_bound (by dsimp only [C]; linarith) (by positivity)),
    (HB hq ha hα hx₁ le_rfl).trans (convert_bound (by dsimp only [C]; linarith) (by positivity)),
    (HD hq ha hα hx).trans (convert_bound (by dsimp only [C]; linarith) (by positivity))⟩

end AnalyticNumberTheory.ExponentialSums
