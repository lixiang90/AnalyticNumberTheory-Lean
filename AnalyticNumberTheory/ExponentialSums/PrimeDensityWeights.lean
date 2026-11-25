import AnalyticNumberTheory.ExponentialSums.PrimeDensityApproximation
import AnalyticNumberTheory.ExponentialSums.PrimeWeightTransfer

/-! # Prime weights and balanced denominators in the zero-density method -/

noncomputable section

open Finset Real
open AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

private lemma sqrt_le_density_scale {x : ℝ} {q : ℕ} (hx : 0 ≤ x) (hq : 1 ≤ q) :
    Real.sqrt x ≤ densityPrimeScale x q :=
  (Real.sqrt_le_sqrt (le_mul_of_one_le_right hx (by exact_mod_cast hq : 1 ≤ (q : ℝ)))).trans
    (sqrt_mul_le_densityPrimeScale hx (Nat.cast_nonneg _))

/-- The zero-density bound on a linear prime sum weighted by `log p`,
uniformly in its endpoint up to `x`. -/
theorem logPrimeExpSum_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x y : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 4 ≤ x → 1 ≤ y → y ≤ x →
      ‖logPrimeExpSum y α‖ ≤ C * densityPrimeScale x q * (1 + Real.log x)^11 := by
  obtain ⟨C, hC, H⟩ := primeExpSum_zero_density
  refine ⟨C+2, by positivity, ?_⟩
  intro a q α x y hq ha hα hx hy hyx
  exact norm_logPrimeExpSum_le_of_primeExpSum (k := 10) hy hyx
    (sqrt_le_density_scale (by linarith) hq) (H hq ha hα hx (zero_le_one.trans hy) hyx)

/-- Removing the prime logarithms from the zero-density bound saves one
power of the logarithm. -/
theorem unweightedPrimeExpSum_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 4 ≤ x →
      ‖unweightedPrimeExpSum x α‖ ≤ C * densityPrimeScale x q * (1 + Real.log x)^10 := by
  obtain ⟨C, hC, H⟩ := logPrimeExpSum_zero_density
  refine ⟨2+12*C, by positivity, ?_⟩
  intro a q α x hq ha hα hx
  exact norm_unweightedPrimeExpSum_le_of_logPrimeExpSum (k := 10) (by linarith) hC.le
    (sqrt_le_density_scale (by linarith) hq) (fun y hy => H hq ha hα hx hy.1 hy.2)

/-- The three weight conventions on the balanced range of the zero-density
method, with a common absolute constant. -/
theorem prime_sums_zero_density_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x Q : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 4 ≤ x → 0 < Q → Q ≤ x^(1/4 : ℝ) →
      Q ≤ q → (q : ℝ)*Q ≤ x →
      ‖primeExpSum x α‖ ≤ C*x/Real.sqrt Q * (1+Real.log x)^11 ∧
      ‖logPrimeExpSum x α‖ ≤ C*x/Real.sqrt Q * (1+Real.log x)^11 ∧
      ‖unweightedPrimeExpSum x α‖ ≤ C*x/Real.sqrt Q * (1+Real.log x)^10 := by
  obtain ⟨A, hA, HA⟩ := primeExpSum_zero_density
  obtain ⟨B, hB, HB⟩ := logPrimeExpSum_zero_density
  obtain ⟨D, hD, HD⟩ := unweightedPrimeExpSum_zero_density
  let C := A+B+D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨4*C, by positivity, ?_⟩
  intro a q α x Q hq ha hα hx hQ hQx hlo hhi
  have hx₀ : 0 < x := by linarith
  have hbound := densityPrimeScale_le_of_denominator_range hx₀ hQ hQx hlo hhi
  have hV := (Real.sqrt_nonneg _).trans (sqrt_le_density_scale hx₀.le hq)
  have hlog := Real.log_nonneg (by linarith : 1 ≤ x)
  have convert_bound {k t : ℝ} (hk : k ≤ C) (ht : 0 ≤ t) :
      k * densityPrimeScale x q * t ≤ (4*C)*x/Real.sqrt Q * t := by
    apply mul_le_mul_of_nonneg_right _ ht
    exact (mul_le_mul hk hbound hV hC.le).trans_eq (by ring)
  have hcA : A ≤ C := by dsimp only [C]; linarith
  have hcB : B ≤ C := by dsimp only [C]; linarith
  have hcD : D ≤ C := by dsimp only [C]; linarith
  exact ⟨(HA hq ha hα hx hx₀.le le_rfl).trans (convert_bound hcA (by positivity)),
    (HB hq ha hα hx (by linarith) le_rfl).trans (convert_bound hcB (by positivity)),
    (HD hq ha hα hx).trans (convert_bound hcD (by positivity))⟩

end AnalyticNumberTheory.ExponentialSums
