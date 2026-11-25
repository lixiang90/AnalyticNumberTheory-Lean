import AnalyticNumberTheory.ExponentialSums.PrimeDensityApproximation
import AnalyticNumberTheory.ExponentialSums.PrimeLinearSums

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
  let V := densityPrimeScale x q
  let L := 1 + Real.log x
  have hs := (Real.sqrt_le_sqrt hyx).trans (sqrt_le_density_scale (by linarith) hq)
  have hV : 0 ≤ V := (Real.sqrt_nonneg y).trans hs
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg (by linarith : 1 ≤ x)]
  have hylog := Real.log_le_log (zero_lt_one.trans_le hy) hyx
  have hlog : Real.log y ≤ L ^ 11 := (show Real.log y ≤ L by dsimp [L]; linarith).trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 11))
  have herror := (norm_primeExpSum_sub_logPrimeExpSum_le y α).trans
    ((le_abs_self _).trans (abs_psi_sub_theta_le_sqrt_mul_log hy))
  have hcomp := mul_le_mul hs hlog (Real.log_nonneg hy) hV
  have htri := norm_sub_le (primeExpSum y α) (primeExpSum y α - logPrimeExpSum y α)
  rw [sub_sub_cancel] at htri
  change ‖logPrimeExpSum y α‖ ≤ (C+2) * V * L^11
  have hmain : ‖primeExpSum y α‖ ≤ C * V * L^11 := H hq ha hα hx (zero_le_one.trans hy) hyx
  nlinarith only [htri, herror, hmain, hcomp]

/-- Removing the prime logarithms from the zero-density bound saves one
power of the logarithm. -/
theorem unweightedPrimeExpSum_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 4 ≤ x →
      ‖unweightedPrimeExpSum x α‖ ≤ C * densityPrimeScale x q * (1 + Real.log x)^10 := by
  obtain ⟨C, hC, H⟩ := logPrimeExpSum_zero_density
  refine ⟨2 + 8*C, by positivity, ?_⟩
  intro a q α x hq ha hα hx
  let V := densityPrimeScale x q
  let L := 1 + Real.log x
  have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
  rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at h4
  have hlog : 1 ≤ Real.log x := by linarith [Real.log_two_gt_d9]
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hs := sqrt_le_density_scale (by linarith : 0 ≤ x) hq
  have hV : 0 ≤ V := (Real.sqrt_nonneg x).trans hs
  have h := norm_sum_primes_le_sqrt_add_of_log_bound (by linarith : 2 ≤ x)
    (H := C * V * L^11) (f := fun p => AdditiveNumberTheory.e (α*p))
    (fun _ => (AdditiveNumberTheory.norm_e _).le) (fun k hk hkx => by
      have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      simpa only [logPrimeExpSum, Nat.floor_natCast] using H hq ha hα hx hk₁ hkx)
  have hsmall : Real.sqrt x ≤ V * L^10 := hs.trans (le_mul_of_one_le_right hV (one_le_pow₀ hL))
  have hlarge : 4 * (C * V * L^11) / Real.log x ≤ 8 * C * V * L^10 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hlog)).mpr
    have hr : L ≤ 2*Real.log x := by dsimp only [L]; linarith
    nlinarith only [mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 4*C*V*L^10)]
  change ‖unweightedPrimeExpSum x α‖ ≤ 2*Real.sqrt x + 4*(C*V*L^11)/Real.log x at h
  change ‖unweightedPrimeExpSum x α‖ ≤ (2+8*C)*V*L^10
  nlinarith only [h, hsmall, hlarge]

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
