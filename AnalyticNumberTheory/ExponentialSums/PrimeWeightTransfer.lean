import AnalyticNumberTheory.ExponentialSums.PrimeLinearSums

/-! # Transferring uniform bounds between the three linear prime weights -/

noncomputable section
open Finset Real
open AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

/-- Removing proper prime powers costs at most two units in the coefficient of
a majorant V(1+log x)^(k+1), provided V dominates sqrt x. -/
theorem norm_logPrimeExpSum_le_of_primeExpSum {x y α C V : ℝ} {k : ℕ}
    (hy : 1 ≤ y) (hyx : y ≤ x) (hs : Real.sqrt x ≤ V)
    (h : ‖primeExpSum y α‖ ≤ C*V*(1+Real.log x)^(k+1)) :
    ‖logPrimeExpSum y α‖ ≤ (C+2)*V*(1+Real.log x)^(k+1) := by
  let L := 1+Real.log x
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg (hy.trans hyx)]
  have hV := (Real.sqrt_nonneg x).trans hs
  have hlog : Real.log y ≤ L^(k+1) := by
    have h₁ := Real.log_le_log (zero_lt_one.trans_le hy) hyx
    exact (by dsimp [L]; linarith only [h₁] : Real.log y ≤ L).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ k+1 by omega))
  have herr := (norm_primeExpSum_sub_logPrimeExpSum_le y α).trans
    ((le_abs_self _).trans (abs_psi_sub_theta_le_sqrt_mul_log hy))
  have hprod := mul_le_mul ((Real.sqrt_le_sqrt hyx).trans hs) hlog (Real.log_nonneg hy) hV
  have htri := norm_sub_le (primeExpSum y α) (primeExpSum y α-logPrimeExpSum y α)
  rw [sub_sub_cancel] at htri
  change _ ≤ C*V*L^(k+1) at h
  change _ ≤ (C+2)*V*L^(k+1)
  nlinarith only [htri,herr,hprod,h]

/-- A uniform bound C V (1+log x)^(k+1) for the log-weighted prime sums up to
x gives the unweighted sum at x with one fewer logarithm, whenever V ≥ sqrt x. -/
theorem norm_unweightedPrimeExpSum_le_of_logPrimeExpSum {x α C V : ℝ} {k : ℕ}
    (hx : 2 ≤ x) (hC : 0 ≤ C) (hs : Real.sqrt x ≤ V)
    (h : ∀ y ∈ Set.Icc 1 x, ‖logPrimeExpSum y α‖ ≤ C*V*(1+Real.log x)^(k+1)) :
    ‖unweightedPrimeExpSum x α‖ ≤ (2+12*C)*V*(1+Real.log x)^k := by
  let L := 1+Real.log x
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx₁]
  have hL₀ := zero_le_one.trans hL
  have hV := (Real.sqrt_nonneg x).trans hs
  have hlog : 1/2 ≤ Real.log x := by
    linarith only [Real.log_two_gt_d9,Real.log_le_log (by norm_num : (0 : ℝ)<2) hx]
  have hlog₀ : 0 < Real.log x := by linarith
  have H := norm_sum_primes_le_sqrt_add_of_log_bound hx (H := C*V*L^(k+1))
    (f := fun p => AdditiveNumberTheory.e (α*p)) (fun _ => (AdditiveNumberTheory.norm_e _).le)
    (fun n hn hnx => by
      have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      simpa only [logPrimeExpSum,Nat.floor_natCast] using h n ⟨hn₁,hnx⟩)
  have hs' := hs.trans (le_mul_of_one_le_right hV (one_le_pow₀ hL (n := k)))
  have hb : 4*(C*V*L^(k+1))/Real.log x ≤ 12*C*V*L^k := by
    apply (div_le_iff₀ hlog₀).mpr
    rw [pow_succ]
    have hl : L ≤ 3*Real.log x := by dsimp only [L]; linarith only [hlog]
    nlinarith only [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4*C*V*L^k)]
  change ‖unweightedPrimeExpSum x α‖ ≤ 2*Real.sqrt x + 4*(C*V*L^(k+1))/Real.log x at H
  change _ ≤ (2+12*C)*V*L^k
  nlinarith only [H,hs',hb]

end AnalyticNumberTheory.ExponentialSums
