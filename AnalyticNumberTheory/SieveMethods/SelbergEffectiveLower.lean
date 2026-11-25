import AnalyticNumberTheory.SieveMethods.SelbergDenominatorFinite
import AnalyticNumberTheory.SieveMethods.SelbergSixHarmonics
import AnalyticNumberTheory.SieveMethods.SelbergWeightedDenominator

/-!
# Effective lower estimates for the Selberg denominators

The finite certificate and the Euler factors at two and three cover all
cutoffs from six on. Abel summation then gives the weighted estimate needed
for the Brun–Titchmarsh inequality.
-/

open Real
namespace AnalyticNumberTheory.SieveMethods

/-- The unrestricted squarefree reciprocal-totient sum exceeds log x by 1.076
at every real cutoff x ≥ 6. -/
theorem selbergDenominator_ge_log_surplus {x : ℝ} (hx : 6≤x) :
    log x+1.076≤selbergDenominator x := by
  rcases lt_or_ge x 1024 with h | h
  · exact selbergDenominator_ge_log_finite hx h
  have h' := selbergDenominator_ge_two_prime_log (by linarith : 0<x)
  have hpow := Real.log_le_log (by norm_num : (0:ℝ)<2^19) (by norm_num : (2:ℝ)^19≤3^12)
  rw [Real.log_pow,Real.log_pow] at hpow
  norm_num only [Nat.cast_ofNat] at hpow
  have hinv : 12/x≤12/1024 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h
  linarith only [h',hpow,hinv,Real.log_two_gt_d9,euler_constant_gt_56]

/-- At every real cutoff z ≥ 100 the weighted denominator is at least log z + 0.31. -/
theorem selbergWeightedDenominator_ge_log {z : ℝ} (hz : 100≤z) :
    log z+0.31≤selbergWeightedDenominator z :=
  selbergWeightedDenominator_ge_of_surplus (fun _ => selbergDenominator_ge_log_surplus) hz

end AnalyticNumberTheory.SieveMethods
