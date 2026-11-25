import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityBalance

/-! # Logarithmic scaling in Montgomery's density estimates -/
open Real
namespace AnalyticNumberTheory.PrimeDistribution

/-- Passing from an integer cutoff X to its comparable conductor-height scale
H preserves the original logarithmic power, for any nonnegative integer k. -/
theorem montgomery_scale_log_power (k : ℕ) {X H Y σ : ℝ} (hX : 1≤X) (hH : 0≤H) (hY : 2≤Y)
    (hXH : X≤10*H) (hHY : H≤Y^2) (hσ : σ∈Set.Icc (1/2:ℝ) 1) :
    (1+Real.log X)^k*X^(montgomeryExponent σ) ≤
      (100*24^k)*(Real.log Y)^k*H^(montgomeryExponent σ) := by
  have he : 0 ≤ montgomeryExponent σ := by unfold montgomeryExponent;apply div_nonneg <;> nlinarith [hσ.2,hσ.1]
  have he' : montgomeryExponent σ≤2 := by
    unfold montgomeryExponent;apply (div_le_iff₀ (by linarith [hσ.1])).mpr;linarith [hσ.1]
  have hp := Real.rpow_le_rpow (zero_le_one.trans hX) hXH he
  rw [Real.mul_rpow (by norm_num) hH] at hp
  have hg : (10:ℝ)^(montgomeryExponent σ)≤100  := by
    convert (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(10:ℝ)) he') using 1 <;> norm_num
  have hZ := hp.trans (mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hH _))
  have hlog := Real.log_le_log (zero_lt_one.trans_le hX) (hXH.trans (mul_le_mul_of_nonneg_left hHY (by norm_num)))
  have hy₀ : 0<Y := by linarith
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hy₀.ne'),Real.log_pow] at hlog
  have hylog : 1/2≤Real.log Y := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hY)
  have h9 : Real.log (10:ℝ)≤9 := by simpa only [show (10:ℝ)-1=9 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)
  norm_num only [Nat.cast_ofNat] at hlog
  have hL : 1+Real.log X≤24*Real.log Y := by linarith only [hlog,h9,hylog]
  have h₇ := pow_le_pow_left₀ (by linarith [Real.log_nonneg hX] : 0≤1+Real.log X) hL k
  rw [mul_pow] at h₇
  exact (mul_le_mul h₇ hZ (Real.rpow_nonneg (zero_le_one.trans hX) _) (by positivity [show 0≤Real.log Y by linarith])).trans_eq (by ring)

/-- The twelve logarithms in the multiplicity-weighted detector estimate
remain twelve when expressed using the original height and conductor. -/
theorem montgomery_scale_log_twelve {X H Y σ : ℝ} (hX : 1≤X) (hH : 0≤H) (hY : 2≤Y)
    (hXH : X≤10*H) (hHY : H≤Y^2) (hσ : σ∈Set.Icc (1/2:ℝ) 1) :
    (1+Real.log X)^12*X^(montgomeryExponent σ) ≤
      (100*24^12)*(Real.log Y)^12*H^(montgomeryExponent σ) :=
  montgomery_scale_log_power 12 hX hH hY hXH hHY hσ

/-- Raising a logarithmic exponent by one costs at most a factor two on [2,∞). -/
theorem log_pow_le_twice_log_succ (k : ℕ) {Y : ℝ} (hY : 2≤Y) :
    (Real.log Y)^k≤2*(Real.log Y)^(k+1) := by
  have hs : 1/2≤Real.log Y := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hY)
  rw [pow_succ]
  nlinarith only [mul_le_mul_of_nonneg_right hs (pow_nonneg (by linarith : 0≤Real.log Y) k)]

end AnalyticNumberTheory.PrimeDistribution
