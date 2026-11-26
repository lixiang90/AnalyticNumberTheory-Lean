import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Explicit comparison of logarithmic powers with positive powers -/

namespace AnalyticNumberTheory.AnalyticTools

/-- A logarithmic power is bounded on the whole ray t ≥ 1 by a positive
power of t with an explicit constant depending on the two exponents. -/
theorem log_pow_le_rpow_mul_const (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 1 ≤ t) :
    (Real.log t)^k ≤ ((k : ℝ)/δ)^k*t^δ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.one_le_rpow ht hδ.le
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have ht₀ := zero_le_one.trans ht
  have h := Real.log_le_rpow_div ht₀ (div_pos hδ hk₀)
  apply (pow_le_pow_left₀ (Real.log_nonneg ht) h k).trans_eq
  rw [show t^(δ/(k : ℝ))/(δ/(k : ℝ)) = ((k : ℝ)/δ)*t^(δ/(k : ℝ)) by field_simp]
  rw [mul_pow, ← Real.rpow_mul_natCast ht₀, div_mul_cancel₀ _ hk₀.ne']

end AnalyticNumberTheory.AnalyticTools
