import AnalyticNumberTheory.PrimeDistribution.RiemannEiZeroSum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The trivial-zero tail and the constant in Riemann's formula -/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.PrimeDistribution

/-- The positive, decaying trivial-zero contribution in the single-endpoint Riemann formula. -/
def riemannTrivialZeroTail (x : ℝ) : ℝ := ∫ t in Ioi x, (t*(t^2-1)*Real.log t)⁻¹

private theorem tail_kernel_bound {x t : ℝ} (hx : 1<x) (ht : x<t) :
    ‖(t*(t^2-1)*Real.log t)⁻¹‖ ≤ ((x-1)*Real.log x)⁻¹*t^(-2:ℝ) := by
  have h₀ := zero_lt_one.trans (hx.trans ht)
  have h₂ : 0 < t^2-1 := by nlinarith [hx.trans ht]
  have hprod : (x-1)*t ≤ t^2-1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.le) h₀.le]
  have hlog := Real.log_le_log (zero_lt_one.trans hx) ht.le
  rw [Real.norm_of_nonneg (by positivity [Real.log_pos (hx.trans ht)]),Real.rpow_neg h₀.le,Real.rpow_two,← mul_inv_rev]
  apply inv_anti₀ (by positivity [sub_pos.mpr hx,Real.log_pos hx])
  calc
    _ = t*((x-1)*t)*Real.log x := by ring
    _ ≤ t*(t^2-1)*Real.log t := mul_le_mul (mul_le_mul_of_nonneg_left hprod h₀.le) hlog
      (Real.log_pos hx).le (mul_nonneg h₀.le h₂.le)

/-- The elementary trivial-zero density divided by log t is integrable on every tail above one. -/
theorem integrableOn_riemannTrivialZeroTail {x : ℝ} (hx : 1<x) :
    IntegrableOn (fun t : ℝ => (t*(t^2-1)*Real.log t)⁻¹) (Ioi x) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (zero_lt_one.trans hx)).const_mul
    (((x-1)*Real.log x)⁻¹)).mono' ?_ ?_
  · exact (show Measurable (fun t : ℝ => (t*(t^2-1)*Real.log t)⁻¹) by fun_prop).aestronglyMeasurable
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => tail_kernel_bound hx ht

/-- The trivial-zero tail is nonnegative and is at most 1/(x(x−1)log x). -/
theorem riemannTrivialZeroTail_bounds {x : ℝ} (hx : 1<x) :
    0 ≤ riemannTrivialZeroTail x ∧ riemannTrivialZeroTail x ≤ (x*(x-1)*Real.log x)⁻¹ := by
  have hx₀ := zero_lt_one.trans hx
  have hp (t : ℝ) (ht : x<t) : 0 ≤ (t*(t^2-1)*Real.log t)⁻¹ := by
    have h₀ := hx₀.trans ht
    have h₂ : 0 < t^2-1 := by nlinarith [hx.trans ht]
    positivity [Real.log_pos (hx.trans ht)]
  refine ⟨integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ioi).mono hp),?_⟩
  apply (integral_mono_ae (integrableOn_riemannTrivialZeroTail hx)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hx₀).const_mul (((x-1)*Real.log x)⁻¹))
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => (le_abs_self _).trans (tail_kernel_bound hx ht))).trans_eq
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hx₀]
  norm_num [Real.rpow_neg_one]
  ring

/-- The contribution of the trivial zeros tends to zero as the cutoff tends to infinity. -/
theorem tendsto_riemannTrivialZeroTail_atTop : Tendsto riemannTrivialZeroTail atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero (μ := volume) tendsto_id

/-- The finite trivial-zero integral is the difference of its two tails for either orientation. -/
theorem trivialZeroLogIntegral_eq_tail_sub {a b : ℝ} (ha : 1<a) (hb : 1<b) :
    trivialZeroLogIntegral a b = riemannTrivialZeroTail a - riemannTrivialZeroTail b :=
  (intervalIntegral.integral_Ioi_sub_Ioi' (integrableOn_riemannTrivialZeroTail ha)
    (integrableOn_riemannTrivialZeroTail hb)).symm

/-- The constant obtained by normalizing below the first prime, here at 3/2. -/
def riemannCountingConstant : ℂ := riemannEiZeroSum (3/2) -
  principalExponentialIntegral (Real.log (3/2) : ℂ) - (riemannTrivialZeroTail (3/2) : ℂ)

/-- Single-endpoint form of Riemann's explicit identity with one constant independent of x. -/
theorem riemannPrimeCounting_eq_Ei_zeroSum_tail_constant {x : ℝ} (hx : 1<x) :
    (riemannPrimeCounting (1/2) x : ℂ) = principalExponentialIntegral (Real.log x : ℂ) -
      riemannEiZeroSum x + (riemannTrivialZeroTail x : ℂ) + riemannCountingConstant := by
  have h := riemannPrimeCounting_eq_Ei_sub_zeroSum (a := 3/2) (by norm_num) (by norm_num) hx
  rw [trivialZeroLogIntegral_eq_tail_sub (by norm_num) hx,Complex.ofReal_sub] at h
  unfold riemannCountingConstant
  linear_combination h

end AnalyticNumberTheory.PrimeDistribution
