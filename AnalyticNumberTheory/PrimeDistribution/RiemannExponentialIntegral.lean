import AnalyticNumberTheory.AnalyticTools.ExponentialIntegral
import AnalyticNumberTheory.PrimeDistribution.PrimeCountingExplicitFormula

/-! # Riemann's logarithmic zero integrals in terms of the principal exponential integral -/

noncomputable section

open Filter Finset Complex
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- On the positive logarithmic ray of an exponent with positive real part,
the derivative of Ei(z log t) is t^(z−1)/log t. -/
theorem hasDerivAt_exponentialIntegral_log {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => principalExponentialIntegral (z*(Real.log u : ℂ)))
      ((t : ℂ)^(z-1)*(↑((Real.log t)⁻¹) : ℂ)) t := by
  have ht₀ := zero_lt_one.trans ht
  have hl := Real.log_pos ht
  have hslit : z*(Real.log t : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr
    (Or.inl (by simpa using mul_pos hz hl))
  have h := (hasDerivAt_principalExponentialIntegral hslit).scomp t
    ((Real.hasDerivAt_log ht₀.ne').ofReal_comp.const_mul z)
  apply h.congr_deriv
  have hz₀ : z ≠ 0 := fun he => by simp [he] at hz
  have he : Complex.exp (z*(Real.log t : ℂ)) = (t : ℂ)^z := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht₀.ne'), ←Complex.ofReal_log ht₀.le,mul_comm z]
  rw [smul_eq_mul,he,Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht₀.ne'),Complex.cpow_one]
  push_cast
  field_simp [hz₀,Complex.ofReal_ne_zero.mpr ht₀.ne',Complex.ofReal_ne_zero.mpr hl.ne']

/-- The logarithmic-integral increment is a difference of principal exponential integrals,
independently of the ordering of the two endpoints above one. -/
theorem zeroLogIntegral_eq_exponentialIntegral_sub {z : ℂ} (hz : 0 < z.re) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) :
    zeroLogIntegral z a b = principalExponentialIntegral (z*(Real.log b : ℂ)) -
      principalExponentialIntegral (z*(Real.log a : ℂ)) := by
  have h₁ {t : ℝ} (ht : t ∈ Set.uIcc a b) : 1 < t := (lt_min ha hb).trans_le ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_exponentialIntegral_log hz (h₁ ht))
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hp := zero_lt_one.trans (h₁ ht)
  exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp.ne')).mul
    (Complex.continuous_ofReal.continuousAt.comp ((Real.continuousAt_log hp.ne').inv₀
      (Real.log_pos (h₁ ht)).ne'))).continuousWithinAt

/-- A finite symmetric-height sum of principal Ei terms, including analytic multiplicity. -/
def sharpZetaEiSum (x T : ℝ) : ℂ :=
  ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*principalExponentialIntegral (z*(Real.log x : ℂ))

/-- For any finite height the zero logarithmic-integral sum is exactly the difference
of the two Ei sums, with identical truncations. -/
theorem sharpZeroLogIntegral_eq_EiSum_sub {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (T : ℝ) :
    sharpZeroLogIntegral a b T = sharpZetaEiSum b T - sharpZetaEiSum a T := by
  rw [sharpZeroLogIntegral,sharpZetaEiSum,sharpZetaEiSum,←sum_sub_distrib]
  refine sum_congr rfl fun z hz => ?_
  rw [zeroLogIntegral_eq_exponentialIntegral_sub (mem_nontrivialZerosUpTo.mp hz).2.1 ha hb,mul_sub]

/-- The Riemann formula written with the principal exponential integral at the pole and
at each nontrivial zero. Subtracting the values at a common reference 1<a<2 fixes
the normalization and yields the midpoint prime-power count for every x>1. -/
theorem tendsto_exponentialIntegral_zero_formula {a x : ℝ} (ha : 1 < a) (ha' : a < 2) (hx : 1 < x) :
    Tendsto (fun T => principalExponentialIntegral (Real.log x : ℂ) -
      principalExponentialIntegral (Real.log a : ℂ) - (sharpZetaEiSum x T - sharpZetaEiSum a T) -
      (trivialZeroLogIntegral a x : ℂ)) atTop (𝓝 (riemannPrimeCounting (1/2) x : ℂ)) := by
  apply (tendsto_riemannExplicitIncrement_midpoint ha ha' hx).congr
  intro T
  simp only [riemannExplicitIncrement,zeroLogIntegral_eq_exponentialIntegral_sub (by norm_num : 0 < (1:ℂ).re) ha hx,
    one_mul,sharpZeroLogIntegral_eq_EiSum_sub ha hx]

end AnalyticNumberTheory.PrimeDistribution
