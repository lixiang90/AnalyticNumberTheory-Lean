import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralAsymptotic
import AnalyticNumberTheory.PrimeDistribution.RiemannExponentialIntegral
import AnalyticNumberTheory.PrimeDistribution.ZeroSumHeightLimit

/-!
# The symmetric Ei sum at a single physical cutoff

The half-plane phases cancel at each finite height. The leading exponential terms have
the sharp Chebyshev limit and the remaining terms form an absolutely convergent series.
-/

noncomputable section

open Complex Filter Finset
open scoped Topology Classical ComplexConjugate
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The remainder of the Ei contribution of one zero after the signed phase and the
Chebyshev leading term have been removed. -/
def riemannEiZeroRemainder (x : ℝ) (z : ℂ) : ℂ :=
  principalExponentialIntegral (z*(Real.log x : ℂ)) - exponentialIntegralPhase z.im -
    ((x : ℂ)^z/z)/(Real.log x : ℂ)

/-- The oscillatory remainder is bounded by x/(log²x Im(z)²) in the half-plane Re z ≤ 1. -/
theorem norm_riemannEiZeroRemainder_le {x : ℝ} (hx : 1<x) {z : ℂ} (hr : z.re ≤ 1) (hy : z.im ≠ 0) :
    ‖riemannEiZeroRemainder x z‖ ≤ (x/(Real.log x)^2)/z.im^2 := by
  have hl := Real.log_pos hx
  have hx₀ := zero_lt_one.trans hx
  have hi : (z*(Real.log x : ℂ)).im = z.im*Real.log x := by simp
  have hre : (z*(Real.log x : ℂ)).re = z.re*Real.log x := by simp
  have hphase : exponentialIntegralPhase (z.im*Real.log x) = exponentialIntegralPhase z.im := by
    rcases lt_or_gt_of_ne hy with h | h
    · have hm := mul_neg_of_neg_of_pos h hl
      simp [exponentialIntegralPhase,h,h.not_gt,hm,hm.not_gt]
    · simp [exponentialIntegralPhase,h,mul_pos h hl]
  have he : Complex.exp (z*(Real.log x : ℂ)) = (x : ℂ)^z := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx₀.ne'),←Complex.ofReal_log hx₀.le,mul_comm z]
  have h := norm_principalExponentialIntegral_sub_phase_sub_le (w := z*(Real.log x : ℂ))
    (by rw [hi]; exact mul_ne_zero hy hl.ne')
  rw [hi,hre,hphase,he,div_mul_eq_div_div] at h
  apply h.trans
  have hp : Real.exp (z.re*Real.log x) ≤ x := by
    simpa [Real.exp_log hx₀] using Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr hl.le)
  apply (div_le_div_of_nonneg_right hp (sq_nonneg _)).trans_eq
  rw [mul_pow]
  ring

/-- The Ei remainders, with analytic multiplicity, are absolutely summable over the distinct zeros. -/
theorem summable_riemannEiZeroRemainder {x : ℝ} (hx : 1<x) :
    Summable (fun z : CriticalStripZeros => (zeroMultiplicity z : ℂ)*riemannEiZeroRemainder x z) := by
  let A := x/(Real.log x)^2
  have hA : 0 ≤ A := div_nonneg (zero_le_one.trans hx.le) (sq_nonneg _)
  have hs : Summable (fun z : CriticalStripZeros => (zeroMultiplicity z : ℝ)/(1+(z:ℂ).im^2)) := by
    simpa only [zero_sub,even_two.neg_pow,zeroMultiplicity] using summable_criticalStripZeros_inv_one_add_sq 0
  apply (hs.mul_left (2*A)).of_norm_bounded_eventually
  filter_upwards [(criticalStripZerosUpTo 1).eventually_cofinite_notMem] with z hz
  have hy : 1 < |(z:ℂ).im| := lt_of_not_ge (fun h => hz (mem_criticalStripZerosUpTo.mpr h))
  have hsq : 1 ≤ (z:ℂ).im^2 := by simpa only [one_pow,sq_abs] using pow_le_pow_left₀ zero_le_one hy.le 2
  have hq : 1/(z:ℂ).im^2 ≤ 2/(1+(z:ℂ).im^2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hm : 0 ≤ (zeroMultiplicity z : ℝ) := Nat.cast_nonneg _
  have hb := norm_riemannEiZeroRemainder_le hx (mem_criticalStripZeros.mp z.property).2.2.le
    (abs_pos.mp (zero_lt_one.trans hy))
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (zeroMultiplicity z : ℝ)*(A/(z:ℂ).im^2) := mul_le_mul_of_nonneg_left hb hm
    _ = (A*(zeroMultiplicity z : ℝ))*(1/(z:ℂ).im^2) := by ring
    _ ≤ (A*(zeroMultiplicity z : ℝ))*(2/(1+(z:ℂ).im^2)) := mul_le_mul_of_nonneg_left hq (mul_nonneg hA hm)
    _ = _ := by ring

/-- At finite height the phases of conjugate zeros cancel. The remaining two pieces
are the Chebyshev zero sum divided by log x and a sum with a squared-ordinate bound. -/
theorem sharpZetaEiSum_eq_leading_add_remainder (x T : ℝ) :
    sharpZetaEiSum x T = sharpZetaZeroSum x T/(Real.log x : ℂ) +
      ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*riemannEiZeroRemainder x z := by
  have hp := sum_zeroMultiplicity_eq_zero_of_conj_odd T (fun z => exponentialIntegralPhase z.im)
    (fun z _ => by simp only [Complex.conj_im,exponentialIntegralPhase_neg])
  calc
    _ = (∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*exponentialIntegralPhase z.im) +
        sharpZetaZeroSum x T/(Real.log x : ℂ) +
        ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*riemannEiZeroRemainder x z := by
      rw [sharpZetaEiSum,sharpZetaZeroSum,sum_div,←sum_add_distrib,←sum_add_distrib]
      refine sum_congr rfl fun z _ => ?_
      unfold riemannEiZeroRemainder
      ring
    _ = _ := by rw [hp,zero_add]

/-- The height-ordered sum of the principal Ei terms at one endpoint. -/
def riemannEiZeroSum (x : ℝ) : ℂ := limUnder atTop (sharpZetaEiSum x)

/-- The individual (unanchored) symmetric Ei sums converge at every cutoff x>1. -/
theorem tendsto_sharpZetaEiSum {x : ℝ} (hx : 1<x) :
    Tendsto (sharpZetaEiSum x) atTop (𝓝 (riemannEiZeroSum x)) := by
  have h := ((tendsto_sharpZetaZeroSum_midpointPsi hx).div_const (Real.log x : ℂ)).add
    (tendsto_sum_nontrivialZerosUpTo_of_summable
      (f := fun z => (zeroMultiplicity z : ℂ)*riemannEiZeroRemainder x z) (summable_riemannEiZeroRemainder hx))
  have hs : Tendsto (sharpZetaEiSum x) atTop (𝓝 _) := h.congr (fun T => (sharpZetaEiSum_eq_leading_add_remainder x T).symm)
  rw [riemannEiZeroSum,hs.limUnder_eq]
  exact hs

/-- Riemann's midpoint count in terms of the two individually convergent Ei sums, for
any fixed reference between one and two. -/
theorem riemannPrimeCounting_eq_Ei_sub_zeroSum {a x : ℝ} (ha : 1<a) (ha' : a<2) (hx : 1<x) :
    (riemannPrimeCounting (1/2) x : ℂ) = principalExponentialIntegral (Real.log x : ℂ) -
      principalExponentialIntegral (Real.log a : ℂ) - (riemannEiZeroSum x-riemannEiZeroSum a) -
      (trivialZeroLogIntegral a x : ℂ) := by
  apply tendsto_nhds_unique (tendsto_exponentialIntegral_zero_formula ha ha' hx)
  exact ((tendsto_const_nhds.sub ((tendsto_sharpZetaEiSum hx).sub (tendsto_sharpZetaEiSum ha))).sub_const _)

end AnalyticNumberTheory.PrimeDistribution
