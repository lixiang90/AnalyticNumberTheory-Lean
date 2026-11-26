import AnalyticNumberTheory.PrimeDistribution.IntegratedShiftedZeros
import AnalyticNumberTheory.PrimeDistribution.IntegratedTrivialZeros
import AnalyticNumberTheory.PrimeDistribution.RiemannPolarNormalization

/-!
# Riemann's prime-power explicit formula

The common additive constant is fixed by integrating the real shift before the
first prime. The nontrivial zeros give the symmetric principal-Ei sum, the negative
even zeros give the elementary tail, and the pole together with −ζ'/ζ gives
Ei(log x) − log 2. Finite Möbius inversion then recovers ordinary prime counting.
-/

noncomputable section

open Filter Finset MeasureTheory Complex
open scoped Topology Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- On the first prime-free interval, the Ei zero sum minus the trivial-zero tail
is exactly Ei(log x) − log 2. -/
theorem riemannEiZeroSum_sub_tail_of_lt_two {x : ℝ} (hx : 1 < x) (hx₂ : x < 2) :
    riemannEiZeroSum x - (riemannTrivialZeroTail x : ℂ) =
      principalExponentialIntegral (Real.log x:ℂ) - (Real.log 2:ℂ) := by
  obtain ⟨Z,_⟩ := exists_centered_logDeriv_riemannZeta
  obtain ⟨hN,HN⟩ := integral_shiftedNontrivialZeroContribution Z hx
  obtain ⟨hT,HT⟩ := integral_shiftedTrivialZeroContribution hx
  let F (y : ℝ) := shiftedNontrivialZeroContribution Z x y + shiftedTrivialZeroContribution x y
  have hI : IntegrableOn F (Set.Ioi 0) := hN.add hT
  have hval : (∫ y in Set.Ioi (0:ℝ), F y) = riemannEiZeroSum x - (riemannTrivialZeroTail x : ℂ) := by
    unfold F
    rw [integral_add hN hT,HN,HT,sub_eq_add_neg]
  have hlim := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hI tendsto_id
  rw [hval] at hlim
  apply tendsto_nhds_unique hlim
  apply (tendsto_integral_riemannPolar_sub_logDeriv (Real.log_pos hx)).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1:ℝ)] with y hy₁ hy
  exact shifted_explicit_formula_of_lt_two Z hx hx₂ ((Set.uIoc_of_le hR ▸ hy).1) hy₁

/-- The universal constant in Riemann's single-endpoint formula is −log 2. -/
theorem riemannCountingConstant_eq_neg_log_two :
    riemannCountingConstant = -(Real.log 2:ℂ) := by
  have h := riemannEiZeroSum_sub_tail_of_lt_two (x := 3/2) (by norm_num) (by norm_num)
  unfold riemannCountingConstant
  linear_combination h

/-- Riemann's explicit formula for the half-weighted prime-power count at every x>1,
with the symmetric principal-Ei sum, −log 2 and the decaying trivial-zero tail. -/
theorem riemannPrimeCounting_explicit_formula {x : ℝ} (hx : 1 < x) :
    (riemannPrimeCounting (1/2) x : ℂ) = principalExponentialIntegral (Real.log x:ℂ) -
      riemannEiZeroSum x - (Real.log 2:ℂ) + (riemannTrivialZeroTail x:ℂ) := by
  rw [riemannPrimeCounting_eq_Ei_zeroSum_tail_constant hx,riemannCountingConstant_eq_neg_log_two]
  ring

/-- The same fully normalized identity as a limit along all real symmetric heights. -/
theorem tendsto_riemannPrimeCounting_principalEi_formula {x : ℝ} (hx : 1 < x) :
    Tendsto (fun T : ℝ => principalExponentialIntegral (Real.log x:ℂ) - sharpZetaEiSum x T -
      (Real.log 2:ℂ) + (riemannTrivialZeroTail x:ℂ)) atTop (𝓝 (riemannPrimeCounting (1/2) x : ℂ)) := by
  rw [riemannPrimeCounting_explicit_formula hx]
  exact ((tendsto_const_nhds.sub (tendsto_sharpZetaEiSum hx)).sub_const _).add_const _

/-- Finite Möbius inversion of the fully evaluated Ei formula gives the inclusive
prime count. Only a prime cutoff requires the displayed half-unit correction. -/
theorem primePi_eq_moebius_principalEi_formula {x : ℝ} (hx : 1 < x) {N : ℕ}
    (hN : 1 ≤ N) (hcut : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    (primePi x : ℂ) = (∑ d ∈ Icc 1 N, (((μ d : ℝ)/d : ℝ):ℂ) *
      (principalExponentialIntegral (Real.log (x^((1:ℝ)/d)) : ℂ) -
        riemannEiZeroSum (x^((1:ℝ)/d)) - (Real.log 2:ℂ) + (riemannTrivialZeroTail (x^((1:ℝ)/d)) : ℂ))) +
      ((if ∃ p : ℕ, p.Prime ∧ (p:ℝ) = x then 1/2 else 0 : ℝ):ℂ) := by
  rw [primePi_eq_midpoint_add_endpoint, Complex.ofReal_add,
    primePiWithEndpoint_eq_sum_moebius_riemannPrimeCounting _ (zero_lt_one.trans hx) hN hcut,Complex.ofReal_sum]
  congr 1
  apply sum_congr rfl
  intro d hd
  have hd₀ : 0 < (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
  rw [Complex.ofReal_mul,riemannPrimeCounting_explicit_formula (Real.one_lt_rpow hx (one_div_pos.mpr hd₀))]

end AnalyticNumberTheory.PrimeDistribution
