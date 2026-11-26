import AnalyticNumberTheory.AnalyticTools.CountingTailIntegral
import AnalyticNumberTheory.PrimeDistribution.PositiveZeroTail

/-! # The asymptotic expansion of the reciprocal-square zero tail -/

noncomputable section

open Real Filter
open scoped Topology Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The positive-ordinate reciprocal-square tail, excluding its lower endpoint,
has main term (log(T/(2π))+1)/(2πT) with error O(log(T)/T²). -/
theorem positiveZeroReciprocalSquareTail_two_term :
    ∃ C > 0, ∀ {T : ℝ}, 2 ≤ T →
      |positiveZeroReciprocalSquareTail T - (Real.log (T/(2*Real.pi))+1)/(2*Real.pi*T)| ≤
        C*Real.log T/T^2 := by
  obtain ⟨K,hK,H⟩ := riemannVonMangoldt_asymptotic
  let a : ℝ := (2*Real.pi)⁻¹
  let b := -a*Real.log (2*Real.pi*Real.exp 1)
  have hN : Measurable (fun u : ℝ => (zeroCountUpTo u:ℝ)) :=
    measurable_from_top.comp (show Monotone zeroCountUpTo from fun _ _ h => zeroCountUpTo_mono h).measurable
  have happrox (u : ℝ) (hu : 2 ≤ u) :
      |(zeroCountUpTo u:ℝ)-(a*u*Real.log u+b*u+7/8)| ≤ K*Real.log u := by
    have heq : u/(2*Real.pi)*Real.log (u/(2*Real.pi*Real.exp 1))+7/8 = a*u*Real.log u+b*u+7/8 := by
      rw [Real.log_div (by linarith) (by positivity)]
      dsimp only [a,b]
      ring
    simpa only [heq] using H u hu
  refine ⟨4*K,by positivity,?_⟩
  intro T hT
  have h := reciprocalSquare_counting_integral_estimate hN hK.le happrox hT
  rw [positiveZeroReciprocalSquareTail_eq_integral (by linarith : 1 ≤ T)]
  have heq : (a*Real.log T+2*a+b)/T = (Real.log (T/(2*Real.pi))+1)/(2*Real.pi*T) := by
    dsimp only [a,b]
    rw [Real.log_div (by linarith) (by positivity),Real.log_mul (by positivity : 2*Real.pi ≠ 0) (Real.exp_ne_zero _),Real.log_exp]
    ring
  rwa [heq] at h

/-- Including every zero at the cutoff preserves both terms of the expansion
and the O(log(T)/T²) remainder. No restriction on the height is required. -/
theorem tsum_positiveZero_div_im_sq_two_term :
    ∃ C > 0, ∀ {T : ℝ}, 2 ≤ T →
      |(∑' z : CriticalStripZeros, if T ≤ (z:ℂ).im then (zeroMultiplicity z:ℝ)/(z:ℂ).im^2 else 0)
        - (Real.log (T/(2*Real.pi))+1)/(2*Real.pi*T)| ≤ C*Real.log T/T^2 := by
  obtain ⟨C,hC,H⟩ := positiveZeroReciprocalSquareTail_two_term
  obtain ⟨D,hD,E⟩ := positiveZeroReciprocalSquareTail_endpoint_error
  refine ⟨D+C,by positivity,?_⟩
  intro T hT
  obtain ⟨hn,he⟩ := E hT
  have ht := H hT
  calc
    _ ≤ _ := abs_sub_le _ (positiveZeroReciprocalSquareTail _) _
    _ ≤ _ := by
      rw [abs_of_nonneg hn,add_mul D C (Real.log T),add_div (D*Real.log T) (C*Real.log T) (T^2)]
      exact add_le_add he ht

/-- The leading-term form for positive ordinates, with a uniform O(1/T) error. -/
theorem tsum_positiveZero_div_im_sq_main_term :
    ∃ C > 0, ∀ {T : ℝ}, 2 ≤ T →
      |(∑' z : CriticalStripZeros, if T ≤ (z:ℂ).im then (zeroMultiplicity z:ℝ)/(z:ℂ).im^2 else 0)
        - Real.log T/(2*Real.pi*T)| ≤ C/T := by
  obtain ⟨K,hK,H⟩ := tsum_positiveZero_div_im_sq_two_term
  let B := |1-Real.log (2*Real.pi)|/(2*Real.pi)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K+B,by positivity,?_⟩
  intro T hT
  have hT₀ : 0 < T := by linarith
  have hm : |(Real.log (T/(2*Real.pi))+1)/(2*Real.pi*T) - Real.log T/(2*Real.pi*T)| = B/T := by
    rw [Real.log_div hT₀.ne' (by positivity),←sub_div,show Real.log T - Real.log (2*Real.pi)+1-Real.log T
      = 1-Real.log (2*Real.pi) by ring,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi*T)]
    dsimp only [B]; ring
  have hk : K*Real.log T/T^2 ≤ K/T := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hT₀) hT₀]
    have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hT₀) hK.le
    nlinarith [mul_le_mul_of_nonneg_right this hT₀.le,mul_nonneg hK.le hT₀.le]
  calc
    _ ≤ _ := abs_sub_le _ ((Real.log (T/(2*Real.pi))+1)/(2*Real.pi*T)) _
    _ ≤ _ := by rw [hm,add_div K B T]; exact add_le_add ((H hT).trans hk) le_rfl

end AnalyticNumberTheory.PrimeDistribution
