import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralShifts
import AnalyticNumberTheory.PrimeDistribution.RiemannEiZeroSum
import AnalyticNumberTheory.PrimeDistribution.ShiftedZeroFormula

/-! # Integration of the shifted nontrivial-zero contribution -/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The zeros in the open critical strip all have nonzero imaginary part. -/
theorem im_ne_zero_of_mem_criticalStripZeros {z : ℂ} (hz : z ∈ CriticalStripZeros) : z.im ≠ 0 := by
  obtain ⟨h,h₀,_⟩ := mem_criticalStripZeros.mp hz
  intro hi
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hi)
  exact riemannZeta_ofReal_ne_zero_of_pos h₀ (he ▸ h)

/-- For a multiplicity-respecting enumeration the inverse squared ordinates are summable. -/
theorem summable_inv_sq_ordinates (Z : ZetaZeroEnumeration) :
    Summable (fun n => ((Z.zero n).im^2)⁻¹) := by
  apply (Z.summable_inv_sq.mul_left 2).of_norm_bounded_eventually
  filter_upwards [(Z.finite_norm_le 2).compl_mem_cofinite] with n hn
  have hr : 2 < ‖Z.zero n‖ := lt_of_not_ge hn
  have hz := mem_criticalStripZeros.mp (Z.mem_strip n)
  have hn₂ : ‖Z.zero n‖^2 = (Z.zero n).re*(Z.zero n).re + (Z.zero n).im*(Z.zero n).im := by
    rw [Complex.sq_norm,Complex.normSq_apply]
  have h₁ : (Z.zero n).re^2 ≤ 1 := by nlinarith [sq_lt_sq' (by linarith [hz.2.1] : -(1:ℝ)<(Z.zero n).re) hz.2.2]
  have h₂ : ‖Z.zero n‖^2 ≤ 2*(Z.zero n).im^2 := by nlinarith [sq_lt_sq' (by linarith [norm_nonneg (Z.zero n)] : -‖Z.zero n‖ < (2:ℝ)) hr]
  have hi := sq_pos_of_ne_zero (im_ne_zero_of_mem_criticalStripZeros (Z.mem_strip n))
  have hnorm := sq_pos_of_pos (zero_lt_two.trans hr)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ = 1/(Z.zero n).im^2 := (one_div _).symm
    _ ≤ 2/‖Z.zero n‖^2 := (div_le_div_iff₀ hi hnorm).mpr (by simpa using h₂)
    _ = _ := div_eq_mul_inv ..

private theorem correction_integral_eq_remainder {x : ℝ} (hx : 1 < x) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ y in Ioi (0:ℝ), shiftedPoleCorrection z y (Real.log x)) = riemannEiZeroRemainder x z := by
  have hu := Real.log_pos hx
  have hx₀ := zero_lt_one.trans hx
  have hi : (z*(Real.log x:ℂ)).im = z.im*Real.log x := by simp
  have hphase : exponentialIntegralPhase (z.im*Real.log x) = exponentialIntegralPhase z.im := by
    rcases lt_or_gt_of_ne hz with h | h
    · have hn := mul_neg_of_neg_of_pos h hu
      simp [exponentialIntegralPhase,h,h.not_gt,hn,hn.not_gt]
    · simp [exponentialIntegralPhase,h,mul_pos h hu]
  have hc : Complex.exp (z*(Real.log x:ℂ)) = (x:ℂ)^z := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx₀.ne'),←Complex.ofReal_log hx₀.le,mul_comm z]
  rw [integral_Ioi_shiftedPoleCorrection hz hu, riemannEiZeroRemainder,
    principalExponentialIntegral_eq_left_add_phase (by rw [hi]; exact mul_ne_zero hz hu.ne'),hi,hphase,hc,div_mul_eq_div_div]
  ring

/-- The damped sharp sum together with the absolutely convergent correction over all
nontrivial zeros. Its integral in the shift variable recovers the symmetric Ei sum. -/
def shiftedNontrivialZeroContribution (Z : ZetaZeroEnumeration) (x y : ℝ) : ℂ :=
  Complex.exp (-(y:ℂ)*(Real.log x:ℂ))*sharpZetaZeroSumLimit x +
    ∑' n, shiftedPoleCorrection (Z.zero n) y (Real.log x)

/-- Integration over the positive shift is absolutely convergent and gives the individual
height-ordered sum of Ei at the nontrivial zeros, for every x>1. -/
theorem integral_shiftedNontrivialZeroContribution (Z : ZetaZeroEnumeration) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (shiftedNontrivialZeroContribution Z x) (Ioi 0) ∧
    (∫ y in Ioi (0:ℝ), shiftedNontrivialZeroContribution Z x y) = riemannEiZeroSum x := by
  let u := Real.log x
  have hu : 0 < u := Real.log_pos hx
  let f (n : ℕ) (y : ℝ) := shiftedPoleCorrection (Z.zero n) y u
  let B (n : ℕ) := Real.exp u*((Z.zero n).im^2)⁻¹
  let G (y : ℝ) := y*Real.exp (-u*y)
  have hB : Summable B := (summable_inv_sq_ordinates Z).mul_left _
  have hG : IntegrableOn G (Ioi 0) := by
    simpa only [G,Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=1) (by norm_num) zero_lt_one hu
  have hbound (n : ℕ) : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ‖f n y‖ ≤ B n*G y :=
    (ae_restrict_mem measurableSet_Ioi).mono fun y hy =>
      norm_shiftedPoleCorrection_le (im_ne_zero_of_mem_criticalStripZeros (Z.mem_strip n)) hy.le hu.le
        (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le
  have hm (n : ℕ) : Measurable (f n) := by unfold f shiftedPoleCorrection; fun_prop
  have hI (n : ℕ) : IntegrableOn (f n) (Ioi 0) :=
    (hG.const_mul (B n)).mono' (hm n).aestronglyMeasurable (hbound n)
  have hS : Summable fun n => ∫ y in Ioi (0:ℝ), ‖f n y‖ := by
    apply (hB.mul_right (∫ y in Ioi (0:ℝ), G y)).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
    intro n
    simpa only [integral_const_mul] using integral_mono_ae (hI n).norm (hG.const_mul (B n)) (hbound n)
  have hTot : IntegrableOn (fun y => ∑' n, f n y) (Ioi 0) := by
    apply (hG.const_mul (∑' n, B n)).mono' (Measurable.tsum hm).aestronglyMeasurable
    filter_upwards [ae_all_iff.mpr hbound] with y hy
    exact tsum_of_norm_bounded (hB.hasSum.mul_right (G y)) hy
  have hJ := hasSum_integral_of_summable_integral_norm hI hS
  have hE : HasSum (fun n => riemannEiZeroRemainder x (Z.zero n)) (∫ y in Ioi (0:ℝ), ∑' n, f n y) := by
    apply hJ.congr_fun
    exact fun n => (correction_integral_eq_remainder hx (im_ne_zero_of_mem_criticalStripZeros (Z.mem_strip n))).symm
  have hD := Z.hasSum_distinct hE
  have hlim := tendsto_sharpZetaZeroSum_midpointPsi hx
  rw [← sharpZetaZeroSumLimit_eq hx] at hlim
  have hK := tendsto_sum_nontrivialZerosUpTo_of_summable
    (f := fun z => (zeroMultiplicity z:ℂ)*riemannEiZeroRemainder x z) hD.summable
  rw [show (∑' z : CriticalStripZeros, (zeroMultiplicity z:ℂ)*riemannEiZeroRemainder x z) =
    (∫ y in Ioi (0:ℝ), ∑' n, f n y) from hD.tsum_eq] at hK
  have hSx := tendsto_nhds_unique (tendsto_sharpZetaEiSum hx) (((hlim.div_const (u:ℂ)).add hK).congr
    (fun T => (sharpZetaEiSum_eq_leading_add_remainder x T).symm))
  have hdec : (fun y : ℝ => shiftedNontrivialZeroContribution Z x y) =
      (fun y : ℝ => Complex.exp (-(u:ℂ)*y)*sharpZetaZeroSumLimit x + ∑' n, f n y) := by
    funext y
    change Complex.exp (-(y:ℂ)*(u:ℂ))*_+_ = _
    rw [show -(y:ℂ)*(u:ℂ) = -(u:ℂ)*y by ring]
  have hi := (integrableOn_exp_mul_complex_Ioi (a := -(u:ℂ)) (by simpa using hu) 0).mul_const (sharpZetaZeroSumLimit x)
  change IntegrableOn (fun y : ℝ => shiftedNontrivialZeroContribution Z x y) _ ∧ _
  rw [hdec]
  refine ⟨hi.add hTot,?_⟩
  rw [integral_add hi hTot,integral_mul_const,integral_exp_mul_complex_Ioi (by simpa using hu),hSx]
  simp [div_eq_mul_inv,mul_comm]

end AnalyticNumberTheory.PrimeDistribution
