import AnalyticNumberTheory.RiemannZeta.LogMeanDerivative
import AnalyticNumberTheory.RiemannZeta.ArgumentPrimitive
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # The first integral of the argument of the zeta function -/
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology Interval
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

/-- Local integrability on the entire nonnegative height axis, with the right-hand
convention for the argument at zero ordinates. -/
theorem intervalIntegrable_argumentS {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable argumentS volume a b := by
  have hN : Monotone (fun t => (zeroCountUpTo t:ℝ)) := fun i j hij => by
    change (zeroCountUpTo i : ℝ) ≤ (zeroCountUpTo j : ℝ)
    exact_mod_cast zeroCountUpTo_mono hij
  let A (t : ℝ) := ((-1/2:ℂ)+(t:ℂ)*I).arg
  let G (t : ℝ) := stirlingLogGamma ((5/4:ℂ)+((t/2:ℝ):ℂ)*I)
  have hA : IntervalIntegrable A volume a b := by
    rw [intervalIntegrable_iff,uIoc_of_le hab]
    apply Integrable.of_bound (C:=Real.pi)
    · exact (Complex.measurable_arg.comp (by fun_prop : Measurable (fun t : ℝ => (-1/2:ℂ)+(t:ℂ)*I))).aestronglyMeasurable
    · exact ae_of_all _ (fun t => (Complex.abs_arg_le_pi _))
  have hG : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (f:=fun t : ℝ => (5/4:ℂ)+((t/2:ℝ):ℂ)*I)
      (hasDerivAt_stirlingLogGamma (Or.inl (by simp) : (5/4:ℂ)+((t/2:ℝ):ℂ)*I ∈ Complex.slitPlane)).continuousAt
    fun_prop
  have hlin : Continuous (fun t : ℝ => (t/(2*Real.pi))*Real.log Real.pi) := by fun_prop
  have H := (hN.intervalIntegrable (a:=a) (b:=b) (μ:=volume)).sub
    (((hA.const_mul (1/Real.pi)).add (((Complex.continuous_im.comp hG).intervalIntegrable a b).const_mul (1/Real.pi))).sub
      (hlin.intervalIntegrable a b))
  apply H.congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  have hz := zeroCountUpTo_eq_stirling_add_argumentS (ha.trans_lt ht.1)
  change (zeroCountUpTo t:ℝ)-_ = argumentS t
  dsimp [A,G] at *
  linarith only [hz]

/-- The primitive of the Riemann–von Mangoldt argument, conventionally denoted `S₁(T)`. -/
def integratedArgument (T : ℝ) : ℝ := ∫ t in (0:ℝ)..T, argumentS t

/-- The increment of the first argument integral is the increment of the horizontal
logarithmic mean plus that of the absolute-convergence-line primitive, divided by π. -/
theorem integratedArgument_increment {a b : ℝ} (ha : 8 ≤ a) (hab : a ≤ b) :
    Real.pi*(integratedArgument b-integratedArgument a) =
      (horizontalLogMean riemannZeta b + argZetaPrimitive b) -
      (horizontalLogMean riemannZeta a + argZetaPrimitive a) := by
  let E := Complex.im '' {ρ ∈ CriticalStripZeros | ρ.im ∈ Icc a b}
  have hfin : E.Finite := (criticalStripZeros_strip_finite a b).image _
  have hI := intervalIntegrable_argumentS (by linarith : 0 ≤ a) hab
  have H := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => horizontalLogMean riemannZeta t + argZetaPrimitive t)
    (fun t => Real.pi*argumentS t) hab hfin.countable
    (fun t ht => ((continuousAt_zeta_horizontalLogMean (ha.trans ht.1)).add
      (hasDerivAt_argZetaPrimitive t).continuousAt).continuousWithinAt)
    (by
      intro t ht
      have hn : ¬ IsZeroOrdinate t := by
        rintro ⟨ρ,hρ,he⟩
        exact ht.2 ⟨ρ,⟨hρ,he ▸ ⟨ht.1.1.le,ht.1.2.le⟩⟩,he⟩
      exact ((hasDerivAt_zeta_horizontalLogMean (by linarith [ht.1.1]) hn).add
        (hasDerivAt_argZetaPrimitive t)).congr_deriv (by ring))
    (hI.const_mul _)
  rw [intervalIntegral.integral_const_mul] at H
  unfold integratedArgument
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_argumentS le_rfl (by linarith : 0≤a)) hI, add_sub_cancel_left]
  exact H

/-- The first integral of the argument satisfies the classical `O(log T)` estimate.
Both the estimate and the primitive include heights that are ordinates of zeros. -/
theorem integratedArgument_abs_le_log :
    ∃ C : ℝ, 0<C ∧ ∀ {T : ℝ}, 8≤T → |integratedArgument T| ≤ C*Real.log T := by
  obtain ⟨D,hD,HD⟩ := zeta_horizontalLogMean_bound
  let B := |Real.pi * integratedArgument 8| + |horizontalLogMean riemannZeta 8| +
    Real.pi^2/(3*Real.log 2)
  have hB : 0≤B := by dsimp [B]; positivity
  have hp := Real.pi_pos
  refine ⟨(B+3*D)/Real.pi, by positivity, ?_⟩
  intro T hT
  have hl : 1 ≤ Real.log T := (Real.le_log_iff_exp_le (by linarith)).2
    (Real.exp_one_lt_d9.le.trans (by linarith))
  have hlog : Real.log (T+4) ≤ 2*Real.log T := by
    rw [show (2:ℝ)*Real.log T=Real.log (T^2) by simpa using (Real.log_pow T 2).symm]
    apply Real.log_le_log (by linarith)
    nlinarith
  have H := integratedArgument_increment (a:=8) le_rfl hT
  have he : Real.pi*integratedArgument T =
      (Real.pi*integratedArgument 8-horizontalLogMean riemannZeta 8)+
      horizontalLogMean riemannZeta T + (argZetaPrimitive T-argZetaPrimitive 8) := by linarith
  have he' := abs_add_le ((Real.pi*integratedArgument 8-horizontalLogMean riemannZeta 8)+
      horizontalLogMean riemannZeta T) (argZetaPrimitive T-argZetaPrimitive 8)
  have hi := abs_integral_arg_riemannZeta_two_le 8 T
  rw [integral_arg_riemannZeta_two] at hi
  have hbound : |Real.pi*integratedArgument T| ≤ B + D*(1+Real.log (T+4)) := by
    rw [he]
    dsimp [B]
    linarith only [he', abs_add_le (Real.pi*integratedArgument 8-horizontalLogMean riemannZeta 8)
      (horizontalLogMean riemannZeta T), abs_sub (Real.pi*integratedArgument 8) (horizontalLogMean riemannZeta 8), HD hT, hi]
  rw [abs_mul, abs_of_pos hp] at hbound
  rw [div_mul_eq_mul_div, le_div_iff₀ hp, mul_comm _ Real.pi]
  nlinarith only [hbound, mul_le_mul_of_nonneg_left hlog hD.le,
    mul_le_mul_of_nonneg_left hl hB, mul_le_mul_of_nonneg_left hl hD.le]

/-- Asymptotic notation for the first integrated argument bound. -/
theorem integratedArgument_isBigO_log :
    Asymptotics.IsBigO atTop integratedArgument Real.log := by
  obtain ⟨C,_,H⟩ := integratedArgument_abs_le_log
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (8:ℝ)] with t ht
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith : 1≤t))] using H ht

end AnalyticNumberTheory.RiemannZeta
