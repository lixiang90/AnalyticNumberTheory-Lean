import AnalyticNumberTheory.ExponentialSums.VanDerCorput
import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans

/-!
# Oscillatory integrals for Hardy's function

The phase in Stirling's formula has a stationary point near `t=2πn²`.
The second derivative controls frequencies up to `2√T`, while the first
derivative is bounded away from zero for larger frequencies.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-- Leading asymptotic to the Riemann–Siegel theta phase on the positive real axis. -/
noncomputable def hardyPhase (t : ℝ) : ℝ :=
  (t*Real.log t - (Real.log (2*π)+1)*t)/2 - π/8

private noncomputable def phaseSlope (n : ℕ) (t : ℝ) := (Real.log t-Real.log (2*π))/2-Real.log n

private theorem phase_hasDerivAt (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => hardyPhase x-x*Real.log n) (phaseSlope n t) t := by
  have h₀ := ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
    ((hasDerivAt_id t).const_mul (Real.log (2*π)+1))
  have h := (((h₀.div_const 2).sub_const (π/8))).sub ((hasDerivAt_id t).mul_const (Real.log n))
  convert h using 1
  · rfl
  · dsimp [phaseSlope]
    field_simp
    ring

private theorem phaseSlope_hasDerivAt (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (phaseSlope n) (1/(2*t)) t := by
  have h := (((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2*π))).div_const 2).sub_const (Real.log n)
  convert h using 1
  · rfl
  · ring

private theorem continuousOn_phaseSecond {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun t : ℝ => 1/(2*t)) (Set.Icc T (2*T)) :=
  continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht =>
    mul_ne_zero (show (2:ℝ) ≠ 0 by norm_num) (hT.trans_le ht.1).ne'

/-- Uniform stationary-phase bound on an arbitrary logarithmic frequency. -/
theorem norm_integral_hardyPhase_sub_log_le_sqrt (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ‖∫ t in T..(2*T), Complex.exp (((hardyPhase t-t*Real.log n:ℝ):ℂ)*I)‖ ≤ 16*√T := by
  have h := vanDerCorput_integral_second_deriv (F' := phaseSlope n) (F'' := fun t => 1/(2*t))
    (show T ≤ 2*T by linarith) (r := 1/(4*T)) (by positivity)
    (fun t ht => phase_hasDerivAt n (hT.trans_le ht.1))
    (fun t ht => phaseSlope_hasDerivAt n (hT.trans_le ht.1)) (continuousOn_phaseSecond hT)
    (fun t ht => by
      rw [abs_of_nonneg (by have := hT.trans_le ht.1; positivity)]
      exact one_div_le_one_div_of_le (by have := hT.trans_le ht.1; positivity) (by linarith [ht.2]))
  apply h.trans_eq
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
  rw [show √(4:ℝ) = 2 by rw [show (4:ℝ)=2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ)≤2)], div_div_eq_mul_div]
  ring

/-- Nonstationary frequencies have an integral bounded independently of the height. -/
theorem norm_integral_hardyPhase_sub_log_le_const {n : ℕ} {T : ℝ} (hT : 0 < T)
    (hn : 2*√T ≤ n) :
    ‖∫ t in T..(2*T), Complex.exp (((hardyPhase t-t*Real.log n:ℝ):ℂ)*I)‖ ≤ 8/Real.log 2 := by
  have hlog := Real.log_pos (show (1:ℝ)<2 by norm_num)
  have h := vanDerCorput_integral_first_deriv (F' := phaseSlope n) (F'' := fun t => 1/(2*t))
    (show T ≤ 2*T by linarith) (m := Real.log 2/2) (by positivity)
    (fun t ht => phase_hasDerivAt n (hT.trans_le ht.1))
    (fun t ht => phaseSlope_hasDerivAt n (hT.trans_le ht.1)) (continuousOn_phaseSecond hT)
    (Or.inl fun t ht => by have := hT.trans_le ht.1; positivity)
    (fun t ht => by
      have h₁ := Real.log_le_log (by positivity : 0 < 2*√T) hn
      have h₂ := Real.log_le_log (hT.trans_le ht.1) ht.2
      rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hT).ne', Real.log_sqrt hT.le] at h₁
      rw [Real.log_mul (by norm_num) hT.ne'] at h₂
      have hπ : 0 ≤ Real.log (2*π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
      exact (le_abs_self (-(phaseSlope n t))).trans' (by dsimp [phaseSlope]; linarith) |>.trans_eq (abs_neg _))
  apply h.trans_eq
  ring

end AnalyticNumberTheory.RiemannZeta
