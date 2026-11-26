import AnalyticNumberTheory.AnalyticTools.EntireFunctions.CenteredPoles
import AnalyticNumberTheory.AnalyticTools.LaplaceInversion

/-!
# Laplace inversion of centered poles after one integration

The inverse transform of a centered pole divided by the square of the transform variable is
a continuous difference of exponentials. Inverse squared radii justify integration of an
infinite family after exponential damping to the right of every pole.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools
open EntireFunctions

/-- Inverse Laplace kernel for `centeredPole ω s / s²`, extended by zero on the negative axis. -/
def integratedPole (ω : ℂ) (u : ℝ) : ℂ := (Complex.exp (ω * (max u 0 : ℝ)) - 1) / ω^2

/-- A common exponential majorant for the integrated contribution of each pole. -/
theorem norm_integratedPole_le {ω : ℂ} {b : ℝ} (hω : ω.re ≤ b) (u : ℝ) :
    ‖integratedPole ω u‖ ≤ (Real.exp (b * max u 0) + 1) * (‖ω‖^2)⁻¹ := by
  rw [integratedPole, norm_div, norm_pow, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (norm_sub_le ..).trans
  rw [Complex.norm_exp, norm_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact add_le_add (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hω (le_max_right u 0))) le_rfl

/-- Integrated poles with a common real-part ceiling and summable inverse squared radii
give an absolutely convergent series for every real argument. -/
theorem summable_integratedPole {a : ℕ → ℂ} {b : ℝ} (hb : ∀ n, (a n).re ≤ b)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) (u : ℝ) :
    Summable fun n => integratedPole (a n) u :=
  (hS.mul_left _).of_norm_bounded fun n => norm_integratedPole_le (hb n) u

/-- The integrated pole series is continuous, including where its zero extension begins. -/
theorem continuous_tsum_integratedPole {a : ℕ → ℂ} {b : ℝ} (h₀ : 0 ≤ b)
    (hb : ∀ n, (a n).re ≤ b) (hS : Summable fun n => (‖a n‖^2)⁻¹) :
    Continuous fun u : ℝ => ∑' n, integratedPole (a n) u := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_tsum_of_dominated_convergence (hS.mul_left (Real.exp (b * max (u+1) 0)+1))
  · intro n
    apply ContinuousAt.tendsto
    unfold integratedPole
    fun_prop
  · filter_upwards [gt_mem_nhds (lt_add_one u)] with v hv n
    apply (norm_integratedPole_le (hb n) v).trans
    exact mul_le_mul_of_nonneg_right (add_le_add (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (max_le_max hv.le le_rfl) h₀)) le_rfl) (by positivity)

/-- A single integrated pole is integrable after damping to the right of the pole and zero. -/
theorem integrableOn_damped_integratedPole {ω s : ℂ} (hs : 0 < s.re) (hωs : ω.re < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s*u) * integratedPole ω u) (Ioi 0) := by
  have h₁ : (ω-s).re < 0 := by simpa using sub_neg.mpr hωs
  have h₂ : (-s).re < 0 := by simpa using hs
  apply (((integrableOn_exp_mul_complex_Ioi h₁ 0).sub
    (integrableOn_exp_mul_complex_Ioi h₂ 0)).div_const (ω^2)).congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  change 0 < u at hu
  simp only [integratedPole, max_eq_left hu.le, ←mul_div_assoc, mul_sub, mul_one, ←Complex.exp_add]
  rw [show -s*(u : ℂ)+ω*u=(ω-s)*u by ring]
  rfl

/-- The damped transform of each integrated pole is its centered partial fraction divided by
`s²`. The line lies to the right of the pole and of the origin. -/
theorem laplaceTransform_integratedPole {ω s : ℂ} (hω : ω ≠ 0) (hs : 0 < s.re)
    (hωs : ω.re < s.re) :
    laplaceTransform (integratedPole ω) s = centeredPole ω s / s^2 := by
  have h₁ : (ω-s).re < 0 := by simpa using sub_neg.mpr hωs
  have h₂ : (-s).re < 0 := by simpa using hs
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hs
  have hsω : ω - s ≠ 0 := fun h => by simp [h] at h₁
  have hω' : s - ω ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hsω).symm
  rw [laplaceTransform]
  calc
    _ = ∫ u in Ioi (0 : ℝ), (Complex.exp ((ω-s)*u) - Complex.exp (-s*u))/ω^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change 0 < u at hu
      simp only [integratedPole, max_eq_left hu.le, ← mul_div_assoc, mul_sub, mul_one,
        ← Complex.exp_add]
      rw [show -s*(u : ℂ)+ω*u=(ω-s)*u by ring]
    _ = _ := by
      rw [integral_div, integral_sub (integrableOn_exp_mul_complex_Ioi h₁ _)
        (integrableOn_exp_mul_complex_Ioi h₂ _), integral_exp_mul_complex_Ioi h₁,
        integral_exp_mul_complex_Ioi h₂, centeredPole]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp [hω, hs₀, hsω, hω']
      ring

private def poleEnvelope (b σ u : ℝ) := Real.exp ((b-σ)*u) + Real.exp (-σ*u)

private theorem integrableOn_poleEnvelope {b : ℝ} {s : ℂ} (h₀ : 0 ≤ b) (hs : b < s.re) :
    IntegrableOn (poleEnvelope b s.re) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (sub_neg.mpr hs) 0).add
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (h₀.trans_lt hs)) 0)

private theorem norm_damped_integratedPole_le {ω s : ℂ} {b u : ℝ} (hb : ω.re ≤ b) (hu : 0 ≤ u) :
    ‖Complex.exp (-s*u) * integratedPole ω u‖ ≤ poleEnvelope b s.re u * (‖ω‖^2)⁻¹ := by
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply (mul_le_mul_of_nonneg_left (norm_integratedPole_le hb u) (Real.exp_pos _).le).trans_eq
  rw [max_eq_left hu]
  dsimp [poleEnvelope]
  rw [←mul_assoc, mul_add, mul_one, ← Real.exp_add]
  congr 3
  ring

/-- On any positive line to the right of a common nonnegative real-part ceiling, the
exponentially damped sum of integrated poles is absolutely integrable on the positive axis. -/
theorem integrableOn_damped_tsum_integratedPole {a : ℕ → ℂ} {b : ℝ} (h₀ : 0 ≤ b)
    (hb : ∀ n, (a n).re ≤ b) (hS : Summable fun n => (‖a n‖^2)⁻¹) {s : ℂ} (hs : b < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s*u) * ∑' n, integratedPole (a n) u) (Ioi 0) := by
  apply ((integrableOn_poleEnvelope h₀ hs).mul_const (∑' n, (‖a n‖^2)⁻¹)).mono'
  · exact ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-s*u))).mul
      (continuous_tsum_integratedPole h₀ hb hS)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    rw [← tsum_mul_left]
    exact tsum_of_norm_bounded (hS.hasSum.mul_left _) fun n => norm_damped_integratedPole_le (hb n) hu.le

/-- The Laplace transform exchanges with a whole inverse-square-summable family of integrated
poles, giving the series of centered fractions on the same line. -/
theorem laplaceTransform_tsum_integratedPole {a : ℕ → ℂ} {b : ℝ} (h₀ : 0 ≤ b)
    (ha : ∀ n, a n ≠ 0) (hb : ∀ n, (a n).re ≤ b) (hS : Summable fun n => (‖a n‖^2)⁻¹)
    {s : ℂ} (hs : b < s.re) :
    laplaceTransform (fun u => ∑' n, integratedPole (a n) u) s =
      (∑' n, centeredPole (a n) s)/s^2 := by
  let f (n : ℕ) (u : ℝ) := Complex.exp (-s*u) * integratedPole (a n) u
  let E := poleEnvelope b s.re
  let B (n : ℕ) := (‖a n‖^2)⁻¹
  have hE : IntegrableOn E (Ioi 0) := integrableOn_poleEnvelope h₀ hs
  have hbound (n : ℕ) : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ‖f n u‖ ≤ E u * B n :=
    (ae_restrict_mem measurableSet_Ioi).mono fun u hu => norm_damped_integratedPole_le (hb n) hu.le
  have hi (n : ℕ) : IntegrableOn (f n) (Ioi 0) :=
    (hE.mul_const (B n)).mono' (by unfold f integratedPole; fun_prop) (hbound n)
  have hsum : Summable fun n => ∫ u in Ioi (0 : ℝ), ‖f n u‖ := by
    refine (hS.mul_left (∫ u in Ioi (0 : ℝ), E u)).of_nonneg_of_le
      (fun n => integral_nonneg fun u => norm_nonneg _) fun n => ?_
    simpa only [integral_mul_const] using integral_mono_ae (hi n).norm (hE.mul_const (B n)) (hbound n)
  rw [laplaceTransform]
  simp_rw [← tsum_mul_left]
  change (∫ t in Ioi (0 : ℝ), ∑' n, f n t) = _
  rw [← integral_tsum_of_summable_integral_norm hi hsum, ← tsum_div_const]
  exact tsum_congr fun n => laplaceTransform_integratedPole (ha n) (h₀.trans_lt hs) ((hb n).trans_lt hs)

end AnalyticNumberTheory.AnalyticTools
