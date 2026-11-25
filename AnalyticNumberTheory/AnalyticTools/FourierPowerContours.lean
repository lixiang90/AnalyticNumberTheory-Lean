import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Turning Fourier integrals of a complex power

The logarithmic covering gives a primitive on the slit plane for every
Fourier mode and every complex exponent. This makes it possible to rotate
the integration paths for truncated periods independently at their ends.
-/
noncomputable section
open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools

/-- A complex power with a Fourier frequency in angular normalization. -/
def fourierPowerMode (s : ℂ) (ω : ℝ) (z : ℂ) := Complex.exp ((ω:ℂ)*z*I)*z^(-s)

/-- On the logarithmic cover the differential becomes an entire function. -/
theorem fourierPowerMode_exactOn (s : ℂ) (ω : ℝ) :
    Complex.IsExactOn (fourierPowerMode s ω) Complex.slitPlane := by
  let H (w : ℂ) := Complex.exp ((1-s)*w+(ω:ℂ)*Complex.exp w*I)
  have hh : Differentiable ℂ H := by unfold H;fun_prop
  obtain ⟨G,hG⟩ := hh.isExactOn_univ
  refine ⟨fun z => G (Complex.log z),?_⟩
  intro z hz
  have hne := Complex.slitPlane_ne_zero hz
  have h := (hG (Complex.log z) trivial).comp z (Complex.hasDerivAt_log hz)
  convert h using 1
  · rfl
  unfold H fourierPowerMode
  rw [Complex.exp_log hne,Complex.cpow_def_of_ne_zero hne]
  rw [show (1-s)*Complex.log z+(ω:ℂ)*z*I=(ω:ℂ)*z*I+Complex.log z*(-s)+Complex.log z by ring,
    Complex.exp_add,Complex.exp_add,Complex.exp_log hne]
  field_simp

/-- A single-valued antiderivative used for rotating the contour. -/
def fourierPowerPrimitive (s : ℂ) (ω : ℝ) := (fourierPowerMode_exactOn s ω).choose

theorem hasDerivAt_fourierPowerPrimitive (s : ℂ) (ω : ℝ) {z : ℂ} (hz : z∈Complex.slitPlane) :
    HasDerivAt (fourierPowerPrimitive s ω) (fourierPowerMode s ω z) z :=
  (fourierPowerMode_exactOn s ω).choose_spec z hz

/-- Straight segments in the slit plane evaluate by their endpoints. -/
theorem integral_fourierPowerMode_line (s : ℂ) (ω : ℝ) (z d : ℂ) (a b : ℝ)
    (hline : ∀ t ∈ uIcc a b, z+d*(t:ℂ)∈Complex.slitPlane) :
    d*(∫ t in a..b, fourierPowerMode s ω (z+d*(t:ℂ))) =
      fourierPowerPrimitive s ω (z+d*(b:ℂ))-fourierPowerPrimitive s ω (z+d*(a:ℂ)) := by
  have h (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt (fun u : ℝ => fourierPowerPrimitive s ω (z+d*(u:ℂ)))
      (d*fourierPowerMode s ω (z+d*(t:ℂ))) t := by
    have hl := (((hasDerivAt_id (t:ℂ)).const_mul d).const_add z)
    simpa only [id_eq,mul_one,mul_comm d (fourierPowerMode _ _ _),Function.comp_def] using
      ((hasDerivAt_fourierPowerPrimitive s ω (hline t ht)).comp (t:ℂ) hl).comp_ofReal
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt h
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.mul
  unfold fourierPowerMode
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.cpow_const (by fun_prop)
  exact fun t ht => hline t ht

end AnalyticNumberTheory.AnalyticTools
