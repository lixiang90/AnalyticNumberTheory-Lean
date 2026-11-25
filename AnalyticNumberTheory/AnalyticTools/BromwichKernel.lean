import AnalyticNumberTheory.AnalyticTools.LaplaceInversion
import AnalyticNumberTheory.DirichletSeries.Perron
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The Bromwich kernel at a jump discontinuity -/
noncomputable section
open Complex Real Set MeasureTheory Filter
open scoped Interval Topology
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.AnalyticTools

/-- Bromwich inversion on the finite vertical segment from σ−iT to σ+iT. -/
def truncatedBromwich (F : ℂ→ℂ) (σ x T : ℝ) : ℂ :=
  (1/(2*Real.pi:ℂ))*∫ t in -T..T, Complex.exp (((σ:ℂ)+(t:ℂ)*I)*x)*F ((σ:ℂ)+(t:ℂ)*I)

/-- The Laplace transform of a unit jump at a nonnegative argument. -/
theorem laplaceTransform_unitStep {a : ℝ} (ha : 0≤a) {z : ℂ} (hz : 0<z.re) :
    laplaceTransform ((Ioi a).indicator (fun _ : ℝ => (1:ℂ))) z = Complex.exp (-z*a)/z := by
  unfold laplaceTransform
  have hs (t : ℝ) : Complex.exp (-z*t)*(Ioi a).indicator (fun _ : ℝ => (1:ℂ)) t =
      (Ioi a).indicator (fun u : ℝ => Complex.exp (-z*u)) t := by
    by_cases h : a<t <;> simp [Set.indicator,Ioi,h]
  simp_rw [hs]
  rw [setIntegral_indicator measurableSet_Ioi,inter_eq_right.mpr (Ioi_subset_Ioi ha)]
  simpa only [neg_div_neg_eq] using integral_exp_mul_complex_Ioi (a:= -z) (by simpa using hz) a

/-- The inverse of exp(−as)/s is the same kernel as Perron's formula after
the logarithmic change of variable y = exp(x−a). -/
theorem truncatedBromwich_step_eq_perron (a x σ T : ℝ) :
    truncatedBromwich (fun z => Complex.exp (-z*a)/z) σ x T =
      perronKernel (Real.exp (x-a)) σ T := by
  unfold truncatedBromwich perronKernel
  congr 1
  apply intervalIntegral.integral_congr;intro t _
  let z := (σ:ℂ)+(t:ℂ)*I
  change Complex.exp (z*x)*(Complex.exp (-z*a)/z)=((Real.exp (x-a):ℝ):ℂ)^z/z
  rw [←mul_div_assoc,←Complex.exp_add,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp,Complex.ofReal_sub]
  congr 2;ring

/-- The midpoint convention for a unit jump, including at the origin. -/
theorem laplace_unitStep_inversion {a σ : ℝ} (ha : 0≤a) (hσ : 0<σ) (x : ℝ) :
    Tendsto (truncatedBromwich (laplaceTransform ((Ioi a).indicator (fun _ : ℝ => (1:ℂ)))) σ x)
      atTop (𝓝 (if a<x then (1:ℂ) else if a=x then 1/2 else 0)) := by
  have he (T : ℝ) : truncatedBromwich (laplaceTransform ((Ioi a).indicator (fun _ : ℝ => (1:ℂ)))) σ x T =
      perronKernel (Real.exp (x-a)) σ T := by
    rw [←truncatedBromwich_step_eq_perron]
    unfold truncatedBromwich
    congr 1
    apply intervalIntegral.integral_congr; intro t _
    dsimp only
    rw [laplaceTransform_unitStep ha (by simpa using hσ)]
  rw [funext he]
  have H := tendsto_perronKernel (Real.exp_pos (x-a)) hσ
  convert H using 2
  rcases lt_trichotomy a x with h|rfl|h
  · simp [perronLimit,h,Real.one_lt_exp_iff.mpr (sub_pos.mpr h)]
  · simp [perronLimit]
  · have hh := Real.exp_lt_one_iff.mpr (sub_neg.mpr h)
    simp [perronLimit,h.not_gt,h.ne',hh.not_gt,hh.ne]

end AnalyticNumberTheory.AnalyticTools