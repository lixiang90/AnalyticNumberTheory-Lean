import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

/-!
# Cauchy's inequality for fourth means

A circle of radius `r` compares the fourth power of a complex derivative
with the angular average of the fourth power of the function. Integration
on vertical segments also allows finite families of functions.
-/

open Real Complex Metric Set Finset MeasureTheory
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Fourth-power Jensen inequality on a finite interval. -/
theorem integral_fourth_power_mean {a b : ℝ} (hab : a<b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in a..b,f t)^4≤(b-a)^3*(∫ t in a..b,f t^4) := by
  let μ := volume.restrict (Ioc a b)
  have h := ((by decide : Even 4).convexOn_pow (𝕜:=ℝ)).map_set_average_le
    (μ:=volume) (t:=Ioc a b) (f:=f) (by fun_prop) isClosed_univ
    (by simp [Real.volume_Ioc,hab]) (by simp [Real.volume_Ioc]) (ae_of_all _ (by simp))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp (hf.intervalIntegrable ..))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp ((hf.pow 4).intervalIntegrable ..))
  simp only [average_eq,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hab.le,smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le hab.le,intervalIntegral.integral_of_le hab.le]
  change ((b-a)⁻¹*_ )^4≤(b-a)⁻¹*_ at h
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (sub_nonneg.mpr hab.le) 4)
  field_simp [(sub_pos.mpr hab).ne'] at hh
  exact hh

/-- The L-fourth Cauchy derivative estimate, expressed as an ordinary angular integral. -/
theorem deriv_fourth_le_circle_mean {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0<r) (hf : DifferentiableOn ℂ f (closedBall z r)) :
    ‖deriv f z‖^4≤(2*Real.pi*r^4)⁻¹*∫ θ in (0:ℝ)..2*Real.pi,‖f (circleMap z r θ)‖^4 := by
  let P := 2*Real.pi
  have hP : 0<P := by dsimp [P]; positivity
  have hF : Continuous (fun θ => ‖f (circleMap z r θ)‖) :=
    (hf.continuousOn.comp_continuous (continuous_circleMap ..)
      (fun θ => sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ))).norm
  have h := hf.deriv_eq_smul_circleIntegral hr
  have hnorm := congrArg norm h
  have hleft (θ : ℝ) : ‖deriv (circleMap z r) θ • ((1/(circleMap z r θ-z)^2) • f (circleMap z r θ))‖=
      r⁻¹*‖f (circleMap z r θ)‖ := by
    rw [deriv_circleMap,norm_smul,norm_smul,norm_mul,Complex.norm_I,mul_one,circleMap_sub_center,
      norm_div,norm_one,norm_pow,norm_circleMap_zero,abs_of_pos hr]
    field_simp
  change ‖∫ θ in (0:ℝ)..P, deriv (circleMap z r) θ • ((1/(circleMap z r θ-z)^2) • f (circleMap z r θ))‖=_ at hnorm
  have hbound := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (a:=(0:ℝ)) (b:=P) (f:=fun θ =>
    deriv (circleMap z r) θ • ((1/(circleMap z r θ-z)^2) • f (circleMap z r θ))) hP.le
  rw [hnorm,norm_smul,norm_mul,norm_mul,Complex.norm_two,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_one] at hbound
  simp only [hleft,intervalIntegral.integral_const_mul] at hbound
  change P*‖deriv f z‖≤r⁻¹*_ at hbound
  have hder : ‖deriv f z‖≤(∫ θ in (0:ℝ)..P, ‖f (circleMap z r θ)‖)/(P*r) := by
    apply (le_div_iff₀ (mul_pos hP hr)).mpr
    field_simp [hr.ne'] at hbound
    linarith only [hbound]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hder 4
  have hj := integral_fourth_power_mean (a:=0) (b:=P) hP hF
  rw [sub_zero] at hj
  rw [div_pow] at hh
  apply hh.trans
  change _≤(P*r^4)⁻¹*_
  exact (div_le_div_of_nonneg_right hj (by positivity)).trans_eq (by field_simp; ring)

/-- Interchanging two finite interval integrals of a continuous function. -/
theorem integral_integral_swap_on_rectangle {F : ℝ×ℝ → ℝ} (hF : Continuous F)
    {a b l u : ℝ} (hab : a≤b) (hlu : l≤u) :
    (∫ x in a..b, ∫ y in l..u,F (x,y))=∫ y in l..u, ∫ x in a..b,F (x,y) := by
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hlu]
  apply integral_integral_swap
  change Integrable F ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc l u)))
  rw [Measure.prod_restrict]
  exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Integrated fourth-power Cauchy estimate for a finite family. The
input moment bound may be summed over the family before taking its
uniform bound in the angle. -/
theorem family_deriv_fourth_le_of_circle_means {ι : Type*} (S : Finset ι) (f : ι→ℂ→ℂ)
    {σ r a b M : ℝ} (hr : 0<r) (hab : a≤b)
    (hDiff : ∀ i∈S, ∀ t∈Icc a b,DifferentiableOn ℂ (f i) (closedBall ((σ:ℂ)+t*I) r))
    (hDer : ∀ i∈S,Continuous (fun t : ℝ => deriv (f i) ((σ:ℂ)+t*I)))
    (hCircle : ∀ i∈S, Continuous (fun x : ℝ×ℝ => ‖f i (circleMap ((σ:ℂ)+x.1*I) r x.2)‖^4))
    (hM : ∀ θ∈Icc 0 (2*Real.pi), (∑ i∈S, ∫ t in a..b,‖f i (circleMap ((σ:ℂ)+t*I) r θ)‖^4) ≤ M) :
    (∑ i∈S, ∫ t in a..b, ‖deriv (f i) ((σ:ℂ)+t*I)‖^4) ≤ M/r^4 := by
  let P := 2*Real.pi
  have hP : 0<P := by dsimp [P];positivity
  let F (i : ι) (x : ℝ×ℝ) := ‖f i (circleMap ((σ:ℂ)+x.1*I) r x.2)‖^4
  let D := (P*r^4)⁻¹
  have hD : 0≤D := by dsimp [D];positivity
  have ht (i : ι) (hi : i∈S) : Continuous (fun t : ℝ => ∫ θ in (0:ℝ)..P, F i (t,θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f:=fun t θ => F i (t,θ)) (hCircle i hi) 0 P
  have hθ (i : ι) (hi : i∈S) : Continuous (fun θ : ℝ => ∫ t in a..b, F i (t,θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f:=fun θ t => F i (t,θ)) ((hCircle i hi).comp continuous_swap) a b
  have hh (i : ι) (hi : i∈S) : (∫ t in a..b,‖deriv (f i) ((σ:ℂ)+t*I)‖^4)≤D*(∫ θ in (0:ℝ)..P,∫ t in a..b,F i (t,θ)) := by
    rw [←integral_integral_swap_on_rectangle (hCircle i hi) hab hP.le,←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (((hDer i hi).norm.pow 4).intervalIntegrable ..)
      ((continuous_const.mul (ht i hi)).intervalIntegrable ..) (fun t ht => deriv_fourth_le_circle_mean hr (hDiff i hi t ht))
  apply (Finset.sum_le_sum hh).trans
  rw [←Finset.mul_sum,←intervalIntegral.integral_finsetSum (s:=S) (fun i hi => (hθ i hi).intervalIntegrable ..)]
  have hlast := intervalIntegral.integral_mono_on hP.le
    ((continuous_finsetSum S (fun i hi => hθ i hi)).intervalIntegrable («μ»:=volume) 0 P)
    (intervalIntegrable_const (c:=M)) (fun θ hθ => hM θ hθ)
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hlast
  exact (mul_le_mul_of_nonneg_left hlast hD).trans_eq (by dsimp [D];field_simp)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
