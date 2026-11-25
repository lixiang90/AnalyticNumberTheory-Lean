import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The circular arc below the diagonal

The graph `t ↦ √(x−t²)` has bounded slope on `[0,√(x/2)]`. Its integral
up to the diagonal is the sum of an octant sector and a right triangle.
-/

noncomputable section
open Real MeasureTheory
open intervalIntegral
open scoped Topology
namespace AnalyticNumberTheory.DivisorProblems

/-- The upper circle of squared radius `x`, viewed as a function of its first coordinate. -/
def circleArc (x t : ℝ) : ℝ := Real.sqrt (x-t^2)

theorem continuous_circleArc (x : ℝ) : Continuous (circleArc x) := by unfold circleArc; fun_prop

theorem circleArc_hasDerivAt {x t : ℝ} (ht : t^2<x) :
    HasDerivAt (circleArc x) (-t/circleArc x t) t := by
  have hp : 0<x-t^2 := sub_pos.mpr ht
  have h := ((hasDerivAt_id t).pow 2).const_sub x
  apply (h.sqrt hp.ne').congr_deriv
  dsimp [circleArc]; ring

theorem circleArc_deriv_hasDerivAt {x t : ℝ} (ht : t^2<x) :
    HasDerivAt (fun t => -t/circleArc x t) (-x/(circleArc x t)^3) t := by
  have h : 0<circleArc x t := Real.sqrt_pos.mpr (sub_pos.mpr ht)
  have hh : (circleArc x t)^2=x-t^2 := Real.sq_sqrt (sub_nonneg.mpr ht.le)
  apply ((hasDerivAt_id t).neg.div (circleArc_hasDerivAt ht) h.ne').congr_deriv
  field_simp [h.ne']; simp only [Pi.neg_apply,id_eq]; nlinarith only [hh]

/-- The area under the first octant's circular arc, in the squared-radius parameter. -/
theorem integral_circleArc_to_diagonal {x : ℝ} (hx : 0≤x) :
    ∫ t in (0:ℝ)..(Real.sqrt (x/2)), circleArc x t = Real.pi*x/8+x/4 := by
  let R := Real.sqrt x
  have hR : 0≤R := Real.sqrt_nonneg _
  have hR2 : R^2=x := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hdiag : R*Real.sin (Real.pi/4) = Real.sqrt (x/2) := by
    rw [Real.sin_pi_div_four]
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by linarith) (by positivity)).mpr
    rw [mul_pow,div_pow,h2,hR2]; ring
  let f := fun t : ℝ => R*Real.sin t
  let df := fun t : ℝ => R*Real.cos t
  have hsub := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=Real.pi/4) (f:=f) (f':=df)
    (g:=circleArc x) (fun t _ => (Real.hasDerivAt_sin t).const_mul R) (by dsimp only [df]; fun_prop)
    (continuous_circleArc x)
  have hπ : 0≤Real.pi/4 := by positivity
  have h0 : f 0=0 := by simp [f]
  rw [h0,show f (Real.pi/4)=Real.sqrt (x/2) from hdiag] at hsub
  rw [←hsub]
  calc
    _ = ∫ t in (0:ℝ)..(Real.pi/4), x*Real.cos t^2 := by
      apply intervalIntegral.integral_congr; intro t ht
      rw [Set.uIcc_of_le hπ] at ht
      have hcos := Real.cos_eq_sqrt_one_sub_sin_sq (by linarith [Real.pi_pos,ht.1] : -(Real.pi/2)≤t) (by linarith [Real.pi_pos,ht.2] : t≤Real.pi/2)
      dsimp only [Function.comp_apply,circleArc,f,df]
      have hs : x-(R*Real.sin t)^2=R^2*(1-Real.sin t^2) := by rw [←hR2]; ring
      rw [hs,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hR,←hcos,←hR2]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_cos_sq,Real.cos_pi_div_four,Real.sin_pi_div_four,Real.sin_zero,Real.cos_zero]
      nlinarith only [congrArg (fun z : ℝ => x*z) h2]

end AnalyticNumberTheory.DivisorProblems
