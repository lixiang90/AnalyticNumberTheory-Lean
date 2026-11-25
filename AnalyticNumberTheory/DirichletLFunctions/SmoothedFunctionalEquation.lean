import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion
import AnalyticNumberTheory.RiemannZeta.SmoothedFunctionalEquation

/-!
# Gaussian functional equation for primitive Dirichlet L-functions

The conductor factor is divided symmetrically between the two sides.
The completed function at the center is a sum of two right-line integrals,
one for the character and one for its dual.
-/

open Real Complex Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The conductor contribution on a shifted vertical contour. -/
noncomputable def conductorWeight (q : ℕ) (w : ℂ) := (q:ℂ)^(w/2)

theorem differentiable_conductorWeight {q : ℕ} [NeZero q] : Differentiable ℂ (conductorWeight q) := by
  unfold conductorWeight; simp_rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q))]; fun_prop

theorem norm_conductorWeight {q : ℕ} [NeZero q] (w : ℂ) :
    ‖conductorWeight q w‖=(q:ℝ)^(w.re/2) := by
  unfold conductorWeight; rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q) : (0:ℝ)<q)]
  simp

/-- A positive-line integral in the smoothed functional equation. -/
noncomputable def completedLGaussianIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (c : ℝ) :=
  verticalCauchyIntegral (fun w => χ.completedLFunction (s+w)*conductorWeight q w*Complex.exp (w^2)) c

private theorem completedLGaussian_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) (s : ℂ) {c : ℝ} (hc : 0<c) :
    ∃ D : ℝ,0≤D ∧ ∀ x∈Icc (-c) c,∀ t : ℝ,
      ‖χ.completedLFunction (s+((x:ℂ)+t*I))*conductorWeight q ((x:ℂ)+t*I)*
        Complex.exp (((x:ℂ)+t*I)^2)‖≤D/(1+t^2) := by
  obtain ⟨A,B,hA,hB,H⟩ := norm_completedLFunction_le_exp_norm_mul_log hχ hq
  have hcont := (differentiable_completedLFunction_of_ne_one (isPrimitive_ne_one hχ hq)).continuous
  obtain ⟨w,_,hmax⟩ := (isCompact_closedBall (0:ℂ) 3).exists_isMaxOn
    (f:=fun w => ‖χ.completedLFunction w‖) (Metric.nonempty_closedBall.mpr (by norm_num)) hcont.norm.continuousOn
  let A' := A+‖χ.completedLFunction w‖
  have hA' : 0≤A' := by dsimp [A']; positivity
  have H' (z : ℂ) : ‖χ.completedLFunction z‖≤A'*Real.exp (B*‖z‖*Real.log (‖z‖+2)) := by
    by_cases hz : 3≤‖z‖
    · apply (H z hz).trans
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _)) (Real.exp_pos _).le
    · have hm := hmax (show z∈Metric.closedBall (0:ℂ) 3 by simpa using (le_of_not_ge hz))
      apply hm.trans
      apply (le_add_of_nonneg_left hA).trans
      apply le_mul_of_one_le_right hA'
      apply Real.one_le_exp
      have := Real.log_nonneg (by linarith [norm_nonneg z] : 1≤‖z‖+2)
      positivity
  obtain ⟨D,hD,HD⟩ := RiemannZeta.gaussian_strip_bound_of_exp_norm_mul_log
    χ.completedLFunction hA' hB H' s 1 hc
  refine ⟨D*(q:ℝ)^(c/2),by positivity,?_⟩
  intro x hx t
  let z := (x:ℂ)+t*I
  have hz : z.re=x := by simp [z]
  have hw := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1≤q by omega) : (1:ℝ)≤q) (by linarith [hx.2] : x/2≤c/2)
  have hd := HD x hx t
  simp only [pow_one] at hd
  change ‖χ.completedLFunction (s+z)*conductorWeight q z*Complex.exp (z^2)‖≤_
  rw [mul_right_comm,norm_mul,norm_conductorWeight,hz]
  exact (mul_le_mul hd hw (by positivity) (by positivity)).trans_eq (by ring)

 /-- Symmetric integral identity for each primitive character of modulus at
least two. The coefficient of its dual is the root number times the
conductor phase `q^(1/2-s)`. -/
theorem completedL_gaussian_functional_equation {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) (s : ℂ) {c : ℝ} (hc : 0<c) :
    completedLGaussianIntegral χ s c +
      ((q:ℂ)^(1/2-s)*χ.rootNumber)*completedLGaussianIntegral (star χ) (1-s) c =
        2*π*χ.completedLFunction s := by
  let F (w : ℂ) := χ.completedLFunction (s+w)*conductorWeight q w*Complex.exp (w^2)
  have hf : Differentiable ℂ F :=
    (((differentiable_completedLFunction_of_ne_one (isPrimitive_ne_one hχ hq)).comp
      ((differentiable_const s).add differentiable_id)).mul differentiable_conductorWeight).mul
      (Complex.differentiable_exp.comp (differentiable_id.pow 2))
  obtain ⟨D,hD,HD⟩ := completedLGaussian_strip hχ hq s hc
  have h := verticalCauchyIntegral_add_reflect (F:=F) hf hc hD HD
  let W := (q:ℂ)^(1/2-s)*χ.rootNumber
  have href (w : ℂ) : F (-w) = W*((star χ).completedLFunction ((1-s)+w)*conductorWeight q w*Complex.exp (w^2)) := by
    have hz := completedLFunction_one_sub_primitive hχ ((1-s)+w)
    rw [show 1-(1-s+w)=s+ -w by ring] at hz
    dsimp only [F,W,conductorWeight]
    rw [hz,neg_sq]
    have hn : (q:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    have he : (q:ℂ)^(1-s+w-1/2)*(q:ℂ)^(-w/2)=(q:ℂ)^(1/2-s)*(q:ℂ)^(w/2) := by
      rw [←Complex.cpow_add _ _ hn,←Complex.cpow_add _ _ hn]; congr 1; ring
    linear_combination (norm:=ring_nf) χ.rootNumber*(star χ).completedLFunction ((1-s)+w)*Complex.exp (w^2)*he
  have hr : verticalCauchyIntegral (fun z => F (-z)) c=W*completedLGaussianIntegral (star χ) (1-s) c := by
    simp only [completedLGaussianIntegral,verticalCauchyIntegral,href,mul_div_assoc,integral_const_mul]
  rw [hr] at h
  simpa only [F,W,completedLGaussianIntegral,conductorWeight,add_zero,zero_div,Complex.cpow_zero,zero_pow (by decide : 2≠0),
    Complex.exp_zero,mul_one] using h

end AnalyticNumberTheory.DirichletLFunctions
