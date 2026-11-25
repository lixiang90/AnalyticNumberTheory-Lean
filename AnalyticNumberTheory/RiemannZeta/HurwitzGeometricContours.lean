import AnalyticNumberTheory.RiemannZeta.HurwitzRotatedTails
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Geometric Fourier sums on sloped contours

A half-integer direct cutoff makes the geometric denominator regular at
the crossing of the real axis. Absolute convergence holds off the crossing,
and uniform bounds justify integration of the limiting geometric sum.
-/
noncomputable section
open Complex Real Finset Filter Set MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- Ratio of consecutive modes on a half-integer contour. -/
def hurwitzRayRatio (d v : ℝ) : ℂ := -Complex.exp ((2*Real.pi*v:ℝ)*(-1+(d:ℂ)*I))

theorem norm_hurwitzRayRatio (d v : ℝ) :
    ‖hurwitzRayRatio d v‖=Real.exp (-2*Real.pi*v) := by
  rw [hurwitzRayRatio,norm_neg,Complex.norm_exp];congr 1;simp [mul_re]

theorem hurwitzRayRatio_ne_one (d v : ℝ) : hurwitzRayRatio d v≠1 := by
  intro h
  have H := congrArg norm h
  rw [norm_one,norm_hurwitzRayRatio,Real.exp_eq_one_iff] at H
  have hv : v=0 := by rcases mul_eq_zero.mp H with hh|hh <;> simp_all [Real.pi_ne_zero]
  subst v;norm_num [hurwitzRayRatio] at h

/-- A uniform bound for the reciprocal on the upper half of the ray. -/
theorem hurwitzRayRatio_inv_bound (d : ℝ) : ∃ C : ℝ, 0<C ∧ ∀ v : ℝ, 0≤v → ‖(1-hurwitzRayRatio d v)⁻¹‖≤C := by
  let F (v : ℝ) := (1-hurwitzRayRatio d v)⁻¹
  have hf : Continuous F := by
    apply Continuous.inv₀ _ (fun v => sub_ne_zero.mpr (hurwitzRayRatio_ne_one d v).symm)
    unfold hurwitzRayRatio;fun_prop
  obtain ⟨M,hM⟩ := (isCompact_Icc (a:=(0:ℝ)) (b:=1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 2 M,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro v hv
  by_cases hh : v≤1
  · exact (hM v ⟨hv,hh⟩).trans (le_max_right _ _)
  · have hq : ‖hurwitzRayRatio d v‖≤1/2 := by
      rw [norm_hurwitzRayRatio,show -2*Real.pi*v= -(2*Real.pi*v) by ring,Real.exp_neg]
      apply inv_le_comm₀ (Real.exp_pos _) (by norm_num) |>.mpr
      norm_num
      apply le_trans (Real.add_one_le_exp _ |>.trans' (by nlinarith [Real.pi_gt_three,mul_nonneg (sub_nonneg.mpr (not_le.mp hh).le) Real.pi_pos.le] : (2:ℝ)≤2*Real.pi*v+1)) le_rfl
    have hd := norm_sub_norm_le (1:ℂ) (hurwitzRayRatio d v)
    rw [norm_one] at hd
    rw [norm_inv];apply (inv_le_comm₀ (by linarith) (by positivity : 0<max 2 M)).mpr
    apply (inv_le_inv₀ (by positivity : 0<max 2 M) (by norm_num : (0:ℝ)<2)).mpr (le_max_left _ _) |>.trans
    linarith

/-- Geometric summation under an arbitrary integrable weight on the ray.
The assumptions allow the weight itself to have no decay at infinity. -/
theorem tendsto_hurwitzRay_geometric_integral (d : ℝ) (q : ℕ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hi : IntegrableOn (fun v : ℝ => ‖f v‖ * Real.exp (-2*Real.pi*v)) (Ioi 0)) :
    Tendsto (fun N : ℕ => ∫ v in Ioi (0:ℝ), f v*(hurwitzRayRatio d v)^(q+1)*
      (∑ n∈range N,(hurwitzRayRatio d v)^n)) atTop
      (𝓝 (∫ v in Ioi (0:ℝ), f v*(hurwitzRayRatio d v)^(q+1)/(1-hurwitzRayRatio d v))) := by
  obtain ⟨C,hC,hbound⟩ := hurwitzRayRatio_inv_bound d
  have hmeas : Continuous (hurwitzRayRatio d) := by unfold hurwitzRayRatio;fun_prop
  refine tendsto_integral_of_dominated_convergence (fun v : ℝ => (2*C)*(‖f v‖*Real.exp (-2*Real.pi*v))) ?_
    (hi.const_mul (2*C)) ?_ ?_
  · intro N
    exact (hf.mul (hmeas.pow _).aestronglyMeasurable).mul ((continuous_finsetSum _ (fun n _ => hmeas.pow n)).aestronglyMeasurable)
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    let r := hurwitzRayRatio d v
    have h1 : ‖r‖<1 := by rw [norm_hurwitzRayRatio,Real.exp_lt_one_iff];nlinarith [Real.pi_pos,mem_Ioi.mp hv,mul_pos Real.pi_pos (mem_Ioi.mp hv)]
    have hr : r≠1 := hurwitzRayRatio_ne_one d v
    have hp : ‖r^(q+1)‖≤‖r‖ := by rw [norm_pow,pow_succ];apply mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h1.le)
    have hg : ‖∑ n∈range N,r^n‖≤2*C := by
      rw [geom_sum_eq hr,norm_div,div_eq_mul_inv,←norm_inv]
      have hden : ‖(r-1)⁻¹‖≤C := by rw [norm_inv,norm_sub_rev,←norm_inv];exact hbound v (mem_Ioi.mp hv).le
      apply mul_le_mul ((norm_sub_le _ _).trans (by rw [norm_pow,norm_one];linarith [pow_le_one₀ (norm_nonneg r) h1.le (n:=N)])) hden (norm_nonneg _) (by norm_num)
    change ‖f v*r^(q+1)*(∑ n∈range N,r^n)‖≤_
    rw [norm_mul,norm_mul,←norm_hurwitzRayRatio d v]
    nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (f v)),mul_le_mul hg (mul_le_mul_of_nonneg_left hp (norm_nonneg (f v))) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity : 0≤2*C)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hr : ‖hurwitzRayRatio d v‖<1 := by rw [norm_hurwitzRayRatio,Real.exp_lt_one_iff];nlinarith [mul_pos Real.pi_pos (mem_Ioi.mp hv)]
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hr).tendsto_sum_nat.const_mul (f v*(hurwitzRayRatio d v)^(q+1))

end AnalyticNumberTheory.RiemannZeta
