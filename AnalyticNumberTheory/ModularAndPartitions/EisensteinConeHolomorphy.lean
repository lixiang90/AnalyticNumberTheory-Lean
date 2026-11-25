import AnalyticNumberTheory.ModularAndPartitions.EisensteinPeriods

/-!
# Holomorphy of the absolutely convergent cone series

Two neighboring real weights give a summable majorant on every
compact rectangle in the half-plane of absolute convergence.
-/

open Complex Real Set Filter
open scoped UpperHalfPlane Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private def coneVector (z : ℍ) (v : Fin 2→ℤ) : ℂ := (v 0:ℂ)*(z:ℂ)+v 1

private theorem summable_vector_norm (z : ℍ) {u : ℝ} (hu : 2<u) :
    Summable (fun v : Fin 2→ℤ => ‖coneVector z v‖^(-u)) := by
  have h : Summable fun v : Fin 2→ℤ => eisensteinLatticeTerm z (u:ℂ) (v 0) (v 1) :=
    (finTwoArrowEquiv ℤ).summable_iff.mpr (summable_eisensteinLatticeTerm z hu)
  apply h.norm.congr; intro v
  have hu' : -u≠0 := by linarith
  have he : ‖eisensteinReflection (u:ℂ)‖=1 := by simp [eisensteinReflection,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  rw [eisensteinLatticeTerm]
  split_ifs with h₀ h₁
  · simp [coneVector,h₀.1,h₀.2,Real.zero_rpow hu']
  · simp only [←Complex.ofReal_neg,Complex.norm_cpow_real,coneVector]
  · simp only [norm_mul,he,one_mul,←Complex.ofReal_neg,Complex.norm_cpow_real,norm_neg,coneVector]

/-- The original cone sum is holomorphic throughout `Re s>2`. -/
theorem differentiableOn_eisensteinConeSum (c d : ℤ) (z : ℍ) :
    DifferentiableOn ℂ (eisensteinConeSum c d z) {s : ℂ | 2<s.re} := by
  intro s hs
  change 2<s.re at hs
  let l := (2+s.re)/2
  let r := s.re+1
  let M := |s.im|+1
  let U := {u : ℂ | l<u.re ∧ u.re<r ∧ |u.im|<M}
  have hl : 2<l := by dsimp [l]; linarith
  have hr : 2<r := by dsimp [r]; linarith
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt Complex.continuous_im.abs continuous_const))
  have hmem : s∈U := by change (2+s.re)/2<s.re ∧ s.re<s.re+1 ∧ |s.im| < |s.im|+1; constructor <;> first | linarith | constructor <;> linarith
  let F (v : Fin 2→ℤ) (u : ℂ) := if 0≤v 0 ∧ d*v 0<c*v 1 then (coneVector z v)^(-u) else 0
  have hsum := ((summable_vector_norm z hl).add (summable_vector_norm z hr)).mul_right (Real.exp (π*M))
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableWithinAt.differentiableAt _ (hU.mem_nhds hmem)
  change DifferentiableWithinAt ℂ (fun u => ∑' v : Fin 2→ℤ,F v u) U s
  apply Complex.differentiableOn_tsum_of_summable_norm hsum _ hU _ s hmem
  · intro v u hu
    by_cases hv : 0≤v 0 ∧ d*v 0<c*v 1
    · simp only [F,if_pos hv]
      apply DifferentiableAt.differentiableWithinAt
      refine differentiableAt_id.neg.const_cpow (Or.inr ?_)
      intro e; have h₁ := hu.1; change -u=0 at e; simp [neg_eq_zero.mp e] at h₁; linarith
    · simp only [F,if_neg hv]; fun_prop
  · intro v u hu
    let x := ‖coneVector z v‖
    have hx : 0≤x := norm_nonneg _
    have hrpow (v : ℝ) : 0≤x^v := Real.rpow_nonneg hx _
    change ‖F v u‖≤(x^(-l)+x^(-r))*Real.exp (π*M)
    by_cases hv : 0≤v 0 ∧ d*v 0<c*v 1
    · simp only [F,if_pos hv]
      have h₁ := AnalyticTools.norm_cpow_le_arg_bound (coneVector z v) (-u)
      simp only [Complex.neg_re,Complex.neg_im,abs_neg] at h₁
      apply h₁.trans
      have hpow : x^(-u.re)≤x^(-l)+x^(-r) := by
        rcases le_or_gt 1 x with h|h
        · exact (Real.rpow_le_rpow_of_exponent_le h (neg_le_neg hu.1.le)).trans (le_add_of_nonneg_right (hrpow _))
        rcases eq_or_lt_of_le hx with h₀|h₀
        · rw [←h₀]; have hh : -(u.re)≠0 := by have := hu.1; linarith
          rw [Real.zero_rpow hh]; positivity
        · exact (Real.rpow_le_rpow_of_exponent_ge h₀ h.le (neg_le_neg hu.2.1.le)).trans (le_add_of_nonneg_left (hrpow _))
      exact mul_le_mul hpow (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2.2.le Real.pi_pos.le))
        (Real.exp_pos _).le (add_nonneg (hrpow _) (hrpow _))
    · simp only [F,if_neg hv,norm_zero]; positivity

end AnalyticNumberTheory.ModularAndPartitions
