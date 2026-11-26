import AnalyticNumberTheory.AnalyticTools.SymmetricPoleKernel
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Symmetric differences of differentiable functions and individual poles -/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- The central difference quotient of a complex-valued function of a real variable
recovers its derivative as the positive width tends to zero. -/
theorem tendsto_symmetricDifference_of_hasDerivAt {f : ℝ → ℂ} {d : ℂ} {u : ℝ}
    (hf : HasDerivAt f d u) :
    Tendsto (fun h : ℝ => (f (u+h)-f (u-h))/(2*(h : ℂ))) (𝓝[>] 0) (𝓝 d) := by
  have ha : HasDerivAt (fun h : ℝ => u+h) 1 0 := (hasDerivAt_id 0).const_add u
  have hs : HasDerivAt (fun h : ℝ => u-h) (-1) 0 := (hasDerivAt_id 0).const_sub u
  have hd : HasDerivAt (fun h : ℝ => f (u+h)-f (u-h)) (d+d) 0 := by
    have h₁ := (show HasDerivAt f d (u+(0 : ℝ)) by simpa using hf).scomp 0 ha
    have h₂ := (show HasDerivAt f d (u-(0 : ℝ)) by simpa using hf).scomp 0 hs
    simpa only [Function.comp_def, Pi.sub_def, one_smul, neg_smul, sub_neg_eq_add] using h₁.sub h₂
  have H := hd.tendsto_slope_zero_right.div_const (2 : ℂ)
  convert H using 1
  · funext h
    simp [Complex.real_smul, div_eq_mul_inv, mul_inv_rev]
    ring
  · congr 1
    ring

/-- On the positive logarithmic axis the derivative of one integrated pole is
the exponential with a single pole denominator. -/
theorem hasDerivAt_integratedPole (ω : ℂ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (integratedPole ω) (Complex.exp (ω*u)/ω) u := by
  have hlin : HasDerivAt (fun t : ℝ => ω*(t : ℂ)) ω u := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul ω
  have H := ((hlin.cexp.sub_const 1).div_const (ω^2))
  have he : Complex.exp (ω*u)/ω = Complex.exp (ω*u)*ω/ω^2 := by
    by_cases hn : ω=0
    · simp [hn]
    · field_simp
  rw [he]
  apply H.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hu] with v hv
  simp only [integratedPole, max_eq_left hv.le]

/-- The symmetric regularization of a single pole tends to its unweighted contribution. -/
theorem tendsto_symmetricPole (ω : ℂ) {u : ℝ} (hu : 0 < u) :
    Tendsto (symmetricPole ω u) (𝓝[>] 0) (𝓝 (Complex.exp (ω*u)/ω)) := by
  apply (tendsto_symmetricDifference_of_hasDerivAt (hasDerivAt_integratedPole ω hu)).congr'
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hu).filter_mono nhdsWithin_le_nhds] with h hh hsmall
  change 0 < h at hh
  exact (symmetricPole_eq_difference ω (by linarith) (by linarith)).symm

end AnalyticNumberTheory.AnalyticTools
