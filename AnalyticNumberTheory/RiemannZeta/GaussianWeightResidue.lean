import AnalyticNumberTheory.RiemannZeta.GaussianWeightShift

/-!
# The residue of a smoothed Dirichlet weight

Moving a Gaussian weight across the origin extracts the full completion factor.
The displacement on the left must keep the translated gamma factor in the
right half-plane.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

/-- Moving a Mellin weight from a positive line to a negative line adds precisely the
residue of its Cauchy denominator. -/
theorem xiDirichletWeight_sub_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : a < s.re) (k n : ℕ) (hn : 0 < n) :
    xiDirichletWeight s k b n - xiDirichletWeight s k (-a) n =
      2*π*xiCompletionFactor s^k := by
  let F (w : ℂ) := xiCompletionFactor (s+w)^k*Complex.exp (w^2)/(n:ℂ)^w
  let U := {w : ℂ | 0 < (s+w).re}
  have hU : IsOpen U := isOpen_lt continuous_const
    (Complex.continuous_re.comp (continuous_const.add continuous_id))
  have hnc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hdiff : DifferentiableOn ℂ F U := by
    intro w hw
    have hh : 0 < (s+w).re := hw
    have hx : DifferentiableAt ℂ (fun w : ℂ => xiCompletionFactor (s+w)) w :=
      (differentiableAt_xiCompletionFactor hh).comp w ((differentiableAt_const _).add differentiableAt_id)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div ((hx.pow k).mul (Complex.differentiableAt_exp.comp w (differentiableAt_id.pow 2)))
    · change DifferentiableAt ℂ (fun w : ℂ => (n:ℂ)^w) w
      simp_rw [Complex.cpow_def_of_ne_zero hnc]
      fun_prop
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  obtain ⟨D,hD,hbound⟩ := xiGaussianNumerator_strip_bound s k n hn
    (by linarith : 0 < s.re+(-a)) (by linarith : -a ≤ a)
  have h := verticalCauchyIntegral_sub_neg (F := F) (fun z hz => (hdiff.analyticOnNhd hU) z
    (by change 0 < (s+z).re; rw [Complex.add_re]; linarith [hz.1])) ha hD hbound
  have he (x : ℝ) : verticalCauchyIntegral F x = xiDirichletWeight s k x n := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [F,xiGaussianKernel]
    ring
  rw [he,he] at h
  rw [xiDirichletWeight_eq_of_pos s (by linarith) k n hn hb ha]
  simpa [F] using h

/-- Complex conjugation commutes with the factor relating zeta to its entire completion. -/
theorem xiCompletionFactor_conj (s : ℂ) :
    xiCompletionFactor (conj s) = conj (xiCompletionFactor s) := by
  simp only [xiCompletionFactor,Complex.Gammaℝ_conj,map_mul,map_sub,map_div₀,map_one,map_ofNat]

end AnalyticNumberTheory.RiemannZeta
