import AnalyticNumberTheory.RiemannZeta.TranslatedPartialFractions
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis
import AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-! # The Poisson sum of zeros from the symmetry of the completed zeta function -/

noncomputable section

open Complex
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.RiemannZeta

/-- Reflection around one half makes the derivative of the completed zeta function vanish there. -/
theorem deriv_xi_half : deriv xi (1 / 2 : ℂ) = 0 := by
  let c : ℂ := 1 / 2
  have hc : 1 - c = c := by dsimp [c]; norm_num
  have hlin := (hasDerivAt_const c (1 : ℂ)).sub (hasDerivAt_id' c)
  have h := (differentiable_xi (1-c)).hasDerivAt.comp c hlin
  change HasDerivAt (fun w : ℂ => xi (1-w)) (deriv xi (1-c)*(0-1)) c at h
  rw [show (fun w : ℂ => xi (1-w)) = xi from funext xi_one_sub, hc] at h
  have he := h.deriv
  change deriv xi c = 0
  linear_combination (1/2 : ℂ)*he

/-- The Hadamard logarithmic derivative of ξ is independent of the chosen
multiplicity-respecting enumeration of its zeros. -/
theorem ZetaZeroEnumeration.exists_logDeriv_xi_centered (Z : ZetaZeroEnumeration) :
    ∃ B : ℂ, ∀ {s : ℂ}, s ≠ 0 → xi s ≠ 0 →
      deriv xi s / xi s = B + ∑' n, centeredPole (Z.zero n) s := by
  obtain ⟨a, B, ha, hf, hm, hsum, _, H⟩ := exists_hadamard_factorization_xi
  have hA : Summable fun n => (‖a n‖^2)⁻¹ := by
    convert hsum using 1
    ext n
    rw [Real.rpow_neg (norm_nonneg _)]
    norm_num
  let W : ZetaZeroEnumeration := ⟨a, ha, hf, hm, hA⟩
  refine ⟨B, fun {s} hs hxi => ?_⟩
  have hw (n : ℕ) : s ≠ W.zero n := by
    intro he
    have hz := W.mem_strip n
    rw [criticalStripZeros_eq_xi_zeros] at hz
    exact hxi (he ▸ hz)
  have hwSum := (W.hasSum_distinct (f := fun ρ => centeredPole ρ s) (W.summable_centered s).hasSum).tsum_eq
  have hzSum := (Z.hasSum_distinct (f := fun ρ => centeredPole ρ s) (Z.summable_centered s).hasSum).tsum_eq
  rw [H s hs hxi, ← hzSum, hwSum]
  congr 1
  exact tsum_congr fun n => (centeredPole_eq (W.zero_ne_zero n) (hw n)).symm

/-- Poisson mass of the zero ordinates, with horizontal displacement measured from
the critical line. Under RH all zeros have this same horizontal displacement. -/
def ZetaZeroEnumeration.poissonMass (Z : ZetaZeroEnumeration) (s : ℂ) : ℝ :=
  (s.re-1/2) * ∑' n, (‖Z.zero n-s‖^2)⁻¹

/-- Under RH the real logarithmic derivative of ξ is exactly the Poisson mass.
The constant in the Hadamard expansion cancels on evaluating at one half. -/
theorem ZetaZeroEnumeration.re_logDeriv_xi_eq_poissonMass (Z : ZetaZeroEnumeration)
    (hRH : RiemannHypothesisProp) {s : ℂ} (hs : s ≠ 0) (hxi : xi s ≠ 0) :
    (deriv xi s / xi s).re = Z.poissonMass s := by
  let c : ℂ := 1 / 2
  have hc : xi c ≠ 0 := by simpa [c] using xi_ne_zero_ofReal (1/2)
  have hn {z : ℂ} (hz : xi z ≠ 0) (n : ℕ) : z ≠ Z.zero n := by
    intro he
    have h := Z.mem_strip n
    rw [criticalStripZeros_eq_xi_zeros] at h
    exact hz (he ▸ h)
  obtain ⟨B, H⟩ := Z.exists_logDeriv_xi_centered
  have hdiff := congrArg Complex.re (congrArg₂ (· - ·) (H hs hxi) (H (s := c) (by norm_num [c]) hc))
  have hsum := (Z.summable_centered s).hasSum.sub (Z.summable_centered c).hasSum
  have hreal := Complex.hasSum_re hsum
  have ht (n : ℕ) : (centeredPole (Z.zero n) s - centeredPole (Z.zero n) c).re =
      (s.re-1/2) * (‖Z.zero n-s‖^2)⁻¹ := by
    have hr := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)
    rw [centeredPole_eq (Z.zero_ne_zero n) (hn hxi n), centeredPole_eq (Z.zero_ne_zero n) (hn hc n)]
    simp only [add_sub_add_right_eq_sub, Complex.sub_re, one_div, Complex.inv_re,
      Complex.normSq_eq_norm_sq, hr, norm_sub_rev s (Z.zero n)]
    norm_num [c, div_eq_mul_inv]
  have hmass : Z.poissonMass s =
      ((∑' n, centeredPole (Z.zero n) s) - ∑' n, centeredPole (Z.zero n) c).re := by
    unfold ZetaZeroEnumeration.poissonMass
    rw [← tsum_mul_left]
    exact (hreal.congr_fun (fun n => (ht n).symm)).tsum_eq
  rw [hmass]
  simp only [c, deriv_xi_half, zero_div, sub_zero, add_sub_add_left_eq_sub] at hdiff
  exact hdiff

end AnalyticNumberTheory.RiemannZeta
