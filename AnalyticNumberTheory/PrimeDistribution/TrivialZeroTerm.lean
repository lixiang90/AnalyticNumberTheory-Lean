import AnalyticNumberTheory.AnalyticTools.SymmetricPoleLimit
import AnalyticNumberTheory.PrimeDistribution.SymmetricExplicitFormula
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The elementary contribution of the trivial zeros to the Chebyshev formula -/

noncomputable section

open Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem exp_trivialZetaZero (n : ℕ) (u : ℝ) :
    Complex.exp (trivialZetaZero n * (u : ℂ)) = ((Real.exp (-2*u) ^ (n+1) : ℝ) : ℂ) := by
  rw [← Real.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  unfold trivialZetaZero
  ring

private theorem re_trivial_nonpos (n : ℕ) : (trivialZetaZero n).re ≤ 0 := by
  simp [trivialZetaZero, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem one_le_norm_trivialZetaZero (n : ℕ) : 1 ≤ ‖trivialZetaZero n‖ := by
  rw [trivialZetaZero, norm_mul, ← Nat.cast_add_one, Complex.norm_natCast]
  norm_num
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Summing the unweighted trivial-zero terms gives half the logarithm of
`1-exp(-2u)` for positive logarithmic arguments. -/
theorem hasSum_exp_trivialZetaZero_div {u : ℝ} (hu : 0 < u) :
    HasSum (fun n => Complex.exp (trivialZetaZero n * (u : ℂ))/trivialZetaZero n)
      ((Real.log (1-Real.exp (-2*u)) : ℂ)/2) := by
  have hq : |Real.exp (-2*u)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have H := Complex.hasSum_ofReal.mpr ((Real.hasSum_pow_div_log_of_abs_lt_one hq).mul_left (-1/2 : ℝ))
  convert H using 1
  · funext n
    rw [exp_trivialZetaZero]
    push_cast
    unfold trivialZetaZero
    simp only [div_eq_mul_inv, mul_inv_rev, inv_neg]
    ring
  · push_cast
    ring

/-- The integrated trivial-zero series is differentiable at every positive argument.
The derivative is the elementary logarithm obtained by summing over the negative even integers. -/
theorem hasDerivAt_tsum_integrated_trivialZetaZero {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => ∑' n, integratedPole (trivialZetaZero n) v)
      ((Real.log (1-Real.exp (-2*u)) : ℂ)/2) u := by
  let q := Real.exp (-u)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hsum : Summable (fun n : ℕ => q^(n+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (Real.exp_pos _).le hq)
  have hh : u ∈ Ioi (u/2) := by change u/2 < u; linarith
  rw [← (hasSum_exp_trivialZetaZero_div hu).tsum_eq]
  apply hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioi isPreconnected_Ioi
    (g := fun n => integratedPole (trivialZetaZero n))
    (g' := fun n v => Complex.exp (trivialZetaZero n * (v : ℂ))/trivialZetaZero n) _ _ hh
    (summable_integratedPole re_trivial_nonpos summable_trivialZetaZero_inv_sq u) hh
  · intro n v hv
    exact hasDerivAt_integratedPole _ ((half_pos hu).trans hv)
  · intro n v hv
    change u/2 < v at hv
    rw [norm_div, exp_trivialZetaZero, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply (div_le_self (by positivity) (one_le_norm_trivialZetaZero n)).trans
    apply pow_le_pow_left₀ (Real.exp_pos _).le _ _
    exact Real.exp_le_exp.mpr (by linarith)

/-- The symmetric trivial-zero series has the same elementary value in the zero-width limit. -/
theorem tendsto_tsum_symmetric_trivialZetaZero {u : ℝ} (hu : 0 < u) :
    Tendsto (fun h => ∑' n, symmetricPole (trivialZetaZero n) u h) (𝓝[>] 0)
      (𝓝 ((Real.log (1-Real.exp (-2*u)) : ℂ)/2)) := by
  apply (tendsto_symmetricDifference_of_hasDerivAt (hasDerivAt_tsum_integrated_trivialZetaZero hu)).congr'
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hu).filter_mono nhdsWithin_le_nhds] with h hh hs
  change 0 < h at hh
  exact (tsum_symmetricPole_eq_difference re_trivial_nonpos summable_trivialZetaZero_inv_sq
    (by linarith) (by linarith)).symm

/-- The regularized nontrivial-zero series has a limit at every physical cutoff greater
than one. The pole, normalization and all trivial zeros are evaluated explicitly. -/
theorem exists_tendsto_symmetric_nontrivial_midpointPsi :
    ∃ Z : ZetaZeroEnumeration, ∀ {x : ℝ}, 1 < x →
      Tendsto (fun h => ∑' n, symmetricPole (Z.zero n) (Real.log x) h) (𝓝[>] 0)
        (𝓝 ((x : ℂ)-Complex.log (2*(Real.pi : ℂ))-(Real.log (1-(x^2)⁻¹) : ℂ)/2-(midpointPsi x : ℂ))) := by
  obtain ⟨Z, H⟩ := exists_symmetric_explicit_formula_midpointPsi
  refine ⟨Z, fun {x} hx => ?_⟩
  have hx₀ := zero_lt_one.trans hx
  have ht := tendsto_tsum_symmetric_trivialZetaZero (Real.log_pos hx)
  rw [show -2*Real.log x= -(Real.log x+Real.log x) by ring, Real.exp_neg, Real.exp_add,
    Real.exp_log hx₀, ← sq] at ht
  have h₁ := tendsto_symmetricPole 1 (Real.log_pos hx)
  rw [one_mul, div_one, Complex.ofReal_log hx₀.le, Complex.exp_log (Complex.ofReal_ne_zero.mpr hx₀.ne')] at h₁
  apply (((h₁.sub_const _).sub ht).sub_const _).congr'
  filter_upwards [H hx] with h he
  rw [he]
  ring

end AnalyticNumberTheory.PrimeDistribution
