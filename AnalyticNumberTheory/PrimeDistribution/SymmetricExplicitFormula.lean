import AnalyticNumberTheory.AnalyticTools.SymmetricPoleKernel
import AnalyticNumberTheory.DirichletSeries.SymmetricLogDifference
import AnalyticNumberTheory.PrimeDistribution.IntegratedExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.RiemannPrimeCounting

/-!
# A symmetric regularization of the explicit formula at jumps

Taking central differences of a logarithmic mean recovers the half-weight Chebyshev
function exactly at every sufficiently small width. Both zero series still converge
absolutely at each such width.
-/

noncomputable section

open Filter Finset
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Chebyshev's prime-power sum with half the von Mangoldt weight at a jump. -/
def midpointPsi (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, endpointWeight (1/2) x n * Λ n

/-- The real midpoint Chebyshev function is the arithmetic midpoint sum for von Mangoldt. -/
theorem midpointPartialSum_vonMangoldt (x : ℝ) :
    midpointPartialSum (fun n => (Λ n : ℂ)) x = (midpointPsi x : ℂ) := by
  unfold midpointPartialSum midpointPsi
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n _
  by_cases he : (n : ℝ) = x <;> simp [endpointWeight, he]

/-- At a positive integer the midpoint function is the mean of the adjacent inclusive
Chebyshev sums, even when the integer is itself a prime power. -/
theorem midpointPsi_nat_succ (n : ℕ) :
    midpointPsi (↑(n+1 : ℕ)) = (Chebyshev.psi (n : ℝ) + Chebyshev.psi (↑(n+1 : ℕ)))/2 := by
  simp only [midpointPsi, psi_eq_sum_Icc, Nat.floor_natCast, sum_Icc_succ_top (Nat.succ_pos n)]
  have h : (∑ k ∈ Icc 1 n, endpointWeight (1/2) (↑(n+1 : ℕ)) k * Λ k) = ∑ k ∈ Icc 1 n, Λ k := by
    refine sum_congr rfl fun k hk => ?_
    have he : (k : ℝ) ≠ ↑(n+1 : ℕ) := by exact_mod_cast (Nat.lt_succ_of_le (mem_Icc.mp hk).2).ne
    simp only [endpointWeight, if_neg he, one_mul]
  rw [h]
  simp [endpointWeight]
  ring

private theorem re_nontrivial_le (Z : ZetaZeroEnumeration) (n : ℕ) : (Z.zero n).re ≤ 1 :=
  (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le

private theorem re_trivial_le (n : ℕ) : (trivialZetaZero n).re ≤ 0 := by
  simp [trivialZetaZero, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Absolute convergence of the symmetric nontrivial-zero sum at a fixed width. -/
theorem summable_symmetric_nontrivial (Z : ZetaZeroEnumeration) {u h : ℝ} (hp : 0 ≤ u+h) (hm : 0 ≤ u-h) :
    Summable fun n => symmetricPole (Z.zero n) u h :=
  summable_symmetricPole (re_nontrivial_le Z) Z.summable_inv_sq hp hm

/-- Absolute convergence of the symmetric sum over the negative even zeros. -/
theorem summable_symmetric_trivial {u h : ℝ} (hp : 0 ≤ u+h) (hm : 0 ≤ u-h) :
    Summable fun n => symmetricPole (trivialZetaZero n) u h :=
  summable_symmetricPole re_trivial_le summable_trivialZetaZero_inv_sq hp hm

/-- The central difference of the integrated zero expression separates the pole at one,
the normalization constant and the two absolutely convergent zero series. -/
theorem symmetricDifference_integratedZetaZeroSum (Z : ZetaZeroEnumeration) {u h : ℝ}
    (hh : 0 < h) (hm : 0 ≤ u-h) :
    (integratedZetaZeroSum Z (u+h) - integratedZetaZeroSum Z (u-h))/(2*(h : ℂ)) =
      symmetricPole 1 u h - Complex.log (2*(Real.pi : ℂ)) -
      (∑' n, symmetricPole (Z.zero n) u h) - ∑' n, symmetricPole (trivialZetaZero n) u h := by
  have hp : 0 ≤ u+h := by linarith
  rw [tsum_symmetricPole_eq_difference (re_nontrivial_le Z) Z.summable_inv_sq hp hm,
    tsum_symmetricPole_eq_difference re_trivial_le summable_trivialZetaZero_inv_sq hp hm,
    symmetricPole_eq_difference _ hp hm, integratedZetaZeroSum, integratedZetaZeroSum]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hh.ne']
  ring

/-- At any physical cutoff greater than one, all sufficiently small positive logarithmic
widths give the exact midpoint Chebyshev value by two absolutely convergent zero series. -/
theorem exists_symmetric_explicit_formula_midpointPsi :
    ∃ Z : ZetaZeroEnumeration, ∀ {x : ℝ}, 1 < x → ∀ᶠ h : ℝ in 𝓝[>] 0,
      (midpointPsi x : ℂ) = symmetricPole 1 (Real.log x) h - Complex.log (2*(Real.pi : ℂ)) -
        (∑' n, symmetricPole (Z.zero n) (Real.log x) h) - ∑' n, symmetricPole (trivialZetaZero n) (Real.log x) h := by
  obtain ⟨Z, H⟩ := exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum
  refine ⟨Z, fun {x} hx => ?_⟩
  let u := Real.log x
  have hu : 0 < u := Real.log_pos hx
  have he : Real.exp u = x := Real.exp_log (zero_lt_one.trans hx)
  filter_upwards [eventually_symmetric_logWeightedSum (fun n => (Λ n : ℂ)) u, self_mem_nhdsWithin,
    (gt_mem_nhds hu).filter_mono nhdsWithin_le_nhds] with h hd hh hs
  change 0 < h at hh
  have hp : 0 ≤ u+h := by linarith
  have hm : 0 ≤ u-h := by linarith
  rw [H (Real.one_le_exp hp), H (Real.one_le_exp hm), Real.log_exp, Real.log_exp, he,
    midpointPartialSum_vonMangoldt] at hd
  exact hd.symm.trans (symmetricDifference_integratedZetaZeroSum Z hh hm)

end AnalyticNumberTheory.PrimeDistribution
