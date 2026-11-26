import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula
import AnalyticNumberTheory.RiemannZeta.CenteredPartialFractions

/-! # Both families of zeta zeros in rectangles extending past the negative even integers -/

noncomputable section

open Finset Set
open scoped Classical
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem trivial_re (n : ℕ) : (trivialZetaZero n).re = -2*((n : ℝ)+1) := by
  simp [trivialZetaZero, Complex.mul_re]

private theorem trivial_im (n : ℕ) : (trivialZetaZero n).im = 0 := by simp [trivialZetaZero, Complex.mul_im]

/-- The parametrization by positive even magnitude counts each trivial zero once. -/
theorem trivialZetaZero_injective : Function.Injective trivialZetaZero := by
  intro n m h
  have he := congrArg Complex.re h
  rw [trivial_re, trivial_re] at he
  exact_mod_cast (show (n : ℝ)=m by linarith)

/-- The multiplicity used in finite Perron sums is one at each trivial zero. -/
theorem zeroMultiplicity_trivialZetaZero (n : ℕ) : zeroMultiplicity (trivialZetaZero n) = 1 := by
  unfold zeroMultiplicity analyticOrderNatAt trivialZetaZero
  rw [analyticOrderAt_riemannZeta_neg_two_mul_nat_add_one]
  rfl

/-- The zeros inside the rectangular contour with left side `-(2N+1)` and horizontal
sides at `±T`, retaining the inclusive height cutoff. -/
def zetaRectangleZeros (N : ℕ) (T : ℝ) : Finset ℂ :=
  nontrivialZerosUpTo T ∪ (range N).image trivialZetaZero

/-- In a rectangle ending at real part two, the finite union of the two zero families
contains every zero of zeta and only the zeros there. -/
theorem mem_zetaRectangleZeros_iff {N : ℕ} {T : ℝ} (hT : 0 ≤ T) {z : ℂ} :
    z ∈ zetaRectangleZeros N T ↔
      riemannZeta z = 0 ∧ -(2*(N : ℝ)+1) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T := by
  rw [zetaRectangleZeros, Finset.mem_union]
  constructor
  · rintro (hn | ht)
    · obtain ⟨hz, h₀, h₁, him⟩ := mem_nontrivialZerosUpTo.mp hn
      exact ⟨hz, by linarith [Nat.cast_nonneg (α := ℝ) N], by linarith, him⟩
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
      have hn' : (n : ℝ)+1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
      rw [trivial_re, trivial_im, abs_zero]
      exact ⟨riemannZeta_trivialZetaZero n, by linarith, by linarith [Nat.cast_nonneg (α := ℝ) n], hT⟩
  · rintro ⟨hz, hlo, _, him⟩
    by_cases hp : 0 < z.re
    · have h₁ : z.re < 1 := lt_of_not_ge (fun he => _root_.riemannZeta_ne_zero_of_one_le_re he hz)
      exact Or.inl (mem_nontrivialZerosUpTo.mpr ⟨hz, hp, h₁, him⟩)
    · obtain ⟨n, he⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos_bridge (le_of_not_gt hp)).mp hz
      change z = trivialZetaZero n at he
      subst z
      rw [trivial_re] at hlo
      have hlt : (n : ℝ) < N := by linarith
      exact Or.inr (Finset.mem_image.mpr ⟨n, mem_range.mpr (by exact_mod_cast hlt), rfl⟩)

/-- A height missing the ordinates of the nontrivial zeros puts every listed zero strictly
inside the rectangle. Its vertical boundaries miss both zero families automatically. -/
theorem zetaRectangleZeros_mem_interior {N : ℕ} {T : ℝ} (hT : 0 < T)
    (hn : ∀ z ∈ nontrivialZerosUpTo T, |z.im| ≠ T) {z : ℂ} (hz : z ∈ zetaRectangleZeros N T) :
    z.re ∈ Ioo (-(2*(N : ℝ)+1)) 2 ∧ z.im ∈ Ioo (-T) T := by
  rcases Finset.mem_union.mp hz with h | h
  · obtain ⟨_, h₀, h₁, him⟩ := mem_nontrivialZerosUpTo.mp h
    exact ⟨⟨by linarith [Nat.cast_nonneg (α := ℝ) N], by linarith⟩, abs_lt.mp (lt_of_le_of_ne him (hn z h))⟩
  · obtain ⟨n, hm, rfl⟩ := Finset.mem_image.mp h
    have hle : (n : ℝ)+1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hm)
    rw [trivial_re, trivial_im]
    exact ⟨⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) n]⟩, neg_lt_zero.mpr hT, hT⟩

/-- Summing any complex weight with analytic multiplicity separates the critical strip
and the finite list of negative even zeros without overlap. -/
theorem sum_zetaRectangleZeros (N : ℕ) (T : ℝ) (w : ℂ → ℂ) :
    (∑ z ∈ zetaRectangleZeros N T, (zeroMultiplicity z : ℂ)*w z) =
      (∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*w z) + ∑ n ∈ range N, w (trivialZetaZero n) := by
  have hd : Disjoint (nontrivialZerosUpTo T) ((range N).image trivialZetaZero) := by
    rw [Finset.disjoint_left]
    intro z hz hm
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hm
    have hh := (mem_nontrivialZerosUpTo.mp hz).2.1
    rw [trivial_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [zetaRectangleZeros, sum_union hd, sum_image (fun _ _ _ _ he => trivialZetaZero_injective he)]
  simp [zeroMultiplicity_trivialZetaZero]

end AnalyticNumberTheory.PrimeDistribution
