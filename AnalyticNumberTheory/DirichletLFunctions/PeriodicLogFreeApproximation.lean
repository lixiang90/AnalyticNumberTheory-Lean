import AnalyticNumberTheory.DirichletLFunctions.PrimitiveApproximateFunctionalEquation
import AnalyticNumberTheory.RiemannZeta.HurwitzLogFreeApproximation

/-!
# Log-free sharp approximation of periodic L-functions

The finite Fourier transform transfers the shift-uniform Hurwitz
estimate to every bounded periodic coefficient sequence. In conductor q,
the basic period factor is q^{1−σ}.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Uniform log-free periodic approximate functional equation on the closed strip. -/
theorem periodicLFunction_logFree_sharp_afe {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (hΦ : ∀ j, ‖Φ j‖≤1)
    {x y : ℝ} (hx : 2≤x) (hy : x≤y) {s : ℂ} (hσ : s.re∈Icc (0:ℝ) 1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖ZMod.LFunction Φ s-dirichletPoly (fun n : ℕ => Φ n) ⌊(q:ℝ)*x⌋₊ s-periodicDualSum Φ y s‖ ≤
      (q:ℝ)^(1-s.re)*(604*x^(-s.re)) :=
  periodicLFunction_estimate_of_hurwitz Φ hΦ (by linarith) (fun _ ha =>
    hurwitzZeta_logFree_sharp_afe ha hx hy hσ hxy)

/-- Primitive-character form, with its single conjugate-character reciprocal polynomial. -/
theorem primitiveLFunction_logFree_sharp_afe {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {x y : ℝ} (hx : 2≤x) (hy : x≤y) {s : ℂ} (hσ : s.re∈Icc (0:ℝ) 1)
    (hxy : |s.im|=2*Real.pi*x*y) :
    ‖χ.LFunction s-dirichletPoly (fun n : ℕ => χ n) ⌊(q:ℝ)*x⌋₊ s-
      primitiveDualGamma χ s*(∑ m∈range ⌊y⌋₊,conj (χ ((m+1:ℕ):ZMod q))*((m:ℂ)+1)^(s-1))‖ ≤
      (q:ℝ)^(1-s.re)*(604*x^(-s.re)) := by
  rw [←periodicDualSum_primitive hχ]
  exact periodicLFunction_logFree_sharp_afe χ χ.norm_le_one hx hy hσ hxy

end AnalyticNumberTheory.DirichletLFunctions
