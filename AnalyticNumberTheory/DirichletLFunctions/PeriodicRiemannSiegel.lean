import AnalyticNumberTheory.DirichletLFunctions.PrimitiveApproximateFunctionalEquation
import AnalyticNumberTheory.RiemannZeta.HurwitzRiemannSiegel

/-!
# The periodic Riemann–Siegel equation with its first correction

Each residue supplies one explicit shifted Mordell coefficient. Summing the
individual errors costs the square root of the period on the critical line.
For primitive characters the finite Fourier transform reduces to a single
conjugate-character polynomial.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Explicit first correction for an arbitrary bounded periodic function,
with absolute error constant independent of its period. -/
theorem periodicLFunction_first_correction : ∃ C : ℝ,0<C ∧
    ∀ {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ), (∀ j, ‖Φ j‖≤1) → ∀ {t : ℝ},8*Real.pi≤t →
    let x := Real.sqrt (t/(2*Real.pi))
    let s := (1/2:ℂ)+(t:ℂ)*I
    ‖ZMod.LFunction Φ s-dirichletPoly (fun n : ℕ => Φ n) ⌊(q:ℝ)*x⌋₊ s-periodicDualSum Φ x s-
      periodicShiftCorrection Φ s (fun a => hurwitzFirstCorrection a x s)‖≤
      Real.sqrt q*(C*t^(-(3/4:ℝ))) := by
  obtain ⟨C,hC,h⟩ := hurwitzZeta_first_correction_height
  refine ⟨C,hC,?_⟩
  intro q _ Φ hΦ t ht x s
  have ht' : 0<t := (by positivity : 0<8*Real.pi).trans_le ht
  have hπ : 0<2*Real.pi := by positivity
  have hx : 1≤x := by
    have h₄ : 4≤t/(2*Real.pi) := (le_div_iff₀ hπ).mpr (by linarith)
    nlinarith [Real.sq_sqrt (show 0≤t/(2*Real.pi) by positivity),Real.sqrt_nonneg (t/(2*Real.pi))]
  have H := periodicLFunction_corrected_estimate_of_hurwitz Φ hΦ hx (fun a => hurwitzFirstCorrection a x s)
    (fun a ha => h ha ht)
  have hσ : 1-s.re=1/2 := by simp [s];norm_num
  change _≤(q:ℝ)^(1-s.re)*(C*t^(-(3/4:ℝ))) at H
  rwa [hσ,←Real.sqrt_eq_rpow] at H

/-- The first corrected primitive character equation at the balanced Hurwitz
cutoff. Its dual term has the conjugate character and the exact Gauss factor. -/
theorem primitiveLFunction_first_correction : ∃ C : ℝ,0<C ∧
    ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive → ∀ {t : ℝ},8*Real.pi≤t →
    let x := Real.sqrt (t/(2*Real.pi))
    let s := (1/2:ℂ)+(t:ℂ)*I
    ‖χ.LFunction s-dirichletPoly (fun n : ℕ => χ n) ⌊(q:ℝ)*x⌋₊ s-
      primitiveDualGamma χ s*(∑ m∈range ⌊x⌋₊,conj (χ ((m+1:ℕ):ZMod q))*((m:ℂ)+1)^(s-1))-
      periodicShiftCorrection χ s (fun a => hurwitzFirstCorrection a x s)‖≤
      Real.sqrt q*(C*t^(-(3/4:ℝ))) := by
  obtain ⟨C,hC,h⟩ := periodicLFunction_first_correction
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ t ht x s
  rw [←periodicDualSum_primitive hχ]
  exact h χ χ.norm_le_one ht

end AnalyticNumberTheory.DirichletLFunctions
