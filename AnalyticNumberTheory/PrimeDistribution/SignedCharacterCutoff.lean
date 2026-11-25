import AnalyticNumberTheory.PrimeDistribution.SignedCharacterHeight
import AnalyticNumberTheory.PrimeDistribution.SmallHeightExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.PerronCutoffBounds

/-! # A complex explicit formula at a fixed square-root height

The cutoff for the zeros is independent of the arithmetic endpoint.
The regularized weight includes real zeros without dividing by their
distance from the origin in an error term.
-/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.DirichletSeries
open scoped Classical ArithmeticFunction.vonMangoldt
namespace AnalyticNumberTheory.PrimeDistribution

/-- Uniform signed explicit formula for primitive characters at all positive
heights R ≤ sqrt x, including heights below the first nonreal zero. -/
theorem primitive_signed_explicit_height_of_perron (H : PrimitiveSignedPerronContourBound) :
    ∃ C : ℝ, 0<C ∧ ∀ {x y R : ℝ} {q : ℕ}, 0<R → R^2≤x → 1≤y → y≤x → 2≤q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ‖psiChar y χ+characterPerronZeroSum χ y R‖ ≤ C*(x/R)*(1+Real.log ((q:ℝ)*x))^2 := by
  obtain ⟨A,hA,large⟩ := primitive_signed_explicit_at_height_of_perron H
  obtain ⟨B,hB,small⟩ := nonprincipal_psi_signed_explicit_small_height
  refine ⟨max A B,hA.trans_le (le_max_left ..),?_⟩
  intro x y R q hR hRx hy hyx hq χ hp
  have hx₀ := zero_lt_one.trans_le (hy.trans hyx)
  have hM := (div_pos hx₀ hR).le
  by_cases h : 8≤R
  · exact (large h hRx hy hyx hq χ hp).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left ..) hM) (sq_nonneg _))
  · letI : NeZero q := ⟨by omega⟩
    have hχ : χ≠1 := by
      intro he
      have ha : χ.conductor=q := hp
      rw [he,DirichletCharacter.conductor_one] at ha
      omega
    exact (small hχ hy hyx hR (le_of_not_ge h)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) hM) (sq_nonneg _))

/-- Replace the selected Perron height by √x and the half-integer arithmetic
endpoint by any real y in [1,x], retaining the signed complex zero sum. -/
theorem primitive_signed_explicit_of_perron (H : PrimitiveSignedPerronContourBound) :
    ∃ C : ℝ,0<C ∧ ∀{x y : ℝ}{q : ℕ},4≤x → 1≤y → y≤x → 2≤q →
      ∀χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ‖psiChar y χ+characterPerronZeroSum χ y (Real.sqrt x)‖ ≤
          C*Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2 := by
  obtain ⟨C,hC,HC⟩ := primitive_signed_explicit_height_of_perron H
  refine ⟨C,hC,?_⟩
  intro x y q hx hy hyx hq χ hp
  have hx₀ : 0<x := by linarith
  have hR := Real.sqrt_pos.mpr hx₀
  have hsq := Real.sq_sqrt hx₀.le
  have hdiv : x/Real.sqrt x=Real.sqrt x := (div_eq_iff hR.ne').mpr (by rw [← sq,hsq])
  simpa only [hdiv] using HC hR hsq.le hy hyx hq χ hp

end AnalyticNumberTheory.PrimeDistribution
