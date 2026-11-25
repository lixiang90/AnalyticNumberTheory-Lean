import AnalyticNumberTheory.PrimeDistribution.PrimitiveConductorBlockSums
import AnalyticNumberTheory.PrimeDistribution.TwistedPerron

/-! # A half-integer Perron contour for a primitive character -/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open scoped Classical ArithmeticFunction.vonMangoldt
namespace AnalyticNumberTheory.PrimeDistribution

/-- Half-integer contour estimate at a height selected inside a unit interval.
The zero sum counts analytic orders of all zeros in the open critical strip. -/
def PrimitivePerronContourBound : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ}, 2≤q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ {N : ℕ} {c A : ℝ}, 2≤N → 1<c → c≤3/2 → 4≤A →
    let h : ℝ := (N:ℝ)+1/2
    ∃ T ∈ Set.Icc (A+1/4) (A+3/4),
      ‖dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) h c T‖ ≤ C*
        ((1+1/(c-1))*(1+Real.log ((q:ℝ)*(A+3)))+
         Real.sqrt h*(1+Real.log ((q:ℝ)*(A+3)))^2+
         (h^c+1)/T*(1+Real.log ((q:ℝ)*(A+3)))^2+
         characterZeroWeight χ T (fun z=>h^z.re/(1+|z.im|)))

end AnalyticNumberTheory.PrimeDistribution
