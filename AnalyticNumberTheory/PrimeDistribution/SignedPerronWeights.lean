import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaWeights
import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronContourBound

/-!
# The signed finite zero sum in Perron's formula

The continued weight has value `log x` at zero and is uniformly Lipschitz
in its positive real endpoint throughout the critical strip.
-/

noncomputable section
open Complex Finset Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Moving either real endpoint by a distance `d` changes a regularized
critical-strip zero weight by at most `d`. -/
theorem norm_perronDifferenceWeight_sub_le {x y : ℝ} (hx : 1≤x) (hy : 1≤y) {z : ℂ}
    (hl : 0<z.re) (hu : z.re≤1) :
    ‖perronDifferenceWeight x z-perronDifferenceWeight y z‖≤|x-y| := by
  have hzn : z≠0 := by intro h; simp [h] at hl
  have he := integral_cpow (a:=y) (b:=x) (r:=z-1) (Or.inl (by simp; linarith))
  rw [sub_add_cancel] at he
  have hid : perronDifferenceWeight x z-perronDifferenceWeight y z=
      ∫ v : ℝ in y..x,(v:ℂ)^(z-1) := by
    rw [perronDifferenceWeight_eq (by linarith) hzn,perronDifferenceWeight_eq (by linarith) hzn,he]
    ring
  rw [hid]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=y) (b:=x) (C:=1)
    (f:=fun v : ℝ => (v:ℂ)^(z-1)) (by
      intro v hv
      have hv' := (le_min hx hy).trans (show min x y≤v by
        rw [min_comm]; exact (Set.uIoc_subset_uIcc hv).1)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),Complex.sub_re,Complex.one_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hv' (by linarith))
  simpa using H

end AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

open AnalyticNumberTheory.DirichletLFunctions

/-- Signed sum over both signs of the zero ordinates, with analytic multiplicity. -/
def characterPerronZeroSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x T : ℝ) : ℂ :=
  ∑ z∈characterStripZeros χ T,(characterZeroMultiplicity χ z:ℂ)*perronDifferenceWeight x z

/-- The selected-height complex approximation before moving the endpoint and cutoff. -/
def PrimitiveSignedPerronContourBound : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ}, 2≤q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ {N : ℕ} {c A : ℝ}, 2≤N → 1<c → c≤3/2 → 4≤A →
    let h : ℝ := (N:ℝ)+1/2
    ∃ T ∈ Set.Icc (A+1/4) (A+3/4),
      ‖dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) h c T+characterPerronZeroSum χ h T‖≤C*
        ((1+1/(c-1))*(1+Real.log ((q:ℝ)*(A+3)))+
         Real.sqrt h*(1+Real.log ((q:ℝ)*(A+3)))^2+
         (h^c+1)/T*(1+Real.log ((q:ℝ)*(A+3)))^2)

end AnalyticNumberTheory.PrimeDistribution
