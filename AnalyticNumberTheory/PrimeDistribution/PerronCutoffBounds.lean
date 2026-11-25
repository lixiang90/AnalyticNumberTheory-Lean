import AnalyticNumberTheory.PrimeDistribution.PerronHeightParameters

/-! # Half-integer Perron parameters for a square-root truncation -/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletSeries
open scoped Classical ArithmeticFunction.vonMangoldt
namespace AnalyticNumberTheory.PrimeDistribution

/-- For x≥64 the abscissa and half-integer endpoint admit a contour with
height within one unit of √x. Both the truncation error and the elementary
contour terms are bounded by √x (1 + log(qx))². -/
theorem perron_halfInteger_sqrt_parameters {x y : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hx' : 64≤x) (hy' : 2≤y) (hyx : y≤x) (hq : 2≤q) :
    let N := ⌊y⌋₊
    let h := (N:ℝ)+1/2
    let R := Real.sqrt x
    let c := 1+1/Real.log (2*x)
    let A := R-1
    let L := 1+Real.log ((q:ℝ)*x)
    let J := 1+Real.log ((q:ℝ)*(A+3))
    2≤N ∧ 1<c ∧ c≤3/2 ∧ 4≤A ∧ ∀ {T : ℝ}, T∈Set.Icc (A+1/4) (A+3/4) →
      ‖dirichletContourIntegral (fun n : ℕ=>χ n*(Λ n:ℂ)) h c T-psiChar y χ‖≤400*(R*L^2) ∧
      (1+1/(c-1))*J+Real.sqrt h*J^2+(h^c+1)/T*J^2≤16*(R*L^2) := by
  have hx₀ : 0<x := by linarith
  have hR : 8≤Real.sqrt x := (Real.le_sqrt (by norm_num) hx₀.le).mpr (by linarith only [hx'])
  have hsq := Real.sq_sqrt hx₀.le
  have hdiv : x/Real.sqrt x=Real.sqrt x := (div_eq_iff (Real.sqrt_pos.mpr hx₀).ne').mpr
    (by rw [← sq,hsq])
  have H := perron_halfInteger_height_parameters χ hR hsq.le hy' hyx hq
  simpa only [hdiv] using H

end AnalyticNumberTheory.PrimeDistribution
