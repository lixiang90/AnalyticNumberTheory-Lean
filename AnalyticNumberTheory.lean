import AnalyticNumberTheory.AnalyticTools.Transforms
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin
import AnalyticNumberTheory.AnalyticTools.Summation.Poisson
import AnalyticNumberTheory.AnalyticTools.Gamma.InfiniteProducts
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HadamardThreeCircles
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PhragmenLindelof
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.Order
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.HadamardFactorization
import AnalyticNumberTheory.DirichletSeries.Convergence
import AnalyticNumberTheory.DirichletSeries.Uniqueness
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.DirichletSeries.EulerProduct
import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-!
# AnalyticNumberTheory

A thematic, completely formalized Lean 4 + Mathlib (`v4.36.0`) library for analytic number theory.
-/

namespace AnalyticNumberTheory

/-- Alias for Riemann's zeta function `ζ(s)` from Mathlib. -/
noncomputable def zetaFn (s : ℂ) : ℂ := riemannZeta s

end AnalyticNumberTheory
