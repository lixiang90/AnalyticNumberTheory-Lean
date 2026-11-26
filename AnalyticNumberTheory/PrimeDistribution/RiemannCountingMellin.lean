import AnalyticNumberTheory.DirichletSeries.SharpPerron
import AnalyticNumberTheory.PrimeDistribution.RiemannPrimeCounting
import AnalyticNumberTheory.RiemannZeta.HadamardProduct
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Mellin inversion of Riemann's prime-power count

The Euler-product logarithm of zeta is the Mellin transform of the inclusive prime-power
count. Symmetric inversion along any line to the right of one recovers the half-weight count.
-/

noncomputable section

open Finset Filter Asymptotics MeasureTheory
open Complex (I)
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem logZetaCoeff_eq (n : ℕ) : logZetaCoeff n = ((Λ n / Real.log n : ℝ) : ℂ) := by
  have hχ : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))
  simp [logZetaCoeff, hχ]

private theorem riemannPrimeCounting_one_eq_partial (t : ℝ) :
    (riemannPrimeCounting 1 t : ℂ) = ∑ n ∈ Icc 1 ⌊t⌋₊, logZetaCoeff n := by
  rw [riemannPrimeCounting_one, ← Finset.Icc_add_one_left_eq_Ioc, zero_add, Complex.ofReal_sum]
  exact sum_congr rfl fun n _ => (logZetaCoeff_eq n).symm

/-- On `Re s > 1`, the Mellin transform of the inclusive prime-power count gives the
holomorphic Euler-product logarithm: `log ζ(s) = s ∫₁^∞ J(t)t^(-s-1) dt`. -/
theorem logZeta_eq_mellin_riemannPrimeCounting {s : ℂ} (hs : 1 < s.re) :
    logZeta s = s * ∫ t in Set.Ioi (1 : ℝ),
      (riemannPrimeCounting 1 t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun N : ℕ => ∑ n ∈ Icc 1 N, ‖logZetaCoeff n‖) =O[atTop]
      fun N : ℕ => (N : ℝ) ^ (1 : ℝ) := by
    apply isBigO_of_le
    intro N
    simp only [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
      abs_of_nonneg (sum_nonneg fun n _ => norm_nonneg _)]
    calc
      _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := sum_le_sum fun n _ => norm_logZetaCoeff_le_one n
      _ = N := by simp
  simp_rw [riemannPrimeCounting_one_eq_partial]
  rw [logZeta_eq_LSeries hs]
  exact LSeries_eq_mul_integral' _ zero_le_one hs hO

/-- The half-weight jump convention for prime powers agrees with the midpoint convention
in sharp Perron inversion. -/
theorem midpointPartialSum_logZetaCoeff (x : ℝ) :
    midpointPartialSum logZetaCoeff x = (riemannPrimeCounting (1/2) x : ℂ) := by
  rw [midpointPartialSum, riemannPrimeCounting, ← Finset.Icc_add_one_left_eq_Ioc,
    zero_add, Complex.ofReal_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : (n : ℝ) = x <;> simp [endpointWeight, hn, logZetaCoeff_eq]

/-- Symmetric vertical Perron integral of the Euler-product logarithm of zeta at `x`. -/
def logZetaPerronIntegral (x c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) * ∫ t in (-T)..T,
    logZeta ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

private theorem logZetaPerronIntegral_eq (x T : ℝ) {c : ℝ} (hc : 1 < c) :
    logZetaPerronIntegral x c T = dirichletContourIntegral logZetaCoeff x c T := by
  unfold logZetaPerronIntegral dirichletContourIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [logZeta_eq_LSeries (s := (c : ℂ) + (t : ℂ) * I) (by simpa using hc)]

/-- At every positive cutoff the error of truncating the `log ζ` inversion integral is
`O(1/T)` for fixed `x` and fixed `c > 1`, with an exact half-weight at prime powers. -/
theorem norm_logZetaPerronIntegral_sub_riemannPrimeCounting_le {x c : ℝ}
    (hx : 0 < x) (hc : 1 < c) :
    ∃ C : ℝ, ∀ T : ℝ, 0 < T →
      ‖logZetaPerronIntegral x c T - (riemannPrimeCounting (1/2) x : ℂ)‖ ≤ C / T := by
  simp_rw [logZetaPerronIntegral_eq _ _ hc, ← midpointPartialSum_logZetaCoeff]
  exact norm_dirichletContourIntegral_sub_midpointPartialSum_le hx (zero_lt_one.trans hc)
    (LSeriesSummable_of_bounded_of_one_lt_real (fun n _ => norm_logZetaCoeff_le_one n) hc)

/-- Riemann's half-weight prime-power count is the limit of symmetric vertical integrals
of `log ζ(s)x^s/s` on every line `Re s = c > 1`. -/
theorem tendsto_logZetaPerronIntegral_riemannPrimeCounting {x c : ℝ}
    (hx : 0 < x) (hc : 1 < c) :
    Tendsto (logZetaPerronIntegral x c) atTop (𝓝 (riemannPrimeCounting (1/2) x : ℂ)) := by
  rw [show logZetaPerronIntegral x c = dirichletContourIntegral logZetaCoeff x c from
    funext fun T => logZetaPerronIntegral_eq x T hc, ← midpointPartialSum_logZetaCoeff]
  exact tendsto_dirichletContourIntegral_midpointPartialSum hx (zero_lt_one.trans hc)
    (LSeriesSummable_of_bounded_of_one_lt_real (fun n _ => norm_logZetaCoeff_le_one n) hc)

end AnalyticNumberTheory.PrimeDistribution
