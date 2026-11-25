import AnalyticNumberTheory.ExponentialSums.PrimeContourPolynomialMeans
import AnalyticNumberTheory.ExponentialSums.PrimeContourDecomposition
import AnalyticNumberTheory.DirichletSeries.LogPerronFamilyBounds

/-! # Integrating the long bilinear term in the prime contour decomposition -/

noncomputable section
open Complex Real Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.ExponentialSums

/-- Absolute mean of the right-hand integrals over all characters. On the
line Re s=1 the normalized Perron mass is x/2, and Cauchy–Schwarz retains
the separate lower cutoffs of the two Dirichlet polynomials. -/
theorem primeContourTail_integral_mean {q U V : ℕ} [NeZero q] (hU : 1≤U) (hV : 1≤V)
    {x : ℝ} (hx : 1≤x) :
    let X := ⌊x⌋₊
    let Y := X/V
    let B := ((q : ℝ)/U+(1+Real.log Y))*(1+Real.log Y)^4
    let A := ((q : ℝ)/V+(1+Real.log X))*(Real.log X*(Real.log X+Real.log 4+8))
    (∑ χ : DirichletCharacter ℂ q, ‖logPerronIntegral (primeContourTailPart χ U V X) 1 x‖) ≤
      x*Real.sqrt B*Real.sqrt A/2 := by
  intro X Y B A
  have hx₀ := zero_lt_one.trans_le hx
  have hX : 1≤X := (Nat.one_le_floor_iff x).mpr hx
  let P (χ : DirichletCharacter ℂ q) := intervalCharacterPolynomial χ (fun n => (vaughanTypeIICoeff U n : ℂ)) U Y
  let Q (χ : DirichletCharacter ℂ q) := intervalCharacterPolynomial χ (fun n => (Λ n : ℂ)) V X
  have hi (χ : DirichletCharacter ℂ q) : Integrable (logPerronTrace (primeContourTailPart χ U V X) 1 x) :=
    (logPerron_intervalCharacter_product χ _ _ U Y V X (by norm_num : (0 : ℝ)<1) hx₀).1
  have h (t : ℝ) : (∑ χ : DirichletCharacter ℂ q, ‖primeContourTailPart χ U V X ((1 : ℂ)+t*I)‖) ≤ Real.sqrt B*Real.sqrt A := by
    let s := (1 : ℂ)+t*I
    have hs : s.re=1 := by simp [s]
    have hb := typeII_tail_polynomial_energy (q := q) hU Y hs
    have ha := vonMangoldt_tail_polynomial_energy (q := q) hV hX hs
    change (∑ χ, ‖P χ s * Q χ s‖) ≤ _
    simp_rw [norm_mul]
    exact (Real.sum_mul_le_sqrt_mul_sqrt univ (fun χ => ‖P χ s‖) (fun χ => ‖Q χ s‖)).trans
      (mul_le_mul (Real.sqrt_le_sqrt hb) (Real.sqrt_le_sqrt ha) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have H := sum_norm_logPerronIntegral_le_uniform univ (fun χ => primeContourTailPart χ U V X)
    (by norm_num : (0 : ℝ)<1) x (fun χ _ => hi χ) (fun t => by simpa only [Complex.ofReal_one] using h t)
  simpa only [one_mul, mul_one, Real.exp_log hx₀, mul_assoc] using H

end AnalyticNumberTheory.ExponentialSums
