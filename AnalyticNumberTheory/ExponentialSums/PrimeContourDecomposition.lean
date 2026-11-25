import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeSums
import AnalyticNumberTheory.ExponentialSums.VaughanIdentity
import AnalyticNumberTheory.DirichletLFunctions.CriticalLogPerron
import AnalyticNumberTheory.DirichletLFunctions.IntervalPerronProducts
import AnalyticNumberTheory.DirichletSeries.LogPerronLinearity

/-! # Two contours for a logarithmically smoothed prime character sum

The first part contains only L, its derivative and short polynomials.
The second is a product of two finite tails. The positive-part Perron
weight enforces the original hyperbola exactly, even at integer cutoffs.
-/

noncomputable section
open Complex Real Finset MeasureTheory
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.ExponentialSums

/-- The part of the prime sum represented on the critical line. Its three
numerators are the short prime polynomial, the Möbius polynomial times −L′,
and the short Dirichlet convolution times L with a minus sign. -/
def primeContourRegularPart {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (U V : ℕ) (s : ℂ) : ℂ :=
  intervalCharacterPolynomial χ (fun n => (Λ n : ℂ)) 0 V s +
    intervalCharacterPolynomial χ (fun n => (μ n : ℂ)) 0 U s * (-deriv χ.LFunction s) -
    intervalCharacterPolynomial χ (fun n => (vaughanTypeICoeff U V n : ℂ)) 0 (U*V) s * χ.LFunction s

/-- The finite tail on the line Re s = 1. Its two factors have lower cutoffs
U and V, and terms past X in their product vanish after logarithmic inversion. -/
def primeContourTailPart {q : ℕ} (χ : DirichletCharacter ℂ q) (U V X : ℕ) (s : ℂ) : ℂ :=
  intervalCharacterPolynomial χ (fun n => (vaughanTypeIICoeff U n : ℂ)) U (X/V) s *
    intervalCharacterPolynomial χ (fun n => (Λ n : ℂ)) V X s

set_option maxHeartbeats 600000 in
/-- Exact two-line integral decomposition for every nonprincipal character
and every positive real cutoff. All vertical integrals converge absolutely. -/
theorem logSmoothedPsiChar_two_contours {q : ℕ} [NeZero q] (hq : 2≤q)
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) {U V : ℕ} (hV : 1≤V) {x : ℝ} (hx : 0<x) :
    let E := primeContourRegularPart χ U V
    let B := primeContourTailPart χ U V ⌊x⌋₊
    Integrable (logPerronTrace E (1/2) x) ∧ Integrable (logPerronTrace B 1 x) ∧
      logSmoothedPsiChar χ x = logPerronIntegral E (1/2) x + logPerronIntegral B 1 x := by
  intro E B
  have hinv {y : ℝ} (hy : 0<y) := nonprincipal_critical_logPerron_inversion hq hχ hy
  have traces (y : ℝ) := integrable_nonprincipal_critical_logPerron hq hχ y
  have hlog : LSeries.logMul (fun n : ℕ => χ n) = fun n : ℕ => (Real.log n : ℂ)*χ n := by
    funext n
    rw [LSeries.logMul, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have A := logPerron_intervalCharacterPolynomial χ (fun n => (Λ n : ℂ)) 0 V (by norm_num : (0 : ℝ)<1/2) hx
  have M := logPerron_intervalCharacter_mul χ (fun n => (μ n : ℂ)) (fun n => (Real.log n : ℂ)) 0 U
    (fun s => -deriv χ.LFunction s) hx (fun y _ => (traces y).2) (fun _ hy => hlog ▸ (hinv hy).2.symm)
  have I₁ := logPerron_intervalCharacter_mul χ (fun n => (vaughanTypeICoeff U V n : ℂ)) (fun _ => 1)
    0 (U*V) χ.LFunction hx (fun y _ => (traces y).1) (fun _ hy => by simpa only [one_mul] using (hinv hy).1.symm)
  have II := logPerron_intervalCharacter_product χ (fun n => (vaughanTypeIICoeff U n : ℂ))
    (fun n => (Λ n : ℂ)) U (⌊x⌋₊/V) V ⌊x⌋₊ (by norm_num : (0 : ℝ)<1) hx
  have AM := logPerronIntegral_add A.1 M.1
  have reg := logPerronIntegral_sub AM.1 I₁.1
  refine ⟨reg.1,II.1,?_⟩
  rw [show logPerronIntegral E (1/2) x = _ from reg.2,
    show logPerronIntegral B 1 x = _ from II.2, AM.2, A.2, M.2, I₁.2]
  have H := vaughan_identity_sum x (U := U) hV (fun n => χ n*(Real.log (x/n) : ℂ))
  simpa only [logSmoothedPsiChar, logWeightedSum, ← Icc_add_one_left_eq_Ioc (a := 0), zero_add,
    min_eq_right (Nat.div_le_self _ _), min_comm V ⌊x⌋₊, Nat.cast_mul, one_mul, mul_comm, mul_left_comm, mul_assoc] using H

end AnalyticNumberTheory.ExponentialSums
