import AnalyticNumberTheory.PrimeDistribution.CharacterTruncatedExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.DensityMaximalProgressions
import AnalyticNumberTheory.PrimeDistribution.MaximalChebyshevTransfer

/-! # Bombieri–Vinogradov by the zero-density method

The primitive-character explicit formula supplies the pointwise input.
Ingham density, summed by ordinate and conductor, controls its zero terms.
-/
noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- The dyadic mean of the individual maximal twisted Chebyshev sums,
obtained by summing the truncated explicit formula over primitive conductors. -/
theorem primitive_dyadic_mean_by_zero_density :
    ∃ C : ℝ,0<C ∧ ∀{Q R : ℕ}{x : ℝ},1≤Q → R≤2*Q → 4≤x → (Q:ℝ)≤Real.sqrt x →
      (∑q∈Ioc Q R,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        maximalPsiCharNorm x χ) ≤
      C*(Real.sqrt x*Q*(Real.log x)^11+x*(Q:ℝ)^(-(1/3:ℝ))*(Real.log x)^10) :=
  primitive_dyadic_mean_of_explicit_bound primitivePsiExplicitBound

/-- The zero-density proof of the primitive mean with a separate endpoint
for each character. The modulus cutoff exponent is explicit. -/
theorem primitive_maximal_mean_by_zero_density (A : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},2≤x → 1≤Real.log x → 1≤Q →
      Q≤x^(1/2:ℝ)/(Real.log x)^(⌈A⌉₊+11) →
      (∑q∈Icc 2 ⌊Q⌋₊,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        maximalPsiCharNorm x χ)≤C*x/(Real.log x)^A :=
  primitive_density_maximal_log_saving primitivePsiExplicitBound A

/-- The Bombieri–Vinogradov theorem from the truncated explicit formula and
the density of the critical-strip zeros of Dirichlet L-functions. -/
theorem bombieriVinogradov_by_zero_density : BombieriVinogradovStatement :=
  bombieriVinogradov_of_density_explicit primitivePsiExplicitBound

/-- Maximal Bombieri–Vinogradov with the cutoff exponent k+12. Each
modulus may independently select both its endpoint and its reduced residue. -/
theorem bombieriVinogradov_maximal_by_zero_density (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},4≤x → 1≤Q →
      Q≤Real.sqrt x/(Real.log x)^(k+12) →
      (∑q∈Icc 1 ⌊Q⌋₊,maximalPsiAPError x q)≤C*x/(Real.log x)^k :=
  bombieriVinogradov_maximal_of_density_explicit primitivePsiExplicitBound k

/-- The first Chebyshev function has the same explicit maximal level. -/
theorem bombieriVinogradov_maximal_theta_by_zero_density (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},4≤x → 1≤Q → Q≤Real.sqrt x/(Real.log x)^(k+12) →
      (∑q∈Icc 1 ⌊Q⌋₊,maximalThetaAPError x q)≤C*x/(Real.log x)^k :=
  maximal_mean_transfer_at_level (by omega) (by positivity)
    (fun {x} hx {q} hq => maximalThetaAPError_le_maximalPsi_add_sqrt hx hq)
    (bombieriVinogradov_maximal_by_zero_density k)

/-- Maximal prime counting in progressions with logarithmic integral main
term, with the same saving and explicit level as the two Chebyshev functions. -/
theorem bombieriVinogradov_maximal_pi_by_zero_density (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},4≤x → 1≤Q → Q≤Real.sqrt x/(Real.log x)^(k+12) →
      (∑q∈Icc 1 ⌊Q⌋₊,maximalPiAPError x q)≤C*x/(Real.log x)^k :=
  maximal_mean_transfer_at_level (by omega) (by positivity)
    (fun {x} hx {q} hq => maximalPiAPError_le_maximalPsi_add_sqrt hx hq)
    (bombieriVinogradov_maximal_by_zero_density k)

end AnalyticNumberTheory.PrimeDistribution
