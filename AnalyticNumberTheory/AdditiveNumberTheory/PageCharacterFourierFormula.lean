import AnalyticNumberTheory.AdditiveNumberTheory.FourierPartialSummation
import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterExpansion
import AnalyticNumberTheory.PrimeDistribution.PageExceptionalExplicitFormula

/-! # Fourier main terms of small-modulus character sums -/

noncomputable section

open Finset AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DirichletLFunctions
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- An arithmetic main term of signed size v for a character produces the
same multiple of the Fourier integral at every real frequency. -/
theorem characterPrimeSum_sub_powerWeight {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x E β : ℝ} (hx : 1 ≤ x) (hβ : 0 < β) (v : ℂ)
    (hP : ∀ t ∈ Set.Icc 1 x, ‖psiChar t χ - v*(((t^β-1)/β : ℝ) : ℂ)‖ ≤ E) (z : ℝ) :
    ‖characterPrimeSum χ ⌊x⌋₊ z - v*powerWeightFourierIntegral β x z‖ ≤
      E*(1+2*Real.pi*x*|z|) :=
  norm_expSum_sub_powerWeightFourierIntegral hx hβ (fun n => χ n*(Λ n : ℂ)) v hP z

/-- Throughout the exponential small-modulus range, one primitive inducing
pair covers all possible exceptional Fourier main terms. For a fixed
character the same zero works at every endpoint and every real frequency. -/
theorem page_characterPrimeSum_explicit :
    ∃ κ C : ℝ, 0 < κ ∧ κ ≤ 1/4 ∧ 0 < C ∧ ∀ {x : ℝ}, 2 ≤ x →
      ∃ e₀ : Σ m : ℕ, DirichletCharacter ℂ m,
        ∀ {q : ℕ} [NeZero q], (q : ℝ) ≤ Real.exp (κ*Real.sqrt (Real.log x)) →
        ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
          (∀ {y : ℝ}, 1 ≤ y → y ≤ x → ∀ z : ℝ, ‖characterPrimeSum χ ⌊y⌋₊ z‖ ≤
            C*x*Real.exp (-(κ/2)*Real.sqrt (Real.log x))*(1+2*Real.pi*y*|z|)) ∨
          ((⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) = e₀ ∧
            ∃ β : ℝ, 1/2 ≤ β ∧ β < 1 ∧ IsReal χ ∧ χ.LFunction (β : ℂ) = 0 ∧
              characterZeroMultiplicity χ (β : ℂ) = 1 ∧
              ∀ {y : ℝ}, 1 ≤ y → y ≤ x → ∀ z : ℝ,
                ‖characterPrimeSum χ ⌊y⌋₊ z + powerWeightFourierIntegral β y z‖ ≤
                  C*x*Real.exp (-(κ/2)*Real.sqrt (Real.log x))*(1+2*Real.pi*y*|z|)) := by
  obtain ⟨κ, C, hκ, hκ4, hC, H⟩ := page_psi_exceptional_explicit
  refine ⟨κ, C, hκ, hκ4, hC, ?_⟩
  intro x hx
  obtain ⟨e₀, he⟩ := H hx
  refine ⟨e₀, ?_⟩
  intro q _ hq χ hχ
  rcases he hq hχ with h | ⟨hp, β, hβ, hβ₁, hr, hz, hm, h⟩
  · left
    intro y hy hyx z
    simpa only [zero_mul, sub_zero] using characterPrimeSum_sub_powerWeight χ hy
      (β:=1) zero_lt_one 0 (fun t ht => by simpa only [zero_mul, sub_zero] using h ht.1 (ht.2.trans hyx)) z
  · refine Or.inr ⟨hp, β, hβ, hβ₁, hr, hz, hm, ?_⟩
    intro y hy hyx z
    simpa only [neg_one_mul, sub_neg_eq_add] using characterPrimeSum_sub_powerWeight χ hy
      (β:=β) (by linarith only [hβ]) (-1)
      (fun t ht => by simpa only [neg_one_mul, sub_neg_eq_add] using h ht.1 (ht.2.trans hyx)) z

end AnalyticNumberTheory.AdditiveNumberTheory
