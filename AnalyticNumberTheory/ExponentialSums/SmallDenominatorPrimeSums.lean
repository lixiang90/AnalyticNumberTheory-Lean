import AnalyticNumberTheory.ExponentialSums.SmallDenominatorScale
import AnalyticNumberTheory.ExponentialSums.PrimeSumsFromDensity

/-! # Prime sums near rational frequencies of small denominator -/

noncomputable section

open Real
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- On an arc with q and x|z| at most exp(η sqrt(log x)), the von Mangoldt
sum is bounded by C x log log(10q)/(sqrt q (1+x|z|)). The numerator
can have either sign. The same bound works at every endpoint up to x. -/
theorem primeExpSum_small_denominator :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < C ∧
      ∀ {x : ℝ} {q : ℕ} {a : ℤ} {z : ℝ}, 2 ≤ x → 0 < q → a.natAbs.Coprime q →
        (q : ℝ) ≤ Real.exp (η*Real.sqrt (Real.log x)) →
        x*|z| ≤ Real.exp (η*Real.sqrt (Real.log x)) →
        ∀ {y : ℝ}, 1 ≤ y → y ≤ x →
          ‖primeExpSum y ((a : ℝ)/q+z)‖ ≤ C*smallDenominatorPrimeScale x q z := by
  obtain ⟨κ,b,A,hκ,hκ₄,hb,hA,H⟩ := primeExpSum_small_denominator_expansion
  let η := min κ (b/4)
  have hη : 0 < η := lt_min hκ (by positivity)
  have hηκ : η ≤ κ := min_le_left ..
  have hηb : 4*η ≤ b := by linarith only [min_le_right κ (b/4)]
  let C := A*(1+4*(1+2*Real.pi))
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨η,C,hη,hηκ.trans hκ₄,hC,?_⟩
  intro x q a z hx hq ha hqx hz y hy hyx
  letI : NeZero q := ⟨hq.ne'⟩
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hqκ := hqx.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hηκ (Real.sqrt_nonneg _)))
  have hnat (n : ℕ) (hn : n.Coprime q) {v : ℝ} (hv : x*|v| ≤ Real.exp (η*Real.sqrt (Real.log x))) :
      ‖primeExpSum y ((n : ℝ)/q+v)‖ ≤ C*smallDenominatorPrimeScale x q v := by
    apply (H hx hqκ hn hy hyx v).trans
    change A*(smallDenominatorPrimeScale y q v+_) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add
      (smallDenominatorPrimeScale_mono (zero_le_one.trans hy) hyx hq v)
      (smallDenominator_error_absorption hη.le hηb hx₁ (zero_le_one.trans hy) hyx hq hqx hv)) hA.le).trans_eq
    dsimp only [C]
    ring
  cases a with
  | ofNat n => exact hnat n ha hz
  | negSucc n =>
    have hh := hnat (n+1) ha (v := -z) (by simpa only [abs_neg] using hz)
    have hs : ((Int.negSucc n : ℤ) : ℝ)/q+z = -(((n+1 : ℕ) : ℝ)/q+(-z)) := by
      push_cast
      ring
    rw [hs, ← star_primeExpSum, norm_star]
    simpa only [smallDenominatorPrimeScale, abs_neg] using hh

end AnalyticNumberTheory.ExponentialSums
