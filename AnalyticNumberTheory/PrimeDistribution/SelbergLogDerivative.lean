import AnalyticNumberTheory.PrimeDistribution.SelbergSlopeBounds
import AnalyticNumberTheory.RiemannZeta.PoissonZeroAsymptotic

/-! # Selberg's bounds to the right of the critical line -/

noncomputable section

open Complex Filter
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Under RH, Selberg smoothing bounds both the Poisson mass and the logarithmic
derivative uniformly in the cutoff. The height-dependent part of the derivative
decays exponentially with the product of the horizontal displacement and log cutoff. -/
theorem selberg_poissonMass_and_logDeriv_le (hRH : RiemannHypothesisProp) :
    ∃ B > 0, ∀ (Z : ZetaZeroEnumeration) {s : ℂ} {u : ℝ},
      1/2 < s.re → s.re ≤ 2 → 2 ≤ |s.im| → 1 ≤ u → 2 ≤ (s.re-1/2)*u →
      Z.poissonMass s ≤ B * (Real.exp (u+u) + Real.log (|s.im|)) ∧
      ‖deriv riemannZeta s / riemannZeta s‖ ≤
        B * (Real.exp (u+u) + Real.exp (-((s.re-1/2)*u)) * Real.log (|s.im|)) := by
  obtain ⟨C, hC, HC⟩ := poissonMass_sub_re_logDeriv_estimate hRH
  let A := Real.log 4 + 8
  have hA : 0 < A := by dsimp [A]; positivity
  let B := 2*(A+C+1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A+B, by positivity, ?_⟩
  intro Z s u hs hs₂ ht hu hδu
  let X := Real.exp (u+u)
  let L := Real.log (|s.im|)
  let q := Real.exp (-((s.re-1/2)*u))
  let D := deriv riemannZeta s / riemannZeta s
  have hL : 0 ≤ L := Real.log_nonneg (one_le_two.trans ht)
  have hX : 1 ≤ X := Real.one_le_exp_iff.mpr (by linarith)
  have hx₀ : 0 ≤ X := zero_le_one.trans hX
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hq : q ≤ 1/2 := by
    dsimp only [q]
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le two_pos
    linarith [Real.add_one_le_exp ((s.re-1/2)*u)]
  have hF₀ : 0 ≤ Z.poissonMass s :=
    mul_nonneg (sub_nonneg.mpr hs.le) (tsum_nonneg fun _ => inv_nonneg.mpr (sq_nonneg _))
  have hD : ‖D‖ ≤ A*X + q*Z.poissonMass s :=
    norm_logDeriv_selberg_le Z hRH hs (one_le_two.trans ht) hu hδu
  have hζ := riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH s hs
  have hP := (le_abs_self _).trans (HC Z (by linarith) hs₂ ht hζ)
  have ht₀ := two_pos.trans_le ht
  have hlog : Real.log (|s.im|/(2*Real.pi)) ≤ L := by
    apply Real.log_le_log (div_pos ht₀ (mul_pos two_pos Real.pi_pos))
    exact div_le_self ht₀.le (by linarith [Real.two_le_pi])
  have hC₁ := (div_le_self hC.le (one_le_two.trans ht)).trans (le_mul_of_one_le_right hC.le hX)
  have hF : Z.poissonMass s ≤ B*(X+L) := by
    calc
      _ ≤ (2*(A+C))*X + 2*L := by
        change Z.poissonMass s - D.re - _ ≤ _ at hP
        linarith [Complex.re_le_norm D, mul_le_mul_of_nonneg_right hq hF₀]
      _ ≤ B*X + B*L := add_le_add
        (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) hx₀)
        (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) hL)
      _ = _ := (mul_add ..).symm
  constructor
  · exact hF.trans (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hx₀ hL))
  · change ‖D‖ ≤ (A+B)*(X+q*L)
    calc
      _ ≤ A*X + q*(B*(X+L)) := hD.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hF hq₀))
      _ = A*X + B*(q*X) + B*(q*L) := by ring
      _ ≤ A*X + B*X + (A+B)*(q*L) := by
        have hqx := mul_le_of_le_one_left hx₀ (show q ≤ 1 by linarith)
        exact add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hqx hB.le))
          (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq₀ hL))
      _ = _ := by ring

end AnalyticNumberTheory.PrimeDistribution
