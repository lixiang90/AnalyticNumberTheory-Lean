import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralBounds
import AnalyticNumberTheory.PrimeDistribution.SelbergLogDerivative
import AnalyticNumberTheory.RiemannZeta.HorizontalLogZeta
import AnalyticNumberTheory.RiemannZeta.LocalPoissonExpansion

/-! # Bounds for the Euler logarithm to the right of a Selberg cutoff -/

noncomputable section

open Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- At distance at least 2/u to the right of the critical line, integrating
Selberg's estimate gives a uniform O(log |t| / u) bound for the horizontal
Euler logarithm. The same scale bounds the number of zeros in the open window. -/
theorem selberg_horizontalLogZeta_and_window_le (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ (Z : ZetaZeroEnumeration) {t u : ℝ}, 4 ≤ |t| → 2 ≤ u →
      Real.exp (4*u) ≤ Real.log |t| →
      ((Z.ordinateWindow t ((2/u)/8)).card : ℝ) ≤ C*(Real.log |t|/u) ∧
      ∀ x : ℝ, 1/2+2/u ≤ x → x ≤ 2 → ‖horizontalLogZeta x t‖ ≤ C*(Real.log |t|/u) := by
  obtain ⟨B, hB, HB⟩ := selberg_poissonMass_and_logDeriv_le hRH
  let A := Real.pi^2/6
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨16*B+A, by positivity, ?_⟩
  intro Z t u ht hu hscale
  let c : ℝ := 1/2
  let δ := 2/u
  let L := Real.log |t|
  let X := Real.exp (u+u)
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let D (x : ℝ) := deriv riemannZeta (p x)/riemannZeta (p x)
  have hu₀ := two_pos.trans_le hu
  have hu₁ := one_le_two.trans hu
  have hδ : 0 < δ := div_pos two_pos hu₀
  have hδ₁ : δ ≤ 1 := (div_le_one hu₀).mpr hu
  have hdu : δ*u = 2 := div_mul_cancel₀ _ hu₀.ne'
  have hL : 0 < L := Real.log_pos (by linarith)
  have ht₀ : t ≠ 0 := fun h => by norm_num [h] at ht
  have hX : 1 ≤ X := Real.one_le_exp_iff.mpr (by linarith)
  have huX : u ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (u+u)]
  have hsmall : X ≤ L/u := (le_div_iff₀ hu₀).mpr (calc
    X*u ≤ X*X := mul_le_mul_of_nonneg_left huX (zero_le_one.trans hX)
    _ = Real.exp (4*u) := by rw [show 4*u = (u+u)+(u+u) by ring, Real.exp_add]
    _ ≤ L := hscale)
  have hXL : X ≤ L := hsmall.trans (div_le_self hL.le hu₁)
  have hR := div_nonneg hL.le hu₀.le
  have hr (y : ℝ) : (p y).re = y := by simp [p]
  have hi (y : ℝ) : (p y).im = t := by simp [p]
  have hright {y : ℝ} (hy : c+δ ≤ y) (hy₂ : y ≤ 2) :
      Z.poissonMass (p y) ≤ B*(X+L) ∧ ‖D y‖ ≤ B*(X+Real.exp (-((y-c)*u))*L) := by
    have hyd : 2 ≤ (y-c)*u := hdu ▸ mul_le_mul_of_nonneg_right (by linarith : δ ≤ y-c) hu₀.le
    have h := HB Z (s := p y) (by rw [hr]; exact (lt_add_of_pos_right c hδ).trans_le hy)
      (by rwa [hr]) (by rw [hi]; linarith) hu₁ (by rwa [hr])
    rwa [hr, hi] at h
  constructor
  · have hd : (p (c+δ)).re-1/2 = δ := by rw [hr]; dsimp [c]; ring
    have hF := (hright (y := c+δ) le_rfl (by dsimp [c]; linarith)).1
    have hcard := Z.card_ordinateWindow_le_poissonMass hRH (w := p (c+δ))
      (by rw [hr]; exact lt_add_of_pos_right c hδ) (d := δ/8) (by rw [hd]; linarith)
    rw [hi, hd] at hcard
    apply hcard.trans
    calc
      4*δ*Z.poissonMass (p (c+δ)) ≤ 4*δ*(B*(L+L)) :=
        mul_le_mul_of_nonneg_left (hF.trans (mul_le_mul_of_nonneg_left (add_le_add hXL le_rfl) hB.le)) (by positivity)
      _ = 16*B*(L/u) := by dsimp only [δ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA) hR
  · intro x hx hx₂
    have hcx := (lt_add_of_pos_right c hδ).le.trans hx
    have hc : ContinuousOn D (Icc x 2) := by
      intro y hy
      apply (continuousAt_horizontal_zeta_logDeriv ht₀ _).continuousWithinAt
      apply riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH
      simpa [c] using ((lt_add_of_pos_right c hδ).trans_le (hx.trans hy.1))
    have hInt := horizontal_exp_majorant_norm_integral hcx hx₂ (by dsimp [c] at hcx; linarith)
      hu₀ (zero_le_one.trans hX) hL.le hB.le D hc (fun y hy => (hright (hx.trans hy.1) hy.2).2)
    have hlog : ‖logZeta (p 2)‖ ≤ A := by
      have h := norm_LSeries_two_le zero_le_one norm_logZetaCoeff_le_one (s := p 2) (hr 2)
      rwa [← logZeta_eq_LSeries (by rw [hr]; norm_num), one_mul] at h
    change ‖logZeta (p 2)-(∫ y in x..2, D y)‖ ≤ (16*B+A)*(L/u)
    apply (norm_sub_le _ _).trans
    have hbase := hlog.trans (le_mul_of_one_le_right hA (hX.trans hsmall))
    have hfar := (intervalIntegral.norm_integral_le_integral_norm (f := D) hx₂).trans hInt
    have hcost := mul_le_mul_of_nonneg_left (by linarith only [hsmall] : 2*X+L/u ≤ 3*(L/u)) hB.le
    linarith only [hbase, hfar, hcost, mul_nonneg hB.le hR]

end AnalyticNumberTheory.PrimeDistribution
