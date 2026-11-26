import AnalyticNumberTheory.AnalyticTools.EntireFunctions.CenteredPoleTranslation
import AnalyticNumberTheory.RiemannZeta.ZeroEnumeration

/-! # Partial fractions for the logarithmic derivative about a regular point -/

noncomputable section

open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.RiemannZeta

/-- The inverse squared distances from any center to the nontrivial zeros are summable. -/
theorem ZetaZeroEnumeration.summable_inv_sq_sub (Z : ZetaZeroEnumeration) (s : ℂ) :
    Summable fun n => (‖Z.zero n - s‖ ^ 2)⁻¹ :=
  summable_inv_sq_translate Z.finite_norm_le Z.summable_inv_sq s

/-- The inverse squared distances from any center to the negative even integers are summable. -/
theorem summable_trivialZetaZero_inv_sq_sub (s : ℂ) :
    Summable fun n => (‖trivialZetaZero n - s‖ ^ 2)⁻¹ :=
  summable_inv_sq_translate finite_trivialZetaZero_norm_le summable_trivialZetaZero_inv_sq s

/-- Any multiplicity-respecting enumeration gives the same partial fractions at a regular point. -/
theorem ZetaZeroEnumeration.neg_logDeriv_eq_centered (Z : ZetaZeroEnumeration) {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s = -Complex.log (2 * (Real.pi : ℂ)) + centeredPole 1 s -
      (∑' n, centeredPole (Z.zero n) s) - ∑' n, centeredPole (trivialZetaZero n) s := by
  rw [neg_logDeriv_riemannZeta_eq_distinct_centered hs hζ,
    (Z.hasSum_distinct (f := fun ρ => centeredPole ρ s) (Z.summable_centered s).hasSum).tsum_eq]

/-- Translating the center from zero to s replaces the constant by −ζ′(s)/ζ(s)
and translates every pole and zero by −s. -/
theorem neg_logDeriv_riemannZeta_translate (Z : ZetaZeroEnumeration) {s w : ℂ}
    (hs : s ≠ 1) (hζs : riemannZeta s ≠ 0) (hw : w + s ≠ 1) (hζw : riemannZeta (w+s) ≠ 0) :
    -deriv riemannZeta (w+s) / riemannZeta (w+s) =
      -deriv riemannZeta s / riemannZeta s + centeredPole (1-s) w -
        (∑' n, centeredPole (Z.zero n-s) w) - ∑' n, centeredPole (trivialZetaZero n-s) w := by
  have h₁ {z : ℂ} (hz : riemannZeta z ≠ 0) (n : ℕ) : z ≠ Z.zero n :=
    fun he => hz (he ▸ (mem_criticalStripZeros.mp (Z.mem_strip n)).1)
  have h₂ {z : ℂ} (hz : riemannZeta z ≠ 0) (n : ℕ) : z ≠ trivialZetaZero n :=
    fun he => hz (he ▸ riemannZeta_trivialZetaZero n)
  rw [Z.neg_logDeriv_eq_centered hw hζw, Z.neg_logDeriv_eq_centered hs hζs,
    centeredPole_translate one_ne_zero hs hw,
    (hasSum_centeredPole_translate Z.zero_ne_zero (h₁ hζs) (h₁ hζw) Z.summable_centered).tsum_eq,
    (hasSum_centeredPole_translate trivialZetaZero_ne_zero (h₂ hζs) (h₂ hζw)
      summable_centered_trivialZetaZero).tsum_eq]
  ring

end AnalyticNumberTheory.RiemannZeta
