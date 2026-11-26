import AnalyticNumberTheory.AnalyticTools.EntireFunctions.CenteredPoles

/-! # Translating the center of a partial fraction expansion -/

noncomputable section

open Filter Complex

namespace AnalyticNumberTheory.AnalyticTools.EntireFunctions

/-- Translating a locally finite inverse-square-summable pole sequence preserves
inverse-square summability, even if one of the translated terms is zero. -/
theorem summable_inv_sq_translate {a : ℕ → ℂ} (hf : ∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite)
    (ha : Summable fun n => (‖a n‖^2)⁻¹) (s : ℂ) : Summable fun n => (‖a n-s‖^2)⁻¹ := by
  apply (ha.mul_left 4).of_norm_bounded_eventually
  have he : ∀ᶠ n in cofinite, n ∉ {n | ‖a n‖ ≤ 2*‖s‖} := by
    simpa [eventually_cofinite] using hf (2*‖s‖)
  filter_upwards [he] with n hn
  have h := lt_of_not_ge (show ¬ ‖a n‖ ≤ 2*‖s‖ from hn)
  have htri := norm_sub_le (a n-s) (-s)
  rw [sub_neg_eq_add,sub_add_cancel,norm_neg] at htri
  have h₀ : 0 < ‖a n‖ := by linarith [norm_nonneg s]
  have h₁ : 0 < ‖a n-s‖ := by linarith [norm_nonneg s]
  have hsq := pow_le_pow_left₀ (norm_nonneg (a n)) (by linarith : ‖a n‖ ≤ 2*‖a n-s‖) 2
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),←one_div,←div_eq_mul_inv,
    div_le_div_iff₀ (sq_pos_of_pos h₁) (sq_pos_of_pos h₀)]
  nlinarith only [hsq]

/-- Recentering a simple-pole term subtracts its value at the new center. -/
theorem centeredPole_translate {ω s w : ℂ} (hω : ω ≠ 0) (hs : s ≠ ω) (hw : w+s ≠ ω) :
    centeredPole (ω-s) w = centeredPole ω (w+s)-centeredPole ω s := by
  have hws : w ≠ ω-s := by intro he; exact hw (eq_sub_iff_add_eq.mp he)
  rw [centeredPole_eq (sub_ne_zero.mpr hs.symm) hws,centeredPole_eq hω hw,centeredPole_eq hω hs,
    show w-(ω-s) = w+s-ω by ring,show ω-s = -(s-ω) by ring]
  simp only [one_div,inv_neg]
  ring

/-- The centered fractions of a translated sequence sum to the difference
of the two original absolutely convergent expansions. -/
theorem hasSum_centeredPole_translate {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) {s w : ℂ}
    (hs : ∀ n, s ≠ a n) (hw : ∀ n, w+s ≠ a n)
    (hsum : ∀ z : ℂ, Summable fun n => centeredPole (a n) z) :
    HasSum (fun n => centeredPole (a n-s) w)
      ((∑' n,centeredPole (a n) (w+s))-∑' n,centeredPole (a n) s) := by
  exact ((hsum (w+s)).hasSum.sub (hsum s).hasSum).congr_fun
    (fun n => centeredPole_translate (ha n) (hs n) (hw n))

end AnalyticNumberTheory.AnalyticTools.EntireFunctions
