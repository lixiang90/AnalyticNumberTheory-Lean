import AnalyticNumberTheory.AnalyticTools.EntireFunctions.CenteredPoleTranslation

/-! # Removing a finite set of nearby poles from a logarithmic derivative -/

noncomputable section

open Complex Finset

namespace AnalyticNumberTheory.AnalyticTools.EntireFunctions

/-- Subtracting the sharp fractions of a finite window from the change of a
centered expansion costs a squared-distance sum at the reference point w.
The two geometric hypotheses apply inside and outside the chosen window. -/
theorem norm_centeredPole_sub_window_le (a : ℕ → ℂ) (S : Finset ℕ) {s w : ℂ} {K : ℝ}
    (ha : ∀ n, a n ≠ 0) (hs : ∀ n, s ≠ a n) (hw : ∀ n, w ≠ a n)
    (hS : Summable fun n => centeredPole (a n) s) (hW : Summable fun n => centeredPole (a n) w)
    (h₂ : Summable fun n => (‖a n-w‖^2)⁻¹)
    (hin : ∀ n ∈ S, ‖w-a n‖ ≤ K)
    (hout : ∀ n ∉ S, ‖w-s‖ * ‖w-a n‖ ≤ K * ‖s-a n‖) :
    ‖(∑' n, centeredPole (a n) s) - (∑' n, centeredPole (a n) w) -
      ∑ n ∈ S, 1/(s-a n)‖ ≤ K * ∑' n, (‖a n-w‖^2)⁻¹ := by
  let g (n : ℕ) : ℂ := if n ∈ S then 1/(s-a n) else 0
  have hg : HasSum g (∑ n ∈ S, 1/(s-a n)) := by
    have hsupport (n : ℕ) (hn : n ∉ S) : g n = 0 := by simp [g, hn]
    have h := hasSum_sum_of_ne_finset_zero (L := .unconditional ℕ) hsupport
    have he : (∑ n ∈ S, g n) = ∑ n ∈ S, 1/(s-a n) := sum_congr rfl (fun n hn => by simp [g, hn])
    exact he ▸ h
  have H := (hS.hasSum.sub hW.hasSum).sub hg
  rw [← H.tsum_eq]
  apply tsum_of_norm_bounded (h₂.hasSum.mul_left K)
  intro n
  dsimp only [Pi.sub_apply, g]
  rw [centeredPole_eq (ha n) (hs n), centeredPole_eq (ha n) (hw n),
    add_sub_add_right_eq_sub, norm_sub_rev (a n) w, ← div_eq_mul_inv]
  have hwp := norm_pos_iff.mpr (sub_ne_zero.mpr (hw n))
  have hsp := norm_pos_iff.mpr (sub_ne_zero.mpr (hs n))
  by_cases hn : n ∈ S
  · rw [ite_eq_left hn, show 1/(s-a n)-1/(w-a n)-1/(s-a n) = -(1/(w-a n)) by ring,
      norm_neg, norm_div, norm_one, div_le_div_iff₀ hwp (sq_pos_of_pos hwp)]
    nlinarith only [mul_le_mul_of_nonneg_right (hin n hn) hwp.le]
  · rw [ite_eq_right hn, sub_zero, one_div, one_div, inv_sub_inv (sub_ne_zero.mpr (hs n)) (sub_ne_zero.mpr (hw n)),
      sub_sub_sub_cancel_right, norm_div, norm_mul,
      div_le_div_iff₀ (mul_pos hsp hwp) (sq_pos_of_pos hwp)]
    nlinarith only [mul_le_mul_of_nonneg_right (hout n hn) hwp.le]

end AnalyticNumberTheory.AnalyticTools.EntireFunctions
