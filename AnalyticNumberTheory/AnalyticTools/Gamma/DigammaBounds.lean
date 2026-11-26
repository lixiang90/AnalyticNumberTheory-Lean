import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.ShiftedReciprocalSums

/-! # Global digamma bounds in terms of the nearest pole -/

noncomputable section

open Complex MeasureTheory Finset Set
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.AnalyticTools.Gamma

/-- The distance to the Gamma poles `0,-1,-2,…`. -/
def poleDistance (s : ℂ) : ℝ := Metric.infDist s nonPoleSetᶜ

private lemma poles_nonempty : nonPoleSetᶜ.Nonempty :=
  ⟨0, by simp [nonPoleSet]⟩

/-- The distance to the poles is strictly positive off the poles. -/
theorem poleDistance_pos {s : ℂ} (hs : s ∈ nonPoleSet) : 0 < poleDistance s :=
  (isOpen_nonPoleSet.isClosed_compl.notMem_iff_infDist_pos poles_nonempty).mp (by simpa using hs)

/-- The distance to the pole set is realized by an actual nonpositive integer. -/
theorem exists_poleDistance_eq_norm (s : ℂ) : ∃ n : ℕ, poleDistance s = ‖s+(n : ℂ)‖ := by
  obtain ⟨w, hw, he⟩ := isOpen_nonPoleSet.isClosed_compl.exists_infDist_eq_dist poles_nonempty s
  have H : ∃ n : ℕ, w = -(n : ℂ) := by simpa [nonPoleSet] using hw
  obtain ⟨n, rfl⟩ := H
  exact ⟨n, by simpa [poleDistance, dist_eq_norm] using he⟩

/-- Explicit growth in the full half-plane `Re(s) ≥ 1`, with an absolute
additive constant independent of the imaginary part. -/
theorem norm_digamma_le_log_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    ‖digamma s‖ ≤ Real.log ‖s‖ + Real.pi + 2 := by
  have hsl : s ∈ Complex.slitPlane := Or.inl (zero_lt_one.trans_le hs)
  have hr := hs.trans (Complex.re_le_norm s)
  have hr0 := zero_lt_one.trans_le hr
  have hc := cos_half_arg_pos_of_mem_slitPlane hsl
  have hcos : 0 ≤ Real.cos s.arg := by rw [Complex.cos_arg (Complex.slitPlane_ne_zero hsl)]; positivity
  have hd := Real.cos_two_mul (s.arg/2)
  rw [show 2*(s.arg/2)=s.arg by ring] at hd
  have hhalf : 1/2 ≤ Real.cos (s.arg/2) := by nlinarith
  have hi : (Real.cos (s.arg/2))⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ hc]; linarith
  have hdR : ‖deriv stirlingRemainder s‖ ≤ 1 := by
    apply (norm_deriv_stirlingRemainder_le hsl).trans
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (inv_pos.mpr hc).le hi 3, one_le_pow₀ hr (n := 2)]
  have hl : ‖Complex.log s‖ ≤ Real.log ‖s‖+Real.pi := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hr)]
    exact add_le_add_right (Complex.abs_arg_le_pi s) _
  have hg : ‖1/(2*s)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    exact div_le_one_of_le₀ (by linarith) (by positivity)
  rw [digamma_eq_stirling hsl]
  exact (norm_add_le ..).trans ((add_le_add (norm_sub_le ..) le_rfl).trans
    (by linarith only [hl,hg,hdR]))

/-- Uniform bound throughout the complex plane away from the Gamma poles.
The inverse distance occurs just once and the remaining growth is logarithmic. -/
theorem norm_digamma_le_poleDistance_inv_add_log {s : ℂ} (hs : s ∈ nonPoleSet) :
    ‖digamma s‖ ≤ (poleDistance s)⁻¹ + 5*Real.log (‖s‖+2) + Real.pi + 6 + Real.log 2 := by
  let N := ⌈‖s‖+1⌉₊
  have hN : ‖s‖+1 ≤ (N : ℝ) := Nat.le_ceil _
  have hNu : (N : ℝ) ≤ ‖s‖+2 := by
    have H := Nat.ceil_lt_add_one (by positivity : 0 ≤ ‖s‖+1)
    dsimp [N]
    linarith
  have hNpos : 0 < (N : ℝ) := by linarith [norm_nonneg s]
  have Hre : 1 ≤ (s+(N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [(abs_le.mp (Complex.abs_re_le_norm s)).1]
  have Hnorm := Hre.trans (Complex.re_le_norm (s+(N : ℂ)))
  have Hu : ‖s+(N : ℂ)‖ ≤ 2*(‖s‖+2) := by
    have H := norm_add_le s (N : ℂ)
    rw [Complex.norm_natCast] at H
    linarith
  have hlogs := Real.log_le_log (zero_lt_one.trans_le Hnorm) Hu
  rw [Real.log_mul (by norm_num) (by positivity)] at hlogs
  have hlogN := Real.log_le_log hNpos hNu
  have hsep (i : ℕ) (_hi : i < N) : poleDistance s ≤ ‖s+(i : ℂ)‖ := by
    have hi : -(i : ℂ) ∈ nonPoleSetᶜ := by simp [nonPoleSet]
    simpa [poleDistance, dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := s) hi
  have hinv := sum_inv_norm_add_nat_le s N (poleDistance_pos hs) hsep
  have hsum : ‖∑ i ∈ range N, (s+(i : ℂ))⁻¹‖ ≤ (poleDistance s)⁻¹ + 4*(harmonic N : ℝ) := by
    apply (norm_sum_le ..).trans
    simpa only [norm_inv] using hinv
  have he : digamma s = digamma (s+N) - ∑ i ∈ range N, (s+(i : ℂ))⁻¹ := by rw [digamma_add_nat hs, add_sub_cancel_right]
  rw [he]
  apply (norm_sub_le ..).trans
  linarith only [hsum, norm_digamma_le_log_of_one_le_re Hre, hlogs, hlogN, harmonic_le_one_add_log N]

end AnalyticNumberTheory.AnalyticTools.Gamma
