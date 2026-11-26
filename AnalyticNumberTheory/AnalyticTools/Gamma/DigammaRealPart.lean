import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling

/-! # The real part of the digamma function at large height -/

noncomputable section

open Complex

namespace AnalyticNumberTheory.AnalyticTools.Gamma

/-- On each bounded vertical strip, the real part of the digamma function is
logarithmic in the absolute height with a uniform inverse-height error. -/
theorem abs_re_digamma_sub_log_height_le (A : ℝ) (hA : 0 ≤ A) :
    ∃ C > 0, ∀ z : ℂ, |z.re| ≤ A → 1 ≤ |z.im| →
      |(digamma z).re - Real.log (|z.im|)| ≤ C / |z.im| := by
  let K : ℝ := 1/2 + (1 + 8 * ((max |(-A)| |A|)^2+1)^(3/2 : ℝ))/12
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K+A, add_pos_of_pos_of_nonneg hK hA, ?_⟩
  intro z hz ht
  have ht₀ := zero_lt_one.trans_le ht
  have hnorm := Complex.abs_im_le_norm z
  have hn₀ := ht₀.trans_le hnorm
  have h₁ := norm_digamma_sub_log_strip_le (Set.mem_Icc.mpr (abs_le.mp hz)) ht
  rw [Complex.re_add_im] at h₁
  have herr : |(digamma z).re - Real.log ‖z‖| ≤ K / |z.im| := by
    simpa only [Complex.sub_re, Complex.log_re] using (Complex.abs_re_le_norm _).trans h₁
  have hn := (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hz (le_refl |z.im|))
  have hlog : |Real.log ‖z‖ - Real.log (|z.im|)| ≤ A / |z.im| := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log ht₀ hnorm))]
    have h := Real.log_le_sub_one_of_pos (div_pos hn₀ ht₀)
    rw [Real.log_div hn₀.ne' ht₀.ne'] at h
    calc
      _ ≤ ‖z‖ / |z.im| - 1 := h
      _ ≤ (A + |z.im|) / |z.im| - 1 := by gcongr
      _ = A / |z.im| := by rw [add_div, div_self ht₀.ne']; ring
  calc
    _ ≤ |(digamma z).re - Real.log ‖z‖| + |Real.log ‖z‖ - Real.log (|z.im|)| := abs_sub_le ..
    _ ≤ K / |z.im| + A / |z.im| := add_le_add herr hlog
    _ = (K+A) / |z.im| := (add_div ..).symm

end AnalyticNumberTheory.AnalyticTools.Gamma
