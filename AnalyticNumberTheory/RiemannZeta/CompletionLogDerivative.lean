import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-! # Size of the completion terms in the zeta logarithmic derivative -/

noncomputable section

open Complex
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.RiemannZeta

/-- On −1 ≤ Re(s) ≤ 2 the difference between the completed and ordinary zeta
logarithmic derivatives is bounded by log |Im(s)| plus an absolute constant. -/
theorem norm_logDeriv_xi_sub_zeta_le :
    ∃ C > 0, ∀ {s : ℂ}, -1 ≤ s.re → s.re ≤ 2 → 4 ≤ |s.im| → riemannZeta s ≠ 0 →
      ‖deriv xi s / xi s - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log (|s.im|) + C := by
  let P := (1/2 : ℂ) * (Real.log Real.pi : ℂ)
  let G : ℝ := Real.log (1 + (max |(0:ℝ)| |(2:ℝ)|)^2)/2 + Real.pi +
    (1/2 + (1+8*((max |(0:ℝ)| |(2:ℝ)|)^2+1)^(3/2 : ℝ))/12)
  refine ⟨1 + ‖P‖ + |G|, by positivity, ?_⟩
  intro s hs hs₂ ht hζ
  have ht₀ : 0 < |s.im| := by linarith
  have hs₁ : s ≠ 1 := fun he => by rw [he, Complex.one_im, abs_zero] at ht; linarith
  let z : ℂ := s/2+1
  have hr : z.re = s.re/2+1 := by simp [z]
  have hi : |z.im| = |s.im|/2 := by simp [z, abs_div]
  have hstrip := norm_digamma_strip_le (σ₁ := 0) (σ₂ := 2) (σ := z.re) (t := z.im)
    ⟨by rw [hr]; linarith, by rw [hr]; linarith⟩ (by rw [hi]; linarith)
  rw [Complex.re_add_im, hi] at hstrip
  have hlog := Real.log_le_log (div_pos ht₀ two_pos) (div_le_self ht₀.le (by norm_num : (1 : ℝ) ≤ 2))
  have hgam : ‖AnalyticTools.Gamma.digamma z‖ ≤ Real.log (|s.im|) + G := by
    dsimp only [G]
    linarith only [hstrip, hlog]
  have hhalf : ‖(1/2 : ℂ)*AnalyticTools.Gamma.digamma z‖ ≤ (Real.log (|s.im|) + |G|)/2 := by
    rw [norm_mul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num]
    linarith only [hgam, le_abs_self G]
  have hp : ‖(1 : ℂ)/(s-1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact div_le_self zero_le_one (by
      have h := Complex.abs_im_le_norm (s-1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at h
      linarith)
  have htriv (m : ℕ) : s ≠ -2*(m : ℂ) := by
    intro he
    have him := congrArg Complex.im he
    simp [Complex.mul_im] at him
    rw [him, abs_zero] at ht
    linarith
  rw [xi_logDeriv_eq_parts_of_ne_neg_even htriv hs₁ hζ, add_sub_cancel_right]
  change ‖1/(s-1) - P + (1/2 : ℂ)*AnalyticTools.Gamma.digamma z‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) hhalf).trans
    (by linarith [Real.log_nonneg (show 1 ≤ |s.im| by linarith), abs_nonneg G]))

end AnalyticNumberTheory.RiemannZeta
