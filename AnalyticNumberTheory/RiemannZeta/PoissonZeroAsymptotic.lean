import AnalyticNumberTheory.AnalyticTools.Gamma.DigammaRealPart
import AnalyticNumberTheory.RiemannZeta.PoissonZeroSum

/-! # The Gamma correction to the Poisson sum of zeta zeros -/

noncomputable section

open Complex
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.RiemannZeta

/-- Under RH the Poisson zero sum differs from Re(ζ′/ζ) by
(1/2) log(|t|/(2π)) with a uniform O(1/|t|) error on 0 < σ ≤ 2.
The constant is independent of the enumeration, the point, and its distance to nearby zeros. -/
theorem poissonMass_sub_re_logDeriv_estimate (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ (Z : ZetaZeroEnumeration) {s : ℂ}, 0 < s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      riemannZeta s ≠ 0 →
      |Z.poissonMass s - (deriv riemannZeta s / riemannZeta s).re -
        (1/2) * Real.log (|s.im|/(2*Real.pi))| ≤ C / |s.im| := by
  obtain ⟨D, hD, H⟩ := abs_re_digamma_sub_log_height_le 2 (by norm_num)
  refine ⟨1+D, by positivity, ?_⟩
  intro Z s hs hs₂ ht hζ
  have ht₀ : 0 < |s.im| := two_pos.trans_le ht
  have hs₀ : s ≠ 0 := fun he => by simp [he] at hs
  have hs₁ : s ≠ 1 := fun he => by rw [he, Complex.one_im, abs_zero] at ht; linarith
  let z : ℂ := s/2+1
  have hzre : z.re = s.re/2+1 := by simp [z]
  have hzim : |z.im| = |s.im|/2 := by simp [z, abs_div]
  have hgz := H z (by rw [hzre, abs_of_nonneg (by linarith)]; linarith)
    (by rw [hzim]; linarith)
  rw [hzim] at hgz
  have hp : |((1 : ℂ)/(s-1)).re| ≤ 1/|s.im| := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le ht₀
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s-1)
  have hlog : Real.log (|s.im|/(2*Real.pi)) = Real.log (|s.im|/2) - Real.log Real.pi := by
    rw [← Real.log_div (div_pos ht₀ two_pos).ne' Real.pi_ne_zero]
    congr 1
    ring
  have he : Z.poissonMass s - (deriv riemannZeta s / riemannZeta s).re -
      (1/2) * Real.log (|s.im|/(2*Real.pi)) =
      ((1 : ℂ)/(s-1)).re + (1/2) * ((AnalyticTools.Gamma.digamma z).re - Real.log (|s.im|/2)) := by
    rw [← Z.re_logDeriv_xi_eq_poissonMass hRH hs₀ (fun hz => hζ (xi_eq_zero_iff.mp hz).1),
      xi_logDeriv_eq_parts hs hs₁ hζ, hlog]
    change _ = _ + (1/2) * ((AnalyticTools.Gamma.digamma (s/2+1)).re - _)
    simp only [Complex.add_re, Complex.sub_re]
    norm_num [Complex.mul_re]
    ring
  rw [he]
  calc
    _ ≤ |((1 : ℂ)/(s-1)).re| + |(1/2 : ℝ) * ((AnalyticTools.Gamma.digamma z).re - Real.log (|s.im|/2))| := abs_add_le ..
    _ ≤ 1/|s.im| + (1/2) * (D/(|s.im|/2)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hgz (by norm_num))
    _ = (1+D) / |s.im| := by ring

end AnalyticNumberTheory.RiemannZeta
