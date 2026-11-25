import AnalyticNumberTheory.DirichletSeries.LogPerronContours

/-! # Linearity and absolute bounds for logarithmic Perron integrals -/

noncomputable section
open Complex Real MeasureTheory

namespace AnalyticNumberTheory.DirichletSeries

/-- Add two numerators whose traces converge absolutely on the chosen line. -/
theorem logPerronIntegral_add {F G : ℂ → ℂ} {σ x : ℝ} (hF : Integrable (logPerronTrace F σ x))
    (hG : Integrable (logPerronTrace G σ x)) :
    Integrable (logPerronTrace (fun s => F s+G s) σ x) ∧
      logPerronIntegral (fun s => F s+G s) σ x = logPerronIntegral F σ x + logPerronIntegral G σ x := by
  have h : logPerronTrace (fun s => F s+G s) σ x = fun t => logPerronTrace F σ x t+logPerronTrace G σ x t :=
    funext fun _ => add_mul ..
  refine ⟨h ▸ hF.add hG, ?_⟩
  simp only [logPerronIntegral, h, integral_add hF hG, add_div]

/-- Subtract two numerators whose traces converge absolutely on the chosen line. -/
theorem logPerronIntegral_sub {F G : ℂ → ℂ} {σ x : ℝ} (hF : Integrable (logPerronTrace F σ x))
    (hG : Integrable (logPerronTrace G σ x)) :
    Integrable (logPerronTrace (fun s => F s-G s) σ x) ∧
      logPerronIntegral (fun s => F s-G s) σ x = logPerronIntegral F σ x - logPerronIntegral G σ x := by
  have h : logPerronTrace (fun s => F s-G s) σ x = fun t => logPerronTrace F σ x t-logPerronTrace G σ x t :=
    funext fun _ => sub_mul ..
  refine ⟨h ▸ hF.sub hG, ?_⟩
  simp only [logPerronIntegral, h, integral_sub hF hG, sub_div]

/-- Taking the norm inside the integral extracts the cutoff power and
retains the absolute boundary weight. -/
theorem norm_logPerronIntegral_le (F : ℂ → ℂ) (σ x : ℝ) :
    ‖logPerronIntegral F σ x‖ ≤
      (Real.exp (σ*Real.log x) * ∫ t : ℝ, ‖F ((σ : ℂ)+t*I)‖/‖(σ : ℂ)+t*I‖^2)/(2*Real.pi) := by
  have H := norm_integral_le_integral_norm (μ := volume) (logPerronTrace F σ x)
  simp_rw [norm_logPerronTrace, integral_const_mul] at H
  have hd : ‖(2*(Real.pi : ℂ))‖ = 2*Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [logPerronIntegral, norm_div, hd]
  exact div_le_div_of_nonneg_right H (by positivity)

end AnalyticNumberTheory.DirichletSeries
