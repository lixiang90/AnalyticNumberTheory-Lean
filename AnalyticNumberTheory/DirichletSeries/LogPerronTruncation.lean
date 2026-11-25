import AnalyticNumberTheory.DirichletSeries.LogPerron

/-! # Uniform height truncation of the logarithmic Perron integral -/

noncomputable section

open Complex MeasureTheory Set

namespace AnalyticNumberTheory.DirichletSeries

private lemma norm_right_tail_le {g : ℝ → ℂ} {σ M T : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hg : ∀ t, ‖g t‖ ≤ M * (σ^2+t^2)⁻¹) :
    ‖∫ t : ℝ in Ioi T, g t‖ ≤ M/T := by
  calc
    _ ≤ ∫ t : ℝ in Ioi T, M*t^(-2 : ℝ) := by
      apply norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul M)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      have ht' := hT.trans ht
      rw [Real.rpow_neg ht'.le, Real.rpow_two]
      exact (hg t).trans (mul_le_mul_of_nonneg_left
        (inv_anti₀ (sq_pos_of_pos ht') (le_add_of_nonneg_left (sq_nonneg σ))) hM)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
      norm_num [div_eq_mul_inv, Real.rpow_neg_one]

/-- Truncating an integrable vertical integrand dominated by a Cauchy kernel at
height `T` costs at most `2M/T` before division by the inversion factor. -/
theorem norm_integral_sub_symmetric_of_quadratic_bound {g : ℝ → ℂ} {σ M T : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hi : Integrable g) (hg : ∀ t, ‖g t‖ ≤ M*(σ^2+t^2)⁻¹) :
    ‖(∫ t : ℝ, g t) - ∫ t : ℝ in -T..T, g t‖ ≤ 2*M/T := by
  have hr := norm_right_tail_le hT hM hg
  have hl := norm_right_tail_le (g := fun t => g (-t)) (σ := σ) hT hM (fun t => by simpa using hg (-t))
  rw [integral_comp_neg_Ioi] at hl
  have htotal := intervalIntegral.integral_Iic_add_Ioi (b := -T) hi.integrableOn hi.integrableOn
  have hmid := intervalIntegral.integral_interval_add_Ioi (a := -T) (b := T) hi.integrableOn hi.integrableOn
  rw [← htotal, ← hmid, show ∀ l m r : ℂ, l+(m+r)-m=l+r by intros; abel]
  exact (norm_add_le ..).trans ((add_le_add hl hr).trans_eq (by ring))

namespace DirichletFrequency

/-- For all real cutoffs and positive heights, truncating logarithmic Perron
inversion costs at most `exp(σu) ∑ |aₙ| exp(−σλₙ)/(πT)`. -/
theorem norm_truncated_logPerron_sub_sum_le (F : DirichletFrequency) (a : ℕ → ℂ)
    {σ T : ℝ} (hσ : 0 < σ) (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) (hT : 0 < T) :
    ‖(∫ t : ℝ in -T..T, F.sum a ((σ : ℂ)+t*I)*logPerronKernel σ u t)/(2*Real.pi) -
      ∑ n ∈ Finset.range (F.count u), a n*((u-F n : ℝ) : ℂ)‖ ≤
      ((∑' n, ‖a n‖*Real.exp (-σ*F n))*Real.exp (σ*u))/(Real.pi*T) := by
  let M := (∑' n, ‖a n‖*Real.exp (-σ*F n))*Real.exp (σ*u)
  have hM : 0 ≤ M := mul_nonneg (tsum_nonneg fun _ => by positivity) (Real.exp_pos _).le
  have hbound (t : ℝ) : ‖F.sum a ((σ : ℂ)+t*I)*logPerronKernel σ u t‖ ≤ M*(σ^2+t^2)⁻¹ := by
    rw [norm_mul, norm_logPerronKernel, show M*(σ^2+t^2)⁻¹ =
      (∑' n, ‖a n‖*Real.exp (-σ*F n))*(Real.exp (σ*u)*(σ^2+t^2)⁻¹) by dsimp [M]; ring]
    exact mul_le_mul_of_nonneg_right (F.norm_sum_absolute_line_le a h t) (by positivity)
  have H := norm_integral_sub_symmetric_of_quadratic_bound hT hM (F.integrable_sum_logPerron a hσ h u) hbound
  rw [← F.logPerron_formula a hσ h, ← sub_div, norm_div, norm_sub_rev]
  have hp : ‖(2*Real.pi : ℂ)‖ = 2*Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [hp]
  exact (div_le_div_of_nonneg_right H (by positivity)).trans_eq (by dsimp [M]; ring)

end DirichletFrequency

end AnalyticNumberTheory.DirichletSeries
