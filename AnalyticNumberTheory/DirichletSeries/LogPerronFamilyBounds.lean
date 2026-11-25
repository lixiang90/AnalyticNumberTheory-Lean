import AnalyticNumberTheory.DirichletSeries.LogPerronLinearity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Absolute estimates for families of logarithmic Perron integrals -/

noncomputable section
open Complex Real Finset MeasureTheory

namespace AnalyticNumberTheory.DirichletSeries

private theorem square_norm_line (σ t : ℝ) : ‖(σ : ℂ)+t*I‖^2 = σ^2+t^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

/-- The real squared-denominator weight on a positive line has exact mass π/σ. -/
theorem vertical_inv_norm_sq_mass {σ : ℝ} (hσ : 0<σ) :
    Integrable (fun t : ℝ => (‖(σ : ℂ)+t*I‖^2)⁻¹) ∧
      (∫ t : ℝ, (‖(σ : ℂ)+t*I‖^2)⁻¹) = Real.pi/σ := by
  simp_rw [square_norm_line]
  refine ⟨integrable_inv_sq_add hσ, ?_⟩
  have he (t : ℝ) : (σ^2+t^2)⁻¹ = (σ^2)⁻¹ * (1+(σ⁻¹*t)^2)⁻¹ := by
    rw [← mul_inv]
    congr 1
    field_simp
  simp_rw [he, integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr hσ)]
  field_simp

/-- Taking a finite sum of norms outside the contour costs at most a single
integral of a common absolute majorant on the line. -/
theorem sum_norm_logPerronIntegral_le {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ)
    (σ x : ℝ) (hF : ∀ i ∈ S, Integrable (logPerronTrace (F i) σ x))
    (B : ℝ → ℝ) (hB : Integrable B)
    (h : ∀ t : ℝ, (∑ i ∈ S, ‖F i ((σ : ℂ)+t*I)‖)/‖(σ : ℂ)+t*I‖^2 ≤ B t) :
    (∑ i ∈ S, ‖logPerronIntegral (F i) σ x‖) ≤
      (Real.exp (σ*Real.log x)*(∫ t : ℝ, B t))/(2*Real.pi) := by
  let c := Real.exp (σ*Real.log x)
  have hc : 0≤c := (Real.exp_pos _).le
  have hd : ‖(2*(Real.pi : ℂ))‖ = 2*Real.pi := by rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]; norm_num
  have hi (i : ι) (hm : i ∈ S) := (hF i hm).norm
  calc
    _ ≤ ∑ i ∈ S, (∫ t : ℝ, ‖logPerronTrace (F i) σ x t‖)/(2*Real.pi) := by
      apply sum_le_sum
      intro i _
      rw [logPerronIntegral, norm_div, hd]
      exact div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) (by positivity)
    _ = (∫ t : ℝ, ∑ i ∈ S, ‖logPerronTrace (F i) σ x t‖)/(2*Real.pi) := by
      rw [← sum_div, integral_finsetSum _ hi]
    _ ≤ (∫ t : ℝ, c*B t)/(2*Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply integral_mono (integrable_finsetSum _ hi) (hB.const_mul c)
      intro t
      simp_rw [norm_logPerronTrace]
      rw [← mul_sum, ← sum_div]
      exact mul_le_mul_of_nonneg_left (h t) hc
    _ = _ := by rw [integral_const_mul]

/-- A height-independent bound for the sum of numerator norms gives the
cutoff factor exp(σ log x)/(2σ), with no loss from truncating the contour. -/
theorem sum_norm_logPerronIntegral_le_uniform {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ)
    {σ : ℝ} (hσ : 0<σ) (x : ℝ) (hF : ∀ i ∈ S, Integrable (logPerronTrace (F i) σ x))
    {B : ℝ} (h : ∀ t : ℝ, (∑ i ∈ S, ‖F i ((σ : ℂ)+t*I)‖) ≤ B) :
    (∑ i ∈ S, ‖logPerronIntegral (F i) σ x‖) ≤ Real.exp (σ*Real.log x)*B/(2*σ) := by
  have k := vertical_inv_norm_sq_mass hσ
  have H := sum_norm_logPerronIntegral_le S F σ x hF _ (k.1.const_mul B)
    (fun t => by
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (h t) (sq_nonneg _))
  rw [integral_const_mul, k.2] at H
  exact H.trans_eq (by field_simp)

end AnalyticNumberTheory.DirichletSeries
