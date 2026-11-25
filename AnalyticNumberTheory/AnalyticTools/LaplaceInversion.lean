import AnalyticNumberTheory.AnalyticTools.Transforms

/-! # Fourier and Bromwich inversion for the one-sided Laplace transform -/
noncomputable section
open Complex Real Set Filter MeasureTheory
open scoped FourierTransform Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- The exponentially damped function, extended to the real line by zero. -/
def laplaceDamped (σ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Ioi 0).indicator (fun t : ℝ => Complex.exp (-(σ:ℂ)*t)*f t)

/-- Restricting the Laplace transform to a vertical line gives the Fourier
transform of the damped function. Frequencies use the Fourier sign −2πi. -/
theorem fourier_laplaceDamped (f : ℝ → ℂ) (σ ξ : ℝ) :
    𝓕 (laplaceDamped σ f) ξ = laplaceTransform f ((σ:ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I) := by
  rw [laplaceTransform,Real.fourier_eq',←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  by_cases ht : t∈Ioi (0:ℝ)
  · simp only [laplaceDamped,indicator_of_mem ht,smul_eq_mul,RCLike.inner_apply,conj_trivial,
      Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
    rw [←mul_assoc,←Complex.exp_add];congr 2;ring
  · simp [laplaceDamped,indicator_of_notMem ht]

/-- The inverse vertical integral in the height parameter. -/
def bromwichIntegral (F : ℂ → ℂ) (σ x : ℝ) : ℂ :=
  (∫ t : ℝ, Complex.exp (((σ:ℂ)+(t:ℂ)*I)*x)*F ((σ:ℂ)+(t:ℂ)*I))/(2*Real.pi)

/-- The inverse vertical integral recovers the exponentially reweighted
zero extension at any continuity point of the damped function. -/
theorem bromwichIntegral_eq_damped {f : ℝ → ℂ} {σ x : ℝ}
    (hf : IntegrableOn (fun u : ℝ => Complex.exp (-(σ:ℂ)*u)*f u) (Ioi 0))
    (hF : Integrable (fun t : ℝ => laplaceTransform f ((σ:ℂ)+t*I)))
    (hx : ContinuousAt (laplaceDamped σ f) x) :
    bromwichIntegral (laplaceTransform f) σ x =
      Complex.exp ((σ:ℂ)*x)*laplaceDamped σ f x := by
  let g := laplaceDamped σ f
  let G (t : ℝ) := Complex.exp ((t:ℂ)*x*I)*laplaceTransform f ((σ:ℂ)+t*I)
  have hg : Integrable g := hf.integrable_indicator measurableSet_Ioi
  have h₂ : 0 < 2*Real.pi := by positivity
  have hG : Integrable (𝓕 g) := by
    apply (hF.comp_mul_left' h₂.ne').congr
    exact ae_of_all _ fun ξ => (fourier_laplaceDamped f σ ξ).symm
  have H := hg.fourierInv_fourier_eq hG hx
  rw [Real.fourierInv_eq'] at H
  have he (ξ : ℝ) : Complex.exp (((2*Real.pi*inner ℝ ξ x : ℝ):ℂ)*I) • 𝓕 g ξ = G ((2*Real.pi)*ξ) := by
    rw [show 𝓕 g ξ = _ from fourier_laplaceDamped f σ ξ]
    simp only [G,smul_eq_mul,RCLike.inner_apply,conj_trivial,Complex.ofReal_mul,Complex.ofReal_ofNat]
    congr 2;ring
  simp_rw [he] at H
  rw [Measure.integral_comp_mul_left G,abs_of_pos (inv_pos.mpr h₂),Complex.real_smul] at H
  have hterm (t : ℝ) : Complex.exp (((σ:ℂ)+(t:ℂ)*I)*x)*laplaceTransform f ((σ:ℂ)+t*I)
      = Complex.exp ((σ:ℂ)*x)*G t := by
    dsimp only [G];rw [←mul_assoc,←Complex.exp_add];congr 2;ring
  unfold bromwichIntegral;simp_rw [hterm]
  rw [integral_const_mul]
  change _ = Complex.exp ((σ:ℂ)*x)*g x
  rw [←H]
  push_cast;ring

/-- The one-sided Bromwich inversion formula at every positive point of
continuity, for an absolutely integrable transform on the vertical line. -/
theorem laplace_inversion {f : ℝ → ℂ} {σ x : ℝ} (hx : 0<x) (hcont : ContinuousAt f x)
    (hf : IntegrableOn (fun u : ℝ => Complex.exp (-(σ:ℂ)*u)*f u) (Ioi 0))
    (hF : Integrable (fun t : ℝ => laplaceTransform f ((σ:ℂ)+t*I))) :
    bromwichIntegral (laplaceTransform f) σ x = f x := by
  have he : laplaceDamped σ f =ᶠ[𝓝 x] fun t : ℝ => Complex.exp (-(σ:ℂ)*t)*f t := by
    filter_upwards [lt_mem_nhds hx] with t ht using indicator_of_mem ht _
  have hc : ContinuousAt (laplaceDamped σ f) x := ((by fun_prop : ContinuousAt
    (fun t : ℝ => Complex.exp (-(σ:ℂ)*t)) x).mul hcont).congr he.symm
  rw [bromwichIntegral_eq_damped hf hF hc,he.eq_of_nhds,←mul_assoc,←Complex.exp_add]
  simp

/-- At negative arguments the inverse of a one-sided Laplace transform vanishes. -/
theorem laplace_inversion_neg {f : ℝ → ℂ} {σ x : ℝ} (hx : x<0)
    (hf : IntegrableOn (fun u : ℝ => Complex.exp (-(σ:ℂ)*u)*f u) (Ioi 0))
    (hF : Integrable (fun t : ℝ => laplaceTransform f ((σ:ℂ)+t*I))) :
    bromwichIntegral (laplaceTransform f) σ x = 0 := by
  have he : laplaceDamped σ f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds hx] with t ht using indicator_of_notMem (not_lt_of_gt ht) _
  rw [bromwichIntegral_eq_damped hf hF (continuousAt_const.congr he.symm),he.eq_of_nhds,mul_zero]

end AnalyticNumberTheory.AnalyticTools