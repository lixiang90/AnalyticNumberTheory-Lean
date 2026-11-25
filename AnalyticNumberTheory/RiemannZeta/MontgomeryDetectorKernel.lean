import AnalyticNumberTheory.RiemannZeta.RieszDetectorKernel
import AnalyticNumberTheory.DirichletSeries.RieszKernelBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A sixth-power kernel for the zeta zero detector

The extra numerator used to cancel the zeta pole is controlled by the
first Riesz denominator factor. The six remaining factors each give one
power of vertical decay, for all ordinates and all mollifier lengths.
-/

open Real Complex MeasureTheory Filter Finset Set
open AnalyticNumberTheory.DirichletSeries
open scoped Topology ArithmeticFunction.Moebius
namespace AnalyticNumberTheory.RiemannZeta

/-- Keeping the first factor of the Riesz denominator in the estimate
preserves six full powers of decay even after the pole correction. -/
theorem riesz_pole_corrected_sixth_kernel {ρ w : ℂ} (hγ : 1≤ρ.im)
    (hw : -(1/2:ℝ)≤w.re) (hd : 1/4≤‖w‖) :
    ‖1+w/(ρ-1)‖/‖rieszDenom 6 w‖≤3645/(1+|w.im|)^6 := by
  let u := 1+|w.im|
  have hu : 0<u := by dsimp [u];positivity
  have hw' : 0<‖w‖ := by linarith
  have hρ : 1≤‖ρ-1‖ := hγ.trans (by simpa using Complex.im_le_norm (ρ-1))
  have hlin : ‖1+w/(ρ-1)‖≤5*‖w‖ := by
    apply (norm_add_le ..).trans
    rw [norm_one,norm_div]
    linarith [div_le_self (norm_nonneg w) hρ]
  have hden := rieszDenom_norm_lower 6 hw (norm_nonneg w) le_rfl
  change ‖w‖*(u/3)^6≤‖rieszDenom 6 w‖ at hden
  apply (div_le_div₀ (by positivity) hlin (by positivity) hden).trans_eq
  change _=3645/u^6
  field_simp [hu.ne',hw'.ne'];ring

/-- Pointwise critical-line estimate for the pole-corrected zeta detector.
The constant is independent of the mollifier length and Riesz cutoff. -/
theorem norm_montgomery_zeta_integrand {ρ : ℂ} (hγ : 1≤ρ.im) (hβ : 3/4≤ρ.re) (hβ' : ρ.re≤1)
    (X : ℕ) {Y : ℝ} (hY : 0<Y) (v : ℝ) :
    ‖rieszDetectorIntegrand X ρ Y (((1/2-ρ.re:ℝ):ℂ)+v*I)‖≤
      (3645*Y^(1/2-ρ.re))*(1/(1+|v|)^6*
        ‖riemannZeta ((1/2:ℂ)+((v+ρ.im:ℝ):ℂ)*I)‖*
        ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((v+ρ.im:ℝ):ℂ)*I)‖) := by
  let w : ℂ := ((1/2-ρ.re:ℝ):ℂ)+v*I
  let s : ℂ := (1/2:ℂ)+((v+ρ.im:ℝ):ℂ)*I
  have hr : w.re=1/2-ρ.re := by simp [w]
  have hi : w.im=v := by simp [w]
  have hs : ρ+w=s := by apply Complex.ext <;> simp [w,s] <;> ring
  have hn := Complex.abs_re_le_norm w
  rw [hr,abs_of_nonpos (by linarith)] at hn
  have hk := riesz_pole_corrected_sixth_kernel (w:=w) hγ (by linarith) (by linarith)
  rw [hi] at hk
  have hy := Complex.norm_cpow_eq_rpow_re_of_pos (y:=w) hY
  rw [hr] at hy
  change ‖rieszDetectorIntegrand X ρ Y w‖≤_
  rw [rieszDetectorIntegrand,norm_div,norm_mul,norm_mul,norm_mul,hs,hy]
  let P := Y^(1/2-ρ.re)*‖riemannZeta s‖*‖rieszMobiusPolynomial X s‖
  calc _ = P*(‖1+w/(ρ-1)‖/‖rieszDenom 6 w‖) := by dsimp [P];ring
       _ ≤ P*(3645/(1+|v|)^6) := mul_le_mul_of_nonneg_left hk (by dsimp [P];positivity)
       _ = _ := by dsimp only [P,s,rieszMobiusPolynomial];ring

/-- A nonzero Mellin integral bounded pointwise by a translated majorant
forces the corresponding convolution to be large on every sufficiently
large symmetric height interval. -/
theorem eventually_convolution_large_of_integral {F : ℝ→ℂ} {G : ℝ→ℝ} {a : ℂ} {B γ : ℝ}
    (hG : Continuous G) (hpt : ∀ v : ℝ,‖F v‖≤B*G (v+γ))
    (hlarge : 1/4≤‖a*(∫ v : ℝ,F v)‖) :
    ∀ᶠ R : ℝ in atTop,1/8≤‖a‖*B*(∫ t in -R..R,G t) := by
  have hi : Integrable F := by
    by_contra h;rw [integral_undef h,mul_zero,norm_zero] at hlarge;norm_num at hlarge
  have hminus : Tendsto (fun R : ℝ => -R-γ) atTop atBot := tendsto_atBot.mpr fun b =>
    (eventually_ge_atTop (-b-γ)).mono (fun R hr => by linarith)
  have hplus : Tendsto (fun R : ℝ => R-γ) atTop atTop := tendsto_atTop.mpr fun b =>
    (eventually_ge_atTop (b+γ)).mono (fun R hr => by linarith)
  have hl := (intervalIntegral_tendsto_integral hi.norm hminus hplus).const_mul ‖a‖
  have htotal := mul_le_mul_of_nonneg_left (show ‖∫ v : ℝ,F v‖≤∫ v : ℝ,‖F v‖ from norm_integral_le_integral_norm F) (norm_nonneg a)
  rw [norm_mul] at hlarge
  have hpos : 1/8<‖a‖*(∫ v : ℝ,‖F v‖) := by linarith only [hlarge,htotal]
  filter_upwards [hl.eventually_const_le hpos,eventually_ge_atTop (0:ℝ)] with R hR hR'
  apply hR.trans
  have hm := intervalIntegral.integral_mono_on (by linarith : -R-γ≤R-γ)
    (hi.norm.intervalIntegrable) ((continuous_const.mul (hG.comp (continuous_id.add_const γ))).intervalIntegrable ..)
    (fun v _ => hpt v)
  change (∫ v in -R-γ..R-γ,‖F v‖)≤∫v in -R-γ..R-γ,B*G (v+γ) at hm
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_right,sub_add_cancel,sub_add_cancel] at hm
  exact (mul_le_mul_of_nonneg_left hm (norm_nonneg a)).trans_eq (mul_assoc ..).symm

end AnalyticNumberTheory.RiemannZeta
