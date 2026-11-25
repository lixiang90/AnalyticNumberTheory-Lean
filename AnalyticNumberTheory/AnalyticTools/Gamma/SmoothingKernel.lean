import AnalyticNumberTheory.AnalyticTools.Gamma.MellinInversion
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalCauchyShift

/-!
# Moving the exponential smoothing kernel across its first pole

Multiplication by Gamma turns polynomial growth on a vertical strip into
rapid decay. Crossing zero contributes exactly the value of the analytic
factor at zero.
-/

open Complex Real Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.AnalyticTools

/-- The normalized integral of `H(w) Γ(w) X^w` on the vertical line of real part `c`. -/
noncomputable def gammaSmoothingIntegral (H : ℂ → ℂ) (X c : ℝ) : ℂ :=
  (2*(π:ℂ))⁻¹ * ∫ t : ℝ, H ((c:ℂ)+t*I) * Complex.Gamma ((c:ℂ)+t*I) * (X:ℂ)^((c:ℂ)+t*I)

/-- Integrability on a vertical line for the contour numerator after removing
the first pole of Gamma. -/
theorem gamma_smoothing_bound {l r X A : ℝ} (hl : -1<l) (hlr : l≤r)
    (hX : 0<X) (m : ℕ) {H : ℂ → ℂ} (hA : 0≤A)
    (hH : ∀ z : ℂ, z.re∈Icc l r → ‖H z‖ ≤ A*(1+|z.im|)^m) :
    ∃ D : ℝ, 0≤D ∧ ∀ x∈Icc l r, ∀ t : ℝ,
      let z := (x:ℂ)+t*I
      ‖H z*Complex.Gamma (z+1)*(X:ℂ)^z‖ ≤ D/(1+t^2) := by
  obtain ⟨C,hC,hg⟩ := norm_Gamma_positive_strip_weight (a:=l+1) (b:=r+1)
    (by linarith) (by linarith) (m+2)
  let B := max (X^l) (X^r)
  have hB : 0≤B := (Real.rpow_nonneg hX.le _).trans (le_max_left ..)
  refine ⟨A*C*B,by positivity,?_⟩
  intro x hx t
  let z := (x:ℂ)+t*I
  have hz : z.re=x := by simp [z]
  have hi : z.im=t := by simp [z]
  have hpow : ‖(X:ℂ)^z‖ ≤ B := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX,hz]
    rcases le_total 1 X with H|H
    · exact (Real.rpow_le_rpow_of_exponent_le H hx.2).trans (le_max_right ..)
    · exact (Real.rpow_le_rpow_of_exponent_ge hX H hx.1).trans (le_max_left ..)
  have hg' := hg (z+1) (by simp [hz];exact hx)
  simp only [Complex.add_im,Complex.one_im,add_zero,hi,pow_add] at hg'
  have hσ := hH z (hz ▸ hx)
  rw [hi] at hσ
  change ‖H z*Complex.Gamma (z+1)*(X:ℂ)^z‖≤_
  rw [norm_mul,norm_mul,le_div_iff₀ (by positivity)]
  have hquad : 1+t^2≤(1+|t|)^2 := by nlinarith only [abs_nonneg t,sq_abs t]
  calc
    _ ≤ (A*(1+|t|)^m)*‖Complex.Gamma (z+1)‖*B*(1+|t|)^2 := by gcongr
    _ = A*((1+|t|)^m*(1+|t|)^2*‖Complex.Gamma (z+1)‖)*B := by ring
    _ ≤ _ := by gcongr

/-- Moving the exponential smoothing contour over zero contributes `H 0`. -/
theorem gammaSmoothingIntegral_sub {l r X A : ℝ} (hl : -1<l) (hl0 : l<0) (hr : 0<r)
    (hX : 0<X) (m : ℕ) {H : ℂ → ℂ} (hA : 0≤A)
    (ha : ∀ z : ℂ, z.re∈Icc l r → AnalyticAt ℂ H z)
    (hH : ∀ z : ℂ, z.re∈Icc l r → ‖H z‖ ≤ A*(1+|z.im|)^m) :
    gammaSmoothingIntegral H X r - gammaSmoothingIntegral H X l = H 0 := by
  let F (z : ℂ) := H z*Complex.Gamma (z+1)*(X:ℂ)^z
  have hX' : (X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hf (z : ℂ) (hz : z.re∈Icc l r) : AnalyticAt ℂ F z := by
    have hpos : 0<(z+1).re := by simp;linarith [hz.1]
    have han : AnalyticAt ℂ Complex.Gamma (z+1) := by
      apply (analyticAt_iff_eventually_differentiableAt).mpr
      filter_upwards [(isOpen_lt (f:=fun _ : ℂ => (0:ℝ)) continuous_const Complex.continuous_re).mem_nhds hpos] with w hw
      apply Complex.differentiableAt_Gamma
      intro k he; rw [he] at hw; simp at hw; linarith [Nat.cast_nonneg (α:=ℝ) k]
    have hshift : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
    have hpow : AnalyticAt ℂ (fun w : ℂ => (X:ℂ)^w) z :=
      (show Differentiable ℂ (fun w : ℂ => (X:ℂ)^w) from differentiable_id.const_cpow (.inl hX')).analyticAt z
    exact ((ha z hz).mul (han.comp (f:=fun w : ℂ => w+1) hshift)).mul hpow
  obtain ⟨D,hD,hd⟩ := gamma_smoothing_bound hl (by linarith : l≤r) hX m hA hH
  have C := verticalCauchyIntegral_sub hl0 hr hf hD hd
  have he (u : ℝ) (hu : u≠0) : gammaSmoothingIntegral H X u = (2*(π:ℂ))⁻¹*verticalCauchyIntegral F u := by
    unfold gammaSmoothingIntegral verticalCauchyIntegral;congr 1
    apply integral_congr_ae;filter_upwards with t
    let z := (u:ℂ)+t*I
    have hn : z ≠ 0 := by intro h; apply hu;simpa [z] using congrArg Complex.re h
    change H z*Complex.Gamma z*(X:ℂ)^z = F z/z
    dsimp only [F];rw [Complex.Gamma_add_one _ hn];field_simp
  rw [he r hr.ne',he l hl0.ne,←mul_sub,C]
  simp [F,Real.pi_ne_zero,field]

end AnalyticNumberTheory.AnalyticTools
