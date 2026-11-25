import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaWeights
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleIntegrals

/-!
# Norm estimates for finite Perron contours

All bounds use the actual lengths of the segments. Along a vertical edge,
the denominator is integrated to give a logarithm.
-/

noncomputable section

open Complex MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Vertical edge with its real parameter measure. -/
def perronVertical (F : ℂ → ℂ) (σ T : ℝ) : ℂ := ∫ t in (-T)..T, F ((σ:ℂ)+t*I)

/-- Horizontal edge with its real parameter measure. -/
def perronHorizontal (F : ℂ → ℂ) (a b t : ℝ) : ℂ := ∫ u in a..b, F ((u:ℂ)+t*I)

/-- Estimating the right edge from a specified contour integral. -/
theorem norm_perronVertical_of_boundary {F : ℂ → ℂ} {a b T : ℝ} {W : ℂ}
    (h : rectangleBoundary F ⟨a,-T⟩ ⟨b,T⟩ = W) :
    ‖perronVertical F b T‖≤‖W‖+‖perronVertical F a T‖+
      ‖perronHorizontal F a b T‖+‖perronHorizontal F a b (-T)‖ := by
  change perronHorizontal F a b (-T)-perronHorizontal F a b T+
    I*perronVertical F b T-I*perronVertical F a T=W at h
  have he : I*perronVertical F b T=W+I*perronVertical F a T+
      perronHorizontal F a b T-perronHorizontal F a b (-T) := by linear_combination h
  have H := congrArg norm he
  simp only [norm_mul,Complex.norm_I,one_mul] at H
  rw [H]
  calc
    _ ≤ ‖W+I*perronVertical F a T+perronHorizontal F a b T‖+‖perronHorizontal F a b (-T)‖ := norm_sub_le _ _
    _ ≤ _ := by
      have h₁ := norm_add_le (W+I*perronVertical F a T) (perronHorizontal F a b T)
      have h₂ := norm_add_le W (I*perronVertical F a T)
      rw [norm_mul,Complex.norm_I,one_mul] at h₂
      linarith

private theorem integral_perron_envelope {T : ℝ} (hT : 0≤T) :
    (∫ t : ℝ in (-T)..T, 1/(1+|t|)) = 2*Real.log (1+T) := by
  let w (t : ℝ) := 1/(1+|t|)
  have hw : Continuous w := continuous_const.div (continuous_const.add continuous_abs) (fun t => ne_of_gt (by linarith [abs_nonneg t] : 0<1+|t|))
  have he : (∫ t in (-T)..0,w t) = ∫ t in (0:ℝ)..T,w t := by
    have h := intervalIntegral.integral_comp_neg (f:=w) (a:=0) (b:=T)
    simpa [w] using h.symm
  have h₀ : (∫ t in (0:ℝ)..T,w t) = Real.log (1+T) := by
    have hh (t : ℝ) (ht : t∈uIcc 0 T) : HasDerivAt (fun t : ℝ => Real.log (1+t)) (w t) t := by
      rw [uIcc_of_le hT] at ht
      have hd := (Real.hasDerivAt_log (by linarith [ht.1] : 1+t≠0)).comp t ((hasDerivAt_id t).const_add 1)
      simpa [w,abs_of_nonneg ht.1,one_div,Function.comp_def] using! hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hh (hw.intervalIntegrable ..)]
    simp
  change (∫ t in (-T)..T,w t)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable (-T) 0) (hw.intervalIntegrable 0 T),he,h₀]
  ring

private theorem norm_vertical_of_envelope {F : ℂ → ℂ} {T σ B : ℝ} (hT : 0≤T) (hB : 0≤B)
    (h : ∀ t∈Icc (-T) T, ‖F ((σ:ℂ)+t*I)‖≤B/(1+|t|)) :
    ‖perronVertical F σ T‖ ≤ 2*B*Real.log (1+T) := by
  unfold perronVertical
  by_cases hI : IntervalIntegrable (fun t : ℝ => F ((σ:ℂ)+t*I)) volume (-T) T
  · apply (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans
    calc
      _ ≤ ∫ t in (-T)..T,B*(1/(1+|t|)) := by
        apply intervalIntegral.integral_mono_on (by linarith) hI.norm
        · apply Continuous.intervalIntegrable
          exact continuous_const.mul (continuous_const.div (continuous_const.add continuous_abs) (fun t => ne_of_gt (by linarith [abs_nonneg t] : 0<1+|t|)))
        · intro t ht; simpa [div_eq_mul_inv] using h t ht
      _ = _ := by rw [intervalIntegral.integral_const_mul,integral_perron_envelope hT]; ring
  · rw [intervalIntegral.integral_undef hI,norm_zero]
    positivity [Real.log_nonneg (by linarith : 1≤1+T)]

private theorem perron_vertical_norm_denom {σ t : ℝ} (hσ : 1/2≤|σ|) :
    1+|t|≤3*‖(σ:ℂ)+t*I‖ := by
  have ha := Complex.abs_re_le_norm ((σ:ℂ)+t*I)
  have hb := Complex.abs_im_le_norm ((σ:ℂ)+t*I)
  simp at ha hb
  linarith

theorem norm_perronVertical_div {F : ℂ → ℂ} {T σ B : ℝ} (hT : 0≤T) (hσ : 1/2≤|σ|)
    (hB : 0≤B) (h : ∀ t∈Icc (-T) T, ‖F ((σ:ℂ)+t*I)‖≤B) :
    ‖perronVertical (fun s => F s/s) σ T‖ ≤ 6*B*Real.log (1+T) := by
  have H := norm_vertical_of_envelope (F:=fun s => F s/s) (σ:=σ) hT (show 0≤3*B by positivity) (by
    intro t ht
    have hd := perron_vertical_norm_denom (t:=t) hσ
    have hd' : 0<‖(σ:ℂ)+t*I‖ := by linarith [abs_nonneg t]
    rw [norm_div]
    apply (div_le_div_of_nonneg_right (h t ht) hd'.le).trans
    rw [div_le_div_iff₀ hd' (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hd hB])
  linarith

theorem norm_perronVertical_weight {F : ℂ → ℂ} {T σ B x : ℝ} (hx : 0<x)
    (hT : 0≤T) (hσ : 1/2≤|σ|) (hB : 0≤B)
    (h : ∀ t∈Icc (-T) T, ‖F ((σ:ℂ)+t*I)‖≤B) :
    ‖perronVertical (fun s => perronDifferenceWeight x s*F s) σ T‖ ≤
      6*((x^σ+1)*B)*Real.log (1+T) := by
  let G (s : ℂ) := ((x:ℂ)^s-1)*F s
  have he (t : ℝ) : perronDifferenceWeight x ((σ:ℂ)+t*I)*F ((σ:ℂ)+t*I) =
      G ((σ:ℂ)+t*I)/((σ:ℂ)+t*I) := by
    have hd := perron_vertical_norm_denom (t:=t) hσ
    rw [perronDifferenceWeight_eq hx (norm_pos_iff.mp (by linarith [abs_nonneg t]))]
    dsimp only [G]; ring
  unfold perronVertical
  simp_rw [he]
  apply norm_perronVertical_div hT hσ (by positivity)
  intro t ht
  unfold G
  rw [norm_mul]
  apply mul_le_mul _ (h t ht) (norm_nonneg _) (by positivity)
  have hh := norm_sub_le ((x:ℂ)^((σ:ℂ)+t*I)) 1
  simpa [Complex.norm_cpow_eq_rpow_re_of_pos hx] using hh

theorem norm_perronHorizontal_weight {F : ℂ → ℂ} {a b t B x : ℝ} (hx : 1≤x)
    (hab : a≤b) (ht : t≠0) (_hB : 0≤B) (h : ∀ u∈Icc a b, ‖F ((u:ℂ)+t*I)‖≤B) :
    ‖perronHorizontal (fun s => perronDifferenceWeight x s*F s) a b t‖ ≤
      (b-a)*((x^b+1)/abs t*B) := by
  have hxp : 0<x := by linarith
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (C:=(x^b+1)/abs t*B) _).trans_eq
  · rw [abs_of_nonneg (sub_nonneg.mpr hab),mul_comm]
  · intro u hu
    rw [Set.uIoc_of_le hab] at hu
    let s := (u:ℂ)+t*I
    have he : s.im=t := by simp [s]
    have hd : |t|≤‖s‖ := by simpa only [he] using Complex.abs_im_le_norm s
    have htp := abs_pos.mpr ht
    have hp := norm_sub_le ((x:ℂ)^s) 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp,show s.re=u by simp [s],norm_one] at hp
    change ‖perronDifferenceWeight x s*F s‖≤_
    rw [norm_mul,perronDifferenceWeight_eq hxp (norm_pos_iff.mp (htp.trans_le hd)),norm_div]
    apply mul_le_mul _ (h u ⟨hu.1.le,hu.2⟩) (norm_nonneg _) (by positivity)
    exact div_le_div₀ (by positivity) (hp.trans (add_le_add_left (Real.rpow_le_rpow_of_exponent_le hx hu.2) _)) htp hd

end AnalyticNumberTheory.DirichletLFunctions
