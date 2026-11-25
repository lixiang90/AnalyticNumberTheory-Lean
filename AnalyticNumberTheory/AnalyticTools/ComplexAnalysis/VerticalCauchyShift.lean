import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalLineShift

/-!
# Cauchy inversion between unequal vertical abscissae
-/

open Complex Real Set MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private theorem verticalCauchyIntegral_eq_away {F : ℂ → ℂ} {a b δ D : ℝ} (hab : a≤b)
    (hδ : 0<δ) (hdist : ∀ x∈Icc a b, δ≤|x|)
    (hF : ∀ z : ℂ, z.re∈Icc a b → AnalyticAt ℂ F z) (hD : 0≤D)
    (hbound : ∀ x∈Icc a b, ∀ t : ℝ, ‖F ((x:ℂ)+t*I)‖≤D/(1+t^2)) :
    verticalCauchyIntegral F a = verticalCauchyIntegral F b := by
  apply integral_verticalLine_eq_of_strip (F:=fun z => F z/z) hab
  · intro z hz
    have hnorm := (hdist z.re hz).trans (Complex.abs_re_le_norm z)
    exact ((hF z hz).differentiableAt.div differentiableAt_id
      (norm_pos_iff.mp (hδ.trans_le hnorm))).differentiableWithinAt
  · exact div_nonneg hD hδ.le
  · intro x hx t
    have hnorm : δ≤‖(x:ℂ)+t*I‖ := (hdist x hx).trans (by simpa using Complex.abs_re_le_norm ((x:ℂ)+t*I))
    rw [norm_div]
    exact (div_le_div₀ (by positivity) (hbound x hx t) hδ hnorm).trans_eq (by ring)

/-- Moving the Cauchy integral from a positive to a negative abscissa
crosses a single pole with residue `F 0`. -/
theorem verticalCauchyIntegral_sub {F : ℂ → ℂ} {a b D : ℝ} (ha : a<0) (hb : 0<b)
    (hF : ∀ z : ℂ, z.re∈Icc a b → AnalyticAt ℂ F z) (hD : 0≤D)
    (hbound : ∀ x∈Icc a b, ∀ t : ℝ, ‖F ((x:ℂ)+t*I)‖≤D/(1+t^2)) :
    verticalCauchyIntegral F b - verticalCauchyIntegral F a = 2*π*F 0 := by
  let c := min (-a) b
  have hc : 0<c := lt_min (neg_pos.mpr ha) hb
  have hca : a ≤ -c := by dsimp [c];linarith only [min_le_left (-a) b]
  have hcb : c ≤ b := min_le_right ..
  have he (u v : ℝ) (hu : a≤u) (hv : v≤b) (huv : u≤v) (hs : ∀ x∈Icc u v, c≤|x|) :=
    verticalCauchyIntegral_eq_away huv hc hs (fun z hz => hF z ⟨hu.trans hz.1,hz.2.trans hv⟩)
      hD (fun x hx => hbound x ⟨hu.trans hx.1,hx.2.trans hv⟩)
  have hl := he a (-c) le_rfl (by linarith) hca (fun x hx => by linarith [hx.2,neg_le_abs x])
  have hr := he c b (by linarith) le_rfl hcb (fun x hx => hx.1.trans (le_abs_self x))
  rw [← hr,hl]
  exact verticalCauchyIntegral_sub_neg
    (fun z hz => hF z ⟨hca.trans hz.1,hz.2.trans hcb⟩) hc hD
    (fun x hx => hbound x ⟨hca.trans hx.1,hx.2.trans hcb⟩)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
