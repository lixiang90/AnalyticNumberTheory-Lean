import AnalyticNumberTheory.AnalyticTools.FourierBromwich
import AnalyticNumberTheory.AnalyticTools.LocalJordanDecomposition
import AnalyticNumberTheory.AnalyticTools.StieltjesFunctionInversion

/-! # The Dirichlet–Jordan midpoint in one-sided Laplace inversion -/

noncomputable section
open MeasureTheory Filter Set Function Complex
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private lemma integrable_monotone_model {p : ℝ → ℝ} {b σ : ℝ} (hσ : 0 < σ)
    (hp : Monotone p) (hneg : ∀ t < 0, p t = 0) (hstop : ∀ t, b ≤ t → p t = p b) :
    Integrable (laplaceDamped σ (fun u : ℝ => (p u : ℂ))) := by
  apply integrable_laplaceDamped_of_bounded (B := p b) hσ
    (Complex.continuous_ofReal.measurable.comp hp.measurable).aestronglyMeasurable
  intro u hu
  have hpos : 0 ≤ p u := (hneg (-1) (by norm_num)) ▸ hp (show -1 ≤ u by linarith)
  change ‖(p u : ℂ)‖ ≤ p b
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  rcases le_total u b with h | h
  · exact hp h
  · exact (hstop u h).le

private lemma midpoint_of_local_difference {f p q : ℝ → ℝ} {σ x b : ℝ}
    (hσ : 0 < σ) (hf : Integrable (laplaceDamped σ (fun t : ℝ => (f t : ℂ))))
    (hp : Monotone p) (hq : Monotone q)
    (hneg : ∀ t < 0, p t = 0 ∧ q t = 0) (hstop : ∀ t, b ≤ t → p t = p b ∧ q t = q b)
    (he : f =ᶠ[𝓝 x] (p-q)) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (f t : ℂ))) σ x)
      atTop (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  let P (u : ℝ) : ℂ := p u
  let Q (u : ℝ) : ℂ := q u
  have hP := integrable_monotone_model hσ hp (fun t ht => (hneg t ht).1) (fun t ht => (hstop t ht).1)
  have hQ := integrable_monotone_model hσ hq (fun t ht => (hneg t ht).2) (fun t ht => (hstop t ht).2)
  have hd : laplaceDamped σ (P-Q) = laplaceDamped σ P - laplaceDamped σ Q := by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ) <;> simp [laplaceDamped, hu, mul_sub]
  have hPQ : Integrable (laplaceDamped σ (P-Q)) := hd ▸ hP.sub hQ
  have near := truncatedBromwich_localization (x := x) hf hPQ (he.mono fun u hu _ => by
    change (f u : ℂ) = (p u : ℂ) - (q u : ℂ)
    rw [hu]; exact Complex.ofReal_sub ..)
  have hpTop : Tendsto p atTop (𝓝 (p b)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop b).mono fun t ht => (hstop t ht).1.symm)
  have hqTop : Tendsto q atTop (𝓝 (q b)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop b).mono fun t ht => (hstop t ht).2.symm)
  have hpLim := laplace_monotone_inversion hp (fun t ht => (hneg t ht).1) hpTop hσ x
  have hqLim := laplace_monotone_inversion hq (fun t ht => (hneg t ht).2) hqTop hσ x
  have model := (hpLim.sub hqLim).congr (fun T => (truncatedBromwich_laplace_sub hP hQ x T).symm)
  have hl : leftLim f x = leftLim p x - leftLim q x := leftLim_eq_of_tendsto
    (((hp.tendsto_leftLim x).sub (hq.tendsto_leftLim x)).congr' (he.filter_mono nhdsWithin_le_nhds).symm)
  have hr : rightLim f x = rightLim p x - rightLim q x := rightLim_eq_of_tendsto
    (((hp.tendsto_rightLim x).sub (hq.tendsto_rightLim x)).congr' (he.filter_mono nhdsWithin_le_nhds).symm)
  have H := near.add model
  simp only [P, Q, sub_add_cancel, zero_add] at H
  convert H using 2
  rw [hl, hr]
  push_cast
  ring

/-- Inversion at a positive point of a real function of bounded variation on
a neighborhood. The damped input must be integrable on the positive half-line. -/
theorem laplace_inversion_boundedVariation_pos {f : ℝ → ℝ} {a x b σ : ℝ}
    (ha : 0 ≤ a) (hax : a < x) (hxb : x < b) (hv : BoundedVariationOn f (Icc a b))
    (hσ : 0 < σ) (hf : Integrable (laplaceDamped σ (fun t : ℝ => (f t : ℂ)))) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (f t : ℂ))) σ x)
      atTop (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  obtain ⟨p,q,hp,hq,hneg,hstop,he⟩ := exists_monotone_extensions_of_boundedVariation (hax.trans hxb).le hv
  apply midpoint_of_local_difference hσ hf hp hq (fun t ht => hneg t (ht.trans_le ha)) hstop
  filter_upwards [Ioo_mem_nhds hax hxb] with u hu using he (Ioo_subset_Icc_self hu)

/-- At the origin, the one-sided transform recovers half the right limit,
regardless of the value assigned to f at zero or to the left of zero. -/
theorem laplace_inversion_boundedVariation_zero {f : ℝ → ℝ} {b σ : ℝ} (hb : 0 < b)
    (hv : BoundedVariationOn f (Icc 0 b)) (hσ : 0 < σ)
    (hf : Integrable (laplaceDamped σ (fun t : ℝ => (f t : ℂ)))) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (f t : ℂ))) σ 0)
      atTop (𝓝 (((rightLim f 0 : ℝ) : ℂ) / 2)) := by
  obtain ⟨p,q,hp,hq,hneg,hstop,he⟩ := exists_monotone_extensions_of_boundedVariation hb.le hv
  let g := (Ici (0 : ℝ)).indicator f
  have hext (u : ℝ) (hu : 0 ≤ u) : g u = f u := indicator_of_mem hu _
  have hneg₀ (u : ℝ) (hu : u < 0) : g u = 0 := indicator_of_notMem (by simpa using hu) _
  have hnear : g =ᶠ[𝓝 0] p-q := by
    filter_upwards [gt_mem_nhds hb] with u hu
    rcases lt_or_ge u 0 with h | h
    · simp [hneg₀ u h, (hneg u h).1, (hneg u h).2]
    · exact (hext u h).trans (he ⟨h,hu.le⟩)
  have hD : laplaceDamped σ (fun u : ℝ => (g u : ℂ)) = laplaceDamped σ (fun u : ℝ => (f u : ℂ)) := by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · simp [laplaceDamped, hu, hext u (le_of_lt hu)]
    · simp [laplaceDamped, hu]
  have hF : laplaceTransform (fun u : ℝ => (g u : ℂ)) = laplaceTransform (fun u : ℝ => (f u : ℂ)) := by
    apply laplaceTransform_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with u hu
    exact congrArg Complex.ofReal (hext u (le_of_lt hu))
  have hleft : leftLim g 0 = 0 := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu using (hneg₀ u hu).symm
  have hright : rightLim g 0 = rightLim f 0 := by
    have hg := ((hp.tendsto_rightLim 0).sub (hq.tendsto_rightLim 0)).congr'
      (hnear.filter_mono nhdsWithin_le_nhds).symm
    have heq : g =ᶠ[𝓝[>] 0] f := by
      filter_upwards [self_mem_nhdsWithin] with u hu using hext u (le_of_lt hu)
    rw [rightLim_eq_of_tendsto hg, rightLim_eq_of_tendsto (hg.congr' heq)]
  have H := midpoint_of_local_difference hσ (hD ▸ hf) hp hq hneg hstop hnear
  simpa only [hF, hleft, hright, Complex.ofReal_zero, zero_add] using H

end AnalyticNumberTheory.AnalyticTools
