import AnalyticNumberTheory.AnalyticTools.LaplaceJordanInversion

/-! # Symmetric Fourier inversion at a point of locally bounded variation -/

noncomputable section
open MeasureTheory Filter Set Function Complex
open scoped FourierTransform Topology

namespace AnalyticNumberTheory.AnalyticTools

private lemma positive_fourier_jordan {f : ℝ → ℝ} {a x b : ℝ} (hf : Integrable f)
    (ha : 0 ≤ a) (hax : a < x) (hxb : x < b) (hv : BoundedVariationOn f (Icc a b)) :
    Tendsto (truncatedFourierInverse (fun t : ℝ => (f t : ℂ)) x) atTop
      (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  let F (u : ℝ) : ℂ := f u
  have hD : laplaceDamped 0 F = (Ioi (0 : ℝ)).indicator F := by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ) <;> simp [laplaceDamped, hu]
  have hi : Integrable (laplaceDamped 0 F) := by
    rw [hD]
    exact (hf.ofReal.integrableOn).integrable_indicator measurableSet_Ioi
  have he : F =ᶠ[𝓝 x] laplaceDamped 0 F := by
    rw [hD]
    filter_upwards [lt_mem_nhds (ha.trans_lt hax)] with u hu using (indicator_of_mem hu F).symm
  have hn := truncatedFourierInverse_localization (f := F) hf.ofReal hi x he
  have H := laplace_jordan_inversion (σ := 0) ha hax hxb hv hi
  have hc : 0 < 2 * Real.pi := by positivity
  have hscale : Tendsto (fun R : ℝ => R * (2 * Real.pi)) atTop atTop := tendsto_id.atTop_mul_const hc
  have hcut (R : ℝ) : truncatedBromwich (laplaceTransform F) 0 x (R * (2 * Real.pi)) =
      truncatedFourierInverse (laplaceDamped 0 F) x R := by
    rw [truncatedBromwich_eq_fourier]
    simp [hc.ne']
  have hp := (H.comp hscale).congr (fun R => hcut R)
  simpa only [sub_add_cancel, zero_add] using hn.add hp

private lemma translate_lt (s x : ℝ) :
    Tendsto (fun u : ℝ => u+s) (𝓝[<] (x-s)) (𝓝[<] x) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun u : ℝ => u+s) := by fun_prop
    simpa only [sub_add_cancel] using (hc.tendsto (x-s)).mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (x-s) ≤ 𝓝 (x-s))
  · filter_upwards [self_mem_nhdsWithin] with u (hu : u < x-s)
    exact (lt_sub_iff_add_lt).mp hu

private lemma translate_gt (s x : ℝ) :
    Tendsto (fun u : ℝ => u+s) (𝓝[>] (x-s)) (𝓝[>] x) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun u : ℝ => u+s) := by fun_prop
    simpa only [sub_add_cancel] using (hc.tendsto (x-s)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (x-s) ≤ 𝓝 (x-s))
  · filter_upwards [self_mem_nhdsWithin] with u (hu : x-s < u)
    exact (sub_lt_iff_lt_add).mp hu

/-- The Dirichlet–Jordan inversion theorem for the Fourier transform on the
real line. Only a compact neighborhood of the inversion point needs bounded
variation. No integrability of the transformed function is required. -/
theorem fourier_jordan_inversion {f : ℝ → ℝ} {a x b : ℝ} (hf : Integrable f)
    (hax : a < x) (hxb : x < b) (hv : BoundedVariationOn f (Icc a b)) :
    Tendsto (truncatedFourierInverse (fun t : ℝ => (f t : ℂ)) x) atTop
      (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  let s := a-1
  let g (u : ℝ) := f (u+s)
  have hg : Integrable g := (measurePreserving_add_right volume s).integrable_comp_of_integrable hf
  have hgvar : BoundedVariationOn g (Icc (a-s) (b-s)) := by
    apply ne_top_of_le_ne_top hv
    apply eVariationOn.comp_le_of_monotoneOn f (fun t : ℝ => t+s) (fun _ _ _ _ huv => by dsimp; linarith)
    intro t ht
    exact ⟨sub_le_iff_le_add.mp ht.1, le_sub_iff_add_le.mp ht.2⟩
  have hmem : Icc a b ∈ 𝓝 x := Icc_mem_nhds hax hxb
  obtain ⟨l, hl⟩ := hv.exists_tendsto_left x
  obtain ⟨r, hr⟩ := hv.exists_tendsto_right x
  rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hmem)] at hl hr
  have hL : leftLim g (x-s) = leftLim f x := by
    rw [leftLim_eq_of_tendsto hl]
    exact leftLim_eq_of_tendsto (hl.comp (translate_lt s x))
  have hR : rightLim g (x-s) = rightLim f x := by
    rw [rightLim_eq_of_tendsto hr]
    exact rightLim_eq_of_tendsto (hr.comp (translate_gt s x))
  have H := positive_fourier_jordan hg (by dsimp [s]; linarith : 0 ≤ a-s)
    (sub_lt_sub_right hax s) (sub_lt_sub_right hxb s) hgvar
  rw [hL, hR] at H
  apply H.congr
  intro R
  unfold truncatedFourierInverse
  simp [g, add_assoc]

end AnalyticNumberTheory.AnalyticTools
