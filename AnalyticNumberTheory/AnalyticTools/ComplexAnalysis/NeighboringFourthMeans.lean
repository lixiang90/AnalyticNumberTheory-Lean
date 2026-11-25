import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.CauchyFourthMeans

/-! # Derivative fourth moments from neighboring vertical lines -/

open Real Complex Metric Set Finset MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private theorem circle_real_displacement {σ r : ℝ} {z : ℂ} (t : ℝ)
    (hz : z∈closedBall ((σ:ℂ)+t*I) r) : |z.re-σ|≤r := by
  have hh := (Complex.abs_re_le_norm (z-((σ:ℂ)+t*I))).trans (by simpa [Complex.dist_eq] using hz)
  simpa using hh

private theorem circle_center_coordinates (σ r t θ : ℝ) :
    circleMap ((σ:ℂ)+t*I) r θ =
      ((σ+(circleMap 0 r θ).re:ℝ):ℂ)+((t+(circleMap 0 r θ).im:ℝ):ℂ)*I := by
  have hh := circleMap_sub_center ((σ:ℂ)+t*I) r θ
  rw [←Complex.re_add_im (circleMap 0 r θ)] at hh
  push_cast;linear_combination hh

private theorem circle_fourth_integral_le_window {f : ℂ→ℂ} {σ r T : ℝ} (hr : 0<r) (hrT : r≤T) (θ : ℝ)
    (hf : Continuous (fun t : ℝ => f (((σ+(circleMap 0 r θ).re:ℝ):ℂ)+t*I))) :
    (∫ t in -T..T,‖f (circleMap ((σ:ℂ)+t*I) r θ)‖^4)≤
      ∫ t in -(2*T)..2*T,‖f (((σ+(circleMap 0 r θ).re:ℝ):ℂ)+t*I)‖^4 := by
  let v := circleMap 0 r θ
  let g (t : ℝ) := ‖f (((σ+v.re:ℝ):ℂ)+t*I)‖^4
  have him : |v.im|≤r := (Complex.abs_im_le_norm v).trans_eq (by dsimp [v];rw [norm_circleMap_zero,abs_of_pos hr])
  have hg : Continuous g := hf.norm.pow 4
  simp_rw [circle_center_coordinates]
  change (∫ t in -T..T,g (t+v.im))≤∫ t in -(2*T)..2*T,g t
  rw [intervalIntegral.integral_comp_add_right]
  exact intervalIntegral.integral_mono_interval (by linarith [(abs_le.mp him).1]) (by linarith) (by linarith [(abs_le.mp him).2])
    (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) (hg.intervalIntegrable ..)

private theorem continuous_vertical_line_of_analytic {f : ℂ→ℂ} {u : ℝ}
    (hf : ∀ z : ℂ,z.re=u → AnalyticAt ℂ f z) :
    Continuous (fun t : ℝ => f ((u:ℂ)+t*I)) :=
  continuous_iff_continuousAt.mpr fun t => (hf ((u:ℂ)+t*I) (by simp)).continuousAt.comp
    (f:=fun t : ℝ => (u:ℂ)+t*I) (by fun_prop)

private theorem continuous_circle_fourth_of_analytic {f : ℂ→ℂ} {σ r : ℝ} (hr : 0<r)
    (hf : ∀ z : ℂ,|z.re-σ|≤r → AnalyticAt ℂ f z) :
    Continuous (fun x : ℝ×ℝ => ‖f (circleMap ((σ:ℂ)+x.1*I) r x.2)‖^4) := by
  let P (x : ℝ×ℝ) := circleMap ((σ:ℂ)+x.1*I) r x.2
  have hP : Continuous P := by dsimp [P,circleMap];fun_prop
  have hc : Continuous (fun x => f (P x)) := continuous_iff_continuousAt.mpr fun x =>
    (hf (P x) (circle_real_displacement x.1 (sphere_subset_closedBall (circleMap_mem_sphere _ hr.le _)))).continuousAt.comp hP.continuousAt
  exact hc.norm.pow 4

/-- The derivative mean on a symmetric height interval is controlled by
the joint fourth means of the original family on the neighboring lines.
The angular shift enlarges the height interval by at most a factor of two. -/
theorem family_deriv_fourth_le_of_neighboring_lines {ι : Type*} (S : Finset ι) (f : ι→ℂ→ℂ)
    {σ r T M : ℝ} (hr : 0<r) (hrT : r≤T)
    (hf : ∀ i∈S,∀ z : ℂ,|z.re-σ|≤r → AnalyticAt ℂ (f i) z)
    (hM : ∀ u : ℝ,|u-σ|≤r → (∑i∈S,∫ t in -(2*T)..2*T,‖f i ((u:ℂ)+t*I)‖^4)≤M) :
    (∑i∈S,∫ t in -T..T,‖deriv (f i) ((σ:ℂ)+t*I)‖^4)≤M/r^4 := by
  refine family_deriv_fourth_le_of_circle_means (σ:=σ) (r:=r) (a:=-T) (b:=T) (M:=M) S f hr (by linarith) ?_ ?_ ?_ ?_
  · exact fun i hi t _ z hz => (hf i hi z (circle_real_displacement t hz)).differentiableAt.differentiableWithinAt
  · intro i hi
    apply continuous_vertical_line_of_analytic;intro z hz
    apply AnalyticAt.deriv
    exact hf i hi z (by simpa [hz] using hr.le)
  · exact fun i hi => continuous_circle_fourth_of_analytic hr (hf i hi)
  · intro θ _
    let v := circleMap 0 r θ
    have hre : |v.re|≤r := (Complex.abs_re_le_norm v).trans_eq (by dsimp [v];rw [norm_circleMap_zero,abs_of_pos hr])
    have hσ : |σ+v.re-σ|≤r := by simpa using hre
    have hline (i) (hi : i∈S) : Continuous (fun t : ℝ => f i (((σ+v.re:ℝ):ℂ)+t*I)) :=
      continuous_vertical_line_of_analytic (fun z hz => hf i hi z (hz ▸ hσ))
    exact (Finset.sum_le_sum (fun i hi => circle_fourth_integral_le_window hr hrT θ (hline i hi))).trans (hM (σ+v.re) hσ)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
