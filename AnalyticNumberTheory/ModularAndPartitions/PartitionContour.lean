import AnalyticNumberTheory.ModularAndPartitions.PartitionFareyArcs
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Contours for Rademacher's rational arcs

The reciprocal substitution maps the horizontal Farey arc to a circle in the
right half-plane. A holomorphic primitive allows replacement of that path
by a vertical segment and horizontal segments joining the endpoints.
-/

open Complex Real Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.ModularAndPartitions

/-- A holomorphic function on the open right half-plane has a primitive there.
The Cayley transform transports the disk version of Cauchy's theorem. -/
theorem isExactOn_rightHalfPlane {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.re}) :
    Complex.IsExactOn f {w : ℂ | 0 < w.re} := by
  let H (z : ℂ) := (1+z)/(1-z)
  let V (w : ℂ) := (w-1)/(w+1)
  have hdisk {z : ℂ} (hz : z ∈ Metric.ball 0 1) : ‖z‖ < 1 := by simpa using hz
  have hden {z : ℂ} (hz : z ∈ Metric.ball 0 1) : 1-z ≠ 0 := by
    intro h
    rw [(sub_eq_zero.mp h).symm] at hz
    simp at hz
  have hhalf {z : ℂ} (hz : z ∈ Metric.ball 0 1) : 0 < (H z).re := by
    have hd := hdisk hz
    have hsq := sq_lt_sq' (by linarith [norm_nonneg z] : -(1:ℝ) < ‖z‖) hd
    rw [Complex.sq_norm, Complex.normSq_apply] at hsq
    have hn := Complex.normSq_pos.mpr (hden hz)
    dsimp [H]
    rw [Complex.div_re, ← add_div, div_pos_iff_of_pos_right hn]
    simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith only [hsq]
  have hVden {w : ℂ} (hw : 0 < w.re) : w+1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hV {w : ℂ} (hw : 0 < w.re) : V w ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [V]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hVden hw))]
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im,
      Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, add_zero]
    linarith only [hw]
  let F (z : ℂ) := f (H z)*(2/(1-z)^2)
  have hf' : DifferentiableOn ℂ F (Metric.ball 0 1) := by
    have hH : DifferentiableOn ℂ H (Metric.ball 0 1) := by
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      dsimp only [H]; fun_prop (disch := exact hden hz)
    apply (hf.comp hH (fun _ hz => hhalf hz)).mul
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := first | exact hden hz | exact pow_ne_zero _ (hden hz))
  obtain ⟨G,hG⟩ := hf'.isExactOn_ball
  refine ⟨fun w => G (V w), fun w hw => ?_⟩
  have hd := hVden hw
  have hdiff : HasDerivAt V (2/(w+1)^2) w := by
    convert ((hasDerivAt_id w).sub_const (1:ℂ)).div ((hasDerivAt_id w).add_const 1) hd using 1
    · rfl
    · dsimp; ring
  have h := (hG _ (hV hw)).comp w hdiff
  have hHV : H (V w) = w := by dsimp [H,V]; field_simp; ring
  dsimp only [F] at h
  rw [hHV] at h
  change HasDerivAt (G ∘ V) (f w) w
  convert h using 1
  dsimp [V]
  field_simp
  ring

/-- Vertical integration over a finite interval can be evaluated from any complex primitive. -/
theorem integral_vertical_eq_primitive {f g : ℂ → ℂ} (hg : ∀ w : ℂ, 0 < w.re → HasDerivAt g (f w) w)
    (hf : ContinuousOn f {w : ℂ | 0 < w.re}) {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    I * (∫ t in a..b, f (c+t*I)) = g (c+b*I)-g (c+a*I) := by
  let w (t : ℝ) : ℂ := c+t*I
  have hw (t : ℝ) : 0 < (w t).re := by simpa [w] using hc
  have hd (t : ℝ) : HasDerivAt (fun t => g (w t)) (I*f (w t)) t := by
    have he : HasDerivAt w I t := by
      simpa [w] using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (c:ℂ)
    simpa only [smul_eq_mul, Function.comp_def] using (hg (w t) (hw t)).scomp t he
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_const.mul (hf.comp (by dsimp [w]; fun_prop) (fun t _ => hw t))

private theorem norm_horizontal_primitive_le {f g : ℂ → ℂ}
    (hg : ∀ w : ℂ, 0 < w.re → HasDerivAt g (f w) w) (hf : ContinuousOn f {w : ℂ | 0 < w.re})
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ z : ℂ, 1/2 ≤ z.re → z.re ≤ 4 → ‖f z‖ ≤ D/(1+z.im^2))
    {w : ℂ} (hw : 1/2 ≤ w.re) (hw' : w.re ≤ 4) :
    ‖g w - g (1+w.im*I)‖ ≤ 3 * D/(1+w.im^2) := by
  let P (x : ℝ) := (x:ℂ)+w.im*I
  have hp (x : ℝ) : (P x).re = x := by simp [P]
  have hs {x : ℝ} (hx : x ∈ Set.uIcc 1 w.re) : 1/2 ≤ x ∧ x ≤ 4 :=
    ⟨(le_min (by norm_num) hw).trans hx.1, hx.2.trans (max_le (by norm_num) hw')⟩
  have hcont : ContinuousOn (fun x => f (P x)) (Set.uIcc 1 w.re) :=
    hf.comp (by dsimp [P]; fun_prop) (fun x hx => by change 0 < (P x).re; rw [hp]; linarith [(hs hx).1])
  have heq : (∫ x in 1..w.re, f (P x)) = g w-g (1+w.im*I) := by
    have ha : P 1 = 1+w.im*I := by simp [P]
    suffices he : (∫ x in (1:ℝ)..w.re, f (P x)) = g (P w.re)-g (P 1) by
      simpa only [ha, P, Complex.re_add_im] using he
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g ∘ P) _ hcont.intervalIntegrable
    intro x hx
    have hx' : 0 < (P x).re := by rw [hp]; linarith [(hs hx).1]
    have hd : HasDerivAt P 1 x := by simpa [P] using ((hasDerivAt_id x).ofReal_comp.add_const (w.im*I))
    simpa only [Function.comp_def, one_smul] using (hg (P x) hx').scomp x hd
  rw [← heq]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := D/(1+w.im^2)) ?_).trans
  · rw [show 3*D/(1+w.im^2) = D/(1+w.im^2)*3 by ring]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
  · intro x hx
    have hxs := hs (Set.uIoc_subset_uIcc hx)
    simpa [P] using hbound (P x) (by simpa only [hp] using hxs.1) (by simpa only [hp] using hxs.2)

private theorem norm_integral_bromwich_tail_le {F : ℝ → ℂ} (hi : Integrable F) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ t : ℝ, ‖F t‖ ≤ D/(1+t^2)) {a : ℝ} (ha : 0 < a) :
    ‖∫ t in Ioi a, F t‖ ≤ D/a := by
  apply (norm_integral_le_integral_norm _).trans
  calc _ ≤ ∫ t in Ioi a, D * t^(-(2:ℝ)) := by
             apply setIntegral_mono_on hi.norm.integrableOn
               ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(2:ℝ) < -1) ha).const_mul D) measurableSet_Ioi
             intro t ht
             apply (hbound t).trans
             rw [Real.rpow_neg (ha.trans ht).le, Real.rpow_two, ← div_eq_mul_inv]
             exact div_le_div_of_nonneg_left hD (pow_pos (ha.trans ht) _) (by linarith)
       _ = _ := by
             rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
             norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- Replacing a contour by the full vertical line costs at most the reciprocal
of each endpoint height when its kernel decays quadratically in the strip. -/
theorem norm_primitive_sub_verticalIntegral_le {f g : ℂ → ℂ}
    (hg : ∀ w : ℂ, 0 < w.re → HasDerivAt g (f w) w) (hf : ContinuousOn f {w : ℂ | 0 < w.re})
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ w : ℂ, 1/2 ≤ w.re → w.re ≤ 4 → ‖f w‖ ≤ D/(1+w.im^2))
    {l r : ℂ} (hl : 1/2 ≤ l.re) (hl' : l.re ≤ 4) (hr : 1/2 ≤ r.re) (hr' : r.re ≤ 4)
    (hlt : l.im < 0) (hrt : 0 < r.im) :
    ‖(g r-g l) - I*(∫ t : ℝ, f (1+t*I))‖ ≤ 4*D*(1/(-l.im)+1/r.im) := by
  let F (t : ℝ) := f (1+t*I)
  have hF (t : ℝ) : ‖F t‖ ≤ D/(1+t^2) := by simpa [F] using hbound (1+t*I) (by norm_num) (by norm_num)
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun t =>
    ContinuousAt.comp (f := fun t : ℝ => (1:ℂ)+t*I)
      (hf.continuousAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp))) (by fun_prop)
  have hi : Integrable F := (integrable_inv_one_add_sq.const_mul D).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun t => by simpa [div_eq_mul_inv] using hF t)
  let left := ∫ t in Iic l.im, F t
  let right := ∫ t in Ioi r.im, F t
  have heq : left + (∫ t in l.im..r.im, F t) + right = ∫ t : ℝ, F t := by
    dsimp [left, right]
    rw [add_assoc, intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn,
      intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn]
  have hright : ‖right‖ ≤ D/r.im := norm_integral_bromwich_tail_le hi hD hF hrt
  have hleft : ‖left‖ ≤ D/(-l.im) := by
    have hh := norm_integral_bromwich_tail_le hi.comp_neg hD
      (fun t => by simpa using hF (-t)) (neg_pos.mpr hlt)
    simpa only [integral_comp_neg_Ioi, neg_neg] using hh
  have hhoriz {w : ℂ} (hw : 1/2 ≤ w.re) (hw' : w.re ≤ 4) (ht : w.im ≠ 0) :
      ‖g w-g (1+w.im*I)‖ ≤ 3*D/|w.im| := by
    apply (norm_horizontal_primitive_le hg hf hD hbound hw hw').trans
    gcongr
    have h := sq_nonneg (|w.im|-1)
    nlinarith [sq_abs w.im, abs_nonneg w.im]
  have ht := integral_vertical_eq_primitive hg hf (by norm_num : (0:ℝ) < 1) l.im r.im
  change I*(∫ t in l.im..r.im, F t) = _ at ht
  simp only [Complex.ofReal_one] at ht
  change ‖_ - I*(∫ t, F t)‖ ≤ _
  rw [← heq, show g r-g l-I*(left+(∫ t in l.im..r.im,F t)+right) =
      (g r-g (1+r.im*I)) - (g l-g (1+l.im*I)) - I*(left+right) by rw [mul_add, mul_add, ht]; ring]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul]
  apply (add_le_add (norm_sub_le _ _) (norm_add_le _ _)).trans
  have h₁ := hhoriz hr hr' hrt.ne'
  have h₂ := hhoriz hl hl' hlt.ne
  rw [abs_of_pos hrt] at h₁
  rw [abs_of_neg hlt] at h₂
  exact (add_le_add (add_le_add h₁ h₂) (add_le_add hleft hright)).trans_eq (by ring)

end AnalyticNumberTheory.ModularAndPartitions
