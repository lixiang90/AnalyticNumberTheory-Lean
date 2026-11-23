import Mathlib.Analysis.Complex.Hadamard

/-!
# Hadamard Three-Circles and Three-Lines Theorems

This file bridges Mathlib's `Complex.HadamardThreeLines` into an ergonomic API on vertical
strips `σ₁ ≤ s.re ≤ σ₂` and deduces Hadamard's three-circles theorem on annuli and disks.

## Main Definitions

* `lineSupNorm f σ` : supremum of `‖f (σ + t * I)‖` over `t : ℝ`.
* `circleMax f c r` : supremum of `‖f z‖` on `Metric.sphere c r`.

## Main Theorems

* `hadamard_three_lines` / `hadamard_three_lines_lineSupNorm` : three-lines convexity bound
  on vertical strips `σ₁ ≤ s.re ≤ σ₂`.
* `hadamard_three_circles_pointwise` / `hadamard_three_circles` : Hadamard three-circles
  theorem `M(r) ≤ M(r₁) ^ (1 - θ) * M(r₂) ^ θ` with `θ = log (r / r₁) / log (r₂ / r₁)`.
* `hadamard_three_circles_rpow` / `hadamard_three_circles_log_convex` : power and logarithmic
  convexity forms of the three-circles theorem.
-/

open Complex Filter Metric Real Set

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-!
### Vertical Strip Three-Lines Theorems
-/

section ThreeLines

variable {E : Type*} [NormedAddCommGroup E]

/-- The supremum of `‖f (σ + t * I)‖` over `t : ℝ`, i.e., along the vertical line `s.re = σ`. -/
noncomputable def lineSupNorm (f : ℂ → E) (σ : ℝ) : ℝ :=
  sSup ((fun t : ℝ ↦ ‖f ((σ : ℂ) + (t : ℂ) * I)‖) '' Set.univ)

/-- `lineSupNorm f σ` equals Mathlib's `Complex.HadamardThreeLines.sSupNormIm f σ`. -/
lemma lineSupNorm_eq_sSupNormIm (f : ℂ → E) (σ : ℝ) :
    lineSupNorm f σ = Complex.HadamardThreeLines.sSupNormIm f σ := by
  unfold lineSupNorm Complex.HadamardThreeLines.sSupNormIm
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_singleton_iff,
    Function.comp_apply]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(σ : ℂ) + (t : ℂ) * I, by simp, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.im, ?_⟩
    have hzeq : (σ : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp [hz]
    rw [hzeq]

/-- `lineSupNorm f σ` is non-negative. -/
lemma lineSupNorm_nonneg (f : ℂ → E) (σ : ℝ) : 0 ≤ lineSupNorm f σ := by
  rw [lineSupNorm_eq_sSupNormIm]
  exact Complex.HadamardThreeLines.sSupNormIm_nonneg f σ

/-- If `‖f (σ + t * I)‖ ≤ M` for all `t : ℝ`, then `lineSupNorm f σ ≤ M`. -/
lemma lineSupNorm_le {f : ℂ → E} {σ M : ℝ} (hM : ∀ t : ℝ, ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    lineSupNorm f σ ≤ M := by
  apply csSup_le
  · exact ⟨‖f (σ : ℂ)‖, 0, Set.mem_univ 0, by simp⟩
  · rintro y ⟨t, -, rfl⟩
    exact hM t

/-- Pointwise bound `‖f s‖ ≤ lineSupNorm f s.re` when `‖f‖` is bounded on the vertical line. -/
lemma norm_le_lineSupNorm {f : ℂ → E} {s : ℂ}
    (hB : BddAbove ((fun t : ℝ ↦ ‖f ((s.re : ℂ) + (t : ℂ) * I)‖) '' Set.univ)) :
    ‖f s‖ ≤ lineSupNorm f s.re := by
  refine le_csSup hB ?_
  refine ⟨s.im, Set.mem_univ _, ?_⟩
  have hs : (s.re : ℂ) + (s.im : ℂ) * I = s := by apply Complex.ext <;> simp
  dsimp only
  rw [hs]

private lemma closure_verticalStrip_eq {a b : ℝ} (hab : a < b) :
    closure (Complex.HadamardThreeLines.verticalStrip a b) =
      Complex.HadamardThreeLines.verticalClosedStrip a b := by
  rw [Complex.HadamardThreeLines.verticalStrip, Complex.HadamardThreeLines.verticalClosedStrip,
    Complex.closure_preimage_re, closure_Ioo hab.ne]

variable [NormedSpace ℂ E]

/-- **Hadamard three-lines theorem** on a vertical strip `σ₁ ≤ s.re ≤ σ₂`:
if `f : ℂ → E` is continuous and bounded on `{s | σ₁ ≤ s.re ∧ s.re ≤ σ₂}`, holomorphic on
`{s | σ₁ < s.re ∧ s.re < σ₂}`, and satisfies `‖f (σ₁ + t * I)‖ ≤ M₁` and
`‖f (σ₂ + t * I)‖ ≤ M₂` for all `t : ℝ`, then for any `s` in the closed strip with
`θ = (s.re - σ₁) / (σ₂ - σ₁)`, we have `‖f s‖ ≤ M₁ ^ (1 - θ) * M₂ ^ θ`. -/
theorem hadamard_three_lines {f : ℂ → E} {σ₁ σ₂ M₁ M₂ : ℝ} {s : ℂ} (hσ : σ₁ < σ₂)
    (hcont : ContinuousOn f {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | σ₁ < z.re ∧ z.re < σ₂})
    (hB : ∃ B : ℝ, ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ → ‖f z‖ ≤ B)
    (hM₁ : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ M₁)
    (hM₂ : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ M₂)
    (hs₁ : σ₁ ≤ s.re) (hs₂ : s.re ≤ σ₂) :
    ‖f s‖ ≤ M₁ ^ (1 - (s.re - σ₁) / (σ₂ - σ₁)) * M₂ ^ ((s.re - σ₁) / (σ₂ - σ₁)) := by
  have hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip σ₁ σ₂) := by
    refine ⟨hdiff, ?_⟩
    rw [closure_verticalStrip_eq hσ]
    exact hcont
  have hB' : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip σ₁ σ₂) := by
    rcases hB with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hB z hz.1 hz.2
  have ha : ∀ z ∈ Complex.re ⁻¹' {σ₁}, ‖f z‖ ≤ M₁ := by
    intro z hz
    have hzeq : z = (σ₁ : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext
      · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
        simp [hz]
      · simp
    rw [hzeq]
    exact hM₁ z.im
  have hb : ∀ z ∈ Complex.re ⁻¹' {σ₂}, ‖f z‖ ≤ M₂ := by
    intro z hz
    have hzeq : z = (σ₂ : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext
      · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
        simp [hz]
      · simp
    rw [hzeq]
    exact hM₂ z.im
  exact Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hσ ⟨hs₁, hs₂⟩ hd hB' ha hb

/-- `lineSupNorm` form of **Hadamard's three-lines theorem**:
for `σ₁ ≤ σ ≤ σ₂` (`σ₁ < σ₂`) and `θ = (σ - σ₁) / (σ₂ - σ₁)`,
`lineSupNorm f σ ≤ (lineSupNorm f σ₁) ^ (1 - θ) * (lineSupNorm f σ₂) ^ θ`. -/
theorem hadamard_three_lines_lineSupNorm {f : ℂ → E} {σ₁ σ₂ σ : ℝ} (hσ : σ₁ < σ₂)
    (hcont : ContinuousOn f {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | σ₁ < z.re ∧ z.re < σ₂})
    (hB : ∃ B : ℝ, ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ → ‖f z‖ ≤ B)
    (hσ₁ : σ₁ ≤ σ) (hσ₂ : σ ≤ σ₂) :
    lineSupNorm f σ ≤
      (lineSupNorm f σ₁) ^ (1 - (σ - σ₁) / (σ₂ - σ₁)) *
        (lineSupNorm f σ₂) ^ ((σ - σ₁) / (σ₂ - σ₁)) := by
  have hB₁ : BddAbove ((fun t : ℝ ↦ ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖) '' Set.univ) := by
    rcases hB with ⟨B, hB⟩
    exact ⟨B, by rintro y ⟨t, -, rfl⟩; exact hB _ (by simp) (by simp [hσ.le])⟩
  have hB₂ : BddAbove ((fun t : ℝ ↦ ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖) '' Set.univ) := by
    rcases hB with ⟨B, hB⟩
    exact ⟨B, by rintro y ⟨t, -, rfl⟩; exact hB _ (by simp [hσ.le]) (by simp)⟩
  apply lineSupNorm_le
  intro t
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have h_pt := hadamard_three_lines hσ hcont hdiff hB
    (fun x ↦ le_csSup hB₁ ⟨x, Set.mem_univ _, rfl⟩)
    (fun x ↦ le_csSup hB₂ ⟨x, Set.mem_univ _, rfl⟩)
    (s := (σ : ℂ) + (t : ℂ) * I) (by simp [hσ₁]) (by simp [hσ₂])
  rw [hre] at h_pt
  exact h_pt

/-- Logarithmic convexity form of **Hadamard's three-lines theorem**:
if `0 < lineSupNorm f σ₁`, `0 < lineSupNorm f σ₂`, and `0 < lineSupNorm f σ`, then
`Real.log (lineSupNorm f σ) ≤ (1 - θ) * Real.log (lineSupNorm f σ₁) + θ * Real.log (lineSupNorm f σ₂)`. -/
theorem hadamard_three_lines_log_convex {f : ℂ → E} {σ₁ σ₂ σ : ℝ} (hσ : σ₁ < σ₂)
    (hcont : ContinuousOn f {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | σ₁ < z.re ∧ z.re < σ₂})
    (hB : ∃ B : ℝ, ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ → ‖f z‖ ≤ B)
    (hσ₁ : σ₁ ≤ σ) (hσ₂ : σ ≤ σ₂)
    (hp : 0 < lineSupNorm f σ) (hp₁ : 0 < lineSupNorm f σ₁) (hp₂ : 0 < lineSupNorm f σ₂) :
    Real.log (lineSupNorm f σ) ≤
      (1 - (σ - σ₁) / (σ₂ - σ₁)) * Real.log (lineSupNorm f σ₁) +
        ((σ - σ₁) / (σ₂ - σ₁)) * Real.log (lineSupNorm f σ₂) := by
  have h3 := hadamard_three_lines_lineSupNorm hσ hcont hdiff hB hσ₁ hσ₂
  have hlog := Real.log_le_log hp h3
  rw [Real.log_mul (Real.rpow_pos_of_pos hp₁ _).ne' (Real.rpow_pos_of_pos hp₂ _).ne',
    Real.log_rpow hp₁, Real.log_rpow hp₂] at hlog
  exact hlog

end ThreeLines

/-!
### Hadamard Three-Circles Theorem
-/

section ThreeCircles

variable {E : Type*} [NormedAddCommGroup E]

/-- Maximum modulus of `f : ℂ → E` on the circle `Metric.sphere c r`. -/
noncomputable def circleMax (f : ℂ → E) (c : ℂ) (r : ℝ) : ℝ :=
  sSup ((norm ∘ f) '' Metric.sphere c r)

/-- `circleMax f c r` is non-negative. -/
lemma circleMax_nonneg (f : ℂ → E) (c : ℂ) (r : ℝ) : 0 ≤ circleMax f c r := by
  apply Real.sSup_nonneg
  rintro y ⟨z, -, rfl⟩
  exact norm_nonneg _

/-- If `f` is continuous on `Metric.sphere c r`, then `‖f z‖ ≤ circleMax f c r` for all
`z ∈ Metric.sphere c r`. -/
lemma norm_le_circleMax {f : ℂ → E} {c z : ℂ} {r : ℝ}
    (hcont : ContinuousOn f (Metric.sphere c r)) (hz : z ∈ Metric.sphere c r) :
    ‖f z‖ ≤ circleMax f c r := by
  have hbdd : BddAbove ((norm ∘ f) '' Metric.sphere c r) :=
    ((isCompact_sphere c r).image_of_continuousOn hcont.norm).bddAbove
  exact le_csSup hbdd ⟨z, hz, rfl⟩

/-- If `‖f z‖ ≤ M` for all `z ∈ Metric.sphere c r` (`0 ≤ r`), then `circleMax f c r ≤ M`. -/
lemma circleMax_le {f : ℂ → E} {c : ℂ} {r M : ℝ} (hr : 0 ≤ r)
    (hM : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ M) : circleMax f c r ≤ M := by
  obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (x := c) (r := r).mpr hr
  apply csSup_le ⟨‖f z‖, Set.mem_image_of_mem (norm ∘ f) hz⟩
  rintro y ⟨w, hw, rfl⟩
  exact hM w hw

variable [NormedSpace ℂ E]

/-- **Hadamard three-circles theorem** (pointwise form on a closed annulus):
if `0 < r₁ < r₂`, `f : ℂ → E` is continuous on `{z | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂}`,
complex differentiable on `{z | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂}`, and bounded by `M₁` on
`Metric.sphere c r₁` and `M₂` on `Metric.sphere c r₂`, then for every `z` in the closed annulus,
letting `θ = Real.log (‖z - c‖ / r₁) / Real.log (r₂ / r₁)`, we have
`‖f z‖ ≤ M₁ ^ (1 - θ) * M₂ ^ θ`. -/
theorem hadamard_three_circles_pointwise {f : ℂ → E} {c z : ℂ} {r₁ r₂ M₁ M₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hcont : ContinuousOn f {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂})
    (hdiff : DifferentiableOn ℂ f {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂})
    (hM₁ : ∀ w ∈ Metric.sphere c r₁, ‖f w‖ ≤ M₁)
    (hM₂ : ∀ w ∈ Metric.sphere c r₂, ‖f w‖ ≤ M₂)
    (hz₁ : r₁ ≤ ‖z - c‖) (hz₂ : ‖z - c‖ ≤ r₂) :
    ‖f z‖ ≤
      M₁ ^ (1 - Real.log (‖z - c‖ / r₁) / Real.log (r₂ / r₁)) *
        M₂ ^ (Real.log (‖z - c‖ / r₁) / Real.log (r₂ / r₁)) := by
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hz_pos : 0 < ‖z - c‖ := hr₁.trans_le hz₁
  have hz_ne : z - c ≠ 0 := norm_pos_iff.mp hz_pos
  let a : ℝ := Real.log r₁
  let b : ℝ := Real.log r₂
  have hab : a < b := Real.log_lt_log hr₁ hr₁₂
  let g : ℂ → E := fun w ↦ f (c + Complex.exp w)
  have hmaps_open : Set.MapsTo (fun w : ℂ ↦ c + Complex.exp w)
      {w : ℂ | a < w.re ∧ w.re < b} {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, add_sub_cancel_left, Complex.norm_exp]
    exact ⟨by rw [← Real.exp_log hr₁]; exact Real.exp_lt_exp.mpr hw.1,
      by rw [← Real.exp_log hr₂]; exact Real.exp_lt_exp.mpr hw.2⟩
  have hmaps_closed : Set.MapsTo (fun w : ℂ ↦ c + Complex.exp w)
      {w : ℂ | a ≤ w.re ∧ w.re ≤ b} {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, add_sub_cancel_left, Complex.norm_exp]
    exact ⟨by rw [← Real.exp_log hr₁]; exact Real.exp_le_exp.mpr hw.1,
      by rw [← Real.exp_log hr₂]; exact Real.exp_le_exp.mpr hw.2⟩
  have hg_cont : ContinuousOn g {w : ℂ | a ≤ w.re ∧ w.re ≤ b} :=
    hcont.comp (continuous_const.add Complex.continuous_exp).continuousOn hmaps_closed
  have hg_diff : DifferentiableOn ℂ g {w : ℂ | a < w.re ∧ w.re < b} :=
    hdiff.comp (differentiable_const c |>.add Complex.differentiable_exp).differentiableOn hmaps_open
  have h_ann_compact : IsCompact {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} := by
    have h_eq : {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} =
        Metric.closedBall c r₂ ∩ (Metric.ball c r₁)ᶜ := by
      ext w
      simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, and_comm]
    rw [h_eq]
    exact (isCompact_closedBall c r₂).inter_right isOpen_ball.isClosed_compl
  obtain ⟨B, hB⟩ := (h_ann_compact.image_of_continuousOn hcont.norm).bddAbove
  have hg_B : ∃ B : ℝ, ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖g w‖ ≤ B := by
    refine ⟨B, fun w hw₁ hw₂ ↦ hB ?_⟩
    exact ⟨c + Complex.exp w, hmaps_closed ⟨hw₁, hw₂⟩, rfl⟩
  have hg_M₁ : ∀ t : ℝ, ‖g ((a : ℂ) + (t : ℂ) * I)‖ ≤ M₁ := by
    intro t
    apply hM₁
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    simp [a, Real.exp_log hr₁]
  have hg_M₂ : ∀ t : ℝ, ‖g ((b : ℂ) + (t : ℂ) * I)‖ ≤ M₂ := by
    intro t
    apply hM₂
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    simp [b, Real.exp_log hr₂]
  let w₀ : ℂ := Complex.log (z - c)
  have hw₀_re : w₀.re = Real.log ‖z - c‖ := Complex.log_re (z - c)
  have h_three := hadamard_three_lines hab hg_cont hg_diff hg_B hg_M₁ hg_M₂
    (hw₀_re ▸ Real.log_le_log hr₁ hz₁) (hw₀_re ▸ Real.log_le_log hz_pos hz₂)
  have hgw₀ : g w₀ = f z := by
    simp [g, w₀, Complex.exp_log hz_ne]
  have h_theta : (w₀.re - a) / (b - a) = Real.log (‖z - c‖ / r₁) / Real.log (r₂ / r₁) := by
    rw [hw₀_re, ← Real.log_div hz_pos.ne' hr₁.ne', ← Real.log_div hr₂.ne' hr₁.ne']
  rwa [hgw₀, h_theta] at h_three

/-- **Hadamard three-circles theorem** (`circleMax` form with prescribed boundary bounds):
for `0 < r₁ ≤ r ≤ r₂` (`r₁ < r₂`) and `θ = Real.log (r / r₁) / Real.log (r₂ / r₁)`,
`circleMax f c r ≤ M₁ ^ (1 - θ) * M₂ ^ θ`. -/
theorem hadamard_three_circles_bound {f : ℂ → E} {c : ℂ} {r₁ r r₂ M₁ M₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁r : r₁ ≤ r) (hrr₂ : r ≤ r₂) (hr₁₂ : r₁ < r₂)
    (hcont : ContinuousOn f {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂})
    (hdiff : DifferentiableOn ℂ f {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂})
    (hM₁ : ∀ w ∈ Metric.sphere c r₁, ‖f w‖ ≤ M₁)
    (hM₂ : ∀ w ∈ Metric.sphere c r₂, ‖f w‖ ≤ M₂) :
    circleMax f c r ≤
      M₁ ^ (1 - Real.log (r / r₁) / Real.log (r₂ / r₁)) *
        M₂ ^ (Real.log (r / r₁) / Real.log (r₂ / r₁)) := by
  have hr : 0 ≤ r := hr₁.le.trans hr₁r
  apply circleMax_le hr
  intro z hz
  have hznorm : ‖z - c‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hpt := hadamard_three_circles_pointwise hr₁ hr₁₂ hcont hdiff hM₁ hM₂
    (hznorm ▸ hr₁r) (hznorm ▸ hrr₂)
  rwa [hznorm] at hpt

/-- **Hadamard three-circles theorem**:
for `0 < r₁ ≤ r ≤ r₂` (`r₁ < r₂`) and `θ = Real.log (r / r₁) / Real.log (r₂ / r₁)`,
`circleMax f c r ≤ (circleMax f c r₁) ^ (1 - θ) * (circleMax f c r₂) ^ θ`. -/
theorem hadamard_three_circles {f : ℂ → E} {c : ℂ} {r₁ r r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁r : r₁ ≤ r) (hrr₂ : r ≤ r₂) (hr₁₂ : r₁ < r₂)
    (hcont : ContinuousOn f {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂})
    (hdiff : DifferentiableOn ℂ f {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂}) :
    circleMax f c r ≤
      (circleMax f c r₁) ^ (1 - Real.log (r / r₁) / Real.log (r₂ / r₁)) *
        (circleMax f c r₂) ^ (Real.log (r / r₁) / Real.log (r₂ / r₁)) := by
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hs₁ : Metric.sphere c r₁ ⊆ {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} := by
    intro w hw
    have hwn : ‖w - c‖ = r₁ := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    exact ⟨hwn.ge, hwn.le.trans hr₁₂.le⟩
  have hs₂ : Metric.sphere c r₂ ⊆ {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} := by
    intro w hw
    have hwn : ‖w - c‖ = r₂ := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    exact ⟨hr₁₂.le.trans hwn.ge, hwn.le⟩
  exact hadamard_three_circles_bound hr₁ hr₁r hrr₂ hr₁₂ hcont hdiff
    (fun w hw ↦ norm_le_circleMax (hcont.mono hs₁) hw)
    (fun w hw ↦ norm_le_circleMax (hcont.mono hs₂) hw)

/-- **Hadamard three-circles theorem** (product-of-powers form):
`M(r) ^ log (r₂ / r₁) ≤ M(r₁) ^ log (r₂ / r) * M(r₂) ^ log (r / r₁)`. -/
theorem hadamard_three_circles_rpow {f : ℂ → E} {c : ℂ} {r₁ r r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁r : r₁ ≤ r) (hrr₂ : r ≤ r₂) (hr₁₂ : r₁ < r₂)
    (hcont : ContinuousOn f {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂})
    (hdiff : DifferentiableOn ℂ f {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂}) :
    (circleMax f c r) ^ Real.log (r₂ / r₁) ≤
      (circleMax f c r₁) ^ Real.log (r₂ / r) * (circleMax f c r₂) ^ Real.log (r / r₁) := by
  have hr : 0 < r := hr₁.trans_le hr₁r
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hlog_pos : 0 < Real.log (r₂ / r₁) := Real.log_pos (by rwa [one_lt_div hr₁])
  have h3 := hadamard_three_circles hr₁ hr₁r hrr₂ hr₁₂ hcont hdiff
  have h_pow := Real.rpow_le_rpow (circleMax_nonneg f c r) h3 hlog_pos.le
  rw [Real.mul_rpow (Real.rpow_nonneg (circleMax_nonneg f c r₁) _)
    (Real.rpow_nonneg (circleMax_nonneg f c r₂) _),
    ← Real.rpow_mul (circleMax_nonneg f c r₁),
    ← Real.rpow_mul (circleMax_nonneg f c r₂)] at h_pow
  have h1 : (1 - Real.log (r / r₁) / Real.log (r₂ / r₁)) * Real.log (r₂ / r₁) = Real.log (r₂ / r) := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hlog_pos.ne']
    rw [Real.log_div hr₂.ne' hr₁.ne', Real.log_div hr.ne' hr₁.ne', Real.log_div hr₂.ne' hr.ne']
    ring
  have h2 : (Real.log (r / r₁) / Real.log (r₂ / r₁)) * Real.log (r₂ / r₁) = Real.log (r / r₁) :=
    div_mul_cancel₀ _ hlog_pos.ne'
  rwa [h1, h2] at h_pow

/-- Logarithmic convexity form of **Hadamard's three-circles theorem**:
`log M(r) ≤ (1 - θ) * log M(r₁) + θ * log M(r₂)` when the three circle maxima are positive. -/
theorem hadamard_three_circles_log_convex {f : ℂ → E} {c : ℂ} {r₁ r r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁r : r₁ ≤ r) (hrr₂ : r ≤ r₂) (hr₁₂ : r₁ < r₂)
    (hcont : ContinuousOn f {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂})
    (hdiff : DifferentiableOn ℂ f {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂})
    (hp : 0 < circleMax f c r) (hp₁ : 0 < circleMax f c r₁) (hp₂ : 0 < circleMax f c r₂) :
    Real.log (circleMax f c r) ≤
      (1 - Real.log (r / r₁) / Real.log (r₂ / r₁)) * Real.log (circleMax f c r₁) +
        (Real.log (r / r₁) / Real.log (r₂ / r₁)) * Real.log (circleMax f c r₂) := by
  have h3 := hadamard_three_circles hr₁ hr₁r hrr₂ hr₁₂ hcont hdiff
  have hlog := Real.log_le_log hp h3
  rw [Real.log_mul (Real.rpow_pos_of_pos hp₁ _).ne' (Real.rpow_pos_of_pos hp₂ _).ne',
    Real.log_rpow hp₁, Real.log_rpow hp₂] at hlog
  exact hlog

/-- Disk corollary of **Hadamard's three-circles theorem**: if `f` is continuous on
`Metric.closedBall c r₂` and differentiable on `Metric.ball c r₂`, then for `0 < r₁ ≤ r ≤ r₂`
(`r₁ < r₂`),
`circleMax f c r ≤ (circleMax f c r₁) ^ (1 - θ) * (circleMax f c r₂) ^ θ`. -/
theorem hadamard_three_circles_of_ball {f : ℂ → E} {c : ℂ} {r₁ r r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁r : r₁ ≤ r) (hrr₂ : r ≤ r₂) (hr₁₂ : r₁ < r₂)
    (hf : DiffContOnCl ℂ f (Metric.ball c r₂)) :
    circleMax f c r ≤
      (circleMax f c r₁) ^ (1 - Real.log (r / r₁) / Real.log (r₂ / r₁)) *
        (circleMax f c r₂) ^ (Real.log (r / r₁) / Real.log (r₂ / r₁)) := by
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have h_sub_closed : {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} ⊆ Metric.closedBall c r₂ :=
    fun w hw ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using hw.2
  have h_sub_open : {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂} ⊆ Metric.ball c r₂ :=
    fun w hw ↦ by simpa [Metric.mem_ball, dist_eq_norm] using hw.2
  have hcont : ContinuousOn f {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂} := by
    have hc : ContinuousOn f (Metric.closedBall c r₂) := by
      simpa [closure_ball c hr₂.ne'] using hf.continuousOn_ball
    exact hc.mono h_sub_closed
  have hdiff : DifferentiableOn ℂ f {w : ℂ | r₁ < ‖w - c‖ ∧ ‖w - c‖ < r₂} :=
    hf.differentiableOn.mono h_sub_open
  exact hadamard_three_circles hr₁ hr₁r hrr₂ hr₁₂ hcont hdiff

end ThreeCircles

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
