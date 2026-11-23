import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phragmén–Lindelöf Principle and Vertical-Strip Growth Interpolation

This file bridges Mathlib's `PhragmenLindelof` API to vertical strips and half-strips, and
proves the Phragmén–Lindelöf polynomial vertical-growth interpolation (convexity) principle.

## Main Definitions

* `verticalStripOpen` / `verticalStripClosed` : open and closed vertical strips `σ₁ < Re s < σ₂`
  and `σ₁ ≤ Re s ≤ σ₂`.
* `upperHalfStripOpen` / `upperHalfStripClosed` : open and closed upper half-strips with
  `t₀ < Im s` and `t₀ ≤ Im s`.
* `linearInterp` : linear interpolation `α₁ * (σ₂ - σ) / (σ₂ - σ₁) + α₂ * (σ - σ₁) / (σ₂ - σ₁)`.

## Main Theorems

* `phragmen_lindelof_vertical_strip` / `phragmen_lindelof_vertical_strip_of_exp_le` /
  `phragmen_lindelof_vertical_strip_of_exp_rpow_le` : boundedness on vertical strips under
  sub-double-exponential or finite-order vertical growth.
* `phragmen_lindelof_upper_half_strip` / `phragmen_lindelof_lower_half_strip` : Phragmén–Lindelöf
  principle on upper and lower vertical half-strips.
* `phragmen_lindelof_upper_half_strip_poly` / `phragmen_lindelof_poly_interp_of_exp_le` /
  `phragmen_lindelof_poly_interp` / `phragmen_lindelof_poly_interp_of_exp_rpow_le` /
  `phragmen_lindelof_poly_interp_of_poly_le` : polynomial vertical-growth interpolation
  `‖f (σ + t * I)‖ ≤ C * (|t| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ`.
-/

open Complex Filter Metric Real Set
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-!
### Vertical Strips, Half-Strips, and Linear Interpolation
-/

/-- The open vertical strip `{z : ℂ | σ₁ < z.re ∧ z.re < σ₂}`. -/
def verticalStripOpen (σ₁ σ₂ : ℝ) : Set ℂ :=
  Complex.re ⁻¹' Set.Ioo σ₁ σ₂

/-- The closed vertical strip `{z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂}`. -/
def verticalStripClosed (σ₁ σ₂ : ℝ) : Set ℂ :=
  Complex.re ⁻¹' Set.Icc σ₁ σ₂

/-- The open upper half-strip `{z : ℂ | σ₁ < z.re ∧ z.re < σ₂ ∧ t₀ < z.im}`. -/
def upperHalfStripOpen (σ₁ σ₂ t₀ : ℝ) : Set ℂ :=
  {z : ℂ | σ₁ < z.re ∧ z.re < σ₂ ∧ t₀ < z.im}

/-- The closed upper half-strip `{z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ t₀ ≤ z.im}`. -/
def upperHalfStripClosed (σ₁ σ₂ t₀ : ℝ) : Set ℂ :=
  {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ t₀ ≤ z.im}

/-- Linear interpolation between `α₁` (at `σ₁`) and `α₂` (at `σ₂`), evaluated at `σ`:
`α₁ * (σ₂ - σ) / (σ₂ - σ₁) + α₂ * (σ - σ₁) / (σ₂ - σ₁)`. -/
noncomputable def linearInterp (σ₁ σ₂ α₁ α₂ σ : ℝ) : ℝ :=
  α₁ * (σ₂ - σ) / (σ₂ - σ₁) + α₂ * (σ - σ₁) / (σ₂ - σ₁)

/-- Value of `linearInterp` at the left endpoint `σ₁`. -/
@[simp]
lemma linearInterp_left {σ₁ σ₂ : ℝ} (hσ : σ₁ ≠ σ₂) (α₁ α₂ : ℝ) :
    linearInterp σ₁ σ₂ α₁ α₂ σ₁ = α₁ := by
  have hne : σ₂ - σ₁ ≠ 0 := sub_ne_zero.mpr hσ.symm
  simp only [linearInterp, sub_self, mul_zero, zero_div, add_zero]
  field_simp [hne]

/-- Value of `linearInterp` at the right endpoint `σ₂`. -/
@[simp]
lemma linearInterp_right {σ₁ σ₂ : ℝ} (hσ : σ₁ ≠ σ₂) (α₁ α₂ : ℝ) :
    linearInterp σ₁ σ₂ α₁ α₂ σ₂ = α₂ := by
  have hne : σ₂ - σ₁ ≠ 0 := sub_ne_zero.mpr hσ.symm
  simp only [linearInterp, sub_self, mul_zero, zero_div, zero_add]
  field_simp [hne]

/-- Reflecting `σ ↦ -σ` swaps the boundary exponents `α₁, α₂` in `linearInterp`. -/
lemma linearInterp_symm (σ₁ σ₂ α₁ α₂ σ : ℝ) :
    linearInterp (-σ₂) (-σ₁) α₂ α₁ (-σ) = linearInterp σ₁ σ₂ α₁ α₂ σ := by
  simp only [linearInterp]
  ring_nf

/-- For `σ ∈ [σ₁, σ₂]` with `σ₁ < σ₂`, `linearInterp σ₁ σ₂ α₁ α₂ σ` lies between `min α₁ α₂`
and `max α₁ α₂`. -/
lemma linearInterp_between {σ₁ σ₂ α₁ α₂ σ : ℝ} (hσ₁ : σ₁ ≤ σ) (hσ₂ : σ ≤ σ₂) (hσ : σ₁ < σ₂) :
    min α₁ α₂ ≤ linearInterp σ₁ σ₂ α₁ α₂ σ ∧ linearInterp σ₁ σ₂ α₁ α₂ σ ≤ max α₁ α₂ := by
  have hden : 0 < σ₂ - σ₁ := sub_pos.mpr hσ
  have hw₁ : 0 ≤ (σ₂ - σ) / (σ₂ - σ₁) := div_nonneg (sub_nonneg.mpr hσ₂) hden.le
  have hw₂ : 0 ≤ (σ - σ₁) / (σ₂ - σ₁) := div_nonneg (sub_nonneg.mpr hσ₁) hden.le
  have hsum : (σ₂ - σ) / (σ₂ - σ₁) + (σ - σ₁) / (σ₂ - σ₁) = 1 := by
    rw [← add_div, sub_add_sub_cancel, div_self hden.ne']
  have hval : linearInterp σ₁ σ₂ α₁ α₂ σ =
      ((σ₂ - σ) / (σ₂ - σ₁)) * α₁ + ((σ - σ₁) / (σ₂ - σ₁)) * α₂ := by
    simp only [linearInterp]
    ring
  rw [hval]
  constructor
  · calc
      min α₁ α₂ = ((σ₂ - σ) / (σ₂ - σ₁) + (σ - σ₁) / (σ₂ - σ₁)) * min α₁ α₂ := by
        rw [hsum, one_mul]
      _ = ((σ₂ - σ) / (σ₂ - σ₁)) * min α₁ α₂ + ((σ - σ₁) / (σ₂ - σ₁)) * min α₁ α₂ := by ring
      _ ≤ ((σ₂ - σ) / (σ₂ - σ₁)) * α₁ + ((σ - σ₁) / (σ₂ - σ₁)) * α₂ := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
  · calc
      ((σ₂ - σ) / (σ₂ - σ₁)) * α₁ + ((σ - σ₁) / (σ₂ - σ₁)) * α₂
        ≤ ((σ₂ - σ) / (σ₂ - σ₁)) * max α₁ α₂ + ((σ - σ₁) / (σ₂ - σ₁)) * max α₁ α₂ := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = ((σ₂ - σ) / (σ₂ - σ₁) + (σ - σ₁) / (σ₂ - σ₁)) * max α₁ α₂ := by ring
      _ = max α₁ α₂ := by rw [hsum, one_mul]

/-- Absolute-value bound on `linearInterp` over `σ ∈ [σ₁, σ₂]`. -/
lemma abs_linearInterp_le {σ₁ σ₂ α₁ α₂ σ : ℝ} (hσ₁ : σ₁ ≤ σ) (hσ₂ : σ ≤ σ₂) (hσ : σ₁ < σ₂) :
    |linearInterp σ₁ σ₂ α₁ α₂ σ| ≤ max |α₁| |α₂| := by
  obtain ⟨hlo, hhi⟩ := linearInterp_between (α₁ := α₁) (α₂ := α₂) hσ₁ hσ₂ hσ
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h1 : -max |α₁| |α₂| ≤ min α₁ α₂ := by
      refine le_min ?_ ?_
      · linarith [neg_abs_le α₁, le_max_left |α₁| |α₂|]
      · linarith [neg_abs_le α₂, le_max_right |α₁| |α₂|]
    exact h1.trans hlo
  · have h2 : max α₁ α₂ ≤ max |α₁| |α₂| :=
      max_le ((le_abs_self α₁).trans (le_max_left _ _))
        ((le_abs_self α₂).trans (le_max_right _ _))
    exact hhi.trans h2

/-- The open vertical strip `verticalStripOpen σ₁ σ₂` is open. -/
lemma isOpen_verticalStripOpen (σ₁ σ₂ : ℝ) : IsOpen (verticalStripOpen σ₁ σ₂) :=
  isOpen_Ioo.preimage Complex.continuous_re

/-- The closed vertical strip `verticalStripClosed σ₁ σ₂` is closed. -/
lemma isClosed_verticalStripClosed (σ₁ σ₂ : ℝ) : IsClosed (verticalStripClosed σ₁ σ₂) :=
  isClosed_Icc.preimage Complex.continuous_re

/-- The open vertical strip `verticalStripOpen σ₁ σ₂` is contained in `verticalStripClosed σ₁ σ₂`. -/
lemma verticalStripOpen_subset_closed (σ₁ σ₂ : ℝ) :
    verticalStripOpen σ₁ σ₂ ⊆ verticalStripClosed σ₁ σ₂ :=
  fun _ hz ↦ Set.Ioo_subset_Icc_self hz

/-- For `σ₁ < σ₂`, the closure of `verticalStripOpen σ₁ σ₂` is `verticalStripClosed σ₁ σ₂`. -/
lemma closure_verticalStripOpen {σ₁ σ₂ : ℝ} (hσ : σ₁ < σ₂) :
    closure (verticalStripOpen σ₁ σ₂) = verticalStripClosed σ₁ σ₂ := by
  apply Subset.antisymm
  · exact closure_minimal (verticalStripOpen_subset_closed σ₁ σ₂) (isClosed_verticalStripClosed σ₁ σ₂)
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    let m : ℝ := (σ₁ + σ₂) / 2
    let p : ℂ := (m : ℂ) + (z.im : ℂ) * I
    let θ : ℝ := min (1 / 2) (ε / (2 * (‖p - z‖ + 1)))
    have hθ_pos : 0 < θ := lt_min (by norm_num) (div_pos hε (by positivity))
    let w : ℂ := z + (θ : ℂ) * (p - z)
    have hp_re : p.re = m := by simp [p]
    have hw_re : w.re = (1 - θ) * z.re + θ * m := by
      simp only [w, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, zero_mul, sub_zero, hp_re]
      ring
    have hm_gt : σ₁ < m := by simp only [m]; linarith
    have hm_lt : m < σ₂ := by simp only [m]; linarith
    have hw_mem : w ∈ verticalStripOpen σ₁ σ₂ := by
      rw [verticalStripOpen, Set.mem_preimage, Set.mem_Ioo, hw_re]
      have hz₁ : σ₁ ≤ z.re := hz.1
      have hz₂ : z.re ≤ σ₂ := hz.2
      have hθ_lt : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
      constructor <;> nlinarith
    have hw_dist : dist z w < ε := by
      rw [dist_eq_norm]
      have hzw : z - w = -(θ : ℂ) * (p - z) := by simp only [w]; ring
      rw [hzw, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ_pos]
      have hθ_le : θ ≤ ε / (2 * (‖p - z‖ + 1)) := min_le_right _ _
      calc
        θ * ‖p - z‖ ≤ (ε / (2 * (‖p - z‖ + 1))) * ‖p - z‖ :=
          mul_le_mul_of_nonneg_right hθ_le (norm_nonneg _)
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (p - z)]
    exact ⟨w, hw_mem, hw_dist⟩

/-- The open upper half-strip `upperHalfStripOpen σ₁ σ₂ t₀` is open. -/
lemma isOpen_upperHalfStripOpen (σ₁ σ₂ t₀ : ℝ) : IsOpen (upperHalfStripOpen σ₁ σ₂ t₀) := by
  have heq : upperHalfStripOpen σ₁ σ₂ t₀ =
      (Complex.re ⁻¹' Set.Ioo σ₁ σ₂) ∩ (Complex.im ⁻¹' Set.Ioi t₀) := by
    ext z
    simp [upperHalfStripOpen, and_assoc]
  rw [heq]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioi.preimage Complex.continuous_im)

/-- The closed upper half-strip `upperHalfStripClosed σ₁ σ₂ t₀` is closed. -/
lemma isClosed_upperHalfStripClosed (σ₁ σ₂ t₀ : ℝ) : IsClosed (upperHalfStripClosed σ₁ σ₂ t₀) := by
  have heq : upperHalfStripClosed σ₁ σ₂ t₀ =
      (Complex.re ⁻¹' Set.Icc σ₁ σ₂) ∩ (Complex.im ⁻¹' Set.Ici t₀) := by
    ext z
    simp [upperHalfStripClosed, and_assoc]
  rw [heq]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Ici.preimage Complex.continuous_im)

/-- The open upper half-strip `upperHalfStripOpen σ₁ σ₂ t₀` is contained in
`upperHalfStripClosed σ₁ σ₂ t₀`. -/
lemma upperHalfStripOpen_subset_closed (σ₁ σ₂ t₀ : ℝ) :
    upperHalfStripOpen σ₁ σ₂ t₀ ⊆ upperHalfStripClosed σ₁ σ₂ t₀ :=
  fun _ ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁.le, h₂.le, h₃.le⟩

/-- For `σ₁ < σ₂`, the closure of `upperHalfStripOpen σ₁ σ₂ t₀` is
`upperHalfStripClosed σ₁ σ₂ t₀`. -/
lemma closure_upperHalfStripOpen {σ₁ σ₂ : ℝ} (hσ : σ₁ < σ₂) (t₀ : ℝ) :
    closure (upperHalfStripOpen σ₁ σ₂ t₀) = upperHalfStripClosed σ₁ σ₂ t₀ := by
  apply Subset.antisymm
  · exact closure_minimal (upperHalfStripOpen_subset_closed σ₁ σ₂ t₀)
      (isClosed_upperHalfStripClosed σ₁ σ₂ t₀)
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    let m : ℝ := (σ₁ + σ₂) / 2
    let p : ℂ := (m : ℂ) + ((t₀ + 1 : ℝ) : ℂ) * I
    let θ : ℝ := min (1 / 2) (ε / (2 * (‖p - z‖ + 1)))
    have hθ_pos : 0 < θ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hθ_lt : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    let w : ℂ := z + (θ : ℂ) * (p - z)
    have hp_re : p.re = m := by simp [p]
    have hp_im : p.im = t₀ + 1 := by simp [p]
    have hw_re : w.re = (1 - θ) * z.re + θ * m := by
      simp only [w, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, zero_mul, sub_zero, hp_re]
      ring
    have hw_im : w.im = (1 - θ) * z.im + θ * (t₀ + 1) := by
      simp only [w, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_im, zero_mul, add_zero, hp_im]
      ring
    have hm_gt : σ₁ < m := by simp only [m]; linarith
    have hm_lt : m < σ₂ := by simp only [m]; linarith
    have hw_mem : w ∈ upperHalfStripOpen σ₁ σ₂ t₀ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hw_re]; nlinarith [hz.1]
      · rw [hw_re]; nlinarith [hz.2.1]
      · rw [hw_im]; nlinarith [hz.2.2]
    have hw_dist : dist z w < ε := by
      rw [dist_eq_norm]
      have hzw : z - w = -(θ : ℂ) * (p - z) := by simp only [w]; ring
      rw [hzw, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ_pos]
      have hθ_le : θ ≤ ε / (2 * (‖p - z‖ + 1)) := min_le_right _ _
      calc
        θ * ‖p - z‖ ≤ (ε / (2 * (‖p - z‖ + 1))) * ‖p - z‖ :=
          mul_le_mul_of_nonneg_right hθ_le (norm_nonneg _)
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (p - z)]
    exact ⟨w, hw_mem, hw_dist⟩

private lemma isCompact_strip_box (σ₁ σ₂ a b : ℝ) :
    IsCompact {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ a ≤ z.im ∧ z.im ≤ b} := by
  let R : ℝ := max |σ₁| |σ₂| + max |a| |b|
  have hsub : {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ a ≤ z.im ∧ z.im ≤ b} ⊆ Metric.closedBall 0 R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ max |σ₁| |σ₂| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hz.1],
        by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hz.2.1]⟩
    have him : |z.im| ≤ max |a| |b| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, hz.2.2.1],
        by linarith [le_abs_self b, le_max_right |a| |b|, hz.2.2.2]⟩
    calc
      ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp
      _ ≤ R := add_le_add hre him
  have hclosed : IsClosed {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ a ≤ z.im ∧ z.im ≤ b} := by
    have heq : {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ a ≤ z.im ∧ z.im ≤ b} =
        (Complex.re ⁻¹' Set.Icc σ₁ σ₂) ∩ (Complex.im ⁻¹' Set.Icc a b) := by
      ext z
      simp [and_assoc]
    rw [heq]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  exact (isCompact_closedBall 0 R).of_isClosed_subset hclosed hsub

/-!
### Growth Helpers for Sub-Double-Exponential Absorption
-/

private lemma exp_rpow_le_exp_exp {γ c : ℝ} (hc : 0 < c) {B : ℝ} (hB : 0 ≤ B) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (B * (t + 2) ^ γ) ≤ A' * Real.exp (B' * Real.exp (c * t)) := by
  by_cases hγ : γ ≤ 0
  · refine ⟨Real.exp B, 0, (Real.exp_pos _).le, le_rfl, fun t ht ↦ ?_⟩
    have hrpow : (t + 2) ^ γ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hγ
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · push Not at hγ
    obtain ⟨n, hn⟩ := exists_nat_gt γ
    let B' : ℝ := B * ((Nat.factorial n : ℝ) / c ^ n * Real.exp (2 * c))
    refine ⟨1, B', zero_le_one, by positivity, fun t ht ↦ ?_⟩
    rw [one_mul]
    refine Real.exp_le_exp.mpr ?_
    have hpow1 : (t + 2) ^ γ ≤ (t + 2) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hn.le
    have hpow2 : (t + 2) ^ (n : ℝ) = (t + 2) ^ n := Real.rpow_natCast (t + 2) n
    have hpow3 : (c * (t + 2)) ^ n / (Nat.factorial n : ℝ) ≤ Real.exp (c * (t + 2)) :=
      Real.pow_div_factorial_le_exp (c * (t + 2)) (by positivity) n
    have hfac_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
    have hcn_pos : (0 : ℝ) < c ^ n := pow_pos hc n
    have hpow4 : (t + 2) ^ n ≤ (Nat.factorial n : ℝ) / c ^ n * Real.exp (2 * c) * Real.exp (c * t) := by
      rw [div_le_iff₀ hfac_pos, mul_pow] at hpow3
      have hexp : Real.exp (c * (t + 2)) = Real.exp (2 * c) * Real.exp (c * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp] at hpow3
      have hdiv := div_le_div_of_nonneg_right hpow3 hcn_pos.le
      rw [mul_div_cancel_left₀ _ hcn_pos.ne'] at hdiv
      refine hdiv.trans_eq ?_
      ring
    have hcomb : (t + 2) ^ γ ≤ (Nat.factorial n : ℝ) / c ^ n * Real.exp (2 * c) * Real.exp (c * t) :=
      hpow1.trans (hpow2 ▸ hpow4)
    calc
      B * (t + 2) ^ γ ≤ B * ((Nat.factorial n : ℝ) / c ^ n * Real.exp (2 * c) * Real.exp (c * t)) :=
        mul_le_mul_of_nonneg_left hcomb hB
      _ = B' * Real.exp (c * t) := by simp only [B']; ring

private lemma rpow_mul_exp_exp_le {K A B c c'' : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hc'' : 0 < c'') (hcc : c ≤ c'') :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ t : ℝ, 0 ≤ t →
      (t + 2) ^ K * (A * Real.exp (B * Real.exp (c * t))) ≤ A' * Real.exp (B' * Real.exp (c'' * t)) := by
  let A' : ℝ := A * Real.exp (K * Real.log 2)
  let B' : ℝ := K / (2 * c'') + max B 0
  refine ⟨A', B', by positivity, by positivity, fun t ht ↦ ?_⟩
  have ht2_pos : 0 < t + 2 := by linarith
  have hlog : Real.log (t + 2) ≤ Real.log 2 + t / 2 := by
    have ht1_pos : 0 < t / 2 + 1 := by linarith
    have hmul : t + 2 = 2 * (t / 2 + 1) := by ring
    rw [hmul, Real.log_mul (by norm_num) ht1_pos.ne']
    linarith [Real.log_le_sub_one_of_pos ht1_pos]
  have hexp_t : c'' * t ≤ Real.exp (c'' * t) := by
    linarith [Real.add_one_le_exp (c'' * t)]
  have hKlog : K * Real.log (t + 2) ≤ K * Real.log 2 + K / (2 * c'') * Real.exp (c'' * t) := by
    calc
      K * Real.log (t + 2) ≤ K * (Real.log 2 + t / 2) := mul_le_mul_of_nonneg_left hlog hK
      _ = K * Real.log 2 + K / (2 * c'') * (c'' * t) := by
        field_simp [hc''.ne']
      _ ≤ K * Real.log 2 + K / (2 * c'') * Real.exp (c'' * t) := by gcongr
  have hBexp : B * Real.exp (c * t) ≤ max B 0 * Real.exp (c'' * t) := by
    calc
      B * Real.exp (c * t) ≤ max B 0 * Real.exp (c * t) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max B 0 * Real.exp (c'' * t) := by gcongr
  calc
    (t + 2) ^ K * (A * Real.exp (B * Real.exp (c * t)))
      = A * (Real.exp (K * Real.log (t + 2)) * Real.exp (B * Real.exp (c * t))) := by
        rw [Real.rpow_def_of_pos ht2_pos, mul_comm (Real.log (t + 2)) K]
        ring
    _ = A * Real.exp (K * Real.log (t + 2) + B * Real.exp (c * t)) := by rw [Real.exp_add]
    _ ≤ A * Real.exp (K * Real.log 2 + (K / (2 * c'') + max B 0) * Real.exp (c'' * t)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
      linarith [hKlog, hBexp]
    _ = A' * Real.exp (B' * Real.exp (c'' * t)) := by
      rw [Real.exp_add]
      simp only [A', B']
      ring

private lemma isBigO_of_exp_le {σ₁ σ₂ : ℝ} {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {A B c : ℝ}
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|))) :
    f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  refine Asymptotics.IsBigO.of_bound A ?_
  rw [Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall fun z hz ↦ by
    simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using hbound z hz

private lemma exp_le_of_isBigO {σ₁ σ₂ : ℝ} (hσ : σ₁ < σ₂)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {B c : ℝ} (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hO : f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|))) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ z ∈ verticalStripClosed σ₁ σ₂, ‖f z‖ ≤ A * Real.exp (B' * Real.exp (c * |z.im|)) := by
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [Filter.eventually_inf_principal, Filter.eventually_comap] at hC
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hC
  have hcont_cl : ContinuousOn f (verticalStripClosed σ₁ σ₂) := by
    rw [← closure_verticalStripOpen hσ]
    exact hf.continuousOn
  let K : Set ℂ := {z : ℂ | σ₁ ≤ z.re ∧ z.re ≤ σ₂ ∧ -max T₀ 0 ≤ z.im ∧ z.im ≤ max T₀ 0}
  have hK_sub : K ⊆ verticalStripClosed σ₁ σ₂ := fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hK_bdd : BddAbove ((fun z ↦ ‖f z‖) '' K) :=
    ((isCompact_strip_box σ₁ σ₂ (-max T₀ 0) (max T₀ 0)).image_of_continuousOn
      (hcont_cl.mono hK_sub).norm).bddAbove
  obtain ⟨M₀, hM₀⟩ := hK_bdd
  have hK_bound : ∀ z ∈ K, ‖f z‖ ≤ max M₀ 0 := fun z hz ↦
    (hM₀ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  let A : ℝ := max (max C 0) (max M₀ 0)
  let B' : ℝ := max B 0
  refine ⟨A, B', by positivity, by positivity, fun z hz ↦ ?_⟩
  by_cases him : max T₀ 0 ≤ |z.im|
  · let m : ℝ := (σ₁ + σ₂) / 2
    let w : ℕ → ℂ := fun n ↦
      (((1 - 1 / ((n : ℝ) + 2)) * z.re + (1 / ((n : ℝ) + 2)) * m : ℝ) : ℂ) + (z.im : ℂ) * I
    have hw_open : ∀ n : ℕ, w n ∈ verticalStripOpen σ₁ σ₂ := by
      intro n
      have hθ_pos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have hθ_lt : (1 : ℝ) / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      have hre : (w n).re = (1 - 1 / ((n : ℝ) + 2)) * z.re + (1 / ((n : ℝ) + 2)) * m := by
        dsimp only [w]
        rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
        ring
      have hm_gt : σ₁ < m := by simp only [m]; linarith
      have hm_lt : m < σ₂ := by simp only [m]; linarith
      rw [verticalStripOpen, Set.mem_preimage, Set.mem_Ioo, hre]
      have hz₁ : σ₁ ≤ z.re := hz.1
      have hz₂ : z.re ≤ σ₂ := hz.2
      constructor <;> nlinarith
    have hw_cl : ∀ n : ℕ, w n ∈ verticalStripClosed σ₁ σ₂ :=
      fun n ↦ verticalStripOpen_subset_closed σ₁ σ₂ (hw_open n)
    have hw_im : ∀ n : ℕ, (w n).im = z.im := fun n ↦ by simp [w]
    have hw_bound : ∀ n : ℕ, ‖f (w n)‖ ≤ A * Real.exp (B' * Real.exp (c * |z.im|)) := by
      intro n
      have h1 := hT₀ |(w n).im| ((le_max_left T₀ 0).trans (hw_im n ▸ him)) (w n) rfl (hw_open n)
      rw [hw_im n, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
      have hC_le : C ≤ A := (le_max_left C 0).trans (le_max_left _ _)
      have hB_le : Real.exp (B * Real.exp (c * |z.im|)) ≤ Real.exp (B' * Real.exp (c * |z.im|)) := by
        gcongr
        exact le_max_left B 0
      exact h1.trans (mul_le_mul hC_le hB_le (Real.exp_pos _).le (by positivity))
    have htend_inv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have htend_re : Tendsto (fun n : ℕ ↦ (1 - 1 / ((n : ℝ) + 2)) * z.re + (1 / ((n : ℝ) + 2)) * m)
        atTop (𝓝 z.re) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub htend_inv |>.mul_const z.re).add
        (htend_inv.mul_const m)
    have htend_w : Tendsto w atTop (𝓝 z) := by
      have h_eq : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
      rw [h_eq]
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp htend_re).add tendsto_const_nhds
    have htend_within : Tendsto w atTop (𝓝[verticalStripClosed σ₁ σ₂] z) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w htend_w
        (Filter.Eventually.of_forall hw_cl)
    have htend_norm : Tendsto (fun n ↦ ‖f (w n)‖) atTop (𝓝 ‖f z‖) :=
      ((hcont_cl z hz).norm.tendsto).comp htend_within
    exact le_of_tendsto htend_norm (Filter.Eventually.of_forall hw_bound)
  · push Not at him
    have hzK : z ∈ K := ⟨hz.1, hz.2, (abs_le.mp him.le).1, (abs_le.mp him.le).2⟩
    have h1 : ‖f z‖ ≤ A := (hK_bound z hzK).trans (le_max_right _ _)
    have h2 : 1 ≤ Real.exp (B' * Real.exp (c * |z.im|)) := by
      rw [Real.one_le_exp_iff]
      exact mul_nonneg (le_max_right B 0) (Real.exp_pos _).le
    calc
      ‖f z‖ ≤ A := h1
      _ = A * 1 := (mul_one A).symm
      _ ≤ A * Real.exp (B' * Real.exp (c * |z.im|)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-!
### Section 1: Vertical Strip Phragmén–Lindelöf Theorems
-/

section VerticalStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Phragmén–Lindelöf theorem on a vertical strip** (bridging Mathlib's
`PhragmenLindelof.vertical_strip`): if `f` is complex differentiable on `verticalStripOpen σ₁ σ₂`,
continuous on its closure, satisfies `f =O exp(B * exp(c * |Im z|))` with `c < π / (σ₂ - σ₁)`,
and is bounded by `C` on both boundary lines `Re z = σ₁` and `Re z = σ₂`, then `‖f z‖ ≤ C`
throughout `verticalStripClosed σ₁ σ₂`. -/
theorem phragmen_lindelof_vertical_strip {σ₁ σ₂ C : ℝ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hB : ∃ c < π / (σ₂ - σ₁), ∃ B,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hle₁ : ∀ z : ℂ, z.re = σ₁ → ‖f z‖ ≤ C)
    (hle₂ : ∀ z : ℂ, z.re = σ₂ → ‖f z‖ ≤ C)
    {z : ℂ} (hz : z ∈ verticalStripClosed σ₁ σ₂) :
    ‖f z‖ ≤ C :=
  PhragmenLindelof.vertical_strip hf hB hle₁ hle₂ hz.1 hz.2

/-- Vertical-strip Phragmén–Lindelöf theorem with boundary bounds parameterized by `σ₁ + t * I`
and `σ₂ + t * I`. -/
theorem phragmen_lindelof_vertical_strip_lines {σ₁ σ₂ C : ℝ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hB : ∃ c < π / (σ₂ - σ₁), ∃ B,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hle₁ : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (hle₂ : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    {z : ℂ} (hz : z ∈ verticalStripClosed σ₁ σ₂) :
    ‖f z‖ ≤ C := by
  refine phragmen_lindelof_vertical_strip hf hB ?_ ?_ hz
  · intro w hw
    have heq : w = (σ₁ : ℂ) + (w.im : ℂ) * I := by rw [← hw, Complex.re_add_im]
    conv_lhs => rw [heq]
    exact hle₁ w.im
  · intro w hw
    have heq : w = (σ₂ : ℂ) + (w.im : ℂ) * I := by rw [← hw, Complex.re_add_im]
    conv_lhs => rw [heq]
    exact hle₂ w.im

/-- Vertical-strip Phragmén–Lindelöf theorem under an explicit double-exponential growth bound
`‖f z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|))` with `c < π / (σ₂ - σ₁)`. -/
theorem phragmen_lindelof_vertical_strip_of_exp_le {σ₁ σ₂ A B c C : ℝ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (_hA : 0 ≤ A) (hc : c < π / (σ₂ - σ₁))
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hle₁ : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (hle₂ : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    {z : ℂ} (hz : z ∈ verticalStripClosed σ₁ σ₂) :
    ‖f z‖ ≤ C :=
  phragmen_lindelof_vertical_strip_lines hf ⟨c, hc, B, isBigO_of_exp_le hbound⟩ hle₁ hle₂ hz

/-- Vertical-strip Phragmén–Lindelöf theorem under finite-order vertical exponential growth
`‖f z‖ ≤ A * Real.exp (B * (|z.im| + 2) ^ γ)` inside `verticalStripOpen σ₁ σ₂`. -/
theorem phragmen_lindelof_vertical_strip_of_exp_rpow_le {σ₁ σ₂ A B γ C : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hA : 0 ≤ A)
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖f z‖ ≤ A * Real.exp (B * (|z.im| + 2) ^ γ))
    (hle₁ : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (hle₂ : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    {z : ℂ} (hz : z ∈ verticalStripClosed σ₁ σ₂) :
    ‖f z‖ ≤ C := by
  let c : ℝ := π / (2 * (σ₂ - σ₁))
  have hc_pos : 0 < c := div_pos Real.pi_pos (by linarith)
  have hc_lt : c < π / (σ₂ - σ₁) := by
    have hpos : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos (sub_pos.mpr hσ)
    have hc_eq : c = (π / (σ₂ - σ₁)) / 2 := by
      simp only [c]
      field_simp
    linarith
  obtain ⟨A', B', hA', _, hgr⟩ := exp_rpow_le_exp_exp (γ := γ) (B := max B 0) hc_pos (le_max_right B 0)
  refine phragmen_lindelof_vertical_strip_of_exp_le (B := B') hf (mul_nonneg hA hA') hc_lt
    (fun w hw ↦ ?_) hle₁ hle₂ hz
  have h1 : B * (|w.im| + 2) ^ γ ≤ max B 0 * (|w.im| + 2) ^ γ :=
    mul_le_mul_of_nonneg_right (le_max_left B 0) (Real.rpow_nonneg (by positivity) γ)
  calc
    ‖f w‖ ≤ A * Real.exp (B * (|w.im| + 2) ^ γ) := hbound w hw
    _ ≤ A * Real.exp (max B 0 * (|w.im| + 2) ^ γ) := by gcongr
    _ ≤ A * (A' * Real.exp (B' * Real.exp (c * |w.im|))) :=
      mul_le_mul_of_nonneg_left (hgr |w.im| (abs_nonneg _)) hA
    _ = (A * A') * Real.exp (B' * Real.exp (c * |w.im|)) := by ring

/-- Uniqueness on a vertical strip: if `f` vanishes on both vertical boundaries and satisfies
the Phragmén–Lindelöf vertical growth condition, then `f` vanishes on `verticalStripClosed`. -/
theorem eq_zero_on_vertical_strip {σ₁ σ₂ : ℝ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hB : ∃ c < π / (σ₂ - σ₁), ∃ B,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (h₀₁ : ∀ z : ℂ, z.re = σ₁ → f z = 0)
    (h₀₂ : ∀ z : ℂ, z.re = σ₂ → f z = 0) :
    EqOn f 0 (verticalStripClosed σ₁ σ₂) :=
  PhragmenLindelof.eq_zero_on_vertical_strip hf hB h₀₁ h₀₂

/-- Identity principle on a vertical strip: two functions agreeing on both vertical boundaries
and satisfying the vertical growth bound agree throughout `verticalStripClosed`. -/
theorem eqOn_vertical_strip {σ₁ σ₂ : ℝ} {f g : ℂ → E}
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hg : DiffContOnCl ℂ g (verticalStripOpen σ₁ σ₂))
    (hBf : ∃ c < π / (σ₂ - σ₁), ∃ B,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hBg : ∃ c < π / (σ₂ - σ₁), ∃ B,
      g =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (h₁ : ∀ z : ℂ, z.re = σ₁ → f z = g z)
    (h₂ : ∀ z : ℂ, z.re = σ₂ → f z = g z) :
    EqOn f g (verticalStripClosed σ₁ σ₂) :=
  PhragmenLindelof.eqOn_vertical_strip hf hBf hg hBg h₁ h₂

end VerticalStrip

/-!
### Section 2: Half-Strip Phragmén–Lindelöf Theorems
-/

section HalfStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Phragmén–Lindelöf theorem on an upper half-strip** `σ₁ ≤ Re s ≤ σ₂`, `t₀ ≤ Im s`:
if `f` is holomorphic on `upperHalfStripOpen σ₁ σ₂ t₀`, continuous on its closure, satisfies
`‖f z‖ ≤ A * Real.exp (B * Real.exp (c * z.im))` with `c < π / (σ₂ - σ₁)`, and is bounded by `M`
on the three boundary segments (`Re s = σ₁`, `Re s = σ₂`, and `Im s = t₀`), then `‖f z‖ ≤ M`
throughout `upperHalfStripClosed σ₁ σ₂ t₀`. -/
theorem phragmen_lindelof_upper_half_strip {σ₁ σ₂ t₀ A B c M : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (upperHalfStripOpen σ₁ σ₂ t₀))
    (hA : 0 ≤ A) (hc : c < π / (σ₂ - σ₁))
    (hbound : ∀ z ∈ upperHalfStripOpen σ₁ σ₂ t₀, ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * z.im)))
    (hleft : ∀ t : ℝ, t₀ ≤ t → ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ M)
    (hright : ∀ t : ℝ, t₀ ≤ t → ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ M)
    (hbot : ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ‖f ((σ : ℂ) + (t₀ : ℂ) * I)‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalfStripClosed σ₁ σ₂ t₀) :
    ‖f z‖ ≤ M := by
  have hM_nonneg : 0 ≤ M := (norm_nonneg _).trans (hbot σ₁ ⟨le_rfl, hσ.le⟩)
  let a : ℝ := (σ₁ + σ₂) / 2
  let d : ℝ := (max c 0 + π / (σ₂ - σ₁)) / 2
  have h_half_pi_pos : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos (sub_pos.mpr hσ)
  have hd_pos : 0 < d := by
    have h1 : 0 ≤ max c 0 := le_max_right _ _
    simp only [d]
    linarith
  have hc_lt_d : c < d := by
    have h1 : c ≤ max c 0 := le_max_left _ _
    have h2 : max c 0 < π / (σ₂ - σ₁) := max_lt hc h_half_pi_pos
    simp only [d]
    linarith
  have hd_lt : d < π / (σ₂ - σ₁) := by
    have h2 : max c 0 < π / (σ₂ - σ₁) := max_lt hc h_half_pi_pos
    simp only [d]
    linarith
  let δ : ℝ := π / 2 - d * (σ₂ - σ₁) / 2
  have hδ_pos : 0 < δ := by
    have h_eq : d * (σ₂ - σ₁) / 2 < π / 2 := by
      have hmul := mul_lt_mul_of_pos_right hd_lt (sub_pos.mpr hσ)
      rw [div_mul_cancel₀ _ (sub_pos.mpr hσ).ne'] at hmul
      linarith
    dsimp only [δ]
    linarith
  have hδ_lt_pi : δ < π := by
    have : 0 ≤ d * (σ₂ - σ₁) / 2 := by positivity
    dsimp only [δ]
    linarith [Real.pi_pos]
  let η : ℝ := Real.sin δ
  have hη_pos : 0 < η := Real.sin_pos_of_pos_of_lt_pi hδ_pos hδ_lt_pi
  let dampener : ℝ → ℂ → ℂ := fun ε s ↦
    Complex.exp (-(ε : ℂ) * Complex.exp (-I * (d : ℂ) * (s - (a : ℂ))))
  have hdamp_norm : ∀ (ε : ℝ) (s : ℂ),
      ‖dampener ε s‖ = Real.exp (-ε * Real.exp (d * s.im) * Real.cos (d * (s.re - a))) := by
    intro ε s
    simp only [dampener, Complex.norm_exp]
    congr 1
    have hre : (-I * (d : ℂ) * (s - (a : ℂ))).re = d * s.im := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
    have him : (-I * (d : ℂ) * (s - (a : ℂ))).im = -(d * (s.re - a)) := by
      simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
    have hexp_re : (Complex.exp (-I * (d : ℂ) * (s - (a : ℂ)))).re =
        Real.exp (d * s.im) * Real.cos (d * (s.re - a)) := by
      rw [Complex.exp_re, hre, him, Real.cos_neg]
    rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero, hexp_re]
    ring
  have hcos_ge : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → η ≤ Real.cos (d * (s.re - a)) := by
    intro s hs₁ hs₂
    have habs : |d * (s.re - a)| ≤ π / 2 - δ := by
      have hre_abs : |s.re - a| ≤ (σ₂ - σ₁) / 2 := by
        rw [abs_le]
        simp only [a]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos hd_pos]
      calc
        d * |s.re - a| ≤ d * ((σ₂ - σ₁) / 2) := mul_le_mul_of_nonneg_left hre_abs hd_pos.le
        _ = π / 2 - δ := by simp only [δ]; ring
    have hcos_eq : η = Real.cos (π / 2 - δ) := by rw [Real.cos_pi_div_two_sub]
    rw [hcos_eq, ← Real.cos_abs (d * (s.re - a))]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) ?_ habs
    linarith [Real.pi_pos]
  have hdamp_le_one : ∀ (ε : ℝ), 0 < ε → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖dampener ε s‖ ≤ 1 := by
    intro ε hε s hs₁ hs₂
    rw [hdamp_norm, Real.exp_le_one_iff]
    have h1 : 0 ≤ Real.cos (d * (s.re - a)) := hη_pos.le.trans (hcos_ge s hs₁ hs₂)
    have h2 : 0 ≤ ε * Real.exp (d * s.im) * Real.cos (d * (s.re - a)) := by positivity
    linarith
  have hdamp_decay : ∀ (ε : ℝ), 0 < ε → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖dampener ε s‖ ≤ Real.exp (-ε * η * Real.exp (d * s.im)) := by
    intro ε hε s hs₁ hs₂
    rw [hdamp_norm]
    refine Real.exp_le_exp.mpr ?_
    have h1 : η ≤ Real.cos (d * (s.re - a)) := hcos_ge s hs₁ hs₂
    have h2 : ε * Real.exp (d * s.im) * η ≤ ε * Real.exp (d * s.im) * Real.cos (d * (s.re - a)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hε_bound : ∀ ε : ℝ, 0 < ε → ‖dampener ε z • f z‖ ≤ M + ε := by
    intro ε hε
    have hdc : 0 < d - c := sub_pos.mpr hc_lt_d
    have htend_exp : Tendsto (fun T : ℝ ↦ Real.exp ((c - d) * T)) atTop (𝓝 0) := by
      have heq : (fun T : ℝ ↦ Real.exp ((c - d) * T)) = fun T ↦ Real.exp (-(d - c) * T) := by
        ext T; congr 1; ring
      rw [heq]
      have htend_neg : Tendsto (fun T : ℝ ↦ -(d - c) * T) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hdc) tendsto_id
      exact Real.tendsto_exp_atBot.comp htend_neg
    have hev_small : ∀ᶠ T : ℝ in atTop,
        max B 0 * Real.exp ((c - d) * T) ≤ (ε * η) / 2 := by
      have htend_mul : Tendsto (fun T : ℝ ↦ max B 0 * Real.exp ((c - d) * T)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := max B 0)).mul htend_exp
      exact htend_mul.eventually (ge_mem_nhds (half_pos (mul_pos hε hη_pos)))
    have htend_inf : Tendsto (fun T : ℝ ↦ Real.exp (-(ε * η / 2) * Real.exp (d * T))) atTop (𝓝 0) := by
      have htend_d : Tendsto (fun T : ℝ ↦ Real.exp (d * T)) atTop atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hd_pos)
      have htend_neg : Tendsto (fun T : ℝ ↦ -(ε * η / 2) * Real.exp (d * T)) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr (half_pos (mul_pos hε hη_pos))) htend_d
      exact Real.tendsto_exp_atBot.comp htend_neg
    have hev_top : ∀ᶠ T : ℝ in atTop,
        A * Real.exp (-(ε * η / 2) * Real.exp (d * T)) ≤ M + ε := by
      have hMε_pos : 0 < M + ε := by linarith
      have htend_A : Tendsto (fun T : ℝ ↦ A * Real.exp (-(ε * η / 2) * Real.exp (d * T)))
          atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := A)).mul htend_inf
      exact htend_A.eventually (ge_mem_nhds hMε_pos)
    have hev_T : ∀ᶠ T : ℝ in atTop, z.im < T ∧ t₀ < T :=
      (eventually_gt_atTop z.im).and (eventually_gt_atTop t₀)
    obtain ⟨T, ⟨hzT, ht₀T⟩, hT_small, hT_top⟩ := (hev_T.and (hev_small.and hev_top)).exists
    let rect : Set ℂ := {s : ℂ | σ₁ < s.re ∧ s.re < σ₂ ∧ t₀ < s.im ∧ s.im < T}
    have hrect_open : IsOpen rect := by
      have heq : rect =
          (Complex.re ⁻¹' Set.Ioo σ₁ σ₂) ∩ (Complex.im ⁻¹' Set.Ioo t₀ T) := by
        ext s; simp [rect, and_assoc]
      rw [heq]
      exact (isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im)
    have hrect_bdd : Bornology.IsBounded rect := by
      let R : ℝ := max |σ₁| |σ₂| + max |t₀| |T|
      have hsub : rect ⊆ Metric.closedBall (0 : ℂ) R := by
        intro s hs
        rw [Metric.mem_closedBall, dist_zero_right]
        have hre : |s.re| ≤ max |σ₁| |σ₂| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hs.1],
            by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hs.2.1]⟩
        have him : |s.im| ≤ max |t₀| |T| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le t₀, le_max_left |t₀| |T|, hs.2.2.1],
            by linarith [le_abs_self T, le_max_right |t₀| |T|, hs.2.2.2]⟩
        calc
          ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * I‖ := by rw [Complex.re_add_im]
          _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * I‖ := norm_add_le _ _
          _ = |s.re| + |s.im| := by simp
          _ ≤ R := add_le_add hre him
      exact isBounded_closedBall.subset hsub
    have hrect_sub_strip : rect ⊆ upperHalfStripOpen σ₁ σ₂ t₀ :=
      fun _ hs ↦ ⟨hs.1, hs.2.1, hs.2.2.1⟩
    have hrect_cl_sub : closure rect ⊆ {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₀ ≤ s.im ∧ s.im ≤ T} := by
      refine closure_minimal (fun s hs ↦ ⟨hs.1.le, hs.2.1.le, hs.2.2.1.le, hs.2.2.2.le⟩) ?_
      have heq : {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₀ ≤ s.im ∧ s.im ≤ T} =
          (Complex.re ⁻¹' Set.Icc σ₁ σ₂) ∩ (Complex.im ⁻¹' Set.Icc t₀ T) := by
        ext s; simp [and_assoc]
      rw [heq]
      exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    have hgd : DiffContOnCl ℂ (fun s ↦ dampener ε s • f s) rect := by
      have hdamp_diff : Differentiable ℂ (dampener ε) := by
        refine Differentiable.cexp (Differentiable.const_mul ?_ _)
        exact Differentiable.cexp (Differentiable.const_mul (differentiable_id.sub_const _) _)
      have hfd_rect : DiffContOnCl ℂ f rect := hf.mono hrect_sub_strip
      exact ⟨(hdamp_diff.differentiableOn).smul hfd_rect.differentiableOn,
        (hdamp_diff.continuous.continuousOn).smul hfd_rect.continuousOn⟩
    have hfront : ∀ s ∈ frontier rect, ‖dampener ε s • f s‖ ≤ M + ε := by
      intro s hs
      have hs_cl : s ∈ {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₀ ≤ s.im ∧ s.im ≤ T} :=
        hrect_cl_sub hs.1
      have hs_not_in : s ∉ rect := hrect_open.interior_eq ▸ hs.2
      rw [norm_smul]
      have hle1 : ‖dampener ε s‖ ≤ 1 := hdamp_le_one ε hε s hs_cl.1 hs_cl.2.1
      have hre_or : s.re = σ₁ ∨ s.re = σ₂ ∨ s.im = t₀ ∨ (σ₁ < s.re ∧ s.re < σ₂ ∧ s.im = T) := by
        rcases eq_or_lt_of_le hs_cl.1 with h1 | h1
        · exact Or.inl h1.symm
        rcases eq_or_lt_of_le hs_cl.2.1 with h2 | h2
        · exact Or.inr (Or.inl h2)
        rcases eq_or_lt_of_le hs_cl.2.2.1 with h3 | h3
        · exact Or.inr (Or.inr (Or.inl h3.symm))
        rcases eq_or_lt_of_le hs_cl.2.2.2 with h4 | h4
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h4⟩))
        · exact False.elim (hs_not_in ⟨h1, h2, h3, h4⟩)
      rcases hre_or with hre₁ | hre₂ | him₀ | ⟨hre₁, hre₂, himT⟩
      · have hs_eq : s = (σ₁ : ℂ) + (s.im : ℂ) * I := by rw [← hre₁, Complex.re_add_im]
        have hf_le : ‖f s‖ ≤ M := hs_eq ▸ hleft s.im hs_cl.2.2.1
        exact (mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)).trans
          (by linarith)
      · have hs_eq : s = (σ₂ : ℂ) + (s.im : ℂ) * I := by rw [← hre₂, Complex.re_add_im]
        have hf_le : ‖f s‖ ≤ M := hs_eq ▸ hright s.im hs_cl.2.2.1
        exact (mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)).trans
          (by linarith)
      · have hs_eq : s = (s.re : ℂ) + (t₀ : ℂ) * I := by rw [← him₀, Complex.re_add_im]
        have hf_le : ‖f s‖ ≤ M := hs_eq ▸ hbot s.re ⟨hs_cl.1, hs_cl.2.1⟩
        exact (mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)).trans
          (by linarith)
      · have hs_open : s ∈ upperHalfStripOpen σ₁ σ₂ t₀ := ⟨hre₁, hre₂, himT ▸ ht₀T⟩
        have hf_le : ‖f s‖ ≤ A * Real.exp (B * Real.exp (c * T)) := himT ▸ hbound s hs_open
        have hd_le : ‖dampener ε s‖ ≤ Real.exp (-ε * η * Real.exp (d * T)) :=
          himT ▸ hdamp_decay ε hε s hs_cl.1 hs_cl.2.1
        have hB_le : B * Real.exp (c * T) ≤ (ε * η / 2) * Real.exp (d * T) := by
          calc
            B * Real.exp (c * T) ≤ max B 0 * Real.exp (c * T) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
            _ = (max B 0 * Real.exp ((c - d) * T)) * Real.exp (d * T) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 2
              ring
            _ ≤ (ε * η / 2) * Real.exp (d * T) :=
              mul_le_mul_of_nonneg_right hT_small (Real.exp_pos _).le
        calc
          ‖dampener ε s‖ * ‖f s‖
            ≤ Real.exp (-ε * η * Real.exp (d * T)) * (A * Real.exp (B * Real.exp (c * T))) :=
              mul_le_mul hd_le hf_le (norm_nonneg _) (Real.exp_pos _).le
          _ ≤ Real.exp (-ε * η * Real.exp (d * T)) *
                (A * Real.exp ((ε * η / 2) * Real.exp (d * T))) := by gcongr
          _ = A * Real.exp (-(ε * η / 2) * Real.exp (d * T)) := by
            rw [mul_left_comm, ← Real.exp_add]
            congr 2
            ring
          _ ≤ M + ε := hT_top
    have hz_cl_rect : z ∈ closure rect := by
      -- Since `z ∈ upperHalfStripClosed σ₁ σ₂ t₀` and `z.im < T`, approximate `z` inside `rect`
      rw [Metric.mem_closure_iff]
      intro ν hν
      let m : ℝ := (σ₁ + σ₂) / 2
      let t_mid : ℝ := (t₀ + T) / 2
      let p : ℂ := (m : ℂ) + (t_mid : ℂ) * I
      let θ : ℝ := min (1 / 2) (ν / (2 * (‖p - z‖ + 1)))
      have hθ_pos : 0 < θ := lt_min (by norm_num) (div_pos hν (by positivity))
      have hθ_lt : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
      let w : ℂ := z + (θ : ℂ) * (p - z)
      have hp_re : p.re = m := by simp [p]
      have hp_im : p.im = t_mid := by simp [p]
      have hw_re : w.re = (1 - θ) * z.re + θ * m := by
        simp only [w, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, zero_mul, sub_zero, hp_re]
        ring
      have hw_im : w.im = (1 - θ) * z.im + θ * t_mid := by
        simp only [w, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_im, zero_mul, add_zero, hp_im]
        ring
      have hm_gt : σ₁ < m := by simp only [m]; linarith
      have hm_lt : m < σ₂ := by simp only [m]; linarith
      have ht_gt : t₀ < t_mid := by simp only [t_mid]; linarith
      have ht_lt : t_mid < T := by simp only [t_mid]; linarith
      have hw_mem : w ∈ rect := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hw_re]; nlinarith [hz.1]
        · rw [hw_re]; nlinarith [hz.2.1]
        · rw [hw_im]; nlinarith [hz.2.2]
        · rw [hw_im]; nlinarith [hzT]
      have hw_dist : dist z w < ν := by
        rw [dist_eq_norm]
        have hzw : z - w = -(θ : ℂ) * (p - z) := by simp only [w]; ring
        rw [hzw, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ_pos]
        have hθ_le : θ ≤ ν / (2 * (‖p - z‖ + 1)) := min_le_right _ _
        calc
          θ * ‖p - z‖ ≤ (ν / (2 * (‖p - z‖ + 1))) * ‖p - z‖ :=
            mul_le_mul_of_nonneg_right hθ_le (norm_nonneg _)
          _ < ν := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg (p - z)]
      exact ⟨w, hw_mem, hw_dist⟩
    exact Complex.norm_le_of_forall_mem_frontier_norm_le hrect_bdd hgd hfront hz_cl_rect
  have htend_damp : Tendsto (fun ε : ℝ ↦ ‖dampener ε z • f z‖) (𝓝[>] 0) (𝓝 ‖f z‖) := by
    have hcont : Continuous (fun ε : ℝ ↦ ‖dampener ε z • f z‖) := by
      refine Continuous.norm ?_
      refine Continuous.smul ?_ continuous_const
      refine Complex.continuous_exp.comp ?_
      exact ((Complex.continuous_ofReal.neg).mul continuous_const)
    have h0 : ‖dampener 0 z • f z‖ = ‖f z‖ := by simp [dampener]
    simpa [h0] using ((hcont.continuousAt (x := (0 : ℝ))).tendsto).mono_left nhdsWithin_le_nhds
  have htend_rhs : Tendsto (fun ε : ℝ ↦ M + ε) (𝓝[>] 0) (𝓝 M) := by
    have hcont : Continuous (fun ε : ℝ ↦ M + ε) := continuous_const.add continuous_id
    simpa using ((hcont.continuousAt (x := (0 : ℝ))).tendsto).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto htend_damp htend_rhs
    (eventually_mem_nhdsWithin.mono fun ε hε ↦ hε_bound ε hε)

/-- **Phragmén–Lindelöf theorem on a lower half-strip** `σ₁ ≤ Re s ≤ σ₂`, `Im s ≤ t₁`:
follows from `phragmen_lindelof_upper_half_strip` via the reflection `s ↦ -s`. -/
theorem phragmen_lindelof_lower_half_strip {σ₁ σ₂ t₁ A B c M : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f {z : ℂ | σ₁ < z.re ∧ z.re < σ₂ ∧ z.im < t₁})
    (hA : 0 ≤ A) (hc : c < π / (σ₂ - σ₁))
    (hbound : ∀ z, σ₁ < z.re → z.re < σ₂ → z.im < t₁ →
      ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * (-z.im))))
    (hleft : ∀ t : ℝ, t ≤ t₁ → ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ M)
    (hright : ∀ t : ℝ, t ≤ t₁ → ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ M)
    (htop : ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ‖f ((σ : ℂ) + (t₁ : ℂ) * I)‖ ≤ M)
    {z : ℂ} (hz₁ : σ₁ ≤ z.re) (hz₂ : z.re ≤ σ₂) (hz_im : z.im ≤ t₁) :
    ‖f z‖ ≤ M := by
  let g : ℂ → E := fun s ↦ f (-s)
  have hmaps : MapsTo Neg.neg (upperHalfStripOpen (-σ₂) (-σ₁) (-t₁))
      {w : ℂ | σ₁ < w.re ∧ w.re < σ₂ ∧ w.im < t₁} := by
    intro s hs
    exact ⟨by simp; linarith [hs.2.1], by simp; linarith [hs.1], by simp; linarith [hs.2.2]⟩
  have hgd : DiffContOnCl ℂ g (upperHalfStripOpen (-σ₂) (-σ₁) (-t₁)) :=
    hf.comp differentiable_neg.diffContOnCl hmaps
  have hσ_neg : -σ₂ < -σ₁ := by linarith
  have hc_neg : c < π / (-σ₁ - -σ₂) := by
    have hden_eq : (-σ₁ : ℝ) - -σ₂ = σ₂ - σ₁ := by ring
    rwa [hden_eq]
  have hz_neg : -z ∈ upperHalfStripClosed (-σ₂) (-σ₁) (-t₁) :=
    ⟨by simp; linarith, by simp; linarith, by simp; linarith⟩
  have hg_le := phragmen_lindelof_upper_half_strip (σ₁ := -σ₂) (σ₂ := -σ₁) (t₀ := -t₁) (B := B)
    hσ_neg hgd hA hc_neg
    (fun s hs ↦ by
      dsimp only [g]
      have him : s.im = -(-s).im := by simp
      rw [him]
      exact hbound (-s) (hmaps hs).1 (hmaps hs).2.1 (hmaps hs).2.2)
    (fun t ht ↦ by
      dsimp only [g]
      have heq : -(((-σ₂ : ℝ) : ℂ) + (t : ℂ) * I) = (σ₂ : ℂ) + ((-t : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [heq]
      exact hright (-t) (by linarith))
    (fun t ht ↦ by
      dsimp only [g]
      have heq : -(((-σ₁ : ℝ) : ℂ) + (t : ℂ) * I) = (σ₁ : ℂ) + ((-t : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [heq]
      exact hleft (-t) (by linarith))
    (fun σ hσmem ↦ by
      dsimp only [g]
      have heq : -((σ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) = ((-σ : ℝ) : ℂ) + (t₁ : ℂ) * I := by
        push_cast; ring
      rw [heq]
      exact htop (-σ) ⟨by linarith [hσmem.2], by linarith [hσmem.1]⟩)
    hz_neg
  simpa [g] using hg_le

end HalfStrip

/-!
### Section 3: Polynomial Vertical-Growth Interpolation
-/

section PolyInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma poly_weight_re_im (σ₁ σ₂ α₁ α₂ : ℝ) (s : ℂ) :
    let ℓ : ℂ → ℂ := fun w ↦
      ((α₁ : ℂ) * ((σ₂ : ℂ) - w) + (α₂ : ℂ) * (w - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)
    (ℓ s).re = linearInterp σ₁ σ₂ α₁ α₂ s.re ∧ (ℓ s).im = (α₂ - α₁) / (σ₂ - σ₁) * s.im := by
  intro ℓ
  have hnum_re : ((α₁ : ℂ) * ((σ₂ : ℂ) - s) + (α₂ : ℂ) * (s - (σ₁ : ℂ))).re =
      α₁ * (σ₂ - s.re) + α₂ * (s.re - σ₁) := by
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re]
  have hnum_im : ((α₁ : ℂ) * ((σ₂ : ℂ) - s) + (α₂ : ℂ) * (s - (σ₁ : ℂ))).im =
      (α₂ - α₁) * s.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
    ring
  constructor
  · change (((α₁ : ℂ) * ((σ₂ : ℂ) - s) + (α₂ : ℂ) * (s - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)).re = _
    rw [Complex.div_ofReal_re, hnum_re, linearInterp]
    ring
  · change (((α₁ : ℂ) * ((σ₂ : ℂ) - s) + (α₂ : ℂ) * (s - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)).im = _
    rw [Complex.div_ofReal_im, hnum_im]
    ring

private lemma poly_weight_diffAt (σ₁ σ₂ α₁ α₂ : ℝ) (s : ℂ) (hs_im : 0 ≤ s.im) :
    DifferentiableAt ℂ (fun w : ℂ ↦ ((2 : ℂ) - I * w) ^ (-(((α₁ : ℂ) * ((σ₂ : ℂ) - w) +
      (α₂ : ℂ) * (w - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)))) s := by
  have hw_diff : DifferentiableAt ℂ (fun w : ℂ ↦ (2 : ℂ) - I * w) s :=
    (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)
  have hℓ_diff : DifferentiableAt ℂ (fun w : ℂ ↦
      -(((α₁ : ℂ) * ((σ₂ : ℂ) - w) + (α₂ : ℂ) * (w - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ))) s := by
    refine DifferentiableAt.neg (DifferentiableAt.div_const ?_ _)
    exact ((differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)).add
      ((differentiableAt_const _).mul (differentiableAt_id.sub (differentiableAt_const _)))
  have h_slit : (2 : ℂ) - I * s ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp [Complex.sub_re, Complex.mul_re]
    linarith
  exact hw_diff.cpow hℓ_diff h_slit

private lemma poly_weight_bounds {σ₁ σ₂ t₀ α₁ α₂ : ℝ} (hσ : σ₁ < σ₂) (ht₀ : 0 ≤ t₀) :
    let S : ℝ := max |σ₁| |σ₂|
    let K : ℝ := max |α₁| |α₂|
    let B_arg : ℝ := (π / 2) * S * |α₂ - α₁| / (σ₂ - σ₁)
    let C_lo : ℝ := (1 + S / 2) ^ (-K) * Real.exp (-B_arg)
    let C_hi : ℝ := (1 + S / 2) ^ K * Real.exp B_arg
    ∀ s ∈ upperHalfStripClosed σ₁ σ₂ t₀,
      C_lo * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
        ‖((2 : ℂ) - I * s) ^ (-(((α₁ : ℂ) * ((σ₂ : ℂ) - s) +
          (α₂ : ℂ) * (s - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)))‖ ∧
      ‖((2 : ℂ) - I * s) ^ (-(((α₁ : ℂ) * ((σ₂ : ℂ) - s) +
        (α₂ : ℂ) * (s - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)))‖ ≤
        C_hi * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := by
  intro S K B_arg C_lo C_hi s hs
  have hden : 0 < σ₂ - σ₁ := sub_pos.mpr hσ
  have hs_im : 0 ≤ s.im := ht₀.trans hs.2.2
  have hst_pos : 0 < s.im + 2 := by linarith
  have hS_nonneg : 0 ≤ S := by positivity
  have hK_nonneg : 0 ≤ K := by positivity
  have h_re_im := poly_weight_re_im σ₁ σ₂ α₁ α₂ s
  dsimp only at h_re_im
  have hw_re : ((2 : ℂ) - I * s).re = s.im + 2 := by
    simp [Complex.sub_re, Complex.mul_re]; ring
  have hw_im : ((2 : ℂ) - I * s).im = -s.re := by
    simp [Complex.sub_im, Complex.mul_im]
  have hw_ne : (2 : ℂ) - I * s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hw_re, Complex.zero_re] at this
    linarith
  have hnorm_ge : s.im + 2 ≤ ‖(2 : ℂ) - I * s‖ := by
    calc
      s.im + 2 = |((2 : ℂ) - I * s).re| := by rw [hw_re, abs_of_pos hst_pos]
      _ ≤ ‖(2 : ℂ) - I * s‖ := Complex.abs_re_le_norm _
  have hsre_abs : |s.re| ≤ S := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hs.1],
      by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hs.2.1]⟩
  have hnorm_le : ‖(2 : ℂ) - I * s‖ ≤ (1 + S / 2) * (s.im + 2) := by
    calc
      ‖(2 : ℂ) - I * s‖ = ‖((((2 : ℂ) - I * s).re : ℂ)) + (((2 : ℂ) - I * s).im : ℂ) * I‖ := by
        rw [Complex.re_add_im]
      _ ≤ ‖(((2 : ℂ) - I * s).re : ℂ)‖ + ‖(((2 : ℂ) - I * s).im : ℂ) * I‖ := norm_add_le _ _
      _ = |((2 : ℂ) - I * s).re| + |((2 : ℂ) - I * s).im| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ = (s.im + 2) + |s.re| := by rw [hw_re, hw_im, abs_of_pos hst_pos, abs_neg]
      _ ≤ (s.im + 2) + S := by linarith [hsre_abs]
      _ ≤ (s.im + 2) + (S / 2) * (s.im + 2) := by nlinarith [hS_nonneg, hst_pos]
      _ = (1 + S / 2) * (s.im + 2) := by ring
  let ℓs : ℂ := ((α₁ : ℂ) * ((σ₂ : ℂ) - s) + (α₂ : ℂ) * (s - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)
  have hnorm_eq : ‖((2 : ℂ) - I * s) ^ (-ℓs)‖ =
      ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) *
        Real.exp (-(Complex.arg ((2 : ℂ) - I * s) * (-ℓs).im)) := by
    rw [Complex.norm_cpow_of_ne_zero hw_ne, Complex.neg_re, h_re_im.1, div_eq_mul_inv,
      ← Real.exp_neg]
  have hbase_ge_one : 1 ≤ 1 + S / 2 := by linarith
  have hp_abs : |-linearInterp σ₁ σ₂ α₁ α₂ s.re| ≤ K := by
    rw [abs_neg]
    exact abs_linearInterp_le hs.1 hs.2.1 hσ
  have hp_bounds : -K ≤ -linearInterp σ₁ σ₂ α₁ α₂ s.re ∧ -linearInterp σ₁ σ₂ α₁ α₂ s.re ≤ K :=
    abs_le.mp hp_abs
  have hrpow_bounds :
      (1 + S / 2) ^ (-K) * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
        ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ∧
      ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
        (1 + S / 2) ^ K * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := by
    by_cases hp : 0 ≤ -linearInterp σ₁ σ₂ α₁ α₂ s.re
    · have hlo1 : (1 + S / 2) ^ (-K) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hbase_ge_one (by linarith)
      have hlo2 : (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
          ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
        Real.rpow_le_rpow hst_pos.le hnorm_ge hp
      have hhi1 : ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
          ((1 + S / 2) * (s.im + 2)) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm_le hp
      have hhi2 : (1 + S / 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤ (1 + S / 2) ^ K :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge_one hp_bounds.2
      rw [Real.mul_rpow (by linarith) hst_pos.le] at hhi1
      refine ⟨?_, ?_⟩
      · calc
          (1 + S / 2) ^ (-K) * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re)
            ≤ 1 * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
              mul_le_mul_of_nonneg_right hlo1 (Real.rpow_nonneg hst_pos.le _)
          _ = (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := one_mul _
          _ ≤ ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := hlo2
      · exact hhi1.trans (mul_le_mul_of_nonneg_right hhi2 (Real.rpow_nonneg hst_pos.le _))
    · push Not at hp
      have hhi1 : 1 ≤ (1 + S / 2) ^ K := Real.one_le_rpow hbase_ge_one hK_nonneg
      have hhi2 : ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
          (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
        Real.rpow_le_rpow_of_nonpos hst_pos hnorm_ge hp.le
      have hlo1 : ((1 + S / 2) * (s.im + 2)) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤
          ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hw_ne) hnorm_le hp.le
      have hlo2 : (1 + S / 2) ^ (-K) ≤ (1 + S / 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge_one hp_bounds.1
      rw [Real.mul_rpow (by linarith) hst_pos.le] at hlo1
      refine ⟨?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_right hlo2 (Real.rpow_nonneg hst_pos.le _)).trans hlo1
      · calc
          ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re)
            ≤ (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := hhi2
          _ = 1 * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := (one_mul _).symm
          _ ≤ (1 + S / 2) ^ K * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
            mul_le_mul_of_nonneg_right hhi1 (Real.rpow_nonneg hst_pos.le _)
  have harg_le : |Complex.arg ((2 : ℂ) - I * s)| ≤ (π / 2) * S / (s.im + 2) := by
    have harg_half_pi : |Complex.arg ((2 : ℂ) - I * s)| ≤ π / 2 := by
      rw [Complex.arg_of_re_nonneg (by rw [hw_re]; exact hst_pos.le), abs_le]
      exact ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
    have hjordan := Real.mul_abs_le_abs_sin harg_half_pi
    rw [Complex.sin_arg, hw_im, abs_div, abs_neg, abs_of_pos (norm_pos_iff.mpr hw_ne)] at hjordan
    have h_sin_le : |s.re| / ‖(2 : ℂ) - I * s‖ ≤ S / (s.im + 2) :=
      div_le_div₀ hS_nonneg hsre_abs hst_pos hnorm_ge
    have h2_le : 2 / π * |Complex.arg ((2 : ℂ) - I * s)| ≤ S / (s.im + 2) :=
      hjordan.trans h_sin_le
    have hpi2 : 0 < π / 2 := Real.pi_div_two_pos
    calc
      |Complex.arg ((2 : ℂ) - I * s)| = (π / 2) * (2 / π * |Complex.arg ((2 : ℂ) - I * s)|) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (π / 2) * (S / (s.im + 2)) := mul_le_mul_of_nonneg_left h2_le hpi2.le
      _ = (π / 2) * S / (s.im + 2) := by ring
  have him_le : |(-ℓs).im| ≤ |α₂ - α₁| / (σ₂ - σ₁) * (s.im + 2) := by
    rw [Complex.neg_im, h_re_im.2, abs_neg, abs_mul, abs_div, abs_of_pos hden,
      abs_of_nonneg hs_im]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (abs_nonneg _) hden.le)
  have hprod_arg : |-(Complex.arg ((2 : ℂ) - I * s) * (-ℓs).im)| ≤ B_arg := by
    rw [abs_neg, abs_mul]
    calc
      |Complex.arg ((2 : ℂ) - I * s)| * |(-ℓs).im|
        ≤ ((π / 2) * S / (s.im + 2)) * (|α₂ - α₁| / (σ₂ - σ₁) * (s.im + 2)) :=
          mul_le_mul harg_le him_le (abs_nonneg _) (by positivity)
      _ = (π / 2) * S * |α₂ - α₁| / (σ₂ - σ₁) := by
        field_simp [hst_pos.ne', hden.ne']
  have hexp_lo : Real.exp (-B_arg) ≤ Real.exp (-(Complex.arg ((2 : ℂ) - I * s) * (-ℓs).im)) :=
    Real.exp_le_exp.mpr (abs_le.mp hprod_arg).1
  have hexp_hi : Real.exp (-(Complex.arg ((2 : ℂ) - I * s) * (-ℓs).im)) ≤ Real.exp B_arg :=
    Real.exp_le_exp.mpr (abs_le.mp hprod_arg).2
  change C_lo * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤ ‖((2 : ℂ) - I * s) ^ (-ℓs)‖ ∧
    ‖((2 : ℂ) - I * s) ^ (-ℓs)‖ ≤ C_hi * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re)
  rw [hnorm_eq]
  constructor
  · calc
      C_lo * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re)
        = ((1 + S / 2) ^ (-K) * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re)) * Real.exp (-B_arg) := by
          simp only [C_lo]; ring
      _ ≤ ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) *
            Real.exp (-(Complex.arg ((2 : ℂ) - I * s) * (-ℓs).im)) :=
          mul_le_mul hrpow_bounds.1 hexp_lo (Real.exp_pos _).le (by positivity)
  · calc
      ‖(2 : ℂ) - I * s‖ ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) *
            Real.exp (-(Complex.arg ((2 : ℂ) - I * s) * (-ℓs).im))
        ≤ ((1 + S / 2) ^ K * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re)) * Real.exp B_arg :=
          mul_le_mul hrpow_bounds.2 hexp_hi (Real.exp_pos _).le (by positivity)
      _ = C_hi * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) := by
        simp only [C_hi]; ring

/-- **Phragmén–Lindelöf polynomial interpolation on an upper half-strip** `σ₁ ≤ Re s ≤ σ₂`,
`0 ≤ t₀ ≤ Im s`: if `f` grows at most as `A * exp(B * exp(c * Im z))` (`c < π / (σ₂ - σ₁)`)
inside the open half-strip, and satisfies `‖f (σ₁ + it)‖ ≤ C₁ (t + 2) ^ α₁`,
`‖f (σ₂ + it)‖ ≤ C₂ (t + 2) ^ α₂` for `t ≥ t₀`, then throughout the closed half-strip
`‖f (σ + it)‖ ≤ C (t + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ`. -/
theorem phragmen_lindelof_upper_half_strip_poly {σ₁ σ₂ t₀ A B c C₁ C₂ α₁ α₂ : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂) (ht₀ : 0 ≤ t₀)
    (hf : DiffContOnCl ℂ f (upperHalfStripOpen σ₁ σ₂ t₀))
    (hA : 0 ≤ A) (hc : c < π / (σ₂ - σ₁))
    (hbound : ∀ z ∈ upperHalfStripOpen σ₁ σ₂ t₀, ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * z.im)))
    (hleft : ∀ t : ℝ, t₀ ≤ t → ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (t + 2) ^ α₁)
    (hright : ∀ t : ℝ, t₀ ≤ t → ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (t + 2) ^ α₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ∀ t : ℝ, t₀ ≤ t →
      ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (t + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ := by
  have hden : 0 < σ₂ - σ₁ := sub_pos.mpr hσ
  have hC₁_nonneg : 0 ≤ C₁ := by
    have h0 := hleft t₀ le_rfl
    have hpow : 0 < (t₀ + 2) ^ α₁ := Real.rpow_pos_of_pos (by linarith) α₁
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h0) hpow
  have hC₂_nonneg : 0 ≤ C₂ := by
    have h0 := hright t₀ le_rfl
    have hpow : 0 < (t₀ + 2) ^ α₂ := Real.rpow_pos_of_pos (by linarith) α₂
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h0) hpow
  let φ : ℂ → ℂ := fun s ↦ ((2 : ℂ) - I * s) ^
    (-(((α₁ : ℂ) * ((σ₂ : ℂ) - s) + (α₂ : ℂ) * (s - (σ₁ : ℂ))) / ((σ₂ - σ₁ : ℝ) : ℂ)))
  let h : ℂ → E := fun s ↦ φ s • f s
  have hgd : DiffContOnCl ℂ h (upperHalfStripOpen σ₁ σ₂ t₀) := by
    have hφ_diffOn : DifferentiableOn ℂ φ (upperHalfStripOpen σ₁ σ₂ t₀) :=
      fun s hs ↦ (poly_weight_diffAt σ₁ σ₂ α₁ α₂ s (ht₀.trans hs.2.2.le)).differentiableWithinAt
    have hφ_contOn : ContinuousOn φ (closure (upperHalfStripOpen σ₁ σ₂ t₀)) := by
      rw [closure_upperHalfStripOpen hσ t₀]
      intro s hs
      exact (poly_weight_diffAt σ₁ σ₂ α₁ α₂ s (ht₀.trans hs.2.2)).continuousAt.continuousWithinAt
    exact ⟨hφ_diffOn.smul hf.differentiableOn, hφ_contOn.smul hf.continuousOn⟩
  let S : ℝ := max |σ₁| |σ₂|
  let K : ℝ := max |α₁| |α₂|
  let B_arg : ℝ := (π / 2) * S * |α₂ - α₁| / (σ₂ - σ₁)
  let C_lo : ℝ := (1 + S / 2) ^ (-K) * Real.exp (-B_arg)
  let C_hi : ℝ := (1 + S / 2) ^ K * Real.exp B_arg
  have hK_nonneg : 0 ≤ K := by positivity
  have hC_lo_pos : 0 < C_lo := by positivity
  have hC_hi_pos : 0 < C_hi := by positivity
  have hφ_bounds : ∀ s ∈ upperHalfStripClosed σ₁ σ₂ t₀,
      C_lo * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) ≤ ‖φ s‖ ∧
      ‖φ s‖ ≤ C_hi * (s.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ s.re) :=
    poly_weight_bounds hσ ht₀
  let K_bot : Set ℂ := {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₀ ≤ s.im ∧ s.im ≤ t₀}
  have hK_bot_sub : K_bot ⊆ upperHalfStripClosed σ₁ σ₂ t₀ := fun _ hs ↦ ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hcont_cl_h : ContinuousOn h (upperHalfStripClosed σ₁ σ₂ t₀) := by
    rw [← closure_upperHalfStripOpen hσ t₀]
    exact hgd.continuousOn
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_strip_box σ₁ σ₂ t₀ t₀).image_of_continuousOn (hcont_cl_h.mono hK_bot_sub).norm).bddAbove
  let M : ℝ := max (max M₀ 0) (max (C_hi * C₁) (C_hi * C₂))
  let c'' : ℝ := (max c 0 + π / (σ₂ - σ₁)) / 2
  have hc_lt_c'' : c ≤ c'' := by
    have h1 : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos hden
    have h2 : c ≤ max c 0 := le_max_left _ _
    have h3 : max c 0 < π / (σ₂ - σ₁) := max_lt hc h1
    simp only [c'']
    linarith
  have hc''_pos : 0 < c'' := by
    have h1 : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos hden
    have h2 : 0 ≤ max c 0 := le_max_right _ _
    simp only [c'']
    linarith
  have hc''_lt : c'' < π / (σ₂ - σ₁) := by
    have h1 : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos hden
    have h3 : max c 0 < π / (σ₂ - σ₁) := max_lt hc h1
    simp only [c'']
    linarith
  obtain ⟨A', B', hA', _, hgr_exp⟩ :=
    rpow_mul_exp_exp_le (B := B) hK_nonneg (mul_nonneg hC_hi_pos.le hA) hc''_pos hc_lt_c''
  have hh_cl : ∀ s ∈ upperHalfStripClosed σ₁ σ₂ t₀, ‖h s‖ ≤ M := by
    intro s hs
    exact phragmen_lindelof_upper_half_strip (B := B') hσ hgd hA' hc''_lt
      (fun w hw ↦ by
        have hw_cl := upperHalfStripOpen_subset_closed σ₁ σ₂ t₀ hw
        have hw_im : 0 ≤ w.im := ht₀.trans hw_cl.2.2
        have hφ_le := (hφ_bounds w hw_cl).2
        have h_abs_le := (abs_le.mp (abs_linearInterp_le (α₁ := α₁) (α₂ := α₂) hw_cl.1 hw_cl.2.1 hσ)).1
        have hpow_le : (w.im + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ w.re) ≤ (w.im + 2) ^ K :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        calc
          ‖h w‖ = ‖φ w‖ * ‖f w‖ := norm_smul _ _
          _ ≤ (C_hi * (w.im + 2) ^ K) * (A * Real.exp (B * Real.exp (c * w.im))) :=
            mul_le_mul (hφ_le.trans (mul_le_mul_of_nonneg_left hpow_le hC_hi_pos.le))
              (hbound w hw) (norm_nonneg _) (by positivity)
          _ = (w.im + 2) ^ K * ((C_hi * A) * Real.exp (B * Real.exp (c * w.im))) := by ring
          _ ≤ A' * Real.exp (B' * Real.exp (c'' * w.im)) := hgr_exp w.im hw_im)
      (fun t ht ↦ by
        let w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I
        have hw_cl : w ∈ upperHalfStripClosed σ₁ σ₂ t₀ :=
          ⟨by simp [w], by simp [w, hσ.le], by simp [w, ht]⟩
        have hw_re : w.re = σ₁ := by simp [w]
        have hw_im : w.im = t := by simp [w]
        have hφ_le := (hφ_bounds w hw_cl).2
        rw [hw_re, hw_im, linearInterp_left hσ.ne] at hφ_le
        have hf_le := hleft t ht
        have ht2_pos : 0 < t + 2 := by linarith
        have hcancel : (t + 2) ^ (-α₁) * (t + 2) ^ α₁ = 1 := by
          rw [Real.rpow_neg ht2_pos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht2_pos α₁).ne']
        calc
          ‖h w‖ = ‖φ w‖ * ‖f w‖ := norm_smul _ _
          _ ≤ (C_hi * (t + 2) ^ (-α₁)) * (C₁ * (t + 2) ^ α₁) :=
            mul_le_mul hφ_le hf_le (norm_nonneg _) (by positivity)
          _ = (C_hi * C₁) * ((t + 2) ^ (-α₁) * (t + 2) ^ α₁) := by ring
          _ = C_hi * C₁ := by rw [hcancel, mul_one]
          _ ≤ M := (le_max_left _ _).trans (le_max_right _ _))
      (fun t ht ↦ by
        let w : ℂ := (σ₂ : ℂ) + (t : ℂ) * I
        have hw_cl : w ∈ upperHalfStripClosed σ₁ σ₂ t₀ :=
          ⟨by simp [w, hσ.le], by simp [w], by simp [w, ht]⟩
        have hw_re : w.re = σ₂ := by simp [w]
        have hw_im : w.im = t := by simp [w]
        have hφ_le := (hφ_bounds w hw_cl).2
        rw [hw_re, hw_im, linearInterp_right hσ.ne] at hφ_le
        have hf_le := hright t ht
        have ht2_pos : 0 < t + 2 := by linarith
        have hcancel : (t + 2) ^ (-α₂) * (t + 2) ^ α₂ = 1 := by
          rw [Real.rpow_neg ht2_pos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht2_pos α₂).ne']
        calc
          ‖h w‖ = ‖φ w‖ * ‖f w‖ := norm_smul _ _
          _ ≤ (C_hi * (t + 2) ^ (-α₂)) * (C₂ * (t + 2) ^ α₂) :=
            mul_le_mul hφ_le hf_le (norm_nonneg _) (by positivity)
          _ = (C_hi * C₂) * ((t + 2) ^ (-α₂) * (t + 2) ^ α₂) := by ring
          _ = C_hi * C₂ := by rw [hcancel, mul_one]
          _ ≤ M := (le_max_right _ _).trans (le_max_right _ _))
      (fun σ hσmem ↦ by
        let w : ℂ := (σ : ℂ) + (t₀ : ℂ) * I
        have hw_bot : w ∈ K_bot :=
          ⟨by simp [w, hσmem.1], by simp [w, hσmem.2], by simp [w], by simp [w]⟩
        exact (hM₀ ⟨w, hw_bot, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _)))
      hs
  have hM_nonneg : 0 ≤ M :=
    (le_max_right M₀ 0).trans (le_max_left _ _)
  refine ⟨M / C_lo, div_nonneg hM_nonneg hC_lo_pos.le, fun σ hσmem t ht ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs_cl : s ∈ upperHalfStripClosed σ₁ σ₂ t₀ :=
    ⟨by simp [s, hσmem.1], by simp [s, hσmem.2], by simp [s, ht]⟩
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hφ_ge := (hφ_bounds s hs_cl).1
  rw [hs_re, hs_im] at hφ_ge
  have hs_M := hh_cl s hs_cl
  rw [norm_smul] at hs_M
  have ht2_pos : 0 < t + 2 := by linarith
  have hpow_pos : 0 < (t + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ σ) :=
    Real.rpow_pos_of_pos ht2_pos _
  have h_prod : C_lo * (t + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ σ) * ‖f s‖ ≤ M :=
    (mul_le_mul_of_nonneg_right hφ_ge (norm_nonneg _)).trans hs_M
  have h_den_pos : 0 < C_lo * (t + 2) ^ (-linearInterp σ₁ σ₂ α₁ α₂ σ) :=
    mul_pos hC_lo_pos hpow_pos
  have hdiv := le_div_iff₀' h_den_pos |>.mpr h_prod
  refine hdiv.trans_eq ?_
  rw [Real.rpow_neg ht2_pos.le, div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- **Phragmén–Lindelöf polynomial interpolation on a vertical strip** with explicit
double-exponential interior growth `‖f z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|))`
(`c < π / (σ₂ - σ₁)`). -/
theorem phragmen_lindelof_poly_interp_of_exp_le {σ₁ σ₂ A B c C₁ C₂ α₁ α₂ : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hA : 0 ≤ A) (hc : c < π / (σ₂ - σ₁))
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (|t| + 2) ^ α₁)
    (hright : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (|t| + 2) ^ α₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ := by
  have hsub_pos : upperHalfStripOpen σ₁ σ₂ 0 ⊆ verticalStripOpen σ₁ σ₂ :=
    fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hf_pos : DiffContOnCl ℂ f (upperHalfStripOpen σ₁ σ₂ 0) := hf.mono hsub_pos
  obtain ⟨Cp, hCp_nonneg, hCp⟩ := phragmen_lindelof_upper_half_strip_poly hσ le_rfl hf_pos hA hc
    (fun z hz ↦ by
      have him : |z.im| = z.im := abs_of_pos hz.2.2
      simpa [him] using hbound z (hsub_pos hz))
    (fun t ht ↦ by simpa [abs_of_nonneg ht] using hleft t)
    (fun t ht ↦ by simpa [abs_of_nonneg ht] using hright t)
  let g : ℂ → E := fun s ↦ f (-s)
  have hmaps_neg : MapsTo Neg.neg (verticalStripOpen (-σ₂) (-σ₁)) (verticalStripOpen σ₁ σ₂) := by
    intro s hs
    exact ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩
  have hg_strip : DiffContOnCl ℂ g (verticalStripOpen (-σ₂) (-σ₁)) :=
    hf.comp differentiable_neg.diffContOnCl hmaps_neg
  have hsub_neg : upperHalfStripOpen (-σ₂) (-σ₁) 0 ⊆ verticalStripOpen (-σ₂) (-σ₁) :=
    fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hσ_neg : -σ₂ < -σ₁ := by linarith
  have hc_neg : c < π / (-σ₁ - -σ₂) := by
    have hden_eq : (-σ₁ : ℝ) - -σ₂ = σ₂ - σ₁ := by ring
    rwa [hden_eq]
  obtain ⟨Cm, hCm_nonneg, hCm⟩ := phragmen_lindelof_upper_half_strip_poly
    (B := B) (C₁ := C₂) (C₂ := C₁) (α₁ := α₂) (α₂ := α₁)
    hσ_neg le_rfl (hg_strip.mono hsub_neg) hA hc_neg
    (fun z hz ↦ by
      dsimp only [g]
      have him : |(-z).im| = z.im := by simp [abs_of_pos hz.2.2]
      rw [← him]
      exact hbound (-z) (hmaps_neg (hsub_neg hz)))
    (fun t ht ↦ by
      dsimp only [g]
      have heq : -(((-σ₂ : ℝ) : ℂ) + (t : ℂ) * I) = (σ₂ : ℂ) + ((-t : ℝ) : ℂ) * I := by
        push_cast; ring
      have habs : |-t| = t := by rw [abs_neg, abs_of_nonneg ht]
      rw [heq]
      refine (hright (-t)).trans_eq ?_
      rw [habs])
    (fun t ht ↦ by
      dsimp only [g]
      have heq : -(((-σ₁ : ℝ) : ℂ) + (t : ℂ) * I) = (σ₁ : ℂ) + ((-t : ℝ) : ℂ) * I := by
        push_cast; ring
      have habs : |-t| = t := by rw [abs_neg, abs_of_nonneg ht]
      rw [heq]
      refine (hleft (-t)).trans_eq ?_
      rw [habs])
  refine ⟨max Cp Cm, le_max_of_le_left hCp_nonneg, fun σ hσmem t ↦ ?_⟩
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    refine (hCp σ hσmem t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  · have ht_le : t ≤ 0 := le_of_not_ge ht
    have hneg_t : 0 ≤ -t := neg_nonneg.mpr ht_le
    have hσ_neg_mem : -σ ∈ Set.Icc (-σ₂) (-σ₁) :=
      ⟨by linarith [hσmem.2], by linarith [hσmem.1]⟩
    have heq : -(((-σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = (σ : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    have h_abs : |t| = -t := abs_of_nonpos ht_le
    have h_res := hCm (-σ) hσ_neg_mem (-t) hneg_t
    rw [linearInterp_symm] at h_res
    dsimp only [g] at h_res
    rw [heq, ← h_abs] at h_res
    refine h_res.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (add_nonneg (abs_nonneg t) (by norm_num)) _)

/-- **Phragmén–Lindelöf polynomial vertical-growth interpolation** (asymptotic growth hypothesis):
if `f` is holomorphic on `verticalStripOpen σ₁ σ₂`, continuous on its closure, satisfies
`f =O[comap (|·| ∘ Im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)] exp(B * exp(c * |Im z|))`
with `c < π / (σ₂ - σ₁)`, and obeys polynomial bounds `‖f (σ₁ + it)‖ ≤ C₁ (|t| + 2) ^ α₁` and
`‖f (σ₂ + it)‖ ≤ C₂ (|t| + 2) ^ α₂` on the vertical boundary lines, then
`‖f (σ + it)‖ ≤ C (|t| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ` throughout the closed strip. -/
theorem phragmen_lindelof_poly_interp {σ₁ σ₂ C₁ C₂ α₁ α₂ : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hB : ∃ c < π / (σ₂ - σ₁), ∃ B,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (|t| + 2) ^ α₁)
    (hright : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (|t| + 2) ^ α₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ := by
  obtain ⟨c, hc, B, hO⟩ := hB
  obtain ⟨A, B', hA, _, hbound⟩ := exp_le_of_isBigO hσ hf hO
  exact phragmen_lindelof_poly_interp_of_exp_le hσ hf hA hc
    (fun z hz ↦ hbound z (verticalStripOpen_subset_closed σ₁ σ₂ hz)) hleft hright

/-- Pointwise `z ∈ verticalStripClosed σ₁ σ₂` formulation of `phragmen_lindelof_poly_interp`. -/
theorem phragmen_lindelof_poly_interp_mem {σ₁ σ₂ C₁ C₂ α₁ α₂ : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hB : ∃ c < π / (σ₂ - σ₁), ∃ B,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (verticalStripOpen σ₁ σ₂)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (|t| + 2) ^ α₁)
    (hright : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (|t| + 2) ^ α₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ verticalStripClosed σ₁ σ₂,
      ‖f z‖ ≤ C * (|z.im| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ z.re := by
  obtain ⟨C, hC, h⟩ := phragmen_lindelof_poly_interp hσ hf hB hleft hright
  refine ⟨C, hC, fun z hz ↦ ?_⟩
  have heq : (z.re : ℂ) + (z.im : ℂ) * I = z := Complex.re_add_im z
  conv_lhs => rw [← heq]
  exact h z.re hz z.im

/-- **Phragmén–Lindelöf polynomial interpolation under finite-order vertical exponential growth**
`‖f z‖ ≤ A * Real.exp (B * (|z.im| + 2) ^ γ)` inside `verticalStripOpen σ₁ σ₂`. -/
theorem phragmen_lindelof_poly_interp_of_exp_rpow_le {σ₁ σ₂ A B γ C₁ C₂ α₁ α₂ : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hA : 0 ≤ A)
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖f z‖ ≤ A * Real.exp (B * (|z.im| + 2) ^ γ))
    (hleft : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (|t| + 2) ^ α₁)
    (hright : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (|t| + 2) ^ α₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ := by
  let c : ℝ := π / (2 * (σ₂ - σ₁))
  have hc_pos : 0 < c := div_pos Real.pi_pos (by linarith)
  have hc_lt : c < π / (σ₂ - σ₁) := by
    have hpos : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos (sub_pos.mpr hσ)
    have hc_eq : c = (π / (σ₂ - σ₁)) / 2 := by
      simp only [c]
      field_simp
    linarith
  obtain ⟨A', B', hA', _, hgr⟩ := exp_rpow_le_exp_exp (γ := γ) (B := max B 0) hc_pos (le_max_right B 0)
  refine phragmen_lindelof_poly_interp_of_exp_le (B := B') hσ hf (mul_nonneg hA hA') hc_lt
    (fun w hw ↦ ?_) hleft hright
  have h1 : B * (|w.im| + 2) ^ γ ≤ max B 0 * (|w.im| + 2) ^ γ :=
    mul_le_mul_of_nonneg_right (le_max_left B 0) (Real.rpow_nonneg (by positivity) γ)
  calc
    ‖f w‖ ≤ A * Real.exp (B * (|w.im| + 2) ^ γ) := hbound w hw
    _ ≤ A * Real.exp (max B 0 * (|w.im| + 2) ^ γ) := by gcongr
    _ ≤ A * (A' * Real.exp (B' * Real.exp (c * |w.im|))) :=
      mul_le_mul_of_nonneg_left (hgr |w.im| (abs_nonneg _)) hA
    _ = (A * A') * Real.exp (B' * Real.exp (c * |w.im|)) := by ring

/-- **Phragmén–Lindelöf polynomial interpolation under a coarse polynomial vertical bound**
`‖f z‖ ≤ A * (|z.im| + 2) ^ γ` inside `verticalStripOpen σ₁ σ₂`. -/
theorem phragmen_lindelof_poly_interp_of_poly_le {σ₁ σ₂ A γ C₁ C₂ α₁ α₂ : ℝ} {f : ℂ → E}
    (hσ : σ₁ < σ₂)
    (hf : DiffContOnCl ℂ f (verticalStripOpen σ₁ σ₂))
    (hA : 0 ≤ A)
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖f z‖ ≤ A * (|z.im| + 2) ^ γ)
    (hleft : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (|t| + 2) ^ α₁)
    (hright : ∀ t : ℝ, ‖f ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (|t| + 2) ^ α₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ∀ t : ℝ,
      ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ linearInterp σ₁ σ₂ α₁ α₂ σ := by
  let c : ℝ := π / (2 * (σ₂ - σ₁))
  have hc_pos : 0 < c := div_pos Real.pi_pos (by linarith)
  have hc_lt : c < π / (σ₂ - σ₁) := by
    have hpos : 0 < π / (σ₂ - σ₁) := div_pos Real.pi_pos (sub_pos.mpr hσ)
    have hc_eq : c = (π / (σ₂ - σ₁)) / 2 := by
      simp only [c]
      field_simp
    linarith
  obtain ⟨A', B', hA', _, hgr⟩ := rpow_mul_exp_exp_le (K := max γ 0) (B := 0) (le_max_right γ 0) hA hc_pos le_rfl
  refine phragmen_lindelof_poly_interp_of_exp_le (B := B') hσ hf hA' hc_lt (fun w hw ↦ ?_) hleft hright
  have h1 : (|w.im| + 2) ^ γ ≤ (|w.im| + 2) ^ max γ 0 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) (le_max_left _ _)
  calc
    ‖f w‖ ≤ A * (|w.im| + 2) ^ γ := hbound w hw
    _ ≤ A * (|w.im| + 2) ^ max γ 0 := mul_le_mul_of_nonneg_left h1 hA
    _ = (|w.im| + 2) ^ max γ 0 * (A * Real.exp (0 * Real.exp (c * |w.im|))) := by
      simp [mul_comm A]
    _ ≤ A' * Real.exp (B' * Real.exp (c * |w.im|)) := hgr |w.im| (abs_nonneg _)

end PolyInterpolation

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

