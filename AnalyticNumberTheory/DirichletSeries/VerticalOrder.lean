import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.SumCoeff
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PhragmenLindelof
import AnalyticNumberTheory.DirichletSeries.Convergence

/-!
# Vertical Order, Lindelöf Convexity, and Mean Value Theorems for Dirichlet Series

This file develops the vertical order function `μ(σ)` of analytic functions in vertical strips
and right half-planes, its convexity, monotonicity, and continuity via Phragmén–Lindelöf
interpolation, specialized bounds and convexity estimates for Dirichlet series, and the
mean-square (mean value) theorems for both Dirichlet polynomials and absolutely convergent
Dirichlet series along vertical lines.

## Main definitions

- `HasPolyVerticalGrowth`: global bound `‖F (σ + it)‖ ≤ C * (|t| + 2) ^ μ`.
- `HasVerticalOrder`: asymptotic vertical growth `F (σ + it) =O (|t| + 2) ^ μ` as `|t| → ∞`.
- `verticalOrder`: the Lindelöf vertical order `μ(σ) = inf {μ ≥ 0 | HasVerticalOrder F σ μ}`.
- `dirichletPoly`: finite Dirichlet polynomial `∑_{1 ≤ n ≤ N} a n * n ^ (-s)`.

## Main theorems

- `verticalOrder_le_linearInterp`: two-point Lindelöf convexity bound on a strip.
- `convexOn_verticalOrder_Ioo`, `continuousOn_verticalOrder_Ioo`: convexity and continuity of
  `verticalOrder` on an open strip.
- `antitoneOn_verticalOrder_Ioi_of_bddAbove`: monotonicity on a half-plane under right boundedness.
- `verticalOrder_LSeries_eq_zero`, `verticalOrder_dirichletSum_le_one`,
  `verticalOrder_dirichletSum_le_interp`: vertical order estimates for Dirichlet series.
- `tendsto_mean_sq_dirichletPoly`, `tendsto_mean_sq_LSeries`: mean value theorems for Dirichlet
  polynomials and Dirichlet series in the region of absolute convergence.
-/

open Complex Filter MeasureTheory Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletSeries

/-! ### Vertical growth predicates and `verticalOrder` -/

/-- Global polynomial bound along the vertical line `Re s = σ`:
there exists `C ≥ 0` such that `‖F (σ + it)‖ ≤ C * (|t| + 2) ^ μ` for all `t : ℝ`. -/
def HasPolyVerticalGrowth (F : ℂ → ℂ) (σ μ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ μ

/-- Asymptotic vertical growth of exponent `μ` at abscissa `σ`:
`F (σ + it) = O((|t| + 2) ^ μ)` as `|t| → ∞`. -/
def HasVerticalOrder (F : ℂ → ℂ) (σ μ : ℝ) : Prop :=
  (fun t : ℝ ↦ F ((σ : ℂ) + (t : ℂ) * I)) =O[Filter.comap _root_.abs atTop]
    fun t : ℝ ↦ (|t| + 2) ^ μ

/-- The vertical order `μ(σ)` of `F` at abscissa `σ`, defined as the infimum of all `μ ≥ 0`
for which `HasVerticalOrder F σ μ` holds (defaulting to `0` when the set is empty). -/
noncomputable def verticalOrder (F : ℂ → ℂ) (σ : ℝ) : ℝ :=
  sInf {μ : ℝ | 0 ≤ μ ∧ HasVerticalOrder F σ μ}

private theorem eventually_two_le_abs :
    ∀ᶠ t : ℝ in Filter.comap _root_.abs atTop, (2 : ℝ) ≤ |t| :=
  Filter.eventually_comap.mpr ((eventually_ge_atTop (2 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)

private theorem eventually_one_le_abs :
    ∀ᶠ t : ℝ in Filter.comap _root_.abs atTop, (1 : ℝ) ≤ |t| :=
  eventually_two_le_abs.mono fun _ ht ↦ by linarith

/-- Equivalence between `HasVerticalOrder F σ μ` and `F (σ + it) = O(|t| ^ μ)` as `|t| → ∞`. -/
theorem hasVerticalOrder_iff_isBigO_abs_rpow (F : ℂ → ℂ) (σ μ : ℝ) :
    HasVerticalOrder F σ μ ↔
      (fun t : ℝ ↦ F ((σ : ℂ) + (t : ℂ) * I)) =O[Filter.comap _root_.abs atTop]
        fun t : ℝ ↦ |t| ^ μ := by
  have h1 : (fun t : ℝ ↦ (|t| + 2) ^ μ) =O[Filter.comap _root_.abs atTop]
      fun t : ℝ ↦ |t| ^ μ := by
    refine Asymptotics.isBigO_iff.mpr ⟨max 1 ((2 : ℝ) ^ μ), ?_⟩
    filter_upwards [eventually_two_le_abs] with t ht
    have ht_pos : 0 < |t| := by linarith
    have ht2_pos : 0 < |t| + 2 := by linarith
    have hle : |t| + 2 ≤ 2 * |t| := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht2_pos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg ht_pos.le _)]
    rcases le_or_gt 0 μ with hμ | hμ
    · calc
        (|t| + 2) ^ μ ≤ (2 * |t|) ^ μ := Real.rpow_le_rpow ht2_pos.le hle hμ
        _ = (2 : ℝ) ^ μ * |t| ^ μ := Real.mul_rpow (by norm_num) ht_pos.le
        _ ≤ max 1 ((2 : ℝ) ^ μ) * |t| ^ μ := by
          gcongr
          exact le_max_right _ _
    · calc
        (|t| + 2) ^ μ ≤ |t| ^ μ := Real.rpow_le_rpow_of_nonpos ht_pos (by linarith) hμ.le
        _ = 1 * |t| ^ μ := (one_mul _).symm
        _ ≤ max 1 ((2 : ℝ) ^ μ) * |t| ^ μ := by
          gcongr
          exact le_max_left _ _
  have h2 : (fun t : ℝ ↦ |t| ^ μ) =O[Filter.comap _root_.abs atTop]
      fun t : ℝ ↦ (|t| + 2) ^ μ := by
    refine Asymptotics.isBigO_iff.mpr ⟨max 1 ((2 : ℝ) ^ (-μ)), ?_⟩
    filter_upwards [eventually_two_le_abs] with t ht
    have ht_pos : 0 < |t| := by linarith
    have ht2_pos : 0 < |t| + 2 := by linarith
    have hle : |t| + 2 ≤ 2 * |t| := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht_pos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg ht2_pos.le _)]
    rcases le_or_gt 0 μ with hμ | hμ
    · calc
        |t| ^ μ ≤ (|t| + 2) ^ μ := Real.rpow_le_rpow ht_pos.le (by linarith) hμ
        _ = 1 * (|t| + 2) ^ μ := (one_mul _).symm
        _ ≤ max 1 ((2 : ℝ) ^ (-μ)) * (|t| + 2) ^ μ := by
          gcongr
          exact le_max_left _ _
    · have hpow_le : (2 * |t|) ^ μ ≤ (|t| + 2) ^ μ :=
        Real.rpow_le_rpow_of_nonpos ht2_pos hle hμ.le
      rw [Real.mul_rpow (by norm_num) ht_pos.le] at hpow_le
      have hmul : |t| ^ μ ≤ (2 : ℝ) ^ (-μ) * (|t| + 2) ^ μ := by
        rw [Real.rpow_neg (by norm_num)]
        calc
          |t| ^ μ = ((2 : ℝ) ^ μ)⁻¹ * ((2 : ℝ) ^ μ * |t| ^ μ) := by
            field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) μ).ne']
          _ ≤ ((2 : ℝ) ^ μ)⁻¹ * (|t| + 2) ^ μ := by
            gcongr
      calc
        |t| ^ μ ≤ (2 : ℝ) ^ (-μ) * (|t| + 2) ^ μ := hmul
        _ ≤ max 1 ((2 : ℝ) ^ (-μ)) * (|t| + 2) ^ μ := by
          gcongr
          exact le_max_right _ _
  exact ⟨fun h ↦ h.trans h1, fun h ↦ h.trans h2⟩

/-- Global polynomial vertical growth implies asymptotic vertical growth. -/
theorem HasPolyVerticalGrowth.hasVerticalOrder {F : ℂ → ℂ} {σ μ : ℝ}
    (h : HasPolyVerticalGrowth F σ μ) : HasVerticalOrder F σ μ := by
  obtain ⟨C, _, hC⟩ := h
  refine Asymptotics.isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall fun t ↦ ?_⟩
  have ht2 : 0 ≤ (|t| + 2) ^ μ := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg ht2]
  exact hC t

/-- When `t ↦ F (σ + it)` is continuous, asymptotic growth `HasVerticalOrder` upgrades to a
global bound `HasPolyVerticalGrowth`. -/
theorem HasVerticalOrder.hasPolyVerticalGrowth_of_continuous {F : ℂ → ℂ} {σ μ : ℝ}
    (hcont : Continuous fun t : ℝ ↦ F ((σ : ℂ) + (t : ℂ) * I))
    (h : HasVerticalOrder F σ μ) : HasPolyVerticalGrowth F σ μ := by
  rw [HasVerticalOrder, Asymptotics.isBigO_iff] at h
  obtain ⟨C, hC⟩ := h
  rw [Filter.eventually_comap, eventually_atTop] at hC
  obtain ⟨R, hR⟩ := hC
  let R₀ : ℝ := max R 0
  have hR₀_nonneg : 0 ≤ R₀ := le_max_right _ _
  have hratio_cont : Continuous fun t : ℝ ↦ ‖F ((σ : ℂ) + (t : ℂ) * I)‖ / (|t| + 2) ^ μ := by
    refine hcont.norm.div ?_ fun t ↦ (Real.rpow_pos_of_pos (by positivity) _).ne'
    exact ((continuous_abs.add continuous_const).rpow continuous_const fun t ↦
      Or.inl (ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg t) two_pos)))
  have hne : (Set.Icc (-R₀) R₀).Nonempty := ⟨0, ⟨by linarith, hR₀_nonneg⟩⟩
  obtain ⟨t₀, _, ht₀_max⟩ := isCompact_Icc.exists_isMaxOn hne hratio_cont.continuousOn
  let M : ℝ := ‖F ((σ : ℂ) + (t₀ : ℂ) * I)‖ / (|t₀| + 2) ^ μ
  refine ⟨max (max C M) 0, le_max_right _ _, fun t ↦ ?_⟩
  have ht2_pos : 0 < (|t| + 2) ^ μ := Real.rpow_pos_of_pos (by positivity) _
  rcases le_or_gt R₀ |t| with hbig | hsmall
  · have htR : R ≤ |t| := (le_max_left R 0).trans hbig
    have hbound := hR |t| htR t rfl
    rw [Real.norm_of_nonneg ht2_pos.le] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C M).trans (le_max_left _ 0)) ht2_pos.le)
  · have hmem : t ∈ Set.Icc (-R₀) R₀ := abs_le.mp hsmall.le
    have hle_M : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ / (|t| + 2) ^ μ ≤ M := ht₀_max hmem
    have hbound : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M * (|t| + 2) ^ μ :=
      (div_le_iff₀ ht2_pos).mp hle_M
    exact hbound.trans (mul_le_mul_of_nonneg_right
      ((le_max_right C M).trans (le_max_left _ 0)) ht2_pos.le)

/-- Monotonicity of `HasPolyVerticalGrowth` with respect to the exponent `μ`. -/
theorem HasPolyVerticalGrowth.mono {F : ℂ → ℂ} {σ μ₁ μ₂ : ℝ} (hμ : μ₁ ≤ μ₂)
    (h : HasPolyVerticalGrowth F σ μ₁) : HasPolyVerticalGrowth F σ μ₂ := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun t ↦ ?_⟩
  refine (hC t).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hμ) hC0

/-- Monotonicity of `HasVerticalOrder` with respect to the exponent `μ`. -/
theorem HasVerticalOrder.mono {F : ℂ → ℂ} {σ μ₁ μ₂ : ℝ} (hμ : μ₁ ≤ μ₂)
    (h : HasVerticalOrder F σ μ₁) : HasVerticalOrder F σ μ₂ := by
  refine h.trans ?_
  refine Asymptotics.isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall fun t ↦ ?_⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hμ

/-- `verticalOrder` is always nonnegative. -/
theorem verticalOrder_nonneg (F : ℂ → ℂ) (σ : ℝ) : 0 ≤ verticalOrder F σ := by
  by_cases hne : {μ : ℝ | 0 ≤ μ ∧ HasVerticalOrder F σ μ}.Nonempty
  · exact le_csInf hne fun _ hμ ↦ hμ.1
  · rw [verticalOrder, Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-- Any nonnegative exponent `μ` witnessing `HasVerticalOrder F σ μ` bounds `verticalOrder F σ`
from above. -/
theorem verticalOrder_le_of_hasVerticalOrder {F : ℂ → ℂ} {σ μ : ℝ} (hμ : 0 ≤ μ)
    (h : HasVerticalOrder F σ μ) : verticalOrder F σ ≤ μ :=
  csInf_le ⟨0, fun _ hν ↦ hν.1⟩ ⟨hμ, h⟩

/-- Any nonnegative exponent `μ` witnessing `HasPolyVerticalGrowth F σ μ` bounds `verticalOrder F σ`
from above. -/
theorem verticalOrder_le_of_hasPolyVerticalGrowth {F : ℂ → ℂ} {σ μ : ℝ} (hμ : 0 ≤ μ)
    (h : HasPolyVerticalGrowth F σ μ) : verticalOrder F σ ≤ μ :=
  verticalOrder_le_of_hasVerticalOrder hμ h.hasVerticalOrder

/-- Above `verticalOrder F σ` (when the admissible set is nonempty), `HasVerticalOrder F σ μ`
holds for every `μ > verticalOrder F σ`. -/
theorem hasVerticalOrder_of_verticalOrder_lt {F : ℂ → ℂ} {σ μ : ℝ}
    (hfin : ∃ μ₀ : ℝ, 0 ≤ μ₀ ∧ HasVerticalOrder F σ μ₀) (hμ : verticalOrder F σ < μ) :
    HasVerticalOrder F σ μ := by
  obtain ⟨μ₀, hμ₀⟩ := hfin
  obtain ⟨μ', hμ', hlt⟩ := exists_lt_of_csInf_lt ⟨μ₀, hμ₀⟩ hμ
  exact hμ'.2.mono hlt.le

/-- Continuous boundary variant: above `verticalOrder F σ`, `HasPolyVerticalGrowth F σ μ` holds. -/
theorem hasPolyVerticalGrowth_of_verticalOrder_lt {F : ℂ → ℂ} {σ μ : ℝ}
    (hcont : Continuous fun t : ℝ ↦ F ((σ : ℂ) + (t : ℂ) * I))
    (hfin : ∃ μ₀ : ℝ, 0 ≤ μ₀ ∧ HasVerticalOrder F σ μ₀) (hμ : verticalOrder F σ < μ) :
    HasPolyVerticalGrowth F σ μ :=
  (hasVerticalOrder_of_verticalOrder_lt hfin hμ).hasPolyVerticalGrowth_of_continuous hcont

/-! ### Phragmén–Lindelöf strip convexity, continuity, and monotonicity -/

private theorem closure_verticalStripOpen_subset (a b : ℝ) :
    closure (verticalStripOpen a b) ⊆ verticalStripClosed a b := by
  refine IsClosed.closure_subset_iff ?_ |>.mpr (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

private theorem continuousOn_line_of_continuousOn_closedStrip {F : ℂ → ℂ} {a b σ : ℝ}
    (hcont : ContinuousOn F (verticalStripClosed a b)) (hσ : σ ∈ Set.Icc a b) :
    Continuous fun t : ℝ ↦ F ((σ : ℂ) + (t : ℂ) * I) := by
  have hmaps : MapsTo (fun t : ℝ ↦ (σ : ℂ) + (t : ℂ) * I) Set.univ (verticalStripClosed a b) := by
    intro t _
    exact ⟨by simpa using hσ.1, by simpa using hσ.2⟩
  have hline : Continuous fun t : ℝ ↦ (σ : ℂ) + (t : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact continuousOn_univ.mp (hcont.comp hline.continuousOn hmaps)

private theorem verticalStripOpen_sub {a b x y : ℝ} (hx : a ≤ x) (hy : y ≤ b) :
    verticalStripOpen x y ⊆ verticalStripOpen a b := fun _ hz ↦
  ⟨lt_of_le_of_lt hx hz.1, lt_of_lt_of_le hz.2 hy⟩

private theorem closure_verticalStripOpen_sub {a b x y : ℝ} (_hxy : x < y)
    (hx : a ≤ x) (hy : y ≤ b) :
    closure (verticalStripOpen x y) ⊆ verticalStripClosed a b :=
  (closure_verticalStripOpen_subset x y).trans fun _ hz ↦
    ⟨hx.trans hz.1, hz.2.trans hy⟩

private theorem diffContOnCl_sub_of_diffContOnCl {F : ℂ → ℂ} {a b x y : ℝ} (hxy : x < y)
    (hx : a ≤ x) (hy : y ≤ b) (hF : DiffContOnCl ℂ F (verticalStripOpen a b)) :
    DiffContOnCl ℂ F (verticalStripOpen x y) := by
  refine ⟨hF.differentiableOn.mono (verticalStripOpen_sub hx hy), ?_⟩
  refine hF.continuousOn.mono ?_
  calc
    closure (verticalStripOpen x y) ⊆ verticalStripClosed x y :=
      closure_verticalStripOpen_subset x y
    _ ⊆ closure (verticalStripOpen a b) := by
      rw [closure_verticalStripOpen (lt_of_le_of_lt hx (lt_of_lt_of_le hxy hy))]
      exact fun _ hz ↦ ⟨hx.trans hz.1, hz.2.trans hy⟩

private theorem combo_mem_Icc {x y t₁ t₂ : ℝ} (hxy : x ≤ y) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hsum : t₁ + t₂ = 1) : t₁ * x + t₂ * y ∈ Set.Icc x y := by
  refine ⟨?_, ?_⟩
  · calc
      x = t₁ * x + t₂ * x := by rw [← add_mul, hsum, one_mul]
      _ ≤ t₁ * x + t₂ * y := by gcongr
  · calc
      t₁ * x + t₂ * y ≤ t₁ * y + t₂ * y := by gcongr
      _ = y := by rw [← add_mul, hsum, one_mul]

/-- **Lindelöf convexity inequality on a strip** (under sub-exponential strip growth):
for `σ ∈ [σ₁, σ₂]`, `verticalOrder F σ ≤ linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ`. -/
theorem verticalOrder_le_linearInterp {F : ℂ → ℂ} {σ₁ σ₂ A B c : ℝ}
    (hσ : σ₁ < σ₂) (hF : DiffContOnCl ℂ F (verticalStripOpen σ₁ σ₂))
    (hA : 0 ≤ A) (hc : c < Real.pi / (σ₂ - σ₁))
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂,
      ‖F z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hfin₁ : ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧ HasVerticalOrder F σ₁ μ₁)
    (hfin₂ : ∃ μ₂ : ℝ, 0 ≤ μ₂ ∧ HasVerticalOrder F σ₂ μ₂)
    {σ : ℝ} (hσmem : σ ∈ Set.Icc σ₁ σ₂) :
    verticalOrder F σ ≤
      linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ := by
  have hcl : ContinuousOn F (verticalStripClosed σ₁ σ₂) := by
    simpa [closure_verticalStripOpen hσ] using hF.continuousOn
  have hc1 := continuousOn_line_of_continuousOn_closedStrip hcl ⟨le_rfl, hσ.le⟩
  have hc2 := continuousOn_line_of_continuousOn_closedStrip hcl ⟨hσ.le, le_rfl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hpg1 : HasPolyVerticalGrowth F σ₁ (verticalOrder F σ₁ + ε) :=
    hasPolyVerticalGrowth_of_verticalOrder_lt hc1 hfin₁ (by linarith)
  have hpg2 : HasPolyVerticalGrowth F σ₂ (verticalOrder F σ₂ + ε) :=
    hasPolyVerticalGrowth_of_verticalOrder_lt hc2 hfin₂ (by linarith)
  obtain ⟨C₁, _, hC₁⟩ := hpg1
  obtain ⟨C₂, _, hC₂⟩ := hpg2
  obtain ⟨C, _, hC⟩ := phragmen_lindelof_poly_interp_of_exp_le hσ hF hA hc hbound hC₁ hC₂
  have hinterp_eq :
      linearInterp σ₁ σ₂ (verticalOrder F σ₁ + ε) (verticalOrder F σ₂ + ε) σ =
        linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ + ε := by
    have hne : σ₂ - σ₁ ≠ 0 := sub_ne_zero.mpr hσ.ne'
    simp only [linearInterp]
    field_simp [hne]
    ring
  have hnonneg :
      0 ≤ linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ + ε := by
    have hnn1 : 0 ≤ verticalOrder F σ₁ + ε :=
      add_nonneg (verticalOrder_nonneg F σ₁) hε.le
    have hnn2 : 0 ≤ verticalOrder F σ₂ + ε :=
      add_nonneg (verticalOrder_nonneg F σ₂) hε.le
    have hden : 0 < σ₂ - σ₁ := sub_pos.mpr hσ
    rw [← hinterp_eq, linearInterp]
    exact add_nonneg
      (div_nonneg (mul_nonneg hnn1 (sub_nonneg.mpr hσmem.2)) hden.le)
      (div_nonneg (mul_nonneg hnn2 (sub_nonneg.mpr hσmem.1)) hden.le)
  have hgrowth : HasPolyVerticalGrowth F σ
      (linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ + ε) := by
    refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
    rw [← hinterp_eq]
    exact (hC σ hσmem t).trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (by positivity) _))
  exact verticalOrder_le_of_hasPolyVerticalGrowth hnonneg hgrowth

/-- Polynomial-strip-bound variant of `verticalOrder_le_linearInterp`. -/
theorem verticalOrder_le_linearInterp_of_poly {F : ℂ → ℂ} {σ₁ σ₂ A γ : ℝ}
    (hσ : σ₁ < σ₂) (hF : DiffContOnCl ℂ F (verticalStripOpen σ₁ σ₂))
    (hA : 0 ≤ A)
    (hbound : ∀ z ∈ verticalStripOpen σ₁ σ₂, ‖F z‖ ≤ A * (|z.im| + 2) ^ γ)
    (hfin₁ : ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧ HasVerticalOrder F σ₁ μ₁)
    (hfin₂ : ∃ μ₂ : ℝ, 0 ≤ μ₂ ∧ HasVerticalOrder F σ₂ μ₂)
    {σ : ℝ} (hσmem : σ ∈ Set.Icc σ₁ σ₂) :
    verticalOrder F σ ≤
      linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ := by
  have hcl : ContinuousOn F (verticalStripClosed σ₁ σ₂) := by
    simpa [closure_verticalStripOpen hσ] using hF.continuousOn
  have hc1 := continuousOn_line_of_continuousOn_closedStrip hcl ⟨le_rfl, hσ.le⟩
  have hc2 := continuousOn_line_of_continuousOn_closedStrip hcl ⟨hσ.le, le_rfl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hpg1 : HasPolyVerticalGrowth F σ₁ (verticalOrder F σ₁ + ε) :=
    hasPolyVerticalGrowth_of_verticalOrder_lt hc1 hfin₁ (by linarith)
  have hpg2 : HasPolyVerticalGrowth F σ₂ (verticalOrder F σ₂ + ε) :=
    hasPolyVerticalGrowth_of_verticalOrder_lt hc2 hfin₂ (by linarith)
  obtain ⟨C₁, _, hC₁⟩ := hpg1
  obtain ⟨C₂, _, hC₂⟩ := hpg2
  obtain ⟨C, _, hC⟩ := phragmen_lindelof_poly_interp_of_poly_le hσ hF hA hbound hC₁ hC₂
  have hinterp_eq :
      linearInterp σ₁ σ₂ (verticalOrder F σ₁ + ε) (verticalOrder F σ₂ + ε) σ =
        linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ + ε := by
    have hne : σ₂ - σ₁ ≠ 0 := sub_ne_zero.mpr hσ.ne'
    simp only [linearInterp]
    field_simp [hne]
    ring
  have hnonneg :
      0 ≤ linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ + ε := by
    have hnn1 : 0 ≤ verticalOrder F σ₁ + ε :=
      add_nonneg (verticalOrder_nonneg F σ₁) hε.le
    have hnn2 : 0 ≤ verticalOrder F σ₂ + ε :=
      add_nonneg (verticalOrder_nonneg F σ₂) hε.le
    have hden : 0 < σ₂ - σ₁ := sub_pos.mpr hσ
    rw [← hinterp_eq, linearInterp]
    exact add_nonneg
      (div_nonneg (mul_nonneg hnn1 (sub_nonneg.mpr hσmem.2)) hden.le)
      (div_nonneg (mul_nonneg hnn2 (sub_nonneg.mpr hσmem.1)) hden.le)
  have hgrowth : HasPolyVerticalGrowth F σ
      (linearInterp σ₁ σ₂ (verticalOrder F σ₁) (verticalOrder F σ₂) σ + ε) := by
    refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
    rw [← hinterp_eq]
    exact (hC σ hσmem t).trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (by positivity) _))
  exact verticalOrder_le_of_hasPolyVerticalGrowth hnonneg hgrowth

private theorem convex_combo_eq_linearInterp {x y t₁ t₂ : ℝ} (hxy : x < y)
    (hsum : t₁ + t₂ = 1) (f : ℝ → ℝ) :
    t₁ * f x + t₂ * f y = linearInterp x y (f x) (f y) (t₁ * x + t₂ * y) := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  have ht1 : (y - (t₁ * x + t₂ * y)) / (y - x) = t₁ := by
    have h : y - (t₁ * x + t₂ * y) = t₁ * (y - x) := by
      have : t₂ = 1 - t₁ := by linarith
      rw [this]
      ring
    rw [h, mul_div_cancel_right₀ _ hne]
  have ht2 : ((t₁ * x + t₂ * y) - x) / (y - x) = t₂ := by
    have h : (t₁ * x + t₂ * y) - x = t₂ * (y - x) := by
      have : t₁ = 1 - t₂ := by linarith
      rw [this]
      ring
    rw [h, mul_div_cancel_right₀ _ hne]
  rw [linearInterp, mul_div_assoc, mul_div_assoc, ht1, ht2, mul_comm (f x), mul_comm (f y)]

/-- Convexity of `verticalOrder F` on the closed strip `Set.Icc a b` under sub-exponential
growth. -/
theorem convexOn_verticalOrder_Icc {F : ℂ → ℂ} {a b A B c : ℝ}
    (hF : DiffContOnCl ℂ F (verticalStripOpen a b))
    (hA : 0 ≤ A) (hc : c < Real.pi / (b - a))
    (hbound : ∀ z ∈ verticalStripOpen a b,
      ‖F z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hfin : ∀ σ ∈ Set.Icc a b, ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder F σ μ) :
    ConvexOn ℝ (Set.Icc a b) (verticalOrder F) := by
  refine ⟨convex_Icc a b, fun x hx y hy t₁ t₂ ht₁ ht₂ hsum ↦ ?_⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hmem : t₁ * x + t₂ * y ∈ Set.Icc x y := combo_mem_Icc hxy.le ht₁ ht₂ hsum
    have hc_sub : c < Real.pi / (y - x) := by
      refine hc.trans_le ?_
      have hba : 0 < b - a := by linarith [hx.1, hy.2, hxy]
      have hyx_pos : 0 < y - x := sub_pos.mpr hxy
      have hyx_le : y - x ≤ b - a := by linarith [hx.1, hy.2]
      exact div_le_div_of_nonneg_left Real.pi_pos.le hyx_pos hyx_le
    have hres := verticalOrder_le_linearInterp hxy
      (diffContOnCl_sub_of_diffContOnCl hxy hx.1 hy.2 hF) hA hc_sub
      (fun z hz ↦ hbound z (verticalStripOpen_sub hx.1 hy.2 hz))
      (hfin x hx) (hfin y hy) hmem
    simpa [smul_eq_mul, convex_combo_eq_linearInterp hxy hsum] using hres
  · simp only [smul_eq_mul]
    rw [← add_mul, hsum, one_mul, ← add_mul, hsum, one_mul]
  · have hsum' : t₂ + t₁ = 1 := by linarith
    have hmem : t₂ * y + t₁ * x ∈ Set.Icc y x := combo_mem_Icc hyx.le ht₂ ht₁ hsum'
    have hc_sub : c < Real.pi / (x - y) := by
      refine hc.trans_le ?_
      have hba : 0 < b - a := by linarith [hy.1, hx.2, hyx]
      have hxy_pos : 0 < x - y := sub_pos.mpr hyx
      have hxy_le : x - y ≤ b - a := by linarith [hy.1, hx.2]
      exact div_le_div_of_nonneg_left Real.pi_pos.le hxy_pos hxy_le
    have hres := verticalOrder_le_linearInterp hyx
      (diffContOnCl_sub_of_diffContOnCl hyx hy.1 hx.2 hF) hA hc_sub
      (fun z hz ↦ hbound z (verticalStripOpen_sub hy.1 hx.2 hz))
      (hfin y hy) (hfin x hx) hmem
    have heq1 : t₁ • x + t₂ • y = t₂ * y + t₁ * x := by simp [smul_eq_mul]; ring
    have heq2 : t₁ • verticalOrder F x + t₂ • verticalOrder F y =
        t₂ * verticalOrder F y + t₁ * verticalOrder F x := by simp [smul_eq_mul]; ring
    rw [heq1, heq2, convex_combo_eq_linearInterp hyx hsum']
    exact hres

/-- Convexity of `verticalOrder F` on an open strip `Set.Ioo a b` when `F` is holomorphic on the
strip and has finite polynomial or sub-exponential vertical growth. -/
theorem convexOn_verticalOrder_Ioo {F : ℂ → ℂ} {a b A B c : ℝ}
    (hF : DifferentiableOn ℂ F (verticalStripOpen a b))
    (hA : 0 ≤ A) (hc : c < Real.pi / (b - a))
    (hbound : ∀ z ∈ verticalStripOpen a b,
      ‖F z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hfin : ∀ σ ∈ Set.Ioo a b, ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder F σ μ) :
    ConvexOn ℝ (Set.Ioo a b) (verticalOrder F) := by
  refine ⟨convex_Ioo a b, fun x hx y hy t₁ t₂ ht₁ ht₂ hsum ↦ ?_⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hdiff : DiffContOnCl ℂ F (verticalStripOpen x y) := by
      refine ⟨hF.mono (verticalStripOpen_sub hx.1.le hy.2.le), ?_⟩
      refine hF.continuousOn.mono ?_
      refine (closure_verticalStripOpen_subset x y).trans fun z hz ↦ ?_
      exact ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    have hc_sub : c < Real.pi / (y - x) := by
      refine hc.trans_le ?_
      have hba : 0 < b - a := by linarith [hx.1, hy.2, hxy]
      have hyx_pos : 0 < y - x := sub_pos.mpr hxy
      have hyx_le : y - x ≤ b - a := by linarith [hx.1, hy.2]
      exact div_le_div_of_nonneg_left Real.pi_pos.le hyx_pos hyx_le
    have hmem : t₁ * x + t₂ * y ∈ Set.Icc x y := combo_mem_Icc hxy.le ht₁ ht₂ hsum
    have hres := verticalOrder_le_linearInterp hxy hdiff hA hc_sub
      (fun z hz ↦ hbound z (verticalStripOpen_sub hx.1.le hy.2.le hz))
      (hfin x hx) (hfin y hy) hmem
    simpa [smul_eq_mul, convex_combo_eq_linearInterp hxy hsum] using hres
  · simp only [smul_eq_mul]
    rw [← add_mul, hsum, one_mul, ← add_mul, hsum, one_mul]
  · have hdiff : DiffContOnCl ℂ F (verticalStripOpen y x) := by
      refine ⟨hF.mono (verticalStripOpen_sub hy.1.le hx.2.le), ?_⟩
      refine hF.continuousOn.mono ?_
      refine (closure_verticalStripOpen_subset y x).trans fun z hz ↦ ?_
      exact ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
    have hc_sub : c < Real.pi / (x - y) := by
      refine hc.trans_le ?_
      have hba : 0 < b - a := by linarith [hy.1, hx.2, hyx]
      have hxy_pos : 0 < x - y := sub_pos.mpr hyx
      have hxy_le : x - y ≤ b - a := by linarith [hy.1, hx.2]
      exact div_le_div_of_nonneg_left Real.pi_pos.le hxy_pos hxy_le
    have hsum' : t₂ + t₁ = 1 := by linarith
    have hmem : t₂ * y + t₁ * x ∈ Set.Icc y x := combo_mem_Icc hyx.le ht₂ ht₁ hsum'
    have hres := verticalOrder_le_linearInterp hyx hdiff hA hc_sub
      (fun z hz ↦ hbound z (verticalStripOpen_sub hy.1.le hx.2.le hz))
      (hfin y hy) (hfin x hx) hmem
    have heq1 : t₁ • x + t₂ • y = t₂ * y + t₁ * x := by simp [smul_eq_mul]; ring
    have heq2 : t₁ • verticalOrder F x + t₂ • verticalOrder F y =
        t₂ * verticalOrder F y + t₁ * verticalOrder F x := by simp [smul_eq_mul]; ring
    rw [heq1, heq2, convex_combo_eq_linearInterp hyx hsum']
    exact hres

/-- Continuity of `verticalOrder F` on the open strip `Set.Ioo a b`, deduced from convexity. -/
theorem continuousOn_verticalOrder_Ioo {F : ℂ → ℂ} {a b A B c : ℝ}
    (hF : DifferentiableOn ℂ F (verticalStripOpen a b))
    (hA : 0 ≤ A) (hc : c < Real.pi / (b - a))
    (hbound : ∀ z ∈ verticalStripOpen a b,
      ‖F z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hfin : ∀ σ ∈ Set.Ioo a b, ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder F σ μ) :
    ContinuousOn (verticalOrder F) (Set.Ioo a b) := by
  have hcvx := convexOn_verticalOrder_Ioo hF hA hc hbound hfin
  simpa [isOpen_Ioo.interior_eq] using hcvx.continuousOn_interior

/-- A nonnegative convex function on `Set.Icc a b` vanishing at `b` is antitone on `Set.Icc a b`. -/
theorem antitoneOn_of_convexOn_Icc_of_right_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hcvx : ConvexOn ℝ (Set.Icc a b) f) (hnonneg : ∀ σ ∈ Set.Icc a b, 0 ≤ f σ)
    (hb : f b = 0) : AntitoneOn f (Set.Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · rcases eq_or_lt_of_le hy.2 with hyb | hyb
    · subst hyb
      rw [hb]
      exact hnonneg x hx
    · have hxb : x < b := lt_trans hlt hyb
      have hden : 0 < b - x := sub_pos.mpr hxb
      let t₁ : ℝ := (b - y) / (b - x)
      let t₂ : ℝ := (y - x) / (b - x)
      have ht₁ : 0 ≤ t₁ := div_nonneg (sub_nonneg.mpr hy.2) hden.le
      have ht₂ : 0 ≤ t₂ := div_nonneg (sub_nonneg.mpr hxy) hden.le
      have hsum : t₁ + t₂ = 1 := by
        dsimp [t₁, t₂]
        field_simp [hden.ne']
        ring
      have hcomb : t₁ • x + t₂ • b = y := by
        simp only [smul_eq_mul, t₁, t₂]
        field_simp [hden.ne']
        ring
      have hineq := hcvx.2 hx ⟨hx.1.trans hxb.le, le_rfl⟩ ht₁ ht₂ hsum
      rw [hcomb, smul_eq_mul, smul_eq_mul, hb, mul_zero, add_zero] at hineq
      have ht₁_le : t₁ ≤ 1 := by
        dsimp [t₁]
        rw [div_le_one hden]
        linarith
      exact hineq.trans (mul_le_of_le_one_left (hnonneg x hx) ht₁_le)

/-- A convex function on an unbounded right ray `Set.Ioi a` that is bounded above on a right tail
is antitone on `Set.Ioi a`. -/
theorem antitoneOn_of_convexOn_Ioi_of_bddAbove {f : ℝ → ℝ} {a : ℝ}
    (hcvx : ConvexOn ℝ (Set.Ioi a) f)
    (hbdd : ∃ σ₀ : ℝ, ∃ M : ℝ, ∀ z : ℝ, σ₀ ≤ z → f z ≤ M) :
    AntitoneOn f (Set.Ioi a) := by
  obtain ⟨σ₀, M, hM⟩ := hbdd
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hbound (z : ℝ) (hz_big : max σ₀ y < z) :
        f y ≤ ((z - y) / (z - x)) * f x + ((y - x) / (z - x)) * M := by
      have hyz : y < z := lt_of_le_of_lt (le_max_right _ _) hz_big
      have hσz : σ₀ ≤ z := (le_max_left _ _).trans hz_big.le
      have hxz : x < z := lt_trans hlt hyz
      have hz_mem : z ∈ Set.Ioi a := lt_trans hy hyz
      have hden : 0 < z - x := sub_pos.mpr hxz
      let t₁ : ℝ := (z - y) / (z - x)
      let t₂ : ℝ := (y - x) / (z - x)
      have ht₁ : 0 ≤ t₁ := div_nonneg (sub_nonneg.mpr hyz.le) hden.le
      have ht₂ : 0 ≤ t₂ := div_nonneg (sub_nonneg.mpr hxy) hden.le
      have hsum : t₁ + t₂ = 1 := by
        dsimp [t₁, t₂]
        field_simp [hden.ne']
        ring
      have hcomb : t₁ • x + t₂ • z = y := by
        simp only [smul_eq_mul, t₁, t₂]
        field_simp [hden.ne']
        ring
      have hineq := hcvx.2 hx hz_mem ht₁ ht₂ hsum
      rw [hcomb, smul_eq_mul, smul_eq_mul] at hineq
      exact hineq.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hM z hσz) ht₂))
    have hlim1 : Tendsto (fun z : ℝ ↦ (z - y) / (z - x)) atTop (𝓝 1) := by
      have hfun : ∀ᶠ z : ℝ in atTop, (z - y) / (z - x) = 1 - (y - x) / (z - x) := by
        filter_upwards [eventually_gt_atTop x] with z hz
        field_simp [(sub_pos.mpr hz).ne']
        ring
      have hzero : Tendsto (fun z : ℝ ↦ (y - x) / (z - x)) atTop (𝓝 0) := by
        have ht := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-x) tendsto_id)
        have hm := ht.const_mul (y - x)
        rw [mul_zero] at hm
        refine hm.congr fun z ↦ ?_
        simp [sub_eq_add_neg, div_eq_mul_inv]
      have ht1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
      rw [sub_zero] at ht1
      exact ht1.congr' (hfun.mono fun _ h ↦ h.symm)
    have hlim2 : Tendsto (fun z : ℝ ↦ (y - x) / (z - x)) atTop (𝓝 0) := by
      have ht := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-x) tendsto_id)
      have hm := ht.const_mul (y - x)
      rw [mul_zero] at hm
      refine hm.congr fun z ↦ ?_
      simp [sub_eq_add_neg, div_eq_mul_inv]
    have hlim_rhs :
        Tendsto (fun z : ℝ ↦ ((z - y) / (z - x)) * f x + ((y - x) / (z - x)) * M)
          atTop (𝓝 (f x)) := by
      have h := (hlim1.mul_const (f x)).add (hlim2.mul_const M)
      simpa using h
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim_rhs
      ((eventually_gt_atTop (max σ₀ y)).mono hbound)

/-! ### Vertical order of Dirichlet series -/

/-- Uniform vertical bound for `LSeries a` in the half-plane `σ₀ ≤ Re s` whenever
`LSeriesSummable a σ₀`. -/
theorem norm_LSeries_le_tsum_norm_of_re_ge {a : ℕ → ℂ} {σ₀ : ℝ}
    (ha : LSeriesSummable a (σ₀ : ℂ)) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖LSeries a s‖ ≤ ∑' n : ℕ, ‖LSeries.term a (σ₀ : ℂ) n‖ := by
  have hterm_le : ∀ n : ℕ, ‖LSeries.term a s n‖ ≤ ‖LSeries.term a (σ₀ : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [Complex.ofReal_re]
      gcongr
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  have hsum_norm : Summable fun n : ℕ ↦ ‖LSeries.term a s n‖ :=
    ha.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le
  exact (norm_tsum_le_tsum_norm hsum_norm).trans (hsum_norm.tsum_le_tsum hterm_le ha.norm)

/-- When `LSeriesSummable a (σ : ℂ)`, `LSeries a` has bounded vertical growth (`μ = 0`). -/
theorem hasPolyVerticalGrowth_LSeries_zero {a : ℕ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a (σ : ℂ)) : HasPolyVerticalGrowth (LSeries a) σ 0 := by
  refine ⟨∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖, tsum_nonneg fun _ ↦ norm_nonneg _, fun t ↦ ?_⟩
  rw [Real.rpow_zero, mul_one]
  exact norm_LSeries_le_tsum_norm_of_re_ge ha (by simp)

/-- For `LSeriesSummable a (σ : ℂ)` (and in particular whenever `σ > σ_a`),
`verticalOrder (LSeries a) σ = 0`. -/
theorem verticalOrder_LSeries_eq_zero {a : ℕ → ℂ} {σ : ℝ} (ha : LSeriesSummable a (σ : ℂ)) :
    verticalOrder (LSeries a) σ = 0 :=
  le_antisymm (verticalOrder_le_of_hasPolyVerticalGrowth le_rfl (hasPolyVerticalGrowth_LSeries_zero ha))
    (verticalOrder_nonneg _ _)

/-- In the region of absolute convergence `σ_a < σ`, `verticalOrder (LSeries a) σ = 0`. -/
theorem verticalOrder_LSeries_eq_zero_of_abscissaOfAbsConv_lt {a : ℕ → ℂ} {σ : ℝ}
    (hσ : LSeries.abscissaOfAbsConv a < (σ : EReal)) :
    verticalOrder (LSeries a) σ = 0 :=
  verticalOrder_LSeries_eq_zero
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ))

/-- In the region of absolute convergence `σ_a < σ`, `verticalOrder (dirichletSum a) σ = 0`. -/
theorem verticalOrder_dirichletSum_eq_zero_of_abscissaOfAbsConv_lt {a : ℕ → ℂ} {σ : ℝ}
    (hσ : LSeries.abscissaOfAbsConv a < (σ : EReal)) :
    verticalOrder (dirichletSum a) σ = 0 := by
  have ha : LSeriesSummable a (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ)
  have hpg : HasPolyVerticalGrowth (dirichletSum a) σ 0 := by
    obtain ⟨C, hC0, hC⟩ := hasPolyVerticalGrowth_LSeries_zero ha
    refine ⟨C, hC0, fun t ↦ ?_⟩
    have hsum_t : LSeriesSummable a ((σ : ℂ) + (t : ℂ) * I) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ)
    rw [hsum_t.dirichletSum_eq_LSeries]
    exact hC t
  exact le_antisymm (verticalOrder_le_of_hasPolyVerticalGrowth le_rfl hpg)
    (verticalOrder_nonneg _ _)

private theorem exists_real_lt_of_abscissa_lt {f : ℕ → ℂ} {σ₀ : ℝ}
    (h : abscissaOfConvergence f < (σ₀ : EReal)) :
    ∃ x₀ : ℝ, DirichletConvergesAt f x₀ ∧ x₀ < σ₀ := by
  rw [abscissaOfConvergence, sInf_lt_iff] at h
  obtain ⟨y, ⟨x₀, hx₀, rfl⟩, hy⟩ := h
  exact ⟨x₀, hx₀, EReal.coe_lt_coe_iff.mp hy⟩

private theorem norm_complex_le_abs_re_add_abs_im (z : ℂ) :
    ‖z‖ ≤ |z.re| + |z.im| := by
  calc
    ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]

/-- Uniform linear-in-`|Im s|` bound for `dirichletSum a s` on any closed half-plane `σ₀ ≤ Re s`
inside the convergence half-plane `σ_c < σ₀`. -/
theorem norm_dirichletSum_le_linear_of_abscissaOfConvergence_lt {a : ℕ → ℂ} {σ₀ : ℝ}
    (hσ₀ : abscissaOfConvergence a < (σ₀ : EReal)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → ‖dirichletSum a s‖ ≤ C * (|s.im| + 2) := by
  obtain ⟨x₀, hx₀, hx₀_lt⟩ := exists_real_lt_of_abscissa_lt hσ₀
  obtain ⟨B, hB_pos, hB⟩ := hx₀.exists_bound
  have hδ_pos : 0 < σ₀ - x₀ := sub_pos.mpr hx₀_lt
  refine ⟨max B (B / (σ₀ - x₀)), le_trans hB_pos.le (le_max_left _ _), fun s hs ↦ ?_⟩
  have hre_gt : (x₀ : ℂ).re < s.re := by
    simp only [Complex.ofReal_re]
    exact lt_of_lt_of_le hx₀_lt hs
  have hpart : ∀ N : ℕ, ‖dirichletPartialSum a s N‖ ≤
      max B (B / (σ₀ - x₀)) * (|s.im| + 2) := by
    intro N
    have hsub := norm_dirichletPartialSum_sub_le_of_re_lt a hre_gt (M := 0) (N := N) (Nat.zero_le N)
      (fun k _ ↦ by simpa [dirichletPartialSum_zero] using hB k)
    rw [dirichletPartialSum_zero, sub_zero] at hsub
    have hsx_pos : 0 < s.re - x₀ := by
      simp only [Complex.ofReal_re] at hre_gt
      linarith
    have hnorm_diff : ‖s - (x₀ : ℂ)‖ ≤ (s.re - x₀) + |s.im| := by
      have h := norm_complex_le_abs_re_add_abs_im (s - (x₀ : ℂ))
      simpa [abs_of_pos hsx_pos] using h
    have hdiv_le : ‖s - (x₀ : ℂ)‖ / (s.re - (x₀ : ℂ).re) ≤ 1 + |s.im| / (σ₀ - x₀) := by
      simp only [Complex.ofReal_re]
      calc
        ‖s - (x₀ : ℂ)‖ / (s.re - x₀) ≤ ((s.re - x₀) + |s.im|) / (s.re - x₀) := by gcongr
        _ = 1 + |s.im| / (s.re - x₀) := by
          rw [add_div, div_self hsx_pos.ne']
        _ ≤ 1 + |s.im| / (σ₀ - x₀) := by gcongr
    calc
      ‖dirichletPartialSum a s N‖ ≤ B * (‖s - (x₀ : ℂ)‖ / (s.re - (x₀ : ℂ).re)) := hsub
      _ ≤ B * (1 + |s.im| / (σ₀ - x₀)) := by gcongr
      _ = B + (B / (σ₀ - x₀)) * |s.im| := by ring
      _ ≤ max B (B / (σ₀ - x₀)) * 2 + max B (B / (σ₀ - x₀)) * |s.im| := by
        gcongr
        · calc
            B ≤ B * 2 := le_mul_of_one_le_right hB_pos.le (by norm_num)
            _ ≤ max B (B / (σ₀ - x₀)) * 2 := by
              gcongr
              exact le_max_left _ _
        · exact le_max_right _ _
      _ = max B (B / (σ₀ - x₀)) * (|s.im| + 2) := by ring
  have hconv : DirichletConvergesAt a s :=
    dirichletConvergesAt_of_abscissaOfConvergence_lt_re
      (lt_of_lt_of_le hσ₀ (EReal.coe_le_coe_iff.mpr hs))
  exact le_of_tendsto hconv.tendsto.norm (Filter.Eventually.of_forall hpart)

/-- For `σ > σ_c`, `dirichletSum a` has polynomial vertical growth of order `≤ 1`. -/
theorem hasPolyVerticalGrowth_dirichletSum_one {a : ℕ → ℂ} {σ : ℝ}
    (hσ : abscissaOfConvergence a < (σ : EReal)) :
    HasPolyVerticalGrowth (dirichletSum a) σ 1 := by
  obtain ⟨C, hC0, hC⟩ := norm_dirichletSum_le_linear_of_abscissaOfConvergence_lt hσ
  refine ⟨C, hC0, fun t ↦ ?_⟩
  simpa [Real.rpow_one] using hC ((σ : ℂ) + (t : ℂ) * I) (by simp)

/-- For `σ > σ_c`, `verticalOrder (dirichletSum a) σ ≤ 1`. -/
theorem verticalOrder_dirichletSum_le_one {a : ℕ → ℂ} {σ : ℝ}
    (hσ : abscissaOfConvergence a < (σ : EReal)) :
    verticalOrder (dirichletSum a) σ ≤ 1 :=
  verticalOrder_le_of_hasPolyVerticalGrowth zero_le_one
    (hasPolyVerticalGrowth_dirichletSum_one hσ)

/-- Convexity of `verticalOrder (dirichletSum a)` on the open half-plane `{σ | σ_c < σ}`. -/
theorem convexOn_verticalOrder_dirichletSum (a : ℕ → ℂ) :
    ConvexOn ℝ {σ : ℝ | abscissaOfConvergence a < (σ : EReal)}
      (verticalOrder (dirichletSum a)) := by
  refine ⟨?_, fun x hx y hy t₁ t₂ ht₁ ht₂ hsum ↦ ?_⟩
  · intro x hx y hy t₁ t₂ ht₁ ht₂ hsum
    have hlt_x : abscissaOfConvergence a < (x : EReal) := hx
    have hlt_y : abscissaOfConvergence a < (y : EReal) := hy
    have hmin : abscissaOfConvergence a < ((min x y : ℝ) : EReal) := by
      rcases min_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> simpa [h]
    have hle : min x y ≤ t₁ • x + t₂ • y := by
      simp only [smul_eq_mul]
      calc
        min x y = t₁ * min x y + t₂ * min x y := by rw [← add_mul, hsum, one_mul]
        _ ≤ t₁ * x + t₂ * y := by
          gcongr
          · exact min_le_left _ _
          · exact min_le_right _ _
    exact lt_of_lt_of_le hmin (EReal.coe_le_coe_iff.mpr hle)
  · rcases lt_trichotomy x y with hxy | rfl | hyx
    · obtain ⟨C, hC0, hC⟩ := norm_dirichletSum_le_linear_of_abscissaOfConvergence_lt hx
      have hdiff : DiffContOnCl ℂ (dirichletSum a) (verticalStripOpen x y) := by
        refine ⟨(dirichletSum_differentiableOn a).mono fun z hz ↦ ?_, ?_⟩
        · exact lt_of_lt_of_le hx (EReal.coe_le_coe_iff.mpr hz.1.le)
        · refine (dirichletSum_differentiableOn a).continuousOn.mono ?_
          exact (closure_verticalStripOpen_subset x y).trans fun z hz ↦
            lt_of_lt_of_le hx (EReal.coe_le_coe_iff.mpr hz.1)
      have hbound : ∀ z ∈ verticalStripOpen x y, ‖dirichletSum a z‖ ≤ C * (|z.im| + 2) ^ (1 : ℝ) :=
        fun z hz ↦ by simpa [Real.rpow_one] using hC z hz.1.le
      have hfinx : ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder (dirichletSum a) x μ :=
        ⟨1, zero_le_one, (hasPolyVerticalGrowth_dirichletSum_one hx).hasVerticalOrder⟩
      have hfiny : ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder (dirichletSum a) y μ :=
        ⟨1, zero_le_one, (hasPolyVerticalGrowth_dirichletSum_one hy).hasVerticalOrder⟩
      have hmem : t₁ * x + t₂ * y ∈ Set.Icc x y := combo_mem_Icc hxy.le ht₁ ht₂ hsum
      have hres := verticalOrder_le_linearInterp_of_poly hxy hdiff hC0 hbound hfinx hfiny hmem
      simpa [smul_eq_mul, convex_combo_eq_linearInterp hxy hsum] using hres
    · simp only [smul_eq_mul]
      rw [← add_mul, hsum, one_mul, ← add_mul, hsum, one_mul]
    · obtain ⟨C, hC0, hC⟩ := norm_dirichletSum_le_linear_of_abscissaOfConvergence_lt hy
      have hdiff : DiffContOnCl ℂ (dirichletSum a) (verticalStripOpen y x) := by
        refine ⟨(dirichletSum_differentiableOn a).mono fun z hz ↦ ?_, ?_⟩
        · exact lt_of_lt_of_le hy (EReal.coe_le_coe_iff.mpr hz.1.le)
        · refine (dirichletSum_differentiableOn a).continuousOn.mono ?_
          exact (closure_verticalStripOpen_subset y x).trans fun z hz ↦
            lt_of_lt_of_le hy (EReal.coe_le_coe_iff.mpr hz.1)
      have hbound : ∀ z ∈ verticalStripOpen y x, ‖dirichletSum a z‖ ≤ C * (|z.im| + 2) ^ (1 : ℝ) :=
        fun z hz ↦ by simpa [Real.rpow_one] using hC z hz.1.le
      have hfiny : ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder (dirichletSum a) y μ :=
        ⟨1, zero_le_one, (hasPolyVerticalGrowth_dirichletSum_one hy).hasVerticalOrder⟩
      have hfinx : ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder (dirichletSum a) x μ :=
        ⟨1, zero_le_one, (hasPolyVerticalGrowth_dirichletSum_one hx).hasVerticalOrder⟩
      have hsum' : t₂ + t₁ = 1 := by linarith
      have hmem : t₂ * y + t₁ * x ∈ Set.Icc y x := combo_mem_Icc hyx.le ht₂ ht₁ hsum'
      have hres := verticalOrder_le_linearInterp_of_poly hyx hdiff hC0 hbound hfiny hfinx hmem
      have heq1 : t₁ • x + t₂ • y = t₂ * y + t₁ * x := by simp [smul_eq_mul]; ring
      have heq2 : t₁ • verticalOrder (dirichletSum a) x + t₂ • verticalOrder (dirichletSum a) y =
          t₂ * verticalOrder (dirichletSum a) y + t₁ * verticalOrder (dirichletSum a) x := by
        simp [smul_eq_mul]; ring
      rw [heq1, heq2, convex_combo_eq_linearInterp hyx hsum']
      exact hres

private theorem isOpen_Ioi_EReal (α : EReal) : IsOpen {σ : ℝ | α < (σ : EReal)} := by
  induction α using EReal.rec with
  | bot =>
    have h : {σ : ℝ | (⊥ : EReal) < (σ : EReal)} = Set.univ := by
      ext σ; simp [EReal.bot_lt_coe]
    rw [h]
    exact isOpen_univ
  | coe r =>
    have h : {σ : ℝ | (r : EReal) < (σ : EReal)} = Set.Ioi r := by
      ext σ
      simp [EReal.coe_lt_coe_iff]
    rw [h]
    exact isOpen_Ioi
  | top =>
    have h : {σ : ℝ | (⊤ : EReal) < (σ : EReal)} = ∅ := by
      ext σ; simp
    rw [h]
    exact isOpen_empty

/-- Continuity of `verticalOrder (dirichletSum a)` on `{σ : ℝ | σ_c < σ}`. -/
theorem continuousOn_verticalOrder_dirichletSum (a : ℕ → ℂ) :
    ContinuousOn (verticalOrder (dirichletSum a))
      {σ : ℝ | abscissaOfConvergence a < (σ : EReal)} := by
  have hcvx := convexOn_verticalOrder_dirichletSum a
  simpa [(isOpen_Ioi_EReal _).interior_eq] using hcvx.continuousOn_interior

/-- Monotonicity (`AntitoneOn`) of `verticalOrder (dirichletSum a)` on `{σ : ℝ | σ_c < σ}`. -/
theorem antitoneOn_verticalOrder_dirichletSum (a : ℕ → ℂ) :
    AntitoneOn (verticalOrder (dirichletSum a))
      {σ : ℝ | abscissaOfConvergence a < (σ : EReal)} := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hσ_a_lt : LSeries.abscissaOfAbsConv a < ((x + 2 : ℝ) : EReal) := by
      have h1 : abscissaOfConvergence a + 1 < ((x + 2 : ℝ) : EReal) := by
        have hlt_x : abscissaOfConvergence a < (x : EReal) := hx
        have hcoe : (x : EReal) + 1 = ((x + 1 : ℝ) : EReal) := rfl
        have hlt1 : abscissaOfConvergence a + 1 ≤ ((x + 1 : ℝ) : EReal) := by
          rw [← hcoe]
          exact add_le_add hlt_x.le le_rfl
        exact lt_of_le_of_lt hlt1 (EReal.coe_lt_coe_iff.mpr (by linarith))
      exact lt_of_le_of_lt (abscissaOfAbsConv_le_abscissaOfConvergence_add_one a) h1
    let z : ℝ := max y x + 3
    have hzy : y < z := by dsimp [z]; linarith [le_max_left y x]
    have hxz3 : x + 2 < z := by dsimp [z]; linarith [le_max_right y x]
    have hz_abs : LSeries.abscissaOfAbsConv a < (z : EReal) :=
      lt_of_lt_of_le hσ_a_lt (EReal.coe_le_coe_iff.mpr hxz3.le)
    have hz_conv : abscissaOfConvergence a < (z : EReal) :=
      lt_of_le_of_lt (abscissaOfConvergence_le_abscissaOfAbsConv a) hz_abs
    have hz0 : verticalOrder (dirichletSum a) z = 0 :=
      verticalOrder_dirichletSum_eq_zero_of_abscissaOfAbsConv_lt hz_abs
    have hxz : x < z := lt_trans hlt hzy
    have hden : 0 < z - x := sub_pos.mpr hxz
    let t₁ : ℝ := (z - y) / (z - x)
    let t₂ : ℝ := (y - x) / (z - x)
    have ht₁ : 0 ≤ t₁ := div_nonneg (sub_nonneg.mpr hzy.le) hden.le
    have ht₂ : 0 ≤ t₂ := div_nonneg (sub_nonneg.mpr hxy) hden.le
    have hsum : t₁ + t₂ = 1 := by
      dsimp [t₁, t₂]
      field_simp [hden.ne']
      ring
    have hcomb : t₁ • x + t₂ • z = y := by
      simp only [smul_eq_mul, t₁, t₂]
      field_simp [hden.ne']
      ring
    have hineq := (convexOn_verticalOrder_dirichletSum a).2 hx hz_conv ht₁ ht₂ hsum
    rw [hcomb, smul_eq_mul, smul_eq_mul, hz0, mul_zero, add_zero] at hineq
    have ht₁_le : t₁ ≤ 1 := by
      dsimp [t₁]
      rw [div_le_one hden]
      linarith
    exact hineq.trans (mul_le_of_le_one_left (verticalOrder_nonneg _ _) ht₁_le)

/-- Two-abscissa Lindelöf interpolation bound for `dirichletSum a`:
if `σ_c < σ₀ < σ₁`, `σ_a < σ₁`, and `σ ∈ [σ₀, σ₁]`, then
`verticalOrder (dirichletSum a) σ ≤ (σ₁ - σ) / (σ₁ - σ₀)`. -/
theorem verticalOrder_dirichletSum_le_interp_of_lt {a : ℕ → ℂ} {σ₀ σ₁ σ : ℝ}
    (hσ : σ₀ < σ₁) (hσ₀ : abscissaOfConvergence a < (σ₀ : EReal))
    (hσ₁ : LSeries.abscissaOfAbsConv a < (σ₁ : EReal)) (hσmem : σ ∈ Set.Icc σ₀ σ₁) :
    verticalOrder (dirichletSum a) σ ≤ (σ₁ - σ) / (σ₁ - σ₀) := by
  obtain ⟨C, hC0, hC⟩ := norm_dirichletSum_le_linear_of_abscissaOfConvergence_lt hσ₀
  have hdiff : DiffContOnCl ℂ (dirichletSum a) (verticalStripOpen σ₀ σ₁) := by
    refine ⟨(dirichletSum_differentiableOn a).mono fun z hz ↦ ?_, ?_⟩
    · exact lt_of_lt_of_le hσ₀ (EReal.coe_le_coe_iff.mpr hz.1.le)
    · refine (dirichletSum_differentiableOn a).continuousOn.mono ?_
      exact (closure_verticalStripOpen_subset σ₀ σ₁).trans fun z hz ↦
        lt_of_lt_of_le hσ₀ (EReal.coe_le_coe_iff.mpr hz.1)
  have hbound : ∀ z ∈ verticalStripOpen σ₀ σ₁,
      ‖dirichletSum a z‖ ≤ C * (|z.im| + 2) ^ (1 : ℝ) :=
    fun z hz ↦ by simpa [Real.rpow_one] using hC z hz.1.le
  have hfin₀ : ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder (dirichletSum a) σ₀ μ :=
    ⟨1, zero_le_one, (hasPolyVerticalGrowth_dirichletSum_one hσ₀).hasVerticalOrder⟩
  have hσ₁_sum : LSeriesSummable a (σ₁ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ₁)
  have hfin₁ : ∃ μ : ℝ, 0 ≤ μ ∧ HasVerticalOrder (dirichletSum a) σ₁ μ := by
    refine ⟨0, le_rfl, ?_⟩
    obtain ⟨C₁, hC₁0, hC₁⟩ := hasPolyVerticalGrowth_LSeries_zero hσ₁_sum
    have hpg : HasPolyVerticalGrowth (dirichletSum a) σ₁ 0 := by
      refine ⟨C₁, hC₁0, fun t ↦ ?_⟩
      have ht : LSeriesSummable a ((σ₁ : ℂ) + (t : ℂ) * I) :=
        LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ₁)
      rw [ht.dirichletSum_eq_LSeries]
      exact hC₁ t
    exact hpg.hasVerticalOrder
  have hres := verticalOrder_le_linearInterp_of_poly hσ hdiff hC0 hbound hfin₀ hfin₁ hσmem
  have h0_val : verticalOrder (dirichletSum a) σ₀ ≤ 1 := verticalOrder_dirichletSum_le_one hσ₀
  have h1_val : verticalOrder (dirichletSum a) σ₁ = 0 :=
    verticalOrder_dirichletSum_eq_zero_of_abscissaOfAbsConv_lt hσ₁
  have hden : 0 < σ₁ - σ₀ := sub_pos.mpr hσ
  have h1_pos : 0 ≤ (σ₁ - σ) / (σ₁ - σ₀) := div_nonneg (sub_nonneg.mpr hσmem.2) hden.le
  calc
    verticalOrder (dirichletSum a) σ ≤
        linearInterp σ₀ σ₁ (verticalOrder (dirichletSum a) σ₀)
          (verticalOrder (dirichletSum a) σ₁) σ := hres
    _ = ((σ₁ - σ) / (σ₁ - σ₀)) * verticalOrder (dirichletSum a) σ₀ := by
      rw [linearInterp, h1_val, zero_mul, zero_div, add_zero, mul_div_assoc, mul_comm]
    _ ≤ ((σ₁ - σ) / (σ₁ - σ₀)) * 1 := by gcongr
    _ = (σ₁ - σ) / (σ₁ - σ₀) := mul_one _

/-- Classical Lindelöf convexity bound for Dirichlet series in the strip `(σ_c, σ_a]`:
if `abscissaOfConvergence a ≤ σ_c`, `LSeries.abscissaOfAbsConv a ≤ σ_a`, `σ_c < σ_a`, and
`σ_c < σ`, then `verticalOrder (dirichletSum a) σ ≤ max 0 ((σ_a - σ) / (σ_a - σ_c))`. -/
theorem verticalOrder_dirichletSum_le_interp {a : ℕ → ℂ} {σ_c σ_a σ : ℝ}
    (hc : abscissaOfConvergence a ≤ (σ_c : EReal))
    (ha : LSeries.abscissaOfAbsConv a ≤ (σ_a : EReal))
    (hca : σ_c < σ_a) (hσ : σ_c < σ) :
    verticalOrder (dirichletSum a) σ ≤ max 0 ((σ_a - σ) / (σ_a - σ_c)) := by
  rcases lt_or_ge σ_a σ with hgt | hle
  · have hσ_abs : LSeries.abscissaOfAbsConv a < (σ : EReal) :=
      lt_of_le_of_lt ha (EReal.coe_lt_coe_iff.mpr hgt)
    rw [verticalOrder_dirichletSum_eq_zero_of_abscissaOfAbsConv_lt hσ_abs]
    exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    let δ : ℝ := min ((σ - σ_c) / 2) (ε * (σ_a - σ_c))
    have hδ_pos : 0 < δ := lt_min (by linarith) (mul_pos hε (sub_pos.mpr hca))
    have hδ_le1 : δ ≤ (σ - σ_c) / 2 := min_le_left _ _
    have hδ_le2 : δ ≤ ε * (σ_a - σ_c) := min_le_right _ _
    let σ₀ : ℝ := σ_c + δ
    let σ₁ : ℝ := σ_a + δ
    have hσ01 : σ₀ < σ₁ := by dsimp [σ₀, σ₁]; linarith
    have hσ0_gt : abscissaOfConvergence a < (σ₀ : EReal) :=
      lt_of_le_of_lt hc (EReal.coe_lt_coe_iff.mpr (by dsimp [σ₀]; linarith))
    have hσ1_gt : LSeries.abscissaOfAbsConv a < (σ₁ : EReal) :=
      lt_of_le_of_lt ha (EReal.coe_lt_coe_iff.mpr (by dsimp [σ₁]; linarith))
    have hσ_mem : σ ∈ Set.Icc σ₀ σ₁ := ⟨by dsimp [σ₀]; linarith, by dsimp [σ₁]; linarith⟩
    have hbound := verticalOrder_dirichletSum_le_interp_of_lt hσ01 hσ0_gt hσ1_gt hσ_mem
    have hden : σ₁ - σ₀ = σ_a - σ_c := by dsimp [σ₀, σ₁]; ring
    have hca_pos : 0 < σ_a - σ_c := sub_pos.mpr hca
    calc
      verticalOrder (dirichletSum a) σ ≤ (σ₁ - σ) / (σ₁ - σ₀) := hbound
      _ = (σ_a - σ) / (σ_a - σ_c) + δ / (σ_a - σ_c) := by
        rw [hden]
        dsimp [σ₁]
        ring
      _ ≤ (σ_a - σ) / (σ_a - σ_c) + ε := by
        gcongr
        exact (div_le_iff₀ hca_pos).mpr hδ_le2

/-! ### Mean value theorems for Dirichlet polynomials and Dirichlet series -/

/-- Finite Dirichlet polynomial `∑_{1 ≤ n ≤ N} a n * n ^ (-s)`. -/
noncomputable def dirichletPoly (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)

/-- `dirichletPoly` agrees with `dirichletPartialSum` at every `s : ℂ`. -/
theorem dirichletPoly_eq_dirichletPartialSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    dirichletPoly a N s = dirichletPartialSum a s N := by
  rw [dirichletPoly, dirichletPartialSum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by
    simp only [Finset.mem_Icc] at hn
    omega
  rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, Complex.cpow_neg]

private theorem continuous_dirichletPoly_vertical (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Continuous fun t : ℝ ↦ dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I) := by
  have hterm (n : ℕ) (hn : n ≠ 0) :
      Continuous fun t : ℝ ↦ a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hfun : (fun t : ℝ ↦ a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) =
        fun t : ℝ ↦ a n * Complex.exp (Complex.log (n : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))) := by
      funext t
      rw [Complex.cpow_def_of_ne_zero hn0]
    rw [hfun]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg))
  induction N with
  | zero =>
    have h0 : (fun t : ℝ ↦ dirichletPoly a 0 ((σ : ℂ) + (t : ℂ) * I)) = fun _ ↦ 0 := by
      funext t
      simp [dirichletPoly]
    rw [h0]
    exact continuous_const
  | succ N ih =>
    have hsplit : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    have hfun : (fun t : ℝ ↦ dirichletPoly a (N + 1) ((σ : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ a (N + 1) * ((N + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) +
          dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I) := by
      funext t
      rw [dirichletPoly, hsplit, Finset.sum_insert hnot, dirichletPoly]
    rw [hfun]
    exact (hterm (N + 1) (Nat.succ_ne_zero N)).add ih

private theorem natCast_cpow_neg_vertical {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * I) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
  have hexp : ((Real.log n : ℝ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * I)) =
      ((Real.log n * (-σ) : ℝ) : ℂ) + (-((t * Real.log n : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hn_pos]

private theorem norm_sq_dirichletPoly_eq_sum (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    ((‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (a m * starRingEnd ℂ (a n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) := by
  let w : ℂ := dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)
  have hw : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hw_eq : w = ∑ m ∈ Finset.Icc 1 N,
      (a m * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)) *
        Complex.exp (-((t * Real.log m : ℝ) : ℂ) * I) := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [natCast_cpow_neg_vertical hm1, mul_assoc]
  have hconj : starRingEnd ℂ w = ∑ n ∈ Finset.Icc 1 N,
      (starRingEnd ℂ (a n) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) *
        Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) := by
    rw [hw_eq, map_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    rw [map_mul, map_neg, Complex.conj_I, Complex.ofReal_mul, map_mul,
      Complex.conj_ofReal, Complex.conj_ofReal, neg_mul_neg]
  rw [hw, hconj, hw_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hexp :
      Complex.exp (-((t * Real.log m : ℝ) : ℂ) * I) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) =
        Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (a m * (((m : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-((t * Real.log m : ℝ) : ℂ) * I)) *
        (starRingEnd ℂ (a n) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))
        = (a m * starRingEnd ℂ (a n) * ((((m : ℝ) ^ (-σ) : ℝ) : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ))) *
            (Complex.exp (-((t * Real.log m : ℝ) : ℂ) * I) *
              Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)) := by ring
    _ = (a m * starRingEnd ℂ (a n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) := by
        rw [hexp, ← Complex.ofReal_mul ((m : ℝ) ^ (-σ)) ((n : ℝ) ^ (-σ))]

private theorem integral_odd_real (f : ℝ → ℝ) (hf : ∀ t : ℝ, f (-t) = -f t) (T : ℝ) :
    (∫ t in (-T)..T, f t) = 0 := by
  have hneg : -(∫ t in (-T)..T, f t) = ∫ t in (-T)..T, f t := by
    rw [← intervalIntegral.integral_neg]
    have hcomp := intervalIntegral.integral_comp_neg f (a := -T) (b := T)
    rw [neg_neg] at hcomp
    calc
      ∫ t in (-T)..T, -f t = ∫ t in (-T)..T, f (-t) :=
        intervalIntegral.integral_congr fun t _ ↦ (hf t).symm
      _ = ∫ t in (-T)..T, f t := hcomp
  linarith

private theorem integral_exp_ofReal_mul_I (r T : ℝ) (hr : r ≠ 0) :
    (∫ t in (-T)..T, Complex.exp (((r * t : ℝ) : ℂ) * I)) =
      ((2 * Real.sin (r * T) / r : ℝ) : ℂ) := by
  have hsplit : (fun t : ℝ ↦ Complex.exp (((r * t : ℝ) : ℂ) * I)) =
      fun t : ℝ ↦ ((Real.cos (r * t) : ℝ) : ℂ) + ((Real.sin (r * t) : ℝ) : ℂ) * I := by
    funext t
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcos_cont : Continuous fun t : ℝ ↦ ((Real.cos (r * t) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hsin_cont : Continuous fun t : ℝ ↦ ((Real.sin (r * t) : ℝ) : ℂ) * I :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul continuous_const
  rw [hsplit, intervalIntegral.integral_add (hcos_cont.intervalIntegrable (-T) T)
    (hsin_cont.intervalIntegrable (-T) T), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hsin_zero : (∫ t in (-T)..T, Real.sin (r * t)) = 0 :=
    integral_odd_real _ (fun t ↦ by rw [mul_neg, Real.sin_neg]) T
  have hcos_val : (∫ t in (-T)..T, Real.cos (r * t)) = 2 * Real.sin (r * T) / r := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun x : ℝ ↦ Real.sin (r * x) / r) (Real.cos (r * t)) t := by
      intro t
      have h1 : HasDerivAt (fun x : ℝ ↦ r * x) r t := by
        simpa using (hasDerivAt_id t).const_mul r
      have h2 := ((Real.hasDerivAt_sin (r * t)).comp t h1).div_const r
      refine h2.congr_deriv ?_
      rw [mul_div_cancel_right₀ _ hr]
    have hcont : Continuous fun t : ℝ ↦ Real.cos (r * t) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hderiv t) (hcont.intervalIntegrable (-T) T)
    rw [hint, mul_neg, Real.sin_neg]
    ring
  rw [hsin_zero, hcos_val, Complex.ofReal_zero, zero_mul, add_zero]

private theorem intervalIntegrable_sum_Icc_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (a b : ℝ) (f : ℕ → ℝ → E)
    (hf : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable (f n) volume a b) :
    IntervalIntegrable (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 N, f n t) volume a b := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hinsert : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    have hfn : (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 (N + 1), f n t) =
        fun t : ℝ ↦ f (N + 1) t + ∑ n ∈ Finset.Icc 1 N, f n t := by
      funext t
      rw [hinsert, Finset.sum_insert hnot]
    rw [hfn]
    exact (hf (N + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos N, le_rfl⟩)).add
      (ih fun n hn ↦ hf n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans (Nat.le_succ _)⟩))

private theorem intervalIntegral_sum_Icc_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (a b : ℝ) (f : ℕ → ℝ → E)
    (hf : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable (f n) volume a b) :
    (∫ t in a..b, ∑ n ∈ Finset.Icc 1 N, f n t) =
      ∑ n ∈ Finset.Icc 1 N, ∫ t in a..b, f n t := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hinsert : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    have hfn : (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 (N + 1), f n t) =
        fun t : ℝ ↦ f (N + 1) t + ∑ n ∈ Finset.Icc 1 N, f n t := by
      funext t
      rw [hinsert, Finset.sum_insert hnot]
    have hf_sub : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable (f n) volume a b := fun n hn ↦
      hf n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans (Nat.le_succ _)⟩)
    rw [hfn, intervalIntegral.integral_add
      (hf (N + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos N, le_rfl⟩))
      (intervalIntegrable_sum_Icc_one N a b f hf_sub),
      hinsert, Finset.sum_insert hnot, ih hf_sub]

/-- Explicit mean-square asymptotic identity with `O(1)` remainder for a Dirichlet polynomial
over `[-T, T]`. -/
theorem integral_norm_sq_dirichletPoly_sub_diag_le (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    ‖(∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)‖ ≤
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if m = n then 0 else
          2 * ‖a m‖ * ‖a n‖ * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m| := by
  let S : Finset ℕ := Finset.Icc 1 N
  let c : ℕ → ℕ → ℂ := fun m n ↦
    a m * starRingEnd ℂ (a n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
  have hterm_cont : ∀ m n : ℕ, Continuous fun t : ℝ ↦
      c m n * Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) := fun m n ↦
    continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const))
  have hint_eq :
      (((∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)) =
        ∑ m ∈ S, ∑ n ∈ S,
          c m n * ∫ t in (-T)..T, Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) := by
    rw [← intervalIntegral.integral_ofReal]
    have hcongr :
        (∫ t in (-T)..T, ((‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)) =
          ∫ t in (-T)..T, ∑ m ∈ S, ∑ n ∈ S,
            c m n * Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) :=
      intervalIntegral.integral_congr fun t _ ↦ norm_sq_dirichletPoly_eq_sum a N σ t
    rw [hcongr, intervalIntegral_sum_Icc_one N (-T) T
      (fun m t ↦ ∑ n ∈ S, c m n * Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I))
      (fun m _ ↦ intervalIntegrable_sum_Icc_one N (-T) T
        (fun n t ↦ c m n * Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I))
        (fun n _ ↦ (hterm_cont m n).intervalIntegrable (-T) T))]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [intervalIntegral_sum_Icc_one N (-T) T
      (fun n t ↦ c m n * Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I))
      (fun n _ ↦ (hterm_cont m n).intervalIntegrable (-T) T)]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [intervalIntegral.integral_const_mul]
  have hdiag_eq :
      ((2 * T * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          if m = n then c m n * ((2 * T : ℝ) : ℂ) else 0 := by
    have hinner (m : ℕ) (hm : m ∈ S) :
        (∑ n ∈ S, if m = n then c m n * ((2 * T : ℝ) : ℂ) else 0) =
          c m m * ((2 * T : ℝ) : ℂ) := by
      have hite : ∀ n ∈ S, (if m = n then c m n * ((2 * T : ℝ) : ℂ) else 0) =
          if n = m then c m n * ((2 * T : ℝ) : ℂ) else 0 := fun n _ ↦ by
        simp [eq_comm]
      rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq']
      simp [hm]
    rw [Finset.sum_congr rfl hinner]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
    have hcc : c m m = ((‖a m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) : ℝ) : ℂ) := by
      dsimp [c]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      congr 1
      have hpow : (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) = (m : ℝ) ^ (-2 * σ) := by
        rw [← Real.rpow_add hm_pos]
        congr 1
        ring
      rw [hpow]
    rw [hcc]
    push_cast
    ring
  have hsub_eq :
      (((∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          2 * T * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          if m = n then 0 else
            c m n * ∫ t in (-T)..T, Complex.exp (((((Real.log n - Real.log m) * t : ℝ) : ℂ)) * I) := by
    rw [Complex.ofReal_sub, hint_eq, hdiag_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    by_cases hmn : m = n
    · subst hmn
      simp [sub_self, intervalIntegral.integral_const]
      ring
    · simp only [hmn, ↓reduceIte, sub_zero]
  rw [← Complex.norm_real, hsub_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte]
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hlog_ne : Real.log n - Real.log m ≠ 0 := by
      intro h
      apply hmn
      have heq : Real.log n = Real.log m := sub_eq_zero.mp h
      exact (Nat.cast_injective
        (Real.log_injOn_pos (Set.mem_Ioi.mpr hn_pos) (Set.mem_Ioi.mpr hm_pos) heq)).symm
    rw [integral_exp_ofReal_mul_I _ T hlog_ne, norm_mul]
    have hc_norm : ‖c m n‖ = ‖a m‖ * ‖a n‖ * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) := by
      dsimp [c]
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hm_pos.le _)
          (Real.rpow_nonneg hn_pos.le _))]
      ring
    have hint_norm : ‖((2 * Real.sin ((Real.log n - Real.log m) * T) /
        (Real.log n - Real.log m) : ℝ) : ℂ)‖ ≤ 2 / |Real.log n - Real.log m| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (by norm_num)]
      have hsin : |Real.sin ((Real.log n - Real.log m) * T)| ≤ 1 := Real.abs_sin_le_one _
      calc
        2 * |Real.sin ((Real.log n - Real.log m) * T)| / |Real.log n - Real.log m|
            ≤ 2 * 1 / |Real.log n - Real.log m| := by gcongr
        _ = 2 / |Real.log n - Real.log m| := by rw [mul_one]
    calc
      ‖c m n‖ * ‖((2 * Real.sin ((Real.log n - Real.log m) * T) /
          (Real.log n - Real.log m) : ℝ) : ℂ)‖
          ≤ (‖a m‖ * ‖a n‖ * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) *
              (2 / |Real.log n - Real.log m|) := by
        rw [hc_norm]
        exact mul_le_mul_of_nonneg_left hint_norm (by positivity)
      _ = 2 * ‖a m‖ * ‖a n‖ * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m| := by
        ring

/-- **Mean value theorem for Dirichlet polynomials**:
`(1 / (2T)) ∫_{-T}^T ‖∑_{n ≤ N} a n n^{-(σ+it)}‖^2 dt → ∑_{1 ≤ n ≤ N} ‖a n‖^2 n^{-2σ}`
as `T → ∞`. -/
theorem tendsto_mean_sq_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * T)) *
        ∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))) := by
  let D : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)
  let C : ℝ := ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m = n then 0 else
      2 * ‖a m‖ * ‖a n‖ * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) / |Real.log n - Real.log m|
  have hC_nonneg : 0 ≤ C := by
    refine Finset.sum_nonneg fun m _ ↦ Finset.sum_nonneg fun n _ ↦ ?_
    split_ifs
    · exact le_rfl
    · positivity
  have hlim : Tendsto (fun T : ℝ ↦ C / (2 * T)) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.const_mul (C / 2)
    rw [mul_zero] at h
    refine h.congr fun T ↦ ?_
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hbound := integral_norm_sq_dirichletPoly_sub_diag_le a N σ T
  rw [Real.norm_eq_abs] at hbound ⊢
  have hcancel : (1 / (2 * T)) * (2 * T * D) = D := by
    field_simp [hT.ne']
  have heq : (1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - D =
      (1 / (2 * T)) * ((∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - 2 * T * D) := by
    rw [mul_sub, hcancel]
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
  calc
    (1 / (2 * T)) * |(∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - 2 * T * D|
        ≤ (1 / (2 * T)) * C := by gcongr
    _ = C / (2 * T) := by ring

private theorem exists_norm_bound_real {u : ℕ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 L)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, |u n| ≤ M := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hu 1 zero_lt_one
  refine ⟨max (|L| + 1) (∑ k ∈ Finset.range N₀, |u k|) + 1, by positivity, fun n ↦ ?_⟩
  rcases le_or_gt N₀ n with hn | hn
  · have hdist : |u n - L| < 1 := by simpa [Real.dist_eq] using hN₀ n hn
    have h1 : |u n| ≤ |L| + 1 := by
      calc
        |u n| = |(u n - L) + L| := by ring_nf
        _ ≤ |u n - L| + |L| := abs_add_le _ _
        _ ≤ 1 + |L| := by linarith
        _ = |L| + 1 := add_comm _ _
    linarith [le_max_left (|L| + 1) (∑ k ∈ Finset.range N₀, |u k|)]
  · have hle : |u n| ≤ ∑ k ∈ Finset.range N₀, |u k| :=
      Finset.single_le_sum (f := fun k ↦ |u k|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr hn)
    linarith [le_max_right (|L| + 1) (∑ k ∈ Finset.range N₀, |u k|)]

/-- Square-summability of `‖LSeries.term a (σ : ℂ) n‖` whenever `LSeriesSummable a (σ : ℂ)`. -/
theorem summable_norm_sq_LSeries_term {a : ℕ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a (σ : ℂ)) :
    Summable fun n : ℕ ↦ ‖LSeries.term a (σ : ℂ) n‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_bound_real ha.norm.tendsto_atTop_zero
  refine (ha.norm.mul_left M).of_nonneg_of_le (fun _ ↦ sq_nonneg _) fun n ↦ ?_
  have hn_le : ‖LSeries.term a (σ : ℂ) n‖ ≤ M := by
    simpa [abs_of_nonneg (norm_nonneg _)] using hM n
  calc
    ‖LSeries.term a (σ : ℂ) n‖ ^ 2 = ‖LSeries.term a (σ : ℂ) n‖ * ‖LSeries.term a (σ : ℂ) n‖ := sq _
    _ ≤ M * ‖LSeries.term a (σ : ℂ) n‖ :=
      mul_le_mul_of_nonneg_right hn_le (norm_nonneg _)

private theorem norm_sq_LSeries_term_of_ne_zero {a : ℕ → ℂ} (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖LSeries.term a (σ : ℂ) n‖ ^ 2 = ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.term_of_ne_zero hn, norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp only [Complex.ofReal_re]
  have hsq : ((n : ℝ) ^ σ) ^ 2 = (n : ℝ) ^ (2 * σ) := by
    rw [← Real.rpow_two ((n : ℝ) ^ σ), ← Real.rpow_mul hn_pos.le, mul_comm σ 2]
  rw [div_pow, div_eq_mul_inv, hsq, ← Real.rpow_neg hn_pos.le]
  congr 2
  ring

private theorem sum_diag_eq_sum_range_norm_sq_term (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) =
      ∑ n ∈ Finset.range (N + 1), ‖LSeries.term a (σ : ℂ) n‖ ^ 2 := by
  have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext x; simp; omega
  rw [hsplit, Finset.sum_insert (by simp), LSeries.term_zero, norm_zero, sq, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by
    simp only [Finset.mem_Icc] at hn
    omega
  exact (norm_sq_LSeries_term_of_ne_zero σ hn0).symm

private theorem tail_tendsto_zero_of_summable {u : ℕ → ℝ} (hu : Summable u) :
    Tendsto (fun N : ℕ ↦ ∑' n : ℕ, if N < n then u n else 0) atTop (𝓝 0) := by
  have hpart : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), u n) atTop (𝓝 (∑' n : ℕ, u n)) :=
    hu.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have htail_eq (N : ℕ) :
      (∑' n : ℕ, if N < n then u n else 0) =
        (∑' n : ℕ, u n) - ∑ n ∈ Finset.range (N + 1), u n := by
    have hsplit_fn : u = (fun n ↦ if n ≤ N then u n else 0) + (fun n ↦ if N < n then u n else 0) := by
      funext n
      simp only [Pi.add_apply]
      rcases le_or_gt n N with h | h
      · simp [h, not_lt_of_ge h]
      · simp [not_le_of_gt h, h]
    have h1 : Summable fun n : ℕ ↦ if n ≤ N then u n else 0 := by
      refine summable_of_hasFiniteSupport ?_
      refine (Finset.finite_toSet (Finset.range (N + 1))).subset fun n hn ↦ ?_
      simp only [Function.mem_support, ne_eq] at hn
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hn (ite_eq_right (Nat.not_le_of_gt hmem))
    have h2 : Summable fun n : ℕ ↦ if N < n then u n else 0 := by
      have heq : (fun n : ℕ ↦ if N < n then u n else 0) =
          u - fun n : ℕ ↦ if n ≤ N then u n else 0 := by
        funext n
        simp only [Pi.sub_apply]
        rcases le_or_gt n N with h | h
        · simp [h, not_lt_of_ge h]
        · simp [h, not_le_of_gt h]
      rw [heq]
      exact hu.sub h1
    have hsum1 : (∑' n : ℕ, if n ≤ N then u n else 0) = ∑ n ∈ Finset.range (N + 1), u n := by
      rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range (N + 1))
        (f := fun n : ℕ ↦ if n ≤ N then u n else 0) fun n hn ↦ by
          simp only [Finset.mem_range, not_lt] at hn
          exact ite_eq_right (Nat.not_le_of_gt hn)]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      exact ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    have hadd : (∑' n : ℕ, u n) =
        (∑' n : ℕ, if n ≤ N then u n else 0) + (∑' n : ℕ, if N < n then u n else 0) := by
      nth_rw 1 [hsplit_fn]
      exact h1.tsum_add h2
    linarith
  have hsub := (tendsto_const_nhds (x := ∑' n : ℕ, u n)).sub hpart
  rw [sub_self] at hsub
  exact hsub.congr fun N ↦ (htail_eq N).symm

private theorem norm_LSeries_sub_dirichletPoly_le {a : ℕ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a (σ : ℂ)) (N : ℕ) (t : ℝ) :
    ‖LSeries a ((σ : ℂ) + (t : ℂ) * I) - dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      ∑' n : ℕ, if N < n then ‖LSeries.term a (σ : ℂ) n‖ else 0 := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hterm_norm : ∀ n : ℕ, ‖LSeries.term a s n‖ = ‖LSeries.term a (σ : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp [s]
  have hs_sum : LSeriesSummable a s := by
    refine Summable.of_norm ?_
    simpa [hterm_norm] using ha.norm
  have hpoly_tsum : dirichletPoly a N s = ∑' n : ℕ, if n ≤ N then LSeries.term a s n else 0 := by
    rw [dirichletPoly_eq_dirichletPartialSum, dirichletPartialSum]
    symm
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.Icc 1 N)
      (f := fun n : ℕ ↦ if n ≤ N then LSeries.term a s n else 0) fun n hn ↦ ?_]
    · refine Finset.sum_congr rfl fun n hn ↦ ?_
      exact ite_eq_left (Finset.mem_Icc.mp hn).2
    · simp only [Finset.mem_Icc, not_and, not_le] at hn
      by_cases hn0 : n = 0
      · subst hn0; simp [LSeries.term_zero]
      · exact ite_eq_right (not_le_of_gt (hn (Nat.pos_of_ne_zero hn0)))
  have h1 : Summable fun n : ℕ ↦ if n ≤ N then LSeries.term a s n else 0 := by
    refine summable_of_hasFiniteSupport ?_
    refine (Finset.finite_toSet (Finset.range (N + 1))).subset fun n hn ↦ ?_
    simp only [Function.mem_support, ne_eq] at hn
    by_contra hmem
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
    exact hn (ite_eq_right (Nat.not_le_of_gt hmem))
  have hdiff : LSeries a s - dirichletPoly a N s =
      ∑' n : ℕ, if N < n then LSeries.term a s n else 0 := by
    rw [LSeries, hpoly_tsum, ← hs_sum.tsum_sub h1]
    congr 1
    funext n
    by_cases hn : n ≤ N
    · simp [hn, not_lt_of_ge hn]
    · simp [hn, lt_of_not_ge hn]
  have h2_norm : Summable fun n : ℕ ↦ ‖if N < n then LSeries.term a s n else 0‖ := by
    refine ha.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    split_ifs <;> simp [hterm_norm]
  rw [hdiff]
  refine (norm_tsum_le_tsum_norm h2_norm).trans ?_
  refine h2_norm.tsum_le_tsum (fun n ↦ ?_) ?_
  · split_ifs
    · exact (hterm_norm n).le
    · simp
  · refine ha.norm.of_nonneg_of_le (fun _ ↦ by split_ifs <;> positivity) fun n ↦ ?_
    split_ifs <;> simp [norm_nonneg]

private theorem continuous_LSeries_vertical {a : ℕ → ℂ} {σ : ℝ} (ha : LSeriesSummable a (σ : ℂ)) :
    Continuous fun t : ℝ ↦ LSeries a ((σ : ℂ) + (t : ℂ) * I) := by
  let tail : ℕ → ℝ := fun N ↦ ∑' n : ℕ, if N < n then ‖LSeries.term a (σ : ℂ) n‖ else 0
  have htail : Tendsto tail atTop (𝓝 0) := tail_tendsto_zero_of_summable ha.norm
  have htu : TendstoUniformly (fun N (t : ℝ) ↦ dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I))
      (fun t : ℝ ↦ LSeries a ((σ : ℂ) + (t : ℂ) * I)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp htail ε hε)] with N hN t
    have hbound := norm_LSeries_sub_dirichletPoly_le ha N t
    have hN_nonneg : 0 ≤ tail N := tsum_nonneg fun n ↦ by split_ifs <;> positivity
    have hN_lt : tail N < ε := by
      have := hN
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hN_nonneg] at this
      exact this
    rw [Complex.dist_eq]
    exact lt_of_le_of_lt hbound hN_lt
  exact htu.continuous (Eventually.of_forall fun N ↦ continuous_dirichletPoly_vertical a N σ).frequently

private theorem abs_sq_sub_sq_le {u v δ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (huv : |v - u| ≤ δ) : |v ^ 2 - u ^ 2| ≤ δ * u ^ 2 + (δ + δ ^ 2) := by
  have hv_le : v ≤ u + δ := by linarith [(abs_le.mp huv).2]
  have huv_abs : |v - u| * (v + u) ≤ δ * (2 * u + δ) := by
    refine mul_le_mul huv (by linarith) (by positivity) hδ
  have hamgm : 2 * u * δ ≤ δ * u ^ 2 + δ := by
    have : 0 ≤ δ * (u - 1) ^ 2 := mul_nonneg hδ (sq_nonneg _)
    nlinarith
  calc
    |v ^ 2 - u ^ 2| = |v - u| * |v + u| := by
      rw [show v ^ 2 - u ^ 2 = (v - u) * (v + u) by ring, abs_mul]
    _ = |v - u| * (v + u) := by rw [abs_of_nonneg (add_nonneg hv hu)]
    _ ≤ δ * (2 * u + δ) := huv_abs
    _ = 2 * u * δ + δ ^ 2 := by ring
    _ ≤ (δ * u ^ 2 + δ) + δ ^ 2 := by linarith
    _ = δ * u ^ 2 + (δ + δ ^ 2) := by ring

/-- **Mean value theorem for Dirichlet series** (summable-term form):
for any `σ` with `LSeriesSummable a (σ : ℂ)`,
`(1 / (2T)) ∫_{-T}^T ‖LSeries a (σ + it)‖^2 dt → ∑' n, ‖LSeries.term a (σ : ℂ) n‖^2` as `T → ∞`. -/
theorem tendsto_mean_sq_LSeries {a : ℕ → ℂ} {σ : ℝ} (ha : LSeriesSummable a (σ : ℂ)) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * T)) *
        ∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ ^ 2)) := by
  let S : ℝ := ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ ^ 2
  have hS_nonneg : 0 ≤ S := tsum_nonneg fun _ ↦ sq_nonneg _
  have hS_sum := summable_norm_sq_LSeries_term ha
  have hf_cont : Continuous fun t : ℝ ↦ LSeries a ((σ : ℂ) + (t : ℂ) * I) :=
    continuous_LSeries_vertical ha
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := min 1 ((ε / 3) / (S + 3))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos (by linarith) (by linarith))
  have hδ_le1 : δ ≤ 1 := min_le_left _ _
  have hδ_small : δ * (S + 1) + (δ + δ ^ 2) ≤ ε / 3 := by
    have hδ_le2 : δ ≤ (ε / 3) / (S + 3) := min_le_right _ _
    have hsq : δ ^ 2 ≤ δ := by nlinarith [sq_nonneg δ]
    calc
      δ * (S + 1) + (δ + δ ^ 2) ≤ δ * (S + 1) + (δ + δ) := by linarith
      _ = δ * (S + 3) := by ring
      _ ≤ ((ε / 3) / (S + 3)) * (S + 3) := by gcongr
      _ = ε / 3 := div_mul_cancel₀ _ (by linarith)
  let tail : ℕ → ℝ := fun N ↦ ∑' n : ℕ, if N < n then ‖LSeries.term a (σ : ℂ) n‖ else 0
  have htail_lim : Tendsto tail atTop (𝓝 0) := tail_tendsto_zero_of_summable ha.norm
  have hpart_lim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
      atTop (𝓝 S) := by
    have h := hS_sum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact h.congr fun N ↦ (sum_diag_eq_sum_range_norm_sq_term a N σ).symm
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp htail_lim δ hδ_pos
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hpart_lim (ε / 3) (by linarith)
  let N : ℕ := max N₁ N₂
  let D : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)
  have hD_le_S : D ≤ S := by
    dsimp only [D]
    rw [sum_diag_eq_sum_range_norm_sq_term]
    exact hS_sum.sum_le_tsum (Finset.range (N + 1)) fun _ _ ↦ sq_nonneg _
  have hD_close : |D - S| < ε / 3 := by
    have hdist := hN₂ N (le_max_right N₁ N₂)
    rw [Real.dist_eq] at hdist
    exact hdist
  have htail_le : tail N ≤ δ := by
    have h0 : 0 ≤ tail N := tsum_nonneg fun n ↦ by split_ifs <;> positivity
    have hlt := hN₁ N (le_max_left N₁ N₂)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hlt
    exact hlt.le
  have hpoly_lim := tendsto_mean_sq_dirichletPoly a N σ
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp hpoly_lim (min (ε / 3) 1) (lt_min (by linarith) zero_lt_one)
  refine ⟨max T₀ 1, fun T hT ↦ ?_⟩
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_right T₀ 1).trans hT)
  have hT_ge : T₀ ≤ T := (le_max_left T₀ 1).trans hT
  have hpoly_close : |(1 / (2 * T)) *
      (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - D| < min (ε / 3) 1 := by
    have hdist := hT₀ T hT_ge
    rw [Real.dist_eq] at hdist
    exact hdist
  have hpoly_le : (1 / (2 * T)) *
      (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ S + 1 := by
    have h1 : (1 / (2 * T)) *
        (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - D < 1 :=
      lt_of_lt_of_le ((abs_lt.mp hpoly_close).2) (min_le_right _ _)
    linarith
  have hmean_diff :
      |(1 / (2 * T)) * (∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        (1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)| ≤
        δ * (S + 1) + (δ + δ ^ 2) := by
    have hc1 : Continuous fun t : ℝ ↦ ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      (hf_cont.norm).pow 2
    have hc2 : Continuous fun t : ℝ ↦ ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      ((continuous_dirichletPoly_vertical a N σ).norm).pow 2
    have hc_abs : Continuous fun t : ℝ ↦
        |‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 -
          ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2| :=
      (hc1.sub hc2).abs
    have hc_rhs : Continuous fun t : ℝ ↦
        δ * ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 + (δ + δ ^ 2) :=
      (continuous_const.mul hc2).add continuous_const
    have hsub_int :
        (∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
          ∫ t in (-T)..T, (‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 -
            ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
      (intervalIntegral.integral_sub (hc1.intervalIntegrable (-T) T)
        (hc2.intervalIntegrable (-T) T)).symm
    have habs_int :
        |(∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
            (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)| ≤
          ∫ t in (-T)..T, |‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 -
            ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2| := by
      rw [hsub_int]
      simpa [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun t : ℝ ↦ ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 -
            ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (by linarith : -T ≤ T)
    have hmono :
        (∫ t in (-T)..T, |‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 -
            ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2|) ≤
          ∫ t in (-T)..T, (δ * ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 + (δ + δ ^ 2)) := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (hc_abs.intervalIntegrable (-T) T) (hc_rhs.intervalIntegrable (-T) T) fun t _ ↦ ?_
      have huv : |‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ -
          ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖| ≤ δ := by
        exact (abs_norm_sub_norm_le _ _).trans
          ((norm_LSeries_sub_dirichletPoly_le ha N t).trans htail_le)
      exact abs_sq_sub_sq_le (norm_nonneg _) (norm_nonneg _) hδ_pos.le huv
    have hrhs_eval :
        (∫ t in (-T)..T, (δ * ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 + (δ + δ ^ 2))) =
          δ * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
            (2 * T) * (δ + δ ^ 2) := by
      have hadd := intervalIntegral.integral_add
        (f := fun t : ℝ ↦ δ * ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        (g := fun _ : ℝ ↦ δ + δ ^ 2)
        ((continuous_const.mul hc2).intervalIntegrable (-T) T)
        (intervalIntegrable_const (μ := volume))
      rw [hadd, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        smul_eq_mul, sub_neg_eq_add, ← two_mul]
    have heq_fac :
        (1 / (2 * T)) * (∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          (1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
          (1 / (2 * T)) * ((∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
            (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)) := by
      ring
    have hmul_scale (x y : ℝ) :
        (1 / (2 * T)) * (δ * x + (2 * T) * y) = δ * ((1 / (2 * T)) * x) + y := by
      field_simp [hT_pos.ne']
    rw [heq_fac, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
    calc
      (1 / (2 * T)) * |(∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)|
          ≤ (1 / (2 * T)) * (δ * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
              (2 * T) * (δ + δ ^ 2)) := by
        gcongr
        exact habs_int.trans (hmono.trans_eq hrhs_eval)
      _ = δ * ((1 / (2 * T)) * ∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
            (δ + δ ^ 2) := hmul_scale _ _
      _ ≤ δ * (S + 1) + (δ + δ ^ 2) := by gcongr
  have hsplit3 (x y z w : ℝ) : x - w = (x - y) + ((y - z) + (z - w)) := by ring
  rw [Real.dist_eq,
    hsplit3 ((1 / (2 * T)) * ∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ((1 / (2 * T)) * ∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) D S]
  calc
    |((1 / (2 * T)) * (∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
          (1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)) +
        (((1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - D) +
          (D - S))|
        ≤ |(1 / (2 * T)) * (∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
            (1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)| +
            (|(1 / (2 * T)) * (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - D| +
              |D - S|) := (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ < (ε / 3) + (ε / 3 + ε / 3) := by
      have hpoly_lt : |(1 / (2 * T)) *
          (∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) - D| < ε / 3 :=
        lt_of_lt_of_le hpoly_close (min_le_left _ _)
      linarith [hmean_diff, hδ_small, hpoly_lt, hD_close]
    _ = ε := by ring

/-- **Mean value theorem for Dirichlet series** (explicit `‖a n‖ ^ 2 * n ^ (-2σ)` form):
when `LSeriesSummable a (σ : ℂ)` and either `σ ≠ 0` or `a 0 = 0` (so the `n = 0` term vanishes),
`(1 / (2T)) ∫_{-T}^T ‖LSeries a (σ + it)‖^2 dt → ∑' n, ‖a n‖^2 * (n : ℝ) ^ (-2σ)` as `T → ∞`. -/
theorem tendsto_mean_sq_LSeries_eq_tsum_norm_sq_mul {a : ℕ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a (σ : ℂ)) (h0 : σ ≠ 0 ∨ a 0 = 0) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * T)) *
        ∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))) := by
  have heq : (fun n : ℕ ↦ ‖LSeries.term a (σ : ℂ) n‖ ^ 2) =
      fun n : ℕ ↦ ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · rcases h0 with hσ | ha0
      · have hexp : -(2 * σ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero two_ne_zero hσ)
        rw [LSeries.term_zero, norm_zero, sq, zero_mul, Nat.cast_zero,
          show -2 * σ = -(2 * σ) by ring, Real.zero_rpow hexp, mul_zero]
      · simp [LSeries.term_zero, ha0]
    · exact norm_sq_LSeries_term_of_ne_zero σ hn
  rw [← heq]
  exact tendsto_mean_sq_LSeries ha

/-- **Mean value theorem for Dirichlet series** in the half-plane `σ_a < σ` (assuming `σ ≠ 0 ∨ a 0 = 0`,
for instance `0 < σ` or arithmetic functions with `a 0 = 0`). -/
theorem tendsto_mean_sq_LSeries_of_abscissaOfAbsConv_lt {a : ℕ → ℂ} {σ : ℝ}
    (hσ : LSeries.abscissaOfAbsConv a < (σ : EReal)) (h0 : σ ≠ 0 ∨ a 0 = 0) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * T)) *
        ∫ t in (-T)..T, ‖LSeries a ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))) :=
  tendsto_mean_sq_LSeries_eq_tsum_norm_sq_mul
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hσ)) h0

end AnalyticNumberTheory.DirichletSeries
