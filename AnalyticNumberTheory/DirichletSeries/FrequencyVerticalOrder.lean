import AnalyticNumberTheory.DirichletSeries.FrequencyVerticalBounds
import AnalyticNumberTheory.DirichletSeries.RightHalfPlaneLowerBound
import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-! # The vertical order of general Dirichlet series -/

noncomputable section

open Complex Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℂ}

/-- The sum on an interior line of ordered convergence has global polynomial
vertical growth of exponent one. -/
theorem hasPolyVerticalGrowth_sum_one {σ : ℝ} (hσ : F.abscissa a < (σ : EReal)) :
    HasPolyVerticalGrowth (F.sum a) σ 1 := by
  obtain ⟨C, hC, h⟩ := norm_sum_le_linear_halfPlane hσ
  refine ⟨C, hC, fun t => ?_⟩
  have H := h ((σ : ℂ) + t*I) (by simp)
  simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at H
  rw [Real.rpow_one]
  exact H.trans (mul_le_mul_of_nonneg_left (by linarith) hC)

/-- The vertical order is at most one throughout the open ordered convergence
half-plane, including frequencies of infinite exponential density. -/
theorem verticalOrder_sum_le_one {σ : ℝ} (hσ : F.abscissa a < (σ : EReal)) :
    verticalOrder (F.sum a) σ ≤ 1 :=
  verticalOrder_le_of_hasPolyVerticalGrowth zero_le_one (hasPolyVerticalGrowth_sum_one hσ)

/-- The vertical order is zero on every line of absolute convergence,
including the boundary line if it converges absolutely there. -/
theorem verticalOrder_sum_eq_zero {σ : ℝ} (h : F.AbsConvergesAt a (σ : ℂ)) :
    verticalOrder (F.sum a) σ = 0 := by
  apply le_antisymm _ (verticalOrder_nonneg _ _)
  apply verticalOrder_le_of_hasPolyVerticalGrowth (le_refl 0)
  refine ⟨∑' k, ‖a k‖ * Real.exp (-σ*F k), tsum_nonneg (fun _ => by positivity), ?_⟩
  intro t
  rw [Real.rpow_zero, mul_one]
  exact h.norm_sum_le_right_halfPlane (by simp)

private lemma convexOn_order_interval {p q : ℝ} (hp : F.abscissa a < (p : EReal)) (hpq : p < q) :
    ConvexOn ℝ (Icc p q) (verticalOrder (F.sum a)) := by
  obtain ⟨C, hC, hbound⟩ := norm_sum_le_linear_halfPlane hp
  let c := (Real.pi / (q-p))/2
  have hπ := div_pos Real.pi_pos (sub_pos.mpr hpq)
  have hc : 0 < c := half_pos hπ
  have hdiff : DiffContOnCl ℂ (F.sum a) (verticalStripOpen p q) := by
    have hf := (F.analyticOnNhd_sum a).differentiableOn
    refine ⟨hf.mono (fun z hz => hp.trans_le (EReal.coe_le_coe_iff.mpr hz.1.le)), hf.continuousOn.mono ?_⟩
    rw [closure_verticalStripOpen hpq]
    exact fun z hz => hp.trans_le (EReal.coe_le_coe_iff.mpr hz.1)
  apply convexOn_verticalOrder_Icc (B := c⁻¹) (c := c) hdiff hC (half_lt_self hπ)
  · intro z hz
    apply (hbound z hz.1.le).trans
    apply mul_le_mul_of_nonneg_left _ hC
    calc
      1 + |z.im| ≤ Real.exp |z.im| := by linarith [Real.add_one_le_exp |z.im|]
      _ ≤ Real.exp (c⁻¹ * Real.exp (c * |z.im|)) := by
        apply Real.exp_le_exp.mpr
        rw [inv_mul_eq_div, le_div_iff₀ hc]
        linarith [Real.add_one_le_exp (c * |z.im|), mul_comm c |z.im|]
  · intro σ hσ
    exact ⟨1, zero_le_one, (hasPolyVerticalGrowth_sum_one
      (hp.trans_le (EReal.coe_le_coe_iff.mpr hσ.1))).hasVerticalOrder⟩

/-- The vertical order is convex on the full open ordered convergence
half-plane. The abscissa may take either extended-real endpoint. -/
theorem convexOn_verticalOrder_sum (F : DirichletFrequency) (a : ℕ → ℂ) :
    ConvexOn ℝ {σ : ℝ | F.abscissa a < (σ : EReal)} (verticalOrder (F.sum a)) := by
  have domain (b : EReal) : Convex ℝ {σ : ℝ | b < (σ : EReal)} := by
    induction b using EReal.rec with
    | bot => simpa using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    | coe b =>
      rw [show {σ : ℝ | (b : EReal) < σ} = Ioi b from Set.ext fun _ => EReal.coe_lt_coe_iff]
      exact convex_Ioi b
    | top => simpa using (convex_empty : Convex ℝ (∅ : Set ℝ))
  refine ⟨domain _, fun x hx y hy tx ty htx hty hsum => ?_⟩
  change F.abscissa a < (x : EReal) at hx
  change F.abscissa a < (y : EReal) at hy
  let p := min x y
  let q := max x y + 1
  have hp : F.abscissa a < (p : EReal) := by
    rcases min_cases x y with ⟨h, _⟩ | ⟨h, _⟩
    · simpa only [p, h] using hx
    · simpa only [p, h] using hy
  have hxI : x ∈ Icc p q := ⟨min_le_left _ _, by dsimp [q]; linarith [le_max_left x y]⟩
  have hyI : y ∈ Icc p q := ⟨min_le_right _ _, by dsimp [q]; linarith [le_max_right x y]⟩
  have hpq : p < q := by dsimp [p, q]; linarith [min_le_left x y, le_max_left x y]
  exact (convexOn_order_interval hp hpq).2 hxI hyI htx hty hsum

/-- On the open ordered convergence half-plane the vertical order is
continuous. -/
theorem continuousOn_verticalOrder_sum (F : DirichletFrequency) (a : ℕ → ℂ) :
    ContinuousOn (verticalOrder (F.sum a)) {σ : ℝ | F.abscissa a < (σ : EReal)} := by
  have hop : IsOpen {σ : ℝ | F.abscissa a < (σ : EReal)} := isOpen_lt continuous_const continuous_coe_real_ereal
  simpa only [hop.interior_eq] using (convexOn_verticalOrder_sum F a).continuousOn_interior

/-- The vertical order is nonincreasing, even when there is no line of
absolute convergence. Convexity and the global upper bound one suffice. -/
theorem antitoneOn_verticalOrder_sum (F : DirichletFrequency) (a : ℕ → ℂ) :
    AntitoneOn (verticalOrder (F.sum a)) {σ : ℝ | F.abscissa a < (σ : EReal)} := by
  intro x hx y _ hxy
  obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
  have hsub : Ioi r ⊆ {σ : ℝ | F.abscissa a < (σ : EReal)} :=
    fun z hz => hr.trans (EReal.coe_lt_coe_iff.mpr hz)
  have hc := (convexOn_verticalOrder_sum F a).subset hsub (convex_Ioi _)
  have hanti := antitoneOn_of_convexOn_Ioi_of_bddAbove hc
    ⟨x, 1, fun z hz => verticalOrder_sum_le_one (hx.trans_le (EReal.coe_le_coe_iff.mpr hz))⟩
  exact hanti (EReal.coe_lt_coe_iff.mp hrx) ((EReal.coe_lt_coe_iff.mp hrx).trans_le hxy) hxy

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
