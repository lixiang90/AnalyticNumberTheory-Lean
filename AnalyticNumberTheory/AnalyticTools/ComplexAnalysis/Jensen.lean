import Mathlib.Analysis.Complex.JensenFormula

/-!
# Shifted Jensen's Formula and Zero-Counting Bounds

This file develops shifted Jensen's formula on `Metric.closedBall z₀ R` and the resulting
upper bounds on the zero-counting function `zeroCount f z₀ r` for analytic functions in
analytic number theory.

## Main Definitions

* `zeroSet f z₀ r` : the set of zeros of `f` in `Metric.closedBall z₀ r`.
* `zeroCount f z₀ r` : the total number of zeros of `f` in `Metric.closedBall z₀ r`,
  counted with multiplicity.

## Main Theorems

* `jensen_formula` : shifted Jensen's formula on `Metric.closedBall z₀ R` for analytic `f`
  with `f z₀ ≠ 0`.
* `zeroCount_le_log_div_log` / `zeroCount_le_sub_log_div_log` : fundamental zero-counting
  inequality `n(r) ≤ (log M - log ‖f z₀‖) / log (R / r)`.
* `zeroCount_le_of_ball` : open-ball variant for functions holomorphic on `Metric.ball z₀ R`.
* `ncard_zeroSet_le_sub_log_div_log` / `finset_card_zeros_le_sub_log_div_log` : explicit
  `Set.ncard` and `Finset.card` bounds for distinct zeros.
-/

open Complex Filter MeromorphicOn Metric Real Set
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- The set of zeros of `f : ℂ → ℂ` lying in `Metric.closedBall z₀ r`. -/
def zeroSet (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) : Set ℂ :=
  {z ∈ Metric.closedBall z₀ r | f z = 0}

/-- The number of zeros of `f : ℂ → ℂ` in `Metric.closedBall z₀ r`, counted with multiplicity
via the meromorphic divisor on the closed ball. -/
noncomputable def zeroCount (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall z₀ r) u).toNat

/-- Characterization of membership in `zeroSet`. -/
@[simp]
lemma mem_zeroSet {f : ℂ → ℂ} {z₀ z : ℂ} {r : ℝ} :
    z ∈ zeroSet f z₀ r ↔ z ∈ Metric.closedBall z₀ r ∧ f z = 0 :=
  Iff.rfl

/-- For an analytic function on `Metric.closedBall z₀ r`, casting `zeroCount` to `ℤ` recovers the
finsum of the divisor. -/
lemma zeroCount_coe_int {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) :
    (zeroCount f z₀ r : ℤ) = ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall z₀ r) u := by
  have hsupp : (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).finiteSupport (isCompact_closedBall z₀ r)
  have hnonneg : ∀ u, 0 ≤ MeromorphicOn.divisor f (Metric.closedBall z₀ r) u :=
    hf.divisor_nonneg
  unfold zeroCount
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset),
    finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    exact Int.toNat_of_nonneg (hnonneg u)
  · intro u hu
    simpa [Function.mem_support] using hu
  · intro u hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    simp only [Function.mem_support, ne_eq] at hu
    intro h0
    apply hu
    simp [h0]

/-- For an analytic function on `Metric.closedBall z₀ r`, casting `zeroCount` to `ℝ` recovers the
real finsum of the divisor. -/
lemma zeroCount_coe_real {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) :
    (zeroCount f z₀ r : ℝ) = ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall z₀ r) u : ℝ) := by
  have hsupp : (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).finiteSupport (isCompact_closedBall z₀ r)
  rw [← Int.cast_natCast (R := ℝ) (zeroCount f z₀ r), zeroCount_coe_int hf]
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset),
    finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset)]
  · push_cast; rfl
  · intro u hu
    simpa using (Function.mem_support.mp hu)
  · intro u hu
    simpa using hu

/-- If `f` is analytic on `Metric.closedBall z₀ r` (`0 ≤ r`) and `f z₀ ≠ 0`, then `analyticOrderAt f u`
is finite at every `u ∈ Metric.closedBall z₀ r`. -/
lemma analyticOrderAt_ne_top_of_closedBall {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) (hz₀ : f z₀ ≠ 0)
    {u : ℂ} (hu : u ∈ Metric.closedBall z₀ r) :
    analyticOrderAt f u ≠ ⊤ := by
  apply hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall z₀ r).isPreconnected
    (mem_closedBall_self hr) hu
  exact (hf z₀ (mem_closedBall_self hr)).analyticOrderAt_eq_zero.mpr hz₀ |>.symm ▸ by simp

/-- Under `AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)` (`0 ≤ r`) and `f z₀ ≠ 0`, the support of the
divisor on `Metric.closedBall z₀ r` coincides with `zeroSet f z₀ r`. -/
lemma divisor_support_eq_zeroSet {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) (hz₀ : f z₀ ≠ 0) :
    (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).support = zeroSet f z₀ r := by
  ext u
  rw [Function.mem_support, mem_zeroSet]
  by_cases hu : u ∈ Metric.closedBall z₀ r
  · have htop : analyticOrderAt f u ≠ ⊤ := analyticOrderAt_ne_top_of_closedBall hr hf hz₀ hu
    have hdiv : MeromorphicOn.divisor f (Metric.closedBall z₀ r) u = (analyticOrderNatAt f u : ℤ) := by
      rw [hf.divisor_apply hu, ← Nat.cast_analyticOrderNatAt htop]
      simp
    rw [hdiv]
    simp only [ne_eq, Int.natCast_eq_zero, hu, true_and]
    have h0 : analyticOrderNatAt f u = 0 ↔ f u ≠ 0 := by
      rw [← (hf u hu).analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt htop]
      norm_cast
    exact h0.not.trans not_not
  · simp [hu]

/-- Under `AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)` (`0 ≤ r`) and `f z₀ ≠ 0`, `zeroSet f z₀ r` is
finite. -/
lemma zeroSet_finite {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) (hz₀ : f z₀ ≠ 0) :
    (zeroSet f z₀ r).Finite := by
  rw [← divisor_support_eq_zeroSet hr hf hz₀]
  exact (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).finiteSupport (isCompact_closedBall z₀ r)

/-- Express `zeroCount f z₀ r` as the sum of `analyticOrderNatAt f u` over any `Finset` `S`
whose coercion equals `zeroSet f z₀ r`. -/
lemma zeroCount_eq_sum_analyticOrderNatAt {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) (hz₀ : f z₀ ≠ 0)
    {S : Finset ℂ} (hS : (S : Set ℂ) = zeroSet f z₀ r) :
    zeroCount f z₀ r = ∑ u ∈ S, analyticOrderNatAt f u := by
  have hsupp : (MeromorphicOn.divisor f (Metric.closedBall z₀ r)).support ⊆ (S : Set ℂ) := by
    rw [hS, divisor_support_eq_zeroSet hr hf hz₀]
  unfold zeroCount
  rw [finsum_eq_sum_of_support_subset _ (s := S)]
  · refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu_mem : u ∈ zeroSet f z₀ r := by rw [← hS]; exact hu
    have hu_ball : u ∈ Metric.closedBall z₀ r := hu_mem.1
    have htop := analyticOrderAt_ne_top_of_closedBall hr hf hz₀ hu_ball
    rw [hf.divisor_apply hu_ball, ← Nat.cast_analyticOrderNatAt htop]
    simp
  · intro u hu
    apply hsupp
    simp only [Function.mem_support, ne_eq, Int.toNat_eq_zero, not_le] at hu ⊢
    exact hu.ne'

/-- The number of distinct zeros in `Metric.closedBall z₀ r` is bounded above by `zeroCount f z₀ r`. -/
theorem ncard_zeroSet_le_zeroCount {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) (hz₀ : f z₀ ≠ 0) :
    (zeroSet f z₀ r).ncard ≤ zeroCount f z₀ r := by
  have hfin := zeroSet_finite hr hf hz₀
  rw [Set.ncard_eq_toFinset_card (zeroSet f z₀ r) hfin,
    zeroCount_eq_sum_analyticOrderNatAt hr hf hz₀ (Set.Finite.coe_toFinset hfin)]
  calc
    hfin.toFinset.card = ∑ _u ∈ hfin.toFinset, 1 := by simp
    _ ≤ ∑ u ∈ hfin.toFinset, analyticOrderNatAt f u := by
      refine Finset.sum_le_sum fun u hu ↦ ?_
      have hu_mem : u ∈ zeroSet f z₀ r := hfin.mem_toFinset.mp hu
      have htop := analyticOrderAt_ne_top_of_closedBall hr hf hz₀ hu_mem.1
      have hne : analyticOrderAt f u ≠ 0 :=
        (hf u hu_mem.1).analyticOrderAt_eq_zero.not.mpr (not_not.mpr hu_mem.2)
      have hnat_ne : analyticOrderNatAt f u ≠ 0 := by
        intro h0
        apply hne
        rw [← Nat.cast_analyticOrderNatAt htop, h0]
        rfl
      exact Nat.one_le_iff_ne_zero.mpr hnat_ne

/-- Any `Finset` of zeros of `f` in `Metric.closedBall z₀ r` has cardinality at most `zeroCount f z₀ r`. -/
theorem finset_card_le_zeroCount {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r)) (hz₀ : f z₀ ≠ 0)
    {S : Finset ℂ} (hS : ∀ z ∈ S, z ∈ Metric.closedBall z₀ r ∧ f z = 0) :
    S.card ≤ zeroCount f z₀ r := by
  have hfin := zeroSet_finite hr hf hz₀
  have hsub : S ⊆ hfin.toFinset := fun z hz ↦ hfin.mem_toFinset.mpr (hS z hz)
  calc
    S.card ≤ hfin.toFinset.card := Finset.card_le_card hsub
    _ = (zeroSet f z₀ r).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    _ ≤ zeroCount f z₀ r := ncard_zeroSet_le_zeroCount hr hf hz₀

/-- Monotonicity of `zeroCount` in the radius `r`. -/
theorem zeroCount_mono {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r₂)) :
    zeroCount f z₀ r₁ ≤ zeroCount f z₀ r₂ := by
  have hsub : Metric.closedBall z₀ r₁ ⊆ Metric.closedBall z₀ r₂ :=
    Metric.closedBall_subset_closedBall hr
  have hf₁ : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r₁) := hf.mono hsub
  have hsupp₁ : (MeromorphicOn.divisor f (Metric.closedBall z₀ r₁)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall z₀ r₁)).finiteSupport (isCompact_closedBall z₀ r₁)
  have hsupp₂ : (MeromorphicOn.divisor f (Metric.closedBall z₀ r₂)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall z₀ r₂)).finiteSupport (isCompact_closedBall z₀ r₂)
  let U : Finset ℂ := hsupp₁.toFinset ∪ hsupp₂.toFinset
  have hs₁ : (fun u ↦ (MeromorphicOn.divisor f (Metric.closedBall z₀ r₁) u).toNat).support ⊆ U := by
    intro u hu
    simp only [Function.mem_support, ne_eq, Int.toNat_eq_zero, not_le] at hu
    exact Finset.mem_union_left _ (hsupp₁.mem_toFinset.mpr (by simp [hu.ne']))
  have hs₂ : (fun u ↦ (MeromorphicOn.divisor f (Metric.closedBall z₀ r₂) u).toNat).support ⊆ U := by
    intro u hu
    simp only [Function.mem_support, ne_eq, Int.toNat_eq_zero, not_le] at hu
    exact Finset.mem_union_right _ (hsupp₂.mem_toFinset.mpr (by simp [hu.ne']))
  unfold zeroCount
  rw [finsum_eq_sum_of_support_subset _ hs₁, finsum_eq_sum_of_support_subset _ hs₂]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  by_cases hu : u ∈ Metric.closedBall z₀ r₁
  · rw [hf₁.divisor_apply hu, hf.divisor_apply (hsub hu)]
  · simp [hu]

/-- Shifted **Jensen's Formula** for a meromorphic function on `Metric.closedBall z₀ R` (`0 < R`). -/
theorem jensen_formula_meromorphic {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (Metric.closedBall z₀ R)) :
    Real.circleAverage (fun z ↦ Real.log ‖f z‖) z₀ R =
      ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall z₀ R) u : ℝ) * Real.log (R / ‖z₀ - u‖)
        + (MeromorphicOn.divisor f (Metric.closedBall z₀ R) z₀ : ℝ) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt f z₀‖ := by
  have hf_abs : MeromorphicOn f (Metric.closedBall z₀ |R|) := by rwa [abs_of_pos hR]
  have h := hf_abs.circleAverage_log_norm (c := z₀) (R := R) hR.ne'
  rw [abs_of_pos hR] at h
  simpa only [div_eq_mul_inv] using h

/-- Shifted **Jensen's Formula** for an analytic function on `Metric.closedBall z₀ R` with `f z₀ ≠ 0`. -/
theorem jensen_formula {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0) :
    Real.circleAverage (fun z ↦ Real.log ‖f z‖) z₀ R =
      ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall z₀ R) u : ℝ) * Real.log (R / ‖z₀ - u‖)
        + Real.log ‖f z₀‖ := by
  have hf_abs : AnalyticOnNhd ℂ f (Metric.closedBall z₀ |R|) := by rwa [abs_of_pos hR]
  have h := hf_abs.circleAverage_log_norm hz₀
  rw [abs_of_pos hR] at h
  simpa only [div_eq_mul_inv] using h

/-- Integral form of shifted **Jensen's Formula** on `0..2 * π` for an analytic function on
`Metric.closedBall z₀ R` with `f z₀ ≠ 0`. -/
theorem jensen_formula_integral {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (z₀ + R * Complex.exp (θ * I))‖ =
      ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall z₀ R) u : ℝ) * Real.log (R / ‖z₀ - u‖)
        + Real.log ‖f z₀‖ := by
  have h := jensen_formula hR hf hz₀
  rw [Real.circleAverage_def, smul_eq_mul] at h
  simpa [circleMap] using h

/-- **Jensen's Zero-Counting Inequality** (ratio form): if `f` is analytic on
`Metric.closedBall z₀ R`, `f z₀ ≠ 0`, and `‖f z‖ ≤ M` on `Metric.sphere z₀ R` (`0 < M`),
then for `0 < r < R`,
`zeroCount f z₀ r ≤ Real.log (M / ‖f z₀‖) / Real.log (R / r)`. -/
theorem zeroCount_le_log_div_log {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.sphere z₀ R, ‖f z‖ ≤ M) :
    (zeroCount f z₀ r : ℝ) ≤ Real.log (M / ‖f z₀‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  let g : ℂ → ℂ := fun z ↦ (M : ℂ)⁻¹ * f z
  have hg : AnalyticOnNhd ℂ g (Metric.closedBall z₀ |R|) := by
    rw [abs_of_pos hR]
    exact analyticOnNhd_const.mul hf
  have hgz₀ : g z₀ ≠ 0 := mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM.ne')) hz₀
  have hg_bound : ∀ z ∈ Metric.sphere z₀ |R|, ‖g z‖ ≤ 1 := by
    intro z hz
    rw [abs_of_pos hR] at hz
    simp only [g, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    rw [inv_mul_le_iff₀ hM, mul_one]
    exact hf_bound z hz
  have hdiv_g := hg.sum_divisor_le (r := r) (R := R) (M := 1)
    (by simpa [abs_of_pos hr] using hr) (by rwa [abs_of_pos hr, abs_of_pos hR]) le_rfl hgz₀ hg_bound
  have h_eq_div : ∀ u, MeromorphicOn.divisor g (Metric.closedBall z₀ |r|) u =
      MeromorphicOn.divisor f (Metric.closedBall z₀ r) u := by
    intro u
    rw [abs_of_pos hr]
    by_cases hu : u ∈ Metric.closedBall z₀ r
    · have hf_r : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r) :=
        hf.mono (Metric.closedBall_subset_closedBall hrR.le)
      have hg_r : AnalyticOnNhd ℂ g (Metric.closedBall z₀ r) := analyticOnNhd_const.mul hf_r
      rw [hg_r.divisor_apply hu, hf_r.divisor_apply hu]
      have htop : analyticOrderAt f u ≠ ⊤ :=
        analyticOrderAt_ne_top_of_closedBall hr.le hf_r hz₀ hu
      have h_ord_g : analyticOrderNatAt g u = analyticOrderNatAt f u := by
        apply analyticOrderNatAt_const_mul (hf_r u hu)
        exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hM.ne')
      have htop_g : analyticOrderAt g u ≠ ⊤ := by
        intro h
        have h' : analyticOrderAt f u = ⊤ := by
          have hg_eq : g = (fun _ ↦ (M : ℂ)⁻¹) * f := rfl
          have h1 := analyticOrderAt_mul (z₀ := u) (analyticAt_const (v := (M : ℂ)⁻¹)) (hf_r u hu)
          rw [← hg_eq, h] at h1
          have hcm : analyticOrderAt (fun _ : ℂ ↦ (M : ℂ)⁻¹) u = 0 :=
            (analyticAt_const).analyticOrderAt_eq_zero.mpr
              (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM.ne'))
          rw [hcm, zero_add] at h1
          exact h1.symm
        exact htop h'
      rw [← Nat.cast_analyticOrderNatAt htop_g, ← Nat.cast_analyticOrderNatAt htop, h_ord_g]
    · simp [hu]
  have hf_r : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r) :=
    hf.mono (Metric.closedBall_subset_closedBall hrR.le)
  have hsum_cast :
      (zeroCount f z₀ r : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor g (Metric.closedBall z₀ |r|) u : ℤ) : ℝ) := by
    exact_mod_cast (by
      rw [zeroCount_coe_int hf_r]
      exact le_of_eq (finsum_congr fun u ↦ (h_eq_div u).symm))
  have hnorm_g : 1 / ‖g z₀‖ = M / ‖f z₀‖ := by
    simp only [g, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    field_simp
  rw [hnorm_g] at hdiv_g
  exact hsum_cast.trans hdiv_g

/-- **Jensen's Zero-Counting Inequality** (difference of logs form):
`zeroCount f z₀ r ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r)`. -/
theorem zeroCount_le_sub_log_div_log {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.sphere z₀ R, ‖f z‖ ≤ M) :
    (zeroCount f z₀ r : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r) := by
  have h := zeroCount_le_log_div_log hr hrR hM hf hz₀ hf_bound
  rwa [Real.log_div hM.ne' (norm_ne_zero_iff.mpr hz₀)] at h

/-- Open-ball version of **Jensen's Zero-Counting Inequality**: if `f` is complex differentiable on
`Metric.ball z₀ R`, `f z₀ ≠ 0`, and `‖f z‖ ≤ M` for all `z ∈ Metric.ball z₀ R`, then
`zeroCount f z₀ r ≤ Real.log (M / ‖f z₀‖) / Real.log (R / r)` for all `0 < r < R`. -/
theorem zeroCount_le_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.ball z₀ R, ‖f z‖ ≤ M) :
    (zeroCount f z₀ r : ℝ) ≤ Real.log (M / ‖f z₀‖) / Real.log (R / r) := by
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball z₀ R) := hf.analyticOnNhd isOpen_ball
  have h_ev : ∀ᶠ R' in 𝓝[<] R,
      (zeroCount f z₀ r : ℝ) ≤ Real.log (M / ‖f z₀‖) / Real.log (R' / r) := by
    filter_upwards [Ioo_mem_nhdsLT hrR] with R' ⟨hrR', hR'R⟩
    refine zeroCount_le_log_div_log hr hrR' hM ?_ hz₀ ?_
    · exact hf_an.mono (Metric.closedBall_subset_ball hR'R)
    · intro z hz
      exact hf_bound z (Metric.closedBall_subset_ball hR'R (Metric.sphere_subset_closedBall hz))
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ h_ev
  refine ContinuousAt.continuousWithinAt ?_
  have h_ne : Real.log (R / r) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by rw [one_lt_div hr]; exact hrR)
  fun_prop (disch := simp [hr.ne', (hr.trans hrR).ne'])

/-- Open-ball version of **Jensen's Zero-Counting Inequality** in `log M - log ‖f z₀‖` form. -/
theorem zeroCount_le_sub_log_div_log_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.ball z₀ R, ‖f z‖ ≤ M) :
    (zeroCount f z₀ r : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r) := by
  have h := zeroCount_le_of_ball hr hrR hM hf hz₀ hf_bound
  rwa [Real.log_div hM.ne' (norm_ne_zero_iff.mpr hz₀)] at h

/-- Half-radius specialization of **Jensen's Zero-Counting Inequality** on `Metric.closedBall z₀ R`:
`zeroCount f z₀ (R / 2) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log 2`. -/
theorem zeroCount_half_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.sphere z₀ R, ‖f z‖ ≤ M) :
    (zeroCount f z₀ (R / 2) : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log 2 := by
  have h := zeroCount_le_sub_log_div_log (half_pos hR) (half_lt_self hR) hM hf hz₀ hf_bound
  have h2 : R / (R / 2) = 2 := by field_simp
  rwa [h2] at h

/-- Half-radius specialization of **Jensen's Zero-Counting Inequality** on `Metric.ball z₀ R`:
`zeroCount f z₀ (R / 2) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log 2`. -/
theorem zeroCount_half_le_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.ball z₀ R, ‖f z‖ ≤ M) :
    (zeroCount f z₀ (R / 2) : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log 2 := by
  have h := zeroCount_le_sub_log_div_log_of_ball (half_pos hR) (half_lt_self hR) hM hf hz₀ hf_bound
  have h2 : R / (R / 2) = 2 := by field_simp
  rwa [h2] at h

/-- Explicit `Set.ncard` form of Jensen's zero-counting inequality on `Metric.closedBall z₀ R`. -/
theorem ncard_zeroSet_le_sub_log_div_log {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.sphere z₀ R, ‖f z‖ ≤ M) :
    ((zeroSet f z₀ r).ncard : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r) := by
  have h1 : ((zeroSet f z₀ r).ncard : ℝ) ≤ zeroCount f z₀ r := by
    exact_mod_cast ncard_zeroSet_le_zeroCount hr.le
      (hf.mono (Metric.closedBall_subset_closedBall hrR.le)) hz₀
  exact h1.trans (zeroCount_le_sub_log_div_log hr hrR hM hf hz₀ hf_bound)

/-- Explicit `Set.ncard` form of Jensen's zero-counting inequality on `Metric.ball z₀ R`. -/
theorem ncard_zeroSet_le_sub_log_div_log_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.ball z₀ R, ‖f z‖ ≤ M) :
    ((zeroSet f z₀ r).ncard : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r) := by
  have hf_an : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r) :=
    (hf.analyticOnNhd isOpen_ball).mono (Metric.closedBall_subset_ball hrR)
  have h1 : ((zeroSet f z₀ r).ncard : ℝ) ≤ zeroCount f z₀ r := by
    exact_mod_cast ncard_zeroSet_le_zeroCount hr.le hf_an hz₀
  exact h1.trans (zeroCount_le_sub_log_div_log_of_ball hr hrR hM hf hz₀ hf_bound)

/-- Explicit `Finset.card` form of Jensen's zero-counting inequality on `Metric.closedBall z₀ R`:
for any finite set `S` of zeros of `f` in `Metric.closedBall z₀ r`,
`(S.card : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r)`. -/
theorem finset_card_zeros_le_sub_log_div_log {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.sphere z₀ R, ‖f z‖ ≤ M)
    {S : Finset ℂ} (hS : ∀ z ∈ S, z ∈ Metric.closedBall z₀ r ∧ f z = 0) :
    (S.card : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r) := by
  have h1 : (S.card : ℝ) ≤ zeroCount f z₀ r := by
    exact_mod_cast finset_card_le_zeroCount hr.le
      (hf.mono (Metric.closedBall_subset_closedBall hrR.le)) hz₀ hS
  exact h1.trans (zeroCount_le_sub_log_div_log hr hrR hM hf hz₀ hf_bound)

/-- Explicit `Finset.card` form of Jensen's zero-counting inequality on `Metric.ball z₀ R`. -/
theorem finset_card_zeros_le_sub_log_div_log_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ z ∈ Metric.ball z₀ R, ‖f z‖ ≤ M)
    {S : Finset ℂ} (hS : ∀ z ∈ S, z ∈ Metric.closedBall z₀ r ∧ f z = 0) :
    (S.card : ℝ) ≤ (Real.log M - Real.log ‖f z₀‖) / Real.log (R / r) := by
  have hf_an : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r) :=
    (hf.analyticOnNhd isOpen_ball).mono (Metric.closedBall_subset_ball hrR)
  have h1 : (S.card : ℝ) ≤ zeroCount f z₀ r := by
    exact_mod_cast finset_card_le_zeroCount hr.le hf_an hz₀ hS
  exact h1.trans (zeroCount_le_sub_log_div_log_of_ball hr hrR hM hf hz₀ hf_bound)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
