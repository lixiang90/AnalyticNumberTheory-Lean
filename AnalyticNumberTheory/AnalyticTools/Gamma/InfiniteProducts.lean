/-
Copyright (c) 2026 AnalyticNumberTheory-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
# Infinite Products and Analyticity

This file develops a unified API for infinite products in `ℝ`, `ℂ`, and complete normed
commutative rings, covering:
- Convergence criteria for `∏' n, (1 + a n)` via absolute summability `Summable (fun n => ‖a n‖)`
  and exact equivalence `Multipliable (fun n => 1 + a n) ↔ Summable a` for non-negative real terms
- Zero criterion `∏' n, f n = 0 ↔ ∃ n, f n = 0` under `Summable (fun n => ‖f n - 1‖)`
- Exponential-sum to infinite-product identities `exp (∑' n, g n) = ∏' n, exp (g n)`
- Uniform and locally uniform convergence of infinite products via Weierstrass M-test bounds
- Holomorphicity (`DifferentiableOn`, `AnalyticOnNhd`) and logarithmic differentiation of
  locally uniformly convergent infinite products of analytic functions.
-/

open Filter Function Set Topology

open scoped BigOperators

namespace AnalyticNumberTheory.AnalyticTools.Gamma

section NonnegReal

variable {ι : Type*}

/-- For non-negative real terms on a finite set `s`, `1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i)`. -/
theorem one_add_sum_le_prod_one_add_of_nonneg (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hai : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
    have hsum : 0 ≤ ∑ j ∈ s, a j :=
      Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have ih' : 1 + ∑ j ∈ s, a j ≤ ∏ j ∈ s, (1 + a j) :=
      ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    nlinarith

/-- For non-negative real terms on a finite set `s`, `∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i)`. -/
theorem prod_one_add_le_rexp_sum_of_nonneg (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  calc ∏ i ∈ s, (1 + a i)
      ≤ ∏ i ∈ s, Real.exp (a i) :=
        Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi])
          fun i _ => by linarith [Real.add_one_le_exp (a i)]
    _ = Real.exp (∑ i ∈ s, a i) := (Real.exp_sum s a).symm

/-- A product `∏' i, (1 + a i)` of non-negative real terms `a i ≥ 0` converges iff `∑' i, a i` converges. -/
theorem multipliable_one_add_iff_summable_of_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Multipliable (fun i => 1 + a i) ↔ Summable a := by
  constructor
  · intro h
    refine summable_of_sum_le ha (c := ∏' i, (1 + a i)) fun s => ?_
    have h1 : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) :=
      one_add_sum_le_prod_one_add_of_nonneg s fun i _ => ha i
    have h2 : ∏ i ∈ s, (1 + a i) ≤ ∏' i, (1 + a i) := by
      refine ge_of_tendsto h.hasProd ?_
      change ∀ᶠ t : Finset ι in atTop, ∏ i ∈ s, (1 + a i) ≤ ∏ i ∈ t, (1 + a i)
      rw [Filter.eventually_atTop]
      refine ⟨s, fun t hst => ?_⟩
      classical
      rw [← Finset.prod_sdiff hst]
      have hge1 : 1 ≤ ∏ i ∈ t \ s, (1 + a i) := by
        induction (t \ s) using Finset.induction_on with
        | empty => simp
        | insert i r hi ih =>
          rw [Finset.prod_insert hi]
          have h1i : 1 ≤ 1 + a i := by linarith [ha i]
          nlinarith
      have hnonneg : 0 ≤ ∏ i ∈ s, (1 + a i) :=
        Finset.prod_nonneg fun i _ => by linarith [ha i]
      nlinarith
    linarith
  · intro h
    exact Real.multipliable_one_add_of_summable h

/-- For non-negative summable `a : ι → ℝ`, `1 + ∑' i, a i ≤ ∏' i, (1 + a i)`. -/
theorem one_add_tsum_le_tprod_one_add_of_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) :
    1 + ∑' i, a i ≤ ∏' i, (1 + a i) := by
  have hm : Multipliable (fun i => 1 + a i) :=
    (multipliable_one_add_iff_summable_of_nonneg ha).mpr hs
  exact le_of_tendsto_of_tendsto (hs.hasSum.const_add 1) hm.hasProd
    (Eventually.of_forall fun s => one_add_sum_le_prod_one_add_of_nonneg s fun i _ => ha i)

/-- For non-negative summable `a : ι → ℝ`, `∏' i, (1 + a i) ≤ Real.exp (∑' i, a i)`. -/
theorem tprod_one_add_le_rexp_tsum_of_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) :
    ∏' i, (1 + a i) ≤ Real.exp (∑' i, a i) := by
  have hm : Multipliable (fun i => 1 + a i) :=
    (multipliable_one_add_iff_summable_of_nonneg ha).mpr hs
  exact le_of_tendsto_of_tendsto hm.hasProd (Real.continuous_exp.tendsto _ |>.comp hs.hasSum)
    (Eventually.of_forall fun s => prod_one_add_le_rexp_sum_of_nonneg s fun i _ => ha i)

end NonnegReal

section ConvergenceCriteria

variable {ι R : Type*}

/-- In a complete normed commutative ring, `∏' i, (1 + a i)` converges whenever `∑' i, ‖a i‖` converges. -/
theorem multipliable_one_add_of_summable_norm [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {a : ι → R} (ha : Summable fun i => ‖a i‖) :
    Multipliable fun i => 1 + a i :=
  _root_.multipliable_one_add_of_summable ha

/-- In a complete normed commutative ring, `∏' i, (1 - a i)` converges whenever `∑' i, ‖a i‖` converges. -/
theorem multipliable_one_sub_of_summable_norm [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {a : ι → R} (ha : Summable fun i => ‖a i‖) :
    Multipliable fun i => 1 - a i :=
  _root_.multipliable_one_sub_of_summable ha

/-- For real sequences, `∑' i, |a i| < ∞` implies `∏' i, (1 + a i)` converges. -/
theorem multipliable_one_add_of_summable_abs {a : ι → ℝ} (ha : Summable fun i => |a i|) :
    Multipliable fun i => 1 + a i :=
  multipliable_one_add_of_summable_norm (by simpa [Real.norm_eq_abs] using ha)

/-- For complex sequences, `∑' i, ‖a i‖ < ∞` implies `∏' i, (1 + a i)` converges. -/
theorem multipliable_one_add_complex_of_summable_norm {a : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) :
    Multipliable fun i => 1 + a i :=
  multipliable_one_add_of_summable_norm ha

/-- Absolute convergence test: if `∏' i, (1 + ‖a i‖)` converges, then `∑' i, ‖a i‖` converges
and hence `∏' i, (1 + a i)` converges. -/
theorem multipliable_one_add_of_multipliable_one_add_norm [NormedCommRing R] [NormOneClass R]
    [CompleteSpace R] {a : ι → R} (ha : Multipliable fun i => 1 + ‖a i‖) :
    Multipliable fun i => 1 + a i :=
  multipliable_one_add_of_summable_norm
    ((multipliable_one_add_iff_summable_of_nonneg fun i => norm_nonneg (a i)).mp ha)

/-- A product `∏' i, f i` converges in a complete normed commutative ring if `∑' i, ‖f i - 1‖` converges. -/
theorem multipliable_of_summable_norm_sub_one [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {f : ι → R} (hf : Summable fun i => ‖f i - 1‖) :
    Multipliable f := by
  simpa using multipliable_one_add_of_summable_norm hf

/-- For a `ℕ`-indexed sequence with `∑' n, ‖a n‖ < ∞`, the partial products over `Finset.range N`
converge to `∏' n, (1 + a n)`. -/
theorem tendsto_finset_range_prod_one_add_of_summable_norm [NormedCommRing R] [NormOneClass R]
    [CompleteSpace R] {a : ℕ → R} (ha : Summable fun n => ‖a n‖) :
    Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + a n)) atTop (𝓝 (∏' n, (1 + a n))) :=
  (multipliable_one_add_of_summable_norm ha).hasProd.tendsto_prod_nat

/-- Necessary condition for non-zero convergence in a normed field: if `Multipliable f` and
`∏' i, f i ≠ 0`, then `f i → 1` along `cofinite`. -/
theorem tendsto_cofinite_one_of_multipliable_ne_zero {K : Type*} [NormedField K]
    {f : ι → K} (hf : Multipliable f) (hne : ∏' i, f i ≠ 0) :
    Tendsto f cofinite (𝓝 1) := by
  classical
  set P : K := ∏' i, f i
  have hP : 0 < ‖P‖ := norm_pos_iff.mpr hne
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlt : 0 < min (‖P‖ / 2) (ε * ‖P‖ / 4) := by positivity
  have hp : Tendsto (fun s : Finset ι => ∏ i ∈ s, f i) atTop (𝓝 P) := hf.hasProd
  rw [Metric.tendsto_atTop] at hp
  obtain ⟨s₀, hs₀⟩ := hp (min (‖P‖ / 2) (ε * ‖P‖ / 4)) hlt
  have hPs₀_dist : dist (∏ i ∈ s₀, f i) P < min (‖P‖ / 2) (ε * ‖P‖ / 4) := hs₀ s₀ le_rfl
  have hPs₀_half : ‖P‖ / 2 ≤ ‖∏ i ∈ s₀, f i‖ := by
    have h1 : ‖P‖ - ‖∏ i ∈ s₀, f i‖ ≤ ‖P - ∏ i ∈ s₀, f i‖ := norm_sub_norm_le _ _
    have h2 : ‖P - ∏ i ∈ s₀, f i‖ < ‖P‖ / 2 := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact lt_of_lt_of_le hPs₀_dist (min_le_left _ _)
    linarith
  have hPs₀_pos : 0 < ‖∏ i ∈ s₀, f i‖ := lt_of_lt_of_le (by positivity) hPs₀_half
  rw [Filter.eventually_cofinite]
  refine s₀.finite_toSet.subset ?_
  intro i hi
  by_contra his₀
  have hsub : s₀ ⊆ insert i s₀ := Finset.subset_insert i s₀
  have hins := hs₀ (insert i s₀) hsub
  rw [Finset.prod_insert his₀] at hins
  have hdiff : ‖f i * (∏ j ∈ s₀, f j) - ∏ j ∈ s₀, f j‖ < ε * ‖P‖ / 2 := by
    calc ‖f i * (∏ j ∈ s₀, f j) - ∏ j ∈ s₀, f j‖
        ≤ ‖f i * (∏ j ∈ s₀, f j) - P‖ + ‖P - ∏ j ∈ s₀, f j‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = dist (f i * ∏ j ∈ s₀, f j) P + dist (∏ j ∈ s₀, f j) P := by
        rw [dist_eq_norm, dist_eq_norm, norm_sub_rev P]
      _ < ε * ‖P‖ / 4 + ε * ‖P‖ / 4 :=
        add_lt_add (lt_of_lt_of_le hins (min_le_right _ _))
          (lt_of_lt_of_le hPs₀_dist (min_le_right _ _))
      _ = ε * ‖P‖ / 2 := by ring
  have hmul : ‖f i - 1‖ * ‖∏ j ∈ s₀, f j‖ = ‖f i * (∏ j ∈ s₀, f j) - ∏ j ∈ s₀, f j‖ := by
    rw [← norm_mul, sub_mul, one_mul]
  have hlt_eps : ‖f i - 1‖ < ε := by
    rw [← mul_lt_mul_iff_left₀ hPs₀_pos, hmul]
    calc ‖f i * (∏ j ∈ s₀, f j) - ∏ j ∈ s₀, f j‖
        < ε * ‖P‖ / 2 := hdiff
      _ = ε * (‖P‖ / 2) := by ring
      _ ≤ ε * ‖∏ j ∈ s₀, f j‖ := mul_le_mul_of_nonneg_left hPs₀_half hε.le
  exact hi (by simpa [dist_eq_norm] using hlt_eps)

/-- Necessary condition for non-zero convergence of `ℕ`-indexed products in a normed field. -/
theorem tendsto_atTop_one_of_multipliable_ne_zero {K : Type*} [NormedField K]
    {f : ℕ → K} (hf : Multipliable f) (hne : ∏' n, f n ≠ 0) :
    Tendsto f atTop (𝓝 1) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_one_of_multipliable_ne_zero hf hne

/-- In a complete normed field, if `f i ≠ 0` for all `i` and `∑' i, ‖f i - 1‖ < ∞`, then
`∑' i, ‖(f i)⁻¹ - 1‖ < ∞`. -/
theorem summable_norm_inv_sub_one_of_summable_norm {K : Type*} [NormedField K] [CompleteSpace K]
    {f : ι → K} (hf0 : ∀ i, f i ≠ 0) (hf : Summable fun i => ‖f i - 1‖) :
    Summable fun i => ‖(f i)⁻¹ - 1‖ := by
  have hlim : Tendsto (fun i => ‖f i - 1‖) cofinite (𝓝 0) := hf.tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, ‖(f i)⁻¹ - 1‖ ≤ 2 * ‖f i - 1‖ := by
    filter_upwards [hlim.eventually_le_const one_half_pos] with i hi
    have hnorm : 1 / 2 ≤ ‖f i‖ := by
      have := norm_sub_norm_le (1 : K) (f i)
      rw [norm_one, norm_sub_rev] at this
      linarith
    have hpos : 0 < ‖f i‖ := by linarith
    have hid : (f i)⁻¹ - 1 = (1 - f i) / f i := by field_simp [hf0 i]
    rw [hid, norm_div, norm_sub_rev, div_le_iff₀ hpos]
    calc ‖f i - 1‖ = 2 * ‖f i - 1‖ * (1 / 2) := by ring
      _ ≤ 2 * ‖f i - 1‖ * ‖f i‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
  refine (hf.mul_left 2).of_norm_bounded_eventually ?_
  filter_upwards [hev] with i hi
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hi

/-- For positive real terms `f i > 0`, `Multipliable f ∧ ∏' i, f i ≠ 0` holds iff
`Summable (fun i => Real.log (f i))`. -/
theorem multipliable_and_tprod_ne_zero_iff_summable_log_of_pos {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) :
    (Multipliable f ∧ ∏' i, f i ≠ 0) ↔ Summable fun i => Real.log (f i) := by
  constructor
  · rintro ⟨hm, hne⟩
    have hcont : ContinuousAt Real.log (∏' i, f i) := Real.continuousAt_log hne
    have hlog :
        Tendsto (fun s : Finset ι => Real.log (∏ i ∈ s, f i)) atTop
          (𝓝 (Real.log (∏' i, f i))) :=
      hcont.tendsto.comp hm.hasProd
    have hsum : HasSum (fun i => Real.log (f i)) (Real.log (∏' i, f i)) := by
      refine hlog.congr fun s => ?_
      exact Real.log_prod fun i _ => (hf i).ne'
    exact hsum.summable
  · intro hlog
    refine ⟨Real.multipliable_of_summable_log hf hlog, ?_⟩
    rw [← Real.rexp_tsum_eq_tprod hf hlog]
    exact Real.exp_ne_zero _

/-- If `∑' i, ‖a i‖ < ∞` in `ℂ`, then `Complex.exp (∑' i, Complex.log (1 + a i)) = ∏' i, (1 + a i)`
whenever `1 + a i ≠ 0` for all `i`. -/
theorem cexp_tsum_log_one_add_eq_tprod {a : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (hne : ∀ i, 1 + a i ≠ 0) :
    Complex.exp (∑' i, Complex.log (1 + a i)) = ∏' i, (1 + a i) := by
  have hlog : Summable fun i => Complex.log (1 + a i) := by
    apply (ha.mul_left (3 / 2)).of_norm_bounded_eventually
    filter_upwards [ha.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    exact Complex.norm_log_one_add_half_le_self hi
  exact Complex.cexp_tsum_eq_tprod hne hlog

end ConvergenceCriteria

section ZeroCriterion

variable {ι R : Type*}

/-- Under absolute convergence `Summable (fun i => ‖f i - 1‖)` in a complete normed field (or ring
with multiplicative norm), an infinite product vanishes if and only if at least one factor vanishes. -/
theorem tprod_eq_zero_iff_exists_eq_zero [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    [NormMulClass R] {f : ι → R} (hf : Summable fun i => ‖f i - 1‖) :
    ∏' i, f i = 0 ↔ ∃ i, f i = 0 := by
  constructor
  · intro hzero
    by_contra hne
    push Not at hne
    have hf1 : ∀ i, 1 + (f i - 1) ≠ 0 := fun i => by simpa using hne i
    have hprod := _root_.tprod_one_add_ne_zero_of_summable hf1 hf
    simp only [add_sub_cancel] at hprod
    exact hprod hzero
  · rintro ⟨i, hi⟩
    exact (hasProd_zero_of_exists_eq_zero ⟨i, hi⟩).tprod_eq

/-- Under `Summable (fun i => ‖a i‖)`, `∏' i, (1 + a i) = 0 ↔ ∃ i, 1 + a i = 0`. -/
theorem tprod_one_add_eq_zero_iff [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    [NormMulClass R] {a : ι → R} (ha : Summable fun i => ‖a i‖) :
    ∏' i, (1 + a i) = 0 ↔ ∃ i, 1 + a i = 0 := by
  refine tprod_eq_zero_iff_exists_eq_zero (f := fun i => 1 + a i) ?_
  simpa using ha

/-- Non-vanishing of `∏' i, (1 + a i)` under `Summable (fun i => ‖a i‖)` when every factor is non-zero. -/
theorem tprod_one_add_ne_zero [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    [NormMulClass R] {a : ι → R} (ha : Summable fun i => ‖a i‖) (hne : ∀ i, 1 + a i ≠ 0) :
    ∏' i, (1 + a i) ≠ 0 :=
  _root_.tprod_one_add_ne_zero_of_summable hne ha

/-- Non-vanishing of `∏' i, f i` under `Summable (fun i => ‖f i - 1‖)` when every factor is non-zero. -/
theorem tprod_ne_zero_of_summable_norm_sub_one [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    [NormMulClass R] {f : ι → R} (hf : Summable fun i => ‖f i - 1‖) (hne : ∀ i, f i ≠ 0) :
    ∏' i, f i ≠ 0 := by
  rw [ne_eq, tprod_eq_zero_iff_exists_eq_zero hf]
  exact not_exists.mpr hne

end ZeroCriterion

section ExponentialOfSum

variable {ι : Type*}

/-- If `g : ι → ℝ` has sum `L`, then `fun i => Real.exp (g i)` has product `Real.exp L`. -/
theorem hasProd_rexp_of_hasSum {g : ι → ℝ} {L : ℝ} (hg : HasSum g L) :
    HasProd (fun i => Real.exp (g i)) (Real.exp L) :=
  hg.rexp

/-- If `g : ι → ℝ` is summable, then `fun i => Real.exp (g i)` is multipliable. -/
theorem multipliable_rexp_of_summable {g : ι → ℝ} (hg : Summable g) :
    Multipliable fun i => Real.exp (g i) :=
  ⟨Real.exp (∑' i, g i), hasProd_rexp_of_hasSum hg.hasSum⟩

/-- For any summable `g : ι → ℝ`, `Real.exp (∑' i, g i) = ∏' i, Real.exp (g i)`. -/
theorem rexp_tsum_eq_tprod {g : ι → ℝ} (hg : Summable g) :
    Real.exp (∑' i, g i) = ∏' i, Real.exp (g i) :=
  (hasProd_rexp_of_hasSum hg.hasSum).tprod_eq.symm

/-- If `g : ι → ℂ` has sum `L`, then `fun i => Complex.exp (g i)` has product `Complex.exp L`. -/
theorem hasProd_cexp_of_hasSum {g : ι → ℂ} {L : ℂ} (hg : HasSum g L) :
    HasProd (fun i => Complex.exp (g i)) (Complex.exp L) :=
  hg.cexp

/-- If `g : ι → ℂ` is summable, then `fun i => Complex.exp (g i)` is multipliable. -/
theorem multipliable_cexp_of_summable {g : ι → ℂ} (hg : Summable g) :
    Multipliable fun i => Complex.exp (g i) :=
  ⟨Complex.exp (∑' i, g i), hasProd_cexp_of_hasSum hg.hasSum⟩

/-- For any summable `g : ι → ℂ`, `Complex.exp (∑' i, g i) = ∏' i, Complex.exp (g i)`. -/
theorem cexp_tsum_eq_tprod {g : ι → ℂ} (hg : Summable g) :
    Complex.exp (∑' i, g i) = ∏' i, Complex.exp (g i) :=
  (hasProd_cexp_of_hasSum hg.hasSum).tprod_eq.symm

end ExponentialOfSum

section UniformAndAnalytic

variable {ι α R : Type*}

/-- Weierstrass M-test for uniform convergence of infinite products on an arbitrary set `S`:
if `‖a i x‖ ≤ u i` for all `i` and all `x ∈ S` with `Summable u`, then `∏' i, (1 + a i x)`
converges uniformly on `S`. -/
theorem hasProdUniformlyOn_one_add_of_le [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {a : ι → α → R} {S : Set α} {u : ι → ℝ} (hu : Summable u)
    (hbound : ∀ i, ∀ x ∈ S, ‖a i x‖ ≤ u i) :
    HasProdUniformlyOn (fun i x => 1 + a i x) (fun x => ∏' i, (1 + a i x)) S := by
  classical
  by_cases hSe : S = ∅
  · subst hSe
    rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simp [TendstoUniformlyOn]
  have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSe
  obtain ⟨x₀, hx₀⟩ := hSne
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i => (norm_nonneg _).trans (hbound i x₀ hx₀)
  have hmulti : ∀ x ∈ S, Multipliable fun i => 1 + a i x := fun x hx =>
    multipliable_one_add_of_summable_norm
      (hu.of_norm_bounded_eventually (Eventually.of_forall fun i => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound i x hx))
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set M : ℝ := Real.exp (∑' i, u i)
  have hM : 0 < M := Real.exp_pos _
  have hlt : (0 : ℝ) < ε / (2 * M) := by positivity
  have hnhds : {r : ℝ | Real.exp r - 1 < ε / (2 * M)} ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt (fun r : ℝ => Real.exp r - 1) 0 := by fun_prop
    refine hcont.preimage_mem_nhds (Iio_mem_nhds ?_)
    change Real.exp 0 - 1 < ε / (2 * M)
    rwa [Real.exp_zero, sub_self]
  obtain ⟨s₀, hs₀⟩ := hu.vanishing hnhds
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs x hx => ?_⟩
  have hpart_bd : ‖∏ i ∈ s, (1 + a i x)‖ ≤ M := by
    calc ‖∏ i ∈ s, (1 + a i x)‖
        ≤ ∏ i ∈ s, ‖1 + a i x‖ := Finset.norm_prod_le s _
      _ ≤ ∏ i ∈ s, (1 + ‖a i x‖) := by
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
        simpa [norm_one] using norm_add_le (1 : R) (a i x)
      _ ≤ ∏ i ∈ s, (1 + u i) := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_
        linarith [hbound i x hx]
      _ ≤ Real.exp (∑ i ∈ s, u i) := prod_one_add_le_rexp_sum_of_nonneg s fun i _ => hu_nonneg i
      _ ≤ Real.exp (∑' i, u i) :=
        Real.exp_le_exp.mpr (hu.sum_le_tsum s fun i _ => hu_nonneg i)
  have htail : ∀ t, s ⊆ t → ‖∏ i ∈ t, (1 + a i x) - ∏ i ∈ s, (1 + a i x)‖ ≤ ε / 2 := by
    intro t hst
    have hdisj : Disjoint (t \ s) s₀ := Disjoint.mono_right hs Finset.sdiff_disjoint
    have hexp : Real.exp (∑ i ∈ t \ s, u i) - 1 < ε / (2 * M) := hs₀ (t \ s) hdisj
    have hdiff : ∏ i ∈ t, (1 + a i x) - ∏ i ∈ s, (1 + a i x) =
        (∏ i ∈ s, (1 + a i x)) * (∏ i ∈ t \ s, (1 + a i x) - 1) := by
      rw [← Finset.prod_sdiff hst, mul_sub_one, mul_comm (∏ i ∈ t \ s, (1 + a i x))]
    rw [hdiff]
    calc ‖(∏ i ∈ s, (1 + a i x)) * (∏ i ∈ t \ s, (1 + a i x) - 1)‖
        ≤ ‖∏ i ∈ s, (1 + a i x)‖ * ‖∏ i ∈ t \ s, (1 + a i x) - 1‖ := norm_mul_le _ _
      _ ≤ M * (Real.exp (∑ i ∈ t \ s, ‖a i x‖) - 1) := by
        refine mul_le_mul hpart_bd (Finset.norm_prod_one_add_sub_one_le _ _) (norm_nonneg _) hM.le
      _ ≤ M * (Real.exp (∑ i ∈ t \ s, u i) - 1) := by
        gcongr with i
        exact hbound i x hx
      _ ≤ M * (ε / (2 * M)) := mul_le_mul_of_nonneg_left hexp.le hM.le
      _ = ε / 2 := by field_simp [hM.ne']
  have hlim : ‖(∏' i, (1 + a i x)) - ∏ i ∈ s, (1 + a i x)‖ ≤ ε / 2 := by
    refine le_of_tendsto ((hmulti x hx).hasProd.sub tendsto_const_nhds).norm ?_
    change ∀ᶠ t : Finset ι in atTop, ‖∏ i ∈ t, (1 + a i x) - ∏ i ∈ s, (1 + a i x)‖ ≤ ε / 2
    rw [Filter.eventually_atTop]
    exact ⟨s, htail⟩
  rw [dist_eq_norm]
  linarith

/-- Weierstrass M-test for `MultipliableUniformlyOn` on an arbitrary set `S`. -/
theorem multipliableUniformlyOn_one_add_of_le [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {a : ι → α → R} {S : Set α} {u : ι → ℝ} (hu : Summable u)
    (hbound : ∀ i, ∀ x ∈ S, ‖a i x‖ ≤ u i) :
    MultipliableUniformlyOn (fun i x => 1 + a i x) S :=
  (hasProdUniformlyOn_one_add_of_le hu hbound).multipliableUniformlyOn

/-- Uniform convergence of `∏' i, (1 + a i x)` on a compact set `K` when norms are eventually
bounded by a summable sequence. -/
theorem hasProdUniformlyOn_one_add_of_compact [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    [TopologicalSpace α] {a : ι → α → R} {K : Set α} {u : ι → ℝ}
    (hK : IsCompact K) (hu : Summable u)
    (hbound : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖a i x‖ ≤ u i)
    (hcts : ∀ i, ContinuousOn (a i) K) :
    HasProdUniformlyOn (fun i x => 1 + a i x) (fun x => ∏' i, (1 + a i x)) K :=
  hu.hasProdUniformlyOn_one_add hK hbound hcts

/-- Locally uniform convergence of `∏' i, (1 + a i x)` on an open set `U` in a locally compact space
under a local Weierstrass M-test bound on compact subsets. -/
theorem hasProdLocallyUniformlyOn_one_add_of_compact_bound [NormedCommRing R] [NormOneClass R]
    [CompleteSpace R] [TopologicalSpace α] [LocallyCompactSpace α]
    {a : ι → α → R} {U : Set α} (hU : IsOpen U) (hcts : ∀ i, ContinuousOn (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖a i x‖ ≤ u i) :
    HasProdLocallyUniformlyOn (fun i x => 1 + a i x) (fun x => ∏' i, (1 + a i x)) U := by
  refine hasProdLocallyUniformlyOn_of_forall_compact hU fun K hKU hK => ?_
  obtain ⟨u, hu, hbu⟩ := hbound K hKU hK
  exact hu.hasProdUniformlyOn_one_add hK hbu fun i => (hcts i).mono hKU

/-- Locally uniform multipliability of `∏' i, (1 + a i x)` on an open set `U` under a local
Weierstrass M-test bound on compact subsets. -/
theorem multipliableLocallyUniformlyOn_one_add_of_compact_bound [NormedCommRing R] [NormOneClass R]
    [CompleteSpace R] [TopologicalSpace α] [LocallyCompactSpace α]
    {a : ι → α → R} {U : Set α} (hU : IsOpen U) (hcts : ∀ i, ContinuousOn (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖a i x‖ ≤ u i) :
    MultipliableLocallyUniformlyOn (fun i x => 1 + a i x) U :=
  (hasProdLocallyUniformlyOn_one_add_of_compact_bound hU hcts hbound).multipliableLocallyUniformlyOn

/-- Locally uniform convergence of `ℕ`-indexed infinite products `∏' n, (1 + a n x)` on an open
set `U` under a local Weierstrass M-test bound on compact subsets. -/
theorem multipliableLocallyUniformlyOn_nat_one_add_of_compact_bound [NormedCommRing R]
    [NormOneClass R] [CompleteSpace R] [TopologicalSpace α] [LocallyCompactSpace α]
    {a : ℕ → α → R} {U : Set α} (hU : IsOpen U) (hcts : ∀ n, ContinuousOn (a n) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ x ∈ K, ‖a n x‖ ≤ u n) :
    MultipliableLocallyUniformlyOn (fun n x => 1 + a n x) U := by
  refine multipliableLocallyUniformlyOn_one_add_of_compact_bound hU hcts fun K hKU hK => ?_
  obtain ⟨u, hu, hbu⟩ := hbound K hKU hK
  exact ⟨u, hu, Nat.cofinite_eq_atTop ▸ hbu⟩

/-- A locally uniformly convergent infinite product of holomorphic functions on an open set `U ⊆ ℂ`
is holomorphic (`DifferentiableOn ℂ · U`). -/
theorem differentiableOn_tprod {f : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) (hm : MultipliableLocallyUniformlyOn f U) :
    DifferentiableOn ℂ (fun z => ∏' i, f i z) U := by
  classical
  have htend : TendstoLocallyUniformlyOn (fun s z => ∏ i ∈ s, f i z)
      (fun z => ∏' i, f i z) atTop U :=
    hm.hasProdLocallyUniformlyOn
  refine htend.differentiableOn (Eventually.of_forall fun s => ?_) hU
  induction s using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hd i).fun_mul ih

/-- A locally uniformly convergent infinite product of holomorphic functions on an open set `U ⊆ ℂ`
is analytic (`AnalyticOnNhd ℂ · U`). -/
theorem analyticOnNhd_tprod {f : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) (hm : MultipliableLocallyUniformlyOn f U) :
    AnalyticOnNhd ℂ (fun z => ∏' i, f i z) U :=
  (differentiableOn_tprod hU hd hm).analyticOnNhd hU

/-- Holomorphicity of `∏' i, (1 + a i z)` on an open set `U ⊆ ℂ` under a compact Weierstrass M-test bound. -/
theorem differentiableOn_tprod_one_add {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∏' i, (1 + a i z)) U := by
  refine differentiableOn_tprod hU (fun i => (differentiableOn_const 1).add (hd i)) ?_
  exact multipliableLocallyUniformlyOn_one_add_of_compact_bound hU
    (fun i => (hd i).continuousOn) hbound

/-- Analyticity (`AnalyticOnNhd`) of `∏' i, (1 + a i z)` on an open set `U ⊆ ℂ` under a compact
Weierstrass M-test bound. -/
theorem analyticOnNhd_tprod_one_add {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i) :
    AnalyticOnNhd ℂ (fun z => ∏' i, (1 + a i z)) U :=
  (differentiableOn_tprod_one_add hU hd hbound).analyticOnNhd hU

/-- Holomorphicity of a `ℕ`-indexed infinite product `∏' n, (1 + a n z)` on an open set `U ⊆ ℂ`
under a compact Weierstrass M-test bound. -/
theorem differentiableOn_tprod_nat_one_add {a : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ n, DifferentiableOn ℂ (a n) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖a n z‖ ≤ u n) :
    DifferentiableOn ℂ (fun z => ∏' n, (1 + a n z)) U :=
  differentiableOn_tprod_one_add hU hd fun K hKU hK => by
    obtain ⟨u, hu, hbu⟩ := hbound K hKU hK
    exact ⟨u, hu, Nat.cofinite_eq_atTop ▸ hbu⟩

/-- Entirety of `∏' n, (1 + a n z)` on `ℂ` when `a n` are entire and uniformly bounded on every
compact subset of `ℂ` by a summable sequence. -/
theorem differentiable_tprod_nat_one_add {a : ℕ → ℂ → ℂ}
    (hd : ∀ n, Differentiable ℂ (a n))
    (hbound : ∀ K : Set ℂ, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖a n z‖ ≤ u n) :
    Differentiable ℂ (fun z => ∏' n, (1 + a n z)) := by
  rw [← differentiableOn_univ]
  exact differentiableOn_tprod_nat_one_add isOpen_univ (fun n => (hd n).differentiableOn)
    fun K _ hK => hbound K hK

/-- Non-vanishing of `∏' i, (1 + a i z)` on `U` when each factor `1 + a i z` is non-zero and
`∑' i, ‖a i z‖` converges at every `z ∈ U`. -/
theorem tprod_one_add_ne_zero_on {a : ι → ℂ → ℂ} {U : Set ℂ}
    (hsum : ∀ z ∈ U, Summable fun i => ‖a i z‖)
    (hne : ∀ i, ∀ z ∈ U, 1 + a i z ≠ 0) :
    ∀ z ∈ U, ∏' i, (1 + a i z) ≠ 0 :=
  fun z hz => tprod_one_add_ne_zero (hsum z hz) fun i => hne i z hz

end UniformAndAnalytic

section LogDeriv

variable {ι : Type*}

/-- Logarithmic derivative of a locally uniformly convergent infinite product of holomorphic
functions equals the sum of the logarithmic derivatives. -/
theorem logDeriv_tprod_eq_tsum {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hm : Summable fun i => logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f U)
    (hnez : ∏' i, f i x ≠ 0) :
    logDeriv (fun z => ∏' i, f i z) x = ∑' i, logDeriv (f i) x :=
  _root_.logDeriv_tprod_eq_tsum hU hx hf hd hm htend hnez

/-- Explicit quotient form of `logDeriv_tprod_eq_tsum`:
`deriv (fun z => ∏' i, f i z) x / ∏' i, f i x = ∑' i, deriv (f i) x / f i x`. -/
theorem deriv_tprod_div_tprod_eq_tsum {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hm : Summable fun i => deriv (f i) x / f i x) (htend : MultipliableLocallyUniformlyOn f U)
    (hnez : ∏' i, f i x ≠ 0) :
    deriv (fun z => ∏' i, f i z) x / ∏' i, f i x = ∑' i, deriv (f i) x / f i x := by
  simpa [logDeriv_apply] using logDeriv_tprod_eq_tsum hU hx hf hd hm htend hnez

/-- `HasDerivAt` version for a locally uniformly convergent infinite product of holomorphic functions. -/
theorem hasDerivAt_tprod {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hm : Summable fun i => deriv (f i) x / f i x) (htend : MultipliableLocallyUniformlyOn f U)
    (hnez : ∏' i, f i x ≠ 0) :
    HasDerivAt (fun z => ∏' i, f i z) ((∏' i, f i x) * ∑' i, deriv (f i) x / f i x) x := by
  have hdiff : DifferentiableAt ℂ (fun z => ∏' i, f i z) x :=
    (differentiableOn_tprod hU hd htend).differentiableAt (hU.mem_nhds hx)
  refine hdiff.hasDerivAt.congr_deriv ?_
  have hld := deriv_tprod_div_tprod_eq_tsum hU hx hf hd hm htend hnez
  rw [← hld]
  field_simp [hnez]

/-- Cauchy estimate for derivatives: under a compact Weierstrass M-test bound on an open set `U ⊆ ℂ`,
`∑' i, ‖deriv (a i) x‖` is summable at every `x ∈ U`. -/
theorem summable_norm_deriv_of_compact_bound {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i)
    {x : ℂ} (hx : x ∈ U) :
    Summable fun i => ‖deriv (a i) x‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  set δ : ℝ := r / 2
  have hδ : 0 < δ := by positivity
  have hδr : δ < r := half_lt_self hr
  have hcball : Metric.closedBall x δ ⊆ U :=
    (Metric.closedBall_subset_ball hδr).trans hball
  obtain ⟨u, hu, hbu⟩ := hbound (Metric.closedBall x δ) hcball (isCompact_closedBall x δ)
  refine (hu.mul_left (1 / δ)).of_norm_bounded_eventually ?_
  filter_upwards [hbu] with i hi
  have hceq := Complex.cderiv_eq_deriv hU (hd i) hδ hcball
  have hcle := Complex.norm_cderiv_le (z := x) (f := a i) (M := u i) hδ
    fun w hw => hi w (Metric.sphere_subset_closedBall hw)
  rw [hceq, div_eq_mul_inv, mul_comm, ← one_div] at hcle
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hcle

/-- Under a compact Weierstrass M-test bound on an open set `U ⊆ ℂ`, the logarithmic derivatives
`fun i => logDeriv (fun z => 1 + a i z) x` are absolutely summable at every `x ∈ U`. -/
theorem summable_logDeriv_one_add_of_compact_bound {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i)
    {x : ℂ} (hx : x ∈ U) :
    Summable fun i => logDeriv (fun z => 1 + a i z) x := by
  have hderiv : Summable fun i => ‖deriv (a i) x‖ :=
    summable_norm_deriv_of_compact_bound hU hd hbound hx
  obtain ⟨u, hu, hbu⟩ := hbound {x} (Set.singleton_subset_iff.mpr hx) isCompact_singleton
  have ha_zero : Tendsto (fun i => ‖a i x‖) cofinite (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu.tendsto_cofinite_zero
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [hbu] with i hi using hi x rfl
  refine (hderiv.mul_left 2).of_norm_bounded_eventually ?_
  filter_upwards [ha_zero.eventually_le_const one_half_pos] with i hi
  have hnorm : 1 / 2 ≤ ‖1 + a i x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-a i x)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖1 + a i x‖ := by linarith
  have hda : deriv (fun z => 1 + a i z) x = deriv (a i) x := by
    have hdiff : DifferentiableAt ℂ (a i) x := (hd i).differentiableAt (hU.mem_nhds hx)
    have h := ((hasDerivAt_const x (1 : ℂ)).add hdiff.hasDerivAt).deriv
    simp at h
    exact h
  rw [logDeriv_apply, hda, norm_div, div_le_iff₀ hpos]
  calc ‖deriv (a i) x‖ = 2 * ‖deriv (a i) x‖ * (1 / 2) := by ring
    _ ≤ 2 * ‖deriv (a i) x‖ * ‖1 + a i x‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)

/-- Logarithmic derivative of `∏' i, (1 + a i z)` under a compact Weierstrass M-test bound on `U ⊆ ℂ`:
if `∀ i, 1 + a i x ≠ 0`, then `logDeriv (fun z => ∏' i, (1 + a i z)) x = ∑' i, logDeriv (fun z => 1 + a i z) x`. -/
theorem logDeriv_tprod_one_add_eq_tsum {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i)
    {x : ℂ} (hx : x ∈ U) (hne : ∀ i, 1 + a i x ≠ 0) :
    logDeriv (fun z => ∏' i, (1 + a i z)) x = ∑' i, logDeriv (fun z => 1 + a i z) x := by
  have hm : MultipliableLocallyUniformlyOn (fun i z => 1 + a i z) U :=
    multipliableLocallyUniformlyOn_one_add_of_compact_bound hU (fun i => (hd i).continuousOn) hbound
  have hsum_ax : Summable fun i => ‖a i x‖ := by
    obtain ⟨u, hu, hbu⟩ := hbound {x} (Set.singleton_subset_iff.mpr hx) isCompact_singleton
    exact hu.of_norm_bounded_eventually (hbu.mono fun i hi => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hi x rfl)
  have hnez : ∏' i, (1 + a i x) ≠ 0 := tprod_one_add_ne_zero hsum_ax hne
  have hsum_ld : Summable fun i => logDeriv (fun z => 1 + a i z) x :=
    summable_logDeriv_one_add_of_compact_bound hU hd hbound hx
  exact logDeriv_tprod_eq_tsum hU hx hne (fun i => (differentiableOn_const 1).add (hd i))
    hsum_ld hm hnez

/-- Explicit derivative quotient formula for `∏' i, (1 + a i z)` under a compact Weierstrass M-test bound:
`deriv (fun z => ∏' i, (1 + a i z)) x / (∏' i, (1 + a i x)) = ∑' i, deriv (a i) x / (1 + a i x)`. -/
theorem deriv_tprod_one_add_div_eq_tsum {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i)
    {x : ℂ} (hx : x ∈ U) (hne : ∀ i, 1 + a i x ≠ 0) :
    deriv (fun z => ∏' i, (1 + a i z)) x / (∏' i, (1 + a i x)) =
      ∑' i, deriv (a i) x / (1 + a i x) := by
  have hld := logDeriv_tprod_one_add_eq_tsum hU hd hbound hx hne
  rw [logDeriv_apply] at hld
  refine hld.trans (tsum_congr fun i => ?_)
  have hdiff : DifferentiableAt ℂ (a i) x := (hd i).differentiableAt (hU.mem_nhds hx)
  have hda : deriv (fun z => 1 + a i z) x = deriv (a i) x := by
    have h := ((hasDerivAt_const x (1 : ℂ)).add hdiff.hasDerivAt).deriv
    simp at h
    exact h
  rw [logDeriv_apply, hda]

/-- `HasDerivAt` for `∏' i, (1 + a i z)` under a compact Weierstrass M-test bound. -/
theorem hasDerivAt_tprod_one_add {a : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (a i) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖a i z‖ ≤ u i)
    {x : ℂ} (hx : x ∈ U) (hne : ∀ i, 1 + a i x ≠ 0) :
    HasDerivAt (fun z => ∏' i, (1 + a i z))
      ((∏' i, (1 + a i x)) * ∑' i, deriv (a i) x / (1 + a i x)) x := by
  have hdiff : DifferentiableAt ℂ (fun z => ∏' i, (1 + a i z)) x :=
    (differentiableOn_tprod_one_add hU hd hbound).differentiableAt (hU.mem_nhds hx)
  have hsum_ax : Summable fun i => ‖a i x‖ := by
    obtain ⟨u, hu, hbu⟩ := hbound {x} (Set.singleton_subset_iff.mpr hx) isCompact_singleton
    exact hu.of_norm_bounded_eventually (hbu.mono fun i hi => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hi x rfl)
  have hnez : ∏' i, (1 + a i x) ≠ 0 := tprod_one_add_ne_zero hsum_ax hne
  refine hdiff.hasDerivAt.congr_deriv ?_
  have hq := deriv_tprod_one_add_div_eq_tsum hU hd hbound hx hne
  rw [← hq]
  field_simp [hnez]

/-- `ℕ`-indexed version of `deriv_tprod_one_add_div_eq_tsum`. -/
theorem deriv_tprod_nat_one_add_div_eq_tsum {a : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ n, DifferentiableOn ℂ (a n) U)
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖a n z‖ ≤ u n)
    {x : ℂ} (hx : x ∈ U) (hne : ∀ n, 1 + a n x ≠ 0) :
    deriv (fun z => ∏' n, (1 + a n z)) x / (∏' n, (1 + a n x)) =
      ∑' n, deriv (a n) x / (1 + a n x) :=
  deriv_tprod_one_add_div_eq_tsum hU hd
    (fun K hKU hK => by
      obtain ⟨u, hu, hbu⟩ := hbound K hKU hK
      exact ⟨u, hu, Nat.cofinite_eq_atTop ▸ hbu⟩)
    hx hne

end LogDeriv

end AnalyticNumberTheory.AnalyticTools.Gamma
