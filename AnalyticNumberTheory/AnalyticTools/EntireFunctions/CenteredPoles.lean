module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Partial fractions centered at zero

Subtracting a pole's value at zero makes its contribution summable over a discrete family
whose inverse squared radii are summable. The resulting partial-fraction sum vanishes at zero.
-/

public section

open Filter Finset
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.EntireFunctions

/-- The simple pole of residue one at `ω`, with its value at zero subtracted. -/
noncomputable def centeredPole (ω z : ℂ) : ℂ := z / (ω * (z-ω))

/-- Away from the pole, the centered term is `1/(z-ω)+1/ω`. -/
theorem centeredPole_eq {ω z : ℂ} (hω : ω ≠ 0) (hz : z ≠ ω) :
    centeredPole ω z = 1 / (z - ω) + 1 / ω := by
  unfold centeredPole
  field_simp [hω, sub_ne_zero.mpr hz]
  ring

/-- A pole outside the disk of radius `2‖z‖` contributes at most `2‖z‖/‖ω‖²`. -/
theorem norm_centeredPole_le {ω z : ℂ} (hω : ω ≠ 0) (h : 2 * ‖z‖ ≤ ‖ω‖) :
    ‖centeredPole ω z‖ ≤ (2 * ‖z‖) * (‖ω‖^2)⁻¹ := by
  have hn := norm_pos_iff.mpr hω
  have ht := norm_sub_norm_le ω z
  rw [norm_sub_rev] at ht
  have hdist : ‖ω‖ / 2 ≤ ‖z-ω‖ := by linarith
  have hden : ‖ω‖^2/2 ≤ ‖ω‖ * ‖z-ω‖ := by nlinarith [mul_le_mul_of_nonneg_left hdist hn.le]
  rw [centeredPole, norm_div, norm_mul]
  exact (div_le_div_of_nonneg_left (norm_nonneg z) (by positivity : 0 < ‖ω‖^2/2) hden).trans_eq
    (by ring)

/-- A locally finite family of poles with summable inverse squared norms has a summable
centered partial-fraction series at any fixed argument. -/
theorem summable_centeredPole {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfin : ∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) (z : ℂ) : Summable fun n => centeredPole (a n) z := by
  apply (hS.mul_left (2*‖z‖)).of_norm_bounded_eventually
  have he : ∀ᶠ n in cofinite, n ∉ {n | ‖a n‖ ≤ 2*‖z‖} := by
    simpa [Filter.eventually_cofinite] using hfin (2*‖z‖)
  filter_upwards [he] with n hn
  exact norm_centeredPole_le (ha n) (not_le.mp hn).le

/-- A single centered pole vanishes continuously at the origin. -/
theorem tendsto_centeredPole_zero {ω : ℂ} (hω : ω ≠ 0) :
    Tendsto (centeredPole ω) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (centeredPole ω) 0 :=
    continuousAt_id.div (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
      (by simpa using mul_ne_zero hω (neg_ne_zero.mpr hω))
  simpa [centeredPole] using hc.tendsto

/-- The centered sum tends to zero at the origin. Discreteness supplies a common neighborhood
free of poles, and inverse squares dominate every term there. -/
theorem tendsto_tsum_centeredPole_zero {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfin : ∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) :
    Tendsto (fun z : ℂ => ∑' n, centeredPole (a n) z) (𝓝 0) (𝓝 0) := by
  classical
  let F := insert 0 (hfin 1).toFinset
  obtain ⟨k, _, hk⟩ := F.exists_min_image (fun n => ‖a n‖) (insert_nonempty ..)
  let δ := min 1 ‖a k‖
  have hδ : 0 < δ := lt_min zero_lt_one (norm_pos_iff.mpr (ha k))
  have hgap (n : ℕ) : δ ≤ ‖a n‖ := by
    by_cases hn : ‖a n‖ ≤ 1
    · exact (min_le_right ..).trans (hk n (mem_insert_of_mem ((hfin 1).mem_toFinset.mpr hn)))
    · exact (min_le_left ..).trans (le_of_not_ge hn)
  have hterm (n : ℕ) : Tendsto (centeredPole (a n)) (𝓝 0) (𝓝 0) := tendsto_centeredPole_zero (ha n)
  have hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ n,
      ‖centeredPole (a n) z‖ ≤ 2 * (‖a n‖^2)⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min zero_lt_one (half_pos hδ))] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    intro n
    have hl := lt_min_iff.mp hz
    exact (norm_centeredPole_le (ha n) (by linarith [hgap n, hl.2])).trans
      (mul_le_mul_of_nonneg_right (by linarith [hl.1]) (by positivity))
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence (f := fun z n => centeredPole (a n) z)
      (g := fun _ => (0 : ℂ)) (hS.mul_left 2) hterm hbound)

end AnalyticNumberTheory.AnalyticTools.EntireFunctions
