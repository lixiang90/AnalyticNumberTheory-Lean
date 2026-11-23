import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Shifted Borel–Carathéodory Theorem, Derivative Bounds, and Landau's Lemma

This file establishes shifted versions of the Borel–Carathéodory theorem on `Metric.ball z₀ R`,
derivative estimates for `deriv` and `iteratedDeriv`, and Landau's logarithmic-derivative lemma
(both in zero-free disks and with explicit sums over zeros in half-radius disks).

## Main Theorems

* `borel_caratheodory_sub` / `borel_caratheodory` : shifted Borel–Carathéodory bounds on
  `Metric.ball z₀ R` without requiring positivity of `M`.
* `norm_deriv_center_le_of_re_le` / `norm_deriv_le_of_re_le` : first-derivative bounds from
  an upper bound on `Re f`.
* `norm_iteratedDeriv_le_of_re_le` : `k`-th derivative bound
  `‖iteratedDeriv k f z‖ ≤ 2^(k+2) * k! * R / (R - r)^(k+1) * (M - (f z₀).re)` for `k ≥ 1`.
* `landau_logDeriv_center_le` / `landau_logDeriv_le` : Landau's logarithmic-derivative lemma
  bounding `‖logDeriv f z - ∑ᶠ ρ, divisor f ... ρ / (z - ρ)‖`.
* `landau_neg_re_logDeriv_center_le` / `landau_neg_re_logDeriv_center_le_sub_zero` :
  real-part estimates for `- (deriv f / f).re` used in zero-free region proofs.
-/

open Complex Filter MeromorphicOn Metric Real Set
open scoped Topology Nat

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-!
### Shifted Borel–Carathéodory Theorem
-/

/-- Shifted **Borel–Carathéodory theorem** (difference form): if `f` is complex differentiable on
`Metric.ball z₀ R` (`0 < R`) and `(f w).re ≤ M` for all `w ∈ Metric.ball z₀ R`, then for every
`z ∈ Metric.ball z₀ R`,
`‖f z - f z₀‖ ≤ 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re)`. -/
theorem borel_caratheodory_sub {f : ℂ → ℂ} {z₀ z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.ball z₀ R) :
    ‖f z - f z₀‖ ≤ 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re) := by
  have hz_norm : ‖z - z₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hM₀ : (f z₀).re ≤ M := hre z₀ (Metric.mem_ball_self hR)
  let g : ℂ → ℂ := fun w ↦ f (z₀ + w) - f z₀
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    have hmap : Set.MapsTo (fun w : ℂ ↦ z₀ + w) (Metric.ball 0 R) (Metric.ball z₀ R) := by
      intro w hw
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact (hf.comp (differentiable_const z₀ |>.add differentiable_id).differentiableOn hmap).sub_const _
  have h_eps : ∀ ε : ℝ, 0 < ε →
      ‖f z - f z₀‖ ≤ 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re + ε) := by
    intro ε hε
    have hA : 0 < M - (f z₀).re + ε := by linarith
    have hg_maps : Set.MapsTo g (Metric.ball 0 R) {w : ℂ | w.re ≤ M - (f z₀).re + ε} := by
      intro w hw
      simp only [Set.mem_ofPred_eq, g, Complex.sub_re]
      have hw' : z₀ + w ∈ Metric.ball z₀ R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      linarith [hre (z₀ + w) hw']
    have hbc := Complex.borelCaratheodory_zero hA hg_diff hg_maps hR
      (by simpa [Metric.mem_ball, dist_eq_norm] using hz_norm) (by simp [g])
    have h_eq : g (z - z₀) = f z - f z₀ := by simp [g, add_sub_cancel]
    rw [h_eq] at hbc
    calc
      ‖f z - f z₀‖ ≤ 2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) := hbc
      _ = 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re + ε) := by ring
  have h_ev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖f z - f z₀‖ ≤ 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re + ε) :=
    eventually_nhdsWithin_of_forall fun ε hε ↦ h_eps ε hε
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ h_ev
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  have hcont : ContinuousAt (fun ε : ℝ ↦ 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re + ε)) 0 := by
    fun_prop
  simpa using hcont.tendsto

/-- Shifted **Borel–Carathéodory theorem** (difference form on a smaller closed disk): for
`0 ≤ r < R` and `z ∈ Metric.closedBall z₀ r`,
`‖f z - f z₀‖ ≤ 2 * r / (R - r) * (M - (f z₀).re)`. -/
theorem borel_caratheodory_sub_on_closedBall {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.closedBall z₀ r) :
    ‖f z - f z₀‖ ≤ 2 * r / (R - r) * (M - (f z₀).re) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hz_ball : z ∈ Metric.ball z₀ R := Metric.closedBall_subset_ball hrR hz
  have hz_norm : ‖z - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hM₀ : 0 ≤ M - (f z₀).re := sub_nonneg.mpr (hre z₀ (Metric.mem_ball_self hR))
  have h_frac : 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) ≤ 2 * r / (R - r) := by
    rw [div_le_div_iff₀ (sub_pos.mpr (hz_norm.trans_lt hrR)) (sub_pos.mpr hrR)]
    nlinarith [norm_nonneg (z - z₀)]
  exact (borel_caratheodory_sub hR hf hre hz_ball).trans
    (mul_le_mul_of_nonneg_right h_frac hM₀)

/-- Shifted **Borel–Carathéodory theorem**: for `f` holomorphic on `Metric.ball z₀ R` (`0 < R`)
with `(f w).re ≤ M` on `Metric.ball z₀ R`, and `z ∈ Metric.ball z₀ R`,
`‖f z‖ ≤ 2 * M * ‖z - z₀‖ / (R - ‖z - z₀‖) + ‖f z₀‖ * (R + ‖z - z₀‖) / (R - ‖z - z₀‖)`. -/
theorem borel_caratheodory {f : ℂ → ℂ} {z₀ z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.ball z₀ R) :
    ‖f z‖ ≤ 2 * M * ‖z - z₀‖ / (R - ‖z - z₀‖) + ‖f z₀‖ * (R + ‖z - z₀‖) / (R - ‖z - z₀‖) := by
  have hz_norm : ‖z - z₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hdenom : 0 < R - ‖z - z₀‖ := sub_pos.mpr hz_norm
  have h_re_neg : -(f z₀).re ≤ ‖f z₀‖ := neg_le_abs (f z₀).re |>.trans (Complex.abs_re_le_norm _)
  calc
    ‖f z‖ ≤ ‖f z - f z₀‖ + ‖f z₀‖ := norm_le_norm_sub_add (f z) (f z₀)
    _ ≤ 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re) + ‖f z₀‖ := by
      gcongr
      exact borel_caratheodory_sub hR hf hre hz
    _ = (2 * M * ‖z - z₀‖ + 2 * (-(f z₀).re) * ‖z - z₀‖ + ‖f z₀‖ * (R - ‖z - z₀‖)) /
        (R - ‖z - z₀‖) := by
      field_simp
      ring
    _ ≤ (2 * M * ‖z - z₀‖ + 2 * ‖f z₀‖ * ‖z - z₀‖ + ‖f z₀‖ * (R - ‖z - z₀‖)) /
        (R - ‖z - z₀‖) := by
      gcongr
    _ = 2 * M * ‖z - z₀‖ / (R - ‖z - z₀‖) + ‖f z₀‖ * (R + ‖z - z₀‖) / (R - ‖z - z₀‖) := by
      field_simp
      ring

/-- Shifted **Borel–Carathéodory theorem** on a closed smaller disk `Metric.closedBall z₀ r`
(`0 ≤ r < R`) when `0 ≤ M`:
`‖f z‖ ≤ 2 * r / (R - r) * M + (R + r) / (R - r) * ‖f z₀‖`. -/
theorem borel_caratheodory_on_closedBall {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.closedBall z₀ r) :
    ‖f z‖ ≤ 2 * r / (R - r) * M + (R + r) / (R - r) * ‖f z₀‖ := by
  have hR : 0 < R := hr.trans_lt hrR
  have hz_ball : z ∈ Metric.ball z₀ R := Metric.closedBall_subset_ball hrR hz
  have hz_norm : ‖z - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have h1 : 2 * M * ‖z - z₀‖ / (R - ‖z - z₀‖) ≤ 2 * r / (R - r) * M := by
    have hfrac : 2 * ‖z - z₀‖ / (R - ‖z - z₀‖) ≤ 2 * r / (R - r) := by
      rw [div_le_div_iff₀ (sub_pos.mpr (hz_norm.trans_lt hrR)) (sub_pos.mpr hrR)]
      nlinarith [norm_nonneg (z - z₀)]
    calc
      2 * M * ‖z - z₀‖ / (R - ‖z - z₀‖) = M * (2 * ‖z - z₀‖ / (R - ‖z - z₀‖)) := by ring
      _ ≤ M * (2 * r / (R - r)) := mul_le_mul_of_nonneg_left hfrac hM
      _ = 2 * r / (R - r) * M := by ring
  have h2 : ‖f z₀‖ * (R + ‖z - z₀‖) / (R - ‖z - z₀‖) ≤ (R + r) / (R - r) * ‖f z₀‖ := by
    rw [mul_div_assoc, mul_comm ‖f z₀‖]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [div_le_div_iff₀ (sub_pos.mpr (hz_norm.trans_lt hrR)) (sub_pos.mpr hrR)]
    nlinarith [norm_nonneg (z - z₀)]
  exact (borel_caratheodory hR hf hre hz_ball).trans (add_le_add h1 h2)

/-!
### Derivative Bounds from Borel–Carathéodory
-/

/-- First-derivative bound at the center `z₀` of `Metric.ball z₀ R`:
`‖deriv f z₀‖ ≤ 2 / R * (M - (f z₀).re)`. -/
theorem norm_deriv_center_le_of_re_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) :
    ‖deriv f z₀‖ ≤ 2 / R * (M - (f z₀).re) := by
  have hd : HasDerivAt f (deriv f z₀) z₀ :=
    (hf.differentiableAt (Metric.ball_mem_nhds z₀ hR)).hasDerivAt
  have htend : Tendsto (fun z : ℂ ↦ ‖(z - z₀)⁻¹ * (f z - f z₀)‖) (𝓝[≠] z₀) (𝓝 ‖deriv f z₀‖) :=
    ((hasDerivAt_iff_tendsto_slope.mp hd).norm).congr'
      (Eventually.of_forall fun z ↦ by simp [slope, vsub_eq_sub, smul_eq_mul])
  have hrhs : Tendsto (fun z : ℂ ↦ 2 / (R - ‖z - z₀‖) * (M - (f z₀).re))
      (𝓝[≠] z₀) (𝓝 (2 / R * (M - (f z₀).re))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have hcont : ContinuousAt (fun z : ℂ ↦ 2 / (R - ‖z - z₀‖) * (M - (f z₀).re)) z₀ := by
      fun_prop (disch := simp [hR.ne'])
    simpa using hcont.tendsto
  have hev : ∀ᶠ z in 𝓝[≠] z₀,
      ‖(z - z₀)⁻¹ * (f z - f z₀)‖ ≤ 2 / (R - ‖z - z₀‖) * (M - (f z₀).re) := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hR), self_mem_nhdsWithin] with z hz hne
    have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
    have hz_pos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr hne'
    have hbc := borel_caratheodory_sub hR hf hre hz
    calc
      ‖(z - z₀)⁻¹ * (f z - f z₀)‖ = ‖z - z₀‖⁻¹ * ‖f z - f z₀‖ := by rw [norm_mul, norm_inv]
      _ ≤ ‖z - z₀‖⁻¹ * (2 * ‖z - z₀‖ / (R - ‖z - z₀‖) * (M - (f z₀).re)) := by
        gcongr
      _ = 2 / (R - ‖z - z₀‖) * (M - (f z₀).re) := by
        field_simp [hz_pos.ne']
  exact le_of_tendsto_of_tendsto htend hrhs hev

/-- First-derivative bound on a smaller closed disk `Metric.closedBall z₀ r` (`0 ≤ r < R`):
`‖deriv f z‖ ≤ 2 * (R + r) / (R - r) ^ 2 * (M - (f z₀).re)`. -/
theorem norm_deriv_le_of_re_le_sharp {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.closedBall z₀ r) :
    ‖deriv f z‖ ≤ 2 * (R + r) / (R - r) ^ 2 * (M - (f z₀).re) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hz_norm : ‖z - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hsub : Metric.ball z (R - r) ⊆ Metric.ball z₀ R := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w z z₀, Metric.mem_closedBall.mp hz]
  have hcenter := norm_deriv_center_le_of_re_le hRr (hf.mono hsub) (fun w hw ↦ hre w (hsub hw))
  have hdiff_re : M - (f z).re ≤ (R + r) / (R - r) * (M - (f z₀).re) := by
    have h1 : (f z₀).re - (f z).re ≤ ‖f z - f z₀‖ := by
      have := Complex.abs_re_le_norm (f z₀ - f z)
      rw [Complex.sub_re, norm_sub_rev] at this
      exact (le_abs_self _).trans this
    have h2 : ‖f z - f z₀‖ ≤ 2 * r / (R - r) * (M - (f z₀).re) :=
      borel_caratheodory_sub_on_closedBall hr hrR hf hre hz
    calc
      M - (f z).re = (M - (f z₀).re) + ((f z₀).re - (f z).re) := by ring
      _ ≤ (M - (f z₀).re) + 2 * r / (R - r) * (M - (f z₀).re) := by linarith
      _ = (R + r) / (R - r) * (M - (f z₀).re) := by
        field_simp [hRr.ne']
        ring
  calc
    ‖deriv f z‖ ≤ 2 / (R - r) * (M - (f z).re) := hcenter
    _ ≤ 2 / (R - r) * ((R + r) / (R - r) * (M - (f z₀).re)) := by gcongr
    _ = 2 * (R + r) / (R - r) ^ 2 * (M - (f z₀).re) := by
      field_simp [hRr.ne']

/-- First-derivative bound on `Metric.closedBall z₀ r` (`0 ≤ r < R`) in `4 * R / (R - r)^2` form:
`‖deriv f z‖ ≤ 4 * R / (R - r) ^ 2 * (M - (f z₀).re)`. -/
theorem norm_deriv_le_of_re_le {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.closedBall z₀ r) :
    ‖deriv f z‖ ≤ 4 * R / (R - r) ^ 2 * (M - (f z₀).re) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hM₀ : 0 ≤ M - (f z₀).re := sub_nonneg.mpr (hre z₀ (Metric.mem_ball_self hR))
  have h_le : 2 * (R + r) ≤ 4 * R := by linarith
  refine (norm_deriv_le_of_re_le_sharp hr hrR hf hre hz).trans ?_
  gcongr

private lemma iteratedDeriv_sub_const_eq {f : ℂ → ℂ} (c : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (k : ℕ) (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv k (fun w ↦ f w - c) z = iteratedDeriv k f z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  refine Filter.EventuallyEq.iteratedDeriv_eq m ?_
  filter_upwards [hU.mem_nhds hz] with w _
  exact deriv_sub_const c

/-- Higher-derivative Borel–Carathéodory bound on `Metric.closedBall z₀ r` (`0 ≤ r < R`, `1 ≤ k`):
`‖iteratedDeriv k f z‖ ≤ 2 ^ (k + 2) * (k ! : ℝ) * R / (R - r) ^ (k + 1) * (M - (f z₀).re)`. -/
theorem norm_iteratedDeriv_le_of_re_le {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) (hz : z ∈ Metric.closedBall z₀ r) :
    ‖iteratedDeriv k f z‖ ≤ 2 ^ (k + 2) * (k ! : ℝ) * R / (R - r) ^ (k + 1) * (M - (f z₀).re) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hM₀ : 0 ≤ M - (f z₀).re := sub_nonneg.mpr (hre z₀ (Metric.mem_ball_self hR))
  let ρ : ℝ := (R - r) / 2
  have hρ : 0 < ρ := half_pos hRr
  let r₁ : ℝ := (R + r) / 2
  have hr₁_nonneg : 0 ≤ r₁ := by positivity
  have hr₁_lt : r₁ < R := by simp [r₁]; linarith
  have hz_norm : ‖z - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have h_ball_sub : Metric.closedBall z ρ ⊆ Metric.ball z₀ R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖w - z₀‖ = ‖(w - z) + (z - z₀)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ ρ + r := add_le_add hw hz_norm
      _ = r₁ := by simp [ρ, r₁]; ring
      _ < R := hr₁_lt
  let g : ℂ → ℂ := fun w ↦ f w - f z₀
  have hg_diff : DifferentiableOn ℂ g (Metric.closedBall z ρ) :=
    (hf.mono h_ball_sub).sub_const _
  have hcauchy := hg_diff.circleIntegral_one_div_sub_center_pow_smul hρ k
  have h_it : iteratedDeriv k g z = iteratedDeriv k f z :=
    iteratedDeriv_sub_const_eq (f z₀) isOpen_ball k hk (Metric.closedBall_subset_ball hrR hz)
  rw [h_it] at hcauchy
  let B : ℝ := 4 * R / (R - r) * (M - (f z₀).re)
  have hB_nonneg : 0 ≤ B := by positivity
  have h_sphere_bound : ∀ w ∈ Metric.sphere z ρ, ‖(1 / (w - z) ^ (k + 1)) • g w‖ ≤ B / ρ ^ (k + 1) := by
    intro w hw
    have hw_dist : ‖w - z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hw_z₀ : w ∈ Metric.closedBall z₀ r₁ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖w - z₀‖ = ‖(w - z) + (z - z₀)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ ρ + r := add_le_add hw_dist.le hz_norm
        _ = r₁ := by simp [ρ, r₁]; ring
    have hgw : ‖g w‖ ≤ B := by
      have hbc := borel_caratheodory_sub_on_closedBall hr₁_nonneg hr₁_lt hf hre hw_z₀
      have h_rr₁ : R - r₁ = (R - r) / 2 := by simp [r₁]; ring
      have h_coeff : 2 * r₁ / (R - r₁) ≤ 4 * R / (R - r) := by
        rw [h_rr₁]
        have h2 : 2 * r₁ / ((R - r) / 2) = 2 * (R + r) / (R - r) := by
          simp only [r₁]
          field_simp [hRr.ne']
        rw [h2]
        have h_num : 2 * (R + r) ≤ 4 * R := by linarith
        gcongr
      exact hbc.trans (mul_le_mul_of_nonneg_right h_coeff hM₀)
    simp only [smul_eq_mul, one_div]
    rw [norm_mul, norm_inv, norm_pow, hw_dist, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right hgw (by positivity)
  have h_int_bound := circleIntegral.norm_integral_le_of_norm_le_const hρ.le h_sphere_bound
  have h_lhs_norm : ‖((2 * π * I : ℂ) / (k ! : ℂ)) • iteratedDeriv k f z‖ =
      (2 * π / (k ! : ℝ)) * ‖iteratedDeriv k f z‖ := by
    rw [smul_eq_mul, norm_mul, norm_div, Complex.norm_mul, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
      Complex.norm_natCast]
  rw [hcauchy, h_lhs_norm] at h_int_bound
  have h_fac_pos : (0 : ℝ) < k ! := by positivity
  have h_pi_pos : 0 < 2 * π / (k ! : ℝ) := by positivity
  have h_res : ‖iteratedDeriv k f z‖ ≤ (k ! : ℝ) * (B / ρ ^ k) := by
    rw [← le_div_iff₀' h_pi_pos] at h_int_bound
    refine h_int_bound.trans_eq ?_
    rw [pow_succ']
    field_simp [Real.pi_ne_zero, hρ.ne', h_fac_pos.ne']
  refine h_res.trans_eq ?_
  have hρ_eq : ρ ^ k = (R - r) ^ k / 2 ^ k := by simp [ρ, div_pow]
  rw [hρ_eq]
  simp only [B]
  rw [pow_add, pow_succ, pow_succ' (R - r) k]
  field_simp [hRr.ne']
  ring

/-- Higher-derivative Borel–Carathéodory bound at the center `z₀` of `Metric.ball z₀ R`
for `k ≥ 1`:
`‖iteratedDeriv k f z₀‖ ≤ 2 ^ (k + 2) * (k ! : ℝ) / R ^ k * (M - (f z₀).re)`. -/
theorem norm_iteratedDeriv_center_le_of_re_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hR : 0 < R) (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) :
    ‖iteratedDeriv k f z₀‖ ≤ 2 ^ (k + 2) * (k ! : ℝ) / R ^ k * (M - (f z₀).re) := by
  have h := norm_iteratedDeriv_le_of_re_le hk le_rfl hR hf hre (Metric.mem_closedBall_self le_rfl)
  rw [sub_zero, pow_succ] at h
  refine h.trans_eq ?_
  field_simp [hR.ne']
  ring

/-!
### Holomorphic Logarithm on a Ball and Landau's Logarithmic-Derivative Lemma
-/

/-- If `f` is complex differentiable and nowhere zero on `Metric.ball z₀ R` (`0 < R`), then
there exists a holomorphic function `h` on `Metric.ball z₀ R` with `h z₀ = 0`,
`Complex.exp (h z) = f z / f z₀`, and `deriv h z = logDeriv f z` on `Metric.ball z₀ R`. -/
theorem exists_holomorphic_log_on_ball {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hf_ne : ∀ z ∈ Metric.ball z₀ R, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball z₀ R) ∧ h z₀ = 0 ∧
      (∀ z ∈ Metric.ball z₀ R, Complex.exp (h z) = f z / f z₀) ∧
      (∀ z ∈ Metric.ball z₀ R, deriv h z = logDeriv f z) := by
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball z₀ R) := hf.analyticOnNhd isOpen_ball
  have h_ld_diff : DifferentiableOn ℂ (logDeriv f) (Metric.ball z₀ R) := by
    intro z hz
    have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (isOpen_ball.mem_nhds hz)
    have hdf : DifferentiableAt ℂ (deriv f) z := (hf_an z hz).deriv.differentiableAt
    exact (hdf.div hfz (hf_ne z hz)).differentiableWithinAt
  obtain ⟨h, hh₀, hh_deriv⟩ := h_ld_diff.isExactOn_ball.with_val_at z₀ 0
  have hh_diff : DifferentiableOn ℂ h (Metric.ball z₀ R) := fun z hz ↦
    (hh_deriv z hz).differentiableAt.differentiableWithinAt
  have hh_deriv_eq : ∀ z ∈ Metric.ball z₀ R, deriv h z = logDeriv f z := fun z hz ↦
    (hh_deriv z hz).deriv
  let q : ℂ → ℂ := fun z ↦ (f z / f z₀) * Complex.exp (-h z)
  have hq_diff : DifferentiableOn ℂ q (Metric.ball z₀ R) := by
    intro z hz
    have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (isOpen_ball.mem_nhds hz)
    have hhz : DifferentiableAt ℂ h z := (hh_deriv z hz).differentiableAt
    exact ((hfz.div_const _).mul (hhz.neg.cexp)).differentiableWithinAt
  have hq_deriv_zero : Set.EqOn (deriv q) 0 (Metric.ball z₀ R) := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hhz : HasDerivAt h (logDeriv f z) z := hh_deriv z hz
    have hexp : HasDerivAt (fun w ↦ Complex.exp (-h w)) (Complex.exp (-h z) * (-logDeriv f z)) z :=
      hhz.neg.cexp
    have hmul : HasDerivAt q ((deriv f z / f z₀) * Complex.exp (-h z) +
        (f z / f z₀) * (Complex.exp (-h z) * (-logDeriv f z))) z :=
      (hfz.div_const (f z₀)).mul hexp
    rw [hmul.deriv]
    simp only [Pi.zero_apply, logDeriv_apply]
    have hfz₀ : f z₀ ≠ 0 := hf_ne z₀ (Metric.mem_ball_self hR)
    have hfzz : f z ≠ 0 := hf_ne z hz
    field_simp [hfz₀, hfzz]
    ring
  have hq_const : Set.EqOn q (fun _ ↦ q z₀) (Metric.ball z₀ R) := by
    intro z hz
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected
      hq_diff hq_deriv_zero hz (Metric.mem_ball_self hR)
    exact this
  have hq_z₀ : q z₀ = 1 := by
    have hfz₀ : f z₀ ≠ 0 := hf_ne z₀ (Metric.mem_ball_self hR)
    simp [q, hh₀, hfz₀]
  refine ⟨h, hh_diff, hh₀, fun z hz ↦ ?_, hh_deriv_eq⟩
  have hqz := hq_const hz
  rw [hq_z₀] at hqz
  dsimp only [q] at hqz
  have h1 : f z / f z₀ = (Complex.exp (-h z))⁻¹ := eq_inv_of_mul_eq_one_left hqz
  rw [← Complex.exp_neg, neg_neg] at h1
  exact h1.symm

/-- **Landau's logarithmic-derivative lemma (zero-free center form)**: if `f` is holomorphic and
nowhere zero on `Metric.ball z₀ R` (`0 < R`) with `‖f w / f z₀‖ ≤ M` on `Metric.ball z₀ R`, then
`‖logDeriv f z₀‖ ≤ 2 / R * Real.log M`. -/
theorem landau_logDeriv_center_le_of_ne_zero {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hf_ne : ∀ w ∈ Metric.ball z₀ R, f w ≠ 0)
    (hf_bound : ∀ w ∈ Metric.ball z₀ R, ‖f w / f z₀‖ ≤ M) :
    ‖logDeriv f z₀‖ ≤ 2 / R * Real.log M := by
  obtain ⟨h, hh_diff, hh₀, hh_exp, hh_deriv⟩ := exists_holomorphic_log_on_ball hR hf hf_ne
  have hM : 1 ≤ M := by
    have h1 := hf_bound z₀ (Metric.mem_ball_self hR)
    simpa [hf_ne z₀ (Metric.mem_ball_self hR)] using h1
  have hM_pos : 0 < M := zero_lt_one.trans_le hM
  have hre : ∀ w ∈ Metric.ball z₀ R, (h w).re ≤ Real.log M := by
    intro w hw
    have hexp := hh_exp w hw
    have hnorm : Real.exp (h w).re = ‖f w / f z₀‖ := by
      rw [← Complex.norm_exp, hexp]
    rw [← Real.exp_le_exp, hnorm, Real.exp_log hM_pos]
    exact hf_bound w hw
  have hcenter := norm_deriv_center_le_of_re_le hR hh_diff hre
  rw [hh_deriv z₀ (Metric.mem_ball_self hR), hh₀, Complex.zero_re, sub_zero] at hcenter
  exact hcenter

/-- **Landau's logarithmic-derivative lemma (zero-free disk form)**: if `f` is holomorphic and
nowhere zero on `Metric.ball z₀ R` (`0 ≤ r < R`) with `‖f w / f z₀‖ ≤ M` on `Metric.ball z₀ R`,
then for all `z ∈ Metric.closedBall z₀ r`,
`‖logDeriv f z‖ ≤ 2 * (R + r) / (R - r) ^ 2 * Real.log M`. -/
theorem landau_logDeriv_le_of_ne_zero {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hf_ne : ∀ w ∈ Metric.ball z₀ R, f w ≠ 0)
    (hf_bound : ∀ w ∈ Metric.ball z₀ R, ‖f w / f z₀‖ ≤ M)
    (hz : z ∈ Metric.closedBall z₀ r) :
    ‖logDeriv f z‖ ≤ 2 * (R + r) / (R - r) ^ 2 * Real.log M := by
  have hR : 0 < R := hr.trans_lt hrR
  obtain ⟨h, hh_diff, hh₀, hh_exp, hh_deriv⟩ := exists_holomorphic_log_on_ball hR hf hf_ne
  have hM : 1 ≤ M := by
    have h1 := hf_bound z₀ (Metric.mem_ball_self hR)
    simpa [hf_ne z₀ (Metric.mem_ball_self hR)] using h1
  have hM_pos : 0 < M := zero_lt_one.trans_le hM
  have hre : ∀ w ∈ Metric.ball z₀ R, (h w).re ≤ Real.log M := by
    intro w hw
    have hexp := hh_exp w hw
    have hnorm : Real.exp (h w).re = ‖f w / f z₀‖ := by
      rw [← Complex.norm_exp, hexp]
    rw [← Real.exp_le_exp, hnorm, Real.exp_log hM_pos]
    exact hf_bound w hw
  have hbound := norm_deriv_le_of_re_le_sharp hr hrR hh_diff hre hz
  rw [hh_deriv z (Metric.closedBall_subset_ball hrR hz), hh₀, Complex.zero_re, sub_zero] at hbound
  exact hbound

/-- Decomposition of an analytic function on `Metric.closedBall z₀ R` by factoring out its zeros in
`Metric.closedBall z₀ r₀` (`0 < r₀ < R`) as a factorized rational polynomial `polyP` times a
nonvanishing analytic function `g` on `Metric.closedBall z₀ r₀`, bounded on `Metric.closedBall z₀ R`
by `M * (r₀ / (R - r₀)) ^ N`. -/
private lemma extract_ball_zeros {f : ℂ → ℂ} {z₀ : ℂ} {r₀ R M : ℝ}
    (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖f w / f z₀‖ ≤ M) :
    let D := MeromorphicOn.divisor f (Metric.closedBall z₀ r₀)
    let hD_fin := D.finiteSupport (isCompact_closedBall z₀ r₀)
    let N : ℕ := ∑ u ∈ hD_fin.toFinset, (D u).toNat
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall z₀ R) ∧
      (∀ u ∈ Metric.closedBall z₀ r₀, g u ≠ 0) ∧
      (∀ w ∈ Metric.closedBall z₀ R, ‖g w / g z₀‖ ≤ M * (r₀ / (R - r₀)) ^ N) ∧
      (∀ z ∈ Metric.ball z₀ R, f z ≠ 0 →
        logDeriv f z - ∑ᶠ ρ, (D ρ : ℂ) / (z - ρ) = logDeriv g z) := by
  classical
  intro D hD_fin N
  let polyP : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  let U := Metric.closedBall z₀ R
  let V := Metric.closedBall z₀ r₀
  have hR : 0 < R := hr₀.trans hr₀R
  have hVU : V ⊆ U := Metric.closedBall_subset_closedBall hr₀R.le
  have hf_V : AnalyticOnNhd ℂ f V := hf.mono hVU
  have hP_nf : MeromorphicNFOn polyP U := Function.FactorizedRational.meromorphicNFOn D U
  have hP_mer : MeromorphicOn polyP U := hP_nf.meromorphicOn
  have h_quot_mer : MeromorphicOn (polyP⁻¹ * f) U := hP_mer.inv.mul hf.meromorphicOn
  let g : ℂ → ℂ := toMeromorphicNFOn (polyP⁻¹ * f) U
  have hg_nf : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn (polyP⁻¹ * f) U
  have h_f_ne_top : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u hu
    have htop : analyticOrderAt f u ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall z₀ R).isPreconnected
        (Metric.mem_closedBall_self hR.le) hu
        ((hf z₀ (Metric.mem_closedBall_self hR.le)).analyticOrderAt_eq_zero.mpr hz₀ |>.symm ▸ by simp)
    rw [(hf u hu).meromorphicOrderAt_eq]
    lift analyticOrderAt f u to ℕ using htop with n hn
    simp
  have h_P_ne_top : ∀ u, meromorphicOrderAt polyP u ≠ ⊤ :=
    fun u ↦ Function.FactorizedRational.meromorphicOrderAt_ne_top D
  have h_div_P : ∀ u, MeromorphicOn.divisor polyP U u = D u := by
    intro u
    by_cases hu : u ∈ U
    · simp only [hP_mer, hu, divisor_apply]
      rw [Function.FactorizedRational.meromorphicOrderAt_eq D hD_fin]
      simp
    · have huV : u ∉ V := fun h ↦ hu (hVU h)
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huV]
  have h_div_g : ∀ u, MeromorphicOn.divisor g U u = MeromorphicOn.divisor f U u - D u := by
    intro u
    have h_inv_ne_top : ∀ w ∈ U, meromorphicOrderAt polyP⁻¹ w ≠ ⊤ := fun w _ ↦ by
      simpa [meromorphicOrderAt_inv] using h_P_ne_top w
    have h_div_prod : MeromorphicOn.divisor (polyP⁻¹ * f) U =
        MeromorphicOn.divisor polyP⁻¹ U + MeromorphicOn.divisor f U :=
      divisor_mul hP_mer.inv hf.meromorphicOn h_inv_ne_top h_f_ne_top
    rw [divisor_of_toMeromorphicNFOn h_quot_mer, h_div_prod]
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, divisor_inv,
      Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, h_div_P u]
    ring
  have hg_an : AnalyticOnNhd ℂ g U := by
    rw [← hg_nf.divisor_nonneg_iff_analyticOnNhd]
    intro u
    rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h_div_g u, sub_nonneg]
    by_cases huV : u ∈ V
    · rw [hf_V.divisor_apply huV, hf.divisor_apply (hVU huV)]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D huV]
      exact hf.divisor_nonneg u
  have hg_ne_V : ∀ u ∈ V, g u ≠ 0 := by
    intro u huV
    have huU : u ∈ U := hVU huV
    rw [← (hg_nf huU).meromorphicOrderAt_eq_zero_iff]
    have hord_g : meromorphicOrderAt g u = meromorphicOrderAt (polyP⁻¹ * f) u :=
      meromorphicOrderAt_congr (toMeromorphicNFOn_eq_self_on_nhdsNE h_quot_mer huU)
    rw [hord_g, meromorphicOrderAt_mul (hP_mer.inv u huU) (hf.meromorphicOn u huU),
      meromorphicOrderAt_inv, Function.FactorizedRational.meromorphicOrderAt_eq D hD_fin]
    have hDu : (D u : WithTop ℤ) = meromorphicOrderAt f u := by
      rw [divisor_apply hf_V.meromorphicOn huV]
      lift meromorphicOrderAt f u to ℤ using h_f_ne_top u huU with n hn
      rfl
    rw [← hDu]
    lift meromorphicOrderAt f u to ℤ using h_f_ne_top u huU with n hn
    have : D u = n := by rw [← WithTop.coe_eq_coe]; exact hDu
    subst this
    simp
  have hg_eq_off : ∀ u ∈ U, u ∉ D.support → g u = (polyP u)⁻¹ * f u := by
    intro u huU hu_supp
    have hD_nonneg : 0 ≤ D u := by
      by_cases huV : u ∈ V
      · rw [divisor_apply hf_V.meromorphicOn huV]
        exact WithTop.untop₀_nonneg.mpr (hf u huU).meromorphicOrderAt_nonneg
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D huV]
    have hP_an : AnalyticAt ℂ polyP u := Function.FactorizedRational.analyticAt hD_nonneg
    have hP_ne : polyP u ≠ 0 :=
      Function.FactorizedRational.ne_zero (Function.notMem_support.mp hu_supp)
    have h_quot_an : AnalyticAt ℂ (polyP⁻¹ * f) u := (hP_an.inv hP_ne).mul (hf u huU)
    dsimp only [g]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt h_quot_mer huU,
      toMeromorphicNFAt_eq_self.mpr h_quot_an.meromorphicNFAt]
    rfl
  have hz₀_not_supp : z₀ ∉ D.support := by
    intro hmem
    have hz₀V : z₀ ∈ V := Metric.mem_closedBall_self hr₀.le
    rw [Function.mem_support, hf_V.divisor_apply hz₀V,
      (hf z₀ (Metric.mem_closedBall_self hR.le)).analyticOrderAt_eq_zero.mpr hz₀] at hmem
    simp at hmem
  have hP_z₀_ne : polyP z₀ ≠ 0 :=
    Function.FactorizedRational.ne_zero (Function.notMem_support.mp hz₀_not_supp)
  have hg_z₀_eq : g z₀ = (polyP z₀)⁻¹ * f z₀ :=
    hg_eq_off z₀ (Metric.mem_closedBall_self hR.le) hz₀_not_supp
  have hM_nonneg : 0 ≤ M := (norm_nonneg _).trans
    (hf_bound (z₀ + R) (by simp [abs_of_pos hR]))
  have h_mulsupp : (fun u ↦ (· - u) ^ D u).mulSupport ⊆ hD_fin.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  have hP_eval : ∀ x, polyP x = ∏ u ∈ hD_fin.toFinset, (x - u) ^ D u := by
    intro x
    have hfun := congrFun (Function.FactorizedRational.finprod_eq_fun hD_fin) x
    dsimp only [polyP] at hfun ⊢
    rw [hfun]
    exact finprod_eq_prod_of_mulSupport_subset _
      (fun u hu ↦ h_mulsupp (fun h1 ↦ hu (by simpa using congrFun h1 x)))
  have hg_sphere_bound : ∀ w ∈ Metric.sphere z₀ R, ‖g w / g z₀‖ ≤ M * (r₀ / (R - r₀)) ^ N := by
    intro w hw
    have hwU : w ∈ U := Metric.sphere_subset_closedBall hw
    have hw_not_supp : w ∉ D.support := by
      intro hmem
      have hwV : w ∈ V := D.supportWithinDomain hmem
      have h1 : ‖w - z₀‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
      have h2 : ‖w - z₀‖ ≤ r₀ := by simpa [V, Metric.mem_closedBall, dist_eq_norm] using hwV
      linarith
    have hg_w_eq : g w = (polyP w)⁻¹ * f w := hg_eq_off w hwU hw_not_supp
    have hP_w_ne : polyP w ≠ 0 :=
      Function.FactorizedRational.ne_zero (Function.notMem_support.mp hw_not_supp)
    have h_ratio_eq : g w / g z₀ = (f w / f z₀) * (polyP z₀ / polyP w) := by
      rw [hg_w_eq, hg_z₀_eq]
      field_simp [hz₀, hP_z₀_ne, hP_w_ne]
    have h_prod_le : ‖polyP z₀ / polyP w‖ ≤ (r₀ / (R - r₀)) ^ N := by
      rw [hP_eval z₀, hP_eval w, ← Finset.prod_div_distrib, norm_prod]
      have hN_sum : N = ∑ u ∈ hD_fin.toFinset, (D u).toNat := rfl
      rw [hN_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun u hu ↦ ?_
      have hu_supp : u ∈ D.support := hD_fin.mem_toFinset.mp hu
      have huV : u ∈ V := D.supportWithinDomain hu_supp
      have hD_nonneg : 0 ≤ D u := by
        rw [divisor_apply hf_V.meromorphicOn huV]
        exact WithTop.untop₀_nonneg.mpr (hf u (hVU huV)).meromorphicOrderAt_nonneg
      have hD_cast : D u = ((D u).toNat : ℤ) := (Int.toNat_of_nonneg hD_nonneg).symm
      rw [← div_zpow, norm_zpow, hD_cast, zpow_natCast]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      have hnum : ‖z₀ - u‖ ≤ r₀ := by
        rw [norm_sub_rev]
        simpa [V, Metric.mem_closedBall, dist_eq_norm] using huV
      have hden : R - r₀ ≤ ‖w - u‖ := by
        have hw_norm : ‖w - z₀‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
        have htri : ‖w - z₀‖ ≤ ‖w - u‖ + ‖z₀ - u‖ := by
          calc
            ‖w - z₀‖ = ‖(w - u) + (u - z₀)‖ := by ring_nf
            _ ≤ ‖w - u‖ + ‖u - z₀‖ := norm_add_le _ _
            _ = ‖w - u‖ + ‖z₀ - u‖ := by rw [norm_sub_rev u z₀]
        linarith
      rw [norm_div]
      exact div_le_div₀ (by positivity) hnum (sub_pos.mpr hr₀R) hden
    rw [h_ratio_eq, norm_mul]
    exact mul_le_mul (hf_bound w hw) h_prod_le (norm_nonneg _) hM_nonneg
  have hg_ball_bound : ∀ w ∈ Metric.closedBall z₀ R, ‖g w / g z₀‖ ≤ M * (r₀ / (R - r₀)) ^ N := by
    have h_diff_quot : DiffContOnCl ℂ (fun w ↦ g w / g z₀) (Metric.ball z₀ R) :=
      (hg_an.differentiableOn.div_const (g z₀)).diffContOnCl_ball Subset.rfl
    intro w hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball h_diff_quot
      (fun x hx ↦ hg_sphere_bound x (Metric.frontier_ball_subset_sphere hx))
      (closure_ball z₀ hR.ne' ▸ hw)
  refine ⟨g, hg_an, hg_ne_V, hg_ball_bound, ?_⟩
  intro z hz hfz
  have hzU : z ∈ U := Metric.ball_subset_closedBall hz
  have hz_not_supp : z ∉ D.support := by
    intro hmem
    have hzV : z ∈ V := D.supportWithinDomain hmem
    rw [Function.mem_support, hf_V.divisor_apply hzV,
      (hf z hzU).analyticOrderAt_eq_zero.mpr hfz] at hmem
    simp at hmem
  have h_open : IsOpen (Metric.ball z₀ R \ (D.support : Set ℂ)) :=
    isOpen_ball.sdiff hD_fin.isClosed
  have hz_in_open : z ∈ Metric.ball z₀ R \ (D.support : Set ℂ) := ⟨hz, hz_not_supp⟩
  have h_ev_eq : f =ᶠ[𝓝 z] polyP * g := by
    filter_upwards [h_open.mem_nhds hz_in_open] with w hw
    have hwU : w ∈ U := Metric.ball_subset_closedBall hw.1
    have hgw := hg_eq_off w hwU hw.2
    have hP_ne : polyP w ≠ 0 :=
      Function.FactorizedRational.ne_zero (Function.notMem_support.mp hw.2)
    rw [Pi.mul_apply, hgw]
    field_simp [hP_ne]
  have hP_an : AnalyticAt ℂ polyP z := by
    have hDz : D z = 0 := Function.notMem_support.mp hz_not_supp
    exact Function.FactorizedRational.analyticAt (by simp [hDz])
  have hP_ne : polyP z ≠ 0 :=
    Function.FactorizedRational.ne_zero (Function.notMem_support.mp hz_not_supp)
  have hg_ne_z : g z ≠ 0 := by
    rw [hg_eq_off z hzU hz_not_supp]
    exact mul_ne_zero (inv_ne_zero hP_ne) hfz
  have h_ld_eq : logDeriv f z = logDeriv polyP z + logDeriv g z := by
    rw [(logDeriv_congr_nhds h_ev_eq).eq_of_nhds]
    exact logDeriv_mul z hP_ne hg_ne_z hP_an.differentiableAt (hg_an z hzU).differentiableAt
  have h_ld_P : logDeriv polyP z = ∑ᶠ ρ, (D ρ : ℂ) / (z - ρ) := by
    have hP_fun : polyP = ∏ u ∈ hD_fin.toFinset, fun x ↦ (x - u) ^ D u := by
      ext x
      rw [hP_eval x, Finset.prod_apply]
    rw [hP_fun, logDeriv_prod]
    · have h_supp_sub : (fun ρ ↦ (D ρ : ℂ) / (z - ρ)).support ⊆ hD_fin.toFinset := by
        intro ρ hρ
        rw [Function.mem_support] at hρ
        apply hD_fin.mem_toFinset.mpr
        rw [Function.mem_support]
        intro h0
        apply hρ
        simp [h0]
      rw [finsum_eq_sum_of_support_subset _ h_supp_sub]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      rw [logDeriv_fun_zpow (by fun_prop) (D ρ)]
      have h_lin : logDeriv (fun x : ℂ ↦ x - ρ) z = 1 / (z - ρ) := by
        simp [logDeriv_apply]
      rw [h_lin, mul_one_div]
    · intro ρ hρ
      have hρ_ne : z - ρ ≠ 0 := sub_ne_zero.mpr fun h ↦ hz_not_supp (h ▸ hD_fin.mem_toFinset.mp hρ)
      exact zpow_ne_zero _ hρ_ne
    · intro ρ hρ
      have hρ_ne : z - ρ ≠ 0 := sub_ne_zero.mpr fun h ↦ hz_not_supp (h ▸ hD_fin.mem_toFinset.mp hρ)
      exact (differentiableAt_id.sub_const ρ).zpow (Or.inl hρ_ne)
  rw [h_ld_eq, h_ld_P]
  ring

/-- **Landau's logarithmic-derivative lemma** at the center `z₀` (closed-ball hypothesis):
for `f` analytic on `Metric.closedBall z₀ R` (`0 < R`) with `f z₀ ≠ 0` and
`‖f w / f z₀‖ ≤ M` on `Metric.sphere z₀ R`,
`‖logDeriv f z₀ - ∑ᶠ ρ, (MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2)) ρ : ℂ) / (z₀ - ρ)‖ ≤ (4 / R) * Real.log M`. -/
theorem landau_logDeriv_center_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖f w / f z₀‖ ≤ M) :
    ‖logDeriv f z₀ - ∑ᶠ ρ, (MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2)) ρ : ℂ) / (z₀ - ρ)‖ ≤
      (4 / R) * Real.log M := by
  obtain ⟨g, hg_an, hg_ne, hg_bound, h_ld⟩ :=
    extract_ball_zeros (half_pos hR) (half_lt_self hR) hf hz₀ hf_bound
  have h_ball : Metric.ball z₀ (R / 2) ⊆ Metric.closedBall z₀ (R / 2) := Metric.ball_subset_closedBall
  have h_ball_R : Metric.ball z₀ (R / 2) ⊆ Metric.closedBall z₀ R :=
    h_ball.trans (Metric.closedBall_subset_closedBall (by linarith))
  have h_ratio_one : (R / 2) / (R - R / 2) = 1 := by field_simp [hR.ne']; ring
  have hc := landau_logDeriv_center_le_of_ne_zero (half_pos hR)
    (hg_an.mono h_ball_R).differentiableOn (fun w hw ↦ hg_ne w (h_ball hw))
    (fun w hw ↦ by simpa [h_ratio_one] using hg_bound w (h_ball_R hw))
  rw [h_ld z₀ (Metric.mem_ball_self hR) hz₀]
  refine hc.trans_eq ?_
  field_simp [hR.ne']
  ring

/-- **Landau's logarithmic-derivative lemma** on `Metric.closedBall z₀ r` (`0 ≤ r < R / 2`):
`‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤ 2 * (R / 2 + r) / (R / 2 - r) ^ 2 * Real.log M`. -/
theorem landau_logDeriv_le_of_lt {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ} (hr : 0 ≤ r)
    (hrR : r < R / 2) (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖f w / f z₀‖ ≤ M)
    (hz : z ∈ Metric.closedBall z₀ r) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤
      2 * (R / 2 + r) / (R / 2 - r) ^ 2 * Real.log M := by
  have hR : 0 < R := by linarith
  obtain ⟨g, hg_an, hg_ne, hg_bound, h_ld⟩ :=
    extract_ball_zeros (half_pos hR) (half_lt_self hR) hf hz₀ hf_bound
  have h_ball : Metric.ball z₀ (R / 2) ⊆ Metric.closedBall z₀ (R / 2) := Metric.ball_subset_closedBall
  have h_ball_R : Metric.ball z₀ (R / 2) ⊆ Metric.closedBall z₀ R :=
    h_ball.trans (Metric.closedBall_subset_closedBall (by linarith))
  have h_ratio_one : (R / 2) / (R - R / 2) = 1 := by field_simp [hR.ne']; ring
  have hb := landau_logDeriv_le_of_ne_zero hr hrR
    (hg_an.mono h_ball_R).differentiableOn (fun w hw ↦ hg_ne w (h_ball hw))
    (fun w hw ↦ by simpa [h_ratio_one] using hg_bound w (h_ball_R hw)) hz
  have hz_ball : z ∈ Metric.ball z₀ R :=
    Metric.closedBall_subset_ball (by linarith) hz
  rwa [h_ld z hz_ball hfz]

/-- **Landau's logarithmic-derivative lemma** on the quarter disk `Metric.closedBall z₀ (R / 4)`:
`‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤ (24 / R) * Real.log M`. -/
theorem landau_logDeriv_le {f : ℂ → ℂ} {z₀ z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖f w / f z₀‖ ≤ M)
    (hz : z ∈ Metric.closedBall z₀ (R / 4)) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤
      (24 / R) * Real.log M := by
  have h := landau_logDeriv_le_of_lt (by positivity) (by linarith) hf hz₀ hf_bound hz hfz
  refine h.trans_eq ?_
  field_simp [hR.ne']
  ring

/-- Open-ball version of **Landau's logarithmic-derivative lemma** at the center `z₀`:
if `f` is complex differentiable on `Metric.ball z₀ R` (`0 < R`), `f z₀ ≠ 0`, and
`‖f w / f z₀‖ ≤ M` on `Metric.ball z₀ R`, then
`‖logDeriv f z₀ - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z₀ - ρ)‖ ≤ (4 / R) * Real.log M`. -/
theorem landau_logDeriv_center_le_of_ball {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.ball z₀ R, ‖f w / f z₀‖ ≤ M) :
    ‖logDeriv f z₀ - ∑ᶠ ρ, (MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2)) ρ : ℂ) / (z₀ - ρ)‖ ≤
      (4 / R) * Real.log M := by
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball z₀ R) := hf.analyticOnNhd isOpen_ball
  let D := MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2))
  let hD_fin := D.finiteSupport (isCompact_closedBall z₀ (R / 2))
  let N : ℕ := ∑ u ∈ hD_fin.toFinset, (D u).toNat
  have hM : 1 ≤ M := by simpa [hz₀] using hf_bound z₀ (Metric.mem_ball_self hR)
  have hM_pos : 0 < M := zero_lt_one.trans_le hM
  have h_ev : ∀ᶠ R' in 𝓝[<] R,
      ‖logDeriv f z₀ - ∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ)‖ ≤
        (4 / R) * Real.log (M * ((R / 2) / (R' - R / 2)) ^ N) := by
    filter_upwards [Ioo_mem_nhdsLT (half_lt_self hR)] with R' ⟨hR'₁, hR'₂⟩
    have hR'_pos : 0 < R' := (half_pos hR).trans hR'₁
    have hf_R' : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R') :=
      hf_an.mono (Metric.closedBall_subset_ball hR'₂)
    have h_ratio : ∀ w ∈ Metric.sphere z₀ R', ‖f w / f z₀‖ ≤ M := fun w hw ↦
      hf_bound w (Metric.closedBall_subset_ball hR'₂ (Metric.sphere_subset_closedBall hw))
    obtain ⟨g, hg_an, hg_ne, hg_bound, h_ld⟩ :=
      extract_ball_zeros (half_pos hR) hR'₁ hf_R' hz₀ h_ratio
    have h_ball : Metric.ball z₀ (R / 2) ⊆ Metric.closedBall z₀ (R / 2) :=
      Metric.ball_subset_closedBall
    have h_ball_R' : Metric.ball z₀ (R / 2) ⊆ Metric.closedBall z₀ R' :=
      h_ball.trans (Metric.closedBall_subset_closedBall hR'₁.le)
    have hc := landau_logDeriv_center_le_of_ne_zero (half_pos hR)
      (hg_an.mono h_ball_R').differentiableOn (fun w hw ↦ hg_ne w (h_ball hw))
      (fun w hw ↦ hg_bound w (h_ball_R' hw))
    rw [h_ld z₀ (Metric.mem_ball_self hR'_pos) hz₀]
    refine hc.trans_eq ?_
    field_simp [hR.ne']
    ring
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ h_ev
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  have h_eq1 : (4 / R) * Real.log (M * ((R / 2) / (R - R / 2)) ^ N) = (4 / R) * Real.log M := by
    have : (R / 2) / (R - R / 2) = 1 := by field_simp [hR.ne']; ring
    simp [this]
  rw [← h_eq1]
  have h_sub_ne : R - R / 2 ≠ 0 := by linarith
  have h_arg_pos : M * ((R / 2) / (R - R / 2)) ^ N ≠ 0 := by
    have : (R / 2) / (R - R / 2) = 1 := by field_simp [hR.ne']; ring
    simp [this, hM_pos.ne']
  have hcont : ContinuousAt
      (fun R' : ℝ ↦ (4 / R) * Real.log (M * ((R / 2) / (R' - R / 2)) ^ N)) R := by
    fun_prop (disch := simp [h_sub_ne, h_arg_pos])
  exact hcont.tendsto

/-- Real-part consequence of **Landau's logarithmic-derivative lemma** at `z₀`:
if all zeros of `f` in `Metric.closedBall z₀ (R / 2)` satisfy `ρ.re ≤ z₀.re`, then
`- (logDeriv f z₀).re ≤ (4 / R) * Real.log M`. -/
theorem landau_neg_re_logDeriv_center_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖f w / f z₀‖ ≤ M)
    (hzeros : ∀ ρ ∈ Metric.closedBall z₀ (R / 2), f ρ = 0 → ρ.re ≤ z₀.re) :
    -(logDeriv f z₀).re ≤ (4 / R) * Real.log M := by
  let D := MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2))
  have hD_fin : D.support.Finite := D.finiteSupport (isCompact_closedBall z₀ (R / 2))
  have hf_half : AnalyticOnNhd ℂ f (Metric.closedBall z₀ (R / 2)) :=
    hf.mono (Metric.closedBall_subset_closedBall (by linarith))
  have h_landau := landau_logDeriv_center_le hR hf hz₀ hf_bound
  have h_re_le : -(logDeriv f z₀).re + (∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ)).re ≤ (4 / R) * Real.log M := by
    have h1 := Complex.abs_re_le_norm (logDeriv f z₀ - ∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ))
    rw [Complex.sub_re] at h1
    have h2 := (neg_le_abs _).trans h1 |>.trans h_landau
    linarith
  have h_sum_nonneg : 0 ≤ (∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ)).re := by
    have h_supp_sub : (fun ρ ↦ (D ρ : ℂ) / (z₀ - ρ)).support ⊆ hD_fin.toFinset := by
      intro ρ hρ
      rw [Function.mem_support] at hρ
      apply hD_fin.mem_toFinset.mpr
      rw [Function.mem_support]
      intro h0; apply hρ; simp [h0]
    rw [finsum_eq_sum_of_support_subset _ h_supp_sub, Complex.re_sum]
    refine Finset.sum_nonneg fun ρ hρ ↦ ?_
    have hρ_supp : ρ ∈ D.support := hD_fin.mem_toFinset.mp hρ
    have hρV : ρ ∈ Metric.closedBall z₀ (R / 2) := D.supportWithinDomain hρ_supp
    have hD_nonneg : (0 : ℝ) ≤ D ρ := by exact_mod_cast hf_half.divisor_nonneg ρ
    have hfρ : f ρ = 0 := by
      by_contra hne
      have h0 : D ρ = 0 := by
        simp [D, hf_half.divisor_apply hρV, (hf_half ρ hρV).analyticOrderAt_eq_zero.mpr hne]
      exact hρ_supp h0
    have hρ_re : ρ.re ≤ z₀.re := hzeros ρ hρV hfρ
    rw [div_eq_mul_inv, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    refine mul_nonneg hD_nonneg ?_
    rw [Complex.inv_re, Complex.sub_re]
    exact div_nonneg (sub_nonneg.mpr hρ_re) (Complex.normSq_nonneg _)
  linarith

/-- Single-zero extraction form of **Landau's logarithmic-derivative lemma** at `z₀`:
if all zeros of `f` in `Metric.closedBall z₀ (R / 2)` satisfy `ρ.re ≤ z₀.re` and `ρ₀` is a
specific zero in `Metric.closedBall z₀ (R / 2)`, then
`-(logDeriv f z₀).re ≤ (4 / R) * Real.log M - ((z₀ - ρ₀)⁻¹).re`. -/
theorem landau_neg_re_logDeriv_center_le_sub_zero {f : ℂ → ℂ} {z₀ ρ₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) (hz₀ : f z₀ ≠ 0)
    (hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖f w / f z₀‖ ≤ M)
    (hzeros : ∀ ρ ∈ Metric.closedBall z₀ (R / 2), f ρ = 0 → ρ.re ≤ z₀.re)
    (hρ₀_mem : ρ₀ ∈ Metric.closedBall z₀ (R / 2)) (hρ₀ : f ρ₀ = 0) :
    -(logDeriv f z₀).re ≤ (4 / R) * Real.log M - ((z₀ - ρ₀)⁻¹).re := by
  let D := MeromorphicOn.divisor f (Metric.closedBall z₀ (R / 2))
  have hD_fin : D.support.Finite := D.finiteSupport (isCompact_closedBall z₀ (R / 2))
  have hf_half : AnalyticOnNhd ℂ f (Metric.closedBall z₀ (R / 2)) :=
    hf.mono (Metric.closedBall_subset_closedBall (by linarith))
  have h_landau := landau_logDeriv_center_le hR hf hz₀ hf_bound
  have h_re_le : -(logDeriv f z₀).re + (∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ)).re ≤ (4 / R) * Real.log M := by
    have h1 := Complex.abs_re_le_norm (logDeriv f z₀ - ∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ))
    rw [Complex.sub_re] at h1
    have h2 := (neg_le_abs _).trans h1 |>.trans h_landau
    linarith
  have hρ₀_ord : 1 ≤ D ρ₀ := by
    have htop : analyticOrderAt f ρ₀ ≠ ⊤ := by
      apply hf_half.analyticOrderAt_ne_top_of_isPreconnected
        (convex_closedBall z₀ (R / 2)).isPreconnected (Metric.mem_closedBall_self (by positivity))
        hρ₀_mem
      exact (hf_half z₀ (Metric.mem_closedBall_self (by positivity))).analyticOrderAt_eq_zero.mpr hz₀
        |>.symm ▸ by simp
    have hne0 : analyticOrderAt f ρ₀ ≠ 0 :=
      (hf_half ρ₀ hρ₀_mem).analyticOrderAt_eq_zero.not.mpr (not_not.mpr hρ₀)
    have hnat : 1 ≤ analyticOrderNatAt f ρ₀ := by
      refine Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hne0 ?_
      rw [← Nat.cast_analyticOrderNatAt htop, h0]
      rfl
    rw [hf_half.divisor_apply hρ₀_mem, ← Nat.cast_analyticOrderNatAt htop]
    simpa using hnat
  have hρ₀_supp : ρ₀ ∈ hD_fin.toFinset :=
    hD_fin.mem_toFinset.mpr (Function.mem_support.mpr (by omega))
  have h_supp_sub : (fun ρ ↦ (D ρ : ℂ) / (z₀ - ρ)).support ⊆ hD_fin.toFinset := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    apply hD_fin.mem_toFinset.mpr
    rw [Function.mem_support]
    intro h0; apply hρ; simp [h0]
  have h_sum_ge : ((z₀ - ρ₀)⁻¹).re ≤ (∑ᶠ ρ, (D ρ : ℂ) / (z₀ - ρ)).re := by
    rw [finsum_eq_sum_of_support_subset _ h_supp_sub, Complex.re_sum]
    have h_term : ((z₀ - ρ₀)⁻¹).re ≤ ((D ρ₀ : ℂ) / (z₀ - ρ₀)).re := by
      rw [div_eq_mul_inv, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
      have h_inv_nonneg : 0 ≤ ((z₀ - ρ₀)⁻¹).re := by
        rw [Complex.inv_re, Complex.sub_re]
        exact div_nonneg (sub_nonneg.mpr (hzeros ρ₀ hρ₀_mem hρ₀)) (Complex.normSq_nonneg _)
      have h1 : (1 : ℝ) ≤ D ρ₀ := by exact_mod_cast hρ₀_ord
      calc
        ((z₀ - ρ₀)⁻¹).re = 1 * ((z₀ - ρ₀)⁻¹).re := (one_mul _).symm
        _ ≤ (D ρ₀ : ℝ) * ((z₀ - ρ₀)⁻¹).re := mul_le_mul_of_nonneg_right h1 h_inv_nonneg
    refine h_term.trans (Finset.single_le_sum (f := fun ρ ↦ ((D ρ : ℂ) / (z₀ - ρ)).re)
      (fun ρ hρ ↦ ?_) hρ₀_supp)
    have hρ_supp : ρ ∈ D.support := hD_fin.mem_toFinset.mp hρ
    have hρV : ρ ∈ Metric.closedBall z₀ (R / 2) := D.supportWithinDomain hρ_supp
    have hD_nonneg : (0 : ℝ) ≤ D ρ := by exact_mod_cast hf_half.divisor_nonneg ρ
    have hfρ : f ρ = 0 := by
      by_contra hne
      have h0 : D ρ = 0 := by
        simp [D, hf_half.divisor_apply hρV, (hf_half ρ hρV).analyticOrderAt_eq_zero.mpr hne]
      exact hρ_supp h0
    rw [div_eq_mul_inv, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    refine mul_nonneg hD_nonneg ?_
    rw [Complex.inv_re, Complex.sub_re]
    exact div_nonneg (sub_nonneg.mpr (hzeros ρ hρV hfρ)) (Complex.normSq_nonneg _)
  linarith

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
