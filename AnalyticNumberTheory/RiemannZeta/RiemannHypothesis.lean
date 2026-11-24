import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PhragmenLindelof
import AnalyticNumberTheory.DirichletSeries.Convergence
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.DirichletSeries.VerticalOrder
import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.RiemannZeta.HadamardProduct

/-!
# The Riemann Hypothesis, Equivalent Formulations, and Lindelöf Consequence

This file states the Riemann Hypothesis (`RiemannHypothesisProp`) and bridges it to Mathlib's
`_root_.RiemannHypothesis`, establishes functional-equation zero-free equivalences, characterizes
the Riemann Hypothesis via holomorphicity of the reciprocal `1 / ζ(s)` on `Re s > 1 / 2`, proves
Hadamard's Three-Circles theorem and conditional Littlewood-type growth bounds on `ζ(s)` and
`ζ(s)⁻¹` for `Re s ≥ σ₀ > 1 / 2`, deduces the equivalence with the Mertens bound
`M(x) = O(x ^ (1 / 2 + ε))` and with `σ_c(μ) ≤ 1 / 2` via Perron's formula and contour
shifting, and defines the Lindelöf Hypothesis (`LindelofHypothesisProp`), proving both its
vertical-order equivalence and the implication `RiemannHypothesisProp → LindelofHypothesisProp`.
-/

open Complex Real Filter MeasureTheory Set Asymptotics
open scoped Topology Nat ArithmeticFunction
open AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

noncomputable section

/-! ### Statement and Functional-Equation Equivalences -/

section Equivalences

/-- **The Riemann Hypothesis**: every zero of `riemannZeta` in the open critical strip
`0 < Re s < 1` has real part `Re s = 1 / 2`. -/
def RiemannHypothesisProp : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Equivalence between `RiemannHypothesisProp` and Mathlib's `_root_.RiemannHypothesis`. -/
theorem riemannHypothesisProp_iff_mathlib :
    RiemannHypothesisProp ↔ _root_.RiemannHypothesis := by
  constructor
  · intro hRH s hs0 htriv _
    have hre := nontrivial_zero_re_mem_Ioo hs0 htriv
    exact hRH s hs0 hre.1 hre.2
  · intro hRH s hs0 h0 h1
    have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have hre : (-2 * ((n : ℂ) + 1)).re ≤ 0 := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.re_ofNat,
          Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.add_im, Complex.natCast_im,
          Complex.one_im]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      linarith
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at h1
    exact hRH s hs0 htriv hs1

/-- Characterization of `RiemannHypothesisProp` in terms of `CriticalStripZeros`. -/
theorem riemannHypothesisProp_iff_criticalStripZeros :
    RiemannHypothesisProp ↔ ∀ ρ ∈ CriticalStripZeros, ρ.re = 1 / 2 :=
  ⟨fun h ρ hρ ↦ h ρ hρ.1 hρ.2.1 hρ.2.2, fun h s hs h0 h1 ↦ h s ⟨hs, h0, h1⟩⟩

/-- Functional-equation equivalence: `RiemannHypothesisProp` holds if and only if
`riemannZeta` does not vanish on the half-plane `1 / 2 < Re s`. -/
theorem riemannHypothesisProp_iff_ne_zero_of_half_lt_re :
    RiemannHypothesisProp ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  constructor
  · intro hRH s hs h0
    rcases le_or_gt 1 s.re with hge | hlt
    · exact riemannZeta_ne_zero_of_one_le_re_bridge hge h0
    · have hs0 : 0 < s.re := by linarith
      have heq := hRH s h0 hs0 hlt
      linarith
  · intro hne s hs0 h0 h1
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have hmem : 1 - s ∈ CriticalStripZeros :=
        one_sub_mem_criticalStripZeros ⟨hs0, h0, h1⟩
      have hre : 1 / 2 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      exact hne (1 - s) hre hmem.1
    · exact hne s hgt hs0

/-- Reflected half-strip equivalence: `RiemannHypothesisProp` holds if and only if
`riemannZeta` does not vanish on `0 < Re s < 1 / 2`. -/
theorem riemannHypothesisProp_iff_ne_zero_of_lt_half :
    RiemannHypothesisProp ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → riemannZeta s ≠ 0 := by
  constructor
  · intro hRH s h0 hlt hs0
    have heq := hRH s hs0 h0 (by linarith)
    linarith
  · intro hne
    rw [riemannHypothesisProp_iff_ne_zero_of_half_lt_re]
    intro s hs hs0
    rcases le_or_gt 1 s.re with hge | hlt1
    · exact riemannZeta_ne_zero_of_one_le_re_bridge hge hs0
    · have hmem : 1 - s ∈ CriticalStripZeros :=
        one_sub_mem_criticalStripZeros ⟨hs0, by linarith, hlt1⟩
      have hre0 : 0 < (1 - s).re := hmem.2.1
      have hre_lt : (1 - s).re < 1 / 2 := by
        simp only [Complex.sub_re, Complex.one_re]; linarith
      exact hne (1 - s) hre0 hre_lt hmem.1

/-- `xi` characterization: `RiemannHypothesisProp` holds if and only if `xi s ≠ 0`
whenever `1 / 2 < Re s`. -/
theorem riemannHypothesisProp_iff_xi_ne_zero_of_half_lt_re :
    RiemannHypothesisProp ↔ ∀ s : ℂ, 1 / 2 < s.re → xi s ≠ 0 := by
  rw [riemannHypothesisProp_iff_ne_zero_of_half_lt_re]
  constructor
  · intro h s hs hxi
    have hc := (xi_eq_zero_iff).mp hxi
    exact h s hs hc.1
  · intro h s hs hz
    rcases le_or_gt 1 s.re with hge | hlt1
    · exact riemannZeta_ne_zero_of_one_le_re_bridge hge hz
    · exact h s hs ((xi_eq_zero_iff).mpr ⟨hz, by linarith, hlt1⟩)

end Equivalences

/-! ### Analyticity of `1 / ζ(s)` on `Re s > 1 / 2` -/

section ReciprocalAnalyticity

/-- Reciprocal of `riemannZeta`, extended by `0` at the simple pole `s = 1`. -/
def riemannZetaInv (s : ℂ) : ℂ :=
  if s = 1 then 0 else (riemannZeta s)⁻¹

/-- Away from `s = 1`, `riemannZetaInv s = (riemannZeta s)⁻¹`. -/
@[simp]
theorem riemannZetaInv_eq_inv_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    riemannZetaInv s = (riemannZeta s)⁻¹ := by
  simp [riemannZetaInv, hs]

private lemma riemannZeta₁_one_eq : riemannZeta₁ 1 = 1 := by
  have hev : (fun s : ℂ ↦ (s - 1) * riemannZeta s) =ᶠ[𝓝[≠] (1 : ℂ)] riemannZeta₁ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]
  have hcont : Tendsto riemannZeta₁ (𝓝[≠] (1 : ℂ)) (𝓝 (riemannZeta₁ 1)) :=
    differentiable_riemannZeta₁_bridge.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hcont (tendsto_sub_one_mul_riemannZeta.congr' hev)

private lemma riemannZeta₁_ne_zero_at_one : riemannZeta₁ 1 ≠ 0 := by
  rw [riemannZeta₁_one_eq]
  exact one_ne_zero

private lemma riemannZetaInv_analyticAt_one : AnalyticAt ℂ riemannZetaInv 1 := by
  have hev_ne : ∀ᶠ z in 𝓝 (1 : ℂ), riemannZeta₁ z ≠ 0 :=
    differentiable_riemannZeta₁_bridge.continuous.continuousAt.eventually_ne
      riemannZeta₁_ne_zero_at_one
  have hev : riemannZetaInv =ᶠ[𝓝 (1 : ℂ)] fun z : ℂ ↦ (z - 1) / riemannZeta₁ z := by
    filter_upwards [hev_ne] with z hz_ne
    by_cases hz1 : z = 1
    · subst hz1; simp [riemannZetaInv]
    · rw [riemannZetaInv_eq_inv_of_ne_one hz1, riemannZeta_eq_inv_sub_mul hz1,
        mul_inv, inv_inv, mul_comm, div_eq_mul_inv]
      ring
  have han_num : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) 1 :=
    (differentiable_id.sub_const (1 : ℂ)).analyticAt 1
  have han_den : AnalyticAt ℂ riemannZeta₁ 1 := differentiable_riemannZeta₁_bridge.analyticAt 1
  exact (han_num.div han_den riemannZeta₁_ne_zero_at_one).congr hev.symm

private lemma riemannZeta₁_not_identically_zero (s : ℂ) :
    ¬ (riemannZeta₁ =ᶠ[𝓝 s] 0) := by
  intro hev
  have heq := (differentiable_riemannZeta₁_bridge.differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s) hev (Set.mem_univ (1 : ℂ))
  exact riemannZeta₁_ne_zero_at_one heq

private lemma riemannZeta_eventually_ne_zero_nhdsWithin {s : ℂ} (hs1 : s ≠ 1) :
    ∀ᶠ z in 𝓝[≠] s, z ≠ 1 ∧ riemannZeta z ≠ 0 := by
  have han_z : AnalyticAt ℂ riemannZeta s :=
    (DifferentiableOn.analyticOnNhd
      (fun w hw ↦ (differentiableAt_riemannZeta hw).differentiableWithinAt) isOpen_ne) s hs1
  have hnot : ¬ (riemannZeta =ᶠ[𝓝 s] 0) := by
    intro h0
    apply riemannZeta₁_not_identically_zero s
    filter_upwards [h0, (isOpen_ne (x := (1 : ℂ))).mem_nhds hs1] with z hz hz1
    rw [riemannZeta_eq_inv_sub_mul hz1] at hz
    have hinv : (z - 1)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hz1)
    exact (mul_eq_zero.mp hz).resolve_left hinv
  have hne_zero := han_z.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  have hne1 : ∀ᶠ z in 𝓝[≠] s, z ≠ 1 :=
    nhdsWithin_le_nhds ((isOpen_ne (x := (1 : ℂ))).mem_nhds hs1)
  exact hne1.and hne_zero

/-- **Analytic reciprocal characterization**: `RiemannHypothesisProp` holds if and only if
`riemannZetaInv` is analytic on the half-plane `{s : ℂ | 1 / 2 < s.re}`. -/
theorem riemannHypothesisProp_iff_analyticOnNhd_riemannZetaInv :
    RiemannHypothesisProp ↔ AnalyticOnNhd ℂ riemannZetaInv {s : ℂ | 1 / 2 < s.re} := by
  constructor
  · intro hRH s hs
    rcases eq_or_ne s 1 with rfl | hs1
    · exact riemannZetaInv_analyticAt_one
    · have hs_re : 1 / 2 < s.re := hs
      have hzeta_ne : riemannZeta s ≠ 0 :=
        (riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH) s hs_re
      have hU_open : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z ≠ 1} :=
        (isOpen_lt (continuous_const (y := (1 / 2 : ℝ))) Complex.continuous_re).inter
          (isOpen_ne (x := (1 : ℂ)))
      have han_z : AnalyticAt ℂ riemannZeta s :=
        (DifferentiableOn.analyticOnNhd
          (fun w hw ↦ (differentiableAt_riemannZeta hw).differentiableWithinAt) isOpen_ne) s hs1
      have han_inv : AnalyticAt ℂ (fun z : ℂ ↦ (riemannZeta z)⁻¹) s := han_z.inv hzeta_ne
      have hev : (fun z : ℂ ↦ (riemannZeta z)⁻¹) =ᶠ[𝓝 s] riemannZetaInv := by
        filter_upwards [hU_open.mem_nhds ⟨hs_re, hs1⟩] with z hz
        exact (riemannZetaInv_eq_inv_of_ne_one hz.2).symm
      exact han_inv.congr hev
  · intro han
    rw [riemannHypothesisProp_iff_ne_zero_of_half_lt_re]
    intro s hs_re hs_zero
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [h] at hs_zero
      exact riemannZeta_ne_zero_of_one_le_re_bridge (le_refl 1) hs_zero
    have hcont_z : ContinuousAt riemannZeta s :=
      (differentiableAt_riemannZeta hs1).continuousAt
    have hcont_inv : ContinuousAt riemannZetaInv s := (han s hs_re).continuousAt
    have htend0 : Tendsto (fun z : ℂ ↦ riemannZeta z * riemannZetaInv z) (𝓝[≠] s) (𝓝 0) := by
      have hm : Tendsto (fun z : ℂ ↦ riemannZeta z * riemannZetaInv z)
          (𝓝[≠] s) (𝓝 (riemannZeta s * riemannZetaInv s)) :=
        (hcont_z.mul hcont_inv).tendsto.mono_left (nhdsWithin_le_nhds (s := ({s}ᶜ : Set ℂ)))
      simpa [hs_zero] using hm
    have hev1 : ∀ᶠ z in 𝓝[≠] s, riemannZeta z * riemannZetaInv z = 1 := by
      filter_upwards [riemannZeta_eventually_ne_zero_nhdsWithin hs1] with z ⟨hz1, hz_ne⟩
      rw [riemannZetaInv_eq_inv_of_ne_one hz1, mul_inv_cancel₀ hz_ne]
    have htend1 : Tendsto (fun z : ℂ ↦ riemannZeta z * riemannZetaInv z) (𝓝[≠] s) (𝓝 1) :=
      tendsto_const_nhds.congr' (hev1.mono fun _ hz ↦ hz.symm)
    exact one_ne_zero (tendsto_nhds_unique htend1 htend0)

end ReciprocalAnalyticity

/-! ### Hadamard's Three-Circles Theorem and Conditional Growth Bounds -/

section ThreeCirclesAndConditionalBounds

private lemma log_le_inv_eps_mul_rpow_local {ε u : ℝ} (hε : 0 < ε) (hu : 1 ≤ u) :
    Real.log u ≤ (1 / ε) * u ^ ε := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hpow_pos : 0 < u ^ ε := Real.rpow_pos_of_pos hu_pos ε
  have hlog_pow : Real.log (u ^ ε) = ε * Real.log u := Real.log_rpow hu_pos ε
  have hle : Real.log (u ^ ε) ≤ u ^ ε - 1 := Real.log_le_sub_one_of_pos hpow_pos
  have hle' : ε * Real.log u ≤ u ^ ε := by linarith
  calc
    Real.log u = (ε * Real.log u) / ε := by field_simp [hε.ne']
    _ ≤ u ^ ε / ε := div_le_div_of_nonneg_right hle' hε.le
    _ = (1 / ε) * u ^ ε := by ring

private lemma rpow_le_eps_mul_add_const {θ ε C : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → C * u ^ θ ≤ ε * u + K := by
  let U : ℝ := (C / ε) ^ (1 / (1 - θ)) + 1
  have hU_nonneg : 0 ≤ U := by positivity
  let K : ℝ := C * U ^ θ
  have hK_nonneg : 0 ≤ K := by positivity
  refine ⟨K, hK_nonneg, fun u hu ↦ ?_⟩
  rcases le_total u U with hu_le | hu_ge
  · have hpow : u ^ θ ≤ U ^ θ := Real.rpow_le_rpow hu hu_le hθ0.le
    have h1 : C * u ^ θ ≤ K := mul_le_mul_of_nonneg_left hpow hC
    linarith [mul_nonneg hε.le hu]
  · have hU_pos : 0 < U := by positivity
    have hu_pos : 0 < u := lt_of_lt_of_le hU_pos hu_ge
    have h1_θ : 0 < 1 - θ := sub_pos.mpr hθ1
    have hC_div_le : C / ε ≤ u ^ (1 - θ) := by
      rcases eq_or_lt_of_le hC with rfl | _
      · simp only [zero_div]
        exact Real.rpow_nonneg hu _
      · have hle_u : (C / ε) ^ (1 / (1 - θ)) ≤ u := by linarith
        have hpow := Real.rpow_le_rpow (by positivity) hle_u h1_θ.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel h1_θ.ne', Real.rpow_one] at hpow
    have hCu : C ≤ ε * u ^ (1 - θ) := by
      rw [mul_comm]
      exact (div_le_iff₀ hε).mp hC_div_le
    have hmul : C * u ^ θ ≤ (ε * u ^ (1 - θ)) * u ^ θ :=
      mul_le_mul_of_nonneg_right hCu (Real.rpow_nonneg hu θ)
    have hadd : u ^ (1 - θ) * u ^ θ = u := by
      rw [← Real.rpow_add hu_pos, sub_add_cancel, Real.rpow_one]
    rw [mul_assoc, hadd] at hmul
    linarith

/-- **Hadamard's Three-Circles Theorem** on an annulus `{w : ℂ | r₁ ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ r₃}`
for a holomorphic function on `Metric.ball z₀ R` (`0 < r₁ < r₃ < R`). -/
theorem hadamard_three_circles_annulus {h : ℂ → ℂ} {z₀ : ℂ} {r₁ r₃ R M₁ M₃ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₃ : r₁ < r₃) (hr₃R : r₃ < R) (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    (hh : DifferentiableOn ℂ h (Metric.ball z₀ R))
    (hbd₁ : ∀ w ∈ Metric.sphere z₀ r₁, ‖h w‖ ≤ M₁)
    (hbd₃ : ∀ w ∈ Metric.sphere z₀ r₃, ‖h w‖ ≤ M₃)
    {w : ℂ} (hw₁ : r₁ ≤ ‖w - z₀‖) (hw₃ : ‖w - z₀‖ ≤ r₃) :
    let θ := Real.log (‖w - z₀‖ / r₁) / Real.log (r₃ / r₁)
    ‖h w‖ ≤ M₁ ^ (1 - θ) * M₃ ^ θ := by
  intro θ
  let σ₁ : ℝ := Real.log r₁
  let σ₂ : ℝ := Real.log r₃
  have hσ₁₂ : σ₁ < σ₂ := Real.log_lt_log hr₁ hr₁₃
  have hden_pos : 0 < σ₂ - σ₁ := sub_pos.mpr hσ₁₂
  let k : ℝ := (Real.log M₃ - Real.log M₁) / (σ₂ - σ₁)
  let b : ℝ := (σ₂ * Real.log M₁ - σ₁ * Real.log M₃) / (σ₂ - σ₁)
  have hk_left : k * σ₁ + b = Real.log M₁ := by
    dsimp only [k, b]
    field_simp [hden_pos.ne']
    ring
  have hk_right : k * σ₂ + b = Real.log M₃ := by
    dsimp only [k, b]
    field_simp [hden_pos.ne']
    ring
  let G : ℂ → ℂ := fun s ↦ h (z₀ + Complex.exp s) * Complex.exp (-((k : ℂ) * s + (b : ℂ)))
  have hmap_ball : ∀ s ∈ verticalStripClosed σ₁ σ₂, z₀ + Complex.exp s ∈ Metric.ball z₀ R := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact lt_of_le_of_lt
      (by simpa [σ₂, Real.exp_log (lt_trans hr₁ hr₁₃)] using Real.exp_le_exp.mpr hs.2)
      hr₃R
  have hG_diff_closed : DifferentiableOn ℂ G (verticalStripClosed σ₁ σ₂) := by
    intro s hs
    have hball : z₀ + Complex.exp s ∈ Metric.ball z₀ R := hmap_ball s hs
    have hh_at : DifferentiableAt ℂ h (z₀ + Complex.exp s) :=
      hh.differentiableAt (Metric.isOpen_ball.mem_nhds hball)
    have hexp_at : DifferentiableAt ℂ (fun u : ℂ ↦ z₀ + Complex.exp u) s :=
      (Complex.differentiable_exp s).const_add z₀
    have h1 : DifferentiableAt ℂ (fun u : ℂ ↦ h (z₀ + Complex.exp u)) s := hh_at.comp s hexp_at
    have h2 : DifferentiableAt ℂ (fun u : ℂ ↦ Complex.exp (-((k : ℂ) * u + (b : ℂ)))) s :=
      ((differentiableAt_id.const_mul (k : ℂ)).add_const (b : ℂ)).neg.cexp
    exact (h1.mul h2).differentiableWithinAt
  have hG_diffCont : DiffContOnCl ℂ G (verticalStripOpen σ₁ σ₂) := by
    have hsub : closure (verticalStripOpen σ₁ σ₂) ⊆ verticalStripClosed σ₁ σ₂ :=
      (isClosed_Icc.preimage Complex.continuous_re).closure_subset_iff.mpr
        (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩)
    exact ⟨hG_diff_closed.mono (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩),
      hG_diff_closed.continuousOn.mono hsub⟩
  have hcomp_bd : ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Metric.closedBall z₀ r₃, ‖h u‖ ≤ K := by
    have hsub : Metric.closedBall z₀ r₃ ⊆ Metric.ball z₀ R := Metric.closedBall_subset_ball hr₃R
    obtain ⟨u, _, hu_max⟩ := (isCompact_closedBall z₀ r₃).exists_isMaxOn
      (Metric.nonempty_closedBall.mpr (lt_trans hr₁ hr₁₃).le)
      (hh.continuousOn.norm.mono hsub)
    exact ⟨‖h u‖, norm_nonneg _, fun v hv ↦ hu_max hv⟩
  obtain ⟨K, hK_nn, hK_bd⟩ := hcomp_bd
  let A : ℝ := K * Real.exp (|k| * max |σ₁| |σ₂| + |b|)
  have hA_nn : 0 ≤ A := by positivity
  have hG_strip_bd : ∀ s ∈ verticalStripOpen σ₁ σ₂,
      ‖G s‖ ≤ A * Real.exp (0 * Real.exp (0 * |s.im|)) := by
    intro s hs
    have hs_cl : s ∈ verticalStripClosed σ₁ σ₂ := ⟨hs.1.le, hs.2.le⟩
    have hdist : z₀ + Complex.exp s ∈ Metric.closedBall z₀ r₃ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
      simpa [σ₂, Real.exp_log (lt_trans hr₁ hr₁₃)] using Real.exp_le_exp.mpr hs_cl.2
    have hnorm_h : ‖h (z₀ + Complex.exp s)‖ ≤ K := hK_bd _ hdist
    have hs_abs : |s.re| ≤ max |σ₁| |σ₂| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le σ₁, le_max_left |σ₁| |σ₂|, hs_cl.1],
        by linarith [le_abs_self σ₂, le_max_right |σ₁| |σ₂|, hs_cl.2]⟩
    have hexp_bd : ‖Complex.exp (-((k : ℂ) * s + (b : ℂ)))‖ ≤
        Real.exp (|k| * max |σ₁| |σ₂| + |b|) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (-((k : ℂ) * s + (b : ℂ))).re = -(k * s.re + b) := by simp
      rw [hre]
      calc
        -(k * s.re + b) ≤ |k * s.re + b| := neg_le_abs _
        _ ≤ |k * s.re| + |b| := abs_add_le _ _
        _ = |k| * |s.re| + |b| := by rw [abs_mul]
        _ ≤ |k| * max |σ₁| |σ₂| + |b| := by gcongr
    have hmul := mul_le_mul hnorm_h hexp_bd (norm_nonneg _) hK_nn
    simpa [G, A] using hmul
  have hline₁ : ∀ t : ℝ, ‖G ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ 1 := by
    intro t
    have hsph : z₀ + Complex.exp ((σ₁ : ℂ) + (t : ℂ) * I) ∈ Metric.sphere z₀ r₁ := by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
      simp [σ₁, Real.exp_log hr₁]
    have hh_le : ‖h (z₀ + Complex.exp ((σ₁ : ℂ) + (t : ℂ) * I))‖ ≤ M₁ := hbd₁ _ hsph
    have hexp_eq : ‖Complex.exp (-((k : ℂ) * ((σ₁ : ℂ) + (t : ℂ) * I) + (b : ℂ)))‖ = M₁⁻¹ := by
      rw [Complex.norm_exp]
      have hre : (-((k : ℂ) * ((σ₁ : ℂ) + (t : ℂ) * I) + (b : ℂ))).re = -(k * σ₁ + b) := by
        simp
      rw [hre, hk_left, Real.exp_neg, Real.exp_log hM₁]
    calc
      ‖G ((σ₁ : ℂ) + (t : ℂ) * I)‖
          = ‖h (z₀ + Complex.exp ((σ₁ : ℂ) + (t : ℂ) * I))‖ *
            ‖Complex.exp (-((k : ℂ) * ((σ₁ : ℂ) + (t : ℂ) * I) + (b : ℂ)))‖ := norm_mul _ _
      _ ≤ M₁ * M₁⁻¹ := by rw [hexp_eq]; exact mul_le_mul_of_nonneg_right hh_le (by positivity)
      _ = 1 := mul_inv_cancel₀ hM₁.ne'
  have hline₂ : ∀ t : ℝ, ‖G ((σ₂ : ℂ) + (t : ℂ) * I)‖ ≤ 1 := by
    intro t
    have hsph : z₀ + Complex.exp ((σ₂ : ℂ) + (t : ℂ) * I) ∈ Metric.sphere z₀ r₃ := by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
      simp [σ₂, Real.exp_log (lt_trans hr₁ hr₁₃)]
    have hh_le : ‖h (z₀ + Complex.exp ((σ₂ : ℂ) + (t : ℂ) * I))‖ ≤ M₃ := hbd₃ _ hsph
    have hexp_eq : ‖Complex.exp (-((k : ℂ) * ((σ₂ : ℂ) + (t : ℂ) * I) + (b : ℂ)))‖ = M₃⁻¹ := by
      rw [Complex.norm_exp]
      have hre : (-((k : ℂ) * ((σ₂ : ℂ) + (t : ℂ) * I) + (b : ℂ))).re = -(k * σ₂ + b) := by
        simp
      rw [hre, hk_right, Real.exp_neg, Real.exp_log hM₃]
    calc
      ‖G ((σ₂ : ℂ) + (t : ℂ) * I)‖
          = ‖h (z₀ + Complex.exp ((σ₂ : ℂ) + (t : ℂ) * I))‖ *
            ‖Complex.exp (-((k : ℂ) * ((σ₂ : ℂ) + (t : ℂ) * I) + (b : ℂ)))‖ := norm_mul _ _
      _ ≤ M₃ * M₃⁻¹ := by rw [hexp_eq]; exact mul_le_mul_of_nonneg_right hh_le (by positivity)
      _ = 1 := mul_inv_cancel₀ hM₃.ne'
  have hpl : ∀ {z : ℂ}, z ∈ verticalStripClosed σ₁ σ₂ → ‖G z‖ ≤ 1 := fun hz ↦
    phragmen_lindelof_vertical_strip_of_exp_le hG_diffCont hA_nn
      (by positivity : (0 : ℝ) < Real.pi / (σ₂ - σ₁)) hG_strip_bd hline₁ hline₂ hz
  let r : ℝ := ‖w - z₀‖
  have hr_pos : 0 < r := lt_of_lt_of_le hr₁ hw₁
  let s₀ : ℂ := (Real.log r : ℂ) + ((w - z₀).arg : ℂ) * I
  have hs₀_mem : s₀ ∈ verticalStripClosed σ₁ σ₂ := by
    refine ⟨?_, ?_⟩
    · simp only [s₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact Real.log_le_log hr₁ hw₁
    · simp only [s₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact Real.log_le_log hr_pos hw₃
  have hexp_s₀ : z₀ + Complex.exp s₀ = w := by
    have hcexp : Complex.exp s₀ = (r : ℂ) * Complex.exp (((w - z₀).arg : ℂ) * I) := by
      rw [show s₀ = (Real.log r : ℂ) + ((w - z₀).arg : ℂ) * I from rfl, Complex.exp_add,
        ← Complex.ofReal_exp, Real.exp_log hr_pos]
    rw [hcexp, Complex.norm_mul_exp_arg_mul_I (w - z₀)]
    ring
  have hGs₀ : ‖G s₀‖ ≤ 1 := hpl hs₀_mem
  have hs₀_re : s₀.re = Real.log r := by simp [s₀]
  have hG_eq : ‖G s₀‖ = ‖h w‖ * Real.exp (-(k * Real.log r + b)) := by
    dsimp only [G]
    rw [hexp_s₀, norm_mul, Complex.norm_exp]
    have hre : (-((k : ℂ) * s₀ + (b : ℂ))).re = -(k * Real.log r + b) := by
      simp [hs₀_re]
    rw [hre]
  have hnorm_hw : ‖h w‖ ≤ Real.exp (k * Real.log r + b) := by
    rw [hG_eq, Real.exp_neg, ← div_eq_mul_inv] at hGs₀
    have hexp_pos : 0 < Real.exp (k * Real.log r + b) := Real.exp_pos _
    exact (div_le_one hexp_pos).mp hGs₀
  have hlin_eq : k * Real.log r + b = (1 - θ) * Real.log M₁ + θ * Real.log M₃ := by
    have hθ_eq : θ = (Real.log r - σ₁) / (σ₂ - σ₁) := by
      dsimp only [θ, σ₁, σ₂, r]
      rw [Real.log_div hr_pos.ne' hr₁.ne', Real.log_div (lt_trans hr₁ hr₁₃).ne' hr₁.ne']
    rw [hθ_eq]
    dsimp only [k, b]
    field_simp [hden_pos.ne']
    ring
  rw [hlin_eq, Real.exp_add, mul_comm (1 - θ) (Real.log M₁), mul_comm θ (Real.log M₃),
    ← Real.rpow_def_of_pos hM₁, ← Real.rpow_def_of_pos hM₃] at hnorm_hw
  exact hnorm_hw

/-- **Conditional uniform Littlewood/Lindelöf bounds** on `ζ(s)` and `ζ(s)⁻¹` in the half-plane
`Re s ≥ σ₀ > 1 / 2` under `RiemannHypothesisProp`. -/
theorem riemannZeta_and_inv_bounds_of_riemannHypothesisProp (hRH : RiemannHypothesisProp)
    {σ₀ ε : ℝ} (hσ₀ : 1 / 2 < σ₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, σ₀ ≤ σ → 4 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ ε ∧
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖⁻¹ ≤ C * (|t| + 2) ^ ε := by
  let δ : ℝ := min (σ₀ - 1 / 2) (1 / 2) / 2
  have hδ_pos : 0 < δ := div_pos (lt_min (sub_pos.mpr hσ₀) (by norm_num)) two_pos
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    dsimp only [δ]
    linarith [min_le_right (σ₀ - 1 / 2) (1 / 2)]
  let r₁ : ℝ := 1 / 2
  let r₃ : ℝ := 3 / 2 - δ
  let R : ℝ := 3 / 2 - δ / 2
  have hr₁_pos : 0 < r₁ := by norm_num
  have hr₁₃ : r₁ < r₃ := by dsimp only [r₁, r₃]; linarith
  have hr₃R : r₃ < R := by dsimp only [r₃, R]; linarith
  have hM₃_pos_den : 0 < Real.log (r₃ / r₁) :=
    Real.log_pos (by rw [one_lt_div hr₁_pos]; exact hr₁₃)
  let r₂_max : ℝ := 3 / 2 - 2 * δ
  have hr₂_max_pos : 0 < r₂_max := by dsimp only [r₂_max]; linarith
  have hr₂_max_lt : r₂_max < r₃ := by dsimp only [r₂_max, r₃]; linarith
  let θ₀ : ℝ := Real.log (r₂_max / r₁) / Real.log (r₃ / r₁)
  have hθ₀_pos : 0 < θ₀ := by
    dsimp only [θ₀]
    refine div_pos (Real.log_pos ?_) hM₃_pos_den
    rw [one_lt_div hr₁_pos]
    dsimp only [r₁, r₂_max]
    linarith [min_le_right (σ₀ - 1 / 2) (1 / 2)]
  have hθ₀_lt1 : θ₀ < 1 := by
    dsimp only [θ₀]
    rw [div_lt_one hM₃_pos_den]
    exact Real.log_lt_log (div_pos hr₂_max_pos hr₁_pos)
      (div_lt_div_of_pos_right hr₂_max_lt hr₁_pos)
  let M₁ : ℝ := max 1 (4 * Real.log 10)
  have hM₁_pos : 0 < M₁ := by positivity
  have hball_coeff : ∃ A_ball : ℝ, 1 ≤ A_ball ∧ ∀ ⦃t : ℝ⦄, 4 ≤ |t| →
      ∀ w ∈ Metric.ball ((2 : ℂ) + (t : ℂ) * I) R,
        Real.log ‖riemannZeta w‖ - Real.log ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖ ≤
          A_ball * Real.log (|t| + 2) := by
    obtain ⟨K, _, hKbd⟩ := norm_riemannZeta_critical_strip_le one_pos
    obtain ⟨C₂, _, hbd₂⟩ := norm_riemannZeta_re_ge_one_le
    let K₀ : ℝ := max 1 (max (4 * K) (2 * C₂))
    have hK₀1 : 1 ≤ K₀ := le_max_left _ _
    let A_ball : ℝ := 2 + Real.log (2 * K₀) + 1
    refine ⟨A_ball, by
      have hlog : 0 ≤ Real.log (2 * K₀) := Real.log_nonneg (by linarith)
      linarith, fun t ht w hw ↦ ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_im_diff : |w.im - t| < 3 / 2 := by
      calc
        |w.im - t| = |(w - ((2 : ℂ) + (t : ℂ) * I)).im| := by simp
        _ ≤ ‖w - ((2 : ℂ) + (t : ℂ) * I)‖ := Complex.abs_im_le_norm _
        _ < R := hw
        _ < 3 / 2 := by dsimp only [R]; linarith
    have hw_im_abs : 2 ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub t w.im
      rw [abs_sub_comm] at this
      linarith
    have hw_im_add : |w.im| + 2 ≤ 2 * (|t| + 2) := by
      have := abs_sub_abs_le_abs_sub w.im t
      linarith [abs_nonneg t]
    have hw_re_pos : 1 / 2 < w.re := by
      have hre : 2 - w.re ≤ ‖w - ((2 : ℂ) + (t : ℂ) * I)‖ := by
        have := Complex.abs_re_le_norm (w - ((2 : ℂ) + (t : ℂ) * I))
        have hsub : (w - ((2 : ℂ) + (t : ℂ) * I)).re = w.re - 2 := by simp
        rw [hsub] at this
        linarith [neg_le_abs (w.re - 2)]
      dsimp only [R] at hw
      linarith
    have hK₀_bd : ‖riemannZeta w‖ ≤ K₀ * (|t| + 2) ^ (2 : ℝ) := by
      rw [(Complex.re_add_im w).symm]
      rcases le_or_gt w.re 1 with hw_le1 | hw_gt1
      · have hstrip := hKbd (⟨by linarith [hw_re_pos], hw_le1⟩ : w.re ∈ Set.Icc (0 : ℝ) 1)
          (by linarith)
        have ht2_ge1 : (1 : ℝ) ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
        have hpow_le : (|w.im| + 2) ^ ((1 - w.re) / 2 + 1) ≤ (|w.im| + 2) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht2_ge1 (by linarith)
        calc
          ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
              ≤ K * (|w.im| + 2) ^ ((1 - w.re) / 2 + 1) := hstrip
          _ ≤ K * (|w.im| + 2) ^ (2 : ℝ) :=
              mul_le_mul_of_nonneg_left hpow_le (by positivity)
          _ ≤ K * (2 * (|t| + 2)) ^ (2 : ℝ) := by gcongr
          _ = (4 * K) * (|t| + 2) ^ (2 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]
            norm_num; ring
          _ ≤ K₀ * (|t| + 2) ^ (2 : ℝ) := by
            gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
      · have hge1 := hbd₂ hw_gt1.le hw_im_abs
        have hlog_le : Real.log (|w.im| + 2) ≤ |w.im| + 2 :=
          (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        have ht_ge1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        have hpow12 : (|t| + 2) ^ (1 : ℝ) ≤ (|t| + 2) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht_ge1 (by norm_num)
        calc
          ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
              ≤ C₂ * Real.log (|w.im| + 2) := hge1
          _ ≤ C₂ * (|w.im| + 2) := by gcongr
          _ ≤ C₂ * (2 * (|t| + 2)) := by gcongr
          _ = (2 * C₂) * (|t| + 2) ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
          _ ≤ (2 * C₂) * (|t| + 2) ^ (2 : ℝ) :=
              mul_le_mul_of_nonneg_left hpow12 (by positivity)
          _ ≤ K₀ * (|t| + 2) ^ (2 : ℝ) := by
            gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
    have hzw_ne : riemannZeta w ≠ 0 :=
      (riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH) w hw_re_pos
    have hz0_inv_le : ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖⁻¹ ≤ 2 := by
      have h := inv_norm_riemannZeta_le_of_one_lt_re (by norm_num : (1 : ℝ) < 2) t
      norm_num at h
      exact h
    have hz0_pos : 0 < ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simp))
    have hlog_sub : Real.log ‖riemannZeta w‖ - Real.log ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖ =
        Real.log (‖riemannZeta w‖ * ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖⁻¹) := by
      rw [Real.log_mul (norm_pos_iff.mpr hzw_ne).ne' (inv_ne_zero hz0_pos.ne'), Real.log_inv]
      ring
    have hprod_le : ‖riemannZeta w‖ * ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖⁻¹ ≤
        (2 * K₀) * (|t| + 2) ^ (2 : ℝ) := by
      calc
        ‖riemannZeta w‖ * ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖⁻¹
            ≤ (K₀ * (|t| + 2) ^ (2 : ℝ)) * 2 :=
              mul_le_mul hK₀_bd hz0_inv_le (by positivity) (by positivity)
        _ = (2 * K₀) * (|t| + 2) ^ (2 : ℝ) := by ring
    have hlog_t_ge1 : 1 ≤ Real.log (|t| + 2) := by
      have hexp1 : Real.exp 1 ≤ |t| + 2 := (Real.exp_one_lt_d9.le).trans (by linarith)
      simpa using Real.log_le_log (Real.exp_pos 1) hexp1
    calc
      Real.log ‖riemannZeta w‖ - Real.log ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖
          = Real.log (‖riemannZeta w‖ * ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖⁻¹) := hlog_sub
      _ ≤ Real.log ((2 * K₀) * (|t| + 2) ^ (2 : ℝ)) :=
        Real.log_le_log (mul_pos (norm_pos_iff.mpr hzw_ne) (inv_pos.mpr hz0_pos)) hprod_le
      _ = Real.log (2 * K₀) + 2 * Real.log (|t| + 2) := by
        rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow (by positivity)]
      _ ≤ Real.log (2 * K₀) * Real.log (|t| + 2) + 2 * Real.log (|t| + 2) := by
        gcongr
        exact le_mul_of_one_le_right (Real.log_nonneg (by linarith)) hlog_t_ge1
      _ ≤ A_ball * Real.log (|t| + 2) := by
        have heq : (2 + Real.log (2 * K₀)) * Real.log (|t| + 2) ≤
            A_ball * Real.log (|t| + 2) := by
          gcongr; dsimp only [A_ball]; linarith
        linarith
  obtain ⟨A_ball, hA_ball1, hball_bd⟩ := hball_coeff
  let C₃ : ℝ := (2 * r₃ / (R - r₃)) * A_ball + M₁
  have hC₃_pos : 0 < C₃ := by
    have : 0 < 2 * r₃ / (R - r₃) := div_pos (by linarith) (sub_pos.mpr hr₃R)
    positivity
  let C_pre : ℝ := M₁ ^ (1 - θ₀) * C₃ ^ θ₀
  have hC_pre_nn : 0 ≤ C_pre := by positivity
  obtain ⟨K_ε, _, hK_ε_bd⟩ := rpow_le_eps_mul_add_const hθ₀_pos hθ₀_lt1 hε hC_pre_nn
  let C : ℝ := max 5 (2 * Real.exp K_ε)
  refine ⟨C, by positivity, fun σ t hσ ht ↦ ?_⟩
  have ht2_ge1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hpow_ge1 : 1 ≤ (|t| + 2) ^ ε := Real.one_le_rpow ht2_ge1 hε.le
  rcases le_or_gt (5 / 4 : ℝ) σ with hσ_large | hσ_mid
  · have h_bd : σ / (σ - 1) ≤ 5 := by
      have hden : (0 : ℝ) < σ - 1 := by linarith
      rw [div_le_iff₀ hden]
      linarith
    have hσ1 : 1 < σ := by linarith
    have hz := (norm_riemannZeta_le_of_one_lt_re hσ1 t).trans h_bd
    have hinv := (inv_norm_riemannZeta_le_of_one_lt_re hσ1 t).trans h_bd
    have h5C : (5 : ℝ) ≤ C * (|t| + 2) ^ ε := by
      calc
        (5 : ℝ) = 5 * 1 := (mul_one _).symm
        _ ≤ C * (|t| + 2) ^ ε := mul_le_mul (le_max_left _ _) hpow_ge1 zero_le_one (by positivity)
    exact ⟨hz.trans h5C, hinv.trans h5C⟩
  · let z₀ : ℂ := (2 : ℂ) + (t : ℂ) * I
    have hball_ne : ∀ w ∈ Metric.ball z₀ R, riemannZeta w ≠ 0 := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hre : 1 / 2 < w.re := by
        have h1 : 2 - w.re ≤ ‖w - z₀‖ := by
          have := Complex.abs_re_le_norm (w - z₀)
          have hsub : (w - z₀).re = w.re - 2 := by simp [z₀]
          rw [hsub] at this
          linarith [neg_le_abs (w.re - 2)]
        dsimp only [R] at hw
        linarith
      exact (riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH) w hre
    have hball_diff : DifferentiableOn ℂ riemannZeta (Metric.ball z₀ R) := by
      intro w hw
      have hw1 : w ≠ 1 := fun h ↦ by
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have him : |t| ≤ ‖(1 : ℂ) - z₀‖ := by
          simpa [z₀] using Complex.abs_im_le_norm ((1 : ℂ) - z₀)
        rw [h] at hw
        have hR_lt : R < 3 / 2 := by dsimp only [R]; linarith
        linarith
      exact (differentiableAt_riemannZeta hw1).differentiableWithinAt
    obtain ⟨h, hh_diff, hh_z₀, hh_exp, _⟩ :=
      exists_holomorphic_log_on_ball (lt_trans (lt_trans hr₁_pos hr₁₃) hr₃R) hball_diff hball_ne
    have hlog_t_ge1 : 1 ≤ Real.log (|t| + 2) := by
      have hexp1 : Real.exp 1 ≤ |t| + 2 := (Real.exp_one_lt_d9.le).trans (by linarith)
      simpa using Real.log_le_log (Real.exp_pos 1) hexp1
    have hh_re_eq : ∀ w ∈ Metric.ball z₀ R,
        (h w).re = Real.log ‖riemannZeta w‖ - Real.log ‖riemannZeta z₀‖ := by
      intro w hw
      have hexp := congrArg norm (hh_exp w hw)
      rw [Complex.norm_exp, norm_div] at hexp
      have hzw := hball_ne w hw
      have hz0 := hball_ne z₀ (Metric.mem_ball_self (lt_trans (lt_trans hr₁_pos hr₁₃) hr₃R))
      have hlog := congrArg Real.log hexp
      rw [Real.log_exp, Real.log_div (norm_pos_iff.mpr hzw).ne' (norm_pos_iff.mpr hz0).ne'] at hlog
      exact hlog
    have hbd_M₁ : ∀ w ∈ Metric.sphere z₀ r₁, ‖h w‖ ≤ M₁ := by
      intro w hw
      have hh_sub : DifferentiableOn ℂ h (Metric.ball z₀ (3 / 4 : ℝ)) :=
        hh_diff.mono (Metric.ball_subset_ball (by dsimp only [R]; linarith))
      have hre_inner : ∀ u ∈ Metric.ball z₀ (3 / 4 : ℝ), (h u).re ≤ Real.log 10 := by
        intro u hu
        rw [hh_re_eq u (Metric.ball_subset_ball (by dsimp only [R]; linarith) hu)]
        rw [Metric.mem_ball, dist_eq_norm] at hu
        have hu_re : 5 / 4 < u.re := by
          have := Complex.abs_re_le_norm (u - z₀)
          have hsub : (u - z₀).re = u.re - 2 := by simp [z₀]
          rw [hsub] at this
          linarith [neg_le_abs (u.re - 2)]
        have hzu_bd : ‖riemannZeta u‖ ≤ 5 := by
          rw [(Complex.re_add_im u).symm]
          refine (norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < u.re) u.im).trans ?_
          rw [div_le_iff₀ (by linarith)]
          linarith
        have hz0_inv_le : ‖riemannZeta z₀‖⁻¹ ≤ 2 := by
          have h := inv_norm_riemannZeta_le_of_one_lt_re (by norm_num : (1 : ℝ) < 2) t
          norm_num at h
          exact h
        have hzu_ne := hball_ne u
          (Metric.ball_subset_ball (show (3 / 4 : ℝ) ≤ R by dsimp only [R]; linarith)
            (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hu)))
        have hz0_ne := hball_ne z₀ (Metric.mem_ball_self (lt_trans (lt_trans hr₁_pos hr₁₃) hr₃R))
        have hsub : Real.log ‖riemannZeta u‖ - Real.log ‖riemannZeta z₀‖ =
            Real.log (‖riemannZeta u‖ * ‖riemannZeta z₀‖⁻¹) := by
          rw [Real.log_mul (norm_pos_iff.mpr hzu_ne).ne' (inv_ne_zero (norm_pos_iff.mpr hz0_ne).ne'),
            Real.log_inv]
          ring
        rw [hsub]
        exact Real.log_le_log (mul_pos (norm_pos_iff.mpr hzu_ne)
          (inv_pos.mpr (norm_pos_iff.mpr hz0_ne)))
          (by calc ‖riemannZeta u‖ * ‖riemannZeta z₀‖⁻¹ ≤ 5 * 2 :=
                mul_le_mul hzu_bd hz0_inv_le (by positivity) (by norm_num)
            _ = 10 := by norm_num)
      have hbc := borel_caratheodory_on_closedBall (r := r₁) (R := (3 / 4 : ℝ)) (M := Real.log 10)
        hr₁_pos.le (by norm_num : r₁ < 3 / 4) (Real.log_nonneg (by norm_num)) hh_sub hre_inner
        (Metric.sphere_subset_closedBall hw)
      rw [hh_z₀, norm_zero, mul_zero, add_zero] at hbc
      have hcoef : 2 * r₁ / (3 / 4 - r₁) = 4 := by dsimp only [r₁]; norm_num
      rw [hcoef] at hbc
      exact hbc.trans (le_max_right _ _)
    let M₃ : ℝ := C₃ * Real.log (|t| + 2)
    have hM₃_pos : 0 < M₃ := mul_pos hC₃_pos (by linarith)
    have hM₁_le_M₃ : M₁ ≤ M₃ := by
      have hA_nn : 0 ≤ 2 * r₃ / (R - r₃) * A_ball := by
        have := div_pos (by linarith : 0 < 2 * r₃) (sub_pos.mpr hr₃R)
        positivity
      have h1 : M₁ ≤ C₃ := by dsimp only [C₃]; linarith
      calc
        M₁ ≤ C₃ := h1
        _ = C₃ * 1 := (mul_one _).symm
        _ ≤ C₃ * Real.log (|t| + 2) := mul_le_mul_of_nonneg_left hlog_t_ge1 hC₃_pos.le
    have hbd_M₃ : ∀ w ∈ Metric.sphere z₀ r₃, ‖h w‖ ≤ M₃ := by
      intro w hw
      have hre_outer : ∀ u ∈ Metric.ball z₀ R, (h u).re ≤ A_ball * Real.log (|t| + 2) := by
        intro u hu
        rw [hh_re_eq u hu]
        exact hball_bd ht u hu
      have hbc := borel_caratheodory_on_closedBall (r := r₃) (R := R)
        (M := A_ball * Real.log (|t| + 2)) (by linarith) hr₃R (by positivity)
        hh_diff hre_outer (Metric.sphere_subset_closedBall hw)
      rw [hh_z₀, norm_zero, mul_zero, add_zero] at hbc
      have hle : 2 * r₃ / (R - r₃) * (A_ball * Real.log (|t| + 2)) ≤ M₃ := by
        dsimp only [M₃, C₃]
        have hM₁_nn : 0 ≤ M₁ * Real.log (|t| + 2) := mul_nonneg hM₁_pos.le (by linarith)
        linarith [show (2 * r₃ / (R - r₃) * A_ball + M₁) * Real.log (|t| + 2) =
          2 * r₃ / (R - r₃) * (A_ball * Real.log (|t| + 2)) + M₁ * Real.log (|t| + 2) by ring]
      exact hbc.trans hle
    let w : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hw_dist : ‖w - z₀‖ = 2 - σ := by
      have hsub : w - z₀ = ((σ - 2 : ℝ) : ℂ) := by
        dsimp only [w, z₀]
        push_cast
        ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hw₁ : r₁ ≤ ‖w - z₀‖ := by rw [hw_dist]; dsimp only [r₁]; linarith
    have hw_le_max : ‖w - z₀‖ ≤ r₂_max := by
      rw [hw_dist]
      dsimp only [r₂_max, δ]
      linarith [min_le_left (σ₀ - 1 / 2) (1 / 2)]
    have hw₃ : ‖w - z₀‖ ≤ r₃ := hw_le_max.trans hr₂_max_lt.le
    have hw_ball : w ∈ Metric.ball z₀ R := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw₃.trans_lt hr₃R
    have h3c := hadamard_three_circles_annulus hr₁_pos hr₁₃ hr₃R hM₁_pos hM₃_pos hh_diff hbd_M₁ hbd_M₃
      hw₁ hw₃
    let θ : ℝ := Real.log (‖w - z₀‖ / r₁) / Real.log (r₃ / r₁)
    have hθ_le : θ ≤ θ₀ := by
      dsimp only [θ, θ₀]
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (div_pos (lt_of_lt_of_le hr₁_pos hw₁) hr₁_pos)
          (div_le_div_of_nonneg_right hw_le_max hr₁_pos.le))
        hM₃_pos_den.le
    have hratio_ge1 : 1 ≤ M₃ / M₁ := (one_le_div hM₁_pos).mpr hM₁_le_M₃
    have hpow_le : M₁ ^ (1 - θ) * M₃ ^ θ ≤ C_pre * (Real.log (|t| + 2)) ^ θ₀ := by
      have hrewrite1 : M₁ ^ (1 - θ) * M₃ ^ θ = M₁ * (M₃ / M₁) ^ θ := by
        rw [Real.rpow_sub hM₁_pos, Real.rpow_one, Real.div_rpow hM₃_pos.le hM₁_pos.le]
        have hM₁_θ_ne : M₁ ^ θ ≠ 0 := (Real.rpow_pos_of_pos hM₁_pos θ).ne'
        field_simp [hM₁_θ_ne]
      have hrewrite2 : M₁ * (M₃ / M₁) ^ θ₀ = C_pre * (Real.log (|t| + 2)) ^ θ₀ := by
        rw [Real.div_rpow hM₃_pos.le hM₁_pos.le,
          Real.mul_rpow hC₃_pos.le (by linarith : 0 ≤ Real.log (|t| + 2))]
        rw [show C_pre = M₁ ^ (1 - θ₀) * C₃ ^ θ₀ from rfl, Real.rpow_sub hM₁_pos, Real.rpow_one]
        have hM₁_θ₀_ne : M₁ ^ θ₀ ≠ 0 := (Real.rpow_pos_of_pos hM₁_pos θ₀).ne'
        field_simp [hM₁_θ₀_ne]
      calc
        M₁ ^ (1 - θ) * M₃ ^ θ = M₁ * (M₃ / M₁) ^ θ := hrewrite1
        _ ≤ M₁ * (M₃ / M₁) ^ θ₀ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hratio_ge1 hθ_le) hM₁_pos.le
        _ = C_pre * (Real.log (|t| + 2)) ^ θ₀ := hrewrite2
    have hhw_le : ‖h w‖ ≤ ε * Real.log (|t| + 2) + K_ε :=
      h3c.trans (hpow_le.trans (hK_ε_bd (Real.log (|t| + 2)) (by linarith)))
    have hre_abs : |(h w).re| ≤ ε * Real.log (|t| + 2) + K_ε :=
      (Complex.abs_re_le_norm (h w)).trans hhw_le
    rw [abs_le] at hre_abs
    have hre_log := hh_re_eq w hw_ball
    have hz0_bd : ‖riemannZeta z₀‖ ≤ 2 := by
      have h := norm_riemannZeta_le_of_one_lt_re (by norm_num : (1 : ℝ) < 2) t
      norm_num at h
      exact h
    have hz0_inv_bd : ‖riemannZeta z₀‖⁻¹ ≤ 2 := by
      have h := inv_norm_riemannZeta_le_of_one_lt_re (by norm_num : (1 : ℝ) < 2) t
      norm_num at h
      exact h
    have hz0_pos : 0 < ‖riemannZeta z₀‖ := norm_pos_iff.mpr (hball_ne z₀
      (Metric.mem_ball_self (lt_trans (lt_trans hr₁_pos hr₁₃) hr₃R)))
    have hzw_pos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr (hball_ne w hw_ball)
    have hexp_hre : Real.exp (h w).re = ‖riemannZeta w‖ / ‖riemannZeta z₀‖ := by
      rw [hre_log, Real.exp_sub, Real.exp_log hzw_pos, Real.exp_log hz0_pos]
    have hzeta_eq : ‖riemannZeta w‖ = ‖riemannZeta z₀‖ * Real.exp (h w).re := by
      rw [hexp_hre, mul_div_cancel₀ _ hz0_pos.ne']
    have hinv_eq : ‖riemannZeta w‖⁻¹ = ‖riemannZeta z₀‖⁻¹ * Real.exp (-(h w).re) := by
      rw [hzeta_eq, mul_inv, Real.exp_neg]
    have hexp_bound : Real.exp (ε * Real.log (|t| + 2) + K_ε) =
        Real.exp K_ε * (|t| + 2) ^ ε := by
      rw [Real.exp_add, mul_comm ε (Real.log (|t| + 2)),
        ← Real.rpow_def_of_pos (by positivity : 0 < |t| + 2), mul_comm]
    have h2C : 2 * Real.exp K_ε ≤ C := le_max_right _ _
    have hpow_nn : 0 ≤ (|t| + 2) ^ ε := Real.rpow_nonneg (by positivity) _
    constructor
    · calc
        ‖riemannZeta w‖ = ‖riemannZeta z₀‖ * Real.exp (h w).re := hzeta_eq
        _ ≤ 2 * Real.exp (ε * Real.log (|t| + 2) + K_ε) :=
          mul_le_mul hz0_bd (Real.exp_le_exp.mpr hre_abs.2) (Real.exp_pos _).le (by norm_num)
        _ = (2 * Real.exp K_ε) * (|t| + 2) ^ ε := by rw [hexp_bound]; ring
        _ ≤ C * (|t| + 2) ^ ε := mul_le_mul_of_nonneg_right h2C hpow_nn
    · calc
        ‖riemannZeta w‖⁻¹ = ‖riemannZeta z₀‖⁻¹ * Real.exp (-(h w).re) := hinv_eq
        _ ≤ 2 * Real.exp (ε * Real.log (|t| + 2) + K_ε) :=
          mul_le_mul hz0_inv_bd (Real.exp_le_exp.mpr (by linarith [hre_abs.1]))
            (Real.exp_pos _).le (by norm_num)
        _ = (2 * Real.exp K_ε) * (|t| + 2) ^ ε := by rw [hexp_bound]; ring
        _ ≤ C * (|t| + 2) ^ ε := mul_le_mul_of_nonneg_right h2C hpow_nn

/-- Global conditional bound on `‖riemannZetaInv (σ + t * I)‖` valid for all `σ ≥ σ₀ > 1 / 2`
and all `t : ℝ`. -/
theorem riemannZetaInv_bound_of_riemannHypothesisProp (hRH : RiemannHypothesisProp)
    {σ₀ ε : ℝ} (hσ₀ : 1 / 2 < σ₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃σ t : ℝ⦄, σ₀ ≤ σ →
      ‖riemannZetaInv ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ ε := by
  obtain ⟨C₁, hC₁_pos, hbd₁⟩ := riemannZeta_and_inv_bounds_of_riemannHypothesisProp hRH hσ₀ hε
  let K : Set ℂ := Set.Icc σ₀ 2 ×ℂ Set.Icc (-4 : ℝ) 4
  have hK_cpt : IsCompact K := (isCompact_Icc.reProdIm isCompact_Icc)
  have hK_sub : K ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs ↦ by
    have hsre : σ₀ ≤ s.re := hs.1.1
    change (1 / 2 : ℝ) < s.re
    linarith [hσ₀, hsre]
  have hcont : ContinuousOn riemannZetaInv K :=
    ((riemannHypothesisProp_iff_analyticOnNhd_riemannZetaInv.mp hRH).continuousOn).mono hK_sub
  have hK_bd : ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ K, ‖riemannZetaInv s‖ ≤ M := by
    by_cases hne : K.Nonempty
    · obtain ⟨s₀, _, hs₀⟩ := hK_cpt.exists_isMaxOn hne hcont.norm
      exact ⟨‖riemannZetaInv s₀‖, norm_nonneg _, fun s hs ↦ hs₀ hs⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, le_rfl, fun s hs ↦ by simp [hne] at hs⟩
  obtain ⟨M, hM_nn, hM_bd⟩ := hK_bd
  let C : ℝ := max (max C₁ M) 2
  refine ⟨C, by positivity, fun σ t hσ ↦ ?_⟩
  have ht2_ge1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hpow_ge1 : 1 ≤ (|t| + 2) ^ ε := Real.one_le_rpow ht2_ge1 hε.le
  have hpow_nn : 0 ≤ (|t| + 2) ^ ε := Real.rpow_nonneg (by positivity) _
  rcases le_or_gt (2 : ℝ) σ with hσ2 | hσ_lt2
  · have hne1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    rw [riemannZetaInv_eq_inv_of_ne_one hne1, norm_inv]
    have hinv := inv_norm_riemannZeta_le_of_one_lt_re (by linarith : (1 : ℝ) < σ) t
    have h2 : σ / (σ - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖⁻¹ ≤ 2 := hinv.trans h2
      _ ≤ 2 * (|t| + 2) ^ ε := le_mul_of_one_le_right zero_le_two hpow_ge1
      _ ≤ C * (|t| + 2) ^ ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow_nn
  · rcases le_or_gt (4 : ℝ) |t| with ht4 | ht_lt4
    · have hne1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
        have him := congrArg Complex.im h
        simp at him
        rw [him, abs_zero] at ht4
        linarith
      rw [riemannZetaInv_eq_inv_of_ne_one hne1, norm_inv]
      calc
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖⁻¹ ≤ C₁ * (|t| + 2) ^ ε := (hbd₁ hσ ht4).2
        _ ≤ C * (|t| + 2) ^ ε :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hpow_nn
    · have ht_abs : |t| ≤ 4 := ht_lt4.le
      have hsK : (σ : ℂ) + (t : ℂ) * I ∈ K := by
        change ((σ : ℂ) + (t : ℂ) * I).re ∈ Set.Icc σ₀ 2 ∧
          ((σ : ℂ) + (t : ℂ) * I).im ∈ Set.Icc (-4 : ℝ) 4
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add]
        exact ⟨⟨hσ, hσ_lt2.le⟩, abs_le.mp ht_abs⟩
      calc
        ‖riemannZetaInv ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M := hM_bd _ hsK
        _ ≤ M * (|t| + 2) ^ ε := le_mul_of_one_le_right hM_nn hpow_ge1
        _ ≤ C * (|t| + 2) ^ ε :=
          mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hpow_nn

end ThreeCirclesAndConditionalBounds

/-! ### Equivalence with the Mertens Bound and Abscissa of Convergence of `μ` -/

section MertensAndMoebiusAbscissa

/-- The Mertens function `M(x) = ∑_{1 ≤ n ≤ ⌊x⌋} μ(n)`. -/
def mertensM (x : ℝ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.moebius n

private lemma abs_moebius_le_one_real (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  have h : (|(ArithmeticFunction.moebius n : ℤ)| : ℝ) ≤ 1 := by
    exact_mod_cast (by
      rw [ArithmeticFunction.abs_moebius]
      split_ifs <;> norm_num : |ArithmeticFunction.moebius n| ≤ 1)
  simpa only [← Int.cast_abs] using h

private lemma norm_moebius_complex_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact abs_moebius_le_one_real n

private lemma integral_inv_abs_add_two_le {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (-T)..T, (|t| + 2)⁻¹ ≤ 2 * Real.log (T + 2) := by
  have hcont : Continuous (fun t : ℝ ↦ (|t| + 2)⁻¹) :=
    (continuous_abs.add continuous_const).inv₀ fun t ↦ by
      change |t| + 2 ≠ 0
      linarith [abs_nonneg t]
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ (|t| + 2)⁻¹) volume (-T) 0 :=
    hcont.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ (|t| + 2)⁻¹) volume 0 T :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hpos_int : ∫ t in (0 : ℝ)..T, (|t| + 2)⁻¹ ≤ Real.log (T + 2) := by
    have hcongr : ∫ t in (0 : ℝ)..T, (|t| + 2)⁻¹ = ∫ t in (0 : ℝ)..T, (t + 2)⁻¹ := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      rw [abs_of_nonneg ht.1]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun u : ℝ ↦ Real.log (u + 2)) (t + 2)⁻¹ t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have hpos : t + 2 ≠ 0 := by linarith [ht.1]
      simpa using ((hasDerivAt_id t).add_const (2 : ℝ)).log hpos
    have hint2 : IntervalIntegrable (fun t : ℝ ↦ (t + 2)⁻¹) volume 0 T :=
      ((continuousOn_id.add continuousOn_const).inv₀ fun t ht ↦ by
        rw [Set.uIcc_of_le (by linarith)] at ht
        change t + 2 ≠ 0
        linarith [ht.1]).intervalIntegrable
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
    have hlog2 : 0 ≤ Real.log (0 + 2) := Real.log_nonneg (by norm_num)
    linarith
  have hneg_int : ∫ t in (-T)..(0 : ℝ), (|t| + 2)⁻¹ ≤ Real.log (T + 2) := by
    have hcongr : ∫ t in (-T)..(0 : ℝ), (|t| + 2)⁻¹ = ∫ t in (-T)..(0 : ℝ), (2 - t)⁻¹ := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      rw [abs_of_nonpos ht.2, show -t + 2 = 2 - t by ring]
    have hderiv : ∀ t ∈ Set.uIcc (-T) 0,
        HasDerivAt (fun u : ℝ ↦ -Real.log (2 - u)) (2 - t)⁻¹ t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have hpos : 2 - t ≠ 0 := by linarith [ht.2]
      have hd : HasDerivAt (fun u : ℝ ↦ 2 - u) (-1) t :=
        ((hasDerivAt_id t).const_sub (2 : ℝ)).congr_deriv (by ring)
      have hneg := (hd.log hpos).neg
      change HasDerivAt (fun u : ℝ ↦ -Real.log (2 - u)) _ t at hneg
      exact hneg.congr_deriv (by ring)
    have hint2 : IntervalIntegrable (fun t : ℝ ↦ (2 - t)⁻¹) volume (-T) 0 :=
      ((continuousOn_const.sub continuousOn_id).inv₀ fun t ht ↦ by
        rw [Set.uIcc_of_le (by linarith)] at ht
        change 2 - t ≠ 0
        linarith [ht.2]).intervalIntegrable
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have h2T : 2 - (-T) = T + 2 := by ring
    rw [sub_zero, h2T]
    linarith
  linarith

private lemma dirichletContourIntegral_moebius_le (hRH : RiemannHypothesisProp)
    {x δ C_inv : ℝ} (hx : 4 ≤ x) (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 8) (hC_inv_pos : 0 < C_inv)
    (hbd : ∀ ⦃σ t : ℝ⦄, 1 / 2 + δ ≤ σ →
      ‖riemannZetaInv ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C_inv * (|t| + 2) ^ δ) :
    ‖dirichletContourIntegral (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) x
      (1 + δ) (x ^ (3 / 2 : ℝ))‖ ≤
      ((1 / (2 * Real.pi)) * (64 / δ + 4)) * C_inv * x ^ (1 / 2 + 4 * δ) := by
  let c : ℝ := 1 + δ
  let c' : ℝ := 1 / 2 + δ
  let T : ℝ := x ^ (3 / 2 : ℝ)
  have hx_pos : 0 < x := by linarith
  have hc'_gt : 1 / 2 < c' := by dsimp only [c']; linarith
  have hc'_pos : 0 < c' := by dsimp only [c']; linarith
  have hcc' : c' < c := by dsimp only [c', c]; linarith
  have hT_ge4 : 4 ≤ T := by
    have h1 : (4 : ℝ) ≤ x ^ (1 : ℝ) := by simpa using hx
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hT_pos : 0 < T := by linarith
  let a : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  let F : ℂ → ℂ := fun s ↦ riemannZetaInv s * (x : ℂ) ^ s / s
  have hF_diff : DifferentiableOn ℂ F (Set.uIcc c' c ×ℂ Set.uIcc (-T) T) := by
    intro s hs
    have hs_re : c' ≤ s.re := by
      have hmem := hs.1
      rw [Set.uIcc_of_le hcc'.le] at hmem
      exact hmem.1
    have hs_half : 1 / 2 < s.re := lt_of_lt_of_le hc'_gt hs_re
    have hs0 : s ≠ 0 := fun h ↦ by
      rw [h] at hs_half
      simp at hs_half
      linarith
    have hz_at : DifferentiableAt ℂ riemannZetaInv s :=
      ((riemannHypothesisProp_iff_analyticOnNhd_riemannZetaInv.mp hRH) s hs_half).differentiableAt
    have hpow_at : DifferentiableAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ w) s :=
      differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx_pos.ne'))
    exact ((hz_at.mul hpow_at).div differentiableAt_id hs0).differentiableWithinAt
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((c' : ℂ) + (-T : ℂ) * I) ((c : ℂ) + (T : ℂ) * I)
    (by
      convert hF_diff using 2 <;> simp)
  have hre_z : ((c' : ℂ) + (-T : ℂ) * I).re = c' := by simp
  have him_z : ((c' : ℂ) + (-T : ℂ) * I).im = -T := by simp
  have hre_w : ((c : ℂ) + (T : ℂ) * I).re = c := by simp
  have him_w : ((c : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [hre_z, him_z, hre_w, him_w] at hcauchy
  simp only [smul_eq_mul] at hcauchy
  have hright_eq : I * ∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I) =
      I * ∫ t in (-T)..T, LSeries a ((c : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
        ((c : ℂ) + (t : ℂ) * I) := by
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have hre1 : 1 < ((c : ℂ) + (t : ℂ) * I).re := by simp [c, hδ0]
    have hne1 : ((c : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
      have := congrArg Complex.re h
      simp [c] at this
      linarith
    dsimp only [F]
    rw [riemannZetaInv_eq_inv_of_ne_one hne1]
    have hL : LSeries a ((c : ℂ) + (t : ℂ) * I) =
        (riemannZeta ((c : ℂ) + (t : ℂ) * I))⁻¹ := by
      simpa [a] using LSeries_moebius_eq_inv_riemannZeta hre1
    rw [hL]
  have hcontour_eq : dirichletContourIntegral a x c T =
      (1 / (2 * Real.pi * I)) *
        ((I * ∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)) +
          (∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)) -
          (∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I))) := by
    rw [← dirichletContourIntegral_eq_div_two_pi_mul_I, ← hright_eq]
    congr 1
    simp only [Complex.ofReal_neg] at hcauchy
    linear_combination hcauchy
  have hleft_bd : ‖∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)‖ ≤
      (64 / δ) * C_inv * x ^ (1 / 2 + 4 * δ) := by
    have hT2_le : T + 2 ≤ 2 * T := by linarith
    have hT2_pow : (T + 2) ^ δ ≤ 2 * x ^ (3 * δ / 2) := by
      have h1 : (T + 2) ^ δ ≤ (2 * T) ^ δ :=
        Real.rpow_le_rpow (by positivity) hT2_le hδ0.le
      have h2 : (2 : ℝ) ^ δ ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith [hδ_le] : δ ≤ 1)
      have h3 : T ^ δ = x ^ (3 * δ / 2) := by
        dsimp only [T]
        rw [← Real.rpow_mul hx_pos.le, show (3 / 2 : ℝ) * δ = 3 * δ / 2 by ring]
      calc
        (T + 2) ^ δ ≤ (2 * T) ^ δ := h1
        _ = (2 : ℝ) ^ δ * T ^ δ := Real.mul_rpow zero_le_two hT_pos.le
        _ ≤ 2 * x ^ (3 * δ / 2) := by rw [h3]; gcongr
    have hlog_T2 : Real.log (T + 2) ≤ (2 / δ) * x ^ (3 * δ / 2) := by
      have hlog1 : Real.log (T + 2) ≤ (1 / δ) * (T + 2) ^ δ :=
        log_le_inv_eps_mul_rpow_local hδ0 (by linarith)
      calc
        Real.log (T + 2) ≤ (1 / δ) * (T + 2) ^ δ := hlog1
        _ ≤ (1 / δ) * (2 * x ^ (3 * δ / 2)) := by gcongr
        _ = (2 / δ) * x ^ (3 * δ / 2) := by ring
    let B : ℝ := 8 * C_inv * x ^ c' * (T + 2) ^ δ
    have hB_nn : 0 ≤ B := by positivity
    have hpt : ∀ t ∈ Set.Icc (-T) T, ‖F ((c' : ℂ) + (t : ℂ) * I)‖ ≤ B * (|t| + 2)⁻¹ := by
      intro t ht
      have ht_abs : |t| ≤ T := abs_le.mpr ht
      have hzeta : ‖riemannZetaInv ((c' : ℂ) + (t : ℂ) * I)‖ ≤ C_inv * (|t| + 2) ^ δ :=
        hbd le_rfl
      have hpow_abs : (|t| + 2) ^ δ ≤ (T + 2) ^ δ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hδ0.le
      have hcpow : ‖(x : ℂ) ^ ((c' : ℂ) + (t : ℂ) * I)‖ = x ^ c' := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        simp
      have hden_ge : (|t| + 2) / 8 ≤ ‖(c' : ℂ) + (t : ℂ) * I‖ := by
        have him : |t| ≤ ‖(c' : ℂ) + (t : ℂ) * I‖ := by
          simpa using Complex.abs_im_le_norm ((c' : ℂ) + (t : ℂ) * I)
        have hre : 1 / 2 ≤ ‖(c' : ℂ) + (t : ℂ) * I‖ := by
          have hre0 : 1 / 2 ≤ ((c' : ℂ) + (t : ℂ) * I).re := by simp [c']; linarith
          exact hre0.trans (Complex.re_le_norm _)
        linarith
      have hinv_le : ‖(c' : ℂ) + (t : ℂ) * I‖⁻¹ ≤ 8 * (|t| + 2)⁻¹ := by
        have hpos1 : 0 < (|t| + 2) / 8 := by positivity
        have h1 : ‖(c' : ℂ) + (t : ℂ) * I‖⁻¹ ≤ ((|t| + 2) / 8)⁻¹ :=
          inv_anti₀ hpos1 hden_ge
        have h2 : ((|t| + 2) / 8)⁻¹ = 8 * (|t| + 2)⁻¹ := by field_simp
        linarith
      dsimp only [F]
      rw [norm_div, norm_mul, hcpow, div_eq_mul_inv]
      calc
        ‖riemannZetaInv ((c' : ℂ) + (t : ℂ) * I)‖ * x ^ c' * ‖(c' : ℂ) + (t : ℂ) * I‖⁻¹
            ≤ (C_inv * (T + 2) ^ δ) * x ^ c' * (8 * (|t| + 2)⁻¹) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (hzeta.trans (mul_le_mul_of_nonneg_left
                hpow_abs hC_inv_pos.le)) (by positivity)) hinv_le (by positivity) (by positivity)
        _ = B * (|t| + 2)⁻¹ := by dsimp only [B]; ring
    have hF_int : IntervalIntegrable (fun t : ℝ ↦ ‖F ((c' : ℂ) + (t : ℂ) * I)‖)
        volume (-T) T := by
      refine ContinuousOn.intervalIntegrable ?_
      have hre_gt : ∀ t : ℝ, 1 / 2 < ((c' : ℂ) + (t : ℂ) * I).re := fun t ↦ by
        simp [c']; exact hδ0
      have hcont_z : Continuous (fun t : ℝ ↦ riemannZetaInv ((c' : ℂ) + (t : ℂ) * I)) :=
        continuous_iff_continuousAt.mpr fun t ↦
          ((riemannHypothesisProp_iff_analyticOnNhd_riemannZetaInv.mp hRH) _
            (hre_gt t)).continuousAt.comp
            (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      have hcont_p : Continuous (fun t : ℝ ↦ (x : ℂ) ^ ((c' : ℂ) + (t : ℂ) * I)) :=
        continuous_iff_continuousAt.mpr fun t ↦
          (differentiableAt_id.const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr hx_pos.ne'))).continuousAt.comp
            (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      have hcont_d : Continuous (fun t : ℝ ↦ (c' : ℂ) + (t : ℂ) * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hne_d : ∀ t : ℝ, (c' : ℂ) + (t : ℂ) * I ≠ 0 := fun t h ↦ by
        have := congrArg Complex.re h; simp [c'] at this; linarith
      exact ((hcont_z.mul hcont_p).div hcont_d hne_d).norm.continuousOn
    have hB_int : IntervalIntegrable (fun t : ℝ ↦ B * (|t| + 2)⁻¹) volume (-T) T :=
      ((continuous_abs.add continuous_const).inv₀ fun t ↦ by
        change |t| + 2 ≠ 0
        linarith [abs_nonneg t]).const_mul B |>.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hF_int hB_int hpt
    have hint_norm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t : ℝ ↦ F ((c' : ℂ) + (t : ℂ) * I)) (by linarith : -T ≤ T)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hI := integral_inv_abs_add_two_le (by linarith : 1 ≤ T)
    have hpow_le_4 : x ^ c' * x ^ (3 * δ / 2) * x ^ (3 * δ / 2) = x ^ (1 / 2 + 4 * δ) := by
      dsimp only [c']
      rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
      congr 1
      ring
    calc
      ‖∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..T, ‖F ((c' : ℂ) + (t : ℂ) * I)‖ := hint_norm
      _ ≤ B * ∫ t in (-T)..T, (|t| + 2)⁻¹ := hmono
      _ ≤ B * (2 * Real.log (T + 2)) := mul_le_mul_of_nonneg_left hI hB_nn
      _ ≤ (8 * C_inv * x ^ c' * (2 * x ^ (3 * δ / 2))) * (2 * ((2 / δ) * x ^ (3 * δ / 2))) := by
        dsimp only [B]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hT2_pow (by positivity))
          (mul_le_mul_of_nonneg_left hlog_T2 zero_le_two)
          (mul_nonneg zero_le_two (Real.log_nonneg (by linarith))) (by positivity)
      _ = (64 / δ) * C_inv * (x ^ c' * x ^ (3 * δ / 2) * x ^ (3 * δ / 2)) := by ring
      _ = (64 / δ) * C_inv * x ^ (1 / 2 + 4 * δ) := by rw [hpow_le_4]
  have hhoriz_bd : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      ‖∫ σ in c'..c, F ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤ 2 * C_inv * x ^ (1 / 2 + 4 * δ) := by
    intro sgn hsgn
    have hsgn_abs : |sgn * T| = T := by
      rcases hsgn with rfl | rfl <;> simp [abs_of_pos hT_pos]
    have hT2_pow : (T + 2) ^ δ ≤ 2 * x ^ (3 * δ / 2) := by
      have h1 : (T + 2) ^ δ ≤ (2 * T) ^ δ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hδ0.le
      have h2 : (2 : ℝ) ^ δ ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith [hδ_le] : δ ≤ 1)
      have h3 : T ^ δ = x ^ (3 * δ / 2) := by
        dsimp only [T]
        rw [← Real.rpow_mul hx_pos.le, show (3 / 2 : ℝ) * δ = 3 * δ / 2 by ring]
      calc
        (T + 2) ^ δ ≤ (2 * T) ^ δ := h1
        _ = (2 : ℝ) ^ δ * T ^ δ := Real.mul_rpow zero_le_two hT_pos.le
        _ ≤ 2 * x ^ (3 * δ / 2) := by rw [h3]; gcongr
    have hpt : ∀ σ ∈ Set.uIoc c' c,
        ‖F ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤ C_inv * (T + 2) ^ δ * x ^ c / T := by
      intro σ hσ
      rw [Set.uIoc_of_le hcc'.le] at hσ
      have hzeta : ‖riemannZetaInv ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤ C_inv * (T + 2) ^ δ := by
        have h0 := hbd (σ := σ) (t := sgn * T) hσ.1.le
        rwa [hsgn_abs] at h0
      have hcpow : ‖(x : ℂ) ^ ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤ x ^ c := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        have hre : ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I).re = σ := by simp
        rw [hre]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
      have hden_ge : T ≤ ‖(σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I‖ := by
        have him : |sgn * T| ≤ ‖(σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I‖ := by
          simpa using Complex.abs_im_le_norm ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)
        simpa [hsgn_abs] using him
      have hinv : ‖(σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I‖⁻¹ ≤ T⁻¹ := inv_anti₀ hT_pos hden_ge
      dsimp only [F]
      rw [norm_div, norm_mul, div_eq_mul_inv]
      calc
        ‖riemannZetaInv ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ *
            ‖(x : ℂ) ^ ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ *
            ‖(σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I‖⁻¹
            ≤ (C_inv * (T + 2) ^ δ * x ^ c) * T⁻¹ :=
              mul_le_mul (mul_le_mul hzeta hcpow (norm_nonneg _) (by positivity)) hinv
                (by positivity : 0 ≤ ‖(σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I‖⁻¹) (by positivity)
        _ = C_inv * (T + 2) ^ δ * x ^ c / T := by ring
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := c') (b := c)
      (C := C_inv * (T + 2) ^ δ * x ^ c / T) hpt
    have hlen : |c - c'| = 1 / 2 := by
      dsimp only [c, c']
      rw [abs_of_pos (by norm_num)]
      ring
    have hexp_eq : x ^ (3 * δ / 2) * x ^ c / T = x ^ (-1 / 2 + 5 * δ / 2) := by
      dsimp only [T, c]
      rw [← Real.rpow_add hx_pos, ← Real.rpow_sub hx_pos]
      congr 1
      ring
    have hexp_le : x ^ (-1 / 2 + 5 * δ / 2) ≤ x ^ (1 / 2 + 4 * δ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc
      ‖∫ σ in c'..c, F ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖
          ≤ (C_inv * (T + 2) ^ δ * x ^ c / T) * |c - c'| := hnorm
      _ ≤ (C_inv * (2 * x ^ (3 * δ / 2)) * x ^ c / T) * (1 / 2) := by
        rw [hlen]
        gcongr
      _ = C_inv * (x ^ (3 * δ / 2) * x ^ c / T) := by ring
      _ = C_inv * x ^ (-1 / 2 + 5 * δ / 2) := by rw [hexp_eq]
      _ ≤ 2 * C_inv * x ^ (1 / 2 + 4 * δ) := by
        calc
          C_inv * x ^ (-1 / 2 + 5 * δ / 2)
              ≤ C_inv * x ^ (1 / 2 + 4 * δ) := by gcongr
          _ ≤ 2 * (C_inv * x ^ (1 / 2 + 4 * δ)) := by
              have hnn : 0 ≤ C_inv * x ^ (1 / 2 + 4 * δ) := by positivity
              linarith
          _ = 2 * C_inv * x ^ (1 / 2 + 4 * δ) := by ring
  have htop : ‖∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)‖ ≤ 2 * C_inv * x ^ (1 / 2 + 4 * δ) := by
    simpa only [one_mul] using hhoriz_bd 1 (Or.inl rfl)
  have hbot : ‖∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I)‖ ≤ 2 * C_inv * x ^ (1 / 2 + 4 * δ) := by
    simpa only [neg_one_mul, Complex.ofReal_neg] using hhoriz_bd (-1) (Or.inr rfl)
  have hpi_norm : ‖(1 : ℂ) / (2 * Real.pi * I)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hcomb : ‖(I * ∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)) +
        (∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)) -
        (∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I))‖ ≤
      (64 / δ + 4) * C_inv * x ^ (1 / 2 + 4 * δ) := by
    calc
      ‖(I * ∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)) +
            (∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)) -
            (∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I))‖
          ≤ ‖I * ∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)‖ +
              ‖∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)‖ +
              ‖∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I)‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)‖ +
            ‖∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)‖ +
            ‖∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I)‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ (64 / δ) * C_inv * x ^ (1 / 2 + 4 * δ) + 2 * C_inv * x ^ (1 / 2 + 4 * δ) +
            2 * C_inv * x ^ (1 / 2 + 4 * δ) := by
          gcongr
      _ = (64 / δ + 4) * C_inv * x ^ (1 / 2 + 4 * δ) := by ring
  calc
    ‖dirichletContourIntegral a x c T‖
        = ‖(1 : ℂ) / (2 * Real.pi * I)‖ *
            ‖(I * ∫ t in (-T)..T, F ((c' : ℂ) + (t : ℂ) * I)) +
              (∫ σ in c'..c, F ((σ : ℂ) + (T : ℂ) * I)) -
              (∫ σ in c'..c, F ((σ : ℂ) + -(T : ℂ) * I))‖ := by
          rw [hcontour_eq, norm_mul]
    _ ≤ (1 / (2 * Real.pi)) * ((64 / δ + 4) * C_inv * x ^ (1 / 2 + 4 * δ)) := by
        rw [hpi_norm]
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = ((1 / (2 * Real.pi)) * (64 / δ + 4)) * C_inv * x ^ (1 / 2 + 4 * δ) := by ring

/-- Conditional Mertens bound under `RiemannHypothesisProp`:
for every `ε > 0`, `|M(x)| ≤ C * x ^ (1 / 2 + ε)` for all `x ≥ 1`. -/
theorem mertensM_isBigO_of_riemannHypothesisProp (hRH : RiemannHypothesisProp) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(mertensM x : ℝ)| ≤ C * x ^ (1 / 2 + ε) := by
  intro ε hε
  let δ : ℝ := min (ε / 4) (1 / 8)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le : δ ≤ 1 / 8 := min_le_right _ _
  have hδ_eps : 4 * δ ≤ ε := by linarith [min_le_left (ε / 4) (1 / 8)]
  let c : ℝ := 1 + δ
  have hc_pos : 0 < c := by dsimp only [c]; linarith
  have hc_gt1 : (1 : ℝ) < ((c : ℂ)).re := by simp [c, hδ0]
  let a : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  have ha_sum : LSeriesSummable a (c : ℂ) := LSeriesSummable_moebius_iff.mpr hc_gt1
  let C_ser : ℝ := ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖
  have hC_ser_nn : 0 ≤ C_ser := tsum_nonneg fun _ ↦ norm_nonneg _
  obtain ⟨C_inv, hC_inv_pos, hbd_inv⟩ :=
    riemannZetaInv_bound_of_riemannHypothesisProp hRH (by linarith : 1 / 2 < 1 / 2 + δ) hδ0
  let K : ℝ := (1 / (2 * Real.pi)) * (64 / δ + 4)
  have hK_pos : 0 < K := by positivity
  let C_main : ℝ := K * C_inv + C_ser / (Real.pi * Real.log 2) + 12 * (2 : ℝ) ^ c / Real.pi
  let C : ℝ := max 3 (2 * C_main)
  refine ⟨C, by positivity, fun y hy ↦ ?_⟩
  rcases lt_or_ge y 4 with hy_lt4 | hy_ge4
  · have hfloor_le3 : ⌊y⌋₊ ≤ 3 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by norm_num) |>.mpr hy_lt4)
    have hsum_le : |(mertensM y : ℝ)| ≤ 3 := by
      dsimp only [mertensM]
      push_cast
      calc
        |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.moebius n : ℝ)|
            ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |(ArithmeticFunction.moebius n : ℝ)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) :=
              Finset.sum_le_sum fun n _ ↦ abs_moebius_le_one_real n
        _ = ((Finset.Icc 1 ⌊y⌋₊).card : ℝ) := by simp
        _ = (⌊y⌋₊ : ℝ) := by rw [Nat.card_Icc]; simp
        _ ≤ 3 := by exact_mod_cast hfloor_le3
    have hpow_ge1 : 1 ≤ y ^ (1 / 2 + ε) := Real.one_le_rpow hy (by positivity)
    calc
      |(mertensM y : ℝ)| ≤ 3 := hsum_le
      _ ≤ 3 * y ^ (1 / 2 + ε) := le_mul_of_one_le_right (by norm_num) hpow_ge1
      _ ≤ C * y ^ (1 / 2 + ε) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  · let N : ℕ := ⌊y⌋₊
    let x : ℝ := (N : ℝ) + 1 / 2
    let T : ℝ := x ^ (3 / 2 : ℝ)
    have hN_ge4 : 4 ≤ N := Nat.le_floor (by exact_mod_cast hy_ge4)
    have hx_ge4 : 4 ≤ x := by
      have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN_ge4
      dsimp only [x]; linarith
    have hx_pos : 0 < x := by linarith
    have hT_pos : 0 < T := Real.rpow_pos_of_pos hx_pos _
    have hx_le_2y : x ≤ 2 * y := by
      have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
      dsimp only [x]
      linarith
    have hcont_bd : ‖dirichletContourIntegral a x c T‖ ≤ K * C_inv * x ^ (1 / 2 + 4 * δ) :=
      dirichletContourIntegral_moebius_le hRH hx_ge4 hδ0 hδ_le hC_inv_pos hbd_inv
    have hperron := perron_truncated_half_integer (N := N) hc_pos hT_pos ha_sum
    dsimp only at hperron
    change ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 N, a n‖ ≤ _ at hperron
    have hT_pow_eq : x ^ c / (Real.pi * T * Real.log 2) ≤ (1 / (Real.pi * Real.log 2)) * x ^ (1 / 2 + 4 * δ) := by
      have h1 : x ^ c / T = x ^ (-1 / 2 + δ) := by
        dsimp only [c, T]
        rw [← Real.rpow_sub hx_pos]
        congr 1
        ring
      have h2 : x ^ (-1 / 2 + δ) ≤ x ^ (1 / 2 + 4 * δ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hden_pos : 0 < Real.pi * Real.log 2 := mul_pos Real.pi_pos (Real.log_pos one_lt_two)
      calc
        x ^ c / (Real.pi * T * Real.log 2) = (x ^ c / T) / (Real.pi * Real.log 2) := by ring
        _ = x ^ (-1 / 2 + δ) / (Real.pi * Real.log 2) := by rw [h1]
        _ ≤ x ^ (1 / 2 + 4 * δ) / (Real.pi * Real.log 2) :=
          div_le_div_of_nonneg_right h2 hden_pos.le
        _ = (1 / (Real.pi * Real.log 2)) * x ^ (1 / 2 + 4 * δ) := by ring
    have hsum_a_bd : ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖ ≤ 3 * x := by
      calc
        ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖
            ≤ ∑ _n ∈ Finset.Icc 1 (2 * N + 1), (1 : ℝ) :=
              Finset.sum_le_sum fun n _ ↦ norm_moebius_complex_le_one n
        _ = (2 * (N : ℝ) + 1) := by rw [Finset.sum_const, Nat.card_Icc]; simp
        _ ≤ 3 * x := by
          dsimp only [x]
          have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN_ge4
          linarith
    have hterm2_bd : (2 ^ c * (4 * x) / (Real.pi * T)) * ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖ ≤
        (12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 + 4 * δ) := by
      have hpow_sq : x * x / T = x ^ (1 / 2 : ℝ) := by
        dsimp only [T]
        calc
          x * x / x ^ (3 / 2 : ℝ) = x ^ (2 : ℝ) / x ^ (3 / 2 : ℝ) := by
            rw [← sq, ← Real.rpow_two x]
          _ = x ^ (2 - 3 / 2 : ℝ) := by rw [← Real.rpow_sub hx_pos]
          _ = x ^ (1 / 2 : ℝ) := by norm_num
      have hpow_le : x ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 + 4 * δ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      calc
        (2 ^ c * (4 * x) / (Real.pi * T)) * ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖
            ≤ (2 ^ c * (4 * x) / (Real.pi * T)) * (3 * x) :=
              mul_le_mul_of_nonneg_left hsum_a_bd (by positivity)
        _ = (12 * (2 : ℝ) ^ c / Real.pi) * (x * x / T) := by ring
        _ = (12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 : ℝ) := by rw [hpow_sq]
        _ ≤ (12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 + 4 * δ) := by gcongr
    have hperron_err : ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 N, a n‖ ≤
        (C_ser / (Real.pi * Real.log 2) + 12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 + 4 * δ) := by
      calc
        ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 N, a n‖
            ≤ (x ^ c / (Real.pi * T * Real.log 2)) * C_ser +
                (2 ^ c * (4 * x) / (Real.pi * T)) * ∑ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖ := hperron
        _ ≤ ((1 / (Real.pi * Real.log 2)) * x ^ (1 / 2 + 4 * δ)) * C_ser +
              (12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 + 4 * δ) :=
            add_le_add (mul_le_mul_of_nonneg_right hT_pow_eq hC_ser_nn) hterm2_bd
        _ = (C_ser / (Real.pi * Real.log 2) + 12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 + 4 * δ) := by
            ring
    have hmert_norm : |(mertensM y : ℝ)| = ‖∑ n ∈ Finset.Icc 1 N, a n‖ := by
      have hsum_eq : ∑ n ∈ Finset.Icc 1 N, a n = ((mertensM y : ℤ) : ℂ) := by
        dsimp only [mertensM, a]
        push_cast
        rfl
      rw [hsum_eq, Complex.norm_intCast]
    have hsum_bd : ‖∑ n ∈ Finset.Icc 1 N, a n‖ ≤ C_main * x ^ (1 / 2 + 4 * δ) := by
      calc
        ‖∑ n ∈ Finset.Icc 1 N, a n‖
            = ‖dirichletContourIntegral a x c T -
                (dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 N, a n)‖ := by ring_nf
        _ ≤ ‖dirichletContourIntegral a x c T‖ +
              ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 N, a n‖ := norm_sub_le _ _
        _ ≤ K * C_inv * x ^ (1 / 2 + 4 * δ) +
              (C_ser / (Real.pi * Real.log 2) + 12 * (2 : ℝ) ^ c / Real.pi) * x ^ (1 / 2 + 4 * δ) :=
            add_le_add hcont_bd hperron_err
        _ = C_main * x ^ (1 / 2 + 4 * δ) := by dsimp only [C_main]; ring
    have hx_y_pow : x ^ (1 / 2 + 4 * δ) ≤ 2 * y ^ (1 / 2 + ε) := by
      have h1 : x ^ (1 / 2 + 4 * δ) ≤ (2 * y) ^ (1 / 2 + 4 * δ) :=
        Real.rpow_le_rpow hx_pos.le hx_le_2y (by positivity)
      have h2 : (2 : ℝ) ^ (1 / 2 + 4 * δ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith [hδ_le] : 1 / 2 + 4 * δ ≤ 1)
      have h3 : y ^ (1 / 2 + 4 * δ) ≤ y ^ (1 / 2 + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      calc
        x ^ (1 / 2 + 4 * δ) ≤ (2 * y) ^ (1 / 2 + 4 * δ) := h1
        _ = (2 : ℝ) ^ (1 / 2 + 4 * δ) * y ^ (1 / 2 + 4 * δ) :=
            Real.mul_rpow zero_le_two (by linarith)
        _ ≤ 2 * y ^ (1 / 2 + ε) := by gcongr
    have hC_main_nn : 0 ≤ C_main := by
      dsimp only [C_main]
      have : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
      positivity
    calc
      |(mertensM y : ℝ)| = ‖∑ n ∈ Finset.Icc 1 N, a n‖ := hmert_norm
      _ ≤ C_main * x ^ (1 / 2 + 4 * δ) := hsum_bd
      _ ≤ C_main * (2 * y ^ (1 / 2 + ε)) := mul_le_mul_of_nonneg_left hx_y_pow hC_main_nn
      _ = (2 * C_main) * y ^ (1 / 2 + ε) := by ring
      _ ≤ C * y ^ (1 / 2 + ε) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)

/-- Upper bound on the abscissa of convergence of `μ` from the Mertens `O(x ^ (1 / 2 + ε))`
bound: `abscissaOfConvergence (fun n ↦ (μ n : ℂ)) ≤ 1 / 2`. -/
theorem abscissaOfConvergence_moebius_le_half_of_mertensM
    (hmert : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(mertensM x : ℝ)| ≤ C * x ^ (1 / 2 + ε)) :
    abscissaOfConvergence (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) ≤
      (1 / 2 : ℝ) := by
  let f : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hx_gt : (1 / 2 : ℝ) < x := EReal.coe_lt_coe_iff.mp hx
  let ε : ℝ := (x - 1 / 2) / 3
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨C, hC_pos, hbd⟩ := hmert ε hε
  have hcoeff_eq : ∀ N : ℕ, ‖coeffPartialSum f N‖ = |(mertensM (N : ℝ) : ℝ)| := by
    intro N
    have hsum : coeffPartialSum f N = ((mertensM (N : ℝ) : ℤ) : ℂ) := by
      rw [coeffPartialSum]
      have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
      dsimp only [mertensM, f]
      rw [hfloor]
      push_cast
      rfl
    rw [hsum, Complex.norm_intCast]
  have hlog_div : Tendsto (fun N : ℕ ↦ Real.log C / Real.log N) atTop (𝓝 0) := by
    have ht_log : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop ht_log
  have hev_le : ∀ᶠ N : ℕ in atTop,
      ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal) ≤
        ((1 / 2 + 2 * ε : ℝ) : EReal) := by
    have hev_log : ∀ᶠ N : ℕ in atTop, Real.log C / Real.log N ≤ ε :=
      hlog_div.eventually_le_const (by linarith : (0 : ℝ) < ε)
    filter_upwards [hev_log, eventually_ge_atTop 2] with N hNC hN2
    refine EReal.coe_le_coe_iff.mpr ?_
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlogN_pos : 0 < Real.log N := Real.log_pos hN1
    rcases eq_or_ne ‖coeffPartialSum f N‖ 0 with h0 | hne0
    · rw [h0, Real.log_zero, zero_div]
      linarith
    · have hnorm_pos : 0 < ‖coeffPartialSum f N‖ :=
        lt_of_le_of_ne (norm_nonneg _) hne0.symm
      have hN_ge1 : (1 : ℝ) ≤ N := by linarith
      have hC_bd : ‖coeffPartialSum f N‖ ≤ C * (N : ℝ) ^ (1 / 2 + ε) := by
        rw [hcoeff_eq]
        exact hbd N hN_ge1
      have hlog_bd : Real.log ‖coeffPartialSum f N‖ ≤
          Real.log C + (1 / 2 + ε) * Real.log N := by
        calc
          Real.log ‖coeffPartialSum f N‖
              ≤ Real.log (C * (N : ℝ) ^ (1 / 2 + ε)) := Real.log_le_log hnorm_pos hC_bd
          _ = Real.log C + (1 / 2 + ε) * Real.log N := by
              rw [Real.log_mul hC_pos.ne' (by positivity), Real.log_rpow (by linarith)]
      calc
        Real.log ‖coeffPartialSum f N‖ / Real.log N
            ≤ (Real.log C + (1 / 2 + ε) * Real.log N) / Real.log N :=
              div_le_div_of_nonneg_right hlog_bd hlogN_pos.le
        _ = Real.log C / Real.log N + (1 / 2 + ε) := by
            rw [add_div, mul_div_cancel_right₀ _ hlogN_pos.ne']
        _ ≤ ε + (1 / 2 + ε) := by linarith [hNC]
        _ = 1 / 2 + 2 * ε := by ring
  have hlimsup : limsup (fun N : ℕ ↦ ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal))
      atTop ≤ ((1 / 2 + 2 * ε : ℝ) : EReal) :=
    Filter.limsup_le_of_le (by isBoundedDefault) hev_le
  exact (abscissaOfConvergence_le_limsup f).trans
    (hlimsup.trans (EReal.coe_le_coe_iff.mpr (by dsimp only [ε]; linarith)))

/-- Deduction of `RiemannHypothesisProp` from `abscissaOfConvergence μ ≤ 1 / 2` via analytic
continuation of `dirichletSum μ s * riemannZeta₁ s = s - 1` onto `{s : ℂ | 1 / 2 < s.re}`. -/
theorem riemannHypothesisProp_of_abscissaOfConvergence_moebius_le_half
    (hab : abscissaOfConvergence (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) ≤
      (1 / 2 : ℝ)) : RiemannHypothesisProp := by
  let f : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  let G : ℂ → ℂ := fun s ↦ dirichletSum f s * riemannZeta₁ s
  have hU_sub : U ⊆ {s : ℂ | abscissaOfConvergence f < (s.re : EReal)} := by
    intro s hs
    exact lt_of_le_of_lt hab (EReal.coe_lt_coe_iff.mpr hs)
  have hds_an : AnalyticOnNhd ℂ (dirichletSum f) U :=
    (dirichletSum_analyticOnNhd f).mono hU_sub
  have hz1_an : AnalyticOnNhd ℂ riemannZeta₁ U :=
    (differentiable_riemannZeta₁_bridge.differentiableOn.analyticOnNhd isOpen_univ).mono
      (Set.subset_univ U)
  have hG_an : AnalyticOnNhd ℂ G U := hds_an.mul hz1_an
  have hlin_an : AnalyticOnNhd ℂ (fun s : ℂ ↦ s - 1) U :=
    ((differentiable_id.sub_const (1 : ℂ)).differentiableOn.analyticOnNhd isOpen_univ).mono
      (Set.subset_univ U)
  have hU_preconn : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
  have hz0_mem : (2 : ℂ) ∈ U := by simp [U]; norm_num
  have hev_eq : G =ᶠ[𝓝 (2 : ℂ)] fun s : ℂ ↦ s - 1 := by
    have hopen : IsOpen {s : ℂ | (1 : ℝ) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < ((2 : ℂ)).re)] with s hs
    have ha_sum : LSeriesSummable f s := LSeriesSummable_moebius_iff.mpr hs
    have hds_eq : dirichletSum f s = LSeries f s := ha_sum.dirichletSum_eq_LSeries
    have hL_eq : LSeries f s = (riemannZeta s)⁻¹ := by
      simpa [f] using LSeries_moebius_eq_inv_riemannZeta hs
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    have hz1_eq : riemannZeta₁ s = (s - 1) * riemannZeta s := by
      rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
    have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    dsimp only [G]
    rw [hds_eq, hL_eq, hz1_eq]
    field_simp [hzeta_ne]
  have hG_eq : Set.EqOn G (fun s : ℂ ↦ s - 1) U :=
    hG_an.eqOn_of_preconnected_of_eventuallyEq hlin_an hU_preconn hz0_mem hev_eq
  rw [riemannHypothesisProp_iff_ne_zero_of_half_lt_re]
  intro s hs hs0
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_ne_zero_of_one_le_re_bridge (le_refl 1) hs0
  · have hEq : dirichletSum f s * riemannZeta₁ s = s - 1 := hG_eq hs
    have hz1_zero : riemannZeta₁ s = 0 := by
      have heq1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1),
          one_mul]
      rw [heq1, hs0, mul_zero]
    rw [hz1_zero, mul_zero] at hEq
    exact sub_ne_zero.mpr hs1 hEq.symm

/-- **Abscissa-of-convergence equivalence**: `RiemannHypothesisProp` holds if and only if
the Dirichlet series `∑ μ(n) n ^ (-s)` converges for all `Re s > 1 / 2`. -/
theorem riemannHypothesisProp_iff_abscissaOfConvergence_moebius_le_half :
    RiemannHypothesisProp ↔
      abscissaOfConvergence (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) ≤
        (1 / 2 : ℝ) :=
  ⟨fun hRH ↦ abscissaOfConvergence_moebius_le_half_of_mertensM
      (mertensM_isBigO_of_riemannHypothesisProp hRH),
    riemannHypothesisProp_of_abscissaOfConvergence_moebius_le_half⟩

/-- **Mertens bound equivalence**: `RiemannHypothesisProp` holds if and only if
`M(x) = O(x ^ (1 / 2 + ε))` for every `ε > 0`. -/
theorem riemannHypothesisProp_iff_mertensM_isBigO :
    RiemannHypothesisProp ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
        |(mertensM x : ℝ)| ≤ C * x ^ (1 / 2 + ε) :=
  ⟨mertensM_isBigO_of_riemannHypothesisProp, fun hmert ↦
    riemannHypothesisProp_of_abscissaOfConvergence_moebius_le_half
      (abscissaOfConvergence_moebius_le_half_of_mertensM hmert)⟩

end MertensAndMoebiusAbscissa

/-! ### The Lindelöf Hypothesis and Vertical Order Consequence -/

section LindelofHypothesis

/-- **The Lindelöf Hypothesis**: on the critical line `Re s = 1 / 2`,
`‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (|t| + 2) ^ ε` for every `ε > 0`. -/
def LindelofHypothesisProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ ε

private noncomputable def zetaStripAuxLH (s : ℂ) : ℂ :=
  riemannZeta₁ s / (s + 2)

private lemma differentiableOn_zetaStripAuxLH_right :
    DifferentiableOn ℂ zetaStripAuxLH {s : ℂ | -1 < s.re} := by
  intro s hs
  have hs_ne : s + 2 ≠ 0 := fun h ↦ by
    have hre := congrArg Complex.re h
    simp at hre
    linarith [show (-1 : ℝ) < s.re from hs]
  exact (differentiable_riemannZeta₁_bridge.differentiableAt.div
    (differentiableAt_id.add_const 2) hs_ne).differentiableWithinAt

private lemma zetaStripAuxLH_eq_mul {s : ℂ} (hs1 : s ≠ 1) :
    zetaStripAuxLH s = ((s - 1) / (s + 2)) * riemannZeta s := by
  have hs_ne1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  dsimp only [zetaStripAuxLH]
  rw [riemannZeta_eq_inv_sub_mul hs1]
  field_simp [hs_ne1]

private lemma norm_sub_one_le_add_two {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    ‖s - 1‖ ≤ ‖s + 2‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
    Complex.add_re, Complex.re_ofNat, Complex.add_im, Complex.im_ofNat, add_zero]
  nlinarith

private lemma hasVerticalOrder_zetaStripAuxLH_iff {σ μ : ℝ} (hσ : 0 ≤ σ) :
    HasVerticalOrder zetaStripAuxLH σ μ ↔ HasVerticalOrder riemannZeta σ μ := by
  constructor <;> intro hvo
  · obtain ⟨C, hC_nn, hC⟩ := Asymptotics.isBigO_iff'.mp hvo
    refine Asymptotics.isBigO_iff.mpr ⟨4 * max C 1, ?_⟩
    filter_upwards [hC, Filter.eventually_comap.mpr
      ((eventually_ge_atTop (1 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t htC ht1
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hs1 : s ≠ 1 := fun h ↦ by
      have him := congrArg Complex.im h
      simp [s] at him
      rw [him, abs_zero] at ht1
      linarith
    have hs_sub1 : 1 ≤ ‖s - 1‖ := by
      have him : |t| ≤ ‖s - 1‖ := by simpa [s] using Complex.abs_im_le_norm (s - 1)
      linarith
    have hratio : ‖(s + 2) / (s - 1)‖ ≤ 4 := by
      have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [show (s + 2) / (s - 1) = 1 + 3 / (s - 1) by field_simp [hne]; ring]
      calc
        ‖1 + 3 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖3 / (s - 1)‖ := norm_add_le _ _
        _ = 1 + 3 / ‖s - 1‖ := by rw [norm_one, norm_div, Complex.norm_ofNat]
        _ ≤ 1 + 3 / 1 := by gcongr
        _ = 4 := by norm_num
    have hne2 : s + 2 ≠ 0 := fun h ↦ by
      have hre := congrArg Complex.re h; simp [s] at hre; linarith
    have hzeq : riemannZeta s = ((s + 2) / (s - 1)) * zetaStripAuxLH s := by
      rw [zetaStripAuxLH_eq_mul hs1]
      field_simp [sub_ne_zero.mpr hs1, hne2]
    have hnorm_aux : ‖zetaStripAuxLH s‖ ≤ max C 1 * ‖(|t| + 2) ^ μ‖ :=
      htC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    calc
      ‖riemannZeta s‖ = ‖(s + 2) / (s - 1)‖ * ‖zetaStripAuxLH s‖ := by rw [hzeq, norm_mul]
      _ ≤ 4 * (max C 1 * ‖(|t| + 2) ^ μ‖) := by gcongr
      _ = (4 * max C 1) * ‖(|t| + 2) ^ μ‖ := by ring
  · obtain ⟨C, _, hC⟩ := Asymptotics.isBigO_iff'.mp hvo
    refine Asymptotics.isBigO_iff.mpr ⟨max C 1, ?_⟩
    filter_upwards [hC, Filter.eventually_comap.mpr
      ((eventually_ge_atTop (1 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t htC ht1
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hs1 : s ≠ 1 := fun h ↦ by
      have him := congrArg Complex.im h
      simp [s] at him
      rw [him, abs_zero] at ht1
      linarith
    have hs_re : -1 / 2 ≤ s.re := by simp [s]; linarith
    have hne2 : s + 2 ≠ 0 := fun h ↦ by
      have hre := congrArg Complex.re h; simp [s] at hre; linarith
    have hratio : ‖(s - 1) / (s + 2)‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hne2)).mpr (norm_sub_one_le_add_two hs_re)
    calc
      ‖zetaStripAuxLH s‖ = ‖(s - 1) / (s + 2)‖ * ‖riemannZeta s‖ := by
        rw [zetaStripAuxLH_eq_mul hs1, norm_mul]
      _ ≤ 1 * (C * ‖(|t| + 2) ^ μ‖) := mul_le_mul hratio htC (norm_nonneg _) zero_le_one
      _ ≤ max C 1 * ‖(|t| + 2) ^ μ‖ := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

private lemma hasFiniteVerticalOrder_riemannZeta {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ μ₀ : ℝ, 0 ≤ μ₀ ∧ HasVerticalOrder riemannZeta σ μ₀ := by
  rcases le_or_gt σ 1 with hle1 | hgt1
  · exact ⟨(1 - σ) / 2 + 1, by linarith,
      hasVerticalOrder_riemannZeta_of_mem_Icc ⟨hσ, hle1⟩ one_pos⟩
  · refine ⟨1, zero_le_one, ?_⟩
    obtain ⟨C, _, hbd⟩ := norm_riemannZeta_re_ge_one_le
    refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [Filter.eventually_comap.mpr
      ((eventually_ge_atTop (2 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t ht
    have hpow_nn : 0 ≤ (|t| + 2) ^ (1 : ℝ) := Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg hpow_nn, Real.rpow_one]
    have hlog : Real.log (|t| + 2) ≤ |t| + 2 :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    exact (hbd hgt1.le ht).trans (by gcongr)

private lemma verticalOrder_zetaStripAuxLH_eq {σ : ℝ} (hσ : 0 ≤ σ) :
    verticalOrder zetaStripAuxLH σ = verticalOrder riemannZeta σ := by
  have hfin_zeta := hasFiniteVerticalOrder_riemannZeta hσ
  have hfin_aux : ∃ μ₀ : ℝ, 0 ≤ μ₀ ∧ HasVerticalOrder zetaStripAuxLH σ μ₀ := by
    obtain ⟨μ₀, hμ₀, hvo⟩ := hfin_zeta
    exact ⟨μ₀, hμ₀, (hasVerticalOrder_zetaStripAuxLH_iff hσ).mpr hvo⟩
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hmu : 0 ≤ verticalOrder riemannZeta σ + ε := by
      linarith [verticalOrder_nonneg riemannZeta σ]
    have hvo := hasVerticalOrder_of_verticalOrder_lt hfin_zeta
      (by linarith : verticalOrder riemannZeta σ < verticalOrder riemannZeta σ + ε)
    exact verticalOrder_le_of_hasVerticalOrder hmu ((hasVerticalOrder_zetaStripAuxLH_iff hσ).mpr hvo)
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hmu : 0 ≤ verticalOrder zetaStripAuxLH σ + ε := by
      linarith [verticalOrder_nonneg zetaStripAuxLH σ]
    have hvo := hasVerticalOrder_of_verticalOrder_lt hfin_aux
      (by linarith : verticalOrder zetaStripAuxLH σ < verticalOrder zetaStripAuxLH σ + ε)
    exact verticalOrder_le_of_hasVerticalOrder hmu ((hasVerticalOrder_zetaStripAuxLH_iff hσ).mp hvo)

private lemma zetaStripAuxLH_poly_on_strip {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂)
    (hσ₂ : σ₂ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ verticalStripOpen σ₁ σ₂,
      ‖zetaStripAuxLH z‖ ≤ A * (|z.im| + 2) ^ (3 / 2 : ℝ) := by
  obtain ⟨C₁, _, hbd₁⟩ := norm_riemannZeta_critical_strip_le (by norm_num : (0 : ℝ) < 1)
  let K : Set ℂ := Set.Icc σ₁ σ₂ ×ℂ Set.Icc (-1 : ℝ) 1
  have hK_cpt : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K ⊆ {s : ℂ | -1 < s.re} := fun s hs ↦ by
    have hsre : σ₁ ≤ s.re := hs.1.1
    change (-1 : ℝ) < s.re
    linarith [hσ₁, hsre]
  have hcont : ContinuousOn zetaStripAuxLH K :=
    (differentiableOn_zetaStripAuxLH_right.continuousOn).mono hK_sub
  obtain ⟨M, hM_bd⟩ : ∃ M : ℝ, ∀ s ∈ K, ‖zetaStripAuxLH s‖ ≤ M := by
    by_cases hne : K.Nonempty
    · obtain ⟨s₀, _, hs₀⟩ := hK_cpt.exists_isMaxOn hne hcont.norm
      exact ⟨‖zetaStripAuxLH s₀‖, fun s hs ↦ hs₀ hs⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, fun s hs ↦ by simp [hne] at hs⟩
  let A : ℝ := max C₁ (max M 1)
  refine ⟨A, by positivity, fun z hz ↦ ?_⟩
  have hz_re_Icc : z.re ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hpow_ge1 : 1 ≤ (|z.im| + 2) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg z.im]) (by norm_num)
  rcases le_or_gt (1 : ℝ) |z.im| with him1 | him_lt1
  · have hz1 : z ≠ 1 := fun h ↦ by simp [h] at him1; linarith
    have hratio : ‖(z - 1) / (z + 2)‖ ≤ 1 := by
      have hne2 : z + 2 ≠ 0 := fun h ↦ by
        have hre := congrArg Complex.re h; simp at hre; linarith [hz.1]
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hne2)).mpr
        (norm_sub_one_le_add_two (by linarith [hz.1]))
    have hstrip := hbd₁ hz_re_Icc him1
    have hexp_le : (1 - z.re) / 2 + 1 ≤ (3 / 2 : ℝ) := by linarith [hz.1]
    have hpow_mono : (|z.im| + 2) ^ ((1 - z.re) / 2 + 1) ≤ (|z.im| + 2) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) hexp_le
    calc
      ‖zetaStripAuxLH z‖ = ‖(z - 1) / (z + 2)‖ * ‖riemannZeta z‖ := by
        rw [zetaStripAuxLH_eq_mul hz1, norm_mul]
      _ ≤ 1 * (C₁ * (|z.im| + 2) ^ ((1 - z.re) / 2 + 1)) := by
          refine mul_le_mul hratio ?_ (norm_nonneg _) zero_le_one
          rw [Complex.re_add_im z] at hstrip
          exact hstrip
      _ ≤ C₁ * (|z.im| + 2) ^ (3 / 2 : ℝ) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow_mono (by positivity)
      _ ≤ A * (|z.im| + 2) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
  · have hzK : z ∈ K := ⟨⟨hz.1.le, hz.2.le⟩, abs_le.mp him_lt1.le⟩
    calc
      ‖zetaStripAuxLH z‖ ≤ M := hM_bd z hzK
      _ ≤ max M 1 := le_max_left _ _
      _ ≤ (max M 1) * (|z.im| + 2) ^ (3 / 2 : ℝ) :=
          le_mul_of_one_le_right (by positivity) hpow_ge1
      _ ≤ A * (|z.im| + 2) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

/-- **Vertical-order equivalence for Lindelöf**: `LindelofHypothesisProp` holds if and only if
`verticalOrder riemannZeta σ = 0` for every `σ ≥ 1 / 2`. -/
theorem lindelofHypothesisProp_iff_verticalOrder :
    LindelofHypothesisProp ↔ ∀ σ : ℝ, 1 / 2 ≤ σ → verticalOrder riemannZeta σ = 0 := by
  constructor
  · intro hLH σ hσ
    rcases le_or_gt 1 σ with hge1 | hlt1
    · exact verticalOrder_riemannZeta_eq_zero_of_one_le hge1
    · refine le_antisymm ?_ (verticalOrder_nonneg riemannZeta σ)
      have hvo_half : verticalOrder riemannZeta (1 / 2) = 0 := by
        refine le_antisymm ?_ (verticalOrder_nonneg riemannZeta (1 / 2))
        refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        obtain ⟨C, _, hbd⟩ := hLH ε hε
        have hvo : HasVerticalOrder riemannZeta (1 / 2) ε := by
          refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
          filter_upwards with t
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
          simpa using hbd t
        simpa using verticalOrder_le_of_hasVerticalOrder hε.le hvo
      have hdiffCont : DiffContOnCl ℂ zetaStripAuxLH (verticalStripOpen (1 / 2) 1) := by
        have hcl : closure (verticalStripOpen (1 / 2) 1) ⊆ verticalStripClosed (1 / 2) 1 :=
          (isClosed_Icc.preimage Complex.continuous_re).closure_subset_iff.mpr
            (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩)
        have hdiff_cl : DifferentiableOn ℂ zetaStripAuxLH (verticalStripClosed (1 / 2) 1) :=
          differentiableOn_zetaStripAuxLH_right.mono fun z hz ↦ by
            have hre : (1 / 2 : ℝ) ≤ z.re := hz.1
            change (-1 : ℝ) < z.re
            linarith
        exact ⟨hdiff_cl.mono (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩), hdiff_cl.continuousOn.mono hcl⟩
      obtain ⟨A, hA_nn, hA_bd⟩ := zetaStripAuxLH_poly_on_strip
        (σ₁ := 1 / 2) (σ₂ := 1) (by norm_num) (by norm_num) le_rfl
      have hfin₁ : ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧ HasVerticalOrder zetaStripAuxLH (1 / 2) μ₁ := by
        refine ⟨1, zero_le_one, ?_⟩
        rw [hasVerticalOrder_zetaStripAuxLH_iff (by norm_num)]
        have hvo_le : verticalOrder riemannZeta (1 / 2) ≤ (1 - (1 / 2 : ℝ)) / 2 :=
          verticalOrder_riemannZeta_le (by constructor <;> norm_num)
        exact hasVerticalOrder_of_verticalOrder_lt (hasFiniteVerticalOrder_riemannZeta (by norm_num))
          (by linarith)
      have hfin₂ : ∃ μ₂ : ℝ, 0 ≤ μ₂ ∧ HasVerticalOrder zetaStripAuxLH 1 μ₂ := by
        refine ⟨1, zero_le_one, ?_⟩
        rw [hasVerticalOrder_zetaStripAuxLH_iff zero_le_one]
        exact hasVerticalOrder_of_verticalOrder_lt (hasFiniteVerticalOrder_riemannZeta zero_le_one)
          (by rw [verticalOrder_riemannZeta_eq_zero_of_one_le le_rfl]; norm_num)
      have hinterp := verticalOrder_le_linearInterp_of_poly (by norm_num : (1 / 2 : ℝ) < 1)
        hdiffCont hA_nn hA_bd hfin₁ hfin₂ ⟨hσ, hlt1.le⟩
      have haux_half : verticalOrder zetaStripAuxLH (1 / 2) = 0 := by
        rw [verticalOrder_zetaStripAuxLH_eq (by norm_num), hvo_half]
      have haux_one : verticalOrder zetaStripAuxLH 1 = 0 := by
        rw [verticalOrder_zetaStripAuxLH_eq zero_le_one,
          verticalOrder_riemannZeta_eq_zero_of_one_le le_rfl]
      rw [haux_half, haux_one] at hinterp
      have hlin0 : linearInterp (1 / 2) 1 0 0 σ = 0 := by simp [linearInterp]
      rw [hlin0, verticalOrder_zetaStripAuxLH_eq (by linarith)] at hinterp
      exact hinterp
  · intro hvo ε hε
    have hvo_half : HasVerticalOrder riemannZeta (1 / 2) ε :=
      hasVerticalOrder_of_verticalOrder_lt (hasFiniteVerticalOrder_riemannZeta (by norm_num))
        (by rw [hvo (1 / 2) le_rfl]; exact hε)
    obtain ⟨C₁, _, hC₁⟩ := Asymptotics.isBigO_iff'.mp hvo_half
    rw [Filter.eventually_comap, Filter.eventually_atTop] at hC₁
    obtain ⟨T₀, hT₀⟩ := hC₁
    let K : Set ℝ := Set.Icc (-max T₀ 0) (max T₀ 0)
    have hK_cpt : IsCompact K := isCompact_Icc
    have hcont : Continuous (fun t : ℝ ↦ riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
      refine continuous_iff_continuousAt.mpr fun t ↦ ?_
      have hne1 : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
        have hre := congrArg Complex.re h
        simp at hre
      exact ContinuousAt.comp (f := fun t : ℝ ↦ (1 / 2 : ℂ) + (t : ℂ) * I)
        (differentiableAt_riemannZeta hne1).continuousAt
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    obtain ⟨t₀, _, ht₀⟩ := hK_cpt.exists_isMaxOn
      (⟨0, by change (0 : ℝ) ∈ Set.Icc (-max T₀ 0) (max T₀ 0); simp⟩ : K.Nonempty)
      hcont.norm.continuousOn
    let C₀ : ℝ := ‖riemannZeta ((1 / 2 : ℂ) + (t₀ : ℂ) * I)‖
    let C : ℝ := max (max C₁ C₀) 1
    refine ⟨C, by positivity, fun t ↦ ?_⟩
    have hpow_ge1 : 1 ≤ (|t| + 2) ^ ε :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) hε.le
    have hpow_nn : 0 ≤ (|t| + 2) ^ ε := Real.rpow_nonneg (by positivity) _
    rcases le_or_gt (max T₀ 0) |t| with hbig | hsmall
    · have hle_C₁ := hT₀ |t| ((le_max_left _ _).trans hbig) t rfl
      rw [Real.norm_of_nonneg hpow_nn] at hle_C₁
      simpa using hle_C₁.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) hpow_nn)
    · have htK : t ∈ K := abs_le.mp hsmall.le
      calc
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := ht₀ htK
        _ ≤ C₀ * (|t| + 2) ^ ε := le_mul_of_one_le_right (norm_nonneg _) hpow_ge1
        _ ≤ C * (|t| + 2) ^ ε := mul_le_mul_of_nonneg_right
            ((le_max_right _ _).trans (le_max_left _ _)) hpow_nn

private lemma norm_riemannZeta_reflected_strip_of_RH (hRH : RiemannHypothesisProp)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ |t| →
      ‖riemannZeta (((1 / 2 - δ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ (2 * δ) := by
  let σ₁ : ℝ := 1 / 2 - δ
  let σ₂ : ℝ := 1 / 2 + δ
  obtain ⟨C_zeta, hC_zeta_pos, hbd_zeta⟩ :=
    riemannZeta_and_inv_bounds_of_riemannHypothesisProp hRH (σ₀ := σ₂)
      (by dsimp only [σ₂]; linarith) hδ0
  obtain ⟨c_γ, C_γ, hc_γ_pos, hcC_γ, hbd_γ⟩ := norm_complex_gamma_strip_bounds (1 / 8) (1 / 2)
  have hC_γ_pos : 0 < C_γ := lt_of_lt_of_le hc_γ_pos hcC_γ
  let C : ℝ := max 1 ((Real.pi ^ (σ₁ - 1 / 2)) * (C_γ / c_γ) * C_zeta)
  refine ⟨C, by positivity, fun t ht ↦ ?_⟩
  let s : ℂ := (σ₁ : ℂ) + (t : ℂ) * I
  have hs_re : 0 < s.re := by simp [s, σ₁]; linarith
  have h1s_re : 0 < (1 - s).re := by simp [s, σ₁]; linarith
  have hs1 : s ≠ 1 := fun h ↦ by
    have := congrArg Complex.re h; simp [s, σ₁] at this; linarith
  have h1s1 : 1 - s ≠ 1 := fun h ↦ by
    have := congrArg Complex.re h; simp [s, σ₁] at this; linarith
  have hxi1 := xi_eq_formula_of_re_pos hs_re hs1
  have hxi2 := xi_eq_formula_of_re_pos h1s_re h1s1
  rw [← xi_one_sub s] at hxi1
  rw [hxi2] at hxi1
  have hpoly : (1 / 2 : ℂ) * s * (s - 1) = (1 / 2 : ℂ) * (1 - s) * (1 - s - 1) := by ring
  have hpoly_ne : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (fun h ↦ by simp [h] at hs_re)) (sub_ne_zero.mpr hs1)
  have hpi_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [hs_re])
  have hzeta_eq : riemannZeta s =
      ((Real.pi : ℂ) ^ (-(1 - s) / 2) / (Real.pi : ℂ) ^ (-s / 2)) *
        (Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)) * riemannZeta (1 - s) := by
    rw [← hpoly] at hxi1
    set A := (1 / 2 : ℂ) * s * (s - 1)
    set P₁ := (Real.pi : ℂ) ^ (-s / 2)
    set P₂ := (Real.pi : ℂ) ^ (-(1 - s) / 2)
    set G₁ := Complex.Gamma (s / 2)
    set G₂ := Complex.Gamma ((1 - s) / 2)
    have hmul : A * (P₂ * G₂ * riemannZeta (1 - s)) = A * (P₁ * G₁ * riemannZeta s) := by
      linear_combination hxi1
    have hcanc := mul_left_cancel₀ hpoly_ne hmul
    have hpg : P₁ * G₁ ≠ 0 := mul_ne_zero hpi_ne hG_ne
    have hdiv : riemannZeta s = (P₂ * G₂ * riemannZeta (1 - s)) / (P₁ * G₁) :=
      eq_div_of_mul_eq hpg (by linear_combination -hcanc)
    rw [hdiv]
    field_simp [hpi_ne, hG_ne]
  have hnorm_pi : ‖(Real.pi : ℂ) ^ (-(1 - s) / 2) / (Real.pi : ℂ) ^ (-s / 2)‖ =
      Real.pi ^ (σ₁ - 1 / 2) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre1 : (-(1 - s) / 2).re = -(1 - σ₁) / 2 := by simp [s, σ₁]
    have hre2 : (-s / 2).re = -σ₁ / 2 := by simp [s, σ₁]
    rw [hre1, hre2, ← Real.rpow_sub Real.pi_pos]
    congr 1
    ring
  have hs_half_re : σ₁ / 2 ∈ Set.Icc (1 / 8 : ℝ) (1 / 2) := ⟨by dsimp only [σ₁]; linarith,
    by dsimp only [σ₁]; linarith⟩
  have h1s_half_re : σ₂ / 2 ∈ Set.Icc (1 / 8 : ℝ) (1 / 2) := ⟨by dsimp only [σ₂]; linarith,
    by dsimp only [σ₂]; linarith⟩
  have ht_half : 1 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
  have hneg_t_half : 1 ≤ |-(t / 2)| := by simpa [abs_neg] using ht_half
  have hG_num_eq : (1 - s) / 2 = ((σ₂ / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I := by
    dsimp only [s, σ₁, σ₂]; push_cast; ring
  have hG_den_eq : s / 2 = ((σ₁ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    dsimp only [s]; push_cast; ring
  have hG_num_bd := (hbd_γ h1s_half_re hneg_t_half).2
  have hG_den_bd := (hbd_γ hs_half_re ht_half).1
  rw [← hG_num_eq] at hG_num_bd
  rw [← hG_den_eq] at hG_den_bd
  have hG_ratio_bd : ‖Complex.Gamma ((1 - s) / 2)‖ / ‖Complex.Gamma (s / 2)‖ ≤
      (C_γ / c_γ) * (|t| + 2) ^ δ := by
    have hden_pos : 0 < c_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₁ / 2 - 1 / 2) := by
      have : 0 < |t / 2| := by linarith
      positivity
    have hnum_exp : |-(t / 2)| = |t / 2| := abs_neg _
    rw [hnum_exp] at hG_num_bd
    have hratio1 : ‖Complex.Gamma ((1 - s) / 2)‖ / ‖Complex.Gamma (s / 2)‖ ≤
        (C_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₂ / 2 - 1 / 2)) /
          (c_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₁ / 2 - 1 / 2)) := by
      calc
        ‖Complex.Gamma ((1 - s) / 2)‖ / ‖Complex.Gamma (s / 2)‖
            ≤ (C_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₂ / 2 - 1 / 2)) /
                ‖Complex.Gamma (s / 2)‖ := div_le_div_of_nonneg_right hG_num_bd (norm_nonneg _)
        _ ≤ (C_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₂ / 2 - 1 / 2)) /
                (c_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₁ / 2 - 1 / 2)) :=
              div_le_div_of_nonneg_left (by positivity) hden_pos hG_den_bd
    have hexp_pos : Real.exp (-(Real.pi / 2) * |t / 2|) ≠ 0 := (Real.exp_pos _).ne'
    have hhalf_pos : 0 < |t / 2| := by linarith
    have hpow_sub : |t / 2| ^ (σ₂ / 2 - 1 / 2) / |t / 2| ^ (σ₁ / 2 - 1 / 2) = |t / 2| ^ δ := by
      rw [← Real.rpow_sub hhalf_pos]
      congr 1
      dsimp only [σ₁, σ₂]
      ring
    have hdiv_simp : (C_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₂ / 2 - 1 / 2)) /
        (c_γ * Real.exp (-(Real.pi / 2) * |t / 2|) * |t / 2| ^ (σ₁ / 2 - 1 / 2)) =
        (C_γ / c_γ) * |t / 2| ^ δ := by
      rw [← hpow_sub]
      field_simp [hc_γ_pos.ne', hexp_pos]
    have hpow_le : |t / 2| ^ δ ≤ (|t| + 2) ^ δ := by
      refine Real.rpow_le_rpow (abs_nonneg _) ?_ hδ0.le
      rw [abs_div, abs_two]
      linarith
    calc
      ‖Complex.Gamma ((1 - s) / 2)‖ / ‖Complex.Gamma (s / 2)‖
          ≤ (C_γ / c_γ) * |t / 2| ^ δ := hratio1.trans_eq hdiv_simp
      _ ≤ (C_γ / c_γ) * (|t| + 2) ^ δ :=
        mul_le_mul_of_nonneg_left hpow_le (div_nonneg hC_γ_pos.le hc_γ_pos.le)
  have h1s_eq : 1 - s = (σ₂ : ℂ) + ((-t : ℝ) : ℂ) * I := by
    dsimp only [s, σ₁, σ₂]; push_cast; ring
  have hzeta_1s_bd : ‖riemannZeta (1 - s)‖ ≤ C_zeta * (|t| + 2) ^ δ := by
    rw [h1s_eq]
    have h := (hbd_zeta (σ := σ₂) (t := -t) le_rfl (by simpa [abs_neg] using ht)).1
    simpa [abs_neg] using h
  have hpow_add : (|t| + 2) ^ δ * (|t| + 2) ^ δ = (|t| + 2) ^ (2 * δ) := by
    rw [← Real.rpow_add (by positivity : 0 < |t| + 2), two_mul]
  calc
    ‖riemannZeta s‖
        = ‖(Real.pi : ℂ) ^ (-(1 - s) / 2) / (Real.pi : ℂ) ^ (-s / 2)‖ *
            (‖Complex.Gamma ((1 - s) / 2)‖ / ‖Complex.Gamma (s / 2)‖) *
            ‖riemannZeta (1 - s)‖ := by
          rw [hzeta_eq, norm_mul, norm_mul, ← norm_div]
    _ ≤ Real.pi ^ (σ₁ - 1 / 2) * ((C_γ / c_γ) * (|t| + 2) ^ δ) * (C_zeta * (|t| + 2) ^ δ) := by
          rw [hnorm_pi]
          have hpi_nn : 0 ≤ Real.pi ^ (σ₁ - 1 / 2) := Real.rpow_nonneg Real.pi_pos.le _
          have hgam_nn : 0 ≤ (C_γ / c_γ) * (|t| + 2) ^ δ := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hG_ratio_bd hpi_nn) hzeta_1s_bd
            (norm_nonneg _) (mul_nonneg hpi_nn hgam_nn)
    _ = ((Real.pi ^ (σ₁ - 1 / 2)) * (C_γ / c_γ) * C_zeta) *
          ((|t| + 2) ^ δ * (|t| + 2) ^ δ) := by ring
    _ = ((Real.pi ^ (σ₁ - 1 / 2)) * (C_γ / c_γ) * C_zeta) * (|t| + 2) ^ (2 * δ) := by
          rw [hpow_add]
    _ ≤ C * (|t| + 2) ^ (2 * δ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

/-- **Conditional implication**: the Riemann Hypothesis implies the Lindelöf Hypothesis
(`RiemannHypothesisProp → LindelofHypothesisProp`). -/
theorem riemannHypothesisProp_implies_lindelof (hRH : RiemannHypothesisProp) :
    LindelofHypothesisProp := by
  rw [lindelofHypothesisProp_iff_verticalOrder]
  have hvo_half : verticalOrder riemannZeta (1 / 2) = 0 := by
    refine le_antisymm ?_ (verticalOrder_nonneg riemannZeta (1 / 2))
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rw [zero_add]
    let δ : ℝ := min (ε / 2) (1 / 4)
    have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ_le : δ ≤ 1 / 4 := min_le_right _ _
    let σ₁ : ℝ := 1 / 2 - δ
    let σ₂ : ℝ := 1 / 2 + δ
    have hσ₁_pos : 0 < σ₁ := by dsimp only [σ₁]; linarith
    have hσ₁₂ : σ₁ < σ₂ := by dsimp only [σ₁, σ₂]; linarith
    have hσ₂_le1 : σ₂ ≤ 1 := by dsimp only [σ₂]; linarith
    obtain ⟨C₁, _, hbd₁⟩ := norm_riemannZeta_reflected_strip_of_RH hRH hδ0 hδ_le
    obtain ⟨C₂, _, hbd₂⟩ :=
      riemannZeta_and_inv_bounds_of_riemannHypothesisProp hRH (σ₀ := σ₂)
        (by dsimp only [σ₂]; linarith) hδ0
    have hvo₁ : HasVerticalOrder zetaStripAuxLH σ₁ (2 * δ) := by
      rw [hasVerticalOrder_zetaStripAuxLH_iff hσ₁_pos.le]
      refine Asymptotics.isBigO_iff.mpr ⟨C₁, ?_⟩
      filter_upwards [Filter.eventually_comap.mpr
        ((eventually_ge_atTop (4 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t ht
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact hbd₁ t ht
    have hvo₂ : HasVerticalOrder zetaStripAuxLH σ₂ δ := by
      rw [hasVerticalOrder_zetaStripAuxLH_iff (by linarith : 0 ≤ σ₂)]
      refine Asymptotics.isBigO_iff.mpr ⟨C₂, ?_⟩
      filter_upwards [Filter.eventually_comap.mpr
        ((eventually_ge_atTop (4 : ℝ)).mono fun _ hb _ h ↦ h ▸ hb)] with t ht
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact (hbd₂ le_rfl ht).1
    have hdiffCont : DiffContOnCl ℂ zetaStripAuxLH (verticalStripOpen σ₁ σ₂) := by
      have hcl : closure (verticalStripOpen σ₁ σ₂) ⊆ verticalStripClosed σ₁ σ₂ :=
        (isClosed_Icc.preimage Complex.continuous_re).closure_subset_iff.mpr
          (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩)
      have hdiff_cl : DifferentiableOn ℂ zetaStripAuxLH (verticalStripClosed σ₁ σ₂) :=
        differentiableOn_zetaStripAuxLH_right.mono fun z hz ↦ by
          have hre : σ₁ ≤ z.re := hz.1
          change (-1 : ℝ) < z.re
          linarith
      exact ⟨hdiff_cl.mono (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩), hdiff_cl.continuousOn.mono hcl⟩
    obtain ⟨A, hA_nn, hA_bd⟩ := zetaStripAuxLH_poly_on_strip hσ₁_pos hσ₁₂ hσ₂_le1
    have hinterp := verticalOrder_le_linearInterp_of_poly hσ₁₂ hdiffCont hA_nn hA_bd
      ⟨2 * δ, by positivity, hvo₁⟩ ⟨δ, hδ0.le, hvo₂⟩
      (⟨by dsimp only [σ₁]; linarith, by dsimp only [σ₂]; linarith⟩ : (1 / 2 : ℝ) ∈ Set.Icc σ₁ σ₂)
    have hle₁ : verticalOrder zetaStripAuxLH σ₁ ≤ 2 * δ :=
      verticalOrder_le_of_hasVerticalOrder (by positivity) hvo₁
    have hle₂ : verticalOrder zetaStripAuxLH σ₂ ≤ δ :=
      verticalOrder_le_of_hasVerticalOrder hδ0.le hvo₂
    have hlin_bd : linearInterp σ₁ σ₂ (verticalOrder zetaStripAuxLH σ₁)
        (verticalOrder zetaStripAuxLH σ₂) (1 / 2) ≤ (3 * δ) / 2 := by
      dsimp only [linearInterp]
      have hc1 : σ₂ - 1 / 2 = δ := by dsimp only [σ₂]; ring
      have hc2 : 1 / 2 - σ₁ = δ := by dsimp only [σ₁]; ring
      have hden : σ₂ - σ₁ = 2 * δ := by dsimp only [σ₁, σ₂]; ring
      rw [hc1, hc2, hden]
      have hdiv_nn : 0 ≤ δ / (2 * δ) := by positivity
      calc
        verticalOrder zetaStripAuxLH σ₁ * δ / (2 * δ) +
            verticalOrder zetaStripAuxLH σ₂ * δ / (2 * δ)
            = verticalOrder zetaStripAuxLH σ₁ * (δ / (2 * δ)) +
                verticalOrder zetaStripAuxLH σ₂ * (δ / (2 * δ)) := by ring
        _ ≤ (2 * δ) * (δ / (2 * δ)) + δ * (δ / (2 * δ)) :=
            add_le_add (mul_le_mul_of_nonneg_right hle₁ hdiv_nn)
              (mul_le_mul_of_nonneg_right hle₂ hdiv_nn)
        _ = (3 * δ) / 2 := by field_simp [hδ0.ne']; ring
    rw [verticalOrder_zetaStripAuxLH_eq (by norm_num)] at hinterp
    linarith [min_le_left (ε / 2) (1 / 4)]
  intro σ hσ
  rcases le_or_gt 1 σ with hge1 | hlt1
  · exact verticalOrder_riemannZeta_eq_zero_of_one_le hge1
  · have hdiffCont : DiffContOnCl ℂ zetaStripAuxLH (verticalStripOpen (1 / 2) 1) := by
      have hcl : closure (verticalStripOpen (1 / 2) 1) ⊆ verticalStripClosed (1 / 2) 1 :=
        (isClosed_Icc.preimage Complex.continuous_re).closure_subset_iff.mpr
          (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩)
      have hdiff_cl : DifferentiableOn ℂ zetaStripAuxLH (verticalStripClosed (1 / 2) 1) :=
        differentiableOn_zetaStripAuxLH_right.mono fun z hz ↦ by
          have hre : (1 / 2 : ℝ) ≤ z.re := hz.1
          change (-1 : ℝ) < z.re
          linarith
      exact ⟨hdiff_cl.mono (fun z hz ↦ ⟨hz.1.le, hz.2.le⟩), hdiff_cl.continuousOn.mono hcl⟩
    obtain ⟨A, hA_nn, hA_bd⟩ := zetaStripAuxLH_poly_on_strip
      (σ₁ := 1 / 2) (σ₂ := 1) (by norm_num) (by norm_num) le_rfl
    have hfin₁ : ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧ HasVerticalOrder zetaStripAuxLH (1 / 2) μ₁ := by
      refine ⟨1, zero_le_one, ?_⟩
      rw [hasVerticalOrder_zetaStripAuxLH_iff (by norm_num)]
      exact hasVerticalOrder_of_verticalOrder_lt (hasFiniteVerticalOrder_riemannZeta (by norm_num))
        (by rw [hvo_half]; norm_num)
    have hfin₂ : ∃ μ₂ : ℝ, 0 ≤ μ₂ ∧ HasVerticalOrder zetaStripAuxLH 1 μ₂ := by
      refine ⟨1, zero_le_one, ?_⟩
      rw [hasVerticalOrder_zetaStripAuxLH_iff zero_le_one]
      exact hasVerticalOrder_of_verticalOrder_lt (hasFiniteVerticalOrder_riemannZeta zero_le_one)
        (by rw [verticalOrder_riemannZeta_eq_zero_of_one_le le_rfl]; norm_num)
    have hinterp := verticalOrder_le_linearInterp_of_poly (by norm_num : (1 / 2 : ℝ) < 1)
      hdiffCont hA_nn hA_bd hfin₁ hfin₂ ⟨hσ, hlt1.le⟩
    have haux_half : verticalOrder zetaStripAuxLH (1 / 2) = 0 := by
      rw [verticalOrder_zetaStripAuxLH_eq (by norm_num), hvo_half]
    have haux_one : verticalOrder zetaStripAuxLH 1 = 0 := by
      rw [verticalOrder_zetaStripAuxLH_eq zero_le_one,
        verticalOrder_riemannZeta_eq_zero_of_one_le le_rfl]
    rw [haux_half, haux_one] at hinterp
    have hlin0 : linearInterp (1 / 2) 1 0 0 σ = 0 := by simp [linearInterp]
    rw [hlin0, verticalOrder_zetaStripAuxLH_eq (by linarith)] at hinterp
    exact le_antisymm hinterp (verticalOrder_nonneg riemannZeta σ)

end LindelofHypothesis

end

end AnalyticNumberTheory.RiemannZeta

