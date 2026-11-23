import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.HadamardFactorization
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import AnalyticNumberTheory.DirichletSeries.Convergence
import AnalyticNumberTheory.DirichletSeries.EulerProduct
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-!
# Hadamard Factorization, Zero Symmetries, and Partial Fractions of `ζ'/ζ`

This file develops the global product structure of `xi` and `riemannZeta` across `ℂ`:

- The set `CriticalStripZeros` of non-trivial zeros in `0 < Re s < 1`, its identification with
  `xi ⁻¹' {0}`, discreteness, compactness finiteness, and the symmetries `ρ ↦ 1 - ρ`,
  `ρ ↦ star ρ`, and `ρ ↦ 1 - star ρ` preserving `analyticOrderAt`.
- Infinitude of `CriticalStripZeros` and Jensen unit-interval zero density
  `unitIntervalZeroCount T ≤ C * log (|T| + 2)`, together with convergence and `O(log (|T| + 2))`
  upper bound for `∑_ρ m_ρ / (1 + (T - Im ρ)^2)`.
- Hadamard factorization of `xi` (`xi z = (1 / 2) * exp (B * z) * canonicalProduct a 1 z`)
  and the partial fraction expansion of `deriv riemannZeta / riemannZeta` involving `digamma (s/2 + 1)`.
- The holomorphic logarithm `logZeta` on `1 < Re s` with `exp (logZeta s) = riemannZeta s` and
  `HasDerivAt logZeta (deriv riemannZeta s / riemannZeta s) s`.
-/

open Complex Filter Topology Metric Set Real
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.EntireFunctions
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-! ### Non-trivial Zeros, Discreteness, and Symmetries -/

/-- The set of non-trivial zeros of `riemannZeta` inside the critical strip `0 < Re s < 1`. -/
def CriticalStripZeros : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Membership characterization for `CriticalStripZeros`. -/
theorem mem_criticalStripZeros {ρ : ℂ} :
    ρ ∈ CriticalStripZeros ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 :=
  Iff.rfl

/-- `CriticalStripZeros` coincides with the full zero set of the completed zeta function `xi`. -/
theorem criticalStripZeros_eq_xi_zeros :
    CriticalStripZeros = xi ⁻¹' {0} := by
  ext ρ
  simp only [mem_criticalStripZeros, Set.mem_preimage, Set.mem_singleton_iff, xi_eq_zero_iff]

/-- Every non-trivial zero belongs to Mathlib's `riemannZetaZeros`. -/
theorem criticalStripZeros_subset_riemannZetaZeros :
    CriticalStripZeros ⊆ riemannZetaZeros := fun _ hρ ↦ hρ.1

/-- Any compact subset of `ℂ` meets `CriticalStripZeros` in only finitely many points. -/
theorem isCompact_inter_criticalStripZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ CriticalStripZeros).Finite :=
  (hS.inter_riemannZetaZeros_finite).subset fun _ ⟨hS', hρ⟩ ↦ ⟨hS', hρ.1⟩

/-- Every horizontal strip `[T₁, T₂]` contains only finitely many non-trivial zeros. -/
theorem criticalStripZeros_strip_finite (T₁ T₂ : ℝ) :
    {ρ ∈ CriticalStripZeros | ρ.im ∈ Set.Icc T₁ T₂}.Finite := by
  let S : Set ℂ := {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc T₁ T₂}
  have hS_eq : S = Complex.equivRealProdCLM.symm '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc T₁ T₂) := by
    ext z
    simp only [S, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
    constructor
    · intro hz
      refine ⟨(z.re, z.im), hz, ?_⟩
      change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) = z
      exact Complex.equivRealProdCLM.symm_apply_apply z
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
  have hS_comp : IsCompact S := by
    rw [hS_eq]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  refine (isCompact_inter_criticalStripZeros_finite hS_comp).subset fun ρ hρ ↦ ?_
  exact ⟨⟨⟨hρ.1.2.1.le, hρ.1.2.2.le⟩, hρ.2⟩, hρ.1⟩

/-- Symmetry `ρ ↦ 1 - ρ` on `CriticalStripZeros`. -/
theorem one_sub_mem_criticalStripZeros {ρ : ℂ} (hρ : ρ ∈ CriticalStripZeros) :
    1 - ρ ∈ CriticalStripZeros := by
  rw [criticalStripZeros_eq_xi_zeros] at hρ ⊢
  simpa [xi_one_sub] using hρ

/-- Schwarz reflection symmetry `ρ ↦ star ρ` on `CriticalStripZeros`. -/
theorem star_mem_criticalStripZeros {ρ : ℂ} (hρ : ρ ∈ CriticalStripZeros) :
    star ρ ∈ CriticalStripZeros := by
  rw [criticalStripZeros_eq_xi_zeros] at hρ ⊢
  change xi (starRingEnd ℂ ρ) = 0
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hρ
  rw [xi_conj, hρ, map_zero]

/-- Reflection symmetry `ρ ↦ 1 - star ρ` across `Re s = 1 / 2` (preserving `Im ρ`). -/
theorem one_sub_star_mem_criticalStripZeros {ρ : ℂ} (hρ : ρ ∈ CriticalStripZeros) :
    1 - star ρ ∈ CriticalStripZeros :=
  one_sub_mem_criticalStripZeros (star_mem_criticalStripZeros hρ)

private lemma xi_eventuallyEq_pre_mul_zeta {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    xi =ᶠ[𝓝 s] fun z ↦
      ((1 / 2 : ℂ) * z * (z - 1) * (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) * riemannZeta z := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    isOpen_Ioo.preimage Complex.continuous_re
  filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
  have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
  exact xi_eq_formula_of_re_pos hz.1 hz1

/-- In the open critical strip `0 < Re s < 1`, the analytic order of `riemannZeta` coincides
with the analytic order of `xi`. -/
theorem analyticOrderAt_riemannZeta_eq_xi {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderAt riemannZeta s = analyticOrderAt xi s := by
  let pre : ℂ → ℂ := fun z ↦
    (1 / 2 : ℂ) * z * (z - 1) * (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)
  have hpre_diff : DifferentiableOn ℂ pre {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz_re : (0 : ℝ) < z.re := hz
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hG : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := fun m h ↦ by
      have hre := congrArg Complex.re h
      have hdiv_re : (z / 2).re = z.re / 2 := by simp
      rw [hdiv_re, Complex.neg_re, Complex.natCast_re] at hre
      have : (0 : ℝ) < z.re / 2 := by linarith
      have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact (((((differentiableAt_const (1 / 2 : ℂ)).mul differentiableAt_id).mul
      (differentiableAt_id.sub_const 1)).mul
      (((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hπ))).mul
      ((differentiableAt_gamma hG).comp z (differentiableAt_id.div_const 2))).differentiableWithinAt
  have hpre_an : AnalyticAt ℂ pre s :=
    (hpre_diff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)) s hs0
  have hpre_ne : pre s ≠ 0 := by
    have hs0' : s ≠ 0 := fun h ↦ by simp [h] at hs0
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hs1
    have hπ : (π : ℂ) ^ (-s / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hG : Complex.Gamma (s / 2) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp [hs0])
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0') hs1') hπ) hG
  have hs_ne1 : s ≠ 1 := fun h ↦ by simp [h] at hs1
  have hzeta_diff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz ↦
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hzeta_an : AnalyticAt ℂ riemannZeta s :=
    (hzeta_diff.analyticOnNhd isOpen_ne) s hs_ne1
  have hev : xi =ᶠ[𝓝 s] pre * riemannZeta := xi_eventuallyEq_pre_mul_zeta hs0 hs1
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hpre_an hzeta_an,
    hpre_an.analyticOrderAt_eq_zero.mpr hpre_ne, zero_add]

/-- Natural-valued multiplicity equality `analyticOrderNatAt riemannZeta s = analyticOrderNatAt xi s`
for `0 < Re s < 1`. -/
theorem analyticOrderNatAt_riemannZeta_eq_xi {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderNatAt riemannZeta s = analyticOrderNatAt xi s := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_eq_xi hs0 hs1]

/-- Invariance of analytic multiplicity of `xi` under `s ↦ 1 - s`. -/
theorem analyticOrderAt_xi_one_sub (s : ℂ) :
    analyticOrderAt xi (1 - s) = analyticOrderAt xi s := by
  have hg_an : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s := by fun_prop
  have hg_deriv : deriv (fun z : ℂ ↦ 1 - z) s ≠ 0 := by
    have hd : HasDerivAt (fun z : ℂ ↦ 1 - z) (0 - 1 : ℂ) s :=
      (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id' s)
    rw [hd.deriv]
    norm_num
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg_an hg_deriv
  have heq : (xi ∘ fun z : ℂ ↦ 1 - z) = xi := by
    ext z
    exact xi_one_sub z
  rw [heq] at hcomp
  exact hcomp.symm

/-- Invariance of analytic multiplicity of `xi` under complex conjugation `s ↦ star s`. -/
theorem analyticOrderAt_xi_star (s : ℂ) :
    analyticOrderAt xi (star s) = analyticOrderAt xi s := by
  have hxi_ne : xi ≠ 0 := fun h ↦ by
    have := congrFun h 0
    rw [xi_zero] at this
    norm_num at this
  have htop : analyticOrderAt xi s ≠ ⊤ :=
    analyticOrderAt_ne_top_of_differentiable_ne_zero differentiable_xi hxi_ne s
  let n : ℕ := analyticOrderNatAt xi s
  have hord : analyticOrderAt xi s = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt htop).symm
  have hxi_an : AnalyticAt ℂ xi s := analyticOnNhd_xi s (Set.mem_univ s)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hxi_an.analyticOrderAt_eq_natCast.mp hord
  obtain ⟨ε, hε, hball_diff, hball_eq⟩ : ∃ ε : ℝ, 0 < ε ∧
      DifferentiableOn ℂ g (Metric.ball s ε) ∧
      ∀ z ∈ Metric.ball s ε, xi z = (z - s) ^ n * g z := by
    have hev_an : ∀ᶠ z in 𝓝 s, AnalyticAt ℂ g z := hg_an.eventually_analyticAt
    obtain ⟨ε, hε, hmem⟩ := Metric.eventually_nhds_iff_ball.mp (hev_an.and hfg)
    refine ⟨ε, hε, fun z hz ↦ (hmem z hz).1.differentiableAt.differentiableWithinAt,
      fun z hz ↦ ?_⟩
    simpa [smul_eq_mul] using (hmem z hz).2
  let g_conj : ℂ → ℂ := fun w ↦ star (g (star w))
  have hg_conj_diff : DifferentiableOn ℂ g_conj (Metric.ball (star s) ε) := by
    intro w hw
    have hw_star : star w ∈ Metric.ball s ε := by
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      have hnorm : ‖star w - s‖ = ‖w - star s‖ := by
        rw [← Complex.norm_conj]
        change ‖starRingEnd ℂ (starRingEnd ℂ w - s)‖ = ‖w - starRingEnd ℂ s‖
        simp
      rwa [hnorm]
    have hg_at : HasDerivAt g (deriv g (star w)) (star w) :=
      (hball_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hw_star)).hasDerivAt
    have hsl : Tendsto (slope g_conj w) (𝓝[≠] w) (𝓝 (star (deriv g (star w)))) := by
      have hsl_g : Tendsto (slope g (star w)) (𝓝[≠] star w) (𝓝 (deriv g (star w))) :=
        hg_at.tendsto_slope
      have hstar_tend : Tendsto (star : ℂ → ℂ) (𝓝[≠] w) (𝓝[≠] star w) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨(continuous_star.continuousAt.mono_left nhdsWithin_le_nhds), ?_⟩
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact fun h ↦ hz (star_injective h)
      have hcont_star : Tendsto (fun z : ℂ ↦ star (slope g (star w) (star z)))
          (𝓝[≠] w) (𝓝 (star (deriv g (star w)))) :=
        continuous_star.continuousAt.tendsto.comp (hsl_g.comp hstar_tend)
      refine hcont_star.congr fun z ↦ ?_
      simp only [g_conj, slope_def_module, smul_eq_mul, star_mul, star_sub, star_inv₀, star_star]
      ring
    have hd_at : HasDerivAt g_conj (star (deriv g (star w))) w :=
      hasDerivAt_iff_tendsto_slope.mpr hsl
    exact hd_at.differentiableAt.differentiableWithinAt
  have hg_conj_an : AnalyticAt ℂ g_conj (star s) :=
    (hg_conj_diff.analyticOnNhd Metric.isOpen_ball) (star s) (Metric.mem_ball_self hε)
  have hg_conj_ne : g_conj (star s) ≠ 0 := by
    simp only [g_conj, star_star, ne_eq, star_eq_zero]
    exact hg_ne
  have hev_conj : ∀ᶠ z in 𝓝 (star s), xi z = (z - star s) ^ n • g_conj z := by
    filter_upwards [Metric.ball_mem_nhds (star s) hε] with z hz
    have hz_star : star z ∈ Metric.ball s ε := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hnorm : ‖star z - s‖ = ‖z - star s‖ := by
        rw [← Complex.norm_conj]
        change ‖starRingEnd ℂ (starRingEnd ℂ z - s)‖ = ‖z - starRingEnd ℂ s‖
        simp
      rwa [hnorm]
    have hxi_conj : xi z = star (xi (star z)) := by
      have hc := (xi_conj (starRingEnd ℂ z)).symm
      change xi z = starRingEnd ℂ (xi (starRingEnd ℂ z))
      simp
    rw [hxi_conj, hball_eq (star z) hz_star, star_mul, star_pow, star_sub, star_star,
      smul_eq_mul, mul_comm]
  exact ((analyticOnNhd_xi (star s) (Set.mem_univ (star s))).analyticOrderAt_eq_natCast.mpr
    ⟨g_conj, hg_conj_an, hg_conj_ne, hev_conj⟩).trans hord.symm

/-- Invariance of zero multiplicity of `riemannZeta` under `ρ ↦ 1 - ρ` in `0 < Re ρ < 1`. -/
theorem analyticOrderNatAt_riemannZeta_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt riemannZeta (1 - ρ) = analyticOrderNatAt riemannZeta ρ := by
  have h0' : 0 < (1 - ρ).re := by simp [h1]
  have h1' : (1 - ρ).re < 1 := by simp [h0]
  rw [analyticOrderNatAt_riemannZeta_eq_xi h0' h1', analyticOrderNatAt_riemannZeta_eq_xi h0 h1]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_xi_one_sub]

/-- Invariance of zero multiplicity of `riemannZeta` under `ρ ↦ star ρ` in `0 < Re ρ < 1`. -/
theorem analyticOrderNatAt_riemannZeta_star {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt riemannZeta (star ρ) = analyticOrderNatAt riemannZeta ρ := by
  have h0' : 0 < (star ρ).re := by simpa using h0
  have h1' : (star ρ).re < 1 := by simpa using h1
  rw [analyticOrderNatAt_riemannZeta_eq_xi h0' h1', analyticOrderNatAt_riemannZeta_eq_xi h0 h1]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_xi_star]

/-- Invariance of zero multiplicity of `riemannZeta` under `ρ ↦ 1 - star ρ` in `0 < Re ρ < 1`. -/
theorem analyticOrderNatAt_riemannZeta_one_sub_star {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt riemannZeta (1 - star ρ) = analyticOrderNatAt riemannZeta ρ := by
  have h0' : 0 < (star ρ).re := by simpa using h0
  have h1' : (star ρ).re < 1 := by simpa using h1
  rw [analyticOrderNatAt_riemannZeta_one_sub h0' h1',
    analyticOrderNatAt_riemannZeta_star h0 h1]

/-! ### Infinitude of Non-trivial Zeros and Jensen Density -/

private lemma xi_ne_zero_fn : xi ≠ 0 := fun h ↦ by
  have := congrFun h 0
  rw [xi_zero] at this
  norm_num at this

private lemma subproduct_factorial_ge_pow (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ m ≤ ((Nat.factorial (2 * m - 1)) : ℝ) := by
  have hprod_le : m ^ m ≤ ∏ k ∈ Finset.Ico m (2 * m), k := by
    have hcard : (Finset.Ico m (2 * m)).card = m := by
      rw [Nat.card_Ico]
      omega
    calc
      m ^ m = ∏ _k ∈ Finset.Ico m (2 * m), m := by
        rw [Finset.prod_const, hcard]
      _ ≤ ∏ k ∈ Finset.Ico m (2 * m), k :=
        Finset.prod_le_prod fun k hk ↦ (Finset.mem_Ico.mp hk).1
  have hle_fac : ∏ k ∈ Finset.Ico m (2 * m), k ≤ Nat.factorial (2 * m - 1) := by
    have hsub : Finset.Ico m (2 * m) ⊆ Finset.Icc 1 (2 * m - 1) := by
      intro k hk
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
      omega
    have hfac : ∏ k ∈ Finset.Icc 1 (2 * m - 1), k = Nat.factorial (2 * m - 1) := by
      induction (2 * m - 1) with
      | zero => simp
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.factorial_succ, mul_comm]
    rw [← hfac]
    exact Finset.prod_le_prod_of_subset_of_one_le hsub fun k hk _ ↦ by
      simp only [Finset.mem_Icc] at hk
      exact hk.1
  exact_mod_cast hprod_le.trans hle_fac

private lemma norm_xi_four_mul_ge (m : ℕ) (hm : 1 ≤ m) :
    (1 / 2 : ℝ) * ((m : ℝ) / Real.pi ^ 2) ^ m ≤ ‖xi ((4 * m : ℕ) : ℂ)‖ := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs_re : (0 : ℝ) < ((4 * m : ℕ) : ℂ).re := by simp; linarith
  have hs1 : ((4 * m : ℕ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [natCast_re, one_re] at this
    have : 4 * m = 1 := by exact_mod_cast this
    omega
  rw [xi_eq_formula_of_re_pos hs_re hs1]
  have hnorm_prod : ‖(1 / 2 : ℂ) * ((4 * m : ℕ) : ℂ) * (((4 * m : ℕ) : ℂ) - 1) *
      (π : ℂ) ^ (-((4 * m : ℕ) : ℂ) / 2) * Complex.Gamma (((4 * m : ℕ) : ℂ) / 2) *
      riemannZeta ((4 * m : ℕ) : ℂ)‖ =
      ‖(1 / 2 : ℂ) * ((4 * m : ℕ) : ℂ) * (((4 * m : ℕ) : ℂ) - 1)‖ *
        ‖(π : ℂ) ^ (-((4 * m : ℕ) : ℂ) / 2)‖ *
        ‖Complex.Gamma (((4 * m : ℕ) : ℂ) / 2)‖ * ‖riemannZeta ((4 * m : ℕ) : ℂ)‖ := by
    simp only [norm_mul]
  rw [hnorm_prod]
  have hpre : 1 ≤ ‖(1 / 2 : ℂ) * ((4 * m : ℕ) : ℂ) * (((4 * m : ℕ) : ℂ) - 1)‖ := by
    have heq : (1 / 2 : ℂ) * ((4 * m : ℕ) : ℂ) * (((4 * m : ℕ) : ℂ) - 1) =
        (((1 / 2 : ℝ) * (4 * m) * (4 * m - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]
    nlinarith
  have hpi : ‖(π : ℂ) ^ (-((4 * m : ℕ) : ℂ) / 2)‖ = (Real.pi ^ 2) ^ (-(m : ℝ)) := by
    have hdiv : -((4 * m : ℕ) : ℂ) / 2 = (((-2 * m : ℤ) : ℝ) : ℂ) := by push_cast; ring
    rw [hdiv, ← Complex.ofReal_cpow Real.pi_nonneg, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg Real.pi_nonneg _),
      Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos (sq_pos_of_pos Real.pi_pos),
      Real.log_pow, Nat.cast_ofNat]
    congr 1; push_cast; ring
  have hG : ((m : ℝ) ^ m) ≤ ‖Complex.Gamma (((4 * m : ℕ) : ℂ) / 2)‖ := by
    have hdiv : ((4 * m : ℕ) : ℂ) / 2 = ((2 * m - 1 : ℕ) : ℂ) + 1 := by
      have hge : 1 ≤ 2 * m := by omega
      push_cast [hge]
      ring
    rw [hdiv, Complex.Gamma_nat_eq_factorial, Complex.norm_natCast]
    exact subproduct_factorial_ge_pow m hm
  have hzeta : (1 / 2 : ℝ) ≤ ‖riemannZeta ((4 * m : ℕ) : ℂ)‖ := by
    have hge := norm_riemannZeta_ge_of_one_lt_re (σ := ((4 * m : ℕ) : ℝ))
      (by exact_mod_cast (by omega : 1 < 4 * m)) 0
    have hz_eq : (((4 * m : ℕ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((4 * m : ℕ) : ℂ) := by simp
    rw [hz_eq] at hge
    have hfrac : (1 / 2 : ℝ) ≤ (((4 * m : ℕ) : ℝ) - 1) / ((4 * m : ℕ) : ℝ) := by
      have h2m : (2 : ℝ) ≤ (4 * m : ℕ) := by exact_mod_cast (by omega : 2 ≤ 4 * m)
      rw [le_div_iff₀ (by linarith)]
      linarith
    exact hfrac.trans hge
  have hpow_eq : (Real.pi ^ 2) ^ (-(m : ℝ)) * (m : ℝ) ^ m = ((m : ℝ) / Real.pi ^ 2) ^ m := by
    rw [← Real.rpow_natCast m m, ← Real.rpow_natCast ((m : ℝ) / Real.pi ^ 2) m,
      Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
      div_eq_mul_inv, mul_comm]
  calc
    (1 / 2 : ℝ) * ((m : ℝ) / Real.pi ^ 2) ^ m
        = 1 * (Real.pi ^ 2) ^ (-(m : ℝ)) * (m : ℝ) ^ m * (1 / 2 : ℝ) := by
      rw [← hpow_eq]; ring
    _ ≤ ‖(1 / 2 : ℂ) * ((4 * m : ℕ) : ℂ) * (((4 * m : ℕ) : ℂ) - 1)‖ *
          ‖(π : ℂ) ^ (-((4 * m : ℕ) : ℂ) / 2)‖ *
          ‖Complex.Gamma (((4 * m : ℕ) : ℂ) / 2)‖ * ‖riemannZeta ((4 * m : ℕ) : ℂ)‖ := by
      rw [← hpi]
      gcongr

private lemma norm_weierstrassPrimaryFactor_one_le (z : ℂ) :
    ‖weierstrassPrimaryFactor 1 z‖ ≤ Real.exp (2 * ‖z‖) := by
  simp only [weierstrassPrimaryFactor, Finset.Icc_self, Finset.sum_singleton, pow_one]
  rw [Nat.cast_one, div_one, norm_mul, Complex.norm_exp]
  have h1 : ‖1 - z‖ ≤ 1 + ‖z‖ := (norm_sub_le (1 : ℂ) z).trans (by rw [norm_one])
  have h2 : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have h3 : Real.exp z.re ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr (Complex.re_le_norm z)
  calc
    ‖1 - z‖ * Real.exp z.re ≤ Real.exp ‖z‖ * Real.exp ‖z‖ :=
      mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ‖z‖) := by rw [← Real.exp_add]; ring_nf

private lemma not_finite_zeros_xi :
    ¬ ∃ (zs : List ℂ) (A B : ℂ),
      (∀ a ∈ zs, a ≠ 0) ∧ (∀ z ≠ 0, zs.count z = analyticOrderNatAt xi z) ∧
      (∀ z : ℂ, xi z = z ^ analyticOrderNatAt xi 0 * Complex.exp (A + B * z) *
        (zs.map (fun a ↦ weierstrassPrimaryFactor 1 (z / a))).prod) := by
  rintro ⟨zs, A, B, hzs_ne, _, hform⟩
  have hord0 : analyticOrderNatAt xi 0 = 0 := by
    have hxi0 : xi 0 ≠ 0 := by rw [xi_zero]; norm_num
    have h0 := (analyticOnNhd_xi 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hxi0
    simp [analyticOrderNatAt, h0]
  let S : ℝ := (zs.map (fun a : ℂ ↦ 2 / ‖a‖)).sum
  have hS_nn : 0 ≤ S := List.sum_nonneg fun x hx ↦ by
    rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
    positivity
  let K : ℝ := ‖B‖ + S
  have hK_nn : 0 ≤ K := by positivity
  let C : ℝ := Real.exp A.re
  have hC_pos : 0 < C := Real.exp_pos _
  have hbound : ∀ x : ℝ, 0 ≤ x → ‖xi (x : ℂ)‖ ≤ C * Real.exp (K * x) := by
    intro x hx
    rw [hform (x : ℂ), hord0, pow_zero, one_mul, norm_mul, Complex.norm_exp]
    have hexp_bd : Real.exp (A + B * (x : ℂ)).re ≤ C * Real.exp (‖B‖ * x) := by
      have hre : (A + B * (x : ℂ)).re = A.re + B.re * x := by simp
      rw [hre, Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC_pos.le
      exact mul_le_mul_of_nonneg_right (Complex.re_le_norm B) hx
    have hprod_bd : ∀ (l : List ℂ), (∀ a ∈ l, a ≠ 0) →
        ‖(l.map (fun a ↦ weierstrassPrimaryFactor 1 ((x : ℂ) / a))).prod‖ ≤
          Real.exp ((l.map (fun a : ℂ ↦ 2 / ‖a‖)).sum * x) := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, norm_mul, add_mul,
          Real.exp_add]
        have hf_bd : ‖weierstrassPrimaryFactor 1 ((x : ℂ) / a)‖ ≤ Real.exp ((2 / ‖a‖) * x) := by
          have h := norm_weierstrassPrimaryFactor_one_le ((x : ℂ) / a)
          have hnorm_eq : ‖(x : ℂ) / a‖ = x / ‖a‖ := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
          rw [hnorm_eq] at h
          have heq : 2 * (x / ‖a‖) = (2 / ‖a‖) * x := by ring
          rwa [heq] at h
        exact mul_le_mul hf_bd (ih fun b hb ↦ hl b (by simp [hb]))
          (norm_nonneg _) (Real.exp_pos _).le
    calc
      Real.exp (A + B * (x : ℂ)).re *
          ‖(zs.map (fun a ↦ weierstrassPrimaryFactor 1 ((x : ℂ) / a))).prod‖
          ≤ (C * Real.exp (‖B‖ * x)) * Real.exp (S * x) :=
        mul_le_mul hexp_bd (hprod_bd zs hzs_ne) (norm_nonneg _) (by positivity)
      _ = C * Real.exp (K * x) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2; dsimp only [K]; ring
  let M₀ : ℝ := Real.pi ^ 2 * (2 * Real.exp (4 * K))
  let m : ℕ := max 2 (Nat.ceil (max M₀ (2 * C)) + 1)
  have hm1 : 1 ≤ m := by omega
  have hm_gt_M₀ : M₀ < m := by
    have h1 : (Nat.ceil (max M₀ (2 * C)) + 1 : ℝ) ≤ m := by exact_mod_cast le_max_right 2 _
    have h2 : max M₀ (2 * C) ≤ Nat.ceil (max M₀ (2 * C)) := Nat.le_ceil _
    linarith [le_max_left M₀ (2 * C)]
  have hm_gt_2C : 2 * C < m := by
    have h1 : (Nat.ceil (max M₀ (2 * C)) + 1 : ℝ) ≤ m := by exact_mod_cast le_max_right 2 _
    have h2 : max M₀ (2 * C) ≤ Nat.ceil (max M₀ (2 * C)) := Nat.le_ceil _
    linarith [le_max_right M₀ (2 * C)]
  have hpi2_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hbase_gt : 2 * Real.exp (4 * K) < (m : ℝ) / Real.pi ^ 2 := by
    rw [lt_div_iff₀ hpi2_pos]
    dsimp only [M₀] at hm_gt_M₀
    linarith
  have hpow_gt : (2 * Real.exp (4 * K)) ^ m < ((m : ℝ) / Real.pi ^ 2) ^ m :=
    pow_lt_pow_left₀ hbase_gt (by positivity) (by omega)
  have h2m_gt : 2 * C < (2 : ℝ) ^ m := by
    have : (m : ℝ) ≤ (2 : ℝ) ^ m := by
      have hnat : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
      exact_mod_cast hnat
    linarith
  have hlow : C * Real.exp (K * ((4 * m : ℕ) : ℝ)) < ‖xi ((4 * m : ℕ) : ℂ)‖ := by
    have hcexp : C * Real.exp (K * ((4 * m : ℕ) : ℝ)) <
        (1 / 2 : ℝ) * (2 * Real.exp (4 * K)) ^ m := by
      have hexp_eq : Real.exp (K * ((4 * m : ℕ) : ℝ)) = (Real.exp (4 * K)) ^ m := by
        rw [← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [mul_pow, hexp_eq]
      calc
        C * (Real.exp (4 * K)) ^ m < ((1 / 2 : ℝ) * (2 : ℝ) ^ m) * (Real.exp (4 * K)) ^ m :=
          mul_lt_mul_of_pos_right (by linarith) (pow_pos (Real.exp_pos _) _)
        _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ m * (Real.exp (4 * K)) ^ m) := by ring
    have hnorm := norm_xi_four_mul_ge m hm1
    have hstrict : (1 / 2 : ℝ) * (2 * Real.exp (4 * K)) ^ m <
        (1 / 2 : ℝ) * ((m : ℝ) / Real.pi ^ 2) ^ m := by linarith
    exact hcexp.trans (hstrict.trans_le hnorm)
  have hup := hbound ((4 * m : ℕ) : ℝ) (Nat.cast_nonneg _)
  exact lt_irrefl _ (hlow.trans_le (by simpa using hup))

/-- **Infinitude of non-trivial zeros**: `riemannZeta` has infinitely many zeros in the
critical strip `0 < Re s < 1`. -/
theorem infinite_criticalStripZeros : CriticalStripZeros.Infinite := by
  intro hfin
  have h_xi_fin : {z : ℂ | xi z = 0}.Finite := by
    have heq : {z : ℂ | xi z = 0} = CriticalStripZeros := by
      rw [criticalStripZeros_eq_xi_zeros]; rfl
    rw [heq]
    exact hfin
  rcases hadamard_logDeriv_genus_one differentiable_xi xi_ne_zero_fn zero_le_one
      entireOrderLe_xi_one one_lt_two with
    ⟨zs, A, B, hzs_ne, hzs_count, hform, _⟩ |
    ⟨a, _, _, ha_ne, ha_fin, ha_card, _, _, _⟩
  · exact not_finite_zeros_xi ⟨zs, A, B, hzs_ne, hzs_count, hform⟩
  · let S : Finset ℂ := h_xi_fin.toFinset
    let R : ℝ := 1 + ∑ z ∈ S, ‖z‖
    have hinf : ({n : ℕ | ‖a n‖ ≤ R}).Infinite := by
      have huniv : {n : ℕ | ‖a n‖ ≤ R} = Set.univ := by
        ext n
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        have hfin_fib : ({k : ℕ | a k = a n}).Finite :=
          (ha_fin ‖a n‖).subset fun k hk ↦ by
            simp only [Set.mem_ofPred_eq] at hk ⊢; rw [hk]
        have hpos : 0 < ({k : ℕ | a k = a n}).ncard := (Set.ncard_pos hfin_fib).mpr ⟨n, rfl⟩
        rw [ha_card (a n) (ha_ne n)] at hpos
        have hzero : xi (a n) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne'
        have ha_mem : a n ∈ S := h_xi_fin.mem_toFinset.mpr hzero
        have hle_sum : ‖a n‖ ≤ ∑ z ∈ S, ‖z‖ :=
          Finset.single_le_sum (fun z _ ↦ norm_nonneg z) ha_mem
        linarith
      rw [huniv]
      exact Set.infinite_univ
    exact hinf (ha_fin R)

/-- Number of non-trivial zeros (counted with multiplicity) of `riemannZeta` in the unit
horizontal strip `T ≤ Im ρ ≤ T + 1`. -/
noncomputable def unitIntervalZeroCount (T : ℝ) : ℕ := by
  classical
  exact ∑ᶠ ρ : ℂ, if ρ ∈ CriticalStripZeros ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1 then
    analyticOrderNatAt riemannZeta ρ else 0

private lemma unitIntervalZeroCount_eq_sum (T : ℝ) :
    unitIntervalZeroCount T =
      ∑ ρ ∈ (criticalStripZeros_strip_finite T (T + 1)).toFinset,
        analyticOrderNatAt riemannZeta ρ := by
  classical
  let S : Finset ℂ := (criticalStripZeros_strip_finite T (T + 1)).toFinset
  unfold unitIntervalZeroCount
  have hsupp : (fun ρ : ℂ ↦
      if ρ ∈ CriticalStripZeros ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1 then
        analyticOrderNatAt riemannZeta ρ else 0).support ⊆ (S : Set ℂ) := by
    intro ρ hρ
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hρ
    rcases hρ with ⟨⟨hcrit, h1, h2⟩, _⟩
    exact (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mpr ⟨hcrit, ⟨h1, h2⟩⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  have hmem := (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp hρ
  simp [hmem.1, hmem.2.1, hmem.2.2]

/-- **Jensen unit-interval zero density**: `unitIntervalZeroCount T ≤ C * Real.log (|T| + 2)`. -/
theorem unitIntervalZeroCount_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, (unitIntervalZeroCount T : ℝ) ≤ C * Real.log (|T| + 2) := by
  obtain ⟨Cs, hCs_pos, hCs_bd⟩ := norm_riemannZeta_critical_strip_le (ε := 1 / 2) (by norm_num)
  obtain ⟨C₁, hC₁_pos, hC₁_bd⟩ := norm_riemannZeta_re_ge_one_le
  let R : ℝ := 3 / 2
  let r : ℝ := 5 / 4
  have hr_pos : 0 < r := by norm_num
  have hrR : r < R := by norm_num
  have hlog_Rr_pos : 0 < Real.log (R / r) := Real.log_pos (by norm_num)
  let C_right : ℝ := max (max (3 * (Cs + 2) * 3) (2 * C₁ + 2)) 4
  let C_large : ℝ := 2 * (Real.log C_right + 1 + Real.log 3) / Real.log (R / r)
  let boxSet := criticalStripZeros_strip_finite (-4) 5
  let C_small : ℝ := ((∑ ρ ∈ boxSet.toFinset, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) / Real.log 2
  let C : ℝ := max C_large C_small + 1
  refine ⟨C, by positivity, fun T ↦ ?_⟩
  rw [unitIntervalZeroCount_eq_sum T]
  rcases le_or_gt |T| 4 with hT4 | hT4
  · have hsub : (criticalStripZeros_strip_finite T (T + 1)).toFinset ⊆ boxSet.toFinset := by
      intro ρ hρ
      have hm := (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp hρ
      refine boxSet.mem_toFinset.mpr ⟨hm.1, ?_⟩
      have hTab : -4 ≤ T ∧ T ≤ 4 := abs_le.mp hT4
      exact ⟨by linarith [hm.2.1], by linarith [hm.2.2]⟩
    have hsum_le :
        ((∑ ρ ∈ (criticalStripZeros_strip_finite T (T + 1)).toFinset,
          analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ boxSet.toFinset, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
      exact_mod_cast Finset.sum_le_sum_of_subset hsub
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog_le : Real.log 2 ≤ Real.log (|T| + 2) :=
      Real.log_le_log two_pos (by linarith [abs_nonneg T])
    calc
      ((∑ ρ ∈ (criticalStripZeros_strip_finite T (T + 1)).toFinset,
          analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ)
          ≤ C_small * Real.log 2 := by
        dsimp only [C_small]
        rw [div_mul_cancel₀ _ hlog2_pos.ne']
        exact hsum_le
      _ ≤ C_small * Real.log (|T| + 2) := mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ ≤ C * Real.log (|T| + 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by linarith [abs_nonneg T]))
        dsimp only [C]
        linarith [le_max_right C_large C_small]
  · let S_all : Finset ℂ := (criticalStripZeros_strip_finite T (T + 1)).toFinset
    let S_right : Finset ℂ := S_all.filter (fun ρ ↦ 1 / 2 ≤ ρ.re)
    let S_left : Finset ℂ := S_all.filter (fun ρ ↦ ρ.re < 1 / 2)
    have hsplit : (∑ ρ ∈ S_all, analyticOrderNatAt riemannZeta ρ) =
        ∑ ρ ∈ S_right, analyticOrderNatAt riemannZeta ρ +
          ∑ ρ ∈ S_left, analyticOrderNatAt riemannZeta ρ := by
      have := Finset.sum_filter_add_sum_filter_not S_all (fun ρ ↦ 1 / 2 ≤ ρ.re)
        (fun ρ ↦ analyticOrderNatAt riemannZeta ρ)
      rw [← this]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext ρ; simp [S_left, not_le]
    have hleft_le_right : (∑ ρ ∈ S_left, analyticOrderNatAt riemannZeta ρ) ≤
        ∑ ρ ∈ S_right, analyticOrderNatAt riemannZeta ρ := by
      have hinj : ∀ ρ ∈ S_left, 1 - star ρ ∈ S_right := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ ⊢
        have hm := (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp hρ.1
        refine ⟨(criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mpr ?_, ?_⟩
        · refine ⟨one_sub_star_mem_criticalStripZeros hm.1, ?_⟩
          have him : (1 - star ρ).im = ρ.im := by simp
          rw [him]
          exact hm.2
        · have hre : (1 - star ρ).re = 1 - ρ.re := by simp
          rw [hre]
          linarith [hρ.2]
      have hinjOn : Set.InjOn (fun ρ : ℂ ↦ 1 - star ρ) S_left := by
        intro a _ b _ hab
        have hstar : star a = star b := by
          have : 1 - star a = 1 - star b := hab
          exact sub_right_inj.mp this
        exact star_injective hstar
      calc
        ∑ ρ ∈ S_left, analyticOrderNatAt riemannZeta ρ
            = ∑ ρ ∈ S_left, analyticOrderNatAt riemannZeta (1 - star ρ) := by
          refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
          have hm := ((criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp
            (Finset.mem_filter.mp hρ).1).1
          exact (analyticOrderNatAt_riemannZeta_one_sub_star hm.2.1 hm.2.2).symm
        _ = ∑ w ∈ S_left.image (fun ρ : ℂ ↦ 1 - star ρ), analyticOrderNatAt riemannZeta w := by
          rw [Finset.sum_image (fun x hx y hy hxy ↦ hinjOn hx hy hxy)]
        _ ≤ ∑ w ∈ S_right, analyticOrderNatAt riemannZeta w := by
          refine Finset.sum_le_sum_of_subset fun w hw ↦ ?_
          rcases Finset.mem_image.mp hw with ⟨ρ, hρ, rfl⟩
          exact hinj ρ hρ
    let z₀ : ℂ := (3 / 2 : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I
    have hz₀_re : z₀.re = 3 / 2 := by simp [z₀]
    have hz₀_im : z₀.im = T + 1 / 2 := by simp [z₀]
    have hclosed_prop : ∀ w ∈ Metric.closedBall z₀ R,
        w ≠ 1 ∧ 0 ≤ w.re ∧ w.re ≤ 3 ∧ 2 ≤ |w.im| ∧ |w.im| ≤ |T| + 2 := by
      intro w hw
      have hdist : ‖w - z₀‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      have hre_diff : |w.re - 3 / 2| ≤ R := by
        rw [← hz₀_re]; exact (Complex.abs_re_le_norm (w - z₀)).trans hdist
      have him_diff : |w.im - (T + 1 / 2)| ≤ R := by
        rw [← hz₀_im]; exact (Complex.abs_im_le_norm (w - z₀)).trans hdist
      have hw_re_nonneg : 0 ≤ w.re := by linarith [(abs_le.mp hre_diff).1]
      have hw_re_ub : w.re ≤ 3 := by linarith [(abs_le.mp hre_diff).2]
      have him_ge2 : 2 ≤ |w.im| := by
        have h1 : |T + 1 / 2| - R ≤ |w.im| := by
          have := abs_sub_abs_le_abs_sub (T + 1 / 2) w.im
          rw [abs_sub_comm] at this
          linarith
        have hT_half : |T| - 1 / 2 ≤ |T + 1 / 2| := by
          have h := abs_sub_abs_le_abs_sub T (-(1 / 2))
          have h1' : T - -(1 / 2) = T + 1 / 2 := by ring
          have h2' : |-(1 / 2 : ℝ)| = 1 / 2 := by norm_num
          rw [h1', h2'] at h
          linarith
        linarith
      have him_le : |w.im| ≤ |T| + 2 := by
        have h1 : |w.im| ≤ |T + 1 / 2| + R := by
          have := abs_sub_abs_le_abs_sub w.im (T + 1 / 2)
          linarith
        have h2 : |T + 1 / 2| ≤ |T| + 1 / 2 :=
          (abs_add_le T (1 / 2)).trans (by norm_num)
        linarith
      have hw1 : w ≠ 1 := fun h ↦ by
        rw [h, Complex.one_im, abs_zero] at him_ge2
        linarith
      exact ⟨hw1, hw_re_nonneg, hw_re_ub, him_ge2, him_le⟩
    have han : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ R) := by
      have hdiff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw ↦
        (differentiableAt_riemannZeta hw).differentiableWithinAt
      exact (hdiff.analyticOnNhd isOpen_ne).mono fun w hw ↦ (hclosed_prop w hw).1
    have hz₀_ne : riemannZeta z₀ ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by rw [hz₀_re]; norm_num)
    let M : ℝ := C_right * (|T| + 2)
    have hM_pos : 0 < M := by positivity
    have hf_bound : ∀ w ∈ Metric.sphere z₀ R, ‖riemannZeta w‖ ≤ M := by
      intro w hw
      obtain ⟨_, hw_re0, _, hw_im2, hw_im_ub⟩ :=
        hclosed_prop w (Metric.sphere_subset_closedBall hw)
      have hw_eq : riemannZeta w = riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I) := by
        congr 1; exact (Complex.re_add_im w).symm
      rcases le_or_gt w.re 1 with hw1 | hw1
      · rw [hw_eq]
        have hstrip := hCs_bd ⟨hw_re0, hw1⟩ (by linarith : 1 ≤ |w.im|)
        have hexp_le : (1 - w.re) / 2 + 1 / 2 ≤ 1 := by linarith
        have hpow_le : (|w.im| + 2) ^ ((1 - w.re) / 2 + 1 / 2) ≤ |w.im| + 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ |w.im| + 2) hexp_le
        have him4 : |w.im| + 2 ≤ 2 * (|T| + 2) := by linarith
        calc
          ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
              ≤ Cs * (|w.im| + 2) ^ ((1 - w.re) / 2 + 1 / 2) := hstrip
          _ ≤ Cs * (|w.im| + 2) := mul_le_mul_of_nonneg_left hpow_le hCs_pos.le
          _ ≤ Cs * (2 * (|T| + 2)) := mul_le_mul_of_nonneg_left him4 hCs_pos.le
          _ = (2 * Cs) * (|T| + 2) := by ring
          _ ≤ C_right * (|T| + 2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            dsimp only [C_right]
            have hcs_le : 2 * Cs ≤ 3 * (Cs + 2) * 3 := by linarith
            exact hcs_le.trans ((le_max_left _ _).trans (le_max_left _ _))
      · rw [hw_eq]
        have hge1 := hC₁_bd hw1.le hw_im2
        have hlog_le : Real.log (|w.im| + 2) ≤ |w.im| + 2 := by
          have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < |w.im| + 2)
          linarith
        have him4 : |w.im| + 2 ≤ 2 * (|T| + 2) := by linarith
        calc
          ‖riemannZeta ((w.re : ℂ) + (w.im : ℂ) * I)‖
              ≤ C₁ * Real.log (|w.im| + 2) := hge1
          _ ≤ C₁ * (|w.im| + 2) := mul_le_mul_of_nonneg_left hlog_le hC₁_pos.le
          _ ≤ C₁ * (2 * (|T| + 2)) := mul_le_mul_of_nonneg_left him4 hC₁_pos.le
          _ = (2 * C₁) * (|T| + 2) := by ring
          _ ≤ C_right * (|T| + 2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            dsimp only [C_right]
            have hc1_le : 2 * C₁ ≤ 2 * C₁ + 2 := by linarith
            exact hc1_le.trans ((le_max_right _ _).trans (le_max_left _ _))
    have hS_right_in_ball : ∀ ρ ∈ S_right, ρ ∈ Metric.closedBall z₀ r := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hm := (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp hρ.1
      have hρ_re_lt1 : ρ.re < 1 := hm.1.2.2
      have hρ_re_ge : 1 / 2 ≤ ρ.re := hρ.2
      have hρ_im_ge : T ≤ ρ.im := hm.2.1
      have hρ_im_le : ρ.im ≤ T + 1 := hm.2.2
      rw [Metric.mem_closedBall, dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _),
        Real.sqrt_le_iff]
      refine ⟨hr_pos.le, ?_⟩
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, hz₀_re, hz₀_im]
      have hre_sq : (ρ.re - 3 / 2) ^ 2 ≤ 1 := by
        nlinarith [show -1 ≤ ρ.re - 3 / 2 by linarith, show ρ.re - 3 / 2 ≤ -1 / 2 by linarith]
      have him_sq : (ρ.im - (T + 1 / 2)) ^ 2 ≤ 1 / 4 := by
        nlinarith [show -1 / 2 ≤ ρ.im - (T + 1 / 2) by linarith,
          show ρ.im - (T + 1 / 2) ≤ 1 / 2 by linarith]
      have hr_sq : r ^ 2 = 25 / 16 := by dsimp only [r]; norm_num
      nlinarith
    have han_r : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z₀ r) :=
      han.mono (Metric.closedBall_subset_closedBall hrR.le)
    have hfin_r := AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroSet_finite
      hr_pos.le han_r hz₀_ne
    have hS_right_sub : S_right ⊆ hfin_r.toFinset := by
      intro ρ hρ
      refine hfin_r.mem_toFinset.mpr ⟨hS_right_in_ball ρ hρ, ?_⟩
      have hm := (criticalStripZeros_strip_finite T (T + 1)).mem_toFinset.mp
        (Finset.mem_filter.mp hρ).1
      exact hm.1.1
    have hsum_right_le :
        ((∑ ρ ∈ S_right, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          (AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount riemannZeta z₀ r : ℝ) := by
      have hcnt := AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount_eq_sum_analyticOrderNatAt
        hr_pos.le han_r hz₀_ne hfin_r.coe_toFinset
      exact_mod_cast (Finset.sum_le_sum_of_subset hS_right_sub).trans_eq hcnt.symm
    have hjensen := AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount_le_sub_log_div_log
      hr_pos hrR hM_pos han hz₀_ne hf_bound
    have hz₀_inv : ‖riemannZeta z₀‖⁻¹ ≤ 3 := by
      have hz₀_eq : riemannZeta z₀ = riemannZeta (((3 / 2 : ℝ) : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I) := by
        congr 1; simp only [z₀]; push_cast; ring
      rw [hz₀_eq]
      have hinv := inv_norm_riemannZeta_le_of_one_lt_re (σ := 3 / 2) (by norm_num) (T + 1 / 2)
      exact hinv.trans (by norm_num)
    have hnorm_z₀_ge : (1 / 3 : ℝ) ≤ ‖riemannZeta z₀‖ := by
      have hz₀_norm_pos : 0 < ‖riemannZeta z₀‖ := norm_pos_iff.mpr hz₀_ne
      rw [one_div]
      exact (inv_le_iff_one_le_mul₀ (by norm_num)).mpr
        (by nlinarith [hz₀_inv, inv_mul_cancel₀ hz₀_norm_pos.ne'])
    have hneg_log_z₀ : -Real.log ‖riemannZeta z₀‖ ≤ Real.log 3 := by
      have hlog_le := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) hnorm_z₀_ge
      rw [one_div, Real.log_inv] at hlog_le
      linarith
    have hlog_T_gt1 : 1 ≤ Real.log (|T| + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg T])]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    have hlogC_pos : 0 < Real.log C_right := by
      apply Real.log_pos
      dsimp only [C_right]
      linarith [le_max_right (max (3 * (Cs + 2) * 3) (2 * C₁ + 2)) 4]
    have hnum_le : Real.log M - Real.log ‖riemannZeta z₀‖ ≤
        (Real.log C_right + 1 + Real.log 3) * Real.log (|T| + 2) := by
      dsimp only [M]
      rw [Real.log_mul (by linarith [le_max_right (max (3 * (Cs + 2) * 3) (2 * C₁ + 2)) 4])
        (by linarith [abs_nonneg T])]
      have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      nlinarith
    have hall_le_two :
        ((∑ ρ ∈ S_all, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          2 * ((∑ ρ ∈ S_right, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
      have hle_nat : ∑ ρ ∈ S_all, analyticOrderNatAt riemannZeta ρ ≤
          2 * ∑ ρ ∈ S_right, analyticOrderNatAt riemannZeta ρ := by
        rw [hsplit]
        omega
      exact_mod_cast hle_nat
    calc
      ((∑ ρ ∈ S_all, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ)
          ≤ 2 * ((∑ ρ ∈ S_right, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := hall_le_two
      _ ≤ 2 * (AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.zeroCount riemannZeta z₀ r : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_right_le (by norm_num)
      _ ≤ 2 * ((Real.log M - Real.log ‖riemannZeta z₀‖) / Real.log (R / r)) :=
        mul_le_mul_of_nonneg_left hjensen (by norm_num)
      _ ≤ 2 * (((Real.log C_right + 1 + Real.log 3) * Real.log (|T| + 2)) / Real.log (R / r)) := by
        gcongr
      _ = C_large * Real.log (|T| + 2) := by
        dsimp only [C_large]; ring
      _ ≤ C * Real.log (|T| + 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by linarith [abs_nonneg T]))
        dsimp only [C]
        linarith [le_max_left C_large C_small]

/-! ### Convergent Reciprocal Sum over Non-trivial Zeros -/

private lemma summable_int_of_summable_nat_abs {g : ℕ → ℝ} (hg_nn : ∀ n, 0 ≤ g n)
    (hg : Summable g) :
    Summable (fun k : ℤ ↦ g k.natAbs) ∧
      ∑' k : ℤ, g k.natAbs ≤ 2 * ∑' n : ℕ, g n := by
  have hsum_bd : ∀ S : Finset ℤ, ∑ k ∈ S, g k.natAbs ≤ 2 * ∑' n : ℕ, g n := by
    intro S
    let N : ℕ := S.sup Int.natAbs
    let Spos : Finset ℤ := S.filter (fun k ↦ 0 ≤ k)
    let Sneg : Finset ℤ := S.filter (fun k ↦ k < 0)
    have hsplit : ∑ k ∈ S, g k.natAbs =
        ∑ k ∈ Spos, g k.natAbs + ∑ k ∈ Sneg, g k.natAbs := by
      have := Finset.sum_filter_add_sum_filter_not S (fun k : ℤ ↦ 0 ≤ k) (fun k ↦ g k.natAbs)
      rw [← this]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext k; simp [Sneg, not_le]
    have hpos_le : ∑ k ∈ Spos, g k.natAbs ≤ ∑' n : ℕ, g n := by
      have hinj : Set.InjOn Int.natAbs Spos := by
        intro a ha b hb hab
        have ha0 : 0 ≤ a := (Finset.mem_filter.mp ha).2
        have hb0 : 0 ≤ b := (Finset.mem_filter.mp hb).2
        omega
      calc
        ∑ k ∈ Spos, g k.natAbs
            = ∑ n ∈ Spos.image Int.natAbs, g n := by
              rw [Finset.sum_image (fun x hx y hy hxy ↦ hinj hx hy hxy)]
        _ ≤ ∑' n : ℕ, g n := hg.sum_le_tsum _ (fun n _ ↦ hg_nn n)
    have hneg_le : ∑ k ∈ Sneg, g k.natAbs ≤ ∑' n : ℕ, g n := by
      have hinj : Set.InjOn Int.natAbs Sneg := by
        intro a ha b hb hab
        have ha0 : a < 0 := (Finset.mem_filter.mp ha).2
        have hb0 : b < 0 := (Finset.mem_filter.mp hb).2
        omega
      calc
        ∑ k ∈ Sneg, g k.natAbs
            = ∑ n ∈ Sneg.image Int.natAbs, g n := by
              rw [Finset.sum_image (fun x hx y hy hxy ↦ hinj hx hy hxy)]
        _ ≤ ∑' n : ℕ, g n := hg.sum_le_tsum _ (fun n _ ↦ hg_nn n)
    linarith
  have hsumm : Summable (fun k : ℤ ↦ g k.natAbs) :=
    summable_of_sum_le (fun k ↦ hg_nn k.natAbs) hsum_bd
  have htsum : ∑' k : ℤ, g k.natAbs ≤ 2 * ∑' n : ℕ, g n :=
    le_of_tendsto hsumm.hasSum (Filter.Eventually.of_forall hsum_bd)
  exact ⟨hsumm, htsum⟩

private lemma summable_one_add_sq_inv_int :
    Summable (fun k : ℤ ↦ (1 : ℝ) / (1 + (k : ℝ) ^ 2)) := by
  let g : ℕ → ℝ := fun n ↦ (1 : ℝ) / (1 + (n : ℝ) ^ 2)
  have hg_nat : Summable g := by
    rw [← summable_nat_add_iff 1]
    have h2 : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h2.of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
    dsimp only [g]
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    refine div_le_div_of_nonneg_left zero_le_one hpos ?_
    linarith
  have hret := (summable_int_of_summable_nat_abs (g := g) (fun n ↦ by positivity) hg_nat).1
  refine hret.congr fun k ↦ ?_
  dsimp only [g]
  congr 2
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    have h := congrArg (Int.cast (R := ℝ)) (Int.abs_eq_natAbs k)
    simp only [Int.cast_abs, Int.cast_natCast] at h
    exact h
  rw [← sq_abs (k : ℝ), habs]

private lemma summable_log_add_two_div_one_add_sq_int :
    Summable (fun k : ℤ ↦ Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2)) := by
  let g : ℕ → ℝ := fun n ↦ Real.log ((n : ℝ) + 2) / (1 + (n : ℝ) ^ 2)
  have hg_nn : ∀ n, 0 ≤ g n := fun n ↦
    div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])) (by positivity)
  have hg_nat : Summable g := by
    rw [← summable_nat_add_iff 1]
    have h32 : Summable (fun n : ℕ ↦ (2 * Real.sqrt 3) / ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
      have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) :=
        (summable_nat_add_iff 1).mpr
          (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))
      simpa [div_eq_mul_inv] using hbase.mul_left (2 * Real.sqrt 3)
    refine h32.of_nonneg_of_le (fun n ↦ hg_nn (n + 1)) fun n ↦ ?_
    dsimp only [g]
    let m : ℝ := ((n + 1 : ℕ) : ℝ)
    have hm1 : 1 ≤ m := by dsimp only [m]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hm_pos : 0 < m := by linarith
    have hlog_sq : Real.log (m + 2) ≤ 2 * Real.sqrt (m + 2) := by
      have hsq_pos : 0 < Real.sqrt (m + 2) := Real.sqrt_pos.mpr (by linarith)
      have hsub : Real.log (Real.sqrt (m + 2)) ≤ Real.sqrt (m + 2) := by
        have h := Real.log_le_sub_one_of_pos hsq_pos
        linarith
      have heq : m + 2 = (Real.sqrt (m + 2)) ^ 2 := (Real.sq_sqrt (by linarith)).symm
      calc
        Real.log (m + 2) = Real.log ((Real.sqrt (m + 2)) ^ 2) := by rw [← heq]
        _ = 2 * Real.log (Real.sqrt (m + 2)) := by rw [Real.log_pow]; norm_num
        _ ≤ 2 * Real.sqrt (m + 2) := mul_le_mul_of_nonneg_left hsub (by norm_num)
    have hsqrt_le : Real.sqrt (m + 2) ≤ Real.sqrt 3 * m ^ ((1 : ℝ) / 2) := by
      have h3m : m + 2 ≤ 3 * m := by linarith
      calc
        Real.sqrt (m + 2) ≤ Real.sqrt (3 * m) := Real.sqrt_le_sqrt h3m
        _ = Real.sqrt 3 * Real.sqrt m := Real.sqrt_mul (by norm_num) m
        _ = Real.sqrt 3 * m ^ ((1 : ℝ) / 2) := by rw [← Real.sqrt_eq_rpow]
    have hden_le : m ^ 2 ≤ 1 + m ^ 2 := by linarith
    have hm_rpow : m ^ ((1 : ℝ) / 2) / m ^ 2 = 1 / m ^ ((3 : ℝ) / 2) := by
      have hmul : m ^ ((1 : ℝ) / 2) * m ^ ((3 : ℝ) / 2) = m ^ 2 := by
        rw [← Real.rpow_add hm_pos, ← Real.rpow_natCast m 2]
        congr 1; norm_num
      have hne : m ^ ((3 : ℝ) / 2) ≠ 0 := by positivity
      have hne2 : m ^ 2 ≠ 0 := by positivity
      rw [div_eq_div_iff hne2 hne, one_mul, hmul]
    calc
      Real.log (m + 2) / (1 + m ^ 2)
          ≤ (2 * Real.sqrt (m + 2)) / m ^ 2 :=
        div_le_div₀ (by positivity) hlog_sq (by positivity) hden_le
      _ ≤ (2 * (Real.sqrt 3 * m ^ ((1 : ℝ) / 2))) / m ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
      _ = (2 * Real.sqrt 3) * (m ^ ((1 : ℝ) / 2) / m ^ 2) := by ring
      _ = (2 * Real.sqrt 3) / m ^ ((3 : ℝ) / 2) := by rw [hm_rpow]; ring
  have hret := (summable_int_of_summable_nat_abs hg_nn hg_nat).1
  refine hret.congr fun k ↦ ?_
  dsimp only [g]
  have habs_eq : |(k : ℝ)| = (k.natAbs : ℝ) := by
    have h := congrArg (Int.cast (R := ℝ)) (Int.abs_eq_natAbs k)
    simp only [Int.cast_abs, Int.cast_natCast] at h
    exact h
  have hsq_eq : (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 := by
    rw [← sq_abs (k : ℝ), habs_eq]
  rw [habs_eq, hsq_eq]

private lemma one_add_int_sq_le_four_mul_one_add_sq {T y : ℝ} (k : ℤ)
    (hk : Int.floor (y - T) = k) :
    1 + (k : ℝ) ^ 2 ≤ 4 * (1 + (T - y) ^ 2) := by
  let x : ℝ := y - T
  have hk1 : (k : ℝ) ≤ x := hk ▸ Int.floor_le x
  have hk2 : x < (k : ℝ) + 1 := hk ▸ Int.lt_floor_add_one x
  have hd_sq : (x - k) ^ 2 ≤ 1 := by
    nlinarith [show 0 ≤ x - k by linarith, show x - k ≤ 1 by linarith]
  have hid : 3 * (4 * (1 + (T - y) ^ 2) - (1 + (k : ℝ) ^ 2)) =
      (3 * (k : ℝ) + 4 * (x - k)) ^ 2 + (9 - 4 * (x - k) ^ 2) := by
    have hsq : (T - y) ^ 2 = x ^ 2 := by dsimp only [x]; ring
    rw [hsq]; ring
  have hpos : 0 ≤ 3 * (4 * (1 + (T - y) ^ 2) - (1 + (k : ℝ) ^ 2)) := by
    rw [hid]
    nlinarith [sq_nonneg (3 * (k : ℝ) + 4 * (x - k))]
  linarith

/-- **Summability of the reciprocal-quadratic sum over non-trivial zeros**: for every `T : ℝ`,
the weighted sum `∑_ρ m_ρ / (1 + (T - Im ρ)^2)` converges absolutely. -/
theorem summable_criticalStripZeros_inv_one_add_sq (T : ℝ) :
    Summable (fun ρ : CriticalStripZeros ↦
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)) := by
  obtain ⟨C_uc, hC_uc_pos, hC_uc_bd⟩ := unitIntervalZeroCount_le_log
  have hs1 := summable_one_add_sq_inv_int
  have hs2 := summable_log_add_two_div_one_add_sq_int
  let B : ℝ := 4 * C_uc * Real.log (|T| + 2) * (∑' k : ℤ, (1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
      4 * C_uc * (∑' k : ℤ, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2))
  refine summable_of_sum_le (c := B) (fun ρ ↦ by positivity) fun F ↦ ?_
  let I : Finset ℤ := F.image (fun ρ : CriticalStripZeros ↦ Int.floor ((ρ : ℂ).im - T))
  have hpart : ∑ ρ ∈ F,
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) =
      ∑ k ∈ I, ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦
          Int.floor ((ρ : ℂ).im - T) = k),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro ρ hρ
    exact Finset.mem_image_of_mem _ hρ
  rw [hpart]
  have hband (k : ℤ) :
      ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦ Int.floor ((ρ : ℂ).im - T) = k),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤
        4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
          4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2)) := by
    let Fk := F.filter (fun ρ : CriticalStripZeros ↦ Int.floor ((ρ : ℂ).im - T) = k)
    let Sk : Finset ℂ := Fk.image Subtype.val
    have hterm_le : ∀ ρ ∈ Fk,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤
          (4 / (1 + (k : ℝ) ^ 2)) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by
      intro ρ hρ
      have hfl : Int.floor ((ρ : ℂ).im - T) = k := (Finset.mem_filter.mp hρ).2
      have hden := one_add_int_sq_le_four_mul_one_add_sq k hfl
      have hinv : 1 / (1 + (T - (ρ : ℂ).im) ^ 2) ≤ 4 / (1 + (k : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
            = (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) *
                (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by ring
        _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
    have hSk_sub : Sk ⊆ (criticalStripZeros_strip_finite (T + k) (T + k + 1)).toFinset := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
      have hfl : Int.floor ((ρ : ℂ).im - T) = k := (Finset.mem_filter.mp hρ).2
      have hk1 : (k : ℝ) ≤ (ρ : ℂ).im - T := hfl ▸ Int.floor_le _
      have hk2 : (ρ : ℂ).im - T < (k : ℝ) + 1 := hfl ▸ Int.lt_floor_add_one _
      exact (criticalStripZeros_strip_finite (T + k) (T + k + 1)).mem_toFinset.mpr
        ⟨ρ.prop, ⟨by linarith, by linarith⟩⟩
    have hsum_mult :
        (∑ ρ ∈ Fk, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) ≤
          (unitIntervalZeroCount (T + k) : ℝ) := by
      have him : ∑ ρ ∈ Fk, analyticOrderNatAt riemannZeta (ρ : ℂ) =
          ∑ z ∈ Sk, analyticOrderNatAt riemannZeta z := by
        symm
        exact Finset.sum_image fun a _ b _ hab ↦ Subtype.val_injective hab
      have hle_nat : ∑ z ∈ Sk, analyticOrderNatAt riemannZeta z ≤
          unitIntervalZeroCount (T + k) := by
        rw [unitIntervalZeroCount_eq_sum (T + k)]
        exact Finset.sum_le_sum_of_subset
          (by simpa only [add_assoc] using hSk_sub)
      exact_mod_cast him.trans_le hle_nat
    have huc := hC_uc_bd (T + k)
    have hlog_sub : Real.log (|T + k| + 2) ≤ Real.log (|T| + 2) + Real.log (|(k : ℝ)| + 2) := by
      have harg : |T + k| + 2 ≤ (|T| + 2) * (|(k : ℝ)| + 2) := by
        have habs : |T + k| ≤ |T| + |(k : ℝ)| := abs_add_le T k
        nlinarith [abs_nonneg T, abs_nonneg (k : ℝ)]
      calc
        Real.log (|T + k| + 2) ≤ Real.log ((|T| + 2) * (|(k : ℝ)| + 2)) :=
          Real.log_le_log (by linarith [abs_nonneg (T + k)]) harg
        _ = Real.log (|T| + 2) + Real.log (|(k : ℝ)| + 2) :=
          Real.log_mul (by linarith [abs_nonneg T]) (by linarith [abs_nonneg (k : ℝ)])
    calc
      ∑ ρ ∈ Fk, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
          ≤ ∑ ρ ∈ Fk, (4 / (1 + (k : ℝ) ^ 2)) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) :=
        Finset.sum_le_sum hterm_le
      _ = (4 / (1 + (k : ℝ) ^ 2)) * ∑ ρ ∈ Fk, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (unitIntervalZeroCount (T + k) : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_mult (by positivity)
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (C_uc * Real.log (|T + k| + 2)) :=
        mul_le_mul_of_nonneg_left huc (by positivity)
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (C_uc * (Real.log (|T| + 2) + Real.log (|(k : ℝ)| + 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_sub hC_uc_pos.le)
          (by positivity)
      _ = 4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
            4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2)) := by ring
  have hsum_I : ∑ k ∈ I, ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦
        Int.floor ((ρ : ℂ).im - T) = k),
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤
      ∑ k ∈ I, (4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
        4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2))) :=
    Finset.sum_le_sum fun k _ ↦ hband k
  have hsum_split : ∑ k ∈ I,
      (4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
        4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2))) =
      4 * C_uc * Real.log (|T| + 2) * ∑ k ∈ I, (1 : ℝ) / (1 + (k : ℝ) ^ 2) +
        4 * C_uc * ∑ k ∈ I, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hs1_le : ∑ k ∈ I, (1 : ℝ) / (1 + (k : ℝ) ^ 2) ≤
      ∑' k : ℤ, (1 : ℝ) / (1 + (k : ℝ) ^ 2) :=
    hs1.sum_le_tsum I (fun k _ ↦ by positivity)
  have hs2_le : ∑ k ∈ I, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) ≤
      ∑' k : ℤ, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) :=
    hs2.sum_le_tsum I (fun k _ ↦
      div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])) (by positivity))
  have hlogT_nn : 0 ≤ Real.log (|T| + 2) := Real.log_nonneg (by linarith [abs_nonneg T])
  calc
    ∑ k ∈ I, ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦
          Int.floor ((ρ : ℂ).im - T) = k),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
        ≤ 4 * C_uc * Real.log (|T| + 2) * ∑ k ∈ I, (1 : ℝ) / (1 + (k : ℝ) ^ 2) +
            4 * C_uc * ∑ k ∈ I, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) :=
      hsum_I.trans_eq hsum_split
    _ ≤ B := by
      dsimp only [B]
      nlinarith [hs1_le, hs2_le, mul_nonneg (by positivity : 0 ≤ 4 * C_uc) hlogT_nn]

/-- **Logarithmic upper bound for the zero-reciprocal sum**:
`∑' ρ : CriticalStripZeros, m_ρ / (1 + (T - Im ρ)^2) ≤ C * Real.log (|T| + 2)`. -/
theorem tsum_criticalStripZeros_inv_one_add_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
      (∑' ρ : CriticalStripZeros,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)) ≤
        C * Real.log (|T| + 2) := by
  obtain ⟨C_uc, hC_uc_pos, hC_uc_bd⟩ := unitIntervalZeroCount_le_log
  have hs1 := summable_one_add_sq_inv_int
  have hs2 := summable_log_add_two_div_one_add_sq_int
  let S₁ : ℝ := ∑' k : ℤ, (1 : ℝ) / (1 + (k : ℝ) ^ 2)
  let S₂ : ℝ := ∑' k : ℤ, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2)
  have hS₁_nn : 0 ≤ S₁ := tsum_nonneg fun k ↦ by positivity
  have hS₂_nn : 0 ≤ S₂ := tsum_nonneg fun k ↦
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])) (by positivity)
  let C : ℝ := 4 * C_uc * S₁ + 4 * C_uc * S₂ / Real.log 2 + 1
  have hC_pos : 0 < C := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  refine ⟨C, hC_pos, fun T ↦ ?_⟩
  have hsumm := summable_criticalStripZeros_inv_one_add_sq T
  refine le_of_tendsto hsumm.hasSum (Filter.Eventually.of_forall fun F ↦ ?_)
  let I : Finset ℤ := F.image (fun ρ : CriticalStripZeros ↦ Int.floor ((ρ : ℂ).im - T))
  have hpart : ∑ ρ ∈ F,
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) =
      ∑ k ∈ I, ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦
          Int.floor ((ρ : ℂ).im - T) = k),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro ρ hρ
    exact Finset.mem_image_of_mem _ hρ
  rw [hpart]
  have hband (k : ℤ) :
      ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦ Int.floor ((ρ : ℂ).im - T) = k),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤
        4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
          4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2)) := by
    let Fk := F.filter (fun ρ : CriticalStripZeros ↦ Int.floor ((ρ : ℂ).im - T) = k)
    let Sk : Finset ℂ := Fk.image Subtype.val
    have hterm_le : ∀ ρ ∈ Fk,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤
          (4 / (1 + (k : ℝ) ^ 2)) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by
      intro ρ hρ
      have hfl : Int.floor ((ρ : ℂ).im - T) = k := (Finset.mem_filter.mp hρ).2
      have hden := one_add_int_sq_le_four_mul_one_add_sq k hfl
      have hinv : 1 / (1 + (T - (ρ : ℂ).im) ^ 2) ≤ 4 / (1 + (k : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
            = (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) *
                (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by ring
        _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
    have hSk_sub : Sk ⊆ (criticalStripZeros_strip_finite (T + k) (T + k + 1)).toFinset := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
      have hfl : Int.floor ((ρ : ℂ).im - T) = k := (Finset.mem_filter.mp hρ).2
      have hk1 : (k : ℝ) ≤ (ρ : ℂ).im - T := hfl ▸ Int.floor_le _
      have hk2 : (ρ : ℂ).im - T < (k : ℝ) + 1 := hfl ▸ Int.lt_floor_add_one _
      exact (criticalStripZeros_strip_finite (T + k) (T + k + 1)).mem_toFinset.mpr
        ⟨ρ.prop, ⟨by linarith, by linarith⟩⟩
    have hsum_mult :
        (∑ ρ ∈ Fk, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) ≤
          (unitIntervalZeroCount (T + k) : ℝ) := by
      have him : ∑ ρ ∈ Fk, analyticOrderNatAt riemannZeta (ρ : ℂ) =
          ∑ z ∈ Sk, analyticOrderNatAt riemannZeta z := by
        symm
        exact Finset.sum_image fun a _ b _ hab ↦ Subtype.val_injective hab
      have hle_nat : ∑ z ∈ Sk, analyticOrderNatAt riemannZeta z ≤
          unitIntervalZeroCount (T + k) := by
        rw [unitIntervalZeroCount_eq_sum (T + k)]
        exact Finset.sum_le_sum_of_subset
          (by simpa only [add_assoc] using hSk_sub)
      exact_mod_cast him.trans_le hle_nat
    have huc := hC_uc_bd (T + k)
    have hlog_sub : Real.log (|T + k| + 2) ≤ Real.log (|T| + 2) + Real.log (|(k : ℝ)| + 2) := by
      have harg : |T + k| + 2 ≤ (|T| + 2) * (|(k : ℝ)| + 2) := by
        have habs : |T + k| ≤ |T| + |(k : ℝ)| := abs_add_le T k
        nlinarith [abs_nonneg T, abs_nonneg (k : ℝ)]
      calc
        Real.log (|T + k| + 2) ≤ Real.log ((|T| + 2) * (|(k : ℝ)| + 2)) :=
          Real.log_le_log (by linarith [abs_nonneg (T + k)]) harg
        _ = Real.log (|T| + 2) + Real.log (|(k : ℝ)| + 2) :=
          Real.log_mul (by linarith [abs_nonneg T]) (by linarith [abs_nonneg (k : ℝ)])
    calc
      ∑ ρ ∈ Fk, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
          ≤ ∑ ρ ∈ Fk, (4 / (1 + (k : ℝ) ^ 2)) * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) :=
        Finset.sum_le_sum hterm_le
      _ = (4 / (1 + (k : ℝ) ^ 2)) * ∑ ρ ∈ Fk, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (unitIntervalZeroCount (T + k) : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_mult (by positivity)
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (C_uc * Real.log (|T + k| + 2)) :=
        mul_le_mul_of_nonneg_left huc (by positivity)
      _ ≤ (4 / (1 + (k : ℝ) ^ 2)) * (C_uc * (Real.log (|T| + 2) + Real.log (|(k : ℝ)| + 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_sub hC_uc_pos.le)
          (by positivity)
      _ = 4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
            4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2)) := by ring
  have hsum_I := Finset.sum_le_sum fun k (_ : k ∈ I) ↦ hband k
  have hsum_split : ∑ k ∈ I,
      (4 * C_uc * Real.log (|T| + 2) * ((1 : ℝ) / (1 + (k : ℝ) ^ 2)) +
        4 * C_uc * (Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2))) =
      4 * C_uc * Real.log (|T| + 2) * ∑ k ∈ I, (1 : ℝ) / (1 + (k : ℝ) ^ 2) +
        4 * C_uc * ∑ k ∈ I, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hs1_le : ∑ k ∈ I, (1 : ℝ) / (1 + (k : ℝ) ^ 2) ≤ S₁ :=
    hs1.sum_le_tsum I (fun k _ ↦ by positivity)
  have hs2_le : ∑ k ∈ I, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) ≤ S₂ :=
    hs2.sum_le_tsum I (fun k _ ↦
      div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])) (by positivity))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_ge : Real.log 2 ≤ Real.log (|T| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg T])
  have hconst_le : 4 * C_uc * S₂ ≤ (4 * C_uc * S₂ / Real.log 2) * Real.log (|T| + 2) := by
    calc
      4 * C_uc * S₂ = (4 * C_uc * S₂ / Real.log 2) * Real.log 2 := by
        field_simp [hlog2_pos.ne']
      _ ≤ (4 * C_uc * S₂ / Real.log 2) * Real.log (|T| + 2) :=
        mul_le_mul_of_nonneg_left hlog_ge (by positivity)
  calc
    ∑ k ∈ I, ∑ ρ ∈ F.filter (fun ρ : CriticalStripZeros ↦
          Int.floor ((ρ : ℂ).im - T) = k),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
        ≤ 4 * C_uc * Real.log (|T| + 2) * ∑ k ∈ I, (1 : ℝ) / (1 + (k : ℝ) ^ 2) +
            4 * C_uc * ∑ k ∈ I, Real.log (|(k : ℝ)| + 2) / (1 + (k : ℝ) ^ 2) :=
      hsum_I.trans_eq hsum_split
    _ ≤ 4 * C_uc * Real.log (|T| + 2) * S₁ + 4 * C_uc * S₂ := by
      have hlogT_nn : 0 ≤ Real.log (|T| + 2) := Real.log_nonneg (by linarith [abs_nonneg T])
      nlinarith [hs1_le, hs2_le, mul_nonneg (by positivity : 0 ≤ 4 * C_uc) hlogT_nn]
    _ ≤ (4 * C_uc * S₁) * Real.log (|T| + 2) +
          (4 * C_uc * S₂ / Real.log 2) * Real.log (|T| + 2) := by
      linarith
    _ ≤ C * Real.log (|T| + 2) := by
      have hlogT_nn : 0 ≤ Real.log (|T| + 2) := Real.log_nonneg (by linarith [abs_nonneg T])
      dsimp only [C]
      nlinarith

/-- Sequence-indexed version of the zero-reciprocal sum bound: for any enumeration `a : ℕ → ℂ` of
`CriticalStripZeros` respecting analytic multiplicity, `∑' n, 1 / (1 + (T - (a n).im)^2)`
converges and is bounded by `C * Real.log (|T| + 2)`. -/
theorem tsum_hadamard_zeros_inv_one_add_sq_le {a : ℕ → ℂ}
    (ha_mem : ∀ n, a n ∈ CriticalStripZeros)
    (ha_card : ∀ ρ ∈ CriticalStripZeros,
      ({n : ℕ | a n = ρ}).ncard = analyticOrderNatAt riemannZeta ρ)
    (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
      Summable (fun n : ℕ ↦ (1 : ℝ) / (1 + (T - (a n).im) ^ 2)) ∧
        ∑' n : ℕ, (1 : ℝ) / (1 + (T - (a n).im) ^ 2) ≤ C * Real.log (|T| + 2) := by
  obtain ⟨C, hC_pos, hC_bd⟩ := tsum_criticalStripZeros_inv_one_add_sq_le
  refine ⟨C, hC_pos, fun T ↦ ?_⟩
  have hsum_crit := summable_criticalStripZeros_inv_one_add_sq T
  let B : ℝ := ∑' ρ : CriticalStripZeros,
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)
  have hfin_bd : ∀ F : Finset ℕ,
      ∑ n ∈ F, (1 : ℝ) / (1 + (T - (a n).im) ^ 2) ≤ B := by
    intro F
    let F_sub : Finset CriticalStripZeros :=
      F.image (fun n ↦ (⟨a n, ha_mem n⟩ : CriticalStripZeros))
    have hsplit : ∑ n ∈ F, (1 : ℝ) / (1 + (T - (a n).im) ^ 2) =
        ∑ ρ ∈ F_sub, ∑ n ∈ F.filter (fun n ↦ (⟨a n, ha_mem n⟩ : CriticalStripZeros) = ρ),
          (1 : ℝ) / (1 + (T - (a n).im) ^ 2) := by
      rw [Finset.sum_fiberwise_of_maps_to]
      intro n hn
      exact Finset.mem_image_of_mem _ hn
    rw [hsplit]
    have hinner (ρ : CriticalStripZeros) :
        ∑ n ∈ F.filter (fun n ↦ (⟨a n, ha_mem n⟩ : CriticalStripZeros) = ρ),
          (1 : ℝ) / (1 + (T - (a n).im) ^ 2) ≤
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) := by
      let Fρ := F.filter (fun n ↦ (⟨a n, ha_mem n⟩ : CriticalStripZeros) = ρ)
      have hcongr : ∀ n ∈ Fρ,
          (1 : ℝ) / (1 + (T - (a n).im) ^ 2) = (1 : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) := by
        intro n hn
        have heq := congrArg Subtype.val (Finset.mem_filter.mp hn).2
        dsimp only at heq
        rw [heq]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
      have hfib_fin : ({n : ℕ | a n = (ρ : ℂ)}).Finite :=
        (ha_fin ‖(ρ : ℂ)‖).subset fun n hn ↦ by
          simp only [Set.mem_ofPred_eq] at hn ⊢; rw [hn]
      have hFρ_sub : (Fρ : Set ℕ) ⊆ {n : ℕ | a n = (ρ : ℂ)} := by
        intro n hn
        have heq := congrArg Subtype.val (Finset.mem_filter.mp hn).2
        simpa [Set.mem_ofPred_eq] using heq
      have hcard_le : Fρ.card ≤ analyticOrderNatAt riemannZeta (ρ : ℂ) := by
        rw [← ha_card (ρ : ℂ) ρ.prop, ← Set.ncard_coe_finset Fρ]
        exact Set.ncard_le_ncard hFρ_sub hfib_fin
      calc
        (Fρ.card : ℝ) * ((1 : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2))
            ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
                ((1 : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
        _ = (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) := by ring
    calc
      ∑ ρ ∈ F_sub, ∑ n ∈ F.filter (fun n ↦ (⟨a n, ha_mem n⟩ : CriticalStripZeros) = ρ),
            (1 : ℝ) / (1 + (T - (a n).im) ^ 2)
          ≤ ∑ ρ ∈ F_sub,
              (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) :=
        Finset.sum_le_sum fun ρ _ ↦ hinner ρ
      _ ≤ B := hsum_crit.sum_le_tsum F_sub (fun ρ _ ↦ by positivity)
  have hsumm : Summable (fun n : ℕ ↦ (1 : ℝ) / (1 + (T - (a n).im) ^ 2)) :=
    summable_of_sum_le (fun n ↦ by positivity) hfin_bd
  refine ⟨hsumm, (le_of_tendsto hsumm.hasSum (Filter.Eventually.of_forall hfin_bd)).trans (hC_bd T)⟩

/-! ### Hadamard Factorization of `xi` and Partial Fractions of `ζ'/ζ` -/

/-- **Genus-1 Hadamard factorization of `xi`**: there exist an enumeration `a : ℕ → ℂ` of
`CriticalStripZeros` (counted with multiplicity) and a constant `B : ℂ` such that
`∑ ‖a n‖ ^ (-2) < ∞`, `xi z = (1 / 2) * exp (B * z) * canonicalProduct a 1 z`, and
`deriv xi z / xi z = B + ∑' n, (1 / (z - a n) + 1 / a n)` away from `0` and the zeros of `xi`. -/
theorem exists_hadamard_factorization_xi :
    ∃ (a : ℕ → ℂ) (B : ℂ),
      (∀ n, a n ∈ CriticalStripZeros) ∧
      (∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) ∧
      (∀ ρ ∈ CriticalStripZeros,
        ({n : ℕ | a n = ρ}).ncard = analyticOrderNatAt riemannZeta ρ) ∧
      Summable (fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
      (∀ z : ℂ, xi z = (1 / 2 : ℂ) * Complex.exp (B * z) * canonicalProduct a 1 z) ∧
      (∀ z : ℂ, z ≠ 0 → xi z ≠ 0 →
        deriv xi z / xi z = B + ∑' n : ℕ, (1 / (z - a n) + 1 / a n)) := by
  rcases hadamard_logDeriv_genus_one differentiable_xi xi_ne_zero_fn zero_le_one
      entireOrderLe_xi_one one_lt_two with
    ⟨zs, A, B, hzs_ne, hzs_count, hform, _⟩ |
    ⟨a, A, B, ha_ne, ha_fin, ha_card, hsum, hform, hld⟩
  · exact False.elim (not_finite_zeros_xi ⟨zs, A, B, hzs_ne, hzs_count, hform⟩)
  · have hord0 : analyticOrderNatAt xi 0 = 0 := by
      have h0 : analyticOrderAt xi 0 = 0 :=
        (analyticOnNhd_xi 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr
          (by rw [xi_zero]; norm_num)
      simp [analyticOrderNatAt, h0]
    have hprod0 : canonicalProduct a 1 0 = 1 := by
      simp [canonicalProduct, weierstrassPrimaryFactor_at_zero]
    have hexpA : Complex.exp A = (1 / 2 : ℂ) := by
      have h0 := hform 0
      rw [hord0, hprod0, pow_zero, mul_zero, add_zero, one_mul, mul_one, xi_zero] at h0
      exact h0.symm
    have hform' : ∀ z : ℂ,
        xi z = (1 / 2 : ℂ) * Complex.exp (B * z) * canonicalProduct a 1 z := by
      intro z
      rw [hform z, hord0, pow_zero, one_mul, Complex.exp_add, hexpA]
    have ha_mem : ∀ n, a n ∈ CriticalStripZeros := by
      intro n
      have hfib : ({k : ℕ | a k = a n}).Finite :=
        (ha_fin ‖a n‖).subset fun k hk ↦ by
          simp only [Set.mem_ofPred_eq] at hk ⊢; rw [hk]
      have hpos : 0 < ({k : ℕ | a k = a n}).ncard := (Set.ncard_pos hfib).mpr ⟨n, rfl⟩
      rw [ha_card (a n) (ha_ne n)] at hpos
      have hzero : xi (a n) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne'
      rw [criticalStripZeros_eq_xi_zeros]
      exact hzero
    have ha_card_zeta : ∀ ρ ∈ CriticalStripZeros,
        ({n : ℕ | a n = ρ}).ncard = analyticOrderNatAt riemannZeta ρ := by
      intro ρ hρ
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        have hlt := hρ.2.1
        simp at hlt
      rw [ha_card ρ hρ0, analyticOrderNatAt_riemannZeta_eq_xi hρ.2.1 hρ.2.2]
    have hld' : ∀ z : ℂ, z ≠ 0 → xi z ≠ 0 →
        deriv xi z / xi z = B + ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
      intro z hz0 hxi0
      have h := hld z hz0 hxi0
      rwa [hord0, Nat.cast_zero, zero_div, zero_add] at h
    exact ⟨a, B, ha_mem, ha_fin, ha_card_zeta, hsum, hform', hld'⟩

/-- Relates the logarithmic derivative partial fraction expansion of `xi` to that of
`riemannZeta`, expressing `deriv riemannZeta s / riemannZeta s` in terms of `B`, `log π`,
`1 / (s - 1)`, `digamma (s / 2 + 1)`, and the Hadamard zero sum. -/
theorem logDeriv_riemannZeta_eq_partial_fractions_of_xi {a : ℕ → ℂ} {B : ℂ}
    (hxi_ld : ∀ z : ℂ, z ≠ 0 → xi z ≠ 0 →
      deriv xi z / xi z = B + ∑' n : ℕ, (1 / (z - a n) + 1 / a n))
    {s : ℂ} (hs : ∀ m : ℕ, s ≠ -2 * (m : ℂ)) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      B + (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) - 1 / (s - 1) -
        (1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma (s / 2 + 1) +
        ∑' n : ℕ, (1 / (s - a n) + 1 / a n) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hs_ne1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hπ_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs_half_ne : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m hm
    apply hs (m + 1)
    push_cast
    linear_combination 2 * hm
  have hG_ne : Complex.Gamma (s / 2 + 1) ≠ 0 :=
    Complex.Gamma_ne_zero hs_half_ne
  have hxi_ne : xi s ≠ 0 := by
    rw [xi_eq_formula hs hs1]
    have hG2_ne : Complex.Gamma (s / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m hm ↦ hs m ?_
      linear_combination 2 * hm
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs_ne1)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ_ne))) hG2_ne) hz
  have hev_eq : xi =ᶠ[𝓝 s] fun z : ℂ ↦
      (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1) * riemannZeta z := by
    let N : ℕ := Nat.ceil (‖s‖ + 2)
    let excl : Finset ℂ := insert (1 : ℂ) ((Finset.range N).image (fun m : ℕ ↦ -2 * (m : ℂ)))
    have hexcl_ne : ∀ w ∈ excl, w ≠ s := by
      intro w hw heq
      subst heq
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact hs1 rfl
      · rcases Finset.mem_image.mp hw' with ⟨m, _, hm⟩
        exact hs m hm.symm
    obtain ⟨w₀, hw₀, hw₀_min⟩ :=
      excl.exists_min_image (fun w : ℂ ↦ ‖s - w‖) ⟨1, Finset.mem_insert_self 1 _⟩
    have hw₀_pos : 0 < ‖s - w₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hexcl_ne w₀ hw₀).symm)
    let r : ℝ := min (1 / 2) (‖s - w₀‖ / 2)
    have hr_pos : 0 < r := lt_min (by norm_num) (half_pos hw₀_pos)
    filter_upwards [Metric.ball_mem_nhds s hr_pos] with z hz_ball
    have hz_dist : ‖z - s‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
    have hz_avoids : (∀ m : ℕ, z ≠ -2 * (m : ℂ)) ∧ z ≠ 1 := by
      have hz_excl : ∀ w ∈ excl, z ≠ w := by
        intro w hw heq
        have h1 : ‖s - w₀‖ ≤ ‖s - w‖ := hw₀_min w hw
        have h2 : ‖s - w‖ ≤ ‖s - z‖ := by rw [heq]
        have h3 : ‖s - z‖ < ‖s - w₀‖ / 2 := by
          rw [norm_sub_rev]
          exact hz_dist.trans_le (min_le_right _ _)
        linarith
      refine ⟨fun m heq ↦ ?_, hz_excl 1 (Finset.mem_insert_self 1 _)⟩
      by_cases hm : m < N
      · exact hz_excl (-2 * (m : ℂ))
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hm))) heq
      · have hm_ge : N ≤ m := Nat.le_of_not_lt hm
        have hceil : ‖s‖ + 2 ≤ (N : ℝ) := Nat.le_ceil (‖s‖ + 2)
        have hnorm_z : ‖z‖ < ‖s‖ + 1 / 2 := by
          calc
            ‖z‖ = ‖(z - s) + s‖ := by congr 1; ring
            _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
            _ < 1 / 2 + ‖s‖ := by linarith [hz_dist.trans_le (min_le_left _ _)]
            _ = ‖s‖ + 1 / 2 := by ring
        have hnorm_m : ‖(-2 * (m : ℂ))‖ = 2 * (m : ℝ) := by
          rw [norm_mul, show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num,
            Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_two, Complex.norm_natCast]
        have hm_r : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm_ge
        rw [heq, hnorm_m] at hnorm_z
        linarith [norm_nonneg s]
    have hz0 : z / 2 ≠ 0 := div_ne_zero (by simpa using hz_avoids.1 0) two_ne_zero
    rw [xi_eq_formula hz_avoids.1 hz_avoids.2, Complex.Gamma_add_one (z / 2) hz0]
    ring
  have hd1 : HasDerivAt (fun z : ℂ ↦ z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hlogπ : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hd2 : HasDerivAt (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ))) s := by
    have hexp : HasDerivAt (fun z : ℂ ↦ -z / 2) (-(1 / 2 : ℂ)) s := by
      have h := ((hasDerivAt_id s).neg).div_const (2 : ℂ)
      exact h.congr_deriv (by ring)
    have hc := HasDerivAt.const_cpow hexp (Or.inl hπ_ne)
    refine hc.congr_deriv ?_
    rw [hlogπ]
    ring
  have hd3 : HasDerivAt (fun z : ℂ ↦ Complex.Gamma (z / 2 + 1))
      (deriv Complex.Gamma (s / 2 + 1) * (1 / 2 : ℂ)) s := by
    have hG_diff : DifferentiableAt ℂ Complex.Gamma (s / 2 + 1) :=
      Complex.differentiableAt_Gamma _ hs_half_ne
    have hlin : HasDerivAt (fun z : ℂ ↦ z / 2 + 1) (1 / 2 : ℂ) s := by
      have h := ((hasDerivAt_id s).div_const (2 : ℂ)).add_const (1 : ℂ)
      exact h.congr_deriv (by ring)
    exact (hG_diff.hasDerivAt).comp s hlin
  have hd4 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hd12 := hd1.mul hd2
  have hd123 := hd12.mul hd3
  have hd_all : HasDerivAt (fun z : ℂ ↦
      (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1) * riemannZeta z)
      (((1 * (Real.pi : ℂ) ^ (-s / 2) + (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) *
          (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)))) *
          Complex.Gamma (s / 2 + 1) +
        ((s - 1) * (Real.pi : ℂ) ^ (-s / 2)) *
          (deriv Complex.Gamma (s / 2 + 1) * (1 / 2 : ℂ))) * riemannZeta s +
      ((s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)) *
        deriv riemannZeta s) s :=
    (hd123.mul hd4)
  have hderiv_xi : deriv xi s =
      (1 * (Real.pi : ℂ) ^ (-s / 2) + (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) *
          (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)))) *
        Complex.Gamma (s / 2 + 1) * riemannZeta s +
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * (deriv Complex.Gamma (s / 2 + 1) * (1 / 2 : ℂ)) *
        riemannZeta s +
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) * deriv riemannZeta s := by
    rw [hev_eq.deriv_eq, hd_all.deriv]
    ring
  have hxi_eq_prod : xi s =
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) * riemannZeta s := by
    have heq := hev_eq.eq_of_nhds
    simpa only [] using heq
  have hπ_pow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ_ne)
  have hdiv_eq : deriv xi s / xi s =
      1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma (s / 2 + 1) +
        deriv riemannZeta s / riemannZeta s := by
    rw [hderiv_xi, hxi_eq_prod, AnalyticNumberTheory.AnalyticTools.Gamma.digamma_def]
    set G := Complex.Gamma (s / 2 + 1)
    set G' := deriv Complex.Gamma (s / 2 + 1)
    have hG_ne' : G ≠ 0 := hG_ne
    field_simp [hs_ne1, hπ_pow_ne, hG_ne', hz]
    ring
  have hsum := hxi_ld s hs0 hxi_ne
  rw [hdiv_eq] at hsum
  linear_combination hsum

/-- **Partial fraction expansion of `ζ'/ζ`**: there exist an enumeration `a : ℕ → ℂ` of
`CriticalStripZeros` (with multiplicity) and `B : ℂ` such that away from `1`, the trivial zeros
`{-2m}`, and non-trivial zeros,
`deriv riemannZeta s / riemannZeta s = B + (1 / 2) * log π - 1 / (s - 1) - (1 / 2) * digamma (s / 2 + 1) + ∑' n, (1 / (s - a n) + 1 / a n)`. -/
theorem exists_logDeriv_riemannZeta_partial_fractions :
    ∃ (a : ℕ → ℂ) (B : ℂ),
      (∀ n, a n ∈ CriticalStripZeros) ∧
      (∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) ∧
      (∀ ρ ∈ CriticalStripZeros,
        ({n : ℕ | a n = ρ}).ncard = analyticOrderNatAt riemannZeta ρ) ∧
      Summable (fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
      (∀ s : ℂ, (∀ m : ℕ, s ≠ -2 * (m : ℂ)) → s ≠ 1 → riemannZeta s ≠ 0 →
        deriv riemannZeta s / riemannZeta s =
          B + (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) - 1 / (s - 1) -
            (1 / 2 : ℂ) * AnalyticNumberTheory.AnalyticTools.Gamma.digamma (s / 2 + 1) +
            ∑' n : ℕ, (1 / (s - a n) + 1 / a n)) := by
  obtain ⟨a, B, ha_mem, ha_fin, ha_card, hsum, _, hxi_ld⟩ := exists_hadamard_factorization_xi
  exact ⟨a, B, ha_mem, ha_fin, ha_card, hsum, fun s hs hs1 hz ↦
    logDeriv_riemannZeta_eq_partial_fractions_of_xi hxi_ld hs hs1 hz⟩

/-! ### Holomorphic Logarithm `logZeta` for `1 < Re s` -/

/-- Branch of `log ζ(s)` on the half-plane `1 < Re s` defined via the Euler product
`∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))`. -/
noncomputable def logZeta (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))

/-- Exponential identity `Complex.exp (logZeta s) = riemannZeta s` for `1 < Re s`. -/
theorem exp_logZeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (logZeta s) = riemannZeta s :=
  _root_.riemannZeta_eulerProduct_exp_log hs

/-- Real part identity `(logZeta s).re = Real.log ‖riemannZeta s‖` for `1 < Re s`. -/
theorem logZeta_re_eq_log_norm {s : ℂ} (hs : 1 < s.re) :
    (logZeta s).re = Real.log ‖riemannZeta s‖ := by
  rw [← exp_logZeta hs, Complex.norm_exp, Real.log_exp]

private noncomputable def logZetaCoeff (n : ℕ) : ℂ :=
  ((1 : DirichletCharacter ℂ 1) n) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)

/-- Dirichlet series representation of `logZeta` on `1 < Re s`:
`logZeta s = LSeries (fun n ↦ Λ n / Real.log n) s`. -/
theorem logZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    logZeta s = LSeries logZetaCoeff s := by
  have h := dirichletLSeries_eulerProduct_log_eq_LSeries (1 : DirichletCharacter ℂ 1) hs
  have htsum : logZeta s =
      ∑' p : Nat.Primes,
        -Complex.log (1 - (1 : DirichletCharacter ℂ 1) (p : ℕ) * (p : ℂ) ^ (-s)) := by
    unfold logZeta
    refine tsum_congr fun p ↦ ?_
    have hp1 : (1 : DirichletCharacter ℂ 1) (p : ℕ) = 1 :=
      MulChar.one_apply (isUnit_of_subsingleton _)
    simp [hp1]
  have hL : LSeries (fun n : ℕ ↦ (1 : DirichletCharacter ℂ 1) n *
        (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) s =
      LSeries logZetaCoeff s :=
    LSeries_congr (fun {n} _ ↦ rfl) s
  exact htsum.trans (h.trans hL)

private lemma abscissaOfAbsConv_logZetaCoeff_le_one :
    LSeries.abscissaOfAbsConv logZetaCoeff ≤ (1 : EReal) := by
  have hle : LSeries.abscissaOfAbsConv logZetaCoeff ≤ ((0 + 1 : ℝ) : EReal) := by
    refine LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) ?_
    refine ⟨1, fun n hn ↦ ?_⟩
    simp only [Real.rpow_zero, mul_one]
    dsimp only [logZetaCoeff]
    have hchar : (1 : DirichletCharacter ℂ 1) n = 1 :=
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))
    rw [hchar, one_mul]
    rcases le_or_gt n 1 with hn1 | hn2
    · have hn' : n = 1 := by omega
      subst hn'
      simp
    · have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hΛ_nn : 0 ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hΛ_le : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hΛ_nn,
        Real.norm_of_nonneg hlog_pos.le]
      exact div_le_one_of_le₀ hΛ_le hlog_pos.le
  simpa using hle

/-- Complex differentiability of `logZeta`: for `1 < Re s`, `logZeta` has derivative
`deriv riemannZeta s / riemannZeta s` at `s`. -/
theorem hasDerivAt_logZeta {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt logZeta (deriv riemannZeta s / riemannZeta s) s := by
  have habs : LSeries.abscissaOfAbsConv logZetaCoeff < (s.re : EReal) :=
    lt_of_le_of_lt abscissaOfAbsConv_logZetaCoeff_le_one (EReal.coe_lt_coe_iff.mpr hs)
  have hd_L : HasDerivAt (LSeries logZetaCoeff)
      (LSeries (fun m ↦ -Complex.log m * logZetaCoeff m) s) s :=
    hasDerivAt_LSeries habs
  have hev : LSeries logZetaCoeff =ᶠ[𝓝 s] logZeta := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    exact (logZeta_eq_LSeries hz).symm
  have hL_eq_negΛ : LSeries (fun m ↦ -Complex.log m * logZetaCoeff m) s =
      deriv riemannZeta s / riemannZeta s := by
    have hcongr : LSeries (fun m ↦ -Complex.log m * logZetaCoeff m) s =
        LSeries (fun m ↦ -(ArithmeticFunction.vonMangoldt m : ℂ)) s := by
      refine LSeries_congr (fun {m} hm ↦ ?_) s
      dsimp only [logZetaCoeff]
      have hchar : (1 : DirichletCharacter ℂ 1) m = 1 :=
        MulChar.one_apply (isUnit_of_subsingleton (m : ZMod 1))
      rw [hchar, one_mul]
      rcases eq_or_ne m 1 with rfl | hm1
      · simp
      · have hm2 : 2 ≤ m := by omega
        have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
        have hlog_ne : (Real.log (m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
        have hclog : Complex.log (m : ℂ) = (Real.log (m : ℝ) : ℂ) := by
          rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg m)]
        rw [hclog]
        field_simp [hlog_ne]
    have hneg_eq : LSeries (fun m ↦ -(ArithmeticFunction.vonMangoldt m : ℂ)) s =
        -LSeries (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) s :=
      LSeries_neg (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) s
    rw [hcongr, hneg_eq, LSeries_vonMangoldt_eq hs]
    ring
  rw [hL_eq_negΛ] at hd_L
  exact hd_L.congr_of_eventuallyEq hev.symm

/-- Formula for `deriv logZeta s` when `1 < Re s`. -/
theorem deriv_logZeta {s : ℂ} (hs : 1 < s.re) :
    deriv logZeta s = deriv riemannZeta s / riemannZeta s :=
  (hasDerivAt_logZeta hs).deriv

/-- `logZeta` is holomorphic on the open half-plane `{s : ℂ | 1 < Re s}`. -/
theorem differentiableOn_logZeta :
    DifferentiableOn ℂ logZeta {s : ℂ | 1 < s.re} := fun _ hs ↦
  (hasDerivAt_logZeta hs).differentiableAt.differentiableWithinAt

end AnalyticNumberTheory.RiemannZeta
