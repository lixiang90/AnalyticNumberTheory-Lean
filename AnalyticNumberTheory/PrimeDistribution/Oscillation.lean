import AnalyticNumberTheory.DirichletSeries.Uniqueness
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.HadamardFactorization
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.Transforms
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Oscillation Theorems for Primes and Arithmetic Functions

This file develops Landau's singularity/oscillation method (for both Dirichlet series and
continuous Mellin transforms), global properties of the zeros and real-axis sign of the Riemann
zeta function via the Hadamard factorization of `ξ` and Stirling's formula, unconditional
Phragmén–Landau `Ω_±` theorems for `ψ(x) - x`, the Mertens function `M(x)`, `θ(x) - x`, and
`π(x) - Li(x)`, and conditional Littlewood `Ω_±` deductions from explicit zero-sum bounds via
simultaneous Dirichlet approximation.
-/

noncomputable section

namespace AnalyticNumberTheory.PrimeDistribution

open Complex MeasureTheory Set Filter Topology
open scoped ComplexOrder
open AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.RiemannZeta
open AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.EntireFunctions
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.Summation

section LandauBridges

/-- **Landau's theorem for Dirichlet series with nonnegative real coefficients.**
If `0 ≤ a n` for all `n`, the Dirichlet series of `a` converges absolutely for `Re s > σ₀`,
and its sum extends analytically to `Metric.ball (σ₀ : ℂ) r`, then the series extends and
converges absolutely for `Re s > σ₀ - r / 6`. -/
theorem landau_dirichlet_real {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₀ r : ℝ} (hr : 0 < r)
    (hσ : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ σ₀)
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
      F z = LSeries (fun n ↦ (a n : ℂ)) z) :
    LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ σ₀ - r / 6 ∧
      (∀ s : ℂ, σ₀ - r / 6 < s.re → LSeriesSummable (fun n ↦ (a n : ℂ)) s) ∧
      (∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ - r / 6 < z.re →
        F z = LSeries (fun n ↦ (a n : ℂ)) z) :=
  AnalyticNumberTheory.DirichletSeries.landau_theorem_real ha hr hσ hF_diff hF_eq

/-- **Landau's theorem for Dirichlet series agreeing on an upper real interval `(σ₀, σ₀ + w)`.** -/
theorem landau_dirichlet_of_eqOn_Ioo {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {σ₀ r w : ℝ} (hr : 0 < r) (hw : 0 < w)
    (hσ : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ σ₀)
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ t : ℝ, σ₀ < t → t < σ₀ + w →
      F (t : ℂ) = LSeries (fun n ↦ (a n : ℂ)) (t : ℂ)) :
    LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ σ₀ - r / 6 := by
  have haℂ : (0 : ℕ → ℂ) ≤ fun n ↦ (a n : ℂ) := fun n ↦ by
    change (0 : ℝ) ≤ ((a n : ℂ)).re ∧ (0 : ℝ) = ((a n : ℂ)).im
    exact ⟨ha n, rfl⟩
  exact AnalyticNumberTheory.DirichletSeries.landau_theorem_of_eqOn_Ioo
    haℂ hr hw hσ hF_diff hF_eq

/-- **Landau singularity at the abscissa of convergence.**
A Dirichlet series with nonnegative coefficients and finite abscissa of absolute convergence `σ₀`
cannot extend analytically across `σ₀`. -/
theorem not_analyticAt_dirichlet_of_abscissa_eq {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {σ₀ : ℝ} (hσ : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) = σ₀)
    {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
      F z = LSeries (fun n ↦ (a n : ℂ)) z) :
    False := by
  have haℂ : (0 : ℕ → ℂ) ≤ fun n ↦ (a n : ℂ) := fun n ↦ by
    change (0 : ℝ) ≤ ((a n : ℂ)).re ∧ (0 : ℝ) = ((a n : ℂ)).im
    exact ⟨ha n, rfl⟩
  exact AnalyticNumberTheory.DirichletSeries.not_analyticAt_of_abscissaOfAbsConv_eq
    haℂ hσ hr hF_diff hF_eq

end LandauBridges

section MellinLandau

private def mellinKernel (g : ℝ → ℝ) (k : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (g t : ℂ) * (-Real.log t : ℂ) ^ k * (t : ℂ) ^ (-z - 1)

private def mellinIntegralK (g : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi x₀, mellinKernel g k z t

private lemma log_pow_le_rpow_mul_const (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 1 ≤ t) :
    (Real.log t) ^ k ≤ ((k : ℝ) / δ) ^ k * t ^ δ := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.one_le_rpow ht hδ.le
  · set y := δ * Real.log t
    have hy : 0 ≤ y := mul_nonneg hδ.le hlog
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    set u := y / (k : ℝ)
    have hu : 0 ≤ u := div_nonneg hy hkpos.le
    have hexp_u : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hpow : u ^ k ≤ (Real.exp u) ^ k := pow_le_pow_left₀ hu hexp_u k
    have hrexp : (Real.exp u) ^ k = Real.exp y := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [u]
      field_simp [hkpos.ne']
    have hyk : y ^ k ≤ (k : ℝ) ^ k * Real.exp y := by
      calc
        y ^ k = ((k : ℝ) * u) ^ k := by
          congr 1
          dsimp [u]
          field_simp [hkpos.ne']
        _ = (k : ℝ) ^ k * u ^ k := mul_pow _ _ _
        _ ≤ (k : ℝ) ^ k * Real.exp y :=
          mul_le_mul_of_nonneg_left (hpow.trans_eq hrexp) (pow_nonneg hkpos.le _)
    calc
      (Real.log t) ^ k = (y / δ) ^ k := by
        congr 1
        dsimp [y]
        field_simp [hδ.ne']
      _ = y ^ k / δ ^ k := div_pow _ _ _
      _ ≤ ((k : ℝ) ^ k * Real.exp y) / δ ^ k :=
        div_le_div_of_nonneg_right hyk (pow_nonneg hδ.le _)
      _ = ((k : ℝ) / δ) ^ k * Real.exp (δ * Real.log t) := by
        rw [div_pow]
        dsimp [y]
        ring
      _ = ((k : ℝ) / δ) ^ k * t ^ δ := by
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one ht), mul_comm (Real.log t) δ]

private lemma norm_mellinKernel_le {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) (k : ℕ)
    {σ₁ σ₂ v : ℝ} (hv : 0 < v) {w : ℂ} (hw₁ : σ₁ + v ≤ w.re) (hw₂ : w.re ≤ σ₂)
    {t : ℝ} (ht : t ∈ Set.Ioi x₀) :
    ‖mellinKernel g k w t‖ ≤
      ((k : ℝ) / v) ^ k * (g t * t ^ (-σ₁ - 1)) +
        |Real.log x₀| ^ k * (g t * t ^ (-σ₂ - 1)) := by
  have htpos : 0 < t := lt_trans hx₀ ht
  have hg : 0 ≤ g t := hg_nonneg t ht
  have hnorm : ‖mellinKernel g k w t‖ =
      g t * |Real.log t| ^ k * t ^ (-w.re - 1) := by
    simp only [mellinKernel, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
    rw [abs_of_nonneg hg]
  rw [hnorm]
  have hterm1_nonneg : 0 ≤ ((k : ℝ) / v) ^ k * (g t * t ^ (-σ₁ - 1)) :=
    mul_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg k) hv.le) _)
      (mul_nonneg hg (Real.rpow_pos_of_pos htpos _).le)
  have hterm2_nonneg : 0 ≤ |Real.log x₀| ^ k * (g t * t ^ (-σ₂ - 1)) :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _)
      (mul_nonneg hg (Real.rpow_pos_of_pos htpos _).le)
  by_cases ht1 : 1 ≤ t
  · have hlog : |Real.log t| ^ k ≤ ((k : ℝ) / v) ^ k * t ^ v := by
      rw [abs_of_nonneg (Real.log_nonneg ht1)]
      exact log_pow_le_rpow_mul_const k hv ht1
    have hrpow : t ^ (-w.re - 1) ≤ t ^ (-(σ₁ + v) - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hsplit : t ^ v * t ^ (-(σ₁ + v) - 1) = t ^ (-σ₁ - 1) := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    calc
      g t * |Real.log t| ^ k * t ^ (-w.re - 1)
          ≤ g t * (((k : ℝ) / v) ^ k * t ^ v) * t ^ (-(σ₁ + v) - 1) := by
            gcongr
      _ = ((k : ℝ) / v) ^ k * (g t * (t ^ v * t ^ (-(σ₁ + v) - 1))) := by ring
      _ = ((k : ℝ) / v) ^ k * (g t * t ^ (-σ₁ - 1)) := by rw [hsplit]
      _ ≤ ((k : ℝ) / v) ^ k * (g t * t ^ (-σ₁ - 1)) +
            |Real.log x₀| ^ k * (g t * t ^ (-σ₂ - 1)) := le_add_of_nonneg_right hterm2_nonneg
  · have htle1 : t ≤ 1 := le_of_not_ge ht1
    have hlog_neg : Real.log t ≤ 0 := Real.log_nonpos htpos.le htle1
    have hlog_x₀ : Real.log x₀ ≤ Real.log t := Real.log_le_log hx₀ ht.le
    have habs : |Real.log t| ≤ |Real.log x₀| := by
      rw [abs_of_nonpos hlog_neg]
      linarith [neg_le_abs (Real.log x₀)]
    have hlog_pow : |Real.log t| ^ k ≤ |Real.log x₀| ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) habs k
    have hrpow : t ^ (-w.re - 1) ≤ t ^ (-σ₂ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge htpos htle1 (by linarith)
    calc
      g t * |Real.log t| ^ k * t ^ (-w.re - 1)
          ≤ g t * |Real.log x₀| ^ k * t ^ (-σ₂ - 1) := by gcongr
      _ = |Real.log x₀| ^ k * (g t * t ^ (-σ₂ - 1)) := by ring
      _ ≤ ((k : ℝ) / v) ^ k * (g t * t ^ (-σ₁ - 1)) +
            |Real.log x₀| ^ k * (g t * t ^ (-σ₂ - 1)) := le_add_of_nonneg_left hterm1_nonneg

private lemma aestronglyMeasurable_of_integrableOn {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    {σ₀ : ℝ} (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) :
    AEStronglyMeasurable g (volume.restrict (Set.Ioi x₀)) := by
  have hg_one : IntegrableOn (fun t : ℝ => g t * t ^ (-(σ₀ + 1) - 1)) (Set.Ioi x₀) :=
    hg_int (σ₀ + 1) (by linarith)
  have hmul := hg_one.aestronglyMeasurable.mul
    (Measurable.aestronglyMeasurable (measurable_id.pow_const (σ₀ + 2)))
  refine hmul.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := lt_trans hx₀ ht
  simp only [Pi.mul_apply, id_eq]
  rw [mul_assoc, ← Real.rpow_add htpos]
  have hexp : -(σ₀ + 1) - 1 + (σ₀ + 2) = (0 : ℝ) := by ring
  rw [hexp, Real.rpow_zero, mul_one]

private lemma aestronglyMeasurable_mellinKernel {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀))
    (k : ℕ) (w : ℂ) :
    AEStronglyMeasurable (mellinKernel g k w) (volume.restrict (Set.Ioi x₀)) := by
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioi x₀)) :=
    aestronglyMeasurable_of_integrableOn hx₀ hg_int
  have hlog_meas : AEStronglyMeasurable (fun t : ℝ => (-Real.log t : ℂ) ^ k)
      (volume.restrict (Set.Ioi x₀)) := by
    have hcont : ContinuousOn (fun t : ℝ => (-Real.log t : ℂ) ^ k) (Set.Ioi x₀) := by
      intro t ht
      have htne : t ≠ 0 := (lt_trans hx₀ ht).ne'
      refine ContinuousAt.continuousWithinAt ?_
      exact (((Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log htne)).neg).congr
        (by filter_upwards with x; simp) |>.pow k)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hcpow_meas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-w - 1))
      (volume.restrict (Set.Ioi x₀)) := by
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-w - 1)) (Set.Ioi x₀) := by
      intro t ht
      refine ContinuousAt.continuousWithinAt ?_
      exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using lt_trans hx₀ ht))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas).mul hlog_meas).mul
    hcpow_meas

private lemma integrableOn_mellinKernel {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀))
    (k : ℕ) {w : ℂ} (hw : σ₀ < w.re) :
    IntegrableOn (mellinKernel g k w) (Set.Ioi x₀) := by
  set v := (w.re - σ₀) / 3
  have hv : 0 < v := by dsimp [v]; linarith
  set σ₁ := w.re - 2 * v
  set σ₂ := w.re + v
  have hσ₁ : σ₀ < σ₁ := by dsimp [σ₁, v]; linarith
  have hw₁ : σ₁ + v ≤ w.re := by dsimp [σ₁, v]; linarith
  have hw₂ : w.re ≤ σ₂ := by dsimp [σ₂, v]; linarith
  have hdom : IntegrableOn (fun t : ℝ =>
      ((k : ℝ) / v) ^ k * (g t * t ^ (-σ₁ - 1)) +
        |Real.log x₀| ^ k * (g t * t ^ (-σ₂ - 1))) (Set.Ioi x₀) :=
    ((hg_int σ₁ hσ₁).const_mul _).add ((hg_int σ₂ (by dsimp [σ₂]; linarith)).const_mul _)
  refine hdom.mono' (aestronglyMeasurable_mellinKernel hx₀ hg_int k w) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_mellinKernel_le hx₀ hg_nonneg k hv hw₁ hw₂ ht

private lemma hasDerivAt_mellinIntegralK {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀))
    (k : ℕ) {z : ℂ} (hz : σ₀ < z.re) :
    HasDerivAt (mellinIntegralK g x₀ k) (mellinIntegralK g x₀ (k + 1) z) z := by
  set v := (z.re - σ₀) / 3
  have hv : 0 < v := by dsimp [v]; linarith
  set σ₁ := z.re - 2 * v
  set σ₂ := z.re + v
  have hσ₁ : σ₀ < σ₁ := by dsimp [σ₁, v]; linarith
  have hdom_int : IntegrableOn (fun t : ℝ =>
      ((k + 1 : ℕ) / v) ^ (k + 1) * (g t * t ^ (-σ₁ - 1)) +
        |Real.log x₀| ^ (k + 1) * (g t * t ^ (-σ₂ - 1))) (Set.Ioi x₀) :=
    ((hg_int σ₁ hσ₁).const_mul _).add ((hg_int σ₂ (by dsimp [σ₂]; linarith)).const_mul _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t => mellinKernel g k w t)
    (F' := fun w t => mellinKernel g (k + 1) w t)
    (bound := fun t => ((k + 1 : ℕ) / v) ^ (k + 1) * (g t * t ^ (-σ₁ - 1)) +
      |Real.log x₀| ^ (k + 1) * (g t * t ^ (-σ₂ - 1)))
    (x₀ := z) (Metric.ball_mem_nhds z hv) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Metric.ball_mem_nhds z hv] with w _
    exact aestronglyMeasurable_mellinKernel hx₀ hg_int k w
  · exact integrableOn_mellinKernel hx₀ hg_nonneg hg_int k hz
  · exact aestronglyMeasurable_mellinKernel hx₀ hg_int (k + 1) z
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    have hw_re : σ₁ + v ≤ w.re ∧ w.re ≤ σ₂ := by
      have hball : ‖w - z‖ < v := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hw
      have hre : |w.re - z.re| < v := (Complex.abs_re_le_norm (w - z)).trans_lt hball
      have h1 : z.re - v < w.re := by linarith [(abs_lt.mp hre).1]
      have h2 : w.re < z.re + v := by linarith [(abs_lt.mp hre).2]
      exact ⟨by dsimp [σ₁]; linarith, by dsimp [σ₂]; linarith⟩
    exact norm_mellinKernel_le hx₀ hg_nonneg (k + 1) hv hw_re.1 hw_re.2 ht
  · exact hdom_int.integrable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w _
    have htpos : 0 < t := lt_trans hx₀ ht
    have hcpow : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (-w - 1))
        ((t : ℂ) ^ (-w - 1) * (-Complex.log (t : ℂ))) w := by
      have hlin : HasDerivAt (fun w : ℂ => -w - 1) (-1) w :=
        (hasDerivAt_id w).neg.sub_const 1
      have hc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
      convert (HasDerivAt.const_cpow (c := (t : ℂ)) hlin (Or.inl hc)) using 1
      ring
    have hlogc : Complex.log (t : ℂ) = (Real.log t : ℂ) := (Complex.ofReal_log htpos.le).symm
    have hderiv := hcpow.const_mul ((g t : ℂ) * (-Real.log t : ℂ) ^ k)
    have heq : (g t : ℂ) * (-Real.log t : ℂ) ^ k * ((t : ℂ) ^ (-w - 1) * -Complex.log (t : ℂ)) =
        mellinKernel g (k + 1) w t := by
      dsimp [mellinKernel]
      rw [hlogc, pow_succ]
      ring
    rwa [heq] at hderiv

private lemma differentiableOn_mellinIntegral {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) :
    DifferentiableOn ℂ (mellinIntegralK g x₀ 0) {z : ℂ | σ₀ < z.re} :=
  fun _ hz => (hasDerivAt_mellinIntegralK hx₀ hg_nonneg hg_int 0 hz).differentiableAt.differentiableWithinAt

/-- The Mellin integral of a signed measurable density is holomorphic in the
open half-plane where all of its real absolute moments converge. -/
theorem differentiableOn_mellin_of_abs_integrable {a σ₀ : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hm : Measurable g) (hi : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun x : ℝ => |g x| * x^(-σ-1)) (Ioi a)) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x in Ioi a, (g x:ℂ)*(x:ℂ)^(-s-1))
      {s : ℂ | σ₀ < s.re} := by
  let p (x : ℝ) := |g x|
  let q (x : ℝ) := |g x|-g x
  have hq (x : ℝ) : 0 ≤ q x := sub_nonneg.mpr (le_abs_self _)
  have hqi (σ : ℝ) (hσ : σ₀ < σ) : IntegrableOn (fun x : ℝ => q x*x^(-σ-1)) (Ioi a) := by
    apply ((hi σ hσ).const_mul 2).mono'
      ((((continuous_abs.measurable.comp hm).sub hm).mul (measurable_id.pow_const (-σ-1))).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx₀ := ha.trans hx
    change |q x*x^(-σ-1)| ≤ 2*(|g x| * x^(-σ-1))
    rw [abs_of_nonneg (mul_nonneg (hq x) (Real.rpow_nonneg hx₀.le _))]
    dsimp only [q]
    have hn : -g x ≤ |g x| := neg_le_abs _
    nlinarith [mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hx₀.le (-σ-1))]
  have hp := differentiableOn_mellinIntegral (g := p) ha (fun x _ => abs_nonneg _) hi
  have hn := differentiableOn_mellinIntegral (g := q) ha (fun x _ => hq x) hqi
  apply (hp.sub hn).congr
  intro s hs
  have ip := integrableOn_mellinKernel (g := p) ha (fun x _ => abs_nonneg _) hi 0 hs
  have iq := integrableOn_mellinKernel (g := q) ha (fun x _ => hq x) hqi 0 hs
  change _ = (∫ x in Ioi a, mellinKernel p 0 s x) - ∫ x in Ioi a, mellinKernel q 0 s x
  rw [←integral_sub ip iq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [mellinKernel,p,q,pow_zero,mul_one,Complex.ofReal_sub]
  ring

private lemma iteratedDeriv_mellinIntegral {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) :
    ∀ k : ℕ, ∀ z : ℂ, σ₀ < z.re →
      iteratedDeriv k (mellinIntegralK g x₀ 0) z = mellinIntegralK g x₀ k z := by
  intro k
  induction k with
  | zero =>
      intro z _
      rw [iteratedDeriv_zero]
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {w : ℂ | σ₀ < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hev : iteratedDeriv k (mellinIntegralK g x₀ 0) =ᶠ[𝓝 z] mellinIntegralK g x₀ k := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact ih w hw
      rw [hev.deriv_eq]
      exact (hasDerivAt_mellinIntegralK hx₀ hg_nonneg hg_int k hz).deriv

private lemma eventuallyEq_iteratedDeriv {f₁ f₂ : ℂ → ℂ} {z : ℂ}
    (h : f₁ =ᶠ[𝓝 z] f₂) : ∀ k : ℕ, iteratedDeriv k f₁ z = iteratedDeriv k f₂ z := by
  intro k
  induction k generalizing z with
  | zero => simp only [iteratedDeriv_zero]; exact h.eq_of_nhds
  | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      obtain ⟨s, hs_sub, hs_open, hzs⟩ := eventually_nhds_iff.mp h
      have hev : iteratedDeriv k f₁ =ᶠ[𝓝 z] iteratedDeriv k f₂ := by
        filter_upwards [hs_open.mem_nhds hzs] with w hw
        exact ih (eventually_nhds_iff.mpr ⟨s, hs_sub, hs_open, hw⟩)
      exact hev.deriv_eq

private lemma integrableOn_small_of_gt {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) (_hx₁ : x₀ ≤ x₁)
    {g : ℝ → ℝ} {σ₀ : ℝ} (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) :
    IntegrableOn g (Set.Ioc x₀ x₁) := by
  set σ₁ := σ₀ + 1
  have h1 : IntegrableOn (fun t : ℝ => g t * t ^ (-σ₁ - 1)) (Set.Ioi x₀) :=
    hg_int σ₁ (by linarith)
  have h1_loc : IntegrableOn (fun t : ℝ => g t * t ^ (-σ₁ - 1)) (Set.Ioc x₀ x₁) :=
    h1.mono_set Set.Ioc_subset_Ioi_self
  have hcont : ContinuousOn (fun t : ℝ => t ^ (σ₁ + 1)) (Set.Icc x₀ x₁) := by
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    exact Real.continuousAt_rpow_const t (σ₁ + 1) (Or.inl (lt_of_lt_of_le hx₀ ht.1).ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (σ₁ + 1)) (volume.restrict (Set.Ioc x₀ x₁)) :=
    (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioc x₀ x₁)) := by
    refine (h1_loc.aestronglyMeasurable.mul hmeas).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := lt_trans hx₀ ht.1
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← Real.rpow_add htpos]
    have hexp : -σ₁ - 1 + (σ₁ + 1) = (0 : ℝ) := by ring
    rw [hexp, Real.rpow_zero, mul_one]
  refine (h1_loc.norm.const_mul C).mono' hg_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htpos : 0 < t := lt_trans hx₀ ht.1
  have hle : ‖t ^ (σ₁ + 1)‖ ≤ C := hC t (Set.Ioc_subset_Icc_self ht)
  have hgt_eq : g t = (g t * t ^ (-σ₁ - 1)) * t ^ (σ₁ + 1) := by
    rw [mul_assoc, ← Real.rpow_add htpos]
    have hexp : -σ₁ - 1 + (σ₁ + 1) = (0 : ℝ) := by ring
    rw [hexp, Real.rpow_zero, mul_one]
  calc
    ‖g t‖ = ‖g t * t ^ (-σ₁ - 1)‖ * ‖t ^ (σ₁ + 1)‖ := by
      conv_lhs => rw [hgt_eq, norm_mul]
    _ ≤ ‖g t * t ^ (-σ₁ - 1)‖ * C := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = C * ‖g t * t ^ (-σ₁ - 1)‖ := mul_comm _ _

private lemma integrableOn_mellin_small {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) (hx₁ : x₀ ≤ x₁)
    {g : ℝ → ℝ} (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioc x₀ x₁) := by
  have hg_loc : IntegrableOn g (Set.Ioc x₀ x₁) :=
    integrableOn_small_of_gt hx₀ hx₁ hg_int
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-z.re - 1)) (Set.Icc x₀ x₁) :=
    fun t ht => (Real.continuousAt_rpow_const t _
      (Or.inl (lt_of_lt_of_le hx₀ ht.1).ne')).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hcont_c : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-z - 1)) (Set.Ioc x₀ x₁) :=
    fun t ht => (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
      (Or.inl (by simpa using lt_trans hx₀ ht.1))).continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1))
      (volume.restrict (Set.Ioc x₀ x₁)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_loc.aestronglyMeasurable).mul
      (hcont_c.aestronglyMeasurable measurableSet_Ioc)
  refine (hg_loc.const_mul C).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htpos : 0 < t := lt_trans hx₀ ht.1
  have hg0 : 0 ≤ g t := hg_nonneg t ht.1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0,
    Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
  calc
    g t * t ^ (-z.re - 1) ≤ g t * ‖t ^ (-z.re - 1)‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hg0
    _ ≤ g t * C := mul_le_mul_of_nonneg_left (hC t (Set.Ioc_subset_Icc_self ht)) hg0
    _ = C * g t := mul_comm _ _

private lemma differentiable_mellinSmall {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) (hx₁ : x₀ ≤ x₁)
    {g : ℝ → ℝ} (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ : ℝ}
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) :
    Differentiable ℂ (fun z : ℂ => ∫ t in Set.Ioc x₀ x₁, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
  have hg_loc : IntegrableOn g (Set.Ioc x₀ x₁) :=
    integrableOn_small_of_gt hx₀ hx₁ hg_int
  intro z
  have hcont_pow : ContinuousOn (fun t : ℝ => t ^ (-(z.re + 1) - 1)) (Set.Icc x₀ x₁) :=
    fun t ht => (Real.continuousAt_rpow_const t _
      (Or.inl (lt_of_lt_of_le hx₀ ht.1).ne')).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_pow
  have hcont_pow2 : ContinuousOn (fun t : ℝ => t ^ (-(z.re - 1) - 1)) (Set.Icc x₀ x₁) :=
    fun t ht => (Real.continuousAt_rpow_const t _
      (Or.inl (lt_of_lt_of_le hx₀ ht.1).ne')).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_pow2
  have hcont_log : ContinuousOn (fun t : ℝ => |Real.log t|) (Set.Icc x₀ x₁) :=
    ContinuousOn.abs (Real.continuousOn_log.mono (fun t ht => (lt_of_lt_of_le hx₀ ht.1).ne'))
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_log
  set C := max C₁ C₂
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioc x₀ x₁)) :=
    hg_loc.aestronglyMeasurable
  have hmeas_F : ∀ w : ℂ, AEStronglyMeasurable
      (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-w - 1)) (volume.restrict (Set.Ioc x₀ x₁)) := by
    intro w
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-w - 1)) (Set.Ioc x₀ x₁) :=
      fun t ht => (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using lt_trans hx₀ ht.1))).continuousWithinAt
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas).mul
      (hcont.aestronglyMeasurable measurableSet_Ioc)
  have hmeas_F' : AEStronglyMeasurable
      (fun t : ℝ => (g t : ℂ) * (-Real.log t : ℂ) * (t : ℂ) ^ (-z - 1))
      (volume.restrict (Set.Ioc x₀ x₁)) := by
    have hcont : ContinuousOn (fun t : ℝ => (-Real.log t : ℂ) * (t : ℂ) ^ (-z - 1))
        (Set.Ioc x₀ x₁) := by
      intro t ht
      have htpos : 0 < t := lt_trans hx₀ ht.1
      have htne : t ≠ 0 := htpos.ne'
      exact ((Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log htne).neg).mul
        (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
          (Or.inl (by simpa using htpos)))).continuousWithinAt
    have h1 := (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas).mul
      (hcont.aestronglyMeasurable measurableSet_Ioc)
    refine h1.congr ?_
    filter_upwards with t
    simp [mul_assoc]
  have hint_z : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1))
      (Set.Ioc x₀ x₁) :=
    integrableOn_mellin_small hx₀ hx₁ hg_nonneg hg_int z
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t => (g t : ℂ) * (t : ℂ) ^ (-w - 1))
    (F' := fun w t => (g t : ℂ) * (-Real.log t : ℂ) * (t : ℂ) ^ (-w - 1))
    (bound := fun t => (L * C) * g t)
    (x₀ := z) (Metric.ball_mem_nhds z zero_lt_one) ?_ hint_z.integrable hmeas_F' ?_ ?_ ?_).2.differentiableAt
  · filter_upwards [Metric.ball_mem_nhds z zero_lt_one] with w _
    exact hmeas_F w
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w hw
    have htpos : 0 < t := lt_trans hx₀ ht.1
    have hg0 : 0 ≤ g t := hg_nonneg t ht.1
    have hw_re : z.re - 1 < w.re ∧ w.re < z.re + 1 := by
      have hball : ‖w - z‖ < 1 := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hw
      have hre : |w.re - z.re| < 1 := (Complex.abs_re_le_norm (w - z)).trans_lt hball
      exact ⟨by linarith [(abs_lt.mp hre).1], by linarith [(abs_lt.mp hre).2]⟩
    have hpow : t ^ (-w.re - 1) ≤ C := by
      by_cases h1 : 1 ≤ t
      · calc
          t ^ (-w.re - 1) ≤ t ^ (-(z.re - 1) - 1) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ ≤ ‖t ^ (-(z.re - 1) - 1)‖ := le_abs_self _
          _ ≤ C₂ := hC₂ t (Set.Ioc_subset_Icc_self ht)
          _ ≤ C := le_max_right _ _
      · calc
          t ^ (-w.re - 1) ≤ t ^ (-(z.re + 1) - 1) :=
            Real.rpow_le_rpow_of_exponent_ge htpos (le_of_not_ge h1) (by linarith)
          _ ≤ ‖t ^ (-(z.re + 1) - 1)‖ := le_abs_self _
          _ ≤ C₁ := hC₁ t (Set.Ioc_subset_Icc_self ht)
          _ ≤ C := le_max_left _ _
    have hlogt : |Real.log t| ≤ L := by
      have := hL t (Set.Ioc_subset_Icc_self ht)
      simpa using this
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
    calc
      g t * |Real.log t| * t ^ (-w.re - 1)
          ≤ g t * L * C := by
            have hL0 : 0 ≤ L := (abs_nonneg _).trans hlogt
            gcongr
      _ = (L * C) * g t := by ring
  · exact hg_loc.const_mul (L * C)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w _
    have htpos : 0 < t := lt_trans hx₀ ht.1
    have hcpow : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (-w - 1))
        ((t : ℂ) ^ (-w - 1) * (-Complex.log (t : ℂ))) w := by
      have hlin : HasDerivAt (fun w : ℂ => -w - 1) (-1) w :=
        (hasDerivAt_id w).neg.sub_const 1
      convert (HasDerivAt.const_cpow (c := (t : ℂ)) hlin
        (Or.inl (Complex.ofReal_ne_zero.mpr htpos.ne'))) using 1
      ring
    have hlogc : Complex.log (t : ℂ) = (Real.log t : ℂ) := (Complex.ofReal_log htpos.le).symm
    have hderiv := hcpow.const_mul (g t : ℂ)
    have heq : (g t : ℂ) * ((t : ℂ) ^ (-w - 1) * -Complex.log (t : ℂ)) =
        (g t : ℂ) * (-Real.log t : ℂ) * (t : ℂ) ^ (-w - 1) := by
      rw [hlogc]
      ring
    rwa [heq] at hderiv

private lemma integrableOn_mellin_of_ge_one {x₁ : ℝ} (hx₁ : 1 ≤ x₁) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₁, 0 ≤ g t) {σ₀ r : ℝ} (hr : 0 < r)
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₁))
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
      F z = ∫ t in Set.Ioi x₁, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) :
    ∀ σ : ℝ, σ₀ - r / 6 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₁) := by
  have hx₀ : 0 < x₁ := lt_of_lt_of_le zero_lt_one hx₁
  set u : ℝ := σ₀ + r / 6
  set R₀ : ℝ := 2 * r / 3
  have hu : σ₀ < u := by dsimp [u]; linarith
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have hball_sub : Metric.ball (u : ℂ) R₀ ⊆ Metric.ball (σ₀ : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have hudist : dist (u : ℂ) (σ₀ : ℂ) = r / 6 := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      dsimp [u]
      rw [add_sub_cancel_left, abs_of_pos (by linarith)]
    have htri : dist z (σ₀ : ℂ) ≤ dist z (u : ℂ) + dist (u : ℂ) (σ₀ : ℂ) := dist_triangle _ _ _
    dsimp [R₀] at hz ⊢
    linarith
  have hF_ball : DifferentiableOn ℂ F (Metric.ball (u : ℂ) R₀) :=
    hF_diff.mono hball_sub
  intro σ hσ
  by_cases hσu : u ≤ σ
  · exact hg_int σ (lt_of_lt_of_le hu hσu)
  · have hσu_lt : σ < u := lt_of_not_ge hσu
    have hmem_σ : (σ : ℂ) ∈ Metric.ball (u : ℂ) R₀ := by
      rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hσu_lt)]
      dsimp [u, R₀]
      linarith
    have hsum_F := Complex.hasSum_taylorSeries_on_ball hF_ball hmem_σ
    have hU₀_open : IsOpen (Metric.ball (σ₀ : ℂ) r ∩ {w : ℂ | σ₀ < w.re}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    have hu_mem_U₀ : (u : ℂ) ∈ Metric.ball (σ₀ : ℂ) r ∩ {w : ℂ | σ₀ < w.re} := by
      refine ⟨?_, by simpa using hu⟩
      rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      dsimp [u]
      rw [add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith
    have hev_F : F =ᶠ[𝓝 (u : ℂ)] mellinIntegralK g x₁ 0 := by
      filter_upwards [hU₀_open.mem_nhds hu_mem_U₀] with w hw
      have := hF_eq w hw.1 hw.2
      simpa [mellinIntegralK, mellinKernel] using this
    let termFn : ℕ → ℝ → ℝ := fun k t =>
      (Nat.factorial k : ℝ)⁻¹ * ((u - σ) * Real.log t) ^ k * (g t * t ^ (-u - 1))
    have hker_term : ∀ k : ℕ, ∀ t ∈ Set.Ioi x₁,
        ((Nat.factorial k : ℂ)⁻¹ * ((σ : ℂ) - (u : ℂ)) ^ k) * mellinKernel g k (u : ℂ) t =
          (termFn k t : ℂ) := by
      intro k t ht
      have htpos : 0 < t := lt_trans hx₀ ht
      have hcpow : (t : ℂ) ^ (-(u : ℂ) - 1) = ((t ^ (-u - 1) : ℝ) : ℂ) := by
        have hc : (-(u : ℂ) - 1 : ℂ) = ((-u - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [hc, ← Complex.ofReal_cpow htpos.le]
      have hpow : ((σ : ℂ) - (u : ℂ)) ^ k * (-Real.log t : ℂ) ^ k =
          ((((u - σ) * Real.log t : ℝ) ^ k : ℝ) : ℂ) := by
        rw [← mul_pow]
        have hsub : ((σ : ℂ) - (u : ℂ)) * (-Real.log t : ℂ) =
            (((u - σ) * Real.log t : ℝ) : ℂ) := by
          push_cast; ring
        rw [hsub, Complex.ofReal_pow]
      dsimp [mellinKernel, termFn]
      rw [hcpow]
      simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
      calc
        (Nat.factorial k : ℂ)⁻¹ * ((σ : ℂ) - (u : ℂ)) ^ k *
            ((g t : ℂ) * (-Real.log t : ℂ) ^ k * ((t ^ (-u - 1) : ℝ) : ℂ))
            = (Nat.factorial k : ℂ)⁻¹ * (((σ : ℂ) - (u : ℂ)) ^ k * (-Real.log t : ℂ) ^ k) *
                ((g t : ℂ) * ((t ^ (-u - 1) : ℝ) : ℂ)) := by ring
        _ = (Nat.factorial k : ℂ)⁻¹ * ((((u - σ) * Real.log t : ℝ) ^ k : ℝ) : ℂ) *
                ((g t : ℂ) * ((t ^ (-u - 1) : ℝ) : ℂ)) := by rw [hpow]
    have hterm_eq : ∀ k : ℕ,
        ((Nat.factorial k : ℂ)⁻¹ • ((σ : ℂ) - (u : ℂ)) ^ k • iteratedDeriv k F (u : ℂ)) =
          ((∫ t in Set.Ioi x₁, termFn k t : ℝ) : ℂ) := by
      intro k
      rw [eventuallyEq_iteratedDeriv hev_F k, iteratedDeriv_mellinIntegral hx₀ hg_nonneg hg_int k u hu]
      dsimp [mellinIntegralK]
      simp only [← integral_const_mul]
      have hint_eq : (fun t : ℝ =>
          (Nat.factorial k : ℂ)⁻¹ * (((σ : ℂ) - (u : ℂ)) ^ k * mellinKernel g k (u : ℂ) t)) =ᶠ[ae (volume.restrict (Set.Ioi x₁))]
            (fun t : ℝ => (termFn k t : ℂ)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [← mul_assoc]
        exact hker_term k t ht
      rw [integral_congr_ae hint_eq]
      exact integral_ofReal
    have hsum_real : HasSum (fun k : ℕ => ∫ t in Set.Ioi x₁, termFn k t) (F (σ : ℂ)).re := by
      have hsum_c : HasSum (fun k : ℕ => ((∫ t in Set.Ioi x₁, termFn k t : ℝ) : ℂ)) (F (σ : ℂ)) := by
        refine hsum_F.congr_fun ?_
        intro k
        exact (hterm_eq k).symm
      exact (Complex.reCLM.hasSum hsum_c).congr_fun (fun _ => rfl)
    have hterm_nonneg : ∀ k : ℕ, ∀ t ∈ Set.Ioi x₁, 0 ≤ termFn k t := by
      intro k t ht
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (hx₁.trans ht.le)
      have htpos : 0 < t := lt_trans hx₀ ht
      dsimp [termFn]
      refine mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (pow_nonneg (mul_nonneg (by linarith) hlog0) _))
        (mul_nonneg (hg_nonneg t ht) (Real.rpow_pos_of_pos htpos _).le)
    have hterm_int : ∀ k : ℕ, IntegrableOn (termFn k) (Set.Ioi x₁) := by
      intro k
      have hu_re : σ₀ < (u : ℂ).re := by simpa using hu
      have hk_ker := (integrableOn_mellinKernel hx₀ hg_nonneg hg_int k hu_re).const_mul
        ((Nat.factorial k : ℂ)⁻¹ * ((σ : ℂ) - (u : ℂ)) ^ k)
      have hre := Complex.reCLM.integrable_comp hk_ker
      refine hre.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change (((Nat.factorial k : ℂ)⁻¹ * ((σ : ℂ) - (u : ℂ)) ^ k) *
          mellinKernel g k (u : ℂ) t).re = termFn k t
      rw [hker_term k t ht, Complex.ofReal_re]
    have hint_nonneg : ∀ k : ℕ, 0 ≤ ∫ t in Set.Ioi x₁, termFn k t := fun k =>
      setIntegral_nonneg measurableSet_Ioi (fun t ht => hterm_nonneg k t ht)
    have htend_enn : Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, ∫⁻ t in Set.Ioi x₁, ENNReal.ofReal (termFn k t))
        atTop (𝓝 (ENNReal.ofReal (F (σ : ℂ)).re)) := by
      have h_eq : ∀ k : ℕ, ∫⁻ t in Set.Ioi x₁, ENNReal.ofReal (termFn k t) =
          ENNReal.ofReal (∫ t in Set.Ioi x₁, termFn k t) := fun k =>
        (ofReal_integral_eq_lintegral_ofReal (hterm_int k)
          (ae_restrict_of_forall_mem measurableSet_Ioi (hterm_nonneg k))).symm
      have hcomp := (ENNReal.continuous_ofReal.tendsto (F (σ : ℂ)).re).comp
        hsum_real.tendsto_sum_nat
      refine hcomp.congr ?_
      intro n
      simp only [Function.comp_apply, h_eq]
      exact ENNReal.ofReal_sum_of_nonneg (fun k _ => hint_nonneg k)
    have htsum_enn : (∑' k : ℕ, ∫⁻ t in Set.Ioi x₁, ENNReal.ofReal (termFn k t)) =
        ENNReal.ofReal (F (σ : ℂ)).re :=
      tendsto_nhds_unique (ENNReal.tendsto_nat_tsum _) htend_enn
    have hlint_lt : (∫⁻ t in Set.Ioi x₁, ∑' k : ℕ, ENNReal.ofReal (termFn k t)) < ⊤ := by
      have hl := lintegral_tsum (fun k =>
        ENNReal.measurable_ofReal.comp_aemeasurable (hterm_int k).aestronglyMeasurable.aemeasurable)
      simp only [Function.comp_apply] at hl
      rw [hl, htsum_enn]
      exact ENNReal.ofReal_lt_top
    have hpt_tsum : ∀ t ∈ Set.Ioi x₁,
        (∑' k : ℕ, ENNReal.ofReal (termFn k t)) = ENNReal.ofReal (g t * t ^ (-σ - 1)) := by
      intro t ht
      have htpos : 0 < t := lt_trans hx₀ ht
      have hhas_exp : HasSum (fun k : ℕ => ((u - σ) * Real.log t) ^ k / (Nat.factorial k : ℝ))
          (Real.exp ((u - σ) * Real.log t)) := by
        rw [Real.exp_eq_exp_ℝ]
        exact NormedSpace.expSeries_div_hasSum_exp ((u - σ) * Real.log t)
      have hhas_term : HasSum (fun k : ℕ => termFn k t) (g t * t ^ (-σ - 1)) := by
        have h1 := hhas_exp.mul_right (g t * t ^ (-u - 1))
        have hsum_eq : (fun k : ℕ => ((u - σ) * Real.log t) ^ k / (Nat.factorial k : ℝ) *
            (g t * t ^ (-u - 1))) = fun k : ℕ => termFn k t := by
          ext k; dsimp [termFn]; ring
        have hval_eq : Real.exp ((u - σ) * Real.log t) * (g t * t ^ (-u - 1)) =
            g t * t ^ (-σ - 1) := by
          rw [mul_comm (u - σ) (Real.log t), ← Real.rpow_def_of_pos htpos,
            mul_left_comm, ← Real.rpow_add htpos]
          have hexp : u - σ + (-u - 1) = -σ - 1 := by ring
          rw [hexp]
        rw [hsum_eq, hval_eq] at h1
        exact h1
      have htend_pt : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, ENNReal.ofReal (termFn k t))
          atTop (𝓝 (ENNReal.ofReal (g t * t ^ (-σ - 1)))) := by
        have hcomp := (ENNReal.continuous_ofReal.tendsto (g t * t ^ (-σ - 1))).comp
          hhas_term.tendsto_sum_nat
        refine hcomp.congr ?_
        intro n
        exact ENNReal.ofReal_sum_of_nonneg (fun k _ => hterm_nonneg k t ht)
      exact tendsto_nhds_unique (ENNReal.tendsto_nat_tsum _) htend_pt
    have hlint_fin : (∫⁻ t in Set.Ioi x₁, ENNReal.ofReal (g t * t ^ (-σ - 1))) < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq ?_) hlint_lt
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hpt_tsum t ht).symm
    have hmeas_res : AEStronglyMeasurable (fun t : ℝ => g t * t ^ (-σ - 1))
        (volume.restrict (Set.Ioi x₁)) := by
      have hg_m := aestronglyMeasurable_of_integrableOn hx₀ hg_int
      have hpow_m : AEStronglyMeasurable (fun t : ℝ => t ^ (-σ - 1))
          (volume.restrict (Set.Ioi x₁)) :=
        (ContinuousOn.aestronglyMeasurable
          (fun t ht => (Real.continuousAt_rpow_const t _ (Or.inl (lt_trans hx₀ ht).ne')).continuousWithinAt)
          measurableSet_Ioi)
      exact hg_m.mul hpow_m
    refine ⟨hmeas_res, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    refine lt_of_le_of_lt (le_of_eq ?_) hlint_fin
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans hx₀ ht
    have hnn : 0 ≤ g t * t ^ (-σ - 1) :=
      mul_nonneg (hg_nonneg t ht) (Real.rpow_pos_of_pos htpos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]

/-- **Continuous Mellin-integral Landau theorem.**
Suppose `x₀ > 0`, `g` is nonnegative on `Ioi x₀`, the Mellin integral
`∫ t in Ioi x₀, g t * t ^ (-σ - 1)` is Lebesgue-integrable for `σ > σ₀`, and
`s ↦ ∫ t in Ioi x₀, (g t : ℂ) * (t : ℂ) ^ (-s - 1)` agrees on `{z ∈ ball (σ₀ : ℂ) r | σ₀ < z.re}`
with a function `F` holomorphic on `Metric.ball (σ₀ : ℂ) r`.
Then the integral converges (absolutely) for `Re s > σ₀ - r / 6` and agrees with `F` on
`{z ∈ ball (σ₀ : ℂ) r | σ₀ - r / 6 < z.re}`. -/
theorem landau_mellin_integral {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ r : ℝ} (hr : 0 < r)
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀))
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
      F z = ∫ t in Set.Ioi x₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) :
    (∀ σ : ℝ, σ₀ - r / 6 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) ∧
      (∀ s : ℂ, σ₀ - r / 6 < s.re →
        IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi x₀)) ∧
      (∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ - r / 6 < z.re →
        F z = ∫ t in Set.Ioi x₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
  set x₁ : ℝ := max x₀ 1
  have hx₁ : 1 ≤ x₁ := le_max_right x₀ 1
  have hx₀₁ : x₀ ≤ x₁ := le_max_left x₀ 1
  have hx₁_pos : 0 < x₁ := lt_of_lt_of_le zero_lt_one hx₁
  let Msmall : ℂ → ℂ := fun z => ∫ t in Set.Ioc x₀ x₁, (g t : ℂ) * (t : ℂ) ^ (-z - 1)
  have hMsmall_diff : Differentiable ℂ Msmall :=
    differentiable_mellinSmall hx₀ hx₀₁ hg_nonneg hg_int
  let F₁ : ℂ → ℂ := fun z => F z - Msmall z
  have hF₁_diff : DifferentiableOn ℂ F₁ (Metric.ball (σ₀ : ℂ) r) :=
    hF_diff.sub hMsmall_diff.differentiableOn
  have hIoi_split : Set.Ioi x₀ = Set.Ioc x₀ x₁ ∪ Set.Ioi x₁ := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t x₁ with hle | hgt
      · exact Or.inl ⟨ht, hle⟩
      · exact Or.inr hgt
    · rintro (⟨ht, _⟩ | hgt)
      · exact ht
      · exact lt_of_le_of_lt hx₀₁ hgt
  have hdisj : Disjoint (Set.Ioc x₀ x₁) (Set.Ioi x₁) := Set.Ioc_disjoint_Ioi_same
  have hF₁_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
      F₁ z = ∫ t in Set.Ioi x₁, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
    intro z hz hzr
    have hint_all : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi x₀) := by
      have hm := integrableOn_mellinKernel hx₀ hg_nonneg hg_int 0 hzr
      refine hm.congr_fun ?_ measurableSet_Ioi
      intro t _
      simp [mellinKernel]
    have hint₁ : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioc x₀ x₁) :=
      hint_all.mono_set Set.Ioc_subset_Ioi_self
    have hint₂ : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi x₁) :=
      hint_all.mono_set (Set.Ioi_subset_Ioi hx₀₁)
    have hunion : (∫ t in Set.Ioi x₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) =
        (∫ t in Set.Ioc x₀ x₁, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) +
          ∫ t in Set.Ioi x₁, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
      rw [hIoi_split]
      exact setIntegral_union hdisj measurableSet_Ioi hint₁ hint₂
    dsimp [F₁, Msmall]
    rw [hF_eq z hz hzr, hunion]
    ring
  have hg_tail : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₁) :=
    fun σ hσ => (hg_int σ hσ).mono_set (Set.Ioi_subset_Ioi hx₀₁)
  have hg_tail_ext : ∀ σ : ℝ, σ₀ - r / 6 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₁) :=
    integrableOn_mellin_of_ge_one hx₁ (fun t ht => hg_nonneg t (lt_of_le_of_lt hx₀₁ ht))
      hr hg_tail hF₁_diff hF₁_eq
  have hreal_ext : ∀ σ : ℝ, σ₀ - r / 6 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀) := by
    intro σ hσ
    rw [hIoi_split]
    refine IntegrableOn.union ?_ (hg_tail_ext σ hσ)
    have hsm := (integrableOn_mellin_small hx₀ hx₀₁ hg_nonneg hg_int (σ : ℂ)).re
    refine hsm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := lt_trans hx₀ ht.1
    have hcpow : (t : ℂ) ^ (-(σ : ℂ) - 1) = ((t ^ (-σ - 1) : ℝ) : ℂ) := by
      have hc : (-(σ : ℂ) - 1 : ℂ) = ((-σ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, ← Complex.ofReal_cpow htpos.le]
    change ((g t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)).re = g t * t ^ (-σ - 1)
    rw [hcpow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hcomplex_ext : ∀ s : ℂ, σ₀ - r / 6 < s.re →
      IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi x₀) := by
    intro s hs
    have hm := integrableOn_mellinKernel hx₀ hg_nonneg hreal_ext 0 hs
    refine hm.congr_fun ?_ measurableSet_Ioi
    intro t _
    simp [mellinKernel]
  refine ⟨hreal_ext, hcomplex_ext, ?_⟩
  have hM_diff : DifferentiableOn ℂ (mellinIntegralK g x₀ 0) {z : ℂ | σ₀ - r / 6 < z.re} :=
    differentiableOn_mellinIntegral hx₀ hg_nonneg hreal_ext
  set U : Set ℂ := Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ - r / 6 < z.re}
  have hU_open : IsOpen U :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hU_preconn : IsPreconnected U := by
    refine Convex.isPreconnected ?_
    refine (convex_ball (σ₀ : ℂ) r).inter ?_
    intro x hx y hy a b ha hb hab
    rw [Set.mem_ofPred_eq] at hx hy
    change σ₀ - r / 6 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hsum : a * (σ₀ - r / 6) + b * (σ₀ - r / 6) = σ₀ - r / 6 := by
      rw [← add_mul, hab, one_mul]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      rw [hb1]; linarith
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · have ha1 : a = 1 := by linarith
        rw [ha1]; linarith
      · have h1 : a * (σ₀ - r / 6) < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
        have h2 : b * (σ₀ - r / 6) < b * y.re := mul_lt_mul_of_pos_left hy hb_pos
        linarith
  have hF_ana : AnalyticOnNhd ℂ F U := (hF_diff.mono Set.inter_subset_left).analyticOnNhd hU_open
  have hM_ana : AnalyticOnNhd ℂ (mellinIntegralK g x₀ 0) U :=
    (hM_diff.mono Set.inter_subset_right).analyticOnNhd hU_open
  set p : ℂ := ((σ₀ + r / 6 : ℝ) : ℂ)
  have hp_mem : p ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith
    · simp [p]; linarith
  have hU₀_open : IsOpen (Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hp_U₀ : p ∈ Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re} :=
    ⟨hp_mem.1, by simp [p]; linarith⟩
  have hev : F =ᶠ[𝓝 p] mellinIntegralK g x₀ 0 := by
    filter_upwards [hU₀_open.mem_nhds hp_U₀] with z hz
    simpa [mellinIntegralK, mellinKernel] using hF_eq z hz.1 hz.2
  have heqOn := hF_ana.eqOn_of_preconnected_of_eventuallyEq hM_ana hU_preconn hp_mem hev
  intro z hz1 hz2
  simpa [mellinIntegralK, mellinKernel] using heqOn ⟨hz1, hz2⟩

/-- **Continuous Mellin-integral Landau theorem from equality on `(σ₀, σ₀ + w)`.** -/
theorem landau_mellin_integral_of_eqOn_Ioo {x₀ : ℝ} (hx₀ : 0 < x₀) {g : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Ioi x₀, 0 ≤ g t) {σ₀ r w : ℝ} (hr : 0 < r) (hw : 0 < w)
    (hg_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀))
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ t : ℝ, σ₀ < t → t < σ₀ + w →
      F (t : ℂ) = ∫ u in Set.Ioi x₀, (g u : ℂ) * (u : ℂ) ^ (-(t : ℂ) - 1)) :
    (∀ σ : ℝ, σ₀ - r / 6 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi x₀)) ∧
      (∀ s : ℂ, σ₀ - r / 6 < s.re →
        IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi x₀)) ∧
      (∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ - r / 6 < z.re →
        F z = ∫ t in Set.Ioi x₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
  set U₀ : Set ℂ := Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re}
  have hU₀_open : IsOpen U₀ :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hU₀_preconn : IsPreconnected U₀ := by
    refine Convex.isPreconnected ?_
    refine (convex_ball (σ₀ : ℂ) r).inter ?_
    intro x hx y hy a b ha hb hab
    rw [Set.mem_ofPred_eq] at hx hy
    change σ₀ < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hsum : a * σ₀ + b * σ₀ = σ₀ := by
      rw [← add_mul, hab, one_mul]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      rw [hb1]; linarith
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · have ha1 : a = 1 := by linarith
        rw [ha1]; linarith
      · have h1 : a * σ₀ < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
        have h2 : b * σ₀ < b * y.re := mul_lt_mul_of_pos_left hy hb_pos
        linarith
  have hM_diff : DifferentiableOn ℂ (mellinIntegralK g x₀ 0) {z : ℂ | σ₀ < z.re} :=
    differentiableOn_mellinIntegral hx₀ hg_nonneg hg_int
  have hF_ana : AnalyticOnNhd ℂ F U₀ := (hF_diff.mono Set.inter_subset_left).analyticOnNhd hU₀_open
  have hM_ana : AnalyticOnNhd ℂ (mellinIntegralK g x₀ 0) U₀ :=
    (hM_diff.mono Set.inter_subset_right).analyticOnNhd hU₀_open
  set δ := min r w / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  set p : ℂ := ((σ₀ + δ : ℝ) : ℂ)
  have hp_mem : p ∈ U₀ := by
    refine ⟨?_, by simp [p]; exact hδ⟩
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hδ]
    dsimp [δ]
    linarith [min_le_left r w]
  have hfreq : ∃ᶠ z in 𝓝[≠] p, F z = mellinIntegralK g x₀ 0 z := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro U hU
    rw [Metric.mem_nhds_iff] at hU
    obtain ⟨ε, hε_pos, hε_sub⟩ := hU
    set η := min (ε / 2) (min r w / 4)
    have hη_pos : 0 < η := by dsimp [η]; positivity
    set q : ℝ := σ₀ + δ + η
    have hq_mem : (q : ℂ) ∈ U := by
      refine hε_sub ?_
      rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      have hdiff : q - (σ₀ + δ) = η := by dsimp [q]; ring
      rw [hdiff, abs_of_pos hη_pos]
      dsimp [η]
      linarith [min_le_left (ε / 2) (min r w / 4)]
    have hq_ne : (q : ℂ) ≠ p := by
      intro heq
      have := congrArg Complex.re heq
      simp [p, q] at this
      linarith
    have hq_low : σ₀ < q := by dsimp [q]; linarith
    have hq_high : q < σ₀ + w := by
      dsimp [q, δ, η]
      linarith [min_le_right r w, min_le_right (ε / 2) (min r w / 4)]
    refine ⟨(q : ℂ), hq_mem, ?_, hq_ne⟩
    simpa [mellinIntegralK, mellinKernel] using hF_eq q hq_low hq_high
  have heqOn : Set.EqOn F (mellinIntegralK g x₀ 0) U₀ :=
    hF_ana.eqOn_of_preconnected_of_frequently_eq hM_ana hU₀_preconn hp_mem hfreq
  refine landau_mellin_integral hx₀ hg_nonneg hr hg_int hF_diff ?_
  intro z hz1 hz2
  simpa [mellinIntegralK, mellinKernel] using heqOn ⟨hz1, hz2⟩

end MellinLandau

section ZetaSignAndZeros

/-- For any real number `x`, `riemannZeta (x : ℂ)` has zero imaginary part. -/
theorem riemannZeta_ofReal_im_eq_zero (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have h := riemannZeta_conj (x : ℂ)
  simp only [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- On the open real interval `(0, 1)`, `riemannZeta` is real and strictly negative. -/
theorem riemannZeta_ofReal_neg_on_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 ∧ (riemannZeta (σ : ℂ)).im = 0 := by
  refine ⟨?_, riemannZeta_ofReal_im_eq_zero σ⟩
  have hne1 : (σ : ℂ) ≠ 1 := by
    intro h
    exact h1.ne (Complex.ofReal_inj.mp h)
  have hem := riemannZeta_eq_eulerMaclaurin_second_order_of_re_gt_neg_one (N := 1) le_rfl
    (by simp; linarith) hne1
  let I : ℂ := ∫ u in Set.Ioi (1 : ℝ),
    (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 2)
  have hI_int_rpow : IntegrableOn (fun u : ℝ => u ^ (-σ - 2)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hI_meas : AEStronglyMeasurable
      (fun u : ℝ => (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 2))
      (volume.restrict (Set.Ioi 1)) := by
    have hb_meas : AEStronglyMeasurable (fun u : ℝ => (bernoulliKernel 2 u : ℂ))
        (volume.restrict (Set.Ioi 1)) :=
      (Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by decide))).aestronglyMeasurable
    have hpow_meas : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-(σ : ℂ) - 2))
        (volume.restrict (Set.Ioi 1)) := by
      have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-(σ : ℂ) - 2)) (Set.Ioi (1 : ℝ)) :=
        fun u hu => (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
          (Or.inl (by simpa using lt_trans zero_lt_one hu))).continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    exact hb_meas.mul hpow_meas
  have hI_int : IntegrableOn
      (fun u : ℝ => (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 2)) (Set.Ioi 1) := by
    refine (hI_int_rpow.const_mul (1 / 12 : ℝ)).mono' hI_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hupos : 0 < u := lt_trans zero_lt_one hu
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hupos, neg_re, sub_re, ofReal_re]
    have hre : (-σ - (2 : ℂ).re : ℝ) = -σ - 2 := by norm_num
    rw [hre]
    exact mul_le_mul_of_nonneg_right (bernoulliKernel_two_abs_le u)
      (Real.rpow_pos_of_pos hupos _).le
  have hI_norm : ‖I‖ ≤ (1 / 12 : ℝ) * (1 / (σ + 1)) := by
    calc
      ‖I‖ ≤ ∫ u in Set.Ioi (1 : ℝ),
            ‖(bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 2)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (1 : ℝ), (1 / 12 : ℝ) * u ^ (-σ - 2) := by
        refine setIntegral_mono_on hI_int.norm (hI_int_rpow.const_mul _) measurableSet_Ioi ?_
        intro u hu
        have hupos : 0 < u := lt_trans zero_lt_one hu
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos hupos, neg_re, sub_re, ofReal_re]
        have hre : (-σ - (2 : ℂ).re : ℝ) = -σ - 2 := by norm_num
        rw [hre]
        exact mul_le_mul_of_nonneg_right (bernoulliKernel_two_abs_le u)
          (Real.rpow_pos_of_pos hupos _).le
      _ = (1 / 12 : ℝ) * ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 2) := integral_const_mul _ _
      _ = (1 / 12 : ℝ) * (1 / (σ + 1)) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
        congr 1
        have hne : -σ - 2 + 1 ≠ 0 := by linarith
        field_simp [hne]
        ring
  have hrem_norm : ‖(σ : ℂ) * ((σ : ℂ) + 1) * I‖ ≤ σ / 12 := by
    have hprod : ‖(σ : ℂ) * ((σ : ℂ) + 1)‖ = σ * (σ + 1) := by
      have hcast : ((σ : ℂ) * ((σ : ℂ) + 1)) = ((σ * (σ + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [norm_mul, hprod]
    calc
      σ * (σ + 1) * ‖I‖ ≤ σ * (σ + 1) * ((1 / 12 : ℝ) * (1 / (σ + 1))) :=
        mul_le_mul_of_nonneg_left hI_norm (by positivity)
      _ = σ / 12 := by
        have hne : σ + 1 ≠ 0 := by linarith
        field_simp [hne]
  have hrem_re : -(((σ : ℂ) * ((σ : ℂ) + 1) * I).re) ≤ σ / 12 := by
    calc
      -(((σ : ℂ) * ((σ : ℂ) + 1) * I).re) = (-((σ : ℂ) * ((σ : ℂ) + 1) * I)).re := rfl
      _ ≤ ‖-((σ : ℂ) * ((σ : ℂ) + 1) * I)‖ := Complex.re_le_norm _
      _ = ‖(σ : ℂ) * ((σ : ℂ) + 1) * I‖ := norm_neg _
      _ ≤ σ / 12 := hrem_norm
  have hem_re : (riemannZeta (σ : ℂ)).re =
      1 - 1 / (1 - σ) - 1 / 2 + σ / 12 - ((σ : ℂ) * ((σ : ℂ) + 1) * I).re := by
    have h1 : (∑ n ∈ Finset.Icc (1 : ℕ) 1, (n : ℂ) ^ (-(σ : ℂ))) = 1 := by simp
    have h2 : ((1 : ℕ) : ℂ) ^ (1 - (σ : ℂ)) = 1 := by simp
    have h3 : ((1 : ℕ) : ℂ) ^ (-(σ : ℂ)) = 1 := by simp
    have h4 : ((1 : ℕ) : ℂ) ^ (-(σ : ℂ) - 1) = 1 := by simp
    have hI_eq : (∫ u in Set.Ioi ((1 : ℕ) : ℝ),
        (bernoulliKernel 2 u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - 2)) = I := by simp [I]
    have hinv : (1 : ℂ) / (1 - (σ : ℂ)) = ((1 / (1 - σ) : ℝ) : ℂ) := by
      push_cast; ring
    have hexp_re : ((1 : ℂ) - (1 : ℂ) / (1 - (σ : ℂ)) - 1 / 2 * 1 + 1 / 12 * (σ : ℂ) * 1).re =
        1 - 1 / (1 - σ) - 1 / 2 + σ / 12 := by
      rw [hinv]
      have hcast : ((1 : ℂ) - ((1 / (1 - σ) : ℝ) : ℂ) - 1 / 2 * 1 + 1 / 12 * (σ : ℂ) * 1) =
          (((1 - 1 / (1 - σ) - 1 / 2 + 1 / 12 * σ : ℝ) : ℂ)) := by
        push_cast; ring
      rw [hcast, Complex.ofReal_re]
      ring
    rw [hem, h1, h2, h3, h4, hI_eq, Complex.sub_re, hexp_re]
  have hinv_gt : 1 < 1 / (1 - σ) := by
    rw [one_lt_div (by linarith)]
    linarith
  linarith

/-- For any positive real `σ`, `riemannZeta (σ : ℂ) ≠ 0`. -/
theorem riemannZeta_ofReal_ne_zero_of_pos {σ : ℝ} (h0 : 0 < σ) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  rcases lt_or_ge σ 1 with hlt | hge
  · intro hzero
    have hneg := (riemannZeta_ofReal_neg_on_Ioo h0 hlt).1
    rw [hzero, Complex.zero_re] at hneg
    exact lt_irrefl _ hneg
  · exact riemannZeta_ne_zero_of_one_le_re_bridge (by simpa using hge)

/-- `riemannZeta₁ 1 = 1`. -/
theorem riemannZeta₁_one : riemannZeta₁ 1 = 1 := by
  have hcont : ContinuousAt riemannZeta₁ 1 := differentiable_riemannZeta₁.continuous.continuousAt
  have hev : (fun s : ℂ => (s - 1) * riemannZeta s) =ᶠ[𝓝[≠] (1 : ℂ)] riemannZeta₁ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    rw [riemannZeta_eq_inv_sub_mul hs]
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp [hne]
  have hlim1 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
    tendsto_sub_one_mul_riemannZeta
  have hlim2 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 (riemannZeta₁ 1)) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact tendsto_nhds_unique hlim2 hlim1

/-- For any positive real `σ`, `riemannZeta₁ (σ : ℂ) ≠ 0`. -/
theorem riemannZeta₁_ofReal_ne_zero_of_pos {σ : ℝ} (h0 : 0 < σ) :
    riemannZeta₁ (σ : ℂ) ≠ 0 := by
  by_cases h1 : σ = 1
  · subst h1
    simp
  · have hne1 : (σ : ℂ) ≠ 1 := fun h => h1 (Complex.ofReal_inj.mp h)
    intro hz
    have hzeta := riemannZeta_eq_inv_sub_mul hne1
    rw [hz, mul_zero] at hzeta
    exact riemannZeta_ofReal_ne_zero_of_pos h0 hzeta

private lemma norm_weierstrassPrimaryFactor_one_le (w : ℂ) :
    ‖weierstrassPrimaryFactor 1 w‖ ≤ Real.exp (2 * ‖w‖) := by
  have hdef : weierstrassPrimaryFactor 1 w = (1 - w) * Complex.exp w := by
    simp [weierstrassPrimaryFactor]
  rw [hdef, norm_mul, Complex.norm_exp]
  have h1 : ‖(1 : ℂ) - w‖ ≤ Real.exp ‖w‖ := by
    calc
      ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le 1 w
      _ = ‖w‖ + 1 := by simp [add_comm]
      _ ≤ Real.exp ‖w‖ := Real.add_one_le_exp ‖w‖
  have h2 : Real.exp w.re ≤ Real.exp ‖w‖ :=
    Real.exp_le_exp.mpr (Complex.re_le_norm w)
  calc
    ‖(1 : ℂ) - w‖ * Real.exp w.re ≤ Real.exp ‖w‖ * Real.exp ‖w‖ :=
      mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ‖w‖) := by rw [← Real.exp_add, two_mul]

private lemma norm_riemannZeta_ofReal_ge_one {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ ‖riemannZeta (x : ℂ)‖ := by
  have hx1 : 1 < (x : ℂ).re := by simpa using lt_of_lt_of_le one_lt_two hx
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hx1]
  have hsum_r : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    have hs := Real.summable_nat_rpow_inv.mpr (by linarith : 1 < x)
    have hshift : Summable (fun n : ℕ => ((↑(n + 1) : ℝ) ^ x)⁻¹) :=
      (summable_nat_add_iff 1).mpr hs
    refine hshift.congr ?_
    intro n
    simp [Nat.cast_add, Nat.cast_one]
  have hterm : ∀ n : ℕ, 1 / ((n : ℂ) + 1) ^ (x : ℂ) = (((((n : ℝ) + 1) ^ x)⁻¹ : ℝ) : ℂ) := by
    intro n
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hpow : ((n : ℂ) + 1) ^ (x : ℂ) = ((((n : ℝ) + 1) ^ x : ℝ) : ℂ) := by
      have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, ← Complex.ofReal_cpow hpos]
    rw [hpow, one_div, ← Complex.ofReal_inv]
  simp_rw [hterm]
  have htsum_re : (∑' n : ℕ, (((((n : ℝ) + 1) ^ x)⁻¹ : ℝ) : ℂ)).re =
      ∑' n : ℕ, (((n : ℝ) + 1) ^ x)⁻¹ := by
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have hge1 : 1 ≤ (∑' n : ℕ, (((((n : ℝ) + 1) ^ x)⁻¹ : ℝ) : ℂ)).re := by
    rw [htsum_re]
    have h0' : 1 = ((((0 : ℕ) : ℝ) + 1) ^ x)⁻¹ := by simp
    calc
      (1 : ℝ) = ((((0 : ℕ) : ℝ) + 1) ^ x)⁻¹ := h0'
      _ ≤ ∑' n : ℕ, (((n : ℝ) + 1) ^ x)⁻¹ :=
        hsum_r.le_tsum 0 (fun n _ => by positivity)
  exact hge1.trans (Complex.re_le_norm _)

private lemma norm_list_weierstrass_le (zs : List ℂ) (hzs : ∀ a ∈ zs, a ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x →
      ‖(zs.map (fun a => weierstrassPrimaryFactor 1 ((x : ℂ) / a))).prod‖ ≤ Real.exp (K * x) := by
  induction zs with
  | nil =>
      refine ⟨0, le_rfl, fun x _ => by simp⟩
  | cons a zs ih =>
      have ha : a ≠ 0 := hzs a (by simp)
      obtain ⟨K, hK0, hK⟩ := ih (fun b hb => hzs b (by simp [hb]))
      refine ⟨2 * ‖a‖⁻¹ + K, by positivity, fun x hx => ?_⟩
      simp only [List.map_cons, List.prod_cons, norm_mul]
      have h1 : ‖weierstrassPrimaryFactor 1 ((x : ℂ) / a)‖ ≤ Real.exp ((2 * ‖a‖⁻¹) * x) := by
        refine (norm_weierstrassPrimaryFactor_one_le ((x : ℂ) / a)).trans_eq ?_
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
        ring_nf
      have h2 := hK x hx
      calc
        ‖weierstrassPrimaryFactor 1 ((x : ℂ) / a)‖ *
            ‖(zs.map (fun a => weierstrassPrimaryFactor 1 ((x : ℂ) / a))).prod‖
            ≤ Real.exp ((2 * ‖a‖⁻¹) * x) * Real.exp (K * x) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp ((2 * ‖a‖⁻¹ + K) * x) := by
          rw [← Real.exp_add]
          ring_nf

private lemma norm_xi_ofReal_ge {x : ℝ} (hx : 4 ≤ x) :
    Real.exp ((x / 4) * Real.log (x / 2) - (1 / 2 + Real.log Real.pi / 2) * x) ≤ ‖xi (x : ℂ)‖ := by
  have hx_pos : 0 < x := by linarith
  have hre : 0 < (x : ℂ).re := by simpa using hx_pos
  have hne1 : (x : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hform := xi_eq_formula_of_re_pos hre hne1
  have hhalf_x : 1 ≤ ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1)‖ := by
    have hc : (1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1) = (((1 / 2 * x * (x - 1)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith
  have hpi_norm : ‖(Real.pi : ℂ) ^ (-(x : ℂ) / 2)‖ = Real.exp (-(x / 2) * Real.log Real.pi) := by
    have hpow : (Real.pi : ℂ) ^ (-(x : ℂ) / 2) = ((Real.pi ^ (-x / 2) : ℝ) : ℂ) := by
      have hc : (-(x : ℂ) / 2 : ℂ) = ((-x / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, ← Complex.ofReal_cpow Real.pi_pos.le]
    rw [hpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos _),
      Real.rpow_def_of_pos Real.pi_pos]
    ring_nf
  have hgamma_eq : Complex.Gamma ((x : ℂ) / 2) = (Real.Gamma (x / 2) : ℂ) := by
    have hc : ((x : ℂ) / 2 : ℂ) = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.Gamma_ofReal]
  have hgamma_ge : Real.exp ((x / 4) * Real.log (x / 2) - x / 2) ≤ ‖Complex.Gamma ((x : ℂ) / 2)‖ := by
    have hx2 : 0 < x / 2 := by linarith
    have hx2_ge : 2 ≤ x / 2 := by linarith
    have hst := real_gamma_eq_stirling hx2
    have hrem : 0 ≤ stirlingRemainderReal (x / 2) := stirlingRemainderReal_nonneg hx2
    have hgamma_pos : 0 < Real.Gamma (x / 2) := Real.Gamma_pos_of_pos hx2
    rw [hgamma_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgamma_pos, hst]
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.one_le_sqrt]
      linarith [Real.two_le_pi]
    have hrpow : Real.exp ((x / 4) * Real.log (x / 2)) ≤ (x / 2) ^ (x / 2 - 1 / 2) := by
      rw [mul_comm (x / 4) (Real.log (x / 2)), ← Real.rpow_def_of_pos hx2]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hexp_rem : Real.exp (-x / 2) ≤ Real.exp (-(x / 2) + stirlingRemainderReal (x / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      Real.exp ((x / 4) * Real.log (x / 2) - x / 2)
          = Real.exp ((x / 4) * Real.log (x / 2)) * Real.exp (-x / 2) := by
            rw [← Real.exp_add]; ring_nf
      _ = 1 * Real.exp ((x / 4) * Real.log (x / 2)) * Real.exp (-x / 2) := by ring
      _ ≤ Real.sqrt (2 * Real.pi) * (x / 2) ^ (x / 2 - 1 / 2) *
            Real.exp (-(x / 2) + stirlingRemainderReal (x / 2)) := by
            gcongr
  have hzeta_ge : 1 ≤ ‖riemannZeta (x : ℂ)‖ := norm_riemannZeta_ofReal_ge_one (by linarith)
  have hnorm_form : ‖xi (x : ℂ)‖ = ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1)‖ *
      ‖(Real.pi : ℂ) ^ (-(x : ℂ) / 2)‖ * ‖Complex.Gamma ((x : ℂ) / 2)‖ *
      ‖riemannZeta (x : ℂ)‖ := by
    rw [hform, norm_mul, norm_mul, norm_mul]
  rw [hnorm_form]
  calc
    Real.exp ((x / 4) * Real.log (x / 2) - (1 / 2 + Real.log Real.pi / 2) * x)
        = 1 * Real.exp (-(x / 2) * Real.log Real.pi) *
            Real.exp ((x / 4) * Real.log (x / 2) - x / 2) * 1 := by
          rw [mul_one, one_mul, ← Real.exp_add]
          ring_nf
    _ ≤ ‖(1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1)‖ * ‖(Real.pi : ℂ) ^ (-(x : ℂ) / 2)‖ *
          ‖Complex.Gamma ((x : ℂ) / 2)‖ * ‖riemannZeta (x : ℂ)‖ := by
          rw [hpi_norm]
          gcongr

/-- `riemannZeta` has infinitely many nontrivial zeros in the critical strip `0 < Re ρ < 1`. -/
theorem infinite_nontrivial_zeros_riemannZeta :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}.Infinite := by
  have hxi_ne : xi ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [xi_zero] at h0
    norm_num at h0
  rcases hadamard_factorization_genus_one differentiable_xi hxi_ne zero_le_one
      entireOrderLe_xi_one (by norm_num : (1 : ℝ) < 2) with
    ⟨zs, A, B, hzs_ne, _, hprod⟩ | ⟨a, A, B, ha_ne, ha_fin, ha_card, _, _⟩
  · exfalso
    obtain ⟨K, _, hK⟩ := norm_list_weierstrass_le zs hzs_ne
    set m : ℕ := analyticOrderNatAt xi 0
    set C₁ : ℝ := ‖A‖
    set C₂ : ℝ := (m : ℝ) + ‖B‖ + K
    have hupper : ∀ x : ℝ, 4 ≤ x → ‖xi (x : ℂ)‖ ≤ Real.exp (C₁ + C₂ * x) := by
      intro x hx
      have hx0 : 0 ≤ x := by linarith
      rw [hprod (x : ℂ), norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hx0, Complex.norm_exp]
      have hxm : x ^ m ≤ Real.exp ((m : ℝ) * x) := by
        have hxexp : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
        calc
          x ^ m ≤ (Real.exp x) ^ m := pow_le_pow_left₀ hx0 hxexp m
          _ = Real.exp ((m : ℝ) * x) := by rw [← Real.exp_nat_mul]
      have hAB : Real.exp (A + B * (x : ℂ)).re ≤ Real.exp (‖A‖ + ‖B‖ * x) := by
        refine Real.exp_le_exp.mpr ?_
        calc
          (A + B * (x : ℂ)).re ≤ ‖A + B * (x : ℂ)‖ := Complex.re_le_norm _
          _ ≤ ‖A‖ + ‖B * (x : ℂ)‖ := norm_add_le _ _
          _ = ‖A‖ + ‖B‖ * x := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
      have hprod_le := hK x hx0
      calc
        x ^ m * Real.exp (A + B * (x : ℂ)).re *
            ‖(zs.map (fun a => weierstrassPrimaryFactor 1 ((x : ℂ) / a))).prod‖
            ≤ Real.exp ((m : ℝ) * x) * Real.exp (‖A‖ + ‖B‖ * x) * Real.exp (K * x) := by
              gcongr
        _ = Real.exp (C₁ + C₂ * x) := by
          rw [← Real.exp_add, ← Real.exp_add]
          dsimp [C₁, C₂]
          ring_nf
    set M : ℝ := 4 * (|C₁| + |C₂| + 2 + |Real.log Real.pi|)
    set x₀ : ℝ := max 4 (2 * Real.exp M)
    have hx₀_4 : 4 ≤ x₀ := le_max_left _ _
    have hx₀_exp : 2 * Real.exp M ≤ x₀ := le_max_right _ _
    have hlog_ge : M ≤ Real.log (x₀ / 2) := by
      have hdiv : Real.exp M ≤ x₀ / 2 := by linarith
      simpa using Real.log_le_log (Real.exp_pos M) hdiv
    have hcomb : Real.exp ((x₀ / 4) * Real.log (x₀ / 2) - (1 / 2 + Real.log Real.pi / 2) * x₀) ≤
        Real.exp (C₁ + C₂ * x₀) :=
      (norm_xi_ofReal_ge hx₀_4).trans (hupper x₀ hx₀_4)
    have hlin := Real.exp_le_exp.mp hcomb
    have hmul_log : x₀ * (|C₁| + |C₂| + 2 + |Real.log Real.pi|) ≤ (x₀ / 4) * Real.log (x₀ / 2) := by
      have h1 : (x₀ / 4) * M ≤ (x₀ / 4) * Real.log (x₀ / 2) :=
        mul_le_mul_of_nonneg_left hlog_ge (by linarith)
      have h2 : x₀ * (|C₁| + |C₂| + 2 + |Real.log Real.pi|) = (x₀ / 4) * M := by
        dsimp [M]; ring
      linarith
    have hC1_x : C₁ ≤ |C₁| * x₀ := by nlinarith [le_abs_self C₁, abs_nonneg C₁]
    have hC2_x : C₂ * x₀ ≤ |C₂| * x₀ := mul_le_mul_of_nonneg_right (le_abs_self C₂) (by linarith)
    have hpi_x : (Real.log Real.pi / 2) * x₀ ≤ |Real.log Real.pi| * x₀ := by
      have hhalf : Real.log Real.pi / 2 ≤ |Real.log Real.pi| := by
        linarith [le_abs_self (Real.log Real.pi), abs_nonneg (Real.log Real.pi)]
      exact mul_le_mul_of_nonneg_right hhalf (by linarith)
    have hlin' : x₀ * (|C₁| + |C₂| + 2 + |Real.log Real.pi|) - (1 / 2 * x₀ + (Real.log Real.pi / 2) * x₀) ≤
        C₁ + C₂ * x₀ := by
      nlinarith
    linarith
  · have ha_mem : ∀ n : ℕ, a n ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by
      intro n
      have hfin_eq : ({k : ℕ | a k = a n}).Finite := by
        refine (ha_fin ‖a n‖).subset ?_
        intro k hk
        simp only [Set.mem_ofPred_eq] at hk ⊢
        rw [hk]
      have hne_eq : ({k : ℕ | a k = a n}).Nonempty := ⟨n, rfl⟩
      have hpos_card : 0 < ({k : ℕ | a k = a n}).ncard := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        rw [Set.ncard_eq_zero hfin_eq] at h0
        exact Set.eq_empty_iff_forall_notMem.mp h0 n rfl
      have hpos_ord : 0 < analyticOrderNatAt xi (a n) := by
        rw [← ha_card (a n) (ha_ne n)]
        exact hpos_card
      have hxi0 : xi (a n) = 0 := by
        by_contra hnz
        have hana : AnalyticAt ℂ xi (a n) := differentiable_xi.analyticAt (a n)
        have hord0 : analyticOrderAt xi (a n) = 0 := hana.analyticOrderAt_eq_zero.mpr hnz
        have hnat0 : analyticOrderNatAt xi (a n) = 0 := by
          simp [analyticOrderNatAt, hord0]
        omega
      exact xi_eq_zero_iff.mp hxi0
    intro hfin
    obtain ⟨R, hR⟩ := (hfin.image norm).bddAbove
    have hsub : (Set.univ : Set ℕ) ⊆ {n : ℕ | ‖a n‖ ≤ R} := by
      intro n _
      exact hR ⟨a n, ha_mem n, rfl⟩
    exact Set.infinite_univ ((ha_fin R).subset hsub)

/-- There exists at least one nontrivial zero `ρ₀` of `riemannZeta` with `1 / 2 ≤ ρ₀.re < 1`. -/
theorem exists_nontrivial_zero_re_ge_half :
    ∃ ρ₀ : ℂ, riemannZeta ρ₀ = 0 ∧ 1 / 2 ≤ ρ₀.re ∧ ρ₀.re < 1 := by
  obtain ⟨ρ₁, hρ₁⟩ := infinite_nontrivial_zeros_riemannZeta.nonempty
  rcases le_or_gt (1 / 2 : ℝ) ρ₁.re with hge | hlt
  · exact ⟨ρ₁, hρ₁.1, hge, hρ₁.2.2⟩
  · have hxi1 : xi (1 - ρ₁) = 0 := by
      rw [xi_one_sub]
      exact xi_eq_zero_iff.mpr hρ₁
    have hmem := xi_eq_zero_iff.mp hxi1
    exact ⟨1 - ρ₁, hmem.1, by simp; linarith, hmem.2.2⟩

/-- The supremum `Θ` of real parts of nontrivial zeros of `riemannZeta`. -/
def zetaSupRe : ℝ :=
  sSup {σ : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = σ}

private lemma zetaZeroReSet_nonempty :
    ({σ : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = σ}).Nonempty := by
  obtain ⟨ρ₀, hz, hge, hlt⟩ := exists_nontrivial_zero_re_ge_half
  exact ⟨ρ₀.re, ρ₀, hz, by linarith, hlt, rfl⟩

private lemma zetaZeroReSet_bddAbove :
    BddAbove {σ : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = σ} :=
  ⟨1, by rintro σ ⟨ρ, _, _, hlt, rfl⟩; exact hlt.le⟩

/-- `1 / 2 ≤ zetaSupRe`. -/
theorem half_le_zetaSupRe : 1 / 2 ≤ zetaSupRe := by
  obtain ⟨ρ₀, hz, hge, hlt⟩ := exists_nontrivial_zero_re_ge_half
  have hmem : ρ₀.re ∈ {σ : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = σ} :=
    ⟨ρ₀, hz, by linarith, hlt, rfl⟩
  exact hge.trans (le_csSup zetaZeroReSet_bddAbove hmem)

/-- `zetaSupRe ≤ 1`. -/
theorem zetaSupRe_le_one : zetaSupRe ≤ 1 :=
  csSup_le zetaZeroReSet_nonempty (by rintro σ ⟨ρ, _, _, hlt, rfl⟩; exact hlt.le)

/-- `zetaSupRe = 1 / 2` if and only if the Riemann Hypothesis holds. -/
theorem zetaSupRe_eq_half_iff_riemannHypothesis :
    zetaSupRe = 1 / 2 ↔ RiemannHypothesis := by
  constructor
  · intro hsup ρ hρ htriv hne1
    have hstrip := nontrivial_zero_re_mem_Ioo hρ htriv
    have hle₁ : ρ.re ≤ zetaSupRe :=
      le_csSup zetaZeroReSet_bddAbove ⟨ρ, hρ, hstrip.1, hstrip.2, rfl⟩
    have hxi : xi (1 - ρ) = 0 := by
      rw [xi_one_sub]
      exact xi_eq_zero_iff.mpr ⟨hρ, hstrip.1, hstrip.2⟩
    have hsym := xi_eq_zero_iff.mp hxi
    have hle₂ : (1 - ρ).re ≤ zetaSupRe :=
      le_csSup zetaZeroReSet_bddAbove ⟨1 - ρ, hsym.1, hsym.2.1, hsym.2.2, rfl⟩
    have h1 : ρ.re ≤ 1 / 2 := hle₁.trans_eq hsup
    have h2 : 1 - ρ.re ≤ 1 / 2 := by simpa using hle₂.trans_eq hsup
    linarith
  · intro hRH
    apply le_antisymm _ half_le_zetaSupRe
    refine csSup_le zetaZeroReSet_nonempty ?_
    rintro σ ⟨ρ, hρ, hpos, _, rfl⟩
    have htriv : ¬ ∃ n : ℕ, ρ = -2 * (↑n + 1) := by
      rintro ⟨n, rfl⟩
      have hneg : ((-2 * (↑n + 1 : ℂ))).re ≤ 0 := by
        norm_cast
        simp
        linarith
      linarith
    have hne1 : ρ ≠ 1 := by
      intro h1
      rw [h1] at hρ
      exact riemannZeta_ne_zero_of_one_le_re_bridge (by simp) hρ
    exact (hRH ρ hρ htriv hne1).le

end ZetaSignAndZeros

section PsiMertensOmega

/-- Elementary improper Mellin integral of `t ^ (-s - 1)` on `(c, ∞)` for `c > 0` and `Re s > 0`. -/
private lemma integral_Ioi_cpow {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Set.Ioi c) ∧
      ∫ t in Set.Ioi c, (t : ℂ) ^ (-s - 1) = (c : ℂ) ^ (-s) / s := by
  have hreal_int : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Set.Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioi c)) := by
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Set.Ioi c) :=
      fun t ht => (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using lt_trans hc ht))).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Set.Ioi c) := by
    refine hreal_int.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans hc ht
    simp only [Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
    exact le_rfl
  refine ⟨hint, ?_⟩
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    exact lt_irrefl 0 hs
  have hderiv : ∀ t ∈ Set.Ici c,
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ ((-s - 1) + 1) / ((-s - 1) + 1)) ((t : ℂ) ^ (-s - 1)) t :=
    fun t ht => hasDerivAt_ofReal_cpow_const' (lt_of_lt_of_le hc ht).ne'
      (by intro h; apply hsne; linear_combination -h)
  have htend : Tendsto (fun t : ℝ => (t : ℂ) ^ ((-s - 1) + 1) / ((-s - 1) + 1)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht_rpow : Tendsto (fun t : ℝ => (‖(-s - 1) + 1‖⁻¹ : ℝ) * t ^ (-s.re)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hs).const_mul (‖(-s - 1) + 1‖⁻¹ : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht_rpow
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hpow : (-s - 1) + 1 = -s := by ring
    rw [hpow, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht, neg_re, div_eq_inv_mul]
  have hid := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hpow : (-s - 1) + 1 = -s := by ring
  have h_simp : -((c : ℂ) ^ (-s) / -s) = (c : ℂ) ^ (-s) / s := by ring
  rw [hpow, zero_sub, h_simp] at hid
  exact hid

/-- Generic Mellin transform identity for partial sums `∑_{1 ≤ n ≤ t} f(n)` when `LSeries f s`
converges absolutely and `0 < s.re`. -/
private lemma mellin_partialSum_eq_LSeries_div {f : ℕ → ℝ} (_hf0 : f 0 = 0)
    {s : ℂ} (hs : 0 < s.re) (hf_sum : LSeriesSummable (fun n => (f n : ℂ)) s) :
    IntegrableOn (fun t : ℝ =>
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) ∧
      IntegrableOn (fun t : ℝ =>
        |(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n : ℝ)| * t ^ (-s.re - 1)) (Set.Ioi 1) ∧
      ∫ t in Set.Ioi (1 : ℝ),
          ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
        LSeries (fun n => (f n : ℂ)) s / s := by
  let S : ℝ → ℝ := fun t => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n
  let F : ℕ → ℝ → ℂ := fun n t =>
    Set.indicator (Set.Ici ((n + 1 : ℕ) : ℝ))
      (fun u => (f (n + 1) : ℂ) * (u : ℂ) ^ (-s - 1)) t
  have hF_int : ∀ n : ℕ, IntegrableOn (F n) (Set.Ioi 1) := by
    intro n
    have hcp := (integral_Ioi_cpow zero_lt_one hs).1.const_mul (f (n + 1) : ℂ)
    exact hcp.indicator measurableSet_Ici
  have hF_norm : ∀ n : ℕ, ∫ t in Set.Ioi (1 : ℝ), ‖F n t‖ =
      |f (n + 1)| * ((n + 1 : ℝ) ^ (-s.re)) / s.re := by
    intro n
    have hsplit : Set.Ioi (1 : ℝ) ∩ Set.Ici ((n + 1 : ℕ) : ℝ) =ᵐ[volume]
        Set.Ioi ((n + 1 : ℕ) : ℝ) := by
      by_cases hn0 : n = 0
      · subst hn0
        have : Set.Ioi (1 : ℝ) ∩ Set.Ici ((0 + 1 : ℕ) : ℝ) = Set.Ioi ((0 + 1 : ℕ) : ℝ) := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici, Nat.cast_one, zero_add]
          exact ⟨And.left, fun h => ⟨h, h.le⟩⟩
        rw [this]
      · have h1le : (1 : ℝ) < (n + 1 : ℝ) := by
          have : 1 ≤ n := Nat.pos_of_ne_zero hn0
          exact_mod_cast (by omega : 1 < n + 1)
        have : Set.Ioi (1 : ℝ) ∩ Set.Ici ((n + 1 : ℕ) : ℝ) = Set.Ici ((n + 1 : ℕ) : ℝ) := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici, Nat.cast_add, Nat.cast_one]
          exact ⟨And.right, fun h => ⟨lt_of_lt_of_le h1le h, h⟩⟩
        rw [this]
        exact Ioi_ae_eq_Ici.symm
    have hint_cp := (integral_Ioi_cpow (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))
      (by simpa using hs : 0 < ((s.re : ℂ)).re)).2
    have hrpow_eq : ∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), t ^ (-s.re - 1) =
        ((n + 1 : ℝ) ^ (-s.re)) / s.re := by
      have hre := congrArg Complex.re hint_cp
      have hc_l : (∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), (t : ℂ) ^ (-(s.re : ℂ) - 1)).re =
          ∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), t ^ (-s.re - 1) := by
        rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM
          (integral_Ioi_cpow (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))
            (by simpa using hs : 0 < ((s.re : ℂ)).re)).1]
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t ht
        have htpos : 0 < t := lt_trans (Nat.cast_pos.mpr (Nat.succ_pos n)) ht
        have hcpow : (t : ℂ) ^ (-(s.re : ℂ) - 1) = ((t ^ (-s.re - 1) : ℝ) : ℂ) := by
          have hc : (-(s.re : ℂ) - 1 : ℂ) = ((-s.re - 1 : ℝ) : ℂ) := by push_cast; ring
          rw [hc, ← Complex.ofReal_cpow htpos.le]
        change ((t : ℂ) ^ (-(s.re : ℂ) - 1)).re = t ^ (-s.re - 1)
        rw [hcpow, Complex.ofReal_re]
      have hc_r : (((((n + 1 : ℕ) : ℝ) : ℂ) ^ (-(s.re : ℂ)) / (s.re : ℂ))).re =
          ((n + 1 : ℝ) ^ (-s.re)) / s.re := by
        have hcpow : ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-(s.re : ℂ)) =
            ((((n + 1 : ℝ) ^ (-s.re)) : ℝ) : ℂ) := by
          have hc : (-(s.re : ℂ) : ℂ) = ((-s.re : ℝ) : ℂ) := by push_cast; ring
          rw [hc, ← Complex.ofReal_cpow (by positivity)]
          push_cast; rfl
        rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [← hc_l, hre, hc_r]
    calc
      ∫ t in Set.Ioi (1 : ℝ), ‖F n t‖
          = ∫ t in Set.Ioi (1 : ℝ),
              Set.indicator (Set.Ici ((n + 1 : ℕ) : ℝ))
                (fun u => |f (n + 1)| * u ^ (-s.re - 1)) t := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t ht
            have htpos : 0 < t := lt_trans zero_lt_one ht
            dsimp [F]

            by_cases hmem : t ∈ Set.Ici ((n + 1 : ℕ) : ℝ)
            · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
            · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, norm_zero]
      _ = ∫ t in Set.Ioi (1 : ℝ) ∩ Set.Ici ((n + 1 : ℕ) : ℝ), |f (n + 1)| * t ^ (-s.re - 1) := by
          rw [setIntegral_indicator measurableSet_Ici]
      _ = ∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), |f (n + 1)| * t ^ (-s.re - 1) :=
          setIntegral_congr_set hsplit
      _ = |f (n + 1)| * ∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), t ^ (-s.re - 1) :=
          integral_const_mul _ _
      _ = |f (n + 1)| * ((n + 1 : ℝ) ^ (-s.re)) / s.re := by
          rw [hrpow_eq]; ring
  have hF_sum : Summable (fun n : ℕ => ∫ t in Set.Ioi (1 : ℝ), ‖F n t‖) := by
    simp_rw [hF_norm]
    have hnorm := hf_sum.norm
    have hshift : Summable (fun n : ℕ => ‖LSeries.term (fun k => (f k : ℂ)) s (n + 1)‖) :=
      (summable_nat_add_iff 1).mpr hnorm
    refine (hshift.div_const s.re).congr ?_
    intro n
    have hterm : ‖LSeries.term (fun k => (f k : ℂ)) s (n + 1)‖ =
        |f (n + 1)| * ((n + 1 : ℝ) ^ (-s.re)) := by
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
      simp only [div_eq_mul_inv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
      rw [← Real.rpow_neg (by positivity)]
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [hterm]
  have hF_tsum_pt : ∀ t ∈ Set.Ioi (1 : ℝ),
      (∑' n : ℕ, F n t) = (S t : ℂ) * (t : ℂ) ^ (-s - 1) := by
    intro t ht
    have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
    have hfin : (∑' n : ℕ, F n t) = ∑ n ∈ Finset.range ⌊t⌋₊, F n t := by
      refine tsum_eq_sum ?_
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      dsimp [F]
      refine Set.indicator_of_notMem ?_ _
      intro hmem
      rw [Set.mem_Ici] at hmem
      have hle : n + 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr hmem
      omega
    rw [hfin]
    have hsum_eq : ∑ n ∈ Finset.range ⌊t⌋₊, F n t =
        ∑ n ∈ Finset.range ⌊t⌋₊, (f (n + 1) : ℂ) * (t : ℂ) ^ (-s - 1) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [Finset.mem_range] at hn
      have hle : ((n + 1 : ℕ) : ℝ) ≤ t := (Nat.le_floor_iff ht0).mp hn
      dsimp [F]
      exact Set.indicator_of_mem hle _
    rw [hsum_eq, ← Finset.sum_mul]
    congr 1
    dsimp [S]
    have hfl : 1 ≤ ⌊t⌋₊ := Nat.floor_pos.mpr ht.le
    have hcard : ∑ n ∈ Finset.range ⌊t⌋₊, (f (n + 1) : ℂ) =
        ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (f k : ℂ) := by
      refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_range] at hn
        exact Finset.mem_Icc.mpr ⟨Nat.succ_pos n, hn⟩
      · intro a₁ _ a₂ _ h
        exact Nat.succ.inj h
      · intro k hk
        rw [Finset.mem_Icc] at hk
        refine ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro n _
        rfl
    rw [hcard, Complex.ofReal_sum]
  have htsum_eq := integral_tsum_of_summable_integral_norm
    (fun n => (hF_int n).integrable) hF_sum
  have hmeas_S : AEStronglyMeasurable (fun t : ℝ => (S t : ℂ) * (t : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioi 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N)
        fun n _ => (hF_int n).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
    rw [← hF_tsum_pt t ht]
    refine tendsto_atTop_of_eventually_const (i₀ := ⌊t⌋₊ + 1) ?_
    intro N hN
    refine (tsum_eq_sum ?_).symm
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    dsimp [F]
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    rw [Set.mem_Ici] at hmem
    have hle : n + 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr hmem
    omega
  have hint_all : IntegrableOn (fun t : ℝ => (S t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
    refine ⟨hmeas_S, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have h_enorm_sum : ∑' n : ℕ, ∫⁻ t in Set.Ioi (1 : ℝ), ‖F n t‖ₑ ≠ ⊤ := by
      have h_eq : ∀ n : ℕ, ∫⁻ t in Set.Ioi (1 : ℝ), ‖F n t‖ₑ =
          ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), ‖F n t‖) := by
        intro n
        have h1 := (ofReal_integral_eq_lintegral_ofReal (hF_int n).norm
          (ae_of_all _ fun _ => norm_nonneg _)).symm
        refine (Eq.trans ?_ h1)
        refine lintegral_congr_ae ?_
        filter_upwards with t
        rw [← Real.eNorm_eq_ofReal (norm_nonneg _), eNorm_norm]
      have h_eq2 : ∀ n : ℕ, ∫⁻ t in Set.Ioi (1 : ℝ), ‖F n t‖ₑ =
          ‖∫ t in Set.Ioi (1 : ℝ), ‖F n t‖‖ₑ := by
        intro n
        rw [h_eq n, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp_rw [h_eq2]
      exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hF_sum.abs)
    have hlint_lt : (∫⁻ t in Set.Ioi (1 : ℝ), ∑' n : ℕ, ‖F n t‖ₑ) < ⊤ := by
      have hl := lintegral_tsum (fun n => (hF_int n).aestronglyMeasurable.eNorm)
      rw [hl]
      exact lt_top_iff_ne_top.mpr h_enorm_sum
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hlint_lt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
    have hfin : (S t : ℂ) * (t : ℂ) ^ (-s - 1) = ∑ n ∈ Finset.range ⌊t⌋₊, F n t := by
      rw [← hF_tsum_pt t ht]
      refine tsum_eq_sum ?_
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      dsimp [F]
      refine Set.indicator_of_notMem ?_ _
      intro hmem
      rw [Set.mem_Ici] at hmem
      have hle : n + 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr hmem
      omega
    rw [← Real.eNorm_eq_ofReal (norm_nonneg _), eNorm_norm, hfin]
    calc
      ‖∑ n ∈ Finset.range ⌊t⌋₊, F n t‖ₑ ≤ ∑ n ∈ Finset.range ⌊t⌋₊, ‖F n t‖ₑ :=
        eNorm_sum_le _ _
      _ ≤ ∑' n : ℕ, ‖F n t‖ₑ :=
        (CompleteLattice.summable (f := fun n => ‖F n t‖ₑ)).sum_le_tsum
          (Finset.range ⌊t⌋₊) (fun _ _ => bot_le)
  have hint_norm : IntegrableOn (fun t : ℝ => |S t| * t ^ (-s.re - 1)) (Set.Ioi 1) := by
    refine hint_all.norm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
  refine ⟨hint_all, hint_norm, ?_⟩
  have hint_eq : ∫ t in Set.Ioi (1 : ℝ), (S t : ℂ) * (t : ℂ) ^ (-s - 1) =
      ∫ t in Set.Ioi (1 : ℝ), ∑' n : ℕ, F n t := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    exact (hF_tsum_pt t ht).symm
  rw [hint_eq, ← htsum_eq]
  have hF_val : ∀ n : ℕ, ∫ t in Set.Ioi (1 : ℝ), F n t =
      LSeries.term (fun k => (f k : ℂ)) s (n + 1) / s := by
    intro n
    have hae : Set.Ioi (1 : ℝ) ∩ Set.Ici ((n + 1 : ℕ) : ℝ) =ᵐ[volume]
        Set.Ioi ((n + 1 : ℕ) : ℝ) := by
      by_cases hn0 : n = 0
      · subst hn0
        have : Set.Ioi (1 : ℝ) ∩ Set.Ici ((0 + 1 : ℕ) : ℝ) = Set.Ioi ((0 + 1 : ℕ) : ℝ) := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici, Nat.cast_one, zero_add]
          exact ⟨And.left, fun h => ⟨h, h.le⟩⟩
        rw [this]
      · have h1le : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
          have : 1 ≤ n := Nat.pos_of_ne_zero hn0
          exact_mod_cast (by omega : 1 < n + 1)
        have : Set.Ioi (1 : ℝ) ∩ Set.Ici ((n + 1 : ℕ) : ℝ) = Set.Ici ((n + 1 : ℕ) : ℝ) := by
          ext t
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨lt_of_lt_of_le h1le h, h⟩⟩
        rw [this]
        exact Ioi_ae_eq_Ici.symm
    have hint_cp := (integral_Ioi_cpow (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hs).2
    have hcast_eq : ((((n + 1 : ℕ) : ℝ) : ℂ)) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
    calc
      ∫ t in Set.Ioi (1 : ℝ), F n t
          = ∫ t in Set.Ioi (1 : ℝ) ∩ Set.Ici ((n + 1 : ℕ) : ℝ),
              (f (n + 1) : ℂ) * (t : ℂ) ^ (-s - 1) := by
            dsimp [F]
            rw [setIntegral_indicator measurableSet_Ici]
      _ = ∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), (f (n + 1) : ℂ) * (t : ℂ) ^ (-s - 1) :=
          setIntegral_congr_set hae
      _ = (f (n + 1) : ℂ) * ∫ t in Set.Ioi ((n + 1 : ℕ) : ℝ), (t : ℂ) ^ (-s - 1) :=
          integral_const_mul _ _
      _ = (f (n + 1) : ℂ) * (((n + 1 : ℕ) : ℂ) ^ (-s) / s) := by rw [hint_cp, hcast_eq]
      _ = LSeries.term (fun k => (f k : ℂ)) s (n + 1) / s := by
          rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
            div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
            ← Complex.cpow_neg (((n + 1 : ℕ) : ℂ))]
          push_cast
          ring
  simp_rw [hF_val, div_eq_mul_inv, tsum_mul_right]
  have hsum_ls : Summable (fun k : ℕ => LSeries.term (fun m => (f m : ℂ)) s k) := hf_sum
  have htsum_shift : LSeries (fun m => (f m : ℂ)) s =
      ∑' n : ℕ, LSeries.term (fun m => (f m : ℂ)) s (n + 1) := by
    rw [LSeries, hsum_ls.tsum_eq_zero_add]
    simp [LSeries.term_zero]
  rw [← htsum_shift]

/-- Holomorphy on all of `ℂ` of the truncated Mellin transform `∫ t in Ioc a b, g t * t^(-z-1)`
for a measurable bounded function `g` on `Ioc a b` (`0 < a ≤ b`). -/
private lemma differentiable_mellin_Ioc {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    {g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    {B : ℝ} (hg_bdd : ∀ t ∈ Set.Ioc a b, |g t| ≤ B) :
    Differentiable ℂ (fun z : ℂ => ∫ t in Set.Ioc a b, (g t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
  let B₀ : ℝ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right B 0
  have hg_bdd₀ : ∀ t ∈ Set.Ioc a b, |g t| ≤ B₀ := fun t ht => (hg_bdd t ht).trans (le_max_left B 0)
  have hIoc_fin : volume (Set.Ioc a b) < ⊤ := measure_Ioc_lt_top
  intro z
  have hcont_pow : ContinuousOn (fun t : ℝ => t ^ (-(z.re + 1) - 1)) (Set.Icc a b) :=
    fun t ht => (Real.continuousAt_rpow_const t _
      (Or.inl (lt_of_lt_of_le ha ht.1).ne')).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_pow
  have hcont_pow2 : ContinuousOn (fun t : ℝ => t ^ (-(z.re - 1) - 1)) (Set.Icc a b) :=
    fun t ht => (Real.continuousAt_rpow_const t _
      (Or.inl (lt_of_lt_of_le ha ht.1).ne')).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_pow2
  have hcont_log : ContinuousOn (fun t : ℝ => |Real.log t|) (Set.Icc a b) :=
    ContinuousOn.abs (Real.continuousOn_log.mono (fun t ht => (lt_of_lt_of_le ha ht.1).ne'))
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_log
  set C := max C₁ C₂
  have hmeas_F : ∀ w : ℂ, AEStronglyMeasurable
      (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-w - 1)) (volume.restrict (Set.Ioc a b)) := by
    intro w
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-w - 1)) (Set.Ioc a b) :=
      fun t ht => (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using lt_trans ha ht.1))).continuousWithinAt
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas).mul
      (hcont.aestronglyMeasurable measurableSet_Ioc)
  have hmeas_F' : AEStronglyMeasurable
      (fun t : ℝ => (g t : ℂ) * (-Real.log t : ℂ) * (t : ℂ) ^ (-z - 1))
      (volume.restrict (Set.Ioc a b)) := by
    have hcont : ContinuousOn (fun t : ℝ => (-Real.log t : ℂ) * (t : ℂ) ^ (-z - 1))
        (Set.Ioc a b) := by
      intro t ht
      have htpos : 0 < t := lt_trans ha ht.1
      exact ((Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log htpos.ne').neg).mul
        (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
          (Or.inl (by simpa using htpos)))).continuousWithinAt
    have h1 := (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas).mul
      (hcont.aestronglyMeasurable measurableSet_Ioc)
    refine h1.congr ?_
    filter_upwards with t
    simp [mul_assoc]
  have hint_z : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioc a b) := by
    refine ((integrableOn_const (C := C * B₀) (hs := hIoc_fin.ne)).mono' (hmeas_F z) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := lt_trans ha ht.1
    have hpow : t ^ (-z.re - 1) ≤ C := by
      by_cases h1 : 1 ≤ t
      · calc
          t ^ (-z.re - 1) ≤ t ^ (-(z.re - 1) - 1) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ ≤ ‖t ^ (-(z.re - 1) - 1)‖ := le_abs_self _
          _ ≤ C₂ := hC₂ t (Set.Ioc_subset_Icc_self ht)
          _ ≤ C := le_max_right _ _
      · calc
          t ^ (-z.re - 1) ≤ t ^ (-(z.re + 1) - 1) :=
            Real.rpow_le_rpow_of_exponent_ge htpos (le_of_not_ge h1) (by linarith)
          _ ≤ ‖t ^ (-(z.re + 1) - 1)‖ := le_abs_self _
          _ ≤ C₁ := hC₁ t (Set.Ioc_subset_Icc_self ht)
          _ ≤ C := le_max_left _ _
    have hC0 : 0 ≤ C := (Real.rpow_pos_of_pos htpos _).le.trans hpow
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
    calc
      |g t| * t ^ (-z.re - 1) ≤ B₀ * C := mul_le_mul (hg_bdd₀ t ht) hpow (Real.rpow_pos_of_pos htpos _).le hB₀
      _ = C * B₀ := mul_comm _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t => (g t : ℂ) * (t : ℂ) ^ (-w - 1))
    (F' := fun w t => (g t : ℂ) * (-Real.log t : ℂ) * (t : ℂ) ^ (-w - 1))
    (bound := fun _ => (L * C) * B₀)
    (x₀ := z) (Metric.ball_mem_nhds z zero_lt_one) ?_ hint_z.integrable hmeas_F' ?_ ?_ ?_).2.differentiableAt
  · filter_upwards [Metric.ball_mem_nhds z zero_lt_one] with w _
    exact hmeas_F w
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w hw
    have htpos : 0 < t := lt_trans ha ht.1
    have hball : ‖w - z‖ < 1 := by
      rw [← Complex.dist_eq]
      exact Metric.mem_ball.mp hw
    have hw_re : z.re - 1 < w.re ∧ w.re < z.re + 1 := by
      have hre : |w.re - z.re| < 1 := (Complex.abs_re_le_norm (w - z)).trans_lt hball
      exact ⟨by linarith [(abs_lt.mp hre).1], by linarith [(abs_lt.mp hre).2]⟩
    have hpow : t ^ (-w.re - 1) ≤ C := by
      by_cases h1 : 1 ≤ t
      · calc
          t ^ (-w.re - 1) ≤ t ^ (-(z.re - 1) - 1) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ ≤ ‖t ^ (-(z.re - 1) - 1)‖ := le_abs_self _
          _ ≤ C₂ := hC₂ t (Set.Ioc_subset_Icc_self ht)
          _ ≤ C := le_max_right _ _
      · calc
          t ^ (-w.re - 1) ≤ t ^ (-(z.re + 1) - 1) :=
            Real.rpow_le_rpow_of_exponent_ge htpos (le_of_not_ge h1) (by linarith)
          _ ≤ ‖t ^ (-(z.re + 1) - 1)‖ := le_abs_self _
          _ ≤ C₁ := hC₁ t (Set.Ioc_subset_Icc_self ht)
          _ ≤ C := le_max_left _ _
    have hlogt : |Real.log t| ≤ L := by
      have := hL t (Set.Ioc_subset_Icc_self ht)
      simpa using this
    have hL0 : 0 ≤ L := (abs_nonneg _).trans hlogt
    have hC0 : 0 ≤ C := (Real.rpow_pos_of_pos htpos _).le.trans hpow
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re]
    calc
      |g t| * |Real.log t| * t ^ (-w.re - 1) ≤ B₀ * L * C := by gcongr; exact hg_bdd₀ t ht
      _ = (L * C) * B₀ := by ring
  · exact integrableOn_const (hs := hIoc_fin.ne)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w _
    have htpos : 0 < t := lt_trans ha ht.1
    have hcpow : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (-w - 1))
        ((t : ℂ) ^ (-w - 1) * (-Complex.log (t : ℂ))) w := by
      have hlin : HasDerivAt (fun w : ℂ => -w - 1) (-1) w :=
        (hasDerivAt_id w).neg.sub_const 1
      convert (HasDerivAt.const_cpow (c := (t : ℂ)) hlin
        (Or.inl (Complex.ofReal_ne_zero.mpr htpos.ne'))) using 1
      ring
    have hlogc : Complex.log (t : ℂ) = (Real.log t : ℂ) := (Complex.ofReal_log htpos.le).symm
    have hderiv := hcpow.const_mul (g t : ℂ)
    have heq : (g t : ℂ) * ((t : ℂ) ^ (-w - 1) * -Complex.log (t : ℂ)) =
        (g t : ℂ) * (-Real.log t : ℂ) * (t : ℂ) ^ (-w - 1) := by
      rw [hlogc]
      ring
    rwa [heq] at hderiv

/-- Mellin transform of `t ^ α` on `(1, ∞)` for `α < Re s`. -/
private lemma integral_Ioi_one_rpow_mul_cpow {α : ℝ} {s : ℂ} (hs : α < s.re) :
    IntegrableOn (fun t : ℝ => (t ^ α : ℝ) * t ^ (-s.re - 1)) (Set.Ioi 1) ∧
      ∫ t in Set.Ioi (1 : ℝ), ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) = 1 / (s - α) := by
  have hsub_re : 0 < (s - (α : ℂ)).re := by simp; linarith
  obtain ⟨hint_c, hid_c⟩ := integral_Ioi_cpow zero_lt_one hsub_re
  have heq : ∀ t ∈ Set.Ioi (1 : ℝ),
      ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) = (t : ℂ) ^ (-(s - (α : ℂ)) - 1) := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    rw [Complex.ofReal_cpow htpos.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr htpos.ne')]
    congr 1
    ring
  have hint_r : IntegrableOn (fun t : ℝ => (t ^ α : ℝ) * t ^ (-s.re - 1)) (Set.Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by linarith : α - s.re - 1 < -1) zero_lt_one).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    dsimp only
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  refine ⟨hint_r, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, hid_c]
  simp

private lemma deriv_riemannZeta₁_eq {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev : riemannZeta₁ =ᶠ[𝓝 s] fun z : ℂ => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    rw [riemannZeta_eq_inv_sub_mul hz]
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    field_simp [hne]
  rw [hev.deriv_eq]
  have hdiff : DifferentiableAt ℂ riemannZeta s :=
    (analyticOn_riemannZeta s hs).differentiableAt
  have hderiv : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul hdiff.hasDerivAt
  simpa using hderiv.deriv

private lemma riemannZeta₁_factor_at_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (_hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    ∃ (m : ℕ) (φ : ℂ → ℂ), 1 ≤ m ∧
      (∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ φ z) ∧
      ContinuousAt (deriv φ) ρ ∧ ContinuousAt φ ρ ∧ φ ρ ≠ 0 ∧
      (∀ z : ℂ, riemannZeta₁ z = (z - ρ) ^ m * φ z) := by
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hre1
    exact lt_irrefl 1 hre1
  have hz1_0 : riemannZeta₁ ρ = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hne1
    rw [hρ] at h
    have hsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hne1
    calc
      riemannZeta₁ ρ = (ρ - 1) * ((ρ - 1)⁻¹ * riemannZeta₁ ρ) := by field_simp [hsub]
      _ = (ρ - 1) * 0 := by rw [← h]
      _ = 0 := mul_zero _
  have hana : AnalyticAt ℂ riemannZeta₁ ρ := differentiable_riemannZeta₁.analyticAt ρ
  obtain ⟨p, hp⟩ := hana
  have hp_ne : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp
    have hev0 : riemannZeta₁ =ᶠ[𝓝 ρ] 0 := by
      filter_upwards [hp.eventually_eq_zero] with z hz
      exact hz
    have h1 := (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_univ (Set.mem_univ ρ) hev0 (Set.mem_univ 1)
    norm_num [Complex.ext_iff] at h1
  let m : ℕ := p.order
  let φ : ℂ → ℂ := (Function.swap dslope ρ)^[m] riemannZeta₁
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hne0 := hp.iterate_dslope_fslope_ne_zero hp_ne
    dsimp [m] at hm0'
    rw [hm0'] at hne0
    exact hne0 hz1_0
  have hana_φ : AnalyticAt ℂ φ ρ := (hp.has_fpower_series_iterate_dslope_fslope m).analyticAt
  have hdiff_ev : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ φ z :=
    hana_φ.eventually_analyticAt.mono fun _ h => h.differentiableAt
  have hd_cont : ContinuousAt (deriv φ) ρ := hana_φ.deriv.continuousAt
  refine ⟨m, φ, hm_pos, hdiff_ev, hd_cont, hana_φ.continuousAt,
    hp.iterate_dslope_fslope_ne_zero hp_ne, fun z => ?_⟩
  simpa [smul_eq_mul, m, φ] using hp.eq_pow_order_mul_iterate_dslope z

private lemma landau_mellin_extend_by_zeta₁ {X₀ β σ₁ : ℝ}
    (hX₀ : 1 ≤ X₀) (hβ : 0 < β) (hσ₁ : β < σ₁)
    {g : ℝ → ℝ} (hg_nonneg : ∀ t ∈ Set.Ioi X₀, 0 ≤ g t)
    (hg_int₁ : IntegrableOn (fun t : ℝ => g t * t ^ (-σ₁ - 1)) (Set.Ioi X₀))
    {H : ℂ → ℂ} (hH_diff : DifferentiableOn ℂ H {z : ℂ | β < z.re})
    (hH_eq : ∀ z : ℂ, σ₁ < z.re →
      IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) ∧
      z * riemannZeta₁ z * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) = H z) :
    (∀ σ : ℝ, β < σ → IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi X₀)) ∧
      (∀ z : ℂ, β < z.re →
        IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) ∧
        z * riemannZeta₁ z * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) = H z) := by
  have hX₀_pos : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  let S : Set ℝ := {σ : ℝ | β < σ ∧ IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi X₀)}
  have hS_ne : S.Nonempty := ⟨σ₁, hσ₁, hg_int₁⟩
  have hS_bdd : BddBelow S := ⟨β, fun _ h => h.1.le⟩
  set σ₀ : ℝ := sInf S
  have hβ_le_σ₀ : β ≤ σ₀ := le_csInf hS_ne (fun _ h => h.1.le)
  have hg_tail_int : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi X₀) := by
    intro σ hσ
    obtain ⟨σ', hσ'mem, hσ'lt⟩ := exists_lt_of_csInf_lt hS_ne hσ
    have hpow_meas : AEStronglyMeasurable (fun t : ℝ => t ^ (σ' - σ))
        (volume.restrict (Set.Ioi X₀)) := by
      have hcont : ContinuousOn (fun t : ℝ => t ^ (σ' - σ)) (Set.Ioi X₀) :=
        fun t ht => (Real.continuousAt_rpow_const t _ (Or.inl (lt_trans hX₀_pos ht).ne')).continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    have hmeas : AEStronglyMeasurable (fun t : ℝ => g t * t ^ (-σ - 1))
        (volume.restrict (Set.Ioi X₀)) := by
      refine (hσ'mem.2.aestronglyMeasurable.mul hpow_meas).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans hX₀_pos ht
      simp only [Pi.mul_apply]
      rw [mul_assoc, ← Real.rpow_add htpos]
      congr 2; ring
    refine hσ'mem.2.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans hX₀_pos ht
    have ht1 : 1 ≤ t := hX₀.trans ht.le
    have hnn1 : 0 ≤ g t * t ^ (-σ - 1) := mul_nonneg (hg_nonneg t ht) (Real.rpow_pos_of_pos htpos _).le
    have hnn2 : 0 ≤ g t * t ^ (-σ' - 1) := mul_nonneg (hg_nonneg t ht) (Real.rpow_pos_of_pos htpos _).le
    simp only [Real.norm_eq_abs, abs_of_nonneg hnn1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (hg_nonneg t ht)
  have heq_above_σ₀ : ∀ z : ℂ, σ₀ < z.re →
      z * riemannZeta₁ z * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) = H z := by
    let U : Set ℂ := {z : ℂ | σ₀ < z.re}
    have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hU_preconn : IsPreconnected U := by
      refine Convex.isPreconnected ?_
      intro x hx y hy a b ha hb hab
      rw [Set.mem_ofPred_eq] at hx hy
      change σ₀ < (a • x + b • y).re
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have hsum : a * σ₀ + b * σ₀ = σ₀ := by rw [← add_mul, hab, one_mul]
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
      · rcases eq_or_lt_of_le hb with rfl | hb_pos
        · have ha1 : a = 1 := by linarith
          rw [ha1]; linarith
        · have h1 : a * σ₀ < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
          have h2 : b * σ₀ < b * y.re := mul_lt_mul_of_pos_left hy hb_pos
          linarith
    have hM_diff : DifferentiableOn ℂ (mellinIntegralK g X₀ 0) U :=
      differentiableOn_mellinIntegral hX₀_pos hg_nonneg hg_tail_int
    have hG_diff : DifferentiableOn ℂ (fun z => z * riemannZeta₁ z * mellinIntegralK g X₀ 0 z) U :=
      ((differentiable_id.differentiableOn.mul differentiable_riemannZeta₁.differentiableOn).mul
        hM_diff)
    have hH_sub : DifferentiableOn ℂ H U :=
      hH_diff.mono (fun _ hz => hβ_le_σ₀.trans_lt hz)
    have hG_ana : AnalyticOnNhd ℂ (fun z => z * riemannZeta₁ z * mellinIntegralK g X₀ 0 z) U :=
      hG_diff.analyticOnNhd hU_open
    have hH_ana : AnalyticOnNhd ℂ H U := hH_sub.analyticOnNhd hU_open
    set p : ℂ := ((max σ₀ σ₁ + 1 : ℝ) : ℂ)
    have hp_mem : p ∈ U := by
      change σ₀ < (max σ₀ σ₁ + 1)
      linarith [le_max_left σ₀ σ₁]
    have hU₁_open : IsOpen {z : ℂ | σ₁ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hp_U₁ : p ∈ {z : ℂ | σ₁ < z.re} := by
      change σ₁ < (max σ₀ σ₁ + 1)
      linarith [le_max_right σ₀ σ₁]
    have hev : (fun z => z * riemannZeta₁ z * mellinIntegralK g X₀ 0 z) =ᶠ[𝓝 p] H := by
      filter_upwards [hU₁_open.mem_nhds hp_U₁] with z hz
      have hhz := (hH_eq z hz).2
      have hm_eq : mellinIntegralK g X₀ 0 z =
          ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
        simp [mellinIntegralK, mellinKernel]
      rwa [hm_eq]
    have heq := hG_ana.eqOn_of_preconnected_of_eventuallyEq hH_ana hU_preconn hp_mem hev
    intro z hz
    have hm_eq : mellinIntegralK g X₀ 0 z =
        ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
      simp [mellinIntegralK, mellinKernel]
    simpa [hm_eq] using heq hz
  have hσ₀_eq_β : σ₀ = β := by
    by_contra hne
    have hβ_lt_σ₀ : β < σ₀ := lt_of_le_of_ne hβ_le_σ₀ (Ne.symm hne)
    have hσ₀_pos : 0 < σ₀ := hβ.trans hβ_lt_σ₀
    have hzeta_ne : riemannZeta₁ (σ₀ : ℂ) ≠ 0 := riemannZeta₁_ofReal_ne_zero_of_pos hσ₀_pos
    obtain ⟨δ, hδ_pos, hδ_ne⟩ := Metric.eventually_nhds_iff.mp
      ((differentiable_riemannZeta₁.continuous.continuousAt.eventually_ne hzeta_ne))
    set r : ℝ := min δ (σ₀ - β)
    have hr : 0 < r := lt_min hδ_pos (sub_pos.mpr hβ_lt_σ₀)
    have hr_re : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, β < z.re ∧ 0 < z.re ∧ z ≠ 0 ∧ riemannZeta₁ z ≠ 0 := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hre : |z.re - σ₀| < r := (Complex.abs_re_le_norm (z - σ₀)).trans_lt hz
      have hzr : β < z.re := by
        have h1 : σ₀ - r < z.re := by linarith [(abs_lt.mp hre).1]
        linarith [min_le_right δ (σ₀ - β)]
      have hz0_pos : 0 < z.re := hβ.trans hzr
      have hz_ne0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz0_pos; exact lt_irrefl 0 hz0_pos
      have hzd : dist z (σ₀ : ℂ) < δ :=
        lt_of_lt_of_le (by rwa [Complex.dist_eq]) (min_le_left δ (σ₀ - β))
      exact ⟨hzr, hz0_pos, hz_ne0, hδ_ne hzd⟩
    let F : ℂ → ℂ := fun z => H z / (z * riemannZeta₁ z)
    have hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r) := by
      intro z hz
      have hinfo := hr_re z hz
      have hH_at : DifferentiableAt ℂ H z :=
        (hH_diff z hinfo.1).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hinfo.1)
      have hden_at : DifferentiableAt ℂ (fun w : ℂ => w * riemannZeta₁ w) z :=
        differentiableAt_id.mul (differentiable_riemannZeta₁ z)
      exact (hH_at.div hden_at (mul_ne_zero hinfo.2.2.1 hinfo.2.2.2)).differentiableWithinAt
    have hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
        F z = ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
      intro z hz hzr
      have hinfo := hr_re z hz
      have hmul := heq_above_σ₀ z hzr
      dsimp [F]
      rw [← hmul]
      have hden : z * riemannZeta₁ z ≠ 0 := mul_ne_zero hinfo.2.2.1 hinfo.2.2.2
      exact mul_div_cancel_left₀ _ hden
    have hlandau := (landau_mellin_integral hX₀_pos hg_nonneg hr hg_tail_int hF_diff hF_eq).1
    set σ₂ : ℝ := σ₀ - r / 12
    have hσ₂_gt_sub : σ₀ - r / 6 < σ₂ := by dsimp [σ₂]; linarith
    have hσ₂_gt_β : β < σ₂ := by dsimp [σ₂]; linarith [min_le_right δ (σ₀ - β)]
    have hmem : σ₂ ∈ S := ⟨hσ₂_gt_β, hlandau σ₂ hσ₂_gt_sub⟩
    have hle := csInf_le hS_bdd hmem
    dsimp [σ₂] at hle
    linarith
  have hg_all_real : ∀ σ : ℝ, β < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi X₀) := by
    intro σ hσ
    rw [← hσ₀_eq_β] at hσ
    exact hg_tail_int σ hσ
  refine ⟨hg_all_real, fun z hz => ⟨?_, ?_⟩⟩
  · have hm := integrableOn_mellinKernel hX₀_pos hg_nonneg hg_all_real 0 hz
    refine hm.congr_fun ?_ measurableSet_Ioi
    intro t _
    simp [mellinKernel]
  · rw [← hσ₀_eq_β] at hz
    exact heq_above_σ₀ z hz

private lemma riemannZeta₁_logDeriv_near_zero {ρ : ℂ} {m : ℕ} {φ : ℂ → ℂ}
    (hm_ge : 1 ≤ m) (hρ_ne0 : ρ ≠ 0)
    (hφ_diff_ev : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ φ z)
    (hφ_cont : ContinuousAt φ ρ) (hφ_ne : φ ρ ≠ 0)
    (hφ_fac : ∀ z : ℂ, riemannZeta₁ z = (z - ρ) ^ m * φ z)
    (h_lin : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ρ)) :
    ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
      φ (ρ + ε) ≠ 0 ∧ riemannZeta₁ (ρ + ε) ≠ 0 ∧ (ρ + (ε : ℂ) ≠ 0) ∧
      (ε : ℂ) * (deriv riemannZeta₁ (ρ + ε) / riemannZeta₁ (ρ + ε)) =
        (m : ℂ) + (ε : ℂ) * (deriv φ (ρ + ε) / φ (ρ + ε)) := by
  have hφ_ev_ne : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), φ (ρ + ε) ≠ 0 :=
    (hφ_cont.tendsto.comp h_lin).eventually_ne hφ_ne
  have h_diff : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), DifferentiableAt ℂ φ (ρ + ε) :=
    h_lin.eventually hφ_diff_ev
  have hρ_ev_ne0 : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), ρ + (ε : ℂ) ≠ 0 :=
    h_lin.eventually_ne hρ_ne0
  filter_upwards [self_mem_nhdsWithin, hφ_ev_ne, h_diff, hρ_ev_ne0] with ε hε hφz hdiffz hzne0
  rw [Set.mem_Ioi] at hε
  have hε_ne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hz1_ne : riemannZeta₁ (ρ + ε) ≠ 0 := by
    rw [hφ_fac (ρ + ε)]
    exact mul_ne_zero (pow_ne_zero m (by rw [add_sub_cancel_left]; exact hε_ne)) hφz
  have hd_eq : HasDerivAt riemannZeta₁
      ((m : ℂ) * ((ρ + (ε : ℂ)) - ρ) ^ (m - 1) * φ (ρ + ε) +
        ((ρ + (ε : ℂ)) - ρ) ^ m * deriv φ (ρ + ε)) (ρ + ε) := by
    have hfn : riemannZeta₁ = fun z : ℂ => (z - ρ) ^ m * φ z := funext hφ_fac
    rw [hfn]
    have hpow : HasDerivAt (fun z : ℂ => (z - ρ) ^ m)
        ((m : ℂ) * ((ρ + (ε : ℂ)) - ρ) ^ (m - 1)) (ρ + ε) :=
      (((hasDerivAt_id (ρ + (ε : ℂ))).sub_const ρ).pow m).congr_deriv (mul_one _)
    exact hpow.mul hdiffz.hasDerivAt
  have hpow_split : (ε : ℂ) ^ m = (ε : ℂ) * (ε : ℂ) ^ (m - 1) := by
    cases m with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  refine ⟨hφz, hz1_ne, hzne0, ?_⟩
  rw [hd_eq.deriv, hφ_fac (ρ + ε)]
  simp only [add_sub_cancel_left]
  rw [hpow_split]
  field_simp [hε_ne, pow_ne_zero (m - 1) hε_ne, hφz]

private lemma psi_mellin_tail_H_eq
    {C sgn β X₀ : ℝ} (hX₀_ge1 : 1 ≤ X₀) (hre1 : β < 1)
    {g : ℝ → ℝ} (hg_def : ∀ t : ℝ, g t = C * t ^ β - sgn * (Chebyshev.psi t - t))
    (hpsi_mellin : ∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun t : ℝ => (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) ∧
        IntegrableOn (fun t : ℝ => |Chebyshev.psi t| * t ^ (-s.re - 1)) (Set.Ioi 1) ∧
        ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-s - 1) =
          (-deriv riemannZeta s / riemannZeta s) / s)
    (hg_int_sigma : ∀ {σ : ℝ}, 1 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi 1))
    {M_init H : ℂ → ℂ}
    (hM_init_def : ∀ z : ℂ, M_init z = ∫ t in Set.Ioc 1 X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1))
    (hH_def : ∀ z : ℂ, H z =
      z * riemannZeta₁ z * ((C : ℂ) / (z - β) - M_init z) +
        (sgn : ℂ) * (riemannZeta₁ z + deriv riemannZeta₁ z)) :
    ∀ z : ℂ, (1 : ℝ) < z.re →
      IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) ∧
      z * riemannZeta₁ z * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) = H z := by
  intro z hz
  have hIoi1_int : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) := by
    have hr_int := hg_int_sigma hz
    have hmeas : AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1))
        (volume.restrict (Set.Ioi 1)) := by
      have hg_m : AEStronglyMeasurable g (volume.restrict (Set.Ioi 1)) :=
        aestronglyMeasurable_of_integrableOn zero_lt_one (fun σ hσ => hg_int_sigma hσ)
      have hpow_m : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-z - 1))
          (volume.restrict (Set.Ioi 1)) :=
        (ContinuousOn.aestronglyMeasurable (fun t ht =>
          (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
            (Or.inl (by simpa using lt_trans zero_lt_one ht))).continuousWithinAt) measurableSet_Ioi)
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_m).mul hpow_m
    refine hr_int.norm.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re,
      abs_of_pos (Real.rpow_pos_of_pos htpos _)]
    exact le_rfl
  have htail_int : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) :=
    hIoi1_int.mono_set (Set.Ioi_subset_Ioi hX₀_ge1)
  refine ⟨htail_int, ?_⟩
  have hIoc_int : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioc 1 X₀) :=
    hIoi1_int.mono_set Set.Ioc_subset_Ioi_self
  have hIoi_split : Set.Ioi (1 : ℝ) = Set.Ioc 1 X₀ ∪ Set.Ioi X₀ := by
    ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    exact ⟨fun h => (le_or_gt t X₀).imp (fun hle => ⟨h, hle⟩) id,
      fun h => h.elim And.left (lt_of_le_of_lt hX₀_ge1)⟩
  have h_union : ∫ t in Set.Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (-z - 1) =
      M_init z + ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
    rw [hM_init_def z, hIoi_split]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc_int htail_int
  have h1_c := integral_Ioi_one_rpow_mul_cpow (α := β) (s := z) (hre1.trans hz)
  have h1_c_int : IntegrableOn (fun t : ℝ => ((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => ((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))
        (volume.restrict (Set.Ioi 1)) :=
      (ContinuousOn.aestronglyMeasurable (fun t ht =>
        ((Complex.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_rpow_const t β (Or.inl (lt_trans zero_lt_one ht).ne'))).mul
          (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
            (Or.inl (by simpa using lt_trans zero_lt_one ht)))).continuousWithinAt) measurableSet_Ioi)
    refine (h1_c.1.mono' hm ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re,
      abs_of_pos (Real.rpow_pos_of_pos htpos _)]
    exact le_rfl
  have h2_c := hpsi_mellin z hz
  have h3_c := integral_Ioi_one_rpow_mul_cpow (α := 1) (s := z) hz
  have h3_c_int : IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-z - 1))
        (volume.restrict (Set.Ioi 1)) :=
      (ContinuousOn.aestronglyMeasurable (fun t ht =>
        (Complex.continuous_ofReal.continuousAt.mul
          (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
            (Or.inl (by simpa using lt_trans zero_lt_one ht)))).continuousWithinAt) measurableSet_Ioi)
    refine (h3_c.1.mono' hm ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re,
      abs_of_pos htpos, Real.rpow_one]
    exact le_rfl
  have h3_c_val : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-z - 1) = 1 / (z - 1) := by
    simpa [Real.rpow_one] using h3_c.2
  have hIoi1_val : ∫ t in Set.Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (-z - 1) =
      (C : ℂ) / (z - β) - (sgn : ℂ) * ((-deriv riemannZeta z / riemannZeta z) / z - 1 / (z - 1)) := by
    have hfn : (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) =
        (fun t : ℝ => (C : ℂ) * (((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) -
          (sgn : ℂ) * ((Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-z - 1) - (t : ℂ) * (t : ℂ) ^ (-z - 1))) := by
      ext t; rw [hg_def t]; push_cast; ring
    have h1_mul : IntegrableOn (fun t : ℝ => (C : ℂ) * (((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))) (Set.Ioi 1) :=
      h1_c_int.const_mul (C : ℂ)
    have hdiff_int : IntegrableOn
        (fun t : ℝ => (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-z - 1) - (t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) :=
      h2_c.1.sub h3_c_int
    have h2_mul : IntegrableOn
        (fun t : ℝ => (sgn : ℂ) * ((Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-z - 1) - (t : ℂ) * (t : ℂ) ^ (-z - 1)))
        (Set.Ioi 1) := hdiff_int.const_mul (sgn : ℂ)
    rw [hfn, integral_sub h1_mul h2_mul, integral_const_mul, integral_const_mul,
      integral_sub h2_c.1 h3_c_int, h1_c.2, h2_c.2.2, h3_c_val]
    ring
  have htail_val : ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) =
      (C : ℂ) / (z - β) - M_init z -
        (sgn : ℂ) * ((-deriv riemannZeta z / riemannZeta z) / z - 1 / (z - 1)) := by
    linear_combination hIoi1_val - h_union
  have hzne1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz; linarith
  have hzne0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; linarith
  have hz_nz : riemannZeta z ≠ 0 := _root_.riemannZeta_ne_zero_of_one_lt_re hz
  have hderiv₁ := deriv_riemannZeta₁_eq hzne1
  have hz₁_eq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hzne1]
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hzne1
    field_simp [hsub]
  rw [htail_val, hH_def z, hz₁_eq, hderiv₁]
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hzne1
  field_simp [hzne0, hsub, hz_nz]
  ring

private lemma psi_sub_id_one_side {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    {C : ℝ} (hC : 0 < C) (hC_lt : C < 1 / ‖ρ‖)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hbound : ∀ᶠ t in atTop, sgn * (Chebyshev.psi t - t) ≤ C * t ^ ρ.re) :
    False := by
  rw [eventually_atTop] at hbound
  obtain ⟨X₁, hX₁⟩ := hbound
  set X₀ : ℝ := max X₁ 1
  have hX₀_ge1 : 1 ≤ X₀ := le_max_right _ _
  have hX₀_pos : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀_ge1
  have hX₀_bound : ∀ t : ℝ, X₀ ≤ t → sgn * (Chebyshev.psi t - t) ≤ C * t ^ ρ.re :=
    fun t ht => hX₁ t ((le_max_left _ _).trans ht)
  let β : ℝ := ρ.re
  let g : ℝ → ℝ := fun t => C * t ^ β - sgn * (Chebyshev.psi t - t)
  have hg_nonneg : ∀ t ∈ Set.Ioi X₀, 0 ≤ g t := by
    intro t ht
    dsimp [g]
    linarith [hX₀_bound t ht.le]
  have hpsi_sum : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    intro s hs
    exact LSeriesSummable_vonMangoldt_iff.mpr hs
  have hpsi_mellin : ∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun t : ℝ => (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) ∧
        IntegrableOn (fun t : ℝ => |Chebyshev.psi t| * t ^ (-s.re - 1)) (Set.Ioi 1) ∧
        ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-s - 1) =
          (-deriv riemannZeta s / riemannZeta s) / s := by
    intro s hs
    have hΛ0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
    have hm := mellin_partialSum_eq_LSeries_div hΛ0 (by linarith) (hpsi_sum s hs)
    have hpsi_eq : ∀ t : ℝ, (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)) =
        Chebyshev.psi t := fun t => (psi_eq_sum_Icc t).symm
    refine ⟨?_, ?_, ?_⟩
    · refine hm.1.congr_fun ?_ measurableSet_Ioi
      intro t _
      dsimp only
      rw [hpsi_eq t]
    · refine hm.2.1.congr_fun ?_ measurableSet_Ioi
      intro t _
      dsimp only
      rw [hpsi_eq t]
    · have hid := hm.2.2
      have hcongr : ∫ t in Set.Ioi (1 : ℝ),
          ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
          ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-s - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t _
        dsimp only
        rw [hpsi_eq t]
      rw [← hcongr, hid]
      have hls : LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := rfl
      rw [hls]
      simpa using congrArg (· / s) (LSeries_vonMangoldt_eq hs)
  have hg_int_sigma : ∀ {σ : ℝ}, 1 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi 1) := by
    intro σ hσ
    have h1 := (integral_Ioi_one_rpow_mul_cpow (α := β) (s := (σ : ℂ))
      (by simpa using hre1.trans hσ)).1.const_mul C
    have h2 := (hpsi_mellin (σ : ℂ) (by simpa using hσ)).2.1
    have h3 := (integral_Ioi_one_rpow_mul_cpow (α := 1) (s := (σ : ℂ))
      (by simpa using hσ)).1
    have h3' : IntegrableOn (fun t : ℝ => t * t ^ (-σ - 1)) (Set.Ioi 1) := by
      refine h3.congr_fun ?_ measurableSet_Ioi
      intro t _
      simp [Real.rpow_one]
    have hdom := h1.add ((h2.add h3').const_mul |sgn|)
    have hmeas : AEStronglyMeasurable (fun t : ℝ => g t * t ^ (-σ - 1))
        (volume.restrict (Set.Ioi 1)) := by
      have h1m := h1.aestronglyMeasurable
      have hpsim : AEStronglyMeasurable (fun t : ℝ => Chebyshev.psi t * t ^ (-σ - 1))
          (volume.restrict (Set.Ioi 1)) := by
        have hcm := (hpsi_mellin (σ : ℂ) (by simpa using hσ)).1.aestronglyMeasurable
        have hr := Complex.reCLM.continuous.comp_aestronglyMeasurable hcm
        refine hr.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := lt_trans zero_lt_one ht
        have hcpow : (t : ℂ) ^ (-(σ : ℂ) - 1) = ((t ^ (-σ - 1) : ℝ) : ℂ) := by
          have hc : (-(σ : ℂ) - 1 : ℂ) = ((-σ - 1 : ℝ) : ℂ) := by push_cast; ring
          rw [hc, ← Complex.ofReal_cpow htpos.le]
        change ((Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)).re =
          Chebyshev.psi t * t ^ (-σ - 1)
        rw [hcpow, ← Complex.ofReal_mul, Complex.ofReal_re]
      have h3m := h3'.aestronglyMeasurable
      refine (h1m.sub ((hpsim.sub h3m).const_mul sgn)).congr ?_
      filter_upwards with t
      dsimp [g]
      ring
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    have hpow_pos : 0 ≤ t ^ (-σ - 1) := (Real.rpow_pos_of_pos htpos _).le
    have hpow_b : 0 ≤ t ^ β := (Real.rpow_pos_of_pos htpos _).le
    have hcomb_nonneg : 0 ≤ C * (t ^ β * t ^ (-σ - 1)) +
        |sgn| * (|Chebyshev.psi t| * t ^ (-σ - 1) + t * t ^ (-σ - 1)) := by
      have hpsi_abs : 0 ≤ |Chebyshev.psi t| * t ^ (-σ - 1) := mul_nonneg (abs_nonneg _) hpow_pos
      have ht_nonneg : 0 ≤ t * t ^ (-σ - 1) := mul_nonneg htpos.le hpow_pos
      positivity
    simp only [Real.norm_eq_abs]
    dsimp [g]
    calc
      |((C * t ^ β - sgn * (Chebyshev.psi t - t)) * t ^ (-σ - 1))|
          = |C * t ^ β - sgn * (Chebyshev.psi t - t)| * t ^ (-σ - 1) := by
            rw [abs_mul, abs_of_nonneg hpow_pos]
      _ ≤ (C * t ^ β + |sgn| * (|Chebyshev.psi t| + t)) * t ^ (-σ - 1) := by
            refine mul_le_mul_of_nonneg_right ?_ hpow_pos
            calc
              |C * t ^ β - sgn * (Chebyshev.psi t - t)|
                  ≤ |C * t ^ β| + |sgn * (Chebyshev.psi t - t)| := abs_sub _ _
              _ = C * t ^ β + |sgn| * |Chebyshev.psi t - t| := by
                rw [abs_of_nonneg (mul_nonneg hC.le hpow_b), abs_mul]
              _ ≤ C * t ^ β + |sgn| * (|Chebyshev.psi t| + t) := by
                gcongr
                calc
                  |Chebyshev.psi t - t| ≤ |Chebyshev.psi t| + |t| := abs_sub _ _
                  _ = |Chebyshev.psi t| + t := by rw [abs_of_pos htpos]
      _ = C * (t ^ β * t ^ (-σ - 1)) +
            |sgn| * (|Chebyshev.psi t| * t ^ (-σ - 1) + t * t ^ (-σ - 1)) := by ring
  let M_init : ℂ → ℂ := fun z => ∫ t in Set.Ioc 1 X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1)
  have hM_init_diff : Differentiable ℂ M_init := by
    have hg_int2 : IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ) - 1)) (Set.Ioi 1) :=
      hg_int_sigma one_lt_two
    have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioc 1 X₀)) := by
      have h1_loc : IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ) - 1)) (Set.Ioc 1 X₀) :=
        hg_int2.mono_set Set.Ioc_subset_Ioi_self
      have hcont : ContinuousOn (fun t : ℝ => t ^ (3 : ℝ)) (Set.Icc 1 X₀) :=
        fun t ht => (Real.continuousAt_rpow_const t 3 (Or.inl (by linarith [ht.1]))).continuousWithinAt
      have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (3 : ℝ)) (volume.restrict (Set.Ioc 1 X₀)) :=
        (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      refine (h1_loc.aestronglyMeasurable.mul hmeas).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htpos : 0 < t := lt_trans zero_lt_one ht.1
      simp only [Pi.mul_apply]
      rw [mul_assoc, ← Real.rpow_add htpos]
      norm_num
    have hpsi_bd : ∀ t ∈ Set.Ioc 1 X₀, |Chebyshev.psi t| ≤
        ∑ n ∈ Finset.Icc 1 ⌊X₀⌋₊, ArithmeticFunction.vonMangoldt n := by
      intro t ht
      rw [psi_eq_sum_Icc]
      have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_of_nonneg hnn]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.floor_mono ht.2))
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    set P := ∑ n ∈ Finset.Icc 1 ⌊X₀⌋₊, ArithmeticFunction.vonMangoldt n
    refine differentiable_mellin_Ioc zero_lt_one hX₀_ge1 hg_meas
      (B := C * X₀ ^ β + |sgn| * (P + X₀)) (fun t ht => ?_)
    have htpos : 0 < t := lt_trans zero_lt_one ht.1
    have hpow_le : t ^ β ≤ X₀ ^ β := Real.rpow_le_rpow htpos.le ht.2 hre0.le
    calc
      |g t| = |C * t ^ β - sgn * (Chebyshev.psi t - t)| := rfl
      _ ≤ |C * t ^ β| + |sgn * (Chebyshev.psi t - t)| := abs_sub _ _
      _ = C * t ^ β + |sgn| * |Chebyshev.psi t - t| := by
        rw [abs_of_nonneg (mul_nonneg hC.le (Real.rpow_pos_of_pos htpos _).le), abs_mul]
      _ ≤ C * X₀ ^ β + |sgn| * (P + X₀) := by
        gcongr
        calc
          |Chebyshev.psi t - t| ≤ |Chebyshev.psi t| + |t| := abs_sub _ _
          _ ≤ P + X₀ := add_le_add (hpsi_bd t ht) (by rw [abs_of_pos htpos]; exact ht.2)
  let H : ℂ → ℂ := fun z =>
    z * riemannZeta₁ z * ((C : ℂ) / (z - β) - M_init z) +
      (sgn : ℂ) * (riemannZeta₁ z + deriv riemannZeta₁ z)
  have hH_diff : DifferentiableOn ℂ H {z : ℂ | β < z.re} := by
    intro z hz
    rw [Set.mem_ofPred_eq] at hz
    have hzneβ : z - β ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re (sub_eq_zero.mp h0)
      simp at hre
      linarith
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w * riemannZeta₁ w * ((C : ℂ) / (w - β) - M_init w)) z :=
      (differentiableAt_id.mul (differentiable_riemannZeta₁ z)).mul
        ((differentiableAt_const (C : ℂ) |>.div (differentiableAt_id.sub_const (β : ℂ)) hzneβ).sub
          (hM_init_diff z))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (sgn : ℂ) * (riemannZeta₁ w + deriv riemannZeta₁ w)) z :=
      ((differentiable_riemannZeta₁ z).add
        ((differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).deriv z
          (Set.mem_univ z)).differentiableAt).const_mul _
    exact (h1.add h2).differentiableWithinAt
  have hH_eq : ∀ z : ℂ, (1 : ℝ) < z.re →
      IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) ∧
      z * riemannZeta₁ z * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) = H z :=
    psi_mellin_tail_H_eq hX₀_ge1 hre1 (fun _ => rfl) hpsi_mellin hg_int_sigma
      (fun _ => rfl) (fun _ => rfl)
  have hg_int_2 : IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ) - 1)) (Set.Ioi X₀) :=
    (hg_int_sigma one_lt_two).mono_set (Set.Ioi_subset_Ioi hX₀_ge1)
  have hext := landau_mellin_extend_by_zeta₁ hX₀_ge1 hre0 (hre1.trans one_lt_two)
    hg_nonneg hg_int_2 hH_diff (fun z hz => hH_eq z (by linarith))
  have hM_bound : ∀ ε : ℝ, 0 < ε →
      ‖(ε : ℂ) * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖ ≤
        ε * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re := by
    intro ε hε
    have hre_ρ : β < (ρ + (ε : ℂ)).re := by simp [β]; exact hε
    have hre_β : β < ((β + ε : ℝ) : ℂ).re := by simp [β]; exact hε
    have hint_ρ := (hext.2 (ρ + ε) hre_ρ).1
    have hint_real : IntegrableOn (fun t : ℝ => g t * t ^ (-(β + ε) - 1)) (Set.Ioi X₀) :=
      hext.1 (β + ε) (by linarith)
    have hnorm_eq : (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re =
        ∫ t in Set.Ioi X₀, g t * t ^ (-(β + ε) - 1) := by
      have hint_β := (hext.2 ((β + ε : ℝ) : ℂ) hre_β).1
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_β]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      have htpos : 0 < t := lt_trans hX₀_pos ht
      have hc : (-((β + ε : ℝ) : ℂ) - 1 : ℂ) = ((-(β + ε) - 1 : ℝ) : ℂ) := by push_cast; ring
      change ((g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re = g t * t ^ (-(β + ε) - 1)
      rw [hc, ← Complex.ofReal_cpow htpos.le, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hnorm_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    calc
      ‖∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖
          ≤ ∫ t in Set.Ioi X₀, ‖(g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ t in Set.Ioi X₀, g t * t ^ (-(β + ε) - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t ht
        have htpos : 0 < t := lt_trans hX₀_pos ht
        have hre_eq : (-(ρ + (ε : ℂ)) - 1).re = -(β + ε) - 1 := by simp [β]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hg_nonneg t ht), Complex.norm_cpow_eq_rpow_re_of_pos htpos, hre_eq]
  have hlim_rhs : Tendsto
      (fun ε : ℝ => ε * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have h_fn : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
        (ε : ℂ) * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1) =
          (C : ℂ) - (ε : ℂ) * M_init (β + ε : ℝ) +
            (ε : ℂ) * ((sgn : ℂ) * (riemannZeta₁ (β + ε : ℝ) + deriv riemannZeta₁ (β + ε : ℝ))) /
              (((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      have hre : β < ((β + ε : ℝ) : ℂ).re := by simp; linarith
      have hid := (hext.2 ((β + ε : ℝ) : ℂ) hre).2
      have hb_pos : 0 < β + ε := by linarith
      have hz1_ne : riemannZeta₁ ((β + ε : ℝ) : ℂ) ≠ 0 := riemannZeta₁_ofReal_ne_zero_of_pos hb_pos
      have hzb_ne : (((β + ε : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hb_pos.ne'
      have hden_ne : ((β + ε : ℝ) : ℂ) * riemannZeta₁ ((β + ε : ℝ) : ℂ) ≠ 0 :=
        mul_ne_zero hzb_ne hz1_ne
      have hsub_ne : (((β + ε : ℝ) : ℂ) - (β : ℂ)) = (ε : ℂ) := by push_cast; ring
      have hM_eq : ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1) =
          H ((β + ε : ℝ) : ℂ) / (((β + ε : ℝ) : ℂ) * riemannZeta₁ ((β + ε : ℝ) : ℂ)) := by
        rw [← hid]
        field_simp [hden_ne]
      rw [hM_eq]
      dsimp [H]
      rw [hsub_ne]
      have hε_ne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
      field_simp [hden_ne, hε_ne]
    have htend_c : Tendsto
        (fun ε : ℝ => (C : ℂ) - (ε : ℂ) * M_init (β + ε : ℝ) +
          (ε : ℂ) * ((sgn : ℂ) * (riemannZeta₁ (β + ε : ℝ) + deriv riemannZeta₁ (β + ε : ℝ))) /
            (((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (C : ℂ)) := by
      have h_lin : Tendsto (fun ε : ℝ => ((β + ε : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (β : ℂ)) := by
        have h : Continuous (fun ε : ℝ => ((β + ε : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
        simpa using ((h.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
      have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      have hM0 : Tendsto (fun ε : ℝ => (ε : ℂ) * M_init (β + ε : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 * M_init β)) :=
        hε0.mul (hM_init_diff.continuous.continuousAt.tendsto.comp h_lin)
      have hdz1 : Continuous (fun z : ℂ => riemannZeta₁ z + deriv riemannZeta₁ z) :=
        differentiable_riemannZeta₁.continuous.add
          (differentiable_riemannZeta₁.contDiff.continuous_deriv le_rfl)
      have hnum : Tendsto (fun ε : ℝ => (ε : ℂ) * ((sgn : ℂ) *
          (riemannZeta₁ (β + ε : ℝ) + deriv riemannZeta₁ (β + ε : ℝ))))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 * ((sgn : ℂ) * (riemannZeta₁ β + deriv riemannZeta₁ β)))) :=
        hε0.mul ((hdz1.continuousAt.tendsto.comp h_lin).const_mul _)
      have hden : Tendsto (fun ε : ℝ => ((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 ((β : ℂ) * riemannZeta₁ β)) :=
        h_lin.mul (differentiable_riemannZeta₁.continuous.continuousAt.tendsto.comp h_lin)
      have hden_ne : (β : ℂ) * riemannZeta₁ β ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hre0.ne') (riemannZeta₁_ofReal_ne_zero_of_pos hre0)
      have hq : Tendsto (fun ε : ℝ =>
          (ε : ℂ) * ((sgn : ℂ) * (riemannZeta₁ (β + ε : ℝ) + deriv riemannZeta₁ (β + ε : ℝ))) /
            (((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hdiv := hnum.div hden hden_ne
        rw [Pi.div_def] at hdiv
        simpa using hdiv
      have hres := ((tendsto_const_nhds (x := (C : ℂ))).sub hM0).add hq
      simpa using hres
    have htend_c' := htend_c.congr' (h_fn.mono fun _ h => h.symm)
    have htend_r := (Complex.continuous_re.continuousAt.tendsto.comp htend_c')
    refine htend_r.congr' ?_
    filter_upwards with ε
    simp
  obtain ⟨m, φ, hm_ge, hφ_diff_ev, hφ_dcont, hφ_cont, hφ_ne, hφ_fac⟩ :=
    riemannZeta₁_factor_at_zero hρ hre0 hre1
  have hρ_im_ne : ρ.im ≠ 0 := by
    intro him
    have hρ_real : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext rfl him
    have hneg := (riemannZeta_ofReal_neg_on_Ioo hre0 hre1).1
    rw [← hρ_real, hρ, Complex.zero_re] at hneg
    exact lt_irrefl 0 hneg
  have hρ_ne_β : ρ ≠ (β : ℂ) := by
    intro h
    have := congrArg Complex.im h
    simp [β] at this
    exact hρ_im_ne this
  have hρ_ne0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
  have hlim_lhs : Tendsto
      (fun ε : ℝ => ‖(ε : ℂ) * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖(sgn : ℂ) * (m : ℂ) / ρ‖)) := by
    have h_lin : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
      simpa using (tendsto_const_nhds.add
        ((Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))))
    have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have h_deriv_fac : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
        φ (ρ + ε) ≠ 0 ∧ riemannZeta₁ (ρ + ε) ≠ 0 ∧ (ρ + (ε : ℂ) ≠ 0) ∧
        (ε : ℂ) * (deriv riemannZeta₁ (ρ + ε) / riemannZeta₁ (ρ + ε)) =
          (m : ℂ) + (ε : ℂ) * (deriv φ (ρ + ε) / φ (ρ + ε)) :=
      riemannZeta₁_logDeriv_near_zero hm_ge hρ_ne0 hφ_diff_ev hφ_cont hφ_ne hφ_fac h_lin
    have h_fn : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
        (ε : ℂ) * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1) =
          (ε : ℂ) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) +
            (ε : ℂ) * (sgn : ℂ) / (ρ + ε) +
            (sgn : ℂ) * ((m : ℂ) + (ε : ℂ) * (deriv φ (ρ + ε) / φ (ρ + ε))) / (ρ + ε) := by
      filter_upwards [self_mem_nhdsWithin, h_deriv_fac] with ε hε ⟨_, hz1_ne, hzne0, hld_eq⟩
      rw [Set.mem_Ioi] at hε
      have hre : β < (ρ + (ε : ℂ)).re := by simp [β]; exact hε
      have hid := (hext.2 (ρ + ε) hre).2
      have hden_ne : (ρ + (ε : ℂ)) * riemannZeta₁ (ρ + ε) ≠ 0 := mul_ne_zero hzne0 hz1_ne
      have hM_eq : ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1) =
          H (ρ + ε) / ((ρ + ε) * riemannZeta₁ (ρ + ε)) := by
        rw [← hid]
        field_simp [hden_ne]
      rw [hM_eq]
      dsimp [H]
      have hsplit : (ε : ℂ) * (((ρ + ε) * riemannZeta₁ (ρ + ε) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) +
            (sgn : ℂ) * (riemannZeta₁ (ρ + ε) + deriv riemannZeta₁ (ρ + ε))) /
            ((ρ + ε) * riemannZeta₁ (ρ + ε))) =
          (ε : ℂ) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) +
            (ε : ℂ) * (sgn : ℂ) / (ρ + ε) +
            (sgn : ℂ) * ((ε : ℂ) * (deriv riemannZeta₁ (ρ + ε) / riemannZeta₁ (ρ + ε))) / (ρ + ε) := by
        field_simp [hden_ne]
        ring
      rw [hsplit, hld_eq]
    have htend_c : Tendsto
        (fun ε : ℝ => (ε : ℂ) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) +
          (ε : ℂ) * (sgn : ℂ) / (ρ + ε) +
          (sgn : ℂ) * ((m : ℂ) + (ε : ℂ) * (deriv φ (ρ + ε) / φ (ρ + ε))) / (ρ + ε))
        (𝓝[>] (0 : ℝ)) (𝓝 ((sgn : ℂ) * (m : ℂ) / ρ)) := by
      have hsub_ne : ρ - (β : ℂ) ≠ 0 := sub_ne_zero.mpr hρ_ne_β
      have hsub_t : Tendsto (fun ε : ℝ => (C : ℂ) / (ρ + ε - β) - M_init (ρ + ε))
          (𝓝[>] (0 : ℝ)) (𝓝 ((C : ℂ) / (ρ - β) - M_init ρ)) :=
        ((tendsto_const_nhds.div (h_lin.sub tendsto_const_nhds) hsub_ne).sub
          (hM_init_diff.continuous.continuousAt.tendsto.comp h_lin))
      have h1 : Tendsto (fun ε : ℝ => (ε : ℂ) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hε0.mul hsub_t
      have h2 : Tendsto (fun ε : ℝ => (ε : ℂ) * (sgn : ℂ) / (ρ + ε))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hdiv := (hε0.mul (tendsto_const_nhds (x := (sgn : ℂ)))).div h_lin hρ_ne0
        rw [Pi.div_def] at hdiv
        simpa using hdiv
      have hder_q : Tendsto (fun ε : ℝ => (ε : ℂ) * (deriv φ (ρ + ε) / φ (ρ + ε)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hq := (hφ_dcont.tendsto.comp h_lin).div (hφ_cont.tendsto.comp h_lin) hφ_ne
        simpa using hε0.mul hq
      have h3 : Tendsto (fun ε : ℝ =>
          (sgn : ℂ) * ((m : ℂ) + (ε : ℂ) * (deriv φ (ρ + ε) / φ (ρ + ε))) / (ρ + ε))
          (𝓝[>] (0 : ℝ)) (𝓝 ((sgn : ℂ) * (m : ℂ) / ρ)) := by
        have hnum := ((tendsto_const_nhds (x := (m : ℂ))).add hder_q).const_mul (sgn : ℂ)
        have hdiv := hnum.div h_lin hρ_ne0
        rw [Pi.div_def] at hdiv
        simpa using hdiv
      have htot := (h1.add h2).add h3
      simpa using htot
    have htend_c' := htend_c.congr' (h_fn.mono fun _ h => h.symm)
    exact continuous_norm.continuousAt.tendsto.comp htend_c'
  have hle_lim : ‖(sgn : ℂ) * (m : ℂ) / ρ‖ ≤ C := by
    refine le_of_tendsto_of_tendsto hlim_lhs hlim_rhs ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hM_bound ε (Set.mem_Ioi.mp hε)
  have hnorm_sgn : ‖(sgn : ℂ)‖ = 1 := by
    rcases hsgn with rfl | rfl <;> simp
  have hge_norm : 1 / ‖ρ‖ ≤ ‖(sgn : ℂ) * (m : ℂ) / ρ‖ := by
    rw [norm_div, norm_mul, hnorm_sgn, one_mul, Complex.norm_natCast]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
    exact div_le_div_of_nonneg_right hm1 (norm_nonneg ρ)
  linarith

/-- **Unconditional Phragmén–Landau oscillation for `ψ(x) - x` from a nontrivial zero.**
If `riemannZeta ρ = 0` with `0 < ρ.re < 1`, then for every `δ > 0`, both
`(1 / ‖ρ‖ - δ) * x ^ ρ.re < Chebyshev.psi x - x` and `Chebyshev.psi x - x < -(1 / ‖ρ‖ - δ) * x ^ ρ.re`
hold frequently as `x → ∞`. -/
theorem psi_sub_id_omega_plus_minus_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    ∀ δ : ℝ, 0 < δ →
      (∃ᶠ x in atTop, (1 / ‖ρ‖ - δ) * x ^ ρ.re < Chebyshev.psi x - x) ∧
      (∃ᶠ x in atTop, Chebyshev.psi x - x < -(1 / ‖ρ‖ - δ) * x ^ ρ.re) := by
  intro δ hδ
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr (by
    intro h0; rw [h0, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0)
  set C : ℝ := max (1 / ‖ρ‖ - δ) (1 / (2 * ‖ρ‖))
  have hC_pos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hC_lt : C < 1 / ‖ρ‖ := max_lt (by linarith) (by
    rw [one_div, one_div, inv_lt_inv₀ (by positivity) hρ_pos]
    linarith)
  have hplus : ∃ᶠ x in atTop, C * x ^ ρ.re < Chebyshev.psi x - x := by
    by_contra hnot
    rw [Filter.not_frequently] at hnot
    exact psi_sub_id_one_side hρ hre0 hre1 hC_pos hC_lt 1 (Or.inl rfl)
      (hnot.mono fun _ h => by linarith)
  have hminus : ∃ᶠ x in atTop, Chebyshev.psi x - x < -C * x ^ ρ.re := by
    by_contra hnot
    rw [Filter.not_frequently] at hnot
    exact psi_sub_id_one_side hρ hre0 hre1 hC_pos hC_lt (-1) (Or.inr rfl)
      (hnot.mono fun _ h => by linarith)
  have hge1 : ∀ᶠ x in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop 1
  refine ⟨?_, ?_⟩
  · refine (hplus.and_eventually hge1).mono ?_
    rintro x ⟨hx, hx1⟩
    have hpow : 0 ≤ x ^ ρ.re := (Real.rpow_pos_of_pos (by linarith) _).le
    have hle : (1 / ‖ρ‖ - δ) * x ^ ρ.re ≤ C * x ^ ρ.re :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
    exact lt_of_le_of_lt hle hx
  · refine (hminus.and_eventually hge1).mono ?_
    rintro x ⟨hx, hx1⟩
    have hpow : 0 ≤ x ^ ρ.re := (Real.rpow_pos_of_pos (by linarith) _).le
    have hle : -C * x ^ ρ.re ≤ -(1 / ‖ρ‖ - δ) * x ^ ρ.re := by
      have : (1 / ‖ρ‖ - δ) ≤ C := le_max_left _ _
      nlinarith
    exact lt_of_lt_of_le hx hle

/-- **Unconditional `ψ(x) - x = Ω_±(x^(1/2))`.** -/
theorem psi_sub_id_omega_half :
    ∃ c > 0,
      (∃ᶠ x in atTop, c * x ^ (1 / 2 : ℝ) ≤ Chebyshev.psi x - x) ∧
      (∃ᶠ x in atTop, Chebyshev.psi x - x ≤ -c * x ^ (1 / 2 : ℝ)) := by
  obtain ⟨ρ₀, hρ₀, hre_ge, hre_lt⟩ := exists_nontrivial_zero_re_ge_half
  have hre0 : 0 < ρ₀.re := lt_of_lt_of_le (by norm_num) hre_ge
  have hρ₀_pos : 0 < ‖ρ₀‖ := norm_pos_iff.mpr (by
    intro h0; rw [h0, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0)
  obtain ⟨hplus, hminus⟩ := psi_sub_id_omega_plus_minus_of_zero hρ₀ hre0 hre_lt
    (1 / (2 * ‖ρ₀‖)) (by positivity)
  have hhalf : 1 / ‖ρ₀‖ - 1 / (2 * ‖ρ₀‖) = 1 / (2 * ‖ρ₀‖) := by field_simp [hρ₀_pos.ne']; ring
  rw [hhalf] at hplus hminus
  refine ⟨1 / (2 * ‖ρ₀‖), by positivity, ?_, ?_⟩
  · refine (hplus.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro x ⟨hx, hx1⟩
    have hpow : x ^ (1 / 2 : ℝ) ≤ x ^ ρ₀.re := Real.rpow_le_rpow_of_exponent_le hx1 hre_ge
    have h1 : 1 / (2 * ‖ρ₀‖) * x ^ (1 / 2 : ℝ) ≤ 1 / (2 * ‖ρ₀‖) * x ^ ρ₀.re :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith
  · refine (hminus.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro x ⟨hx, hx1⟩
    have hpow : x ^ (1 / 2 : ℝ) ≤ x ^ ρ₀.re := Real.rpow_le_rpow_of_exponent_le hx1 hre_ge
    have h1 : -(1 / (2 * ‖ρ₀‖)) * x ^ ρ₀.re ≤ -(1 / (2 * ‖ρ₀‖)) * x ^ (1 / 2 : ℝ) := by
      have hle := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1 / (2 * ‖ρ₀‖))
      linarith
    linarith [h1]

/-- **Unconditional `ψ(x) - x = Ω_±(x^(zetaSupRe - ε))` for every `ε > 0` and constant `M`.** -/
theorem psi_sub_id_omega_supRe :
    ∀ ε > 0, ∀ M : ℝ,
      (∃ᶠ x in atTop, M * x ^ (zetaSupRe - ε) ≤ Chebyshev.psi x - x) ∧
      (∃ᶠ x in atTop, Chebyshev.psi x - x ≤ -M * x ^ (zetaSupRe - ε)) := by
  intro ε hε M
  have hlt : zetaSupRe - ε < zetaSupRe := by linarith
  obtain ⟨σ, ⟨ρ, hρ, hre0, hre1, rfl⟩, hσ_gt⟩ := exists_lt_of_lt_csSup zetaZeroReSet_nonempty hlt
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr (by
    intro h0; rw [h0, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0)
  obtain ⟨hplus, hminus⟩ := psi_sub_id_omega_plus_minus_of_zero hρ hre0 hre1
    (1 / (2 * ‖ρ‖)) (by positivity)
  have hhalf : 1 / ‖ρ‖ - 1 / (2 * ‖ρ‖) = 1 / (2 * ‖ρ‖) := by field_simp [hρ_pos.ne']; ring
  rw [hhalf] at hplus hminus
  set c := 1 / (2 * ‖ρ‖)
  have hc : 0 < c := by positivity
  have hdom : ∀ᶠ x in atTop, |M| * x ^ (zetaSupRe - ε) ≤ c * x ^ ρ.re := by
    have hpow_lim : Tendsto (fun x : ℝ => x ^ (ρ.re - (zetaSupRe - ε))) atTop atTop :=
      tendsto_rpow_atTop (by linarith)
    have hev_big := hpow_lim.eventually_ge_atTop (|M| / c)
    filter_upwards [hev_big, eventually_gt_atTop 0] with x hx hx0
    have hdiv : |M| ≤ c * x ^ (ρ.re - (zetaSupRe - ε)) := by
      have := mul_le_mul_of_nonneg_left hx hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    calc
      |M| * x ^ (zetaSupRe - ε) ≤ (c * x ^ (ρ.re - (zetaSupRe - ε))) * x ^ (zetaSupRe - ε) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_pos_of_pos hx0 _).le
      _ = c * (x ^ (ρ.re - (zetaSupRe - ε)) * x ^ (zetaSupRe - ε)) := by ring
      _ = c * x ^ ρ.re := by rw [← Real.rpow_add hx0]; ring_nf
  refine ⟨?_, ?_⟩
  · refine (hplus.and_eventually (hdom.and (eventually_gt_atTop 0))).mono ?_
    rintro x ⟨hx, hdx, hx0⟩
    have hM : M * x ^ (zetaSupRe - ε) ≤ |M| * x ^ (zetaSupRe - ε) :=
      mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_pos_of_pos hx0 (zetaSupRe - ε)).le
    linarith
  · refine (hminus.and_eventually (hdom.and (eventually_gt_atTop 0))).mono ?_
    rintro x ⟨hx, hdx, hx0⟩
    have hM : -(|M| * x ^ (zetaSupRe - ε)) ≤ -M * x ^ (zetaSupRe - ε) := by
      have h0 : 0 ≤ x ^ (zetaSupRe - ε) := (Real.rpow_pos_of_pos hx0 (zetaSupRe - ε)).le
      have hle := mul_le_mul_of_nonneg_right (neg_le_neg (le_abs_self M)) h0
      linarith
    linarith

/-- The Mertens summatory function `M(x) = ∑_{1 ≤ n ≤ ⌊x⌋₊} μ(n)`. -/
def mertensM (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)

/-- For Re(s) > 1 the absolutely convergent Mellin integral of M(x) equals 1/(sζ(s)). -/
theorem mertensM_mellin_of_one_lt : ∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun t : ℝ => (mertensM t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) ∧
        IntegrableOn (fun t : ℝ => |mertensM t| * t ^ (-s.re - 1)) (Set.Ioi 1) ∧
        ∫ t in Set.Ioi (1 : ℝ), (mertensM t : ℂ) * (t : ℂ) ^ (-s - 1) =
          (s * riemannZeta s)⁻¹ := by
  have hμ_sum : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℝ) : ℂ)) s := by
    intro s hs
    have hμ := LSeriesSummable_moebius_iff.mpr hs
    exact hμ.congr fun n => by simp [LSeries.term]
  have hμ0 : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by simp
  intro s hs
  have hm := mellin_partialSum_eq_LSeries_div hμ0 (by linarith) (hμ_sum s hs)
  refine ⟨hm.1, hm.2.1, ?_⟩
  have hm2 := hm.2.2
  have hls : LSeries (fun n => ((ArithmeticFunction.moebius n : ℝ) : ℂ)) s =
      LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
    simp
  rw [hls] at hm2
  have hinv := LSeries_moebius_eq_inv_riemannZeta hs
  have hM_eq : ∫ t in Set.Ioi (1 : ℝ), (mertensM t : ℂ) * (t : ℂ) ^ (-s - 1) =
      ∫ t in Set.Ioi (1 : ℝ),
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius n : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := rfl
  rw [hM_eq, hm2]
  change LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s / s = (s * riemannZeta s)⁻¹
  rw [show LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = (riemannZeta s)⁻¹ from hinv]
  rw [div_eq_mul_inv, mul_inv, mul_comm]

private lemma mertensM_one_side {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    {C : ℝ} (hC : 0 < C) (hC_lt : C * (‖ρ‖ * ‖deriv riemannZeta ρ‖) < 1)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hbound : ∀ᶠ t in atTop, sgn * mertensM t ≤ C * t ^ ρ.re) :
    False := by
  rw [eventually_atTop] at hbound
  obtain ⟨X₁, hX₁⟩ := hbound
  set X₀ : ℝ := max X₁ 1
  have hX₀_ge1 : 1 ≤ X₀ := le_max_right _ _
  have hX₀_pos : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀_ge1
  have hX₀_bound : ∀ t : ℝ, X₀ ≤ t → sgn * mertensM t ≤ C * t ^ ρ.re :=
    fun t ht => hX₁ t ((le_max_left _ _).trans ht)
  let β : ℝ := ρ.re
  let g : ℝ → ℝ := fun t => C * t ^ β - sgn * mertensM t
  have hg_nonneg : ∀ t ∈ Set.Ioi X₀, 0 ≤ g t := by
    intro t ht
    dsimp [g]
    linarith [hX₀_bound t ht.le]
  have hM_mellin := @mertensM_mellin_of_one_lt
  have hg_int_sigma : ∀ {σ : ℝ}, 1 < σ →
      IntegrableOn (fun t : ℝ => g t * t ^ (-σ - 1)) (Set.Ioi 1) := by
    intro σ hσ
    have h1 := (integral_Ioi_one_rpow_mul_cpow (α := β) (s := (σ : ℂ))
      (by simpa using hre1.trans hσ)).1.const_mul C
    have h2 := (hM_mellin (σ : ℂ) (by simpa using hσ)).2.1
    have hdom := h1.add (h2.const_mul |sgn|)
    have hmeas : AEStronglyMeasurable (fun t : ℝ => g t * t ^ (-σ - 1))
        (volume.restrict (Set.Ioi 1)) := by
      have h1m := h1.aestronglyMeasurable
      have hMm : AEStronglyMeasurable (fun t : ℝ => mertensM t * t ^ (-σ - 1))
          (volume.restrict (Set.Ioi 1)) := by
        have hcm := (hM_mellin (σ : ℂ) (by simpa using hσ)).1.aestronglyMeasurable
        have hr := Complex.reCLM.continuous.comp_aestronglyMeasurable hcm
        refine hr.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := lt_trans zero_lt_one ht
        have hcpow : (t : ℂ) ^ (-(σ : ℂ) - 1) = ((t ^ (-σ - 1) : ℝ) : ℂ) := by
          have hc : (-(σ : ℂ) - 1 : ℂ) = ((-σ - 1 : ℝ) : ℂ) := by push_cast; ring
          rw [hc, ← Complex.ofReal_cpow htpos.le]
        change ((mertensM t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)).re = mertensM t * t ^ (-σ - 1)
        rw [hcpow, ← Complex.ofReal_mul, Complex.ofReal_re]
      refine (h1m.sub (hMm.const_mul sgn)).congr ?_
      filter_upwards with t
      dsimp [g]
      ring
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    have hpow_pos : 0 ≤ t ^ (-σ - 1) := (Real.rpow_pos_of_pos htpos _).le
    have hpow_b : 0 ≤ t ^ β := (Real.rpow_pos_of_pos htpos _).le
    have hcomb_nonneg : 0 ≤ C * (t ^ β * t ^ (-σ - 1)) +
        |sgn| * (|mertensM t| * t ^ (-σ - 1)) := by
      have hM_abs : 0 ≤ |mertensM t| * t ^ (-σ - 1) := mul_nonneg (abs_nonneg _) hpow_pos
      positivity
    simp only [Real.norm_eq_abs]
    dsimp [g]
    calc
      |((C * t ^ β - sgn * mertensM t) * t ^ (-σ - 1))|
          = |C * t ^ β - sgn * mertensM t| * t ^ (-σ - 1) := by
            rw [abs_mul, abs_of_nonneg hpow_pos]
      _ ≤ (C * t ^ β + |sgn| * |mertensM t|) * t ^ (-σ - 1) := by
            refine mul_le_mul_of_nonneg_right ?_ hpow_pos
            calc
              |C * t ^ β - sgn * mertensM t| ≤ |C * t ^ β| + |sgn * mertensM t| := abs_sub _ _
              _ = C * t ^ β + |sgn| * |mertensM t| := by
                rw [abs_of_nonneg (mul_nonneg hC.le hpow_b), abs_mul]
      _ = C * (t ^ β * t ^ (-σ - 1)) + |sgn| * (|mertensM t| * t ^ (-σ - 1)) := by ring
  let M_init : ℂ → ℂ := fun z => ∫ t in Set.Ioc 1 X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1)
  have hM_init_diff : Differentiable ℂ M_init := by
    have hg_int2 : IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ) - 1)) (Set.Ioi 1) :=
      hg_int_sigma one_lt_two
    have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioc 1 X₀)) := by
      have h1_loc : IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ) - 1)) (Set.Ioc 1 X₀) :=
        hg_int2.mono_set Set.Ioc_subset_Ioi_self
      have hcont : ContinuousOn (fun t : ℝ => t ^ (3 : ℝ)) (Set.Icc 1 X₀) :=
        fun t ht => (Real.continuousAt_rpow_const t 3 (Or.inl (by linarith [ht.1]))).continuousWithinAt
      have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (3 : ℝ)) (volume.restrict (Set.Ioc 1 X₀)) :=
        (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      refine (h1_loc.aestronglyMeasurable.mul hmeas).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htpos : 0 < t := lt_trans zero_lt_one ht.1
      simp only [Pi.mul_apply]
      rw [mul_assoc, ← Real.rpow_add htpos]
      norm_num
    have hM_bd : ∀ t ∈ Set.Ioc 1 X₀, |mertensM t| ≤ (⌊X₀⌋₊ : ℝ) := by
      intro t ht
      dsimp [mertensM]
      calc
        |∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius n : ℝ)|
            ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, |(ArithmeticFunction.moebius n : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        _ ≤ (⌊X₀⌋₊ : ℝ) := by
          simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
          have hfl : ⌊t⌋₊ ≤ ⌊X₀⌋₊ := Nat.floor_mono ht.2
          have : ⌊t⌋₊ + 1 - 1 ≤ ⌊X₀⌋₊ := by omega
          exact_mod_cast this
    refine differentiable_mellin_Ioc zero_lt_one hX₀_ge1 hg_meas
      (B := C * X₀ ^ β + |sgn| * (⌊X₀⌋₊ : ℝ)) (fun t ht => ?_)
    have htpos : 0 < t := lt_trans zero_lt_one ht.1
    have hpow_le : t ^ β ≤ X₀ ^ β := Real.rpow_le_rpow htpos.le ht.2 hre0.le
    calc
      |g t| = |C * t ^ β - sgn * mertensM t| := rfl
      _ ≤ |C * t ^ β| + |sgn * mertensM t| := abs_sub _ _
      _ = C * t ^ β + |sgn| * |mertensM t| := by
        rw [abs_of_nonneg (mul_nonneg hC.le (Real.rpow_pos_of_pos htpos _).le), abs_mul]
      _ ≤ C * X₀ ^ β + |sgn| * (⌊X₀⌋₊ : ℝ) := by
        gcongr; exact hM_bd t ht
  let H : ℂ → ℂ := fun z =>
    z * riemannZeta₁ z * ((C : ℂ) / (z - β) - M_init z) - (sgn : ℂ) * (z - 1)
  have hH_diff : DifferentiableOn ℂ H {z : ℂ | β < z.re} := by
    intro z hz
    rw [Set.mem_ofPred_eq] at hz
    have hzneβ : z - β ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re (sub_eq_zero.mp h0)
      simp at hre
      linarith
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w * riemannZeta₁ w * ((C : ℂ) / (w - β) - M_init w)) z :=
      (differentiableAt_id.mul (differentiable_riemannZeta₁ z)).mul
        ((differentiableAt_const (C : ℂ) |>.div (differentiableAt_id.sub_const (β : ℂ)) hzneβ).sub
          (hM_init_diff z))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (sgn : ℂ) * (w - 1)) z :=
      ((differentiableAt_id.sub_const 1).const_mul _)
    exact (h1.sub h2).differentiableWithinAt
  have hH_eq : ∀ z : ℂ, (1 : ℝ) < z.re →
      IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) ∧
      z * riemannZeta₁ z * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) = H z := by
    intro z hz
    have hIoi1_int : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) := by
      have hr_int := hg_int_sigma hz
      have hmeas : AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1))
          (volume.restrict (Set.Ioi 1)) := by
        have hg_m : AEStronglyMeasurable g (volume.restrict (Set.Ioi 1)) :=
          aestronglyMeasurable_of_integrableOn zero_lt_one (fun σ hσ => hg_int_sigma hσ)
        have hpow_m : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-z - 1))
            (volume.restrict (Set.Ioi 1)) :=
          (ContinuousOn.aestronglyMeasurable (fun t ht =>
            (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
              (Or.inl (by simpa using lt_trans zero_lt_one ht))).continuousWithinAt) measurableSet_Ioi)
        exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_m).mul hpow_m
      refine hr_int.norm.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans zero_lt_one ht
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re,
        abs_of_pos (Real.rpow_pos_of_pos htpos _)]
      exact le_rfl
    have htail_int : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi X₀) :=
      hIoi1_int.mono_set (Set.Ioi_subset_Ioi hX₀_ge1)
    refine ⟨htail_int, ?_⟩
    have hIoc_int : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioc 1 X₀) :=
      hIoi1_int.mono_set Set.Ioc_subset_Ioi_self
    have hIoi_split : Set.Ioi (1 : ℝ) = Set.Ioc 1 X₀ ∪ Set.Ioi X₀ := by
      ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      exact ⟨fun h => (le_or_gt t X₀).imp (fun hle => ⟨h, hle⟩) id,
        fun h => h.elim And.left (lt_of_le_of_lt hX₀_ge1)⟩
    have h_union : ∫ t in Set.Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (-z - 1) =
        M_init z + ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) := by
      rw [hIoi_split]
      exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc_int htail_int
    have h1_c := integral_Ioi_one_rpow_mul_cpow (α := β) (s := z) (hre1.trans hz)
    have h1_c_int : IntegrableOn (fun t : ℝ => ((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) := by
      have hm : AEStronglyMeasurable (fun t : ℝ => ((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))
          (volume.restrict (Set.Ioi 1)) :=
        (ContinuousOn.aestronglyMeasurable (fun t ht =>
          ((Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_rpow_const t β (Or.inl (lt_trans zero_lt_one ht).ne'))).mul
            (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
              (Or.inl (by simpa using lt_trans zero_lt_one ht)))).continuousWithinAt) measurableSet_Ioi)
      refine (h1_c.1.mono' hm ?_)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans zero_lt_one ht
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, sub_re, one_re,
        abs_of_pos (Real.rpow_pos_of_pos htpos _)]
      exact le_rfl
    have h2_c := hM_mellin z hz
    have hIoi1_val : ∫ t in Set.Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (-z - 1) =
        (C : ℂ) / (z - β) - (sgn : ℂ) * (z * riemannZeta z)⁻¹ := by
      have hfn : (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (-z - 1)) =
          (fun t : ℝ => (C : ℂ) * (((t ^ β : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) -
            (sgn : ℂ) * ((mertensM t : ℂ) * (t : ℂ) ^ (-z - 1))) := by
        ext t; dsimp [g]; push_cast; ring
      rw [hfn, integral_sub (h1_c_int.const_mul (C : ℂ)) (h2_c.1.const_mul (sgn : ℂ)),
        integral_const_mul, integral_const_mul, h1_c.2, h2_c.2.2]
      ring
    have htail_val : ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-z - 1) =
        (C : ℂ) / (z - β) - M_init z - (sgn : ℂ) * (z * riemannZeta z)⁻¹ := by
      linear_combination hIoi1_val - h_union
    have hzne1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz; linarith
    have hzne0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; linarith
    have hz_nz : riemannZeta z ≠ 0 := _root_.riemannZeta_ne_zero_of_one_lt_re hz
    have hz₁_eq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hzne1]
      have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hzne1
      field_simp [hsub]
    rw [htail_val]
    dsimp [H]
    rw [hz₁_eq]
    have hden : z * riemannZeta z ≠ 0 := mul_ne_zero hzne0 hz_nz
    field_simp [hden]
  have hg_int_2 : IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ) - 1)) (Set.Ioi X₀) :=
    (hg_int_sigma one_lt_two).mono_set (Set.Ioi_subset_Ioi hX₀_ge1)
  have hext := landau_mellin_extend_by_zeta₁ hX₀_ge1 hre0 (hre1.trans one_lt_two)
    hg_nonneg hg_int_2 hH_diff (fun z hz => hH_eq z (by linarith))
  have hM_bound : ∀ ε : ℝ, 0 < ε →
      ‖(ε : ℂ) * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖ ≤
        ε * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re := by
    intro ε hε
    have hre_ρ : β < (ρ + (ε : ℂ)).re := by simp [β]; exact hε
    have hre_β : β < ((β + ε : ℝ) : ℂ).re := by simp [β]; exact hε
    have hint_β := (hext.2 ((β + ε : ℝ) : ℂ) hre_β).1
    have hnorm_eq : (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re =
        ∫ t in Set.Ioi X₀, g t * t ^ (-(β + ε) - 1) := by
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_β]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      have htpos : 0 < t := lt_trans hX₀_pos ht
      have hc : (-((β + ε : ℝ) : ℂ) - 1 : ℂ) = ((-(β + ε) - 1 : ℝ) : ℂ) := by push_cast; ring
      change ((g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re = g t * t ^ (-(β + ε) - 1)
      rw [hc, ← Complex.ofReal_cpow htpos.le, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hnorm_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    calc
      ‖∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖
          ≤ ∫ t in Set.Ioi X₀, ‖(g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ t in Set.Ioi X₀, g t * t ^ (-(β + ε) - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t ht
        have htpos : 0 < t := lt_trans hX₀_pos ht
        have hre_eq : (-(ρ + (ε : ℂ)) - 1).re = -(β + ε) - 1 := by simp [β]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hg_nonneg t ht), Complex.norm_cpow_eq_rpow_re_of_pos htpos, hre_eq]
  have hlim_rhs : Tendsto
      (fun ε : ℝ => ε * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have h_fn : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
        (ε : ℂ) * ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1) =
          (C : ℂ) - (ε : ℂ) * M_init (β + ε : ℝ) -
            (ε : ℂ) * ((sgn : ℂ) * (((β + ε : ℝ) : ℂ) - 1)) /
              (((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      have hre : β < ((β + ε : ℝ) : ℂ).re := by simp; linarith
      have hid := (hext.2 ((β + ε : ℝ) : ℂ) hre).2
      have hb_pos : 0 < β + ε := by linarith
      have hz1_ne : riemannZeta₁ ((β + ε : ℝ) : ℂ) ≠ 0 := riemannZeta₁_ofReal_ne_zero_of_pos hb_pos
      have hzb_ne : (((β + ε : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hb_pos.ne'
      have hden_ne : ((β + ε : ℝ) : ℂ) * riemannZeta₁ ((β + ε : ℝ) : ℂ) ≠ 0 :=
        mul_ne_zero hzb_ne hz1_ne
      have hsub_ne : (((β + ε : ℝ) : ℂ) - (β : ℂ)) = (ε : ℂ) := by push_cast; ring
      have hM_eq : ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1) =
          H ((β + ε : ℝ) : ℂ) / (((β + ε : ℝ) : ℂ) * riemannZeta₁ ((β + ε : ℝ) : ℂ)) := by
        rw [← hid]
        field_simp [hden_ne]
      rw [hM_eq]
      dsimp [H]
      rw [hsub_ne]
      have hε_ne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
      field_simp [hden_ne, hε_ne]
    have htend_c : Tendsto
        (fun ε : ℝ => (C : ℂ) - (ε : ℂ) * M_init (β + ε : ℝ) -
          (ε : ℂ) * ((sgn : ℂ) * (((β + ε : ℝ) : ℂ) - 1)) /
            (((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (C : ℂ)) := by
      have h_lin : Tendsto (fun ε : ℝ => ((β + ε : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (β : ℂ)) := by
        have h : Continuous (fun ε : ℝ => ((β + ε : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
        simpa using ((h.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
      have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      have hM0 : Tendsto (fun ε : ℝ => (ε : ℂ) * M_init (β + ε : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 * M_init β)) :=
        hε0.mul (hM_init_diff.continuous.continuousAt.tendsto.comp h_lin)
      have hnum : Tendsto (fun ε : ℝ => (ε : ℂ) * ((sgn : ℂ) * (((β + ε : ℝ) : ℂ) - 1)))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 * ((sgn : ℂ) * ((β : ℂ) - 1)))) :=
        hε0.mul ((h_lin.sub tendsto_const_nhds).const_mul _)
      have hden : Tendsto (fun ε : ℝ => ((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 ((β : ℂ) * riemannZeta₁ β)) :=
        h_lin.mul (differentiable_riemannZeta₁.continuous.continuousAt.tendsto.comp h_lin)
      have hden_ne : (β : ℂ) * riemannZeta₁ β ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hre0.ne') (riemannZeta₁_ofReal_ne_zero_of_pos hre0)
      have hq : Tendsto (fun ε : ℝ =>
          (ε : ℂ) * ((sgn : ℂ) * (((β + ε : ℝ) : ℂ) - 1)) /
            (((β + ε : ℝ) : ℂ) * riemannZeta₁ (β + ε : ℝ)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hdiv := hnum.div hden hden_ne
        rw [Pi.div_def] at hdiv
        simpa using hdiv
      have hres := ((tendsto_const_nhds (x := (C : ℂ))).sub hM0).sub hq
      simpa using hres
    have htend_c' := htend_c.congr' (h_fn.mono fun _ h => h.symm)
    have htend_r := (Complex.continuous_re.continuousAt.tendsto.comp htend_c')
    refine htend_r.congr' ?_
    filter_upwards with ε
    simp
  have hne1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hre1; exact lt_irrefl 1 hre1
  have hρ_im_ne : ρ.im ≠ 0 := by
    intro him
    have hρ_real : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext rfl him
    have hneg := (riemannZeta_ofReal_neg_on_Ioo hre0 hre1).1
    rw [← hρ_real, hρ, Complex.zero_re] at hneg
    exact lt_irrefl 0 hneg
  have hρ_ne_β : ρ ≠ (β : ℂ) := by
    intro h; have := congrArg Complex.im h; simp [β] at this; exact hρ_im_ne this
  have h_lin : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa using (tendsto_const_nhds.add
      ((Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))))
  have h_id_prod : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
      (ε : ℂ) * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)) *
          ((ρ + ε) * (riemannZeta (ρ + ε) / ε)) =
        (ρ + ε) * riemannZeta (ρ + ε) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ) := by
    have hev_ne1 : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), ρ + (ε : ℂ) ≠ 1 :=
      h_lin.eventually_ne hne1
    filter_upwards [self_mem_nhdsWithin, hev_ne1] with ε hε hne1_ε
    rw [Set.mem_Ioi] at hε
    have hε_ne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    have hre : β < (ρ + (ε : ℂ)).re := by simp [β]; exact hε
    have hid := (hext.2 (ρ + ε) hre).2
    have hsub1 : (ρ + (ε : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr hne1_ε
    have hz1 : riemannZeta₁ (ρ + ε) = (ρ + ε - 1) * riemannZeta (ρ + ε) := by
      rw [riemannZeta_eq_inv_sub_mul hne1_ε]
      field_simp [hsub1]
    dsimp [H] at hid
    rw [hz1] at hid
    have hmul : (ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
          ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1) =
        (ρ + ε) * riemannZeta (ρ + ε) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ) := by
      have hid2 : (ρ + (ε : ℂ) - 1) * ((ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
            ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)) =
          (ρ + (ε : ℂ) - 1) *
            ((ρ + ε) * riemannZeta (ρ + ε) * ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ)) := by
        calc
          _ = (ρ + ε) * ((ρ + ε - 1) * riemannZeta (ρ + ε)) *
                ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1) := by ring
          _ = _ := hid
          _ = _ := by ring
      exact mul_left_cancel₀ hsub1 hid2
    calc
      (ε : ℂ) * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1)) *
            ((ρ + ε) * (riemannZeta (ρ + ε) / ε))
          = (ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
              ∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-(ρ + ε) - 1) := by
            field_simp [hε_ne]
      _ = _ := hmul
  have htend_slope : Tendsto (fun ε : ℝ => riemannZeta (ρ + (ε : ℂ)) / (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv riemannZeta ρ)) := by
    have hderiv : HasDerivAt riemannZeta (deriv riemannZeta ρ) ρ :=
      (analyticOn_riemannZeta ρ hne1).differentiableAt.hasDerivAt
    have hsl := hderiv.tendsto_slope_zero
    have hof : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hε).ne'
    have hcomp := hsl.comp hof
    refine hcomp.congr' ?_
    filter_upwards with ε
    simp [Function.comp_apply, hρ, smul_eq_mul, div_eq_inv_mul]
  have htend_factor : Tendsto
      (fun ε : ℝ => ‖(ρ + (ε : ℂ)) * (riemannZeta (ρ + ε) / ε)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖ρ * deriv riemannZeta ρ‖)) :=
    continuous_norm.continuousAt.tendsto.comp (h_lin.mul htend_slope)
  have htend_rhs_norm : Tendsto
      (fun ε : ℝ => ‖(ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
          ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖-(sgn : ℂ)‖)) := by
    have hzeta_cont : ContinuousAt riemannZeta ρ :=
      (analyticOn_riemannZeta ρ hne1).continuousAt
    have hsub_ne : ρ - (β : ℂ) ≠ 0 := sub_ne_zero.mpr hρ_ne_β
    have hsub_t : Tendsto (fun ε : ℝ => (C : ℂ) / (ρ + ε - β) - M_init (ρ + ε))
        (𝓝[>] (0 : ℝ)) (𝓝 ((C : ℂ) / (ρ - β) - M_init ρ)) :=
      ((tendsto_const_nhds.div (h_lin.sub tendsto_const_nhds) hsub_ne).sub
        (hM_init_diff.continuous.continuousAt.tendsto.comp h_lin))
    have hlim0 : Tendsto
        (fun ε : ℝ => (ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
          ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (ρ * 0 * ((C : ℂ) / (ρ - β) - M_init ρ) - (sgn : ℂ))) := by
      refine (((h_lin.mul ((hzeta_cont.tendsto.comp h_lin).trans_eq (congrArg 𝓝 hρ))).mul hsub_t).sub
        tendsto_const_nhds)
    have hlim0' : Tendsto
        (fun ε : ℝ => (ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
          ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(sgn : ℂ))) := by
      simpa using hlim0
    exact continuous_norm.continuousAt.tendsto.comp hlim0'
  have hnorm_sgn : ‖-(sgn : ℂ)‖ = 1 := by
    rcases hsgn with rfl | rfl <;> simp
  rw [hnorm_sgn] at htend_rhs_norm
  have hprod_le : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
      ‖(ρ + (ε : ℂ)) * riemannZeta (ρ + ε) *
          ((C : ℂ) / (ρ + ε - β) - M_init (ρ + ε)) - (sgn : ℂ)‖ ≤
        (ε * (∫ t in Set.Ioi X₀, (g t : ℂ) * (t : ℂ) ^ (-((β + ε : ℝ) : ℂ) - 1)).re) *
          ‖(ρ + (ε : ℂ)) * (riemannZeta (ρ + ε) / ε)‖ := by
    filter_upwards [self_mem_nhdsWithin, h_id_prod] with ε hε hid
    rw [Set.mem_Ioi] at hε
    rw [← hid, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM_bound ε hε) (norm_nonneg _)
  have hfinal := le_of_tendsto_of_tendsto htend_rhs_norm (hlim_rhs.mul htend_factor) hprod_le
  rw [norm_mul] at hfinal
  linarith

/-- **Unconditional Phragmén–Landau oscillation for `mertensM x` from a nontrivial zero.** -/
theorem mertensM_omega_plus_minus_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    ∃ c > 0,
      (∃ᶠ x in atTop, c * x ^ ρ.re < mertensM x) ∧
      (∃ᶠ x in atTop, mertensM x < -c * x ^ ρ.re) := by
  let c : ℝ := 1 / (2 * max 1 (‖ρ‖ * ‖deriv riemannZeta ρ‖))
  have hc : 0 < c := by positivity
  have hc_lt : c * (‖ρ‖ * ‖deriv riemannZeta ρ‖) < 1 := by
    dsimp [c]
    have hmax : ‖ρ‖ * ‖deriv riemannZeta ρ‖ ≤ max 1 (‖ρ‖ * ‖deriv riemannZeta ρ‖) := le_max_right _ _
    have hden : 0 < max 1 (‖ρ‖ * ‖deriv riemannZeta ρ‖) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    calc
      1 / (2 * max 1 (‖ρ‖ * ‖deriv riemannZeta ρ‖)) * (‖ρ‖ * ‖deriv riemannZeta ρ‖)
          ≤ 1 / (2 * max 1 (‖ρ‖ * ‖deriv riemannZeta ρ‖)) * max 1 (‖ρ‖ * ‖deriv riemannZeta ρ‖) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = 1 / 2 := by field_simp [hden.ne']
      _ < 1 := by norm_num
  refine ⟨c, hc, ?_, ?_⟩
  · by_contra hnot
    rw [Filter.not_frequently] at hnot
    exact mertensM_one_side hρ hre0 hre1 hc hc_lt 1 (Or.inl rfl)
      (hnot.mono fun _ h => by linarith)
  · by_contra hnot
    rw [Filter.not_frequently] at hnot
    exact mertensM_one_side hρ hre0 hre1 hc hc_lt (-1) (Or.inr rfl)
      (hnot.mono fun _ h => by linarith)

/-- **Unconditional `M(x) = Ω_±(x^(1/2))`.** -/
theorem mertensM_omega_half :
    ∃ c > 0,
      (∃ᶠ x in atTop, c * x ^ (1 / 2 : ℝ) ≤ mertensM x) ∧
      (∃ᶠ x in atTop, mertensM x ≤ -c * x ^ (1 / 2 : ℝ)) := by
  obtain ⟨ρ₀, hρ₀, hre_ge, hre_lt⟩ := exists_nontrivial_zero_re_ge_half
  have hre0 : 0 < ρ₀.re := lt_of_lt_of_le (by norm_num) hre_ge
  obtain ⟨c, hc, hplus, hminus⟩ := mertensM_omega_plus_minus_of_zero hρ₀ hre0 hre_lt
  refine ⟨c, hc, ?_, ?_⟩
  · refine (hplus.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro x ⟨hx, hx1⟩
    have hpow : x ^ (1 / 2 : ℝ) ≤ x ^ ρ₀.re := Real.rpow_le_rpow_of_exponent_le hx1 hre_ge
    linarith [mul_le_mul_of_nonneg_left hpow hc.le]
  · refine (hminus.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro x ⟨hx, hx1⟩
    have hpow : x ^ (1 / 2 : ℝ) ≤ x ^ ρ₀.re := Real.rpow_le_rpow_of_exponent_le hx1 hre_ge
    nlinarith [mul_le_mul_of_nonneg_left hpow hc.le]

/-- **Unconditional `M(x) = Ω_±(x^(zetaSupRe - ε))` for every `ε > 0` and constant `K`.** -/
theorem mertensM_omega_supRe :
    ∀ ε > 0, ∀ K : ℝ,
      (∃ᶠ x in atTop, K * x ^ (zetaSupRe - ε) ≤ mertensM x) ∧
      (∃ᶠ x in atTop, mertensM x ≤ -K * x ^ (zetaSupRe - ε)) := by
  intro ε hε K
  have hlt : zetaSupRe - ε < zetaSupRe := by linarith
  obtain ⟨σ, ⟨ρ, hρ, hre0, hre1, rfl⟩, hσ_gt⟩ := exists_lt_of_lt_csSup zetaZeroReSet_nonempty hlt
  obtain ⟨c, hc, hplus, hminus⟩ := mertensM_omega_plus_minus_of_zero hρ hre0 hre1
  have hdom : ∀ᶠ x in atTop, |K| * x ^ (zetaSupRe - ε) ≤ c * x ^ ρ.re := by
    have hpow_lim : Tendsto (fun x : ℝ => x ^ (ρ.re - (zetaSupRe - ε))) atTop atTop :=
      tendsto_rpow_atTop (by linarith)
    have hev_big := hpow_lim.eventually_ge_atTop (|K| / c)
    filter_upwards [hev_big, eventually_gt_atTop 0] with x hx hx0
    have hdiv : |K| ≤ c * x ^ (ρ.re - (zetaSupRe - ε)) := by
      have := mul_le_mul_of_nonneg_left hx hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    calc
      |K| * x ^ (zetaSupRe - ε) ≤ (c * x ^ (ρ.re - (zetaSupRe - ε))) * x ^ (zetaSupRe - ε) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_pos_of_pos hx0 _).le
      _ = c * (x ^ (ρ.re - (zetaSupRe - ε)) * x ^ (zetaSupRe - ε)) := by ring
      _ = c * x ^ ρ.re := by rw [← Real.rpow_add hx0]; ring_nf
  refine ⟨?_, ?_⟩
  · refine (hplus.and_eventually (hdom.and (eventually_gt_atTop 0))).mono ?_
    rintro x ⟨hx, hdx, hx0⟩
    have hK : K * x ^ (zetaSupRe - ε) ≤ |K| * x ^ (zetaSupRe - ε) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_pos_of_pos hx0 _).le
    linarith
  · refine (hminus.and_eventually (hdom.and (eventually_gt_atTop 0))).mono ?_
    rintro x ⟨hx, hdx, hx0⟩
    have hK : -(|K| * x ^ (zetaSupRe - ε)) ≤ -K * x ^ (zetaSupRe - ε) := by
      have h0 : 0 ≤ x ^ (zetaSupRe - ε) := (Real.rpow_pos_of_pos hx0 (zetaSupRe - ε)).le
      have hle := mul_le_mul_of_nonneg_right (neg_le_neg (le_abs_self K)) h0
      linarith
    linarith

end PsiMertensOmega


end AnalyticNumberTheory.PrimeDistribution
