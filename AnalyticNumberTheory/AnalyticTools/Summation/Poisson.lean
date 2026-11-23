import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Poisson Summation Formula

This file provides Poisson summation bridges and applications for analytic number theory:

- General Poisson summation bridges wrapping `Real.tsum_eq_tsum_fourier`,
  `Real.tsum_eq_tsum_fourier_of_rpow_decay`, and `SchwartzMap.tsum_eq_tsum_fourier`, together
  with `x = 0` specializations and lattice-scaling variants.
- Jacobi theta transformation identities for real (`t > 0`) and complex (`0 < Re z`) parameters,
  plus shifted theta transformations, bridging `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`.
- Poisson summation for compactly-supported `C^1` and smooth functions (using Parseval's identity
  on `[0, 1]` and integration by parts for `L^1`-summability of Fourier coefficients), together with
  finite-sum / finite-interval truncated Poisson summation identities on `[a, b]`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform ContDiff

namespace AnalyticNumberTheory.AnalyticTools.Summation

section GeneralPoissonBridges

/-- **Poisson summation formula** (general form), wrapping `Real.tsum_eq_tsum_fourier`. -/
theorem poisson_summation_general {f : C(ℝ, ℂ)}
    (h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier h_norm h_sum x

/-- **Poisson summation formula** at `x = 0` (general form). -/
theorem poisson_summation_general_zero {f : C(ℝ, ℂ)}
    (h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) :
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n := by
  simpa using poisson_summation_general h_norm h_sum 0

/-- **Poisson summation formula** under polynomial decay `O(|x| ^ (-b))` (`1 < b`) for both `f`
and `𝓕 f`. -/
theorem poisson_summation_rpow_decay {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier_of_rpow_decay hc hb hf hFf x

/-- **Poisson summation formula** at `x = 0` under polynomial decay `O(|x| ^ (-b))` (`1 < b`). -/
theorem poisson_summation_rpow_decay_zero {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) :
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n := by
  simpa using poisson_summation_rpow_decay hc hb hf hFf 0

/-- **Poisson summation formula** for Schwartz functions `f : SchwartzMap ℝ ℂ`. -/
theorem poisson_summation_schwartz (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f x

/-- **Poisson summation formula** at `x = 0` for Schwartz functions `f : SchwartzMap ℝ ℂ`. -/
theorem poisson_summation_schwartz_zero (f : SchwartzMap ℝ ℂ) :
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n := by
  simpa using poisson_summation_schwartz f 0

/-- Scaling identity for the 1D Fourier transform on `ℝ` (`L > 0`):
`𝓕 (fun u => f (L * u)) w = (L⁻¹ : ℂ) * 𝓕 f (w / L)`. -/
theorem fourier_scale_real (f : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (w : ℝ) :
    𝓕 (fun u : ℝ => f (L * u)) w = ((L⁻¹ : ℝ) : ℂ) * 𝓕 f (w / L) := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have h : ∀ u : ℝ, Complex.exp ((-2 * Real.pi * u * w : ℝ) * Complex.I) * f (L * u) =
      (fun y : ℝ => Complex.exp ((-2 * Real.pi * y * (w / L) : ℝ) * Complex.I) * f y) (L * u) := by
    intro u
    congr 3
    field_simp [hL.ne']
  simp_rw [h]
  rw [Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp ((-2 * Real.pi * y * (w / L) : ℝ) * Complex.I) * f y) L,
    Complex.real_smul, abs_inv, abs_of_pos hL]

private lemma tendsto_mul_cocompact {L : ℝ} (hL : 0 < L) :
    Tendsto (fun u : ℝ => L * u) (cocompact ℝ) (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
  have htop : Tendsto (fun u : ℝ => L * u) atTop atTop :=
    tendsto_id.const_mul_atTop hL
  have hbot : Tendsto (fun u : ℝ => L * u) atBot atBot := by
    simpa [Function.comp_def, mul_neg, neg_neg] using
      tendsto_neg_atTop_atBot.comp (htop.comp tendsto_neg_atBot_atTop)
  exact ⟨hbot.mono_right le_sup_left, htop.mono_right le_sup_right⟩

/-- Lattice-scaled Poisson summation for polynomial-decay functions (`L > 0`):
`∑' n : ℤ, f (x + L * n) = (L⁻¹ : ℂ) * ∑' n : ℤ, 𝓕 f (n / L) * fourier n ((x / L : ℝ) : UnitAddCircle)`. -/
theorem poisson_summation_scale_rpow_decay {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∑' n : ℤ, f (x + L * n) =
      ((L⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 f ((n : ℝ) / L) * fourier n ((x / L : ℝ) : UnitAddCircle) := by
  let g : ℝ → ℂ := fun u => f (L * u)
  have hg_cont : Continuous g := hc.comp (continuous_const.mul continuous_id)
  have hg_bd : g =O[cocompact ℝ] (|·| ^ (-b)) := by
    have h1 := hf.comp_tendsto (tendsto_mul_cocompact hL)
    have h2 : (fun u : ℝ => |L * u| ^ (-b)) =O[cocompact ℝ] (|·| ^ (-b)) := by
      refine IsBigO.of_bound (L ^ (-b)) (Eventually.of_forall fun u => ?_)
      rw [abs_mul, Real.mul_rpow (abs_nonneg L) (abs_nonneg u), abs_of_pos hL,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg (abs_nonneg u) _)),
        Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _)]
    exact h1.trans h2
  have hFg_bd : (𝓕 g) =O[cocompact ℝ] (|·| ^ (-b)) := by
    have hEq : 𝓕 g = fun w : ℝ => ((L⁻¹ : ℝ) : ℂ) * 𝓕 f (L⁻¹ * w) := by
      ext w
      rw [fourier_scale_real f hL w, div_eq_inv_mul]
    rw [hEq]
    have hL_inv : 0 < L⁻¹ := inv_pos.mpr hL
    have h1 := (hFf.comp_tendsto (tendsto_mul_cocompact hL_inv)).const_mul_left ((L⁻¹ : ℝ) : ℂ)
    have h2 : (fun w : ℝ => |L⁻¹ * w| ^ (-b)) =O[cocompact ℝ] (|·| ^ (-b)) := by
      refine IsBigO.of_bound ((L⁻¹) ^ (-b)) (Eventually.of_forall fun w => ?_)
      rw [abs_mul, Real.mul_rpow (abs_nonneg L⁻¹) (abs_nonneg w), abs_of_pos hL_inv,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hL_inv.le _) (Real.rpow_nonneg (abs_nonneg w) _)),
        Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _)]
    exact h1.trans h2
  have hps := Real.tsum_eq_tsum_fourier_of_rpow_decay hg_cont hb hg_bd hFg_bd (x / L)
  have hlhs : (∑' n : ℤ, g (x / L + n)) = ∑' n : ℤ, f (x + L * n) := by
    refine tsum_congr fun n => ?_
    simp only [g]
    congr 1
    field_simp [hL.ne']
  have hrhs : (∑' n : ℤ, 𝓕 g n * fourier n ((x / L : ℝ) : UnitAddCircle)) =
      ((L⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 f ((n : ℝ) / L) * fourier n ((x / L : ℝ) : UnitAddCircle) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [fourier_scale_real f hL n, mul_assoc]
  rw [← hlhs, ← hrhs]
  exact hps

/-- Lattice-scaled Poisson summation at `x = 0` for polynomial-decay functions (`L > 0`). -/
theorem poisson_summation_scale_rpow_decay_zero {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) {L : ℝ} (hL : 0 < L) :
    ∑' n : ℤ, f (L * n) = ((L⁻¹ : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 f ((n : ℝ) / L) := by
  simpa using poisson_summation_scale_rpow_decay hc hb hf hFf hL 0

end GeneralPoissonBridges

section JacobiTheta

/-- Real Jacobi theta series `θ(t) = ∑' n : ℤ, exp (-π * t * n²)` (`t > 0`). -/
def jacobiTheta (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)

/-- Complex Jacobi theta series `θ(z) = ∑' n : ℤ, cexp (-π * z * n²)` (`0 < z.re`). -/
def jacobiThetaComplex (z : ℂ) : ℂ :=
  ∑' n : ℤ, Complex.exp (-Real.pi * z * (n : ℂ) ^ 2)

private lemma summable_int_sq_inv : Summable fun n : ℤ => ((n : ℝ) ^ 2)⁻¹ := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · simp [Real.summable_nat_pow_inv.mpr one_lt_two]
  · simp [Real.summable_nat_pow_inv.mpr one_lt_two]

/-- Summability of the real Jacobi theta series for `t > 0`. -/
theorem jacobiTheta_summable {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2) := by
  have hzero : Summable fun n : ℤ => if n = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [hn]
  have hdom : Summable fun n : ℤ => (Real.pi * t)⁻¹ * ((n : ℝ) ^ 2)⁻¹ + if n = 0 then (1 : ℝ) else 0 :=
    (summable_int_sq_inv.mul_left _).add hzero
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hdom
  by_cases hn : n = 0
  · subst hn
    simp
  · have hpos : 0 < Real.pi * t * (n : ℝ) ^ 2 := by
      have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
      positivity
    have hle : Real.pi * t * (n : ℝ) ^ 2 ≤ Real.exp (Real.pi * t * (n : ℝ) ^ 2) := by
      linarith [Real.add_one_le_exp (Real.pi * t * (n : ℝ) ^ 2)]
    have hinv : Real.exp (-Real.pi * t * (n : ℝ) ^ 2) ≤ (Real.pi * t * (n : ℝ) ^ 2)⁻¹ := by
      have heq : -Real.pi * t * (n : ℝ) ^ 2 = -(Real.pi * t * (n : ℝ) ^ 2) := by ring
      rw [heq, Real.exp_neg]
      exact (inv_anti₀ hpos hle)
    simp only [hn, ite_false, add_zero]
    rw [mul_inv] at hinv
    exact hinv

/-- Summability of the complex Jacobi theta series for `0 < z.re`. -/
theorem jacobiThetaComplex_summable {z : ℂ} (hz : 0 < z.re) :
    Summable fun n : ℤ => Complex.exp (-Real.pi * z * (n : ℂ) ^ 2) := by
  refine Summable.of_norm ?_
  have hnorm : (fun n : ℤ => ‖Complex.exp (-Real.pi * z * (n : ℂ) ^ 2)‖) =
      fun n : ℤ => Real.exp (-Real.pi * z.re * (n : ℝ) ^ 2) := by
    ext n
    rw [Complex.norm_exp]
    congr 1
    have hcast : (-Real.pi * z * (n : ℂ) ^ 2) =
        ((-Real.pi * ((n : ℝ) ^ 2 : ℝ) : ℝ) : ℂ) * z := by
      push_cast
      ring
    rw [hcast, Complex.re_ofReal_mul]
    ring
  rw [hnorm]
  exact jacobiTheta_summable hz

/-- Compatibility between the real and complex Jacobi theta functions. -/
theorem jacobiTheta_eq_jacobiThetaComplex (t : ℝ) :
    (jacobiTheta t : ℂ) = jacobiThetaComplex t := by
  simp only [jacobiTheta, jacobiThetaComplex, Complex.ofReal_tsum, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_intCast]

/-- Positivity of `jacobiTheta t` for `t > 0`. -/
theorem jacobiTheta_pos {t : ℝ} (ht : 0 < t) : 0 < jacobiTheta t := by
  refine Summable.tsum_pos (jacobiTheta_summable ht) (fun _ => (Real.exp_pos _).le) 0 ?_
  simp

/-- **Jacobi theta transformation identity** (real parameter `t > 0`):
`∑' n : ℤ, Real.exp (-π * t * n²) = t ^ (-1 / 2) * ∑' n : ℤ, Real.exp (-π * n² / t)`. -/
theorem jacobiTheta_transformation {t : ℝ} (ht : 0 < t) :
    jacobiTheta t = t ^ (-(1 / 2 : ℝ)) * jacobiTheta t⁻¹ := by
  have h := Real.tsum_exp_neg_mul_int_sq ht
  simp only [jacobiTheta]
  rw [h, Real.rpow_neg ht.le, one_div]
  congr 1

/-- **Jacobi theta transformation identity** (complex parameter `0 < z.re`):
`jacobiThetaComplex z = (1 / z ^ (1 / 2 : ℂ)) * jacobiThetaComplex (1 / z)`. -/
theorem jacobiTheta_transformation_complex {z : ℂ} (hz : 0 < z.re) :
    jacobiThetaComplex z = 1 / z ^ (1 / 2 : ℂ) * jacobiThetaComplex (1 / z) := by
  simpa only [jacobiThetaComplex, div_eq_mul_inv, one_mul] using
    Complex.tsum_exp_neg_mul_int_sq hz

/-- **Shifted Jacobi theta transformation identity** for `0 < z.re` and shift `w : ℂ`,
bridging `Complex.tsum_exp_neg_quadratic`. -/
theorem jacobiTheta_shifted_transformation {z : ℂ} (hz : 0 < z.re) (w : ℂ) :
    (∑' n : ℤ, Complex.exp (-Real.pi * z * (n : ℂ) ^ 2 + 2 * Real.pi * w * n)) =
      1 / z ^ (1 / 2 : ℂ) * ∑' n : ℤ, Complex.exp (-Real.pi / z * ((n : ℂ) + Complex.I * w) ^ 2) :=
  Complex.tsum_exp_neg_quadratic hz w

end JacobiTheta

section CompactSupportAndTruncatedPoisson

private lemma compactSupport_bound {E : Type*} [Zero E] {f : ℝ → E}
    (hf : HasCompactSupport f) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  by_contra hne
  have hmem : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have hle : |x| ≤ R := by simpa [Metric.mem_closedBall, Real.dist_eq] using hR hmem
  exact absurd hx (not_lt.mpr (hle.trans (le_max_left _ _)))

private lemma compactSupport_deriv_eq_zero_of_bound {f f' : ℝ → ℂ} {R : ℝ}
    (hR : ∀ x : ℝ, R < |x| → f x = 0) (hf : ∀ x : ℝ, HasDerivAt f (f' x) x)
    {y : ℝ} (hy : R < |y|) : f' y = 0 := by
  have hopen : IsOpen {z : ℝ | R < |z|} := isOpen_lt continuous_const continuous_abs
  have hev : f =ᶠ[𝓝 y] fun _ => (0 : ℂ) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) fun z hz => hR z hz
  have h0 : HasDerivAt f 0 y := (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq hev
  exact (hf y).unique h0

private lemma compactSupport_locally_summable_norm {f : C(ℝ, ℂ)} (hf : HasCompactSupport f)
    (K : TopologicalSpace.Compacts ℝ) :
    Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖ := by
  obtain ⟨R, hR0, hR⟩ := compactSupport_bound hf
  obtain ⟨M, hM⟩ := K.isCompact.isBounded.subset_closedBall 0
  let M' : ℝ := max M 0
  let N : ℤ := ⌈M' + R⌉
  refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun n hn => ?_
  have hn_gt : M' + R < |(n : ℝ)| := by
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    by_cases hneg : n < -N
    · have h1 : (⌈M' + R⌉ : ℝ) < -(n : ℝ) := by
        have hlt : N < -n := by omega
        exact_mod_cast hlt
      have h2 : M' + R < -(n : ℝ) := (Int.le_ceil (M' + R)).trans_lt h1
      exact h2.trans_le (neg_le_abs _)
    · have hlt : N < n := hn (not_lt.mp hneg)
      have h1 : (⌈M' + R⌉ : ℝ) < (n : ℝ) := by exact_mod_cast hlt
      have h2 : M' + R < (n : ℝ) := (Int.le_ceil (M' + R)).trans_lt h1
      exact h2.trans_le (le_abs_self _)
  have hzero : (f.comp <| ContinuousMap.addRight n).restrict K = 0 := by
    ext x
    have hxM : |(x : ℝ)| ≤ M' := by
      have hmem : (x : ℝ) ∈ Metric.closedBall (0 : ℝ) M := hM x.2
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
      exact hmem.trans (le_max_left _ _)
    have hxn : R < |(x : ℝ) + n| := by
      have htri : |(n : ℝ)| ≤ |(x : ℝ) + n| + |(x : ℝ)| := by
        calc |(n : ℝ)| = |((x : ℝ) + n) - x| := by ring_nf
          _ ≤ |(x : ℝ) + n| + |(x : ℝ)| := abs_sub _ _
      linarith
    exact hR ((x : ℝ) + n) hxn
  rw [hzero, norm_zero]

/-- **Poisson summation formula for compactly-supported `C^1` functions**:
if `f : ℝ → ℂ` has compact support and continuous derivative `f'`, then `∑' n : ℤ, 𝓕 f n`
converges and `∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)`. -/
theorem poisson_summation_compactSupport_c1 {f f' : ℝ → ℂ} (hf_supp : HasCompactSupport f)
    (hf_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf'_cont : Continuous f') (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) := by
  let f_cmap : C(ℝ, ℂ) := ⟨f, continuous_iff_continuousAt.mpr fun z => (hf_deriv z).continuousAt⟩
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(f_cmap.comp <| ContinuousMap.addRight n).restrict K‖ :=
    compactSupport_locally_summable_norm hf_supp
  obtain ⟨R, hR0, hR⟩ := compactSupport_bound hf_supp
  let N : ℤ := ⌈R + 2⌉
  let S : Finset ℤ := Finset.Icc (-N) N
  let F : ℝ → ℂ := fun y => ∑' n : ℤ, f (y + n)
  let F' : ℝ → ℂ := fun y => ∑' n : ℤ, f' (y + n)
  have h_out : ∀ y ∈ Set.Icc (-1 : ℝ) 2, ∀ n : ℤ, n ∉ S →
      f (y + n) = 0 ∧ f' (y + n) = 0 := by
    intro y hy n hn
    have hy_bd : |y| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hy.1], hy.2⟩
    have hn_gt : R + 2 < |(n : ℝ)| := by
      simp only [S, Finset.mem_Icc, not_and, not_le] at hn
      by_cases hneg : n < -N
      · have h1 : (⌈R + 2⌉ : ℝ) < -(n : ℝ) := by
          have hlt : N < -n := by omega
          exact_mod_cast hlt
        exact ((Int.le_ceil (R + 2)).trans_lt h1).trans_le (neg_le_abs _)
      · have hlt : N < n := hn (not_lt.mp hneg)
        have h1 : (⌈R + 2⌉ : ℝ) < (n : ℝ) := by exact_mod_cast hlt
        exact ((Int.le_ceil (R + 2)).trans_lt h1).trans_le (le_abs_self _)
    have hyn : R < |y + n| := by
      have htri : |(n : ℝ)| ≤ |y + n| + |y| := by
        calc |(n : ℝ)| = |(y + n) - y| := by ring_nf
          _ ≤ |y + n| + |y| := abs_sub _ _
      linarith
    exact ⟨hR (y + n) hyn, compactSupport_deriv_eq_zero_of_bound hR hf_deriv hyn⟩
  have hF_eq : ∀ y ∈ Set.Icc (-1 : ℝ) 2, F y = ∑ n ∈ S, f (y + n) := by
    intro y hy
    exact tsum_eq_sum fun n hn => (h_out y hy n hn).1
  have hF'_eq : ∀ y ∈ Set.Icc (-1 : ℝ) 2, F' y = ∑ n ∈ S, f' (y + n) := by
    intro y hy
    exact tsum_eq_sum fun n hn => (h_out y hy n hn).2
  have hF_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    have hy_ioo : y ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hsum_deriv : HasDerivAt (fun z : ℝ => ∑ n ∈ S, f (z + n)) (∑ n ∈ S, f' (y + n)) y := by
      refine HasDerivAt.fun_sum fun n _ => ?_
      have hd := hf_deriv (y + n)
      have hadd : HasDerivAt (fun z : ℝ => z + (n : ℝ)) 1 y := (hasDerivAt_id' y).add_const (n : ℝ)
      have hc := hd.scomp y hadd
      simpa only [Function.comp_def, one_smul] using hc
    have hev : F =ᶠ[𝓝 y] fun z : ℝ => ∑ n ∈ S, f (z + n) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy_ioo) fun z hz =>
        hF_eq z (Set.Ioo_subset_Icc_self hz)
    rw [hF'_eq y ⟨by linarith [hy.1], by linarith [hy.2]⟩]
    exact hsum_deriv.congr_of_eventuallyEq hev
  have hF'_cont : ContinuousOn F' (Set.Icc (0 : ℝ) 1) := by
    have hsum_cont : Continuous fun z : ℝ => ∑ n ∈ S, f' (z + n) := by
      induction S using Finset.induction with
      | empty => simpa using continuous_const
      | @insert m s hms ih =>
        simp_rw [Finset.sum_insert hms]
        exact (hf'_cont.comp (continuous_id.add continuous_const)).add ih
    exact hsum_cont.continuousOn.congr fun z hz =>
      hF'_eq z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hF'_int : IntervalIntegrable F' volume 0 1 :=
    hF'_cont.intervalIntegrable_of_Icc zero_le_one
  have hF10 : F 1 = F 0 := by
    have hshift : (∑' n : ℤ, f (1 + (n : ℝ))) = ∑' n : ℤ, f (0 + ((n + 1 : ℤ) : ℝ)) := by
      refine tsum_congr fun n => ?_
      push_cast
      ring_nf
    simp only [F]
    rw [hshift]
    exact (Equiv.addRight (1 : ℤ)).tsum_eq fun m : ℤ => f (0 + (m : ℝ))
  have hcoeff_eq : ∀ n : ℤ, fourierCoeffOn zero_lt_one F n = 𝓕 f n := by
    intro n
    have h1 : fourierCoeff (Function.Periodic.lift <| f_cmap.periodic_tsum_comp_add_zsmul 1) n =
        𝓕 f n := Real.fourierCoeff_tsum_comp_add h_norm n
    rw [← h1, fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    simp_rw [smul_eq_mul, fourier_coe_apply]
    simp only [sub_zero, div_one, Complex.ofReal_one]
    congr 1
    refine intervalIntegral.integral_congr fun z _ => ?_
    have hz_val : (Function.Periodic.lift <| f_cmap.periodic_tsum_comp_add_zsmul 1)
        (z : UnitAddCircle) = F z := by
      rw [Function.Periodic.lift_coe]
      simp only [zsmul_one]
      rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm h_norm)]
      rfl
    rw [hz_val]
  have hF'_L2 : MemLp F' 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'_cont
    have hmeas : AEStronglyMeasurable F' (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hF'_cont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    exact MemLp.of_bound hmeas C
      ((ae_restrict_mem measurableSet_Ioc).mono fun z hz => hC z (Set.Ioc_subset_Icc_self hz))
  have hparseval : Summable fun n : ℤ => ‖fourierCoeffOn zero_lt_one F' n‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn zero_lt_one hF'_L2).summable
  have h_sum_norm : Summable fun n : ℤ => ‖𝓕 f n‖ := by
    have hzero : Summable fun n : ℤ => if n = 0 then ‖𝓕 f 0‖ else 0 :=
      summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) fun n hn => by
        simp only [Finset.mem_singleton] at hn
        simp [hn]
    have hdom : Summable fun n : ℤ =>
        (4 * Real.pi)⁻¹ * (((n : ℝ) ^ 2)⁻¹ + ‖fourierCoeffOn zero_lt_one F' n‖ ^ 2) +
          if n = 0 then ‖𝓕 f 0‖ else 0 :=
      ((summable_int_sq_inv.add hparseval).mul_left _).add hzero
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hdom
    by_cases hn : n = 0
    · subst hn
      have hpos1 : 0 ≤ (4 * Real.pi)⁻¹ * ((((0 : ℤ) : ℝ) ^ 2)⁻¹ +
          ‖fourierCoeffOn zero_lt_one F' 0‖ ^ 2) := by positivity
      have hif : (if (0 : ℤ) = 0 then ‖𝓕 f 0‖ else 0) = ‖𝓕 f 0‖ := rfl
      rw [hif]
      exact le_add_of_nonneg_left hpos1
    · have hibp := fourierCoeffOn_of_hasDerivAt zero_lt_one hn hF_deriv hF'_int
      simp only [hF10, sub_self, mul_zero, zero_sub, Complex.ofReal_one, Complex.ofReal_zero,
        sub_zero, one_mul] at hibp
      rw [← hcoeff_eq n, hibp, norm_mul, norm_neg]
      have hdenom : ‖(1 : ℂ) / (-2 * Real.pi * Complex.I * n)‖ =
          (2 * Real.pi * |(n : ℝ)|)⁻¹ := by
        rw [one_div, norm_inv, norm_mul, norm_mul, norm_mul, norm_neg,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]
      rw [hdenom]
      have hpi : 0 < 2 * Real.pi := by positivity
      have ham : |(n : ℝ)|⁻¹ * ‖fourierCoeffOn zero_lt_one F' n‖ ≤
          2⁻¹ * (((n : ℝ) ^ 2)⁻¹ + ‖fourierCoeffOn zero_lt_one F' n‖ ^ 2) := by
        have hsq : 0 ≤ (|(n : ℝ)|⁻¹ - ‖fourierCoeffOn zero_lt_one F' n‖) ^ 2 := sq_nonneg _
        have hsq_id : (|(n : ℝ)|⁻¹) ^ 2 = ((n : ℝ) ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
        nlinarith [hsq, hsq_id]
      calc (2 * Real.pi * |(n : ℝ)|)⁻¹ * ‖fourierCoeffOn zero_lt_one F' n‖
          = (2 * Real.pi)⁻¹ * (|(n : ℝ)|⁻¹ * ‖fourierCoeffOn zero_lt_one F' n‖) := by
              rw [mul_inv]; ring
        _ ≤ (2 * Real.pi)⁻¹ * (2⁻¹ * (((n : ℝ) ^ 2)⁻¹ + ‖fourierCoeffOn zero_lt_one F' n‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left ham (inv_nonneg.mpr hpi.le)
        _ = (4 * Real.pi)⁻¹ * (((n : ℝ) ^ 2)⁻¹ + ‖fourierCoeffOn zero_lt_one F' n‖ ^ 2) +
              if n = 0 then ‖𝓕 f 0‖ else 0 := by
              simp only [hn, ite_false, add_zero]
              ring
  have h_sum : Summable fun n : ℤ => 𝓕 (f_cmap : ℝ → ℂ) n := h_sum_norm.of_norm
  exact Real.tsum_eq_tsum_fourier h_norm h_sum x

/-- **Poisson summation formula at `x = 0` for compactly-supported `C^1` functions**. -/
theorem poisson_summation_compactSupport_c1_zero {f f' : ℝ → ℂ} (hf_supp : HasCompactSupport f)
    (hf_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf'_cont : Continuous f') :
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n := by
  simpa using poisson_summation_compactSupport_c1 hf_supp hf_deriv hf'_cont 0

/-- **Poisson summation formula for compactly-supported smooth functions** (`ContDiff ℝ n f`,
`1 ≤ n`). -/
theorem poisson_summation_compactSupport_smooth {n : ℕ∞} (hn : 1 ≤ n) {f : ℝ → ℂ}
    (hf_supp : HasCompactSupport f) (hf_diff : ContDiff ℝ n f) (x : ℝ) :
    ∑' k : ℤ, f (x + k) = ∑' k : ℤ, 𝓕 f k * fourier k (x : UnitAddCircle) := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hd : Differentiable ℝ f := hf_diff.differentiable hn0
  have hf_deriv : ∀ z : ℝ, HasDerivAt f (deriv f z) z := fun z => (hd z).hasDerivAt
  have hf'_cont : Continuous (deriv f) := hf_diff.continuous_deriv hn1
  exact poisson_summation_compactSupport_c1 hf_supp hf_deriv hf'_cont x

/-- **Truncated Poisson summation formula** for a `C^1` function `f : ℝ → ℂ` supported inside a
compact interval `[a, b]` (`a ≤ b`):
`∑ n ∈ Finset.Icc ⌈a - x⌉ ⌊b - x⌋, f (x + n) =`
`∑' n : ℤ, (∫ t in a..b, Complex.exp ((-2 * π * t * n : ℝ) * I) * f t) * fourier n (x : UnitAddCircle)`. -/
theorem poisson_summation_compactSupport_truncated {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℂ}
    (hf_supp : ∀ t ∉ Set.Icc a b, f t = 0) (hf_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hf'_cont : Continuous f') (x : ℝ) :
    ∑ n ∈ Finset.Icc ⌈a - x⌉ ⌊b - x⌋, f (x + n) =
      ∑' n : ℤ, (∫ t in a..b, Complex.exp ((-2 * Real.pi * t * n : ℝ) * Complex.I) * f t) *
        fourier n (x : UnitAddCircle) := by
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun t ht => by
      by_contra hnot
      exact ht (hf_supp t hnot)
  have hps := poisson_summation_compactSupport_c1 hcs hf_deriv hf'_cont x
  have hlhs : ∑' n : ℤ, f (x + n) = ∑ n ∈ Finset.Icc ⌈a - x⌉ ⌊b - x⌋, f (x + n) := by
    refine tsum_eq_sum fun n hn => ?_
    refine hf_supp (x + n) fun hmem => hn ?_
    simp only [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (by linarith [hmem.1]), Int.le_floor.mpr (by linarith [hmem.2])⟩
  have hrhs : ∀ n : ℤ,
      𝓕 f n = ∫ t in a..b, Complex.exp ((-2 * Real.pi * t * n : ℝ) * Complex.I) * f t := by
    intro n
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
    have hint_eq :
        ∫ v : ℝ, Complex.exp ((-2 * Real.pi * v * (n : ℝ) : ℝ) * Complex.I) * f v =
          ∫ v in Set.Icc a b,
            Complex.exp ((-2 * Real.pi * v * (n : ℝ) : ℝ) * Complex.I) * f v := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
      rw [hf_supp v hv, mul_zero]
    rw [hint_eq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [← hlhs]
  simpa only [hrhs] using hps

/-- **Truncated Poisson summation formula at `x = 0`** for a `C^1` function supported inside
`[a, b]` (`a ≤ b`):
`∑ n ∈ Finset.Icc ⌈a⌉ ⌊b⌋, f n = ∑' n : ℤ, ∫ t in a..b, cexp ((-2 * π * t * n : ℝ) * I) * f t`. -/
theorem poisson_summation_compactSupport_truncated_zero {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℂ}
    (hf_supp : ∀ t ∉ Set.Icc a b, f t = 0) (hf_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hf'_cont : Continuous f') :
    ∑ n ∈ Finset.Icc ⌈a⌉ ⌊b⌋, f n =
      ∑' n : ℤ, ∫ t in a..b, Complex.exp ((-2 * Real.pi * t * n : ℝ) * Complex.I) * f t := by
  simpa only [sub_zero, zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] using
    poisson_summation_compactSupport_truncated hab hf_supp hf_deriv hf'_cont 0

end CompactSupportAndTruncatedPoisson

end AnalyticNumberTheory.AnalyticTools.Summation
