import AnalyticNumberTheory.ModularAndPartitions.DedekindEta
import AnalyticNumberTheory.ModularAndPartitions.Partitions
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Modular inversion of the partition generating function

Writing the nome as `exp(-2πz)` sends the upper half-plane to the right
half-plane. Dedekind eta inversion exchanges `z` with `1/z` and isolates
the exponential growth at the principal cusp.
-/

open Complex Filter Real Set
open scoped Topology Asymptotics

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The nome at the upper-half-plane parameter `i z`. -/
noncomputable def partitionNome (z : ℂ) : ℂ := Complex.exp (-2 * (π : ℂ) * z)

theorem norm_partitionNome (z : ℂ) : ‖partitionNome z‖ = Real.exp (-2 * π * z.re) := by
  rw [partitionNome, Complex.norm_exp]
  congr 1
  simp

theorem norm_partitionNome_lt_one {z : ℂ} (hz : 0 < z.re) : ‖partitionNome z‖ < 1 := by
  rw [norm_partitionNome, Real.exp_lt_one_iff]
  nlinarith [mul_pos Real.pi_pos hz]

/-- Inside any closed disk of radius strictly below one the generating series is continuous. -/
theorem continuousOn_partitionGenFun_closedBall {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ContinuousOn partitionGenFun (Metric.closedBall 0 r) := by
  have hseries := continuousOn_tsum (f := fun n (z : ℂ) => (partitionCount n : ℂ) * z ^ n)
    (s := Metric.closedBall 0 r) (fun n => (continuous_const.mul (continuous_id.pow n)).continuousOn)
    (summable_partitionCount_mul_pow_real hr0 hr) (fun n z hz => by
      rw [norm_mul, Complex.norm_natCast, norm_pow]
      gcongr
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  apply hseries.congr
  intro z hz
  exact (tsum_partitionCount_mul_pow (lt_of_le_of_lt (by simpa using hz) hr)).symm

@[simp] theorem partitionGenFun_zero : partitionGenFun 0 = 1 := by
  simp [partitionGenFun]

theorem tendsto_partitionGenFun_zero : Tendsto partitionGenFun (𝓝 0) (𝓝 1) := by
  have h := (continuousOn_partitionGenFun_closedBall (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).continuousAt
    (Metric.closedBall_mem_nhds _ (by norm_num))
  simpa [ContinuousAt] using h

/-- Euler's partition product cancels the product part of Dedekind's eta function. -/
theorem eta_mul_partitionGenFun_nome {z : ℂ} (hz : 0 < z.re) :
    ModularForm.eta (I * z) * partitionGenFun (partitionNome z) =
      Complex.exp (-(π : ℂ) * z / 12) := by
  have hi : I * I = -1 := Complex.I_mul_I
  rw [eta_eq_cexp_mul_tprod]
  have h1 : (π : ℂ) * I * (I * z) / 12 = -π * z / 12 := by linear_combination (π*z/12)*hi
  have hq (m : ℕ) : Complex.exp (2 * π * I * ((m : ℂ)+1) * (I*z)) =
      partitionNome z ^ (m+1) := by
    rw [partitionNome, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    linear_combination (2*π*(m+1)*z)*hi
  simp_rw [h1, hq]
  rw [partitionGenFun, mul_assoc, mul_inv_cancel₀ (tprod_one_sub_pow_ne_zero (norm_partitionNome_lt_one hz)), mul_one]

/-- Exact modular inversion at the principal cusp, with the principal complex square root. -/
theorem partitionGenFun_nome_inversion {z : ℂ} (hz : 0 < z.re) :
    partitionGenFun (partitionNome z) = z ^ (1/2 : ℂ) *
      Complex.exp ((π : ℂ)/12 * (z⁻¹-z)) * partitionGenFun (partitionNome z⁻¹) := by
  have hzi : 0 < z⁻¹.re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr (fun he => by simp [he] at hz))
  let τ : UpperHalfPlane := ⟨I*z, by simpa using hz⟩
  have hinv := eta_inv τ
  change ModularForm.eta (-(I*z)⁻¹) = (-I*(I*z)) ^ (1/2 : ℂ) * ModularForm.eta (I*z) at hinv
  rw [show -(I*z)⁻¹ = I*z⁻¹ by rw [mul_inv_rev, Complex.inv_I]; ring,
    show -I*(I*z) = z by rw [neg_mul, ← mul_assoc, Complex.I_mul_I]; ring] at hinv
  have h := eta_mul_partitionGenFun_nome hzi
  rw [hinv] at h
  have hη : ModularForm.eta (I*z) ≠ 0 := eta_ne_zero_of_im_pos (by simpa using hz)
  apply mul_left_cancel₀ hη
  rw [eta_mul_partitionGenFun_nome hz]
  calc _ = Complex.exp ((π : ℂ)/12*(z⁻¹-z)) * Complex.exp (-π*z⁻¹/12) := by
           rw [← Complex.exp_add]; congr 1; ring
       _ = _ := by rw [← h]; ring

/-- Radial evaluation of the complex nome. -/
theorem partitionNome_ofReal (y : ℝ) : partitionNome y = (Real.exp (-2 * π * y) : ℝ) := by
  rw [partitionNome, Complex.ofReal_exp]
  push_cast
  rfl

theorem partitionGenFun_nome_ofReal {y : ℝ} (hy : 0 < y) :
    partitionGenFun (partitionNome y) = (partitionGenFunReal (Real.exp (-2 * π * y)) : ℝ) := by
  rw [partitionNome_ofReal]
  apply partitionGenFun_ofReal
  rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  nlinarith [mul_pos Real.pi_pos hy]

/-- Comparison with a positive radial value uniformly on a closed disk. -/
theorem norm_partitionGenFun_le_of_norm_le {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < 1) :
    ‖partitionGenFun z‖ ≤ partitionGenFunReal r := by
  have hr0 := (norm_nonneg z).trans hz
  rw [partitionGenFun, partitionGenFunReal, ← tsum_partitionCount_mul_pow (hz.trans_lt hr),
    ← tsum_partitionCount_mul_pow_real (by rwa [abs_of_nonneg hr0])]
  apply (norm_tsum_le_tsum_norm (summable_norm_partitionCount_mul_pow (hz.trans_lt hr))).trans
  apply Summable.tsum_le_tsum _ (summable_norm_partitionCount_mul_pow (hz.trans_lt hr))
    (summable_partitionCount_mul_pow_real hr0 hr)
  intro n
  rw [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr

/-- A dual nome stays in a fixed compact subdisk when the real part of its parameter is bounded below. -/
theorem norm_partitionGenFun_nome_le {z : ℂ} {a : ℝ} (ha : 0 < a) (hz : a ≤ z.re) :
    ‖partitionGenFun (partitionNome z)‖ ≤ partitionGenFunReal (Real.exp (-2*π*a)) := by
  apply norm_partitionGenFun_le_of_norm_le
  · rw [norm_partitionNome, Real.exp_le_exp]
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hz)]
  · rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos Real.pi_pos ha]

/-- At the principal cusp the transformed product tends to one. -/
theorem tendsto_partitionGenFun_nome_of_re_atTop {ι : Type*} {l : Filter ι} {z : ι → ℂ}
    (hz : Tendsto (fun i => (z i).re) l atTop) :
    Tendsto (fun i => partitionGenFun (partitionNome (z i))) l (𝓝 1) := by
  apply tendsto_partitionGenFun_zero.comp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [norm_partitionNome]
  exact Real.tendsto_exp_atBot.comp (hz.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos] : -2*π < 0))

/-- The positive real form of the modular transformation. -/
theorem partitionGenFunReal_inversion {y : ℝ} (hy : 0 < y) :
    partitionGenFunReal (Real.exp (-2*π*y)) =
      √y * Real.exp (π/12 * (y⁻¹-y)) * partitionGenFunReal (Real.exp (-2*π*y⁻¹)) := by
  apply Complex.ofReal_injective
  push_cast
  rw [← partitionGenFun_nome_ofReal hy, ← partitionGenFun_nome_ofReal (inv_pos.mpr hy),
    partitionGenFun_nome_inversion (by simpa using hy)]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
  push_cast
  rfl

/-- The radial generating function has leading term
`√y exp(π/(12y))` as `y` decreases to zero. -/
theorem partitionGenFunReal_radial_isEquivalent :
    (fun y : ℝ => partitionGenFunReal (Real.exp (-2*π*y))) ~[𝓝[>] 0]
      (fun y => √y * Real.exp (π/(12*y))) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hF := tendsto_partitionGenFun_nome_of_re_atTop (z := fun y : ℝ => ((y⁻¹ : ℝ) : ℂ))
    (l := 𝓝[>] 0) (by simpa using tendsto_inv_nhdsGT_zero)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hF
  have hE : Tendsto (fun y : ℝ => Real.exp (-π/12*y)) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous (fun y : ℝ => Real.exp (-π/12*y)) := by fun_prop
    simpa using h.continuousAt.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  have h := hE.mul hreal
  simp only [Complex.one_re, mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < y := hy
  dsimp
  rw [partitionGenFunReal_inversion hy', partitionGenFun_nome_ofReal (inv_pos.mpr hy')]
  simp only [Complex.ofReal_re]
  rw [show π / 12 * (y⁻¹-y) = π/(12*y) + (-π/12*y) by ring, Real.exp_add]
  field_simp [Real.sqrt_ne_zero'.mpr hy']

/-- Continuity of the partition generating function on the open unit disk. -/
theorem continuousAt_partitionGenFun {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt partitionGenFun z := by
  let r := (1+‖z‖)/2
  have hr : ‖z‖ < r := by dsimp [r]; linarith
  apply (continuousOn_partitionGenFun_closedBall ((norm_nonneg z).trans hr.le)
    (by dsimp [r]; linarith)).continuousAt
  exact Metric.closedBall_mem_nhds_of_mem (by simpa using hr)

end AnalyticNumberTheory.ModularAndPartitions
