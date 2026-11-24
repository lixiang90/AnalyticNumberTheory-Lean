import AnalyticNumberTheory.ModularAndPartitions.PartitionSaddlePoint
import AnalyticNumberTheory.ModularAndPartitions.PartitionTransitionArcs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Hardy–Ramanujan asymptotic formula

The Fourier coefficient on the saddle circle splits into a central Gaussian
integral and the complementary arcs.
-/

open Complex Filter Real Set MeasureTheory
open scoped Topology Asymptotics

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The radius parameter for the saddle at Fourier index `n`. -/
noncomputable def partitionSaddleHeight (n : ℕ) : ℝ := (√(24*(n:ℝ)))⁻¹

theorem partitionSaddleHeight_pos {n : ℕ} (hn : 0 < n) : 0 < partitionSaddleHeight n := by
  dsimp [partitionSaddleHeight]; positivity

private theorem height_sq {n : ℕ} (hn : 0 < n) :
    partitionSaddleHeight n ^ 2 = (24*(n:ℝ))⁻¹ := by
  simp only [partitionSaddleHeight, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 24*(n:ℝ))]

theorem tendsto_partitionSaddleHeight :
    Tendsto partitionSaddleHeight atTop (𝓝[>] 0) := by
  apply tendsto_inv_atTop_nhdsGT_zero.comp
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)

private theorem height_frequency {n : ℕ} (hn : 0 < n) :
    π/12/(partitionSaddleHeight n)^2 = 2*π*n := by rw [height_sq hn, div_inv_eq_mul]; ring

/-- The saddle normalization including its Gaussian mass equals the Hardy–Ramanujan main term. -/
theorem hardyRamanujanMainTerm_eq_saddle {n : ℕ} (hn : 0 < n) :
    hardyRamanujanMainTerm n =
      partitionSaddleHeight n ^ 2 * Real.exp (π/(6*partitionSaddleHeight n)) * √12 := by
  have hpos := partitionSaddleHeight_pos hn
  have h1 : π/(6*partitionSaddleHeight n) = π * √(2*(n:ℝ)/3) := by
    dsimp [partitionSaddleHeight]
    have h : √(24*(n:ℝ))/6 = √(2*(n:ℝ)/3) := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring
    rw [← h]; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  have h2 : √12 * √3 = 6 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [hardyRamanujanMainTerm, height_sq hn, h1]
  field_simp
  nlinarith only [h2]

/-- Exact extraction of the partition coefficient on its centered saddle circle. -/
theorem partitionCount_eq_integral_saddle {n : ℕ} (hn : 0 < n) :
    (partitionCount n : ℂ) = ∫ x in (-(1/2:ℝ))..(1/2:ℝ), partitionSaddleIntegrand (partitionSaddleHeight n) x := by
  let y := partitionSaddleHeight n
  let r := Real.exp (-2*π*y)
  have hy : 0 < y := partitionSaddleHeight_pos hn
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hy])
  let f (x : ℝ) := partitionGenFun ((r:ℂ)*Complex.exp (2*π*x*I)) * Complex.exp (-2*π*(n:ℂ)*x*I)
  have he (x : ℝ) : (r:ℂ)^(-(n:ℤ)) * f x = partitionSaddleIntegrand y x := by
    have hq : (r:ℂ)*Complex.exp (2*π*x*I) = partitionNome ((y:ℂ)-x*I) := by
      dsimp [r, partitionNome]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      push_cast; congr 1; ring
    have hw : (π:ℂ)/12/(y:ℂ)^2 = 2*π*n := by exact_mod_cast height_frequency hn
    dsimp [f, partitionSaddleIntegrand]
    rw [hq]
    have hrpow : (r:ℂ)^(-(n:ℤ)) = Complex.exp (2*π*n*y) := by
      dsimp [r]
      rw [Complex.ofReal_exp, ← Complex.exp_int_mul]
      push_cast; congr 1; ring
    rw [hrpow, mul_left_comm, ← Complex.exp_add]
    congr 2
    calc _ = ((π:ℂ)/12/(y:ℂ)^2)*((y:ℂ)-x*I) := by rw [hw]; ring
         _ = _ := by ring
  have hper : Function.Periodic f 1 := by
    intro x
    dsimp [f]
    push_cast
    rw [show 2*(π:ℂ)*(x+1)*I = 2*π*x*I + 2*π*I by ring, Complex.exp_add, Complex.exp_two_pi_mul_I,
      show -2*(π:ℂ)*n*(x+1)*I = -2*π*n*x*I + ((-(n:ℤ):ℤ):ℂ)*(2*π*I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, mul_one]
  have heq := hper.intervalIntegral_add_eq 0 (-(1/2:ℝ))
  norm_num at heq
  rw [partitionCount_eq_intervalIntegral hr hr1 n]
  change (r:ℂ)^(-(n:ℤ)) * (∫ x in (0:ℝ)..1, f x) = _
  rw [heq, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun x _ => he x)

private theorem norm_partitionSaddleIntegrand {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖partitionSaddleIntegrand y x‖ =
      ‖partitionGenFun (partitionNome ((y:ℂ)-x*I))‖ * Real.exp (π/(12*y)) := by
  dsimp only [partitionSaddleIntegrand]
  rw [norm_mul, Complex.norm_exp]
  congr 2
  rw [show (π:ℂ)/12*((y:ℂ)-x*I)/(y:ℂ)^2 = ((π/12/y^2 : ℝ):ℂ)*((y:ℂ)-x*I) by push_cast; ring]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero]
  field_simp

/-- After normalization the contribution of the complementary arcs tends to zero. -/
theorem tendsto_partitionSaddleIntegral_off_center :
    Tendsto (fun y : ℝ => ((∫ x in (-(1/2:ℝ))..(1/2:ℝ), partitionSaddleIntegrand y x) -
        ∫ x in (-y)..y, partitionSaddleIntegrand y x) /
      ((y^2 * Real.exp (π/(6*y)) : ℝ):ℂ)) (𝓝[>] 0) (𝓝 0) := by
  let E (y : ℝ) := Real.exp (π/(12*y))
  let F (y : ℝ) := partitionGenFunReal (Real.exp (-2*π*y))
  let H (y : ℝ) := y^2 * Real.exp (π/(6*y))
  have hH (y : ℝ) : H y = y^2*(E y)^2 := by
    dsimp [H,E]
    rw [sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  have hdiv : Tendsto (fun y => F y/(√y*E y)) (𝓝[>] 0) (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (by
      filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
      exact (mul_pos (Real.sqrt_pos.mpr hy) (Real.exp_pos _)).ne')).mp partitionGenFunReal_radial_isEquivalent
  have hsmall : Tendsto (fun y => F y / E y) (𝓝[>] 0) (𝓝 0) := by
    have h := hdiv.mul ((Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    simp only [Real.sqrt_zero, mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    field_simp [Real.sqrt_ne_zero'.mpr hy]
  obtain ⟨C, hC, hb⟩ := eventually_norm_partitionGenFun_off_center_le
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := hsmall.const_mul C
  rw [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [hb, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with y hb hy hy1
  have hy' : 0 < y := hy
  let U := Set.Ioc (-(1/2:ℝ)) (1/2)
  let V := Set.Ioc (-y) y
  have hsub : V ⊆ U := Set.Ioc_subset_Ioc (by linarith) hy1.le
  have hF0 : 0 < F y := partitionGenFunReal_pos (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hy']))
  have hE := Real.exp_pos (π/(12*y))
  have hh : 0 < H y := by dsimp [H]; positivity
  rw [intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2), intervalIntegral.integral_of_le (neg_le_self hy'.le),
    ← setIntegral_sdiff measurableSet_Ioc ((continuous_partitionSaddleIntegrand hy').integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) hsub,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  let B := C*y^2*F y*E y
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg y)) hF0.le) hE.le
  have hmeasure : volume.real (U \ V) ≤ 1 := by
    apply (measureReal_mono Set.sdiff_subset (μ := volume) (s₂ := U) measure_Ioc_lt_top.ne).trans
    dsimp only [U]
    rw [Real.volume_real_Ioc_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2)]; norm_num
  have hbound : ‖∫ x in U \ V, partitionSaddleIntegrand y x‖ ≤ B := by
    apply (norm_setIntegral_le_of_norm_le_const ((measure_mono Set.sdiff_subset).trans_lt (measure_Ioc_lt_top (a := -(1/2:ℝ)) (b := 1/2))) ?_).trans
    · exact (mul_le_mul_of_nonneg_left hmeasure hB).trans_eq (mul_one B)
    · rintro x ⟨hx, hx'⟩
      have hx0 : y ≤ |x| := le_of_not_gt fun h => hx' ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
      have hx1 : |x| ≤ 1/2 := abs_le.mpr ⟨hx.1.le, hx.2⟩
      rw [norm_partitionSaddleIntegrand hy']
      exact mul_le_mul_of_nonneg_right (hb x hx0 hx1) hE.le
  change ‖∫ x in U \ V, partitionSaddleIntegrand y x‖ / H y ≤ C * (F y / E y)
  rw [div_le_iff₀ hh]
  apply hbound.trans_eq
  rw [hH]
  dsimp only [B]
  field_simp [hE.ne']

/-- The complete normalized saddle integral has Gaussian mass `√12`. -/
theorem tendsto_partitionSaddleIntegral :
    Tendsto (fun y : ℝ => (∫ x in (-(1/2:ℝ))..(1/2:ℝ), partitionSaddleIntegrand y x) /
      ((y^2 * Real.exp (π/(6*y)) : ℝ):ℂ)) (𝓝[>] 0) (𝓝 ((√12:ℝ):ℂ)) := by
  have h := tendsto_partitionSaddleIntegral_off_center.add tendsto_integral_partitionSaddleKernel
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  rw [integral_partitionSaddleIntegrand_central hy]
  have hc : ((y^2 * Real.exp (π/(6*y)) : ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (pow_pos hy _) (Real.exp_pos _)).ne'
  rw [sub_div, mul_div_cancel_left₀ _ hc, sub_add_cancel]

/-- **Hardy–Ramanujan's partition asymptotic.** As `n` tends to infinity,
`p(n) ~ exp(π√(2n/3)) / (4n√3)`. -/
theorem hardyRamanujanAsymptotic : HardyRamanujanAsymptotic := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := ((Complex.continuous_re.continuousAt.tendsto.comp tendsto_partitionSaddleIntegral).comp
    tendsto_partitionSaddleHeight).div_const (√12)
  simp only [Complex.ofReal_re, div_self (by positivity : √(12:ℝ) ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply, Pi.div_apply, ← partitionCount_eq_integral_saddle hn,
    hardyRamanujanMainTerm_eq_saddle hn, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

end AnalyticNumberTheory.ModularAndPartitions
