import AnalyticNumberTheory.ModularAndPartitions.PartitionInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Gaussian saddle in the partition integral

At the circle of radius `exp(-2πy)`, writing the angular displacement
as `y√y u` makes the linear terms in the modular exponent cancel.
-/

open Complex Filter Real Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.ModularAndPartitions

private noncomputable def direction (v : ℝ) : ℂ := 1 - v*I

private theorem direction_re (v : ℝ) : (direction v).re = 1 := by simp [direction]
private theorem direction_im (v : ℝ) : (direction v).im = -v := by simp [direction]
private theorem direction_ne (v : ℝ) : direction v ≠ 0 := by
  intro h
  simpa [h] using direction_re v
private theorem direction_normSq (v : ℝ) : Complex.normSq (direction v) = 1+v^2 := by
  rw [Complex.normSq_apply, direction_re, direction_im]; ring
private theorem direction_inv_re (v : ℝ) : (direction v)⁻¹.re = 1 / (1+v^2) := by
  rw [Complex.inv_re, direction_re, direction_normSq]
private theorem dual_re (y v : ℝ) :
    ((y : ℂ) * direction v)⁻¹.re = 1 / (y*(1+v^2)) := by
  rw [mul_inv_rev, ← Complex.ofReal_inv, Complex.mul_re, direction_inv_re]
  simp

/-- The normalized integrand after the saddle change of variables `x = y√y u`. -/
noncomputable def partitionSaddleKernel (y u : ℝ) : ℂ :=
  let w := direction (√y*u)
  w ^ (1/2 : ℂ) * Complex.exp (-(π : ℂ)/12 * ((u : ℂ)^2/w + y*w)) *
    partitionGenFun (partitionNome ((y : ℂ)*w)⁻¹)

private theorem kernel_exponent_re (y u v : ℝ) :
    (-(π : ℂ)/12 * ((u : ℂ)^2/direction v + y*direction v)).re =
      -π/12 * (u^2/(1+v^2) + y) := by
  rw [div_eq_mul_inv ((u : ℂ)^2), show (-(π:ℂ)/12) = ((-π/12:ℝ):ℂ) by push_cast; rfl]
  simp [Complex.mul_re, direction_normSq, direction_re, ← Complex.ofReal_pow, div_eq_mul_inv]

/-- At fixed rescaled displacement the kernel converges to the Gaussian `exp(-πu²/12)`. -/
theorem tendsto_partitionSaddleKernel (u : ℝ) :
    Tendsto (fun y : ℝ => partitionSaddleKernel y u) (𝓝[>] 0) (𝓝 (Complex.exp (-(π:ℂ)/12*u^2))) := by
  have hy : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hv : Tendsto (fun y : ℝ => √y*u) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hy).mul_const u
  have hw : Tendsto (fun y : ℝ => direction (√y*u)) (𝓝[>] 0) (𝓝 1) := by
    simpa [direction] using tendsto_const_nhds.sub ((Complex.continuous_ofReal.continuousAt.tendsto.comp hv).mul_const I)
  have hroot := (continuousAt_cpow_const (b := (1/2:ℂ)) (by simp : (1:ℂ) ∈ Complex.slitPlane)).tendsto.comp hw
  have hphase := Complex.continuous_exp.continuousAt.tendsto.comp
    (((tendsto_const_nhds (x := (u:ℂ)^2)).div hw one_ne_zero).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hy).mul hw) |>.const_mul (-(π:ℂ)/12))
  have hd : Tendsto (fun y : ℝ => y*(1+(√y*u)^2)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using hy.mul (tendsto_const_nhds.add (hv.pow 2))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      change 0 < y*(1+(√y*u)^2)
      exact mul_pos hy (by positivity)
  have hprod := tendsto_partitionGenFun_nome_of_re_atTop (z := fun y : ℝ => ((y:ℂ)*direction (√y*u))⁻¹)
    (by simpa only [dual_re, one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hd)
  simpa [partitionSaddleKernel, Function.comp_def] using (hroot.mul hphase).mul hprod

/-- An integrable Gaussian dominates the normalized central arc, uniformly for `0<y≤1`. -/
theorem norm_partitionSaddleKernel_le {y u : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hu : |√y*u| ≤ 1) :
    ‖partitionSaddleKernel y u‖ ≤
      (2 * partitionGenFunReal (Real.exp (-2*π*(1/2)))) * Real.exp (-π/24*u^2) := by
  let v := √y*u
  change |v| ≤ 1 at hu
  have hv2 : v^2 ≤ 1 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg v) hu 2
  have hpos : 0 < 1+v^2 := by positivity
  have hr : ‖direction v ^ (1/2:ℂ)‖ ≤ 2 := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := norm_sub_le (1:ℂ) ((v:ℂ)*I)
    simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at h
    change ‖1-(v:ℂ)*I‖ ≤ _
    linarith
  have hq : (1/2 : ℝ) ≤ ((y:ℂ)*direction v)⁻¹.re := by
    rw [dual_re, le_div_iff₀ (mul_pos hy hpos)]
    nlinarith [mul_le_mul_of_nonneg_right hy1 hpos.le]
  have hE : ‖Complex.exp (-(π:ℂ)/12 * ((u:ℂ)^2/direction v + y*direction v))‖ ≤ Real.exp (-π/24*u^2) := by
    rw [Complex.norm_exp, kernel_exponent_re, Real.exp_le_exp]
    have h : u^2/2 ≤ u^2/(1+v^2) := by gcongr; linarith
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h), mul_nonneg Real.pi_pos.le hy.le]
  change ‖_ * _ * partitionGenFun (partitionNome ((y:ℂ)*direction v)⁻¹)‖ ≤ _
  rw [norm_mul, norm_mul, mul_right_comm (2 : ℝ)]
  exact mul_le_mul (mul_le_mul hr hE (norm_nonneg _) (by norm_num))
    (norm_partitionGenFun_nome_le (by norm_num) hq) (norm_nonneg _) (by positivity)

private theorem continuous_partitionSaddleKernel {y : ℝ} (hy : 0 < y) : Continuous (partitionSaddleKernel y) := by
  let W (u : ℝ) := direction (√y*u)
  have hw : Continuous W := by dsimp [W, direction]; fun_prop
  have hw0 (u : ℝ) : W u ≠ 0 := direction_ne _
  have hpow : Continuous (fun u => W u ^ (1/2:ℂ)) := continuous_iff_continuousAt.mpr fun u =>
    (continuousAt_cpow_const (Or.inl (by simp [W, direction_re] : 0 < (W u).re))).comp hw.continuousAt
  have hq : Continuous (fun u => partitionNome ((y:ℂ)*W u)⁻¹) := by
    unfold partitionNome
    apply Complex.continuous_exp.comp
    have hyc : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    exact continuous_const.mul ((continuous_const.mul hw).inv₀ (fun u => mul_ne_zero hyc (hw0 u)))
  have hF : Continuous (fun u => partitionGenFun (partitionNome ((y:ℂ)*W u)⁻¹)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hpos : 0 < ((y:ℂ)*W u)⁻¹.re := by dsimp only [W]; rw [dual_re]; positivity
    exact ContinuousAt.comp (f := fun a => partitionNome ((y:ℂ)*W a)⁻¹)
      (continuousAt_partitionGenFun (norm_partitionNome_lt_one hpos)) hq.continuousAt
  apply (hpow.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))).mul hF
  exact ((Complex.continuous_ofReal.pow 2).div hw hw0).add (continuous_const.mul hw)

/-- The central arc has a Gaussian limit after rescaling, with total mass `√12`. -/
theorem tendsto_integral_partitionSaddleKernel :
    Tendsto (fun y : ℝ => ∫ u in (-(1/√y))..(1/√y), partitionSaddleKernel y u)
      (𝓝[>] 0) (𝓝 ((√12 : ℝ) : ℂ)) := by
  let U (y : ℝ) := Set.Ioc (-(1/√y)) (1/√y)
  let G (y : ℝ) := (U y).indicator (partitionSaddleKernel y)
  let M := 2 * partitionGenFunReal (Real.exp (-2*π*(1/2)))
  have hM : 0 ≤ M := by
    dsimp [M]
    apply mul_nonneg (by norm_num)
    exact (partitionGenFunReal_pos (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))).le
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := G) (f := fun u : ℝ => Complex.exp (-(π:ℂ)/12*u^2)) (fun u : ℝ => M*Real.exp (-π/24*u^2))
  have hmeas : ∀ᶠ y in 𝓝[>] (0:ℝ), AEStronglyMeasurable (G y) volume := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (continuous_partitionSaddleKernel hy).aestronglyMeasurable.indicator measurableSet_Ioc
  have hbound : ∀ᶠ y in 𝓝[>] (0:ℝ), ∀ᵐ u ∂volume, ‖G y u‖ ≤ M*Real.exp (-π/24*u^2) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds zero_lt_one)] with y hy hy1
    refine ae_of_all _ fun u => ?_
    by_cases hu : u ∈ U y
    · dsimp only [G]
      rw [Set.indicator_of_mem hu]
      apply norm_partitionSaddleKernel_le hy hy1.le
      have hp := Real.sqrt_pos.mpr hy
      rw [abs_mul, abs_of_pos hp, mul_comm, ← le_div_iff₀ hp, abs_le]
      exact ⟨hu.1.le, hu.2⟩
    · dsimp only [G]
      rw [Set.indicator_of_notMem hu, norm_zero]
      positivity
  have hi : Integrable (fun u : ℝ => M*Real.exp (-π/24*u^2)) := by
    simpa only [neg_div] using (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < π/24)).const_mul M
  have hpoint : ∀ u : ℝ, Tendsto (fun y => G y u) (𝓝[>] 0) (𝓝 (Complex.exp (-(π:ℂ)/12*u^2))) := by
    intro u
    apply (tendsto_partitionSaddleKernel u).congr'
    have h : Tendsto (fun y : ℝ => √y*|u|) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).mul_const |u|
    filter_upwards [self_mem_nhdsWithin, h.eventually_lt_const zero_lt_one] with y hy hsmall
    have hu : |u| < 1/√y := (lt_div_iff₀ (Real.sqrt_pos.mpr hy)).mpr (by simpa [mul_comm] using hsmall)
    exact (Set.indicator_of_mem (s := U y) ⟨(abs_lt.mp hu).1, (abs_lt.mp hu).2.le⟩ _).symm
  have h := hlim hmeas hbound hi (ae_of_all _ hpoint)
  have hgauss : (∫ u : ℝ, Complex.exp (-(π:ℂ)/12*u^2)) = ((√12 : ℝ):ℂ) := by
    rw [show -(π:ℂ)/12 = -((π/12 : ℝ):ℂ) by push_cast; ring, integral_gaussian_complex (by simp; positivity)]
    rw [show π / ((π/12 : ℝ):ℂ) = (12:ℂ) by push_cast; field_simp]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
    push_cast
    rfl
  rw [hgauss] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [intervalIntegral.integral_of_le (neg_le_self (by positivity)), ← integral_indicator measurableSet_Ioc]

/-- The partition coefficient integrand on a circle at the real saddle. Here
`π/(12y²)` is the Fourier index multiplied by `2π`. -/
noncomputable def partitionSaddleIntegrand (y x : ℝ) : ℂ :=
  let z := (y:ℂ) - x*I
  partitionGenFun (partitionNome z) * Complex.exp ((π:ℂ)/12*z/(y:ℂ)^2)

theorem continuous_partitionSaddleIntegrand {y : ℝ} (hy : 0 < y) : Continuous (partitionSaddleIntegrand y) := by
  let z (x : ℝ) := (y:ℂ) - x*I
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hq : Continuous (fun x => partitionNome (z x)) := by unfold partitionNome; fun_prop
  have hF : Continuous (fun x => partitionGenFun (partitionNome (z x))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun a => partitionNome (z a))
      (continuousAt_partitionGenFun (norm_partitionNome_lt_one (by simpa [z] using hy : 0 < (z x).re)))
      hq.continuousAt
  exact hF.mul (Complex.continuous_exp.comp ((continuous_const.mul hz).div_const _))

/-- Exact Gaussian rescaling of the modular kernel, before taking a limit. -/
theorem partitionSaddleIntegrand_rescale {y : ℝ} (hy : 0 < y) (u : ℝ) :
    partitionSaddleIntegrand y (u*(y*√y)) =
      ((√y * Real.exp (π/(6*y)) : ℝ):ℂ) * partitionSaddleKernel y u := by
  let w := direction (√y*u)
  have hyc : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hw : w ≠ 0 := direction_ne _
  have hsq : (w-1)^2 = -((y:ℂ)*u^2) := by
    dsimp [w, direction]
    push_cast
    rw [show 1 - (√y:ℂ)*u*I - 1 = -((√y:ℂ)*u*I) by ring]
    rw [neg_sq, mul_pow, Complex.I_sq, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hy.le]
    ring
  have harg : (y:ℂ) - ((u*(y*√y):ℝ):ℂ)*I = (y:ℂ)*w := by dsimp [w, direction]; push_cast; ring
  have hr : ((y:ℂ)*w) ^ (1/2:ℂ) = (√y:ℂ) * w^(1/2:ℂ) := by
    rw [Complex.mul_cpow, Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
    · push_cast; rfl
    · simp only [Complex.arg_ofReal_of_nonneg hy.le, zero_add]
      exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have he : (π:ℂ)/12*((y*w)⁻¹-y*w) + (π:ℂ)/12*(y*w)/(y:ℂ)^2 =
      (π:ℂ)/(6*y) + (-(π:ℂ)/12)*((u:ℂ)^2/w + y*w) := by
    calc _ = (π:ℂ)/(6*y) + (π:ℂ)/12 * ((w-1)^2/(y*w)-y*w) := by field_simp; ring
         _ = _ := by rw [hsq]; field_simp; ring
  dsimp only [partitionSaddleIntegrand, partitionSaddleKernel]
  rw [harg, partitionGenFun_nome_inversion (by simpa [w, Complex.mul_re, direction_re] using hy), hr]
  push_cast
  change _ = _ * (_ * Complex.exp _ * partitionGenFun (partitionNome ((y:ℂ)*w)⁻¹))
  rw [show (√y:ℂ)*w^(1/2:ℂ)*Complex.exp ((π:ℂ)/12*((y*w)⁻¹-y*w)) *
      partitionGenFun (partitionNome ((y:ℂ)*w)⁻¹) * Complex.exp ((π:ℂ)/12*(y*w)/(y:ℂ)^2) =
      (√y:ℂ)*w^(1/2:ℂ)*partitionGenFun (partitionNome ((y:ℂ)*w)⁻¹) *
        (Complex.exp ((π:ℂ)/12*((y*w)⁻¹-y*w)) * Complex.exp ((π:ℂ)/12*(y*w)/(y:ℂ)^2)) by ring,
    ← Complex.exp_add, he, Complex.exp_add]
  ring

/-- The central contour integral equals a positive normalization times the Gaussian kernel integral. -/
theorem integral_partitionSaddleIntegrand_central {y : ℝ} (hy : 0 < y) :
    (∫ x in (-y)..y, partitionSaddleIntegrand y x) =
      ((y^2 * Real.exp (π/(6*y)) : ℝ):ℂ) *
        ∫ u in (-(1/√y))..(1/√y), partitionSaddleKernel y u := by
  have hs := Real.sqrt_pos.mpr hy
  have h := intervalIntegral.smul_integral_comp_mul_right (E := ℂ) (a := -(1/√y)) (b := 1/√y)
    (partitionSaddleIntegrand y) (y*√y)
  rw [show -(1/√y)*(y*√y) = -y by field_simp, show 1/√y*(y*√y) = y by field_simp] at h
  simp_rw [partitionSaddleIntegrand_rescale hy] at h
  rw [← h, intervalIntegral.integral_const_mul, Complex.real_smul, ← mul_assoc]
  congr 1
  push_cast
  have he : (√y:ℂ)^2 = y := by exact_mod_cast Real.sq_sqrt hy.le
  linear_combination (y*Complex.exp ((π:ℂ)/(6*y)))*he

end AnalyticNumberTheory.ModularAndPartitions
