import AnalyticNumberTheory.ModularAndPartitions.PartitionMinorArcs
import AnalyticNumberTheory.ModularAndPartitions.PartitionInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Transition arcs at the principal cusp for the partition function

Modular inversion gives exponential suppression on the band between the
saddle width cutoff `y` and the outer cutoff `√y`. The outer arcs are covered
by the finite Euler-product estimate.
-/

open Real Filter Set MeasureTheory
open scoped Topology Asymptotics

namespace AnalyticNumberTheory.ModularAndPartitions

/-- On `y ≤ |x| ≤ √y` the real part of the inverse cusp parameter lies in
`[1/2, 1/(2y)]`. In particular the transformed generating function is bounded. -/
theorem norm_partitionGenFun_transitionArc_le {y x : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (hlo : y ≤ |x|) (hhi : |x| ≤ √y) :
    ‖partitionGenFun (partitionNome ((y:ℂ)-x*Complex.I))‖ ≤
      (2 * partitionGenFunReal (Real.exp (-Real.pi))) * Real.exp (Real.pi/(24*y)) := by
  let z := (y:ℂ)-x*Complex.I
  have hzr : z.re = y := by simp [z]
  have hzi : z.im = -x := by simp [z]
  have hsq : Complex.normSq z = y^2+x^2 := by rw [Complex.normSq_apply,hzr,hzi]; ring
  have hden : 0 < y^2+x^2 := by positivity
  have hinv : z⁻¹.re = y/(y^2+x^2) := by rw [Complex.inv_re, hzr, hsq]
  have hx2 : x^2 ≤ y := by simpa only [sq_abs, Real.sq_sqrt hy.le] using (pow_le_pow_left₀ (abs_nonneg x) hhi 2)
  have hy2 : y^2 ≤ x^2 := by simpa only [sq_abs] using (pow_le_pow_left₀ hy.le hlo 2)
  have hinv_lo : 1/2 ≤ z⁻¹.re := by rw [hinv, le_div_iff₀ hden]; nlinarith
  have hinv_hi : z⁻¹.re ≤ 1/(2*y) := by rw [hinv, div_le_div_iff₀ hden (by positivity)]; nlinarith
  have hnorm : ‖z‖ ≤ 2 := by
    have hnormSq := Complex.sq_norm z
    rw [hsq] at hnormSq
    nlinarith [norm_nonneg z, sq_nonneg (1-y)]
  have hroot : ‖z^(1/2:ℂ)‖ ≤ 2 := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_sqrt hnorm).trans (by norm_num)
  have hexp : ‖Complex.exp ((Real.pi:ℂ)/12 * (z⁻¹-z))‖ ≤ Real.exp (Real.pi/(24*y)) := by
    rw [Complex.norm_exp, show (Real.pi:ℂ)/12 = ((Real.pi/12:ℝ):ℂ) by norm_num, Complex.re_ofReal_mul,
      Complex.sub_re, hzr, Real.exp_le_exp]
    calc
      _ ≤ Real.pi/12 * (1/(2*y)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hF := norm_partitionGenFun_nome_le (by norm_num : (0:ℝ) < 1/2) hinv_lo
  rw [show -2*Real.pi*(1/2) = -Real.pi by ring] at hF
  change ‖partitionGenFun (partitionNome z)‖ ≤ _
  rw [partitionGenFun_nome_inversion (hzr ▸ hy), norm_mul, norm_mul]
  calc
    _ ≤ (2 * Real.exp (Real.pi/(24*y))) * partitionGenFunReal (Real.exp (-Real.pi)) := by gcongr
    _ = _ := by ring

/-- The smaller exponential scale on the transition arcs is negligible relative
to `y²` times the radial generating function. -/
private theorem eventually_exp_le_partition_radial :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in 𝓝[>] 0, Real.exp (Real.pi/(24*y)) ≤
      c * y^2 * partitionGenFunReal (Real.exp (-2*Real.pi*y)) := by
  obtain ⟨c,hc,h⟩ := partitionGenFunReal_radial_isEquivalent.isBigO_symm.exists_pos
  let a := Real.pi/24
  have ha : 0 < a := by dsimp [a]; positivity
  have hdec := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha).comp tendsto_inv_nhdsGT_zero
  refine ⟨c,hc,?_⟩
  filter_upwards [h.bound, hdec.eventually_lt_const zero_lt_one, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))] with y hrad hdecay hy hy1
  change 0 < y at hy
  have hF := partitionGenFunReal_pos (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (show -2*Real.pi*y < 0 by nlinarith [mul_pos Real.pi_pos hy]))
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le), Real.norm_of_nonneg hF.le] at hrad
  let E := Real.exp (a/y)
  have he : 0 < E := Real.exp_pos _
  have hsmall : 1 ≤ y^3 * E := by
    have ht : y⁻¹ ^ (3 : ℕ) / E < 1 := by
      convert hdecay using 1
      dsimp only [Function.comp_apply]
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv, ← Real.exp_neg]
      ring_nf
    rw [div_lt_one he, inv_pow, inv_lt_iff_one_lt_mul₀' (pow_pos hy 3)] at ht
    exact ht.le
  have hyS : y ≤ √y := Real.le_sqrt_self_iff.mpr hy1.le
  have hhalf : Real.exp (Real.pi/(24*y)) = E := by dsimp [E,a]; congr 1; ring
  have hfull : Real.exp (Real.pi/(12*y)) = E^2 := by
    rw [sq, ← Real.exp_add]
    dsimp [a]
    congr 1
    ring
  rw [hhalf]
  rw [hfull] at hrad
  calc
    E = 1*E := (one_mul _).symm
    _ ≤ (y^3*E)*E := mul_le_mul_of_nonneg_right hsmall he.le
    _ ≤ y^2*(√y*E^2) := by
      rw [show (y^3*E)*E = y^2*(y*E^2) by ring]
      gcongr
    _ ≤ y^2*(c*partitionGenFunReal (Real.exp (-2*Real.pi*y))) := by gcongr
    _ = _ := by ring

/-- Uniformly on the whole complement of the central arc `|x| < y`, the
partition generating function is `O(y²)` relative to its radial value. -/
theorem eventually_norm_partitionGenFun_off_center_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ x : ℝ, y ≤ |x| → |x| ≤ 1/2 →
      ‖partitionGenFun (partitionNome ((y:ℂ)-x*Complex.I))‖ ≤
        C*y^2*partitionGenFunReal (Real.exp (-2*Real.pi*y)) := by
  obtain ⟨c,hc,h⟩ := eventually_exp_le_partition_radial
  let K := 2*partitionGenFunReal (Real.exp (-Real.pi))
  have hK : 0 < K := mul_pos two_pos (partitionGenFunReal_pos (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)))
  let C := max (K*c) ((16*Real.pi)^4)
  refine ⟨C,(mul_pos hK hc).trans_le (le_max_left _ _),?_⟩
  filter_upwards [h,self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))] with y hrad hy hy1
  change 0 < y at hy
  intro x hlo hhi
  have hF := (partitionGenFunReal_pos (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (show -2*Real.pi*y < 0 by nlinarith [mul_pos Real.pi_pos hy]))).le
  rcases le_total |x| (√y) with hx | hx
  · calc
      _ ≤ K * Real.exp (Real.pi/(24*y)) := norm_partitionGenFun_transitionArc_le hy hy1.le hlo hx
      _ ≤ K * (c*y^2*partitionGenFunReal (Real.exp (-2*Real.pi*y))) := mul_le_mul_of_nonneg_left hrad hK.le
      _ = (K*c)*y^2*partitionGenFunReal (Real.exp (-2*Real.pi*y)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · apply (norm_partitionGenFun_exp_minorArc_le hy hx hhi).trans
    gcongr
    exact le_max_right _ _

/-- A bounded Fourier weight on any subset of the complement of `|x| < y`
has the same uniform integrated error bound. -/
theorem eventually_norm_setIntegral_partitionGenFun_off_center_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ E : Set ℝ, (∀ x ∈ E, y ≤ |x| ∧ |x| ≤ 1/2) →
      ∀ w : ℝ → ℂ, (∀ x ∈ E, ‖w x‖ ≤ 1) →
      ‖∫ x in E, partitionGenFun (partitionNome ((y:ℂ)-x*Complex.I)) * w x‖ ≤
        C*y^2*partitionGenFunReal (Real.exp (-2*Real.pi*y)) := by
  obtain ⟨C,hC,h⟩ := eventually_norm_partitionGenFun_off_center_le
  refine ⟨C,hC,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with y h hy
  change 0 < y at hy
  intro E hE w hw
  have hsub : E ⊆ Icc (-(1/2:ℝ)) (1/2) := fun x hx => abs_le.mp (hE x hx).2
  have hvol : volume.real E ≤ 1 := by
    apply (measureReal_mono (μ := volume) hsub measure_Icc_lt_top.ne).trans
    norm_num [measureReal_def, Real.volume_Icc]
  apply (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub).trans_lt measure_Icc_lt_top) (fun x hx => ?_)).trans
  · have hF := (partitionGenFunReal_pos (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (show -2*Real.pi*y < 0 by nlinarith [mul_pos Real.pi_pos hy]))).le
    exact mul_le_of_le_one_right (mul_nonneg (mul_nonneg hC.le (sq_nonneg y)) hF) hvol
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hw x hx)).trans (h x (hE x hx).1 (hE x hx).2)

end AnalyticNumberTheory.ModularAndPartitions
