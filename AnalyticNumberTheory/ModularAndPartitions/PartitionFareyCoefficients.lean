import AnalyticNumberTheory.AnalyticTools.FareyDissection
import AnalyticNumberTheory.ModularAndPartitions.PartitionFareyArcs

/-!
# Extracting partition coefficients on a Farey dissection

Use the circle at height `N⁻²`. After modular inversion, the contribution
from the nonconstant Fourier terms at all the rational cusps is bounded by a
constant (depending on the Fourier index) times `N⁻¹/²`.
-/

open Complex Real Filter Set Finset MeasureTheory
open scoped Topology Interval
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The generating function and its Fourier weight on the circle at height `y`. -/
noncomputable def partitionCoefficientIntegrand (n : ℕ) (y t : ℝ) : ℂ :=
  let w := (y:ℂ)-t*I
  partitionGenFun (partitionNome w) * Complex.exp (2*π*n*w)

theorem continuous_partitionCoefficientIntegrand (n : ℕ) {y : ℝ} (hy : 0 < y) :
    Continuous (partitionCoefficientIntegrand n y) := by
  let w (t : ℝ) := (y:ℂ)-t*I
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hq : Continuous (fun t => partitionNome (w t)) := by unfold partitionNome; fun_prop
  have hF : Continuous (fun t => partitionGenFun (partitionNome (w t))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun t => partitionNome (w t))
      (continuousAt_partitionGenFun (norm_partitionNome_lt_one (by simpa [w] using hy))) hq.continuousAt
  exact hF.mul (Complex.continuous_exp.comp (continuous_const.mul hw))

theorem periodic_partitionCoefficientIntegrand (n : ℕ) (y : ℝ) :
    Function.Periodic (partitionCoefficientIntegrand n y) 1 := by
  intro t
  simp only [partitionCoefficientIntegrand, partitionNome, Complex.ofReal_add, Complex.ofReal_one]
  rw [show -2*(π:ℂ)*(y-(t+1)*I) = -2*π*(y-t*I)+2*π*I by ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one,
    show 2*(π:ℂ)*n*(y-(t+1)*I) = 2*π*n*(y-t*I)+((-(n:ℤ):ℤ):ℂ)*(2*π*I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Coefficient extraction with the radial factor absorbed into the integrand. -/
theorem partitionCount_eq_integral_height (n : ℕ) {y : ℝ} (hy : 0 < y) :
    (partitionCount n : ℂ) = ∫ t in (0:ℝ)..1, partitionCoefficientIntegrand n y t := by
  let r := Real.exp (-2*π*y)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hy])
  rw [partitionCount_eq_intervalIntegral hr hr1 n, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have hq : (r:ℂ)*Complex.exp (2*π*t*I) = partitionNome ((y:ℂ)-t*I) := by
    dsimp [r, partitionNome]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast; congr 1; ring
  have hrpow : (r:ℂ)^(-(n:ℤ)) = Complex.exp (2*π*n*y) := by
    dsimp [r]
    rw [Complex.ofReal_exp, ← Complex.exp_int_mul]
    push_cast; congr 1; ring
  simp only [partitionCoefficientIntegrand, hq, hrpow, Complex.ofReal_natCast]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- The unit-modulus multiplier at the cusp `h/k`, including the Fourier phase. -/
noncomputable def rademacherPhase (h k n : ℕ) : ℂ :=
  Complex.exp (π*I*(dedekindSum h k : ℂ)-2*π*I*(n:ℂ)*h/k)

theorem norm_rademacherPhase (h k n : ℕ) : ‖rademacherPhase h k n‖ = 1 := by
  unfold rademacherPhase
  rw [show π*I*(dedekindSum h k : ℂ)-2*π*I*(n:ℂ)*h/k =
    ((π*dedekindSum h k-2*π*n*h/k : ℝ):ℂ)*I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private noncomputable def arcKernel (n k : ℕ) (N t : ℝ) : ℂ :=
  let z := partitionFareyDisplacement k N t
  z^(1/2:ℂ)*Complex.exp ((π:ℂ)/(12*k)*z⁻¹+(2*π*n-π/12)/k*z)

private theorem center_cast (h k : ℕ) : ((mkRat (h:ℤ) k : ℚ):ℝ) = (h:ℝ)/k := by
  rw [Rat.mkRat_eq_div]
  push_cast
  rfl

private theorem arc_integrand_eq (h k n : ℕ) (hk : 0 < k) (N t : ℝ) :
    let z := partitionFareyDisplacement k N t
    let w := (((N^2)⁻¹:ℝ):ℂ)-(((h:ℝ)/k+t:ℝ):ℂ)*I
    partitionNome w = partitionCuspNome h k z ∧
      partitionCuspMain h k z * Complex.exp (2*π*n*w) = rademacherPhase h k n * arcKernel n k N t := by
  intro z w
  have hk' : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw : w = (z-(h:ℂ)*I)/k := by dsimp [w,z,partitionFareyDisplacement]; push_cast; field_simp; ring
  constructor
  · rw [hw]; rfl
  · simp only [partitionCuspMain, rademacherPhase, arcKernel, show partitionFareyDisplacement k N t = z from rfl]
    rw [show Complex.exp (π*I*(dedekindSum h k:ℂ))*z^(1/2:ℂ)*Complex.exp ((π:ℂ)/(12*k)*(z⁻¹-z))*
        Complex.exp (2*π*n*w) = z^(1/2:ℂ)*(Complex.exp (π*I*(dedekindSum h k:ℂ))*
        (Complex.exp ((π:ℂ)/(12*k)*(z⁻¹-z))*Complex.exp (2*π*n*w))) by ring,
      mul_left_comm (Complex.exp _) (z^(1/2:ℂ)) (Complex.exp _)]
    simp only [← Complex.exp_add]
    congr 2
    rw [hw]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

private theorem continuous_arcKernel (n k : ℕ) (hk : 0 < k) {N : ℝ} (hN : 0 < N) :
    Continuous (arcKernel n k N) := by
  let z := partitionFareyDisplacement k N
  have hz : Continuous z := by change Continuous (fun t : ℝ => (k:ℂ)*(_-(t:ℂ)*I)); fun_prop
  have hr (t : ℝ) : 0 < (z t).re := by rw [show z t = _ from rfl, partitionFareyDisplacement_re]; positivity
  have hne (t : ℝ) : z t ≠ 0 := by intro h; simpa [h] using hr t
  have hs : Continuous (fun t => z t^(1/2:ℂ)) := continuous_iff_continuousAt.mpr
    (fun t => (continuousAt_cpow_const (Or.inl (hr t))).comp hz.continuousAt)
  exact hs.mul (Complex.continuous_exp.comp
    ((continuous_const.mul (hz.inv₀ hne)).add (continuous_const.mul hz)))

private theorem farey_integrand_error (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N k h : ℕ}, 0 < k → k ≤ N → h.Coprime k →
      ∀ t : ℝ, |t| ≤ 1/((k:ℝ)*N) →
      ‖partitionCoefficientIntegrand n ((N:ℝ)^2)⁻¹ ((h:ℝ)/k+t) -
        rademacherPhase h k n * arcKernel n k N t‖ ≤ C/√N := by
  obtain ⟨C,hC,hbound⟩ := norm_partitionGenFun_farey_sub_main_le
  refine ⟨C*Real.exp (2*π*n),by positivity,?_⟩
  intro N k h hk hkN hcop t ht
  obtain ⟨u,v,huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hinv : (h:ℤ)*(-u) ≡ -1 [ZMOD (k:ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨-v,by linarith only [huv]⟩
  let z := partitionFareyDisplacement k N t
  let w : ℂ := ((((N:ℝ)^2)⁻¹:ℝ):ℂ)-(((h:ℝ)/k+t:ℝ):ℂ)*I
  obtain ⟨hq,he⟩ := arc_integrand_eq h k n hk N t
  change partitionNome w = partitionCuspNome h k z at hq
  change partitionCuspMain h k z * Complex.exp (2*π*n*w) = _ at he
  change ‖partitionGenFun (partitionNome w)*_ - _‖ ≤ _
  rw [hq, ← he, ← sub_mul, norm_mul]
  have hN : 1 ≤ N := hk.trans_le hkN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hheight : ((N:ℝ)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hNr)
  have he' : ‖Complex.exp (2*π*n*w)‖ ≤ Real.exp (2*π*n) := by
    rw [Complex.norm_exp, Real.exp_le_exp,
      show 2*(π:ℂ)*n*w = ((2*π*n : ℝ):ℂ)*w by push_cast; rfl]
    simp only [w,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.sub_re,Complex.I_re,mul_zero]
    exact mul_le_of_le_one_right (by positivity) hheight
  have hb := hbound hk (by exact_mod_cast hkN : (k:ℝ) ≤ N) hinv ht
  exact (mul_le_mul hb he' (norm_nonneg _) (by positivity)).trans_eq (by ring)

private theorem farey_arc_error (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N k h : ℕ}, 0 < k → k ≤ N → h < k → h.Coprime k →
      let z := mkRat (h:ℤ) k
      let L := fareyFullLeft N z
      let R := fareyRight N z
      ‖(∫ t in L..R, partitionCoefficientIntegrand n ((N:ℝ)^2)⁻¹ (z+t)) -
        rademacherPhase h k n * rademacherArcIntegral n k N (-L) R‖ ≤ (C/√N)*(R-L) := by
  obtain ⟨C,hC,hb⟩ := farey_integrand_error n
  refine ⟨C,hC,?_⟩
  intro N k h hk hkN hlt hcop z L R
  have H := fareyReduced_width_bounds hk hkN hlt hcop
  change (_ ≤ -L ∧ -L ≤ _) ∧ (_ ≤ R ∧ R ≤ _) at H
  have hN : 0 < (N:ℝ) := by exact_mod_cast hk.trans_le hkN
  have hlow : 0 ≤ 1/((k:ℝ)*(2*N)) := by positivity
  have hLR : L ≤ R := by linarith only [H.1.1,H.2.1,hlow]
  have hc := continuous_partitionCoefficientIntegrand n (by positivity : 0 < ((N:ℝ)^2)⁻¹)
  have h1 : Continuous (fun t : ℝ => partitionCoefficientIntegrand n ((N:ℝ)^2)⁻¹ (z+t)) :=
    hc.comp (continuous_const.add continuous_id)
  have h2 : Continuous (fun t => rademacherPhase h k n * arcKernel n k N t) :=
    continuous_const.mul (continuous_arcKernel n k hk hN)
  change ‖(∫ t in L..R, _) - rademacherPhase h k n * (∫ t in -(-L)..R, arcKernel n k N t)‖ ≤ _
  rw [neg_neg, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    (h1.intervalIntegrable ..) (h2.intervalIntegrable ..), ← abs_of_nonneg (sub_nonneg.mpr hLR)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [Set.uIoc_of_le hLR] at ht
  have habs : |t| ≤ 1/((k:ℝ)*N) := abs_le.mpr ⟨by linarith only [ht.1,H.1.2],ht.2.trans H.2.2⟩
  simpa only [z,center_cast] using hb hk hkN hcop t habs

/-- Approximating every reduced cusp by its principal integral has total
error at most `C(n)/√N`. The widths sum to one, so no factor counting the
number of fractions is lost. -/
theorem partitionCount_sub_sum_rademacherArcs_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 0 < N →
    ‖(partitionCount n : ℂ) - ∑ k ∈ Icc 1 N, ∑ h ∈ (range k).filter (fun h => h.Coprime k),
        rademacherPhase h k n * rademacherArcIntegral n k N
          (-fareyFullLeft N (mkRat h k)) (fareyRight N (mkRat h k))‖ ≤ C/√N := by
  obtain ⟨C,hC,hb⟩ := farey_arc_error n
  refine ⟨C,hC,fun {N} hN => ?_⟩
  let f := partitionCoefficientIntegrand n ((N:ℝ)^2)⁻¹
  have hc : Continuous f := continuous_partitionCoefficientIntegrand n (by positivity)
  rw [partitionCount_eq_integral_height n (by positivity : 0 < ((N:ℝ)^2)⁻¹),
    integral_eq_sum_fareyArcs hN hc (periodic_partitionCoefficientIntegrand n _), ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Icc 1 N, ∑ h ∈ (range k).filter (fun h => h.Coprime k),
          ((C/√N)*(fareyRight N (mkRat h k)-fareyFullLeft N (mkRat h k))) := by
          apply (norm_sum_le ..).trans
          apply sum_le_sum
          intro k hk
          apply (norm_sum_le ..).trans
          apply sum_le_sum
          intro h hh
          exact hb (mem_Icc.mp hk).1 (mem_Icc.mp hk).2 (mem_range.mp (mem_filter.mp hh).1) (mem_filter.mp hh).2
       _ = _ := by simp_rw [← mul_sum]; rw [sum_fareyArc_widths hN, mul_one]

end AnalyticNumberTheory.ModularAndPartitions
