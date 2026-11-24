import AnalyticNumberTheory.ModularAndPartitions.PartitionInversion

/-!
# The partition generating function at a rational cusp

For a reduced fraction `h/k`, choose `a h ≡ -1 (mod k)`. The eta multiplier
then contributes exactly the phase `exp(π i s(h,k))` in the Rademacher sum.
-/

open Complex Real

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The nome `exp(2πi(h+iz)/k)`, with `Re z>0` inside the unit disk. -/
noncomputable def partitionCuspNome (h : ℤ) (k : ℕ) (z : ℂ) : ℂ :=
  partitionNome ((z - h*I)/k)

private theorem cusp_parameter_re (h : ℤ) (k : ℕ) (z : ℂ) :
    ((z - h*I)/k).re = z.re/k := by
  rw [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re,
    Complex.mul_I_re, Complex.intCast_im, neg_zero, div_eq_mul_inv]

/-- The exponential magnitude of a rational cusp's nome is independent of its numerator. -/
theorem norm_partitionCuspNome (h : ℤ) (k : ℕ) (z : ℂ) :
    ‖partitionCuspNome h k z‖ = Real.exp (-2*π*z.re/k) := by
  rw [partitionCuspNome, norm_partitionNome, cusp_parameter_re]
  congr 1; ring

private theorem eta_mul_cuspNome {k : ℕ} (hk : 0 < k) (h : ℤ) {z : ℂ} (hz : 0 < z.re) :
    ModularForm.eta ((h+I*z)/k) * partitionGenFun (partitionCuspNome h k z) =
      Complex.exp ((π:ℂ)*I*((h+I*z)/k)/12) := by
  have hpos : 0 < ((z-h*I)/k).re := by rw [cusp_parameter_re]; exact div_pos hz (by exact_mod_cast hk)
  have hh := eta_mul_partitionGenFun_nome hpos
  have he : I*((z-h*I)/k) = (h+I*z)/k := by
    linear_combination (-(h:ℂ)/(k:ℂ))*Complex.I_mul_I
  rw [he] at hh
  rw [partitionCuspNome, hh]
  congr 1
  linear_combination (-(π:ℂ)*z/(12*k))*Complex.I_mul_I

/-- The modular transformation at the reduced cusp `h/k`, using any negative
inverse `a` of `h` modulo `k`. The two nomes have displacements `z` and `1/z`. -/
theorem partitionGenFun_cusp_inversion {h a : ℤ} {k : ℕ} (hk : 0 < k)
    (ha : h*a ≡ -1 [ZMOD (k:ℤ)]) {z : ℂ} (hz : 0 < z.re) :
    partitionGenFun (partitionCuspNome h k z) =
      Complex.exp ((π:ℂ)*I*(dedekindSum h k)) * z^(1/2:ℂ) *
        Complex.exp ((π:ℂ)/(12*k)*(z⁻¹-z)) * partitionGenFun (partitionCuspNome a k z⁻¹) := by
  obtain ⟨b, hb⟩ := Int.modEq_iff_dvd.mp ha
  have hdet : a*(-h)-b*(k:ℤ) = 1 := by linarith only [hb]
  have hdetC : (a:ℂ)*(-h)-b*k = 1 := by exact_mod_cast hdet
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hz0 : z ≠ 0 := fun he => by simp [he] at hz
  have hz' : 0 < z⁻¹.re := by rw [Complex.inv_re]; exact div_pos hz (Complex.normSq_pos.mpr hz0)
  let τ : UpperHalfPlane := ⟨((h:ℂ)+I*z)/k, by
    rw [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_im]
    simp; exact mul_pos hz (inv_pos.mpr hkR)⟩
  let τ' : ℂ := ((a:ℂ)+I*z⁻¹)/k
  have hd : ModularForm.eta τ' =
      Complex.exp ((π:ℂ)*I*(((a:ℂ)-h)/(12*k) + (dedekindSum h k:ℝ))) *
        z^(1/2:ℂ) * ModularForm.eta τ := by
    have hh := eta_moebius_of_pos hdet (by exact_mod_cast hk) τ
    have hden : (k:ℂ)*(τ:ℂ)+(-h:ℤ) = I*z := by dsimp [τ]; push_cast; field_simp; ring
    have hfrac : ((a:ℂ)*(τ:ℂ)+b)/(I*z) = τ' := by
      dsimp [τ, τ']
      field_simp [Complex.I_ne_zero]
      linear_combination -hdetC - Complex.I_mul_I
    rw [Int.cast_natCast (R := ℂ), hden, hfrac] at hh
    simp only [Int.natAbs_natCast, dedekindSum_neg, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_intCast, Complex.ofReal_natCast, sub_neg_eq_add] at hh
    convert hh using 2; push_cast; ring_nf; simp
  let m := (π:ℂ)*I*(((a:ℂ)-h)/(12*k) + (dedekindSum h k:ℝ))
  have hta := eta_mul_cuspNome hk a hz'
  change ModularForm.eta τ' * _ = Complex.exp ((π:ℂ)*I*τ'/12) at hta
  rw [hd] at hta
  have hη := eta_ne_zero_of_im_pos τ.im_pos
  apply mul_left_cancel₀ (mul_ne_zero (Complex.exp_ne_zero m) hη)
  calc Complex.exp m * ModularForm.eta τ * partitionGenFun (partitionCuspNome h k z) =
        Complex.exp m * Complex.exp ((π:ℂ)*I*(τ:ℂ)/12) := by rw [mul_assoc, eta_mul_cuspNome hk h hz]
       _ = Complex.exp ((π:ℂ)*I*dedekindSum h k) * Complex.exp ((π:ℂ)/(12*k)*(z⁻¹-z)) *
            Complex.exp ((π:ℂ)*I*τ'/12) := by
          simp only [← Complex.exp_add]
          congr 1
          dsimp [m, τ, τ']
          linear_combination ((π:ℂ)*(z-z⁻¹)/(12*k))*Complex.I_mul_I
       _ = _ := by rw [← hta]; dsimp only [m]; ring

/-- The nonconstant part of the partition product is bounded linearly by the
nome on every closed subdisk of the open unit disk. -/
theorem norm_partitionGenFun_sub_one_le {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ r → ‖partitionGenFun z - 1‖ ≤ C * ‖z‖ := by
  let b (n : ℕ) := (partitionCount (n+1) : ℝ)*r^n
  have hb : Summable b := by
    have h := ((summable_nat_add_iff 1).mpr (summable_partitionCount_mul_pow_real hr.le hr1)).mul_right r⁻¹
    apply h.congr
    intro n
    dsimp only [b]
    rw [pow_succ]; field_simp
  refine ⟨∑' n, b n, tsum_nonneg (fun n => by dsimp [b]; positivity), fun z hz => ?_⟩
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_partitionCount_mul_pow (hz.trans_lt hr1))
  simp only [Finset.sum_range_one, partitionCount_zero, Nat.cast_one, pow_zero, mul_one] at h
  rw [← h.tsum_eq]
  have hnorm := (summable_nat_add_iff 1).mpr (summable_norm_partitionCount_mul_pow (hz.trans_lt hr1))
  apply (norm_tsum_le_tsum_norm hnorm).trans
  rw [← tsum_mul_right]
  apply Summable.tsum_le_tsum _ hnorm (hb.mul_right _)
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow, pow_succ, b]
  rw [← mul_assoc]
  gcongr

/-- The principal exponential factor in Rademacher's rational-cusp approximation. -/
noncomputable def partitionCuspMain (h : ℤ) (k : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((π:ℂ)*I*dedekindSum h k) * z^(1/2:ℂ) * Complex.exp ((π:ℂ)/(12*k)*(z⁻¹-z))

private theorem norm_partitionCuspMain (h : ℤ) (k : ℕ) (z : ℂ) :
    ‖partitionCuspMain h k z‖ =
      √‖z‖ * Real.exp (π/(12*k)*(z⁻¹.re-z.re)) := by
  have hphase : (π:ℂ)*I*dedekindSum h k = ((π*dedekindSum h k : ℝ):ℂ)*I := by push_cast; ring
  rw [partitionCuspMain, norm_mul, norm_mul, hphase, Complex.norm_exp_ofReal_mul_I, one_mul,
    show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow,
    Complex.norm_exp, show (π:ℂ)/(12*k) = ((π/(12*k) : ℝ):ℂ) by push_cast; rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]

/-- On the Farey arcs, replacing the transformed generating function by its
constant term incurs at most `C√‖z‖`, uniformly in the cusp. -/
theorem norm_partitionGenFun_cusp_sub_main_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h a : ℤ} {k : ℕ} (z : ℂ), 0 < k → h*a ≡ -1 [ZMOD (k:ℤ)] →
      0 < z.re → (1/2:ℝ) ≤ z⁻¹.re/k →
      ‖partitionGenFun (partitionCuspNome h k z) - partitionCuspMain h k z‖ ≤ C * √‖z‖ := by
  obtain ⟨C,hC,hbound⟩ := norm_partitionGenFun_sub_one_le (Real.exp_pos (-π))
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos))
  refine ⟨C,hC,?_⟩
  intro h a k z hk ha hz hcut
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hq : ‖partitionCuspNome a k z⁻¹‖ ≤ Real.exp (-π) := by
    rw [norm_partitionCuspNome, Real.exp_le_exp]
    rw [show -2*π*z⁻¹.re/k = -2*π*(z⁻¹.re/k) by ring]
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hcut)]
  rw [partitionGenFun_cusp_inversion hk ha hz]
  change ‖partitionCuspMain h k z * partitionGenFun (partitionCuspNome a k z⁻¹) - partitionCuspMain h k z‖ ≤ _
  rw [← mul_sub_one, norm_mul]
  apply (mul_le_mul_of_nonneg_left (hbound _ hq) (norm_nonneg _)).trans
  rw [norm_partitionCuspMain h k, norm_partitionCuspNome]
  have hsmall : Real.exp (π/(12*k)*(z⁻¹.re-z.re)) * Real.exp (-2*π*z⁻¹.re/k) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have hi : 0 ≤ z⁻¹.re := le_of_lt <| by rw [Complex.inv_re]; exact div_pos hz (Complex.normSq_pos.mpr (fun he => by simp [he] at hz))
    have he : π/(12*k)*(z⁻¹.re-z.re) + -2*π*z⁻¹.re/k = -π/(12*k)*(23*z⁻¹.re+z.re) := by ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (by positivity)) (by positivity)
  calc _ = (C*√‖z‖) * (Real.exp (π/(12*k)*(z⁻¹.re-z.re)) * Real.exp (-2*π*z⁻¹.re/k)) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC (Real.sqrt_nonneg _))).trans_eq (mul_one _)

end AnalyticNumberTheory.ModularAndPartitions
