import AnalyticNumberTheory.ModularAndPartitions.PartitionRationalCusps

/-!
# Partition estimates on Farey arcs

The horizontal contour at height `N⁻²` is split at mediants of neighboring
Farey fractions. On the arc centered at `h/k` its displacement satisfies
`|φ| ≤ 1/(kN)`, which keeps the dual nome uniformly away from the unit circle.
-/

open Complex Real

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The cusp parameter on the horizontal line at height `N⁻²`. -/
noncomputable def partitionFareyDisplacement (k : ℕ) (N φ : ℝ) : ℂ :=
  (k:ℂ) * (((N^2)⁻¹:ℝ) - (φ:ℂ)*I)

theorem partitionFareyDisplacement_re (k : ℕ) (N φ : ℝ) :
    (partitionFareyDisplacement k N φ).re = k*(N^2)⁻¹ := by
  simp only [partitionFareyDisplacement, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, sub_zero, zero_mul, mul_zero]

/-- The cusp parameter has norm at most `2/N` throughout a Farey arc. -/
theorem norm_partitionFareyDisplacement_le {k : ℕ} {N φ : ℝ} (hk : 0 < k) (hkN : (k:ℝ) ≤ N)
    (hφ : |φ| ≤ 1/(k*N)) : ‖partitionFareyDisplacement k N φ‖ ≤ 2/N := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hN := hk'.trans_le hkN
  rw [partitionFareyDisplacement, norm_mul, Complex.norm_natCast]
  calc _ ≤ k * (‖((((N^2)⁻¹:ℝ)):ℂ)‖ + ‖(φ:ℂ)*I‖) := by
            apply mul_le_mul_of_nonneg_left (norm_sub_le _ _) hk'.le
       _ ≤ k * ((N^2)⁻¹ + 1/(k*N)) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_mul, Complex.norm_I,
              Complex.norm_real, Real.norm_eq_abs, mul_one]
            gcongr
       _ ≤ _ := by field_simp; nlinarith [mul_nonneg (sub_nonneg.mpr hkN) hk'.le]

private theorem reciprocal_re (k : ℕ) (N φ : ℝ) :
    (partitionFareyDisplacement k N φ)⁻¹.re / k =
      (N^2)⁻¹ / ((k:ℝ)^2 * (((N^2)⁻¹)^2+φ^2)) := by
  rw [partitionFareyDisplacement, mul_inv_rev, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.inv_re,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, sub_zero, zero_sub, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- The real part in the transformed exponential is at least `1/2`. -/
theorem partitionFareyDisplacement_reciprocal_ge {k : ℕ} {N φ : ℝ} (hk : 0 < k) (hkN : (k:ℝ) ≤ N)
    (hφ : |φ| ≤ 1/(k*N)) : (1/2:ℝ) ≤ (partitionFareyDisplacement k N φ)⁻¹.re / k := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hN := hk'.trans_le hkN
  rw [reciprocal_re, le_div_iff₀ (by positivity)]
  have hφ' := (le_div_iff₀ (mul_pos hk' hN)).mp hφ
  have hφ2 : (k:ℝ)^2*N^2*φ^2 ≤ 1 := by
    have h := pow_le_pow_left₀ (mul_nonneg (abs_nonneg φ) (mul_pos hk' hN).le) hφ' 2
    simp only [mul_pow, sq_abs, one_pow] at h
    linarith only [h]
  have hk2 := pow_le_pow_left₀ hk'.le hkN 2
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hφ2) (sq_nonneg N)]

/-- Uniform approximation by the principal exponential term, with error
`O(N⁻¹/²)` independent of the rational center and the angular displacement. -/
theorem norm_partitionGenFun_farey_sub_main_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h a : ℤ} {k : ℕ} {N φ : ℝ}, 0 < k → (k:ℝ) ≤ N →
      h*a ≡ -1 [ZMOD (k:ℤ)] → |φ| ≤ 1/(k*N) →
      let z := partitionFareyDisplacement k N φ
      ‖partitionGenFun (partitionCuspNome h k z) - partitionCuspMain h k z‖ ≤ C / √N := by
  obtain ⟨C,hC,h⟩ := norm_partitionGenFun_cusp_sub_main_le
  refine ⟨C*√2, by positivity, ?_⟩
  intro h' a k N φ hk hkN ha hφ
  let z := partitionFareyDisplacement k N φ
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hN := hk'.trans_le hkN
  have hz : 0 < z.re := by rw [show z = _ from rfl, partitionFareyDisplacement_re]; positivity
  apply (h z hk ha hz (partitionFareyDisplacement_reciprocal_ge hk hkN hφ)).trans
  rw [mul_div_assoc, ← Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (norm_partitionFareyDisplacement_le hk hkN hφ)) hC

/-- Local principal integral on a Farey arc. The factor `exp(2π n/N²)`
needed for coefficient extraction is included in the exponent. -/
noncomputable def rademacherArcIntegral (n k : ℕ) (N L R : ℝ) : ℂ :=
  ∫ φ in (-L)..R,
    let z := partitionFareyDisplacement k N φ
    z^(1/2:ℂ) * Complex.exp ((π:ℂ)/(12*k)*z⁻¹ + (2*π*n-π/12)/k*z)

/-- Reciprocal coordinate used to straighten the contour of the principal integral. -/
noncomputable def rademacherArcReciprocal (k : ℕ) (N φ : ℝ) : ℂ :=
  ((k:ℂ)*partitionFareyDisplacement k N φ)⁻¹

theorem rademacherArcReciprocal_re (k : ℕ) (N φ : ℝ) :
    (rademacherArcReciprocal k N φ).re =
      (N^2)⁻¹ / ((k:ℝ)^2 * (((N^2)⁻¹)^2 + φ^2)) := by
  rw [← reciprocal_re, rademacherArcReciprocal, mul_inv_rev, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]

theorem rademacherArcReciprocal_im (k : ℕ) (N φ : ℝ) :
    (rademacherArcReciprocal k N φ).im =
      φ / ((k:ℝ)^2 * (((N^2)⁻¹)^2 + φ^2)) := by
  rw [rademacherArcReciprocal, partitionFareyDisplacement, ← mul_assoc, mul_inv_rev,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_im,
    Complex.ofReal_re, neg_zero, sub_zero, zero_sub, neg_neg, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- At a mediant endpoint, the reciprocal lies in the fixed strip `1/2≤Re w≤4`;
its imaginary part has magnitude at least `N/(4k)`. -/
theorem rademacherArcReciprocal_endpoint {k : ℕ} {N φ : ℝ} (hk : 0 < k) (hkN : (k:ℝ) ≤ N)
    (hl : 1/(2*k*N) ≤ |φ|) (hu : |φ| ≤ 1/(k*N)) :
    let w := rademacherArcReciprocal k N φ
    1/2 ≤ w.re ∧ w.re ≤ 4 ∧ N/(4*k) ≤ |w.im| := by
  intro w
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hN := hk'.trans_le hkN
  have hr : 1/2 ≤ w.re := by
    rw [show w.re = _ from rademacherArcReciprocal_re k N φ, ← reciprocal_re]
    exact partitionFareyDisplacement_reciprocal_ge hk hkN hu
  have hl' := (div_le_iff₀ (by positivity : 0 < 2*k*N)).mp hl
  have hl2 : 1 ≤ 4*(k:ℝ)^2*N^2*φ^2 := by
    have h := pow_le_pow_left₀ (zero_le_one : (0:ℝ) ≤ 1) hl' 2
    simp only [mul_pow, sq_abs, one_pow] at h
    linarith only [h]
  refine ⟨hr,?_,?_⟩
  · rw [show w.re = _ from rademacherArcReciprocal_re k N φ, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hl2) (sq_nonneg N)]
  · have him : w.im = φ*N^2*w.re := by
      dsimp only [w]
      rw [rademacherArcReciprocal_re, rademacherArcReciprocal_im]
      field_simp
    rw [him, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg N), abs_of_nonneg (le_trans (by norm_num) hr),
      div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hl') hN.le,
      mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ 4*(k:ℝ)*N^2*|φ| by positivity)]

end AnalyticNumberTheory.ModularAndPartitions
