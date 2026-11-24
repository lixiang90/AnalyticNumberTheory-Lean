import AnalyticNumberTheory.ModularAndPartitions.PartitionContour
import AnalyticNumberTheory.ModularAndPartitions.PartitionBessel

/-!
# The principal integral on one Rademacher arc

In the reciprocal coordinate `w=1/(kz)`, the contour may be deformed
to a vertical line. The complete vertical integral gives the analytic
factor in the Rademacher series.
-/

open Complex Real Set MeasureTheory

namespace AnalyticNumberTheory.ModularAndPartitions

set_option maxHeartbeats 1100000

/-- The coefficient of `1/w` in the transformed principal exponential. -/
noncomputable def rademacherReciprocalCoefficient (n k : ℕ) : ℝ :=
  (2*π*n-π/12)/(k:ℝ)^2

private theorem coefficient_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    0 < rademacherReciprocalCoefficient n k := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  dsimp [rademacherReciprocalCoefficient]
  exact div_pos (by nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn')]) (by positivity)

/-- With Rademacher's parameters the complete line integral equals `k³ψ_k(n)`. -/
theorem integral_rademacherVerticalKernel_eq_psi {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (∫ t : ℝ, rademacherVerticalKernel (5/2) (π/12) (rademacherReciprocalCoefficient n k) (1+(t:ℂ)*I)) =
      (((k:ℝ)^3 * rademacherPsi k n : ℝ):ℂ) := by
  let x := (n:ℝ)-1/24
  have hx : 0 < x := by
    have h : (1:ℝ) ≤ n := by exact_mod_cast hn
    dsimp [x]; linarith
  let A := rademacherReciprocalCoefficient n k
  have hA : 0 < A := coefficient_pos hn hk
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have ha : A = (2*π*x)/(k:ℝ)^2 := by dsimp [A, rademacherReciprocalCoefficient, x]; ring
  have hay : √A = √2*√π*√x/k := by
    rw [ha, Real.sqrt_div (by positivity), Real.sqrt_sq hk'.le, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
  have harg : 2*√(π/12)*√A = (π/k*√(2/3))*√x := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, div_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hx.le, Real.sq_sqrt (by positivity : 0 ≤ π/12),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/3)]
    rw [ha]
    ring
  rw [integral_rademacherVerticalKernel_half (by positivity) hA, rademacherPsi_eq hk hn]
  change ((√π/(A*√A) * (2*√(π/12)*√A*Real.cosh (2*√(π/12)*√A)-Real.sinh (2*√(π/12)*√A)) : ℝ):ℂ) = _
  rw [harg]
  apply congrArg Complex.ofReal
  change _ = (k:ℝ)^3 * ((1/(2*π*√2*(√x)^3)) * _)
  rw [← mul_assoc]
  congr 1
  rw [hay, ha, show (√x)^3 = x*√x by rw [pow_succ, Real.sq_sqrt hx.le]]
  field_simp

private theorem differentiableOn_rademacherVerticalKernel (s b A : ℝ) :
    DifferentiableOn ℂ (rademacherVerticalKernel s b A) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul (differentiableAt_id.cpow_const (Or.inl hw))
  apply DifferentiableAt.cexp
  apply DifferentiableAt.add
  · exact (differentiableAt_const (c := (b:ℂ))).mul differentiableAt_id
  · exact (differentiableAt_const (c := (A:ℂ))).div differentiableAt_id hw0

private theorem verticalKernel_strip_bound (n : ℕ) {k : ℕ} (hk : 0 < k) (hn : 0 < n)
    {w : ℂ} (hl : 1/2 ≤ w.re) (hr : w.re ≤ 4) :
    ‖rademacherVerticalKernel (5/2) (π/12) (rademacherReciprocalCoefficient n k) w‖ ≤
      (8 * Real.exp (π/3 + 4*π*n))/(1+w.im^2) := by
  let A := rademacherReciprocalCoefficient n k
  have hA : 0 < A := coefficient_pos hn hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hA' : A ≤ 2*π*n := by
    dsimp [A,rademacherReciprocalCoefficient]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2*π*n) (sub_nonneg.mpr (one_le_pow₀ hk1 (n := 2))), Real.pi_pos]
  have hnorm : 1/2 ≤ ‖w‖ := hl.trans (Complex.re_le_norm w)
  have hwn : 0 < ‖w‖ := by linarith
  have hn2 : 1+w.im^2 ≤ 4*‖w‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (w.re-1/2), sq_nonneg w.im]
  have hroot : (‖w‖^(1/2:ℝ))⁻¹ ≤ 2 := by
    rw [← Real.sqrt_eq_rpow, inv_le_comm₀ (Real.sqrt_pos.mpr hwn) (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hpow : ‖w^(-(5/2:ℂ))‖ ≤ 8/(1+w.im^2) := by
    rw [show -(5/2:ℂ) = ((-(2:ℝ)-1/2:ℝ):ℂ) by norm_num, Complex.norm_cpow_real,
      Real.rpow_sub hwn, Real.rpow_neg hwn.le, Real.rpow_two, div_eq_mul_inv]
    calc _ ≤ (‖w‖^2)⁻¹*2 := mul_le_mul_of_nonneg_left hroot (by positivity)
         _ ≤ _ := by rw [le_div_iff₀ (by positivity)]; field_simp; linarith only [hn2]
  have hwi : w⁻¹.re ≤ 2 := (Complex.re_le_norm _).trans (by rw [norm_inv]; exact (inv_le_comm₀ hwn (by norm_num)).mpr (by linarith))
  have he : ‖Complex.exp (((π/12:ℝ):ℂ)*w+(A:ℂ)/w)‖ ≤ Real.exp (π/3+4*π*n) := by
    rw [Complex.norm_exp, Real.exp_le_exp, div_eq_mul_inv ((A:ℝ):ℂ) w]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hwi), mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)]
  unfold rademacherVerticalKernel
  rw [show ((5/2:ℝ):ℂ) = (5/2:ℂ) by push_cast; rfl]
  rw [norm_mul, show (8 * Real.exp (π/3+4*π*n))/(1+w.im^2) = (8/(1+w.im^2))*Real.exp (π/3+4*π*n) by ring]
  exact mul_le_mul hpow he (norm_nonneg _) (by positivity)

private theorem arcIntegral_primitive {k n : ℕ} {N : ℝ} (hk : 0 < k) (hN : 0 < N)
    (L R : ℝ) {g : ℂ → ℂ}
    (hg : ∀ w : ℂ, 0 < w.re →
      HasDerivAt g (rademacherVerticalKernel (5/2) (π/12) (rademacherReciprocalCoefficient n k) w) w) :
    I * (((k:ℂ)^2 * (√(k:ℝ):ℂ)) * rademacherArcIntegral n k N L R) =
      g (rademacherArcReciprocal k N R) - g (rademacherArcReciprocal k N (-L)) := by
  let z := partitionFareyDisplacement k N
  let W := rademacherArcReciprocal k N
  let f (φ : ℝ) := (z φ)^(1/2:ℂ) * Complex.exp ((π:ℂ)/(12*k)*(z φ)⁻¹ + (2*π*n-π/12)/k*z φ)
  let K := rademacherVerticalKernel (5/2) (π/12) (rademacherReciprocalCoefficient n k)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hz (φ : ℝ) : 0 < (z φ).re := by dsimp only [z]; rw [partitionFareyDisplacement_re]; positivity
  have hz0 (φ : ℝ) : z φ ≠ 0 := fun hh => by simpa [hh] using hz φ
  have hW (φ : ℝ) : 0 < (W φ).re := by dsimp only [W]; rw [rademacherArcReciprocal_re]; positivity
  have hW0 (φ : ℝ) : W φ ≠ 0 := fun hh => by simpa [hh] using hW φ
  have hD (φ : ℝ) : HasDerivAt W (I*(k:ℂ)^2*(W φ)^2) φ := by
    have hzD : HasDerivAt z (-(k:ℂ)*I) φ := by
      have hφ := ((hasDerivAt_id φ).ofReal_comp).mul_const I
      have h := (hφ.const_sub (((N^2)⁻¹:ℝ):ℂ)).const_mul (k:ℂ)
      change HasDerivAt (fun y : ℝ => (k:ℂ) * (((N^2)⁻¹:ℝ) - (y:ℂ)*I)) _ φ
      simpa using h
    have h := ((hzD.const_mul (k:ℂ)).inv (mul_ne_zero hkC (hz0 φ)))
    convert h using 1
    · rfl
    · change I*(k:ℂ)^2*((k*z φ)⁻¹)^2 = _
      rw [inv_pow]
      field_simp
  have hphase (φ : ℝ) : ((π/12:ℝ):ℂ)*W φ + ((rademacherReciprocalCoefficient n k:ℝ):ℂ)/W φ =
      (π:ℂ)/(12*k)*(z φ)⁻¹ + (2*π*n-π/12)/k*z φ := by
    dsimp only [W, rademacherArcReciprocal, z, rademacherReciprocalCoefficient]
    push_cast
    field_simp [hz0 φ]
  have hpow (φ : ℝ) : (W φ)^(-(5/2:ℂ))*(W φ)^2 = (√(k:ℝ):ℂ) * (z φ)^(1/2:ℂ) := by
    calc _ = (W φ)^(-(1/2:ℂ)) := by
             rw [← Complex.cpow_two, ← Complex.cpow_add _ _ (hW0 φ)]
             congr 1
             norm_num
         _ = ((W φ)⁻¹)^(1/2:ℂ) := by
             rw [Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi (Or.inl (hW φ))), Complex.cpow_neg]
         _ = _ := by
             change (((k:ℂ)*z φ)⁻¹)⁻¹^(1/2:ℂ) = _
             rw [inv_inv, Complex.mul_cpow, Real.sqrt_eq_rpow, Complex.ofReal_cpow hk'.le]
             · push_cast; rfl
             · rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hk'.le, zero_add]
               exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hder (φ : ℝ) : HasDerivAt (g ∘ W) (I*(((k:ℂ)^2*(√(k:ℝ):ℂ))*f φ)) φ := by
    have h := (hg _ (hW φ)).scomp φ (hD φ)
    change HasDerivAt (g ∘ W) ((I*(k:ℂ)^2*(W φ)^2) * K (W φ)) φ at h
    convert h using 1
    dsimp only [f, K, rademacherVerticalKernel]
    rw [hphase]
    push_cast
    linear_combination -(I*(k:ℂ)^2*Complex.exp ((π:ℂ)/(12*k)*(z φ)⁻¹+(2*π*n-π/12)/k*z φ))*(hpow φ)
  have hf : Continuous f := by
    have hc : Continuous z := by change Continuous (fun t : ℝ => (k:ℂ)*(_-(t:ℂ)*I)); fun_prop
    have hs : Continuous (fun t => z t^(1/2:ℂ)) := continuous_iff_continuousAt.mpr
      (fun t => (continuousAt_cpow_const (Or.inl (hz t))).comp hc.continuousAt)
    exact hs.mul (Complex.continuous_exp.comp
      ((continuous_const.mul (hc.inv₀ hz0)).add (continuous_const.mul hc)))
  change I*(_*(∫ φ in (-L)..R, f φ)) = _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g ∘ W) (fun φ _ => hder φ)
    ((continuous_const.mul (continuous_const.mul hf)).intervalIntegrable _ _)

/-- Quantitative extension of a principal Farey arc to the full Bromwich line.
The constant depends only on the Fourier index. -/
theorem norm_rademacherArcIntegral_sub_psi_le (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {N L R : ℝ}, 0 < k → (k:ℝ) ≤ N →
      1/(2*k*N) ≤ L → L ≤ 1/(k*N) → 1/(2*k*N) ≤ R → R ≤ 1/(k*N) →
      ‖rademacherArcIntegral n k N L R - (√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ)‖ ≤
        C / ((k:ℝ)*√(k:ℝ)*N) := by
  let D := 8*Real.exp (π/3+4*π*n)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨32*D, by positivity, ?_⟩
  intro k N L R hk hkN hL hL' hR hR'
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hN := hk'.trans_le hkN
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  let l := rademacherArcReciprocal k N (-L)
  let r := rademacherArcReciprocal k N R
  obtain ⟨hl,hl',hli⟩ := rademacherArcReciprocal_endpoint (φ := -L) hk hkN
    (by simpa [abs_of_pos hL0] using hL) (by simpa [abs_of_pos hL0] using hL')
  obtain ⟨hr,hr',hri⟩ := rademacherArcReciprocal_endpoint (φ := R) hk hkN
    (by simpa [abs_of_pos hR0] using hR) (by simpa [abs_of_pos hR0] using hR')
  have hl0 : l.im < 0 := by
    dsimp only [l]; rw [rademacherArcReciprocal_im]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hL0) (by positivity)
  have hr0 : 0 < r.im := by dsimp only [r]; rw [rademacherArcReciprocal_im]; positivity
  change N/(4*k) ≤ |l.im| at hli
  change N/(4*k) ≤ |r.im| at hri
  rw [abs_of_neg hl0] at hli
  rw [abs_of_pos hr0] at hri
  let K := rademacherVerticalKernel (5/2) (π/12) (rademacherReciprocalCoefficient n k)
  have hdiff : DifferentiableOn ℂ K {w : ℂ | 0 < w.re} := differentiableOn_rademacherVerticalKernel _ _ _
  obtain ⟨g,hg⟩ := isExactOn_rightHalfPlane hdiff
  have hb := norm_primitive_sub_verticalIntegral_le hg hdiff.continuousOn hD.le
    (fun w h₁ h₂ => verticalKernel_strip_bound n hk hn h₁ h₂) hl hl' hr hr' hl0 hr0
  change ‖(g r-g l) - I*(∫ t : ℝ, rademacherVerticalKernel _ _ _ (1+(t:ℂ)*I))‖ ≤ _ at hb
  rw [← arcIntegral_primitive hk hN L R hg, integral_rademacherVerticalKernel_eq_psi hk hn,
    ← mul_sub, norm_mul, Complex.norm_I, one_mul] at hb
  let ρ := (k:ℝ)^2 * √(k:ℝ)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : ((k:ℂ)^2 * (√(k:ℝ):ℂ)) * rademacherArcIntegral n k N L R -
        (((k:ℝ)^3 * rademacherPsi k n : ℝ):ℂ) =
      (ρ:ℂ)*(rademacherArcIntegral n k N L R - (√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ)) := by
    dsimp only [ρ]
    push_cast
    have he : (√(k:ℝ):ℂ)^2 = k := by exact_mod_cast Real.sq_sqrt hk'.le
    linear_combination ((k:ℂ)^2*(rademacherPsi k n:ℂ))*he
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hb
  apply (le_div_iff₀ (by positivity : 0 < (k:ℝ)*√(k:ℝ)*N)).mpr
  have hrec {t : ℝ} (ht : N/(4*k) ≤ t) : 1/t ≤ 4*k/N := by
    calc 1/t ≤ 1/(N/(4*k)) := one_div_le_one_div_of_le (by positivity) ht
         _ = _ := by field_simp
  have hbd := hb.trans (mul_le_mul_of_nonneg_left (add_le_add (hrec hli) (hrec hri)) (by positivity))
  change ρ * _ ≤ _ at hbd
  have h := (le_div_iff₀ hN).mp (show ρ * ‖rademacherArcIntegral n k N L R -
      (√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ)‖ ≤ (32*D*k)/N by apply hbd.trans_eq; ring)
  dsimp [ρ] at h
  apply (le_of_mul_le_mul_left (a := (k:ℝ)) _ hk')
  nlinarith only [h]

end AnalyticNumberTheory.ModularAndPartitions
