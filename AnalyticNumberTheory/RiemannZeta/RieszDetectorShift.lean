import AnalyticNumberTheory.RiemannZeta.RieszDetectorKernel
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalLineShift
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Shifting the sixth Riesz kernel at a zero of zeta

The numerator vanishes at the origin. A linear factor removes the pole of
zeta, leaving a holomorphic integrand throughout the shifted strip.
-/
open Complex Real Finset Filter MeasureTheory
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

private noncomputable def regularPart (ρ : ℂ) (w : ℂ) := riemannZeta₁ (ρ+w)
private noncomputable def lastFactors (w : ℂ) := ∏ i ∈ range 6,(w+(i+1:ℕ))
private noncomputable def regularKernel (X : ℕ) (ρ : ℂ) (Y : ℝ) (w : ℂ) :=
  dslope (regularPart ρ) 0 w/(ρ-1)*rieszMobiusPolynomial X (ρ+w)*(Y:ℂ)^w/lastFactors w

private theorem riesz_six (w : ℂ) : rieszDenom 6 w = w*lastFactors w := by
  rw [rieszDenom,Finset.prod_range_succ',lastFactors]
  simp only [Nat.cast_zero,add_zero,mul_comm]

private theorem regularPart_formula {ρ w : ℂ} (hs : ρ+w≠1) :
    regularPart ρ w = (ρ+w-1)*riemannZeta (ρ+w) := by
  rw [riemannZeta_eq_inv_sub_mul hs,regularPart]
  field_simp [sub_ne_zero.mpr hs]

private theorem regularKernel_eq {ρ w : ℂ} (hρ : ρ≠1) (hz : riemannZeta ρ=0)
    (hw : w≠0) (hs : ρ+w≠1) (X : ℕ) (Y : ℝ) :
    regularKernel X ρ Y w = rieszDetectorIntegrand X ρ Y w := by
  have h0 : regularPart ρ 0=0 := by rw [regularPart_formula (by simpa using hρ)]; simp [hz]
  have hd := sub_smul_dslope (regularPart ρ) 0 w
  rw [sub_zero,smul_eq_mul,h0,sub_zero,regularPart_formula hs] at hd
  have he : dslope (regularPart ρ) 0 w = (ρ+w-1)*riemannZeta (ρ+w)/w :=
    (eq_div_iff hw).mpr (by rwa [mul_comm] at hd)
  rw [regularKernel,rieszDetectorIntegrand,he,riesz_six]
  by_cases hD : lastFactors w=0
  · simp [hD]
  · field_simp [hD,hw,sub_ne_zero.mpr hρ] <;> ring

set_option maxHeartbeats 1400000 in
private theorem differentiable_regular {ρ : ℂ} (hρ : ρ.re<1) (X : ℕ) {Y : ℝ} (hY : 1≤Y) :
    DifferentiableOn ℂ (regularKernel X ρ Y) {z : ℂ | z.re∈Set.Icc (1/2-ρ.re) 2} := by
  have hshift : Differentiable ℂ (fun z : ℂ => ρ+z) := by fun_prop
  have hR : Differentiable ℂ (regularPart ρ) := by
    unfold regularPart
    exact differentiable_riemannZeta₁.comp hshift
  have hS (z : ℂ) : DifferentiableAt ℂ (dslope (regularPart ρ) 0) z :=
    ((hR.analyticAt z).dslope 0).differentiableAt
  intro z hz
  have hz' : -(1/2:ℝ)<z.re := by linarith [hz.1]
  have hden : lastFactors z ≠ 0 := by
    unfold lastFactors
    apply prod_ne_zero_iff.mpr
    intro i _ he
    have he' : z.re+((i+1:ℕ):ℝ)=0 := by simpa only [add_re,natCast_re,zero_re] using congrArg Complex.re he
    rw [Nat.cast_add,Nat.cast_one] at he'
    linarith only [he',hz',Nat.cast_nonneg (α:=ℝ) i]
  have hd : DifferentiableAt ℂ lastFactors z := by
    unfold lastFactors
    fun_prop
  have hm : DifferentiableAt ℂ (fun w => rieszMobiusPolynomial X (ρ+w)) z :=
    ((differentiable_rieszMobiusPolynomial X).comp hshift) z
  have hy : (Y:ℂ)≠0 := by exact_mod_cast (show Y≠0 by linarith)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Y:ℂ)^w) z :=
    differentiableAt_id.const_cpow (Or.inl hy)
  exact (((((hS z).div_const _).mul hm).mul hpow).div hd hden).differentiableWithinAt

private theorem detector_tail (X : ℕ) {ρ : ℂ} (hβ : 1/2<ρ.re) (hβ' : ρ.re<1)
    {Y : ℝ} (hY : 1≤Y) :
    ∃ D≥0, ∀ x ∈ Set.Icc (1/2-ρ.re) 2, ∀ t : ℝ, |ρ.im|+4≤|t| →
      ‖rieszDetectorIntegrand X ρ Y ((x:ℂ)+t*I)‖ ≤ D/(1+t^2) := by
  obtain ⟨C,hC,HC⟩ := riemannZeta_halfplane_linear_bound
  let P := ∑ n ∈ Icc 1 X,‖(ArithmeticFunction.moebius n:ℂ)‖
  let L := 1+3/‖ρ-1‖
  let U := 4*C*P*L*Y^2
  have hP : 0≤P := sum_nonneg fun _ _ => norm_nonneg _
  have hL : 0≤L := by dsimp [L]; positivity
  have hU : 0≤U := by dsimp [U]; positivity
  refine ⟨2*U,by positivity,?_⟩
  intro x hx t ht
  let w : ℂ := (x:ℂ)+t*I
  have hwre : w.re=x := by simp [w]
  have hwim : w.im=t := by simp [w]
  let q := |t|
  have hq : 1≤q := by dsimp [q]; linarith [abs_nonneg ρ.im]
  have hq0 : 0<q := by linarith
  have him : |(ρ+w).im|≤2*q := by
    rw [add_im,hwim]
    apply (abs_add_le ..).trans
    dsimp [q]; linarith
  have him' : 2≤|(ρ+w).im| := by
    have hi := abs_sub (ρ.im+t) ρ.im
    rw [add_sub_cancel_left] at hi
    rw [add_im,hwim]; linarith
  have hre : 1/2≤(ρ+w).re := by rw [add_re,hwre]; linarith [hx.1]
  have hz : ‖riemannZeta (ρ+w)‖ ≤ 4*C*q := by
    apply (HC hre him').trans
    nlinarith only [mul_le_mul_of_nonneg_left him hC,mul_le_mul_of_nonneg_left hq hC]
  have hx' : |x|≤2 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hw : ‖w‖≤3*q := by
    have hw := norm_add_le (x:ℂ) ((t:ℂ)*I)
    simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hw
    change ‖(x:ℂ)+t*I‖ ≤ _
    dsimp [q] at hq ⊢
    linarith
  have hlin : ‖1+w/(ρ-1)‖≤L*q := by
    apply (norm_add_le ..).trans
    rw [norm_one,norm_div]
    calc 1+‖w‖/‖ρ-1‖ ≤ q+(3*q)/‖ρ-1‖ := add_le_add hq (div_le_div_of_nonneg_right hw (norm_nonneg _))
         _ = _ := by dsimp [L]; ring
  have hY0 : 0<Y := by linarith
  have hy : ‖(Y:ℂ)^w‖≤Y^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0,hwre,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hY (by simpa using hx.2)
  have hden : q^7≤‖rieszDenom 6 w‖ := by simpa only [hwim,q] using rieszDenom_six_norm_ge w
  change ‖rieszDetectorIntegrand X ρ Y w‖ ≤ _
  rw [rieszDetectorIntegrand,norm_div,norm_mul,norm_mul,norm_mul]
  have hM := norm_rieszMobiusPolynomial_le X (show 0≤(ρ+w).re by linarith)
  change _ ≤ P at hM
  calc _ ≤ (4*C*q*P*(L*q)*Y^2)/q^7 := div_le_div₀ (by positivity) (by gcongr)
            (pow_pos hq0 _) hden
       _ = U*(q^2/q^7) := by dsimp [U]; ring
       _ ≤ U*(2/(1+q^2)) := by
         have h₁ := pow_le_pow_right₀ hq (show 2≤7 by decide)
         have h₂ := pow_le_pow_right₀ hq (show 4≤7 by decide)
         apply mul_le_mul_of_nonneg_left _ hU
         rw [div_le_div_iff₀ (pow_pos hq0 _) (by positivity)]
         nlinarith only [h₁,h₂]
       _ = (2*U)/(1+t^2) := by dsimp [q]; rw [sq_abs]; ring

set_option maxHeartbeats 1400000 in
/-- Move the full mollified Riesz integral from real part two to the line
on which the zeta argument has real part one half. -/
theorem rieszDetector_shift (X : ℕ) {ρ : ℂ} {Y : ℝ} (hY : 1≤Y)
    (hβ : 1/2<ρ.re) (hβ' : ρ.re<1) (_hγ : 1≤ρ.im) (hz : riemannZeta ρ=0) :
    (∫ t : ℝ, rieszDetectorIntegrand X ρ Y ((2:ℂ)+t*I)) =
      ∫ t : ℝ, rieszDetectorIntegrand X ρ Y (((1/2-ρ.re:ℝ):ℂ)+t*I) := by
  let a : ℝ := 1/2-ρ.re
  have hρ : ρ≠1 := by intro he; simp [he] at hβ'
  have he (x t : ℝ) (hx : x≠0) (hs : ρ.re+x≠1) :
      regularKernel X ρ Y ((x:ℂ)+t*I) = rieszDetectorIntegrand X ρ Y ((x:ℂ)+t*I) := by
    apply regularKernel_eq (ρ:=ρ) (w:=(x:ℂ)+t*I) hρ hz _ _ X Y
    · intro hw
      exact hx (by simpa using congrArg Complex.re hw)
    · intro hw
      exact hs (by simpa using congrArg Complex.re hw)
  obtain ⟨D,hD,H⟩ := detector_tail X hβ hβ' hY
  have htail (x : ℝ) (hx : x∈Set.Icc a 2) (t : ℝ) (ht : |ρ.im|+4≤|t|) :
      ‖regularKernel X ρ Y ((x:ℂ)+t*I)‖ ≤ D/(1+t^2) := by
    have hw : (x:ℂ)+t*I≠0 := by
      intro hw
      have him : t=0 := by simpa using congrArg Complex.im hw
      rw [him,abs_zero] at ht
      linarith only [ht,abs_nonneg ρ.im]
    have hs : ρ+((x:ℂ)+t*I)≠1 := by
      intro hs
      have him : ρ.im+t=0 := by simpa using congrArg Complex.im hs
      have heq : t = -ρ.im := by linarith only [him]
      rw [heq,abs_neg] at ht; linarith only [ht]
    rw [regularKernel_eq (w:=(x:ℂ)+t*I) hρ hz hw hs X Y]
    exact H x hx t ht
  have shift := integral_verticalLine_eq_of_strip_tail (F:=regularKernel X ρ Y)
    (a:=a) (b:=2) (D:=D) (T:=|ρ.im|+4)
    (by dsimp [a]; linarith only [hβ]) (differentiable_regular hβ' X hY) hD htail
  have hleft (t : ℝ) := he a t (by dsimp [a]; linarith only [hβ])
    (by dsimp [a]; linarith)
  have hright (t : ℝ) := he 2 t (by norm_num) (by linarith only [hβ])
  calc _ = ∫ t : ℝ, regularKernel X ρ Y (((2:ℝ):ℂ)+t*I) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun t => by simpa only [Complex.ofReal_ofNat] using (hright t).symm)
       _ = ∫ t : ℝ, regularKernel X ρ Y ((a:ℂ)+t*I) := shift.symm
       _ = _ := integral_congr_ae (Filter.Eventually.of_forall hleft)

end AnalyticNumberTheory.RiemannZeta
