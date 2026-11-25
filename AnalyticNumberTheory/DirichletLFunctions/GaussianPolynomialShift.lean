import AnalyticNumberTheory.DirichletLFunctions.ConductorGaussianKernel
import AnalyticNumberTheory.DirichletLFunctions.AbsolutePolynomialBounds
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalCauchyShift
import AnalyticNumberTheory.AnalyticTools.Gamma.VerticalDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Displacement of Gaussian-weighted character polynomials

Shifting the positive line through zero extracts the initial Dirichlet
polynomial. All error integrals are normalized by the central gamma factor.
-/

open Real Complex Finset Set MeasureTheory Filter
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

/-- A normalized Gaussian Mellin integral of a Dirichlet series or polynomial. -/
noncomputable def characterGaussianMean {q : ℕ} (χ : DirichletCharacter ℂ q) (t c : ℝ) (f : ℂ→ℂ) :=
  ∫ v : ℝ,characterGaussianKernel χ t c v*f ((1/2:ℂ)+t*I+((c:ℂ)+v*I))

private theorem gaussian_integrable : Integrable (fun v : ℝ => Real.exp (-v^2/2)) := by
  convert integrable_exp_neg_mul_sq (by norm_num : 0<(1/2:ℝ)) using 1
  ext v; congr 1; ring

/-- A bounded vertical factor can be taken out of a Gaussian integral at
the cost of the precise conductor length to the power `c`. -/
theorem norm_characterGaussianMean_le {c : ℝ} (hc : -(1/2:ℝ)<c) (hc₀ : c≠0) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
      (f : ℂ→ℂ) {B : ℝ},0≤B →
      (∀ v : ℝ,‖f ((1/2:ℂ)+t*I+((c:ℂ)+v*I))‖≤B) →
      ‖characterGaussianMean χ t c f‖≤C*(conductorLength q t)^c*B := by
  obtain ⟨K,hK,H⟩ := norm_characterGaussianKernel_le hc hc₀
  let J := ∫ v : ℝ,Real.exp (-v^2/2)
  have hJ : 0≤J := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨K*(1+J),by positivity,?_⟩
  intro q _ χ t f B hB hf
  let E := K*(conductorLength q t)^c*B
  have hX := one_le_conductorLength (q:=q) t
  have hE : 0≤E := mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _)) hB
  apply (norm_integral_le_of_norm_le (gaussian_integrable.const_mul E) (Filter.Eventually.of_forall (fun v => ?_))).trans
  · rw [integral_const_mul]
    change E*J≤_; dsimp [E]; nlinarith only [hE]
  · rw [norm_mul]; apply (mul_le_mul (H χ t v) (hf v) (norm_nonneg _) (by positivity)).trans_eq
    dsimp [E]; ring

theorem integrable_characterGaussianMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {c : ℝ} (hc : -(1/2:ℝ)<c) (hc₀ : c≠0) (f : ℂ→ℂ) {B : ℝ} (hB : 0≤B)
    (hcont : Continuous (fun v : ℝ => f ((1/2:ℂ)+t*I+((c:ℂ)+v*I))))
    (hf : ∀ v : ℝ,‖f ((1/2:ℂ)+t*I+((c:ℂ)+v*I))‖≤B) :
    Integrable (fun v : ℝ => characterGaussianKernel χ t c v*f ((1/2:ℂ)+t*I+((c:ℂ)+v*I))) := by
  obtain ⟨K,hK,H⟩ := norm_characterGaussianKernel_le hc hc₀
  let E := K*(conductorLength q t)^c*B
  apply (gaussian_integrable.const_mul E).mono' ((continuous_characterGaussianKernel χ t hc hc₀).mul hcont).aestronglyMeasurable
  filter_upwards with v
  change ‖characterGaussianKernel χ t c v*f _‖≤_
  rw [norm_mul]
  apply (mul_le_mul (H χ t v) (hf v) (norm_nonneg _) ((norm_nonneg _).trans (H χ t v))).trans_eq
  dsimp [E]; ring

private theorem characterGaussianMean_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t c : ℝ) (f : ℂ→ℂ) :
    let s := (1/2:ℂ)+t*I
    characterGaussianMean χ t c f = verticalCauchyIntegral
      (fun w => χ.gammaFactor (s+w)*f (s+w)*conductorWeight q w*Complex.exp (w^2)) c / χ.gammaFactor s := by
  dsimp only [characterGaussianMean,verticalCauchyIntegral]
  rw [←integral_div]
  apply integral_congr_ae; filter_upwards with v
  dsimp only [characterGaussianKernel]; ring

/-- The full right-line integral normalized by the central gamma factor. -/
theorem completedLGaussianIntegral_div_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {c : ℝ} (hc : -(1/2:ℝ)<c) :
    let s := (1/2:ℂ)+t*I
    completedLGaussianIntegral χ s c/χ.gammaFactor s=characterGaussianMean χ t c χ.LFunction := by
  dsimp only
  rw [characterGaussianMean_eq]
  unfold completedLGaussianIntegral verticalCauchyIntegral
  apply congrArg (fun u : ℂ => u/χ.gammaFactor ((1/2:ℂ)+t*I))
  apply integral_congr_ae; filter_upwards with v
  let u := (1/2:ℂ)+t*I+((c:ℂ)+v*I)
  have hu : 0<u.re := by simp [u]; linarith
  have he := completedLFunction_eq_mul_gammaFactor χ (s:=u)
    (Or.inl (by intro h; rw [h] at hu; norm_num at hu))
    (by rw [gammaFactor_eq_Gammaℝ]; apply Complex.Gammaℝ_ne_zero_of_re_pos; simp; linarith [Nat.cast_nonneg (α:=ℝ) (parityExp χ)])
  change χ.completedLFunction u*conductorWeight q _*Complex.exp _/_=χ.gammaFactor u*χ.LFunction u*conductorWeight q _*Complex.exp _/_
  rw [he]; ring

/-- Crossing zero extracts the polynomial multiplied by `2π`. -/
theorem characterGaussianMean_polynomial_shift_to {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (t : ℝ) {c : ℝ} (hc : 0<c) (hc' : c≤1) :
    let P := dirichletPoly (fun n : ℕ => χ n) N
    let s := (1/2:ℂ)+t*I
    characterGaussianMean χ t c P-characterGaussianMean χ t (-(1/4)) P=2*π*P s := by
  let P := dirichletPoly (fun n : ℕ => χ n) N
  let s := (1/2:ℂ)+t*I
  let F (w : ℂ) := χ.gammaFactor (s+w)*P (s+w)*conductorWeight q w*Complex.exp (w^2)
  have hp (w : ℂ) (hw : -(1/4:ℝ)≤w.re) : 0<(s+w).re := by simp [s]; linarith
  have hG (w : ℂ) (hw : -(1/4:ℝ)≤w.re) : 0<(s+w+(parityExp χ:ℂ)).re := by
    exact (hp w hw).trans_le (by simp only [Complex.add_re,Complex.natCast_re]; linarith [Nat.cast_nonneg (α:=ℝ) (parityExp χ)])
  have hdiff : ∀ w : ℂ,w.re∈Icc (-(1/4:ℝ)) c → AnalyticAt ℂ F w := by
    intro w hw
    have hfG : AnalyticAt ℂ (fun z => χ.gammaFactor (s+z)) w := by
      simp_rw [gammaFactor_eq_Gammaℝ]
      have hU : IsOpen {z : ℂ | 0<z.re} := isOpen_lt continuous_const Complex.continuous_re
      have H : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0<z.re} := fun z hz => (differentiableAt_GammaReal hz).differentiableWithinAt
      exact ((H.analyticOnNhd hU) _ (hG w hw.1)).comp (by fun_prop)
    have hP : AnalyticAt ℂ (fun z => P (s+z)) w := ((differentiable_dirichletPoly _ _).analyticAt (s+w)).comp (by fun_prop)
    exact ((hfG.mul hP).mul (differentiable_conductorWeight.analyticAt w)).mul (by fun_prop)
  obtain ⟨G,hG₀,HG⟩ := norm_Gamma_positive_strip_weight (a:=1/8) (b:=5/4) (by norm_num) (by norm_num) 0
  let Q := (q:ℝ)^(1/2:ℝ)
  have hq : (1:ℝ)≤q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hbound (x : ℝ) (hx : x∈Icc (-(1/4:ℝ)) c) (v : ℝ) :
      ‖F ((x:ℂ)+v*I)‖≤G*N*Q*Real.exp 1/(1+v^2) := by
    let w := (x:ℂ)+v*I
    let u := s+w+(parityExp χ:ℂ)
    have hre : u.re=1/2+x+parityExp χ := by simp [s,w,u]
    have hpar : parityExp χ≤1 := by unfold parityExp; split <;> omega
    have hu : (u/2).re∈Icc (1/8:ℝ) (5/4) := by
      rw [Complex.div_ofNat_re,hre]
      constructor <;> linarith only [hx.1,hx.2,hc',Nat.cast_nonneg (α:=ℝ) (parityExp χ),show (parityExp χ:ℝ)≤1 by exact_mod_cast hpar]
    have hgam : ‖χ.gammaFactor (s+w)‖≤G := by
      rw [gammaFactor_eq_Gammaℝ]
      change ‖Complex.Gammaℝ u‖≤_
      rw [Complex.Gammaℝ_def,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have hh := HG (u/2) hu; simp only [pow_zero,one_mul] at hh
      apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
      apply mul_le_of_le_one_left hG₀.le
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      simp; linarith [hu.1,show (u/2).re=u.re/2 by simp]
    have hpol : ‖P (s+w)‖≤N := by
      apply (norm_characterPolynomial_le_power_sum χ N _).trans
      calc _ ≤ ∑ _n∈Finset.Icc 1 N,(1:ℝ) := by
                  apply sum_le_sum; intro n hn
                  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
                  apply neg_nonpos.mpr; exact (hp w (by simpa [w] using hx.1)).le
           _ = _ := by simp
    have hcq : ‖conductorWeight q w‖≤Q := by
      rw [norm_conductorWeight]
      apply Real.rpow_le_rpow_of_exponent_le hq; simp [w]; linarith [hx.2,hc']
    have he : (w^2).re=x^2-v^2 := by simp [w,pow_two]
    have hGauss : Real.exp (w^2).re≤Real.exp 1/(1+v^2) := by
      rw [he,Real.exp_sub]
      apply div_le_div₀ (Real.exp_pos 1).le (Real.exp_le_exp.mpr (by nlinarith [hx.1,hx.2,mul_nonneg (sub_nonneg.mpr hx.1) (show 0≤1-x by linarith [hx.2,hc'])])) (by positivity)
      linarith only [Real.add_one_le_exp (v^2)]
    dsimp only [F]; rw [norm_mul,norm_mul,norm_mul,Complex.norm_exp]
    apply (mul_le_mul (mul_le_mul (mul_le_mul hgam hpol (norm_nonneg _) hG₀.le)
      hcq (norm_nonneg _) (by positivity)) hGauss (Real.exp_pos _).le (by positivity)).trans_eq
    ring
  have H := verticalCauchyIntegral_sub (F:=F) (by norm_num : -(1/4:ℝ)<0) hc hdiff (by positivity) hbound
  dsimp only; rw [characterGaussianMean_eq,characterGaussianMean_eq,←sub_div]
  change (verticalCauchyIntegral F _-verticalCauchyIntegral F _)/χ.gammaFactor s=_
  rw [H]; dsimp [F,conductorWeight]
  have hne : χ.gammaFactor s≠0 := by
    rw [gammaFactor_eq_Gammaℝ]; apply Complex.Gammaℝ_ne_zero_of_re_pos; simp [s]; positivity
  simp; field_simp; ring
  rfl

/-- Crossing zero extracts the polynomial multiplied by `2π`. -/
theorem characterGaussianMean_polynomial_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (t : ℝ) :
    let P := dirichletPoly (fun n : ℕ => χ n) N
    let s := (1/2:ℂ)+t*I
    characterGaussianMean χ t (3/4) P-characterGaussianMean χ t (-(1/4)) P=2*π*P s :=
  characterGaussianMean_polynomial_shift_to χ N t (by norm_num) (by norm_num)

end AnalyticNumberTheory.DirichletLFunctions
