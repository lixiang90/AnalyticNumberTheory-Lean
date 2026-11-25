import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaContours
import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaGamma
import AnalyticNumberTheory.PrimeDistribution.TwistedPerron

/-!
# Completing and regularizing the Perron integral

The right vertical integral is expressed using the completed L-function, an
archimedean correction, and the subtracted numerator at zero.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

/-- Exact complex completion of the finite Perron integral. The last term
accounts for subtracting the value of its numerator at the origin. -/
theorem twistedPerron_completion_identity {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hq : 2≤q) {x c T : ℝ} (hx : 0<x) (hc : 1<c) :
    dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) x c T =
      -(1/(2*Real.pi:ℂ)) * (
        perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T-
        perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T+
        perronVertical (fun s => logDeriv χ.LFunction s/s) c T) := by
  let p (t : ℝ) := (c:ℂ)+t*I
  let W := perronDifferenceWeight x
  let F := logDeriv χ.LFunction
  let G := characterGammaLogCorrection χ
  let V := fun (h : ℝ→ℂ) => ∫ t in (-T)..T,h t
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hr (t : ℝ) : (p t).re=c := by simp [p]
  have hL (t : ℝ) : χ.LFunction (p t)≠0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by rw [hr]; linarith)
  have hpn (t : ℝ) : p t≠0 := by intro he; have := hr t; rw [he] at this; simp at this; linarith
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hdF : Continuous (fun t => F (p t)) := by
    exact (((hf.contDiff (n:=1)).continuous_deriv le_rfl).comp hp).div (hf.continuous.comp hp) hL
  have hdG : Continuous (fun t => G (p t)) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_characterGammaLogCorrection χ (by rw [hr]; linarith)).continuousAt.comp hp.continuousAt
  have hdW : Continuous (fun t => W (p t)) := (differentiable_perronDifferenceWeight x).continuous.comp hp
  have hsplit (t : ℝ) : logDeriv (DirichletCharacter.completedLFunction χ) (p t)=F (p t)+G (p t) :=
    logDeriv_completedLFunction_eq_add_gammaFactor_eq χ hq (.inl hχ) (hL t)
      (gammaFactor_ne_zero_of_re_pos χ (by rw [hr]; linarith))
  let J := V (fun t => W (p t)*logDeriv (DirichletCharacter.completedLFunction χ) (p t))
  let K := V (fun t => W (p t)*G (p t))
  let U := V (fun t => F (p t)/p t)
  have hJ : J=V (fun t => W (p t)*F (p t))+K := by
    dsimp only [J,K,V]
    simp_rw [hsplit,mul_add]
    exact intervalIntegral.integral_add ((hdW.mul hdF).intervalIntegrable ..) ((hdW.mul hdG).intervalIntegrable ..)
  have hpoint (t : ℝ) : LSeries (fun n : ℕ => χ n*(Λ n:ℂ)) (p t)*(x:ℂ)^(p t)/p t =
      -(W (p t)*F (p t)+F (p t)/p t) := by
    rw [←(neg_logDeriv_LFunction_eq_LSeries χ (by rw [hr]; exact hc)).2]
    dsimp only [W,F,logDeriv_apply]
    rw [perronDifferenceWeight_eq hx (hpn t)]
    ring
  have he : dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) x c T =
      -(1/(2*Real.pi:ℂ))*(J-K+U) := by
    unfold dirichletContourIntegral
    change 1/(2*Real.pi:ℂ)*(∫ t in (-T)..T, LSeries (fun n : ℕ => χ n*(Λ n:ℂ)) (p t)*(x:ℂ)^(p t)/p t)=_
    simp_rw [hpoint]
    rw [intervalIntegral.integral_neg,intervalIntegral.integral_add (f:=fun t => W (p t)*F (p t))
      (g:=fun t => F (p t)/p t) ((hdW.mul hdF).intervalIntegrable ..)
      ((hdF.div hp hpn).intervalIntegrable ..),hJ]
    dsimp only [U,V]
    ring
  exact he

theorem norm_twistedPerron_le_completed_and_corrections {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hq : 2≤q) {x c T : ℝ} (hx : 0<x) (hc : 1<c) :
    ‖dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) x c T‖ ≤
      ‖perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T‖+
      ‖perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T‖+
      ‖perronVertical (fun s => logDeriv χ.LFunction s/s) c T‖ := by
  let J := perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T
  let K := perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T
  let U := perronVertical (fun s => logDeriv χ.LFunction s/s) c T
  have he : dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) x c T= -(1/(2*Real.pi:ℂ))*(J-K+U) :=
    twistedPerron_completion_identity hχ hq hx hc
  have hn : ‖-(1/(2*Real.pi:ℂ))‖≤1 := by
    rw [norm_neg,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  change _≤‖J‖+‖K‖+‖U‖
  rw [he,norm_mul]
  calc
    _ ≤ ‖J-K+U‖ := (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := (norm_add_le _ _).trans (by linarith [norm_sub_le J K])

theorem archimedean_perron_shift_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {x c T M : ℝ} (hx : 1≤x) (hc : 1<c) (hc' : c≤3/2) (hT : 0<T) (hM : 0≤M)
    (H : ∀ s : ℂ, 1/2≤s.re → s.re≤c → |s.im|≤T → ‖characterGammaLogCorrection χ s‖≤M) :
    ‖perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T‖≤
      12*Real.sqrt x*M*Real.log (1+T) + 2*((x^c+1)/T)*M := by
  let F := fun s : ℂ => perronDifferenceWeight x s*characterGammaLogCorrection χ s
  have hxp : 0<x := by linarith
  have hrect : rectangleBoundary F ⟨1/2,-T⟩ ⟨c,T⟩=0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    intro s hs
    have hsr := hs.1
    change s.re∈uIcc (1/2:ℝ) c at hsr
    rw [uIcc_of_le (by linarith)] at hsr
    exact (((differentiable_perronDifferenceWeight x) s).mul
      (differentiableAt_characterGammaLogCorrection χ (by linarith [hsr.1]))).differentiableWithinAt
  have h := norm_perronVertical_of_boundary hrect
  rw [norm_zero,zero_add] at h
  have hv := norm_perronVertical_weight (F:=characterGammaLogCorrection χ) hxp hT.le
    (σ:=1/2) (by norm_num) hM (fun t ht => H _ (by simp) (by simp; linarith) (by simpa using abs_le.mpr ht))
  rw [←Real.sqrt_eq_rpow] at hv
  have hh (t : ℝ) (ht : |t|=T) := norm_perronHorizontal_weight (F:=characterGammaLogCorrection χ)
    (a:=1/2) (b:=c) hx (by linarith) (t:=t) (by intro he; rw [he,abs_zero] at ht; linarith) hM
    (fun u hu => H _ (by simpa using hu.1) (by simpa using hu.2) (by simpa using ht.le))
  have hplus := hh T (abs_of_pos hT)
  have hminus := hh (-T) (by rw [abs_neg,abs_of_pos hT])
  rw [abs_of_pos hT] at hplus
  rw [abs_neg,abs_of_pos hT] at hminus
  have hsqrt := Real.one_le_sqrt.mpr hx
  have hlog := Real.log_nonneg (by linarith : 1≤1+T)
  have h₁ := mul_le_mul_of_nonneg_right (show Real.sqrt x+1≤2*Real.sqrt x by linarith)
    (mul_nonneg hM hlog)
  have hz : 0≤(x^c+1)/T*M := by positivity
  have h₂ := mul_le_mul_of_nonneg_right (show c-1/2≤1 by linarith) hz
  apply h.trans
  change ‖perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) (1/2) T‖+
    ‖perronHorizontal (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) (1/2) c T‖+
    ‖perronHorizontal (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) (1/2) c (-T)‖≤_
  linarith

end AnalyticNumberTheory.PrimeDistribution
