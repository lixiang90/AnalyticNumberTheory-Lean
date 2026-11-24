import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogDerivativeDetection
import AnalyticNumberTheory.DirichletLFunctions.LogDerivativePowerSums

/-!
# High derivatives detecting a Dirichlet L-function zero

At the point `1+η+it`, a zero at distance at most `2η` forces a large high
derivative of the logarithmic derivative. The order is proportional to
`1+η log Y` for any conductor bound `Y ≥ q(|t|+2)`.
-/

noncomputable section

open Complex Metric
open scoped Classical ArithmeticFunction
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletLFunctions

/-- A high logarithmic derivative detects any zero within distance `2η` of the
center `1+η+it`. The lower bound and order parameter are uniform in the family. -/
theorem LFunction_turan_zero_detector :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
    ∀ {t η Y : ℝ}, (q:ℝ)*(|t|+2) ≤ Y → 0 < η → η ≤ 1/1024 → 1 ≤ η*Real.log Y →
    ∀ {ρ : ℂ}, DirichletCharacter.LFunction χ ρ = 0 →
      ‖(((1+η:ℝ):ℂ)+(t:ℂ)*I)-ρ‖ ≤ 2*η →
    ∀ {M : ℕ}, C*(1+η*Real.log Y) ≤ M →
      ∃ k ∈ Finset.Ioc M (2*M), (1/64:ℝ)^k ≤
        η^k * ‖signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction χ))
          (((1+η:ℝ):ℂ)+(t:ℂ)*I) (k-1)‖ := by
  obtain ⟨B,hB,H⟩ := norm_logDeriv_LFunction_re_gt_one_le
  refine ⟨16*256^2*(2+B+4224),by positivity,?_⟩
  intro q _ χ hχ t η Y hQ hη hη' hg ρ hz hd M hM
  let c := ((1+η:ℝ):ℂ)+(t:ℂ)*I
  have hcr : c.re = 1+η := by simp [c]
  have hci : c.im = t := by simp [c]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hY : 2 ≤ Y := by nlinarith [abs_nonneg t,mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hY₀ : 0 < Y := by linarith
  have hlog := Real.log_nonneg (by linarith : 1 ≤ Y)
  have hc : 1 < c.re := by linarith
  have hnorm := H χ c hc (by linarith)
  rw [hcr,add_sub_cancel_left] at hnorm
  have hG : 0 < 512*Y^3 := by positivity
  have hlogG : Real.log (512*Y^3) ≤ 12*Real.log Y := by
    rw [Real.log_mul (by norm_num) (by positivity),show (512:ℝ) = 2^9 by norm_num,Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_log (by norm_num) hY]
  have hbound (w : ℂ) (hw : w ∈ sphere c (3/4)) : ‖DirichletCharacter.LFunction χ w / DirichletCharacter.LFunction χ c‖ ≤ 512*Y^3 := by
    have hdist : ‖w-c‖=3/4 := by simpa only [mem_sphere,dist_eq_norm] using hw
    have hr := Complex.abs_re_le_norm (w-c)
    have hi := Complex.abs_im_le_norm (w-c)
    rw [sub_re,hcr,hdist] at hr
    rw [sub_im,hci,hdist] at hi
    have hi' : |w.im|+2 ≤ 2*(|t|+2) := by
      linarith [abs_sub_abs_le_abs_sub w.im t,abs_nonneg t,le_abs_self (w.im-t)]
    have hw' := norm_LFunction_strip_poly_le hχ (by linarith [(abs_le.mp hr).1] : -(1/2:ℝ)≤w.re)
      (by linarith [(abs_le.mp hr).2])
    have hnum : ‖DirichletCharacter.LFunction χ w‖ ≤ 196*Y^2 := by
      apply hw'.trans
      calc
        _ ≤ (49*(q:ℝ)^2)*(2*(|t|+2))^2 := by gcongr; nlinarith [sq_nonneg ((q:ℝ)-1)]
        _ = 196*((q:ℝ)*(|t|+2))^2 := by ring
        _ ≤ _ := by gcongr
    have hinv := norm_inv_LFunction_le_one_add_inv χ hc
    rw [hcr,add_sub_cancel_left] at hinv
    have hrec : 1/η ≤ Real.log Y := (div_le_iff₀ hη).mpr (by linarith only [hg])
    have hmul := mul_le_mul hnum (hinv.trans (by linarith [Real.log_le_sub_one_of_pos hY₀] : 1+1/η ≤ 2*Y))
      (norm_nonneg _) (by positivity)
    rw [div_eq_mul_inv,norm_mul]
    apply hmul.trans; nlinarith [pow_nonneg hY₀.le 3]
  apply local_logDeriv_turan_detector hη hη' hcr
    (((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _))
    (fun u hu => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hu)
    hG hbound (show 0 ≤ 4224*Real.log Y by positivity) (by linarith) hnorm hz hd
  apply le_trans _ hM
  have hηB := mul_le_mul_of_nonneg_right (by linarith : η ≤ 1) hB.le
  have hnon := mul_nonneg (by linarith : 0 ≤ 2+B) (mul_nonneg hη.le hlog)
  have hcancel : η*(1/η) = 1 := by field_simp
  nlinarith only [hηB,hnon,hcancel]

end AnalyticNumberTheory.DirichletLFunctions
