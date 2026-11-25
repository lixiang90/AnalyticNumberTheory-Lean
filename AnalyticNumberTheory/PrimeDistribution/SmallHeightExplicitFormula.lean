import AnalyticNumberTheory.PrimeDistribution.PerronZeroWindows
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-! # Small truncation heights in the character explicit formula -/

noncomputable section
open Real Finset
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- At heights up to eight the local zero count and the elementary
Chebyshev bound control the signed remainder even when T is below one. -/
theorem nonprincipal_psi_signed_explicit_small_height :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ≠1 →
      ∀ {x y T : ℝ}, 1≤y → y≤x → 0<T → T≤8 →
      ‖psiChar y χ+characterPerronZeroSum χ y T‖ ≤ C*(x/T)*(1+Real.log ((q : ℝ)*x))^2 := by
  let J := jensenUnitZeroDensityConst
  let B := Real.log 4+4
  have hJ : 0<J := jensenUnitZeroDensityConst_pos
  have hB : 0<B := by dsimp only [B]; positivity
  refine ⟨8*(B+330*J),by positivity,?_⟩
  intro q _ χ hχ x y T hy hyx hT hT₈
  let L := 1+Real.log ((q : ℝ)*x)
  have hx := hy.trans hyx
  have hx₀ := zero_lt_one.trans_le hx
  have hq : (1 : ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  have hqx := one_le_mul_of_one_le_of_one_le hq hx
  have hlog := Real.log_nonneg hqx
  have hL : 1≤L := by dsimp only [L]; linarith only [hlog]
  have hL₀ := zero_le_one.trans hL
  have hsmall : x≤8*(x/T) := by
    calc x = T*(x/T) := (mul_div_cancel₀ _ hT.ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_right hT₈ (div_nonneg hx₀.le hT.le)
  have hlogq : Real.log ((q : ℝ)*(T+3)) ≤ 11*L := by
    have hcompare : (q : ℝ)*(T+3) ≤ 11*((q : ℝ)*x) := by
      calc _ ≤ (q : ℝ)*11 := mul_le_mul_of_nonneg_left (by linarith only [hT₈]) hq₀.le
           _ ≤ 11*((q : ℝ)*x) := by nlinarith only [le_mul_of_one_le_right hq₀.le hx]
    have h := Real.log_le_log (by positivity : 0<(q : ℝ)*(T+3)) hcompare
    rw [Real.log_mul (by norm_num : (11 : ℝ)≠0) (mul_pos hq₀ hx₀).ne'] at h
    dsimp only [L]
    linarith only [h,hlog,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<11)]
  have hcount : (zeroCountL χ T : ℝ) ≤ 330*J*L := by
    apply (zeroCountL_le_mul_log hχ hT.le).trans
    have hpos : 0≤Real.log ((q : ℝ)*(T+3)) := Real.log_nonneg
      (one_le_mul_of_one_le_of_one_le hq (by linarith only [hT]))
    calc
      _ ≤ (3*J*10)*(11*L) := mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith only [hT₈] : T+2≤10) (by positivity)) hlogq hpos (by positivity)
      _ = _ := by ring
  have hz := norm_characterPerronZeroSum_sub_endpoint χ hy (le_refl 1) T
  rw [characterPerronZeroSum_one,sub_zero,abs_of_nonneg (sub_nonneg.mpr hy)] at hz
  have hz' := hz.trans (mul_le_mul hcount (by linarith only [hyx] : y-1≤x) (sub_nonneg.mpr hy) (by positivity))
  have hp := (norm_psiChar_le_const_mul_self (zero_le_one.trans hy) χ).trans (mul_le_mul_of_nonneg_left hyx hB.le)
  have hXL : x ≤ x*L^2 := le_mul_of_one_le_right hx₀.le (one_le_pow₀ hL)
  have hLL : L*x ≤ x*L^2 := by
    rw [mul_comm L]
    exact mul_le_mul_of_nonneg_left (by rw [sq]; exact le_mul_of_one_le_right hL₀ hL) hx₀.le
  apply (norm_add_le _ _).trans ((add_le_add hp hz').trans ?_)
  calc
    _ ≤ (B+330*J)*(x*L^2) := by
      have h₁ := mul_le_mul_of_nonneg_left hXL hB.le
      have h₂ := mul_le_mul_of_nonneg_left hLL (by positivity : 0≤330*J)
      nlinarith only [h₁,h₂]
    _ ≤ (B+330*J)*((8*(x/T))*L^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)) (by positivity)
    _ = _ := by ring

end AnalyticNumberTheory.PrimeDistribution
