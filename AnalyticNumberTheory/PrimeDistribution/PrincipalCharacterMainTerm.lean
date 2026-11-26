import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-! # Uniform principal-character main terms at independently chosen endpoints -/

noncomputable section

open Real Complex

namespace AnalyticNumberTheory.PrimeDistribution

/-- A square-root error is absorbed by square-root-logarithmic exponential
decay with any prescribed rate. The coefficient is uniform for x ≥ 1. -/
theorem sqrt_le_exp_sqrtLog_error {x : ℝ} (hx : 1 ≤ x) (b : ℝ) :
    Real.sqrt x ≤ Real.exp (b^2/2)*x*Real.exp (-b*Real.sqrt (Real.log x)) := by
  have hx₀ := zero_lt_one.trans_le hx
  let u := Real.sqrt (Real.log x)
  have hsq : u^2 = Real.log x := Real.sq_sqrt (Real.log_nonneg hx)
  calc Real.sqrt x = Real.exp (Real.log x/2) := by
         rw [← Real.log_sqrt hx₀.le, Real.exp_log (Real.sqrt_pos.mpr hx₀)]
       _ ≤ Real.exp (b^2/2+Real.log x+(-b*u)) := Real.exp_le_exp.mpr (by
         nlinarith only [sq_nonneg (u-b), hsq])
       _ = _ := by rw [Real.exp_add,Real.exp_add,Real.exp_log hx₀]

/-- The contribution from prime powers dividing a level q ≤ x is at most
a constant times sqrt x at every intermediate endpoint. -/
theorem log_modulus_partial_le_sqrt {x y : ℝ} {q : ℕ} [NeZero q]
    (hy : 1 ≤ y) (hyx : y ≤ x) (hq : (q : ℝ) ≤ x) :
    (Real.log q/Real.log 2)*Real.log y ≤ (16/Real.log 2)*Real.sqrt x := by
  have hx := hy.trans hyx
  have hx₀ := zero_lt_one.trans_le hx
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hl : Real.log x ≤ 4*x^(1/4:ℝ) := by
    linarith only [Real.log_le_rpow_div hx₀.le (by norm_num : (0:ℝ)<1/4)]
  have hh := pow_le_pow_left₀ (Real.log_nonneg hx) hl 2
  have hp : (x^(1/4:ℝ))^2 = Real.sqrt x := by
    rw [← Real.rpow_mul_natCast hx₀.le, Real.sqrt_eq_rpow]
    norm_num
  rw [mul_pow, hp] at hh
  have hprod := mul_le_mul (Real.log_le_log (zero_lt_one.trans_le hq₁) hq)
    (Real.log_le_log (zero_lt_one.trans_le hy) hyx) (Real.log_nonneg hy) (Real.log_nonneg hx)
  calc _ = (Real.log q*Real.log y)/Real.log 2 := by ring
       _ ≤ (16*Real.sqrt x)/Real.log 2 := div_le_div_of_nonneg_right
         (hprod.trans (by nlinarith only [hh])) (by positivity)
       _ = _ := by ring

/-- The de la Vallée Poussin remainder for ψ(y) can be bounded at the
upper scale x, simultaneously for every real 1 ≤ y ≤ x and x ≥ 2. -/
theorem abs_psi_sub_id_uniform_exp :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ {x y : ℝ}, 2 ≤ x → 1 ≤ y → y ≤ x →
      |Chebyshev.psi y-y| ≤ C*x*Real.exp (-b*Real.sqrt (Real.log x)) := by
  obtain ⟨A,hA,c,hc,H⟩ := abs_psi_sub_id_le_exp
  let b := c/2
  let B := Real.log 4+4
  have hb : 0 < b := half_pos hc
  have hB : 0 < B := by dsimp only [B]; positivity
  let K := 2*(B+1)*Real.exp (b^2/2)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨b,A+K,hb,by positivity,?_⟩
  intro x y hx hy hyx
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := zero_lt_one.trans_le hx₁
  have hy₀ := zero_lt_one.trans_le hy
  by_cases h : y ≤ 2*Real.sqrt x
  · have htriv : |Chebyshev.psi y-y| ≤ (B+1)*y := by
      have hl : Chebyshev.psi y ≤ B*y := psi_le_const_mul_self hy₀.le
      exact abs_le.mpr ⟨by nlinarith only [Chebyshev.psi_nonneg (x:=y),mul_nonneg hB.le hy₀.le],
        by nlinarith only [hl,hy₀.le]⟩
    have hscale := sqrt_le_exp_sqrtLog_error hx₁ b
    calc _ ≤ (B+1)*(2*Real.sqrt x) := htriv.trans
               (mul_le_mul_of_nonneg_left h (by positivity))
         _ ≤ (B+1)*(2*(Real.exp (b^2/2)*x*Real.exp (-b*Real.sqrt (Real.log x)))) := by gcongr
         _ = K*x*Real.exp (-b*Real.sqrt (Real.log x)) := by dsimp only [K]; ring
         _ ≤ _ := by gcongr; linarith only [hA]
  · have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx₁
    have hy₂ : 2 ≤ y := by linarith only [h,hs]
    have hlog := Real.log_le_log (Real.sqrt_pos.mpr hx₀)
      (show Real.sqrt x ≤ y by linarith only [h,hs])
    rw [Real.log_sqrt hx₀.le] at hlog
    have hu := Real.sqrt_le_sqrt (show Real.log x ≤ 4*Real.log y by
      linarith only [hlog,Real.log_nonneg hy])
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt (4:ℝ) = 2 from (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)] at hu
    have he : -c*Real.sqrt (Real.log y) ≤ -b*Real.sqrt (Real.log x) := by
      dsimp only [b]
      linarith only [mul_le_mul_of_nonneg_left hu hc.le]
    exact (H y hy₂).trans (mul_le_mul
      (mul_le_mul (by linarith only [hK] : A ≤ A+K) hyx hy₀.le (by positivity))
      (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity))

/-- The principal character has the linear main term y−1 with a common
exponentially small error throughout 1 ≤ y ≤ x, for every positive q ≤ x. -/
theorem principal_psi_sub_linear_uniform_exp :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ {x y : ℝ} {q : ℕ} [NeZero q],
      2 ≤ x → (q : ℝ) ≤ x → 1 ≤ y → y ≤ x →
      ‖psiChar y (1 : DirichletCharacter ℂ q) - ((y-1 : ℝ) : ℂ)‖ ≤
        C*x*Real.exp (-b*Real.sqrt (Real.log x)) := by
  obtain ⟨b,A,hb,hA,H⟩ := abs_psi_sub_id_uniform_exp
  let B := 16/Real.log 2+1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨b,A+B*Real.exp (b^2/2),hb,by positivity,?_⟩
  intro x y q _ hx hq hy hyx
  have hx₁ := hy.trans hyx
  let P := psiChar y (1 : DirichletCharacter ℂ q)
  let S : ℂ := Chebyshev.psi y
  have hp : ‖P-S‖ ≤ (16/Real.log 2)*Real.sqrt x :=
    (norm_sub_rev P S).le.trans ((norm_psi_sub_psiChar_one_le hy (NeZero.pos q)).trans
      (log_modulus_partial_le_sqrt hy hyx hq))
  have hs : ‖S-(y : ℂ)‖ ≤ A*x*Real.exp (-b*Real.sqrt (Real.log x)) := by
    simpa only [S, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using H hx hy hyx
  have he : P-((y-1 : ℝ) : ℂ) = ((P-S)+(S-(y : ℂ)))+1 := by push_cast; ring
  change ‖P-((y-1 : ℝ) : ℂ)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_one]
  apply (add_le_add ((norm_add_le _ _).trans (add_le_add hp hs)) (le_refl 1)).trans
  have hroot := Real.one_le_sqrt.mpr hx₁
  have hc := mul_le_mul_of_nonneg_left (sqrt_le_exp_sqrtLog_error hx₁ b) hB.le
  dsimp only [B] at hc ⊢
  linarith only [hc,hroot]

end AnalyticNumberTheory.PrimeDistribution
