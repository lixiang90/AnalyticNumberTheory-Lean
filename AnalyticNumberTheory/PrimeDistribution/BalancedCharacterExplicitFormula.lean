import AnalyticNumberTheory.PrimeDistribution.RightmostCharacterZeros

/-! # Balancing the real-part and height cutoffs in the character explicit formula -/

noncomputable section

open Finset Real AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- If T² x^σ ≤ x, removing the zeros to the left of σ costs at most the
order of the original Perron error. No restriction on the modulus is required. -/
theorem nonprincipal_psi_balanced_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ {x y T σ : ℝ}, 1 ≤ T → T^2 ≤ x → T^2 * x^σ ≤ x → 1 ≤ y → y ≤ x →
        ‖psiChar y χ + rightmostPerronZeroSum χ y σ T‖ ≤
          C * (x/T) * (1 + Real.log ((q : ℝ)*x))^2 := by
  obtain ⟨C, hC, H⟩ := nonprincipal_psi_rightmost_explicit
  let J := jensenUnitZeroDensityConst
  have hJ : 0 < J := jensenUnitZeroDensityConst_pos
  refine ⟨C + 36*J, by positivity, ?_⟩
  intro q _ χ hχ x y T σ hT hTx hbal hy hyx
  have hx := hy.trans hyx
  have hx₀ := zero_lt_one.trans_le hx
  have hT₀ := zero_lt_one.trans_le hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  let L := 1 + Real.log ((q : ℝ)*x)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith only [Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq hx)]
  have hL₀ := zero_le_one.trans hL
  have hlx : Real.log x ≤ L := by
    dsimp only [L]
    rw [Real.log_mul hq₀.ne' hx₀.ne']
    linarith only [Real.log_nonneg hq]
  have hT' : T ≤ x := (le_mul_of_one_le_right hT₀.le hT).trans (by simpa only [sq] using hTx)
  have hlog : Real.log ((q : ℝ)*(T+3)) ≤ 4*L := by
    have h := Real.log_le_log (by positivity : 0 < (q : ℝ)*(T+3))
      (mul_le_mul_of_nonneg_left (by linarith only [hT',hx] : T+3 ≤ 4*x) hq₀.le)
    rw [show (q : ℝ)*(4*x) = 4*((q : ℝ)*x) by ring,
      Real.log_mul (by norm_num) (mul_pos hq₀ hx₀).ne'] at h
    change Real.log ((q : ℝ)*(T+3)) ≤ 4*(1+Real.log ((q : ℝ)*x))
    change 1 ≤ 1+Real.log ((q : ℝ)*x) at hL
    linarith only [h, hL, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hN : (zeroCountL χ T : ℝ) ≤ 36*J*T*L := by
    apply (zeroCountL_le_mul_log hχ hT₀.le).trans
    calc _ ≤ (3*J*(3*T))*(4*L) := mul_le_mul
           (mul_le_mul_of_nonneg_left (by linarith : T+2 ≤ 3*T) (by positivity))
           hlog (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))) (by positivity)
         _ = _ := by ring
  have hb : T * x^σ ≤ x/T := (le_div_iff₀ hT₀).mpr (by
    convert hbal using 1
    ring)
  have hrest : (zeroCountL χ T : ℝ) * (Real.log x * x^σ) ≤ 36*J*(x/T)*L^2 := by
    calc _ ≤ (36*J*T*L) * (L*x^σ) := mul_le_mul hN
               (mul_le_mul_of_nonneg_right hlx (Real.rpow_nonneg hx₀.le _))
               (mul_nonneg (Real.log_nonneg hx) (Real.rpow_nonneg hx₀.le _)) (by positivity)
         _ = (36*J*L^2) * (T*x^σ) := by ring
         _ ≤ (36*J*L^2) * (x/T) := mul_le_mul_of_nonneg_left hb (by positivity)
         _ = _ := by ring
  apply (H hχ hT₀ hTx hy hyx σ).trans
  change C*(x/T)*L^2 + _ ≤ (C+36*J)*(x/T)*L^2
  linarith only [hrest]

/-- Choosing σ = 1 − 2 log T / log x makes the two cutoffs balance exactly. -/
theorem height_sq_mul_rpow_balanced {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    T^2 * x^(1-2*Real.log T/Real.log x) = x := by
  have hl := (Real.log_pos hx).ne'
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have h : Real.log x*(1-2*Real.log T/Real.log x) = Real.log x - 2*Real.log T := by
    field_simp
  rw [h, Real.exp_sub, Real.exp_log (zero_lt_one.trans hx),
    show 2*Real.log T = Real.log (T^2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (sq_pos_of_pos hT)]
  field_simp

end AnalyticNumberTheory.PrimeDistribution
