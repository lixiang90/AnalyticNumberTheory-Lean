import AnalyticNumberTheory.PrimeDistribution.BalancedCharacterExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovSmallConductors

/-! # The character explicit formula at exponential square-root-logarithmic height -/

noncomputable section

open Real AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- For q ≤ exp(κ sqrt(log x)), the rightmost-zero formula has an
exponentially small remainder uniform in every endpoint up to x. -/
theorem nonprincipal_psi_sqrtLog_explicit {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ}, Real.exp 1 ≤ x →
      ∀ {q : ℕ} [NeZero q], (q : ℝ) ≤ Real.exp (κ*Real.sqrt (Real.log x)) →
      ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 → ∀ {y : ℝ}, 1 ≤ y → y ≤ x →
        ‖psiChar y χ + rightmostPerronZeroSum χ y (1-2*κ/Real.sqrt (Real.log x))
          (Real.exp (κ*Real.sqrt (Real.log x)))‖ ≤
          C*x*Real.exp (-(κ/2)*Real.sqrt (Real.log x)) := by
  obtain ⟨B, hB, H⟩ := nonprincipal_psi_balanced_explicit
  obtain ⟨K, hK, hsave⟩ := log_rpow_mul_exp_neg_sqrt_log_le 2 (show 0 < κ/2 by positivity)
  refine ⟨9*B*K, by positivity, ?_⟩
  intro x hx q _ hq χ hχ y hy hyx
  have hx₁ : 1 < x := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx
  have hx₀ := zero_lt_one.trans hx₁
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx₀).mpr hx
  let u := Real.sqrt (Real.log x)
  let T := Real.exp (κ*u)
  have hu : 1 ≤ u := Real.one_le_sqrt.mpr hl
  have hu₀ := zero_lt_one.trans_le hu
  have hsq : u^2 = Real.log x := Real.sq_sqrt (zero_le_one.trans hl)
  have huL : u ≤ Real.log x := by
    rw [←hsq, sq]
    exact le_mul_of_one_le_right hu₀.le hu
  have hT : 1 ≤ T := Real.one_le_exp (mul_nonneg hκ.le hu₀.le)
  have hTx : T^2 ≤ x := by
    calc T^2 = Real.exp (κ*u+κ*u) := by rw [Real.exp_add, sq]
         _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by
           linarith only [mul_le_mul_of_nonneg_right hκ' hu₀.le, huL])
         _ = x := Real.exp_log hx₀
  have he : 1-2*κ/u = 1-2*Real.log T/Real.log x := by
    rw [show Real.log T = κ*u from Real.log_exp _, ←hsq]
    field_simp
  have hb : T^2*x^(1-2*κ/u) ≤ x := by
    rw [he, height_sq_mul_rpow_balanced hx₁ (Real.exp_pos _)]
  have hL : 1+Real.log ((q : ℝ)*x) ≤ 3*Real.log x := by
    have hq₀ : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have hlog := Real.log_le_log hq₀ hq
    change Real.log (q : ℝ) ≤ Real.log (Real.exp (κ*u)) at hlog
    rw [Real.log_exp] at hlog
    rw [Real.log_mul hq₀.ne' hx₀.ne']
    linarith only [hl, huL, hlog, mul_le_mul_of_nonneg_right hκ' hu₀.le]
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL₀ : 0 ≤ 1+Real.log ((q : ℝ)*x) :=
    add_nonneg zero_le_one (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq₁ hx₁.le))
  have hpol : Real.log x ^ (2:ℕ) * Real.exp (-(κ/2)*u) ≤ K := by
    simpa only [Real.rpow_two] using hsave hl
  have hex : T⁻¹ = Real.exp (-(κ/2)*u)*Real.exp (-(κ/2)*u) := by
    dsimp only [T]
    rw [←Real.exp_neg, ←Real.exp_add]
    congr 1
    ring
  apply (H hχ hT hTx hb hy hyx).trans
  calc _ ≤ B*(x/T)*(3*Real.log x)^2 :=
             mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL₀ hL 2) (by positivity)
       _ = (9*B*x*Real.exp (-(κ/2)*u)) * (Real.log x^2*Real.exp (-(κ/2)*u)) := by
             rw [div_eq_mul_inv, hex]
             ring
       _ ≤ (9*B*x*Real.exp (-(κ/2)*u)) * K := mul_le_mul_of_nonneg_left hpol (by positivity)
       _ = _ := by ring

/-- A common real-part cutoff for the classical and Page zero-free regions.
The extra four in the allowed conductor parameter covers the shift Q+2. -/
theorem sqrtLog_zeroFreeThreshold {κ c u a : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hc : 16*κ ≤ c) (hu : 1 ≤ u) (ha : 1 ≤ a) (haT : a ≤ Real.exp (κ*u)+4) :
    1 - c/Real.log (a*(Real.exp (κ*u)+2)) ≤ 1 - 2*κ/u := by
  let T := Real.exp (κ*u)
  have hu₀ := zero_lt_one.trans_le hu
  have hT : 1 ≤ T := Real.one_le_exp (mul_nonneg hκ.le hu₀.le)
  have hT₀ := zero_lt_one.trans_le hT
  have hp : 1 < a*(T+2) := by
    have h := mul_le_mul_of_nonneg_right ha (show 0 ≤ T+2 by linarith)
    linarith only [h, hT]
  have hl : Real.log (a*(T+2)) ≤ 6+2*(κ*u) := by
    have ht := mul_le_mul (haT.trans (by linarith only [hT] : T+4 ≤ 5*T))
      (by linarith only [hT] : T+2 ≤ 3*T) (by linarith : 0 ≤ T+2) (by positivity : 0 ≤ 5*T)
    have hm := Real.log_le_log (zero_lt_one.trans hp) ht
    rw [Real.log_mul (by positivity : (5:ℝ)*T ≠ 0) (by positivity : (3:ℝ)*T ≠ 0),
      Real.log_mul (by norm_num : (5:ℝ) ≠ 0) hT₀.ne', Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hT₀.ne',
      show Real.log T = κ*u from Real.log_exp _] at hm
    linarith only [hm, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5),
      Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  apply sub_le_sub_left
  apply (div_le_div_iff₀ hu₀ (Real.log_pos hp)).mpr
  calc 2*κ*Real.log (a*(T+2)) ≤ 2*κ*(6+2*(κ*u)) :=
         mul_le_mul_of_nonneg_left hl (by positivity)
       _ ≤ (16*κ)*u := by
         nlinarith only [mul_le_mul_of_nonneg_left hu hκ.le,
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ₁ hκ.le) hu₀.le]
       _ ≤ c*u := mul_le_mul_of_nonneg_right hc hu₀.le

end AnalyticNumberTheory.PrimeDistribution
