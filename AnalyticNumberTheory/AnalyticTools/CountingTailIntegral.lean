import AnalyticNumberTheory.AnalyticTools.LogPowerTailIntegral
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Reciprocal-square tails from a logarithmic counting expansion -/

noncomputable section

open Filter Real Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- Transfer an expansion N(u) = a u log u + b u + c + O(log u) to the
integral for its reciprocal-square tail. The constant c cancels exactly. -/
theorem reciprocalSquare_counting_integral_estimate {N : ℝ → ℝ} (hN : Measurable N)
    {a b c K : ℝ} (hK : 0 ≤ K)
    (H : ∀ u : ℝ, 2 ≤ u → |N u - (a*u*Real.log u+b*u+c)| ≤ K*Real.log u)
    {T : ℝ} (hT : 2 ≤ T) :
    |(∫ u in Ioi T, 2*(N u - N T)*u^(-3:ℝ)) - (a*Real.log T+2*a+b)/T| ≤
      4*K*Real.log T/T^2 := by
  have hT₁ : 1 ≤ T := by linarith
  have hT₀ : 0 < T := by linarith
  have hl : 1/2 ≤ Real.log T := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hT)
  let B := 2*T*(a*Real.log T+b)
  let G (u : ℝ) := (2*a)*(Real.log u*u^(-2:ℝ))+(2*b)*u^(-2:ℝ)-B*u^(-3:ℝ)
  let F (u : ℝ) := 2*(N u-N T)*u^(-3:ℝ)
  have h₂ := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT₀
  have h₃ := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hT₀
  have h₂' : (∫ u in Ioi T, u^(-2:ℝ)) = T⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hT₀]; norm_num [Real.rpow_neg_one]
  have h₃' : (∫ u in Ioi T, u^(-3:ℝ)) = 1/(2*T^2) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hT₀]; norm_num [Real.rpow_neg hT₀.le]; ring
  have hlog₂ := integral_log_mul_rpow_tail hT₁ (p:=1) one_pos
  have hlog₃ := integral_log_mul_rpow_tail hT₁ (p:=2) two_pos
  rw [show -(1:ℝ)-1 = -2 by norm_num,Real.rpow_neg_one] at hlog₂
  simp only [div_one,one_pow] at hlog₂
  rw [show -(2:ℝ)-1 = -3 by norm_num,Real.rpow_neg hT₀.le,Real.rpow_two] at hlog₃
  rw [show (2:ℝ)^2 = 4 by norm_num] at hlog₃
  have hiG : IntegrableOn G (Ioi T) :=
    ((hlog₂.1.const_mul (2*a)).add (h₂.const_mul (2*b))).sub (h₃.const_mul B)
  have hG : (∫ u in Ioi T, G u) = (a*Real.log T+2*a+b)/T := by
    dsimp only [G]
    have hPQ : IntegrableOn (fun u : ℝ => (2*a)*(Real.log u*u^(-2:ℝ))+(2*b)*u^(-2:ℝ)) (Ioi T) :=
      (hlog₂.1.const_mul (2*a)).add (h₂.const_mul (2*b))
    rw [integral_sub hPQ (h₃.const_mul B),
      integral_add (hlog₂.1.const_mul (2*a)) (h₂.const_mul (2*b)),integral_const_mul,integral_const_mul,
      integral_const_mul,h₂',h₃',hlog₂.2]
    dsimp only [B]
    field_simp [hT₀.ne']
    ring
  have hbound (u : ℝ) (hu : T ≤ u) :
      ‖F u - G u‖ ≤ (4*K)*(Real.log u*u^(-3:ℝ)) := by
    have hu0 := hT₀.trans_le hu
    let P (x:ℝ) := a*x*Real.log x+b*x+c
    have hp : u*u^(-3:ℝ) = u^(-2:ℝ) := by
      rw [mul_comm,← Real.rpow_add_one hu0.ne']; norm_num
    have hEq : F u-G u = 2*((N u-P u)-(N T-P T))*u^(-3:ℝ) := by
      dsimp only [F,G,P,B]
      rw [←hp]
      ring
    have he := (abs_sub (N u-P u) (N T-P T)).trans (add_le_add (H u (hT.trans hu)) (H T hT))
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_log hT₀ hu) hK
    rw [hEq,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_pos two_pos]
    calc
      _ ≤ (4*K*Real.log u)*u^(-3:ℝ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hu0.le _)
      _ = _ := by ring
  have hmes : Measurable F := (measurable_const.mul (hN.sub measurable_const)).mul (measurable_id.pow_const _)
  have hiE : IntegrableOn (fun u => F u-G u) (Ioi T) := by
    apply (hlog₃.1.const_mul (4*K)).mono' (hmes.aestronglyMeasurable.sub hiG.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with u hu using hbound u hu.le
  have hiF : IntegrableOn F (Ioi T) := by
    convert hiE.add hiG using 1
    ext u; exact (sub_add_cancel _ _).symm
  change |(∫ u in Ioi T, F u) - _| ≤ _
  rw [←hG,←integral_sub hiF hiG,←Real.norm_eq_abs]
  calc
    _ ≤ ∫ u in Ioi T, (4*K)*(Real.log u*u^(-3:ℝ)) := by
      apply norm_integral_le_of_norm_le (hlog₃.1.const_mul _)
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with u hu using hbound u hu.le
    _ = (4*K)*(T^2)⁻¹*(Real.log T/2+1/4) := by rw [integral_const_mul,hlog₃.2]; ring
    _ ≤ _ := by
      calc _ ≤ (4*K)*(T^2)⁻¹*Real.log T := by
             apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
           _ = _ := by ring

end AnalyticNumberTheory.AnalyticTools
