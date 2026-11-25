import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Integrating powers and logarithms against the squared Perron denominator -/

noncomputable section

open Real Complex MeasureTheory

namespace AnalyticNumberTheory.AnalyticTools

private lemma critical_weight_bound {q : ℝ} (hq : 1 ≤ q) (t : ℝ) {k : ℕ} (hk : k ≤ 2) :
    let s := (1/2 : ℂ) + t*I
    Real.sqrt (1+‖s‖) * (1 + Real.log (q*(1+‖s‖)))^k / ‖s‖^2 ≤
      5832 * (1+Real.log q)^k * (1+|t|)^(-(5/4 : ℝ)) := by
  intro s
  let W := 1 + |t|
  let U := 1 + ‖s‖
  let L := 1 + Real.log q
  have hq₀ := zero_lt_one.trans_le hq
  have hW : 1 ≤ W := by dsimp only [W]; linarith [abs_nonneg t]
  have hW₀ := zero_lt_one.trans_le hW
  have hU : 1 ≤ U := by dsimp only [U]; linarith [norm_nonneg s]
  have hU₀ := zero_lt_one.trans_le hU
  have hqlog := Real.log_nonneg hq
  have hWlog := Real.log_nonneg hW
  have hL : 0 < L := by dsimp only [L]; linarith
  have hs₁ : 1/2 ≤ ‖s‖ := by simpa [s] using Complex.abs_re_le_norm s
  have hs₂ : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have hs₀ : 0 < ‖s‖ := by linarith
  have hlow : W ≤ 3*‖s‖ := by dsimp only [W]; linarith
  have hhigh : U ≤ 2*W := by
    have ht := norm_add_le (1/2 : ℂ) ((t : ℂ)*I)
    change ‖s‖ ≤ _ at ht
    norm_num [norm_mul] at ht
    dsimp only [U, W]
    linarith [abs_nonneg t]
  have hroot : Real.sqrt U ≤ 2*Real.sqrt W := Real.sqrt_le_iff.mpr
    ⟨by positivity, by nlinarith only [hhigh, hW₀.le, Real.sq_sqrt hW₀.le]⟩
  have hLU₀ := add_nonneg zero_le_one (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq hU))
  have hLU : 1+Real.log (q*U) ≤ 2*L*(1+Real.log W) := by
    have hl := Real.log_le_log hU₀ hhigh
    rw [Real.log_mul (by norm_num) hW₀.ne'] at hl
    rw [Real.log_mul hq₀.ne' hU₀.ne']
    dsimp only [L]
    nlinarith only [hl, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
      hqlog, hWlog, mul_nonneg hqlog hWlog]
  have hlogW : 1 + Real.log W ≤ 9*W^(1/8 : ℝ) := by
    have hh := Real.log_le_rpow_div hW₀.le (by norm_num : (0 : ℝ) < 1/8)
    linarith only [hh, Real.one_le_rpow hW (by norm_num : (0 : ℝ) ≤ 1/8)]
  have hbase : 1+Real.log (q*U) ≤ 18*L*W^(1/8 : ℝ) := hLU.trans
    ((mul_le_mul_of_nonneg_left hlogW (by positivity)).trans_eq (by ring))
  have hwk : (W^(1/8 : ℝ))^k ≤ W^(1/4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hW₀.le]
    apply Real.rpow_le_rpow_of_exponent_le hW
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith
  have hpow : (1+Real.log (q*U))^k ≤ 324*L^k*W^(1/4 : ℝ) := by
    apply (pow_le_pow_left₀ hLU₀ hbase k).trans
    rw [mul_pow, mul_pow]
    have hc : (18 : ℝ)^k ≤ 324 := (pow_le_pow_right₀ (by norm_num) hk).trans_eq (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hwk (by positivity) (by positivity)
  have hden : 1/‖s‖^2 ≤ 9/W^2 := (div_le_div_iff₀ (sq_pos_of_pos hs₀) (sq_pos_of_pos hW₀)).mpr (by
    nlinarith only [pow_le_pow_left₀ hW₀.le hlow 2])
  have he : Real.sqrt W * W^(1/4 : ℝ) / W^2 = W^(-(5/4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hW₀, ← Real.rpow_two, ← Real.rpow_sub hW₀]
    norm_num
  change Real.sqrt U * (1 + Real.log (q*U))^k / ‖s‖^2 ≤ 5832*L^k*W^(-(5/4 : ℝ))
  calc
    _ = (Real.sqrt U * (1+Real.log (q*U))^k) * (1/‖s‖^2) := by ring
    _ ≤ (2*Real.sqrt W * (324*L^k*W^(1/4 : ℝ))) * (9/W^2) :=
      mul_le_mul (mul_le_mul hroot hpow (pow_nonneg hLU₀ _) (by positivity)) hden (by positivity) (by positivity)
    _ = (5832*L^k) * (Real.sqrt W * W^(1/4 : ℝ) / W^2) := by ring
    _ = _ := by rw [he]

/-- A continuous nonnegative function bounded on the critical line by
`A√(1+‖s‖) (1+log(q(1+‖s‖)))^k`, with `k ≤ 2`, is integrable against
`dt/‖s‖²`. Integration preserves the logarithmic power in the modulus. -/
theorem critical_line_perron_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {q A : ℝ} {k : ℕ}, 1 ≤ q → 0 ≤ A → k ≤ 2 →
      ∀ (f : ℝ → ℝ), Continuous f → (∀ t, 0 ≤ f t) →
        (∀ t : ℝ, let s := (1/2 : ℂ) + t*I
          f t ≤ A * (Real.sqrt (1+‖s‖) * (1+Real.log (q*(1+‖s‖)))^k)) →
        Integrable (fun t : ℝ => f t / ‖(1/2 : ℂ) + t*I‖^2) ∧
        (∫ t : ℝ, f t / ‖(1/2 : ℂ) + t*I‖^2) ≤ C*A*(1+Real.log q)^k := by
  let w := fun t : ℝ => (1+|t|)^(-(5/4 : ℝ))
  have hw : Integrable w := by
    simpa only [w, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (5/4 : ℝ)) (by norm_num))
  have hw₀ : 0 ≤ ∫ t, w t := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨5832*(1+∫ t, w t), by positivity, ?_⟩
  intro q A k hq hA hk f hf hf₀ H
  let B := A*5832*(1+Real.log q)^k
  let g := fun t : ℝ => f t / ‖(1/2 : ℂ)+t*I‖^2
  have hlog := Real.log_nonneg hq
  have hbound (t : ℝ) : g t ≤ B*w t := by
    let s := (1/2 : ℂ)+t*I
    apply (div_le_div_of_nonneg_right (H t) (sq_nonneg ‖s‖)).trans
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left (critical_weight_bound hq t hk) hA).trans_eq (by dsimp only [B, w]; ring)
  have hm : Measurable g := hf.measurable.div
    (show Continuous (fun t : ℝ => ‖(1/2 : ℂ)+t*I‖^2) by fun_prop).measurable
  have hg : Integrable g := (hw.const_mul B).mono' hm.aestronglyMeasurable (ae_of_all _ fun t => by
    rw [Real.norm_of_nonneg (div_nonneg (hf₀ t) (sq_nonneg _))]
    exact hbound t)
  refine ⟨hg, (integral_mono hg (hw.const_mul B) hbound).trans ?_⟩
  rw [integral_const_mul]
  dsimp only [B]
  nlinarith only [mul_nonneg hA (pow_nonneg (add_nonneg zero_le_one hlog) k)]

end AnalyticNumberTheory.AnalyticTools
