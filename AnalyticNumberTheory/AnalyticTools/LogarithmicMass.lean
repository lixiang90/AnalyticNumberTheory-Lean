import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! # Mellin weights for a density of logarithmic cumulative mass -/

noncomputable section

open Real Filter Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- If a nonnegative density has cumulative mass at most B + C log X on [1,X],
then its Mellin integral with the extra weight x^(-δ) is at most B + C/δ.
The constants are uniform as δ decreases to zero. -/
theorem mellin_weight_of_logarithmic_mass {f : ℝ → ℝ} {B C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x ≥ 1, 0 ≤ f x) (hloc : ∀ X ≥ 1, IntervalIntegrable f volume 1 X)
    (hmass : ∀ X ≥ 1, ∫ x in (1:ℝ)..X, f x ≤ B+C*Real.log X) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x : ℝ => x^(-δ)*f x) (Ioi 1) ∧
      ∫ x in Ioi (1:ℝ), x^(-δ)*f x ≤ B+C/δ := by
  let w (x : ℝ) := x^(-δ)
  let v (x : ℝ) := C*x⁻¹
  have hw {X : ℝ} (hX : 1 ≤ X) : ContinuousOn w (uIcc 1 X) := by
    rw [uIcc_of_le hX]
    intro x hx
    exact (Real.continuousAt_rpow_const _ _ (.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
  have hv {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable v volume 1 X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hX]
    exact continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => (zero_lt_one.trans_le hx.1).ne'))
  have hweight {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable (fun x => w x*f x) volume 1 X :=
    (hloc X hX).continuousOn_mul (hw hX)
  have htail := (integrableOn_Ioi_rpow_of_lt (by linarith : -δ-1 < -1) (c := (1:ℝ)) zero_lt_one).const_mul C
  have htotal : ∫ x in Ioi (1:ℝ), C*x^(-δ-1) = C/δ := by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp; ring
  have hinterval {X : ℝ} (hX : 1 ≤ X) : ∫ x in (1:ℝ)..X, w x*f x ≤ B+C/δ := by
    have hwdec : AntitoneOn w (Icc 1 X) := fun x hx y _ hxy =>
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (neg_nonpos.mpr hδ.le)
    obtain ⟨u,hu,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
      (f := w) hX (Real.rpow_nonneg (zero_le_one.trans hX) _) hwdec ((hloc X hX).sub (hv hX))
    have hprim : ∫ x in (1:ℝ)..u, (f x-v x) ≤ B := by
      rw [intervalIntegral.integral_sub (hloc u hu.1) (hv hu.1)]
      dsimp only [v]
      rw [intervalIntegral.integral_const_mul,integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hu.1),div_one]
      linarith [hmass u hu.1]
    have hwe : ∫ x in (1:ℝ)..X, (w x*f x-w x*v x) ≤ B := by
      simp only [w,Real.one_rpow,one_mul] at he
      simpa only [mul_sub,w] using he.trans_le hprim
    rw [intervalIntegral.integral_sub (hweight hX) ((hv hX).continuousOn_mul (hw hX))] at hwe
    have hcomp : ∫ x in (1:ℝ)..X, w x*v x ≤ C/δ := by
      rw [intervalIntegral.integral_of_le hX,←htotal]
      calc
        _ = ∫ x in Ioc (1:ℝ) X, C*x^(-δ-1) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro x hx
          dsimp only [w,v]
          rw [Real.rpow_sub_one (zero_lt_one.trans hx.1).ne' (-δ)]
          ring
        _ ≤ _ := setIntegral_mono_set htail ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono (fun x hx =>
          mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hx.le) _))) (ae_of_all _ (fun _ hx => hx.1))
    linarith
  have hi : IntegrableOn (fun x => w x*f x) (Ioi (1:ℝ)) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (B+C/δ) 1 (b := id) (l := atTop) _ tendsto_id
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
      change (∫ x in (1:ℝ)..X, ‖w x*f x‖) ≤ B+C/δ
      apply le_trans _ (hinterval hX)
      apply le_of_eq
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hX] at hx
      exact abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx.1) _) (hf x hx.1))
    · intro X
      rcases le_total 1 X with hX | hX
      · exact (hweight hX).1
      · simp [Ioc_eq_empty hX.not_gt]
  exact ⟨hi,le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_id)
    ((eventually_ge_atTop (1:ℝ)).mono fun X hX => hinterval hX)⟩

end AnalyticNumberTheory.AnalyticTools
