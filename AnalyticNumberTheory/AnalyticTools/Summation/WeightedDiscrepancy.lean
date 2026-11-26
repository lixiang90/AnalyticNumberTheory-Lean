import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.WeightedIntegrals

/-!
# Partial summation of a counting discrepancy

Compare a weighted discrete count on (a,b] with the density of a differentiable main term.
A nonnegative decreasing weight costs at most twice its value at the left endpoint.
-/

open Finset MeasureTheory

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- Suppose all partial sums on `[a,b]` differ from `F` by at most `M`, and `w` is a
nonnegative decreasing differentiable weight. The weighted count over `(a,b]` differs from
the integral of `w F'` by at most `2 M w(a)`, also when either endpoint carries an atom. -/
theorem norm_weighted_sum_sub_integral_of_partial_sums {a b M : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (c : ℕ → ℂ) (F g : ℝ → ℂ) (w w' : ℝ → ℝ)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (g t) t) (hg : ContinuousOn g (Set.Icc a b))
    (hw : ∀ t ∈ Set.Icc a b, HasDerivAt w (w' t) t) (hd : ContinuousOn w' (Set.Icc a b))
    (hw₀ : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hd₀ : ∀ t ∈ Set.Icc a b, w' t ≤ 0)
    (hM : ∀ t ∈ Set.Icc a b, ‖(∑ n ∈ Icc 1 ⌊t⌋₊, c n) - F t‖ ≤ M) :
    ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c n * (w n : ℂ)) -
      (∫ t in a..b, g t * (w t : ℂ))‖ ≤ 2 * M * w a := by
  let P (t : ℝ) := ∑ n ∈ Icc 1 ⌊t⌋₊, c n
  let W (t : ℝ) : ℂ := w t
  let D (t : ℝ) : ℂ := w' t
  have hW (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt W (D t) t := (hw t ht).ofReal_comp
  have hD : ContinuousOn D (Set.Icc a b) := Complex.continuous_ofReal.comp_continuousOn hd
  have hFC : ContinuousOn F (Set.Icc a b) := fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have inI {t : ℝ} (ht : t ∈ Set.uIcc a b) : t ∈ Set.Icc a b := by
    simpa only [Set.uIcc_of_le hab] using ht
  have hPint : IntervalIntegrable (fun t => P t * D t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    simpa only [P, mul_comm] using integrableOn_mul_sum_Icc c (m := 1) ha hD.integrableOn_Icc
  have hFint : IntervalIntegrable (fun t => F t * D t) volume a b :=
    (hFC.mul hD).intervalIntegrable_of_Icc hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hF t (inI ht)) (fun t ht => hW t (inI ht))
    (hg.intervalIntegrable_of_Icc hab) (hD.intervalIntegrable_of_Icc hab)
  have habW := abel_summation_Ioc_one c ha hab (fun t ht => (hW t ht).differentiableAt)
    (hD.congr fun t ht => (hW t ht).deriv)
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c n * W n) = P b * W b - P a * W a -
    (∫ t in a..b, P t * deriv W t) at habW
  have hrewrite : (∫ t in a..b, P t * deriv W t) = ∫ t in a..b, P t * D t :=
    intervalIntegral.integral_congr fun t ht => congrArg (P t * ·) (hW t (inI ht)).deriv
  rw [hrewrite] at habW
  have hidentity : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c n * W n) - (∫ t in a..b, g t * W t) =
      (P b - F b) * W b - (P a - F a) * W a - ∫ t in a..b, (P t - F t) * D t := by
    simp_rw [sub_mul]
    rw [habW, intervalIntegral.integral_sub hPint hFint, hparts]
    ring
  have hend (t : ℝ) (ht : t ∈ Set.Icc a b) : ‖(P t - F t) * W t‖ ≤ M * w t := by
    rw [norm_mul, show ‖W t‖ = w t by simp [W, abs_of_nonneg (hw₀ t ht)]]
    exact mul_le_mul_of_nonneg_right (hM t ht) (hw₀ t ht)
  have hEint : IntervalIntegrable (fun t => (P t - F t) * D t) volume a b := by
    simpa only [sub_mul] using hPint.sub hFint
  have hbound : ‖∫ t in a..b, (P t - F t) * D t‖ ≤ M * (w a - w b) := by
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    calc
      _ ≤ ∫ t in a..b, M * (-w' t) := by
        apply intervalIntegral.integral_mono_on hab hEint.norm
          ((continuousOn_const.mul hd.neg).intervalIntegrable_of_Icc hab)
        intro t ht
        rw [norm_mul, show ‖D t‖ = -w' t by simp [D, abs_of_nonpos (hd₀ t ht)]]
        exact mul_le_mul_of_nonneg_right (hM t ht) (neg_nonneg.mpr (hd₀ t ht))
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hw t (inI ht))
            (hd.intervalIntegrable_of_Icc hab)]
        ring
  change ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c n * W n) - (∫ t in a..b, g t * W t)‖ ≤ _
  rw [hidentity]
  apply (norm_sub_le ..).trans
  exact (add_le_add ((norm_sub_le ..).trans (add_le_add (hend b ⟨hab, le_rfl⟩)
    (hend a ⟨le_rfl, hab⟩))) hbound).trans_eq (by ring)

end AnalyticNumberTheory.AnalyticTools.Summation
