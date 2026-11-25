import AnalyticNumberTheory.AnalyticTools.HarmonicRemainder
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The diagonal contribution to the critical-line mean square

At the Riemann–Siegel cutoff the diagonal is twice the harmonic sum up
to √(t/(2π)). Its integral has linear coefficient 2γ − 1 and an error
bounded by a constant times √T.
-/
noncomputable section
open Finset Real Set Filter MeasureTheory Asymptotics
open scoped Topology Interval
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private def criticalDiagonalValue (t : ℝ) :=
  2*∑ n∈Finset.Icc 1 ⌊Real.sqrt (t/(2*π))⌋₊, (n:ℝ)⁻¹

private def criticalDiagonalMain (t : ℝ) :=
  t*log (t/(2*π))+(2*eulerMascheroniConstant-1)*t

private theorem diagonal_main_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt criticalDiagonalMain (log (t/(2*π))+2*eulerMascheroniConstant) t := by
  have hc : 0<2*π := by positivity
  have h := (((hasDerivAt_id' t).div_const (2*π)).log (div_pos ht hc).ne')
  have H := ((hasDerivAt_id' t).mul h).add ((hasDerivAt_id' t).const_mul (2*eulerMascheroniConstant-1))
  convert H using 1
  · rfl
  · field_simp [ht.ne',Real.pi_ne_zero] <;> ring

private theorem diagonal_value_error {t : ℝ} (ht : 0<t) :
    |criticalDiagonalValue t-(log (t/(2*π))+2*eulerMascheroniConstant)| ≤ 2*sqrt (2*π)/sqrt t := by
  have hc : 0<2*π := by positivity
  have hy := div_pos ht hc
  have H := harmonic_floor_remainder (Real.sqrt_pos.mpr hy)
  have hz := mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤2)
  rw [←abs_of_nonneg (show (0:ℝ)≤2 by norm_num),←abs_mul] at hz
  simp only [abs_of_nonneg (show (0:ℝ)≤2 by norm_num)] at hz
  rw [Real.log_sqrt hy.le] at hz
  rw [criticalDiagonalValue,sum_inv_eq_harmonic]
  convert hz using 1
  · congr 1
    ring
  · rw [Real.sqrt_div ht.le]
    field_simp

private theorem diagonal_monotone : Monotone criticalDiagonalValue := by
  intro s t hst
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  apply Finset.Icc_subset_Icc_right
  exact Nat.floor_mono (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hst (by positivity)))

/-- The Riemann–Siegel diagonal integral with its explicit linear coefficient
and a uniform square-root error. -/
theorem critical_diagonal_integral_error :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 8*π≤T →
      |(∫ t in (8*π)..T, 2*∑ n∈Finset.Icc 1 ⌊sqrt (t/(2*π))⌋₊,(n:ℝ)⁻¹)-
        (T*log (T/(2*π))+(2*eulerMascheroniConstant-1)*T)|≤C*sqrt T := by
  let a := 8*π
  let D := criticalDiagonalValue
  let F := criticalDiagonalMain
  let f := fun t : ℝ => log (t/(2*π))+2*eulerMascheroniConstant
  let g := fun t : ℝ => 2*sqrt (2*π)/sqrt t
  let G := fun t : ℝ => 4*sqrt (2*π)*sqrt t
  have ha : 1≤a := by dsimp [a]; linarith [Real.pi_gt_three]
  have ha₀ : 0<a := by linarith
  refine ⟨4*sqrt (2*π)+|F a|,by positivity,?_⟩
  intro T hT
  have hT' : a≤T := hT
  have hp {t} (ht : t∈Set.uIcc a T) : 0<t := by
    rw [Set.uIcc_of_le hT'] at ht
    exact ha₀.trans_le ht.1
  have hf : ContinuousOn f (Set.uIcc a T) := fun t ht => by
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    fun_prop (disch := positivity [hp ht])
  have hg : ContinuousOn g (Set.uIcc a T) := fun t ht => by
    apply ContinuousAt.continuousWithinAt
    dsimp [g]
    fun_prop (disch := positivity [hp ht])
  have hmain : (∫ t in a..T, f t)=F T-F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => diagonal_main_deriv (hp ht)) hf.intervalIntegrable
  have hmaj : (∫ t in a..T,g t)=G T-G a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hg.intervalIntegrable
    intro t ht
    have h := (Real.hasDerivAt_sqrt (hp ht).ne').const_mul (4*sqrt (2*π))
    convert h using 1
    dsimp [g]
    ring
  have herr := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) (f:=fun t => D t-f t) (g:=g) hT'
    (Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs]
      exact diagonal_value_error (ha₀.trans ht.1))) hg.intervalIntegrable
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub (diagonal_monotone.intervalIntegrable ..) hf.intervalIntegrable,
    hmain,hmaj] at herr
  have ht₁ : 1≤sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  have hGa : 0≤G a := by dsimp [G]; positivity
  change |(∫ t in a..T,D t)-F T|≤_
  calc _ = |((∫ t in a..T,D t)-(F T-F a))-F a| := by congr 1; ring
       _ ≤ |(∫ t in a..T,D t)-(F T-F a)|+|F a| := abs_sub _ _
       _ ≤ G T-G a+|F a| := add_le_add_left herr _
       _ ≤ _ := by
          have H := le_mul_of_one_le_right (abs_nonneg (F a)) ht₁
          dsimp only [G] at hGa ⊢
          linarith only [hGa,H]

/-- Big-O form of the diagonal asymptotic. -/
theorem critical_diagonal_integral_isBigO :
    (fun T : ℝ => (∫ t in (8*π)..T, 2*∑ n∈Finset.Icc 1 ⌊sqrt (t/(2*π))⌋₊,(n:ℝ)⁻¹)-
       (T*log (T/(2*π))+(2*eulerMascheroniConstant-1)*T)) =O[atTop] Real.sqrt := by
  obtain ⟨C,hC,H⟩ := critical_diagonal_integral_error
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (8*π)] with T hT
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg T)] using H T hT

end AnalyticNumberTheory.RiemannZeta
