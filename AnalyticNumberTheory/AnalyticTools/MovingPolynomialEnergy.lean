import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Mean squares with individual entry times

The diagonal separates exactly for a finite sum of continuous complex
waves whose terms enter at different times. Each off-diagonal integral
starts when both terms have entered.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- Restrict a wave to the heights at or above its entry time. -/
def enteredWave (c : ℝ) {E : Type*} [Zero E] (f : ℝ→E) := (Ici c).indicator f

theorem enteredWave_intervalIntegrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) {f : ℝ→E} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (enteredWave c f) volume a b := by
  rw [intervalIntegrable_iff,enteredWave,integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
  exact (hf.intervalIntegrable (μ:=volume) a b).def'.mono_set inter_subset_right

theorem integral_enteredWave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a≤b) (c : ℝ) (f : ℝ→E) :
    (∫t in a..b,enteredWave c f t)=∫t in min b (max a c)..b,f t := by
  by_cases hc : c≤b
  · rw [min_eq_right (max_le hab hc),intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le (max_le hab hc),enteredWave,
      MeasureTheory.integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,inter_comm,←Ioc_inter_Ioi]
    apply setIntegral_congr_set
    exact ae_eq_set_inter (Filter.Eventually.of_forall (fun _ => Iff.rfl)) (Ioi_ae_eq_Ici (a:=c) (μ:=volume)).symm
  · rw [min_eq_left ((le_of_not_ge hc).trans (le_max_right ..)),intervalIntegral.integral_same]
    rw [←intervalIntegral.integral_zero (a:=a) (b:=b) (μ:=volume)]
    apply intervalIntegral.integral_congr
    intro t ht;rw [uIcc_of_le hab] at ht
    exact Set.indicator_of_notMem (show t∉Ici c from fun h => hc (h.trans ht.2)) f

private theorem square_sum_sub_diagonal {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι→ℂ) :
    ‖∑i∈S,g i‖^2-∑i∈S,‖g i‖^2=∑i∈S,∑j∈S,if i=j then 0 else (g i*conj (g j)).re := by
  have he (z : ℂ) : ‖z‖^2=(z*conj z).re := by rw [Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
  rw [he,map_sum,sum_mul,Complex.re_sum,←sum_sub_distrib]
  apply sum_congr rfl;intro i hi
  rw [mul_sum,Complex.re_sum,he]
  have hdiag : (g i*conj (g i)).re=∑j∈S,if i=j then (g i*conj (g j)).re else 0 := by simp [hi]
  rw [hdiag,←sum_sub_distrib];apply sum_congr rfl;intro j _;split_ifs <;>simp

/-- Absolute mean-square error after removing the moving diagonal. Each
remaining complex integral uses the intersection of the two time ranges. -/
theorem moving_polynomial_energy_bound {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι→ℝ) (p : ι→ℝ→ℂ) (hp : ∀i,Continuous (p i)) {a b : ℝ} (hab : a≤b) :
    |∫t in a..b,‖∑i∈S,enteredWave (c i) (p i) t‖^2-∑i∈S,‖enteredWave (c i) (p i) t‖^2|≤
    ∑i∈S,∑j∈S,if i=j then 0 else ‖∫t in min b (max a (max (c i) (c j)))..b,p i t*conj (p j t)‖ := by
  let f := fun i j t => (p i t*conj (p j t)).re
  let K := fun i j => enteredWave (max (c i) (c j)) (f i j)
  let H := fun i j t => if i=j then 0 else K i j t
  have hfi (i j) : Continuous (fun t => p i t*conj (p j t)) := (hp i).mul (Complex.continuous_conj.comp (hp j))
  have hI (i j) : IntervalIntegrable (H i j) volume a b := by
    dsimp only [H];split_ifs
    · exact continuous_const.intervalIntegrable ..
    · exact enteredWave_intervalIntegrable _ (Complex.continuous_re.comp (hfi i j)) _ _
  have he (t : ℝ) : ‖∑i∈S,enteredWave (c i) (p i) t‖^2-∑i∈S,‖enteredWave (c i) (p i) t‖^2=
      ∑i∈S,∑j∈S,H i j t := by
    rw [square_sum_sub_diagonal]
    apply sum_congr rfl;intro i _
    apply sum_congr rfl;intro j _
    change (if i=j then 0 else ((if c i≤t then p i t else 0)*conj (if c j≤t then p j t else 0)).re)=
      (if i=j then 0 else if max (c i) (c j)≤t then (p i t*conj (p j t)).re else 0)
    by_cases hi : c i≤t <;>by_cases hj : c j≤t <;>simp [hi,hj,max_le_iff]
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (f:=fun i t => ∑j∈S,H i j t)
    (fun i _ => intervalIntegrable_iff.mpr (integrable_finsetSum S (fun j _ => (hI i j).def')))]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum;intro i _
  rw [intervalIntegral.integral_finsetSum (f:=fun j t => H i j t) (fun j _ => hI i j)]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum;intro j _
  by_cases hij : i=j
  · simp [H,hij]
  · simp only [H,hij,ite_false,K,integral_enteredWave hab]
    have hR := intervalIntegral.intervalIntegral_re ((hfi i j).intervalIntegrable (μ:=volume) (min b (max a (max (c i) (c j)))) b)
    change (∫t in min b (max a (max (c i) (c j)))..b,f i j t)=_ at hR
    rw [hR];apply Complex.abs_re_le_norm

end AnalyticNumberTheory.AnalyticTools
