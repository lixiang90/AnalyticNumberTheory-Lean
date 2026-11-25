import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integrating a finite sum over a sliding frequency window -/

noncomputable section

open Finset MeasureTheory

namespace AnalyticNumberTheory.SieveMethods

/-- Each coefficient enters an interval of length one, so sliding the
window over all real centers integrates to the sum of the coefficients. -/
theorem frequencyWindow_integral (S : Finset ℕ) (ξ : ℕ → ℝ) (b : ℕ → ℝ) :
    Integrable (fun u => ∑ n ∈ S.filter (fun n => |u-ξ n|≤1/2),b n) ∧
      (∫ u : ℝ, ∑ n ∈ S.filter (fun n => |u-ξ n|≤1/2),b n)=∑ n ∈ S,b n := by
  let I := fun n : ℕ => Set.Icc (ξ n-1/2) (ξ n+1/2)
  have hf (n : ℕ) : Integrable ( (I n).indicator (fun _ : ℝ => b n)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs:=measure_Icc_lt_top.ne))
  have he : (fun u => ∑ n ∈ S.filter (fun n => |u-ξ n|≤1/2),b n) =
      fun u : ℝ => ∑ n ∈ S,(I n).indicator (fun _ => b n) u := by
    ext u
    rw [sum_filter]
    apply sum_congr rfl; intro n hn
    rw [Set.indicator_apply]
    congr 1
    apply propext
    change |u-ξ n|≤1/2 ↔ _ ≤ _ ∧ _ ≤ _
    rw [abs_le]; constructor <;> intro hh <;> constructor <;> linarith [hh.1,hh.2]
  rw [he]
  refine ⟨integrable_finsetSum S (fun n _ => hf n),?_⟩
  rw [integral_finsetSum S (fun n _ => hf n)]
  apply sum_congr rfl; intro n hn
  rw [integral_indicator measurableSet_Icc, setIntegral_const,Real.volume_real_Icc,smul_eq_mul,max_eq_left (by linarith)]
  ring

end AnalyticNumberTheory.SieveMethods
