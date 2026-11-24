import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Integrating detection intervals around zeros

A lower bound for one of finitely many polynomials at each covered ordinate,
together with a bound for the local multiplicity, controls the total
multiplicity by integrated squares.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

/-- Integrate the multiplicities on intervals of length `η` around zeros.
All intervals lie in `[-T-1,T+1]`. The orders detecting a zero can vary with
the ordinate and with the zero. -/
theorem weighted_zero_detection_integral {ι κ : Type*} (S : Finset ι) (orders : Finset κ)
    (ord wt : ι → ℝ) (P : κ → ℝ → ℂ) {T η δ K : ℝ}
    (hT : 0 ≤ T) (hη : 0 < η) (hη' : η ≤ 1) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hord : ∀ z ∈ S, |ord z| ≤ T) (hwt : ∀ z ∈ S, 0 ≤ wt z)
    (hcont : ∀ m ∈ orders, Continuous (P m))
    (hmass : ∀ t ∈ Set.Icc (-T-1) (T+1),
      ∑ z ∈ S.filter (fun z => t ∈ Set.Ioc (ord z-η/2) (ord z+η/2)), wt z ≤ K)
    (hdetect : ∀ z ∈ S, ∀ t ∈ Set.Ioc (ord z-η/2) (ord z+η/2),
      ∃ m ∈ orders, δ ≤ ‖P m t‖) :
    δ^2*η*(∑ z ∈ S, wt z) ≤
      K * ∑ m ∈ orders, ∫ t in (-T-1)..(T+1), ‖P m t‖^2 := by
  let W (z : ι) := Set.Ioc (ord z-η/2) (ord z+η/2)
  let f (z : ι) := (W z).indicator (fun _ => wt z)
  have hi (z : ι) : IntervalIntegrable (f z) volume (-T-1) (T+1) := by
    apply Integrable.intervalIntegrable
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hp (m : κ) (hm : m∈orders) : IntervalIntegrable (fun t => ‖P m t‖^2) volume (-T-1) (T+1) :=
    ((hcont m hm).norm.pow 2).intervalIntegrable ..
  have hab : -T-1 ≤ T+1 := by linarith
  have hI (z : ι) (hz : z∈S) : (∫ t in (-T-1)..(T+1), f z t) = η*wt z := by
    have hz' := abs_le.mp (hord z hz)
    have hsub : W z ⊆ Set.Ioc (-T-1) (T+1) := Set.Ioc_subset_Ioc (by linarith) (by linarith)
    rw [intervalIntegral.integral_of_le hab, show f z = (W z).indicator (fun _ => wt z) by rfl,
      setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub]
    change (∫ _ in Set.Ioc (ord z-η/2) (ord z+η/2), wt z) = _
    rw [← intervalIntegral.integral_of_le (by linarith : ord z-η/2 ≤ ord z+η/2)]
    simp only [intervalIntegral.integral_const,smul_eq_mul]
    ring
  have hfi : IntervalIntegrable (fun t => ∑ z ∈ S, f z t) volume (-T-1) (T+1) := by
    have he : (fun t => ∑ z ∈ S, f z t) = ∑ z ∈ S, f z := by ext t; rw [Finset.sum_apply]
    rw [he]; exact IntervalIntegrable.sum S (fun z _ => hi z)
  have hpi : IntervalIntegrable (fun t => ∑ m ∈ orders, ‖P m t‖^2) volume (-T-1) (T+1) := by
    have he : (fun t => ∑ m ∈ orders, ‖P m t‖^2) = ∑ m ∈ orders, (fun t => ‖P m t‖^2) := by ext t; rw [Finset.sum_apply]
    rw [he]; exact IntervalIntegrable.sum orders hp
  have hmain : (∫ t in (-T-1)..(T+1), δ^2*(∑ z ∈ S, f z t)) ≤
      ∫ t in (-T-1)..(T+1), K*(∑ m ∈ orders, ‖P m t‖^2) := by
    apply intervalIntegral.integral_mono_on hab (hfi.const_mul _) (hpi.const_mul _)
    intro t ht
    let Z := S.filter (fun z => t ∈ W z)
    have hF : ∑ z ∈ S, f z t = ∑ z ∈ Z, wt z := by
      rw [Finset.sum_filter]
      exact sum_congr rfl fun z _ => by simp [f,Set.indicator_apply]
    rw [hF]
    by_cases hne : Z.Nonempty
    · obtain ⟨z,hz⟩ := hne
      obtain ⟨m,hm,hval⟩ := hdetect z (mem_filter.mp hz).1 t (mem_filter.mp hz).2
      have hsq : δ^2 ≤ ∑ j ∈ orders, ‖P j t‖^2 := (by gcongr : δ^2≤‖P m t‖^2).trans
        (single_le_sum (f:=fun j => ‖P j t‖^2) (fun _ _ => sq_nonneg _) hm)
      rw [mul_comm K]
      exact mul_le_mul hsq (hmass t ht) (sum_nonneg (fun j hj => hwt j (mem_filter.mp hj).1)) (by positivity)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,sum_empty,mul_zero]
      positivity
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun z _ => hi z),intervalIntegral.integral_finsetSum hp] at hmain
  simpa only [sum_congr rfl hI,←mul_sum,←mul_assoc] using hmain

end AnalyticNumberTheory.PrimeDistribution
