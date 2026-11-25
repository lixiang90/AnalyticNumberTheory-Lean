import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Tactic.Linarith

/-! # Bounded monotone extensions of a local Jordan decomposition -/

noncomputable section
open Set
namespace AnalyticNumberTheory.AnalyticTools

private def extendMonotone (p : ℝ → ℝ) (a b L u : ℝ) : ℝ :=
  if u < a then 0 else p (min u b) - L

private lemma monotone_extend {p : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hp : MonotoneOn p (Icc a b)) (hL : L ≤ p a) : Monotone (extendMonotone p a b L) := by
  have hmem (t : ℝ) (ht : a ≤ t) : min t b ∈ Icc a b := ⟨le_min ht hab, min_le_right ..⟩
  intro u v huv
  by_cases hv : v < a
  · simp [extendMonotone, hv, huv.trans_lt hv]
  by_cases hu : u < a
  · simp only [extendMonotone, if_pos hu, if_neg hv, sub_nonneg]
    exact hL.trans (hp ⟨le_rfl, hab⟩ (hmem v (le_of_not_gt hv)) (hmem v (le_of_not_gt hv)).1)
  · simp only [extendMonotone, if_neg hu, if_neg hv, sub_le_sub_iff_right]
    exact hp (hmem u (le_of_not_gt hu)) (hmem v (le_of_not_gt hv)) (min_le_min_right b huv)

/-- A real function of bounded variation on a compact interval agrees there
with the difference of two bounded nondecreasing functions on the whole line.
Both extensions vanish below the interval and are constant above it. -/
theorem exists_monotone_extensions_of_boundedVariation {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : BoundedVariationOn f (Icc a b)) :
    ∃ p q : ℝ → ℝ, Monotone p ∧ Monotone q ∧ (∀ t < a, p t = 0 ∧ q t = 0) ∧
      (∀ t, b ≤ t → p t = p b ∧ q t = q b) ∧ EqOn f (p-q) (Icc a b) := by
  obtain ⟨p,q,hp,hq,he⟩ := hv.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  let L := min (p a) (q a)
  refine ⟨extendMonotone p a b L, extendMonotone q a b L,
    monotone_extend hab hp (min_le_left ..), monotone_extend hab hq (min_le_right ..), ?_, ?_, ?_⟩
  · intro t ht
    simp [extendMonotone, ht]
  · intro t ht
    simp [extendMonotone, not_lt.mpr hab, not_lt.mpr (hab.trans ht), min_eq_right ht]
  · intro t ht
    simp only [he, Pi.sub_apply, extendMonotone, if_neg (not_lt.mpr ht.1), min_eq_left ht.2]
    abel

end AnalyticNumberTheory.AnalyticTools
