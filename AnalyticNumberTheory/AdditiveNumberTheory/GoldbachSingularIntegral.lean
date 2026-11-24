import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcIntegral
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The ternary Goldbach singular integral

The full-period integral counts compositions of an integer into three positive parts.
Outside a small interval around zero the geometric sum decays, giving a uniform
estimate for replacing the truncated integral by its full-period value.
-/

noncomputable section
open Finset MeasureTheory
open scoped Classical
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem count_positive_triples (N : ℕ) :
    (∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, if i + j + k = N then 1 else 0) =
      (N - 1).choose 2 := by
  have inner (i j : ℕ) : (∑ k ∈ Icc 1 N, if i + j + k = N then 1 else 0) =
      if i + j < N then 1 else 0 := by
    by_cases hij : i + j < N
    · simp only [hij, ↓reduceIte]
      simp_rw [show ∀ k : ℕ, i + j + k = N ↔ k = N - (i + j) from fun k => by omega]
      rw [sum_ite_eq']
      simp [mem_Icc, show 1 ≤ N - (i + j) by omega]
    · simp only [hij, ↓reduceIte]
      exact sum_eq_zero fun k hk => by
        have hne : i + j + k ≠ N := by have := (mem_Icc.mp hk).1; omega
        simp [hne]
  simp_rw [inner]
  have row (i : ℕ) : (∑ j ∈ Icc 1 N, if i + j < N then 1 else 0) = N - 1 - i := by
    rw [← sum_filter]
    have hh : ((Icc 1 N).filter fun j => i + j < N) = Icc 1 (N - 1 - i) := by
      ext j
      simp only [mem_filter, mem_Icc]
      omega
    rw [hh]
    simp
  simp_rw [row]
  rw [← sum_subset (s₁ := Icc 1 (N - 1)) (Icc_subset_Icc_right (Nat.sub_le N 1))
    (fun i hi hmiss => by simp only [mem_Icc] at hi hmiss; omega)]
  rw [Nat.choose_two_right, ← sum_range_id]
  refine sum_bij (fun i _ => N - 1 - i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    simp only [mem_Icc, mem_range] at *
    omega
  · intro i hi j hj heq
    simp only [mem_Icc] at *
    omega
  · intro m hm
    refine ⟨N - 1 - m, ?_, ?_⟩ <;> simp only [mem_Icc, mem_range] at * <;> omega

/-- At half-width `1/2` the singular integral extracts exactly the number of ordered
triples of positive integers summing to `N`. -/
theorem ternarySingularIntegral_half (N : ℕ) :
    ternarySingularIntegral N (1 / 2) = ((N - 1).choose 2 : ℕ) := by
  have hmain (x : ℝ) : mainExpSum N x = expSum (fun _ => 1) (Icc 1 N) x := by
    simp [mainExpSum, expSum]
  have h := integral_expSum_mul_three_mul_e_neg_shift
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (Icc 1 N) (Icc 1 N) (Icc 1 N) N (-(1 / 2))
  simp only [← hmain, ← sq, ← pow_succ] at h
  rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num] at h
  rw [ternarySingularIntegral, h, ← count_positive_triples N]
  push_cast
  simp only [one_pow]

/-- The geometric sum has norm at most `1 / (2 |β|)` within half a period of zero. -/
theorem norm_mainExpSum_le_inv_two_abs (N : ℕ) {β : ℝ} (hβ : 0 < |β|) (hhalf : |β| ≤ 1 / 2) :
    ‖mainExpSum N β‖ ≤ 1 / (2 * |β|) := by
  have hdabs : ExponentialSums.distToInt |β| = |β| := by
    rw [ExponentialSums.distToInt_eq_min, Int.fract_eq_self.mpr ⟨hβ.le, by linarith⟩,
      min_eq_left (by linarith)]
  have hd : ExponentialSums.distToInt β = |β| := by
    rcases le_or_gt 0 β with h | h
    · simpa only [abs_of_nonneg h] using hdabs
    · rwa [abs_of_neg h, ExponentialSums.distToInt_neg, ← abs_of_neg h] at hdabs
  have hn : ∀ n : ℤ, β ≠ n := (ExponentialSums.distToInt_pos_iff β).mp (hd ▸ hβ)
  exact (ExponentialSums.norm_sum_Icc_one_e_le_min β hn N).trans
    ((min_le_right _ _).trans_eq (by rw [hd]))

private theorem norm_tail_integral_le {f : ℝ → ℂ} (hf : Continuous f)
    {H : ℝ} (hH : 0 < H) (hhalf : H ≤ 1 / 2)
    (hb : ∀ x ∈ Set.Icc H (1 / 2), ‖f x‖ ≤ 1 / (8 * x ^ 3)) :
    ‖∫ x in H..(1 / 2), f x‖ ≤ 1 / (16 * H ^ 2) := by
  have hz : (0 : ℝ) ∉ Set.uIcc H (1 / 2) := by
    rw [Set.uIcc_of_le hhalf]
    exact fun h => hH.not_ge h.1
  have hc : ContinuousOn (fun x : ℝ => 1 / (8 * x ^ 3)) (Set.uIcc H (1 / 2)) := by
    apply continuousOn_const.div (continuous_const.mul (continuous_id.pow 3)).continuousOn
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hz hx
    change (8 : ℝ) * x ^ 3 ≠ 0
    exact mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero _ hx0)
  apply (intervalIntegral.norm_integral_le_integral_norm hhalf).trans
  apply (intervalIntegral.integral_mono_on hhalf (hf.norm.intervalIntegrable _ _)
    hc.intervalIntegrable hb).trans
  have he (x : ℝ) : 1 / (8 * x ^ 3) = (1 / 8) * x ^ (-3 : ℤ) := by
    simp [zpow_neg, div_mul_eq_div_mul_one_div, one_div, mul_comm]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
  norm_num
  field_simp [hH.ne']
  nlinarith [sq_nonneg H]

/-- Removing the two outer pieces of the unit period costs at most `1/(8 H²)`.
The bound is uniform in the truncation length `N`. -/
theorem norm_ternarySingularIntegral_sub_choose_le (N : ℕ) {H : ℝ}
    (hH : 0 < H) (hhalf : H ≤ 1 / 2) :
    ‖ternarySingularIntegral N H - ((N - 1).choose 2 : ℕ)‖ ≤ 1 / (8 * H ^ 2) := by
  let f := fun β : ℝ => mainExpSum N β ^ 3 * e (-β * N)
  have hf : Continuous f :=
    ((continuous_mainExpSum N).pow 3).mul (continuous_e.comp (continuous_neg.mul continuous_const))
  have hb {β : ℝ} (hβ : 0 < |β|) (hh : |β| ≤ 1 / 2) : ‖f β‖ ≤ 1 / (8 * |β| ^ 3) := by
    dsimp only [f]
    rw [norm_mul, norm_e, mul_one, norm_pow]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_mainExpSum_le_inv_two_abs N hβ hh) 3).trans_eq
    ring
  have hpos := norm_tail_integral_le hf hH hhalf (fun x hx => by
    have hx0 : 0 < x := hH.trans_le hx.1
    simpa only [abs_of_pos hx0] using hb (abs_pos.mpr hx0.ne') (by simpa only [abs_of_pos hx0] using hx.2))
  have hneg := norm_tail_integral_le (hf.comp continuous_neg) hH hhalf (fun x hx => by
    have hx0 : 0 < x := hH.trans_le hx.1
    simpa only [Function.comp_apply, abs_neg, abs_of_pos hx0] using
      hb (β := -x) (by simpa only [abs_neg, abs_of_pos hx0] using hx0) (by simpa only [abs_neg, abs_of_pos hx0] using hx.2))
  change ‖∫ x in H..(1 / 2), f (-x)‖ ≤ _ at hneg
  rw [intervalIntegral.integral_comp_neg] at hneg
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-(1 / 2)) (-H)) (hf.intervalIntegrable (-H) H)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-(1 / 2)) H) (hf.intervalIntegrable H (1 / 2))
  rw [← ternarySingularIntegral_half, ternarySingularIntegral, ternarySingularIntegral]
  change ‖(∫ x in (-H)..H, f x) - ∫ x in (-(1 / 2))..(1 / 2), f x‖ ≤ _
  rw [← h2, ← h1, show ∀ u v w : ℂ, v - (u + v + w) = -(u + w) by intros; ring, norm_neg]
  apply (norm_add_le _ _).trans
  exact (add_le_add hneg hpos).trans_eq (by ring)

end AnalyticNumberTheory.AdditiveNumberTheory
