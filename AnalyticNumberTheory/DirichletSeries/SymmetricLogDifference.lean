import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary
import AnalyticNumberTheory.DirichletSeries.SharpPerron

/-! # Recovering midpoint sums by logarithmic central differences -/

noncomputable section

open Filter Finset
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries

private theorem pos_of_one_le {n : ℕ} (hn : 1 ≤ n) : 0 < (n : ℝ) := by exact_mod_cast hn

/-- On any fixed finite index interval containing the cutoff, the first logarithmic mean
is a sum of positive parts in the logarithmic variable. -/
theorem logWeightedSum_exp_eq_sum_max (a : ℕ → ℂ) (u : ℝ) {N : ℕ} (hN : ⌊Real.exp u⌋₊ ≤ N) :
    logWeightedSum a (Real.exp u) =
      ∑ n ∈ Icc 1 N, a n * (max (u-Real.log n) 0 : ℝ) := by
  unfold logWeightedSum
  calc
    _ = ∑ n ∈ Icc 1 ⌊Real.exp u⌋₊, a n * (max (u-Real.log n) 0 : ℝ) := by
      refine sum_congr rfl fun n hn => ?_
      obtain ⟨hn₁, hnx⟩ := mem_Icc.mp hn
      have hp := pos_of_one_le hn₁
      have hlog := (Real.log_le_iff_le_exp hp).mpr ((Nat.le_floor_iff (Real.exp_pos u).le).mp hnx)
      rw [max_eq_left (sub_nonneg.mpr hlog), Real.log_div (Real.exp_pos u).ne' hp.ne', Real.log_exp]
    _ = _ := by
      apply sum_subset (Icc_subset_Icc_right hN)
      intro n hn hout
      have hn₁ := (mem_Icc.mp hn).1
      have hh : ⌊Real.exp u⌋₊ < n := lt_of_not_ge (fun he => hout (mem_Icc.mpr ⟨hn₁, he⟩))
      have hlog := (Real.lt_log_iff_exp_lt (pos_of_one_le hn₁)).mpr ((Nat.floor_lt (Real.exp_pos u).le).mp hh)
      simp [max_eq_right (sub_nonpos.mpr hlog.le)]

private def hingeWeight (t : ℝ) : ℝ := if t = 0 then 1/2 else if 0 < t then 1 else 0

private theorem eventually_hinge_difference (t : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, max (t+h) 0 - max (t-h) 0 = 2*h*hingeWeight t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (neg_pos.mpr ht)).filter_mono nhdsWithin_le_nhds]
      with h hh hsmall
    change 0 < h at hh
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    simp [hingeWeight, ht.ne, not_lt.mpr ht.le]
  · filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    simp [hingeWeight, max_eq_left hh.le, max_eq_right (neg_nonpos.mpr hh.le)]
    ring
  · filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds ht).filter_mono nhdsWithin_le_nhds]
      with h hh hsmall
    change 0 < h at hh
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    simp [hingeWeight, ht.ne', ht]
    ring

private theorem midpointPartialSum_exp_eq_sum_weight (a : ℕ → ℂ) (u : ℝ) {N : ℕ}
    (hN : ⌊Real.exp u⌋₊ ≤ N) :
    midpointPartialSum a (Real.exp u) =
      ∑ n ∈ Icc 1 N, a n * (hingeWeight (u-Real.log n) : ℂ) := by
  unfold midpointPartialSum
  calc
    _ = ∑ n ∈ Icc 1 ⌊Real.exp u⌋₊, a n * (hingeWeight (u-Real.log n) : ℂ) := by
      refine sum_congr rfl fun n hn => ?_
      obtain ⟨hn₁, hnx⟩ := mem_Icc.mp hn
      have hx := (Nat.le_floor_iff (Real.exp_pos u).le).mp hnx
      rcases hx.eq_or_lt with he | hl
      · simp [he, hingeWeight, mul_comm]
      · have hh := sub_pos.mpr ((Real.log_lt_iff_lt_exp (pos_of_one_le hn₁)).mpr hl)
        simp [hl.ne, hingeWeight, hh.ne', hh]
    _ = _ := by
      apply sum_subset (Icc_subset_Icc_right hN)
      intro n hn hout
      have hn₁ := (mem_Icc.mp hn).1
      have hh : ⌊Real.exp u⌋₊ < n := lt_of_not_ge (fun he => hout (mem_Icc.mpr ⟨hn₁, he⟩))
      have hlog := sub_neg.mpr ((Real.lt_log_iff_exp_lt (pos_of_one_le hn₁)).mpr
        ((Nat.floor_lt (Real.exp_pos u).le).mp hh))
      simp [hingeWeight, hlog.ne, not_lt.mpr hlog.le]

/-- At any real logarithmic cutoff, the central difference is exactly the midpoint
partial sum for all sufficiently small positive widths. This includes every jump. -/
theorem eventually_symmetric_logWeightedSum (a : ℕ → ℂ) (u : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logWeightedSum a (Real.exp (u+h)) - logWeightedSum a (Real.exp (u-h))) / (2*(h : ℂ)) =
        midpointPartialSum a (Real.exp u) := by
  let N := ⌊Real.exp (u+1)⌋₊
  have hn {v : ℝ} (hv : v ≤ u+1) : ⌊Real.exp v⌋₊ ≤ N := Nat.floor_mono (Real.exp_le_exp.mpr hv)
  have hall := (eventually_all_finset (Icc 1 N)).mpr (fun n _ => eventually_hinge_difference (u-Real.log n))
  filter_upwards [hall, self_mem_nhdsWithin, (gt_mem_nhds (zero_lt_one : (0 : ℝ)<1)).filter_mono
    nhdsWithin_le_nhds] with h hh hp hsmall
  change 0 < h at hp
  rw [div_eq_iff (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne')),
    logWeightedSum_exp_eq_sum_max a _ (hn (by linarith)), logWeightedSum_exp_eq_sum_max a _ (hn (by linarith)),
    midpointPartialSum_exp_eq_sum_weight a _ (hn (by linarith)), sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hmem
  have he := congrArg (fun v : ℝ => (v : ℂ)) (hh n hmem)
  rw [show u+h-Real.log n = u-Real.log n+h by ring, show u-h-Real.log n = u-Real.log n-h by ring,
    ← mul_sub]
  push_cast at he
  rw [he]
  ring

end AnalyticNumberTheory.DirichletSeries
