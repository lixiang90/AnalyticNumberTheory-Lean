import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary

/-! # Slopes of logarithmic means of nonnegative coefficients -/

noncomputable section

open Finset

namespace AnalyticNumberTheory.DirichletSeries

/-- The slope of a logarithmic mean between two cutoffs is bounded by the
inclusive partial sums of its nonnegative coefficients at the two ends.
The undivided inequalities also hold when the cutoffs coincide. -/
theorem logWeightedSum_increment_bounds (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    let Δ := (logWeightedSum (fun n => (a n : ℂ)) y - logWeightedSum (fun n => (a n : ℂ)) x).re
    (∑ n ∈ Ioc 0 ⌊x⌋₊, a n)*Real.log (y/x) ≤ Δ ∧
      Δ ≤ (∑ n ∈ Ioc 0 ⌊y⌋₊, a n)*Real.log (y/x) := by
  dsimp only
  rw [logWeightedSum_sub_eq_short_sum _ hx hxy]
  have hc : coeffPartialSum (fun n => (a n : ℂ)) ⌊x⌋₊ = ((∑ n ∈ Ioc 0 ⌊x⌋₊,a n : ℝ) : ℂ) := by
    rw [←Icc_add_one_left_eq_Ioc,zero_add,Complex.ofReal_sum]
    rfl
  rw [hc]
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,←Complex.ofReal_add,Complex.ofReal_re]
  have hw (n : ℕ) (hn : n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊) :
      0 ≤ Real.log (y/n) ∧ Real.log (y/n) ≤ Real.log (y/x) := by
    obtain ⟨hnx,hny⟩ := mem_Ioc.mp hn
    have hn' := (Nat.floor_lt hx.le).mp hnx
    have hy' := (Nat.le_floor_iff (hx.trans_le hxy).le).mp hny
    have h₁ := (one_le_div (hx.trans hn')).mpr hy'
    exact ⟨Real.log_nonneg h₁,Real.log_le_log (zero_lt_one.trans_le h₁)
      (div_le_div_of_nonneg_left (hx.trans_le hxy).le hx hn'.le)⟩
  constructor
  · exact le_add_of_nonneg_right (sum_nonneg fun n hn => mul_nonneg (ha n) (hw n hn).1)
  · rw [←sum_Ioc_consecutive a (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxy),add_mul]
    apply add_le_add le_rfl
    rw [Finset.sum_mul]
    exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hw n hn).2 (ha n)

end AnalyticNumberTheory.DirichletSeries
