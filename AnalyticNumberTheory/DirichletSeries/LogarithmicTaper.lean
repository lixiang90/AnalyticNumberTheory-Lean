import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary

/-! # A finite Dirichlet sum with a linear logarithmic taper -/

noncomputable section

open Finset

namespace AnalyticNumberTheory.DirichletSeries

/-- The coefficients have weight one up to exp(u), followed by the linear
weight (2u − log n)/u up to exp(2u). -/
def logTaperedSum (a : ℕ → ℂ) (u : ℝ) : ℂ :=
  coeffPartialSum a ⌊Real.exp u⌋₊ +
    ∑ n ∈ Ioc ⌊Real.exp u⌋₊ ⌊Real.exp (u+u)⌋₊, a n * (((u+u-Real.log n)/u : ℝ) : ℂ)

/-- Differencing two logarithmic means at u and 2u produces the tapered finite sum,
including at integral endpoints. -/
theorem logTaperedSum_eq_difference (a : ℕ → ℂ) {u : ℝ} (hu : 0 < u) :
    logTaperedSum a u = (logWeightedSum a (Real.exp (u+u)) -
      logWeightedSum a (Real.exp u))/(u : ℂ) := by
  have hxy : Real.exp u ≤ Real.exp (u+u) := Real.exp_le_exp.mpr (by linarith)
  rw [logWeightedSum_sub_eq_short_sum a (Real.exp_pos u) hxy, ← Real.exp_sub,
    add_sub_cancel_right, Real.log_exp, add_div, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hu.ne'),
    Finset.sum_div, logTaperedSum]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn₀ : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_le ⌊Real.exp u⌋₊).trans_lt (mem_Ioc.mp hn).1
  rw [Real.log_div (Real.exp_pos _).ne' hn₀.ne', Real.log_exp, Complex.ofReal_div, mul_div_assoc]

/-- The taper takes values between zero and one, so its norm costs at most the
unweighted sum of coefficient norms up to the outer cutoff. -/
theorem norm_logTaperedSum_le (a : ℕ → ℂ) {u : ℝ} (hu : 0 < u) :
    ‖logTaperedSum a u‖ ≤ ∑ n ∈ Icc 1 ⌊Real.exp (u+u)⌋₊, ‖a n‖ := by
  let A := ⌊Real.exp u⌋₊
  let B := ⌊Real.exp (u+u)⌋₊
  have hAB : A ≤ B := Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hsplit := sum_Ioc_consecutive (fun n : ℕ => ‖a n‖) (Nat.zero_le A) hAB
  rw [← Icc_add_one_left_eq_Ioc, zero_add] at hsplit
  change ‖coeffPartialSum a A + _‖ ≤ ∑ n ∈ Icc 1 B, ‖a n‖
  calc
    _ ≤ ‖coeffPartialSum a A‖ + ‖∑ n ∈ Ioc A B, a n * (((u+u-Real.log n)/u : ℝ) : ℂ)‖ := norm_add_le ..
    _ ≤ (∑ n ∈ Icc 1 A, ‖a n‖) + ∑ n ∈ Ioc A B, ‖a n‖ := by
      apply add_le_add (norm_sum_le ..)
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro n hn
      have hx : Real.exp u < n := (Nat.floor_lt (Real.exp_pos u).le).mp (mem_Ioc.mp hn).1
      have hy : (n : ℝ) ≤ Real.exp (u+u) := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hn).2
      have hn₀ := (Real.exp_pos _).trans hx
      have hl : u < Real.log n := (Real.lt_log_iff_exp_lt hn₀).mpr hx
      have hr : Real.log n ≤ u+u := (Real.log_le_iff_le_exp hn₀).mpr hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr hr) hu.le)]
      exact mul_le_of_le_one_right (norm_nonneg _) ((div_le_one hu).mpr (by linarith))
    _ = ∑ n ∈ Icc 1 B, ‖a n‖ := by simpa only [← Icc_add_one_left_eq_Ioc, zero_add] using hsplit

end AnalyticNumberTheory.DirichletSeries
