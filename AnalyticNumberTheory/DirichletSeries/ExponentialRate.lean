import AnalyticNumberTheory.DirichletSeries.GeneralFrequency

/-! # Exponential growth along a Dirichlet frequency -/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (g : ℕ → ℂ)

/-- Upper exponential rate of a sequence along the frequency. A zero value
has logarithm minus infinity, so eventually zero sequences have rate minus
infinity even when the frequency grows very rapidly. -/
def exponentialRate : EReal := by
  classical
  exact limsup (fun n => if g n = 0 then (⊥ : EReal)
    else ((Real.log ‖g n‖ / F n : ℝ) : EReal)) atTop

/-- Above the upper exponential rate the sequence is eventually bounded by
a pure exponential with leading constant one. -/
theorem eventually_norm_le_exp_of_exponentialRate_lt {t : ℝ}
    (ht : F.exponentialRate g < (t : EReal)) :
    ∀ᶠ n in atTop, ‖g n‖ ≤ Real.exp (t * F n) := by
  classical
  unfold exponentialRate at ht
  filter_upwards [eventually_lt_of_limsup_lt ht, F.tendsto_atTop.eventually_gt_atTop 0] with n hn hpos
  by_cases hg : g n = 0
  · simpa only [hg, norm_zero] using (Real.exp_pos (t * F n)).le
  · simp only [hg, ↓reduceIte] at hn
    exact ((Real.log_le_iff_le_exp (norm_pos_iff.mpr hg)).mp
      ((div_lt_iff₀ hpos).mp (EReal.coe_lt_coe_iff.mp hn)).le)

/-- An exponent above the rate admits a single multiplicative bound for all
indices, including the initial terms. -/
theorem exists_bound_of_exponentialRate_lt {t : ℝ} (ht : F.exponentialRate g < (t : EReal)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖g n‖ ≤ C * Real.exp (t * F n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (F.eventually_norm_le_exp_of_exponentialRate_lt g ht)
  let b (n : ℕ) := ‖g n‖ / Real.exp (t * F n)
  have hb (n : ℕ) : 0 ≤ b n := div_nonneg (norm_nonneg _) (Real.exp_pos _).le
  let S := ∑ k ∈ Finset.range N, b k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hb k
  refine ⟨1 + S, by linarith, fun n => (div_le_iff₀ (Real.exp_pos _)).mp ?_⟩
  change b n ≤ 1 + S
  by_cases hn : n < N
  · have hsingle : b n ≤ S := Finset.single_le_sum (fun k _ => hb k) (Finset.mem_range.mpr hn)
    linarith
  · have htail : b n ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (hN n (Nat.le_of_not_gt hn))
    linarith

/-- Any eventual exponential majorant bounds the upper rate. Its leading
constant disappears upon division by the frequency. -/
theorem exponentialRate_le_of_eventually_norm_le {t C : ℝ}
    (h : ∀ᶠ n in atTop, ‖g n‖ ≤ C * Real.exp (t * F n)) :
    F.exponentialRate g ≤ (t : EReal) := by
  classical
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r hr
  have hrt : 0 < r - t := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hr)
  have hC := (Real.tendsto_exp_atTop.comp (F.tendsto_atTop.const_mul_atTop hrt)).eventually_ge_atTop C
  unfold exponentialRate
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [h, hC, F.tendsto_atTop.eventually_gt_atTop 0] with n hn hCn hpos
  by_cases hg : g n = 0
  · simp [hg]
  · simp only [hg, ↓reduceIte]
    rw [EReal.coe_le_coe_iff, div_le_iff₀ hpos, Real.log_le_iff_le_exp (norm_pos_iff.mpr hg)]
    calc
      ‖g n‖ ≤ C * Real.exp (t * F n) := hn
      _ ≤ Real.exp ((r-t) * F n) * Real.exp (t * F n) :=
        mul_le_mul_of_nonneg_right hCn (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
