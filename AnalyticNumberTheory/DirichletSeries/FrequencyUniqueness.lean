import AnalyticNumberTheory.DirichletSeries.FrequencyConvergence

/-! # Recovering general Dirichlet coefficients on the real axis -/

noncomputable section

open Complex Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a b : ℕ → ℂ} {σ₀ : ℝ}

/-- Beyond a point of ordered convergence on the real axis, the error after
`n` terms decays at the exponential rate of the first omitted frequency. -/
theorem ConvergesAt.real_remainder (h : F.ConvergesAt a (σ₀ : ℂ)) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, σ₀ < t →
      ‖F.sum a t - F.partialSum a t n‖ ≤ B * Real.exp (-t * F n) := by
  obtain ⟨C,hC,hbound⟩ := h.exists_bound
  refine ⟨2*C*Real.exp (σ₀ * F n) + ‖a n‖, by positivity, ?_⟩
  intro t ht
  have hshift : (σ₀ : ℂ) + ((t-σ₀ : ℝ) : ℂ) = (t : ℂ) := by push_cast; ring
  have H := F.norm_partialSum_sub_sum_le a (s₀ := (σ₀ : ℂ)) (α := 0) (C := C)
    (fun u _ => by simpa using hbound u) (z := ((t-σ₀ : ℝ) : ℂ)) (by simpa using sub_pos.mpr ht) n
  rw [hshift, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht),
    ofReal_re, sub_zero, div_self (sub_ne_zero.mpr ht.ne'), ← norm_neg, neg_sub] at H
  have hterm : ‖a n * Complex.exp (-(t : ℂ) * F n)‖ = ‖a n‖ * Real.exp (-t * F n) := by
    simp [Complex.norm_exp,Complex.mul_re]
  calc
    _ = ‖(F.sum a t - F.partialSum a t (n+1)) + a n * Complex.exp (-(t : ℂ) * F n)‖ := by
      rw [partialSum_succ]; congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add H hterm.le
    _ = _ := by
      rw [add_mul, mul_assoc (2*C), ← Real.exp_add, show σ₀ * F n + -t * F n = -(t-σ₀)*F n by ring]
      ring

/-- Each coefficient is recovered by subtracting the preceding terms and
multiplying by its own exponential weight as the real argument tends to infinity.
A single point of ordered convergence suffices. -/
theorem tendsto_coefficient (h : F.ConvergesAt a (σ₀ : ℂ)) (n : ℕ) :
    Tendsto (fun t : ℝ => Complex.exp ((t : ℂ)*F n) * (F.sum a t - F.partialSum a t n))
      atTop (𝓝 (a n)) := by
  obtain ⟨B,_,hB⟩ := h.real_remainder (n+1)
  have hg := F.strictMono (Nat.lt_succ_self n)
  have hdecay : Tendsto (fun t : ℝ => B * Real.exp ((F n - F (n+1)) * t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hg))).const_mul B
  have htail : Tendsto (fun t : ℝ => Complex.exp ((t : ℂ)*F n) * (F.sum a t - F.partialSum a t (n+1)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hdecay
    filter_upwards [eventually_gt_atTop σ₀] with t ht
    rw [norm_mul, Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ ≤ Real.exp (t*F n) * (B*Real.exp (-t*F (n+1))) := mul_le_mul_of_nonneg_left (hB t ht) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have H := htail.add_const (a n)
  rw [zero_add] at H
  apply H.congr
  intro t
  rw [partialSum_succ]
  have he : Complex.exp ((t : ℂ)*F n) * Complex.exp (-(t : ℂ)*F n) = 1 := by
    rw [← Complex.exp_add, show (t : ℂ)*F n + -(t : ℂ)*F n = 0 by ring, Complex.exp_zero]
  linear_combination (-(a n)) * (he)

/-- If two general Dirichlet series with the same frequencies agree along a
real sequence tending to infinity, their coefficients agree term by term. -/
theorem eq_of_sum_eq_on_seq {σ₁ : ℝ} (ha : F.ConvergesAt a (σ₀ : ℂ)) (hb : F.ConvergesAt b (σ₁ : ℂ))
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (hab : ∀ᶠ m in atTop, F.sum a (t m) = F.sum b (t m)) :
    a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hP (x : ℝ) : F.partialSum a x n = F.partialSum b x n := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]
    have H := (tendsto_coefficient ha n).comp ht
    refine tendsto_nhds_unique (H.congr' ?_) ((tendsto_coefficient hb n).comp ht)
    filter_upwards [hab] with m hm
    dsimp only [Function.comp_apply]
    rw [hm,hP]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
