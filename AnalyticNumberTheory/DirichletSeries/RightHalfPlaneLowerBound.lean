import AnalyticNumberTheory.DirichletSeries.FrequencyDensity

/-! # First nonzero coefficients and lower bounds on a right half-plane -/

noncomputable section

open Complex Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℂ} {r : ℝ}

private lemma norm_term_le_shift {s : ℂ} (hs : r ≤ s.re) {m n : ℕ} (hn : n ≤ m) :
    ‖a m * Complex.exp (-s * F m)‖ ≤
      Real.exp (-(s.re-r)*F n) * (‖a m‖ * Real.exp (-r * F m)) := by
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [show -s.re * F m = -(s.re-r)*F m + -r*F m by ring, Real.exp_add, mul_left_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (F.strictMono.monotone hn) (neg_nonpos.mpr (sub_nonneg.mpr hs))))
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

/-- To the right of an absolute convergence line, the tail after `n` terms
is bounded by its absolute mass on the line times the exponential at the first
omitted frequency. The estimate is uniform in the imaginary part. -/
theorem AbsConvergesAt.norm_sum_sub_partialSum_le (h : F.AbsConvergesAt a (r : ℂ))
    {s : ℂ} (hs : r ≤ s.re) (n : ℕ) :
    ‖F.sum a s - F.partialSum a s n‖ ≤ Real.exp (-(s.re-r)*F n) *
      ∑' k, ‖a (k+n)‖ * Real.exp (-r*F (k+n)) := by
  let c (k : ℕ) := a k * Complex.exp (-s * F k)
  let b (k : ℕ) := ‖a k‖ * Real.exp (-r * F k)
  let D := Real.exp (-(s.re-r)*F n)
  have hsc : F.AbsConvergesAt a s := h.of_re_le (w := s) hs
  have ht : Summable c := hsc
  have hb : Summable b := by
    simpa only [b, Complex.ofReal_re] using (F.absConvergesAt_iff (a := a) (s := (r : ℂ))).mp h
  have htail : Summable (fun k => ‖c (k+n)‖) :=
    (summable_nat_add_iff (f := fun k => ‖c k‖) n).mpr ht.norm
  have hmajor : Summable (fun k => D * b (k+n)) :=
    ((summable_nat_add_iff (f := b) n).mpr hb).mul_left D
  have hsplit : F.sum a s - F.partialSum a s n = ∑' k, c (k+n) := by
    rw [hsc.sum_eq_tsum]
    exact sub_eq_of_eq_add' (ht.sum_add_tsum_nat_add n).symm
  rw [hsplit]
  calc
    ‖∑' k, c (k+n)‖ ≤ ∑' k, ‖c (k+n)‖ := norm_tsum_le_tsum_norm htail
    _ ≤ ∑' k, D * b (k+n) := htail.tsum_le_tsum
      (fun k => norm_term_le_shift (F := F) (a := a) (s := s) (m := k+n) (n := n)
        hs (Nat.le_add_left n k)) hmajor
    _ = _ := by rw [tsum_mul_left]

/-- The absolute mass at a real convergence point bounds the sum throughout
the closed half-plane to its right. -/
theorem AbsConvergesAt.norm_sum_le_right_halfPlane (h : F.AbsConvergesAt a (r : ℂ)) {s : ℂ}
    (hs : r ≤ s.re) : ‖F.sum a s‖ ≤ ∑' k, ‖a k‖ * Real.exp (-r*F k) := by
  have H := h.norm_sum_sub_partialSum_le hs 0
  simp only [partialSum, Finset.range_zero, Finset.sum_empty, sub_zero, Nat.add_zero] at H
  apply H.trans
  apply mul_le_of_le_one_left (tsum_nonneg fun _ => by positivity)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sub_nonneg.mpr hs)) (F.nonneg 0))

/-- To the right of an absolute convergence line each coefficient can be
recovered with unrestricted imaginary part as the real part tends to infinity. -/
theorem AbsConvergesAt.tendsto_scaled_remainder_re_atTop (h : F.AbsConvergesAt a (r : ℂ)) (n : ℕ) :
    Tendsto (fun s : ℂ => Complex.exp (s * F n) * (F.sum a s - F.partialSum a s n))
      (comap Complex.re atTop) (𝓝 (a n)) := by
  let M := ∑' k, ‖a (k+(n+1))‖ * Real.exp (-r * F (k+(n+1)))
  have hre : Tendsto Complex.re (comap Complex.re atTop) atTop := tendsto_comap
  have hgap := sub_neg.mpr (F.strictMono (Nat.lt_succ_self n))
  have hlim := (Real.tendsto_exp_atBot.comp (hre.const_mul_atTop_of_neg hgap)).const_mul
    (M * Real.exp (r * F (n+1)))
  have htail : Tendsto (fun s : ℂ => Complex.exp (s * F n) * (F.sum a s - F.partialSum a s (n+1)))
      (comap Complex.re atTop) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hlim)
    filter_upwards [hre.eventually_ge_atTop r] with s hs
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (s.re*F n) * (Real.exp (-(s.re-r)*F (n+1)) * M) :=
        mul_le_mul_of_nonneg_left (h.norm_sum_sub_partialSum_le hs (n+1)) (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add, mul_comm _ M, mul_assoc M, ← Real.exp_add]
        congr 2
        ring
  have H := htail.add_const (a n)
  rw [zero_add] at H
  apply H.congr
  intro s
  rw [F.partialSum_succ]
  have he : Complex.exp (s * F n) * Complex.exp (-s * F n) = 1 := by
    rw [← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero]
  linear_combination (-(a n)) * he

/-- The first nonzero coefficient bounds the modulus from below at every
height sufficiently far to the right. In particular this half-plane is free
of zeros. -/
theorem AbsConvergesAt.exists_halfPlane_lower_bound (h : F.AbsConvergesAt a (r : ℂ))
    {n : ℕ} (hn : a n ≠ 0) (hprev : ∀ k < n, a k = 0) :
    ∃ B : ℝ, ∀ s : ℂ, B ≤ s.re →
      ‖a n‖ / 2 * Real.exp (-s.re * F n) ≤ ‖F.sum a s‖ := by
  have hp (s : ℂ) : F.partialSum a s n = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hprev k (Finset.mem_range.mp hk), zero_mul]
  have H := (h.tendsto_scaled_remainder_re_atTop n).norm
  simp only [hp, sub_zero, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at H
  have hpos := norm_pos_iff.mpr hn
  have he := H.eventually_const_lt (by linarith : ‖a n‖/2 < ‖a n‖)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨B, fun s hs => ?_⟩
  have hh := (hB s.re hs s rfl).le
  have hx := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-s.re*F n)).le
  rwa [mul_right_comm (Real.exp _) _ _, ← Real.exp_add,
    show s.re*F n + -s.re*F n = 0 by ring, Real.exp_zero, one_mul] at hx

/-- Every nonzero series with a point of absolute convergence is zero-free
throughout some right half-plane, uniformly at all heights. -/
theorem AbsConvergesAt.exists_zeroFree_halfPlane (h : F.AbsConvergesAt a (r : ℂ)) (ha : ∃ n, a n ≠ 0) :
    ∃ B : ℝ, ∀ s : ℂ, B ≤ s.re → F.sum a s ≠ 0 := by
  classical
  let n := Nat.find ha
  have hn : a n ≠ 0 := Nat.find_spec ha
  obtain ⟨B, hB⟩ := h.exists_halfPlane_lower_bound hn (fun k hk => not_not.mp (Nat.find_min ha hk))
  refine ⟨B, fun s hs => ?_⟩
  exact norm_pos_iff.mp ((mul_pos (half_pos (norm_pos_iff.mpr hn)) (Real.exp_pos _)).trans_le (hB s hs))

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
