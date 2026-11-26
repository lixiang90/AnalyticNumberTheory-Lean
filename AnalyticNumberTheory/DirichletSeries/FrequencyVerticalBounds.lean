import AnalyticNumberTheory.DirichletSeries.FrequencyConvergence

/-! # Uniform growth in a half-plane of ordered convergence -/

noncomputable section

open Complex Filter
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- A finite frequency sum is uniformly bounded throughout a closed right
half-plane by the sum of the absolute terms at its real boundary. -/
theorem norm_partialSum_le_of_re_ge {β : ℝ} {s : ℂ} (hs : β ≤ s.re) (N : ℕ) :
    ‖F.partialSum a s N‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ * Real.exp (-β * F n) := by
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro n _
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hs) (F.nonneg n))) (norm_nonneg _)

variable {F a}

/-- At positive distance from a real point of ordered convergence, the
truncation error is uniformly at most a linear height factor times an
exponentially small factor in the last included frequency. -/
theorem ConvergesAt.uniform_vertical_remainder {r β : ℝ} (h : F.ConvergesAt a (r : ℂ)) (hr : r < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (s : ℂ), β ≤ s.re →
      ‖F.sum a s - F.partialSum a s (n+1)‖ ≤
        K * (1 + |s.im|) * Real.exp (-(β-r) * F n) := by
  obtain ⟨C, hC, hb⟩ := h.exists_bound
  let δ := β-r
  have hδ : 0 < δ := sub_pos.mpr hr
  refine ⟨C*(2+δ⁻¹), by positivity, ?_⟩
  intro n s hs
  let z := s - (r : ℂ)
  have hd : δ ≤ z.re := by simpa [δ, z] using sub_le_sub_right hs r
  have hd0 := hδ.trans_le hd
  have hz : (r : ℂ) + z = s := add_sub_cancel _ _
  have H := F.norm_partialSum_sub_sum_le a (s₀ := (r : ℂ)) (z := z) (α := 0)
    (fun u _ => by simpa using hb u) hd0 n
  rw [hz, sub_zero] at H
  have hnorm : ‖z‖ ≤ z.re + |s.im| := by
    simpa [z, abs_of_pos (sub_pos.mpr (hr.trans_le hs))] using Complex.norm_le_abs_re_add_abs_im z
  have hratio : ‖z‖ / z.re ≤ 1 + |s.im| / δ := by
    calc
      _ ≤ (z.re + |s.im|) / z.re := div_le_div_of_nonneg_right hnorm hd0.le
      _ = 1 + |s.im| / z.re := by rw [add_div, div_self hd0.ne']
      _ ≤ _ := by gcongr
  have hlin : 1 + ‖z‖ / z.re ≤ (2+δ⁻¹) * (1+|s.im|) := by
    simp only [div_eq_mul_inv] at hratio ⊢
    nlinarith only [hratio, inv_nonneg.mpr hδ.le, abs_nonneg s.im]
  rw [norm_sub_rev]
  apply H.trans
  calc
    _ ≤ C * ((2+δ⁻¹) * (1+|s.im|)) * Real.exp (-δ * F n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlin hC)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hd) (F.nonneg n)))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- A closed half-plane strictly inside the half-plane of ordered convergence
has a single linear height bound for the sum, with arbitrary frequencies. -/
theorem norm_sum_le_linear_halfPlane {β : ℝ} (hβ : F.abscissa a < (β : EReal)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, β ≤ s.re → ‖F.sum a s‖ ≤ C * (1 + |s.im|) := by
  obtain ⟨r, hr, hrβ⟩ := exists_real_of_abscissa_lt hβ
  obtain ⟨K, hK, hrem⟩ := hr.uniform_vertical_remainder hrβ
  let B := ∑ n ∈ Finset.range 1, ‖a n‖ * Real.exp (-β * F n)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨K+B, add_nonneg hK hB, fun s hs => ?_⟩
  have hd : Real.exp (-(β-r)*F 0) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hrβ.le)) (F.nonneg 0))
  calc
    ‖F.sum a s‖ ≤ ‖F.sum a s - F.partialSum a s 1‖ + ‖F.partialSum a s 1‖ := norm_le_norm_sub_add _ _
    _ ≤ K*(1+|s.im|)*Real.exp (-(β-r)*F 0) + B :=
      add_le_add (hrem 0 s hs) (F.norm_partialSum_le_of_re_ge a hs 1)
    _ ≤ K*(1+|s.im|)*1 + B := by gcongr
    _ ≤ _ := by nlinarith only [mul_nonneg hB (abs_nonneg s.im)]

/-- The sum is uniformly little-o of the absolute height throughout each
closed half-plane strictly inside the half-plane of ordered convergence.
Both the real part and the sign of the imaginary part may vary. -/
theorem uniform_sublinear_vertical_growth {β : ℝ} (hβ : F.abscissa a < (β : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ s : ℂ, β ≤ s.re → T ≤ |s.im| → ‖F.sum a s‖ ≤ ε * |s.im| := by
  obtain ⟨r, hr, hrβ⟩ := exists_real_of_abscissa_lt hβ
  obtain ⟨K, _, hrem⟩ := hr.uniform_vertical_remainder hrβ
  have hlim : Tendsto (fun n => K * Real.exp (-(β-r)*F n)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (F.tendsto_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr (sub_pos.mpr hrβ)))).const_mul K
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const (by linarith : 0 < ε/4)).exists
  let B := ∑ j ∈ Finset.range (n+1), ‖a j‖ * Real.exp (-β * F j)
  refine ⟨max 1 (2*B/ε), zero_le_one.trans (le_max_left _ _), fun s hs ht => ?_⟩
  have h1 : 1 ≤ |s.im| := (le_max_left _ _).trans ht
  have hB := (div_le_iff₀ hε).mp ((le_max_right _ _).trans ht)
  have hR := hrem n s hs
  have he := mul_le_mul_of_nonneg_right hn.le (by positivity : 0 ≤ 1+|s.im|)
  calc
    ‖F.sum a s‖ ≤ ‖F.sum a s - F.partialSum a s (n+1)‖ + ‖F.partialSum a s (n+1)‖ := norm_le_norm_sub_add _ _
    _ ≤ K*(1+|s.im|)*Real.exp (-(β-r)*F n) + B :=
      add_le_add hR (F.norm_partialSum_le_of_re_ge a hs (n+1))
    _ ≤ _ := by nlinarith only [he, hB, mul_nonneg hε.le (sub_nonneg.mpr h1)]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
