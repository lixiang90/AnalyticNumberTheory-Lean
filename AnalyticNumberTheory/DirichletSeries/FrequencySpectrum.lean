import AnalyticNumberTheory.DirichletSeries.FrequencyUniqueness

/-! # Coefficients indexed by their real exponents -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- The coefficient at a real exponent, extended by zero outside the
frequency sequence. This records the series independently of zero terms
inserted in its representation. -/
def coefficientAt : ℝ → ℂ := Function.extend F.exponent a (fun _ => 0)

@[simp] theorem coefficientAt_exponent (n : ℕ) : F.coefficientAt a (F n) = a n :=
  F.strictMono.injective.extend_apply _ _ _

theorem coefficientAt_of_notMem_range {u : ℝ} (hu : u ∉ Set.range F.exponent) :
    F.coefficientAt a u = 0 := Function.extend_apply' _ _ _ hu

/-- The finite set of exponents included at a real cutoff. -/
def exponentsThrough (u : ℝ) : Finset ℝ := (Finset.range (F.count u)).image F.exponent

theorem mem_exponentsThrough {u v : ℝ} : v ∈ F.exponentsThrough u ↔ v ≤ u ∧ v ∈ Set.range F.exponent := by
  classical
  simp only [exponentsThrough, Finset.mem_image, Finset.mem_range, lt_count_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨hn, n, rfl⟩
  · rintro ⟨hu, n, rfl⟩
    exact ⟨n, hu, rfl⟩

/-- One may compute a real-cutoff sum over any finite collection of
exponents up to the cutoff that contains the series' own exponents. -/
theorem summatory_eq_sum_coefficientAt {S : Finset ℝ} {u : ℝ} (hs : F.exponentsThrough u ⊆ S)
    (hu : ∀ v ∈ S, v ≤ u) (s : ℂ) :
    F.summatory a s u = ∑ v ∈ S, F.coefficientAt a v * Complex.exp (-s * v) := by
  classical
  have hsame := Finset.sum_subset (f := fun v : ℝ => F.coefficientAt a v * Complex.exp (-s * v))
    hs (fun v hv hnot => by
      rw [F.coefficientAt_of_notMem_range a (fun hin => hnot (F.mem_exponentsThrough.mpr ⟨hu v hv, hin⟩)), zero_mul])
  rw [← hsame, exponentsThrough, Finset.sum_image (fun _ _ _ _ h => F.strictMono.injective h)]
  simp only [F.coefficientAt_exponent, summatory, partialSum]

/-- After every exponent through `u` is removed, the remainder on the real
axis decays faster than `exp(-vt)` for each `v ≤ u`. The next exponent
strictly exceeds `u` even when the cutoff lies in a large gap. -/
theorem ConvergesAt.tendsto_scaled_cutoff_remainder {F : DirichletFrequency} {a : ℕ → ℂ}
    {σ : ℝ} (h : F.ConvergesAt a (σ : ℂ)) {u v : ℝ} (hv : v ≤ u) :
    Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * v) * (F.sum a t - F.summatory a t u))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := h.real_remainder (F.count u)
  have hnext : u < F (F.count u) := lt_of_not_ge fun hn => (lt_irrefl _) (F.lt_count_iff.mpr hn)
  have hlim := (Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr (hv.trans_lt hnext)))).const_mul C
  apply squeeze_zero_norm' _ (by simpa using hlim)
  filter_upwards [eventually_gt_atTop σ] with t ht
  rw [norm_mul, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ Real.exp (t*v) * (C * Real.exp (-t * F (F.count u))) :=
      mul_le_mul_of_nonneg_left (hC t ht) (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
