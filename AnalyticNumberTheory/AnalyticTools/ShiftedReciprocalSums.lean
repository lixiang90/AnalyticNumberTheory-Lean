module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # A harmonic bound for shifted reciprocal integers -/

public section

noncomputable section

open Complex Finset

namespace AnalyticNumberTheory.AnalyticTools

/-- For a finite interval of consecutive integers shifted by a complex
number, only a closest point can contribute more than a harmonic sum.
The coefficient of the inverse minimal separation is exactly one. -/
theorem sum_inv_norm_add_nat_le (s : ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i < N, δ ≤ ‖s+(i : ℂ)‖) :
    ∑ i ∈ range N, ‖s+(i : ℂ)‖⁻¹ ≤ δ⁻¹ + 4*(harmonic N : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hδ.le]
  let f (i : ℕ) := ‖s+(i : ℂ)‖⁻¹
  obtain ⟨k, hk, hmin⟩ := (range N).exists_min_image (fun i : ℕ => ‖s+(i : ℂ)‖) (nonempty_range_iff.mpr hN.ne')
  have hkN := mem_range.mp hk
  have hd (i : ℕ) (hi : i < N) : |(i : ℝ)-(k : ℝ)| ≤ 2*‖s+(i : ℂ)‖ := by
    have h := norm_sub_le (s+(i : ℂ)) (s+(k : ℂ))
    rw [add_sub_add_left_eq_sub, ← Complex.ofReal_natCast i, ← Complex.ofReal_natCast k,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    exact h.trans (by simpa only [Complex.ofReal_natCast] using
      (show ‖s+(i : ℂ)‖+‖s+(k : ℂ)‖ ≤ 2*‖s+(i : ℂ)‖ by linarith [hmin i (mem_range.mpr hi)]))
  have hside (i j : ℕ) (hi : i < N) (he : |(i : ℝ)-k| = (j+1 : ℝ)) :
      f i ≤ 2/(j+1 : ℝ) := by
    have hh := hd i hi
    rw [he] at hh
    have hn := hδ.trans_le (hsep i hi)
    dsimp [f]
    rw [inv_eq_one_div, div_le_div_iff₀ hn (by positivity)]
    linarith
  have hh (l : ℕ) (hl : l ≤ N) :
      ∑ j ∈ range l, 2/(j+1 : ℝ) ≤ 2*(harmonic N : ℝ) := by
    rw [harmonic, Rat.cast_sum, mul_sum]
    simp only [Rat.cast_inv, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, div_eq_mul_inv]
    exact sum_le_sum_of_subset_of_nonneg (range_mono hl) (fun i _ _ => by positivity)
  have hleft : ∑ i ∈ range k, f i ≤ 2*(harmonic N : ℝ) := by
    rw [← sum_range_reflect f k]
    apply le_trans (sum_le_sum (g := fun i : ℕ => 2/(i+1 : ℝ)) (fun i hi => ?_)) (hh k hkN.le)
    have hi' := mem_range.mp hi
    apply hside _ i (by omega)
    rw [show k-1-i = k-(i+1) by omega, Nat.cast_sub (by omega : i+1 ≤ k), Nat.cast_add,
      Nat.cast_one, abs_of_nonpos (by linarith)]
    ring
  let L := N-(k+1)
  have hL : k+1+L = N := by dsimp [L]; omega
  have hright : ∑ i ∈ range L, f (k+1+i) ≤ 2*(harmonic N : ℝ) := by
    apply le_trans (sum_le_sum (g := fun i : ℕ => 2/(i+1 : ℝ)) (fun i hi => ?_)) (hh L (by dsimp [L]; omega))
    have hi' := mem_range.mp hi
    apply hside _ i (by omega)
    push_cast
    rw [abs_of_nonneg (by linarith)]
    ring
  have hmid : f k ≤ δ⁻¹ := inv_anti₀ hδ (hsep k hkN)
  change ∑ i ∈ range N, f i ≤ _
  calc
    _ = (∑ i ∈ range k, f i) + f k + ∑ i ∈ range L, f (k+1+i) := by
      conv_lhs => rw [← hL, sum_range_add, sum_range_succ]
    _ ≤ _ := by linarith

end AnalyticNumberTheory.AnalyticTools
