import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

/-!
# Rapid vertical decay of the Gamma function

The defining integral on a positive strip and the recurrence give uniform
bounds after multiplication by any fixed power of the imaginary part.
-/

open Complex Real Set MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools

/-- The defining integral bounds the Gamma function by its value on the real axis. -/
theorem norm_Gamma_le_real {z : ℂ} (hz : 0 < z.re) : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Complex.GammaIntegral,Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

private theorem im_pow_mul_norm_Gamma_le (z : ℂ) (ht : z.im ≠ 0) (k : ℕ) :
    |z.im|^k * ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z+k)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hn : z+(k:ℂ) ≠ 0 := by intro h; apply ht; simpa using congrArg Complex.im h
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hn, norm_mul, pow_succ]
    calc
      _ = |z.im| *(|z.im|^k*‖Complex.Gamma z‖) := by ring
      _ ≤ ‖z+k‖*‖Complex.Gamma (z+k)‖ := mul_le_mul
        (by simpa using Complex.abs_im_le_norm (z+(k:ℂ))) ih (by positivity) (norm_nonneg _)

/-- Gamma decreases faster than every inverse power, uniformly on a finite vertical strip. -/
theorem norm_Gamma_strip_rapid_decay {a b : ℝ} (hab : a ≤ b) (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      |z.im|^m * ‖Complex.Gamma z‖ ≤ C := by
  let k := m+⌈-a⌉₊+1
  have hka : 0 < a+k := by dsimp [k]; push_cast; linarith [Nat.le_ceil (-a),Nat.cast_nonneg (α:=ℝ) m]
  have hg : ContinuousOn Real.Gamma (Icc (a+k) (b+k)) := Real.differentiableOn_Gamma_Ioi.continuousOn.mono
    (fun x hx => hka.trans_le hx.1)
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn (f:=Real.Gamma)
    (nonempty_Icc.mpr (show a+(k:ℝ)≤b+k by linarith)) hg
  refine ⟨Real.Gamma x,Real.Gamma_pos_of_pos (hka.trans_le hx.1),?_⟩
  intro z hz ht
  have hσ : (z+k).re ∈ Icc (a+k) (b+k) := by
    simp only [Complex.add_re,Complex.natCast_re]; exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  calc
    _ ≤ |z.im|^k * ‖Complex.Gamma z‖ := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (by dsimp [k]; omega)) (norm_nonneg _)
    _ ≤ ‖Complex.Gamma (z+k)‖ := im_pow_mul_norm_Gamma_le z (fun h => by rw [h,abs_zero] at ht; linarith) k
    _ ≤ _ := (norm_Gamma_le_real (hka.trans_le hσ.1)).trans (hmax hσ)

/-- On a positive strip a polynomial weight can be used at every height, including zero. -/
theorem norm_Gamma_positive_strip_weight {a b : ℝ} (ha : 0<a) (hab : a≤b) (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, z.re∈Icc a b → (1+|z.im|)^m*‖Complex.Gamma z‖≤C := by
  obtain ⟨C,hC,H⟩ := norm_Gamma_strip_rapid_decay hab m
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn (f:=Real.Gamma) (nonempty_Icc.mpr hab)
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun t ht => ha.trans_le ht.1))
  refine ⟨2^m * max C (Real.Gamma x),mul_pos (by positivity) (lt_of_lt_of_le hC (le_max_left ..)),?_⟩
  intro z hz
  by_cases ht : 1 ≤ |z.im|
  · calc
      _ ≤ (2*|z.im|)^m*‖Complex.Gamma z‖ := by gcongr; linarith
      _ = 2^m*(|z.im|^m*‖Complex.Gamma z‖) := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((H z hz ht).trans (le_max_left ..)) (by positivity)
  · apply mul_le_mul _ ((norm_Gamma_le_real (ha.trans_le hz.1)).trans ((hmax hz).trans (le_max_right ..))) (norm_nonneg _) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _

end AnalyticNumberTheory.AnalyticTools
