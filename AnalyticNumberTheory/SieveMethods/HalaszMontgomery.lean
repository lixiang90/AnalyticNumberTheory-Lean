import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-!
# The Halász–Montgomery inequality

A finite family of vectors with small pairwise inner products has few large
correlations with a fixed vector. This form applies directly to the vectors
of coefficients of a Dirichlet polynomial. On the imaginary axis, off-diagonal
Gram entries are values of the unit-coefficient Dirichlet polynomial at height
differences. A uniform bound for those entries controls the number of large values.
-/

namespace AnalyticNumberTheory.SieveMethods

open scoped InnerProductSpace ComplexConjugate

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The square of the sum of the absolute correlations is bounded by the
energy of the test vector times the sum of the absolute Gram matrix entries. -/
theorem halasz_montgomery_inequality (s : Finset ι) (v : E) (w : ι → E) :
    (∑ i ∈ s, ‖⟪v, w i⟫_ℂ‖) ^ 2 ≤ ‖v‖ ^ 2 * ∑ i ∈ s, ∑ j ∈ s, ‖⟪w i, w j⟫_ℂ‖ := by
  let c (i : ι) : ℂ := conj ⟪v, w i⟫_ℂ / ‖⟪v, w i⟫_ℂ‖
  have hc (i : ι) : ‖c i‖ ≤ 1 := by
    by_cases h : ⟪v, w i⟫_ℂ = 0
    · simp [c, h]
    · simp only [c, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h), le_refl]
  have hphase (i : ι) : c i * ⟪v, w i⟫_ℂ = (‖⟪v, w i⟫_ℂ‖ : ℂ) := by
    by_cases h : ⟪v, w i⟫_ℂ = 0
    · simp [h]
    · have hn : (↑‖⟪v, w i⟫_ℂ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
      dsimp only [c]
      rw [div_mul_eq_mul_div, mul_comm (conj _), Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow, sq, mul_div_cancel_right₀ _ hn]
  let u := ∑ i ∈ s, c i • w i
  have hu : ‖⟪v, u⟫_ℂ‖ = ∑ i ∈ s, ‖⟪v, w i⟫_ℂ‖ := by
    simp only [u, inner_sum, inner_smul_right, hphase, ← Complex.ofReal_sum,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  have hgram : ‖u‖ ^ 2 ≤ ∑ i ∈ s, ∑ j ∈ s, ‖⟪w i, w j⟫_ℂ‖ := by
    calc
      ‖u‖ ^ 2 = ‖⟪u, u⟫_ℂ‖ := by simp [inner_self_eq_norm_sq_to_K]
      _ = ‖∑ i ∈ s, ∑ j ∈ s, conj (c i) * (c j * ⟪w i, w j⟫_ℂ)‖ := by
        simp only [u, sum_inner]
        simp only [inner_sum, inner_smul_left, inner_smul_right, mul_left_comm]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖⟪w i, w j⟫_ℂ‖ := by
        apply (norm_sum_le _ _).trans
        refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun j _ => ?_
        simpa only [norm_mul, Complex.norm_conj, one_mul] using
          mul_le_mul (hc i) (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
  calc
    (∑ i ∈ s, ‖⟪v, w i⟫_ℂ‖) ^ 2 = ‖⟪v, u⟫_ℂ‖ ^ 2 := by rw [hu]
    _ ≤ (‖v‖ * ‖u‖) ^ 2 := by gcongr; exact norm_inner_le_norm v u
    _ ≤ ‖v‖ ^ 2 * ∑ i ∈ s, ∑ j ∈ s, ‖⟪w i, w j⟫_ℂ‖ := by rw [mul_pow]; gcongr

/-- A threshold for every correlation gives a cardinality bound for the
corresponding set of large values. -/
theorem halasz_montgomery_large_values (s : Finset ι) (v : E) (w : ι → E) {V : ℝ}
    (hV : 0 ≤ V) (h : ∀ i ∈ s, V ≤ ‖⟪v, w i⟫_ℂ‖) :
    ((s.card : ℝ) * V) ^ 2 ≤ ‖v‖ ^ 2 * ∑ i ∈ s, ∑ j ∈ s, ‖⟪w i, w j⟫_ℂ‖ := by
  have hsum : (s.card : ℝ) * V ≤ ∑ i ∈ s, ‖⟪v, w i⟫_ℂ‖ := by
    simpa using Finset.sum_le_sum h
  exact (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hV) hsum 2).trans
    (halasz_montgomery_inequality s v w)

open Finset AnalyticNumberTheory.DirichletSeries

/-- Halász–Montgomery's large-values inequality for a Dirichlet polynomial at finitely
many complex points. On a vertical line the kernel depends only on the difference of
the two heights. -/
theorem halasz_montgomery_dirichletPoly_large_values {ι : Type*} (s : Finset ι)
    (a : ℕ → ℂ) (N : ℕ) (z : ι → ℂ) {V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ s, V ≤ ‖dirichletPoly a N (z i)‖) :
    ((s.card : ℝ) * V) ^ 2 ≤ (∑ n ∈ Icc 1 N, ‖a n‖ ^ 2) *
      ∑ i ∈ s, ∑ j ∈ s, ‖dirichletPoly (fun _ => 1) N (conj (z i) + z j)‖ := by
  classical
  let A := Icc 1 N
  let v : EuclideanSpace ℂ A := WithLp.toLp 2 (fun n => conj (a n))
  let w (i : ι) : EuclideanSpace ℂ A := WithLp.toLp 2 (fun n => ((n : ℕ) : ℂ) ^ (-z i))
  have hvw (i : ι) : ⟪v, w i⟫_ℂ = dirichletPoly a N (z i) := by
    rw [PiLp.inner_apply, dirichletPoly]
    simpa only [v, w, RCLike.inner_apply, PiLp.toLp_apply, Complex.conj_conj, mul_comm]
      using Finset.sum_coe_sort A (fun n => a n * (n : ℂ) ^ (-z i))
  have hv : ‖v‖ ^ 2 = ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [v, PiLp.toLp_apply, Complex.norm_conj]
      using Finset.sum_coe_sort A (fun n => ‖a n‖ ^ 2)
  have hkernel (i j : ι) :
      ⟪w i, w j⟫_ℂ = dirichletPoly (fun _ => 1) N (conj (z i) + z j) := by
    rw [PiLp.inner_apply, dirichletPoly]
    change (∑ n : A, (n.val : ℂ) ^ (-z j) * conj ((n.val : ℂ) ^ (-z i))) = _
    rw [Finset.sum_coe_sort A (fun n => (n : ℂ) ^ (-z j) * conj ((n : ℂ) ^ (-z i)))]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hn).1
    have harg : (n : ℂ).arg ≠ Real.pi := by simpa using Real.pi_ne_zero.symm
    have hc := Complex.cpow_conj (n : ℂ) (-z i) harg
    simp only [map_natCast, map_neg] at hc
    rw [← hc, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn0), one_mul]
    congr 1
    ring
  simpa only [hv, hkernel] using halasz_montgomery_large_values s v w hV
    (fun i hi => (hvw i).symm ▸ hlarge i hi)

/-- A bound `B` for the kernels at the pairwise height differences gives a count
of large values on the imaginary axis. The diagonal kernel is exactly `N`. -/
theorem halasz_montgomery_dirichletPoly_count_le {ι : Type*} (s : Finset ι)
    (a : ℕ → ℂ) (N : ℕ) (t : ι → ℝ) {B V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ s, V ≤ ‖dirichletPoly a N (t i * Complex.I)‖)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ‖dirichletPoly (fun _ => 1) N ((t j - t i : ℝ) * Complex.I)‖ ≤ B) :
    s.card * V ^ 2 ≤ (∑ n ∈ Icc 1 N, ‖a n‖ ^ 2) * (N + (s.card - 1 : ℕ) * B) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
    positivity
  have hp := halasz_montgomery_dirichletPoly_large_values s a N
    (fun i => t i * Complex.I) hV hlarge
  have hphase (i j : ι) : conj ((t i : ℂ) * Complex.I) + (t j : ℂ) * Complex.I =
      ((t j - t i : ℝ) : ℂ) * Complex.I := by simp; ring
  simp_rw [hphase] at hp
  have hrow (i : ι) (hi : i ∈ s) :
      ∑ j ∈ s, ‖dirichletPoly (fun _ => 1) N ((t j - t i : ℝ) * Complex.I)‖ ≤
        N + (s.card - 1 : ℕ) * B := by
    rw [← Finset.sum_erase_add _ _ hi]
    simp only [sub_self, Complex.ofReal_zero, zero_mul, dirichletPoly, neg_zero, Complex.cpow_zero,
      mul_one, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, one_mul,
      Complex.norm_natCast]
    have hsum := Finset.sum_le_sum (s := s.erase i) (fun j hj =>
      hoff i hi j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm)
    simpa [dirichletPoly, Finset.card_erase_of_mem hi, nsmul_eq_mul, add_comm, mul_one] using
      (add_le_add_right hsum (N : ℝ))
  have htotal := hp.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  rw [Finset.sum_const, nsmul_eq_mul] at htotal
  have hpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  apply (le_of_mul_le_mul_left _ hpos)
  convert htotal using 1 <;> ring

end AnalyticNumberTheory.SieveMethods
