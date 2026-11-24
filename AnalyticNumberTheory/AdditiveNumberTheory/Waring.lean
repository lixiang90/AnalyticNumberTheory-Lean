import AnalyticNumberTheory.AdditiveNumberTheory.CircleMethod
import Mathlib.NumberTheory.SumFourSquares

/-!
# Waring representations

Count ordered representations by nonnegative powers, extract the count as a Fourier
coefficient, and split the integral into major and minor arcs. The cutoff condition is
stated in natural numbers so no rounding of real roots is needed.
-/

noncomputable section

open Finset
open scoped Classical

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Ordered tuples in the box `[0, P]^s` whose `k`-th powers sum to `n`. -/
def waringTuples (k s P n : ℕ) : Finset (Fin s → ℕ) :=
  (Fintype.piFinset (fun _ : Fin s => range (P + 1))).filter
    (fun x => ∑ i, x i ^ k = n)

/-- Once the next power exceeds the target, the box contains every solution. -/
theorem mem_waringTuples_iff {k s P n : ℕ} (hP : n < (P + 1) ^ k) (x : Fin s → ℕ) :
    x ∈ waringTuples k s P n ↔ ∑ i, x i ^ k = n := by
  simp only [waringTuples, mem_filter, Fintype.mem_piFinset, mem_range]
  refine ⟨And.right, fun hx => ⟨fun i => ?_, hx⟩⟩
  by_contra! hi
  have hle : x i ^ k ≤ ∑ j, x j ^ k :=
    single_le_sum (fun j _ => Nat.zero_le (x j ^ k)) (mem_univ i)
  exact hP.not_ge ((Nat.pow_le_pow_left hi k).trans (hx ▸ hle))

/-- Number of ordered representations. For positive degree the cutoff `n` suffices. -/
def waringCount (k s n : ℕ) : ℕ := (waringTuples k s n n).card

/-- One may truncate at any `P` with `n < (P + 1)^k`, in particular at the integer
part of the positive `k`-th root of `n`. -/
theorem waringCount_eq_card {k s P n : ℕ} (hk : 0 < k) (hP : n < (P + 1) ^ k) :
    waringCount k s n = (waringTuples k s P n).card := by
  unfold waringCount
  congr 1
  ext x
  rw [mem_waringTuples_iff hP, mem_waringTuples_iff
    ((Nat.lt_succ_self n).trans_le (Nat.le_self_pow hk.ne' (n + 1)))]

/-- Positivity is equivalent to solvability in nonnegative integers. -/
theorem waringCount_pos_iff {k s n : ℕ} (hk : 0 < k) :
    0 < waringCount k s n ↔ ∃ x : Fin s → ℕ, ∑ i, x i ^ k = n := by
  simp only [waringCount, card_pos, Finset.Nonempty, mem_waringTuples_iff
    ((Nat.lt_succ_self n).trans_le (Nat.le_self_pow hk.ne' (n + 1)))]

/-- Lagrange's four-square theorem gives a positive representation count at every target. -/
theorem waringCount_four_squares_pos (n : ℕ) : 0 < waringCount 2 4 n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact (waringCount_pos_iff (by decide)).2 ⟨![a, b, c, d], by
    simpa [Fin.sum_univ_succ, add_assoc] using h⟩

/-- Weyl sum over the nonnegative bases `0, …, P`. -/
def waringSum (k P : ℕ) : ℝ → ℂ :=
  genExpSum (fun _ => 1) (fun x : ℕ => (x : ℤ) ^ k) (range (P + 1))

/-- Fourier extraction of the representation count on any interval of length one. -/
theorem integral_waringSum_pow {k s P n : ℕ} (hk : 0 < k) (hP : n < (P + 1) ^ k)
    (t : ℝ) :
    (∫ α in t..(t + 1), waringSum k P α ^ s * e (-α * n)) = (waringCount k s n : ℂ) := by
  rw [waringSum, ← Int.cast_natCast (R := ℝ) n, integral_genExpSum_pow_mul_e_neg_shift,
    waringCount_eq_card hk hP]
  have hsum (x : Fin s → ℕ) : (∑ i, (x i : ℤ) ^ k) = n ↔ ∑ i, x i ^ k = n := by
    exact_mod_cast Iff.rfl (a := ∑ i, x i ^ k = n)
  simp [repCountGen, waringTuples, hsum]

/-- The major and minor arcs give an exact decomposition of the Waring count. -/
theorem waringCount_eq_arcIntegrals {k s P n : ℕ} (hk : 0 < k) (hP : n < (P + 1) ^ k)
    {Q T : ℝ} (hQ : 1 ≤ Q) (hQT : 2 * Q ≤ T) :
    (waringCount k s n : ℂ) =
      majorArcIntegral (fun α => waringSum k P α ^ s * e (-α * n)) Q T +
      minorArcIntegral (fun α => waringSum k P α ^ s * e (-α * n)) Q T := by
  rw [← integral_waringSum_pow hk hP 0, zero_add]
  apply representationIntegral_eq_majorArcIntegral_add_minorArcIntegral_of_continuous _ _ hQ hQT
  · intro α
    change waringSum k P (α + 1) ^ s * e (-(α + 1) * n) = _
    rw [show waringSum k P (α + 1) = waringSum k P α from periodic_genExpSum _ _ _ α]
    congr 1
    rw [show -(α + 1) * (n : ℝ) = -α * n + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring,
      e_add_intCast]
  · exact ((continuous_genExpSum _ _ _).pow s).mul
      (continuous_e.comp (continuous_neg.mul continuous_const))

end AnalyticNumberTheory.AdditiveNumberTheory
