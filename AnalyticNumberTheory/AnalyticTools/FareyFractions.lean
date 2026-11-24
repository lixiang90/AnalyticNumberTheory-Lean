import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-!
# Farey neighbours and mediant intervals

The determinant of two consecutive reduced fractions is one. The sum of
their denominators exceeds the order of the Farey sequence. These two facts
control both the gap and the two pieces obtained by cutting at the mediant.
Integer numerators allow the same formulas across the endpoints of a period.
-/

namespace AnalyticNumberTheory.AnalyticTools

/-- Oriented Farey adjacency of `a/q < b/r` at order `N`, recorded entirely
in integer arithmetic. -/
structure FareyAdjacent (N : ℕ) (a : ℤ) (q : ℕ) (b : ℤ) (r : ℕ) : Prop where
  left_pos : 0 < q
  left_le : q ≤ N
  right_pos : 0 < r
  right_le : r ≤ N
  determinant : b * q - a * r = 1
  sum_gt : N < q + r

private theorem exists_denominator_in_last_period {N q : ℕ} (hq : 0 < q) (hN : q ≤ N)
    (z : ℤ) : ∃ r : ℕ, 0 < r ∧ r ≤ N ∧ N < q+r ∧ ∃ t : ℤ, (r : ℤ) = z + q*t := by
  let m := ((N : ℤ) - z) % (q : ℤ)
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hm : 0 ≤ m := Int.emod_nonneg _ hqZ.ne'
  have hm' : m < q := Int.emod_lt_of_pos _ hqZ
  have hr : 0 ≤ (N : ℤ) - m := by omega
  refine ⟨((N : ℤ)-m).toNat, by omega, by omega, by omega, ((N : ℤ)-z) / q, ?_⟩
  rw [Int.toNat_of_nonneg hr]
  have h := Int.emod_add_mul_ediv ((N : ℤ)-z) (q : ℤ)
  change m + _ = _ at h
  linarith

/-- A reduced fraction of denominator at most `N` has a left neighbour;
its numerator may be negative at the beginning of a period. -/
theorem exists_fareyAdjacent_left {N q : ℕ} {a : ℤ} (hq : 0 < q) (hN : q ≤ N)
    (ha : IsCoprime a (q : ℤ)) : ∃ (b : ℤ) (r : ℕ), FareyAdjacent N b r a q := by
  obtain ⟨s, t, hst⟩ := ha
  obtain ⟨r, hr, hrN, hsum, k, hk⟩ := exists_denominator_in_last_period hq hN s
  refine ⟨a*k-t, r, hr, hrN, hq, hN, ?_, by omega⟩
  rw [hk]
  linarith only [hst]

/-- A reduced fraction of denominator at most `N` has a right neighbour. -/
theorem exists_fareyAdjacent_right {N q : ℕ} {a : ℤ} (hq : 0 < q) (hN : q ≤ N)
    (ha : IsCoprime a (q : ℤ)) : ∃ (b : ℤ) (r : ℕ), FareyAdjacent N a q b r := by
  obtain ⟨s, t, hst⟩ := ha
  obtain ⟨r, hr, hrN, hsum, k, hk⟩ := exists_denominator_in_last_period hq hN (-s)
  refine ⟨a*k+t, r, hq, hN, hr, hrN, ?_, hsum⟩
  rw [hk]
  linarith only [hst]

namespace FareyAdjacent

variable {N q r : ℕ} {a b : ℤ} (h : FareyAdjacent N a q b r)
include h

theorem left_coprime : IsCoprime a (q : ℤ) :=
  ⟨-(r : ℤ), b, by linarith only [h.determinant]⟩

theorem right_coprime : IsCoprime b (r : ℤ) :=
  ⟨(q : ℤ), -a, by linarith only [h.determinant]⟩

/-- The exact gap between adjacent fractions. -/
theorem sub_eq : (b : ℝ)/r - (a : ℝ)/q = 1/((q : ℝ)*r) := by
  have hd : (b : ℝ)*q - a*r = 1 := by exact_mod_cast h.determinant
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.left_pos.ne'
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.right_pos.ne'
  field_simp
  linarith only [hd]

theorem lt : (a : ℝ)/q < (b : ℝ)/r := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr h.left_pos
  have hr : (0 : ℝ) < r := Nat.cast_pos.mpr h.right_pos
  exact sub_pos.mp (h.sub_eq ▸ one_div_pos.mpr (mul_pos hq hr))

/-- A fraction lying strictly between determinant-one neighbours has denominator
at least the sum of their denominators, even if it is written in unreduced form. -/
theorem denom_ge_of_between {v : ℕ} (hv : 0 < v) {c : ℤ}
    (hl : (a : ℝ)/q < (c : ℝ)/v) (hr : (c : ℝ)/v < (b : ℝ)/r) : q+r ≤ v := by
  have hqR := Nat.cast_pos (α := ℝ) |>.mpr h.left_pos
  have hrR := Nat.cast_pos (α := ℝ) |>.mpr h.right_pos
  have hvR := Nat.cast_pos (α := ℝ) |>.mpr hv
  have hl' : a*(v : ℤ) < c*q := by exact_mod_cast (div_lt_div_iff₀ hqR hvR).mp hl
  have hr' : c*(r : ℤ) < b*v := by exact_mod_cast (div_lt_div_iff₀ hvR hrR).mp hr
  have h1 : 1 ≤ c*q-a*v := by omega
  have h2 : 1 ≤ b*v-c*r := by omega
  have heq : (v : ℤ) = r*(c*q-a*v)+q*(b*v-c*r) := by
    calc _ = v*(b*q-a*r) := by rw [h.determinant,mul_one]
         _ = _ := by ring
  have hh := add_le_add (mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg r))
    (mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg q))
  omega

theorem no_fraction_between {v : ℕ} (hv : 0 < v) (hvN : v ≤ N) (c : ℤ) :
    ¬ ((a : ℝ)/q < (c : ℝ)/v ∧ (c : ℝ)/v < (b : ℝ)/r) :=
  fun hh => (not_le_of_gt h.sum_gt) ((h.denom_ge_of_between hv hh.1 hh.2).trans hvN)

/-- The mediant between the neighbours is at this distance from the left fraction. -/
theorem mediant_sub_left : ((a : ℝ)+b)/(q+r : ℝ) - a/q = 1/((q : ℝ)*(q+r)) := by
  have hd : (b : ℝ)*q - a*r = 1 := by exact_mod_cast h.determinant
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr h.left_pos
  have hr : (0 : ℝ) < r := Nat.cast_pos.mpr h.right_pos
  field_simp
  linarith only [hd]

/-- The mediant between the neighbours is at this distance from the right fraction. -/
theorem right_sub_mediant : (b : ℝ)/r - ((a : ℝ)+b)/(q+r : ℝ) = 1/((r : ℝ)*(q+r)) := by
  have hd : (b : ℝ)*q - a*r = 1 := by exact_mod_cast h.determinant
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr h.left_pos
  have hr : (0 : ℝ) < r := Nat.cast_pos.mpr h.right_pos
  field_simp
  linarith only [hd]

end FareyAdjacent

end AnalyticNumberTheory.AnalyticTools
