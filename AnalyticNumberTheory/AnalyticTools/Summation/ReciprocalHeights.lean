import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # Dyadic summation of reciprocal heights -/

open Finset
open scoped Classical

namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- Summing nonnegative weights divided by one plus their height reduces to
the cumulative weights at the dyadic endpoints, with no restriction at height zero. -/
theorem reciprocal_height_sum_le_dyadic {ι : Type*} (S : Finset ι) (v w : ι → ℝ)
    {T : ℝ} (hv : ∀ i ∈ S, 0 ≤ v i ∧ v i ≤ T) (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i/(1+v i)) ≤ ∑ j ∈ range (Nat.log 2 ⌊T+1⌋₊+1),
      (∑ i ∈ S with v i ≤ (2 : ℝ)^(j+1), w i)/(2 : ℝ)^j := by
  let J := Nat.log 2 ⌊T+1⌋₊
  let I := range (J+1)
  let part (j : ℕ) (i : ι) := if v i≤(2:ℝ)^(j+1) then w i/(2:ℝ)^j else 0
  have hp (j i) (hi : i∈S) : 0≤part j i := by dsimp [part];split_ifs <;> positivity [hw i hi]
  have each (i : ι) (hi : i∈S) : w i/(1+v i)≤∑j∈I,part j i := by
    obtain ⟨h₀,h₁⟩ := hv i hi
    let n := ⌊1+v i⌋₊
    let k := Nat.log 2 n
    have hn : 1≤n := (Nat.le_floor_iff (by linarith)).mpr (by push_cast;linarith)
    have hnj : n≤⌊T+1⌋₊ := Nat.floor_mono (by linarith)
    have hk : k∈I := mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hnj))
    have hl : (2:ℝ)^k≤1+v i := (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n≠0)
        : (2:ℝ)^k≤n).trans (Nat.floor_le (by linarith))
    have hu : v i≤(2:ℝ)^(k+1) := by
      have hf := Nat.lt_floor_add_one (1+v i)
      have hpow : (n:ℝ)<(2:ℝ)^(k+1) := by exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n
      change 1+v i<(n:ℝ)+1 at hf
      linarith
    apply le_trans _ (single_le_sum (f:=fun j => part j i) (fun j _ => hp j i hi) hk)
    rw [show part k i=w i/(2:ℝ)^k by simp [part,hu]]
    exact div_le_div_of_nonneg_left (hw i hi) (by positivity) hl
  have hsum := (sum_le_sum each).trans_eq (sum_comm (s := S) (t := I))
  apply hsum.trans_eq
  apply sum_congr rfl
  intro j _
  rw [sum_div, sum_filter]

/-- Any sublinear power bound on cumulative nonnegative weights gives a uniform
reciprocal-height bound, with the geometric constant explicit in the exponent. -/
theorem reciprocal_height_sum_le_of_sublinear {ι : Type*} (S : Finset ι) (v w : ι → ℝ)
    {A β T : ℝ} (hA : 0 ≤ A) (hβ : β < 1)
    (hv : ∀ i ∈ S, 0 ≤ v i ∧ v i ≤ T) (hw : ∀ i ∈ S, 0 ≤ w i)
    (H : ∀ u : ℝ, 2 ≤ u → (∑ i ∈ S with v i ≤ u, w i) ≤ A*u^β) :
    (∑ i ∈ S, w i/(1+v i)) ≤ A*2^β/(1-2^β/2) := by
  let I := range (Nat.log 2 ⌊T+1⌋₊+1)
  let r := (2 : ℝ)^β/2
  have hr₀ : 0 ≤ r := by dsimp only [r]; positivity
  have hr : r < 1 := (div_lt_one two_pos).mpr (by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hβ)
  have hrow (j : ℕ) (_ : j ∈ I) :
      (∑ i ∈ S with v i ≤ (2 : ℝ)^(j+1), w i)/(2 : ℝ)^j ≤ A*2^β*r^j := by
    have hj : 2 ≤ (2 : ℝ)^(j+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ)) (n := j)]
    apply (div_le_div_of_nonneg_right (H _ hj) (by positivity : 0 ≤ (2 : ℝ)^j)).trans_eq
    have he : ((2 : ℝ)^(j+1))^β = ((2 : ℝ)^β)^(j+1) := by
      rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num), mul_comm]
    rw [he, pow_succ, show r^j = ((2 : ℝ)^β)^j/(2 : ℝ)^j from div_pow ..]
    ring
  have hp := mul_nonneg hA (Real.rpow_pos_of_pos two_pos β).le
  have hgeom : (∑ j ∈ I, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
    have h := geom_sum_mul_neg r (Nat.log 2 ⌊T+1⌋₊+1)
    nlinarith only [h, pow_nonneg hr₀ (Nat.log 2 ⌊T+1⌋₊+1)]
  apply (reciprocal_height_sum_le_dyadic S v w hv hw).trans ((sum_le_sum hrow).trans ?_)
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left hgeom hp).trans_eq (by dsimp only [r]; ring)

end AnalyticNumberTheory.AnalyticTools.Summation
