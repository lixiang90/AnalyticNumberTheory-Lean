import AnalyticNumberTheory.PrimeDistribution.ZeroHeightSummation
import Mathlib.Algebra.BigOperators.Intervals

/-! # Summing dyadic conductor estimates -/
noncomputable section
open Finset Real
namespace AnalyticNumberTheory.PrimeDistribution

/-- Summing a block estimate of the form A Q + B Q^(-1/3) costs no
logarithm. The former term is governed by the largest conductor and the
latter by the smallest. The last block may be truncated. -/
theorem conductor_dyadic_summation (f : ℕ→ℝ) {d D : ℕ} (hd : 1≤d) (hdD : d≤D)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (H : ∀{Q R : ℕ},d≤Q → Q≤D → R≤2*Q →
      (∑q∈Ioc Q R,f q)≤ A*Q+B*(Q:ℝ)^(-(1/3:ℝ))) :
    (∑q∈Ioc d D,f q) ≤ 2*A*D + (1-(2:ℝ)^(-(1/3:ℝ)))⁻¹*B*(d:ℝ)^(-(1/3:ℝ)) := by
  let n := D/d
  let k := Nat.log 2 n
  let b (j : ℕ) := 2^j*d
  let r := (2:ℝ)^(-(1/3:ℝ))
  have hn : 1≤n := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdD)
  have hk : b k≤D := (Nat.mul_le_mul_right d (Nat.pow_log_le_self 2 (by omega : n≠0))).trans (Nat.div_mul_le_self D d)
  have hk' : D<b (k+1) := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_pow_succ_log_self one_lt_two n)
  have hb (j : ℕ) : d≤b j := Nat.le_mul_of_pos_left d (Nat.one_le_pow _ _ (by decide))
  have hmono : Monotone b := fun j k h => Nat.mul_le_mul_right d (Nat.pow_le_pow_right (by decide) h)
  have he' (j : ℕ) (hj : j≤k+1) :
      (∑q∈Ioc d (min D (b j)),f q)=∑i∈range j,∑q∈Ioc (b i) (min D (b (i+1))),f q := by
    induction j with
    | zero => simp [b,min_eq_right hdD]
    | succ j ih =>
      rw [sum_range_succ,←ih (by omega),min_eq_right ((hmono (by omega : j≤k)).trans hk)]
      exact (sum_Ioc_consecutive f (hb j) (le_min ((hmono (by omega : j≤k)).trans hk) (hmono (by omega)))).symm
  have he := he' (k+1) le_rfl
  rw [min_eq_left hk'.le] at he
  rw [he]
  have hblock (j : ℕ) (hj : j∈range (k+1)) :=
    H (Q:=b j) (R:=min D (b (j+1))) (hb j) ((hmono (Nat.lt_succ_iff.mp (mem_range.mp hj))).trans hk)
      ((min_le_right _ _).trans_eq (by dsimp only [b];ring))
  apply (sum_le_sum hblock).trans
  have hcoef (j : ℕ) : ((b j:ℕ):ℝ)^(-(1/3:ℝ))=r^j*(d:ℝ)^(-(1/3:ℝ)) := by
    dsimp only [b,r];push_cast
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg d),
      ←Real.rpow_natCast (2:ℝ),←Real.rpow_mul (by norm_num),←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    congr 2;ring
  have hbg (j : ℕ) : ((b j:ℕ):ℝ)=(2:ℝ)^j*d := by simp [b]
  simp_rw [hcoef,hbg,mul_left_comm A ((2:ℝ)^_) (d:ℝ),←mul_assoc B]
  rw [sum_add_distrib]
  have hsum₁ : (∑j∈range (k+1),(2:ℝ)^j*(A*d))≤2*A*D := by
    rw [←sum_mul]
    have hg := geom_sum_mul (2:ℝ) (k+1)
    norm_num only [Nat.cast_ofNat,sub_self,sub_zero,show (2:ℝ)-1=1 by norm_num,mul_one] at hg
    rw [hg,pow_succ]
    have hkv : (2:ℝ)^k*d≤D := by exact_mod_cast hk
    nlinarith only [mul_le_mul_of_nonneg_left hkv hA,mul_nonneg hA (Nat.cast_nonneg (α:=ℝ) d)]
  have hr : r<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr₀ : 0≤r := Real.rpow_nonneg (by norm_num) _
  have hgeom : (∑j∈range (k+1),r^j)≤(1-r)⁻¹ := by
    rw [←one_div];apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
    linarith only [geom_sum_mul_neg r (k+1),pow_nonneg hr₀ (k+1)]
  apply add_le_add hsum₁
  rw [←sum_mul,←mul_sum]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom hB) (by positivity)).trans_eq (by dsimp only [r];ring)

end AnalyticNumberTheory.PrimeDistribution
