import AnalyticNumberTheory.PrimeDistribution.InghamTypeI
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Removing the reciprocal height weight in a family of zeros

A linear term in the cumulative height bound costs one logarithm. A term
with square-root growth instead gives a convergent geometric series.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- Reciprocal-height summation for any finite sample, including height zero.
Only cutoffs between 2 and twice T+1 are needed in the cumulative estimate. -/
theorem reciprocal_height_sum_le {ι : Type*} (S : Finset ι) (v w : ι→ℝ)
    {A B T : ℝ} (hA : 0≤A) (hB : 0≤B) (hT : 1≤T)
    (hv : ∀i∈S,0≤v i ∧ v i≤T) (hw : ∀i∈S,0≤w i)
    (H : ∀ u : ℝ,2≤u → u≤2*(T+1) → (∑i∈S with v i≤u,w i)≤A*u+B*Real.sqrt u) :
    (∑i∈S,w i/(1+v i)) ≤ 6*(A*(1+Real.log (T+1))+B) := by
  let J := Nat.log 2 ⌊T+1⌋₊
  let I := range (J+1)
  have hfloor : 1≤⌊T+1⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by push_cast;linarith)
  have hJT : (2:ℝ)^J≤T+1 := (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : ⌊T+1⌋₊≠0)
      : (2:ℝ)^J≤⌊T+1⌋₊).trans (Nat.floor_le (by linarith))
  have hJ : (J:ℝ)+1≤2*(1+Real.log (T+1)) := by
    have h := Real.log_le_log (by positivity) hJT
    rw [Real.log_pow] at h
    nlinarith only [h,mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2) (Nat.cast_nonneg (α:=ℝ) J)]
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
  have per (j : ℕ) (hj : j∈I) : (∑i∈S,part j i)≤2*A+(3/2:ℝ)*B*(3/4:ℝ)^j := by
    have hj' : j≤J := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hle : 2≤(2:ℝ)^(j+1) := by rw [pow_succ];linarith [one_le_pow₀ (by norm_num : 1≤(2:ℝ)) (n:=j)]
    have hcut : (2:ℝ)^(j+1)≤2*(T+1) := by
      rw [pow_succ];linarith [(pow_le_pow_right₀ (by norm_num : 1≤(2:ℝ)) hj').trans hJT]
    have hs : Real.sqrt ((2:ℝ)^(j+1))≤(3/2:ℝ)^(j+1) := by
      apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
      calc (2:ℝ)^(j+1) ≤ ((3/2:ℝ)^2)^(j+1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
           _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    have hd : ((∑i∈S with v i≤(2:ℝ)^(j+1),w i)/(2:ℝ)^j)≤
        (A*(2:ℝ)^(j+1)+B*((3/2:ℝ)^(j+1)))/(2:ℝ)^j := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (H _ hle hcut).trans (add_le_add_right (mul_le_mul_of_nonneg_left hs hB) _)
    have hrow : (∑i∈S,part j i)=(∑i∈S with v i≤(2:ℝ)^(j+1),w i)/(2:ℝ)^j := by
      rw [sum_div, sum_filter]
    rw [hrow]
    apply hd.trans_eq
    rw [pow_succ,pow_succ,show (3/4:ℝ)^j=(3/2:ℝ)^j/(2:ℝ)^j by rw [←div_pow];norm_num]
    field_simp <;> ring
  have hsum := (sum_le_sum each).trans_eq (sum_comm (s:=S) (t:=I))
  apply hsum.trans ((sum_le_sum per).trans ?_)
  simp only [sum_add_distrib,sum_const,I,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,←mul_sum]
  have hgeom : (∑j∈range (J+1),(3/4:ℝ)^j)≤4 := by
    nlinarith only [geom_sum_mul_neg (3/4:ℝ) (J+1),pow_nonneg (by norm_num : 0≤(3/4:ℝ)) (J+1)]
  nlinarith only [mul_le_mul_of_nonneg_right hJ hA,mul_le_mul_of_nonneg_left hgeom hB,
    mul_nonneg hA (show 0≤1+Real.log (T+1) by linarith [Real.log_nonneg (by linarith : 1≤T+1)])]

end AnalyticNumberTheory.PrimeDistribution
