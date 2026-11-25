import AnalyticNumberTheory.SieveMethods.SelbergSmallPrimeComparison
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Selberg denominator at small cutoffs

For the finite range below 1024 we round every reciprocal totient down to
five decimal places. A power-of-two comparison bounds the logarithm at the
right endpoint of each unit interval. The kernel checks all integer comparisons.
-/

open Real Finset
namespace AnalyticNumberTheory.SieveMethods

private def selbergCertificate : ℕ → ℕ × Bool
  | 0 => (0,true)
  | n+1 =>
    let prev := selbergCertificate n
    let count := prev.1 + (if Squarefree (n+1) then 100000 / (n+1).totient else 0)
    let ok := n+1<6 || (107600*32 + 69400*((n+2)^32).log2.succ ≤ count*32)
    (count,prev.2 && ok)

private theorem certificate_prefix (n : ℕ) :
    ((selbergCertificate n).1:ℝ) ≤ 100000*selbergDenominator n := by
  induction n with
  | zero => simp [selbergCertificate,selbergDenominator]
  | succ n ih =>
    have ht : 0<((n+1).totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr n.succ_pos
    have hdiv := Nat.div_mul_le_self 100000 (n+1).totient
    have hbound : ((100000/(n+1).totient:ℕ):ℝ)≤100000*((n+1).totient:ℝ)⁻¹ := by
      rw [←div_eq_mul_inv,le_div_iff₀ ht];exact_mod_cast hdiv
    simp only [selbergDenominator,Nat.floor_natCast,sum_filter] at ih ⊢
    rw [sum_Icc_succ_top (by omega),mul_add]
    simp only [selbergCertificate,Nat.cast_add,Nat.cast_ite,Nat.cast_zero]
    split_ifs with h
    · exact add_le_add ih hbound
    · simpa using ih

private theorem certificate_entry {n N : ℕ} (h₆ : 6≤n) (hn : n≤N)
    (h : (selbergCertificate N).2=true) :
    107600*32+69400*((n+1)^32).log2.succ ≤ (selbergCertificate n).1*32 := by
  induction N with
  | zero => omega
  | succ k ih =>
    have H := Bool.and_eq_true_iff.mp h
    by_cases hnk : n=k+1
    · subst n
      simpa [selbergCertificate,show ¬k+1<6 by omega] using H.2
    · exact ih (by omega) H.1

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem certificate_checked : (selbergCertificate 1023).2=true := by decide +kernel

/-- On each unit interval between six and 1024 the Selberg denominator
exceeds the logarithm by at least 1.076. -/
theorem selbergDenominator_ge_log_finite {x : ℝ} (hl : 6≤x) (hu : x<1024) :
    log x+1.076 ≤ selbergDenominator x := by
  let n := ⌊x⌋₊
  have hn : 6≤n := (Nat.le_floor_iff (by linarith : 0≤x)).mpr (by norm_num;exact hl)
  have hN : n≤1023 := by
    have h := (Nat.floor_lt (by linarith : 0≤x)).mpr (show x<(1024:ℕ) by exact_mod_cast hu)
    dsimp [n];omega
  let k := ((n+1)^32).log2.succ
  have he : 107600*32+69400*k ≤ (selbergCertificate n).1*32 := certificate_entry hn hN certificate_checked
  have he' : (107600:ℝ)*32+69400*k ≤ ((selbergCertificate n).1:ℝ)*32 := by exact_mod_cast he
  have H := certificate_prefix n
  have Hx : selbergDenominator (n:ℝ) = selbergDenominator x := by simp [n,selbergDenominator]
  rw [Hx] at H
  have hpow : (n+1)^32<2^k := (Nat.log2_lt (by positivity)).mp (Nat.lt_succ_self _)
  clear_value k
  have hR : ((n:ℝ)+1)^32<2^k := by
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using (Nat.cast_lt (α:=ℝ)).mpr hpow
  have hlog := Real.log_le_log (by positivity : 0<((n:ℝ)+1)^32) hR.le
  rw [Real.log_pow,Real.log_pow] at hlog
  have hxlog := Real.log_le_log (by linarith : 0<x) (Nat.lt_floor_add_one x).le
  change log x ≤ log ((n:ℝ)+1) at hxlog
  have hk := mul_le_mul_of_nonneg_left (show log 2≤0.694 by linarith [log_two_lt_d9])
    (Nat.cast_nonneg (α:=ℝ) k)
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [he',H,hlog,hxlog,hk]

end AnalyticNumberTheory.SieveMethods
