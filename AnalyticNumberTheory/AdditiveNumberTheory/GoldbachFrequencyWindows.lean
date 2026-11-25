import AnalyticNumberTheory.SieveMethods.BrunTitchmarshFull
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalPrimeCounts

/-! # Von Mangoldt mass in short frequency windows

The Brun–Titchmarsh bound at modulus one controls the primes in the window.
The global prime-power correction suffices as soon as the width is at least
the square root of the upper cutoff.
-/

noncomputable section

open Finset Real AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.SieveMethods
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A uniform explicit upper bound for the `ψ` increment in an interval
of length `2 H` with left endpoint at most `H²`. -/
theorem psi_interval_le_fifty {x H : ℝ} (hx : 0≤x) (hH : 1≤H) (hxH : x≤H^2) :
    Chebyshev.psi (x+2*H)-Chebyshev.psi x ≤ 50*H := by
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ))
  by_cases hzero : x=0
  · subst x
    simp only [zero_add,Chebyshev.psi_eq_zero_of_le_one (by norm_num : (0:ℝ)≤1),sub_zero]
    have h := psi_le_const_mul_self (show 0≤2*H by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hl4 (show 0≤2*H by linarith)]
  have hpos : 0<x := lt_of_le_of_ne hx (Ne.symm hzero)
  have hb : x+2*H≤(2*H)^2 := by nlinarith [sq_nonneg (H-1)]
  have hsqrt : sqrt (x+2*H) ≤ 2*H := (sqrt_le_iff).2 ⟨by linarith,hb⟩
  have hlog : log (x+2*H)≤2*log (2*H) := by
    have hl := Real.log_le_log (by linarith : 0<x+2*H) hb
    rwa [Real.log_pow,Nat.cast_ofNat] at hl
  have hlog0 : 0<log (2*H) := Real.log_pos (by linarith)
  have hp := brun_titchmarsh_primeCounting hx (show 1<2*H by linarith)
  change primePi (x+2*H)-primePi x≤2*(2*H)/log (2*H) at hp
  have hθ := (theta_interval_primePi_comparison hpos (by linarith : x≤x+2*H)).2
  have hθ' : Chebyshev.theta (x+2*H)-Chebyshev.theta x ≤ 8*H := by
    apply hθ.trans
    calc _ ≤ (2*(2*H)/log (2*H))*(2*log (2*H)) :=
            mul_le_mul hp hlog (Real.log_nonneg (by linarith)) (by positivity)
         _ = _ := by field_simp; ring
  have hpow := (le_abs_self _).trans (abs_psi_sub_theta_le_mul_sqrt (x+2*H))
  have hs := mul_le_mul (by linarith : (log 4+4)*3≤21) hsqrt (sqrt_nonneg _) (by norm_num)
  linarith [Chebyshev.theta_le_psi x]

/-- The `Λ`-mass of any set of integers of diameter at most `H` below `H²`. -/
theorem sum_vonMangoldt_window_le {N : ℕ} {H : ℝ} (hH : 1≤H) (hN : (N:ℝ)≤H^2)
    (S : Finset ℕ) (hS : S⊆Icc 1 N)
    (hdiam : ∀ m∈S, ∀ n∈S, (n:ℝ)-m≤H) : ∑ n∈S,Λ n≤50*H := by
  classical
  rcases S.eq_empty_or_nonempty with hs|hs
  · simp [hs]; linarith
  let m := S.min' hs
  have hm : m∈S := S.min'_mem hs
  have hm1 := (mem_Icc.mp (hS hm)).1
  let k := m-1
  have hmk : m=k+1 := by dsimp [k]; omega
  have hmN : (k:ℝ)≤N := by exact_mod_cast (show k≤N by have := (mem_Icc.mp (hS hm)).2; omega)
  let U := ⌊(k:ℝ)+2*H⌋₊
  have hkU : k≤U := Nat.le_floor (by linarith)
  have hsub : Icc 1 k⊆Icc 1 U := Icc_subset_Icc_right hkU
  have hin : S⊆Icc 1 U\Icc 1 k := by
    intro n hn
    have hn1 := (mem_Icc.mp (hS hn)).1
    have hmn : m≤n := S.min'_le n hn
    have h := hdiam m hm n hn
    have hcast : (m:ℝ)=k+1 := by exact_mod_cast hmk
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hn1,Nat.le_floor (by linarith)⟩,
      fun hh => (by have := (mem_Icc.mp hh).2; omega)⟩
  have hsum := sum_le_sum_of_subset_of_nonneg (f:=fun n=>Λ n) hin
    (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  rw [sum_sdiff_eq_sub hsub] at hsum
  have hpsi := psi_interval_le_fifty (Nat.cast_nonneg k) hH (hmN.trans hN)
  rw [psi_eq_sum_Icc,psi_eq_sum_Icc,Nat.floor_natCast] at hpsi
  exact hsum.trans hpsi

end AnalyticNumberTheory.AdditiveNumberTheory
