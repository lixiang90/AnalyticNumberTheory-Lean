import AnalyticNumberTheory.AnalyticTools.HarmonicRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Harmonic sums over integers prime to a modulus

Removing the multiples of each new prime gives the secondary constant
as a finite sum over the prime divisors. The absolute remainder is at
most q/x, for every x>0.
-/
noncomputable section
open Real Finset
namespace AnalyticNumberTheory.AnalyticTools

def reducedReciprocalSum (q : ℕ) (x : ℝ) :=
  ∑n∈Finset.Icc 1 ⌊x⌋₊,if n.Coprime q then (n:ℝ)⁻¹ else 0

def primeDivisorLogSum (q : ℕ) := ∑p∈q.primeFactors,Real.log p/((p:ℝ)-1)

private theorem erase_old {p q : ℕ} (hpq : p∣q) (x : ℝ) :
    reducedReciprocalSum (p*q) x=reducedReciprocalSum q x := by
  unfold reducedReciprocalSum;apply sum_congr rfl;intro n _
  by_cases h : n.Coprime q
  · rw [if_pos h,if_pos (Nat.coprime_mul_iff_right.mpr ⟨Nat.Coprime.of_dvd_right hpq h,h⟩)]
  · rw [if_neg h,if_neg (fun hc => h (Nat.coprime_mul_iff_right.mp hc).2)]

private theorem erase_prime {p q : ℕ} (hp : p.Prime) (hpq : ¬p∣q) (x : ℝ) :
    reducedReciprocalSum (p*q) x=reducedReciprocalSum q x-(p:ℝ)⁻¹*reducedReciprocalSum q (x/p) := by
  let I := Finset.Icc 1 ⌊x⌋₊
  let f := fun n : ℕ => if n.Coprime q then (n:ℝ)⁻¹ else 0
  have hcop := hp.coprime_iff_not_dvd.mpr hpq
  have H : (∑n∈I,if p∣n then f n else 0)=(p:ℝ)⁻¹*reducedReciprocalSum q (x/p) := by
    rw [←sum_filter,reducedReciprocalSum,mul_sum,Nat.floor_div_natCast]
    symm
    refine sum_bij (fun n _ => n*p) ?_ ?_ ?_ ?_
    · intro n hn;obtain ⟨hn,hN⟩ := Finset.mem_Icc.mp hn
      exact mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hn hp.pos,(Nat.le_div_iff_mul_le hp.pos).mp hN⟩,dvd_mul_left ..⟩
    · intro n hn m hm e;exact Nat.eq_of_mul_eq_mul_right hp.pos e
    · intro n hn;obtain ⟨hn,hp'⟩ := mem_filter.mp hn;obtain ⟨v,rfl⟩ := hp'
      refine ⟨v,Finset.mem_Icc.mpr ⟨?_,(Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [mul_comm] using (Finset.mem_Icc.mp hn).2)⟩,mul_comm v p⟩
      by_contra! h;have hv : v=0 := by omega
      simp [hv,I] at hn
    · intro n _
      simp only [f,Nat.coprime_mul_iff_left,hcop,and_true,Nat.cast_mul,mul_inv_rev]
      split_ifs <;>simp_all
  change (∑n∈I,if n.Coprime (p*q) then (n:ℝ)⁻¹ else 0)=(∑n∈I,f n)-_
  rw [←H,←sum_sub_distrib];apply sum_congr rfl;intro n _
  have he : n.Coprime p ↔ ¬p∣n := Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  simp only [Nat.coprime_mul_iff_right,he];dsimp only [f]
  by_cases h : p∣n <;>by_cases h₁ : n.Coprime q <;>simp [h,h₁]

/-- Two-term asymptotic for a reduced harmonic sum with the explicit
error q/x. No lower cutoff beyond positivity is required. -/
theorem reduced_reciprocal_prime_sum_error (q : ℕ) (hq : 0<q) {x : ℝ} (hx : 0<x) :
    |reducedReciprocalSum q x-(q.totient/q:ℝ)*(Real.log x+Real.eulerMascheroniConstant+primeDivisorLogSum q)|≤q/x := by
  induction q using Nat.strong_induction_on generalizing x with
  | ind q ih =>
    by_cases hq₁ : q=1
    · subst q
      have H := harmonic_floor_remainder hx
      have he : reducedReciprocalSum 1 x=∑n∈Finset.Icc 1 ⌊x⌋₊,(n:ℝ)⁻¹ := sum_congr rfl (fun n _ => if_pos (Nat.coprime_one_right n))
      simpa only [he,Nat.totient_one,Nat.cast_one,div_one,
        primeDivisorLogSum,Nat.primeFactors_one,sum_empty,add_zero,one_mul,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
        Rat.cast_natCast,←sub_sub] using H
    let p := q.minFac
    let m := q/p
    have hp : p.Prime := Nat.minFac_prime hq₁
    have hpq : p∣q := Nat.minFac_dvd _
    have he : p*m=q := Nat.mul_div_cancel' hpq
    have hm : 0<m := Nat.pos_of_ne_zero (fun h₀ => hq.ne' (he.symm.trans (by rw [h₀,mul_zero])))
    have hmq : m<q := Nat.div_lt_self hq hp.one_lt
    have h₁ := ih m hmq hm hx
    have h₂ := ih m hmq hm (div_pos hx (Nat.cast_pos.mpr hp.pos))
    have hm₀ := Nat.cast_pos (α:=ℝ).mpr hm
    have hp₀ := Nat.cast_pos (α:=ℝ).mpr hp.pos
    have hp₁ : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
    let k := (m.totient/m:ℝ)
    let u := Real.log x+Real.eulerMascheroniConstant+primeDivisorLogSum m
    change |reducedReciprocalSum m x-k*u|≤m/x at h₁
    have H : (p*m).primeFactors=insert p m.primeFactors := by rw [Nat.primeFactors_mul hp.ne_zero hm.ne',hp.primeFactors];simp
    rw [←he,Nat.cast_mul]
    by_cases hpm : p∣m
    · have hmem := Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne'⟩
      rw [erase_old hpm,Nat.totient_mul_of_dvd hpm,Nat.cast_mul,primeDivisorLogSum,H,insert_eq_of_mem hmem]
      rw [mul_div_mul_left _ _ hp₀.ne']
      exact h₁.trans (div_le_div_of_nonneg_right (le_mul_of_one_le_left hm₀.le hp₁.le) hx.le)
    · have hn : p∉m.primeFactors := fun h => hpm (Nat.mem_primeFactors.mp h).2.1
      rw [erase_prime hp hpm,Nat.totient_mul_of_prime_of_not_dvd hp hpm,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,
        primeDivisorLogSum,H,sum_insert hn]
      rw [Real.log_div hx.ne' hp₀.ne'] at h₂
      change |reducedReciprocalSum m (x/p)-k*(Real.log x-Real.log p+Real.eulerMascheroniConstant+primeDivisorLogSum m)|≤_ at h₂
      let e := reducedReciprocalSum m x-k*u
      let f := reducedReciprocalSum m (x/p)-k*(Real.log x-Real.log p+Real.eulerMascheroniConstant+primeDivisorLogSum m)
      have hh : reducedReciprocalSum m x-(p:ℝ)⁻¹*reducedReciprocalSum m (x/p)-
          (((p:ℝ)-1)*m.totient/(p*m))*(Real.log x+Real.eulerMascheroniConstant+
            (Real.log p/((p:ℝ)-1)+∑v∈m.primeFactors,Real.log v/((v:ℝ)-1)))=e-(p:ℝ)⁻¹*f := by
        dsimp only [e,f,u,k,primeDivisorLogSum];field_simp [hp₀.ne',hm₀.ne',(sub_pos.mpr hp₁).ne'];ring
      rw [hh]
      apply (abs_sub e ((p:ℝ)⁻¹*f)).trans
      rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hp₀.le)]
      apply (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (inv_nonneg.mpr hp₀.le))).trans
      have hx' : (p:ℝ)⁻¹*((m:ℝ)/(x/p))=m/x := by field_simp
      rw [hx']
      rw [←add_div];apply div_le_div_of_nonneg_right _ hx.le
      nlinarith [mul_le_mul_of_nonneg_right (show (2:ℝ)≤p by exact_mod_cast hp.two_le) hm₀.le]

end AnalyticNumberTheory.AnalyticTools
