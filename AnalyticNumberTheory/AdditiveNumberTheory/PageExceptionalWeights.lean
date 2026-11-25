import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSieveDivisors
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import Mathlib.NumberTheory.ZetaValues

/-! # The sum of exceptional Gauss weights over multiples of a conductor

The arithmetic weight from cubing the Gauss coefficient at modulus `q`
and summing over the reduced numerators is `d^(3/2)/φ(q)²`.
-/

noncomputable section
open Finset Real AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- An elementary explicit bound for the inverse totient ratio. -/
theorem div_totient_le_six_mul_log {n : ℕ} (hn : 0<n) :
    (n:ℝ)/n.totient≤6*(1+log n) := by
  have hφ : (0:ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  let f := fun p : ℕ => (p:ℝ)/((p:ℝ)-1)
  have hratio : (n:ℝ)/n.totient=∏p∈n.primeFactors,f p := by
    let g := fun p : ℕ => ((p-1:ℕ):ℝ)
    have hg : 0 < ∏p∈n.primeFactors,g p := prod_pos (fun p hp =>
      Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt))
    have hmul := congrArg (Nat.cast (R:=ℝ)) (Nat.totient_mul_prod_primeFactors n)
    push_cast at hmul
    have he : (n:ℝ)/n.totient=(∏p∈n.primeFactors,(p:ℝ))/(∏p∈n.primeFactors,g p) := by
      apply (div_eq_div_iff hφ.ne' hg.ne').2
      simpa only [g,mul_comm] using hmul.symm
    rw [he,←prod_div_distrib]
    apply prod_congr rfl; intro p hp
    simp [f,g,Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]
  have hodd : n.primeFactors.erase 2 = n.primeFactors.filter (fun p => 2<p) := by
    ext p
    simp only [mem_erase,mem_filter]
    constructor
    · intro ⟨h,hp⟩; have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact ⟨hp,by omega⟩
    · intro ⟨hp,h⟩; exact ⟨by omega,hp⟩
  have hprod : ∏p∈n.primeFactors.erase 2,f p ≤ goldbachSieveFactor n := by
    rw [hodd]
    unfold goldbachSieveFactor
    refine prod_le_prod₀ ?_ ?_
    · intro p hp
      have hh : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    intro p hp
    have hh : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
    change (p:ℝ)/((p:ℝ)-1) ≤ 1+1/((p:ℝ)-2)
    rw [one_add_div (by linarith : (p:ℝ)-2≠0)]
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith
  have hF : (n:ℝ)/n.totient≤2*goldbachSieveFactor n := by
    rw [hratio]
    by_cases h2 : 2∈n.primeFactors
    · rw [←mul_prod_erase _ f h2,show f 2=2 by norm_num [f]]
      exact mul_le_mul_of_nonneg_left hprod (by norm_num)
    · rw [erase_eq_of_notMem h2] at hprod
      linarith [one_le_goldbachSieveFactor n]
  have hσ : ∑d∈n.divisors,(d:ℝ)⁻¹≤1+log n := by
    apply (sum_le_sum_of_subset_of_nonneg (f:=fun d : ℕ => (d:ℝ)⁻¹) (t:=Icc 1 n) _ (fun _ _ _ => by positivity)).trans
    · simpa only [Nat.floor_natCast] using sum_inv_le_one_add_log (x:=(n:ℝ)) (by exact_mod_cast hn)
    · intro d hd
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
  linarith [goldbachSieveFactor_le_divisor_sum hn]

/-- Cubed Gauss weights over every multiple of the exceptional conductor,
with all reduced numerators already counted. -/
theorem exceptional_gauss_weight_sum {d M : ℕ} (hd : 0<d) (hM : 1≤M) :
    ∑q∈(Icc 1 M).filter (d∣·), (sqrt d)^3/(q.totient:ℝ)^2 ≤
      6*Real.pi^2*(1+log M)^2/sqrt d := by
  let S := (Icc 1 M).filter (d∣·)
  let L := 1+log M
  have hL : 0≤L := by dsimp [L]; linarith [log_nonneg (show 1≤(M:ℝ) by exact_mod_cast hM)]
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hsd : 0<sqrt (d:ℝ) := sqrt_pos.mpr hdR
  have hs2 := sq_sqrt hdR.le
  have hw (q : ℕ) (hq : q∈S) : (sqrt d)^3/(q.totient:ℝ)^2 ≤
      (36*L^2/sqrt d)*(1/(q/d:ℕ)^2 : ℝ) := by
    have ⟨hqI,hdiv⟩ := mem_filter.mp hq
    have hq1 := (mem_Icc.mp hqI).1
    have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hqr : (0:ℝ)<q := by exact_mod_cast hq1
    have hk : (0:ℝ)<(q/d:ℕ) := Nat.cast_pos.mpr (Nat.div_pos (Nat.le_of_dvd hq1 hdiv) hd)
    have he : (d:ℝ)*(q/d:ℕ)=q := by exact_mod_cast Nat.mul_div_cancel' hdiv
    have hf : (q:ℝ)/q.totient≤6*L := (div_totient_le_six_mul_log hq1).trans
      (by dsimp [L]; gcongr; exact_mod_cast (mem_Icc.mp hqI).2)
    have hs := pow_le_pow_left₀ (div_nonneg hqr.le hφ.le) hf 2
    calc (sqrt d)^3/(q.totient:ℝ)^2 = ((q:ℝ)/q.totient)^2/
          (sqrt d*(q/d:ℕ)^2) := by
          field_simp [hφ.ne',hsd.ne',hk.ne']
          rw [←he]
          nlinarith only [sq_nonneg (sqrt d),hs2,show (sqrt d)^4=(d:ℝ)^2 by rw [show (4:ℕ)=2*2 by decide,pow_mul,hs2]]
         _ ≤ (6*L)^2/(sqrt d*(q/d:ℕ)^2) := div_le_div_of_nonneg_right hs (by positivity)
         _ = _ := by ring
  have hinj : Set.InjOn (fun q : ℕ => q/d) S := by
    intro q hq r hr he
    simpa only [Nat.mul_div_cancel' (mem_filter.mp hq).2,Nat.mul_div_cancel' (mem_filter.mp hr).2]
      using congrArg (fun k : ℕ => d*k) he
  have hζ : (∑q∈S,(1/(q/d:ℕ)^2 : ℝ))≤Real.pi^2/6 := by
    have he : (∑k∈S.image (fun q => q/d),1/(k:ℝ)^2) = ∑q∈S,(1/(q/d:ℕ)^2 : ℝ) :=
      sum_image hinj
    rw [←he]
    exact (hasSum_zeta_two.summable.sum_le_tsum _ (fun _ _ => by positivity)).trans_eq hasSum_zeta_two.tsum_eq
  apply (sum_le_sum (s:=S) hw).trans
  rw [←mul_sum]
  apply (mul_le_mul_of_nonneg_left hζ (by positivity : 0≤36*L^2/sqrt d)).trans_eq
  dsimp [L]; ring

end AnalyticNumberTheory.AdditiveNumberTheory
