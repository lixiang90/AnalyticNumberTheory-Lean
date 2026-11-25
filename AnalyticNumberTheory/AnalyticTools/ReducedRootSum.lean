import AnalyticNumberTheory.AnalyticTools.ReducedResidueHarmonics
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks

/-!
# Reciprocal square roots in reduced residue classes

Removing multiples of one prime at a time isolates the density term with an
error given by a finite Euler product. At a full period the result is uniform
in the modulus.
-/

open Real Finset
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.AnalyticTools

private noncomputable def rootWeight (n : ℕ) : ℝ := (sqrt n)⁻¹
private noncomputable def rootProduct (q : ℕ) : ℝ := ∏ p∈q.primeFactors,(1+(sqrt p)⁻¹)

private theorem sqrt_sum_lower (K : ℕ) :
    2*(sqrt ((K:ℝ)+1)-1) ≤ ∑ n∈Icc 1 K,rootWeight n := by
  rw [show Icc 1 K=Ioc 0 K by rw [←Icc_add_one_left_eq_Ioc,zero_add]]
  induction K with
  | zero => simp
  | succ k ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _)]
    let x := sqrt ((k:ℝ)+1)
    let y := sqrt ((k:ℝ)+1+1)
    have hx : 0<x := sqrt_pos.mpr (by positivity)
    have hx2 : x^2=(k:ℝ)+1 := sq_sqrt (by positivity)
    have hy2 : y^2=(k:ℝ)+1+1 := sq_sqrt (by positivity)
    have hstep : 2*(y-x)≤x⁻¹ := by
      rw [←one_div,le_div_iff₀ hx]
      nlinarith only [hx2,hy2,sq_nonneg (y-x)]
    change 2*(sqrt ((k:ℝ)+1)-1)≤_ at ih
    simp only [Nat.cast_succ,rootWeight] at *
    linarith only [ih,hstep]

private theorem initial_error {x : ℝ} (hx : 0<x) :
    |reducedWeightSum rootWeight 1 x - 2*sqrt x|≤2 := by
  have he : reducedWeightSum rootWeight 1 x=∑ n∈Icc 1 ⌊x⌋₊,rootWeight n :=
    sum_congr rfl (fun n _ => if_pos (Nat.coprime_one_right n))
  have hlo := sqrt_sum_lower ⌊x⌋₊
  have hhi := sum_Icc_inv_sqrt_le ⌊x⌋₊
  have hx₁ := sqrt_le_sqrt (Nat.floor_le hx.le)
  have hx₂ := sqrt_le_sqrt (Nat.lt_floor_add_one x).le
  rw [he,abs_le]
  dsimp only [rootWeight] at *
  constructor <;> linarith only [hlo,hhi,hx₁,hx₂]

private theorem root_reduced_error (q : ℕ) (hq : 0<q) {x : ℝ} (hx : 0<x) :
    |reducedWeightSum rootWeight q x-2*((q.totient:ℝ)/q)*sqrt x|≤2*rootProduct q := by
  induction q using Nat.strong_induction_on generalizing x with
  | ind q ih =>
    by_cases h1 : q=1
    · subst q
      simpa [rootProduct] using initial_error hx
    let p := q.minFac
    let m := q/p
    have hp : p.Prime := Nat.minFac_prime h1
    have he : p*m=q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
    have hm : 0<m := Nat.pos_of_ne_zero (fun h => hq.ne' (he.symm.trans (by rw [h,mul_zero])))
    have hmq : m<q := Nat.div_lt_self hq hp.one_lt
    have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
    have hm₀ : 0<(m:ℝ) := Nat.cast_pos.mpr hm
    have h₁ := ih m hmq hm hx
    have h₂ := ih m hmq hm (div_pos hx hp₀)
    have H : (p*m).primeFactors=insert p m.primeFactors := by
      rw [Nat.primeFactors_mul hp.ne_zero hm.ne',hp.primeFactors];simp
    rw [←he,Nat.cast_mul]
    by_cases hpm : p∣m
    · have hmem := Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne'⟩
      rw [reducedWeightSum_erase_old _ hpm,Nat.totient_mul_of_dvd hpm,Nat.cast_mul,
        mul_div_mul_left _ _ hp₀.ne',rootProduct,H,insert_eq_of_mem hmem]
      exact h₁
    · have hh : p∉m.primeFactors := fun h => hpm (Nat.dvd_of_mem_primeFactors h)
      have hw (n : ℕ) : rootWeight (n*p)=rootWeight p*rootWeight n := by
        simp [rootWeight,Nat.cast_mul,sqrt_mul (Nat.cast_nonneg n),mul_comm]
      rw [reducedWeightSum_erase_prime _ hp hpm hw,Nat.totient_mul_of_prime_of_not_dvd hp hpm,Nat.cast_mul,
        Nat.cast_sub hp.one_lt.le,Nat.cast_one,rootProduct,H,prod_insert hh]
      let e := reducedWeightSum rootWeight m x-2*((m.totient:ℝ)/m)*sqrt x
      let f := reducedWeightSum rootWeight m (x/p)-2*((m.totient:ℝ)/m)*sqrt (x/p)
      have hsplit : reducedWeightSum rootWeight m x-rootWeight p*reducedWeightSum rootWeight m (x/p)-
          2*(((p:ℝ)-1)*m.totient/(p*m))*sqrt x=e-rootWeight p*f := by
        dsimp only [e,f,rootWeight];rw [sqrt_div hx.le]
        field_simp [hp₀.ne',hm₀.ne',(sqrt_pos.mpr hp₀).ne']
        ring_nf
        simp only [sq_sqrt hp₀.le] <;> ring
      rw [hsplit]
      have hn : 0≤rootWeight p := by dsimp [rootWeight];positivity
      have ht := abs_sub e (rootWeight p*f)
      rw [abs_mul,abs_of_nonneg hn] at ht
      have H' := mul_le_mul_of_nonneg_left h₂ hn
      change |e|≤2*rootProduct m at h₁
      change rootWeight p*|f|≤rootWeight p*(2*rootProduct m) at H'
      change _≤2*((1+rootWeight p)*rootProduct m)
      linarith only [ht,h₁,H']

private theorem root_product_le_totient {q : ℕ} (hq : 0<q) :
    rootProduct q*sqrt q≤9*q.totient := by
  classical
  let B (p : ℕ) : ℝ := if p<4 then 3 else 1
  let F (p : ℕ) : ℝ := 1-(p:ℝ)⁻¹
  have hF {p : ℕ} (hp : p∈q.primeFactors) : 0≤F p := by
    have h : 1≤(p:ℝ) := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h)
  have hlocal (p : ℕ) (hp : p∈q.primeFactors) : 1+(sqrt p)⁻¹≤(B p*F p)*sqrt p := by
    have hp₂ : 2≤(p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp₀ : 0<(p:ℝ) := by linarith
    have hs := sqrt_pos.mpr hp₀
    have hh := sq_sqrt hp₀.le
    apply (mul_le_mul_iff_left₀ hs).mp
    have he : (1+(sqrt p)⁻¹)*sqrt p=sqrt p+1 := by field_simp
    have he' : (B p*F p*sqrt p)*sqrt p=B p*((p:ℝ)-1) := by
      dsimp only [F]
      rw [mul_assoc _ (sqrt p) (sqrt p),Real.mul_self_sqrt hp₀.le]
      field_simp
    rw [he,he']
    dsimp only [B]
    split_ifs with h
    · nlinarith only [hp₂,show sqrt p≤(p:ℝ) from (sqrt_le_iff).mpr ⟨hp₀.le,by nlinarith only [mul_nonneg hp₀.le (show 0≤(p:ℝ)-1 by linarith)]⟩]
    · have hh' : 4≤(p:ℝ) := by exact_mod_cast le_of_not_gt h
      have hroot : sqrt p≤(p:ℝ)-2 := (sqrt_le_iff).mpr ⟨by linarith,by
        nlinarith only [mul_nonneg (show 0≤(p:ℝ)-4 by linarith) (show 0≤(p:ℝ)-1 by linarith)]⟩
      linarith
  have H := Finset.prod_le_prod₀ (fun (p:ℕ) (_ : p∈q.primeFactors) => show 0≤1+(sqrt p)⁻¹ by positivity) hlocal
  rw [prod_mul_distrib,prod_mul_distrib,←sqrt_prod _ (fun p _ => Nat.cast_nonneg p)] at H
  have hroot : sqrt (∏ p∈q.primeFactors,(p:ℝ))≤sqrt q := by
    apply sqrt_le_sqrt
    rw [←Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq q.prod_primeFactors_dvd
  have hB : ∏ p∈q.primeFactors,B p ≤9 := by
    have hset : q.primeFactors.filter (·<4)⊆({2,3}:Finset ℕ) := by
      intro p hp
      have h := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
      have h' := (mem_filter.mp hp).2
      simp only [mem_insert,mem_singleton];omega
    have hcard := card_le_card hset
    norm_num at hcard
    simp only [B,prod_ite,prod_const,one_pow,mul_one]
    exact (pow_le_pow_right₀ (by norm_num : 1≤(3:ℝ)) hcard).trans_eq (by norm_num)
  have hpositive : 0≤∏ p∈q.primeFactors,F p := prod_nonneg (fun _ hp => hF hp)
  have hmain : (q.totient:ℝ)=q*∏ p∈q.primeFactors,F p := by
    have h := congrArg ((↑):ℚ→ℝ) (Nat.totient_eq_mul_prod_factors q)
    simpa [F] using h
  have hh := (mul_le_mul (mul_le_mul_of_nonneg_right hB hpositive) hroot (sqrt_nonneg _) (by positivity))
  have H' := mul_le_mul_of_nonneg_right (H.trans hh) (sqrt_nonneg (q:ℝ))
  rw [mul_assoc _ (sqrt q) (sqrt q),Real.mul_self_sqrt (Nat.cast_nonneg q)] at H'
  dsimp [rootProduct]
  rw [hmain]
  linarith only [H']

/-- Uniform average of the singular Hurwitz weight over a complete set of
reduced residues. The absolute constant is independent of the modulus. -/
theorem reduced_sqrt_ratio_sum_le {q : ℕ} (hq : 0<q) :
    (∑ h∈Icc 1 q,if h.Coprime q then sqrt ((q:ℝ)/h) else 0) ≤ 20*q.totient := by
  have hqr := Nat.cast_pos (α:=ℝ).mpr hq
  have he : (∑ h∈Icc 1 q,if h.Coprime q then sqrt ((q:ℝ)/h) else 0)=
      sqrt q*reducedWeightSum rootWeight q q := by
    unfold reducedWeightSum
    rw [Nat.floor_natCast,mul_sum]
    apply sum_congr rfl
    intro h hh
    by_cases hp : h.Coprime q <;> simp [hp,rootWeight,sqrt_div hqr.le,div_eq_mul_inv]
  have H := (abs_le.mp (root_reduced_error q hq hqr)).2
  have H' := mul_le_mul_of_nonneg_right H (sqrt_nonneg (q:ℝ))
  have hmain : (2*((q.totient:ℝ)/q)*sqrt q)*sqrt q=2*q.totient := by
    rw [mul_assoc _ (sqrt q) (sqrt q),Real.mul_self_sqrt hqr.le]
    field_simp
  rw [sub_mul,hmain] at H'
  rw [he]
  linarith only [H',root_product_le_totient hq]

end AnalyticNumberTheory.AnalyticTools
