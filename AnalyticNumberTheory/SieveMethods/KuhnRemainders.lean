import AnalyticNumberTheory.SieveMethods.KuhnWeights
import AnalyticNumberTheory.SieveMethods.LinearSieveArithmetic

/-!
# Multiplicity of the arithmetic remainder in Kuhn's sieve

A modulus below z^4 has at most three distinct prime factors at least z.
Hence summing the upper sieves with a tagged medium prime costs a bounded
multiplicity in the original distribution estimate.
-/
noncomputable section
open Finset Set Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

theorem kuhn_large_divisors {M : Finset ℕ} {z : ℝ} {n : ℕ}
    (hz : 1<z) (hn : n≠0) (hnz : (n:ℝ)<z^4) (hM : ∀q∈M,q.Prime ∧ z≤q) :
    (M.filter (·∣n)).card≤3 := by
  let S := M.filter (·∣n)
  have hf : S⊆n.primeFactors := fun q hq => Nat.mem_primeFactors.mpr
    ⟨(hM q (mem_filter.mp hq).1).1,(mem_filter.mp hq).2,hn⟩
  have hd : (∏q∈S,q)∣n := (prod_dvd_prod_of_subset _ _ _ hf).trans (Nat.prod_primeFactors_dvd _)
  have hl : z^S.card≤(n:ℝ) := by
    calc _ = ∏q∈S,z := by rw [prod_const]
         _ ≤ ∏q∈S,(q:ℝ) := prod_le_prod₀ (fun _ _ => (zero_lt_one.trans hz).le) (fun q hq => (hM q (mem_filter.mp hq).1).2)
         _ ≤ _ := by rw [←Nat.cast_prod]; exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  change S.card≤3
  by_contra h
  have hc : 4≤S.card := by omega
  exact (not_le.mpr hnz) ((pow_le_pow_right₀ hz.le hc).trans hl)

private theorem kuhn_tagged_sum {M : Finset ℕ} {z y : ℝ} {N : ℕ} (F : ℕ → ℝ)
    (hz : 1<z) (hy : y<z^4) (hM : ∀q∈M,q.Prime ∧ z≤q)
    (hy₀ : 0≤y) (hF : ∀n∈Finset.Icc 1 ⌊y⌋₊,0≤F n) :
    (∑q∈M,∑d∈N.divisors.filter (fun d : ℕ => (d:ℝ)<y/q),F (q*d))≤
      3*∑n∈Finset.Icc 1 ⌊y⌋₊,F n := by
  let T := Finset.Icc 1 ⌊y⌋₊
  have himg (q : ℕ) (hq : q∈M) :
      (∑d∈N.divisors.filter (fun d : ℕ => (d:ℝ)<y/q),F (q*d))≤∑n∈T.filter (q∣·),F n := by
    let D := N.divisors.filter (fun d : ℕ => (d:ℝ)<y/q)
    have hqp := (hM q hq).1.pos
    have hqr : (0:ℝ)<q := by exact_mod_cast hqp
    have hsub : D.image (q*·)⊆T.filter (q∣·) := by
      intro n hn; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hdN,hdq⟩ := mem_filter.mp hd
      have hd₀ := Nat.pos_of_mem_divisors hdN
      have hsmall : ((q*d:ℕ):ℝ)<y := by push_cast; linarith [(lt_div_iff₀ hqr).mp hdq]
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hqp hd₀,Nat.le_floor hsmall.le⟩,dvd_mul_right ..⟩
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hF n (mem_filter.mp hn).1))
    rw [sum_image (by intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hqp hab : Set.InjOn (q*·) (D : Set ℕ))]
  apply (sum_le_sum himg).trans
  simp_rw [sum_filter]; rw [sum_comm,mul_sum]
  apply sum_le_sum; intro n hn
  have hny : (n:ℝ)≤y := (Nat.le_floor_iff hy₀).mp (mem_Icc.mp hn).2
  rw [←sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast kuhn_large_divisors hz (Nat.ne_of_gt (mem_Icc.mp hn).1) (hny.trans_lt hy) hM) (hF n hn)

/-- A combined nonnegative error majorant for all the tagged sieve levels.
The prime q and the divisor d contribute through their product qd. -/
theorem kuhn_remainder_sum {M : Finset ℕ} {z y : ℝ} {N : ℕ} (F : ℕ → ℝ)
    (hz : 1<z) (hy : y<z^4) (hM : ∀q∈M,q.Prime ∧ z≤q)
    (hy₀ : 0≤y) (hF : ∀n∈Finset.Icc 1 ⌊y⌋₊,0≤F n) (hN : N≠0) :
    (∑d∈N.divisors.filter (fun d : ℕ => (d:ℝ)<y),F d)+
      (1/2:ℝ)*(∑q∈M,∑d∈N.divisors.filter (fun d : ℕ => (d:ℝ)<y/q),F (q*d))≤
      (5/2:ℝ)*∑n∈Finset.Icc 1 ⌊y⌋₊,F n := by
  have hh := kuhn_tagged_sum (N:=N) F hz hy hM hy₀ hF
  have hm : (∑d∈N.divisors.filter (fun d : ℕ => (d:ℝ)<y),F d)≤∑n∈Finset.Icc 1 ⌊y⌋₊,F n := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun n hn _ => hF n hn)
    intro n hn; obtain ⟨hd,hy'⟩ := mem_filter.mp hn
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_floor hy'.le⟩
  linarith only [hh,hm]

end AnalyticNumberTheory.SieveMethods
