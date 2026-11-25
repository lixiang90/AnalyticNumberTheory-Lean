import AnalyticNumberTheory.SieveMethods.PrimePairPartialSums
import AnalyticNumberTheory.PrimeDistribution.WeightedBombieriVinogradov

/-!
# Uniform upper bounds for pairs of primes

A single absolute error constant applies to every nonzero even integral
shift. At shift −2 this gives the twin-prime bound, and evaluating the
shift at the even integer being counted gives the ordered Goldbach bound.
-/

noncomputable section
open Finset Real Filter
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution

/-- Selberg's upper bound with leading coefficient 8 C(h), uniform over
every nonzero even integral shift and every real partial-sum endpoint x ≥ 3. -/
theorem primePair_eight :
    ∃ C : ℝ, 0<C ∧ ∀ {x : ℝ}, 3≤x → ∀ {h : ℤ}, Even h.natAbs → h.natAbs≠0 →
      (primePairCount x h:ℝ)≤8*primePairSingularFactor h.natAbs*(x/(log x)^2)*
        (1+C*(log (log x)/log x)) := by
  obtain ⟨B,hB,K,hK,HE⟩ := squarefree_weighted_bombieri_vinogradov 3 (by norm_num)
  obtain ⟨A,hA,H⟩ := primePair_eight_of_error hB hK (by simpa only [Real.rpow_ofNat] using HE)
  exact primePair_eight_all_of_eventual hA H

/-- Twin primes with the standard Euler constant, whose factor at two is one. -/
theorem twinPrime_eight :
    ∃ C : ℝ, 0<C ∧ ∀ {x : ℝ}, 3≤x →
      selbergTwinCount x≤8*twinPrimeEulerConstant*(x/(log x)^2)*(1+C*(log (log x)/log x)) := by
  obtain ⟨C,hC,H⟩ := primePair_eight
  refine ⟨C,hC,fun {x} hx => ?_⟩
  have h := H hx (h:=(-2:ℤ)) (by decide) (by decide)
  rw [primePairCount_neg_two] at h
  have he : ({2}:Finset ℕ).filter (fun p => 2<p)=∅ := by decide
  simpa [primePairSingularFactor,Nat.prime_two.primeFactors,he] using h

/-- Ordered representations of an even N as a sum of two primes, with the
same leading coefficient and the same relative error order. -/
theorem goldbachRepCount_eight :
    ∃ C : ℝ, 0<C ∧ ∀ {N : ℕ}, 3≤N → Even N →
      (goldbachRepCount N:ℝ)≤8*primePairSingularFactor N*((N:ℝ)/(log N)^2)*
        (1+C*(log (log N)/log N)) := by
  obtain ⟨C,hC,H⟩ := primePair_eight
  refine ⟨C,hC,fun {N} hN hE => ?_⟩
  have hl : (3:ℝ)≤N := by exact_mod_cast hN
  have h := H hl (h:=(N:ℤ)) (by simpa using hE) (by simpa using (show N≠0 by omega))
  simpa only [Int.natAbs_natCast,primePairCount_at_shift] using h

/-- Brun's reciprocal tail, uniform in both partial-sum endpoints and the shift. -/
theorem primePair_reciprocal_partial_sum :
    ∃ C : ℝ, 0<C ∧ ∀ {a b : ℝ}, 3≤a → ∀ {h : ℤ}, Even h.natAbs → h.natAbs≠0 →
      primePairReciprocalSum h a b ≤ C*primePairSingularFactor h.natAbs/log a := by
  obtain ⟨A,hA,H⟩ := primePair_eight
  let K := 8*(1+A)
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨2*K/log 2,by positivity,?_⟩
  intro a b ha h hh hh0
  let S := primePairSingularFactor h.natAbs
  have hS : 0<S := twinPrimeEulerConstant_pos.trans_le (twinPrimeEulerConstant_le_primePairSingularFactor _)
  have H' (t : ℝ) (ht : a≤t) : (primePairCount t h:ℝ) ≤ (K*S)*(t/log t^2) := by
    have hl := log_pos (show 1<t by linarith)
    have hm : log (log t)/log t≤1 := (div_le_one hl).mpr ((Real.log_le_sub_one_of_pos hl).trans (by linarith))
    have ht0 : 0≤t := by linarith
    have h0 := H (ha.trans ht) hh hh0
    calc _ ≤ 8*S*(t/log t^2)*(1+A*(log (log t)/log t)) := h0
         _ ≤ 8*S*(t/log t^2)*(1+A*1) :=
           mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hA.le)) (mul_nonneg (mul_nonneg (by norm_num) hS.le) (div_nonneg ht0 (sq_nonneg _)))
         _ = _ := by dsimp [K];ring
  exact (primePair_reciprocal_tail_of_count (b:=b) ha (mul_nonneg hK.le hS.le) H').trans_eq (by ring)

/-- The infinite reciprocal tail converges and satisfies the same uniform
bound as the finite sums. -/
theorem primePair_reciprocal_tail :
    ∃ C : ℝ, 0<C ∧ ∀ {a : ℝ}, 3≤a → ∀ {h : ℤ}, Even h.natAbs → h.natAbs≠0 →
      let f := fun p : ℕ => if a<(p:ℝ) ∧ p.Prime ∧ (primeShift h p).Prime then (p:ℝ)⁻¹ else 0
      Summable f ∧ ∑' p,f p ≤ C*primePairSingularFactor h.natAbs/log a := by
  classical
  obtain ⟨C,hC,H⟩ := primePair_reciprocal_partial_sum
  refine ⟨C,hC,?_⟩
  intro a ha h hh hh0 f
  have hf (p : ℕ) : 0≤f p := by dsimp [f];split_ifs <;>positivity
  have hb (N : ℕ) : ∑p∈range N,f p ≤ C*primePairSingularFactor h.natAbs/log a := by
    apply le_trans _ (H (b:=(N:ℝ)) ha hh hh0)
    dsimp only [f,primePairReciprocalSum]
    rw [←sum_filter,Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp,ha',hp',hq⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith : 0≤a)).mpr ha',(mem_range.mp hp).le⟩,hp',hq⟩
    · intro p _ _;positivity
  exact ⟨summable_of_sum_range_le hf hb,Real.tsum_le_of_sum_range_le hf hb⟩

end AnalyticNumberTheory.SieveMethods
