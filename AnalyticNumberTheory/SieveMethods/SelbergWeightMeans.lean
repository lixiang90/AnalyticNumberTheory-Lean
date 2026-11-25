import AnalyticNumberTheory.SieveMethods.SelbergEulerValues
import AnalyticNumberTheory.SieveMethods.LargeSieve

/-!
# Mean values of the Selberg denominator and weight mass

For the unrestricted sieve the denominator is Real.log N plus an explicit positive
constant and a term tending to zero. The weight mass is asymptotic to
(15/π²)N.
-/

open Filter Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma Topology
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.SieveMethods

private theorem weight_squarefree {n : ℕ} (hn : Squarefree n) (c : ℝ) :
    selbergWeightCoefficient c n=(∏p∈n.primeFactors, ((p:ℝ)+c))/(n.totient:ℝ) := by
  rw [selbergWeightCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    ← Int.cast_pow,moebius_sq_eq_one_of_squarefree hn,Int.cast_one,one_mul,
    prodPrimeFactors_apply hn.ne_zero,Finset.prod_div_distrib,totient_squarefree_eq_prod
      (Nat.pos_of_ne_zero hn.ne_zero) hn,Nat.cast_prod]
  congr 1
  apply prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le,Nat.cast_one]

private theorem weight_not_squarefree {n : ℕ} (hn : ¬Squarefree n) (c : ℝ) :
    selbergWeightCoefficient c n=0 := by
  simp [selbergWeightCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    moebius_eq_zero_of_not_squarefree hn]

private theorem weight_sigma {n : ℕ} (hn : Squarefree n) :
    selbergWeightCoefficient 1 n=(∑ d∈n.divisors,(d:ℝ))/(n.totient:ℝ) := by
  rw [weight_squarefree hn]
  congr 1
  have hs := (isMultiplicative_sigma (k:=1)).prod_primeFactors hn
  rw [← Nat.cast_sum,← sigma_one_apply,← hs,Nat.cast_prod]
  refine prod_congr rfl fun p hp => ?_
  simp [sigma_apply,(Nat.prime_of_mem_primeFactors hp).divisors,
    (Nat.prime_of_mem_primeFactors hp).ne_one,Ne.symm (Nat.prime_of_mem_primeFactors hp).ne_one,add_comm]

private theorem weight_phi {n : ℕ} (hn : Squarefree n) :
    selbergWeightCoefficient 0 n/(n:ℝ)=(n.totient:ℝ)⁻¹ := by
  rw [weight_squarefree hn]
  have hprod : (∏p∈n.primeFactors,(p:ℝ))=n := by
    have hh := congrArg (fun m : ℕ => (m:ℝ)) (Nat.prod_primeFactors_of_squarefree hn)
    simpa only [Nat.cast_prod] using hh
  simp only [add_zero,hprod]
  field_simp [show (n:ℝ)≠0 by exact_mod_cast hn.ne_zero]

/-- The second-order constant in the denominator of the one-dimensional Selberg sieve. -/
noncomputable def selbergDenominatorConstant : ℝ := Real.eulerMascheroniConstant+
  ∑' p : Nat.Primes, Real.log p.val/((p.val:ℝ)*(p.val-1))

private theorem log_limit_value :
    (∑' n : ℕ,selbergNormalizedCoefficient 0 n*(Real.eulerMascheroniConstant-Real.log n))=
      selbergDenominatorConstant := by
  have hm := selbergMeanCoefficient_moments (c:=0) (le_refl _) (by norm_num)
  have h₁ : Summable (selbergNormalizedCoefficient 0) := hm.1.of_abs
  have h₂ : Summable (fun n : ℕ => selbergNormalizedCoefficient 0 n*Real.log n) := hm.2.of_abs
  have hp := hasSum_selbergNormalizedCoefficient_log.tsum_eq
  simp_rw [neg_div] at hp
  rw [tsum_neg] at hp
  simp_rw [mul_sub]
  rw [(h₁.mul_right _).tsum_sub h₂,tsum_mul_right,tsum_selbergNormalizedCoefficient_zero,one_mul,
    ← hp,selbergDenominatorConstant,sub_neg_eq_add]

/-- Asymptotic expansion of the squarefree reciprocal-totient sum through its constant term. -/
theorem tendsto_selberg_denominator_centered :
    Tendsto (fun N : ℕ => (∑ d∈(Icc 1 N).filter Squarefree,(d.totient:ℝ)⁻¹)-Real.log N)
      atTop (𝓝 selbergDenominatorConstant) := by
  have H := tendsto_divisor_harmonic_centered (h:=selbergNormalizedCoefficient 0)
    (by simp [selbergNormalizedCoefficient]) (selbergMeanCoefficient_log_summable (le_refl 0) (by norm_num))
  rw [log_limit_value] at H
  apply H.congr'
  apply Eventually.of_forall
  intro N
  have hs (d : ℕ) (hd : d∉Icc 1 N) : selbergNormalizedCoefficient 0 d*(harmonic (N/d):ℝ)=0 := by
    by_cases hz : d=0
    · simp [hz,selbergNormalizedCoefficient]
    rw [Nat.div_eq_of_lt (by simp only [mem_Icc,not_and_or,not_le] at hd; omega : N<d)]
    simp
  have hfin := (hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) hs).summable
  have h₁ : Summable (selbergNormalizedCoefficient 0) :=
    (selbergMeanCoefficient_moments (le_refl 0) (by norm_num)).1.of_abs
  simp_rw [mul_sub]
  rw [hfin.tsum_sub (h₁.mul_right _),tsum_mul_right,tsum_selbergNormalizedCoefficient_zero,one_mul]
  congr 1
  change (∑' d : ℕ,(selbergMeanCoefficient 0 d/(d:ℝ))*(harmonic (N/d):ℝ))=_
  rw [← sum_divisor_sum_div_eq_tsum_harmonic,Finset.sum_filter]
  simp_rw [sum_selbergMeanCoefficient_divisors]
  apply sum_congr rfl
  intro d hd
  split_ifs with h
  · exact weight_phi h
  · simp [weight_not_squarefree h]

/-- The absolute-weight mass grows as (15/π²)N. -/
theorem tendsto_selbergWeightMass_div :
    Tendsto (fun N : ℕ => selbergWeightMass ((Icc 1 N).filter Squarefree)/(N:ℝ)) atTop (𝓝 (15/π^2)) := by
  have H := tendsto_divisor_weighted_count (h:=selbergMeanCoefficient 1)
    (by simpa only [abs_div,show ∀ n : ℕ, |(n:ℝ)|=(n:ℝ) from fun n => abs_of_nonneg (Nat.cast_nonneg n)] using
      (selbergMeanCoefficient_moments (c:=1) (by norm_num) (le_refl _)).1)
  change Tendsto _ _ (𝓝 (∑' n : ℕ,selbergNormalizedCoefficient 1 n)) at H
  rw [tsum_selbergNormalizedCoefficient_one] at H
  apply H.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [← sum_divisor_sum_eq_weighted_floor,selbergWeightMass,Finset.sum_filter]
  simp_rw [sum_selbergMeanCoefficient_divisors]
  congr 1
  apply sum_congr rfl
  intro d hd
  split_ifs with h
  · exact weight_sigma h
  · exact weight_not_squarefree h _

end AnalyticNumberTheory.SieveMethods
