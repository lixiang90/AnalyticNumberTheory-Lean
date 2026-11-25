import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSieveFactor

/-! # A divisor-sum majorant for the Goldbach sieve factor

The ratio of each local factor to 1 + 1/p is at least one. Its product
over all integers from three to m telescopes and is bounded by three.
-/
noncomputable section
open Finset Real
namespace AnalyticNumberTheory.AdditiveNumberTheory

private def localRatio (p : ℕ) : ℝ := (p:ℝ)*((p:ℝ)-1)/(((p:ℝ)+1)*((p:ℝ)-2))

private theorem one_le_localRatio {p : ℕ} (hp : 2<p) : 1≤localRatio p := by
  have h : (2:ℝ)<p := by exact_mod_cast hp
  apply (one_le_div (mul_pos (by positivity) (sub_pos.mpr h))).2
  nlinarith

private theorem ratio_product (m : ℕ) :
    (∏p∈Icc 3 (m+2),localRatio p)=3*((m:ℝ)+1)/(m+3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hset : Icc 3 (m+1+2)=insert (m+3) (Icc 3 (m+2)) := by
      ext k; simp only [mem_Icc,mem_insert]; omega
    rw [hset,prod_insert (by simp),ih]
    dsimp [localRatio]; push_cast
    ring_nf
    field_simp [show 1+(m:ℝ)≠0 by positivity,show 3+(m:ℝ)≠0 by positivity,show 4+(m:ℝ)≠0 by positivity]
    ring

/-- The Goldbach correction is at most three times the reciprocal-divisor sum. -/
theorem goldbachSieveFactor_le_divisor_sum {n : ℕ} (hn : 0<n) :
    goldbachSieveFactor n ≤ 3*∑d∈n.divisors,(d:ℝ)⁻¹ := by
  let P := n.primeFactors.filter (fun p => 2<p)
  let W := ∏ p∈n.primeFactors,p
  let ν : ArithmeticFunction ℝ := ⟨fun d : ℕ => (d:ℝ)⁻¹,by simp⟩
  have hν : ν.IsMultiplicative := by
    constructor
    · simp [ν]
    · intro m n _; simp [ν,Nat.cast_mul] <;> ring
  have hW : Squarefree W := Nat.squarefree_prod_primeFactors n
  have hfac := hν.prodPrimeFactors_one_add_of_squarefree hW
  have hpr : W.primeFactors=n.primeFactors := Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  rw [hpr] at hfac
  have hdiv : (∏p∈P,(1+(p:ℝ)⁻¹)) ≤ ∑d∈n.divisors,(d:ℝ)⁻¹ := by
    calc _ ≤ ∏p∈n.primeFactors,(1+(p:ℝ)⁻¹) := prod_le_prod_of_subset_of_one_le₀ (filter_subset ..)
            (fun p _ => by positivity) (fun p _ _ => by linarith only [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) p)])
         _ = ∑d∈W.divisors,(d:ℝ)⁻¹ := hfac
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn.ne' (Nat.prod_primeFactors_dvd n)) (fun _ _ _ => by positivity)
  have hP : P⊆Icc 3 (n+2) := by
    intro p hp
    exact mem_Icc.mpr ⟨(mem_filter.mp hp).2,(Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)).trans (by omega)⟩
  have hR : (∏p∈P,localRatio p)≤3 := by
    apply (prod_le_prod_of_subset_of_one_le₀ hP (fun p hp => zero_le_one.trans (one_le_localRatio (mem_filter.mp hp).2))
      (fun p hp _ => one_le_localRatio (mem_Icc.mp hp).1)).trans
    rw [ratio_product]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have he : goldbachSieveFactor n=(∏p∈P,localRatio p)*∏p∈P,(1+(p:ℝ)⁻¹) := by
    rw [←prod_mul_distrib]
    apply prod_congr rfl; intro p hp
    have hh : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
    dsimp [localRatio]
    field_simp [show (p:ℝ)≠0 by linarith,show (p:ℝ)-2≠0 by linarith]
    ring
  rw [he]
  exact mul_le_mul hR hdiv (prod_nonneg (fun p _ => by positivity)) (by norm_num)

end AnalyticNumberTheory.AdditiveNumberTheory
