import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach

/-!
# Prime-power contribution to the binary Goldbach count

If an integer has no representation by two primes, every von Mangoldt
weighted pair has a nonprime summand. The total weight of higher prime
powers bounds its entire binary convolution.
-/

noncomputable section
open Finset
open scoped Classical ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Removing one summation index from the binary von Mangoldt convolution. -/
theorem goldbachBinaryWeighted_eq_sum (n : ℕ) :
    goldbachBinaryWeighted n = ∑ j ∈ Icc 1 (n-1), Λ j * Λ (n-j) := by
  unfold goldbachBinaryWeighted
  have row (j : ℕ) : (∑ k ∈ Icc 1 n, if j+k=n then Λ j*Λ k else 0) =
      if j<n then Λ j*Λ (n-j) else 0 := by
    by_cases hj : j<n
    · simp only [hj,↓reduceIte]
      simp_rw [show ∀ k : ℕ, j+k=n ↔ k=n-j from fun k => by omega]
      rw [sum_ite_eq']
      simp [mem_Icc,show 1 ≤ n-j by omega]
    · simp only [hj,↓reduceIte]
      apply sum_eq_zero
      intro k hk
      have := (mem_Icc.mp hk).1
      simp [show j+k≠n by omega]
  simp_rw [row]
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter,mem_Icc]
  omega

/-- Without any prime-pair representation, only higher prime powers can
contribute. Their von Mangoldt weight gives a square-root bound. -/
theorem goldbachBinaryWeighted_le_of_no_prime_pair {n : ℕ} (hn : 1 ≤ n)
    (h : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) :
    goldbachBinaryWeighted n ≤ 42*Real.sqrt n*Real.log n := by
  let r := fun j : ℕ => if j.Prime then 0 else Λ j
  let S := Icc 1 (n-1)
  have hr (j : ℕ) : 0 ≤ r j := by dsimp [r]; split <;> positivity
  have hlog := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
  have hL (i : ℕ) (hi : i∈S) : Λ i ≤ Real.log n := by
    have ⟨h1,hi'⟩ := mem_Icc.mp hi
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast hi'.trans (Nat.sub_le n 1)))
  have hmem (i : ℕ) (hi : i∈S) : n-i∈S := by
    obtain ⟨h1,hi'⟩ := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hs : ∑ i ∈ S, r (n-i) = ∑ i ∈ S, r i := by
    refine sum_bij (fun i _ => n-i) hmem ?_ ?_ (fun _ _ => rfl)
    · intro i hi j hj he
      have := (mem_Icc.mp hi).2
      have := (mem_Icc.mp hj).2
      omega
    · intro i hi
      exact ⟨n-i,hmem i hi,by have := (mem_Icc.mp hi).2; omega⟩
  have hsR : ∑ i ∈ S, r i ≤ 21*Real.sqrt n := by
    calc
      _ ≤ ∑ i ∈ Icc 1 n, r i := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.sub_le n 1)) (fun i _ _ => hr i)
      _ = Chebyshev.psi n - Chebyshev.theta n := by
        rw [psi_eq_sum_Icc,theta_eq_sum_Icc,Nat.floor_natCast,sum_filter,← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        by_cases hp : i.Prime <;> simp [r,hp,ArithmeticFunction.vonMangoldt_apply_prime]
      _ ≤ _ := ((le_abs_self _).trans (abs_psi_sub_theta_le_mul_sqrt n)).trans
        (mul_le_mul_of_nonneg_right (by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ))]) (Real.sqrt_nonneg _))
  rw [goldbachBinaryWeighted_eq_sum]
  calc
    _ ≤ ∑ j ∈ S, (r j+r (n-j))*Real.log n := by
      refine sum_le_sum fun j hj => ?_
      by_cases hp : j.Prime
      · have hq : ¬ (n-j).Prime := fun hq => h ⟨j,n-j,hp,hq,by have := (mem_Icc.mp hj).2; omega⟩
        simp only [r,hp,hq,↓reduceIte,zero_add]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right (hL j hj) (ArithmeticFunction.vonMangoldt_nonneg (n := n-j))
      · have hj' : r j = Λ j := by simp [r,hp]
        calc
          _ ≤ Λ j * Real.log n := mul_le_mul_of_nonneg_left (hL _ (hmem j hj)) ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [hj']; linarith [hr (n-j)]) hlog
    _ = ((∑ i ∈ S, r i)+(∑ i ∈ S, r i))*Real.log n := by rw [← sum_mul,sum_add_distrib,hs]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsR hlog]

end AnalyticNumberTheory.AdditiveNumberTheory
