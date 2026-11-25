import AnalyticNumberTheory.PrimeDistribution.ReciprocalMertensProduct
import AnalyticNumberTheory.PrimeDistribution.TotientLargePrimeFactors

/-! # The doubly logarithmic bound for the reciprocal totient -/

noncomputable section
open Real Finset

namespace AnalyticNumberTheory.PrimeDistribution

/-- Split the reciprocal totient at any real y ≥ 2. The small primes cost
the reciprocal Mertens product, and the large primes cost an exponential
with exponent at most 2 log n/(y log 2). -/
theorem div_totient_le_mertens_mul_exp {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 2 ≤ y) :
    (n : ℝ)/n.totient ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1-(p : ℝ)⁻¹)⁻¹) *
      Real.exp (2*Real.log n/(y*Real.log 2)) := by
  let f (p : ℕ) : ℝ := (1-(p : ℝ)⁻¹)⁻¹
  let S := n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)
  let T := n.primeFactors.filter (fun p : ℕ => y < (p : ℝ))
  have h1 (p : ℕ) (hp : p.Prime) : 1 ≤ f p := by
    have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact (one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp₁))).mpr (by linarith only [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p)])
  have hs : S ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    obtain ⟨hp',hpy⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by linarith : 0 ≤ y)).mpr hpy,Nat.prime_of_mem_primeFactors hp'⟩
  have hsmall : (∏ p ∈ S,f p) ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊, f p :=
    prod_le_prod_of_subset_of_one_le₀ hs
      (fun p hp => zero_le_one.trans (h1 p (Nat.prime_of_mem_primesLE (hs hp))))
      (fun p hp _ => h1 p (Nat.prime_of_mem_primesLE hp))
  have hsplit : (∏ p ∈ S,f p)*(∏ p ∈ T,f p) = ∏ p ∈ n.primeFactors, f p := by
    simpa only [S,T,not_le] using prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ => (p : ℝ) ≤ y) f
  rw [div_totient_eq_reciprocal_product hn, ← hsplit]
  exact mul_le_mul hsmall (reciprocal_totient_large_primes_le hn hy)
    (prod_nonneg fun p hp => zero_le_one.trans (h1 p (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)))
    (prod_nonneg fun p hp => zero_le_one.trans (h1 p (Nat.prime_of_mem_primesLE hp)))

/-- For all positive integers n one has n/φ(n) ≤ C log log (10n), with
a single absolute constant. No lower threshold on the modulus is needed. -/
theorem div_totient_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 0 < n → (n : ℝ)/n.totient ≤ C*Real.log (Real.log (10*n)) := by
  obtain ⟨K,hK,H⟩ := reciprocal_mertens_product_le
  let E := Real.exp (2/Real.log 2)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨K*E, by positivity, ?_⟩
  intro n hn
  let Y := Real.log (10*n)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hn₁
  have hy : 2 ≤ Y := by
    apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ)<10*n)).mpr
    rw [show (2 : ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith only [mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three.le,hn₁]
  have hY : 0 < Y := by linarith only [hy]
  have hnY : Real.log n ≤ Y := Real.log_le_log hn₀ (by nlinarith only [hn₀.le])
  have hlog := Real.log_pos one_lt_two
  have he : Real.exp (2*Real.log n/(Y*Real.log 2)) ≤ E := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (mul_pos hY hlog) hlog]
    nlinarith only [mul_le_mul_of_nonneg_right hnY hlog.le]
  apply (div_totient_le_mertens_mul_exp hn hy).trans
  exact (mul_le_mul (H hy) he (Real.exp_pos _).le (mul_nonneg hK.le (Real.log_nonneg (by linarith)))).trans_eq
    (by change K*Real.log Y*E = (K*E)*Real.log Y; ring)

end AnalyticNumberTheory.PrimeDistribution
