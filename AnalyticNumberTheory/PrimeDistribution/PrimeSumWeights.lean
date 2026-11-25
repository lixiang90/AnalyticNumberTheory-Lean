import AnalyticNumberTheory.PrimeDistribution.Chebyshev

/-! # Comparing von Mangoldt weights, prime logarithms, and prime counting -/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.PrimeDistribution

/-- Replacing the von Mangoldt weight by prime logarithms costs at most
`ψ(x) − θ(x)` against any complex function of modulus at most one. -/
theorem norm_sum_vonMangoldt_sub_log_primes_le (x : ℝ) {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℂ) * f n) -
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p : ℂ) * f p‖ ≤ Chebyshev.psi x - Chebyshev.theta x := by
  rw [Nat.primesLE_eq_filter_Icc_one, sum_filter, ← sum_sub_distrib,
    psi_eq_sum_Icc, theta_eq_sum_Icc, sum_filter, ← sum_sub_distrib]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun n _ => ?_
  by_cases hp : n.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime]
  · simp only [hp, ite_false, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (hf n)

/-- For bounded complex weights, removing prime logarithms after division by
`log x` costs at most the scalar difference `π(x) − θ(x)/log x`.
The estimate is exact for the constant weight one. -/
theorem norm_sum_primes_sub_log_primes_div_log_le {x : ℝ} (hx : 1 < x) {f : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(∑ p ∈ Nat.primesLE ⌊x⌋₊, f p) -
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p : ℂ) * f p) / (Real.log x : ℂ)‖ ≤
      primePi x - Chebyshev.theta x / Real.log x := by
  rw [sum_div, ← sum_sub_distrib, primePi_eq_sum, theta_eq_sum_primesLE, sum_div, ← sum_sub_distrib]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun p hp => ?_
  have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff (zero_lt_one.trans hx).le).mp (Nat.le_of_mem_primesLE hp)
  have hlog := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) hpx
  have hpos : 0 ≤ 1 - Real.log p / Real.log x := sub_nonneg.mpr
      ((div_le_one (Real.log_pos hx)).mpr hlog)
  rw [show f p - (Real.log p : ℂ)*f p/(Real.log x : ℂ) =
        ((1 - Real.log p / Real.log x : ℝ) : ℂ) * f p by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  exact mul_le_of_le_one_right hpos (hf p)

/-- Abel summation removes a prime logarithm on the block `m < p ≤ N`.
A common bound on the initial logarithmic sums costs at most `2H/log m`
on this block, plus the trivial bound for the first `m` integers. -/
theorem norm_sum_primes_le_of_log_partial_bounds {m N : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {H : ℝ}
    (hS : ∀ k, m ≤ k → k ≤ N → ‖∑ p ∈ Nat.primesLE k, (Real.log p : ℂ) * f p‖ ≤ H) :
    ‖∑ p ∈ Nat.primesLE N, f p‖ ≤ m + 2*H / Real.log m := by
  let b := fun n : ℕ => if n.Prime then f n else 0
  let c := fun n : ℕ => (Real.log n : ℂ) * b n
  let w := fun n : ℕ => 1 / Real.log (max 2 (n : ℝ))
  have hb (k : ℕ) : ∑ n ∈ Ioc 0 k, b n = ∑ p ∈ Nat.primesLE k, f p := by
    rw [Nat.primesLE_eq_filter_Ioc_zero, sum_filter]
  have hc (k : ℕ) : ∑ n ∈ Ioc 0 k, c n = ∑ p ∈ Nat.primesLE k, (Real.log p : ℂ)*f p := by
    rw [Nat.primesLE_eq_filter_Ioc_zero, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : n.Prime <;> simp [c, b, hn]
  have hlog (n : ℕ) : 0 < Real.log (max 2 (n : ℝ)) :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _))
  have hw : Antitone w := fun i j hij => one_div_le_one_div_of_le (hlog i)
    (Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left 2 (i : ℝ)))
      (max_le_max_left 2 (Nat.cast_le.mpr hij)))
  have hH := (norm_nonneg _).trans (hS m le_rfl hmN)
  have htail := AnalyticNumberTheory.AnalyticTools.Summation.norm_sum_Ioc_antitone_weight w c hw
    (fun n => one_div_nonneg.mpr (hlog n).le) hmN (show 0 ≤ 2*H by positivity)
    (fun k hmk hkN => by
      have hsplit := sum_Ioc_consecutive c (Nat.zero_le m) hmk
      rw [hc m, hc k] at hsplit
      rw [show (∑ n ∈ Ioc m k, c n) = _ - _ from eq_sub_of_add_eq' hsplit]
      exact (norm_sub_le ..).trans ((add_le_add (hS k hmk hkN) (hS m le_rfl hmN)).trans_eq (by ring)))
  have heq : ∑ n ∈ Ioc m N, (w n : ℂ)*c n = ∑ n ∈ Ioc m N, b n := by
    apply sum_congr rfl
    intro n hn
    have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hm.trans (mem_Ioc.mp hn).1.le
    have hnlog := (Real.log_pos (show (1 : ℝ) < n by linarith)).ne'
    dsimp only [w, c]
    rw [max_eq_right hn₂, one_div, Complex.ofReal_inv, ← mul_assoc,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hnlog), one_mul]
  rw [heq] at htail
  have hinit : ‖∑ n ∈ Ioc 0 m, b n‖ ≤ m := by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑ _n ∈ Ioc 0 m, (1 : ℝ) := sum_le_sum fun n _ => by
            by_cases h : n.Prime <;> simp [b, h, hf]
         _ = _ := by simp
  rw [← hb N, ← sum_Ioc_consecutive b (Nat.zero_le m) hmN]
  apply (norm_add_le ..).trans ((add_le_add hinit htail).trans_eq ?_)
  dsimp [w]
  rw [max_eq_right (by exact_mod_cast hm)]
  ring

/-- A uniform logarithm-weighted bound through a real cutoff gives a saving
of one logarithm in the unweighted prime sum. -/
theorem norm_sum_primes_le_sqrt_add_of_log_bound {x H : ℝ} (hx : 2 ≤ x)
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hS : ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ x → ‖∑ p ∈ Nat.primesLE k, (Real.log p : ℂ)*f p‖ ≤ H) :
    ‖∑ p ∈ Nat.primesLE ⌊x⌋₊, f p‖ ≤ 2*Real.sqrt x + 4*H / Real.log x := by
  let m := ⌈Real.sqrt x⌉₊
  have hx0 : 0 < x := by linarith
  have hs := Real.sq_sqrt hx0.le
  have hs₁ : 1 < Real.sqrt x := by nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x-1)]
  have hceil : Real.sqrt x ≤ (m : ℝ) := Nat.le_ceil _
  have hm : 2 ≤ m := by exact_mod_cast (show (1 : ℝ) < m from hs₁.trans_le hceil)
  have hf₂ : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by simpa using hx)
  have hf₂' : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hf₂
  have hmf : m ≤ ⌊x⌋₊ := Nat.ceil_le.mpr (Real.sqrt_le_iff.mpr ⟨by positivity, by
    nlinarith [Nat.lt_floor_add_one x, sq_nonneg ((⌊x⌋₊ : ℝ)-2)]⟩)
  have h := norm_sum_primes_le_of_log_partial_bounds hm hmf hf
    (fun k hk hk' => hS k (hm.trans hk) ((Nat.cast_le.mpr hk').trans (Nat.floor_le hx0.le)))
  have hprev : (m : ℝ) ≤ 2*Real.sqrt x := by
    have ht := Nat.ceil_lt_add_one (Real.sqrt_nonneg x)
    change (m : ℝ) < _ at ht
    linarith
  have hlog := Real.log_le_log (Real.sqrt_pos.mpr hx0) hceil
  rw [Real.log_sqrt hx0.le] at hlog
  have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos (hs₁.trans_le hceil)
  have hxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hH := (norm_nonneg _).trans (hS 2 le_rfl (by simpa using hx))
  apply h.trans (add_le_add hprev ?_)
  apply (div_le_div_iff₀ hmpos hxpos).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hlog hH]

end AnalyticNumberTheory.PrimeDistribution
