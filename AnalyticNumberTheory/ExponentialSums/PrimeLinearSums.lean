import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import AnalyticNumberTheory.PrimeDistribution.PrimeSumWeights

/-! # Linear exponential sums over primes with and without logarithmic weights -/

noncomputable section

open Finset AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.ExponentialSums

/-- The linear exponential sum over primes, each prime counted once. -/
def unweightedPrimeExpSum (x α : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, AdditiveNumberTheory.e (α*p)

/-- The linear exponential sum over primes with their logarithms as weights. -/
def logPrimeExpSum (x α : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p : ℂ) * AdditiveNumberTheory.e (α*p)

/-- The three terms in Vaughan's estimate before the logarithmic factor. -/
def vaughanPrimeScale (x : ℝ) (q : ℕ) : ℝ :=
  x * (q : ℝ)^(-(1/2 : ℝ)) + x^(4/5 : ℝ) + x^(1/2 : ℝ) * (q : ℝ)^(1/2 : ℝ)

theorem vaughanPrimeScale_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (q : ℕ) :
    vaughanPrimeScale x q ≤ vaughanPrimeScale y q := by
  unfold vaughanPrimeScale
  gcongr

private lemma sqrt_le_scale {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    Real.sqrt x ≤ vaughanPrimeScale x q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow := Real.one_le_rpow hq' (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [Real.sqrt_eq_rpow]
  calc _ ≤ x^(1/2 : ℝ) * (q : ℝ)^(1/2 : ℝ) := le_mul_of_one_le_right (by positivity) hqpow
       _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- The omitted higher prime powers have mass at most `ψ(x) − θ(x)`, uniformly in the phase. -/
theorem norm_primeExpSum_sub_logPrimeExpSum_le (x α : ℝ) :
    ‖primeExpSum x α - logPrimeExpSum x α‖ ≤ Chebyshev.psi x - Chebyshev.theta x :=
  norm_sum_vonMangoldt_sub_log_primes_le x (f := fun n => AdditiveNumberTheory.e (α*n))
    (fun _ => (AdditiveNumberTheory.norm_e _).le)

/-- Pointwise comparison between the unweighted and logarithmic exponential sums. -/
theorem norm_unweightedPrimeExpSum_sub_div_log_le {x : ℝ} (hx : 1 < x) (α : ℝ) :
    ‖unweightedPrimeExpSum x α - logPrimeExpSum x α / (Real.log x : ℂ)‖ ≤
      primePi x - Chebyshev.theta x / Real.log x :=
  norm_sum_primes_sub_log_primes_div_log_le hx (f := fun n => AdditiveNumberTheory.e (α*n))
    (fun _ => (AdditiveNumberTheory.norm_e _).le)

private lemma half_le_log {x : ℝ} (hx : 2 ≤ x) : 1/2 ≤ Real.log x := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  linarith [Real.log_two_gt_d9]

/-- Vaughan's rational-approximation estimate for the sum with prime logarithms.
The right-hand side is uniform in the numerator and the real cutoff. -/
theorem logPrimeExpSum_vaughan_bound {x α : ℝ} (hx : 2 ≤ x) {a : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hα : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ‖logPrimeExpSum x α‖ ≤ 10016 * vaughanPrimeScale x q * (Real.log x)^4 := by
  have hx0 : 0 ≤ x := by linarith
  have hL := half_le_log hx
  have hL0 : 0 ≤ Real.log x := by linarith
  have hB := sqrt_le_scale hx0 hq
  have hB0 := (Real.sqrt_nonneg x).trans hB
  have hpow := one_le_pow₀ (show 1 ≤ 2*Real.log x by linarith) (n := 3)
  have hweight : 2 * Real.log x ≤ 16 * (Real.log x)^4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hpow hL0]
  have hV : ‖primeExpSum x α‖ ≤ 10000 * vaughanPrimeScale x q * (Real.log x)^4 :=
    vinogradov_prime_exp_sum_bound hq hcop hα hx
  have hE := (norm_primeExpSum_sub_logPrimeExpSum_le x α).trans ((le_abs_self _).trans
    (abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)))
  have h := norm_sub_le (primeExpSum x α) (primeExpSum x α - logPrimeExpSum x α)
  rw [sub_sub_cancel] at h
  apply h.trans
  nlinarith only [hV, hE, mul_le_mul_of_nonneg_right hB (show 0 ≤ 2*Real.log x by positivity),
    mul_le_mul_of_nonneg_left hweight hB0]

/-- The unweighted linear prime sum gains one logarithm throughout the full
Vaughan range, including real cutoffs between consecutive integers. -/
theorem unweightedPrimeExpSum_vaughan_bound {x α : ℝ} (hx : 2 ≤ x) {a : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hα : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ‖unweightedPrimeExpSum x α‖ ≤ 40080 * vaughanPrimeScale x q * (Real.log x)^3 := by
  have hx0 : 0 ≤ x := by linarith
  have hB := sqrt_le_scale hx0 hq
  have hB0 := (Real.sqrt_nonneg x).trans hB
  have hL := half_le_log hx
  have hLpos : 0 < Real.log x := by linarith
  have hpow := one_le_pow₀ (show 1 ≤ 2*Real.log x by linarith) (n := 3)
  have hsmall : 2*Real.sqrt x ≤ 16*vaughanPrimeScale x q*(Real.log x)^3 := by
    nlinarith only [hB, mul_le_mul_of_nonneg_left hpow hB0]
  have H := norm_sum_primes_le_sqrt_add_of_log_bound (H := 10016*vaughanPrimeScale x q*(Real.log x)^4)
    hx (f := fun p => AdditiveNumberTheory.e (α*p)) (fun _ => (AdditiveNumberTheory.norm_e _).le)
    (fun k hk hkx => by
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hs := logPrimeExpSum_vaughan_bound hk' hq hcop hα
      simp only [logPrimeExpSum, Nat.floor_natCast] at hs
      apply hs.trans
      have hscale := vaughanPrimeScale_mono (Nat.cast_nonneg k) hkx q
      have hlog := Real.log_le_log (by linarith : (0 : ℝ) < k) hkx
      gcongr)
  apply H.trans
  field_simp [hLpos.ne']
  nlinarith only [hsmall]

/-- On a balanced denominator range `Q ≤ q ≤ x/Q`, Vaughan's three terms
are individually bounded by `x/√Q` as long as `Q ≤ x^(2/5)`. -/
theorem vaughanPrimeScale_le_of_denominator_range {x Q : ℝ} {q : ℕ}
    (hx : 0 < x) (hQ : 0 < Q) (hQx : Q ≤ x^(2/5 : ℝ))
    (hl : Q ≤ q) (hr : (q : ℝ)*Q ≤ x) :
    vaughanPrimeScale x q ≤ 3*x/Real.sqrt Q := by
  have hq := hQ.trans_le hl
  have hs := Real.sqrt_pos.mpr hQ
  have h₁ : x*(q : ℝ)^(-(1/2 : ℝ)) ≤ x/Real.sqrt Q := by
    rw [Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hx.le hs (Real.sqrt_le_sqrt hl)
  have hsQ : Real.sqrt Q ≤ x^(1/5 : ℝ) := by
    calc Real.sqrt Q ≤ Real.sqrt (x^(2/5 : ℝ)) := Real.sqrt_le_sqrt hQx
         _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num
  have h₂ : x^(4/5 : ℝ) ≤ x/Real.sqrt Q := by
    apply (le_div_iff₀ hs).mpr
    calc _ ≤ x^(4/5 : ℝ) * x^(1/5 : ℝ) := mul_le_mul_of_nonneg_left hsQ (by positivity)
         _ = _ := by rw [← Real.rpow_add hx]; norm_num
  have h₃ : x^(1/2 : ℝ)*(q : ℝ)^(1/2 : ℝ) ≤ x/Real.sqrt Q := by
    apply (le_div_iff₀ hs).mpr
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_assoc, ← Real.sqrt_mul hq.le]
    calc _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _)
         _ = _ := Real.mul_self_sqrt hx.le
  exact (add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring)

/-- Simultaneous minor-arc estimates for the von Mangoldt, prime-logarithm
and unweighted prime sums in a balanced rational-approximation range. -/
theorem prime_exp_sums_balanced_bound {x α Q : ℝ} (hx : 2 ≤ x) {a : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hα : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (hQ : 0 < Q) (hQx : Q ≤ x^(2/5 : ℝ)) (hl : Q ≤ q) (hr : (q : ℝ)*Q ≤ x) :
    ‖primeExpSum x α‖ ≤ 30000*x/Real.sqrt Q*(Real.log x)^4 ∧
    ‖logPrimeExpSum x α‖ ≤ 30048*x/Real.sqrt Q*(Real.log x)^4 ∧
    ‖unweightedPrimeExpSum x α‖ ≤ 120240*x/Real.sqrt Q*(Real.log x)^3 := by
  have h := vaughanPrimeScale_le_of_denominator_range (by linarith : 0 < x) hQ hQx hl hr
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have estimate (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
      c * vaughanPrimeScale x q * (Real.log x)^k ≤ (3*c)*x/Real.sqrt Q*(Real.log x)^k := by
    calc _ ≤ c*(3*x/Real.sqrt Q)*(Real.log x)^k := by gcongr
         _ = _ := by ring
  have h₁ := estimate 4 (c := 10000) (by norm_num)
  have h₂ := estimate 4 (c := 10016) (by norm_num)
  have h₃ := estimate 3 (c := 40080) (by norm_num)
  norm_num only [show (3 : ℝ)*10000 = 30000 by norm_num, show (3 : ℝ)*10016 = 30048 by norm_num,
    show (3 : ℝ)*40080 = 120240 by norm_num] at h₁ h₂ h₃
  exact ⟨(vinogradov_prime_exp_sum_bound hq hcop hα hx).trans h₁,
    (logPrimeExpSum_vaughan_bound hx hq hcop hα).trans h₂,
    (unweightedPrimeExpSum_vaughan_bound hx hq hcop hα).trans h₃⟩

end AnalyticNumberTheory.ExponentialSums
