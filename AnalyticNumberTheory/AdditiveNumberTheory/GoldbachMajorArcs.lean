import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import AnalyticNumberTheory.AnalyticTools.Summation.Abel

/-!
# Prime exponential sums at rational frequencies

At a reduced fraction `a / q`, the exponential weight is constant on residue
classes modulo `q`. The principal term is `μ(q) x / φ(q)`. Its error involves
the distribution of primes among reduced residue classes and prime powers with
prime base dividing `q`. Abel summation extends this approximation throughout each
major arc of width `1/(qQ)` using progression bounds up to the truncation point.
-/

noncomputable section

open Finset
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- At the rational frequency `a / q`, reduction of the index modulo `q` preserves the phase. -/
theorem e_rat_mul_eq_mod (a : ℤ) {q : ℕ} (hq : 0 < q) (n : ℕ) :
    e (((a : ℝ) / q) * n) = e ((n % q : ℕ) * (a : ℝ) / q) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hn : (q : ℝ) * (n / q : ℕ) + (n % q : ℕ) = n := by
    exact_mod_cast Nat.div_add_mod n q
  have heq : ((a : ℝ) / q) * n =
      (n % q : ℕ) * (a : ℝ) / q + ((a * (n / q : ℕ) : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
    field_simp [hq']
    linear_combination (a : ℝ) * -hn
  rw [heq, e_add_intCast]

/-- The exact finite Fourier transform of the progression counts gives the prime exponential sum
at each rational frequency. -/
theorem primeExpSum_rat_eq_sum_psiAP (x : ℝ) (a : ℤ) {q : ℕ} (hq : 0 < q) :
    primeExpSum x ((a : ℝ) / q) =
      ∑ r ∈ range q, (psiAP x q r : ℂ) * e ((r : ℝ) * a / q) := by
  unfold primeExpSum expSum
  have hmaps : ∀ n ∈ Icc 1 ⌊x⌋₊, n % q ∈ range q :=
    fun n _ => mem_range.mpr (Nat.mod_lt n hq)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun r hr => ?_
  have hfilter : ((Icc 1 ⌊x⌋₊).filter fun n => n % q = r) =
      ((Icc 1 ⌊x⌋₊).filter fun n => n ≡ r [MOD q]) := by
    ext n
    simp [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hr)]
  rw [psiAP, Complex.ofReal_sum, sum_mul, ← hfilter]
  refine sum_congr rfl fun n hn => ?_
  rw [e_rat_mul_eq_mod a hq, (mem_filter.mp hn).2]

/-- Prime powers with prime base dividing the modulus have total mass at most
`log q / log 2 * log x`. -/
theorem sum_psiAP_nonCoprime_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 0 < q) :
    ∑ r ∈ range q with ¬ r.Coprime q, psiAP x q r ≤ Real.log q / Real.log 2 * Real.log x := by
  have hmaps : ∀ n ∈ ((Icc 1 ⌊x⌋₊).filter fun n => ¬ n.Coprime q),
      n % q ∈ ((range q).filter fun r => ¬ r.Coprime q) := by
    intro n hn
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hq), fun h =>
      (mem_filter.mp hn).2 ((ZMod.coprime_mod_iff_coprime n q).mp h)⟩
  have hsum : ∑ r ∈ range q with ¬ r.Coprime q, psiAP x q r =
      ∑ n ∈ Icc 1 ⌊x⌋₊ with ¬ n.Coprime q, Λ n := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun r hr => ?_
    obtain ⟨hrq, hrnc⟩ := mem_filter.mp hr
    apply sum_congr _ fun _ _ => rfl
    ext n
    simp only [mem_filter, Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hrq)]
    constructor
    · rintro ⟨hn, hnr⟩
      refine ⟨⟨hn, fun h => hrnc ?_⟩, hnr⟩
      exact hnr ▸ (ZMod.coprime_mod_iff_coprime n q).mpr h
    · rintro ⟨⟨hn, _⟩, hnr⟩
      exact ⟨hn, hnr⟩
  rw [hsum]
  have h := norm_psi_sub_psiChar_one_le hx hq
  rw [psiChar_one_eq_psi_sub, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))] at h
  exact h

/-- A common error bound for the reduced residue classes gives a quantitative approximation
to the prime exponential sum at the center of a major arc. -/
theorem norm_primeExpSum_rat_sub_le {x E : ℝ} (hx : 1 ≤ x) (a : ℤ) {q : ℕ}
    (hq : 0 < q) (hcop : a.natAbs.Coprime q)
    (hE : ∀ r ∈ coprimeResidues q, |psiAP x q r - x / q.totient| ≤ E) :
    ‖primeExpSum x ((a : ℝ) / q) - (μ q : ℂ) * (x / q.totient : ℝ)‖ ≤
      (q.totient : ℝ) * E + Real.log q / Real.log 2 * Real.log x := by
  let phase := fun r : ℕ => e ((r : ℝ) * a / q)
  let w := fun r : ℕ => (psiAP x q r : ℂ) * phase r
  have hsplit := sum_filter_add_sum_filter_not (range q) (fun r => r.Coprime q) w
  change ∑ r ∈ coprimeResidues q, w r + ∑ r ∈ range q with ¬ r.Coprime q, w r =
    ∑ r ∈ range q, w r at hsplit
  have hmain : (μ q : ℂ) * (x / q.totient : ℝ) =
      ∑ r ∈ coprimeResidues q, ((x / q.totient : ℝ) : ℂ) * phase r := by
    rw [← ramanujanSum_coprime hq hcop, ramanujanSum, mul_comm, Finset.mul_sum]
  rw [primeExpSum_rat_eq_sum_psiAP x a hq, hmain]
  change ‖∑ r ∈ range q, w r - _‖ ≤ _
  rw [← hsplit, add_sub_right_comm, ← sum_sub_distrib]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _r ∈ coprimeResidues q, E := by
        refine sum_le_sum fun r hr => ?_
        dsimp only [w, phase]
        rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, norm_e, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        exact hE r hr
      _ = (q.totient : ℝ) * E := by
        simp [coprimeResidues, Nat.totient_eq_card_coprime, Nat.coprime_comm, nsmul_eq_mul]
  · apply (norm_sum_le _ _).trans
    simpa [w, phase, norm_mul, Complex.norm_real, Real.norm_of_nonneg (psiAP_nonneg _ _ _)]
      using sum_psiAP_nonCoprime_le hx hq

/-- Discrete partial summation transports an approximation at a single frequency to a nearby
frequency. The error grows by at most `1 + 2π N |β|` within the shifted exponential sum. -/
theorem norm_primeExpSum_shift_sub_main_le {N : ℕ} {α β : ℝ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ k ∈ Icc 1 N, ‖primeExpSum k α - c * k‖ ≤ D) :
    ‖primeExpSum N (α + β) - c * mainExpSum N β‖ ≤ D * (1 + 2 * Real.pi * N * |β|) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa [primeExpSum, expSum, mainExpSum] using hD
  let b := fun n : ℕ => (Λ n : ℂ) * e (α * n) - c
  let f := fun n : ℕ => e (β * n)
  have hb (k : ℕ) : ∑ n ∈ Icc 1 k, b n = primeExpSum k α - c * k := by
    simp [b, primeExpSum, expSum, sum_sub_distrib, nsmul_eq_mul, mul_comm]
  have heq : primeExpSum N (α + β) - c * mainExpSum N β =
      ∑ n ∈ Icc 1 N, b n * f n := by
    simp only [primeExpSum, expSum, mainExpSum, Nat.floor_natCast, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [add_mul, e_add, b, f]
    ring
  have hphase : e β = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    unfold e
    congr 1
    push_cast
    ring
  have hstep : ‖e β - 1‖ ≤ 2 * Real.pi * |β| := by
    rw [hphase]
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_nonneg] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β))
  have hdiff (k : ℕ) : ‖f (k + 1) - f k‖ ≤ 2 * Real.pi * |β| := by
    simp only [f, Nat.cast_add, Nat.cast_one, mul_add, mul_one, e_add, ← mul_sub_one,
      norm_mul, norm_e, one_mul]
    exact hstep
  rw [heq, abel_discrete_Icc_one]
  apply (norm_sub_le _ _).trans
  have hlast : ‖(∑ n ∈ Icc 1 N, b n) * f N‖ ≤ D := by
    simpa [hb, f, norm_mul] using hpartial N (mem_Icc.mpr ⟨hN, le_rfl⟩)
  have hsum : ‖∑ k ∈ Ico 1 N, (∑ n ∈ Icc 1 k, b n) * (f (k + 1) - f k)‖ ≤
      (N : ℝ) * (D * (2 * Real.pi * |β|)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k ∈ Ico 1 N, D * (2 * Real.pi * |β|) := by
        refine sum_le_sum fun k hk => ?_
        obtain ⟨hk1, hkN⟩ := mem_Ico.mp hk
        rw [norm_mul, hb]
        exact mul_le_mul (hpartial k (mem_Icc.mpr ⟨hk1, hkN.le⟩)) (hdiff k) (norm_nonneg _) hD
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Ico]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le N 1)) (by positivity)
  exact (add_le_add hlast hsum).trans_eq (by ring)

/-- Major-arc approximation for a reduced fraction with a displacement `β`, assuming a
bound for all reduced-class progression errors up to `N`. -/
theorem norm_primeExpSum_majorArc_sub_le {N q : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (a : ℤ) (hcop : a.natAbs.Coprime q) (β : ℝ) {E : ℝ} (hE : 0 ≤ E)
    (hprog : ∀ k ∈ Icc 1 N, ∀ r ∈ coprimeResidues q,
      |psiAP k q r - k / q.totient| ≤ E) :
    ‖primeExpSum N ((a : ℝ) / q + β) - ((μ q : ℂ) / q.totient) * mainExpSum N β‖ ≤
      (q.totient * E + Real.log q / Real.log 2 * Real.log N) *
        (1 + 2 * Real.pi * N * |β|) := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hfac : 0 ≤ Real.log q / Real.log 2 := div_nonneg hlogq (Real.log_nonneg (by norm_num))
  apply norm_primeExpSum_shift_sub_main_le (by positivity)
  intro k hk
  obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
  have h := norm_primeExpSum_rat_sub_le (by exact_mod_cast hk1 : (1 : ℝ) ≤ k) a hq hcop (hprog k hk)
  push_cast at h
  rw [div_mul_comm, mul_comm (↑k / ↑q.totient : ℂ)]
  apply h.trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by exact_mod_cast hk1 : (0 : ℝ) < k)
      (by exact_mod_cast hkN : (k : ℝ) ≤ N)) hfac)

/-- The approximation is uniform throughout the closed major arc of radius `1 / (q Q)`. -/
theorem norm_primeExpSum_sub_le_of_mem_majorArc {N q : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    {a : ℤ} (hcop : a.natAbs.Coprime q) {α Q E : ℝ} (hα : α ∈ majorArc q a Q) (hE : 0 ≤ E)
    (hprog : ∀ k ∈ Icc 1 N, ∀ r ∈ coprimeResidues q,
      |psiAP k q r - k / q.totient| ≤ E) :
    ‖primeExpSum N α - ((μ q : ℂ) / q.totient) * mainExpSum N (α - a / q)‖ ≤
      (q.totient * E + Real.log q / Real.log 2 * Real.log N) *
        (1 + 2 * Real.pi * N / (q * Q)) := by
  have h := norm_primeExpSum_majorArc_sub_le hN hq a hcop (α - a / q) hE hprog
  rw [add_sub_cancel] at h
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  refine h.trans ?_
  rw [div_eq_mul_one_div (2 * Real.pi * N)]
  gcongr
  exact mem_majorArc_iff.mp hα

/-- Under the Siegel–Walfisz hypothesis a cutoff `Y ≥ 2` gives a uniform approximation across
a major arc for all moduli `q ≤ (log Y)^A`. Below `Y` the Chebyshev bound controls the
partial sums needed by Abel summation. -/
theorem siegelWalfisz_primeExpSum_majorArc (hSW : SiegelWalfiszBound) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C > 0, ∃ c > 0, ∀ {N q : ℕ} {Y : ℝ}, 2 ≤ Y → Y ≤ N → 0 < q →
      (q : ℝ) ≤ (Real.log Y) ^ A → ∀ {a : ℤ}, a.natAbs.Coprime q → ∀ {α Q : ℝ},
      α ∈ majorArc q a Q →
      ‖primeExpSum N α - ((μ q : ℂ) / q.totient) * mainExpSum N (α - a / q)‖ ≤
        (q.totient * max (7 * Y) (C * N * Real.exp (-c * Real.sqrt (Real.log Y))) +
          Real.log q / Real.log 2 * Real.log N) * (1 + 2 * Real.pi * N / (q * Q)) := by
  obtain ⟨C, hC, c, hc, hsw⟩ := hSW A hA
  refine ⟨C, hC, c, hc, ?_⟩
  intro N q Y hY hYN hq hqY a ha α Q hα
  have hN : 1 ≤ N := by exact_mod_cast (by linarith : (1 : ℝ) ≤ N)
  have hYpos : 0 < Y := by linarith
  apply norm_primeExpSum_sub_le_of_mem_majorArc hN hq ha hα (le_trans (by positivity) (le_max_left _ _))
  intro k hk r hr
  obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases le_or_gt Y (k : ℝ) with hYk | hkY
  · apply le_trans _ (le_max_right _ _)
    have hlog : Real.log Y ≤ Real.log k := Real.log_le_log hYpos hYk
    have hqk := hqY.trans (Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog hA)
    apply (hsw k q r (hY.trans hYk) hq hqk (mem_filter.mp hr).2).trans
    have he : Real.exp (-c * Real.sqrt (Real.log k)) ≤ Real.exp (-c * Real.sqrt (Real.log Y)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hlog) (by linarith))
    gcongr
  · apply le_trans _ (le_max_left _ _)
    have hlog4 : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hpsi := (psiAP_le_psi k q r).trans (psi_le_const_mul_self hk0)
    have hpsi' : psiAP k q r ≤ 7 * Y := by nlinarith
    have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast (Nat.totient_pos.mpr hq)
    have hdiv : (k : ℝ) / q.totient ≤ Y :=
      (div_le_self hk0 ht).trans hkY.le
    exact abs_le.mpr ⟨by linarith [psiAP_nonneg (k : ℝ) q r],
      by linarith [div_nonneg hk0 (Nat.cast_nonneg q.totient)]⟩

end AnalyticNumberTheory.AdditiveNumberTheory
