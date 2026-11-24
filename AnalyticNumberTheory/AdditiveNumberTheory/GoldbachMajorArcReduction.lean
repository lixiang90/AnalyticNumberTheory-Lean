import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSingularIntegral

/-!
# Ternary Goldbach error estimates

Combine the truncated integral and Ramanujan-series bounds with the major and
minor arc estimates. The principal term is the full singular series times the
number of positive compositions. All estimates retain the arc parameters.
-/

noncomputable section
open Finset MeasureTheory
open scoped Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Uniform error of truncating the arithmetic singular series at a positive integer. -/
theorem abs_singularSeries_sub_sum_le {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    |goldbachTernarySingularSeries N - ∑ q ∈ Icc 1 M, singularTermTernary q N| ≤
      32 * (M : ℝ) ^ (-1 / 2 : ℝ) := by
  let f := fun q => singularTermTernary q N
  let u := fun q => if q ≤ M then f q else 0
  let v := fun q => if M < q then f q else 0
  have hu : Summable u := by
    refine ((summable_singularTermTernary N).indicator (Set.Iic M)).congr fun q => ?_
    by_cases h : q ≤ M <;> simp [Set.indicator, u, f, h]
  have hv : Summable v := by
    refine ((summable_singularTermTernary N).indicator (Set.Ioi M)).congr fun q => ?_
    by_cases h : M < q <;> simp [Set.indicator, v, f, h]
  have huv : (fun q => u q + v q) = f := by ext q; by_cases h : q ≤ M <;> simp [u, v, not_lt_of_ge, *]
  have hs : (∑' q, u q) + ∑' q, v q = goldbachTernarySingularSeries N := by
    rw [← hu.tsum_add hv, huv]; rfl
  have hsplit : range (M + 1) = insert 0 (Icc 1 M) := by
    ext q
    simp only [mem_range, mem_insert, mem_Icc]; omega
  have htrunc : (∑' q, u q) = ∑ q ∈ Icc 1 M, f q := by
    calc
      _ = ∑ q ∈ range (M + 1), f q := by
        rw [sum_eq_tsum_indicator]
        congr 1
        ext q
        simp [u, Set.indicator]
      _ = _ := by
        rw [hsplit, sum_insert (by simp)]
        simp [f, singularTermTernary_zero]
  rw [← hs, htrunc, add_sub_cancel_left]
  have habs : Summable fun q => ‖v q‖ := by
    refine ((summable_abs_singularTermTernary N).indicator (Set.Ioi M)).congr fun q => ?_
    by_cases h : M < q <;> simp [v, f, Set.indicator, h, Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm habs).trans
  simpa [v, f, apply_ite norm, Real.norm_eq_abs] using tsum_tail_abs_singularTermTernary_le hM N

/-- Replacing the denominator-dependent integral by the full-period count and extending the
arithmetic sum to infinity produces two separate explicit errors. -/
theorem norm_sum_singularTerm_mul_integral_sub_le {M : ℕ} (hM : 1 ≤ M) (N : ℕ)
    {Q : ℝ} (hQ : 2 ≤ Q) :
    ‖(∑ q ∈ Icc 1 M, (singularTermTernary q N : ℂ) * ternarySingularIntegral N (1 / (q * Q))) -
      (goldbachTernarySingularSeries N : ℂ) * ((N - 1).choose 2 : ℕ)‖ ≤
      2 * Q ^ 2 * M * Real.sqrt M + 32 * (M : ℝ) ^ (-1 / 2 : ℝ) * ((N - 1).choose 2 : ℕ) := by
  let C : ℂ := ((N - 1).choose 2 : ℕ)
  let A := ∑ q ∈ Icc 1 M, (singularTermTernary q N : ℂ)
  have hi : ‖(∑ q ∈ Icc 1 M, (singularTermTernary q N : ℂ) * ternarySingularIntegral N (1 / (q * Q)))
      - A * C‖ ≤ 2 * Q ^ 2 * M * Real.sqrt M := by
    dsimp only [A]
    rw [sum_mul, ← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _q ∈ Icc 1 M, 2 * Q ^ 2 * Real.sqrt M := by
        refine sum_le_sum fun q hq => ?_
        obtain ⟨hq1, hqM⟩ := mem_Icc.mp hq
        have hp : (0 : ℝ) < q := by exact_mod_cast hq1
        have hden : 2 ≤ q * Q := by nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast hq1]
        have hH : 0 < 1 / (q * Q) := by positivity
        have hhalf : 1 / (q * Q) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hden
        have ht := norm_ternarySingularIntegral_sub_choose_le N hH hhalf
        have hw := abs_singularTermTernary_le (N := N) hq1
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        apply (mul_le_mul hw ht (norm_nonneg _) (by positivity)).trans
        have hs : (q : ℝ) ^ (-(3 : ℝ) / 2) * (q : ℝ) ^ 2 = Real.sqrt q := by
          rw [← Real.rpow_two, ← Real.rpow_add hp, Real.sqrt_eq_rpow]
          norm_num
        calc
          _ = 2 * Q ^ 2 * ((q : ℝ) ^ (-(3 : ℝ) / 2) * (q : ℝ) ^ 2) := by
            field_simp [hp.ne', show Q ≠ 0 by linarith]
            ring
          _ ≤ _ := by rw [hs]; gcongr
      _ = _ := by simp [nsmul_eq_mul]; ring
  have ha : ‖A * C - (goldbachTernarySingularSeries N : ℂ) * C‖ ≤
      32 * (M : ℝ) ^ (-1 / 2 : ℝ) * ((N - 1).choose 2 : ℕ) := by
    dsimp only [A, C]
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm, Complex.norm_natCast]
    gcongr
    exact abs_singularSeries_sub_sum_le hM N
  exact (norm_sub_le_norm_sub_add_norm_sub _ (A * C) _).trans (add_le_add hi ha)

/-- Bound the cubic major-arc contribution relative to the complete singular series.
The first term integrates the prime-sum approximation errors; the last two terms
bound the analytic and arithmetic truncations. -/
theorem norm_goldbachTernary_majorArcIntegral_sub_series_le {N M : ℕ} (hM : 1 ≤ M)
    {Q : ℝ} (hMQ : 2 * (M : ℝ) ≤ Q) (D : ℕ → ℝ)
    (happrox : ∀ q ∈ Icc 1 M, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a Q,
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ ≤ D q) :
    ‖majorArcIntegral (fun α => primeExpSum N α ^ 3 * e (-α * N)) M Q -
      (goldbachTernarySingularSeries N : ℂ) * ((N - 1).choose 2 : ℕ)‖ ≤
      (∑ q ∈ Icc 1 M, (q.totient : ℝ) * (D q * (43 * N ^ 2) * (2 / (q * Q)))) +
        (2 * Q ^ 2 * M * Real.sqrt M + 32 * (M : ℝ) ^ (-1 / 2 : ℝ) * ((N - 1).choose 2 : ℕ)) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd : majorArcDenoms (M : ℝ) = Icc 1 M := by simp [majorArcDenoms]
  have h1 := norm_goldbachTernary_majorArcIntegral_sub_le N hM' hMQ D (hd ▸ happrox)
  rw [hd] at h1
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add h1 (norm_sum_singularTerm_mul_integral_sub_le hM N (by linarith)))

/-- Full weighted three-prime count with an explicit error expressed in terms of the
linear major-arc approximation, the two truncations and the unconditional minor arcs. -/
theorem abs_goldbachTernaryWeighted_sub_series_le {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M)
    {Q : ℝ} (hMQ : 2 * (M : ℝ) ≤ Q) (D : ℕ → ℝ)
    (happrox : ∀ q ∈ Icc 1 M, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a Q,
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ ≤ D q) :
    |goldbachTernaryWeighted N - goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ)| ≤
      ((∑ q ∈ Icc 1 M, (q.totient : ℝ) * (D q * (43 * N ^ 2) * (2 / (q * Q)))) +
        (2 * Q ^ 2 * M * Real.sqrt M + 32 * (M : ℝ) ^ (-1 / 2 : ℝ) * ((N - 1).choose 2 : ℕ))) +
        10000 * (N * (M : ℝ) ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (4 / 5 : ℝ) +
        (N : ℝ) ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * (Real.log N) ^ 4 *
        (Chebyshev.psi N * Real.log N) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let f := fun α : ℝ => primeExpSum N α ^ 3 * e (-α * N)
  have he : Function.Periodic (fun α : ℝ => e (-α * N)) 1 := by
    simpa only [Int.cast_neg, Int.cast_natCast, mul_neg, neg_mul] using e_periodic_mul_int (-(N : ℤ))
  have hper : Function.Periodic f 1 := by
    intro α
    dsimp only [f]
    rw [periodic_primeExpSum N α]
    exact congrArg (fun z => primeExpSum N α ^ 3 * z) (he α)
  have hcont : Continuous f := ((continuous_primeExpSum N).pow 3).mul
    (continuous_e.comp (continuous_neg.mul continuous_const))
  have h := representationIntegral_eq_majorArcIntegral_add_minorArcIntegral_of_continuous hper hcont hM' hMQ
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_natCast, goldbachTernaryWeighted_eq_representationIntegral, h, add_sub_right_comm]
  exact (norm_add_le _ _).trans (add_le_add (norm_goldbachTernary_majorArcIntegral_sub_series_le
    hM hMQ D happrox) (norm_goldbachTernary_minorArcIntegral_le hN hM' hMQ))

end AnalyticNumberTheory.AdditiveNumberTheory
