import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcs

/-!
# Ternary Goldbach integrals over the major arcs

Integrating the cube of the rational-arc approximation separates the arithmetic
factor from the integral at the origin. The result at each denominator has a
truncated singular integral whose radius is the half-width of that arc.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- The truncated singular integral for three positive summands up to `N`. -/
def ternarySingularIntegral (N : ℕ) (H : ℝ) : ℂ :=
  ∫ β in (-H)..H, mainExpSum N β ^ 3 * e (-β * N)

private def ternaryModel (N q : ℕ) (a : ℤ) (α : ℝ) : ℂ :=
  ((μ q : ℂ) / q.totient * mainExpSum N (α - a / q)) ^ 3 * e (-α * N)

private theorem continuous_ternaryIntegrand (N : ℕ) :
    Continuous (fun α : ℝ => primeExpSum N α ^ 3 * e (-α * N)) :=
  ((continuous_primeExpSum N).pow 3).mul (continuous_e.comp (continuous_neg.mul continuous_const))

private theorem continuous_ternaryModel (N q : ℕ) (a : ℤ) : Continuous (ternaryModel N q a) :=
  ((continuous_const.mul ((continuous_mainExpSum N).comp
    (continuous_id.sub continuous_const))).pow 3).mul
    (continuous_e.comp (continuous_neg.mul continuous_const))

private theorem setIntegral_ternaryModel {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (N : ℕ)
    {Q : ℝ} (hQ : 0 < Q) :
    ∫ α in majorArc q a Q, ternaryModel N q a α =
      ((μ q : ℂ) / q.totient) ^ 3 * e ((a : ℝ) * (-(N : ℝ)) / q) *
        ternarySingularIntegral N (1 / (q * Q)) := by
  rw [setIntegral_majorArc_eq _ hq a hQ, ternarySingularIntegral,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro β _
  simp only [ternaryModel, add_sub_cancel_left]
  rw [show -((a : ℝ) / q + β) * N = (a : ℝ) * (-(N : ℝ)) / q + -β * N by ring, e_add]
  ring

private theorem sum_setIntegral_ternaryModel {q : ℕ} (hq : 1 ≤ q) (N : ℕ)
    {Q : ℝ} (hQ : 0 < Q) :
    ∑ a ∈ coprimeResidues q, ∫ α in majorArc q a Q, ternaryModel N q a α =
      (singularTermTernary q N : ℂ) * ternarySingularIntegral N (1 / (q * Q)) := by
  simp_rw [setIntegral_ternaryModel hq _ N hQ]
  rw [← sum_mul, ← mul_sum]
  congr 1
  have hmu : (μ q : ℂ) ^ 3 = (μ q : ℂ) := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
  rw [div_pow, hmu, singularTermTernary]
  simp only [show q ≠ 0 by omega, ↓reduceIte]
  push_cast
  rw [← ramanujanSum_eq_ofReal_re hq, ramanujanSum]
  simp

private theorem norm_ternaryModel_diff {q N : ℕ} (hq : 0 < q) (a : ℤ) (α : ℝ) :
    ‖primeExpSum N α ^ 3 * e (-α * N) - ternaryModel N q a α‖ ≤
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ * (43 * N ^ 2) := by
  let z := primeExpSum N α
  let w := (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)
  have hz : ‖z‖ ≤ 6 * N := norm_primeExpSum_le (Nat.cast_nonneg N) α
  have hmu : ‖(μ q : ℂ)‖ ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hw : ‖w‖ ≤ N := by
    dsimp only [w]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    have hc : ‖(μ q : ℂ)‖ / q.totient ≤ 1 :=
      (div_le_one (by linarith)).mpr (hmu.trans hφ)
    simpa only [one_mul] using mul_le_mul hc (norm_mainExpSum_le N (α - a / q))
      (norm_nonneg _) zero_le_one
  change ‖z ^ 3 * _ - w ^ 3 * _‖ ≤ ‖z - w‖ * _
  rw [← sub_mul, norm_mul, norm_e, mul_one, show z ^ 3 - w ^ 3 = (z - w) * (z ^ 2 + z*w + w^2) by ring, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖z ^ 2 + z*w + w^2‖ ≤ ‖z ^ 2‖ + ‖z*w‖ + ‖w^2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (6 * (N : ℝ)) ^ 2 + (6 * N) * N + N ^ 2 := by
      rw [norm_pow, norm_mul, norm_pow]
      gcongr
    _ = _ := by ring

/-- Cubic error integrated over the reduced numerators of one fixed denominator. -/
theorem norm_ternary_arc_denominator_error {q : ℕ} (hq1 : 1 ≤ q) (N : ℕ) {Q D : ℝ}
    (hQ : 0<Q) (happrox : ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a Q,
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α-a/q)‖ ≤ D) :
    ‖(∑ a ∈ coprimeResidues q, ∫ α in majorArc q a Q, primeExpSum N α^3*e (-α*N)) -
      (singularTermTernary q N : ℂ)*ternarySingularIntegral N (1/(q*Q))‖ ≤
      (q.totient:ℝ)*(D*(43*N^2)*(2/(q*Q))) := by
  rw [← sum_setIntegral_ternaryModel hq1 N hQ, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ coprimeResidues q, D * (43 * N ^ 2) * (2 / (q * Q)) := by
      refine sum_le_sum fun a ha => ?_
      have hf : IntegrableOn (fun α : ℝ => primeExpSum N α ^ 3 * e (-α * N)) (majorArc q a Q) :=
        (continuous_ternaryIntegrand N).continuousOn.integrableOn_Icc
      have hg : IntegrableOn (ternaryModel N q a) (majorArc q a Q) :=
        (continuous_ternaryModel N q a).continuousOn.integrableOn_Icc
      rw [← integral_sub hf hg]
      have hmeas : volume (majorArc q a Q) < ⊤ := by rw [volume_majorArc hq1 _ hQ]; simp
      have hb := norm_setIntegral_le_of_norm_le_const hmeas
        (fun α hα => (norm_ternaryModel_diff hq1 a α).trans (mul_le_mul_of_nonneg_right
          (by simpa using happrox a ha α hα) (by positivity)))
      simpa [Measure.real, volume_majorArc hq1 _ hQ, ENNReal.toReal_ofReal (by positivity :
        (0 : ℝ) ≤ 2 / (q * Q))] using hb
    _ = _ := by
      simp [coprimeResidues, Nat.totient_eq_card_coprime, Nat.coprime_comm, nsmul_eq_mul]

/-- Cubing the major-arc approximations and integrating gives the truncated singular series,
with its singular integral at each arc width. The error `D q` bounds the linear
approximation pointwise on all major arcs of denominator `q`. -/
theorem norm_goldbachTernary_majorArcIntegral_sub_le (N : ℕ) {P Q : ℝ} (hP : 1 ≤ P)
    (hPQ : 2 * P ≤ Q) (D : ℕ → ℝ)
    (happrox : ∀ q ∈ majorArcDenoms P, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a Q,
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ ≤ D q) :
    ‖majorArcIntegral (fun α => primeExpSum N α ^ 3 * e (-α * N)) P Q -
      ∑ q ∈ majorArcDenoms P, (singularTermTernary q N : ℂ) *
        ternarySingularIntegral N (1 / (q * Q))‖ ≤
      ∑ q ∈ majorArcDenoms P, (q.totient : ℝ) * (D q * (43 * N ^ 2) * (2 / (q * Q))) := by
  have hQ : 0 < Q := by linarith
  rw [majorArcIntegral_eq_sum_of_continuous (continuous_ternaryIntegrand N) hPQ, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  refine sum_le_sum fun q hq => ?_
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  exact norm_ternary_arc_denominator_error hq1 N hQ (happrox q hq)

/-- Integrated major-arc approximation with errors expressed wholly in terms of
Chebyshev progression estimates up to `N`. -/
theorem norm_goldbachTernary_majorArcIntegral_sub_le_of_progressions {N : ℕ} (hN : 1 ≤ N)
    {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q) (E : ℕ → ℝ)
    (hE : ∀ q ∈ majorArcDenoms P, 0 ≤ E q)
    (hprog : ∀ q ∈ majorArcDenoms P, ∀ k ∈ Icc 1 N, ∀ r ∈ coprimeResidues q,
      |psiAP k q r - k / q.totient| ≤ E q) :
    ‖majorArcIntegral (fun α => primeExpSum N α ^ 3 * e (-α * N)) P Q -
      ∑ q ∈ majorArcDenoms P, (singularTermTernary q N : ℂ) *
        ternarySingularIntegral N (1 / (q * Q))‖ ≤
      ∑ q ∈ majorArcDenoms P, (q.totient : ℝ) *
        ((q.totient * E q + Real.log q / Real.log 2 * Real.log N) *
          (1 + 2 * Real.pi * N / (q * Q)) * (43 * N ^ 2) * (2 / (q * Q))) := by
  apply norm_goldbachTernary_majorArcIntegral_sub_le N hP hPQ
  intro q hq a ha α hα
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  have hcop : (a : ℤ).natAbs.Coprime q := (mem_filter.mp ha).2
  simpa only [Int.cast_natCast] using
    norm_primeExpSum_sub_le_of_mem_majorArc hN hq1 hcop hα (hE q hq) (hprog q hq)

end AnalyticNumberTheory.AdditiveNumberTheory
