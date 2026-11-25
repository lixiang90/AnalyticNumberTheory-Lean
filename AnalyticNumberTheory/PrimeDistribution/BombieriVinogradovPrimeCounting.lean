import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovMaximal

/-!
# The Bombieri–Vinogradov theorem for prime counts

Abel summation transfers a uniform estimate for the Chebyshev function to prime
counts with the logarithmic integral as main term. The normalization here is
`logIntegral 2 = 0`.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical Interval

namespace AnalyticNumberTheory.PrimeDistribution

/-- Abel summation with a uniform error on the full interval. The lower endpoint
contributes `2/φ(q)` because the logarithmic integral starts at two. -/
theorem abs_piAP_sub_logIntegral_le_of_uniform_theta {y M : ℝ} (hy : 2 ≤ y) {q a : ℕ}
    (hq : 1 ≤ q) (hM : ∀ t ∈ Set.Icc (2:ℝ) y, |thetaAP t q a - t/q.totient| ≤ M) :
    |piAP y q a - logIntegral y/q.totient| ≤ (M + 2/q.totient) / Real.log 2 := by
  let φ := (q.totient:ℝ)
  let E (t : ℝ) := thetaAP t q a - t/φ
  let w (t : ℝ) := (t * Real.log t ^ 2)⁻¹
  have hφ : 0 < φ := by dsimp [φ]; exact_mod_cast Nat.totient_pos.mpr hq
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM y ⟨hy,le_rfl⟩)
  have hwcont : ContinuousOn w (Set.uIcc 2 y) := by
    rw [Set.uIcc_of_le hy]
    have hlog : ContinuousOn Real.log (Set.Icc 2 y) :=
      Real.continuousOn_log.mono fun t ht => (zero_lt_two.trans_le ht.1).ne'
    refine (continuousOn_id.mul (hlog.pow 2)).inv₀ fun t ht => ?_
    exact mul_ne_zero (zero_lt_two.trans_le ht.1).ne' (pow_ne_zero 2 (Real.log_pos (one_lt_two.trans_le ht.1)).ne')
  have hwint := hwcont.intervalIntegrable (μ:=volume)
  have hθ : IntervalIntegrable (fun t => thetaAP t q a) volume 2 y :=
    (show Monotone (fun t => thetaAP t q a) from fun _ _ h => thetaAP_mono h).monotoneOn _ |>.intervalIntegrable
  have hl : IntervalIntegrable (fun t : ℝ => t/φ) volume 2 y :=
    (continuous_id.div_const φ).intervalIntegrable ..
  have hE := (hθ.sub hl).mul_continuousOn hwcont
  have hwt : ∀ t ∈ Set.uIcc 2 y, HasDerivAt (fun u => -(Real.log u)⁻¹) (w t) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht₀ := (zero_lt_two.trans_le ht.1).ne'
    have ht₁ := (Real.log_pos (one_lt_two.trans_le ht.1)).ne'
    convert ((Real.hasDerivAt_log ht₀).inv ht₁).neg using 1
    dsimp only [w]; field_simp
  have hintw : ∫ t in (2:ℝ)..y, w t = (Real.log 2)⁻¹-(Real.log y)⁻¹ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hwt hwint]; ring
  have hmain : ∫ t in (2:ℝ)..y, (t/φ)*w t = (∫ t in (2:ℝ)..y, 1/Real.log t^2)/φ := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hy] at ht
    dsimp only [w]; field_simp [(zero_lt_two.trans_le ht.1).ne']
  have hid : piAP y q a - logIntegral y/φ =
      E y/Real.log y + (2/φ)/Real.log 2 + ∫ t in (2:ℝ)..y, E t*w t := by
    rw [piAP_eq_thetaAP_div_log_add_integral hy, logIntegral_eq_div_log_add_integral hy]
    have hsplit : ∫ t in (2:ℝ)..y, E t*w t =
        (∫ t in (2:ℝ)..y, thetaAP t q a * w t) - ∫ t in (2:ℝ)..y, (t/φ)*w t := by
      rw [← intervalIntegral.integral_sub (hθ.mul_continuousOn hwcont) (hl.mul_continuousOn hwcont)]
      exact intervalIntegral.integral_congr fun t _ => by dsimp only [E]; ring
    rw [hsplit,hmain]
    simp only [E,w,div_eq_mul_inv]
    ring
  have hbound : |∫ t in (2:ℝ)..y, E t*w t| ≤ M*((Real.log 2)⁻¹-(Real.log y)⁻¹) := by
    have hh := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=fun t => E t*w t) hy
    rw [Real.norm_eq_abs] at hh
    apply hh.trans
    rw [← hintw, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hy hE.norm (hwint.const_mul M)
    intro t ht
    have ht₀ := zero_lt_two.trans_le ht.1
    have hw : 0 ≤ w t := by dsimp [w]; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (hM t ht) hw
  have hY : |E y / Real.log y| ≤ M / Real.log y := by
    rw [abs_div, abs_of_pos hlogy]
    exact div_le_div_of_nonneg_right (hM y ⟨hy,le_rfl⟩) hlogy.le
  have hlower : |(2/φ)/Real.log 2| = (2/φ)/Real.log 2 := abs_of_pos (div_pos (div_pos zero_lt_two hφ) hlog2)
  change |piAP y q a - logIntegral y/φ| ≤ (M+2/φ)/Real.log 2
  rw [hid]
  calc
    _ ≤ (|E y / Real.log y| + |(2/φ)/Real.log 2|) + |∫ t in (2:ℝ)..y, E t*w t| :=
      (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
    _ ≤ (M/Real.log y + (2/φ)/Real.log 2) + M*((Real.log 2)⁻¹-(Real.log y)⁻¹) := by
      rw [hlower]
      linarith only [hY, hbound]
    _ = _ := by ring

/-- The supremum of prime-counting errors over endpoints `2 ≤ y ≤ x` and all
reduced residue classes. -/
def maximalPiAPError (x : ℝ) (q : ℕ) : ℝ :=
  sSup {z | ∃ y ∈ Set.Icc (2:ℝ) x, ∃ a : ℕ, a.Coprime q ∧ z = |piAP y q a - logIntegral y/q.totient|}

private lemma piAPError_le {x y : ℝ} (hy : y ∈ Set.Icc 2 x) {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    |piAP y q a - logIntegral y/q.totient| ≤ (((Real.log 4+4)*3+2)/Real.log 2) *
      (maximalPsiAPError x q + Real.sqrt x) := by
  have hx := hy.1.trans hy.2
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  have hφ : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog2 := Real.log_pos one_lt_two
  have hp := (maxPsiAPError_nonneg 0 q).trans
    (maxPsiAPError_le_maximalPsiAPError le_rfl (by linarith : 0 ≤ x) hq)
  let c := (Real.log 4+4)*3
  have hc : 0 ≤ c := by dsimp [c]; positivity
  apply (abs_piAP_sub_logIntegral_le_of_uniform_theta hy.1 hq (M:=maximalPsiAPError x q+c*Real.sqrt x)
    (fun t ht => abs_thetaAP_sub_le_maximalPsiAPError (zero_lt_two.le.trans ht.1) (ht.2.trans hy.2) hq ha)).trans
  change (maximalPsiAPError x q+c*Real.sqrt x+2/q.totient)/Real.log 2 ≤ (c+2)/Real.log 2*_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog2.le
  nlinarith only [hs, hp, mul_nonneg hc hp, div_le_self (by norm_num : 0 ≤ (2:ℝ)) hφ]

/-- The error at each admissible endpoint and residue is bounded by the maximal error. -/
theorem abs_piAP_sub_le_maximalPiAPError {x y : ℝ} (hy : y ∈ Set.Icc 2 x)
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    |piAP y q a - logIntegral y/q.totient| ≤ maximalPiAPError x q := by
  unfold maximalPiAPError
  apply le_csSup
  · refine ⟨(((Real.log 4+4)*3+2)/Real.log 2)*(maximalPsiAPError x q+Real.sqrt x), ?_⟩
    rintro z ⟨t, ht, b, hb, rfl⟩
    exact piAPError_le ht hq hb
  · exact ⟨y,hy,a,ha,rfl⟩

/-- Partial summation transfers the maximal Chebyshev discrepancy to the
prime counting function and its logarithmic integral main term. -/
theorem maximalPiAPError_le_maximalPsi_add_sqrt {x : ℝ} (hx : 2 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    maximalPiAPError x q ≤ (((Real.log 4+4)*3+2)/Real.log 2) *
      (maximalPsiAPError x q + Real.sqrt x) := by
  unfold maximalPiAPError
  apply csSup_le
  · exact ⟨_, (2:ℝ), ⟨le_rfl,hx⟩, 1, Nat.coprime_one_left _, rfl⟩
  · rintro z ⟨y, hy, a, ha, rfl⟩
    exact piAPError_le hy hq ha

/-- Maximal Bombieri–Vinogradov for the prime counts `π(y;q,a)` with main term
`Li(y)/φ(q)`. -/
theorem bombieriVinogradov_piAP (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ Real.sqrt x / Real.log x^B →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, maximalPiAPError x q ≤ C*x/Real.log x^A :=
  bombieriVinogradov_of_le_maximal_add_sqrt (by positivity) (fun hx _ hq => maximalPiAPError_le_maximalPsi_add_sqrt hx hq) A

end AnalyticNumberTheory.PrimeDistribution
