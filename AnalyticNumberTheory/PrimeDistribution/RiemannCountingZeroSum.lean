import AnalyticNumberTheory.AnalyticTools.Summation.WeightedDiscrepancy
import AnalyticNumberTheory.PrimeDistribution.RiemannPrimeCounting
import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula

/-!
# A truncated zero formula for Riemann's prime-power count on intervals

For 2 ≤ T ≤ a ≤ b the pole and the nontrivial zeros up to height T contribute logarithmic
integrals over the positive interval [a,b]. These differences do not require a choice of an
exponential-integral branch. On b ≤ 2a the uniform error is O(b log(b)/T + 1).
-/

noncomputable section

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.PrimeDistribution

/-- The increment of the inclusive Riemann count sums the prime-power masses over `(a,b]`. -/
theorem riemannPrimeCounting_sub_eq_sum_Ioc {a b : ℝ} (hab : a ≤ b) :
    riemannPrimeCounting 1 b - riemannPrimeCounting 1 a =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n / Real.log n := by
  rw [riemannPrimeCounting_one, riemannPrimeCounting_one]
  exact sub_eq_iff_eq_add.mpr (by
    rw [add_comm]
    exact (sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono hab)).symm)

/-- Finite logarithmic integral of a complex power. In particular `ρ = 1` gives the
ordinary logarithmic integral between the same endpoints. -/
def zeroLogIntegral (ρ : ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, (t : ℂ) ^ (ρ - 1) * (↑((Real.log t)⁻¹) : ℂ)

/-- At the pole exponent one the kernel is the real logarithmic integral. -/
theorem zeroLogIntegral_one (a b : ℝ) :
    zeroLogIntegral 1 a b = ((∫ t in a..b, (Real.log t)⁻¹ : ℝ) : ℂ) := by
  simp only [zeroLogIntegral, sub_self, Complex.cpow_zero, one_mul]
  exact intervalIntegral.integral_ofReal

private theorem continuousOn_powerKernel (ρ : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (ρ-1)) (Set.Icc a b) :=
  fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ha.trans_le ht.1).ne')).continuousWithinAt

private theorem integral_truncated_zero_sum (T : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, (1 - ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) *
      (t : ℂ) ^ (ρ-1)) * (↑((Real.log t)⁻¹) : ℂ)) =
      zeroLogIntegral 1 a b - ∑ ρ ∈ nontrivialZerosUpTo T,
        (zeroMultiplicity ρ : ℂ) * zeroLogIntegral ρ a b := by
  let W (t : ℝ) : ℂ := ↑((Real.log t)⁻¹)
  let K (ρ : ℂ) (t : ℝ) := (t : ℂ) ^ (ρ-1) * W t
  have hW : ContinuousOn W (Set.Icc a b) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    exact fun t ht => ((Real.continuousAt_log (zero_lt_one.trans (ha.trans_le ht.1)).ne').inv₀
      (Real.log_pos (ha.trans_le ht.1)).ne').continuousWithinAt
  have hK (ρ : ℂ) : ContinuousOn (K ρ) (Set.Icc a b) :=
    (continuousOn_powerKernel ρ (zero_lt_one.trans ha)).mul hW
  let m (ρ : ℂ) (t : ℝ) := (zeroMultiplicity ρ : ℂ) * K ρ t
  have hm (ρ : ℂ) : ContinuousOn (m ρ) (Set.Icc a b) := continuousOn_const.mul (hK ρ)
  calc
    _ = ∫ t in a..b, W t - ∑ ρ ∈ nontrivialZerosUpTo T, m ρ t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp [W, K, m, sub_mul, sum_mul, mul_assoc]
    _ = _ := by
      rw [intervalIntegral.integral_sub (hW.intervalIntegrable_of_Icc hab)
        ((continuousOn_finsetSum _ fun ρ _ => hm ρ).intervalIntegrable_of_Icc hab),
        intervalIntegral.integral_finsetSum (fun ρ _ => (hm ρ).intervalIntegrable_of_Icc hab)]
      simp [W, m, K, zeroLogIntegral, intervalIntegral.integral_const_mul]

/-- A finite, multiplicity-weighted zero formula for `J(b)-J(a)` over `2 ≤ T ≤ a ≤ b`.
The pole contributes the logarithmic integral and each zero its logarithmic power integral. -/
theorem riemannPrimeCounting_interval_zero_formula :
    ∃ C > 0, ∀ {a b T : ℝ}, 2 ≤ T → T ≤ a → a ≤ b →
      ‖((riemannPrimeCounting 1 b - riemannPrimeCounting 1 a : ℝ) : ℂ) -
        (zeroLogIntegral 1 a b - ∑ ρ ∈ nontrivialZerosUpTo T,
          (zeroMultiplicity ρ : ℂ) * zeroLogIntegral ρ a b)‖ ≤
        C * (b * (Real.log b)^2 / T + Real.log b) / Real.log a := by
  obtain ⟨C, hC, hform⟩ := explicit_formula_psi
  refine ⟨2*C, by positivity, ?_⟩
  intro a b T hT hTa hab
  have ha : 1 < a := by linarith
  have ha₀ := zero_lt_one.trans ha
  have ht₀ (t : ℝ) (ht : t ∈ Set.Icc a b) := ha₀.trans_le ht.1
  have hlog (t : ℝ) (ht : t ∈ Set.Icc a b) := Real.log_pos (ha.trans_le ht.1)
  let S := nontrivialZerosUpTo T
  let m (ρ : ℂ) : ℂ := zeroMultiplicity ρ
  let G (t : ℝ) := (t : ℂ) + (-deriv riemannZeta 0 / riemannZeta 0) -
    ∑ ρ ∈ S, m ρ * ((t : ℂ)^ρ / ρ)
  let g (t : ℝ) := 1 - ∑ ρ ∈ S, m ρ * (t : ℂ)^(ρ-1)
  have hdG (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt G (g t) t := by
    have hi : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    apply (hi.add_const _).sub
    apply HasDerivAt.fun_sum
    intro ρ hρ
    have hpos := (mem_nontrivialZerosUpTo.mp hρ).2.1
    have hr : ρ ≠ 0 := fun he => by simp [he] at hpos
    apply HasDerivAt.const_mul
    exact (((hasDerivAt_ofReal_cpow_const (ht₀ t ht).ne' hr).div_const ρ)).congr_deriv
      (by field_simp [hr])
  have hcg : ContinuousOn g (Set.Icc a b) := continuousOn_const.sub
    (continuousOn_finsetSum _ fun ρ _ => continuousOn_const.mul (continuousOn_powerKernel ρ ha₀))
  let M := C * (b * (Real.log b)^2 / T + Real.log b)
  have hM (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖(∑ n ∈ Icc 1 ⌊t⌋₊, (Λ n : ℂ)) - G t‖ ≤ M := by
    rw [← Complex.ofReal_sum, ← psi_eq_sum_Icc]
    apply (hform t T (by linarith [ht.1]) hT (hTa.trans ht.1)).trans
    have hl := Real.log_le_log (ht₀ t ht) ht.2
    exact mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right
      (mul_le_mul ht.2 (pow_le_pow_left₀ (hlog t ht).le hl 2) (sq_nonneg _)
        (ha₀.trans_le hab).le) (zero_lt_two.trans_le hT).le) hl) hC.le
  let w (t : ℝ) := (Real.log t)⁻¹
  let D (t : ℝ) := -t⁻¹ / (Real.log t)^2
  have hw (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt w (D t) t :=
    Real.hasDerivAt_inv_log (ht₀ t ht).ne' (ha.trans_le ht.1).ne' (by linarith [ht₀ t ht])
  have hD : ContinuousOn D (Set.Icc a b) := by
    intro t ht
    have ht' := (ht₀ t ht).ne'
    have hl' := (hlog t ht).ne'
    exact (((continuousAt_id.inv₀ ht').neg).div ((Real.continuousAt_log ht').pow 2)
      (pow_ne_zero 2 hl')).continuousWithinAt
  have H := norm_weighted_sum_sub_integral_of_partial_sums ha₀.le hab
    (fun n => (Λ n : ℂ)) G g w D hdG hcg hw hD
    (fun t ht => inv_nonneg.mpr (hlog t ht).le)
    (fun t ht => div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr (ht₀ t ht).le))
      (sq_nonneg _)) hM
  have hsum : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Λ n : ℂ) * (w n : ℂ)) =
      ((riemannPrimeCounting 1 b - riemannPrimeCounting 1 a : ℝ) : ℂ) := by
    rw [riemannPrimeCounting_sub_eq_sum_Ioc hab, Complex.ofReal_sum]
    simp [w, div_eq_mul_inv]
  rw [hsum] at H
  change ‖_ - (∫ t in a..b, (1 - ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℂ) *
    (t : ℂ) ^ (ρ-1)) * (↑((Real.log t)⁻¹) : ℂ))‖ ≤ _ at H
  rw [integral_truncated_zero_sum T ha hab] at H
  exact H.trans_eq (by dsimp [M, w]; ring)

/-- On any interval with `2 ≤ T ≤ a ≤ b ≤ 2a`, the error in the truncated logarithmic
zero formula is `O(b log(b)/T + 1)` with one absolute constant for all three parameters. -/
theorem riemannPrimeCounting_dyadic_zero_formula :
    ∃ C > 0, ∀ {a b T : ℝ}, 2 ≤ T → T ≤ a → a ≤ b → b ≤ 2*a →
      ‖((riemannPrimeCounting 1 b - riemannPrimeCounting 1 a : ℝ) : ℂ) -
        (zeroLogIntegral 1 a b - ∑ ρ ∈ nontrivialZerosUpTo T,
          (zeroMultiplicity ρ : ℂ) * zeroLogIntegral ρ a b)‖ ≤
        C * (b * Real.log b / T + 1) := by
  obtain ⟨C, hC, H⟩ := riemannPrimeCounting_interval_zero_formula
  refine ⟨2*C, by positivity, ?_⟩
  intro a b T hT hTa hab hb
  have ha : 2 ≤ a := hT.trans hTa
  have hpa : 0 < a := zero_lt_two.trans_le ha
  have hla : 0 < Real.log a := Real.log_pos (one_lt_two.trans_le ha)
  have hlb : 0 < Real.log b := Real.log_pos (one_lt_two.trans_le (ha.trans hab))
  have hl : Real.log b ≤ 2 * Real.log a := by
    calc
      _ ≤ Real.log (2*a) := Real.log_le_log (hpa.trans_le hab) hb
      _ = Real.log 2 + Real.log a := Real.log_mul (by norm_num) hpa.ne'
      _ ≤ _ := by linarith [Real.log_le_log zero_lt_two ha]
  apply (H hT hTa hab).trans
  calc
    _ = (C * (b * Real.log b / T + 1)) * (Real.log b / Real.log a) := by ring
    _ ≤ (C * (b * Real.log b / T + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_left ((div_le_iff₀ hla).mpr hl)
      have := hpa.trans_le hab
      have := zero_lt_two.trans_le hT
      positivity
    _ = _ := by ring

end AnalyticNumberTheory.PrimeDistribution
