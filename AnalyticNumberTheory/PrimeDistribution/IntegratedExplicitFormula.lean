import AnalyticNumberTheory.AnalyticTools.IntegratedPoleTransform
import AnalyticNumberTheory.AnalyticTools.GammaLaplace
import AnalyticNumberTheory.DirichletSeries.LogPerronContours
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.RiemannZeta.CenteredPartialFractions

/-!
# The once-integrated explicit formula for the Chebyshev function

Integrating in the logarithmic variable gives each zero a squared denominator.
The resulting sums over all nontrivial and trivial zeros converge absolutely.
Bromwich inversion of the centered logarithmic derivative identifies their sum
with the first logarithmic mean of the von Mangoldt coefficients.
-/

noncomputable section

open Filter MeasureTheory Set
open Complex (I)
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.EntireFunctions
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem trivialZetaZero_re_le_one (n : ℕ) : (trivialZetaZero n).re ≤ 1 := by
  simp [trivialZetaZero, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem nontrivial_re_le_one (Z : ZetaZeroEnumeration) (n : ℕ) : (Z.zero n).re ≤ 1 :=
  (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le

/-- The integrated contribution of the pole at one, the value at zero, and both zero
families, in the real logarithmic variable. -/
def integratedZetaZeroSum (Z : ZetaZeroEnumeration) (u : ℝ) : ℂ :=
  integratedPole 1 u - Complex.log (2 * (Real.pi : ℂ)) * (u : ℂ) -
    (∑' n, integratedPole (Z.zero n) u) - ∑' n, integratedPole (trivialZetaZero n) u

/-- Continuity of the entire integrated zero expression, including at the origin. -/
theorem continuous_integratedZetaZeroSum (Z : ZetaZeroEnumeration) :
    Continuous (integratedZetaZeroSum Z) := by
  have h₁ : Continuous (integratedPole 1) := by unfold integratedPole; fun_prop
  exact ((h₁.sub (continuous_const.mul Complex.continuous_ofReal)).sub
    (continuous_tsum_integratedPole zero_le_one (nontrivial_re_le_one Z) Z.summable_inv_sq)).sub
    (continuous_tsum_integratedPole zero_le_one trivialZetaZero_re_le_one summable_trivialZetaZero_inv_sq)

set_option maxHeartbeats 1200000 in
private theorem transform_integratedZetaZeroSum (Z : ZetaZeroEnumeration) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s*u) * integratedZetaZeroSum Z u) (Ioi 0) ∧
    laplaceTransform (integratedZetaZeroSum Z) s =
      (-Complex.log (2 * (Real.pi : ℂ)) + centeredPole 1 s -
        (∑' n, centeredPole (Z.zero n) s) - ∑' n, centeredPole (trivialZetaZero n) s)/s^2 := by
  let C := Complex.log (2 * (Real.pi : ℂ))
  let E (u : ℝ) := Complex.exp (-s*u)
  have hs₀ := zero_lt_one.trans hs
  have h₁ : IntegrableOn (fun u => E u * integratedPole 1 u) (Ioi 0) :=
    integrableOn_damped_integratedPole hs₀ (by simpa only [Complex.one_re] using hs)
  have h₂ : IntegrableOn (fun u : ℝ => E u * (u : ℂ)) (Ioi 0) := by
    have hK := integrable_gammaLaplaceKernel (s := 2) (by norm_num) hs₀
    change IntegrableOn (fun u : ℝ => E u * (u : ℂ)^((2 : ℂ)-1)) (Ioi 0) at hK
    simpa only [show (2 : ℂ)-1=1 by norm_num, Complex.cpow_one] using hK
  have h₃ : IntegrableOn (fun u => E u * ∑' n, integratedPole (Z.zero n) u) (Ioi 0) :=
    integrableOn_damped_tsum_integratedPole zero_le_one (nontrivial_re_le_one Z)
    Z.summable_inv_sq hs
  have h₄ : IntegrableOn (fun u => E u * ∑' n, integratedPole (trivialZetaZero n) u) (Ioi 0) :=
    integrableOn_damped_tsum_integratedPole zero_le_one trivialZetaZero_re_le_one
    summable_trivialZetaZero_inv_sq hs
  have hlinear : (∫ u : ℝ in Ioi 0, E u * (u : ℂ)) = 1/s^2 := by
    have hΓ : Complex.Gamma 2 = 1 := by
      rw [show (2 : ℂ) = 1+1 by norm_num, Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, mul_one]
    simpa [E, show (2 : ℂ)-1=1 by norm_num, Complex.cpow_neg, hΓ, one_div] using
      (integral_gammaLaplaceKernel_rightHalfPlane (s := 2) (by norm_num) hs₀)
  have hfun : (fun u => E u * integratedZetaZeroSum Z u) =
      (fun u => E u * integratedPole 1 u - C * (E u * (u : ℂ)) -
        (E u * ∑' n, integratedPole (Z.zero n) u) - E u * ∑' n, integratedPole (trivialZetaZero n) u) := by
    funext u
    unfold integratedZetaZeroSum C
    ring
  have h₂C : IntegrableOn (fun u : ℝ => C * (E u * (u : ℂ))) (Ioi 0) := h₂.const_mul C
  have h₁₂ : IntegrableOn (fun u : ℝ => E u * integratedPole 1 u - C * (E u * (u : ℂ))) (Ioi 0) :=
    h₁.sub h₂C
  have h₁₂₃ : IntegrableOn (fun u : ℝ => E u * integratedPole 1 u - C * (E u * (u : ℂ)) -
      E u * ∑' n, integratedPole (Z.zero n) u) (Ioi 0) := h₁₂.sub h₃
  constructor
  · rw [show (fun u : ℝ => Complex.exp (-s*u) * integratedZetaZeroSum Z u) = _ from hfun]
    exact h₁₂₃.sub h₄
  · change (∫ u in Ioi (0 : ℝ), E u * integratedZetaZeroSum Z u) = _
    rw [hfun, integral_sub h₁₂₃ h₄, integral_sub h₁₂ h₃, integral_sub h₁ h₂C,
      integral_const_mul, hlinear]
    change laplaceTransform (integratedPole 1) s - C * (1/s^2) -
      laplaceTransform (fun u => ∑' n, integratedPole (Z.zero n) u) s -
      laplaceTransform (fun u => ∑' n, integratedPole (trivialZetaZero n) u) s = _
    rw [laplaceTransform_integratedPole one_ne_zero hs₀ (by simpa only [Complex.one_re] using hs),
      laplaceTransform_tsum_integratedPole zero_le_one Z.zero_ne_zero (nontrivial_re_le_one Z)
        Z.summable_inv_sq hs,
      laplaceTransform_tsum_integratedPole zero_le_one trivialZetaZero_ne_zero trivialZetaZero_re_le_one
        summable_trivialZetaZero_inv_sq hs]
    unfold C
    ring

/-- For one multiplicity-respecting enumeration the integrated expression has Laplace
transform equal to the von Mangoldt Dirichlet series divided by the square of the variable. -/
theorem exists_laplaceTransform_integratedZetaZeroSum :
    ∃ Z : ZetaZeroEnumeration, ∀ {s : ℂ}, 1 < s.re →
      laplaceTransform (integratedZetaZeroSum Z) s = LSeries (fun n => (Λ n : ℂ)) s / s^2 := by
  obtain ⟨Z, H⟩ := exists_centered_logDeriv_riemannZeta
  refine ⟨Z, fun {s} hs => ?_⟩
  have hs₁ : s ≠ 1 := fun he => by simp [he] at hs
  rw [(transform_integratedZetaZeroSum Z hs).2, LSeries_vonMangoldt_eq hs,
    H hs₁ (_root_.riemannZeta_ne_zero_of_one_lt_re hs)]

/-- The integrated von Mangoldt sum is exactly the logarithmic integral of the Chebyshev
function, also when the upper endpoint is a prime power. -/
theorem logWeightedSum_vonMangoldt_eq_integral_psi {x : ℝ} (hx : 1 ≤ x) :
    logWeightedSum (fun n => (Λ n : ℂ)) x = ∫ t : ℝ in 1..x, (Chebyshev.psi t : ℂ)/(t : ℂ) := by
  rw [logWeightedSum_eq_integral hx]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [psi_eq_sum_Icc, Complex.ofReal_sum]
  rfl

/-- Bromwich inversion gives the integrated zero expression at every cutoff at least one. -/
theorem exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum :
    ∃ Z : ZetaZeroEnumeration, ∀ {x : ℝ}, 1 ≤ x →
      logWeightedSum (fun n => (Λ n : ℂ)) x = integratedZetaZeroSum Z (Real.log x) := by
  obtain ⟨Z, H⟩ := exists_laplaceTransform_integratedZetaZeroSum
  refine ⟨Z, fun {x} hx => ?_⟩
  rcases hx.eq_or_lt with rfl | hx
  · simp [integratedZetaZeroSum, integratedPole, logWeightedSum]
  let a (n : ℕ) : ℂ := Λ n
  have h2 : LSeriesSummable a (2 : ℂ) := LSeriesSummable_vonMangoldt_iff.mpr (by norm_num)
  have hline (t : ℝ) : 1 < ((2 : ℂ)+(t : ℂ)*I).re := by simp
  have hF : Integrable fun t : ℝ => laplaceTransform (integratedZetaZeroSum Z) ((2 : ℂ)+t*I) := by
    apply (integrable_logPerronTrace_LSeries (σ := 2) (by norm_num) h2 1).congr
    apply ae_of_all _ fun t => ?_
    dsimp only
    rw [logPerronTrace_eq_cpow _ _ zero_lt_one, H (hline t)]
    simp [a]
  have hi := laplace_inversion (σ := 2) (Real.log_pos hx) (continuous_integratedZetaZeroSum Z).continuousAt
    (transform_integratedZetaZeroSum Z (s := 2) (by norm_num)).1 hF
  rw [← hi, logWeightedSum_eq_perron (zero_lt_one.trans hx) (by norm_num : (0 : ℝ)<2) h2, bromwichIntegral]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  dsimp only [Complex.ofReal_ofNat]
  rw [H (hline t), Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'),
    ← Complex.ofReal_log (zero_lt_one.trans hx).le, mul_comm ((2 : ℂ)+(t : ℂ)*I)]
  dsimp only [a]
  ring

/-- The integrated pole at a positive physical cutoff, written as a complex power. -/
theorem integratedPole_log (ω : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    integratedPole ω (Real.log x) = ((x : ℂ)^ω-1)/ω^2 := by
  have h := zero_lt_one.trans_le hx
  rw [integratedPole, max_eq_left (Real.log_nonneg hx), Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'),
    ← Complex.ofReal_log h.le, mul_comm ω]

/-- The full once-integrated explicit formula. Every nontrivial zero is counted with its
analytic multiplicity, and the trivial-zero sum runs through all negative even integers. -/
theorem exists_integrated_explicit_formula_psi :
    ∃ Z : ZetaZeroEnumeration, ∀ {x : ℝ}, 1 ≤ x →
      (∫ t : ℝ in 1..x, (Chebyshev.psi t : ℂ)/(t : ℂ)) =
        (x : ℂ)-1 - Complex.log (2*(Real.pi : ℂ))*(Real.log x : ℂ) -
        (∑' n, ((x : ℂ)^(Z.zero n)-1)/(Z.zero n)^2) -
        ∑' n, ((x : ℂ)^(trivialZetaZero n)-1)/(trivialZetaZero n)^2 := by
  obtain ⟨Z, H⟩ := exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum
  refine ⟨Z, fun {x} hx => ?_⟩
  rw [← logWeightedSum_vonMangoldt_eq_integral_psi hx, H hx, integratedZetaZeroSum]
  simp_rw [integratedPole_log _ hx]
  simp

end AnalyticNumberTheory.PrimeDistribution
