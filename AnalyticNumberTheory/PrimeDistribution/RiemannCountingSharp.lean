import AnalyticNumberTheory.AnalyticTools.Summation.WeightedDerivativeLimit
import AnalyticNumberTheory.PrimeDistribution.LocallyBoundedZeroSums
import AnalyticNumberTheory.PrimeDistribution.MidpointCountingAbel

/-!
# Riemann's sharp explicit formula for differences of prime-power counts

Symmetric truncation in the ordinate gives a convergent logarithmic-integral formula on
any interval above one. Both endpoint atoms carry half weight. The real logarithmic
integral for the trivial zeros has density 1/(t(t²−1)log t).
-/

noncomputable section

open Filter Finset MeasureTheory
open scoped Topology Classical
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Density obtained by differentiating the elementary trivial-zero term in the
Chebyshev formula on the open half-line above one. -/
def trivialZeroDensity (x : ℝ) : ℝ := (x*(x^2-1))⁻¹

/-- Derivative of the logarithmic sum of the trivial zeros. -/
theorem hasDerivAt_trivialZeroLog {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => Real.log (1-(t^2)⁻¹)/2) (trivialZeroDensity x) x := by
  have h₀ := zero_lt_one.trans hx
  have h₂ : 1 < x^2 := by nlinarith
  have h₁ : 0 < 1-(x^2)⁻¹ := sub_pos.mpr ((inv_lt_one₀ (sq_pos_of_pos h₀)).mpr h₂)
  have h := ((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 h₀.ne'))).log h₁.ne'
  apply (h.div_const 2).congr_deriv
  simp only [Pi.pow_apply,Pi.sub_apply,Pi.inv_apply,id_eq,trivialZeroDensity]
  field_simp [h₀.ne', (sub_pos.mpr h₂).ne', h₁.ne']
  ring

/-- Sum of the logarithmic integrals of the critical-strip zeros up to height T. -/
def sharpZeroLogIntegral (a b T : ℝ) : ℂ :=
  ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*zeroLogIntegral z a b

/-- The elementary integral of the contribution of all negative even zeros on a positive interval. -/
def trivialZeroLogIntegral (a b : ℝ) : ℝ :=
  ∫ t in a..b, (t*(t^2-1)*Real.log t)⁻¹

private theorem hasDerivAt_zeroSum {t : ℝ} (ht : 0 < t) (T : ℝ) :
    HasDerivAt (fun u => sharpZetaZeroSum u T)
      (∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*(t : ℂ)^(z-1)) t := by
  unfold sharpZetaZeroSum
  apply HasDerivAt.fun_sum
  intro z hz
  have hp := (mem_nontrivialZerosUpTo.mp hz).2.1
  have h₀ : z ≠ 0 := fun he => by simp [he] at hp
  apply HasDerivAt.const_mul
  exact ((hasDerivAt_ofReal_cpow_const ht.ne' h₀).div_const z).congr_deriv (by field_simp [h₀])

/-- The sharp interval explicit formula for the midpoint Riemann count on 1 < a ≤ b.
Every height is allowed and zeros are counted with their analytic multiplicities. -/
theorem tendsto_riemannPrimeCounting_interval_explicit_formula {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Tendsto (fun T => zeroLogIntegral 1 a b - sharpZeroLogIntegral a b T - (trivialZeroLogIntegral a b : ℂ))
      atTop (𝓝 ((riemannPrimeCounting (1/2) b - riemannPrimeCounting (1/2) a : ℝ) : ℂ)) := by
  let L (t : ℝ) : ℝ := Real.log (1-(t^2)⁻¹)/2
  let H (t : ℝ) : ℂ := (t : ℂ) - Complex.log (2*(Real.pi : ℂ)) - (L t : ℂ)
  let F (T t : ℝ) := H t - sharpZetaZeroSum t T
  let Z (T t : ℝ) := ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*(t : ℂ)^(z-1)
  let g (T t : ℝ) : ℂ := 1 - Z T t - (trivialZeroDensity t : ℂ)
  let W (t : ℝ) : ℂ := ↑((Real.log t)⁻¹)
  let D (t : ℝ) : ℂ := ↑(-t⁻¹/(Real.log t)^2)
  have ht₁ {t : ℝ} (ht : t ∈ Set.Icc a b) := ha.trans_le ht.1
  have ht₀ {t : ℝ} (ht : t ∈ Set.Icc a b) := zero_lt_one.trans (ht₁ ht)
  have hdH (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt H (1-(trivialZeroDensity t : ℂ)) t :=
    ((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const _).sub (hasDerivAt_trivialZeroLog (ht₁ ht)).ofReal_comp
  have hF (T t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt (F T) (g T t) t := by
    apply ((hdH t ht).sub (hasDerivAt_zeroSum (ht₀ ht) T)).congr_deriv
    dsimp [g,Z]
    ring
  have hZ (T : ℝ) : ContinuousOn (Z T) (Set.Icc a b) := by
    apply continuousOn_finsetSum
    intro z _
    apply continuousOn_const.mul
    exact fun t ht => (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ht₀ ht).ne')).continuousWithinAt
  have hc : ContinuousOn (fun t => (trivialZeroDensity t : ℂ)) (Set.Icc a b) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    intro t ht
    have h₂ : 0 < t^2-1 := by nlinarith [ht₁ ht]
    exact (continuousAt_id.mul ((continuousAt_id.pow 2).sub continuousAt_const)
      |>.inv₀ (mul_ne_zero (ht₀ ht).ne' h₂.ne')).continuousWithinAt
  have hg (T : ℝ) : ContinuousOn (g T) (Set.Icc a b) := (continuousOn_const.sub (hZ T)).sub hc
  have hw (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt W (D t) t :=
    (Real.hasDerivAt_inv_log (ht₀ ht).ne' (ht₁ ht).ne' (by linarith [ht₀ ht])).ofReal_comp
  have hD : ContinuousOn D (Set.Icc a b) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    intro t ht
    have h := (ht₀ ht).ne'
    exact (((continuousAt_id.inv₀ h).neg).div ((Real.continuousAt_log h).pow 2)
      (pow_ne_zero 2 (Real.log_pos (ht₁ ht)).ne')).continuousWithinAt
  have hW : ContinuousOn W (Set.Icc a b) := fun t ht => (hw t ht).continuousAt.continuousWithinAt
  have hlim (t : ℝ) (ht : t ∈ Set.Icc a b) : Tendsto (F · t) atTop (𝓝 (midpointPsi t : ℂ)) := by
    apply (tendsto_explicit_formula_midpointPsi (ht₁ ht)).congr
    intro T
    simp only [F,H,L,Complex.ofReal_div,Complex.ofReal_ofNat]
    ring
  obtain ⟨B,hB⟩ := eventually_norm_sharpZetaZeroSum_le_on_Icc ha hab
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn H (Set.Icc a b) from fun t ht => (hdH t ht).continuousAt.continuousWithinAt)
  have hbound : ∃ M : ℝ, ∀ᶠ T : ℝ in atTop, ∀ t ∈ Set.Icc a b, ‖F T t‖ ≤ M :=
    ⟨C+B,hB.mono fun T h t ht => (norm_sub_le ..).trans (add_le_add (hC t ht) (h t ht))⟩
  have h := tendsto_weighted_derivatives_of_bounded_primitives hab hF hg hw hD hlim hbound
  have hfinite (T : ℝ) : (∫ t in a..b, g T t * W t) =
      zeroLogIntegral 1 a b - sharpZeroLogIntegral a b T - (trivialZeroLogIntegral a b : ℂ) := by
    rw [show (fun t => g T t * W t) = (fun t => (1-Z T t)*W t - (trivialZeroDensity t : ℂ)*W t) from
      funext fun t => sub_mul ..]
    rw [intervalIntegral.integral_sub (μ := volume) (f := fun t => (1-Z T t)*W t)
      (g := fun t => (trivialZeroDensity t : ℂ)*W t)
      (((continuousOn_const.sub (hZ T)).mul hW).intervalIntegrable_of_Icc hab)
      ((hc.mul hW).intervalIntegrable_of_Icc hab)]
    change ((∫ t in a..b, (1-Z T t)*W t) - _) = _
    rw [show (∫ t in a..b, (1-Z T t)*W t) = _ from integral_one_sub_zeroPowers_invLog T ha hab]
    congr 1
    rw [trivialZeroLogIntegral, ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    simp [W,trivialZeroDensity,mul_inv_rev,mul_comm]
  have hintegral : (∫ t in a..b, (midpointPsi t : ℂ)*D t) =
      ((∫ t in a..b, Chebyshev.psi t*(-t⁻¹/(Real.log t)^2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [midpointPsi_ae_eq_psi] with t he
    intro _
    simp only [D,he,Complex.ofReal_mul]
  rw [hintegral] at h
  have hend := congrArg (fun t : ℝ => (t : ℂ)) (riemannPrimeCounting_midpoint_abel ha hab)
  push_cast only [Complex.ofReal_sub,Complex.ofReal_mul] at hend
  rw [Complex.ofReal_sub, hend]
  exact h.congr hfinite

end AnalyticNumberTheory.PrimeDistribution
