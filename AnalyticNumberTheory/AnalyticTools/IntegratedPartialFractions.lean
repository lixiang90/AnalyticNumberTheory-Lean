import AnalyticNumberTheory.AnalyticTools.IntegratedPoleTransform
import AnalyticNumberTheory.AnalyticTools.GammaLaplace

/-! # Laplace inversion of a centered partial fraction expansion -/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.AnalyticTools

/-- Integrated partial fractions with a simple pole p, constant c, and two
families of negative residues, such as the nontrivial and trivial zeta zeros. -/
def integratedPartialFractions (p c : ℂ) (a b : ℕ → ℂ) (u : ℝ) : ℂ :=
  integratedPole p u+c*(u:ℂ)-(∑' n, integratedPole (a n) u)-∑' n, integratedPole (b n) u

/-- Continuity of the integrated partial fractions for inverse-square-summable pole families. -/
theorem continuous_integratedPartialFractions (p c : ℂ) {a b : ℕ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ n, (a n).re ≤ M) (hb : ∀ n, (b n).re ≤ M)
    (hA : Summable fun n => (‖a n‖^2)⁻¹) (hB : Summable fun n => (‖b n‖^2)⁻¹) :
    Continuous (integratedPartialFractions p c a b) := by
  have hp : Continuous (integratedPole p) := by unfold integratedPole; fun_prop
  exact (((hp.add (continuous_const.mul Complex.continuous_ofReal)).sub
    (continuous_tsum_integratedPole hM ha hA)).sub (continuous_tsum_integratedPole hM hb hB))

/-- Damping to the right of every pole recovers the centered partial fractions
divided by s². The constant contributes c/s². -/
theorem laplaceTransform_integratedPartialFractions {p s : ℂ} (c : ℂ) {a b : ℕ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hp : p ≠ 0) (hpM : p.re ≤ M) (ha₀ : ∀ n, a n ≠ 0) (hb₀ : ∀ n, b n ≠ 0)
    (ha : ∀ n, (a n).re ≤ M) (hb : ∀ n, (b n).re ≤ M)
    (hA : Summable fun n => (‖a n‖^2)⁻¹) (hB : Summable fun n => (‖b n‖^2)⁻¹) (hs : M < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s*u)*integratedPartialFractions p c a b u) (Ioi 0) ∧
    laplaceTransform (integratedPartialFractions p c a b) s =
      (c+centeredPole p s-(∑' n,centeredPole (a n) s)-∑' n,centeredPole (b n) s)/s^2 := by
  let E (u : ℝ) := Complex.exp (-s*u)
  have hs₀ := hM.trans_lt hs
  have h₁ : IntegrableOn (fun u : ℝ => E u*integratedPole p u) (Ioi 0) := integrableOn_damped_integratedPole (ω := p) hs₀ (hpM.trans_lt hs)
  have h₂ : IntegrableOn (fun u : ℝ => E u*(u:ℂ)) (Ioi 0) := by
    have h := integrable_gammaLaplaceKernel (s := 2) (by norm_num) hs₀
    change IntegrableOn (fun u : ℝ => E u*(u:ℂ)^((2:ℂ)-1)) (Ioi 0) at h
    simpa only [show (2:ℂ)-1=1 by norm_num,Complex.cpow_one] using h
  have h₃ : IntegrableOn (fun u : ℝ => E u*∑' n,integratedPole (a n) u) (Ioi 0) := integrableOn_damped_tsum_integratedPole hM ha hA hs
  have h₄ : IntegrableOn (fun u : ℝ => E u*∑' n,integratedPole (b n) u) (Ioi 0) := integrableOn_damped_tsum_integratedPole hM hb hB hs
  have hlin : (∫ u : ℝ in Ioi 0, E u*(u:ℂ)) = 1/s^2 := by
    have hΓ : Complex.Gamma 2 = 1 := by
      rw [show (2:ℂ)=1+1 by norm_num,Complex.Gamma_add_one 1 one_ne_zero,Complex.Gamma_one,mul_one]
    simpa [E,show (2:ℂ)-1=1 by norm_num,Complex.cpow_neg,hΓ,one_div] using
      (integral_gammaLaplaceKernel_rightHalfPlane (s := 2) (by norm_num) hs₀)
  have he : (fun u => E u*integratedPartialFractions p c a b u) = (fun u : ℝ =>
      E u*integratedPole p u+c*(E u*(u:ℂ))-E u*(∑' n,integratedPole (a n) u)-
      E u*(∑' n,integratedPole (b n) u)) := by
    funext u
    unfold integratedPartialFractions
    ring
  have h₂c : IntegrableOn (fun u : ℝ => c*(E u*(u:ℂ))) (Ioi 0) := h₂.const_mul c
  have h₁₂ : IntegrableOn (fun u : ℝ => E u*integratedPole p u+c*(E u*(u:ℂ))) (Ioi 0) := h₁.add h₂c
  have h₁₂₃ : IntegrableOn (fun u : ℝ => E u*integratedPole p u+c*(E u*(u:ℂ))-
      E u*(∑' n,integratedPole (a n) u)) (Ioi 0) := h₁₂.sub h₃
  constructor
  · change IntegrableOn (fun u => E u*integratedPartialFractions p c a b u) _
    rw [he]
    exact (h₁₂.sub h₃).sub h₄
  · change (∫ u : ℝ in Ioi 0, E u*integratedPartialFractions p c a b u) = _
    rw [he,integral_sub h₁₂₃ h₄,integral_sub h₁₂ h₃,integral_add h₁ h₂c,
      integral_const_mul,hlin]
    change laplaceTransform (integratedPole p) s + c*(1/s^2) -
      laplaceTransform (fun u => ∑' n,integratedPole (a n) u) s -
      laplaceTransform (fun u => ∑' n,integratedPole (b n) u) s = _
    rw [laplaceTransform_integratedPole hp hs₀ (hpM.trans_lt hs),
      laplaceTransform_tsum_integratedPole hM ha₀ ha hA hs,laplaceTransform_tsum_integratedPole hM hb₀ hb hB hs]
    ring

end AnalyticNumberTheory.AnalyticTools
