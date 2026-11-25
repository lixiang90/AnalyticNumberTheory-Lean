import AnalyticNumberTheory.PrimeDistribution.HoheiselZeroSums
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Vinogradov–Korobov zero-free width

A pointwise zero-free bound at large ordinates yields a uniform gap for
the complete box of height `T`, including its bounded-height part.
-/
noncomputable section
open Finset Complex Real Filter
namespace AnalyticNumberTheory.PrimeDistribution

/-- Denominator of the classical Vinogradov–Korobov width at height `T`. -/
def vinogradovKorobovDenom (T : ℝ) : ℝ :=
  (Real.log T)^(2/3:ℝ)*(Real.log (Real.log T))^(1/3:ℝ)

/-- Vinogradov–Korobov's zero-free region formulated at individual zeros of zeta. -/
def VinogradovKorobovZeroFreeHypothesis : Prop :=
  ∃ c>(0:ℝ), ∃ T₀ : ℝ, ∀ z : ℂ, riemannZeta z=0 → 0<z.re → z.re<1 → T₀≤|z.im| →
    c≤(1-z.re)*vinogradovKorobovDenom |z.im|

theorem tendsto_vinogradovKorobovDenom :
    Tendsto vinogradovKorobovDenom atTop atTop := by
  exact ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp Real.tendsto_log_atTop).atTop_mul_atTop₀
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))

/-- The gap at all zeros up to a given height, with the same width at the upper endpoint. -/
theorem vinogradovKorobov_box_gap (h : VinogradovKorobovZeroFreeHypothesis) :
    ∃ c>(0:ℝ), ∀ᶠ T : ℝ in atTop, ∀ z∈nontrivialZerosUpTo T,
      c≤(1-z.re)*vinogradovKorobovDenom T := by
  obtain ⟨c,hc,T₀,hz⟩ := h
  obtain ⟨d,hd,hdz⟩ := zeta_scaled_gap_pos
  let U := max (Real.exp 1) (max 2 T₀)
  have hU : Real.exp 1≤U := le_max_left ..
  have hU₀ : T₀≤U := (le_max_right ..).trans (le_max_right ..)
  have hU₂ : 2≤U := (le_max_left ..).trans (le_max_right ..)
  have hln : 0<Real.log (U+2) := Real.log_pos (by linarith)
  have hm : MonotoneOn vinogradovKorobovDenom (Set.Ici U) := by
    intro a ha b _ hab
    have hl : 1≤Real.log a := by rw [←Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) (hU.trans ha)
    have ha₀ : 0<a := (Real.exp_pos _).trans_le (hU.trans ha)
    have hl' := Real.log_le_log ha₀ hab
    dsimp [vinogradovKorobovDenom]
    exact mul_le_mul (Real.rpow_le_rpow (by linarith) hl' (by norm_num))
      (Real.rpow_le_rpow (Real.log_nonneg hl) (Real.log_le_log (by linarith) hl') (by norm_num))
      (Real.rpow_nonneg (Real.log_nonneg hl) _) (Real.rpow_nonneg (by linarith) _)
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop U,tendsto_vinogradovKorobovDenom.eventually_ge_atTop (c*Real.log (U+2)/d)] with T hT hsize z hmem
  obtain ⟨hz₀,hz₁,hz₂,hz₃⟩ := mem_nontrivialZerosUpTo.mp hmem
  by_cases hu : U≤|z.im|
  · exact (hz z hz₀ hz₁ hz₂ (hU₀.trans hu)).trans (mul_le_mul_of_nonneg_left (hm hu hT hz₃) (by linarith))
  · have hzu : z∈nontrivialZerosUpTo U := mem_nontrivialZerosUpTo.mpr ⟨hz₀,hz₁,hz₂,(le_of_not_ge hu)⟩
    have hg := hdz z (T:=U) hzu
    have hD : 0≤vinogradovKorobovDenom T := (div_nonneg (mul_nonneg hc.le hln.le) hd.le).trans hsize
    apply le_of_mul_le_mul_right (a:=Real.log (U+2)) _ hln
    nlinarith only [(div_le_iff₀ hd).mp hsize,mul_le_mul_of_nonneg_right hg hD]

end AnalyticNumberTheory.PrimeDistribution
