import AnalyticNumberTheory.AnalyticTools.FourierJordanInversion
import AnalyticNumberTheory.AnalyticTools.MellinTruncation
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # The Jordan midpoint for a truncated inverse Mellin integral -/

noncomputable section
open MeasureTheory Set Filter Function Complex
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private lemma variation_exp_weight (k A B : ℝ) :
    BoundedVariationOn (fun u : ℝ => Real.exp (k*u)) (Icc A B) := by
  have hd : ContDiffOn ℝ 1 (fun u : ℝ => Real.exp (k*u)) (Icc A B) := by fun_prop
  obtain ⟨C,hC⟩ := hd.exists_lipschitzOnWith (by norm_num) (convex_Icc A B) isCompact_Icc
  have hi : BoundedVariationOn id (Icc A B) := by
    rw [BoundedVariationOn, eVariationOn_id_Icc]
    exact ENNReal.ofReal_ne_top
  exact hC.comp_boundedVariationOn (fun _ hu => hu) hi

/-- At a positive point of locally bounded variation, the symmetric inverse
Mellin integral recovers the average of the two one-sided limits on every
line of absolute Mellin convergence. -/
theorem mellin_jordan_inversion {f : ℝ → ℝ} {a x b σ : ℝ} (ha : 0 < a) (hax : a < x) (hxb : x < b)
    (hv : BoundedVariationOn f (Icc a b)) (hf : MellinConvergent (fun t : ℝ => (f t : ℂ)) (σ : ℂ)) :
    Tendsto (truncatedMellinInverse (mellin (fun t : ℝ => (f t : ℂ))) σ x) atTop
      (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  let P (u : ℝ) := Real.exp (-u)
  let W (u : ℝ) := Real.exp (-σ*u)
  let z := -Real.log x
  let A := -Real.log b
  let B := -Real.log a
  let g (u : ℝ) := W u * f (P u)
  have hx : 0 < x := ha.trans hax
  have hb : 0 < b := hx.trans hxb
  have hPa : P B = a := by simp [P,B,Real.exp_log ha]
  have hPb : P A = b := by simp [P,A,Real.exp_log hb]
  have hPx : P z = x := by simp [P,z,Real.exp_log hx]
  have hanti : StrictAnti P := fun u v huv => Real.exp_lt_exp.mpr (neg_lt_neg huv)
  have hAz : A < z := neg_lt_neg (Real.log_lt_log hx hxb)
  have hzB : z < B := neg_lt_neg (Real.log_lt_log ha hax)
  have hcomp : BoundedVariationOn (fun u : ℝ => f (P u)) (Icc A B) := by
    apply ne_top_of_le_ne_top hv
    apply eVariationOn.comp_le_of_antitoneOn f P (hanti.antitone.antitoneOn _)
    intro u hu
    rw [← hPa, ← hPb]
    exact ⟨hanti.antitone hu.2, hanti.antitone hu.1⟩
  have hvar : BoundedVariationOn g (Icc A B) := (variation_exp_weight (-σ) A B).mul hcomp
  have hcast : mellinLogPullback σ (fun t : ℝ => (f t : ℂ)) = fun u : ℝ => (g u : ℂ) := by
    funext u
    simp [g,P,W,mellinLogPullback,Complex.real_smul]
  have hi := integrable_mellinLogPullback hf
  rw [hcast] at hi
  have hg : Integrable g := by simpa using hi.re
  have hc : Continuous P := by dsimp [P]; fun_prop
  have hw : Continuous W := by dsimp [W]; fun_prop
  have hrevL : Tendsto P (𝓝[<] z) (𝓝[>] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hPx ▸ (hc.tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u (hu : u < z)
    change x < P u
    rw [← hPx]
    exact hanti hu
  have hrevR : Tendsto P (𝓝[>] z) (𝓝[<] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hPx ▸ (hc.tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u (hu : z < u)
    change P u < x
    rw [← hPx]
    exact hanti hu
  have hmem := Icc_mem_nhds hax hxb
  obtain ⟨l, hl⟩ := hv.exists_tendsto_left x
  obtain ⟨r, hr⟩ := hv.exists_tendsto_right x
  rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hmem)] at hl hr
  have hL : leftLim g z = W z * rightLim f x := by
    rw [rightLim_eq_of_tendsto hr]
    exact leftLim_eq_of_tendsto (((hw.tendsto z).mono_left nhdsWithin_le_nhds).mul (hr.comp hrevL))
  have hR : rightLim g z = W z * leftLim f x := by
    rw [leftLim_eq_of_tendsto hl]
    exact rightLim_eq_of_tendsto (((hw.tendsto z).mono_left nhdsWithin_le_nhds).mul (hl.comp hrevR))
  have H := fourier_jordan_inversion hg hAz hzB hvar
  rw [hL, hR] at H
  have hT : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have Hlim := (H.comp hT).const_mul (Real.exp (-σ*Real.log x) : ℂ)
  have hwz : (Real.exp (-σ*Real.log x) : ℂ) * (W z : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    dsimp only [W,z]
    rw [← Real.exp_add, show -σ*Real.log x + -σ*(-Real.log x) = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  have hmid : (Real.exp (-σ*Real.log x) : ℂ) *
      ((((W z * rightLim f x : ℝ) : ℂ) + ((W z * leftLim f x : ℝ) : ℂ)) / 2) =
      ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2) := by
    simp only [Complex.ofReal_mul]
    rw [← mul_add, ← mul_div_assoc, ← mul_assoc, hwz, one_mul, add_comm]
  rw [hmid] at Hlim
  apply Hlim.congr
  intro T
  rw [truncatedMellinInverse_eq_fourier _ _ hx, hcast]
  rfl

end AnalyticNumberTheory.AnalyticTools
