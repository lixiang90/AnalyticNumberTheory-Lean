import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LocalPoleIntegrals
import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralBounds
import AnalyticNumberTheory.PrimeDistribution.SelbergLocalExpansion
import AnalyticNumberTheory.RiemannZeta.HorizontalLogMeanIdentity

/-! # Horizontal integrals of the zeta logarithmic derivative under RH -/

noncomputable section

open Complex Set MeasureTheory
open scoped Interval
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

/-- At every nonzero ordinate avoiding zeros, the integral of Im(ζ′/ζ) gains
one power of the logarithmic cutoff u, and the first horizontal moment of Re(ζ′/ζ)
gains two, provided exp(4u) ≤ log t and u ≥ 2. -/
theorem selberg_horizontal_logDeriv_integrals (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ {t u : ℝ}, 4 ≤ t → 2 ≤ u → Real.exp (4*u) ≤ Real.log t → ¬ IsZeroOrdinate t →
      (|∫ x in (1/2 : ℝ)..2, (deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) /
        riemannZeta ((x : ℂ)+(t : ℂ)*I)).im| ≤ C*(Real.log t/u)) ∧
      |∫ x in (1/2 : ℝ)..2, (x-1/2)*(deriv riemannZeta ((x : ℂ)+(t : ℂ)*I) /
        riemannZeta ((x : ℂ)+(t : ℂ)*I)).re| ≤ C*(Real.log t/u^2) := by
  obtain ⟨B, hB, HB⟩ := selberg_poissonMass_and_logDeriv_le hRH
  obtain ⟨K, hK, HK⟩ := norm_logDeriv_zeta_sub_window_le_of_cutoff hRH
  obtain ⟨Z, _⟩ := exists_centered_logDeriv_riemannZeta
  let N := K + 8*(Real.pi+1)*B
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨4*N + 5*B, by positivity, ?_⟩
  intro t u ht hu hscale hno
  let c : ℝ := 1/2
  let δ := 2/u
  let b := c+δ
  let L := Real.log t
  let X := Real.exp (u+u)
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let f (x : ℝ) := deriv riemannZeta (p x) / riemannZeta (p x)
  have hu₀ := two_pos.trans_le hu
  have hu₁ := one_le_two.trans hu
  have ht₀ : 0 < t := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hδ : 0 < δ := div_pos two_pos hu₀
  have hδ₁ : δ ≤ 1 := (div_le_one hu₀).mpr hu
  have hcb : c ≤ b := le_add_of_nonneg_right hδ.le
  have hb : b ≤ 2 := by dsimp only [b, c]; linarith
  have hdiff : b-c = δ := by dsimp only [b]; ring
  have hdu : δ*u = 2 := div_mul_cancel₀ _ hu₀.ne'
  have hX₀ : 0 ≤ X := (Real.exp_pos _).le
  have huE : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hX₂ : X*u^2 ≤ L := by
    refine le_trans ?_ hscale
    calc
      _ ≤ X*(Real.exp u)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu₀.le huE 2) hX₀
      _ = Real.exp (4*u) := by
        dsimp only [X]
        rw [show 4*u = (u+u)+(u+u) by ring]
        simp only [Real.exp_add]
        ring
  have hX₁ : X*u ≤ L := le_trans (mul_le_mul_of_nonneg_left
    (by nlinarith only [mul_nonneg hu₀.le (sub_nonneg.mpr hu₁)] : u ≤ u^2) hX₀) hX₂
  have hX : X ≤ L := (le_mul_of_one_le_right hX₀ hu₁).trans hX₁
  have hscale₁ : X ≤ L/u := (le_div_iff₀ hu₀).mpr hX₁
  have hscale₂ : X ≤ L/u^2 := (le_div_iff₀ (sq_pos_of_pos hu₀)).mpr hX₂
  have hr (x : ℝ) : (p x).re = x := by simp [p]
  have hi (x : ℝ) : (p x).im = t := by simp [p]
  have hheight (x : ℝ) : |(p x).im| = t := by rw [hi, abs_of_pos ht₀]
  have hz (x : ℝ) (hx : c ≤ x) : riemannZeta (p x) ≠ 0 :=
    riemannZeta_ne_zero_on_horizontal_of_no_ordinate hno (by dsimp [c] at hx; linarith)
  have hwb : 1/2 < (p b).re := by rw [hr]; exact lt_add_of_pos_right _ hδ
  have hdw : (p b).re-1/2 = δ := by rw [hr]; exact hdiff
  have hF : Z.poissonMass (p b) ≤ 2*B*L := by
    have h := (HB Z hwb (by rwa [hr]) (by rw [hheight]; linarith)
      hu₁ (by rw [hdw, hdu])).1
    rw [hheight] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add hX le_rfl) hB.le).trans_eq (by ring))
  let S := Z.ordinateWindow t (δ/8)
  have hcard : (S.card : ℝ) ≤ (8*B)*δ*L := by
    have h := Z.card_ordinateWindow_le_poissonMass hRH hwb (d := δ/8) (by rw [hdw]; linarith)
    rw [hi, hdw] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ 4*δ)).trans_eq (by ring))
  have hf : ContinuousOn f (Icc c 2) := continuousOn_horizontal_zeta_logDeriv ht₀.ne' hno
  have hf₁ := hf.mono (Icc_subset_Icc_right hb)
  have hf₂ := hf.mono (Icc_subset_Icc_left hcb)
  have hlocal (x : ℝ) (hx : x ∈ Icc c b) :
      ‖f x - ∑ n ∈ S, 1/(p x-Z.zero n)‖ ≤ K*L := by
    have h := HK Z (s := p x) (w := p b) (by rw [hr]; exact hx.1) (by rw [hr]; exact hx.2.trans hb)
      hwb (by rwa [hr]) ((hi x).trans (hi b).symm) (by rwa [hheight]) hu₁
      (by rw [hdw, hdu]) (by rw [hheight]; exact hX) (hz x hx.1)
    rwa [hheight, hi, hdw] at h
  have hnear := local_pole_integral_bounds S Z.zero hcb
    (fun n _ => riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n))
    (fun n _ he => hno ⟨Z.zero n, Z.mem_strip n, he.symm⟩) f hf₁ hlocal
  rw [hdiff] at hnear
  have hfar (x : ℝ) (hx : x ∈ Icc b 2) :
      ‖f x‖ ≤ B*(X+Real.exp (-((x-c)*u))*L) := by
    have hxδ : 2 ≤ (x-c)*u := hdu ▸ mul_le_mul_of_nonneg_right
      (show δ ≤ x-c by linarith [hdiff, hx.1]) hu₀.le
    have h := (HB Z (s := p x) (by rw [hr]; exact (lt_add_of_pos_right c hδ).trans_le hx.1)
      (by rw [hr]; exact hx.2) (by rw [hheight]; linarith) hu₁ (by rwa [hr])).2
    rwa [hheight, hr] at h
  have hright := horizontal_exp_majorant_integrals hcb hb (by dsimp [c]; norm_num : (2 : ℝ) ≤ c+2)
    hu₀ hX₀ hL.le hB.le f hf₂ hfar
  have hNI : |∫ x in c..b, (f x).im| ≤ N*δ*L := by
    have hcardπ := mul_le_mul_of_nonneg_left hcard Real.pi_pos.le
    have hBL := mul_nonneg (mul_nonneg hB.le hδ.le) hL.le
    dsimp only [N]
    linarith only [hnear.1, hcardπ, hBL]
  have hNR : |∫ x in c..b, (x-c)*(f x).re| ≤ N*δ^2*L := by
    have hcardδ := mul_le_mul_of_nonneg_right hcard hδ.le
    have hpos := mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hB.le) (sq_nonneg δ)) hL.le
    dsimp only [N]
    linarith only [hnear.2, hcardδ, hpos]
  have hFI : |∫ x in b..2, (f x).im| ≤ 3*B*(L/u) :=
    hright.1.trans ((mul_le_mul_of_nonneg_left (by linarith only [hscale₁] : 2*X+L/u ≤ 3*(L/u)) hB.le).trans_eq (by ring))
  have hFR : |∫ x in b..2, (x-c)*(f x).re| ≤ 5*B*(L/u^2) :=
    hright.2.trans ((mul_le_mul_of_nonneg_left (by linarith only [hscale₂] : 4*X+L/u^2 ≤ 5*(L/u^2)) hB.le).trans_eq (by ring))
  have hadd (g : ℝ → ℝ) (hg : ContinuousOn g (Icc c 2)) :
      |∫ x in c..2, g x| ≤ |∫ x in c..b, g x|+|∫ x in b..2, g x| := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hg.mono (Icc_subset_Icc_right hb)).intervalIntegrable_of_Icc hcb)
      ((hg.mono (Icc_subset_Icc_left hcb)).intervalIntegrable_of_Icc hb)]
    exact abs_add_le _ _
  constructor
  · apply (hadd _ (Complex.continuous_im.comp_continuousOn hf)).trans ((add_le_add hNI hFI).trans ?_)
    change N*(2/u)*L+3*B*(L/u) ≤ (4*N+5*B)*(L/u)
    rw [show N*(2/u)*L+3*B*(L/u) = (2*N+3*B)*(L/u) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hL.le hu₀.le)
  · apply (hadd _ ((continuous_id.sub continuous_const).continuousOn.mul
      (Complex.continuous_re.comp_continuousOn hf))).trans ((add_le_add hNR hFR).trans ?_)
    change N*(2/u)^2*L+5*B*(L/u^2) ≤ (4*N+5*B)*(L/u^2)
    exact le_of_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
