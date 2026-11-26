import AnalyticNumberTheory.PrimeDistribution.PositiveZeroTail
import AnalyticNumberTheory.PrimeDistribution.SelbergLogDerivative

/-! # Zero counts in windows of inverse log-log width -/

noncomputable section

open Complex Filter Finset
open scoped Classical
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Under RH the Poisson mass at horizontal distance δ bounds the total multiplicity
of any finite set of zeros with ordinates at distance at most δ. -/
theorem sum_multiplicity_le_poissonMass (Z : ZetaZeroEnumeration) (hRH : RiemannHypothesisProp)
    {s : ℂ} (hs : 1/2 < s.re) (S : Finset CriticalStripZeros)
    (hS : ∀ z ∈ S, |(z : ℂ).im - s.im| ≤ s.re-1/2) :
    (∑ z ∈ S, (zeroMultiplicity z : ℝ)) ≤ 2*(s.re-1/2)*Z.poissonMass s := by
  let δ := s.re - 1/2
  have hδ : 0 < δ := sub_pos.mpr hs
  let v (z : ℂ) := (‖z-s‖^2)⁻¹
  let m (z : CriticalStripZeros) : ℝ := zeroMultiplicity z
  have h := Z.hasSum_distinct (f := fun z => (v z : ℂ))
    (Complex.hasSum_ofReal.mpr (Z.summable_inv_sq_sub s).hasSum)
  have H : HasSum (fun z : CriticalStripZeros => m z * v z) (∑' n, v (Z.zero n)) := by
    simpa only [m, zeroMultiplicity, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using Complex.hasSum_re h
  have hv (z : CriticalStripZeros) (hz : z ∈ S) : 1 ≤ (2*δ^2) * v z := by
    have hr := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ z.property
    have hsq : ‖(z : ℂ)-s‖^2 = δ^2 + ((z:ℂ).im-s.im)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hr]
      dsimp only [δ]
      ring
    have hgap := pow_le_pow_left₀ (abs_nonneg _) (hS z hz) 2
    rw [sq_abs] at hgap
    change 1 ≤ (2*δ^2) * (‖(z:ℂ)-s‖^2)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (hsq ▸ add_pos_of_pos_of_nonneg (sq_pos_of_pos hδ) (sq_nonneg _)), hsq]
    change _ ≤ δ^2 at hgap
    linarith
  calc
    _ ≤ ∑ z ∈ S, (2*δ^2) * (m z * v z) := by
      apply sum_le_sum
      intro z hz
      have hm := mul_le_mul_of_nonneg_left (hv z hz) (show 0 ≤ m z from Nat.cast_nonneg _)
      dsimp only [m] at hm ⊢
      linarith only [hm]
    _ = (2*δ^2) * ∑ z ∈ S, m z * v z := (mul_sum ..).symm
    _ ≤ (2*δ^2) * ∑' n, v (Z.zero n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← H.tsum_eq]
      exact H.summable.sum_le_tsum _ (fun z _ => mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (sq_nonneg _)))
    _ = 2*(s.re-1/2)*Z.poissonMass s := by
      dsimp only [δ, v, ZetaZeroEnumeration.poissonMass]
      ring

/-- The count with its usual inclusive upper endpoint is controlled by the
Poisson mass at a point to the right of the critical line. -/
theorem zeroCountUpTo_sub_le_poissonMass (Z : ZetaZeroEnumeration) (hRH : RiemannHypothesisProp)
    {s : ℂ} (hs : 1/2 < s.re) {d : ℝ} (hd : 0 ≤ d) (hwidth : d ≤ s.re-1/2) :
    (zeroCountUpTo (s.im+d) : ℝ) - (zeroCountUpTo (s.im-d) : ℝ) ≤
      2*(s.re-1/2)*Z.poissonMass s := by
  let S := positiveZerosUpTo (s.im+d) \ positiveZerosUpTo (s.im-d)
  have hsub : positiveZerosUpTo (s.im-d) ⊆ positiveZerosUpTo (s.im+d) := by
    intro z hz
    obtain ⟨hp, hm⟩ := mem_positiveZerosUpTo.mp hz
    exact mem_positiveZerosUpTo.mpr ⟨hp, by linarith⟩
  have he : (∑ z ∈ S, (zeroMultiplicity z : ℝ)) =
      (zeroCountUpTo (s.im+d) : ℝ) - (zeroCountUpTo (s.im-d) : ℝ) := by
    rw [← sum_positiveZerosUpTo_multiplicity, ← sum_positiveZerosUpTo_multiplicity]
    exact eq_sub_of_add_eq (sum_sdiff hsub)
  rw [← he]
  apply sum_multiplicity_le_poissonMass Z hRH hs
  intro z hz
  obtain ⟨hp, hn⟩ := mem_sdiff.mp hz
  obtain ⟨hz₀, hz₁⟩ := mem_positiveZerosUpTo.mp hp
  have hz₂ : s.im-d < (z : ℂ).im := lt_of_not_ge fun he => hn (mem_positiveZerosUpTo.mpr ⟨hz₀, he⟩)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Under RH a symmetric window of radius 1/log log T contains at most
O(log T / log log T) zeros, counted with analytic multiplicity at every large height. -/
theorem zeroCountUpTo_inverse_loglog_window_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ᶠ T : ℝ in atTop,
      (zeroCountUpTo (T+1/Real.log (Real.log T)) : ℝ) -
        (zeroCountUpTo (T-1/Real.log (Real.log T)) : ℝ) ≤ C*(Real.log T/Real.log (Real.log T)) := by
  obtain ⟨Z, _⟩ := exists_centered_logDeriv_riemannZeta
  obtain ⟨B, hB, HB⟩ := selberg_poissonMass_and_logDeriv_le hRH
  refine ⟨32*B, by positivity, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 8,
    eventually_ge_atTop (2:ℝ)] with T hlog hT
  let L := Real.log (Real.log T)
  change 8 ≤ L at hlog
  have hL : 0 < L := by linarith
  have ht : 0 < Real.log T := Real.log_pos (one_lt_two.trans_le hT)
  let u := L/4
  let δ := 8/L
  let s : ℂ := ((1/2+δ : ℝ) : ℂ) + (T : ℂ)*I
  have hδ : 0 < δ := div_pos (by norm_num) hL
  have hδ₁ : δ ≤ 1 := (div_le_one hL).mpr hlog
  have hr : s.re = 1/2+δ := by simp [s]
  have hi : s.im = T := by simp [s]
  have hdisp : s.re-1/2 = δ := by rw [hr]; ring
  have hs : 1/2 < s.re := by rw [hr]; linarith
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hδu : (s.re-1/2)*u = 2 := by rw [hdisp]; dsimp [δ, u]; field_simp; ring
  have hpo := (HB Z hs (by rw [hr]; linarith) (by rwa [hi, abs_of_pos (two_pos.trans_le hT)])
    hu hδu.ge).1
  rw [hi, abs_of_pos (two_pos.trans_le hT)] at hpo
  have hX : Real.exp (u+u) ≤ Real.log T := by
    rw [← Real.exp_log ht]
    apply Real.exp_le_exp.mpr
    change L/4+L/4 ≤ L
    linarith
  have hcount := zeroCountUpTo_sub_le_poissonMass Z hRH hs (d := 1/L)
    (by positivity) (by rw [hdisp]; exact div_le_div_of_nonneg_right (by norm_num) hL.le)
  rw [hi, hdisp] at hcount
  apply hcount.trans
  calc
    _ ≤ 2*δ*(B*(Real.log T + Real.log T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hpo.trans (mul_le_mul_of_nonneg_left (add_le_add hX le_rfl) hB.le)
    _ = (32*B)*(Real.log T / Real.log (Real.log T)) := by dsimp only [δ, L]; ring

end AnalyticNumberTheory.PrimeDistribution
