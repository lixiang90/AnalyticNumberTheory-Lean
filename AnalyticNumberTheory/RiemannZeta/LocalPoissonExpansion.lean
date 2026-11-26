import AnalyticNumberTheory.AnalyticTools.EntireFunctions.LocalPoleWindow
import AnalyticNumberTheory.RiemannZeta.PoissonZeroSum

/-! # The local pole expansion of the completed zeta function under RH -/

noncomputable section

open Complex Finset
open scoped Classical
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.RiemannZeta

/-- Indices of all zeros whose ordinates lie strictly within d of t.
Each occurrence of a multiple zero contributes a separate index. -/
def ZetaZeroEnumeration.ordinateWindow (Z : ZetaZeroEnumeration) (t d : ℝ) : Finset ℕ :=
  ((Z.finite_norm_le (1+d+|t|)).toFinset).filter (fun n => |(Z.zero n).im-t| < d)

/-- Membership in the open ordinate window is exactly its height inequality. -/
theorem ZetaZeroEnumeration.mem_ordinateWindow (Z : ZetaZeroEnumeration) {t d : ℝ} {n : ℕ} :
    n ∈ Z.ordinateWindow t d ↔ |(Z.zero n).im-t| < d := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro hn
    apply mem_filter.mpr
    refine ⟨(Z.finite_norm_le _).mem_toFinset.mpr ?_, hn⟩
    have hr := (mem_criticalStripZeros.mp (Z.mem_strip n)).2
    have hi := abs_add_le ((Z.zero n).im-t) t
    rw [sub_add_cancel] at hi
    have h := Complex.norm_le_abs_re_add_abs_im (Z.zero n)
    rw [abs_of_pos hr.1] at h
    change ‖Z.zero n‖ ≤ _
    linarith [hr.2]

private theorem norm_sub_zero_le_displacements (Z : ZetaZeroEnumeration) (hRH : RiemannHypothesisProp)
    {w : ℂ} (hw : 1/2 < w.re) (n : ℕ) :
    ‖w-Z.zero n‖ ≤ w.re-1/2 + |(Z.zero n).im-w.im| := by
  have hr := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)
  simpa only [Complex.sub_re, Complex.sub_im, hr, abs_of_pos (sub_pos.mpr hw),
    abs_sub_comm w.im (Z.zero n).im] using Complex.norm_le_abs_re_add_abs_im (w-Z.zero n)

/-- The number of indices in a window of radius at most the horizontal displacement
is bounded by the displacement times the Poisson mass, with absolute constant four. -/
theorem ZetaZeroEnumeration.card_ordinateWindow_le_poissonMass (Z : ZetaZeroEnumeration)
    (hRH : RiemannHypothesisProp) {w : ℂ} (hw : 1/2 < w.re) {d : ℝ} (hd : d ≤ w.re-1/2) :
    ((Z.ordinateWindow w.im d).card : ℝ) ≤ 4*(w.re-1/2)*Z.poissonMass w := by
  let δ := w.re-1/2
  let S := Z.ordinateWindow w.im d
  have hδ : 0 < δ := sub_pos.mpr hw
  have hb (n : ℕ) (hn : n ∈ S) : 1 ≤ (4*δ^2) * (‖Z.zero n-w‖^2)⁻¹ := by
    have h := Z.mem_ordinateWindow.mp hn
    have hdist : ‖w-Z.zero n‖ ≤ 2*δ := by
      dsimp only [δ]
      linarith [norm_sub_zero_le_displacements Z hRH hw n]
    have hne : Z.zero n ≠ w := fun he => by
      have hr := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)
      rw [he] at hr
      linarith
    rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))),
      one_mul, norm_sub_rev]
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hdist 2]
  calc
    _ = ∑ _n ∈ S, (1 : ℝ) := by simp [S]
    _ ≤ ∑ n ∈ S, (4*δ^2) * (‖Z.zero n-w‖^2)⁻¹ := sum_le_sum hb
    _ ≤ (4*δ^2) * ∑' n, (‖Z.zero n-w‖^2)⁻¹ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left ((Z.summable_inv_sq_sub w).sum_le_tsum _ (fun n _ =>
        inv_nonneg.mpr (sq_nonneg _))) (by positivity)
    _ = _ := by dsimp only [δ, ZetaZeroEnumeration.poissonMass]; ring

/-- To the right of the reference point each sharp pole term is bounded by
the inverse horizontal distance. Summing costs at most four times the Poisson mass. -/
theorem ZetaZeroEnumeration.norm_ordinateWindow_sum_le (Z : ZetaZeroEnumeration)
    (hRH : RiemannHypothesisProp) {w s : ℂ} (hw : 1/2 < w.re) (hs : w.re ≤ s.re)
    {d : ℝ} (hd : d ≤ w.re-1/2) :
    ‖∑ n ∈ Z.ordinateWindow w.im d, 1/(s-Z.zero n)‖ ≤ 4*Z.poissonMass w := by
  let S := Z.ordinateWindow w.im d
  let δ := w.re-1/2
  have hδ : 0 < δ := sub_pos.mpr hw
  calc
    _ ≤ ∑ n ∈ S, ‖(1 : ℂ)/(s-Z.zero n)‖ := norm_sum_le ..
    _ ≤ ∑ _n ∈ S, 1/δ := by
      apply sum_le_sum
      intro n _
      rw [norm_div, norm_one]
      apply one_div_le_one_div_of_le hδ
      have h := Complex.re_le_norm (s-Z.zero n)
      rw [Complex.sub_re, riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)] at h
      dsimp only [δ]
      linarith
    _ = (S.card : ℝ)*(1/δ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (4*δ*Z.poissonMass w)*(1/δ) := mul_le_mul_of_nonneg_right
      (Z.card_ordinateWindow_le_poissonMass hRH hw hd) (by positivity)
    _ = _ := by field_simp

/-- With a reference point w at distance δ to the right of the critical line,
the local pole sum of ξ′/ξ uses the window |γ−Im w| < δ/8. The remaining change
of the logarithmic derivative costs at most eighteen times the Poisson mass at w. -/
theorem ZetaZeroEnumeration.norm_logDeriv_xi_sub_window_le (Z : ZetaZeroEnumeration)
    (hRH : RiemannHypothesisProp) {s w : ℂ} (hw : 1/2 < w.re) (hi : s.im = w.im)
    (hs : |s.re-1/2| ≤ w.re-1/2) (hs₀ : s ≠ 0) (hξ : xi s ≠ 0) :
    ‖deriv xi s / xi s - deriv xi w / xi w -
      ∑ n ∈ Z.ordinateWindow w.im ((w.re-1/2)/8), 1/(s-Z.zero n)‖ ≤ 18 * Z.poissonMass w := by
  let δ := w.re-1/2
  have hδ : 0 < δ := sub_pos.mpr hw
  let S := Z.ordinateWindow w.im (δ/8)
  have hws : ‖w-s‖ ≤ 2*δ := by
    have h := Complex.norm_le_abs_re_add_abs_im (w-s)
    rw [Complex.sub_im, hi, sub_self, abs_zero, add_zero, Complex.sub_re] at h
    refine h.trans (abs_le.mpr ⟨?_, ?_⟩) <;> dsimp only [δ] <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
  have hdist (n : ℕ) : ‖w-Z.zero n‖ ≤ δ + |(Z.zero n).im-w.im| :=
    norm_sub_zero_le_displacements Z hRH hw n
  have hin (n : ℕ) (hn : n ∈ S) : ‖w-Z.zero n‖ ≤ 18*δ := by
    have h := Z.mem_ordinateWindow.mp hn
    linarith [hdist n]
  have hout (n : ℕ) (hn : n ∉ S) : ‖w-s‖ * ‖w-Z.zero n‖ ≤ (18*δ) * ‖s-Z.zero n‖ := by
    have hgap : δ/8 ≤ |(Z.zero n).im-w.im| := le_of_not_gt fun h => hn (Z.mem_ordinateWindow.mpr h)
    have hsn : |(Z.zero n).im-w.im| ≤ ‖s-Z.zero n‖ := by
      simpa only [Complex.sub_im, hi, abs_sub_comm w.im (Z.zero n).im] using Complex.abs_im_le_norm (s-Z.zero n)
    calc
      _ ≤ (2*δ) * (9 * ‖s-Z.zero n‖) :=
        mul_le_mul hws (by linarith [hdist n]) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hwζ := riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH w hw
  have hwξ : xi w ≠ 0 := fun he => hwζ (xi_eq_zero_iff.mp he).1
  have hne {z : ℂ} (hz : xi z ≠ 0) (n : ℕ) : z ≠ Z.zero n := by
    intro he
    have h := Z.mem_strip n
    rw [criticalStripZeros_eq_xi_zeros] at h
    exact hz (he ▸ h)
  obtain ⟨B, H⟩ := Z.exists_logDeriv_xi_centered
  have hw₀ : w ≠ 0 := fun he => by rw [he, Complex.zero_re] at hw; linarith
  rw [H hs₀ hξ, H hw₀ hwξ, add_sub_add_left_eq_sub]
  exact (norm_centeredPole_sub_window_le Z.zero S Z.zero_ne_zero (hne hξ) (hne hwξ)
    (Z.summable_centered s) (Z.summable_centered w) (Z.summable_inv_sq_sub w) hin hout).trans_eq
    (by dsimp only [ZetaZeroEnumeration.poissonMass, δ]; ring)

end AnalyticNumberTheory.RiemannZeta
