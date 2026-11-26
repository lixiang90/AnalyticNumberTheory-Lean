import AnalyticNumberTheory.PrimeDistribution.SelbergLogDerivative
import AnalyticNumberTheory.RiemannZeta.CompletionLogDerivative
import AnalyticNumberTheory.RiemannZeta.LocalPoissonExpansion

/-! # Selberg's local expansion for the logarithmic derivative of zeta -/

noncomputable section

open Complex Finset Filter
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The sharp zero fractions inside a shrinking open window approximate ζ′/ζ
with uniform logarithmic error. The reference point w chooses the window width. -/
theorem norm_logDeriv_zeta_sub_window_le_of_cutoff (hRH : RiemannHypothesisProp) :
    ∃ K > 0, ∀ (Z : ZetaZeroEnumeration) {s w : ℂ} {u : ℝ},
      1/2 ≤ s.re → s.re ≤ 2 → 1/2 < w.re → w.re ≤ 2 → s.im = w.im →
      4 ≤ |w.im| → 1 ≤ u → 2 ≤ (w.re-1/2)*u → Real.exp (u+u) ≤ Real.log (|w.im|) →
      riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s -
        ∑ n ∈ Z.ordinateWindow w.im ((w.re-1/2)/8), 1/(s-Z.zero n)‖ ≤ K * Real.log (|w.im|) := by
  obtain ⟨B, hB, HB⟩ := selberg_poissonMass_and_logDeriv_le hRH
  obtain ⟨C, hC, HC⟩ := norm_logDeriv_xi_sub_zeta_le
  refine ⟨40*B + 2*(1+C), by positivity, ?_⟩
  intro Z s w u hs hs₂ hw hw₂ hi ht hu huδ hX hζ
  let L := Real.log (|w.im|)
  have hL : 1 ≤ L := (Real.one_le_exp_iff.mpr (show 0 ≤ u+u by linarith)).trans hX
  have hL₀ := zero_le_one.trans hL
  let D (p : ℂ) := deriv riemannZeta p / riemannZeta p
  let E (p : ℂ) := deriv xi p / xi p
  let S := Z.ordinateWindow w.im ((w.re-1/2)/8)
  let A := ∑ n ∈ S, 1/(s-Z.zero n)
  have H {p : ℂ} (hp : 1/2 < p.re) (hp₂ : p.re ≤ 2) (hi' : p.im = w.im)
      (hpu : 2 ≤ (p.re-1/2)*u) : Z.poissonMass p ≤ 2*B*L ∧ ‖D p‖ ≤ 2*B*L := by
    have h := HB Z hp hp₂ (by rw [hi']; linarith) hu hpu
    rw [hi'] at h
    have hq := Real.exp_le_one_iff.mpr (show -((p.re-1/2)*u) ≤ 0 by linarith)
    have hx : Real.exp (u+u) ≤ L := hX
    constructor
    · exact h.1.trans ((mul_le_mul_of_nonneg_left (add_le_add hx le_rfl) hB.le).trans_eq (by ring))
    · have h₀ := mul_le_of_le_one_left hL₀ hq
      exact h.2.trans ((mul_le_mul_of_nonneg_left (add_le_add hx h₀) hB.le).trans_eq (by ring))
  have HG {p : ℂ} (hp : 0 < p.re) (hp₂ : p.re ≤ 2) (hi' : p.im = w.im)
      (hpζ : riemannZeta p ≠ 0) : ‖E p - D p‖ ≤ (1+C)*L := by
    have h := HC (show -1 ≤ p.re by linarith) hp₂ (by rwa [hi']) hpζ
    rw [hi'] at h
    exact h.trans (by change L+C ≤ _; linarith [le_mul_of_one_le_right hC.le hL])
  have hRef := H hw hw₂ rfl huδ
  have hwζ := riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH w hw
  change ‖D s - A‖ ≤ _ * L
  by_cases hsw : s.re ≤ w.re
  · have hsband : |s.re-1/2| ≤ w.re-1/2 := by rw [abs_of_nonneg (sub_nonneg.mpr hs)]; linarith
    have hs₀ : s ≠ 0 := fun he => by rw [he, Complex.zero_re] at hs; linarith
    have hnear : ‖E s - E w - A‖ ≤ 18 * Z.poissonMass w :=
      Z.norm_logDeriv_xi_sub_window_le hRH hw hi hsband hs₀ (fun he => hζ (xi_eq_zero_iff.mp he).1)
    have hGs := HG (p := s) (by linarith) hs₂ hi hζ
    have hGw := HG (p := w) (by linarith) hw₂ rfl hwζ
    rw [norm_sub_rev] at hGs
    rw [show D s - A = (D s-E s) + (E s-E w-A) + (E w-D w) + D w by ring]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans ?_))
    linarith [hRef.1, hRef.2, mul_nonneg hB.le hL₀]
  · have hsw' := lt_of_not_ge hsw
    have hD := (H (hw.trans hsw') hs₂ hi (huδ.trans (mul_le_mul_of_nonneg_right
      (sub_le_sub_right hsw'.le _) (zero_le_one.trans hu)))).2
    have hsA : ‖A‖ ≤ 4 * Z.poissonMass w :=
      Z.norm_ordinateWindow_sum_le hRH hw hsw'.le (by linarith)
    exact (norm_sub_le _ _).trans (by linarith [hRef.1, mul_nonneg hB.le hL₀, mul_nonneg hC.le hL₀])

/-- On the half of the critical strip from Re(s) = 1/2 to 2, the only sharp
zero fractions needed at large height are those with |γ−t| < 1/log log |t|.
The O(log |t|) error is uniform up to the critical line at all regular points. -/
theorem logDeriv_zeta_local_inverse_loglog_of_rh (hRH : RiemannHypothesisProp) :
    ∃ K > 0, ∃ T₀ > 0, ∀ (Z : ZetaZeroEnumeration) {s : ℂ}, T₀ ≤ |s.im| →
      1/2 ≤ s.re → s.re ≤ 2 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s -
        ∑ n ∈ Z.ordinateWindow s.im (1/Real.log (Real.log (|s.im|))), 1/(s-Z.zero n)‖ ≤
          K * Real.log (|s.im|) := by
  obtain ⟨K, hK, HK⟩ := norm_logDeriv_zeta_sub_window_le_of_cutoff hRH
  obtain ⟨T, hT⟩ := tendsto_atTop_atTop.mp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) 8
  refine ⟨K, hK, max 4 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z s ht hs hs₂ hζ
  let L := Real.log (Real.log (|s.im|))
  have h₈ : 8 ≤ L := hT _ ((le_max_right _ _).trans ht)
  have hL : 0 < L := by linarith
  have ht₄ : 4 ≤ |s.im| := (le_max_left _ _).trans ht
  have hlog := Real.log_pos (show 1 < |s.im| by linarith)
  let u := L/4
  let δ := 8/L
  let w : ℂ := ((1/2+δ : ℝ) : ℂ) + (s.im : ℂ)*I
  have hr : w.re = 1/2+δ := by simp [w]
  have hi : w.im = s.im := by simp [w]
  have hd : w.re-1/2 = δ := by rw [hr]; ring
  have hδ₀ : 0 < δ := div_pos (by norm_num) hL
  have hδ₁ : δ ≤ 1 := (div_le_one hL).mpr h₈
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hdu : (w.re-1/2)*u = 2 := by rw [hd]; dsimp [δ, u]; field_simp; ring
  have hX : Real.exp (u+u) ≤ Real.log (|w.im|) := by
    rw [hi, ← Real.exp_log hlog]
    apply Real.exp_le_exp.mpr
    change L/4+L/4 ≤ L
    linarith
  have h := HK Z hs hs₂ (by rw [hr]; linarith) (by rw [hr]; linarith) hi.symm
    (by rwa [hi]) hu hdu.ge hX hζ
  rw [hi, hd, show δ/8 = 1/L by dsimp [δ]; ring] at h
  exact h

/-- Across the whole strip −1 ≤ Re(s) ≤ 2 the logarithmic derivative differs
from the open inverse-log-log window of nearby poles by O(log |Im(s)|), uniformly
at every regular point of sufficiently large positive or negative height. -/
theorem logDeriv_zeta_local_inverse_loglog_strip_of_rh (hRH : RiemannHypothesisProp) :
    ∃ K > 0, ∃ T₀ > 0, ∀ (Z : ZetaZeroEnumeration) {s : ℂ}, T₀ ≤ |s.im| →
      -1 ≤ s.re → s.re ≤ 2 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s -
        ∑ n ∈ Z.ordinateWindow s.im (1/Real.log (Real.log (|s.im|))), 1/(s-Z.zero n)‖ ≤
          K * Real.log (|s.im|) := by
  obtain ⟨K, hK, T, hT, H⟩ := logDeriv_zeta_local_inverse_loglog_of_rh hRH
  obtain ⟨C, hC, HC⟩ := norm_logDeriv_xi_sub_zeta_le
  refine ⟨K+2*(1+C), by positivity, max T (max 4 (Real.exp 1)), hT.trans_le (le_max_left _ _), ?_⟩
  intro Z s ht hs hs₂ hζ
  let L := Real.log (|s.im|)
  have ht₀ : T ≤ |s.im| := (le_max_left _ _).trans ht
  have ht₄ : 4 ≤ |s.im| := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hL : 1 ≤ L := (Real.le_log_iff_exp_le (by linarith : 0 < |s.im|)).mpr
    ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hL₀ := zero_le_one.trans hL
  by_cases hside : 1/2 ≤ s.re
  · exact (H Z ht₀ hside hs₂ hζ).trans (mul_le_mul_of_nonneg_right (by linarith) hL₀)
  let w := 1-star s
  have hr : w.re = 1 - s.re := by simp [w]
  have hi : w.im = s.im := by simp [w]
  have hw : 1/2 < w.re := by rw [hr]; linarith
  have hw₂ : w.re ≤ 2 := by rw [hr]; linarith
  have hwζ := riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH w hw
  let S := Z.ordinateWindow s.im (1/Real.log L)
  let A (z : ℂ) := ∑ n ∈ S, 1/(z-Z.zero n)
  let D (z : ℂ) := deriv riemannZeta z / riemannZeta z
  let E (z : ℂ) := deriv xi z / xi z
  have hDw : ‖D w - A w‖ ≤ K*L := by
    have h := H Z (s := w) (by rwa [hi]) hw.le hw₂ hwζ
    rwa [hi] at h
  have hEa : E w = -(starRingEnd ℂ) (E s) :=
    xi_logDeriv_one_sub_star s (fun he => hζ (xi_eq_zero_iff.mp he).1)
  have hAa : A w = -(starRingEnd ℂ) (A s) := by
    unfold A
    rw [map_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro n _
    have hρ := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)
    have he : w-Z.zero n = -(starRingEnd ℂ) (s-Z.zero n) := by
      apply Complex.ext <;> simp [w, hρ] <;> ring
    rw [he, map_div₀, map_one, div_neg]
  have hn : ‖E w - A w‖ = ‖E s - A s‖ := by
    rw [hEa, hAa, show -(starRingEnd ℂ) (E s) - -(starRingEnd ℂ) (A s) =
      -((starRingEnd ℂ) (E s - A s)) by rw [map_sub]; ring, norm_neg]
    exact norm_star _
  have hGs : ‖D s - E s‖ ≤ L+C := by
    rw [norm_sub_rev]
    exact HC hs hs₂ ht₄ hζ
  have hGw : ‖E w - D w‖ ≤ L+C := by
    have h := HC (s := w) (by linarith) hw₂ (by rwa [hi]) hwζ
    rwa [hi] at h
  change ‖D s - A s‖ ≤ _ * L
  calc
    _ ≤ ‖D s - E s‖ + ‖E s - A s‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (D s-E s) (E s-A s)
    _ ≤ (L+C) + (‖E w - D w‖ + ‖D w - A w‖) := by
      rw [← hn]
      exact add_le_add hGs (by simpa only [sub_add_sub_cancel] using norm_add_le (E w-D w) (D w-A w))
    _ ≤ _ := by linarith [le_mul_of_one_le_right hC.le hL]

end AnalyticNumberTheory.PrimeDistribution
