import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogPoleExpansion
import AnalyticNumberTheory.PrimeDistribution.SelbergLocalExpansion
import AnalyticNumberTheory.PrimeDistribution.SelbergLogZetaBounds

/-! # Local logarithmic expansion of zeta through its nearby zeros under RH -/

noncomputable section

open Complex Set Finset Filter
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

/-- With logarithms normalized at a reference point at least 2/u to the right
of the critical line, the error in the local expansion is O(log |t| / u).
All regular endpoints on the closed half-strip are allowed. -/
theorem horizontalLogZeta_sub_normalized_window_le_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ (Z : ZetaZeroEnumeration) {σ t u : ℝ}, 4 ≤ |t| → 2 ≤ u →
      Real.exp (4*u) ≤ Real.log |t| → 1/2 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ)+(t : ℂ)*I) ≠ 0 →
      let b := max σ (1/2+2/u)
      ‖horizontalLogZeta σ t - ∑ n ∈ Z.ordinateWindow t ((2/u)/8),
        (Complex.log ((σ : ℂ)+(t : ℂ)*I-Z.zero n) -
          Complex.log ((b : ℂ)+(t : ℂ)*I-Z.zero n))‖ ≤ C*(Real.log |t|/u) := by
  obtain ⟨B, hB, HB⟩ := selberg_horizontalLogZeta_and_window_le hRH
  obtain ⟨K, hK, HK⟩ := norm_logDeriv_zeta_sub_window_le_of_cutoff hRH
  refine ⟨B+2*K, by positivity, ?_⟩
  intro Z σ t u ht hu hscale hσ hσ₂ hζ
  let c : ℝ := 1/2
  let δ := 2/u
  let w := c+δ
  let b := max σ w
  let L := Real.log |t|
  let S := Z.ordinateWindow t (δ/8)
  let p (x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I
  let D (x : ℝ) := deriv riemannZeta (p x)/riemannZeta (p x)
  let Q (x : ℝ) := ∑ n ∈ S, Complex.log (p x-Z.zero n)
  have hu₀ := two_pos.trans_le hu
  have hL : 0 < L := Real.log_pos (by linarith)
  have hδ : 0 < δ := div_pos two_pos hu₀
  have hδ₁ : δ ≤ 1 := (div_le_one hu₀).mpr hu
  have hdu : δ*u = 2 := div_mul_cancel₀ _ hu₀.ne'
  have hw : c < w := lt_add_of_pos_right _ hδ
  have hw₂ : w ≤ 2 := by dsimp only [w, c]; linarith
  have hb : σ ≤ b := le_max_left _ _
  have hwb : w ≤ b := le_max_right _ _
  have hb₂ : b ≤ 2 := max_le hσ₂ hw₂
  have hbδ : b-σ ≤ δ := sub_le_iff_le_add.mpr (max_le (by linarith) (by dsimp [w,c]; linarith))
  have ht₀ : t ≠ 0 := fun h => by norm_num [h] at ht
  have hr (x : ℝ) : (p x).re = x := by simp [p]
  have hi (x : ℝ) : (p x).im = t := by simp [p]
  have hd : (p w).re-1/2 = δ := by rw [hr]; dsimp [w,c]; ring
  have hX : Real.exp (u+u) ≤ L := (Real.exp_le_exp.mpr (by linarith : u+u ≤ 4*u)).trans hscale
  have hz (x : ℝ) (hx : σ ≤ x) : riemannZeta (p x) ≠ 0 := by
    rcases hx.eq_or_lt with rfl | hy
    · exact hζ
    · exact riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH _ (by rw [hr]; linarith)
  have hc : ContinuousOn D (Icc σ b) :=
    fun x hx => (continuousAt_horizontal_zeta_logDeriv ht₀ (hz x hx.1)).continuousWithinAt
  have hcut (n : ℕ) (_ : n ∈ S) (x : ℝ) (hx : x ∈ Icc σ b) : p x-Z.zero n ∈ slitPlane := by
    have hρ := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)
    have hpos : 0 ≤ (p x-Z.zero n).re := by rw [Complex.sub_re, hr, hρ]; linarith [hx.1]
    apply mem_slitPlane_iff.mpr
    rcases hpos.eq_or_lt with he | he
    · right
      intro him
      have heq : p x = Z.zero n := sub_eq_zero.mp (Complex.ext (by simpa using he.symm) (by simpa using him))
      exact hz x hx.1 (heq ▸ (mem_criticalStripZeros.mp (Z.mem_strip n)).1)
    · exact .inl he
  have hlocal (x : ℝ) (hx : x ∈ Icc σ b) : ‖D x-∑ n ∈ S, 1/(p x-Z.zero n)‖ ≤ K*L := by
    have hh := HK Z (s := p x) (w := p w) (by rw [hr]; exact hσ.trans hx.1)
      (by rw [hr]; exact hx.2.trans hb₂) (by rwa [hr]) (by rwa [hr]) ((hi x).trans (hi w).symm)
      (by rwa [hi]) (one_le_two.trans hu) (by rw [hd, hdu]) (by rwa [hi]) (hz x hx.1)
    rwa [hi, hd] at hh
  have hres := norm_integral_sub_horizontal_log_increments_le S Z.zero hb hcut D hc hlocal
  change ‖(∫ x in σ..b, D x)-(Q b-Q σ)‖ ≤ K*L*(b-σ) at hres
  have hinc := horizontalLogZeta_sub hb hb₂ ht₀ (fun x hx => hz x hx.1)
  change horizontalLogZeta b t-horizontalLogZeta σ t = ∫ x in σ..b, D x at hinc
  rw [← hinc] at hres
  have hfar := (HB Z ht hu hscale).2 b hwb hb₂
  dsimp only
  rw [Finset.sum_sub_distrib]
  change ‖horizontalLogZeta σ t-(Q σ-Q b)‖ ≤ (B+2*K)*(L/u)
  rw [show horizontalLogZeta σ t-(Q σ-Q b) = horizontalLogZeta b t -
    ((horizontalLogZeta b t-horizontalLogZeta σ t)-(Q b-Q σ)) by abel]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hfar (hres.trans (mul_le_mul_of_nonneg_left hbδ (mul_nonneg hK.le hL.le)))).trans_eq
  dsimp only [δ, L]
  ring

/-- Under RH, throughout the closed half-strip from one half to two, the
Euler-normalized log ζ equals the sum of the principal logarithms of the zeros
in the inverse-log-log window, with uniform error O(log |t| log log log |t| / log log |t|). -/
theorem horizontalLogZeta_local_inverse_loglog_of_rh (hRH : RiemannHypothesisProp) :
    ∃ K > 0, ∃ T₀ > 0, ∀ (Z : ZetaZeroEnumeration) {s : ℂ}, T₀ ≤ |s.im| →
      1/2 ≤ s.re → s.re ≤ 2 → riemannZeta s ≠ 0 →
      let L := Real.log (Real.log |s.im|)
      ‖horizontalLogZeta s.re s.im - ∑ n ∈ Z.ordinateWindow s.im (1/L),
        Complex.log (s-Z.zero n)‖ ≤ K * (Real.log |s.im| * Real.log L / L) := by
  obtain ⟨K, hK, HK⟩ := horizontalLogZeta_sub_normalized_window_le_of_rh hRH
  obtain ⟨B, hB, HB⟩ := selberg_horizontalLogZeta_and_window_le hRH
  obtain ⟨T, hT⟩ := tendsto_atTop_atTop.mp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
    (max 8 (Real.exp 1))
  refine ⟨4*(K+B*(2+Real.pi)), by positivity, max 4 T,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z s ht hs hs₂ hζ
  let L := Real.log (Real.log |s.im|)
  let u := L/4
  let b := max s.re (1/2+2/u)
  let w : ℂ := (b : ℂ)+(s.im : ℂ)*I
  let S := Z.ordinateWindow s.im (1/L)
  have hlarge : max 8 (Real.exp 1) ≤ L := hT _ ((le_max_right _ _).trans ht)
  have h₈ : 8 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hL).mpr ((le_max_right _ _).trans hlarge)
  have ht₄ : 4 ≤ |s.im| := (le_max_left _ _).trans ht
  have hℓ : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hu : 2 ≤ u := by dsimp only [u]; linarith
  have hu₀ := two_pos.trans_le hu
  have he : Real.exp (4*u) = Real.log |s.im| := by
    rw [show 4*u = L by dsimp [u]; ring, Real.exp_log hℓ]
  have hδ : 2/u = 8/L := by dsimp only [u]; field_simp [hL.ne']; ring
  have hd : (2/u)/8 = 1/L := by rw [hδ]; ring
  have hb : 1/2+2/u ≤ b := le_max_right _ _
  have hb₂ : b ≤ 2 := max_le hs₂ (by linarith [(div_le_one hu₀).mpr hu] : 1/2+2/u ≤ 2)
  have hnorm := HK Z ht₄ hu he.le hs hs₂ (by rwa [Complex.re_add_im])
  dsimp only at hnorm
  rw [hd, Complex.re_add_im, Finset.sum_sub_distrib] at hnorm
  let Q (z : ℂ) := ∑ n ∈ S, Complex.log (z-Z.zero n)
  change ‖horizontalLogZeta s.re s.im-(Q s-Q w)‖ ≤ K*(Real.log |s.im| / u) at hnorm
  have hcard := (HB Z ht₄ hu he.le).1
  rw [hd] at hcard
  have hterm (n : ℕ) (hn : n ∈ S) : ‖Complex.log (w-Z.zero n)‖ ≤ (2+Real.pi)*Real.log L := by
    have hρ := riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)
    have hr : (w-Z.zero n).re = b-1/2 := by simp [w, hρ]
    have him : |(w-Z.zero n).im| < 1/L := by
      simpa [w, abs_sub_comm s.im (Z.zero n).im] using Z.mem_ordinateWindow.mp hn
    have h₁ : L⁻¹ ≤ 2/u := by
      rw [hδ, ← one_div]
      exact div_le_div_of_nonneg_right (by norm_num) hL.le
    have hb₀ : 0 ≤ b-1/2 := by linarith [inv_pos.mpr hL]
    apply norm_log_le_of_inv_le_norm_le_three hL hlog
    · exact (le_trans (by rw [hr]; linarith : L⁻¹ ≤ (w-Z.zero n).re) (Complex.re_le_norm _))
    · have hh := Complex.norm_le_abs_re_add_abs_im (w-Z.zero n)
      rw [hr, abs_of_nonneg hb₀] at hh
      linarith [him, (div_le_one hL).mpr (show 1 ≤ L by linarith)]
  have hsum : ‖Q w‖ ≤ B*(Real.log |s.im| / u)*((2+Real.pi)*Real.log L) := calc
    _ ≤ ∑ n ∈ S, ‖Complex.log (w-Z.zero n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, (2+Real.pi)*Real.log L := Finset.sum_le_sum hterm
    _ = (S.card : ℝ)*((2+Real.pi)*Real.log L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  change ‖horizontalLogZeta s.re s.im-Q s‖ ≤ 4*(K+B*(2+Real.pi))*(Real.log |s.im| * Real.log L/L)
  rw [show horizontalLogZeta s.re s.im-Q s =
    (horizontalLogZeta s.re s.im-(Q s-Q w))-Q w by abel]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (hnorm.trans (le_mul_of_one_le_right (mul_nonneg hK.le (div_nonneg hℓ.le hu₀.le)) hlog)) hsum).trans_eq
  dsimp only [u]
  field_simp [hL.ne']

end AnalyticNumberTheory.PrimeDistribution
