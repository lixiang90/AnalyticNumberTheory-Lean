import AnalyticNumberTheory.PrimeDistribution.FullPerronContour
import AnalyticNumberTheory.RiemannZeta.LogDerivativeLeft

/-! # Bounds on three sides of an expanding sharp Perron rectangle -/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Left edge of a rectangle of height comparable to `R²`, at a negative odd integer. -/
def perronLeftEdge (R : ℝ) : ℝ := -(2*(⌈R⌉₊ : ℝ)+1)

/-- The negative odd abscissa recedes linearly in the square root of the height. -/
theorem perronLeftEdge_bounds {R : ℝ} (hR : 3 ≤ R) :
    perronLeftEdge R ≤ -R ∧ -4*R ≤ perronLeftEdge R := by
  have hlo := Nat.le_ceil R
  have hhi := Nat.ceil_lt_add_one (by linarith : 0 ≤ R)
  dsimp only [perronLeftEdge]
  constructor <;> linarith

private theorem norm_box {R σ t : ℝ} (hR : 3 ≤ R) (hσ : σ ∈ Icc (perronLeftEdge R) 2)
    (ht : |t| ≤ R^2+1) : ‖(σ : ℂ)+t*I‖+3 ≤ R^4 := by
  have h₁ := (perronLeftEdge_bounds hR).2
  have hσ' : |σ| ≤ 4*R := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hnorm := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ)+t*I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add] at hnorm
  have h₂ : 9 ≤ R^2 := by nlinarith
  nlinarith [sq_nonneg (R^2-5), mul_nonneg (by linarith : 0≤R-3) (by linarith : 0≤R+2)]

private theorem log_box {R σ t : ℝ} (hR : 3 ≤ R) (hσ : σ ∈ Icc (perronLeftEdge R) 2)
    (ht : |t| ≤ R^2+1) : Real.log (‖(σ : ℂ)+t*I‖+3) ≤ 4*Real.log R := by
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) (norm_box hR hσ ht)

/-- There are symmetric horizontal heights in `(R²,R²+1)` missing every zero. For all
large `R`, both horizontal edges have logarithmic derivative `O(log² R)`, while the
whole negative odd vertical edge has logarithmic derivative `O(log R)`. -/
theorem exists_expandingPerron_heights :
    ∃ (U : ℝ → ℝ) (C : ℝ), 0 < C ∧ ∀ᶠ R : ℝ in atTop,
      R^2 < U R ∧ U R < R^2+1 ∧
      (∀ z ∈ nontrivialZerosUpTo (U R), |z.im| ≠ U R) ∧
      (∀ σ ∈ Icc (perronLeftEdge R) 2, ∀ t : ℝ, |t|=U R →
        ‖logDeriv riemannZeta ((σ : ℂ)+t*I)‖ ≤ C*(Real.log R)^2) ∧
      (∀ t : ℝ, |t| ≤ U R →
        ‖logDeriv riemannZeta ((perronLeftEdge R : ℂ)+t*I)‖ ≤ C*Real.log R) := by
  obtain ⟨c,hc,hgood⟩ := exists_good_T_avoiding_zeros
  obtain ⟨A,hA,hleft⟩ := norm_logDeriv_zeta_left_edges
  obtain ⟨B,hB,hstrip⟩ := norm_neg_logDeriv_zeta_avoiding_le
  choose U hl hh hgap using (fun R : ℝ => hgood (max 2 (R^2)) (le_max_left ..))
  let k := min c 1
  have hk : 0 < k := lt_min hc zero_lt_one
  let C := (20+A)+8*B/k
  have hC₁ : 20+A ≤ C := le_add_of_nonneg_right (by positivity)
  have hC₂ : 8*B/k ≤ C := by dsimp [C]; linarith
  refine ⟨U, C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 3 (Real.exp 1))] with R hR₀
  have hR := (le_max_left ..).trans hR₀
  have hlog : 1 ≤ Real.log R := (Real.le_log_iff_exp_le (by linarith)).mpr ((le_max_right ..).trans hR₀)
  have hsq : 2 ≤ R^2 := by nlinarith
  have hU := hl R
  have hU' := hh R
  have hsep := hgap R
  rw [max_eq_right hsq] at hU hU' hsep
  have hRpos : 0 < R := by linarith
  have hlogpos : 0 < Real.log R := by linarith
  let δ := k/(2*Real.log R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [min_le_right c (1 : ℝ)]
  have hgap' {z : ℂ} (hz : riemannZeta z = 0) (h₀ : 0<z.re) (h₁ : z.re<1) :
      δ ≤ abs (|z.im|-U R) := by
    have H := hsep z hz h₀ h₁
    rw [Real.log_pow, Nat.cast_ofNat] at H
    exact (div_le_div_of_nonneg_right (min_le_left c 1) (by positivity)).trans H
  have hslog {σ t : ℝ} (hs : σ ∈ Icc (perronLeftEdge R) 2) (ht : |t| ≤ U R) (hle : σ ≤ -1/2)
      (he : 1 ≤ |t| ∨ ∃ n : ℕ, σ= -(2*n+1 : ℝ)) :
      ‖logDeriv riemannZeta ((σ : ℂ)+t*I)‖ ≤ (20+A)*Real.log R := by
    apply (hleft (s := (σ : ℂ)+t*I) (by simpa using hle) (by simpa using he)).trans
    have hb := log_box hR hs (ht.trans hU'.le)
    nlinarith [mul_le_mul_of_nonneg_left hlog hA.le]
  refine ⟨hU, hU', ?_, ?_, ?_⟩
  · intro z hz he
    obtain ⟨hz',h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
    have H := hgap' hz' h₀ h₁
    rw [he,sub_self,abs_zero] at H
    linarith
  · intro σ hσ t ht
    by_cases hle : σ ≤ -1/2
    · apply (hslog hσ ht.le hle (Or.inl (by linarith))).trans
      apply (mul_le_mul_of_nonneg_right hC₁ hlogpos.le).trans
      exact mul_le_mul_of_nonneg_left (by nlinarith : Real.log R ≤ (Real.log R)^2) (by dsimp [C]; positivity)
    · have H := (hstrip σ t δ (le_of_not_ge hle) (by linarith [hσ.2]) (by linarith) hδ hδ'
        (fun z hz h₀ h₁ => (hgap' hz h₀ h₁).trans (by
          rw [←ht, abs_sub_comm |z.im|, abs_sub_comm t z.im]
          simpa only [abs_sub_comm] using abs_abs_sub_abs_le_abs_sub z.im t))).2
      have hlg : Real.log (|t|+2) ≤ 4*Real.log R := by
        rw [ht]
        have hb : U R+2 ≤ R^4 := by nlinarith [sq_nonneg (R^2-3)]
        simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by linarith : 0<U R+2) hb
      rw [neg_div, norm_neg, ← logDeriv_apply] at H
      apply H.trans
      calc
        _ ≤ B*(1/δ)*(4*Real.log R) := mul_le_mul_of_nonneg_left hlg (by positivity)
        _ = (8*B/k)*(Real.log R)^2 := by dsimp [δ]; field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC₂ (sq_nonneg _)
  · intro t ht
    have he := (perronLeftEdge_bounds hR).1
    have H := hslog (σ := perronLeftEdge R) ⟨le_rfl, by linarith⟩ ht (by linarith)
      (Or.inr ⟨⌈R⌉₊, rfl⟩)
    exact H.trans (mul_le_mul_of_nonneg_right hC₁ hlogpos.le)

end AnalyticNumberTheory.PrimeDistribution
