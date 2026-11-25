import AnalyticNumberTheory.RiemannZeta.ZeroFreeRegion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Littlewood's enlargement of the classical zero-free region

An arbitrarily small ratio between the growth exponent and the width of a strip gives
a zero-free region of width `B/log |t|` for every fixed `B` at sufficiently large height.
The radii in Landau's logarithmic derivative estimate are the widths of the available strips.
-/

open Complex Real Filter Metric Set
open scoped Topology Asymptotics
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

/-- Arbitrarily small zeta growth exponents relative to the width of a fixed strip. -/
def LittlewoodStripGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧
    ∀ᶠ T : ℝ in atTop, ∀ z : ℂ, 1-η ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → |z.im| ≤ 3*T →
      ‖riemannZeta z‖ ≤ T^(ε*η)

private noncomputable def center (h y : ℝ) : ℂ := ((1+h:ℝ):ℂ)+y*I

private theorem center_re (h y : ℝ) : (center h y).re = 1+h := by simp [center]
private theorem center_im (h y : ℝ) : (center h y).im = y := by simp [center]

private theorem disk_bound {ε R h u y : ℝ} (hε : 0 < ε) (hR : 0 < R) (hR' : R ≤ 1/4)
    (hh : 0 < h) (hh' : h ≤ 1/4) (hu : 4 ≤ u) (hy₁ : u ≤ |y|) (hy₂ : |y| ≤ 2*u)
    (hg : ∀ z : ℂ, 1-R ≤ z.re → z.re ≤ 2 → 3*u/4 ≤ |z.im| → |z.im| ≤ 3*(3*u/4) →
      ‖riemannZeta z‖ ≤ (3*u/4)^(ε*R)) (hinv : 2/h ≤ u^(ε*R)) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (center h y) R) ∧ riemannZeta (center h y) ≠ 0 ∧
      ∀ w ∈ sphere (center h y) R, ‖riemannZeta w/riemannZeta (center h y)‖ ≤ u^(2*(ε*R)) := by
  have hdist (w : ℂ) (hw : w ∈ closedBall (center h y) R) :
      |w.re-(1+h)| ≤ R ∧ |w.im-y| ≤ R := by
    have hd : ‖w-center h y‖ ≤ R := by simpa [mem_closedBall,dist_eq_norm] using hw
    exact ⟨by simpa only [Complex.sub_re,center_re] using (Complex.abs_re_le_norm (w-center h y)).trans hd,
      by simpa only [Complex.sub_im,center_im] using (Complex.abs_im_le_norm (w-center h y)).trans hd⟩
  have him (w : ℂ) (hw : w ∈ closedBall (center h y) R) : 3*u/4 ≤ |w.im| ∧ |w.im| ≤ 3*(3*u/4) := by
    have hab := abs_sub_abs_le_abs_sub w.im y
    have hba := abs_sub_abs_le_abs_sub y w.im
    rw [abs_sub_comm y w.im] at hba
    have hd := (hdist w hw).2
    constructor <;> linarith
  have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hnoPole : ∀ w ∈ closedBall (center h y) R, w ≠ 1 := by
    intro w hw he
    have := (him w hw).1
    rw [he,Complex.one_im,abs_zero] at this
    linarith
  have hcn := riemannZeta_ne_zero_of_one_lt_re (s := center h y) (by rw [center_re]; linarith)
  refine ⟨(hdiff.analyticOnNhd isOpen_ne).mono hnoPole,hcn,?_⟩
  intro w hw
  have hcb := Metric.sphere_subset_closedBall hw
  have hr := abs_le.mp (hdist w hcb).1
  have hm := him w hcb
  have hw' := hg w (by linarith [hr.1]) (by linarith [hr.2]) hm.1 hm.2
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 3*u/4) (by linarith : 3*u/4 ≤ u) (mul_nonneg hε.le hR.le)
  have hlow : h/2 ≤ ‖riemannZeta (center h y)‖ := by
    have H := norm_riemannZeta_ge_of_one_lt_re (σ := 1+h) (by linarith) y
    change (1+h-1)/(1+h) ≤ ‖riemannZeta (center h y)‖ at H
    rw [show 1+h-1=h by ring] at H
    exact (div_le_div_of_nonneg_left hh.le (by linarith) (by linarith)).trans H
  rw [norm_div,show 2*(ε*R) = ε*R+ε*R by ring,Real.rpow_add (by linarith : 0 < u)]
  calc _ ≤ u^(ε*R)/(h/2) := div_le_div₀ (by positivity) (hw'.trans hpow) (by positivity) hlow
       _ = u^(ε*R)*(2/h) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

private theorem local_zero_inequality {h R M t β : ℝ} (hh : 0 < h) (hR : 0 < R)
    (hβ : β < 1) (hnear : 1+h-β ≤ R/2) (hzer : riemannZeta ((β:ℂ)+t*I) = 0)
    (hdisc : ∀ y : ℝ, y = t ∨ y = 2*t →
      AnalyticOnNhd ℂ riemannZeta (closedBall (center h y) R) ∧ riemannZeta (center h y) ≠ 0 ∧
      ∀ w ∈ sphere (center h y) R, ‖riemannZeta w/riemannZeta (center h y)‖ ≤ M)
    {C : ℝ} (hpole : (-deriv riemannZeta ((1+h:ℝ):ℂ)/riemannZeta ((1+h:ℝ):ℂ)).re ≤ 1/h+C) :
    4/(1+h-β) ≤ 3/h+3*C+20/R*Real.log M := by
  let ρ := (β:ℂ)+t*I
  have hmem : ρ ∈ closedBall (center h t) (R/2) := by
    rw [mem_closedBall,dist_eq_norm]
    have he : ρ-center h t = ((β-(1+h):ℝ):ℂ) := by dsimp [ρ,center]; push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hz (y : ℝ) (w : ℂ) (_ : w ∈ closedBall (center h y) (R/2)) (hw : riemannZeta w=0) :
      w.re ≤ (center h y).re := by
    have hr : w.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hw
    rw [center_re]; linarith
  obtain ⟨ha,hn,hb⟩ := hdisc t (Or.inl rfl)
  obtain ⟨ha',hn',hb'⟩ := hdisc (2*t) (Or.inr rfl)
  have h₁ := landau_neg_re_logDeriv_center_le_sub_zero hR ha hn hb (hz t) hmem hzer
  have h₂ := landau_neg_re_logDeriv_center_le hR ha' hn' hb' (hz (2*t))
  have hi : ((center h t-ρ)⁻¹).re = 1/(1+h-β) := by
    have he : center h t-ρ = ((1+h-β:ℝ):ℂ) := by dsimp [center,ρ]; push_cast; ring
    rw [he,← Complex.ofReal_inv,Complex.ofReal_re,one_div]
  have hld (z : ℂ) : -(logDeriv riemannZeta z).re = (-deriv riemannZeta z/riemannZeta z).re := by
    rw [logDeriv_apply,neg_div,Complex.neg_re]
  rw [hld,hi] at h₁
  rw [hld] at h₂
  have h3 := three_neg_logDeriv_add_four_add_nonneg (σ := 1+h) (by linarith) t
  have he : center h (2*t) = ((1+h:ℝ):ℂ)+2*(t:ℂ)*I := by dsimp [center]; push_cast; ring
  rw [he] at h₂
  dsimp only [center] at h₁
  calc 4/(1+h-β) = 4*(1/(1+h-β)) := by ring
       _ ≤ 3*(1/h+C) + 5*(4/R*Real.log M) := by linarith only [hpole,h₁,h₂,h3]
       _ = _ := by ring

/-- A fixed arbitrary multiple of the classical `1/log |t|` width is zero-free above a
sufficiently large height under the weak strip-growth hypothesis. -/
theorem littlewood_zero_free_of_stripGrowth (hg : LittlewoodStripGrowth) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ T : ℝ in atTop, ∀ σ t : ℝ, T ≤ |t| → 1-B/Real.log |t| ≤ σ →
      riemannZeta ((σ:ℂ)+t*I) ≠ 0 := by
  let ε := 1/(4000*B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R,hR,hR',hgR⟩ := hg ε hε
  obtain ⟨C,hC,hpole⟩ := neg_logDeriv_riemannZeta_one_add_le
  have hscale : Tendsto (fun u : ℝ => 3*u/4) atTop atTop := by
    have H : Tendsto (fun u : ℝ => (3/4)*u) atTop atTop := (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<3/4)).mpr tendsto_id
    exact H.congr fun u => by ring
  have hlog := (isLittleO_log_rpow_atTop (mul_pos hε hR)).bound (by positivity : 0 < 5*B)
  have hsmall : Tendsto (fun u : ℝ => 10*B/Real.log u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hevent : ∀ᶠ u : ℝ in atTop, ∀ σ t : ℝ, |t|=u → 1-B/Real.log u ≤ σ → riemannZeta ((σ:ℂ)+t*I) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (4:ℝ),Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ)),
      hscale.eventually hgR,hlog,hsmall.eventually_lt_const (by linarith : 0 < R/4),
      hsmall.eventually_lt_const (by positivity : 0 < 1/(30*C))] with u hu hL hstrip hlg hsmallR hsmallC
    intro σ t ht hσ
    by_cases hβ : 1 ≤ σ
    · apply riemannZeta_ne_zero_of_one_le_re; simpa using hβ
    intro hzero
    let L := Real.log u
    let h := 10*B/L
    have hh : 0 < h := div_pos (by positivity) hL
    have hhr : h ≤ 1/4 := by dsimp [h,L]; linarith
    let M := u^(2*(ε*R))
    have hinv : 2/h ≤ u^(ε*R) := by
      rw [Real.norm_of_nonneg hL.le,Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0≤u) _)] at hlg
      dsimp only [h]
      have he : 2/(10*B/L) = L/(5*B) := by field_simp [(show 0 < L from hL).ne',hB.ne']; ring
      rw [he,div_le_iff₀ (by positivity)]
      exact hlg.trans_eq (by ring)
    have hd : ∀ y : ℝ, y = t ∨ y = 2*t →
        AnalyticOnNhd ℂ riemannZeta (closedBall (center h y) R) ∧ riemannZeta (center h y) ≠ 0 ∧
        ∀ w ∈ sphere (center h y) R, ‖riemannZeta w/riemannZeta (center h y)‖ ≤ M := by
      intro y hy
      apply disk_bound hε hR hR' hh hhr hu _ _ hstrip hinv
      · rcases hy with rfl | rfl
        · exact ht.ge
        · rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),ht]; linarith
      · rcases hy with rfl | rfl
        · rw [ht]; linarith
        · rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),ht]
    have hrel : B/Real.log u = h/10 := by dsimp [h,L]; ring
    rw [hrel] at hσ
    have hdif : 1+h-σ ≤ R/2 := by change h < R/4 at hsmallR; linarith
    have H := local_zero_inequality hh hR (lt_of_not_ge hβ) hdif hzero hd (hpole hh (by linarith))
    have hu0 : 0 < u := by linarith
    rw [show Real.log M = 2*(ε*R)*L by dsimp only [M,L]; rw [Real.log_rpow hu0]] at H
    have hp : 3*C*h ≤ 1/10 := by
      change h < 1/(30*C) at hsmallC
      have hc := (lt_div_iff₀ (by positivity : 0 < 30*C)).mp hsmallC
      linarith
    have hk : (20/R*(2*(ε*R)*L))*h = 1/10 := by dsimp only [h,ε]; field_simp [(show 0 < L from hL).ne',hB.ne',hR.ne']; ring
    have hpos : 0 < 1+h-σ := by linarith
    have hden : 1+h-σ ≤ 11*h/10 := by linarith
    have hfrac : (40/11:ℝ)/h ≤ 4/(1+h-σ) := by
      apply (div_le_div₀ (by norm_num : (0:ℝ) ≤ 4) le_rfl hpos hden).trans_eq'
      ring
    have H' := mul_le_mul_of_nonneg_right (hfrac.trans H) hh.le
    rw [add_mul,add_mul,hk,div_mul_cancel₀ _ hh.ne',div_mul_cancel₀ _ hh.ne'] at H'
    linarith
  obtain ⟨T,hT⟩ := eventually_atTop.mp hevent
  filter_upwards [eventually_ge_atTop T] with T' hT'
  intro σ t ht hσ
  exact hT |t| (hT'.trans ht) σ t rfl hσ

end AnalyticNumberTheory.RiemannZeta
