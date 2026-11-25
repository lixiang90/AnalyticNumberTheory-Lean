import AnalyticNumberTheory.RiemannZeta.FourthMomentDerivativeStrip
import AnalyticNumberTheory.AnalyticTools.FourthMomentSampling

/-!
# Fourth powers of zeta at separated ordinates

The spacing may vary with the height. The bound holds for any finite
set of ordinates on the positive and negative parts of the critical line.
-/

open Complex Real Set Finset MeasureTheory
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- Fourth powers at separated ordinates on a common vertical line in the strip of width `1/(800 log T)`. -/
theorem fourthMoment_riemannZeta_separated_narrow_strip :
    ∃ C : ℝ,0<C ∧ ∀ {T δ σ : ℝ},2≤T → 0<δ → |σ-1/2|≤1/(800*Real.log T) → ∀ (S : Finset ℝ),
      (∀ t∈S,|t|≤T) → (∀ t∈S,∀ u∈S,t≠u → δ≤|t-u|) →
      (∑ t∈S,‖riemannZeta ((σ:ℂ)+t*I)‖^4)≤C*(δ⁻¹+Real.log T)*T*(Real.log T)^4 := by
  obtain ⟨A,hA,HA⟩ := fourthMoment_riemannZeta_narrow_symmetric_window
  obtain ⟨B,hB,HB⟩ := fourthMoment_deriv_riemannZeta_narrow_symmetric
  refine ⟨5*A+512*B,by positivity,?_⟩
  intro T δ σ hT hδ hσ S hS hsep
  let L := Real.log T
  have hL : 1/2≤L := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have hLp : 0<L := by linarith
  let w := min δ 1
  have hw : 0<w := lt_min hδ zero_lt_one
  have hwδ : w≤δ := min_le_left ..
  have hw₁ : w≤1 := min_le_right ..
  have hwinv : w⁻¹≤δ⁻¹+2*L := by
    dsimp [w];rcases le_or_gt δ 1 with hd|hd
    · rw [min_eq_left hd];linarith
    · rw [min_eq_right hd.le,inv_one];linarith [inv_pos.mpr hδ]
  have h200 : |σ-1/2|≤1/(200*Real.log T) := hσ.trans (one_div_le_one_div_of_le (by change 0<200*L;positivity) (by change 200*L≤800*L;linarith))
  have hsmall : |σ-1/2|≤1/4 := hσ.trans ((div_le_iff₀ (by change 0<800*L;positivity)).mpr (by change 1≤1/4*(800*L);linarith))
  let s (t : ℝ) := (σ:ℂ)+t*I
  let f (t : ℝ) := riemannZeta (s t)
  let g (t : ℝ) := deriv riemannZeta (s t)*I
  have hs (t : ℝ) : s t≠1 := by intro he; have h' := congrArg Complex.re he;simp [s] at h';linarith [(abs_le.mp hsmall).2]
  have ha (t : ℝ) : AnalyticAt ℂ riemannZeta (s t) :=
    DifferentiableOn.analyticOnNhd (s:={(1:ℂ)}ᶜ) (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
      isOpen_compl_singleton _ (hs t)
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    have hlin : HasDerivAt (fun z : ℂ => (σ:ℂ)+z*I) I (t:ℂ) := by
      simpa using (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (σ:ℂ))
    exact (((ha t).differentiableAt.hasDerivAt.comp (h:=fun z : ℂ => (σ:ℂ)+z*I) (t:ℂ) hlin).comp_ofReal)
  have hg : Continuous g := (continuous_iff_continuousAt.mpr (fun t : ℝ =>
    (ha t).deriv.continuousAt.comp (f:=s) (by dsimp [s];fun_prop))).mul continuous_const
  have hn (t : ℝ) : ‖g t‖=‖deriv riemannZeta (s t)‖ := by simp [g]
  have hh := sum_fourth_separated_le S id (a:=-(2*T)) (b:=2*T) hw (by linarith) hLp
    (fun t ht u hu hne => hwδ.trans (hsep t ht u hu hne)) (fun t ht => by
      change -(2*T)≤t-w/2 ∧ t+w/2≤2*T
      constructor <;> linarith [(abs_le.mp (hS t ht)).1,(abs_le.mp (hS t ht)).2]) hf hg
  have h₁ := HA hT h200
  have hlog : Real.log (2*T)≤2*L := by
    rw [Real.log_mul (by norm_num) (by linarith)];dsimp [L];linarith [Real.log_le_log (by norm_num) hT]
  have h₂ := HB (σ:=σ) (T:=2*T) (by linarith) (hσ.trans (one_div_le_one_div_of_le
    (by positivity [Real.log_pos (show 1<2*T by linarith)]) (by change 400*Real.log (2*T)≤800*L;linarith only [hlog])))
  have hlog' := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1≤2*T)) hlog 8
  rw [mul_pow] at hlog'
  have h₂' := h₂.trans (mul_le_mul_of_nonneg_left hlog' (by positivity : 0≤B*(2*T)))
  simp_rw [hn] at hh
  apply hh.trans
  apply (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity : 0≤w⁻¹+3*L))
    (mul_le_mul_of_nonneg_left h₂' (by positivity : 0≤(L^3)⁻¹))).trans
  change (w⁻¹+3*L)*(A*T*L^4)+(L^3)⁻¹*(B*(2*T)*(2^8*L^8))≤(5*A+512*B)*(δ⁻¹+L)*T*L^4
  rw [show (L^3)⁻¹*(B*(2*T)*(2^8*L^8))=512*B*T*L^5 by field_simp;ring]
  have hb := mul_le_mul_of_nonneg_right (by linarith only [hwinv] : w⁻¹+3*L≤δ⁻¹+5*L) (by positivity : 0≤A*T*L^4)
  nlinarith only [hb,mul_nonneg (by positivity : 0≤A*δ⁻¹*T) (pow_nonneg hLp.le 4),
    mul_nonneg (by positivity : 0≤B*δ⁻¹*T) (pow_nonneg hLp.le 4)]

/-- The discrete fourth moment at arbitrary `δ`-separated heights in
`[-T,T]` is `O((1/δ+log T) T log⁴ T)`, with one absolute constant. -/
theorem fourthMoment_riemannZeta_separated :
    ∃ C : ℝ,0<C ∧ ∀ {T δ : ℝ},2≤T → 0<δ → ∀ (S : Finset ℝ),
      (∀ t∈S,|t|≤T) → (∀ t∈S,∀ u∈S,t≠u → δ≤|t-u|) →
      (∑ t∈S,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)≤C*(δ⁻¹+Real.log T)*T*(Real.log T)^4 := by
  obtain ⟨C,hC,H⟩ := fourthMoment_riemannZeta_separated_narrow_strip
  refine ⟨C,hC,?_⟩
  intro T δ hT hδ S hS hsep
  simpa using H (σ:=1/2) hT hδ (by simp; positivity [Real.log_nonneg (show 1≤T by linarith)]) S hS hsep

end AnalyticNumberTheory.RiemannZeta
