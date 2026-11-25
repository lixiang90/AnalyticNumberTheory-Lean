import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.NeighboringFourthMeans
import AnalyticNumberTheory.AnalyticTools.FourthMomentSampling

/-!
# Logarithmic derivative losses and separated fourth moments

The scale `L` can be the logarithm of any analytic conductor. The bounds
are for finite analytic families and permit independent sample sets.
-/

open Real Complex Set Finset MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- A symmetric strip of width `1/(200L)` controls the fourth moment of
the derivatives in the half-width strip, with a loss of `(400L)^4`. -/
theorem family_deriv_fourth_logarithmic_strip {ι : Type*} (S : Finset ι) (f : ι→ℂ→ℂ)
    {L T σ M : ℝ} (hlog : 1/2≤L) (hT : 2≤T) (hσ : |σ-1/2|≤1/(400*L))
    (hf : ∀ i∈S,∀ z : ℂ,z.re<1 → AnalyticAt ℂ (f i) z)
    (hM : ∀ u : ℝ,|u-1/2|≤1/(200*L) →
      (∑i∈S,∫ t in -(2*T)..2*T,‖f i ((u:ℂ)+t*I)‖^4)≤M) :
    (∑i∈S,∫ t in -T..T,‖deriv (f i) ((σ:ℂ)+t*I)‖^4)≤400^4*M*L^4 := by
  have hL : 0<L := by linarith
  let r := 1/(400*L)
  have hr : 0<r := by dsimp [r];positivity
  have hr₁ : r≤1/8 := (div_le_iff₀ (by positivity : 0<400*L)).mpr (by linarith)
  have hσ' : |σ-1/2|≤r := hσ
  have hh := family_deriv_fourth_le_of_neighboring_lines (σ:=σ) (r:=r) (T:=T) (M:=M) S f hr (by linarith : r≤T)
    (fun i hi z hz => hf i hi z (by linarith [(abs_le.mp hz).2,(abs_le.mp hσ').2]))
    (fun u hu => hM u (by
      calc |u-1/2|=|(u-σ)+(σ-1/2)| := by ring_nf
           _ ≤ |u-σ|+|σ-1/2| := abs_add_le ..
           _ ≤ r+r := add_le_add hu hσ'
           _ = _ := by dsimp [r];ring))
  exact hh.trans_eq (by dsimp [r];field_simp)

/-- From joint fourth-moment bounds for a family and its derivatives on
the doubled height window, obtain a discrete bound with the spacing
factor `δ⁻¹+L`. Each family member may use different ordinates. -/
theorem family_fourth_separated_of_means {ι : Type*} (S : Finset ι) (v : ι→ℂ→ℂ) (E : ι→Finset ℝ)
    {L T δ A B : ℝ} (hlog : 1/2≤L) (hT : 2≤T) (hδ : 0<δ) (hA : 0≤A) (hB : 0≤B)
    (hf : ∀ i∈S,∀ t : ℝ,AnalyticAt ℂ (v i) ((1/2:ℂ)+t*I))
    (hE : ∀ i∈S,∀ t∈E i,|t|≤T) (hsep : ∀ i∈S,∀ t∈E i,∀ u∈E i,t≠u → δ≤|t-u|)
    (hF : (∑i∈S,∫ t in -(2*T)..2*T,‖v i ((1/2:ℂ)+t*I)‖^4)≤A*L^4)
    (hG : (∑i∈S,∫ t in -(2*T)..2*T,‖deriv (v i) ((1/2:ℂ)+t*I)‖^4)≤B*L^8) :
    (∑i∈S,∑t∈E i,‖v i ((1/2:ℂ)+t*I)‖^4)≤(5*A+B)*(δ⁻¹+L)*L^4 := by
  have hL : 0<L := by linarith
  let w := min δ 1
  have hw : 0<w := lt_min hδ zero_lt_one
  have hwδ : w≤δ := min_le_left ..
  have hw₁ : w≤1 := min_le_right ..
  have hwinv : w⁻¹≤δ⁻¹+2*L := by
    dsimp [w];rcases le_or_gt δ 1 with hd|hd
    · rw [min_eq_left hd];linarith
    · rw [min_eq_right hd.le,inv_one];linarith [inv_pos.mpr hδ]
  let s (t : ℝ) := (1/2:ℂ)+t*I
  let F (χ : ι) := ∫ t in -(2*T)..2*T, ‖v χ (s t)‖^4
  let G (χ : ι) := ∫ t in -(2*T)..2*T, ‖deriv (v χ) (s t)‖^4
  have hrow (χ : ι) (hχ : χ∈S) :
      (∑t∈E χ,‖v χ (s t)‖^4)≤(w⁻¹+3*L)*F χ+(L^3)⁻¹*G χ := by
    let f (t : ℝ) := v χ (s t)
    let g (t : ℝ) := deriv (v χ) (s t)*I
    have ha (t : ℝ) := hf χ hχ t
    have hf (t : ℝ) : HasDerivAt f (g t) t := by
      have hlin : HasDerivAt (fun z : ℂ => (1/2:ℂ)+z*I) I (t:ℂ) := by
        simpa using (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (1/2:ℂ))
      exact (((ha t).differentiableAt.hasDerivAt.comp (h:=fun z : ℂ => (1/2:ℂ)+z*I) (t:ℂ) hlin).comp_ofReal)
    have hg : Continuous g := (continuous_iff_continuousAt.mpr (fun t : ℝ => (ha t).deriv.continuousAt.comp
      (f:=s) (by dsimp [s];fun_prop))).mul continuous_const
    have hh := sum_fourth_separated_le (E χ) id hw (by linarith : -(2*T)≤2*T) hL
      (fun t ht u hu hne => hwδ.trans (hsep χ hχ t ht u hu hne)) (fun t ht => by
        change -(2*T)≤t-w/2 ∧ t+w/2≤2*T
        constructor <;> linarith [(abs_le.mp (hE χ hχ t ht)).1,(abs_le.mp (hE χ hχ t ht)).2]) hf hg
    simpa [F,G,f,g] using hh
  have hsum := Finset.sum_le_sum hrow
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hsum
  apply hsum.trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hF (by positivity : 0≤w⁻¹+3*L))
    (mul_le_mul_of_nonneg_left hG (by positivity : 0≤(L^3)⁻¹))).trans
  rw [show (L^3)⁻¹*(B*L^8)=B*L^5 by field_simp]
  have hb := mul_le_mul_of_nonneg_right (by linarith only [hwinv] : w⁻¹+3*L≤δ⁻¹+5*L) (by positivity : 0≤A*L^4)
  nlinarith only [hb,mul_nonneg (mul_nonneg hA (inv_pos.mpr hδ).le) (pow_nonneg hL.le 4),
    mul_nonneg (mul_nonneg hB (inv_pos.mpr hδ).le) (pow_nonneg hL.le 4)]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
