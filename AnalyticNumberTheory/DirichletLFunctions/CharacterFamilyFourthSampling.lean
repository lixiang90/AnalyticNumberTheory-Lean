import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthStrips
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogarithmicFourthMeans

/-!
# Derivative means and separated samples for character families

Both estimates use the same summed critical-line input. Different
characters may be sampled at different sets of positive and negative ordinates.
-/

open Real Complex Set Finset MeasureTheory
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem half_le_log_height {q : ℕ} [NeZero q] {T : ℝ} (hT : 2≤T) : 1/2≤Real.log ((q:ℝ)*T) := by
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  exact (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num)
    (hT.trans (by simpa using mul_le_mul_of_nonneg_right hq (show 0≤T by linarith))))

/-- Symmetric fourth moment of the derivatives, with a uniform constant for
all moduli and all finite character families satisfying the same input bound. -/
theorem character_family_deriv_fourth_narrow_symmetric {D : ℝ} (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)),
      CharacterFamilyCriticalFourthBound S D → ∀ {T σ : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log (q*T)) →
      (∑χ∈S,∫ t in -T..T,‖deriv χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q.totient*T*(Real.log (q*T))^8 := by
  obtain ⟨A,hA,H⟩ := character_family_fourth_narrow_window hD
  refine ⟨400^4*A,by positivity,?_⟩
  intro q _ S hS T σ hT hσ
  have hlog := half_le_log_height (q:=q) hT
  have hh := family_deriv_fourth_logarithmic_strip S (fun χ => χ.LFunction) hlog hT hσ
    (fun χ _ _ hz => analyticAt_LFunction_re_lt_one χ hz) (fun u hu => H S hS hT hu)
  exact hh.trans_eq (by ring)

/-- Positive-height derivative estimate in the logarithmically narrow strip. -/
theorem character_family_deriv_fourth_narrow_strip {D : ℝ} (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)),
      CharacterFamilyCriticalFourthBound S D → ∀ {T σ : ℝ},2≤T → |σ-1/2|≤1/(400*Real.log (q*T)) →
      (∑χ∈S,∫ t in (0:ℝ)..T,‖deriv χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q.totient*T*(Real.log (q*T))^8 := by
  obtain ⟨A,hA,H⟩ := character_family_deriv_fourth_narrow_symmetric hD
  refine ⟨A,hA,?_⟩
  intro q _ S hS T σ hT hσ
  have hlog := half_le_log_height (q:=q) hT
  have hbound : 1/(400*Real.log ((q:ℝ)*T))≤1/4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hs : σ<1 := by linarith [(abs_le.mp hσ).2]
  apply (Finset.sum_le_sum (fun χ hi => ?_)).trans (H S hS hT hσ)
  have hc : Continuous (fun t : ℝ => deriv χ.LFunction ((σ:ℂ)+t*I)) := continuous_iff_continuousAt.mpr (fun t =>
    (analyticAt_LFunction_re_lt_one χ (z:=(σ:ℂ)+t*I) (by simpa using hs)).deriv.continuousAt.comp
      (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop))
  exact intervalIntegral.integral_mono_interval (by linarith : -T≤0) (by linarith) le_rfl
    (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) ((hc.norm.pow 4).intervalIntegrable ..)

/-- Discrete fourth moments for arbitrary separated height sets, chosen
independently for every character of the family. -/
theorem character_family_fourth_separated {D : ℝ} (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)),
      CharacterFamilyCriticalFourthBound S D → ∀ {T δ : ℝ},2≤T → 0<δ →
      ∀ (E : DirichletCharacter ℂ q→Finset ℝ),
      (∀ χ∈S,∀ t∈E χ,|t|≤T) → (∀ χ∈S,∀ t∈E χ,∀ u∈E χ,t≠u → δ≤|t-u|) →
      (∑χ∈S,∑t∈E χ,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤C*(δ⁻¹+Real.log (q*T))*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨A,hA,HA⟩ := character_family_fourth_narrow_window hD
  obtain ⟨B,hB,HB⟩ := character_family_deriv_fourth_narrow_symmetric hD
  refine ⟨5*A+512*B,by positivity,?_⟩
  intro q _ S hS T δ hT hδ E hE hsep
  let X := (q:ℝ)*T
  let L := Real.log X
  have hlog : 1/2≤L := half_le_log_height (q:=q) hT
  have hL : 0<L := by linarith
  have hh := HA S hS (σ:=1/2) hT (by simp;positivity [show 0<Real.log ((q:ℝ)*T) from hL])
  have h₂T : 2≤2*T := by linarith
  have hh' := HB S hS (σ:=1/2) h₂T (by simp;positivity [show 0<Real.log ((q:ℝ)*(2*T)) by linarith [half_le_log_height (q:=q) h₂T]])
  push_cast at hh hh'
  have hid : (q:ℝ)*(2*T)=2*X := by dsimp [X];ring
  have hx : 1≤X := one_le_mul_of_one_le_of_one_le (by exact_mod_cast NeZero.pos q) (by linarith)
  have hx' := zero_lt_one.trans_le hx
  have hlog' : Real.log ((q:ℝ)*(2*T))≤2*L := by
    rw [hid,Real.log_mul (by norm_num) hx'.ne'];dsimp [L]
    have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
    exact (by linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) (hT.trans (by simpa using mul_le_mul_of_nonneg_right hq (show 0≤T by linarith)))])
  have hL' := pow_le_pow_left₀ (by rw [hid];exact Real.log_nonneg (by linarith) : 0≤Real.log ((q:ℝ)*(2*T))) hlog' 8
  rw [mul_pow] at hL'
  have hG := hh'.trans (mul_le_mul_of_nonneg_left hL' (by positivity : 0≤B*q.totient*(2*T)))
  have hresult := family_fourth_separated_of_means S (fun χ => χ.LFunction) E hlog hT hδ
    (by positivity : 0≤A*q.totient*T) (by positivity : 0≤512*B*q.totient*T)
    (fun χ _ t => analyticAt_LFunction_re_lt_one χ (by simp;norm_num)) hE hsep hh (hG.trans_eq (by ring))
  exact hresult.trans_eq (by dsimp [L,X];ring)

end AnalyticNumberTheory.DirichletLFunctions
