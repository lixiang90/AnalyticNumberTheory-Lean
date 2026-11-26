import AnalyticNumberTheory.AdditiveNumberTheory.ExceptionalGaussWeights
import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterFourierFormula
import AnalyticNumberTheory.AdditiveNumberTheory.ShiftedCharacterExpansion
import AnalyticNumberTheory.PrimeDistribution.PrincipalCharacterMainTerm

/-! # A uniform major-arc estimate with a possible exceptional character -/

noncomputable section

open Real Finset
open AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

/-- Below the exponential square-root-logarithmic conductor cutoff, the
principal and possible exceptional terms share the same Fourier decay.
The upper scale x, the arithmetic endpoint y and the frequency shift z are
independent. The error is explicit even for shifts outside the major arc. -/
theorem primeExpSum_small_denominator_expansion :
    ∃ κ b A : ℝ, 0 < κ ∧ κ ≤ 1/4 ∧ 0 < b ∧ 0 < A ∧
      ∀ {x y : ℝ} {q a : ℕ} [NeZero q], 2 ≤ x → (q : ℝ) ≤ Real.exp (κ*Real.sqrt (Real.log x)) →
        a.Coprime q → 1 ≤ y → y ≤ x → ∀ z : ℝ,
        ‖primeExpSum y ((a : ℝ)/q+z)‖ ≤ A*(
          Real.log (Real.log (10*q))/Real.sqrt q*(y/(1+y*|z|)) +
          q*x*Real.exp (-b*Real.sqrt (Real.log x))*(1+2*Real.pi*y*|z|)) := by
  obtain ⟨κ,C,hκ,hκ4,hC,H⟩ := page_characterPrimeSum_explicit
  obtain ⟨b₀,P,hb₀,hP,HP⟩ := principal_psi_sub_linear_uniform_exp
  obtain ⟨G,hG,HG⟩ := rationalCharacterCoefficient_loglog
  let b := min (κ/2) b₀
  have hb : 0 < b := lt_min (half_pos hκ) hb₀
  let D := C+P
  let K := (16/Real.log 2)*Real.exp (b^2/2)
  let A := 4*G+D+K
  have hD : 0 < D := add_pos hC hP
  have hK : 0 < K := by dsimp only [K]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨κ,b,A,hκ,hκ4,hb,hA,?_⟩
  intro x y q a _ hx hq ha hy hyx z
  let u := Real.sqrt (Real.log x)
  have hx₁ := hy.trans hyx
  have hx₀ := zero_lt_one.trans_le hx₁
  have hy₀ := zero_lt_one.trans_le hy
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq₁
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have huκ : κ ≤ u := hκ4.trans (Real.le_sqrt_of_sq_le (by
    linarith only [Real.log_two_gt_d9, Real.log_le_log (by norm_num : (0:ℝ)<2) hx]))
  have hqx : (q : ℝ) ≤ x := hq.trans ((Real.exp_le_exp.mpr
    ((mul_le_mul_of_nonneg_right huκ hu).trans_eq (by rw [←sq,Real.sq_sqrt (Real.log_nonneg hx₁)]))).trans_eq
    (Real.exp_log hx₀))
  let S := x*Real.exp (-b*u)
  let F := 1+2*Real.pi*y*|z|
  let E := D*S*F
  let M := 2*y/(1+y*|z|)
  let L := Real.log (Real.log (10*(q : ℝ)))
  let B := G*L/Real.sqrt q
  have hS : 0 < S := mul_pos hx₀ (Real.exp_pos _)
  have hF : 1 ≤ F := le_add_of_nonneg_right (by positivity)
  have hF₀ := zero_lt_one.trans_le hF
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hL : 0 ≤ L := Real.log_nonneg ((Real.le_log_iff_exp_le
    (by positivity : 0 < 10*(q:ℝ))).mpr (Real.exp_one_lt_d9.le.trans (by linarith only [hq₁])))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hscale {V d : ℝ} (hVD : V ≤ D) (hbd : b ≤ d) :
      V*x*Real.exp (-d*u) ≤ D*S := by
    rw [show D*S = (D*x)*Real.exp (-b*u) by dsimp only [S]; ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hVD hx₀.le)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hbd) hu))
      (Real.exp_pos _).le (mul_nonneg hD.le hx₀.le)
  have hPscale := hscale (show P ≤ D by dsimp [D]; linarith only [hC]) (min_le_right (κ/2) b₀)
  have hCscale := hscale (show C ≤ D by dsimp [D]; linarith only [hP]) (min_le_left (κ/2) b₀)
  let f (χ : DirichletCharacter ℂ q) := characterPrimeSum χ ⌊y⌋₊ z
  have hmodel {v w : ℂ} (herr : ‖v-w‖ ≤ E) (hw : ‖w‖ ≤ M) : ‖v‖ ≤ E+M := by
    calc ‖v‖ = ‖(v-w)+w‖ := by rw [sub_add_cancel]
         _ ≤ _ := (norm_add_le _ _).trans (add_le_add herr hw)
  have hprin : ‖f 1‖ ≤ E+M := by
    apply hmodel (w:=powerWeightFourierIntegral 1 y z) _ (norm_powerWeightFourierIntegral_le le_rfl hy z)
    have h := characterPrimeSum_sub_powerWeight (1 : DirichletCharacter ℂ q) hy
      (β:=1) zero_lt_one 1 (E:=D*S) (fun t ht => by
        simpa only [Real.rpow_one, div_one, one_mul] using (HP hx hqx ht.1 (ht.2.trans hyx)).trans hPscale) z
    simpa only [f, E, F, one_mul] using h
  obtain ⟨e₀, he⟩ := H hx
  have hnon (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1) :
      ‖f χ‖ ≤ E ∨
      ((⟨χ.conductor,χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) = e₀ ∧ ‖f χ‖ ≤ E+M) := by
    rcases he hq hn with hall | ⟨hpair,β,_,hβ,_,_,_,hall⟩
    · exact Or.inl ((hall hy hyx z).trans (mul_le_mul_of_nonneg_right hCscale hF₀.le))
    · refine Or.inr ⟨hpair,hmodel (w := -powerWeightFourierIntegral β y z) ?_ ?_⟩
      · simpa only [sub_neg_eq_add] using (hall hy hyx z).trans (mul_le_mul_of_nonneg_right hCscale hF₀.le)
      · rw [norm_neg]
        exact norm_powerWeightFourierIntegral_le hβ.le hy z
  have hsum := norm_sum_rationalCharacterCoefficient_exceptional a e₀ f hB hE hM
    (fun χ => (HG χ ha).2) (fun χ => by
      by_cases h : χ = 1
      · simpa only [h] using hprin
      · exact (hnon χ h).elim (fun hl => hl.trans (le_add_of_nonneg_right hM)) (fun hh => hh.2))
    (fun χ hn hne => (hnon χ hn).elim id (fun hh => (hne hh.1).elim))
  have hram := norm_primeExpSum_shift_sub_character_expansion (q:=q) hy a z
  let U := (q : ℝ)*S*F
  let V := L/Real.sqrt q*(y/(1+y*|z|))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hSU : S ≤ U := (le_mul_of_one_le_left hS.le hq₁).trans (le_mul_of_one_le_right
    (mul_nonneg hq₀.le hS.le) hF)
  have hr : (Real.log q/Real.log 2)*Real.log y ≤ K*U := by
    apply (log_modulus_partial_le_sqrt hy hyx hqx).trans
    calc _ ≤ (16/Real.log 2)*(Real.exp (b^2/2)*x*Real.exp (-b*u)) :=
             mul_le_mul_of_nonneg_left (sqrt_le_exp_sqrtLog_error hx₁ b) (by positivity)
         _ = K*S := by dsimp only [K,S]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hSU hK.le
  have htot : (q.totient : ℝ)*E ≤ D*U := by
    calc _ ≤ (q : ℝ)*E := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) hE
         _ = _ := by dsimp only [E,U]; ring
  have hmain : 2*B*M = 4*G*V := by dsimp only [B,M,V]; ring
  let Z := ∑ χ : DirichletCharacter ℂ q, rationalCharacterCoefficient χ a*f χ
  have htri := norm_add_le (primeExpSum y ((a : ℝ)/q+z) - Z) Z
  rw [sub_add_cancel] at htri
  apply htri.trans ((add_le_add (hram.trans hr) hsum).trans ?_)
  rw [hmain]
  change _ ≤ A*(V+(q : ℝ)*x*Real.exp (-b*u)*F)
  rw [show V+(q : ℝ)*x*Real.exp (-b*u)*F = V+U by dsimp only [U,S]; ring]
  have h₁ : D+K ≤ A := by dsimp only [A]; linarith only [hG]
  have h₂ : 4*G ≤ A := by dsimp only [A]; linarith only [hD,hK]
  nlinarith only [htot, mul_le_mul_of_nonneg_right h₁ hU, mul_le_mul_of_nonneg_right h₂ hV]

end AnalyticNumberTheory.ExponentialSums
