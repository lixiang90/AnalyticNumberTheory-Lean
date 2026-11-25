import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovSmallConductors
import AnalyticNumberTheory.PrimeDistribution.PrimitiveConductorBlockSums

/-!
# Siegel–Walfisz estimates with independent endpoints

The conductor cutoff is given in terms of the upper endpoint x, while
each character sum may stop at a different y ≤ x. For y ≥ √x,
a doubled logarithmic exponent suffices in Siegel–Walfisz. The elementary
Chebyshev bound controls the complementary range.
-/
noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- Maximal Siegel–Walfisz character estimate, with the modulus cutoff
specified at x and the character sum maximized over all real y in [0,x]. -/
theorem maximalPsiCharNorm_siegelWalfisz {L : ℝ} (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∃ c : ℝ, 0<c ∧ ∀ {x : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q),
      2≤x → 1≤Real.log x → 1≤q → (q:ℝ)≤(Real.log x)^L → χ≠1 →
      maximalPsiCharNorm x χ≤C*x*Real.exp (-c*Real.sqrt (Real.log x)) := by
  obtain ⟨K,hK,γ,hγ,hsw⟩ := norm_psiChar_siegelWalfisz (2*L) (by positivity)
  let c := min γ 1 / 2
  let B := Real.log 4+4
  have hc : 0<c := by dsimp [c]; positivity
  have hcγ : 2*c≤γ := by dsimp [c]; linarith [min_le_left γ 1]
  have hc₁ : 2*c≤1 := by dsimp [c]; linarith [min_le_right γ 1]
  have hB : 0<B := by dsimp [B]; positivity
  let C := max K (B*Real.exp 2)
  have hKC : K≤C := le_max_left ..
  have hBC : B*Real.exp 2≤C := le_max_right ..
  have hBC' : B≤C := (le_mul_of_one_le_right hB.le (Real.one_le_exp (by norm_num))).trans hBC
  refine ⟨C,hK.trans_le hKC,c,hc,?_⟩
  intro x q χ hx hlog hq hqx hχ
  have hx₀ : 0<x := by linarith
  have hs := Real.sq_sqrt (by linarith : 0≤Real.log x)
  have hs₀ := Real.sqrt_nonneg (Real.log x)
  apply csSup_le
  · exact ⟨_,⟨0,⟨le_rfl,hx₀.le⟩,rfl⟩⟩
  rintro u ⟨y,hy,rfl⟩
  obtain ⟨hy₀,hyx⟩ := hy
  have htriv := norm_psiChar_le_const_mul_self hy₀ χ
  change ‖psiChar y χ‖≤B*y at htriv
  by_cases hsmall : Real.log x≤4
  · have hs₂ : Real.sqrt (Real.log x)≤2 := by nlinarith
    have hex := Real.exp_le_exp.mpr (show c*Real.sqrt (Real.log x)≤2 by nlinarith [mul_nonneg (sub_nonneg.mpr (show c≤1 by linarith)) hs₀])
    rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
    calc _ ≤ (B*x)*Real.exp 2 := mul_le_mul (htriv.trans (mul_le_mul_of_nonneg_left hyx hB.le)) hex (Real.exp_nonneg _) (by positivity)
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hBC hx₀.le]
  by_cases hys : y≤Real.sqrt x
  · have hslog := Real.log_sqrt hx₀.le
    have hlog' : c*Real.sqrt (Real.log x)≤Real.log x/2 := by
      nlinarith [Real.sqrt_le_self_iff.mpr (Or.inr hlog),mul_nonneg (sub_nonneg.mpr hc₁) hs₀]
    have hex := Real.exp_le_exp.mpr (hlog'.trans_eq hslog.symm)
    rw [Real.exp_log (Real.sqrt_pos.mpr hx₀)] at hex
    rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
    calc _ ≤ (B*Real.sqrt x)*Real.sqrt x := mul_le_mul (htriv.trans (mul_le_mul_of_nonneg_left hys hB.le)) hex (Real.exp_nonneg _) (by positivity)
         _ = B*x := by rw [mul_assoc,Real.mul_self_sqrt hx₀.le]
         _ ≤ _ := mul_le_mul_of_nonneg_right hBC' hx₀.le
  have hylog := Real.log_le_log (Real.sqrt_pos.mpr hx₀) (le_of_not_ge hys)
  rw [Real.log_sqrt hx₀.le] at hylog
  have hlogy : 2≤Real.log y := by linarith
  have hy₂ : 2≤y := by linarith [Real.log_le_sub_one_of_pos ((Real.sqrt_pos.mpr hx₀).trans_le (le_of_not_ge hys))]
  have hpow : (q:ℝ)≤(Real.log y)^(2*L) := by
    rw [Real.rpow_mul (by linarith),Real.rpow_two]
    exact hqx.trans (Real.rpow_le_rpow (by linarith) (by nlinarith) hL)
  have hsy := Real.sq_sqrt (by linarith : 0≤Real.log y)
  have hsy₀ := Real.sqrt_nonneg (Real.log y)
  have hcomp : Real.sqrt (Real.log x)≤2*Real.sqrt (Real.log y) := by nlinarith
  have hex := Real.exp_le_exp.mpr (show -γ*Real.sqrt (Real.log y) ≤ -c*Real.sqrt (Real.log x) by
    nlinarith only [mul_le_mul_of_nonneg_left hcomp hc.le,mul_le_mul_of_nonneg_right hcγ hsy₀])
  exact (hsw y q χ hy₂ hq hpow hχ).trans (mul_le_mul (mul_le_mul hKC hyx hy₀ (hK.trans_le hKC).le) hex (Real.exp_nonneg _) (mul_nonneg (hK.trans_le hKC).le hx₀.le))

/-- The small-conductor primitive mean retains every logarithmic saving
when each character independently chooses a real endpoint. -/
theorem sum_smallConductor_maximalPsiChar_le (A : ℝ) {L : ℝ} (hL : 0≤L) :
    ∃ C : ℝ,0<C ∧ ∀ {x Q : ℝ}, 2≤x → 1≤Real.log x →
      ∑ d ∈ Icc 2 ⌊min Q (Real.log x ^ L)⌋₊, (d.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ d with χ.IsPrimitive, maximalPsiCharNorm x χ ≤
        C*x/(Real.log x)^A := by
  obtain ⟨C,hC,c,hc,H⟩ := maximalPsiCharNorm_siegelWalfisz hL
  obtain ⟨K,hK,habsorb⟩ := log_rpow_mul_exp_neg_sqrt_log_le (L+A) hc
  refine ⟨C*K,by positivity,?_⟩
  intro x Q hx hl
  have hl₀ : 0<Real.log x := by linarith
  let E := C*x*Real.exp (-c*Real.sqrt (Real.log x))
  have hE : 0≤E := by dsimp [E]; positivity
  let S := Icc 2 ⌊min Q ((Real.log x)^L)⌋₊
  have hupper : (⌊min Q ((Real.log x)^L)⌋₊:ℝ)≤(Real.log x)^L :=
    (Nat.cast_le.mpr (Nat.floor_mono (min_le_right ..))).trans (Nat.floor_le (Real.rpow_nonneg hl₀.le _))
  have hsum (d : ℕ) (hd : d∈S) :
      (d.totient:ℝ)⁻¹*(∑χ : DirichletCharacter ℂ d with χ.IsPrimitive,maximalPsiCharNorm x χ)≤E := by
    obtain ⟨hd₂,hd'⟩ := mem_Icc.mp hd
    haveI : NeZero d := ⟨by omega⟩
    have htot : 0<(d.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    rw [inv_mul_le_iff₀ htot]
    let F := (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ=>χ.IsPrimitive)
    calc _ ≤ ∑ _χ ∈ F,E := by
           apply sum_le_sum;intro χ hχ
           have hp := (mem_filter.mp hχ).2
           apply H χ hx hl (by omega) ((Nat.cast_le.mpr hd').trans hupper)
           intro he
           have hh : χ.conductor=d := hp
           rw [he,DirichletCharacter.conductor_one] at hh;omega
         _ ≤ _ := by
           simp only [sum_const,nsmul_eq_mul]
           have hcard := card_le_univ F
           rw [Fintype.card_eq_nat_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity] at hcard
           exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hE
  have hcard : (S.card:ℝ)≤(Real.log x)^L := by
    apply le_trans _ hupper;exact_mod_cast (show S.card≤⌊min Q ((Real.log x)^L)⌋₊ by simp [S,Nat.card_Icc])
  have hab := habsorb hl
  rw [Real.rpow_add hl₀] at hab
  calc _ ≤ ∑ _d ∈ S,E := sum_le_sum hsum
       _ ≤ (Real.log x)^L*E := by simp only [sum_const,nsmul_eq_mul];exact mul_le_mul_of_nonneg_right hcard hE
       _ ≤ _ := by
         rw [le_div_iff₀ (Real.rpow_pos_of_pos hl₀ _)]
         calc _ = (C*x)*(((Real.log x)^L*(Real.log x)^A)*Real.exp (-c*Real.sqrt (Real.log x))) := by dsimp [E];ring
              _ ≤ _ := (mul_le_mul_of_nonneg_left hab (by positivity : 0≤C*x)).trans_eq (by ring)
end AnalyticNumberTheory.PrimeDistribution
