import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalArc
import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalWeightDecay

/-! # The total major-arc integral at exceptional denominators -/

noncomputable section

open Finset Real MeasureTheory AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Sum of the absolute values of all exceptional major-arc integrals.
Both terms are finite numerical expressions. The same `PagePartialBound`
controls the major arcs outside this set of denominators. -/
theorem page_exceptional_arcs_integral {N M : ℕ} {K c R E : ℝ}
    (hN : 1≤N) (hM : 1≤M) (hK : 2≤K) (hc : 0<c) (hMK : (M:ℝ)≤K)
    (hR : 1≤R) (hNR : (N:ℝ)≤R^2) (hE : 0≤E)
    {e₀ : Σ m : ℕ,DirichletCharacter ℂ m} (he₀ : e₀.1=0 ∨ PageExceptionalCharacter K c e₀.2)
    (hdata : PagePartialBound N K E e₀) :
    (∑q∈(Icc 1 M).filter (e₀.1∣·), ∑a∈coprimeResidues q,
      ‖∫ α in majorArc q (a:ℤ) R,primeExpSum N α^3*e (-α*N)‖) ≤
      (66150*Real.pi^3*N^2)*(77760*Real.pi^2*c*(1+log M)^2*log ((M:ℝ)+2)^3/log (K+2))+
      54*M/R*(pageArcRemainder N M R E)^3 := by
  obtain ⟨d,ψ⟩ := e₀
  change d=0 ∨ PageExceptionalCharacter K c ψ at he₀
  change (∑q∈(Icc 1 M).filter (d∣·), _) ≤ _
  let D := pageArcRemainder N M R E
  let A := 66150*Real.pi^3*(N:ℝ)^2
  let S := (Icc 1 M).filter (d∣·)
  have hA : 0≤A := by dsimp [A]; positivity
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hl : 0<log (K+2) := log_pos (by linarith)
  have hd0 : 0≤D := by
    have := log_nonneg hm
    have := log_nonneg (show 1≤(N:ℝ) by exact_mod_cast hN)
    dsimp [D,pageArcRemainder]; positivity
  rcases he₀ with hd|he
  · subst d
    have hn : (Icc 1 M).filter ((0:ℕ)∣·)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have := (mem_filter.mp hq).2
      have := (mem_Icc.mp (mem_filter.mp hq).1).1
      simp_all
    rw [hn,sum_empty]
    have := log_nonneg (show 1≤(M:ℝ)+2 by linarith)
    change 0≤ A*_+54*M/R*D^3
    positivity
  have hweight := page_exceptional_weight_sum hK hc he hM
  obtain ⟨_,hd,_,hp,_,hψ,_⟩ := he
  have hden (q : ℕ) (hq : q∈S) :
      (∑a∈coprimeResidues q, ‖∫ α in majorArc q (a:ℤ) R,primeExpSum N α^3*e (-α*N)‖)
      ≤ A*((sqrt d)^3/(q.totient:ℝ)^2)+(54/R*D^3) := by
    obtain ⟨hqI,hdq⟩ := mem_filter.mp hq
    obtain ⟨hq1,hqM⟩ := mem_Icc.mp hqI
    have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hqr : (0:ℝ)<q := by exact_mod_cast hq1
    have hcard : (coprimeResidues q).card=q.totient := by
      simp [coprimeResidues,Nat.totient_eq_card_coprime,Nat.coprime_comm]
    calc _ ≤ ∑ _a∈coprimeResidues q,
          (A*(sqrt d)^3/(q.totient:ℝ)^3+54*(1/(q*R))*D^3) :=
            sum_le_sum fun a ha => page_exceptional_arc_integral hN hq1 hqM hMK hR hNR
              (by omega) hdq hp hψ hdata hE (mem_filter.mp ha).2
         _ = A*((sqrt d)^3/(q.totient:ℝ)^2)+(q.totient/q:ℝ)*(54/R*D^3) := by
            rw [sum_const,hcard,nsmul_eq_mul]
            field_simp [hφ.ne',hqr.ne',show R≠0 by linarith] <;> ring
         _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left (by positivity)
           ((div_le_one hqr).2 (by exact_mod_cast Nat.totient_le q)))
  have hcardS : S.card≤M := (card_le_card (filter_subset ..)).trans_eq (by simp)
  apply (sum_le_sum (s:=S) hden).trans
  rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
  apply (add_le_add (mul_le_mul_of_nonneg_left hweight hA)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardS : (S.card:ℝ)≤M)
      (by positivity : 0≤54/R*D^3))).trans_eq
  change A*_+(M:ℝ)*(54/R*D^3)=A*_+54*M/R*D^3
  ring

end AnalyticNumberTheory.AdditiveNumberTheory
