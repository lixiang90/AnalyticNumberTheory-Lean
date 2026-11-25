import AnalyticNumberTheory.AdditiveNumberTheory.PageMajorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalArcs
import AnalyticNumberTheory.AdditiveNumberTheory.PageParameterBounds

/-! # One choice of Page parameters for all ternary major arcs

The regular arcs and the arcs with an exceptional denominator use the same
primitive pair. The powers in the cutoff and in the linear approximation
can be prescribed independently. All dependence on the analytic constants
in the finite error terms is explicit.
-/

noncomputable section

open Finset Real MeasureTheory AnalyticNumberTheory.PrimeDistribution
open scoped ArithmeticFunction.Moebius

namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem common_page_partial_bounds :
    ∃ c A b : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0<b ∧ ∀ {K : ℝ},2≤K →
    ∃ e : Σ m : ℕ,DirichletCharacter ℂ m, (e.1=0 ∨ PageExceptionalCharacter K c e.2) ∧
      ∀ {N : ℕ},Real.exp 16≤sqrt N → K+2≤exp (sqrt (log (sqrt N))) →
        let U := max (7*sqrt N) (A*N*exp (-b*sqrt (log (sqrt N))))
        PagePartialBound N K U e ∧ ∀ k∈Icc 1 N, |Chebyshev.psi k-k|≤U := by
  obtain ⟨c,Z,hc,hc4,hZ,HP⟩ := page_partial_bound
  obtain ⟨A₀,hA₀,b₀,hb₀,hpnt⟩ := abs_psi_sub_id_le_exp
  let A := max A₀ (2*pageCharacterConstant c Z)
  let b := min b₀ (c/256)
  have hA : 0<A := hA₀.trans_le (le_max_left ..)
  have hb : 0<b := lt_min hb₀ (by positivity)
  refine ⟨c,A,b,hc,hc4,hA,hb,fun {K} hK => ?_⟩
  obtain ⟨e,he,H⟩ := HP hK
  refine ⟨e,he,fun {N} hY hKY => ?_⟩
  let Y := sqrt (N:ℝ)
  let u := sqrt (log Y)
  let U := max (7*Y) (A*N*exp (-b*u))
  have hu : 0≤u := sqrt_nonneg _
  have hY2 : 2≤Y := by dsimp [Y]; linarith [Real.add_one_le_exp (16:ℝ)]
  have hY0 : 0<Y := by linarith
  have hec (y : ℝ) (hy : b≤y) : exp (-y*u)≤exp (-b*u) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hy) hu)
  constructor
  · intro q _ hq χ hne hχ k hk
    apply (H hY hKY hq hne hχ k hk).trans
    apply max_le (le_max_left ..) (le_trans _ (le_max_right ..))
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg N))
      (hec _ (min_le_right ..)) (exp_pos _).le (by positivity)
  · intro k hk
    have hkN : (k:ℝ)≤N := by exact_mod_cast (mem_Icc.mp hk).2
    by_cases hsmall : (k:ℝ)≤Y
    · apply le_trans _ (le_max_left ..)
      have hc' := psi_le_const_mul_self (Nat.cast_nonneg k)
      have hl := log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ))
      exact abs_le.mpr ⟨by linarith [Chebyshev.psi_nonneg (x:=(k:ℝ))],
        by nlinarith [mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α:=ℝ) k)]⟩
    · have hYk := le_of_not_ge hsmall
      apply le_trans _ (le_max_right ..)
      apply (hpnt k (hY2.trans hYk)).trans
      have hstep := sqrt_le_sqrt (log_le_log hY0 hYk)
      have ht := mul_le_mul_of_nonpos_left hstep (neg_nonpos.mpr hb₀.le)
      exact mul_le_mul (mul_le_mul (le_max_left ..) hkN (Nat.cast_nonneg _) hA.le)
        ((exp_le_exp.mpr ht).trans (hec b₀ (min_le_left ..))) (exp_pos _).le (by positivity)

private theorem common_arc_error_bound {N M q : ℕ} (hN : 1≤N) (hM : 1≤M)
    (hq : 1≤q) (hqM : q≤M) {U : ℝ} (hU : 0≤U) :
    (U+2*(log q/log 2*log N)+q.totient*U)*(1+2*Real.pi*N/(q*((N:ℝ)/M)))
      ≤9*(M:ℝ)^2*(2*U+4*log N) ∧
    pageArcRemainder N M ((N:ℝ)/M) U≤9*(M:ℝ)^2*(2*U+4*log N) := by
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hqmr : (q:ℝ)≤M := by exact_mod_cast hqM
  have hnr : (1:ℝ)≤N := by exact_mod_cast hN
  have hφ : (q.totient:ℝ)≤M := by exact_mod_cast (Nat.totient_le q).trans hqM
  have hL : 0≤log N := log_nonneg hnr
  have hlg (t : ℝ) (ht : 1≤t) :
      log t/log 2≤2*t := by
    apply (div_le_iff₀ (log_pos one_lt_two)).2
    have hh : 1/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith only [log_le_self (zero_le_one.trans ht),mul_le_mul_of_nonneg_left hh (zero_le_one.trans ht)]
  have huR : 2*Real.pi*(N:ℝ)/((N:ℝ)/M)=2*Real.pi*M := by
    field_simp [show (N:ℝ)≠0 by linarith,show (M:ℝ)≠0 by linarith]
  have hwidth : 1+2*Real.pi*(N:ℝ)/(q*((N:ℝ)/M))≤9*M := by
    have hR : 0<(N:ℝ)/M := by positivity
    have hd := le_mul_of_one_le_left hR.le hq1
    have hh := div_le_div_of_nonneg_left (by positivity : 0≤2*Real.pi*(N:ℝ)) hR hd
    rw [huR] at hh
    nlinarith only [hh,Real.pi_le_four,hm,mul_le_mul_of_nonneg_right Real.pi_le_four (Nat.cast_nonneg (α:=ℝ) M)]
  have hUφ := mul_le_mul_of_nonneg_right hφ hU
  have hUm := le_mul_of_one_le_left hU hm
  have hlogq := mul_le_mul_of_nonneg_right ((hlg q hq1).trans (by linarith : 2*(q:ℝ)≤2*M)) hL
  have hlogm := mul_le_mul_of_nonneg_right (hlg M hm) hL
  have hmajor : U+2*(log q/log 2*log N)+q.totient*U≤M*(2*U+4*log N) := by
    nlinarith only [hUφ,hUm,hlogq]
  have hminor : log M/log 2*log N+M*U≤M*(2*U+4*log N) := by
    nlinarith only [hlogm,mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) hU,mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) hL]
  constructor
  · apply (mul_le_mul hmajor hwidth (by positivity) (by positivity)).trans_eq
    ring
  · dsimp only [pageArcRemainder]
    rw [huR]
    apply (mul_le_mul hminor (show 1+2*Real.pi*(M:ℝ)≤9*M by
      nlinarith only [hm,mul_le_mul_of_nonneg_right Real.pi_le_four (Nat.cast_nonneg (α:=ℝ) M)]) (by positivity)
        (by positivity)).trans_eq
    ring

/-- Finite Page major-arc estimates for all regular arcs and the total
exceptional cubic contribution. At `K+2 = exp (sqrt (log (sqrt N)))`
the conductor term saves two fifths of a logarithm. -/
theorem page_majorArc_parameters (B J : ℕ) :
    ∃ c A b : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0<b ∧ ∀ {N M : ℕ} {K : ℝ},
      1≤M → (M:ℝ)≤(log N)^B → 2*(M:ℝ)^2≤N → exp 16≤sqrt N → 2≤K →
      (M:ℝ)≤K → K+2≤exp (sqrt (log (sqrt N))) →
      ∃ e₀ : Σ m : ℕ,DirichletCharacter ℂ m, (e₀.1=0 ∨ PageExceptionalCharacter K c e₀.2) ∧
      let D := pageMajorArcLogConstant A b B J*N/(log N)^J
      (∀ q∈Icc 1 M, ¬e₀.1∣q → ∀ a∈coprimeResidues q,∀ α∈majorArc q a ((N:ℝ)/M),
        ‖primeExpSum N α-(μ q:ℂ)/q.totient*mainExpSum N (α-a/q)‖≤D) ∧
      (∑q∈(Icc 1 M).filter (e₀.1∣·), ∑a∈coprimeResidues q,
        ‖∫ α in majorArc q (a:ℤ) ((N:ℝ)/M),primeExpSum N α^3*e (-α*N)‖) ≤
        (66150*Real.pi^3*N^2)*(77760*Real.pi^2*c*(1+log M)^2*log ((M:ℝ)+2)^3/log (K+2))+
        54*M/((N:ℝ)/M)*D^3 := by
  obtain ⟨c,A,b,hc,hc4,hA,hb,H⟩ := common_page_partial_bounds
  refine ⟨c,A,b,hc,hc4,hA,hb,fun {N M} {K} hM hMB hNM hY hK hMK hKY => ?_⟩
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hn : (1:ℝ)≤N := by nlinarith [sq_nonneg ((M:ℝ)-1)]
  have hN : 1≤N := by exact_mod_cast hn
  have hL : 1≤log N := by
    have hs : sqrt (N:ℝ)≤N := (sqrt_le_iff).2 ⟨zero_le_one.trans hn,by nlinarith [sq_nonneg ((N:ℝ)-1)]⟩
    exact (by norm_num : (1:ℝ)≤16).trans ((Real.le_log_iff_exp_le (by linarith)).2 (hY.trans hs))
  obtain ⟨e₀,he₀,H'⟩ := H hK
  obtain ⟨hdata,hψ⟩ := H' hY hKY
  let U := max (7*sqrt N) (A*N*exp (-b*sqrt (log (sqrt N))))
  have hU : 0≤U := le_trans (by positivity) (le_max_left ..)
  have hbound := page_majorArc_log_saving hn hL (Nat.cast_nonneg (α:=ℝ) M) hA.le hb B J hMB
  have hR : 1≤(N:ℝ)/M := (le_div_iff₀ (by linarith)).2 (by nlinarith [sq_nonneg ((M:ℝ)-1)])
  have hNR : (N:ℝ)≤((N:ℝ)/M)^2 := by
    rw [div_pow,le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left (by linarith only [hNM] : (M:ℝ)^2≤N)
      (Nat.cast_nonneg (α:=ℝ) N)).trans_eq (by ring)
  refine ⟨e₀,he₀,?_⟩
  dsimp only
  constructor
  · intro q hq hnd a ha α hα
    obtain ⟨hq1,hqM⟩ := mem_Icc.mp hq
    have h := norm_primeExpSum_page_good hN hq1 hdata
      (((Nat.cast_le (α:=ℝ)).2 hqM).trans hMK) hnd hU hU hψ
      (show (a:ℤ).natAbs.Coprime q from (mem_filter.mp ha).2) hα
    push_cast at h
    exact h.trans ((common_arc_error_bound hN hM hq1 hqM hU).1.trans hbound)
  · apply (page_exceptional_arcs_integral hN hM hK hc hMK hR hNR hU he₀ hdata).trans
    have hD := ((common_arc_error_bound hN hM hM le_rfl hU).2.trans hbound)
    have hD0 : 0≤pageArcRemainder N M ((N:ℝ)/M) U := by
      have := log_nonneg hm
      dsimp [pageArcRemainder]
      positivity
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 3) (by positivity))

end AnalyticNumberTheory.AdditiveNumberTheory
