import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcs
import AnalyticNumberTheory.PrimeDistribution.PageProgressions

/-! # Major arcs outside the Page exceptional conductor

The exceptional conductor is fixed throughout the modulus range, including
all intermediate cutoffs used in partial summation.
-/

noncomputable section

open Finset AnalyticNumberTheory.PrimeDistribution
open scoped ArithmeticFunction.Moebius

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Pointwise good-arc estimate using any common choice of Page data, with
`F` bounding the ordinary prime counting error at the intermediate cutoffs. -/
theorem norm_primeExpSum_page_good {K E F : ℝ} {N q : ℕ} (hN : 1≤N) (hq : 0<q)
    {e : Σ m : ℕ,DirichletCharacter ℂ m} (hdata : PagePartialBound N K E e)
    (hK : (q:ℝ)≤K) (hnd : ¬e.1∣q) (hE : 0≤E) (hF : 0≤F)
    (hψ : ∀ k∈Icc 1 N, |Chebyshev.psi k-k|≤F)
    {a : ℤ} (ha : a.natAbs.Coprime q) {α R : ℝ} (hα : α∈majorArc q a R) :
    ‖primeExpSum N α-((μ q:ℂ)/q.totient)*mainExpSum N (α-a/q)‖≤
      (F+2*(Real.log q/Real.log 2*Real.log N)+q.totient*E)*(1+2*Real.pi*N/(q*R)) := by
  let : NeZero q := ⟨by omega⟩
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  let V := Real.log q/Real.log 2*Real.log N
  have hqlog : 0≤Real.log q/Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (by positivity)
  have hV : 0≤V := mul_nonneg hqlog (Real.log_nonneg (by exact_mod_cast hN))
  let B := (F+V)/q.totient+E
  have hB : 0≤B := by dsimp [B]; positivity
  have hp : ∀ k∈Icc 1 N, ∀ r∈coprimeResidues q, |psiAP k q r-k/q.totient|≤B := by
    intro k hk r hr
    have hk1 : (1:ℝ)≤k := by exact_mod_cast (mem_Icc.mp hk).1
    have hqk (χ : DirichletCharacter ℂ q) (hχ : χ≠1) : ‖psiChar k χ‖≤E :=
      hdata hK (fun he => hnd (congrArg Sigma.fst he ▸ χ.conductor_dvd_level)) hχ k hk
    apply (abs_psiAP_sub_main_le_of_uniform_char hk1 hE hq (mem_filter.mp hr).2 hqk).trans
    exact add_le_add (div_le_div_of_nonneg_right (add_le_add (hψ k hk)
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by exact_mod_cast (mem_Icc.mp hk).2)) hqlog))
      hφ.le) le_rfl
  apply (norm_primeExpSum_sub_le_of_mem_majorArc hN hq ha hα hB hp).trans_eq
  congr 1
  change (q.totient:ℝ)*((F+V)/q.totient+E)+V=F+2*V+q.totient*E
  field_simp [hφ.ne']
  ring

/-- Uniform major-arc error in terms of the Page region and the ordinary
prime number theorem. The parameter `K` bounds the entire modulus range;
`R` determines the arc width. -/
theorem page_primeExpSum_majorArc :
    ∃ c Z A b : ℝ, 0<c ∧ c≤1/4 ∧ 0<Z ∧ 0<A ∧ 0<b ∧ ∀ {K : ℝ}, 2≤K →
    ∃ d : ℕ, (d=0 ∨ ∃ χ : DirichletCharacter ℂ d,PageExceptionalCharacter K c χ) ∧
    ∀ {N q : ℕ} {Y : ℝ}, 1≤N → 0<q → (q:ℝ)≤K → ¬d∣q →
      Real.exp 16≤Y → K+2≤Real.exp (Real.sqrt (Real.log Y)) →
      ∀ {a : ℤ}, a.natAbs.Coprime q → ∀ {α R : ℝ}, α∈majorArc q a R →
      ‖primeExpSum N α-((μ q:ℂ)/q.totient)*mainExpSum N (α-a/q)‖≤
        (max (7*Y) (A*N*Real.exp (-b*Real.sqrt (Real.log Y)))+
          2*(Real.log q/Real.log 2*Real.log N)+q.totient*pagePartialError N Y c Z)*
          (1+2*Real.pi*N/(q*R)) := by
  obtain ⟨c,Z,hc,hc4,hZ,H⟩ := page_psiAP
  obtain ⟨A,hA,b,hb,Hψ⟩ := abs_psi_sub_id_le_exp
  refine ⟨c,Z,A,b,hc,hc4,hZ,hA,hb,fun {K} hK => ?_⟩
  obtain ⟨d,hd,hAP⟩ := H hK
  refine ⟨d,hd,fun {N q} {Y} hN hq hqK hnd hY hKY {a} ha {α R} hα => ?_⟩
  have hY2 : 2≤Y := by linarith [Real.add_one_le_exp (16:ℝ)]
  have hY0 : 0<Y := by linarith
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  let U := max (7*Y) (A*N*Real.exp (-b*Real.sqrt (Real.log Y)))
  let V := Real.log q/Real.log 2*Real.log N
  have hU : 0≤U := le_trans (by positivity) (le_max_left ..)
  have hV : 0≤V := by
    dsimp [V]
    exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (by positivity))
      (Real.log_nonneg (by exact_mod_cast hN))
  let E := (U+V)/q.totient+pagePartialError N Y c Z
  have hE : 0≤E := add_nonneg (by positivity) (le_trans (by positivity) (le_max_left ..))
  have hp : ∀ k∈Icc 1 N, ∀ r∈coprimeResidues q, |psiAP k q r-k/q.totient|≤E := by
    intro k hk r hr
    have hkN : (k:ℝ)≤N := by exact_mod_cast (mem_Icc.mp hk).2
    have hk1 : (1:ℝ)≤k := by exact_mod_cast (mem_Icc.mp hk).1
    have hψ : |Chebyshev.psi k-k|≤U := by
      by_cases hsmall : (k:ℝ)≤Y
      · apply le_trans _ (le_max_left ..)
        have hbound := psi_le_const_mul_self (Nat.cast_nonneg k)
        have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ))
        exact abs_le.mpr ⟨by linarith [Chebyshev.psi_nonneg (x:=(k:ℝ))],
          by nlinarith [mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg (α:=ℝ) k)]⟩
      · apply le_trans _ (le_max_right ..)
        apply (Hψ k (hY2.trans (le_of_not_ge hsmall))).trans
        exact mul_le_mul (by gcongr) (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
          (Real.sqrt_le_sqrt (Real.log_le_log hY0 (le_of_not_ge hsmall))) (by linarith : -b≤0)))
          (Real.exp_pos _).le (by positivity)
    have hlog : Real.log (k:ℝ)≤Real.log N := Real.log_le_log (by linarith) hkN
    exact (hAP hq hqK hnd (mem_filter.mp hr).2 hY hKY hk).trans
      (add_le_add (div_le_div_of_nonneg_right (add_le_add hψ (mul_le_mul_of_nonneg_left hlog
        (div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (by positivity)))) hφ.le) le_rfl)
  apply (norm_primeExpSum_sub_le_of_mem_majorArc hN hq ha hα hE hp).trans_eq
  congr 1
  change (q.totient:ℝ)*((U+V)/q.totient+pagePartialError N Y c Z)+V=
    U+2*V+q.totient*pagePartialError N Y c Z
  field_simp [hφ.ne']
  ring

end AnalyticNumberTheory.AdditiveNumberTheory
