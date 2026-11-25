import AnalyticNumberTheory.AnalyticTools.Gamma.ReflectedStripRatio
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion
import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import AnalyticNumberTheory.DirichletSeries.Operations

/-!
# The left edge of a Dirichlet functional equation

The constant is uniform as the line Re(s) = −δ approaches the imaginary
axis. The sole singular factor in the bound is the elementary 1+1/δ
from the absolutely convergent reflected Dirichlet series.
-/
open Real Complex Finset
open scoped Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem two_pow_card_le {m : ℕ} (hm : 0<m) :
    (2:ℝ)^m.primeFactors.card ≤ 2*(m:ℝ)^(1/2:ℝ) := by
  have hh := congrArg (fun F : ArithmeticFunction ℕ => F m) zeta_mul_absMoebius_eq_twoPowOmega
  change (_ * absMoebiusAF) m=twoPowOmegaAF m at hh
  rw [ArithmeticFunction.zeta_mul_apply,twoPowOmegaAF_apply_ne hm.ne',ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hh
  have hsum := sum_abs_moebius_divisors_le_two_sqrt hm
  rw [Real.sqrt_eq_rpow] at hsum
  apply le_trans _ hsum
  have he (n : ℕ) : (absMoebiusAF n:ℝ)=|(μ n:ℝ)| := by exact_mod_cast absMoebiusAF_coe_int n
  rw [←sum_congr rfl (fun n _ => he n),←Nat.cast_sum,hh];norm_num

private theorem level_euler_negative {d m : ℕ} [NeZero d] [NeZero m] (χ : DirichletCharacter ℂ d)
    {s : ℂ} {δ : ℝ} (hre : s.re = -δ) (hδ : 0≤δ) :
    ‖∏p∈(d*m).primeFactors,(1-χ p*(p:ℂ)^(-s))‖≤2*(m:ℝ)^(1/2+δ) := by
  let f (p:ℕ) := 1-χ p*(p:ℂ)^(-s)
  have hprod : ∏p∈(d*m).primeFactors,f p=∏p∈m.primeFactors,f p := by
    rw [Nat.primeFactors_mul (NeZero.ne _) (NeZero.ne _)]
    symm;apply prod_subset subset_union_right;intro p h hp
    have hpd := (mem_union.mp h).resolve_right hp
    have hz : χ p=0 := by
      rw [MulChar.apply_eq_zero_iff,ZMod.isUnit_iff_coprime]
      exact (Nat.prime_of_mem_primeFactors hpd).coprime_iff_not_dvd.not.mpr (not_not.mpr (Nat.dvd_of_mem_primeFactors hpd))
    simp [f,hz]
  change ‖∏p∈(d*m).primeFactors,f p‖≤_
  rw [hprod,norm_prod]
  have hp (p:ℕ) (hp:p∈m.primeFactors) : ‖f p‖≤2*(p:ℝ)^δ := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpow : 1≤(p:ℝ)^δ := Real.one_le_rpow (by exact_mod_cast hpp.one_le) hδ
    have h := norm_sub_le (1:ℂ) (χ p*(p:ℂ)^(-s))
    rw [norm_one,norm_mul,Complex.norm_natCast_cpow_of_pos hpp.pos,neg_re,hre,neg_neg] at h
    exact h.trans (by nlinarith only [hpow,mul_le_mul_of_nonneg_right (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) δ)])
  apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hp).trans
  rw [prod_mul_distrib,prod_const]
  have hrad (S : Finset ℕ) : (∏p∈S,(p:ℝ)^δ) = ((∏p∈S,p : ℕ):ℝ)^δ := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih => rw [prod_insert hi,prod_insert hi,ih,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  rw [hrad]
  have hradle := Nat.le_of_dvd (NeZero.pos m) (Nat.prod_primeFactors_dvd m)
  apply (mul_le_mul (two_pow_card_le (NeZero.pos m)) (Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast hradle : ((∏p∈m.primeFactors,p : ℕ):ℝ)≤m) hδ) (by positivity) (by positivity)).trans_eq
  rw [mul_assoc,←Real.rpow_add (Nat.cast_pos.mpr (NeZero.pos m))]

/-- Uniform conductor-height bound to the left of the imaginary axis for all
Dirichlet characters, with explicit dependence on the distance from the axis. -/
theorem norm_LFunction_conductor_left_edge :
    ∃C : ℝ,0<C ∧ ∀{δ : ℝ},0<δ → δ≤1/4 → ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖χ.LFunction (-(δ:ℂ)+(t:ℂ)*I)‖ ≤ C*(1+1/δ)*((q:ℝ)*(|t|+2))^(1/2+δ) := by
  obtain ⟨M,hM,HM⟩ := gammaReal_reflected_strip_ratio
  have hprim {δ:ℝ} (hδ : 0<δ) (hδ' : δ≤1/4) {d : ℕ} [NeZero d]
      (χ : DirichletCharacter ℂ d) (hχ : χ.IsPrimitive) (t : ℝ) :
      ‖χ.LFunction (-(δ:ℂ)+(t:ℂ)*I)‖≤M*(1+1/δ)*((d:ℝ)*(|t|+2))^(1/2+δ) := by
    let w : ℂ := 1+(δ:ℂ)-(t:ℂ)*I
    have hw : w.re=1+δ := by simp [w]
    have hw' : 1-w= -(δ:ℂ)+(t:ℂ)*I := by dsimp [w];ring
    have hz : 1-w≠0 := by intro h;have hh := congrArg Complex.re h;simp [hw] at hh;linarith
    have hne : w≠0 := by intro h;have hh := congrArg Complex.re h;rw [hw,zero_re] at hh;linarith
    have hg : DirichletCharacter.gammaFactor (star χ) w≠0 := by
      rw [gammaFactor_eq_Gammaℝ];apply Complex.Gammaℝ_ne_zero_of_re_pos;rw [add_re,hw,natCast_re];positivity
    have H := LFunction_one_sub_primitive hχ (Or.inl hz) (Or.inl hne) hg
    rw [hw'] at H
    have hk : parityExp χ≤1 := by
      rcases χ.even_or_odd with h|h
      · rw [parityExp_of_even h];omega
      · rw [parityExp_of_odd h]
    have hr := HM ⟨hδ.le,hδ'⟩ (parityExp χ) hk t
    have hL := norm_LFunction_le_one_add_inv (star χ) (by rw [hw];linarith : 1<w.re)
    rw [hw,add_sub_cancel_left] at hL
    have hn : ‖(d:ℂ)^(w-1/2)‖=(d:ℝ)^(1/2+δ) := by
      rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos d)]
      congr 1;rw [sub_re,hw];norm_num;ring
    rw [H,norm_mul,norm_mul,norm_mul,hn,norm_rootNumber_primitive hχ,mul_one,norm_div,
      gammaFactor_eq_Gammaℝ,gammaFactor_eq_Gammaℝ,parityExp_star,Real.mul_rpow (by positivity) (by positivity)]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity)) hL (norm_nonneg _) (by positivity)).trans_eq
    ring
  refine ⟨2*M,by positivity,?_⟩
  intro δ hδ hδ' q _ χ t
  let d := χ.conductor
  letI : NeZero d := ⟨χ.conductor_ne_zero⟩
  obtain ⟨m,hm⟩ : d∣q := χ.conductor_dvd_level
  have hm₀ : m≠0 := by intro h;have := NeZero.ne q;simp [hm,h] at this
  letI : NeZero m := ⟨hm₀⟩
  let s : ℂ := -(δ:ℂ)+(t:ℂ)*I
  have hrs : s.re= -δ := by simp [s]
  have hs : s≠1 := by intro h;have hh := congrArg Complex.re h;rw [hrs,one_re] at hh;linarith
  have he := LFunction_changeLevel_eq χ.conductor_dvd_level χ.primitiveCharacter (s:=s) (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter] at he
  change ‖χ.LFunction s‖≤_
  rw [he,norm_mul]
  have hb := level_euler_negative χ.primitiveCharacter (m:=m) hrs hδ.le
  have hr := hprim hδ hδ' χ.primitiveCharacter χ.primitiveCharacter_isPrimitive t
  change ‖∏p∈(d*m).primeFactors,(1-χ.primitiveCharacter p*(p:ℂ)^(-s))‖≤_ at hb
  rw [←hm] at hb
  apply (mul_le_mul hr hb (norm_nonneg _) (by positivity)).trans_eq
  change M*(1+1/δ)*((d:ℝ)*(|t|+2))^(1/2+δ)*(2*(m:ℝ)^(1/2+δ)) = _
  rw [show (q:ℝ)=(d:ℝ)*m by exact_mod_cast hm]
  rw [show (d:ℝ)*m*(|t|+2)=(d*(|t|+2))*(m:ℝ) by ring,
    Real.mul_rpow (by positivity : 0≤(d:ℝ)*(|t|+2)) (Nat.cast_nonneg m)]
  ring

end AnalyticNumberTheory.DirichletLFunctions
