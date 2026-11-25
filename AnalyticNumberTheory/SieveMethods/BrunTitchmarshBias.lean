import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.DirichletLFunctions.Characters

/-!
# A bias constraint from a stronger Brun–Titchmarsh inequality

An upper bound whose coefficient is strictly below two leaves a positive
proportion of the prime mass in the weight `1 + Re χ(p)`. The primes
dividing the modulus cost at most its logarithm.
-/

open Finset Real Filter Set
open scoped ArithmeticFunction.vonMangoldt Topology
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- A fixed improvement of the Brun–Titchmarsh coefficient on a power range of moduli. -/
def BrunTitchmarshImprovement (η α : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ q a : ℕ, 3≤q → (q:ℝ)<x^α → a.Coprime q →
    piAP x q a ≤ (2-η)*x/(q.totient*log (x/q))

/-- Nonnegative Mangoldt coefficients of the product of zeta with a character L-function. -/
noncomputable def positiveCharacterMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  Λ n*(1+(χ n).re)

theorem positiveCharacterMangoldt_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    0≤positiveCharacterMangoldt χ n := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (norm_char_le_one χ (n:ZMod q)))).1
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by linarith)

private theorem sum_primeFactors_log_le (q : ℕ) [NeZero q] :
    ∑ p∈q.primeFactors, log p ≤ log q := by
  have hn (p : ℕ) (hp : p∈q.primeFactors) : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Real.log_prod hn]
  have hle : ((∏p∈q.primeFactors,p : ℕ):ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
  apply Real.log_le_log (Finset.prod_pos (fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos))
  simpa using hle

private theorem sum_thetaAP_residues {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (x : ℝ) :
    ∑ u : ZMod q, f u*thetaAP x q u.val =
      ∑ p∈Ioc 0 ⌊x⌋₊ with p.Prime, f (p:ZMod q)*log p := by
  classical
  simp only [thetaAP_eq_sum_Ioc,sum_filter,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have he (u : ZMod q) : p ≡ u.val [MOD q] ↔ (p:ZMod q)=u := by
    rw [← ZMod.natCast_eq_natCast_iff,ZMod.natCast_zmod_val]
  by_cases h : p.Prime
  · simp only [h,true_and,he]
    simp [mul_ite]
  · simp [h]

private theorem bias_count_lower {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1)
    {x B : ℝ} (hB : ∀ a : ℕ, a.Coprime q → thetaAP x q a≤B/q.totient) :
    2*Chebyshev.theta x-B-log q ≤ ∑ n∈Icc 1 ⌊x⌋₊, positiveCharacterMangoldt χ n := by
  classical
  let W (u : ZMod q) := ((1 : DirichletCharacter ℂ q) u).re-(χ u).re
  have hW (u : ZMod q) : 0≤W u := by
    dsimp [W]; by_cases hu : IsUnit u
    · rw [MulChar.one_apply hu,Complex.one_re]
      exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (norm_char_le_one χ u))
    · simp [MulChar.map_nonunit _ hu]
  have hWt : ∑u : ZMod q,W u=q.totient := by
    simp only [W,sum_sub_distrib,← Complex.re_sum]
    rw [sum_zmod_eq_zero_of_ne_one hχ,MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
    simp
  let S := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hupper : ∑p∈S,W (p:ZMod q)*log p ≤ B := by
    rw [← sum_thetaAP_residues]
    calc _ ≤ ∑u : ZMod q,W u*(B/q.totient) := by
               apply sum_le_sum; intro u _
               by_cases hu : IsUnit u
               · apply mul_le_mul_of_nonneg_left _ (hW _)
                 apply hB
                 exact (ZMod.isUnit_iff_coprime _ _).mp (by simpa using hu)
               · simp [W,MulChar.map_nonunit _ hu]
         _ = B := by rw [← sum_mul,hWt];field_simp [Nat.ne_of_gt (Nat.totient_pos.mpr (NeZero.pos q))]
  have hbad : ∑p∈S,(1-((1:DirichletCharacter ℂ q) p).re)*log p ≤ log q := by
    apply le_trans _ (sum_primeFactors_log_le q)
    let R := S.filter (fun p => p∣q)
    have he : ∑p∈S,(1-((1:DirichletCharacter ℂ q) p).re)*log p = ∑p∈R,log p := by
      change _ = ∑ p∈S with p∣q, log p
      rw [Finset.sum_filter (s:=S) (p:=fun p : ℕ => p∣q)]; apply sum_congr rfl
      intro p hp
      have hpr := (mem_filter.mp hp).2
      by_cases h : p∣q
      · have hu : ¬IsUnit (p:ZMod q) := fun hu => (hpr.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime _ _).mp hu)) h
        simp [h,MulChar.map_nonunit _ hu]
      · have hu := (ZMod.isUnit_iff_coprime p q).mpr (hpr.coprime_iff_not_dvd.mpr h)
        simp [h,MulChar.one_apply hu]
    rw [he]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp; obtain ⟨hpr,hd⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hpr).2,hd,NeZero.ne q⟩
    · intro p hp _; exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
  have hsum : ∑p∈S,positiveCharacterMangoldt χ p ≤ ∑n∈Icc 1 ⌊x⌋₊,positiveCharacterMangoldt χ n := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp; exact mem_Icc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hp).1).1,(mem_Ioc.mp (mem_filter.mp hp).1).2⟩
    · intro n _ _;exact positiveCharacterMangoldt_nonneg _ _
  have hidentity : 2*Chebyshev.theta x = (∑p∈S,positiveCharacterMangoldt χ p) +
      (∑p∈S,W (p:ZMod q)*log p) + ∑p∈S,(1-((1:DirichletCharacter ℂ q) p).re)*log p := by
    change 2*(∑p∈S,log p)=_
    rw [mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl; intro p hp
    rw [positiveCharacterMangoldt,ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
    dsimp [W];ring
  linarith

/-- A uniform surplus in the coefficients of `-ζ'/ζ - L'/L` for every nonprincipal
character follows from a strict improvement of the Brun–Titchmarsh coefficient. -/
theorem positiveCharacterMangoldt_of_brunTitchmarsh {η α : ℝ} (hη : 0<η) (hη' : η<1)
    (hα : 0<α) (H : BrunTitchmarshImprovement η α) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      3≤q → χ≠1 → log q≤δ*log x →
      (η/4)*x ≤ ∑n∈Icc 1 ⌊x⌋₊,positiveCharacterMangoldt χ n := by
  let δ := min (α/2) (η/8)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hδ,?_⟩
  have hpnt : ∀ᶠ x : ℝ in atTop, 1-η/16 < Chebyshev.theta x/x :=
    tendsto_theta_div_atTop.eventually_const_lt (by linarith)
  filter_upwards [H,hpnt,eventually_gt_atTop (1:ℝ)] with x hbt hθ hx
  intro q _ χ hq hχ hlog
  have hq0 : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hx0 := zero_lt_one.trans hx
  have hxl := log_pos hx
  have hδ₁ : δ≤α/2 := min_le_left ..
  have hδ₂ : δ≤η/8 := min_le_right ..
  have hqd : log q < α*log x := hlog.trans_lt (mul_lt_mul_of_pos_right (by linarith) hxl)
  have hpow : (q:ℝ)<x^α := by
    rw [Real.rpow_def_of_pos hx0,← Real.exp_log hq0]; apply Real.exp_lt_exp.mpr;linarith only [hqd, mul_comm α (log x)]
  have hqsmall : log q ≤ (η/8)*log x := hlog.trans (mul_le_mul_of_nonneg_right hδ₂ hxl.le)
  have hL : 0<log (x/q) := by rw [Real.log_div hx0.ne' hq0.ne'];nlinarith
  have hφ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hratio : (2-η)*log x ≤ (2-η/2)*log (x/q) := by
    rw [Real.log_div hx0.ne' hq0.ne']
    have H' := mul_le_mul_of_nonneg_left hqsmall (by linarith : 0≤2-η/2)
    nlinarith [mul_nonneg (sq_nonneg η) hxl.le]
  have hupper (a : ℕ) (ha : a.Coprime q) : thetaAP x q a≤((2-η/2)*x)/q.totient := by
    apply (thetaAP_le_piAP_mul_log ..).trans
    apply (mul_le_mul_of_nonneg_right (hbt q a hq hpow ha) hxl.le).trans
    calc _ = x*((2-η)*log x)/(q.totient*log (x/q)) := by ring
         _ ≤ x*((2-η/2)*log (x/q))/(q.totient*log (x/q)) := by gcongr
         _ = _ := by field_simp
  have hbound := bias_count_lower hχ hupper
  have herr := hqsmall.trans (mul_le_mul_of_nonneg_left (Real.log_le_self hx0.le) (by positivity))
  have hh := (lt_div_iff₀ hx0).mp hθ
  linarith

end AnalyticNumberTheory.SieveMethods
