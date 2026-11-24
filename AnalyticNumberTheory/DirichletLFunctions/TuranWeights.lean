import AnalyticNumberTheory.DirichletLFunctions.TuranZeroDetection
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Weights and absolutely convergent series for the Turán zero detector

Signed Taylor coefficients of the logarithmic derivative are represented by
von Mangoldt sums with a Poisson weight in the logarithm of the index.
-/

noncomputable section

open Finset Complex Filter Asymptotics
open scoped Classical ArithmeticFunction Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletLFunctions

/-- The order-`k` Poisson weight evaluated at `x`. -/
def turanWeight (k : ℕ) (x : ℝ) : ℝ := x^k/(k.factorial:ℝ)*Real.exp (-x)

theorem turanWeight_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ turanWeight k x := by
  dsimp only [turanWeight]; positivity

theorem turanWeight_le_one (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : turanWeight k x ≤ 1 := by
  apply (mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp x hx k) (Real.exp_pos (-x)).le).trans_eq
  rw [← Real.exp_add]; simp

private theorem poisson_scale {k : ℕ} {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    x^k/(k.factorial:ℝ) ≤ a⁻¹^k*Real.exp (a*x) := by
  have h := Real.pow_div_factorial_le_exp (a*x) (mul_nonneg ha.le hx) k
  calc
    _ = a⁻¹^k*((a*x)^k/(k.factorial:ℝ)) := by rw [mul_pow,inv_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- Exponential suppression below the lower logarithmic cutoff. -/
theorem turanWeight_le_at_small {k : ℕ} {x : ℝ} (hx : 0 ≤ x) (hsmall : 1024*x ≤ k) :
    turanWeight k x ≤ (1/256:ℝ)^k * Real.exp (-x) := by
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have h := poisson_scale (k:=k) hx (by norm_num : (0:ℝ)<1024)
  apply h.trans
  have hexp : Real.exp (1024*x) ≤ (4:ℝ)^k := by
    apply (Real.exp_le_exp.mpr hsmall).trans
    rw [show Real.exp (k:ℝ) = (Real.exp 1)^k by rw [← Real.exp_nat_mul]; simp]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_three]) k
  calc
    _ ≤ (1024:ℝ)⁻¹^k*4^k := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by rw [←mul_pow]; norm_num

/-- Exponential suppression above the upper logarithmic cutoff, retaining enough
decay for absolute summation over all larger integers. -/
theorem turanWeight_le_at_large {k : ℕ} {x : ℝ} (hx : 0 ≤ x) (hlarge : 64*k ≤ x) :
    turanWeight k x ≤ (1/256:ℝ)^k * Real.exp (-(x/4)) := by
  apply (mul_le_mul_of_nonneg_right (poisson_scale (k:=k) hx (by norm_num : (0:ℝ)<1/2)) (Real.exp_pos _).le).trans
  rw [mul_assoc,←Real.exp_add, show (1/2:ℝ)*x + -x = -(x/4) + -(x/4) by ring, Real.exp_add,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have he : Real.exp (-(x/4)) ≤ (1/512:ℝ)^k := by
    apply (Real.exp_le_exp.mpr (by linarith : -(x/4) ≤ k*(-16:ℝ))).trans
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le _ k
    rw [Real.exp_neg,one_div,inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    have h := pow_le_pow_left₀ (by norm_num : 0≤(2:ℝ)) Real.exp_one_gt_two.le 16
    rw [←Real.exp_nat_mul] at h; norm_num at h ⊢; linarith
  calc
    _ ≤ (1/2:ℝ)⁻¹^k*(1/512:ℝ)^k := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [←mul_pow]; norm_num

/-- Von Mangoldt mass under a decaying exponential in the logarithm. -/
def mangoldtLaplaceTerm (η : ℝ) (n : ℕ) : ℝ := Λ n / n * Real.exp (-(η*Real.log n))

/-- The small parameter cancels the pole of `−ζ'/ζ` in the positive mass of the weights. -/
theorem mangoldtLaplaceTerm_sum_bound :
    ∃ C > 0, ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      Summable (mangoldtLaplaceTerm η) ∧ η*(∑' n, mangoldtLaplaceTerm η n) ≤ C := by
  obtain ⟨B,hB,H⟩ := neg_logDeriv_riemannZeta_real_le
  refine ⟨1+B,by linarith,?_⟩
  intro η hη hη'
  let s := ((1+η:ℝ):ℂ)
  have hs : 1 < s.re := by simp [s,hη]
  obtain ⟨hconv,he⟩ := neg_logDeriv_riemannZeta_eq_LSeries hs
  have hsum := Complex.reCLM.hasSum hconv.hasSum
  have hterm (n : ℕ) : (LSeries.term (fun n => (Λ n:ℂ)) s n).re = mangoldtLaplaceTerm η n := by
    by_cases hn : n=0
    · subst n; simp [mangoldtLaplaceTerm]
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,←Complex.cpow_neg]
    have hpow : (n:ℂ)^(-s) = (((n:ℝ)^(-(1+η):ℝ):ℝ):ℂ) := by
      rw [←Complex.ofReal_natCast,show -s = ((-(1+η):ℝ):ℂ) by simp [s],Complex.ofReal_cpow hn'.le]
    rw [hpow,←Complex.ofReal_mul,Complex.ofReal_re]
    dsimp only [mangoldtLaplaceTerm]
    rw [show -(1+η) = -1 + -η by ring, Real.rpow_add hn',Real.rpow_neg_one,
      Real.rpow_def_of_pos hn' (-η), show Real.log n * -η = -(η*Real.log n) by ring]
    ring
  have hh : HasSum (mangoldtLaplaceTerm η) (LSeries (fun n => (Λ n:ℂ)) s).re :=
    hsum.congr_fun fun n => (hterm n).symm
  refine ⟨hh.summable,?_⟩
  rw [hh.tsum_eq,←he]
  have hm := H (1+η) ⟨by linarith,by linarith⟩
  rw [add_sub_cancel_left] at hm
  apply (mul_le_mul_of_nonneg_left hm hη.le).trans
  rw [mul_add,show η*(1/η) = 1 by field_simp]
  linarith [mul_le_mul_of_nonneg_right hη' hB.le]

/-- The finite or infinite character sum detected by a high logarithmic derivative. -/
def turanMangoldtTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (η t : ℝ) (k n : ℕ) : ℂ :=
  ((η * (Λ n/n) * turanWeight k (η*Real.log n) : ℝ):ℂ) * (χ n*(n:ℂ)^(-(t:ℂ)*I))

/-- Exact Dirichlet-series representation for a Taylor coefficient at `1+η+it`. -/
theorem hasSum_turanMangoldtTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {η : ℝ} (hη : 0 < η) (t : ℝ) (k : ℕ) :
    HasSum (turanMangoldtTerm χ η t k)
      (-((η:ℂ)^(k+1))*signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction χ)) (((1+η:ℝ):ℂ)+t*I) k) := by
  let s := ((1+η:ℝ):ℂ)+(t:ℂ)*I
  have hs : 1<s.re := by simp [s,hη]
  have h := signedTaylorCoeff_LSeries_logDeriv (f:=DirichletCharacter.LFunction χ)
    (a:=fun n => χ n*(Λ n:ℂ)) (fun hh => neg_logDeriv_LFunction_eq_LSeries χ hh) hs k
  have hscaled := h.mul_left ((η:ℂ)^(k+1)/(k.factorial:ℂ))
  have hk : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  convert hscaled.congr_fun (g:=turanMangoldtTerm χ η t k) (fun n => ?_) using 1
  · field_simp [s]; ring
  · by_cases hn : n=0
    · subst n; simp [turanMangoldtTerm]
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [show s = ((1+η:ℝ):ℂ)+t*I from rfl,term_iter_factor _ hn]
    have hpow : (n:ℝ)^(-(1+η)) = (n:ℝ)⁻¹*Real.exp (-(η*Real.log n)) := by
      rw [show -(1+η) = -1 + -η by ring,Real.rpow_add hn',Real.rpow_neg_one,Real.rpow_def_of_pos hn']
      congr 2; ring
    dsimp only [turanMangoldtTerm,turanWeight]
    rw [hpow,pow_succ]
    push_cast
    ring

/-- The absolutely summable weight for the contribution of proper prime powers. -/
def higherPrimePowerWeight (n : ℕ) : ℝ := if n.Prime then 0 else Λ n * (n:ℝ)^(-(3/4:ℝ))

theorem higherPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ higherPrimePowerWeight n := by
  dsimp only [higherPrimePowerWeight]; have h := ArithmeticFunction.vonMangoldt_nonneg (n:=n); split_ifs <;> positivity

theorem summable_higherPrimePowerWeight : Summable higherPrimePowerWeight := by
  let a (n : ℕ) : ℝ := if n.Prime then 0 else Λ n
  have ha (n : ℕ) : 0 ≤ a n := by dsimp only [a]; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  have heq (n : ℕ) : (∑ k ∈ Icc 1 n, a k) = Chebyshev.psi n-Chebyshev.theta n := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
    change (∑ k ∈ Icc 1 n, if k.Prime then 0 else Λ k) = ∑ k ∈ Icc 1 n, if ¬ k.Prime then Λ k else 0
    simp
  have hO : (fun n => ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n => (n:ℝ)^(1/2:ℝ) := by
    apply Asymptotics.IsBigO.of_bound (3*(Real.log 4+4))
    filter_upwards [] with n
    rw [heq,Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    simpa only [Real.sqrt_eq_rpow,mul_comm (Real.log 4+4)] using
      AnalyticNumberTheory.PrimeDistribution.abs_psi_sub_theta_le_mul_sqrt (n:ℝ)
  have hs := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s:=(3/4:ℂ)) hO ha (by norm_num) (by norm_num)
  apply (Complex.reCLM.summable hs).congr
  intro n
  by_cases hn : n=0
  · subst n; simp [higherPrimePowerWeight]
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,←Complex.cpow_neg,
    show (n:ℂ)^(-(3/4:ℂ)) = (((n:ℝ)^(-(3/4:ℝ)):ℝ):ℂ) by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_natCast] using (Complex.ofReal_cpow hn'.le (-(3/4:ℝ))).symm]
  change (((a n:ℝ):ℂ)*_).re = _
  rw [←Complex.ofReal_mul,Complex.ofReal_re]
  dsimp only [a,higherPrimePowerWeight]; split_ifs <;> simp

private lemma norm_turan_term_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {η : ℝ} (hη : 0 ≤ η) (t : ℝ) (m n : ℕ) :
    ‖turanMangoldtTerm χ η t m n‖ ≤ η*(Λ n/n)*turanWeight m (η*Real.log n) := by
  by_cases hn : n=0
  · subst n; simp [turanMangoldtTerm]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have ht : ‖(n:ℂ)^(-(t:ℂ)*I)‖ = 1 := by rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
  have hw := turanWeight_nonneg m (mul_nonneg hη (Real.log_nonneg hn'))
  have hb := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  simp only [turanMangoldtTerm,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ η*(Λ n/n)*turanWeight m (η*Real.log n)),ht,mul_one]
  exact mul_le_of_le_one_right (by positivity) (χ.norm_le_one _)

theorem norm_turan_term_small {q : ℕ} (χ : DirichletCharacter ℂ q)
    {η : ℝ} (hη : 0 ≤ η) (t : ℝ) (m n : ℕ) (hsmall : 1024*(η*Real.log n) ≤ m) :
    ‖turanMangoldtTerm χ η t m n‖ ≤ (1/256:ℝ)^m*η*mangoldtLaplaceTerm η n := by
  have hb := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  have hn : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  apply (norm_turan_term_le χ hη t m n).trans
  apply (mul_le_mul_of_nonneg_left (turanWeight_le_at_small (mul_nonneg hη hn) hsmall) (by positivity : 0 ≤ η*(Λ n/n))).trans_eq
  dsimp only [mangoldtLaplaceTerm]; ring

theorem norm_turan_term_large {q : ℕ} (χ : DirichletCharacter ℂ q)
    {η : ℝ} (hη : 0 ≤ η) (t : ℝ) (m n : ℕ) (hlarge : 64*m ≤ η*Real.log n) :
    ‖turanMangoldtTerm χ η t m n‖ ≤ (1/256:ℝ)^m*η*mangoldtLaplaceTerm (η/4) n := by
  have hb := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  have hn := Real.log_natCast_nonneg n
  apply (norm_turan_term_le χ hη t m n).trans
  apply (mul_le_mul_of_nonneg_left (turanWeight_le_at_large (mul_nonneg hη hn) hlarge) (by positivity : 0 ≤ η*(Λ n/n))).trans_eq
  dsimp only [mangoldtLaplaceTerm]; rw [show η*Real.log n/4 = η/4*Real.log n by ring]; ring

/-- The prime-power contribution is exponentially small in the derivative order,
uniformly over the whole positive half of the small-`η` range. -/
theorem norm_turan_term_nonprime {q : ℕ} (χ : DirichletCharacter ℂ q)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/1024) (t : ℝ) (m n : ℕ) (hnp : ¬n.Prime) :
    ‖turanMangoldtTerm χ η t m n‖ ≤ (1/256:ℝ)^m*η*higherPrimePowerWeight n := by
  by_cases hn : n=0
  · subst n; simp [turanMangoldtTerm,higherPrimePowerWeight]
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hx := mul_nonneg hη.le (Real.log_natCast_nonneg n)
  have hb := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  have hw : turanWeight m (η*Real.log n) ≤ (1/256:ℝ)^m*(n:ℝ)^(1/4:ℝ) := by
    have h := poisson_scale (k:=m) hx (a:=(4*η)⁻¹) (by positivity)
    have heq : (4*η)⁻¹*(η*Real.log n) = Real.log n*(1/4) := by field_simp
    rw [inv_inv,heq,← Real.rpow_def_of_pos hn'] at h
    apply (mul_le_of_le_one_right (div_nonneg (pow_nonneg hx _) (by positivity))
      (Real.exp_le_one_iff.mpr (by linarith : -(η*Real.log n) ≤ 0))).trans
    apply h.trans
    gcongr
    linarith
  apply (norm_turan_term_le χ hη.le t m n).trans
  apply (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ η*(Λ n/n))).trans_eq
  rw [higherPrimePowerWeight,ite_eq_right hnp,show -(3/4:ℝ) = (1/4)-1 by norm_num,
    Real.rpow_sub_one hn'.ne']
  ring

end AnalyticNumberTheory.DirichletLFunctions
