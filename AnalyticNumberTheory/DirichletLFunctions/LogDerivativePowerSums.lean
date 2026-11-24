import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LocalPowerSums
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# Positivity for shifted logarithmic derivatives

The four factors ζ(s), L(s,χ), L(s+it,ψ), L(s+it,χψ) have a nonnegative
combined logarithmic-derivative Dirichlet series on the real axis when χ
is real. Each successive signed derivative introduces the nonnegative
weight (log n)^k.
-/

noncomputable section
open Complex Filter Set
open scoped Topology ArithmeticFunction
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

theorem signedTaylorCoeff_LSeries_logDeriv {f : ℂ → ℂ} {a : ℕ → ℂ}
    (h : ∀ {s : ℂ}, 1<s.re → LSeriesSummable a s ∧ -deriv f s / f s = LSeries a s)
    {s : ℂ} (hs : 1<s.re) (k : ℕ) :
    HasSum (fun n => LSeries.term (LSeries.logMul^[k] a) s n)
      (-(k.factorial:ℂ)*signedTaylorCoeff (logDeriv f) s k) := by
  have ha : LSeries.abscissaOfAbsConv a ≤ (1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy => (h (by simpa using hy)).1)
  have hb : LSeries.abscissaOfAbsConv a < s.re := ha.trans_lt (by exact_mod_cast hs)
  have hsum : LSeriesSummable (LSeries.logMul^[k] a) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa only [LSeries.abscissaOfAbsConv_logPowMul] using hb)
  have he : logDeriv f =ᶠ[𝓝 s] fun w => -LSeries a w := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with w hw
    simpa [logDeriv,neg_div] using congrArg Neg.neg (h hw).2
  rw [signedTaylorCoeff_congr he,signedTaylorCoeff,iteratedDeriv_fun_neg,LSeries_iteratedDeriv k hb]
  have hk : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hsg : (-1:ℂ)^k*(-1)^k=1 := by rw [←mul_pow]; simp
  convert hsum.hasSum using 1
  change _ = LSeries _ s
  calc
    _ = ((k.factorial:ℂ)/(k.factorial:ℂ))*((-1:ℂ)^k*(-1)^k)*LSeries (LSeries.logMul^[k] a) s := by ring
    _ = _ := by rw [div_self hk,hsg,one_mul,one_mul]

private theorem logMul_iter_apply (a : ℕ → ℂ) (n k : ℕ) :
    (LSeries.logMul^[k] a) n = (Complex.log n)^k * a n := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply',LSeries.logMul,ih,pow_succ',mul_assoc]

theorem term_iter_factor (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) (σ t : ℝ) :
    LSeries.term (LSeries.logMul^[k] a) (σ+t*I) n =
      (((Real.log n)^k*(n:ℝ)^(-σ):ℝ):ℂ)*(a n*(n:ℂ)^(-(t:ℂ)*I)) := by
  have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn,logMul_iter_apply,div_eq_mul_inv,← Complex.cpow_neg,
    show -((σ:ℂ)+t*I) = (-(σ:ℂ))+ (-(t:ℂ)*I) by ring,Complex.cpow_add _ _ hc]
  have hg : (n:ℂ)^(-(σ:ℂ)) = (((n:ℝ)^(-σ):ℝ):ℂ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_neg,Complex.ofReal_cpow hn']
  rw [hg,← Complex.ofReal_natCast,← Complex.ofReal_log hn']
  push_cast
  ring

/-- Positivity for every derivative order, at any vertical shift. Only the
unshifted character must be real. -/
theorem shifted_four_logDeriv_power_nonpos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hr : IsReal χ) (ψ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1<σ) (t : ℝ) (k : ℕ) :
    (signedTaylorCoeff (logDeriv riemannZeta) σ k).re +
      (signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction χ)) σ k).re +
      (signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction ψ)) (σ+t*I) k).re +
      (signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction (χ*ψ))) (σ+t*I) k).re ≤ 0 := by
  have h₀ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)) (fun h => neg_logDeriv_riemannZeta_eq_LSeries h)
    (by simpa using hσ) k
  have h₁ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)) (fun h => neg_logDeriv_LFunction_eq_LSeries χ h)
    (by simpa using hσ) k
  have h₂ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)+t*I) (fun h => neg_logDeriv_LFunction_eq_LSeries ψ h)
    (by simpa using hσ) k
  have h₃ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)+t*I) (fun h => neg_logDeriv_LFunction_eq_LSeries (χ*ψ) h)
    (by simpa using hσ) k
  have h := Complex.reCLM.hasSum (((h₀.add h₁).add h₂).add h₃)
  have hp := h.nonneg (fun n => by
    simp only [Complex.reCLM_apply,Complex.add_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    have hfirst (a : ℕ → ℂ) : LSeries.term (LSeries.logMul^[k] a) σ n =
        (((Real.log n)^k*(n:ℝ)^(-σ):ℝ):ℂ)*a n := by simpa using term_iter_factor a hn k σ 0
    rw [hfirst,hfirst,term_iter_factor _ hn,term_iter_factor _ hn]
    let u := ψ n*(n:ℂ)^(-(t:ℂ)*I)
    have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hv : ‖(n:ℂ)^(-(t:ℂ)*I)‖ = 1 := by
      rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
    have hu : ‖u‖ ≤ 1 := by dsimp [u]; rw [norm_mul,hv,mul_one]; exact norm_char_le_one ψ _
    have hu' := (abs_le.mp ((Complex.abs_re_le_norm u).trans hu)).1
    have hχ' := (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (norm_char_le_one χ _))).1
    have him := hr (n:ZMod q)
    have heq : ((χ*ψ) n : ℂ)*(Λ n:ℂ)*(n:ℂ)^(-(t:ℂ)*I) = (Λ n:ℂ)*(χ n*u) := by
      change (χ n*ψ n)*_ * _ = _; dsimp [u]; ring
    have heq' : (ψ n*(Λ n:ℂ))*(n:ℂ)^(-(t:ℂ)*I) = (Λ n:ℂ)*u := by dsimp [u]; ring
    rw [heq,heq']
    simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      mul_zero,sub_zero,him,zero_mul]
    have hw : 0 ≤ (Real.log n)^k*(n:ℝ)^(-σ)*Λ n :=
      mul_nonneg (mul_nonneg (pow_nonneg (Real.log_nonneg hn') _) (Real.rpow_nonneg (by positivity) _))
        ArithmeticFunction.vonMangoldt_nonneg
    nlinarith only [mul_nonneg hw (mul_nonneg (by linarith : 0≤1+(χ n).re) (by linarith : 0≤1+u.re))])
  simp only [Complex.reCLM_apply,Complex.add_re,neg_mul,Complex.neg_re,
    Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hp
  have hk : 0<(k.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  by_contra! hbad
  nlinarith only [hp,mul_pos hk hbad]

end AnalyticNumberTheory.DirichletLFunctions
