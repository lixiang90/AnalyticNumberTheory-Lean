import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import AnalyticNumberTheory.DirichletLFunctions.Truncation

/-!
# Finite zero detection for Dirichlet L-functions

Abel summation bounds the error of a length-`N` truncation in terms of
the modulus, the height, and the real part. At a zero, multiplication by
a truncated Möbius polynomial detects a large sum supported on `(N,N²]`.
-/

noncomputable section

open Finset Complex MeasureTheory
open scoped Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- A finite partial sum for a nonprincipal character approximates its L-function
throughout `Re s > 0`, with explicit dependence on the modulus and the height. -/
theorem norm_LFunction_sub_dirichletPoly_le {q N : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s - dirichletPoly (fun n => χ n) N s‖ ≤
      q * (N:ℝ)^(-s.re) * (1 + ‖s‖ / s.re) :=
  norm_sub_dirichletPoly_le hχ hN hs

/-- The product of the Möbius twist and the character polynomial consists of
one constant and the twisted high-frequency detector. -/
theorem dirichletDetector_product_eq_one_add {q N : ℕ} (χ : DirichletCharacter ℂ q)
    (hN : 1 ≤ N) (s : ℂ) :
    dirichletPoly (fun n => (μ n:ℂ)*χ n) N s * dirichletPoly (fun n => χ n) N s =
      1 + ∑ n ∈ Ioc N (N^2), zetaDetectorCoeff N n * χ n * (n:ℂ)^(-s) := by
  rw [zetaDetector_product_twist (fun n : ℕ => χ n) (by intro m n; simp),
    dirichletPoly, ← sum_filter_add_sum_filter_not (Icc 1 (N^2)) (fun n => n ≤ N)]
  have hNN : N ≤ N^2 := by nlinarith
  have hs : (Icc 1 (N^2)).filter (· ≤ N) = Icc 1 N := by ext n; simp only [mem_filter,mem_Icc]; omega
  have ht : (Icc 1 (N^2)).filter (fun n => ¬n ≤ N) = Ioc N (N^2) := by ext n; simp only [mem_filter,mem_Icc,mem_Ioc]; omega
  rw [hs,ht]
  congr 1
  rw [sum_eq_single 1]
  · simp [zetaDetectorCoeff_of_le hN]
  · intro n hn hn'
    simp [zetaDetectorCoeff_of_le (mem_Icc.mp hn).2, hn']
  · simp [hN]

/-- The twisted Möbius polynomial has size at most twice the square root of
its length on and to the right of the critical line. -/
lemma norm_moebiusCharPoly_le {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1/2 ≤ s.re) :
    ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) N s‖ ≤ 2*Real.sqrt N := by
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum _).trans (DivisorProblems.sum_Icc_inv_sqrt_le N)
  intro n hn
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (mem_Icc.mp hn).1, neg_re]
  have hc : ‖(μ n:ℂ)‖ * ‖χ n‖ ≤ 1 := mul_le_one₀ (norm_moebius_complex_le _) (norm_nonneg _) (χ.norm_le_one _)
  apply (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
  rw [one_mul, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow_of_exponent_le hnr (by linarith)

/-- Every zero on or to the right of the three-quarters line forces a large
Möbius detector. The cutoff can be chosen uniformly for a family of moduli
and heights, including real zeros. -/
theorem dirichletDetector_large_at_zero {q N : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hN : 1 ≤ N)
    {s : ℂ} (hs : 3/4 ≤ s.re) (hz : DirichletCharacter.LFunction χ s = 0)
    (hcut : 4*q*(1+‖s‖/s.re) ≤ (N:ℝ)^(1/4:ℝ)) :
    1/2 ≤ ‖∑ n ∈ Ioc N (N^2), zetaDetectorCoeff N n * χ n * (n:ℂ)^(-s)‖ := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hsr : 0 < s.re := by linarith
  let A := (q:ℝ)*(1+‖s‖/s.re)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpower := Real.rpow_le_rpow_of_exponent_le hn (by linarith : -s.re ≤ -(3/4:ℝ))
  have hp := norm_LFunction_sub_dirichletPoly_le hχ hN hsr
  rw [hz, zero_sub, norm_neg] at hp
  have hp' : ‖dirichletPoly (fun n => χ n) N s‖ ≤ A*(N:ℝ)^(-(3/4:ℝ)) := by
    apply hp.trans
    change _ ≤ (q:ℝ)*(1+‖s‖/s.re)*_
    calc
      _ = (q:ℝ)*(1+‖s‖/s.re)*(N:ℝ)^(-s.re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower hA
  have hm := norm_moebiusCharPoly_le (N:=N) (s:=s) χ (by linarith)
  have hbd : 2*Real.sqrt N*(A*(N:ℝ)^(-(3/4:ℝ))) ≤ 1/2 := by
    rw [Real.sqrt_eq_rpow, show 2*(N:ℝ)^(1/2:ℝ)*(A*(N:ℝ)^(-(3/4:ℝ))) =
      2*A*((N:ℝ)^(1/2:ℝ)*(N:ℝ)^(-(3/4:ℝ))) by ring, ← Real.rpow_add hn0]
    norm_num
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    dsimp only [A]
    linarith
  have hprod := (mul_le_mul hm hp' (norm_nonneg _) (by positivity)).trans hbd
  rw [← norm_mul, dirichletDetector_product_eq_one_add χ hN] at hprod
  have htri := norm_sub_norm_le (1:ℂ) (-(∑ n ∈ Ioc N (N^2), zetaDetectorCoeff N n * χ n * (n:ℂ)^(-s)))
  rw [norm_one, norm_neg, sub_neg_eq_add] at htri
  linarith

end AnalyticNumberTheory.PrimeDistribution
