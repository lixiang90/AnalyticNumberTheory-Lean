import AnalyticNumberTheory.AnalyticTools.LambertDivisors
import AnalyticNumberTheory.DirichletLFunctions.QuadraticConvolution

/-!
# The exponentially smoothed convolution of a character with one

Expanding the geometric kernel and grouping by the product of the two
positive summation indices produces the coefficients of ζ(s)L(s,χ).
-/

open Real Finset Filter ArithmeticFunction
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem char_lambert_factor {X : ℝ} (hX : 0<X) (n : ℕ) :
    exp (-1/X)^n / (1-exp (-1/X)^n) = 1/(exp ((n:ℝ)/X)-1) := by
  have e : exp (-1/X)^n = (exp ((n:ℝ)/X))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
  rw [e]
  by_cases h : exp ((n:ℝ)/X)=1
  · simp [h]
  · field_simp [h, (exp_pos ((n:ℝ)/X)).ne', sub_ne_zero.mpr h]

/-- The ordinary partial sums of the Lambert expansion converge to the
exponentially smoothed sum of the real convolution coefficients. -/
theorem tendsto_char_lambert {q : ℕ} (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0<X) :
    Tendsto (fun N : ℕ => ∑ d ∈ Ioc 0 N, (χ d).re/(exp ((d:ℝ)/X)-1)) atTop
      (𝓝 (∑' n : ℕ, (χ.zetaMul n).re * exp (-(n:ℝ)/X))) := by
  let r := exp (-1/X)
  have hr : 0 ≤ r := (exp_pos _).le
  have hr' : r < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hX)
  have hnorm : ‖r‖<1 := by rwa [Real.norm_of_nonneg hr]
  have hrpow (n : ℕ) : r^n=exp (-(n:ℝ)/X) := by rw [← Real.exp_nat_mul]; congr 1; ring
  let f (n : ℕ) := (χ n).re / (exp ((n:ℝ)/X)-1)
  have hchar (n : ℕ) : |(χ n).re|≤1 := (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
  have hfac (n : ℕ) : f n = (χ n).re * (r^n/(1-r^n)) := by
    rw [char_lambert_factor hX]; dsimp only [f]; ring
  have hs : Summable f := by
    have H : Summable fun n : ℕ => r^n/(1-r^n) := by simpa using summable_norm_pow_mul_geometric_div_one_sub 0 hnorm
    apply Summable.of_norm_bounded H.norm
    intro n; rw [hfac, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hchar _)
  have hconv (n : ℕ) : (χ.zetaMul n).re = ∑ d ∈ n.divisors, (χ d).re := by
    rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply, Complex.re_sum]
    exact sum_congr rfl fun d hd => by simp [toArithmeticFunction,(Nat.pos_of_mem_divisors hd).ne']
  have hsum : ∑' d : ℕ+, f d = ∑' n : ℕ, (χ.zetaMul n).re * exp (-(n:ℝ)/X) := by
    simp_rw [hfac]
    rw [lambert_divisor_sum hchar hr hr', ← tsum_zero_pnat_eq_tsum_nat (summable_zetaMul_re_exp χ hX)]
    simp only [ArithmeticFunction.map_zero, Complex.zero_re, zero_mul, zero_add]
    exact tsum_congr fun n => by rw [hconv, hrpow]
  have hshift : Summable (fun n : ℕ => f (n+1)) := hs.comp_injective Nat.succ_injective
  have ht := hshift.hasSum.tendsto_sum_nat
  rw [← tsum_pnat_eq_tsum_succ (f:=f), hsum] at ht
  convert ht using 1
  funext N
  change ∑ n ∈ Ioc 0 N, f n = ∑ n ∈ range N, f (n+1)
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Ioc_succ_top (Nat.zero_le _), sum_range_succ, ih]

end AnalyticNumberTheory.DirichletLFunctions
