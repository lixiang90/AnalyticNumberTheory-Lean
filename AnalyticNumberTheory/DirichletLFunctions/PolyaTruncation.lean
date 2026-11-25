import AnalyticNumberTheory.DirichletLFunctions.Truncation
import AnalyticNumberTheory.DirichletLFunctions.CharacterSums

/-! # Truncating a nonprincipal L-function using character cancellation -/

noncomputable section

open Complex Finset Filter
open scoped Topology
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- On the entire open right half-plane the ordinary Dirichlet polynomials
of a nonprincipal character converge to its analytically continued L-function. -/
theorem tendsto_dirichletPoly_LFunction {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => dirichletPoly (fun n => χ n) N s) atTop (𝓝 (χ.LFunction s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let B := (q : ℝ) * (1 + ‖s‖ / s.re)
  have hd := ((tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul B
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun N : ℕ => B * (N : ℝ)^(-s.re)) _ (by simpa using hd)
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [norm_sub_rev]
  exact (norm_sub_dirichletPoly_le hχ hN hs).trans_eq (by dsimp only [B]; ring)

/-- Pólya–Vinogradov bounds every interval of character coefficients. Abel
summation then bounds the L-function tail even when `M=0`, with decay at the
first omitted integer `M+1`. -/
theorem norm_LFunction_sub_polynomial_polya {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    ‖χ.LFunction s - dirichletPoly (fun n => χ n) M s‖ ≤
      (4 * Real.sqrt q * Real.log q) * (‖s‖ / s.re) * ((M+1 : ℕ) : ℝ)^(-s.re) := by
  apply le_of_tendsto (((tendsto_dirichletPoly_LFunction hχ hs).sub_const
    (dirichletPoly (fun n => χ n) M s)).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  have hB (k : ℕ) (hk : k ∈ Icc M N) :
      ‖dirichletPartialSum (fun n => χ n) 0 k - dirichletPartialSum (fun n => χ n) 0 M‖ ≤
        4 * Real.sqrt q * Real.log q := by
    rw [dirichletPartialSum_sub_eq_sum_Ioc _ _ (mem_Icc.mp hk).1]
    apply le_trans (le_of_eq (congrArg norm (show (∑ n ∈ Ioc M k, LSeries.term (fun n => χ n) 0 n) =
        ∑ n ∈ Ioc M k, χ n from ?_))) (polya_vinogradov_Ioc hq hχ M k)
    apply sum_congr rfl
    intro n hn
    have hn₀ : n ≠ 0 := Nat.ne_of_gt ((Nat.zero_le M).trans_lt (mem_Ioc.mp hn).1)
    simp [LSeries.term_of_ne_zero hn₀]
  have H := norm_dirichletPartialSum_sub_le (fun n => χ n) (s₀ := 0) (s := s) (by simpa using hs) hMN hB
  simpa only [dirichletPoly_eq_dirichletPartialSum, Complex.zero_re, sub_zero, zero_sub] using H

/-- On the critical line a polynomial extending to `q‖s‖` has uniform
remainder at most `8√‖s‖ log q`. -/
theorem norm_LFunction_sub_polynomial_critical {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : s.re = 1/2) {M : ℕ}
    (hM : (q : ℝ) * ‖s‖ ≤ ((M+1 : ℕ) : ℝ)) :
    ‖χ.LFunction s - dirichletPoly (fun n => χ n) M s‖ ≤ 8 * Real.sqrt ‖s‖ * Real.log q := by
  have hp : 0 < s.re := by rw [hs]; norm_num
  have H := norm_LFunction_sub_polynomial_polya hq hχ hp M
  have hN : 0 < ((M+1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hscale : Real.sqrt q * Real.sqrt ‖s‖ ≤ Real.sqrt ((M+1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
    exact Real.sqrt_le_sqrt hM
  rw [hs, Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at H
  apply H.trans ((div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr ?_)
  calc
    _ = (8 * Real.sqrt ‖s‖ * Real.log q) * (Real.sqrt q * Real.sqrt ‖s‖) := by
      nlinarith only [congrArg (fun z : ℝ => (8 * Real.sqrt q * Real.log q) * z)
        (Real.sq_sqrt (norm_nonneg s))]
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

end AnalyticNumberTheory.DirichletLFunctions
