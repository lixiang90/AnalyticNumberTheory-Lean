import AnalyticNumberTheory.DirichletLFunctions.PolyaTruncation
import AnalyticNumberTheory.DirichletLFunctions.AbsolutePolynomialBounds
import Mathlib.Analysis.Complex.Liouville

/-! # The logarithm-weighted polynomial approximation to an L-function derivative -/

noncomputable section

open Complex Finset Metric
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Differentiating a finite Dirichlet polynomial inserts the negative logarithm. -/
theorem deriv_dirichletPoly_eq_log_weight (a : ℕ → ℂ) (M : ℕ) (s : ℂ) :
    deriv (dirichletPoly a M) s = dirichletPoly (fun n => -Complex.log n * a n) M s := by
  rw [show dirichletPoly a M = fun z => dirichletPartialSum a z M from
    funext fun z => dirichletPoly_eq_dirichletPartialSum a M z,
    (hasDerivAt_dirichletPartialSum a M s).deriv, dirichletPoly_eq_dirichletPartialSum]

/-- On the critical line, if `M+1 ≥ q(1+‖s‖)`, Cauchy's estimate applied to
the Pólya–Vinogradov remainder gives one extra logarithm for its derivative. -/
theorem norm_deriv_LFunction_sub_polynomial_critical {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : s.re = 1/2) {M : ℕ}
    (hM : (q : ℝ) * (1+‖s‖) ≤ ((M+1 : ℕ) : ℝ)) :
    ‖deriv χ.LFunction s - deriv (dirichletPoly (fun n => χ n) M) s‖ ≤
      16 * Real.exp 1 * Real.sqrt (1+‖s‖) * Real.log q * (4 + Real.log ((M+1 : ℕ) : ℝ)) := by
  let A := ((M+1 : ℕ) : ℝ)
  let U := 1 + ‖s‖
  let δ := (4 + Real.log A)⁻¹
  let F := fun z => χ.LFunction z - dirichletPoly (fun n => χ n) M z
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast Nat.succ_pos M
  have hA₀ := zero_lt_one.trans_le hA
  have hlogA := Real.log_nonneg hA
  have hU : 0 < U := by dsimp [U]; positivity
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1/4 := by
    dsimp only [δ]
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδlog : Real.log A * δ ≤ 1 := by
    calc
      _ ≤ (4+Real.log A) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hscale : Real.sqrt q * Real.sqrt U ≤ Real.sqrt A := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
    exact Real.sqrt_le_sqrt hM
  have hχd := differentiable_LFunction_of_ne_one hχ
  have hPd := differentiable_dirichletPoly (fun n => χ n) M
  have hbound (z : ℂ) (hz : z ∈ sphere s δ) :
      ‖F z‖ ≤ 16 * Real.exp 1 * Real.sqrt U * Real.log q := by
    have he : ‖z-s‖ = δ := by simpa only [dist_eq_norm] using mem_sphere.mp hz
    have hre : |z.re-s.re| ≤ δ := by simpa only [Complex.sub_re, he] using Complex.abs_re_le_norm (z-s)
    have hlower : 1/2 - δ ≤ z.re := by linarith only [(abs_le.mp hre).1, hs]
    have hr : 1/4 ≤ z.re := by linarith
    have hr₀ : 0 < z.re := by linarith
    have hzU : ‖z‖ ≤ U := by
      have ht := norm_le_norm_sub_add z s
      rw [he] at ht
      dsimp only [U]
      linarith
    have hheight : ‖z‖ / z.re ≤ 4*U := (div_le_iff₀ hr₀).mpr (by
      nlinarith only [hzU, mul_le_mul_of_nonneg_left hr hU.le])
    have hpow : A ^ (-z.re) ≤ Real.exp 1 / Real.sqrt A := by
      calc
        _ ≤ A^(-(1/2 : ℝ)+δ) := Real.rpow_le_rpow_of_exponent_le hA (by linarith)
        _ = (Real.sqrt A)⁻¹ * Real.exp (Real.log A * δ) := by
          rw [Real.rpow_add hA₀, Real.rpow_neg hA₀.le, ← Real.sqrt_eq_rpow, Real.rpow_def_of_pos hA₀]
        _ ≤ (Real.sqrt A)⁻¹ * Real.exp 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hδlog) (by positivity)
        _ = _ := by ring
    have h := norm_LFunction_sub_polynomial_polya hq hχ hr₀ M
    apply h.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hheight (by positivity)) hpow
      (Real.rpow_nonneg hA₀.le _) (by positivity)).trans ?_)
    calc
      _ = (16 * Real.exp 1 * Real.sqrt q * U * Real.log q) / Real.sqrt A := by ring
      _ ≤ _ := (div_le_iff₀ (Real.sqrt_pos.mpr hA₀)).mpr (by
        calc
          _ = (16 * Real.exp 1 * Real.sqrt U * Real.log q) * (Real.sqrt q * Real.sqrt U) := by
            nlinarith only [congrArg (fun v : ℝ => (16 * Real.exp 1 * Real.sqrt q * Real.log q) * v)
              (Real.sq_sqrt hU.le)]
          _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity))
  have H := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ (hχd.sub hPd).diffContOnCl hbound
  change ‖deriv F s‖ ≤ _ at H
  rw [show deriv F s = deriv χ.LFunction s - deriv (dirichletPoly (fun n => χ n) M) s from
    deriv_sub (hχd s) (hPd s)] at H
  exact H.trans_eq (by simp [δ, A, U, div_eq_mul_inv])

end AnalyticNumberTheory.DirichletLFunctions
