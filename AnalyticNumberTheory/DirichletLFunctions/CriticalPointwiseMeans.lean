import AnalyticNumberTheory.DirichletLFunctions.CriticalPolynomialEnergy
import AnalyticNumberTheory.DirichletLFunctions.PolyaDerivativeTruncation

/-! # Pointwise critical-line means of L-functions and their first derivatives -/

noncomputable section

open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

private lemma log_coefficient_bound {N n : ℕ} (hn : n ∈ Icc 1 N) :
    ‖-Complex.log (n : ℂ)‖ ≤ Real.log (N : ℝ) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [norm_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n),
    Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn₁)]
  exact Real.log_le_log (zero_lt_one.trans_le hn₁) (Nat.cast_le.mpr (mem_Icc.mp hn).2)

/-- At a single point of the critical line, average over the nonprincipal
characters of one modulus. With `U=1+‖s‖`, the mean square of `L` costs
two logarithms of `qU`, and the mean square of `L′` costs four. -/
theorem nonprincipal_critical_pointwise_means :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {s : ℂ}, s.re = 1/2 →
      let U := 1 + ‖s‖
      let L := 1 + Real.log ((q : ℝ)*U)
      (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖χ.LFunction s‖^2) ≤ C * q.totient * U * L^2 ∧
      (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖deriv χ.LFunction s‖^2) ≤ C * q.totient * U * L^4 := by
  let C := 140 + 2 * (80 * Real.exp 1)^2
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro q _ hq s hs U L
  let Y := (q : ℝ)*U
  let N := ⌈Y⌉₊
  let Φ := (q.totient : ℝ)
  let P (χ : DirichletCharacter ℂ q) := dirichletPoly (fun n => χ n) N
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < q := by linarith
  have hU : 1 ≤ U := by dsimp only [U]; linarith [norm_nonneg s]
  have hU₀ := zero_lt_one.trans_le hU
  have hφ : 0 ≤ Φ := Nat.cast_nonneg _
  have hqY : (q : ℝ) ≤ Y := le_mul_of_one_le_right hq₀.le hU
  have hY := hq₂.trans hqY
  have hY₀ := hq₀.trans_le hqY
  have hNlo : Y ≤ (N : ℝ) := Nat.le_ceil Y
  have hN₁ : (1 : ℝ) ≤ N := by linarith
  have hN₀ := zero_lt_one.trans_le hN₁
  have hM : Y ≤ ((N+1 : ℕ) : ℝ) := by push_cast; linarith
  have hceil : (N : ℝ) < Y+1 := Nat.ceil_lt_add_one hY₀.le
  have hupper : ((N+1 : ℕ) : ℝ) ≤ 2*Y := by push_cast; linarith
  have hlength : 1 + (N : ℝ)/q ≤ 3*U := by
    have h := (div_le_iff₀ hq₀).mpr (show (N : ℝ) ≤ 2*U*q by
      dsimp only [Y] at hceil hY
      nlinarith only [hceil, hY])
    linarith only [h, hU]
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg (by linarith : 1 ≤ Y)]
  have hL₀ := zero_lt_one.trans_le hL
  have hlogq := Real.log_nonneg (show (1 : ℝ) ≤ q by linarith)
  have hqL : Real.log q ≤ L := by
    have he := Real.log_le_log hq₀ hqY
    change Real.log q ≤ 1 + Real.log Y
    linarith
  have hlogA : Real.log ((N+1 : ℕ) : ℝ) ≤ L := by
    have hh := Real.log_le_log (by positivity) hupper
    rw [Real.log_mul (by norm_num) hY₀.ne'] at hh
    change _ ≤ 1+Real.log Y
    linarith only [hh, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogN : Real.log N ≤ L := (Real.log_le_log hN₀ (by push_cast; linarith : (N : ℝ) ≤ ((N+1 : ℕ) : ℝ))).trans hlogA
  have hlogN₀ := Real.log_nonneg hN₁
  have hLsq : L ≤ L^2 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 2)
  have hsumlog : 1 + Real.log N ≤ 2*L^2 := by linarith
  have hmain := mul_le_mul_of_nonneg_left hlength hφ
  have hratio : (q : ℝ)*‖s‖ ≤ ((N+1 : ℕ) : ℝ) := (mul_le_mul_of_nonneg_left
    (by dsimp only [U]; linarith : ‖s‖ ≤ U) hq₀.le).trans hM
  have hp₀ : (∑ χ : DirichletCharacter ℂ q, ‖P χ s‖^2) ≤ 6*Φ*U*L^2 := by
    have hh := critical_polynomial_energy_of_bound (q := q) (fun _ => (1 : ℂ)) (N := N)
      (B := 1) (fun _ _ => (norm_one ..).le) hs
    simp only [one_mul, one_pow] at hh
    apply hh.trans ((mul_le_mul hmain hsumlog (by positivity) (by positivity)).trans_eq ?_)
    ring
  have herr₀ (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
      ‖χ.LFunction s - P χ s‖ ≤ 8*Real.sqrt U*L := by
    have hh := norm_LFunction_sub_polynomial_critical hq hne hs hratio
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (by dsimp only [U]; linarith)) (by norm_num)) hqL hlogq (by positivity))
  have hp₁ : (∑ χ : DirichletCharacter ℂ q, ‖deriv (P χ) s‖^2) ≤ 6*Φ*U*L^4 := by
    simp only [P, deriv_dirichletPoly_eq_log_weight]
    apply (critical_polynomial_energy_of_bound _ (fun _ hn => log_coefficient_bound hn) hs).trans
    have hweighted := mul_le_mul (pow_le_pow_left₀ hlogN₀ hlogN 2) hsumlog (by positivity) (sq_nonneg L)
    exact (mul_le_mul hmain hweighted (by positivity) (by positivity)).trans_eq (by ring)
  have herr₁ (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
      ‖deriv χ.LFunction s - deriv (P χ) s‖ ≤ (80 * Real.exp 1)*Real.sqrt U*L^2 := by
    have hh := norm_deriv_LFunction_sub_polynomial_critical hq hne hs hM
    have h₄ : 4+Real.log ((N+1 : ℕ) : ℝ) ≤ 5*L := by linarith
    have hn : 0 ≤ Real.log ((N+1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
    exact hh.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hqL (by positivity : 0 ≤ 16 * Real.exp 1 * Real.sqrt U))
      h₄ (by positivity) (by positivity)).trans_eq (by ring))
  have h₀ := nonprincipal_square_sum_le_of_approx _ _ herr₀ hp₀
  have h₁ := nonprincipal_square_sum_le_of_approx _ _ herr₁ hp₁
  have hsqrt := Real.sq_sqrt hU₀.le
  have he₀ : (8*Real.sqrt U*L)^2 = 64*U*L^2 := by rw [mul_pow, mul_pow, hsqrt]; ring
  have he₁ : ((80 * Real.exp 1)*Real.sqrt U*L^2)^2 = (80*Real.exp 1)^2*U*L^4 := by
    rw [mul_pow, mul_pow, hsqrt]; ring
  rw [he₀] at h₀
  rw [he₁] at h₁
  have hC₀ : 140 ≤ C := le_add_of_nonneg_right (by positivity)
  have hC₁ : 12 + 2*(80*Real.exp 1)^2 ≤ C := by dsimp only [C]; linarith
  change (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖χ.LFunction s‖^2) ≤ C*Φ*U*L^2 ∧
    (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖deriv χ.LFunction s‖^2) ≤ C*Φ*U*L^4
  constructor
  · apply h₀.trans
    change 2*(6*Φ*U*L^2) + 2*Φ*(64*U*L^2) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right hC₀ (by positivity : 0 ≤ Φ*U*L^2)]
  · apply h₁.trans
    change 2*(6*Φ*U*L^4) + 2*Φ*((80*Real.exp 1)^2*U*L^4) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right hC₁ (by positivity : 0 ≤ Φ*U*L^4)]

end AnalyticNumberTheory.DirichletLFunctions
