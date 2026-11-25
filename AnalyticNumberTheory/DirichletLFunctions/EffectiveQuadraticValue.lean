import AnalyticNumberTheory.DirichletLFunctions.CharacterLambert
import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import AnalyticNumberTheory.DirichletLFunctions.Truncation
import AnalyticNumberTheory.AnalyticTools.LambertRemainder

/-!
# An effective lower bound for a real Dirichlet L-value at one

Positive square coefficients give a lower bound for the smoothed convolution
of the character with one. Subtracting the pole of its Lambert kernel leaves a
decreasing weight, so Pólya–Vinogradov controls the error with explicit constants.
-/

open Finset Filter Real
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Exponential smoothing introduces at most the Pólya–Vinogradov error in
the upper bound for the convolution sum. -/
theorem smoothed_zetaMul_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {X : ℝ} (hX : 0<X) :
    ∑' n : ℕ, (χ.zetaMul n).re * exp (-(n:ℝ)/X) ≤
      X * (χ.LFunction 1).re + 4 * sqrt q * log q := by
  let M := 4 * sqrt q * log q
  let w (n : ℕ) := lambertRemainder ((max 1 (n:ℝ))/X)
  have hpos (n : ℕ) : 0 < max 1 (n:ℝ)/X := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left ..)) hX
  have hM : 0 ≤ M := by
    dsimp [M]; exact mul_nonneg (by positivity) (log_nonneg (by exact_mod_cast (show 1≤q by omega)))
  have hw : Antitone w := fun i j hij => antitoneOn_lambertRemainder (hpos i) (hpos j)
    (div_le_div_of_nonneg_right (max_le_max_left (1:ℝ) (show (i:ℝ) ≤ (j:ℝ) by exact_mod_cast hij)) hX.le)
  have hlim := (Complex.continuous_re.tendsto _).comp (tendsto_char_div_nat hχ)
  apply le_of_tendsto_of_tendsto' (tendsto_char_lambert χ hX) ((hlim.const_mul X).add_const M)
  intro N
  let S := ∑ n ∈ Ioc 0 N, (w n : ℂ)*χ n
  have hb : ‖S‖ ≤ M := (norm_sum_Ioc_antitone_weight w (fun n => χ n) hw
    (fun n => lambertRemainder_nonneg (hpos n)) (Nat.zero_le N) hM
    (fun k _ _ => polya_vinogradov_Ioc hq hχ 0 k)).trans
    (mul_le_of_le_one_left hM (lambertRemainder_le_one (hpos 0)))
  have hid : S.re = X * (∑ d ∈ Ioc 0 N, χ d / (d : ℂ)).re -
      ∑ d ∈ Ioc 0 N, (χ d).re / (exp ((d:ℝ)/X)-1) := by
    simp only [S, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.div_natCast_re, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1≤n from (mem_Ioc.mp hn).1)
    simp only [w, max_eq_right hn', lambertRemainder, div_div_eq_mul_div]
    ring
  have hneg := (neg_le_abs S.re).trans ((Complex.abs_re_le_norm S).trans hb)
  change _ ≤ X * (∑ d ∈ Ioc 0 N, χ d / (d:ℂ)).re + M
  linarith only [hneg, hid]

/-- An absolute effective lower bound for a nonprincipal real character,
including imprimitive characters. -/
theorem quadratic_LFunction_one_lower_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hr : χ^2=1) (hχ : χ ≠ 1) :
    1 / (180 * sqrt q * log ((q:ℝ)+2)) ≤ (χ.LFunction 1).re := by
  let M := 4 * sqrt q * log q
  let K := 6*(M+1)
  have hq₁ : 1 ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hM : 0 ≤ M := mul_nonneg (by positivity) (log_nonneg hq₁)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlow := sqrt_floor_le_zetaMul_exp hr (sq_pos_of_pos hK)
  rw [Real.sqrt_sq hK.le] at hlow
  have hupp := smoothed_zetaMul_le hq hχ (sq_pos_of_pos hK)
  have H := hlow.trans hupp
  have he : 1/3 ≤ exp (-1) := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have H₁ := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg ⌊K⌋₊)
  have H₂ := Nat.sub_one_lt_floor K
  change exp (-1)*(⌊K⌋₊:ℝ) ≤ K^2*(χ.LFunction 1).re+M at H
  have H₃ : M+1 ≤ K^2*(χ.LFunction 1).re := by dsimp [K] at H₂; linarith
  have H₄ : 1/(36*(M+1)) ≤ (χ.LFunction 1).re := by
    rw [div_le_iff₀ (by positivity)]
    apply (mul_le_mul_iff_right₀ (show 0 < M+1 by positivity)).mp
    dsimp only [K] at H₃
    nlinarith only [H₃]
  apply le_trans _ H₄
  apply one_div_le_one_div_of_le (by positivity)
  have hs : 1 ≤ sqrt q := by simpa using Real.sqrt_le_sqrt hq₁
  have hl : 1 ≤ log ((q:ℝ)+2) := (Real.log_exp 1).symm.trans_le
    (Real.log_le_log (exp_pos _) (by linarith [Real.exp_one_lt_d9]))
  have hqlog : log q ≤ log ((q:ℝ)+2) := Real.log_le_log (by positivity) (by linarith)
  have hab : 1 ≤ sqrt q * log ((q:ℝ)+2) := one_le_mul_of_one_le_of_one_le hs hl
  dsimp only [M]
  nlinarith only [mul_le_mul_of_nonneg_left hqlog (sqrt_nonneg q), hab]

end AnalyticNumberTheory.DirichletLFunctions
