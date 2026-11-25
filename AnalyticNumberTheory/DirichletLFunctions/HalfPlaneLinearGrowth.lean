import AnalyticNumberTheory.DirichletLFunctions.PolyaDerivativeTruncation

/-! # Linear growth of nonprincipal L-functions on closed right half-planes -/

open Complex Real Metric
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Above real part one quarter, Pólya–Vinogradov at the empty cutoff bounds
the L-function by an explicit constant times the distance from the origin. -/
theorem norm_LFunction_quarter_linear {q : ℕ} [NeZero q] (hq : 2≤q)
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) {s : ℂ} (hs : 1/4 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ (16*Real.sqrt q*Real.log q)*‖s‖ := by
  have hp : 0 < s.re := by linarith
  have H := norm_LFunction_sub_polynomial_polya hq hχ hp 0
  have h : ‖s‖/s.re ≤ 4*‖s‖ := (div_le_iff₀ hp).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hs (norm_nonneg s)])
  simp [dirichletPoly] at H
  exact H.trans ((mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring))

/-- For a fixed modulus, the L-function and its first derivative have at
most linear growth uniformly on the whole half-plane `Re s ≥ 1/2`. -/
theorem norm_LFunction_deriv_halfPlane_linear {q : ℕ} [NeZero q] (hq : 2≤q)
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) {s : ℂ} (hs : 1/2 ≤ s.re) :
    let B := 64*Real.sqrt q*Real.log q*(1+‖s‖)
    ‖χ.LFunction s‖ ≤ B ∧ ‖deriv χ.LFunction s‖ ≤ B := by
  intro B
  let K := 16*Real.sqrt q*Real.log q
  have hK : 0≤K := by dsimp [K]; positivity
  have hval := norm_LFunction_quarter_linear hq hχ (show 1/4≤s.re by linarith)
  have bound (z : ℂ) (hz : z ∈ sphere s (1/4 : ℝ)) : ‖χ.LFunction z‖ ≤ K*(1+‖s‖) := by
    have he : ‖z-s‖ = 1/4 := by simpa only [dist_eq_norm] using mem_sphere.mp hz
    have hdiff := Complex.abs_re_le_norm (z-s)
    rw [Complex.sub_re, he] at hdiff
    have hn := norm_le_norm_sub_add z s
    rw [he] at hn
    exact (norm_LFunction_quarter_linear hq hχ (by linarith only [(abs_le.mp hdiff).1,hs])).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hn]) hK)
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/4)
    (differentiable_LFunction_of_ne_one hχ).diffContOnCl bound
  constructor
  · change ‖χ.LFunction s‖ ≤ 64*Real.sqrt q*Real.log q*(1+‖s‖)
    apply hval.trans
    calc
      _ ≤ K*(1+‖s‖) := mul_le_mul_of_nonneg_left (by linarith) hK
      _ ≤ 4*(K*(1+‖s‖)) := by nlinarith only [mul_nonneg hK (by positivity : 0≤1+‖s‖)]
      _ = _ := by dsimp [K]; ring
  · exact hder.trans_eq (by dsimp [K,B]; ring)

end AnalyticNumberTheory.DirichletLFunctions
