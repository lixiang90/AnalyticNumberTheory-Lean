import AnalyticNumberTheory.AnalyticTools.SelbergKernel
import AnalyticNumberTheory.PrimeDistribution.ShiftedMangoldtMean
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.RiemannZeta.PoissonZeroSum
import AnalyticNumberTheory.RiemannZeta.TrivialZeroBounds

/-! # Bounds for the individual terms of Selberg's explicit formula -/

noncomputable section

open Complex Finset
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Chebyshev's estimate bounds the smoothed von Mangoldt polynomial uniformly in
the closed right half-plane by a constant times its outer cutoff. -/
theorem norm_selbergMangoldt_sum_le {s : ℂ} (hs : 0 ≤ s.re) {u : ℝ} (hu : 0 < u) :
    ‖logTaperedSum (powMul (-s) (fun n => (Λ n : ℂ))) u‖ ≤ (Real.log 4+4) * Real.exp (u+u) := by
  apply (norm_logTaperedSum_le _ hu).trans
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self (Real.exp_pos (u+u)).le)
  rw [psi_eq_sum_Icc]
  apply sum_le_sum
  intro n hn
  have hn₁ := (mem_Icc.mp hn).1
  rw [powMul, ite_eq_right (Nat.ne_of_gt hn₁), norm_mul, Complex.norm_natCast_cpow_of_pos hn₁,
    Complex.neg_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn₁) (neg_nonpos.mpr hs))

private theorem selberg_pole_bound {s : ℂ} (hs : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {u : ℝ} (hu : 1 ≤ u) :
    ‖logarithmicPoleSlope (1-s) u u‖ ≤ 2 * Real.exp (u+u) := by
  have hu₀ := zero_lt_one.trans_le hu
  have ht₀ : s.im ≠ 0 := abs_pos.mp (zero_lt_one.trans_le ht)
  have H := norm_logarithmicPoleSlope_le_height (ω := 1-s) (by simpa using ht₀) u hu₀.ne'
  simp only [Complex.sub_re, Complex.one_re, abs_of_pos hu₀, Complex.sub_im, Complex.one_im,
    zero_sub, even_two.neg_pow] at H
  have hr : Real.exp ((1-s.re)*u) ≤ Real.exp u := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hs hu₀.le]
  have hden : 1 ≤ u * s.im^2 := by
    apply one_le_mul_of_one_le_of_one_le hu
    nlinarith only [sq_abs s.im, ht, sq_nonneg (|s.im|-1)]
  refine H.trans ((div_le_self (by positivity) hden).trans ?_)
  have hx := Real.one_le_exp_iff.mpr hu₀.le
  calc
    _ ≤ Real.exp u * (Real.exp u+Real.exp u) := by gcongr
    _ = 2 * Real.exp (u+u) := by rw [Real.exp_add]; ring

private theorem selberg_trivial_bound {s : ℂ} (hs : 0 ≤ s.re) {u : ℝ} (hu : 1 ≤ u) :
    ‖∑' n, logarithmicPoleSlope (trivialZetaZero n-s) u u‖ ≤ 2 := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left (1:ℝ)
  apply (tsum_of_norm_bounded hg ?_).trans_eq (by norm_num)
  intro n
  have hr : (trivialZetaZero n-s).re ≤ (trivialZetaZero n).re := by rw [Complex.sub_re]; linarith
  have ht : (trivialZetaZero n).re ≤ -2 := by rw [re_trivialZetaZero]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnorm : 1 ≤ ‖trivialZetaZero n-s‖ := by
    have hb := Complex.abs_re_le_norm (trivialZetaZero n-s)
    linarith [neg_le_abs (trivialZetaZero n-s).re]
  have he (v : ℝ) (hv : 1 ≤ v) : Real.exp ((trivialZetaZero n-s).re*v) ≤ (1/2 : ℝ)^(n+1) :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr (zero_le_one.trans hv))).trans
      (exp_re_trivialZetaZero_le_half_pow n hv)
  apply (norm_logarithmicPoleSlope_le_endpoints (norm_pos_iff.mp (zero_lt_one.trans_le hnorm)) u
    (zero_lt_one.trans_le hu).ne').trans
  refine (div_le_self (by positivity) hnorm).trans ?_
  exact (add_le_add (he _ (by linarith)) (he _ hu)).trans_eq (by rw [pow_succ]; ring)

/-- Once the horizontal displacement δ satisfies δu ≥ 2, the nontrivial-zero
term costs at most exp(−δu) times its Poisson mass. -/
theorem norm_selberg_zero_sum_le (Z : ZetaZeroEnumeration) (hRH : RiemannHypothesisProp)
    (s : ℂ) {u : ℝ} (hu : 0 < u) (hδu : 2 ≤ (s.re-1/2)*u) :
    ‖∑' n, logarithmicPoleSlope (Z.zero n-s) u u‖ ≤ Real.exp (-((s.re-1/2)*u)) * Z.poissonMass s := by
  have H := (Z.summable_inv_sq_sub s).hasSum.mul_left (Real.exp (-((s.re-1/2)*u)) * (s.re-1/2))
  refine (tsum_of_norm_bounded H (fun n => norm_selbergKernel_le_poisson (by
    rw [Complex.sub_re, riemannHypothesisProp_iff_criticalStripZeros.mp hRH _ (Z.mem_strip n)]
    ring) hu hδu)).trans_eq ?_
  unfold ZetaZeroEnumeration.poissonMass
  ring

/-- The explicit formula bounds ζ′/ζ by a finite polynomial contribution and
an exponentially discounted Poisson mass. The estimate holds for either sign of t. -/
theorem norm_logDeriv_selberg_le (Z : ZetaZeroEnumeration) (hRH : RiemannHypothesisProp)
    {s : ℂ} (hs : 1/2 < s.re) (ht : 1 ≤ |s.im|) {u : ℝ} (hu : 1 ≤ u) (hδu : 2 ≤ (s.re-1/2)*u) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (Real.log 4+8) * Real.exp (u+u) + Real.exp (-((s.re-1/2)*u)) * Z.poissonMass s := by
  have hs₀ : 0 ≤ s.re := by linarith
  have hs₁ : s ≠ 1 := fun he => by rw [he, Complex.one_im, abs_zero] at ht; linarith
  have hζ := riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH s hs
  have hu₀ := zero_lt_one.trans_le hu
  have H := congrArg norm (selberg_logDeriv_explicit_formula Z hs₁ hζ hu₀)
  rw [neg_div, norm_neg] at H
  rw [H]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _)
    (norm_selberg_zero_sum_le Z hRH s hu₀ hδu))) (selberg_trivial_bound hs₀ hu)).trans ?_
  linarith [norm_selbergMangoldt_sum_le hs₀ hu₀, selberg_pole_bound hs₀ ht hu,
    Real.one_le_exp_iff.mpr (show 0 ≤ u+u by linarith)]

end AnalyticNumberTheory.PrimeDistribution
