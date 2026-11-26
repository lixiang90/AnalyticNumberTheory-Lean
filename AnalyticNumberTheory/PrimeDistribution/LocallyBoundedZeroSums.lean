import AnalyticNumberTheory.PrimeDistribution.SharpExplicitFormula

/-!
# Local boundedness of the sharp nontrivial-zero sums

The height may tend to infinity while the physical cutoff ranges through a compact
interval in the open half-line above one, including intervals containing prime powers.
-/

noncomputable section

open Complex Filter Finset MeasureTheory
open scoped Topology Classical ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.PrimeDistribution

private theorem trivial_partial_bound {a x : ℝ} (ha : 1 < a) (hx : a ≤ x) (N : ℕ) :
    ‖∑ n ∈ range N, (x : ℂ)^(trivialZetaZero n)/trivialZetaZero n‖ ≤
      ∑' n, ‖(a : ℂ)^(trivialZetaZero n)/trivialZetaZero n‖ := by
  have ha₀ := zero_lt_one.trans ha
  apply (norm_sum_le ..).trans
  apply (sum_le_sum (g := fun n => ‖(a : ℂ)^(trivialZetaZero n)/trivialZetaZero n‖) ?_).trans
    ((hasSum_cpow_trivialZetaZero_div ha).summable.norm.sum_le_tsum _ (fun _ _ => norm_nonneg _))
  intro n _
  simp only [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha₀, Complex.norm_cpow_eq_rpow_re_of_pos (ha₀.trans_le hx)]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply Real.rpow_le_rpow_of_nonpos ha₀ hx
  simp [trivialZetaZero, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- On every compact interval above one a single bound controls all sharp zero sums at
sufficiently large heights, including at the jumps of the Chebyshev function. -/
theorem eventually_norm_sharpZetaZeroSum_le_on_Icc {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∃ B : ℝ, ∀ᶠ T : ℝ in atTop, ∀ x ∈ Set.Icc a b, ‖sharpZetaZeroSum x T‖ ≤ B := by
  obtain ⟨U,C,hC,H⟩ := exists_expandingPerron_heights
  obtain ⟨K,hK,hstep⟩ := sharpZetaZeroSum_unit_variation
  let v (n : ℕ) : ℂ := Λ n
  let M := ∑' n, ‖LSeries.term v (2 : ℂ) n‖
  let J := ∑' n, ‖(a : ℂ)^(trivialZetaZero n)/trivialZetaZero n‖
  let A : ℂ := 2*Real.pi*I
  have hb := ha.trans_le hab
  have hM : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  have hsum : LSeriesSummable v (2 : ℂ) := LSeriesSummable_vonMangoldt_iff.mpr (by norm_num)
  have hhlim : Tendsto (fun R : ℝ => (Real.log R)^2/R) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
    (tendsto_id.atTop_mul_const (Real.log_pos ha))
  have hv : Tendsto (fun R : ℝ => R^3*Real.exp (-(R*Real.log a))) atTop (𝓝 0) := by
    convert he.div_const ((Real.log a)^3) using 1
    · funext R
      dsimp only [Function.comp_apply, id_eq]
      field_simp [(Real.log_pos ha).ne']
    · simp
  have hgood : ∀ᶠ R : ℝ in atTop, ∀ x ∈ Set.Icc a b, ‖sharpZetaZeroSum x (U R)‖ ≤
      b+‖Complex.log (2*(Real.pi : ℂ))‖+J+(2*b^2)*M+(6*C*b^2+6*C*b^2+4*C)/‖A‖ := by
    filter_upwards [H, eventually_ge_atTop 3, hhlim.eventually_le_const zero_lt_one,
      hv.eventually_le_const zero_lt_one] with R hh hR hhor hleft
    intro x hx
    have hx₁ := ha.trans_le hx.1
    have hx₀ := zero_lt_one.trans hx₁
    have hR₀ : 0 ≤ R := by linarith
    have hU₀ := (sq_nonneg R).trans_lt hh.1
    have hsquare := pow_le_pow_left₀ hx₀.le hx.2 2
    have hH (y : ℝ) (hy : |y| = U R) : ‖zetaPerronHorizontal x R y‖ ≤ 6*C*b^2 := by
      apply (norm_zetaPerronHorizontal_le hx₁ hR hh.1 hy hC (fun σ hσ => hh.2.2.2.1 σ hσ y hy)).trans
      exact (mul_le_of_le_one_right (by positivity) hhor).trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
    have hL : ‖zetaPerronLeft x R (U R)‖ ≤ 4*C := by
      apply (norm_zetaPerronLeft_le hx₁ hR hU₀ hh.2.1 hC hh.2.2.2.2).trans
      apply mul_le_of_le_one_right (by positivity)
      apply le_trans _ hleft
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left
        (Real.log_le_log (zero_lt_one.trans ha) hx.1) hR₀))
    have hD : ‖dirichletContourIntegral v x 2 (U R)‖ ≤ (2*b^2)*M := by
      apply (norm_dirichletContourIntegral_le (c := (2:ℝ)) hx₀ (by norm_num) hU₀ (by simpa only [Complex.ofReal_ofNat] using hsum)).trans
      simpa only [Real.rpow_two, Complex.ofReal_ofNat, M] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num : (0:ℝ)≤2)) hM
    rw [sharpZetaZeroSum_eq_contour hx₀ hU₀ R hh.2.2.1]
    apply (norm_add_le ..).trans
    apply add_le_add
    · apply (norm_sub_le ..).trans
      refine add_le_add ?_ hD
      apply (norm_sub_le ..).trans
      refine add_le_add ?_ (trivial_partial_bound ha hx.1 _)
      apply (norm_sub_le ..).trans
      simpa [abs_of_pos hx₀] using add_le_add_left hx.2 ‖Complex.log (2*(Real.pi : ℂ))‖
    · rw [norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply (norm_add_le ..).trans
      rw [norm_mul, Complex.norm_I, one_mul]
      exact add_le_add ((norm_sub_le ..).trans (add_le_add (hH _ (abs_of_pos hU₀))
        (hH _ (by rw [abs_neg,abs_of_pos hU₀])))) hL
  refine ⟨(b+‖Complex.log (2*(Real.pi : ℂ))‖+J+(2*b^2)*M+(6*C*b^2+6*C*b^2+4*C)/‖A‖)+K*b, ?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually hgood, Real.tendsto_sqrt_atTop.eventually H,
    eventually_ge_atTop 2] with T hg hh hT
  intro x hx
  rw [Real.sq_sqrt (by linarith)] at hh
  have hT₀ : 0 < T := by linarith
  have hdiff := hstep (ha.le.trans hx.1) hT hh.1.le hh.2.1.le
  have hsmall := (div_le_one hT₀).mpr (Real.log_le_self hT₀.le)
  calc
    ‖sharpZetaZeroSum x T‖ ≤ ‖sharpZetaZeroSum x (U (Real.sqrt T))‖ +
      ‖sharpZetaZeroSum x (U (Real.sqrt T))-sharpZetaZeroSum x T‖ := by
        simpa only [sub_sub_cancel] using norm_sub_le (sharpZetaZeroSum x (U (Real.sqrt T)))
          (sharpZetaZeroSum x (U (Real.sqrt T))-sharpZetaZeroSum x T)
    _ ≤ _ := add_le_add (hg x hx) (hdiff.trans ((mul_le_of_le_one_right
      (mul_nonneg hK.le (zero_le_one.trans (ha.le.trans hx.1))) hsmall).trans (mul_le_mul_of_nonneg_left hx.2 hK.le)))

end AnalyticNumberTheory.PrimeDistribution
