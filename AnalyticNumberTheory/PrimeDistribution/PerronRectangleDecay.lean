import AnalyticNumberTheory.PrimeDistribution.ExpandingPerronRectangles

/-! # Vanishing of the other three sides of a sharp Perron rectangle -/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.PrimeDistribution

/-- Horizontal integral, directed from the negative odd edge to real part two. -/
def zetaPerronHorizontal (x R y : ℝ) : ℂ :=
  ∫ σ : ℝ in perronLeftEdge R..2, zetaPerronIntegrand x ((σ : ℂ)+y*I)

/-- The left vertical integral, directed upwards and parametrized by the ordinate. -/
def zetaPerronLeft (x R T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T, zetaPerronIntegrand x ((perronLeftEdge R : ℂ)+y*I)

private theorem norm_integrand {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖zetaPerronIntegrand x s‖ = ‖logDeriv riemannZeta s‖ * x^s.re / ‖s‖ := by
  rw [zetaPerronIntegrand, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- Uniform bound for either horizontal edge in an expanding good-height rectangle. -/
theorem norm_zetaPerronHorizontal_le {x R T y C : ℝ} (hx : 1<x) (hR : 3 ≤ R) (hT : R^2 < T)
    (hy : |y|=T) (hC : 0 < C) (hbound : ∀ σ ∈ Icc (perronLeftEdge R) 2,
      ‖logDeriv riemannZeta ((σ : ℂ)+y*I)‖ ≤ C*(Real.log R)^2) :
    ‖zetaPerronHorizontal x R y‖ ≤ (6*C*x^2)*((Real.log R)^2/R) := by
  have hx₀ := zero_lt_one.trans hx
  have hR₀ : 0 < R := by linarith
  obtain ⟨ha, ha'⟩ := perronLeftEdge_bounds hR
  have hwidth : |2-perronLeftEdge R| ≤ 6*R := by rw [abs_of_nonneg (by linarith)]; linarith
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := perronLeftEdge R) (b := 2)
    (f := fun σ : ℝ => zetaPerronIntegrand x ((σ : ℂ)+y*I)) (C := C*(Real.log R)^2*x^2/R^2) (by
      intro σ hσ
      have hm : σ ∈ Icc (perronLeftEdge R) 2 := Ioc_subset_Icc_self
        (by simpa only [uIoc_of_le (by linarith : perronLeftEdge R ≤ 2)] using hσ)
      have hden : R^2 ≤ ‖(σ : ℂ)+y*I‖ := hT.le.trans (by
        simpa only [←hy, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
          using Complex.abs_im_le_norm ((σ : ℂ)+y*I))
      rw [norm_integrand hx₀]
      have hpow : x^((σ : ℂ)+y*I).re ≤ x^2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le hx.le hm.2
      exact div_le_div₀ (by positivity) (mul_le_mul (hbound σ hm) hpow (Real.rpow_nonneg hx₀.le _) (by positivity))
        (sq_pos_of_pos hR₀) hden)
  change ‖zetaPerronHorizontal x R y‖ ≤ _ at H
  apply H.trans
  calc
    _ ≤ C*(Real.log R)^2*x^2/R^2*(6*R) := mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by field_simp

/-- Exponential decay on a negative odd left edge, with explicit dependence on the cutoff. -/
theorem norm_zetaPerronLeft_le {x R T C : ℝ} (hx : 1<x) (hR : 3 ≤ R) (hT₀ : 0<T) (hT : T<R^2+1)
    (hC : 0<C) (hbound : ∀ t : ℝ, |t|≤T →
      ‖logDeriv riemannZeta ((perronLeftEdge R : ℂ)+t*I)‖ ≤ C*Real.log R) :
    ‖zetaPerronLeft x R T‖ ≤ (4*C)*(R^3*Real.exp (-(R*Real.log x))) := by
  have hx₀ := zero_lt_one.trans hx
  have hR₀ : 0<R := by linarith
  have hlog := Real.log_nonneg (by linarith : 1 ≤ R)
  have ha := (perronLeftEdge_bounds hR).1
  have hpow : x^perronLeftEdge R ≤ Real.exp (-(R*Real.log x)) := by
    rw [Real.rpow_def_of_pos hx₀]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ha (Real.log_pos hx).le]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (f := fun t : ℝ => zetaPerronIntegrand x ((perronLeftEdge R : ℂ)+t*I))
    (C := C*R*Real.exp (-(R*Real.log x))) (by
      intro t ht
      have hmem : t ∈ Icc (-T) T := Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by linarith : -T ≤ T)] using ht)
      have hden : 1 ≤ ‖(perronLeftEdge R : ℂ)+t*I‖ := by
        apply le_trans _ (Complex.abs_re_le_norm _)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
        rw [abs_of_neg (by linarith)]
        linarith
      rw [norm_integrand hx₀]
      apply (div_le_self (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx₀.le _)) hden).trans
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
      exact mul_le_mul ((hbound t (abs_le.mpr hmem)).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_self hR₀.le) hC.le)) hpow (Real.rpow_nonneg hx₀.le _) (by positivity))
  change ‖zetaPerronLeft x R T‖ ≤ _ at H
  apply H.trans
  rw [abs_of_nonneg (by linarith : 0 ≤ T- -T)]
  have hlen : T- -T ≤ 4*R^2 := by nlinarith
  apply (mul_le_mul_of_nonneg_left hlen (by positivity)).trans_eq
  ring

/-- On a single family of heights avoiding the zero ordinates, the two horizontal sides
and the left vertical side all vanish for each fixed `x>1`. -/
theorem exists_tendsto_zetaPerron_edges :
    ∃ U : ℝ → ℝ, (∀ᶠ R : ℝ in atTop, R^2 < U R ∧ U R < R^2+1 ∧
      ∀ z ∈ nontrivialZerosUpTo (U R), |z.im| ≠ U R) ∧ ∀ {x : ℝ}, 1<x →
      Tendsto (fun R => zetaPerronHorizontal x R (U R)) atTop (𝓝 0) ∧
      Tendsto (fun R => zetaPerronHorizontal x R (-U R)) atTop (𝓝 0) ∧
      Tendsto (fun R => zetaPerronLeft x R (U R)) atTop (𝓝 0) := by
  obtain ⟨U, C, hC, H⟩ := exists_expandingPerron_heights
  refine ⟨U, H.mono (fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩), fun {x} hx => ?_⟩
  have hlog := Real.log_pos hx
  have hlim : Tendsto (fun R : ℝ => (Real.log R)^2/R) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hhor (y : ℝ → ℝ) (hy : ∀ᶠ R in atTop, |y R|=U R) :
      Tendsto (fun R => zetaPerronHorizontal x R (y R)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hlim.const_mul (6*C*x^2))
    filter_upwards [hy, H, eventually_ge_atTop 3] with R he hh hR
    exact norm_zetaPerronHorizontal_le hx hR hh.1 he hC (fun σ hσ => hh.2.2.2.1 σ hσ _ he)
  have hpos : ∀ᶠ R in atTop, 0<U R := H.mono fun R hh => (sq_nonneg R).trans_lt hh.1
  refine ⟨hhor U (hpos.mono fun R h => abs_of_pos h),
    hhor (fun R => -U R) (hpos.mono fun R h => by rw [abs_neg,abs_of_pos h]), ?_⟩
  have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
    (tendsto_id.atTop_mul_const hlog)
  have hv : Tendsto (fun R : ℝ => R^3*Real.exp (-(R*Real.log x))) atTop (𝓝 0) := by
    convert he.div_const ((Real.log x)^3) using 1
    · funext R
      dsimp only [Function.comp_apply, id_eq]
      field_simp
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hv.const_mul (4*C))
  filter_upwards [H, hpos, eventually_ge_atTop 3] with R hh hp hR
  exact norm_zetaPerronLeft_le hx hR hp hh.2.1 hC hh.2.2.2.2

end AnalyticNumberTheory.PrimeDistribution
