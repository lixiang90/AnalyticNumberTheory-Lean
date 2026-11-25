import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HigherCauchy

/-!
# A finite-order pole between two vertical lines

A quadratically decaying numerator permits the horizontal sides of the
higher Cauchy formula to tend to infinity.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Shifting past a pole of order at most `k+1` contributes the `k`-th
Taylor coefficient of the pole-cleared numerator. -/
theorem integral_verticalLine_sub_residue {F : ℂ → ℂ} {p : ℂ} {a b D : ℝ} (k : ℕ)
    (ha : a<p.re) (hb : p.re<b)
    (hF : ∀ z : ℂ, z.re∈Icc a b → AnalyticAt ℂ F z) (hD : 0≤D)
    (hd : ∀ x∈Icc a b, ∀ t : ℝ, ‖F ((x:ℂ)+t*I)‖ ≤ D/(1+t^2)) :
    (∫ t : ℝ, F ((b:ℂ)+t*I)/((b:ℂ)+t*I-p)^(k+1)) -
      (∫ t : ℝ, F ((a:ℂ)+t*I)/((a:ℂ)+t*I-p)^(k+1)) =
      2*π*iteratedDeriv k F p/(k.factorial:ℂ) := by
  let K (w : ℂ) := F w/(w-p)^(k+1)
  let V (x t : ℝ) := K ((x:ℂ)+t*I)
  let E (t : ℝ) := ∫ x in a..b, V x t
  have hab := (ha.trans hb).le
  have hi (x : ℝ) (hx : x∈Icc a b) (hne : x≠p.re) : Integrable (V x) := by
    let d := |x-p.re|
    have hd0 : 0<d := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hdn (t : ℝ) : d≤‖(x:ℂ)+t*I-p‖ := by simpa [d] using Complex.abs_re_le_norm ((x:ℂ)+t*I-p)
    have hw : Continuous (fun t : ℝ => (x:ℂ)+t*I) := by fun_prop
    have hf : Continuous (fun t : ℝ => F ((x:ℂ)+t*I)) :=
      continuous_iff_continuousAt.mpr (fun t => (hF _ (by simpa using hx)).continuousAt.comp hw.continuousAt)
    have hc : Continuous (V x) := hf.div ((hw.sub continuous_const).pow _) (fun t =>
      pow_ne_zero _ (norm_pos_iff.mp (hd0.trans_le (hdn t))))
    apply (integrable_inv_one_add_sq.const_mul (D/d^(k+1))).mono' hc.aestronglyMeasurable
    filter_upwards with t
    dsimp only [V,K]; rw [norm_div,norm_pow]
    exact (div_le_div₀ (by positivity) (hd x hx t) (pow_pos hd0 _) (pow_le_pow_left₀ hd0.le (hdn t) _)).trans_eq (by ring)
  have hE (t : ℝ) (ht : |p.im|+1≤|t|) : ‖E t‖ ≤ (b-a)*D/(1+t^2) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (f:=fun x => V x t)
      (C:=D/(1+t^2)) (fun x hx => by
        have hx' := Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hx)
        have ht' := abs_sub_abs_le_abs_sub t p.im
        have hn : 1≤‖(x:ℂ)+t*I-p‖ := (show 1≤|t-p.im| by linarith).trans
          (by simpa using Complex.abs_im_le_norm ((x:ℂ)+t*I-p))
        dsimp [V,K]; rw [norm_div,norm_pow]
        exact (div_le_self (norm_nonneg _) (one_le_pow₀ hn)).trans (hd x hx' t))
    change ‖E t‖≤_ at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hh
    exact hh.trans_eq (by ring)
  have hlim : Tendsto (fun t : ℝ => ((b-a)*D)/(1+t^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by decide : 2≠0)))
  have hEu : Tendsto E atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (by
      filter_upwards [eventually_ge_atTop (|p.im|+1)] with t ht; exact hE _ (ht.trans (le_abs_self _))) hlim)
  have hEl : Tendsto (fun t => E (-t)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (by
      filter_upwards [eventually_ge_atTop (|p.im|+1)] with t ht
      simpa only [neg_sq] using hE (-t) (by rw [abs_neg]; exact ht.trans (le_abs_self _))) hlim)
  have hl := intervalIntegral_tendsto_integral (hi a ⟨le_rfl,hab⟩ ha.ne) tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have hr := intervalIntegral_tendsto_integral (hi b ⟨hab,le_rfl⟩ hb.ne') tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have hI : Tendsto (fun _ : ℝ => I) atTop (𝓝 I) := tendsto_const_nhds
  have H := (((hEl.sub hEu).add (hI.mul hr)).sub (hI.mul hl))
  change Tendsto (fun t : ℝ => E (-t)-E t+I*(∫ y in (-t)..t,V b y)-I*(∫ y in (-t)..t,V a y))
    atTop (𝓝 (0-0+I*(∫ y,V b y)-I*(∫ y,V a y))) at H
  have H' : ∀ᶠ t : ℝ in atTop, E (-t)-E t+I*(∫ y in (-t)..t,V b y)-I*(∫ y in (-t)..t,V a y)
      = 2*π*I*iteratedDeriv k F p/(k.factorial:ℂ) := by
    filter_upwards [eventually_gt_atTop |p.im|] with t ht
    have he := rectangleBoundary_cauchy_pow (p:=p) (z:=⟨a,-t⟩) (w:=⟨b,t⟩) k hF ha hb
      (by change -t<p.im; linarith [neg_le_abs p.im]) ((le_abs_self _).trans_lt ht)
    simpa only [rectangleBoundary,Complex.ofReal_neg,E,V,K] using he
  have he := tendsto_nhds_unique H (tendsto_const_nhds.congr' (H'.mono fun _ hh => hh.symm))
  change (∫ t,V b t)-(∫ t,V a t) = _
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination he

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
