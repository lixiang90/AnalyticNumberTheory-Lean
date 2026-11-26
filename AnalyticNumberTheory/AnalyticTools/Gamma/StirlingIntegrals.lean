import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.Summation.BernoulliKernels

/-! # Bernoulli integrals for the Stirling expansion on the slit plane -/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AnalyticTools.Gamma

/-- The Bernoulli integral with independent kernel order and denominator degree. -/
def stirlingBernoulliIntegral (j q : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (bernoulliKernel j t : ℂ) / ((t : ℂ)+s)^q

private lemma inv_shift_pow_integral {p : ℕ} (hp : 0 < p) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => ((t+r)^(p+1))⁻¹) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), ((t+r)^(p+1))⁻¹) = ((p : ℝ)*r^p)⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  let A (t : ℝ) := -(↑(n+1 : ℕ) : ℝ)⁻¹ * ((t+r)^(n+1))⁻¹
  have hd (u : ℝ) (hu : u ∈ Ici (0 : ℝ)) :
      HasDerivAt A (((u+r)^(n+1+1))⁻¹) u := by
    have hx : 0 < u+r := add_pos_of_nonneg_of_pos hu hr
    have hp' : (↑(n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h := ((((hasDerivAt_id' u).add_const r).pow (n+1)).inv (pow_ne_zero _ hx.ne')).const_mul
      (-(↑(n+1 : ℕ) : ℝ)⁻¹)
    convert h using 1
    simp only [Pi.pow_apply, Nat.add_sub_cancel, mul_one, pow_succ]
    field_simp [hx.ne', hp']
  have ht : Tendsto A atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp
      (tendsto_id.atTop_add (tendsto_const_nhds (x := r)))).inv_tendsto_atTop
    simpa only [A, mul_zero, Pi.inv_apply, Function.comp_apply, id_eq, Nat.succ_eq_add_one] using h.const_mul (-(↑(n+1 : ℕ) : ℝ)⁻¹)
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd (fun u hu => by
    have : 0 < u+r := add_pos hu hr
    positivity) ht
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht]
  simp [A, mul_inv_rev, mul_comm]

private lemma norm_bernoulliIntegrand_le {s : ℂ} (hs : s ∈ Complex.slitPlane) {j : ℕ} (q : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, |bernoulliKernel j t| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖(bernoulliKernel j t : ℂ) / ((t : ℂ)+s)^q‖ ≤
      (M / Real.cos (s.arg/2)^q) * ((t+‖s‖)^q)⁻¹ := by
  have hc := cos_half_arg_pos_of_mem_slitPlane hs
  have hr := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  have hx := mul_pos hc (add_pos_of_nonneg_of_pos ht hr)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  calc
    _ ≤ M / ‖(t : ℂ)+s‖^q := div_le_div_of_nonneg_right (hb t) (by positivity)
    _ ≤ M / (Real.cos (s.arg/2)*(t+‖s‖))^q := div_le_div_of_nonneg_left hM (pow_pos hx _)
      (pow_le_pow_left₀ hx.le (cos_half_arg_mul_le_norm_ofReal_add hs ht) _)
    _ = _ := by rw [mul_pow]; ring

/-- On the slit plane the Bernoulli integral is absolutely convergent for
denominator degree at least two, at any Bernoulli order. -/
theorem integrable_stirlingBernoulliIntegrand (j : ℕ) {p : ℕ} (hp : 0 < p) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    IntegrableOn (fun t : ℝ => (bernoulliKernel j t : ℂ)/((t : ℂ)+s)^(p+1)) (Ioi 0) := by
  obtain ⟨M, hM, hb⟩ := bernoulliKernel_bounded j
  have hr := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  have hdom := (inv_shift_pow_integral hp hr).1.const_mul (M / Real.cos (s.arg/2)^(p+1))
  apply hdom.mono'
  · have hm : Measurable (bernoulliKernel j) :=
      ((continuous_bernoulliFun j).measurable.comp measurable_fract).div_const _
    exact ((Complex.continuous_ofReal.measurable.comp hm).div (by fun_prop)).aestronglyMeasurable
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => norm_bernoulliIntegrand_le hs _ hM hb ht.le

/-- An explicit sector bound. For an even Bernoulli order the sharp choice
of numerator is the absolute value of the kernel at zero. -/
theorem norm_stirlingBernoulliIntegral_le {j p : ℕ} (hp : 0 < p) {s : ℂ} (hs : s ∈ Complex.slitPlane)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, |bernoulliKernel j t| ≤ M) :
    ‖stirlingBernoulliIntegral j (p+1) s‖ ≤
      M / (Real.cos (s.arg/2)^(p+1) * p * ‖s‖^p) := by
  have hi := inv_shift_pow_integral hp (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs))
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), (M / Real.cos (s.arg/2)^(p+1))*((t+‖s‖)^(p+1))⁻¹ := by
      apply norm_integral_le_of_norm_le (hi.1.const_mul _)
      exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => norm_bernoulliIntegrand_le hs _ hM hb ht.le
    _ = _ := by rw [integral_const_mul, hi.2]; ring

end AnalyticNumberTheory.AnalyticTools.Gamma
