import AnalyticNumberTheory.AnalyticTools.Gamma.StirlingIntegrals

/-! # Integration by parts for Stirling's Bernoulli remainder -/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.AnalyticTools.Gamma

/-- Increasing both the Bernoulli order and the denominator degree by one
extracts the exact endpoint coefficient. It works on the full slit plane. -/
theorem stirlingBernoulliIntegral_step {j p : ℕ} (hj : 1 ≤ j) (hp : 0 < p)
    {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    stirlingBernoulliIntegral j (p+1) s =
      -(bernoulliKernel (j+1) 0 : ℂ)/s^(p+1) + (p+1 : ℕ) * stirlingBernoulliIntegral (j+1) (p+1+1) s := by
  let q := p+1
  let b := (bernoulliKernel (j+1) 0 : ℂ)
  let f (t : ℝ) := (((t : ℂ)+s)^q)⁻¹
  let f' (t : ℝ) := -(q : ℂ) / ((t : ℂ)+s)^(q+1)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt f (f' t) t := by
    have hn := ofReal_add_ne_zero_of_mem_slitPlane hs ht
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ)+s) 1 t := Complex.ofRealCLM.hasDerivAt.add_const s
    convert (hlin.pow q).inv (pow_ne_zero _ hn) using 1
    dsimp only [f', q]
    simp only [Pi.pow_apply, Nat.add_sub_cancel, mul_one, pow_succ]
    field_simp [hn]
  have hfinite (N : ℕ) :
      (∫ t in (0 : ℝ)..N, (bernoulliKernel j t : ℂ)/((t : ℂ)+s)^q) =
        b * f N - b/s^q + (q : ℂ) *
          ∫ t in (0 : ℝ)..N, (bernoulliKernel (j+1) t : ℂ)/((t : ℂ)+s)^(q+1) := by
    have hbN : bernoulliKernel (j+1) (N : ℝ) = bernoulliKernel (j+1) 0 := by
      simpa using (bernoulliKernel_intCast (j+1) (N : ℤ)).trans (bernoulliKernel_intCast (j+1) 0).symm
    have hf' : ContinuousOn f' (Icc (0 : ℝ) N) := by
      have hden : Continuous (fun t : ℝ => ((t : ℂ)+s)^(q+1)) :=
        (Complex.continuous_ofReal.add continuous_const).pow _
      have hnum : ContinuousOn (fun _ : ℝ => -(q : ℂ)) (Icc (0 : ℝ) N) := continuousOn_const
      exact hnum.div hden.continuousOn (fun t ht => pow_ne_zero _ (ofReal_add_ne_zero_of_mem_slitPlane (s := s) hs (u := t) ht.1))
    have H := integral_bernoulliKernel_mul_complex (j := j) (a := 0) (b := (N : ℝ)) (g := f) (g' := f') hj (Nat.cast_nonneg N)
      (fun t ht => hd t ht.1) hf'
    have he (t : ℝ) : (bernoulliKernel (j+1) t : ℂ)*f' t =
        -(q : ℂ) * ((bernoulliKernel (j+1) t : ℂ)/((t : ℂ)+s)^(q+1)) := by dsimp [f']; ring
    simp_rw [he] at H
    rw [intervalIntegral.integral_const_mul, hbN] at H
    simpa only [b, f, Complex.ofReal_zero, zero_add, div_eq_mul_inv, neg_mul, sub_neg_eq_add] using H
  have hnorm : Tendsto (fun N : ℕ => ‖(N : ℂ)+s‖) atTop atTop := by
    have hreal : Tendsto (fun n : ℕ => (n : ℝ)+s.re) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_atTop_mono (fun n => by simpa using Complex.re_le_norm ((n : ℂ)+s)) hreal
  have hf : Tendsto (fun N : ℕ => f N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply ((tendsto_pow_atTop (Nat.succ_ne_zero p)).comp hnorm).inv_tendsto_atTop.congr
    intro n
    simp only [f, q, Complex.ofReal_natCast, norm_inv, norm_pow, Pi.inv_apply, Function.comp_apply, Nat.succ_eq_add_one]
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 (integrable_stirlingBernoulliIntegrand j hp hs)
    tendsto_natCast_atTop_atTop
  have h2 := intervalIntegral_tendsto_integral_Ioi 0 (integrable_stirlingBernoulliIntegrand (j+1) (Nat.succ_pos p) hs)
    tendsto_natCast_atTop_atTop
  have H := (((hf.const_mul b).sub_const (b/s^q)).add (h2.const_mul (q : ℂ))).congr (fun N => (hfinite N).symm)
  simpa only [stirlingBernoulliIntegral, q, b, mul_zero, zero_sub, neg_div] using tendsto_nhds_unique h1 H

end AnalyticNumberTheory.AnalyticTools.Gamma
