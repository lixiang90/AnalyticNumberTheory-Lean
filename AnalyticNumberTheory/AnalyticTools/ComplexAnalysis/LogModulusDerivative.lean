import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Differentiating the log modulus along a real curve -/

noncomputable section

open Complex Filter
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Along a differentiable complex-valued real curve g, log |g| has derivative
Re(g′/g) at every nonzero value. A local normalization puts the logarithm on its slit plane. -/
theorem hasDerivAt_real_log_norm {g : ℝ → ℂ} {x : ℝ} {v : ℂ} (hg : HasDerivAt g v x)
    (hn : g x ≠ 0) : HasDerivAt (fun y => Real.log ‖g y‖) (v/g x).re x := by
  have hratio := hg.div_const (g x)
  have hlog := hratio.clog_real (by rw [div_self hn]; exact Complex.one_mem_slitPlane)
  have hr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hlog).add_const (Real.log ‖g x‖)
  have hfun : (fun y => Real.log ‖g y‖) =ᶠ[𝓝 x]
      (fun y => (Complex.log (g y/g x)).re + Real.log ‖g x‖) := by
    filter_upwards [hg.continuousAt.eventually_ne hn] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hy) (norm_ne_zero_iff.mpr hn)]
    ring
  apply (hr.congr_of_eventuallyEq hfun).congr_deriv
  change ((v/g x)/(g x/g x)).re = _
  rw [div_self hn, div_one]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
