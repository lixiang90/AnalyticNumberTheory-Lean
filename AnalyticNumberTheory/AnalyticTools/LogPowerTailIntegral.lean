import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The first logarithmic moment of a power tail -/

noncomputable section

open Filter Set Real MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- Exact first logarithmic moment of the power density on the upper half-line.
The two terms come from differentiating the lower-end power and its exponent. -/
theorem integral_log_mul_rpow_tail {T p : ℝ} (hT : 1 ≤ T) (hp : 0 < p) :
    IntegrableOn (fun u : ℝ => Real.log u * u^(-p-1)) (Ioi T) ∧
    ∫ u in Ioi T, Real.log u * u^(-p-1) = T^(-p)*(Real.log T/p+1/p^2) := by
  let F (u : ℝ) := -(u^(-p)*(Real.log u/p+1/p^2))
  have hder (u : ℝ) (hu : u ∈ Ici T) : HasDerivAt F (Real.log u*u^(-p-1)) u := by
    have hu0 : 0 < u := zero_lt_one.trans_le (hT.trans hu)
    have hd := ((Real.hasDerivAt_rpow_const (x := u) (p := -p) (.inl hu0.ne')).mul
      (((Real.hasDerivAt_log hu0.ne').div_const p).add_const (1/p^2))).neg
    convert hd using 1
    rw [Real.rpow_sub_one hu0.ne' (-p)]
    field_simp [hu0.ne', hp.ne']
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hlog := (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero
    have hinv := (tendsto_rpow_atTop hp).inv_tendsto_atTop
    have h := ((hlog.div_const p).add (hinv.div_const (p^2))).neg
    simp only [zero_div,zero_add,neg_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    dsimp only [F,Pi.div_apply,Pi.neg_apply,Pi.add_apply,Pi.inv_apply]
    rw [Real.rpow_neg hu.le]
    ring
  have hi := integrableOn_Ioi_deriv_of_nonneg' hder
    (fun u hu => mul_nonneg (Real.log_nonneg (hT.trans hu.le))
      (Real.rpow_nonneg (zero_lt_one.trans_le (hT.trans hu.le)).le _)) hlim
  refine ⟨hi,?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hder hi hlim]
  simp [F]

end AnalyticNumberTheory.AnalyticTools
