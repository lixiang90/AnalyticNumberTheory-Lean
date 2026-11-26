import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogModulusDerivative
import AnalyticNumberTheory.RiemannZeta.ZetaLogMean
import AnalyticNumberTheory.RiemannZeta.ZeroCounting
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # Vertical differentiation of the horizontal logarithmic mean -/
noncomputable section
open Complex Set Metric Filter MeasureTheory
open scoped Topology Interval
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

private theorem hasDerivAt_vertical_log_norm {f : ℂ → ℂ} {x t : ℝ}
    (hd : DifferentiableAt ℂ f ((x:ℂ)+(t:ℂ)*I)) (hn : f ((x:ℂ)+(t:ℂ)*I) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log ‖f ((x:ℂ)+(u:ℂ)*I)‖)
      (-(deriv f ((x:ℂ)+(t:ℂ)*I) / f ((x:ℂ)+(t:ℂ)*I)).im) t := by
  let z : ℂ := (x:ℂ)+(t:ℂ)*I
  let g (w : ℂ) := f ((x:ℂ)+w*I)
  have hlin : HasDerivAt (fun w : ℂ => (x:ℂ)+w*I) I (t:ℂ) :=
    (((hasDerivAt_id _).mul_const I).const_add _).congr_deriv (by simp)
  have hg : HasDerivAt g (deriv f z * I) (t:ℂ) := hd.hasDerivAt.comp (t:ℂ) hlin
  have hnorm := hasDerivAt_real_log_norm hg.comp_ofReal hn
  apply hnorm.congr_deriv
  rw [mul_div_right_comm, Complex.mul_I_re]

private theorem hasDerivAt_rectangle_integral {F D : ℝ → ℝ → ℝ} {T a b : ℝ} {J : Set ℝ}
    (hab : a≤b) (hj : J∈𝓝 T) (hc : IsCompact J)
    (hF : ContinuousOn (fun p : ℝ×ℝ => F p.2 p.1) (Icc a b ×ˢ J))
    (hD : ContinuousOn (fun p : ℝ×ℝ => D p.2 p.1) (Icc a b ×ˢ J))
    (hder : ∀ x ∈ Icc a b, ∀ t ∈ J, HasDerivAt (fun u => F u x) (D t x) t) :
    HasDerivAt (fun t => ∫ x in a..b, F t x) (∫ x in a..b, D T x) T := by
  have hslice {f : ℝ → ℝ → ℝ} (h : ContinuousOn (fun p : ℝ×ℝ => f p.2 p.1) (Icc a b ×ˢ J))
      {t : ℝ} (ht : t ∈ J) : ContinuousOn (f t) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact h.comp (f:=fun x : ℝ => (x,t)) (continuous_id.prodMk continuous_const).continuousOn (fun _ hx => ⟨hx,ht⟩)
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn hD
  have hT := mem_of_mem_nhds hj
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume) (F:=F) (F':=D) (a:=a) (b:=b) (bound:=fun _ => M) hj
    ((show ∀ᶠ t in 𝓝 T, t∈J from hj).mono fun t ht => ((hslice hF ht).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    (hslice hF hT).intervalIntegrable
    (((hslice hD hT).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc) ?_
    intervalIntegrable_const ?_).2
  · exact ae_of_all _ fun x hx t ht => hM (x,t) ⟨(uIcc_of_le hab) ▸ uIoc_subset_uIcc hx,ht⟩
  · exact ae_of_all _ fun x hx => hder x ((uIcc_of_le hab) ▸ uIoc_subset_uIcc hx)

/-- At a positive height missing every zero, the vertical derivative of the
horizontal logarithmic mean recovers the Riemann–von Mangoldt argument term. -/
theorem hasDerivAt_zeta_horizontalLogMean {T : ℝ} (hT : 0<T) (hno : ¬ IsZeroOrdinate T) :
    HasDerivAt (horizontalLogMean riemannZeta)
      (Real.pi * argumentS T - (riemannZeta (2+(T:ℂ)*I)).arg) T := by
  obtain ⟨δ,hδ,H⟩ := exists_zeta_zeroFree_horizontal_rectangle hT hno
  let X := Icc (1/2:ℝ) 2
  let J := Icc (T-δ) (T+δ)
  let Z (p : ℝ×ℝ) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
  let F (t x : ℝ) := Real.log ‖riemannZeta (Z (x,t))‖
  let D (t x : ℝ) := -(deriv riemannZeta (Z (x,t)) / riemannZeta (Z (x,t))).im
  have hmap : Continuous Z :=
    (Complex.continuous_ofReal.comp continuous_fst).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have HF : ContinuousOn (fun p : ℝ×ℝ => Real.log ‖riemannZeta (Z p)‖) (X ×ˢ J) := by
    intro p hp
    have hz : ContinuousAt (fun q => riemannZeta (Z q)) p :=
      ContinuousAt.comp (f:=Z) (differentiableAt_riemannZeta (H p hp).1).continuousAt hmap.continuousAt
    exact (hz.norm.log (norm_ne_zero_iff.mpr (H p hp).2)).continuousWithinAt
  have HD : ContinuousOn (fun p : ℝ×ℝ => D p.2 p.1) (X ×ˢ J) :=
    (continuousOn_im_zeta_logDeriv H).neg
  have hj : J ∈ 𝓝 T := Icc_mem_nhds (sub_lt_self _ hδ) (lt_add_of_pos_right _ hδ)
  have h := hasDerivAt_rectangle_integral (F:=F) (D:=D) (by norm_num : (1/2:ℝ)≤2)
    hj isCompact_Icc HF HD (by
      intro x hx t ht
      have hh := H (x,t) ⟨hx,ht⟩
      exact hasDerivAt_vertical_log_norm (f:=riemannZeta) (x:=x) (t:=t)
        (differentiableAt_riemannZeta hh.1) hh.2)
  apply h.congr_deriv
  rw [argumentS_eq_argumentSApprox_of_not_isZeroOrdinate hT hno,argumentSApprox]
  dsimp only [D,Z]
  rw [intervalIntegral.integral_neg]
  field_simp [Real.pi_ne_zero]
  <;> ring

end AnalyticNumberTheory.RiemannZeta
