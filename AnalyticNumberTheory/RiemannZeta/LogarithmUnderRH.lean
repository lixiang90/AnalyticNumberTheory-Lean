import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogarithmBranch
import AnalyticNumberTheory.RiemannZeta.ArgumentPrimitive
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis

/-!
# The Euler-normalized logarithm of zeta under the Riemann hypothesis

Factoring out the pole gives a holomorphic logarithm on the full half-plane
Re s > 1/2. Subtracting the principal logarithm of s−1 produces a branch of log ζ
on the slit half-plane that agrees with the Euler product to the right of one.
-/

noncomputable section

open Complex Set Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

private theorem pole_removed_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s-1)*riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs,mul_inv_cancel_left₀ (sub_ne_zero.mpr hs)]

private theorem isOpen_right (b : ℝ) : IsOpen {z : ℂ | b < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem regular_log_exists (hRH : RiemannHypothesisProp) :
    ∃ g : ℂ → ℂ, g 2 = logZeta 2 ∧ (∀ s : ℂ, 1/2 < s.re → Complex.exp (g s) = riemannZeta₁ s) ∧
      ∀ s : ℂ, 1/2 < s.re → HasDerivAt g (deriv riemannZeta₁ s/riemannZeta₁ s) s := by
  let U := {s : ℂ | 1/2 < s.re}
  have h2 : (2:ℂ) ∈ U := by change 1/2 < (2:ℂ).re; norm_num
  let : ContractibleSpace U := (convex_halfSpace_re_gt (1/2)).contractibleSpace ⟨2,h2⟩
  have hsc : IsSimplyConnected U := inferInstanceAs (SimplyConnectedSpace U)
  apply exists_holomorphic_logarithm (U := U) (isOpen_right _) hsc differentiable_riemannZeta₁.differentiableOn _ h2
  · rw [exp_logZeta (by norm_num),pole_removed_eq (by norm_num : (2:ℂ) ≠ 1)]
    norm_num
  · intro s hs
    rcases eq_or_ne s 1 with rfl | hne
    · simp
    · rw [pole_removed_eq hne]
      exact mul_ne_zero (sub_ne_zero.mpr hne) (riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH s hs)

/-- Under RH, the holomorphic logarithm of the pole-removed factor, normalized
at 2 by the absolutely convergent Euler product. -/
def regularizedLogZeta (hRH : RiemannHypothesisProp) : ℂ → ℂ :=
  Classical.choose (regular_log_exists hRH)

/-- Value at the Euler-product base point. -/
theorem regularizedLogZeta_two (hRH : RiemannHypothesisProp) : regularizedLogZeta hRH 2 = logZeta 2 :=
  (Classical.choose_spec (regular_log_exists hRH)).1

/-- Exponentiation recovers the entire pole-removed factor on the half-plane. -/
theorem exp_regularizedLogZeta (hRH : RiemannHypothesisProp) {s : ℂ} (hs : 1/2 < s.re) :
    Complex.exp (regularizedLogZeta hRH s) = riemannZeta₁ s :=
  (Classical.choose_spec (regular_log_exists hRH)).2.1 s hs

/-- The derivative is the logarithmic derivative of the entire pole-removed factor. -/
theorem hasDerivAt_regularizedLogZeta (hRH : RiemannHypothesisProp) {s : ℂ} (hs : 1/2 < s.re) :
    HasDerivAt (regularizedLogZeta hRH) (deriv riemannZeta₁ s / riemannZeta₁ s) s :=
  (Classical.choose_spec (regular_log_exists hRH)).2.2 s hs

/-- RH is equivalent to the existence of a single holomorphic logarithm of (s−1)ζ(s)
on the entire half-plane to the right of the critical line, including the point s=1. -/
theorem riemannHypothesisProp_iff_exists_regularizedLog :
    RiemannHypothesisProp ↔ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g {s : ℂ | 1/2 < s.re} ∧
      ∀ s : ℂ, 1/2 < s.re → Complex.exp (g s) = riemannZeta₁ s := by
  constructor
  · intro hRH
    refine ⟨regularizedLogZeta hRH, DifferentiableOn.analyticOnNhd ?_ (isOpen_right _),
      fun _ hs => exp_regularizedLogZeta hRH hs⟩
    exact fun _ hs => (hasDerivAt_regularizedLogZeta hRH hs).differentiableAt.differentiableWithinAt
  · rintro ⟨g,_,hg⟩
    apply riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mpr
    intro s hs
    rcases eq_or_ne s 1 with rfl | hne
    · exact riemannZeta_ne_zero_of_one_le_re (by simp)
    · rw [riemannZeta_eq_inv_sub_mul hne,←hg s hs]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hne)) (Complex.exp_ne_zero _)

/-- Subtracting the principal logarithm of s−1 yields the Euler-normalized logarithm
of ζ on the right half-plane slit from the pole leftward along the real axis. -/
def slitLogZeta (hRH : RiemannHypothesisProp) (s : ℂ) : ℂ :=
  regularizedLogZeta hRH s - Complex.log (s-1)

/-- Off the pole, exponentiation recovers ζ itself. -/
theorem exp_slitLogZeta (hRH : RiemannHypothesisProp) {s : ℂ} (hs : 1/2 < s.re) (hs₁ : s ≠ 1) :
    Complex.exp (slitLogZeta hRH s) = riemannZeta s := by
  rw [slitLogZeta,Complex.exp_sub,exp_regularizedLogZeta hRH hs,Complex.exp_log (sub_ne_zero.mpr hs₁),
    pole_removed_eq hs₁,mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs₁)]

/-- The derivative of the Euler-normalized branch is ζ'/ζ at every point of the slit half-plane. -/
theorem hasDerivAt_slitLogZeta (hRH : RiemannHypothesisProp) {s : ℂ} (hs : 1/2 < s.re)
    (hcut : s-1 ∈ slitPlane) :
    HasDerivAt (slitLogZeta hRH) (deriv riemannZeta s / riemannZeta s) s := by
  have hne := sub_ne_zero.mp (slitPlane_ne_zero hcut)
  have hc : ContinuousAt (slitLogZeta hRH) s :=
    (hasDerivAt_regularizedLogZeta hRH hs).continuousAt.sub
      ((continuousAt_id.sub continuousAt_const).clog hcut)
  apply hasDerivAt_logarithm_of_eventually_exp_eq hc (differentiableAt_riemannZeta hne).hasDerivAt
  filter_upwards [(isOpen_right (1/2)).mem_nhds hs,compl_singleton_mem_nhds hne] with z hz hn
  exact exp_slitLogZeta hRH hz hn

/-- The continued branch agrees with the Euler product throughout Re s>1. -/
theorem slitLogZeta_eq_logZeta (hRH : RiemannHypothesisProp) {s : ℂ} (hs : 1 < s.re) :
    slitLogZeta hRH s = logZeta s := by
  have hd (z : ℂ) (hz : 1 < z.re) := hasDerivAt_slitLogZeta hRH (by linarith : 1/2 < z.re)
    (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr hz : 0 < (z-1).re)))
  apply eqOn_holomorphic_logarithms (isOpen_right 1) (convex_halfSpace_re_gt 1).isPreconnected
    (f := riemannZeta) (g := slitLogZeta hRH) (h := logZeta)
    (fun z hz => (differentiableAt_riemannZeta (by intro h; simp [h] at hz)).differentiableWithinAt)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt) differentiableOn_logZeta.continuousOn
    (fun z hz => exp_slitLogZeta hRH (by change 1 < z.re at hz; linarith) (by intro h; simp [h] at hz))
    (fun _ hz => exp_logZeta hz) (a := 2) (by change 1 < (2:ℂ).re; norm_num) ?_ hs
  norm_num [slitLogZeta,regularizedLogZeta_two]

private theorem logZeta_two_eq_principal : logZeta 2 = Complex.log (riemannZeta 2) := by
  apply Complex.ext
  · rw [logZeta_re_eq_log_norm (by norm_num),Complex.log_re]
  · rw [Complex.log_im]
    exact logZeta_im_two (s := 2) (by norm_num)

/-- The regularized logarithm vanishes at the pole, with the Euler-product normalization. -/
theorem regularizedLogZeta_one (hRH : RiemannHypothesisProp) : regularizedLogZeta hRH 1 = 0 := by
  let D (z : ℂ) := regularizedLogZeta hRH z - Complex.log (riemannZeta₁ z)
  have hd (t : ℝ) (ht : t ∈ uIcc (1:ℝ) 2) : HasDerivAt (fun v : ℝ => D v) 0 t := by
    have ht₁ : 1 ≤ t := ((uIcc_of_le (by norm_num : (1:ℝ)≤2)) ▸ ht).1
    have hp : 0 < (riemannZeta₁ t).re := by
      rcases ht₁.eq_or_lt with rfl | h
      · norm_num
      · rw [pole_removed_eq (by exact_mod_cast h.ne')]
        simpa [Complex.mul_re] using mul_pos (sub_pos.mpr h) (riemannZeta_re_pos_of_one_lt h)
    have h := (hasDerivAt_regularizedLogZeta hRH (by simpa using (by linarith : 1/2 < t))).fun_sub
      ((differentiable_riemannZeta₁ (t:ℂ)).hasDerivAt.clog (mem_slitPlane_iff.mpr (.inl hp)))
    apply h.comp_ofReal.congr_deriv
    simp [div_eq_mul_inv]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (1:ℝ)) (b := 2) hd intervalIntegrable_const
  have h₂ : D 2 = 0 := by
    rw [show D 2 = regularizedLogZeta hRH 2 - Complex.log (riemannZeta₁ 2) from rfl,
      regularizedLogZeta_two,logZeta_two_eq_principal,pole_removed_eq (by norm_num : (2:ℂ)≠1)]
    norm_num
  simp only [intervalIntegral.integral_zero,Complex.ofReal_one,Complex.ofReal_ofNat,h₂,zero_sub,zero_eq_neg] at h
  simpa [D] using h

/-- After adding back the logarithmic singularity, the Euler branch approaches zero
at s=1 from every direction within the slit domain. -/
theorem tendsto_slitLogZeta_add_log_at_one (hRH : RiemannHypothesisProp) :
    Tendsto (fun s : ℂ => slitLogZeta hRH s + Complex.log (s-1)) (𝓝 1) (𝓝 0) := by
  simpa only [slitLogZeta,sub_add_cancel,regularizedLogZeta_one] using
    (hasDerivAt_regularizedLogZeta hRH (s := 1) (by norm_num)).continuousAt.tendsto

end AnalyticNumberTheory.RiemannZeta
