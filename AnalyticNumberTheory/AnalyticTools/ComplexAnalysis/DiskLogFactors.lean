import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory

/-!
# Finite logarithmic factorization on a disk

The logarithm of the norm splits into logarithms of distances to the zeros
and the logarithm of a nonvanishing analytic factor. Jensen's bound counts
the terms with multiplicity.
-/

open Complex Real Set Metric Finset MeromorphicOn
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Interior oscillation of the logarithm of the norm of a zero-free function. -/
theorem abs_log_norm_sub_le_of_ne_zero {g : ℂ → ℂ} {c z : ℂ} {r R M : ℝ} (hr : 0≤r)
    (hrR : r<R) (hg : DifferentiableOn ℂ g (ball c R))
    (hn : ∀ w∈ball c R, g w≠0) (hb : ∀ w∈ball c R, ‖g w/g c‖≤M)
    (hz : z∈closedBall c r) :
    |Real.log ‖g z‖-Real.log ‖g c‖| ≤ 2*r/(R-r)*Real.log M := by
  have hR := hr.trans_lt hrR
  have hc := hn c (mem_ball_self hR)
  have hz' := closedBall_subset_ball hrR hz
  obtain ⟨h,hd,hc',he,_⟩ := exists_holomorphic_log_on_ball hR hg hn
  have hre (w : ℂ) (hw : w∈ball c R) : (h w).re=Real.log ‖g w/g c‖ := by
    rw [←he w hw,Complex.norm_exp,Real.log_exp]
  have H := borel_caratheodory_sub_on_closedBall hr hrR hd (fun w hw => (hre w hw).le.trans
    (Real.log_le_log (norm_pos_iff.mpr (div_ne_zero (hn w hw) hc)) (hb w hw))) hz
  rw [hc',sub_zero,Complex.zero_re,sub_zero] at H
  have h := (Complex.abs_re_le_norm (h z)).trans H
  rwa [hre z hz',norm_div,Real.log_div (norm_ne_zero_iff.mpr (hn z hz')) (norm_ne_zero_iff.mpr hc)] at h

/-- The logarithm of the norm on an inner disk, with a finite sum over zeros,
a bound for their total multiplicity and a zero-free analytic remainder. -/
theorem disk_log_norm_factorization {f : ℂ→ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0<r) (hrR : r<R) (hM : 0<M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c≠0)
    (hb : ∀ z∈sphere c R, ‖f z/f c‖≤M) :
    ∃ (Z : Finset ℂ) (g : ℂ→ℂ), (Z:Set ℂ)=zeroSet f c r ∧
      (∑ u∈Z,(analyticOrderNatAt f u:ℝ))≤Real.log M/Real.log (R/r) ∧
      AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ w∈closedBall c r,g w≠0) ∧
      (∀ w∈closedBall c R, ‖g w/g c‖≤M*(r/(R-r))^(∑ u∈Z,analyticOrderNatAt f u)) ∧
      ∀ z∈closedBall c r, z∉Z → Real.log ‖f z‖ =
        (∑ u∈Z,(analyticOrderNatAt f u:ℝ)*Real.log ‖z-u‖)+Real.log ‖g z‖ := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c r)
  let Z := (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hf' := hf.mono (closedBall_subset_closedBall hrR.le)
  have hZ : (Z:Set ℂ)=zeroSet f c r := by
    simpa only [Z,Set.Finite.coe_toFinset,D] using divisor_support_eq_zeroSet hr.le hf' hc
  have hmem {u : ℂ} (hu : u∈Z) : u∈closedBall c r ∧ f u=0 := by
    apply mem_zeroSet.mp; rw [←hZ]; exact hu
  have hD (u : ℂ) (hu : u∈Z) : D u=(analyticOrderNatAt f u:ℤ) := by
    dsimp only [D]
    rw [AnalyticOnNhd.divisor_apply hf' (hmem hu).1,←Nat.cast_analyticOrderNatAt
      (analyticOrderAt_ne_top_of_closedBall hr.le hf' hc (hmem hu).1)]
    simp
  obtain ⟨g,hg,hn,hgb,hfac,_⟩ := extract_ball_zero_factors hr hrR hf hc hb
  have hcnt : (∑ u∈Z,(D u).toNat)=∑ u∈Z,analyticOrderNatAt f u := by
    apply sum_congr rfl
    intro u hu
    simp [hD u hu]
  refine ⟨Z,g,hZ,?_,hg,hn,?_,?_⟩
  · have H := zeroCount_le_log_div_log hr hrR (mul_pos hM (norm_pos_iff.mpr hc)) hf hc
      (fun z hz => by have H := hb z hz; rwa [norm_div,div_le_iff₀ (norm_pos_iff.mpr hc)] at H)
    rw [mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hc),zeroCount_eq_sum_analyticOrderNatAt hr.le hf' hc hZ] at H
    exact_mod_cast H
  · intro w hw
    exact (hgb w hw).trans_eq (by rw [←hcnt])
  · intro z hz hnot
    have hne {u : ℂ} (hu : u∈Z) : z-u≠0 := sub_ne_zero.mpr (fun he => hnot (he ▸ hu))
    have hprod : ∏ u∈Z,(z-u)^D u=∏ u∈Z,(z-u)^analyticOrderNatAt f u := by
      apply prod_congr rfl
      intro u hu
      simp [hD u hu]
    have H := hfac z (closedBall_subset_closedBall hrR.le hz)
      (fun h => hnot ((D.finiteSupport (isCompact_closedBall _ _)).mem_toFinset.mpr h))
    rw [show (∏ u∈Z,(z-u)^D u)=_ from hprod] at H
    rw [H,norm_mul,Real.log_mul (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr
      (fun u hu => pow_ne_zero _ (hne hu)))) (norm_ne_zero_iff.mpr (hn z hz)),Complex.norm_prod]
    rw [Real.log_prod (fun u hu => norm_ne_zero_iff.mpr (pow_ne_zero _ (hne hu)))]
    simp [norm_pow,Real.log_pow]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
