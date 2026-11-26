import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalLogMean
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-! # Horizontal integrals of the logarithmic modulus of the Riemann zeta function -/
noncomputable section
open Complex Set Metric
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

/-- On the line Re(s)=2 the zeta modulus lies between one half and two,
so the absolute logarithm of the modulus is bounded by log 2. -/
theorem abs_log_norm_zeta_two_le (t : ℝ) :
    |Real.log ‖riemannZeta ((2 : ℂ)+(t : ℂ)*I)‖| ≤ Real.log 2 := by
  have hlo : (2:ℝ)⁻¹ ≤ ‖riemannZeta ((2 : ℂ)+(t : ℂ)*I)‖ := by
    convert norm_riemannZeta_ge_of_one_lt_re (by norm_num : (1:ℝ)<2) t using 1 <;> norm_num
  have hhi : ‖riemannZeta ((2 : ℂ)+(t : ℂ)*I)‖ ≤ 2 := by
    convert norm_riemannZeta_le_of_one_lt_re (by norm_num : (1:ℝ)<2) t using 1 <;> norm_num
  exact abs_le.mpr ⟨(Real.log_inv _).symm.le.trans (Real.log_le_log (by norm_num) hlo),
    Real.log_le_log (by linarith) hhi⟩

private theorem logMean_disk_geometry {T : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (2+(T:ℂ)*I) (7/4)) :
    1/4 ≤ z.re ∧ T-7/4 ≤ z.im ∧ z.im ≤ T+7/4 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h₁ := (Complex.abs_re_le_norm (z-(2+(T:ℂ)*I))).trans hz
  have h₂ := (Complex.abs_im_le_norm (z-(2+(T:ℂ)*I))).trans hz
  simp at h₁ h₂
  rcases abs_le.mp h₁ with ⟨h₁,_⟩
  rcases abs_le.mp h₂ with ⟨h₂,h₃⟩
  exact ⟨by linarith,by linarith,by linarith⟩

private theorem analyticOnNhd_zeta_logMean {T : ℝ} (hT : 8 ≤ T) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (2+(T:ℂ)*I) (7/4)) := by
  intro z hz
  apply (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) z
  intro he
  have h := (logMean_disk_geometry hz).2.1
  change z = 1 at he
  rw [he, Complex.one_im] at h
  linarith

private theorem zeta_logMean_disk_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {T : ℝ}, 8 ≤ T →
      ∀ z ∈ sphere (2+(T:ℂ)*I) (7/4),
      ‖riemannZeta z / riemannZeta (2+(T:ℂ)*I)‖ ≤ K*(T+4) := by
  obtain ⟨A,hA,HA⟩ := norm_riemannZeta_critical_strip_le_of_two_le (ε:=1/2) (by norm_num)
  obtain ⟨B,hB,HB⟩ := norm_riemannZeta_re_ge_one_le
  refine ⟨2*(1+A+B), by linarith, ?_⟩
  intro T hT z hz
  obtain ⟨hr,hi,hj⟩ := logMean_disk_geometry (sphere_subset_closedBall hz)
  have hi₀ : 2 ≤ |z.im| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hi' : |z.im| ≤ T + 7/4 := by rwa [abs_of_nonneg (by linarith)]
  have hzn : ‖riemannZeta z‖ ≤ (1+A+B)*(T+4) := by
    rcases le_or_gt 1 z.re with h | h
    · have H := HB h hi₀
      rw [Complex.re_add_im] at H
      have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < |z.im|+2)
      nlinarith only [H, mul_le_mul_of_nonneg_left (show Real.log (|z.im|+2) ≤ T+4 by linarith) hB.le,
        mul_nonneg (by linarith : 0≤1+A) (by linarith : 0≤T+4)]
    · have H := HA (show z.re ∈ Icc 0 1 from ⟨by linarith,h.le⟩) hi₀
      rw [Complex.re_add_im] at H
      have hp : |z.im|^((1-z.re)/2+1/2) ≤ |z.im| :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith : (1-z.re)/2+1/2≤1)).trans_eq (Real.rpow_one _)
      nlinarith only [H,mul_le_mul_of_nonneg_left (hp.trans hi') hA.le,
        mul_nonneg (by linarith : 0≤1+B) (by linarith : 0≤T+4),hA.le]
  have hlo : 1/2 ≤ ‖riemannZeta (2+(T:ℂ)*I)‖ := by
    convert norm_riemannZeta_ge_of_one_lt_re (by norm_num : (1:ℝ)<2) T using 1 <;> norm_num
  rw [norm_div,div_le_iff₀ (by linarith)]
  nlinarith only [hzn, mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ 2*(1+A+B)*(T+4) by positivity)]

/-- The integral over the horizontal segment is continuous through zero ordinates. -/
theorem continuousAt_zeta_horizontalLogMean {T : ℝ} (hT : 8 ≤ T) :
    ContinuousAt (horizontalLogMean riemannZeta) T := by
  obtain ⟨K,hK,HK⟩ := zeta_logMean_disk_bound
  apply continuousAt_horizontalLogMean (M:=K*(T+4)) (by positivity)
    (analyticOnNhd_zeta_logMean hT) (riemannZeta_ne_zero_of_one_lt_re (by simp))
  exact HK hT

/-- Horizontal logarithmic mean bound, valid also when a zero lies on the segment. -/
theorem zeta_horizontalLogMean_bound :
    ∃ C : ℝ, 0<C ∧ ∀ {T : ℝ}, 8 ≤ T →
      |horizontalLogMean riemannZeta T| ≤ C*(1+Real.log (T+4)) := by
  obtain ⟨K,hK,HK⟩ := zeta_logMean_disk_bound
  obtain ⟨C,hC,HC⟩ := abs_horizontalLogMean_le
  have hk₀ : 0<K := by linarith
  have hlogK := Real.log_nonneg hK
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  refine ⟨C*(1+Real.log 2+Real.log K),by positivity,?_⟩
  intro T hT
  let c : ℂ := 2+(T:ℂ)*I
  have hsep : ∀ u∈zeroSet riemannZeta c (13/8), 1≤‖c-u‖ := by
    intro u hu
    have hr : u.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re_bridge h (mem_zeroSet.mp hu).2
    have H := (Complex.abs_re_le_norm (c-u))
    have h := (le_abs_self (c-u).re).trans H
    simp [c] at h
    linarith
  have H := HC (f:=riemannZeta) (T:=T) (M:=K*(T+4))
    (one_le_mul_of_one_le_of_one_le hK (by linarith))
    (analyticOnNhd_zeta_logMean hT) (riemannZeta_ne_zero_of_one_lt_re (by simp)) (HK hT) hsep
  have hlogc : |Real.log ‖riemannZeta c‖| ≤ Real.log 2 := abs_log_norm_zeta_two_le T
  change |horizontalLogMean riemannZeta T| ≤ C*(|Real.log ‖riemannZeta c‖|+Real.log (K*(T+4))) at H
  rw [Real.log_mul hk₀.ne' (by linarith)] at H
  have htlog := Real.log_nonneg (by linarith : 1 ≤ T+4)
  apply H.trans
  calc
    _ ≤ C*((1+Real.log 2+Real.log K)*(1+Real.log (T+4))) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      nlinarith only [hlogc,mul_nonneg (add_nonneg hlog2.le hlogK) htlog]
    _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
