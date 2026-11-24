import AnalyticNumberTheory.RiemannZeta.FourthMomentDiagonalComparison

/-!
# The leading term of the fourth moment from its divisor diagonal

The length of the short polynomial is a fixed fraction of the height. After taking the
height to infinity, that fraction can be made arbitrarily small to eliminate the
mean-value error.
-/

open Real Complex MeasureTheory Filter Set
open scoped Topology

namespace AnalyticNumberTheory.RiemannZeta

private theorem scaled_diagonal_tendsto {κ δ : ℝ} (hδ : 0 < δ)
    (hd : Tendsto (fun x : ℝ => fourthMomentDiagonal ⌊x⌋₊/(Real.log x)^4) atTop (𝓝 κ)) :
    Tendsto (fun T : ℝ => fourthMomentDiagonal ⌊δ*T⌋₊/(Real.log T)^4) atTop (𝓝 κ) := by
  have hdt : Tendsto (fun T : ℝ => δ*T) atTop atTop := (tendsto_const_mul_atTop_of_pos hδ).mpr tendsto_id
  have hratio : Tendsto (fun T : ℝ => Real.log (δ*T)/Real.log T) atTop (𝓝 1) := by
    have H : Tendsto (fun T : ℝ => Real.log δ/Real.log T + 1) atTop (𝓝 (0+1)) :=
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add_const 1
    rw [zero_add] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    rw [Real.log_mul hδ.ne' (by linarith),add_div,div_self (Real.log_pos hT).ne']
  have H := (hd.comp hdt).mul (hratio.pow 4)
  simp only [one_pow,mul_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),hdt.eventually (eventually_gt_atTop (1:ℝ))] with T hT ht
  change (fourthMomentDiagonal ⌊δ*T⌋₊/(Real.log (δ*T))^4)*(Real.log (δ*T)/Real.log T)^4 = _
  field_simp [(Real.log_pos ht).ne',(Real.log_pos hT).ne']

private theorem logarithmic_remainder_tendsto :
    Tendsto (fun T : ℝ => (1+Real.log T)^3 / (Real.log T)^4) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have H := ((tendsto_const_nhds.add h : Tendsto (fun T : ℝ => 1+(Real.log T)⁻¹) atTop (𝓝 (1+0))).pow 3).mul h
  simp only [add_zero,one_pow,mul_zero] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  field_simp [(Real.log_pos hT).ne']
  ring

/-- The dyadic fourth moment tends to twice the leading coefficient of the harmonic
divisor-square sum. -/
theorem fourthMoment_dyadic_tendsto_of_diagonal {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : Tendsto (fun x : ℝ => fourthMomentDiagonal ⌊x⌋₊/(Real.log x)^4) atTop (𝓝 κ)) :
    Tendsto (fun T : ℝ => (∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) /
      (T*(Real.log T)^4)) atTop (𝓝 (2*κ)) := by
  obtain ⟨C,hC,hc⟩ := fourthMoment_riemannZeta_dyadic_log_le
  let A := 16*C
  have hA : 0 < A := by dsimp [A]; positivity
  let Z (T : ℝ) := ∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4
  let W (T : ℝ) := T*(Real.log T)^4
  have hbound {T : ℝ} (hT : 2 ≤ T) (hl : 1 ≤ Real.log T) : Z T/W T ≤ A := by
    have hp : 0 < W T := by dsimp [W]; positivity
    apply (div_le_iff₀ hp).mpr
    apply (hc hT).trans
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log T)
      (by linarith : 1+Real.log T ≤ 2*Real.log T) 4) (show 0 ≤ C*T by positivity)
    exact H.trans_eq (by dsimp [W,A]; ring)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(4*(A+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηA : η*A ≤ ε/4 := by
    calc η*A ≤ η*(A+1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
         _ = _ := by dsimp [η]; field_simp
  let δ := min 1 (min (1/(4*π)) (ε/(16*π*(κ+1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left ..
  have hδπ : δ ≤ 1/(4*π) := (min_le_right ..).trans (min_le_left ..)
  have hδε : 4*π*δ*κ ≤ ε/4 := by
    have hh : δ ≤ ε/(16*π*(κ+1)) := (min_le_right ..).trans (min_le_right ..)
    have hh' := (le_div_iff₀ (by positivity : 0 < 16*π*(κ+1))).mp hh
    nlinarith only [hh',mul_pos Real.pi_pos hδ]
  obtain ⟨B,hB,hcomp⟩ := fourthMoment_dyadic_diagonal_comparison hδ hδ1 hδπ
  let d (T : ℝ) := fourthMomentDiagonal ⌊δ*T⌋₊/(Real.log T)^4
  let r (T : ℝ) := (1+Real.log T)^3/(Real.log T)^4
  let b := (1+1/η)*B
  have hd' : Tendsto d atTop (𝓝 κ) := scaled_diagonal_tendsto hδ hd
  have hr : Tendsto r atTop (𝓝 0) := logarithmic_remainder_tendsto
  have hlim : Tendsto (fun T => η*A+b*r T+(4*π*δ)*d T+2*|d T-κ|) atTop (𝓝 (η*A+4*π*δ*κ)) := by
    have hconstant : Tendsto (fun _ : ℝ => η*A) atTop (𝓝 (η*A)) := tendsto_const_nhds
    have H := ((hconstant.add (hr.const_mul b)).add (hd'.const_mul (4*π*δ))).add
      (((hd'.sub_const κ).abs).const_mul 2)
    simpa using H
  have hlε : η*A+4*π*δ*κ < ε := by linarith
  have hdt : Tendsto (fun T : ℝ => δ*T) atTop atTop := (tendsto_const_mul_atTop_of_pos hδ).mpr tendsto_id
  filter_upwards [eventually_ge_atTop (2:ℝ),hdt.eventually (eventually_ge_atTop (2:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),hlim.eventually_lt_const hlε] with T ht hdtT hl hsmall
  change dist (Z T/W T) (2*κ) < ε
  rw [Real.dist_eq]
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := by linarith
  have hW : 0 < W T := by dsimp [W]; positivity
  have hh := hcomp ht hdtT hη
  have hraw := div_le_div_of_nonneg_right hh hW.le
  have h₁ : |Z T/W T-2*d T| ≤ η*A+b*r T + (4*π*δ)*d T := by
    calc _ = |Z T-2*T*fourthMomentDiagonal ⌊δ*T⌋₊|/W T := by
              rw [show |Z T-2*T*fourthMomentDiagonal ⌊δ*T⌋₊|/W T = |(Z T-2*T*fourthMomentDiagonal ⌊δ*T⌋₊)/W T| by rw [abs_div,abs_of_pos hW]]
              congr 1
              dsimp only [d,W]
              field_simp
         _ ≤ _ := hraw
         _ = η*(Z T/W T)+b*r T+(4*π*δ)*d T := by
              change (η*Z T+(1+1/η)*B*T*(1+Real.log T)^3 + 4*π*δ*T*fourthMomentDiagonal ⌊δ*T⌋₊)/W T = _
              dsimp only [W,d,r,b]
              field_simp
         _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left (hbound ht hl) hη.le]
  apply lt_of_le_of_lt _ hsmall
  apply (abs_sub_le _ (2*d T) _).trans
  rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [h₁]

end AnalyticNumberTheory.RiemannZeta
