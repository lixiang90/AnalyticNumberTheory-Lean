import AnalyticNumberTheory.RiemannZeta.RiemannSiegelElementaryPhase
import AnalyticNumberTheory.RiemannZeta.CriticalCorrectionOscillation

/-!
# The corrected critical-line square mean on one block

The remainder in the corrected Riemann–Siegel formula is O(j^(-3/2)).
Multiplication by a polynomial of size O(sqrt j), followed by integration
over the block of length O(j), costs only a constant per block.
-/
noncomputable section
open Real Finset Set MeasureTheory
open scoped Interval
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

theorem hardyCutoffIndex_on_block {j : ℕ} {t : ℝ} (ht : t∈Ico (hardyCutoff j) (hardyCutoff (j+1))) :
    hardyCutoffIndex t=j := by
  have ht' : 0≤t := (show 0≤hardyCutoff j by dsimp [hardyCutoff];positivity).trans ht.1
  have H := (le_hardyCutoffIndex_iff ht').mpr ht.1
  have H' : ¬j+1≤hardyCutoffIndex t := fun h => ht.2.not_ge ((le_hardyCutoffIndex_iff ht').mp h)
  omega

private theorem abs_block_polynomial (j : ℕ) (t : ℝ) : |hardyBlockPolynomial j t|≤4*Real.sqrt j := by
  unfold hardyBlockPolynomial
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h : (∑n∈Finset.Icc 1 j, |Real.cos (hardyAngle n t)/Real.sqrt n|)≤∑n∈Finset.Icc 1 j,(Real.sqrt (n:ℝ))⁻¹ := by
    apply sum_le_sum;intro n _
    rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)).trans_eq (one_div _)
  linarith only [abs_sum_le_sum_abs (fun n : ℕ => Real.cos (hardyAngle n t)/Real.sqrt n) (Finset.Icc 1 j),
    h,sum_Icc_inv_sqrt_le j]

private theorem corrected_block_pointwise : ∃ C : ℝ,0<C ∧ ∀{j : ℕ} {t : ℝ},2≤j →
    t∈Ico (hardyCutoff j) (hardyCutoff (j+1)) →
    |hardyZ t^2-hardyBlockPolynomial j t^2-
      2*(-1:ℝ)^(j+1)*(hardyBlockPolynomial j t*hardyCorrectionWeight j t)|≤C/(j:ℝ) := by
  obtain ⟨K,hK,H⟩ := hardyZ_elementary_first_correction
  obtain ⟨D,hD,Hd⟩ := hardyCorrectionWeight_bounds
  refine ⟨8*K+(D+K)^2,by positivity,?_⟩
  intro j t hj ht
  let p := hardyBlockPolynomial j t
  let s := (-1:ℝ)^(j+1)
  let w := hardyCorrectionWeight j t
  let r := hardyZ t-p-s*w
  have hj' : (2:ℝ)≤j := by exact_mod_cast hj
  have hp : 0<(j:ℝ) := by linarith
  have hjsq : (j:ℝ)^2≤hardyCutoff j := by dsimp [hardyCutoff];nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg (j:ℝ))]
  have hmin : 8*Real.pi≤t := by
    have H' := mul_le_mul_of_nonneg_left (show 4≤(j:ℝ)^2 by nlinarith) (show 0≤2*Real.pi by positivity)
    dsimp [hardyCutoff] at ht;linarith only [H',ht.1]
  have hr := H hmin
  have hidx := hardyCutoffIndex_on_block ht
  change ⌊hardySaddleRoot t⌋₊=j at hidx
  change |hardyZ t-hardyBlockPolynomial ⌊hardySaddleRoot t⌋₊ t-
    (-1:ℝ)^(⌊hardySaddleRoot t⌋₊+1)*(Real.sqrt (hardySaddleRoot t))⁻¹*
    riemannSiegelCorrection (2*(hardySaddleRoot t-⌊hardySaddleRoot t⌋₊))|≤_ at hr
  rw [hidx,mul_assoc] at hr
  have hx := hardySaddleRoot_pos ((hardyCutoff_pos (by omega : 0<j)).trans_le ht.1)
  have hwe : (Real.sqrt (hardySaddleRoot t))⁻¹*riemannSiegelCorrection (2*(hardySaddleRoot t-j))=w := by
    dsimp [w,hardyCorrectionWeight];rw [Real.rpow_neg hx.le,←Real.sqrt_eq_rpow]
  rw [hwe] at hr
  change |r|≤K*t^(-(3/4:ℝ)) at hr
  have hpow : t^(-(3/4:ℝ))≤(j:ℝ)^(-(3/2:ℝ)) := by
    apply (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hp) (hjsq.trans ht.1) (by norm_num : -(3/4:ℝ)≤0)).trans_eq
    rw [←Real.rpow_natCast (j:ℝ) 2,←Real.rpow_mul hp.le];norm_num
  have hR := hr.trans (mul_le_mul_of_nonneg_left hpow hK.le)
  have hW := (Hd (by omega : 1≤j) ⟨ht.1,ht.2.le⟩).1
  change |w|≤_ at hW
  have hs : |s|=1 := by simp [s,abs_pow]
  have hcmp := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤j by linarith) (by norm_num : -(3/2:ℝ)≤ -(1/2))
  have hsl : |s*w+r|≤(D+K)*(j:ℝ)^(-(1/2:ℝ)) := by
    have hh := abs_add_le (s*w) r
    rw [abs_mul,hs,one_mul] at hh
    linarith only [hh,hW,hR,mul_le_mul_of_nonneg_left hcmp hK.le]
  have hP : |p|≤4*Real.sqrt j := abs_block_polynomial j t
  have he : hardyZ t^2-p^2-2*s*(p*w)=2*p*r+(s*w+r)^2 := by dsimp [r];ring
  change |hardyZ t^2-p^2-2*s*(p*w)|≤_
  rw [he]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg (s*w+r))]
  have hcross := mul_le_mul hP hR (abs_nonneg _) (show 0≤4*Real.sqrt j by positivity)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hsl 2
  rw [sq_abs,mul_pow,←Real.rpow_natCast ((j:ℝ)^(-(1/2:ℝ))) 2,←Real.rpow_mul hp.le,
    show -(1/2:ℝ)*(2:ℕ) = -1 by norm_num,Real.rpow_neg_one] at hsq
  have hpowers : Real.sqrt j*(j:ℝ)^(-(3/2:ℝ))=(j:ℝ)⁻¹ := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hp,show (1/2:ℝ)+ -(3/2)= -1 by norm_num,Real.rpow_neg_one]
  rw [show 4*Real.sqrt j*(K*(j:ℝ)^(-(3/2:ℝ)))=4*K*(Real.sqrt j*(j:ℝ)^(-(3/2:ℝ))) by ring,hpowers] at hcross
  rw [div_eq_mul_inv];linarith only [hcross,hsq]

/-- The corrected cosine-square discrepancy on each partial block is
controlled by one stationary term plus the logarithmic gaps. -/
theorem critical_corrected_block_mean : ∃ C : ℝ,0<C ∧ ∀ {j : ℕ} {b : ℝ},2≤j →
    b∈Icc (hardyCutoff j) (hardyCutoff (j+1)) →
    |∫t in (hardyCutoff j)..b,hardyZ t^2-hardyCosineMain t^2|≤
      C*(1+∑n∈Finset.Icc 1 j,criticalCosineGap j n) := by
  obtain ⟨A,hA,H⟩ := corrected_block_pointwise
  obtain ⟨B,hB,K⟩ := hardyBlock_correction_cross_term
  refine ⟨24*A+2*B,by positivity,?_⟩
  intro j b hj hb
  let a := hardyCutoff j
  let v := fun t => hardyBlockPolynomial j t*hardyCorrectionWeight j t
  let s := (-1:ℝ)^(j+1)
  let f := fun t => hardyZ t^2-hardyCosineMain t^2
  let S := ∑n∈Finset.Icc 1 j,criticalCosineGap j n
  have hS : 0≤S := sum_nonneg fun n _ => by unfold criticalCosineGap;split_ifs <;> positivity
  have ha : 0<a := hardyCutoff_pos (by omega)
  have hfc : IntervalIntegrable f volume a b := ((continuous_hardyZ.pow 2).intervalIntegrable ..).sub
    (hardyCosineMain_sq_intervalIntegrable ha.le hb.1)
  have hv : IntervalIntegrable v volume a b := by
    have h : ContinuousOn (hardyCorrectionWeight j) (uIcc a b) := by
      rw [uIcc_of_le hb.1];exact fun t ht => (hardyCorrectionWeight_hasDerivAt j (ha.trans_le ht.1)).continuousAt.continuousWithinAt
    exact ((continuous_hardyBlockPolynomial j).continuousOn.mul h).intervalIntegrable
  have hr := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a:=a) (b:=b) (C:=A/(j:ℝ))
    (f:=fun t=>f t-(2*s)*v t) (by
      filter_upwards [volume.ae_ne (hardyCutoff (j+1))] with t hne ht
      rw [uIoc_of_le hb.1] at ht
      have ht' : t∈Ico (hardyCutoff j) (hardyCutoff (j+1)) := ⟨ht.1.le,lt_of_le_of_ne (ht.2.trans hb.2) hne⟩
      have he : hardyCosineMain t=hardyBlockPolynomial j t := by
        dsimp only [hardyCosineMain,hardyBlockPolynomial];rw [hardyCutoffIndex_on_block ht']
      simpa only [Real.norm_eq_abs,f,v,s,he] using H hj ht')
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb.1),intervalIntegral.integral_sub (f:=f) (g:=fun t => (2*s)*v t)
    hfc (hv.const_mul _),intervalIntegral.integral_const_mul] at hr
  have hLen := le_trans (sub_le_sub_right hb.2 _) (hardyCutoff_step_length (by omega : 1≤j))
  have hp : 0<(j:ℝ) := Nat.cast_pos.mpr (by omega)
  have hR := hr.trans (mul_le_mul_of_nonneg_left hLen (by positivity))
  rw [show A/(j:ℝ)*(24*j)=24*A by field_simp] at hR
  have hh := K (by omega : 1≤j) hb
  change |∫t in a..b,v t|≤B*(1+S) at hh
  have hs : |2*s|=2 := by simp [s,abs_mul,abs_pow]
  let I := ∫t in a..b,f t
  let J := ∫t in a..b,v t
  change |I-2*s*J|≤24*A at hR
  have ht := abs_add_le (I-2*s*J) (2*s*J)
  rw [sub_add_cancel,abs_mul,hs] at ht
  change |I|≤(24*A+2*B)*(1+S)
  linarith only [ht,hR,hh,mul_nonneg hA.le hS]

end AnalyticNumberTheory.RiemannZeta
