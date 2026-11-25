import AnalyticNumberTheory.AnalyticTools.BoundedAmplitude
import AnalyticNumberTheory.RiemannZeta.CriticalCorrectionWeights
import AnalyticNumberTheory.RiemannZeta.CriticalCosineOffDiagonal

/-!
# Oscillation of the first correction against the main cosine sum

On block j the j-th mode is treated at its stationary endpoint.
All earlier modes are nonstationary; integration against the smooth
correction retains their reciprocal logarithmic spacing.
-/
noncomputable section
open Real Finset MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

def hardyBlockPolynomial (j : ℕ) (t : ℝ) :=
  2*∑n∈Finset.Icc 1 j,Real.cos (hardyAngle n t)/Real.sqrt n

theorem continuous_hardyBlockPolynomial (j : ℕ) : Continuous (hardyBlockPolynomial j) := by
  change Continuous (fun t : ℝ => 2*∑n∈Finset.Icc 1 j,Real.cos (hardyAngle n t)/Real.sqrt n)
  apply Continuous.mul continuous_const
  exact continuous_finsetSum (f:=fun n (t:ℝ) => Real.cos (hardyAngle n t)/Real.sqrt n) (Finset.Icc 1 j)
    (fun n _ => (Real.continuous_cos.comp (continuous_hardyAngle n)).div_const (Real.sqrt (n:ℝ)))

theorem hardyCutoff_step_length {j : ℕ} (hj : 1≤j) :
    hardyCutoff (j+1)-hardyCutoff j≤24*(j:ℝ) := by
  have hj' : (1:ℝ)≤j := by exact_mod_cast hj
  dsimp [hardyCutoff];push_cast
  nlinarith only [mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Nat.cast_nonneg j),Real.pi_lt_four.le,hj']

theorem hardyCutoff_pos {j : ℕ} (hj : 0<j) : 0<hardyCutoff j := by dsimp [hardyCutoff];positivity

private theorem correction_weight_integral_terms {C : ℝ} (hC : 0<C)
    (H : ∀ {j : ℕ} {t : ℝ},1≤j → t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) →
      |hardyCorrectionWeight j t|≤C*(j:ℝ)^(-(1/2:ℝ)) ∧ |hardyCorrectionWeightDeriv j t|≤C*(j:ℝ)^(-(3/2:ℝ)))
    {j n : ℕ} (hj : 1≤j) (hn : n∈Finset.Icc 1 j) {b : ℝ} (hb : b∈Icc (hardyCutoff j) (hardyCutoff (j+1))) :
    |∫t in (hardyCutoff j)..b,(Real.cos (hardyAngle n t)/Real.sqrt n)*hardyCorrectionWeight j t|≤
      (if n=j then 24*C else 0)+50*C*criticalCosineGap j n := by
  let a := hardyCutoff j
  let f := fun t : ℝ => Real.cos (hardyAngle n t)
  let w := hardyCorrectionWeight j
  have hnp := (Finset.mem_Icc.mp hn).1
  have hnj := (Finset.mem_Icc.mp hn).2
  have hj' : 0<(j:ℝ) := Nat.cast_pos.mpr hj
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hnp
  have ha : 0<a := hardyCutoff_pos hj
  have hLen : b-a≤24*(j:ℝ) := le_trans (sub_le_sub_right hb.2 _) (hardyCutoff_step_length hj)
  have hw (t : ℝ) (ht : t∈Icc a b) := H hj (show t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) from ⟨ht.1,ht.2.trans hb.2⟩)
  have he : (∫t in a..b,(Real.cos (hardyAngle n t)/Real.sqrt n)*hardyCorrectionWeight j t)=
      (∫t in a..b,f t*w t)/Real.sqrt n := by rw [←intervalIntegral.integral_div];apply intervalIntegral.integral_congr;intro t _;dsimp [f,w];ring
  rw [he,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases he : n=j
  · subst n
    simp only [ite_true,criticalCosineGap,mul_zero,add_zero]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (f:=fun t=>f t*w t)
      (C:=C*(j:ℝ)^(-(1/2:ℝ))) (fun t ht => by
        rw [uIoc_of_le hb.1] at ht
        rw [Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa [w] using (hw t ⟨ht.1.le,ht.2⟩).1))
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb.1)] at hi
    apply (div_le_div_of_nonneg_right (hi.trans (mul_le_mul_of_nonneg_left hLen (by positivity))) (Real.sqrt_nonneg _)).trans_eq
    rw [Real.rpow_neg hj'.le,←Real.sqrt_eq_rpow]
    have hs := Real.sq_sqrt hj'.le
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hj')] <;> nlinarith only [hs]
  · have hnj' := lt_of_le_of_ne hnj he
    let d := Real.log j-Real.log n
    have hd : 0<d := sub_pos.mpr (Real.log_lt_log hn' (by exact_mod_cast hnj'))
    have HF (t : ℝ) (ht : t∈Icc a b) : |∫u in a..t,f u|≤4/d :=
      abs_integral_hardyPhase_from_later_mode hnp hnj' le_rfl ht.1
    have hi := abs_integral_mul_of_partial_integrals (g:=w) hb.1 (Real.continuous_cos.comp (continuous_hardyAngle n))
      (fun t ht => hardyCorrectionWeight_hasDerivAt j (ha.trans_le ht.1))
      ((continuousOn_hardyCorrectionWeightDeriv j).mono (fun t ht => ha.trans_le ht.1))
      HF (hw b ⟨hb.1,le_rfl⟩).1 (fun t ht => (hw t ht).2)
    have hfee : C*(j:ℝ)^(-(1/2:ℝ))+(b-a)*(C*(j:ℝ)^(-(3/2:ℝ)))≤25*C*(j:ℝ)^(-(1/2:ℝ)) := by
      have H' := mul_le_mul_of_nonneg_right hLen (show 0≤C*(j:ℝ)^(-(3/2:ℝ)) by positivity)
      rw [show (j:ℝ)^(-(3/2:ℝ))=(j:ℝ)^(-(1/2:ℝ))/(j:ℝ) by rw [←Real.rpow_sub_one hj'.ne'];norm_num] at H'
      have h := (show 24*(j:ℝ)*(C*((j:ℝ)^(-(1/2:ℝ))/j))=24*C*(j:ℝ)^(-(1/2:ℝ)) by field_simp)
      rw [h] at H'
      rw [show (j:ℝ)^(-(3/2:ℝ))=(j:ℝ)^(-(1/2:ℝ))/(j:ℝ) by rw [←Real.rpow_sub_one hj'.ne'];norm_num]
      linarith only [H']
    apply (div_le_div_of_nonneg_right (hi.trans (mul_le_mul_of_nonneg_left hfee (by positivity))) (Real.sqrt_nonneg _)).trans_eq
    simp only [he,ite_false,zero_add,criticalCosineGap,Ne.symm he]
    rw [abs_of_nonpos (by dsimp [d] at hd;linarith : Real.log n-Real.log j≤0),neg_sub,
      Real.rpow_neg hn'.le,←Real.sqrt_eq_rpow]
    dsimp [d];ring

/-- Integral of the main polynomial against the first smooth amplitude
on a complete or partial block. -/
theorem hardyBlock_correction_cross_term : ∃ C : ℝ,0<C ∧ ∀ {j : ℕ} {b : ℝ},1≤j →
    b∈Icc (hardyCutoff j) (hardyCutoff (j+1)) →
    |∫t in (hardyCutoff j)..b,hardyBlockPolynomial j t*hardyCorrectionWeight j t|≤
      C*(1+∑n∈Finset.Icc 1 j,criticalCosineGap j n) := by
  obtain ⟨C,hC,H⟩ := hardyCorrectionWeight_bounds
  refine ⟨100*C,by positivity,?_⟩
  intro j b hj hb
  let S := Finset.Icc 1 j
  let a := hardyCutoff j
  let w := hardyCorrectionWeight j
  let f := fun n (t : ℝ) => (Real.cos (hardyAngle n t)/Real.sqrt n)*w t
  have hmem : j∈S := Finset.mem_Icc.mpr ⟨hj,le_rfl⟩
  have hcont : ContinuousOn w (uIcc a b) := by
    rw [uIcc_of_le hb.1]
    exact fun t ht => (hardyCorrectionWeight_hasDerivAt j ((hardyCutoff_pos hj).trans_le ht.1)).continuousAt.continuousWithinAt
  have hi (n : ℕ) : IntervalIntegrable (f n) volume a b :=
    (((Real.continuous_cos.comp (continuous_hardyAngle n)).div_const _).continuousOn.mul hcont).intervalIntegrable
  have he : (∫t in a..b,hardyBlockPolynomial j t*w t)=2*(∑n∈S,∫t in a..b,f n t) := by
    rw [←intervalIntegral.integral_finsetSum (f:=f) (fun n _ => hi n),←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr;intro t _
    dsimp only [hardyBlockPolynomial,f,S];rw [mul_assoc,sum_mul]
  change |∫t in a..b,hardyBlockPolynomial j t*w t|≤_
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have H' := (abs_sum_le_sum_abs (fun n => ∫t in a..b,f n t) S).trans
    (sum_le_sum (fun n hn => correction_weight_integral_terms hC H hj hn hb))
  rw [sum_add_distrib,sum_ite_eq',if_pos hmem,←mul_sum] at H'
  linarith only [H',hC.le]

end AnalyticNumberTheory.RiemannZeta
