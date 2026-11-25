import AnalyticNumberTheory.SieveMethods.SelbergSharpInterval
import AnalyticNumberTheory.AnalyticTools.Summation.Abel

/-!
# The weighted Selberg denominator

Abel summation transfers a lower bound for the ordinary denominator to
the denominator with the Farey cost factor 1 + d/z.
-/

open Finset Real MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.SieveMethods

/-- The Selberg denominator with the individual Farey costs retained. -/
noncomputable def selbergWeightedDenominator (z : ℝ) : ℝ :=
  ∑ d∈(Icc 1 ⌊z⌋₊).filter Squarefree,(d.totient:ℝ)⁻¹*(z/(z+d))

private noncomputable def coefficient (n : ℕ) : ℝ :=
  if Squarefree n then (n.totient:ℝ)⁻¹ else 0

private theorem denominator_eq_sum (x : ℝ) :
    selbergDenominator x = ∑n ∈ Icc 1 ⌊x⌋₊,coefficient n := by simp [selbergDenominator,coefficient,sum_filter]

private noncomputable def kernel (z t : ℝ) := z/(z+t)^2

private theorem kernel_cont {z a b : ℝ} (hz : 0<z) (ha : 0≤a) :
    ContinuousOn (kernel z) (Set.Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have hp : z+t≠0 := (add_pos_of_pos_of_nonneg hz (ha.trans ht.1)).ne'
  unfold kernel;fun_prop (disch := positivity)

private theorem weighted_denominator_abel {z : ℝ} (hz : 1≤z) :
    selbergWeightedDenominator z = selbergDenominator z/2+
      ∫ t in (1:ℝ)..z, kernel z t*selbergDenominator t := by
  let f (t:ℝ) := z/(z+t)
  have hpos : 0<z := by linarith
  have hd (t : ℝ) (ht : t∈Set.Icc (1:ℝ) z) : HasDerivAt f (-kernel z t) t := by
    have hzt : z+t≠0 := by linarith [ht.1]
    have H := (hasDerivAt_const t z).div ((hasDerivAt_id t).const_add z) hzt
    convert H using 1
    · rfl
    · simp [kernel,neg_div]
  have H := abel_summation_Icc_one_hasDerivAt coefficient hz hd (kernel_cont hpos zero_le_one).neg
  have hsum : selbergWeightedDenominator z = ∑k∈Icc 1 ⌊z⌋₊,coefficient k*f k := by
    simp only [selbergWeightedDenominator,sum_filter,coefficient]
    apply sum_congr rfl;intro k _;split_ifs <;> simp [f]
  have hzval : f z=1/2 := by dsimp [f];field_simp;ring
  rw [hsum,H,hzval,←denominator_eq_sum]
  simp_rw [←denominator_eq_sum,mul_neg,intervalIntegral.integral_neg,sub_neg_eq_add]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr;intro t _;ring

private theorem kernel_times_denominator_integrable {z a b : ℝ} (hz : 0<z) (ha : 0≤a) (hab : a≤b) :
    IntervalIntegrable (fun t => kernel z t*selbergDenominator t) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  simpa only [denominator_eq_sum] using
    integrableOn_mul_sum_Icc coefficient (m:=1) ha (kernel_cont hz ha).integrableOn_Icc

private theorem kernel_log_primitive {z t : ℝ} (hz : 0<z) (ht : 0<t) (b : ℝ) :
    HasDerivAt (fun u : ℝ => u/(z+u)*(log u+b)-log (z+u)) (kernel z t*(log t+b)) t := by
  have hzt := add_pos hz ht
  have hd := (hasDerivAt_id t).const_add z
  have H := (((hasDerivAt_id t).div hd hzt.ne').mul ((Real.hasDerivAt_log ht.ne').add_const b)).sub
    ((Real.hasDerivAt_log hzt.ne').comp t hd)
  convert H using 1
  · rfl
  · simp only [kernel,id_eq,Pi.div_apply]; field_simp [ht.ne',hzt.ne'];ring

private theorem integral_kernel_log {z a b : ℝ} (hz : 0<z) (ha : 0<a) (hab : a≤b) (c : ℝ) :
    (∫ t in a..b,kernel z t*(log t+c)) =
      (b/(z+b)*(log b+c)-log (z+b))-(a/(z+a)*(log a+c)-log (z+a)) := by
  have hg : ContinuousOn (fun t => kernel z t*(log t+c)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (kernel_cont hz ha.le).mul ((Real.continuousOn_log.mono fun (t : ℝ) (ht : t ∈ Set.Icc a b) => (ha.trans_le ht.1).ne').add continuousOn_const)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hg.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact kernel_log_primitive hz (ha.trans_le ht.1) c

/-- For cutoffs at least 100, a surplus of 1.076 beyond the logarithm
from 6 on gives a surplus of 0.31 in the denominator with Farey weights. -/
theorem selbergWeightedDenominator_ge_of_surplus
    (H : ∀ t : ℝ,6≤t → log t+1.076≤selbergDenominator t) {z : ℝ} (hz : 100≤z) :
    log z+0.31≤selbergWeightedDenominator z := by
  have hpos : 0<z := by linarith
  have step {a b c : ℝ} (ha : 0<a) (hab : a≤b)
      (h : ∀t∈Set.Icc a b, log t+c≤selbergDenominator t) :
      (b/(z+b)*(log b+c)-log (z+b))-(a/(z+a)*(log a+c)-log (z+a)) ≤
        ∫t in a..b,kernel z t*selbergDenominator t := by
    rw [←integral_kernel_log hpos ha hab]
    have hcont : ContinuousOn (fun t => kernel z t*(log t+c)) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact (kernel_cont hpos ha.le).mul ((Real.continuousOn_log.mono fun (t : ℝ) (ht : t ∈ Set.Icc a b) => (ha.trans_le ht.1).ne').add continuousOn_const)
    apply intervalIntegral.integral_mono_on hab hcont.intervalIntegrable (kernel_times_denominator_integrable hpos ha.le hab)
    intro t ht;exact mul_le_mul_of_nonneg_left (h t ht) (by dsimp [kernel];positivity)
  have h₁ := step (a:=1) (b:=6) (c:=0) (by norm_num) (by norm_num)
    (fun t ht => by simpa [selbergDenominator] using sum_squarefree_inv_totient_ge_log ht.1)
  have h₂ := step (a:=6) (b:=z) (c:=1.076) (by norm_num) (by linarith) (fun t ht => H t ht.1)
  have hDz := H z (by linarith)
  rw [weighted_denominator_abel (by linarith : 1≤z),←intervalIntegral.integral_add_adjacent_intervals
    (kernel_times_denominator_integrable hpos zero_le_one (by norm_num : (1:ℝ)≤6))
    (kernel_times_denominator_integrable hpos (by norm_num : (0:ℝ)≤6) (by linarith : 6≤z))]
  have hzz : z/(z+z)=1/2 := by field_simp;ring
  have hlz : log (z+z) = log 2+log z := by rw [←Real.log_mul (by norm_num) hpos.ne'];congr 1;ring
  have hzl : log z≤log (z+1) := Real.log_le_log hpos (by linarith)
  have hs : 6/(z+6)≤0.06 := by rw [div_le_iff₀ (by linarith : 0<z+6)];linarith
  rw [hzz,hlz] at h₂
  simp only [Real.log_one,add_zero,mul_zero,zero_sub,sub_neg_eq_add] at h₁
  nlinarith only [h₁,h₂,hDz,hzl,hs,Real.log_two_lt_d9]

end AnalyticNumberTheory.SieveMethods
