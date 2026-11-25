import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Dyadic increments and power-weighted integrals

A local power-saving for the primitive on each dyadic interval sums with
a geometric series. Partial integration transfers the discrepancy to a
power weight with its supremum on the interval.
-/
open MeasureTheory Real Set
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- A uniform bound for every partial dyadic increment gives the same
power bound for the full increment from a fixed positive endpoint. -/
theorem power_bound_of_dyadic_increments {F : ℝ→ℝ} {a q C : ℝ} (ha : 0<a) (hq : 0<q) (hC : 0≤C)
    (H : ∀ {t u : ℝ},a≤t → t≤u → u≤2*t → |F u-F t|≤C*t^q) :
    ∃ K : ℝ,0<K ∧ ∀ {T : ℝ},a≤T → |F T-F a|≤K*T^q := by
  let b := (2:ℝ)^q
  let A := C/(b-1)+1
  have hb : 1<b := Real.one_lt_rpow (by norm_num) hq
  have hA : 0<A := by dsimp [A];positivity
  have hrec : C+A ≤ A*b := by
    have hh := (div_le_iff₀ (by linarith : 0<b-1)).mp (show C/(b-1)≤A by dsimp [A];linarith)
    linarith
  have hgrid (n : ℕ) : |F (a*2^n)-F a|≤A*(a*2^n)^q := by
    induction n with
    | zero => simpa using (show 0≤A*a^q by positivity)
    | succ n ih =>
      let t := a*2^n
      have ht : a≤t := by dsimp [t];nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=n)]
      have he : a*2^(n+1)=2*t := by dsimp [t];ring
      rw [he,Real.mul_rpow (by norm_num) (by linarith : 0≤t)]
      calc |F (2*t)-F a| ≤ |F (2*t)-F t|+|F t-F a| := abs_sub_le ..
           _ ≤ C*t^q+A*t^q := add_le_add (H ht (by linarith) le_rfl) ih
           _ ≤ _ := by have := mul_le_mul_of_nonneg_right hrec (Real.rpow_nonneg (by linarith : 0≤t) q)
                       dsimp only [b] at this;linarith only [this]
  refine ⟨A+C,by positivity,?_⟩
  intro T hT
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near ((one_le_div ha).mpr hT) (by norm_num : (1:ℝ)<2)
  let t := a*2^n
  have ht : a≤t := by dsimp [t];nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=n)]
  have htT : t≤T := by dsimp [t]; linarith [(le_div_iff₀ ha).mp hn]
  have hTt : T≤2*t := by dsimp [t]; rw [pow_succ] at hn';linarith [(div_lt_iff₀ ha).mp hn']
  calc |F T-F a| ≤ |F T-F t|+|F t-F a| := abs_sub_le ..
       _ ≤ C*t^q+A*t^q := add_le_add (H ht htT hTt) (hgrid n)
       _ ≤ _ := by rw [←add_mul,add_comm C];gcongr

/-- If every partial integral of f over [a,b] has absolute value at most
E, multiplying by the increasing weight t^k costs at most 2 b^k. -/
theorem abs_power_weighted_integral_le {f : ℝ→ℝ} (hf : Continuous f) {a b k E : ℝ}
    (ha : 0<a) (hab : a≤b) (hk : 0≤k)
    (hF : ∀t∈Icc a b, |∫ u in a..t,f u|≤E) :
    |∫ t in a..b,f t*t^k|≤2*E*b^k := by
  let F := fun t : ℝ => ∫ u in a..t,f u
  let w := fun t : ℝ => t^k
  let w' := fun t : ℝ => k*t^(k-1)
  have hE : 0≤E := by simpa using hF a ⟨le_rfl,hab⟩
  have hF' (t : ℝ) : HasDerivAt F (f t) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hw' (t : ℝ) (ht : 0<t) : HasDerivAt w (w' t) t := Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hcont : ContinuousOn w' (uIcc a b) := by
    rw [uIcc_of_le hab];exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ha.trans_le ht.1).ne'))
  have hw : ContinuousOn w (uIcc a b) := by
    rw [uIcc_of_le hab];exact continuousOn_id.rpow_const (fun t ht => Or.inl (ha.trans_le ht.1).ne')
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF' t).continuousAt
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hFc.continuousOn hw
    (fun t _ => hF' t) (fun t ht => hw' t (by rw [min_eq_left hab,max_eq_right hab] at ht;linarith [ht.1]))
    (hf.intervalIntegrable ..) (hcont.intervalIntegrable (μ:=volume))
  have hent : (∫ t in a..b,w' t)=w b-w a := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hw' t (by rw [uIcc_of_le hab] at ht;linarith [ht.1])) hcont.intervalIntegrable
  have hI : |∫ t in a..b,F t*w' t|≤E*(w b-w a) := by
    rw [←hent,←intervalIntegral.integral_const_mul,←Real.norm_eq_abs]
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    apply intervalIntegral.integral_mono_on hab ((hFc.continuousOn.mul hcont).norm.intervalIntegrable)
      ((continuousOn_const.mul hcont).intervalIntegrable)
    intro t ht
    have hpos : 0≤w' t := mul_nonneg hk (Real.rpow_nonneg (ha.trans_le ht.1).le _)
    change ‖F t*w' t‖≤E*w' t
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hpos]
    exact mul_le_mul_of_nonneg_right (hF t ht) hpos
  rw [intervalIntegral.integral_add (f:=fun t => f t*w t) (g:=fun t => F t*w' t) ((hf.continuousOn.mul hw).intervalIntegrable)
    ((hFc.continuousOn.mul hcont).intervalIntegrable)] at hparts
  have hFa : F a=0 := by simp [F]
  rw [hFa,zero_mul,sub_zero] at hparts
  have hb : 0≤w b := Real.rpow_nonneg (ha.trans_le hab).le _
  have hwa : 0≤w a := Real.rpow_nonneg ha.le _
  change |∫ t in a..b,f t*w t|≤_
  rw [show (∫ t in a..b,f t*w t)=F b*w b-(∫ t in a..b,F t*w' t) by linarith only [hparts] ]
  exact (abs_sub _ _).trans (by rw [abs_mul,abs_of_nonneg hb];change _≤2*E*w b
                                nlinarith only [mul_le_mul_of_nonneg_right (hF b ⟨hab,le_rfl⟩) hb,hI,mul_nonneg hE hwa])

end AnalyticNumberTheory.AnalyticTools
