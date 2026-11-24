import AnalyticNumberTheory.DivisorProblems.DivisorSquareConvolution

/-!
# Harmonic means under divisor transformation

Convolution with the constant-one function integrates the leading
logarithmic term. The error in replacing the inner harmonic sum by its
logarithm is bounded by the preceding harmonic mean.
-/
noncomputable section
open Finset Real MeasureTheory
open scoped LSeries.notation ArithmeticFunction.zeta ArithmeticFunction.Moebius
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DivisorProblems

/-- The harmonic sum of an arithmetic function over the positive integers
up to a real cutoff. -/
def harmonicMean (f : ArithmeticFunction ℝ) (x : ℝ) : ℝ :=
  partialSum (fun n : ℕ => f n / n) x

private theorem partialSum_mul_intervalIntegrable (a : ℕ → ℝ) {g : ℝ → ℝ} {x : ℝ} (hx : 1≤x)
    (hg : ContinuousOn g (Set.Icc 1 x)) :
    IntervalIntegrable (fun t => partialSum a t*g t) volume 1 x := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
  simpa only [partialSum,mul_comm] using integrableOn_mul_sum_Icc a (m:=1) zero_le_one hg.integrableOn_Icc

private theorem log_kernel_integral (k : ℕ) {x : ℝ} (hx : 1≤x) :
    ∫ t in (1:ℝ)..x,(log t)^k/t = (log x)^(k+1)/(k+1) := by
  have hc : ContinuousOn (fun t : ℝ => (log t)^k/t) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx]; apply continuousOn_of_forall_continuousAt
    intro t ht; have ht' : t≠0 := (zero_lt_one.trans_le ht.1).ne'; fun_prop (disch := assumption)
  have hd (t : ℝ) (ht : t∈Set.uIcc 1 x) :
      HasDerivAt (fun u : ℝ => (log u)^(k+1)/((k:ℝ)+1)) ((log t)^k/t) t := by
    rw [Set.uIcc_of_le hx] at ht; have ht' := (zero_lt_one.trans_le ht.1).ne'
    convert ((Real.hasDerivAt_log ht').pow (k+1)).div_const ((k:ℝ)+1) using 1
    push_cast; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]; simp

private theorem harmonic_transform_sum (f : ArithmeticFunction ℝ) (x : ℝ) :
    harmonicMean (divisorTransform f) x =
      ∑ n ∈ Icc 1 ⌊x⌋₊,(f n/n)*partialSum (fun m : ℕ => (m:ℝ)⁻¹) (x/n) := by
  change partialSum _ x=_
  rw [←partialSum_convolution_eq_sum]
  apply congrArg (fun g : ℕ → ℝ => partialSum g x)
  funext n
  rw [divisorTransform,ArithmeticFunction.mul_apply,LSeries.convolution_def,Finset.sum_div]
  apply sum_congr rfl
  rintro ⟨d,m⟩ hdm
  obtain ⟨he,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hdm
  have hm : m≠0 := by rintro rfl; simp_all
  rw [←he,Nat.cast_mul,ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hm]
  push_cast; ring

/-- The harmonic mean of a divisor transform differs from the integral of
the preceding mean by a quantity between zero and the preceding mean. -/
theorem harmonic_transform_integral_error (f : ArithmeticFunction ℝ) (hf : ∀ n, 0≤f n) {x : ℝ} (hx : 1≤x) :
    |harmonicMean (divisorTransform f) x - ∫ t in (1:ℝ)..x,harmonicMean f t/t| ≤ harmonicMean f x := by
  let w (n : ℕ) : ℝ := f n / n
  have hp (n : ℕ) (hn : n∈Icc 1 ⌊x⌋₊) : 0<(n:ℝ) ∧ (n:ℝ)≤x :=
    ⟨by exact_mod_cast (mem_Icc.mp hn).1,(Nat.le_floor_iff (zero_le_one.trans hx)).mp (mem_Icc.mp hn).2⟩
  have hlog := abel_summation_Icc_one_hasDerivAt w hx
    (fun t ht => Real.hasDerivAt_log (zero_lt_one.trans_le ht.1).ne')
    (continuousOn_id.inv₀ (fun t ht => (zero_lt_one.trans_le ht.1).ne'))
  have hsign : (∑ n∈Icc 1 ⌊x⌋₊,w n*log (x/n)) = ∫ t in (1:ℝ)..x,harmonicMean f t/t := by
    simp_rw [div_eq_mul_inv] at *
    change _=∫ t in (1:ℝ)..x,(∑ n∈Icc 1 ⌊t⌋₊,w n)*t⁻¹
    rw [show (∑ n∈Icc 1 ⌊x⌋₊,w n*log (x*(n:ℝ)⁻¹)) =
      (∑ n∈Icc 1 ⌊x⌋₊,w n)*log x-∑ n∈Icc 1 ⌊x⌋₊,w n*log n by
      rw [Finset.sum_mul,←sum_sub_distrib]; apply sum_congr rfl; intro n hn
      rw [Real.log_mul (zero_lt_one.trans_le hx).ne' (inv_ne_zero (hp n hn).1.ne'),Real.log_inv]; ring]
    linarith
  rw [←hsign,harmonic_transform_sum,←sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  change _ ≤ ∑ n∈Icc 1 ⌊x⌋₊,w n
  apply sum_le_sum; intro n hn
  have hu : 1≤x/n := (one_le_div (hp n hn).1).mpr (hp n hn).2
  have h1 := log_le_sum_inv (zero_le_one.trans hu)
  have h2 := sum_inv_le_one_add_log hu
  have hnw : 0≤w n := div_nonneg (hf _) (Nat.cast_nonneg _)
  change |w n*(_ : ℝ)-w n*_| ≤ w n
  rw [←mul_sub,abs_mul,abs_of_nonneg hnw]
  apply mul_le_of_le_one_right hnw
  change |(∑ m ∈ Icc 1 ⌊x/n⌋₊,(m:ℝ)⁻¹) - log (x/n)| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]; linarith

/-- A uniform error of logarithmic degree k becomes a uniform error of
degree k+1 under divisor transformation. -/
theorem harmonic_transform_log_asymptotic {f : ArithmeticFunction ℝ} (hf : ∀ n, 0≤f n)
    (k : ℕ) {c B : ℝ} (hc : 0≤c) (hB : 0≤B)
    (ha : ∀ {x:ℝ}, 1≤x → |harmonicMean f x-c*(log x)^(k+1)| ≤ B*(1+log x)^k) :
    ∀ {x:ℝ}, 1≤x →
      |harmonicMean (divisorTransform f) x-(c/(k+2))*(log x)^(k+2)| ≤
        (c+2*B)*(1+log x)^(k+1) := by
  intro x hx
  have hl := Real.log_nonneg hx
  have hs := harmonic_transform_integral_error f hf hx
  have hA := ha hx
  have hpow : (1+log x)^k≤(1+log x)^(k+1) := by rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hxH : harmonicMean f x≤(c+B)*(1+log x)^(k+1) := by
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl (show log x≤1+log x by linarith) (k+1)) hc
    nlinarith only [(abs_le.mp hA).2,hm,mul_le_mul_of_nonneg_left hpow hB]
  have hd (t : ℝ) (ht : t ∈ Set.Icc (1:ℝ) x) : 0<t := zero_lt_one.trans_le ht.1
  have hi : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) := continuousOn_id.inv₀ fun t ht => (hd t ht).ne'
  have hI : IntervalIntegrable (fun t => harmonicMean f t/t) volume 1 x := by
    simpa only [harmonicMean,div_eq_mul_inv] using partialSum_mul_intervalIntegrable (fun n : ℕ => f n/n) hx hi
  have hJ : ContinuousOn (fun t : ℝ => c*((log t)^(k+1)/t)) (Set.Icc 1 x) := by
    apply continuousOn_of_forall_continuousAt; intro t ht; have := (hd t ht).ne'; fun_prop (disch := assumption)
  have hK : IntervalIntegrable (fun t : ℝ => B*(1+log x)^k*t⁻¹) volume 1 x :=
    (hi.const_mul _).intervalIntegrable_of_Icc hx
  have herr := intervalIntegral.norm_integral_le_of_norm_le (f:=fun t : ℝ => harmonicMean f t/t-c*((log t)^(k+1)/t)) hx
    (Filter.Eventually.of_forall fun t ht => show ‖_‖≤B*(1+log x)^k*t⁻¹ by
      have ht' := hd t ⟨ht.1.le,ht.2⟩
      rw [Real.norm_eq_abs,show harmonicMean f t/t-c*((log t)^(k+1)/t) = (harmonicMean f t-c*(log t)^(k+1))/t by ring,
        abs_div,abs_of_pos ht',←div_eq_mul_inv]
      exact div_le_div_of_nonneg_right ((ha ht.1.le).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Real.log_nonneg ht.1.le]) (by linarith [Real.log_le_log ht' ht.2]) k) hB)) ht'.le) hK
  rw [intervalIntegral.integral_sub hI (hJ.intervalIntegrable_of_Icc hx),intervalIntegral.integral_const_mul,
    log_kernel_integral (k+1) hx,intervalIntegral.integral_const_mul,integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx),div_one,Real.norm_eq_abs] at herr
  push_cast at herr
  have htri := abs_sub_le (harmonicMean (divisorTransform f) x) (∫ t in (1:ℝ)..x,harmonicMean f t/t)
    ((c/(k+2))*(log x)^(k+2))
  have heq : c*((log x)^(k+1+1)/((k:ℝ)+1+1)) = (c/(k+2))*(log x)^(k+2) := by ring
  rw [heq] at herr
  have hsmall : B*(1+log x)^k*log x ≤ B*(1+log x)^(k+1) := by
    rw [pow_succ,mul_assoc B]; apply mul_le_mul_of_nonneg_left _ hB
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) k)
  exact htri.trans ((add_le_add (hs.trans hxH) (herr.trans hsmall)).trans_eq (by ring))

end AnalyticNumberTheory.DivisorProblems
