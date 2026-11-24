import Mathlib.Analysis.Real.Pi.Bounds
import AnalyticNumberTheory.DivisorProblems.DivisorTransformHarmonic

/-!
# The leading term for the harmonic mean of the squared divisor function

The squarefree density is 6/π². Three successive divisor transforms
divide this coefficient by 2, 3 and 4. Abel summation gives a uniform
lower-order error throughout.
-/
noncomputable section
open Real Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.Moebius
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DivisorProblems

/-- The squarefree integers have harmonic mean (6/π²) log x with uniformly bounded remainder. -/
theorem squarefree_harmonic_error {x : ℝ} (hx : 1≤x) :
    |harmonicMean squarefreeIndicator x-(6/π^2)*log x| ≤ 20+6/π^2 := by
  let c : ℝ := 6/π^2
  let a (n : ℕ) : ℝ := squarefreeIndicator n - c
  have hc : 0≤c := by dsimp [c]; positivity
  have hc1 : c≤1 := by dsimp [c]; rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA {t : ℝ} (ht : 1≤t) : |partialSum a t| ≤ 4*√t := by
    have he : partialSum a t = squarefreeError t+c*(t-⌊t⌋₊) := by
      simp [a,partialSum,Finset.sum_sub_distrib,squarefreeError,squarefreeCount,c]; ring
    rw [he]
    have hf : 0≤t-⌊t⌋₊ := sub_nonneg.mpr (Nat.floor_le (zero_le_one.trans ht))
    have hf1 : t-⌊t⌋₊≤1 := by linarith [Nat.lt_floor_add_one t]
    have h1 : 1≤√t := by simpa using Real.sqrt_le_sqrt ht
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (mul_nonneg hc hf)]; nlinarith [abs_squarefreeError_le (zero_le_one.trans ht),mul_le_mul hc1 hf1 hf zero_le_one])
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hAb := abel_summation_Icc_one_hasDerivAt a (f:=fun t : ℝ => t⁻¹) (f':=fun t : ℝ => -(t^2)⁻¹) hx
    (fun t ht => by convert hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne' using 1)
    (by apply continuousOn_of_forall_continuousAt; intro t ht; have hn := (zero_lt_one.trans_le ht.1).ne'; fun_prop (disch := positivity))
  have he : (∑ n∈Icc 1 ⌊x⌋₊,a n*(n:ℝ)⁻¹) = partialSum a x/x+∫ t in (1:ℝ)..x,partialSum a t/t^2 := by
    simpa only [partialSum,mul_neg,intervalIntegral.integral_neg,sub_neg_eq_add,div_eq_mul_inv] using hAb
  have hden : |partialSum a x/x| ≤ 4 := by
    rw [abs_div,abs_of_pos hxp,div_le_iff₀ hxp]
    exact (hA hx).trans (by gcongr; exact Real.sqrt_le_self_iff.mpr (.inr hx))
  have hdec : ContinuousOn (fun t : ℝ => 4*t^(-(3/2):ℝ)) (Set.Icc 1 x) := by
    apply continuousOn_of_forall_continuousAt; intro t ht
    exact continuousAt_const.mul (Real.continuousAt_rpow_const t _ (.inl (zero_lt_one.trans_le ht.1).ne'))
  have herr := intervalIntegral.norm_integral_le_of_norm_le («μ»:=volume) (f:=fun t : ℝ => partialSum a t/t^2) hx
    (Filter.Eventually.of_forall fun t ht => show ‖_‖≤4*t^(-(3/2):ℝ) by
      have ht' := zero_lt_one.trans ht.1
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (sq_pos_of_pos ht')]
      apply (div_le_div_of_nonneg_right (hA ht.1.le) (sq_nonneg _)).trans_eq
      rw [Real.sqrt_eq_rpow,div_eq_mul_inv,←Real.rpow_two,←Real.rpow_neg ht'.le,mul_assoc,←Real.rpow_add ht']
      norm_num) (hdec.intervalIntegrable_of_Icc hx)
  have hnot : (0:ℝ)∉Set.uIcc 1 x := by rw [Set.uIcc_of_le hx]; simp
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inr ⟨by norm_num,hnot⟩),Real.one_rpow,Real.norm_eq_abs] at herr
  norm_num at herr
  have hb : |∑ n∈Icc 1 ⌊x⌋₊,a n*(n:ℝ)⁻¹| ≤ 12 := by
    rw [he]; exact (abs_add_le _ _).trans (by nlinarith [Real.rpow_nonneg hxp.le (-(1/2):ℝ)])
  let H := ∑ n∈Icc 1 ⌊x⌋₊,(n:ℝ)⁻¹
  have h1 : log x≤H := log_le_sum_inv hxp.le
  have h2 : H≤1+log x := sum_inv_le_one_add_log hx
  have hsplit : harmonicMean squarefreeIndicator x-c*log x = (∑ n∈Icc 1 ⌊x⌋₊,a n*(n:ℝ)⁻¹)+c*(H-log x) := by
    simp only [harmonicMean,partialSum,a,sub_mul,sum_sub_distrib,H,←Finset.mul_sum,div_eq_mul_inv]; ring
  change |harmonicMean squarefreeIndicator x-c*log x|≤20+c
  rw [hsplit]; apply (abs_add_le _ _).trans; rw [abs_of_nonneg (mul_nonneg hc (sub_nonneg.mpr h1))]
  nlinarith only [hb,mul_le_mul_of_nonneg_left h2 hc]

/-- The harmonic second moment of the divisor function has a remainder
bounded by a constant times the third power of 1+log x. -/
theorem divisor_square_harmonic_error :
    ∃ B : ℝ, 0<B ∧ ∀ {x:ℝ}, 1≤x →
      |(∑ n∈Icc 1 ⌊x⌋₊,(n.divisors.card:ℝ)^2/n) - (1/(4*π^2))*(log x)^4| ≤ B*(1+log x)^3 := by
  let c : ℝ := 6/π^2
  have hc : 0≤c := by dsimp [c]; positivity
  have hnon (f : ArithmeticFunction ℝ) (h : ∀ n, 0≤f n) (n : ℕ) : 0≤divisorTransform f n := by
    rw [divisorTransform_apply]; exact sum_nonneg (fun i _ => h i)
  have hf (n : ℕ) : 0≤squarefreeIndicator n := by simp [sq_nonneg]
  have hs {x:ℝ} (hx : 1≤x) : |harmonicMean squarefreeIndicator x-c*(log x)^(0+1)|≤(20+c)*(1+log x)^0 := by
    simpa [c] using squarefree_harmonic_error hx
  let B₁ := c+2*(20+c)
  let B₂ := c/2+2*B₁
  let B₃ := c/6+2*B₂
  have h₁ {x : ℝ} (hx : 1≤x) : |harmonicMean (divisorTransform squarefreeIndicator) x-(c/2)*(log x)^2|≤B₁*(1+log x)^1 := by
    simpa [B₁] using harmonic_transform_log_asymptotic hf 0 hc (show 0≤20+c by linarith) @hs hx
  have h₂ {x : ℝ} (hx : 1≤x) : |harmonicMean (divisorTransform (divisorTransform squarefreeIndicator)) x-(c/6)*(log x)^3|≤B₂*(1+log x)^2 := by
    have h := harmonic_transform_log_asymptotic (hnon _ hf) 1 (c:=c/2) (B:=B₁) (by positivity) (by dsimp [B₁]; positivity) @h₁ hx
    norm_num at h
    simpa only [B₂,show c/2/3=c/6 by ring] using h
  refine ⟨B₃,by dsimp [B₃,B₂,B₁]; positivity,fun {x} hx => ?_⟩
  have h := harmonic_transform_log_asymptotic (hnon _ (hnon _ hf)) 2 (c:=c/6) (B:=B₂) (by positivity) (by dsimp [B₂,B₁]; positivity) @h₂ hx
  simp only [harmonicMean,partialSum,divisorTransform_three_squarefree] at h
  norm_num at h
  simpa only [B₃,c,show (6/π^2:ℝ)/6/4=1/(4*π^2) by ring] using h

/-- The normalized square-divisor diagonal tends to 1/(4π²). -/
theorem tendsto_divisor_square_harmonic :
    Tendsto (fun x : ℝ => (∑ n∈Icc 1 ⌊x⌋₊,(n.divisors.card:ℝ)^2/(n:ℝ))/(log x)^4)
      atTop (𝓝 (1/(4*π^2))) := by
  obtain ⟨B,hB,h⟩ := divisor_square_harmonic_error
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (16*B/ε)),eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hl : 1≤log x := (le_max_left ..).trans hx
  have hep := (div_le_iff₀ hε).mp ((le_max_right ..).trans hx)
  let S := ∑ n∈Icc 1 ⌊x⌋₊,(n.divisors.card:ℝ)^2/(n:ℝ)
  have hx' := h hx1
  change |S-_*_|≤_ at hx'
  change dist (S/(log x)^4) _ < ε
  rw [Real.dist_eq,div_sub' (pow_ne_zero 4 (by linarith : log x≠0)),mul_comm ((log x)^4) (1/(4*π^2)),abs_div,abs_of_pos (pow_pos (by linarith : 0<log x) 4),div_lt_iff₀ (by positivity)]
  have hpow := pow_le_pow_left₀ (show 0≤1+log x by linarith) (show 1+log x≤2*log x by linarith) 3
  nlinarith only [hx',mul_le_mul_of_nonneg_left hpow hB.le,mul_le_mul_of_nonneg_right hep (show 0≤(log x)^3 by positivity),mul_pos hB (show 0<(log x)^3 by positivity)]

/-- Asymptotic equivalence form of the harmonic second moment of the
divisor function. -/
theorem divisor_square_harmonic_equivalent :
    Asymptotics.IsEquivalent atTop
      (fun x : ℝ => ∑ n∈Icc 1 ⌊x⌋₊,(n.divisors.card:ℝ)^2/(n:ℝ))
      (fun x : ℝ => (log x)^4/(4*π^2)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := tendsto_divisor_square_harmonic.mul_const (4*π^2)
  rw [one_div_mul_cancel (show 4*π^2≠0 by positivity)] at h
  exact h.congr (fun x => by simp only [Pi.div_apply,div_eq_mul_inv,mul_inv_rev,inv_inv]; ring)

end AnalyticNumberTheory.DivisorProblems
