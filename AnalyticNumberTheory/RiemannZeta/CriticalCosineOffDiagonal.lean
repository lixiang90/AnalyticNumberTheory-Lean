import AnalyticNumberTheory.RiemannZeta.CriticalCosineExpansion
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The integrated unequal-frequency terms on the critical line

There is one stationary endpoint on the sum-phase diagonal. Every
other pair is controlled by its logarithmic gap. Their total is
O(sqrt(T) (1+log T)).
-/
noncomputable section
open Real Finset MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- Absolute logarithmic-gap kernel at the critical-line coefficient weights. -/
def criticalCosineGap (m n : ℕ) :=
  if m=n then (0:ℝ) else 2*(m:ℝ)^(-(1/2:ℝ))*(n:ℝ)^(-(1/2:ℝ))/|Real.log n-Real.log m|

private theorem abs_integral_pair_bound {m n : ℕ} (hm : 0<m) (hn : 0<n) {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hmA : hardyCutoff m≤a) (hnA : hardyCutoff n≤a) :
    |∫t in a..b,hardyCosinePair m n t|≤(if m=n then 16*Real.sqrt b*(m:ℝ)⁻¹ else 0)+8*criticalCosineGap m n := by
  unfold hardyCosinePair
  by_cases he : m=n
  · subst n
    simp only [ite_true,add_zero,criticalCosineGap,mul_zero,add_zero]
    rw [intervalIntegral.integral_const_mul,abs_mul,abs_of_nonneg (by positivity : 0≤2/(Real.sqrt m*Real.sqrt m)),
      ←sq (Real.sqrt (m:ℝ)),Real.sq_sqrt (Nat.cast_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (abs_integral_hardyAngle_add_le_sqrt m m ha hab) (by positivity : 0≤2/(m:ℝ))).trans_eq (by ring)
  · simp only [he,ite_false,zero_add,criticalCosineGap]
    let f := fun t => Real.cos (hardyAngle m t+hardyAngle n t)
    let g := fun t => Real.cos (hardyAngle m t-hardyAngle n t)
    have hf : Continuous f := Real.continuous_cos.comp ((continuous_hardyAngle m).add (continuous_hardyAngle n))
    have hg : Continuous g := Real.continuous_cos.comp ((continuous_hardyAngle m).sub (continuous_hardyAngle n))
    let c := 2/(Real.sqrt m*Real.sqrt n)
    have hc : 0≤c := by dsimp [c];positivity
    change |∫ t in a..b,c*(f t+g t)|≤_
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f:=f) (g:=g)
      (hf.intervalIntegrable ..) (hg.intervalIntegrable ..),abs_mul,abs_of_nonneg hc]
    have h₁ := abs_integral_hardyAngle_add_of_ne hm hn he hmA hnA hab
    have h₂ := abs_integral_hardyAngle_sub_of_ne hm hn he hab
    change |∫t in a..b,f t|≤_ at h₁
    change |∫t in a..b,g t|≤_ at h₂
    apply (mul_le_mul_of_nonneg_left ((abs_add_le ..).trans (add_le_add h₁ h₂)) hc).trans_eq
    simp only [Real.rpow_neg (Nat.cast_nonneg _) _,←Real.sqrt_eq_rpow]
    dsimp [c];ring

/-- Absolute off-diagonal cost over a square of indices. -/
theorem sum_criticalCosineGap (N : ℕ) (hN : 1≤N) :
    (∑m∈Finset.Icc 1 N,∑n∈Finset.Icc 1 N,criticalCosineGap m n)≤
      (16/Real.log 2+8)*(N:ℝ)*(1+Real.log N) := by
  have H := offDiag_dirichlet_sum_bound_of_ge_half (σ:=1/2) le_rfl N hN
  have he : 1-2*(1/2:ℝ)=0 := by norm_num
  simp only [he,Real.rpow_zero,sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,Nat.add_sub_cancel] at H
  change (∑m∈Finset.Icc 1 N,∑n∈Finset.Icc 1 N,criticalCosineGap m n)≤_ at H
  have Hs := sum_Icc_inv_sqrt_le N
  simp only [Real.rpow_neg (Nat.cast_nonneg _) _,←Real.sqrt_eq_rpow] at H
  have Hs' := pow_le_pow_left₀ (sum_nonneg (fun i _ => inv_nonneg.mpr (Real.sqrt_nonneg ((i:ℕ):ℝ)))) Hs 2
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at Hs'
  have hlog := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
  have hk : 0≤16/Real.log 2 := by positivity
  have hh := mul_nonneg (mul_nonneg hk (Nat.cast_nonneg N)) hlog
  apply H.trans
  apply (add_le_add (mul_le_mul_of_nonneg_left Hs' (by positivity : 0≤4/Real.log 2)) le_rfl).trans
  rw [show (16/Real.log 2+8)*(N:ℝ)*(1+Real.log N)=4/Real.log 2*(2^2*(N:ℝ))+8*(1+Real.log N)*N+16/Real.log 2*N*Real.log N by ring]
  exact le_add_of_nonneg_right hh

/-- The integrated cosine square differs from its moving harmonic
diagonal by at most O(sqrt(T) (1+log T)). -/
theorem hardyCosine_off_diagonal_error : ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},8*Real.pi≤T →
    |(∫t in (8*Real.pi)..T,hardyCosineMain t^2)-(∫t in (8*Real.pi)..T,hardyCosineDiagonal t)|≤
      C*Real.sqrt T*(1+Real.log T) := by
  let D := 16/Real.log 2+8
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨16+8*D,by positivity,?_⟩
  intro T ht
  let a := 8*Real.pi
  let N := hardyCutoffIndex T
  let S := Finset.Icc 1 N
  let P := fun m n => fromHeight (max (hardyCutoff m) (hardyCutoff n)) (hardyCosinePair m n)
  have ha : 0<a := by dsimp [a];positivity
  have ht' : 1≤T := by linarith [Real.pi_gt_three]
  have hN : 1≤N := (le_hardyCutoffIndex_iff (by linarith : 0≤T)).mpr (by dsimp [hardyCutoff];norm_num;linarith)
  have hNT : (N:ℝ)≤Real.sqrt T := (Nat.floor_le (Real.sqrt_nonneg _)).trans
    (Real.sqrt_le_sqrt (div_le_self (by linarith) (by linarith [Real.pi_gt_three])))
  have hNL : Real.log N≤Real.log T := Real.log_le_log (Nat.cast_pos.mpr hN) (hNT.trans (by nlinarith [Real.sq_sqrt (show 0≤T by linarith),Real.sqrt_nonneg T,sq_nonneg (Real.sqrt T-1)]))
  have hi (m n : ℕ) : IntervalIntegrable (P m n) volume a T :=
    fromHeight_intervalIntegrable _ (continuous_hardyCosinePair m n) _ _
  have hi' (m : ℕ) : IntervalIntegrable (fun t => ∑n∈S,P m n t) volume a T := by
    apply intervalIntegrable_iff.mpr
    exact integrable_finsetSum S (fun n _ => (hi m n).def')
  have hsum : (∫t in a..T,hardyCosineMain t^2)-(∫t in a..T,hardyCosineDiagonal t)=
      ∑m∈S,∑n∈S,∫t in a..T,P m n t := by
    rw [←intervalIntegral.integral_sub (hardyCosineMain_sq_intervalIntegrable ha.le ht)
      (hardyCosineDiagonal_monotone.intervalIntegrable ..)]
    rw [intervalIntegral.integral_congr (g:=fun t => ∑m∈S,∑n∈S,P m n t) (fun t ht' => by
      rw [uIcc_of_le (show a≤T from ht)] at ht';exact hardyCosine_square_sub_diagonal (ha.le.trans ht'.1) ht'.2)]
    rw [intervalIntegral.integral_finsetSum (f:=fun m t => ∑n∈S,P m n t) (fun m _ => hi' m)]
    apply sum_congr rfl;intro m _
    exact intervalIntegral.integral_finsetSum (fun n _ => hi m n)
  have hpair (m : ℕ) (hm : m∈S) (n : ℕ) (hn : n∈S) :
      |∫t in a..T,P m n t|≤(if m=n then 16*Real.sqrt T*(m:ℝ)⁻¹ else 0)+8*criticalCosineGap m n := by
    have hm' := (le_hardyCutoffIndex_iff (by linarith : 0≤T)).mp (Finset.mem_Icc.mp hm).2
    have hn' := (le_hardyCutoffIndex_iff (by linarith : 0≤T)).mp (Finset.mem_Icc.mp hn).2
    dsimp only [P];rw [integral_fromHeight ht (max_le hm' hn')]
    exact abs_integral_pair_bound (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 (ha.trans_le (le_max_left ..))
      (max_le ht (max_le hm' hn')) ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))
  have H := calc |∑m∈S,∑n∈S,∫t in a..T,P m n t| ≤ ∑m∈S, |∑n∈S,∫t in a..T,P m n t| := abs_sum_le_sum_abs ..
                 _ ≤ ∑m∈S,∑n∈S,((if m=n then 16*Real.sqrt T*(m:ℝ)⁻¹ else 0)+8*criticalCosineGap m n) :=
                   sum_le_sum (fun m hm => (abs_sum_le_sum_abs ..).trans (sum_le_sum (hpair m hm)))
  simp only [sum_add_distrib,sum_ite_eq,←mul_sum] at H
  have hatt : (∑m∈S,if m∈S then 16*Real.sqrt T*(m:ℝ)⁻¹ else 0)=16*Real.sqrt T*∑m∈S,(m:ℝ)⁻¹ := by
    rw [mul_sum];exact sum_congr rfl (fun i hi => if_pos hi)
  rw [hatt] at H
  have hh : (∑m∈S,(m:ℝ)⁻¹)≤1+Real.log N := by
    simpa only [S,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log N
  have hlog : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
  change |(∫t in a..T,hardyCosineMain t^2)-(∫t in a..T,hardyCosineDiagonal t)|≤_
  rw [hsum]
  apply H.trans
  have H₁ := mul_le_mul_of_nonneg_left (hh.trans (by linarith : 1+Real.log N≤1+Real.log T)) (by positivity : 0≤16*Real.sqrt T)
  have H₂ := mul_le_mul_of_nonneg_left (sum_criticalCosineGap N hN) (by norm_num : (0:ℝ)≤8)
  have H₃ := mul_le_mul_of_nonneg_left (mul_le_mul hNT (by linarith : 1+Real.log N≤1+Real.log T) hlog (Real.sqrt_nonneg T)) (show 0≤8*D by positivity)
  dsimp only [D] at *
  linarith only [H₁,H₂,H₃]

end AnalyticNumberTheory.RiemannZeta
