import AnalyticNumberTheory.RiemannZeta.WeightedHardyWaves

/-!
# A mean-square estimate for weighted moving Hardy polynomials

The term from possible stationary points has size sqrt(T) log N. All
other pairs have total cost N log N independently of the common scale.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

def weightedHardyPolynomial (d : ℝ) (w : Bool×ℕ→ℂ) (N : ℕ) (t : ℝ) :=
  ∑i∈scaledWaveIndex N,enteredWave (scaledHardyEntry d i.2) (weightedHardyWave d w i) t

def weightedHardyDiagonal (d : ℝ) (w : Bool×ℕ→ℂ) (N : ℕ) (t : ℝ) :=
  ∑i∈scaledWaveIndex N,‖enteredWave (scaledHardyEntry d i.2) (weightedHardyWave d w i) t‖^2

private theorem sum_indices (N : ℕ) (f : ℕ→ℝ) :
    (∑i∈scaledWaveIndex N,f i.2)=2*∑m∈Finset.Icc 1 N,f m := by
  rw [scaledWaveIndex,sum_product (f:=fun i : Bool×ℕ => f i.2),Fintype.sum_bool];ring

/-- Mean square of a general two-sided polynomial on the scaled grid
n/d, with independent bounded coefficients and sharp moving cutoffs. -/
theorem weighted_hardy_energy_bound {d : ℝ} (hd : 0<d) (w : Bool×ℕ→ℂ) (hw : ∀i,‖w i‖≤1)
    {a T : ℝ} (ha : 0<a) (hT : a≤T) (N : ℕ) (hN : 1≤N) :
    |∫t in a..T,‖weightedHardyPolynomial d w N t‖^2-weightedHardyDiagonal d w N t|≤
      32*Real.sqrt T*(1+Real.log N)+8*((16/Real.log 2+8)*N*(1+Real.log N)) := by
  let F := fun m n : ℕ => (if m=n then 8*Real.sqrt T*(m:ℝ)⁻¹ else 0)+2*criticalCosineGap m n
  have hF (m n : ℕ) : 0≤F m n := by dsimp [F,criticalCosineGap];split_ifs <;>positivity
  have H := moving_polynomial_energy_bound (scaledWaveIndex N) (fun i => scaledHardyEntry d i.2)
    (weightedHardyWave d w) (continuous_weightedHardyWave d w) hT
  apply H.trans
  apply le_trans (b:=∑i∈scaledWaveIndex N,∑j∈scaledWaveIndex N,F i.2 j.2)
  · apply sum_le_sum;intro i hi;apply sum_le_sum;intro j hj
    by_cases hij : i=j
    · simpa only [if_pos hij] using hF i.2 j.2
    · rw [if_neg hij]
      let c := max a (max (scaledHardyEntry d i.2) (scaledHardyEntry d j.2))
      by_cases hc : c≤T
      · change ‖∫t in min T c..T,_‖≤_;rw [min_eq_right hc]
        apply weighted_hardy_pair_bound hd w hw i j (Finset.mem_Icc.mp (Finset.mem_product.mp hi).2).1
          (Finset.mem_Icc.mp (Finset.mem_product.mp hj).2).1 hij (ha.trans_le (le_max_left ..)) hc
          ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))
      · change ‖∫t in min T c..T,_‖≤_;rw [min_eq_left (le_of_not_ge hc),intervalIntegral.integral_same,norm_zero]
        exact hF _ _
  · have e (i : Bool×ℕ) := sum_indices N (F i.2)
    simp_rw [e];rw [sum_indices N (fun m => 2*∑n∈Finset.Icc 1 N,F m n)]
    simp only [F,sum_add_distrib,sum_ite_eq,←mul_sum]
    have hdiag : (∑m∈Finset.Icc 1 N,if m∈Finset.Icc 1 N then 8*Real.sqrt T*(m:ℝ)⁻¹ else 0)=
        8*Real.sqrt T*∑m∈Finset.Icc 1 N,(m:ℝ)⁻¹ := by
      rw [mul_sum];apply sum_congr rfl;intro m hm;rw [if_pos hm]
    rw [hdiag]
    have hH : (∑m∈Finset.Icc 1 N,(m:ℝ)⁻¹)≤1+Real.log N := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log N
    linarith only [mul_le_mul_of_nonneg_left hH (show 0≤32*Real.sqrt T by positivity),sum_criticalCosineGap N hN]

theorem weightedHardyPolynomial_sq_intervalIntegrable (d : ℝ) (w : Bool×ℕ→ℂ) (N : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => ‖weightedHardyPolynomial d w N t‖^2) volume u v := by
  let D := ∑i∈scaledWaveIndex N,‖w i‖*(Real.sqrt i.2)⁻¹
  have hm : Measurable (weightedHardyPolynomial d w N) := by
    unfold weightedHardyPolynomial;apply Finset.measurable_fun_sum
    intro i _;exact (continuous_weightedHardyWave d w i).measurable.indicator measurableSet_Ici
  have hb (t : ℝ) : ‖weightedHardyPolynomial d w N t‖≤D := by
    apply (norm_sum_le ..).trans;apply sum_le_sum
    intro i _;change ‖if scaledHardyEntry d i.2≤t then _ else 0‖≤_
    split_ifs
    · exact (norm_weightedHardyWave ..).le
    · rw [norm_zero];positivity
  apply intervalIntegrable_iff.mpr
  have hI : IntervalIntegrable (fun _ : ℝ => D^2) volume u v := continuous_const.intervalIntegrable ..
  apply hI.def'.mono' (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with t;rw [Real.norm_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2

end AnalyticNumberTheory.RiemannZeta
