import AnalyticNumberTheory.RiemannZeta.CriticalCorrectedBlock
import AnalyticNumberTheory.RiemannZeta.CriticalDiagonalIntegral

/-!
# The square-root error in the critical-line second moment

The first Riemann–Siegel correction has an oscillatory cross term on
each block. Summing the logarithmic spacings over all modes gives the
classical O(sqrt(T) log T) remainder in the two-term formula.
-/
noncomputable section
open Real Complex Finset Set Filter MeasureTheory Asymptotics
open scoped Topology Interval
namespace AnalyticNumberTheory.RiemannZeta

private theorem hardyCutoff_mono : Monotone hardyCutoff := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hij) 2) (by positivity)

private theorem sum_block_cost {N : ℕ} (hN : 1≤N) :
    (∑j∈Finset.Icc 2 N,(1+∑n∈Finset.Icc 1 j,criticalCosineGap j n))≤
      (1+(16/Real.log 2+8))*(N:ℝ)*(1+Real.log N) := by
  let S := Finset.Icc 1 N
  have H (j n : ℕ) : 0≤criticalCosineGap j n := by dsimp [criticalCosineGap];split_ifs <;> positivity
  have H₁ : ∑j∈Finset.Icc 2 N,(1:ℝ)≤N := by
    simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc]
    exact_mod_cast (by omega : N+1-2≤N)
  have H₂ : (∑j∈Finset.Icc 2 N,∑n∈Finset.Icc 1 j,criticalCosineGap j n)≤∑j∈S,∑n∈S,criticalCosineGap j n := by
    apply le_trans (sum_le_sum (g:=fun j => ∑n∈S,criticalCosineGap j n) _)
    · exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl) (fun i _ _ => sum_nonneg (fun j _ => H i j))
    · intro j hj;exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Finset.mem_Icc.mp hj).2) (fun i _ _ => H j i)
  rw [sum_add_distrib]
  have H₃ := H₂.trans (sum_criticalCosineGap N hN)
  have hlog := mul_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) (Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN))
  linarith only [H₁,H₃,hlog]

set_option maxHeartbeats 700000 in
/-- The integrated error incurred by squaring the elementary cosine
polynomial, after using the oscillation of its first correction. -/
theorem hardyZ_square_cosine_mean_sharp : ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi≤T →
    |(∫t in (8*Real.pi)..T,hardyZ t^2)-(∫t in (8*Real.pi)..T,hardyCosineMain t^2)|≤
      C*Real.sqrt T*(1+Real.log T) := by
  obtain ⟨C,hC,H⟩ := critical_corrected_block_mean
  let D := 1+(16/Real.log 2+8)
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨C*D,by positivity,?_⟩
  intro T ht
  let N := hardyCutoffIndex T
  let a := hardyCutoff 2
  let f := fun t=>hardyZ t^2-hardyCosineMain t^2
  have ha : a=8*Real.pi := by dsimp [a,hardyCutoff];norm_num;ring
  have haT : a≤T := ha ▸ ht
  have ht' : 1≤T := by linarith [Real.pi_gt_three]
  have hp : 0<T := by linarith
  have hN : 2≤N := (le_hardyCutoffIndex_iff hp.le).mpr haT
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hNt : hardyCutoff N≤T := (le_hardyCutoffIndex_iff hp.le).mp le_rfl
  have htN : T≤hardyCutoff (N+1) := le_of_lt (not_le.mp fun h => by
    have h' := (le_hardyCutoffIndex_iff hp.le).mpr h;change N+1≤N at h';omega)
  have hL : (N:ℝ)≤Real.sqrt T := (Nat.floor_le (Real.sqrt_nonneg _)).trans
    (Real.sqrt_le_sqrt (div_le_self hp.le (by linarith [Real.pi_gt_three])))
  have hlog : Real.log N≤Real.log T := Real.log_le_log (by linarith) (hL.trans
    (by nlinarith [Real.sq_sqrt hp.le,Real.sqrt_nonneg T,sq_nonneg (Real.sqrt T-1)]))
  have hi {a b : ℝ} (ha : 0≤a) (hab : a≤b) : IntervalIntegrable f volume a b :=
    ((continuous_hardyZ.pow 2).intervalIntegrable ..).sub (hardyCosineMain_sq_intervalIntegrable ha hab)
  let J := fun j : ℕ => ∫t in (hardyCutoff j)..(min (hardyCutoff (j+1)) T), f t
  have he : (∫t in a..T,f t)=∑j∈Finset.Icc 2 N,J j := by
    rw [←Finset.Ico_add_one_right_eq_Icc,sum_Ico_succ_top hN]
    have hcalc : (∑j∈Finset.Ico 2 N,J j)=∫t in a..(hardyCutoff N),f t := by
      apply (sum_congr rfl (g:=fun j => ∫t in (hardyCutoff j)..(hardyCutoff (j+1)),f t) (fun j hj => ?_)).trans
      · exact intervalIntegral.sum_integral_adjacent_intervals_Ico hN (fun j hj => hi
          (hardyCutoff_pos (by have := hj.1;omega)).le (hardyCutoff_mono (Nat.le_succ _)))
      · dsimp [J];rw [min_eq_left ((hardyCutoff_mono (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2)).trans hNt)]
    rw [hcalc,show J N=(∫t in (hardyCutoff N)..T,f t) by dsimp [J];rw [min_eq_right htN] ]
    exact (intervalIntegral.integral_add_adjacent_intervals (hi (hardyCutoff_pos (by decide : 0<2)).le (hardyCutoff_mono hN))
      (hi (hardyCutoff_pos (by omega : 0<N)).le hNt)).symm
  have hterm (j : ℕ) (hj : j∈Finset.Icc 2 N) : |J j|≤C*(1+∑n∈Finset.Icc 1 j,criticalCosineGap j n) := by
    exact H (Finset.mem_Icc.mp hj).1 ⟨le_min (hardyCutoff_mono (Nat.le_succ _)) ((hardyCutoff_mono (Finset.mem_Icc.mp hj).2).trans hNt),min_le_left ..⟩
  have hsum := (abs_sum_le_sum_abs J (Finset.Icc 2 N)).trans (sum_le_sum hterm)
  rw [←mul_sum] at hsum
  change |(∫t in (8*Real.pi)..T,hardyZ t^2)-(∫t in (8*Real.pi)..T,hardyCosineMain t^2)|≤_
  rw [←ha,←intervalIntegral.integral_sub (f:=fun t=>hardyZ t^2) (g:=fun t=>hardyCosineMain t^2)
    ((continuous_hardyZ.pow 2).intervalIntegrable ..) (hardyCosineMain_sq_intervalIntegrable (hardyCutoff_pos (by decide : 0<2)).le haT)]
  change |∫t in a..T,f t|≤_
  rw [he]
  apply (hsum.trans (mul_le_mul_of_nonneg_left (sum_block_cost (by omega : 1≤N)) hC.le)).trans
  have hh := mul_le_mul hL (by linarith : 1+Real.log N≤1+Real.log T) (by linarith [Real.log_nonneg (by linarith : (1:ℝ)≤N)]) (Real.sqrt_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hh (show 0≤C*D by positivity)
  dsimp [D] at *;linarith only [hm]

/-- The classical two-term formula with a square-root times logarithm
error, uniform for every height at least 8π. -/
theorem riemannZeta_critical_second_moment_sharp : ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi≤T →
    |(∫t in (1:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^2)-
      (T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T)|≤
      C*Real.sqrt T*(1+Real.log T) := by
  obtain ⟨A,hA,H⟩ := hardyZ_square_cosine_mean_sharp
  obtain ⟨B,hB,K⟩ := hardyCosine_off_diagonal_error
  obtain ⟨D,hD,J⟩ := critical_diagonal_integral_error
  let a := 8*Real.pi
  let m := ∫t in (1:ℝ)..a,hardyZ t^2
  have ha : 1≤a := by dsimp [a];linarith [Real.pi_gt_three]
  have hm : 0≤m := intervalIntegral.integral_nonneg ha (fun _ _ => sq_nonneg _)
  refine ⟨m+A+B+D,by positivity,?_⟩
  intro T ht
  have ht₁ : 1≤T := ha.trans ht
  let V := Real.sqrt T*(1+Real.log T)
  have hL : 1≤1+Real.log T := by linarith [Real.log_nonneg ht₁]
  have hs : 1≤Real.sqrt T := Real.le_sqrt_of_sq_le (by simpa using ht₁)
  have hV : 1≤V := one_le_mul_of_one_le_of_one_le hs hL
  have hV' : Real.sqrt T≤V := le_mul_of_one_le_right (Real.sqrt_nonneg _) hL
  let z := ∫t in a..T,hardyZ t^2
  let p := ∫t in a..T,hardyCosineMain t^2
  let d := ∫t in a..T,hardyCosineDiagonal t
  let M := T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T
  have H' : |z-p|≤A*V := by simpa only [V,mul_assoc] using H ht
  have K' : |p-d|≤B*V := by simpa only [V,mul_assoc] using K ht
  have J' : |d-M|≤D*Real.sqrt T := J T ht
  have he : (∫t in (1:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^2)=m+z := by
    simp_rw [←hardyZ_sq_eq]
    exact (intervalIntegral.integral_add_adjacent_intervals ((continuous_hardyZ.pow 2).intervalIntegrable ..)
      ((continuous_hardyZ.pow 2).intervalIntegrable ..)).symm
  rw [he,mul_assoc]
  change |m+z-M|≤(m+A+B+D)*V
  rw [show m+z-M=m+(z-M) by ring]
  have he' := abs_add_le m (z-M)
  rw [abs_of_nonneg hm] at he'
  linarith only [he',abs_sub_le z p M,abs_sub_le p d M,H',K',J',mul_le_mul_of_nonneg_left hV' hD.le,
    mul_le_mul_of_nonneg_left hV hm]

/-- The square-root logarithmic remainder in asymptotic notation. -/
theorem riemannZeta_critical_second_moment_sharp_remainder :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^2)-
      (T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T)) =O[atTop]
      (fun T : ℝ => Real.sqrt T*Real.log T) := by
  obtain ⟨C,hC,H⟩ := riemannZeta_critical_second_moment_sharp
  apply IsBigO.of_bound (2*C)
  filter_upwards [eventually_ge_atTop (8*Real.pi),eventually_ge_atTop (Real.exp 1)] with T ht he
  have hp : 0<T := (Real.exp_pos _).trans_le he
  have hL : 1≤Real.log T := by rw [←Real.log_exp 1];exact Real.log_le_log (Real.exp_pos _) he
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]
  linarith only [H ht,mul_le_mul_of_nonneg_left hL (show 0≤C*Real.sqrt T by positivity)]

end AnalyticNumberTheory.RiemannZeta
