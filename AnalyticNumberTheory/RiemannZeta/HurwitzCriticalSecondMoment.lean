import AnalyticNumberTheory.RiemannZeta.HurwitzWaveComparison
import AnalyticNumberTheory.RiemannZeta.HurwitzWaveEnergy

/-!
# The first two terms of the Hurwitz critical-line second moment

For each fixed real shift a in (0,1], the linear coefficient is
γ−ψ(a)−1 after the leading term T log(T/(2π)). A power-saving error
follows from the two shifted Hardy polynomials and their frequency gaps.
-/
noncomputable section
open Real Complex MeasureTheory Filter Set Asymptotics
open scoped Topology Interval
open AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.RiemannZeta

/-- The critical-line second moment of Hurwitz zeta, including its
shift-dependent linear term and an O_a(T^(3/4) sqrt(log(T+2))) remainder. -/
theorem hurwitz_critical_second_moment_expansion {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2)-
      (T*Real.log (T/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  obtain ⟨A,hA,HA⟩ := hurwitz_wave_mean_comparison ha
  obtain ⟨B,hB,HB⟩ := hurwitz_wave_energy_error ha
  obtain ⟨C,hC,HC⟩ := hurwitz_critical_diagonal_expansion ha
  let b := 8*Real.pi
  let z := fun t : ℝ => ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2
  let m := ∫t in (1:ℝ)..b,z t
  have hb : 1≤b := by dsimp [b];linarith [Real.pi_gt_three]
  have hm : 0≤m := intervalIntegral.integral_nonneg hb (fun t _ => sq_nonneg _)
  have hz : Continuous z := (continuous_hurwitz_critical_line a).norm.pow 2
  apply IsBigO.of_bound (m+A+5*B+C)
  filter_upwards [HA,eventually_ge_atTop b] with T hcmp ht
  let N := ⌊Real.sqrt (T/(2*Real.pi))⌋₊+1
  let Z := ∫t in b..T,z t
  let P := ∫t in b..T,‖hurwitzWaveSum a N t‖^2
  let D := ∫t in b..T,hurwitzCriticalDiagonal a t
  let M := T*Real.log (T/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T
  let L := Real.sqrt (Real.log (T+2))
  let V := T^(3/4:ℝ)*L
  have hT : 1≤T := hb.trans ht
  have hp : 0<T := zero_lt_one.trans_le hT
  have hL : 1≤L := Real.le_sqrt_of_sq_le (by
    rw [one_pow,←Real.log_exp 1];apply Real.log_le_log (Real.exp_pos _);dsimp only [b] at ht;linarith [Real.pi_gt_three,Real.exp_one_lt_d9])
  have h₁ : 1≤V := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT (by norm_num)) hL
  have hs : Real.sqrt T≤V := by
    rw [Real.sqrt_eq_rpow];exact (Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1/2:ℝ)≤3/4)).trans (le_mul_of_one_le_right (by positivity) hL)
  have herr : Real.sqrt T*(1+Real.log T)≤5*V := by
    have hq := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp (1/4:ℝ))
    rw [Real.log_rpow hp] at hq
    have he : Real.sqrt T*T^(1/4:ℝ)=T^(3/4:ℝ) := by rw [Real.sqrt_eq_rpow,←Real.rpow_add hp];norm_num
    have h₀ := mul_le_mul_of_nonneg_left (show 1+Real.log T≤5*T^(1/4:ℝ) by linarith [Real.one_le_rpow hT (by norm_num : 0≤(1/4:ℝ))]) (Real.sqrt_nonneg T)
    have hq' : T^(3/4:ℝ)≤V := le_mul_of_one_le_right (by positivity) hL
    linarith only [h₀,he,hq']
  have h₁' : |Z-P|≤A*V := by simpa only [Z,P,z,N,b,V,L,mul_assoc] using hcmp
  have h₂ : |∫t in b..T,‖hurwitzWaveSum a N t‖^2-hurwitzCriticalDiagonal a t|≤B*Real.sqrt T*(1+Real.log T) := HB ht
  rw [intervalIntegral.integral_sub (f:=fun t => ‖hurwitzWaveSum a N t‖^2) (g:=hurwitzCriticalDiagonal a)
    (hurwitzWaveSum_sq_intervalIntegrable a N b T) ((hurwitzCriticalDiagonal_monotone ha.1).intervalIntegrable)] at h₂
  have h₂' : |P-D|≤5*B*V := by
    have H : |P-D|≤B*(Real.sqrt T*(1+Real.log T)) := by simpa only [P,D,N,b,mul_assoc] using h₂
    linarith only [H,mul_le_mul_of_nonneg_left herr hB.le]
  have h₃ : |D-M|≤C*V := (HC ht).trans (mul_le_mul_of_nonneg_left hs hC.le)
  have he : (∫t in (1:ℝ)..T,z t)=m+Z :=
    (intervalIntegral.integral_add_adjacent_intervals (hz.intervalIntegrable ..) (hz.intervalIntegrable ..)).symm
  change ‖(∫t in (1:ℝ)..T,z t)-M‖≤(m+A+5*B+C)*‖V‖
  rw [he,Real.norm_eq_abs,Real.norm_of_nonneg (zero_le_one.trans h₁),show m+Z-M=m+(Z-M) by ring]
  have hadd := abs_add_le m (Z-M);rw [abs_of_nonneg hm] at hadd
  linarith only [hadd,abs_sub_le Z P M,abs_sub_le P D M,h₁',h₂',h₃,mul_le_mul_of_nonneg_left h₁ hm]

end AnalyticNumberTheory.RiemannZeta
