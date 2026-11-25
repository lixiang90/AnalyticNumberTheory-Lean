import AnalyticNumberTheory.RiemannZeta.CriticalCosineMeanComparison
import AnalyticNumberTheory.RiemannZeta.CriticalCosineOffDiagonal
import AnalyticNumberTheory.RiemannZeta.CriticalDiagonalIntegral

/-!
# The linear secondary term of the critical-line second moment

The moving harmonic diagonal contributes Euler's constant twice. The
cosine-product cancellation and the pointwise Riemann–Siegel expansion
give a power-saving remainder after the linear secondary term.
-/
noncomputable section
open Real Complex MeasureTheory Filter Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem sqrt_log_height {T : ℝ} (hT : 1≤T) :
    Real.sqrt (Real.log (T+2))≤2*T^(1/4:ℝ) := by
  have ht : 0<T := by linarith
  have hp : 0<T+2 := by linarith
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hs
  have hh := Real.sqrt_le_sqrt (show T+2≤4*T by linarith)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at hh
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity,?_⟩
  rw [mul_pow,←Real.rpow_natCast (T^(1/4:ℝ)) 2,←Real.rpow_mul ht.le,show (1/4:ℝ)*(2:ℕ)=1/2 by norm_num,←Real.sqrt_eq_rpow]
  linarith

/-- The two leading terms of the Riemann zeta second moment on the
critical line, with an explicit-order error O(T^(3/4) sqrt(log(T+2))). -/
theorem riemannZeta_critical_second_moment_expansion : ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},8*Real.pi≤T →
    |(∫t in (1:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^2)-
      (T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T)|≤
      C*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)) := by
  obtain ⟨A,hA,H⟩ := hardyZ_square_cosine_mean_error
  obtain ⟨B,hB,K⟩ := hardyCosine_off_diagonal_error
  obtain ⟨D,hD,J⟩ := critical_diagonal_integral_error
  let a := 8*Real.pi
  let m := ∫t in (1:ℝ)..a,hardyZ t^2
  have ha : 1≤a := by dsimp [a];linarith [Real.pi_gt_three]
  have hm : 0≤m := intervalIntegral.integral_nonneg ha (fun _ _ => sq_nonneg _)
  refine ⟨m+A+4*B+D,by positivity,?_⟩
  intro T ht
  have ht₁ : 1≤T := ha.trans ht
  have hp : 0<T := by linarith
  let s := Real.sqrt T
  let L := Real.sqrt (Real.log (T+2))
  let V := T^(3/4:ℝ)*L
  have hL₁ : 1≤Real.log (T+2) := by
    rw [←Real.log_exp 1];apply Real.log_le_log (Real.exp_pos _);linarith [Real.exp_one_lt_d9]
  have hL : 1≤L := Real.le_sqrt_of_sq_le (by simpa using hL₁)
  have hL' : L^2=Real.log (T+2) := Real.sq_sqrt (by linarith)
  have hV : 1≤V := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow ht₁ (by norm_num)) hL
  have hs : s≤V := by
    have hh := Real.rpow_le_rpow_of_exponent_le ht₁ (show (1/2:ℝ)≤3/4 by norm_num)
    rw [←Real.sqrt_eq_rpow] at hh
    exact hh.trans (le_mul_of_one_le_right (by positivity) hL)
  have hsum : s*(1+Real.log T)≤4*V := by
    have hh := Real.log_le_log hp (show T≤T+2 by linarith)
    have h₁ : 1+Real.log T≤2*L^2 := by linarith
    have h₂ := sqrt_log_height ht₁
    change L≤2*T^(1/4:ℝ) at h₂
    calc s*(1+Real.log T) ≤ s*(2*L^2) := mul_le_mul_of_nonneg_left h₁ (Real.sqrt_nonneg _)
         _ ≤ 4*(s*T^(1/4:ℝ))*L := by
           have H' := mul_le_mul_of_nonneg_left h₂ (show 0≤2*s*L by dsimp [s,L];positivity)
           linarith only [H']
         _ = _ := by
           dsimp only [s,V];rw [Real.sqrt_eq_rpow,←Real.rpow_add hp,show (1/2:ℝ)+1/4=3/4 by norm_num];ring
  let z := ∫t in a..T,hardyZ t^2
  let p := ∫t in a..T,hardyCosineMain t^2
  let d := ∫t in a..T,hardyCosineDiagonal t
  let M := T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T
  have H' : |z-p|≤A*V := by simpa only [V,mul_assoc] using H ht
  have K' : |p-d|≤B*(s*(1+Real.log T)) := by simpa only [s,mul_assoc] using K ht
  have J' : |d-M|≤D*s := J T ht
  have he : (∫t in (1:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^2)=m+z := by
    simp_rw [←hardyZ_sq_eq]
    exact (intervalIntegral.integral_add_adjacent_intervals ((continuous_hardyZ.pow 2).intervalIntegrable ..)
      ((continuous_hardyZ.pow 2).intervalIntegrable ..)).symm
  rw [he]
  change |m+z-M|≤(m+A+4*B+D)*T^(3/4:ℝ)*L
  rw [mul_assoc,show m+z-M=m+(z-M) by ring]
  have he' := abs_add_le m (z-M)
  rw [abs_of_nonneg hm] at he'
  change _≤(m+A+4*B+D)*V
  linarith only [he',abs_sub_le z p M,abs_sub_le p d M,H',K',J',
    mul_le_mul_of_nonneg_left hsum hB.le,mul_le_mul_of_nonneg_left hs hD.le,
    mul_le_mul_of_nonneg_left hV hm]

/-- Asymptotic-notation version of the two-term formula. -/
theorem riemannZeta_critical_second_moment_remainder :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^2)-
      (T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  obtain ⟨C,hC,H⟩ := riemannZeta_critical_second_moment_expansion
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (8*Real.pi)] with T ht
  have ht' : 0<T := (by positivity : 0<8*Real.pi).trans_le ht
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (by positivity : 0≤T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)))]
  exact (H ht).trans_eq (by ring)

end AnalyticNumberTheory.RiemannZeta
