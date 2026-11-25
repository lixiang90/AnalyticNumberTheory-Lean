import AnalyticNumberTheory.DirichletLFunctions.PrimitiveMomentComparison

/-!
# Two terms of the critical-line mean square of a primitive character

For a single primitive character the leading coefficient is φ(q)/q.
The secondary coefficient is expressed by a finite real digamma sum
over the reduced residue classes and the logarithm of the conductor.
-/
noncomputable section
open Real Complex MeasureTheory Filter Set Asymptotics
open scoped Topology Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- A power-saving two-term expansion for the second moment of each fixed
primitive Dirichlet L-function, including nonreal characters. -/
theorem primitive_critical_second_moment_expansion {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)-
      ((q.totient/q:ℝ)*(T*Real.log (T/(2*Real.pi)))+primitiveMomentLinearTerm q*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  obtain ⟨A,hA,HA⟩ := primitive_moment_diagonal_comparison hχ
  obtain ⟨B,hB,HB⟩ := primitive_critical_diagonal_expansion χ
  let b := 8*Real.pi*q
  let z := fun t : ℝ => ‖χ.LFunction ((1/2:ℂ)+t*I)‖^2
  let m := ∫t in (1:ℝ)..b,z t
  have hq : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hb : 8*Real.pi≤b := le_mul_of_one_le_right (by positivity) hq
  have hb₁ : 1≤b := by linarith [Real.pi_gt_three]
  have hm : 0≤m := intervalIntegral.integral_nonneg hb₁ (fun t _ => sq_nonneg _)
  have hz : Continuous z := (continuous_character_critical_line χ).norm.pow 2
  apply IsBigO.of_bound (m+A+B)
  filter_upwards [HA,eventually_ge_atTop b] with T hcomp ht
  let Z := ∫t in b..T,z t
  let D := ∫t in b..T,primitiveCriticalDiagonal χ t
  let M := (q.totient/q:ℝ)*(T*Real.log (T/(2*Real.pi)))+primitiveMomentLinearTerm q*T
  let V := T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))
  have hT := hb₁.trans ht
  have hL : 1≤Real.sqrt (Real.log (T+2)) := Real.le_sqrt_of_sq_le (by
    rw [one_pow,←Real.log_exp 1];apply Real.log_le_log (Real.exp_pos _);linarith [Real.exp_one_lt_d9,Real.pi_gt_three])
  have hV : 1≤V := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT (by norm_num)) hL
  have hs : Real.sqrt T≤V := by
    rw [Real.sqrt_eq_rpow];exact (Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1/2:ℝ)≤3/4)).trans (le_mul_of_one_le_right (by positivity) hL)
  have H : |Z-D|≤A*V := by simpa only [Z,D,b,z,V,mul_assoc] using hcomp
  have J : |D-M|≤B*V := (HB ht).trans (mul_le_mul_of_nonneg_left hs hB.le)
  have he : (∫t in (1:ℝ)..T,z t)=m+Z :=
    (intervalIntegral.integral_add_adjacent_intervals (hz.intervalIntegrable ..) (hz.intervalIntegrable ..)).symm
  change ‖(∫t in (1:ℝ)..T,z t)-M‖≤(m+A+B)*‖V‖
  rw [he,Real.norm_eq_abs,Real.norm_of_nonneg (zero_le_one.trans hV),show m+Z-M=m+(Z-M) by ring]
  have hadd := abs_add_le m (Z-M);rw [abs_of_nonneg hm] at hadd
  linarith only [hadd,abs_sub_le Z D M,H,J,mul_le_mul_of_nonneg_left hV hm]

end AnalyticNumberTheory.DirichletLFunctions
