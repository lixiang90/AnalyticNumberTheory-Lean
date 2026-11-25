import AnalyticNumberTheory.DirichletLFunctions.PeriodicMomentComparison

/-!
# The two-term critical-line mean square of a periodic L-function

The secondary term is the sum of two digamma-weighted period means,
one for the original coefficients and one for their normalized finite
Fourier transform, together with the conductor and integration terms.
-/
noncomputable section
open Real Complex Finset MeasureTheory Filter Set Asymptotics
open scoped Topology Interval
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem bounded_periodic_moment {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ)
    (hΦ : ∀r,‖Φ r‖≤1) (hΨ : ∀r,‖periodicDualWeight Φ r‖≤1) :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖^2)-
      (periodicNormMean Φ*(T*Real.log (T/(2*Real.pi)))+periodicMomentLinearTerm Φ*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  obtain ⟨A,hA,HA⟩ := periodic_moment_diagonal_comparison Φ hΦ hΨ
  obtain ⟨B,hB,HB⟩ := periodic_critical_diagonal_expansion Φ
  let b := 8*Real.pi*q
  let z := fun t : ℝ => ‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖^2
  let m := ∫t in (1:ℝ)..b,z t
  have hq : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hb : 8*Real.pi≤b := le_mul_of_one_le_right (by positivity) hq
  have hb₁ : 1≤b := by linarith [Real.pi_gt_three]
  have hm : 0≤m := intervalIntegral.integral_nonneg hb₁ (fun t _ => sq_nonneg _)
  have hz : Continuous z := (continuous_periodic_critical_line Φ).norm.pow 2
  apply IsBigO.of_bound (m+A+B)
  filter_upwards [HA,eventually_ge_atTop b] with T hcomp ht
  let Z := ∫t in b..T,z t
  let D := ∫t in b..T,periodicCriticalDiagonal Φ t
  let M := periodicNormMean Φ*(T*Real.log (T/(2*Real.pi)))+periodicMomentLinearTerm Φ*T
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

private theorem dual_weight_scale {q : ℕ} [NeZero q] (c : ℂ) (Φ : ZMod q→ℂ) (r : ZMod q) :
    periodicDualWeight (fun n=>c*Φ n) r=c*periodicDualWeight Φ r := by
  rw [periodicDualWeight,periodicDualWeight,ZMod.dft_apply,ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [show (∑j : ZMod q,ZMod.stdAddChar (-(j*r))*(c*Φ j))=c*∑j : ZMod q,ZMod.stdAddChar (-(j*r))*Φ j by
    rw [mul_sum];apply sum_congr rfl;intro j _;ring]
  ring

private theorem period_mean_scale {q : ℕ} [NeZero q] (c : ℂ) (Φ : ZMod q→ℂ) :
    periodicNormMean (fun r=>c*Φ r)=‖c‖^2*periodicNormMean Φ := by
  simp only [periodicNormMean,norm_mul,mul_pow,←mul_sum];ring

private theorem harmonic_constant_scale {q : ℕ} [NeZero q] (c : ℂ) (Φ : ZMod q→ℂ) :
    periodicHarmonicConstant (fun r=>c*Φ r)=‖c‖^2*periodicHarmonicConstant Φ := by
  simp only [periodicHarmonicConstant,norm_mul,mul_pow,mul_assoc,←mul_sum];ring

private theorem linear_term_scale {q : ℕ} [NeZero q] (c : ℂ) (Φ : ZMod q→ℂ) :
    periodicMomentLinearTerm (fun r=>c*Φ r)=‖c‖^2*periodicMomentLinearTerm Φ := by
  have hh : periodicDualWeight (fun r=>c*Φ r)=fun r=>c*periodicDualWeight Φ r := funext (dual_weight_scale c Φ)
  rw [periodicMomentLinearTerm,periodicMomentLinearTerm,hh,harmonic_constant_scale,harmonic_constant_scale,period_mean_scale]
  ring

/-- Two terms and a power-saving remainder in the critical-line second moment
of an arbitrary fixed periodic L-function. Both coefficients are explicit
finite expressions in the original coefficient sequence. -/
theorem periodic_critical_second_moment {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖^2)-
      (periodicNormMean Φ*(T*Real.log (T/(2*Real.pi)))+periodicMomentLinearTerm Φ*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  let A : ℝ := 1+(∑r,‖Φ r‖)+∑r,‖periodicDualWeight Φ r‖
  have hA : 0<A := by dsimp [A];positivity
  let Ψ := fun r => (A:ℂ)⁻¹*Φ r
  have hbound (r : ZMod q) : ‖Φ r‖≤A ∧ ‖periodicDualWeight Φ r‖≤A := by
    have h₁ := single_le_sum (f:=fun r=>‖Φ r‖) (fun j _=>norm_nonneg _) (mem_univ r)
    have h₂ := single_le_sum (f:=fun r=>‖periodicDualWeight Φ r‖) (fun j _=>norm_nonneg _) (mem_univ r)
    dsimp [A];constructor <;>linarith only [h₁,h₂,norm_nonneg (Φ r),norm_nonneg (periodicDualWeight Φ r)]
  have hnorm (z : ℂ) (h : ‖z‖≤A) : ‖(A:ℂ)⁻¹*z‖≤1 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hA.le,←div_eq_inv_mul,div_le_one hA];exact h
  have hΨ (r) : ‖Ψ r‖≤1 := hnorm _ (hbound r).1
  have hdual (r) : ‖periodicDualWeight Ψ r‖≤1 := by rw [show periodicDualWeight Ψ r=(A:ℂ)⁻¹*periodicDualWeight Φ r from dual_weight_scale _ _ _];exact hnorm _ (hbound r).2
  have he : Φ=fun r=>(A:ℂ)*Ψ r := funext fun r => by simp [Ψ,←mul_assoc,Complex.ofReal_ne_zero.mpr hA.ne']
  have hL (s : ℂ) : ZMod.LFunction Φ s=(A:ℂ)*ZMod.LFunction Ψ s := by
    conv_lhs => rw [he]
    simp only [ZMod.LFunction,mul_assoc,←Finset.mul_sum];ring
  have hM : periodicNormMean Φ=A^2*periodicNormMean Ψ := by
    conv_lhs => rw [he]
    simpa only [Complex.norm_real,Real.norm_of_nonneg hA.le] using period_mean_scale (A:ℂ) Ψ
  have hC : periodicMomentLinearTerm Φ=A^2*periodicMomentLinearTerm Ψ := by
    conv_lhs => rw [he]
    simpa only [Complex.norm_real,Real.norm_of_nonneg hA.le] using linear_term_scale (A:ℂ) Ψ
  have hh := (bounded_periodic_moment Ψ hΨ hdual).const_mul_left (A^2)
  convert hh using 2 with T
  simp only [hL,norm_mul,Complex.norm_real,Real.norm_of_nonneg hA.le,mul_pow,
    intervalIntegral.integral_const_mul,hM,hC,Pi.mul_apply,Function.const_apply]
  ring

/-- For any individual character, primitive or imprimitive, the leading
coefficient is φ(q)/q. Its linear term contains the squared Gauss sums
of that particular character at all frequencies. -/
theorem individual_character_second_moment {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)-
      ((q.totient/q:ℝ)*(T*Real.log (T/(2*Real.pi)))+
        (periodicHarmonicConstant χ+
          periodicHarmonicConstant (fun r=>(((Real.sqrt q)⁻¹:ℝ):ℂ)*gaussSum χ (-r))-
          (q.totient/q:ℝ)*(Real.log q+1))*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  have h := periodic_critical_second_moment χ
  simpa only [periodicMomentLinearTerm,periodicNormMean_char,funext (periodicDualWeight_char χ),DirichletCharacter.LFunction] using h

end AnalyticNumberTheory.DirichletLFunctions
