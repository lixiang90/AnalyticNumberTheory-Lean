import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximation
import AnalyticNumberTheory.DirichletLFunctions.CharacterHarmonics
import AnalyticNumberTheory.DirichletSeries.CriticalMeanValues

/-!
# The second moment of a Dirichlet L-function on the critical line

For any fixed character of modulus `q`, the leading diagonal contribution
is `φ(q)/q`. This includes principal and imprimitive characters.
-/

open Complex Real Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

private noncomputable def lineValue {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (t : ℝ) :=
  ZMod.LFunction Φ ((1/2:ℂ)+t*I)

private theorem continuous_lineValue {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) :
    Continuous (lineValue Φ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have he : (1/2:ℂ)+(t:ℂ)*I ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num at hh
  exact (ZMod.differentiableAt_LFunction Φ _ (Or.inl he)).continuousAt.comp
    (f := fun t : ℝ => (1/2:ℂ)+t*I) (by fun_prop)

private theorem mean_long_error {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (hΦ : ∀ j, ‖Φ j‖ ≤ 1) :
    ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, ‖lineValue Φ t -
        criticalLinePolynomial (fun n : ℕ => Φ n) (q*(⌊T⌋₊+2)) t‖^2)/T ≤ C := by
  obtain ⟨K,hK,H⟩ := periodicLFunction_approx_dirichletPoly zero_lt_one
    (by linarith [Real.two_le_pi] : (1:ℝ) < 2*π)
  refine ⟨(q:ℝ)*(6+2*K^2),?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  let N := ⌊T⌋₊+1
  have ht0 : 0 < T := by linarith
  have hn : 1 ≤ N := Nat.succ_pos _
  have hnr : (1:ℝ) ≤ N := by exact_mod_cast hn
  have hlo : T ≤ (N:ℝ) := by simpa [N] using (Nat.lt_floor_add_one T).le
  have hhi : (N:ℝ)+1 ≤ T+2 := by dsimp [N]; push_cast; linarith [Nat.floor_le ht0.le]
  let f := fun t : ℝ => lineValue Φ t - criticalLinePolynomial (fun n : ℕ => Φ n) (q*(N+1)) t
  have hcont : Continuous f := (continuous_lineValue Φ).sub (continuous_criticalLinePolynomial ..)
  have hp (t : ℝ) (ht : t ∈ Set.Icc 1 T) :
      ‖f t‖^2 ≤ (2*q*(T+2))*t^(-2:ℝ) + 2*q*K^2 := by
    have htp : 0 < t := by linarith [ht.1]
    have htN : |t| ≤ 1*(N:ℝ) := by rw [abs_of_pos htp,one_mul]; exact ht.2.trans hlo
    have h := H Φ hΦ (N:=N) hn (σ:=1/2) (by norm_num)
      (by norm_num) (abs_pos.mpr htp.ne') htN
    simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at h
    change ‖f t‖ ≤ (q:ℝ)^(1-(1/2:ℝ))*(((N:ℝ)+1)^(1-1/2:ℝ)/|t|+K*(N:ℝ)^(-(1/2:ℝ))) at h
    rw [show 1-(1/2:ℝ)=1/2 by norm_num, ← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,abs_of_pos htp] at h
    have hb : (N:ℝ)^(-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnr (by norm_num)
    have hle : ‖f t‖ ≤ √(q:ℝ)*(√((N:ℝ)+1)/t+K) := by
      apply h.trans
      gcongr
      exact mul_le_of_le_one_right hK.le hb
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hy : (√((N:ℝ)+1)/t+K)^2 ≤ 2*(√((N:ℝ)+1)/t)^2+2*K^2 := by
      nlinarith only [sq_nonneg (√((N:ℝ)+1)/t-K)]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg q)] at hsq
    rw [div_pow,Real.sq_sqrt (by positivity)] at hy
    have hrpow : t^(-2:ℝ) = (t^2)⁻¹ := by rw [Real.rpow_neg htp.le]; norm_num
    rw [hrpow]
    have hm := mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg q)
    have hx := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hhi (sq_nonneg t)) (by positivity : 0 ≤ 2*(q:ℝ))
    calc _ ≤ (q:ℝ)*(2*(((N:ℝ)+1)/t^2)+2*K^2) := hsq.trans hm
         _ = 2*q*(((N:ℝ)+1)/t^2)+2*q*K^2 := by ring
         _ ≤ _ := (add_le_add_left hx (2*(q:ℝ)*K^2)).trans_eq (by ring)
  have hi : IntervalIntegrable (fun t : ℝ => 2*q*(T+2)*t^(-2:ℝ)) volume 1 T :=
    (continuousOn_const.mul (continuousOn_id.rpow_const fun t ht => Or.inl (by dsimp; linarith [ht.1]))).intervalIntegrable_of_Icc hT
  have hb := intervalIntegral.integral_mono_on hT ((hcont.norm.pow 2).intervalIntegrable ..)
    (hi.add intervalIntegrable_const) hp
  have he : (∫ t in (1:ℝ)..T, t^(-2:ℝ)) = 1-T⁻¹ := by
    rw [integral_rpow (Or.inr ⟨by norm_num,fun h => by rw [Set.uIcc_of_le hT] at h; linarith [h.1]⟩)]
    simp only [show (-2:ℝ)+1 = -1 by norm_num,Real.rpow_neg_one]
    ring
  rw [intervalIntegral.integral_add hi intervalIntegrable_const, intervalIntegral.integral_const_mul,
    he, intervalIntegral.integral_const, smul_eq_mul] at hb
  change (∫ t in (1:ℝ)..T, ‖f t‖^2)/T ≤ _
  rw [div_le_iff₀ ht0]
  simp only [Pi.pow_apply] at hb
  have h1 := mul_le_mul_of_nonneg_left (show 1-T⁻¹ ≤ 1 by linarith only [inv_nonneg.mpr ht0.le]) (by positivity : 0 ≤ 2*q*(T+2))
  have h2 := mul_le_mul_of_nonneg_left (by linarith : T+2 ≤ 3*T) (by positivity : 0 ≤ 2*(q:ℝ))
  nlinarith only [hb,h1,h2, show 0 ≤ 2*(q:ℝ)*K^2 by positivity]

/-- Bounded periodic coefficients have a critical-line second moment with
leading constant equal to the average squared amplitude in one period. -/
theorem mean_sq_periodicLFunction_half {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (hΦ : ∀ j, ‖Φ j‖ ≤ 1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖^2)/(T*Real.log T))
      atTop (𝓝 (periodicNormMean Φ)) := by
  apply criticalMeanSquare_of_approx (continuous_lineValue Φ) (fun n : ℕ => Φ n)
    (fun n => hΦ n) (by dsimp [periodicNormMean]; positivity) ⟨q,abs_periodic_harmonic_sub_mean_le Φ hΦ⟩
    (fun T => q*(⌊T⌋₊+2)) _ (mean_long_error Φ hΦ)
  refine ⟨3*(q:ℝ),by have := NeZero.pos q; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
  constructor
  · have hq := NeZero.pos q
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hq)
  · push_cast
    have h := mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0 ≤ T)) (Nat.cast_nonneg q)
    nlinarith only [h,mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg q)]

/-- For every fixed positive modulus and every character, the critical-line
mean square divided by `T log T` tends to `φ(q)/q`. -/
theorem mean_sq_LFunction_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)/(T*Real.log T))
      atTop (𝓝 ((q.totient:ℝ)/q)) := by
  simpa only [periodicNormMean_char,DirichletCharacter.LFunction] using mean_sq_periodicLFunction_half χ (norm_char_le_one χ)

/-- For a rational shift, the Hurwitz zeta function has the same
critical-line second-moment leading constant as the Riemann zeta function. -/
theorem mean_sq_hurwitzZeta_rational_half {q : ℕ} [NeZero q] (r : ZMod q) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T,
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) ((1/2:ℂ)+t*I)‖^2)/(T*Real.log T))
      atTop (𝓝 1) := by
  classical
  let Φ : ZMod q → ℂ := fun j => if j = r then 1 else 0
  have hΦ (j : ZMod q) : ‖Φ j‖ ≤ 1 := by by_cases h : j=r <;> simp [Φ,h]
  have hmean : periodicNormMean Φ = (q:ℝ)⁻¹ := by
    simp only [periodicNormMean,Φ]
    simp [apply_ite (fun z : ℂ => ‖z‖),ite_pow,one_div]
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have he (t : ℝ) :
      ‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖^2 =
        (q:ℝ)⁻¹ * ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) ((1/2:ℂ)+t*I)‖^2 := by
    simp only [ZMod.LFunction,Φ,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [norm_mul,mul_pow, Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
    congr 1
    have hreal : (-((1/2:ℂ)+t*I)).re = -(1/2:ℝ) := by norm_num
    rw [hreal,Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow,inv_pow,Real.sq_sqrt hq.le]
  have H := (mean_sq_periodicLFunction_half Φ hΦ).const_mul (q:ℝ)
  rw [hmean,mul_inv_cancel₀ hq.ne'] at H
  refine H.congr (fun T => ?_)
  simp_rw [he,intervalIntegral.integral_const_mul]
  rw [← mul_div_assoc,← mul_assoc,mul_inv_cancel₀ hq.ne',one_mul]

end AnalyticNumberTheory.DirichletLFunctions
