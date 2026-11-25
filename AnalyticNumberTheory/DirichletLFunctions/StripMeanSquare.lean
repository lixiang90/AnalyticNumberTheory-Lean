import AnalyticNumberTheory.AnalyticTools.VerticalApproximationMean
import AnalyticNumberTheory.DirichletSeries.SquareSummableMean
import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximation
import AnalyticNumberTheory.DirichletLFunctions.CriticalMeanSquare

/-!
# The square mean of a periodic Dirichlet series in the right critical strip

A fixed periodic sequence has a convergent diagonal above the critical
line. On each such line up to and including real part one, the mean square
is asymptotic to the height times this diagonal.
-/

open Real Complex Filter Finset MeasureTheory
open scoped Topology
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem continuousOn_periodicLine {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (σ T : ℝ) :
    ContinuousOn (fun t : ℝ => ZMod.LFunction Φ ((σ:ℂ)+t*I)) (Set.Icc 1 T) := by
  intro t ht
  have hs : (σ:ℂ)+t*I≠1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith [ht.1]
  exact ((ZMod.differentiableAt_LFunction Φ _ (Or.inl hs)).continuousAt.comp
    (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop)).continuousWithinAt

private theorem mean_sq_periodicLine_bounded {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ)
    (hΦ : ∀ j, ‖Φ j‖≤1) {σ : ℝ} (hσ : 1/2<σ) (hσ' : σ≤1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖ZMod.LFunction Φ ((σ:ℂ)+t*I)‖^2)/T)
      atTop (𝓝 (∑' n : ℕ, ‖Φ (n+1:ℕ)‖^2*((n+1:ℕ):ℝ)^(-2*σ))) := by
  let P (n : ℕ) (t : ℝ) := dirichletPoly (fun j : ℕ => Φ j) (q*(n+1)) ((σ:ℂ)+t*I)
  let Z (t : ℝ) := ZMod.LFunction Φ ((σ:ℂ)+t*I)
  have hP (n : ℕ) : Continuous (P n) := continuous_vertical_dirichletPoly ..
  have hc (T : ℝ) : ContinuousOn Z (Set.Icc 1 T) := continuousOn_periodicLine Φ σ T
  apply tendsto_squareMean_of_difference (F:=fun T => P (⌊T⌋₊+1)) (G:=fun _ => Z)
    (eventually_ge_atTop (1:ℝ)) (eventually_gt_atTop 0)
    (Eventually.of_forall fun T => (hP _).continuousOn) (Eventually.of_forall hc)
  · apply tendsto_dirichletPoly_squareMean _ σ (fun T => q*(⌊T⌋₊+2)) (L:=3*q) (by positivity)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
      refine ⟨(Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (NeZero.pos q)),?_⟩
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0≤T)) (Nat.cast_nonneg q),
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg q)]
    · have H := (Real.summable_nat_rpow.mpr (by linarith : -2*σ < -1))
      apply Summable.of_nonneg_of_le (f:=fun n : ℕ => ((n+1:ℕ):ℝ)^(-2*σ))
        (fun n => by positivity) _ ((summable_nat_add_iff 1).mpr H)
      intro n
      simpa only [one_mul,one_pow] using mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hΦ (n+1:ℕ)) 2)
        (Real.rpow_nonneg (Nat.cast_nonneg (n+1)) (-2*σ))
  · obtain ⟨K,_,H⟩ := periodicLFunction_approx_dirichletPoly zero_lt_one
      (by linarith [Real.two_le_pi] : (1:ℝ)<2*π)
    apply tendsto_squareMean_of_vertical_error (fun n => P n-Z) (A:=(q:ℝ)^(1-σ))
      (B:=(q:ℝ)^(1-σ)*K) hσ hσ' (fun n T => (hP n).continuousOn.sub (hc T))
    intro n hn t ht ht'
    have ht0 : 0<t := by linarith
    have h := H Φ hΦ hn (by linarith : 0<σ) hσ' (t:=t) (by rwa [abs_of_pos ht0])
      (by simpa [abs_of_pos ht0] using ht')
    change ‖P n t-Z t‖ ≤ _
    rw [norm_sub_rev]
    simpa only [P,Z,abs_of_pos ht0,mul_add,mul_div_assoc,mul_assoc] using h

/-- The mean square of any fixed complex periodic sequence equals its
weighted coefficient diagonal on each line `1/2 < σ ≤ 1`. -/
theorem mean_sq_periodicLFunction_of_half_lt {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ)
    {σ : ℝ} (hσ : 1/2<σ) (hσ' : σ≤1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖ZMod.LFunction Φ ((σ:ℂ)+t*I)‖^2)/T)
      atTop (𝓝 (∑' n : ℕ, ‖Φ (n+1:ℕ)‖^2*((n+1:ℕ):ℝ)^(-2*σ))) := by
  let A : ℝ := 1+∑ r, ‖Φ r‖
  have hA : 0<A := by dsimp [A]; positivity
  let Ψ (r : ZMod q) := ((A:ℂ)⁻¹)*Φ r
  have hΨ (r) : ‖Ψ r‖≤1 := by
    have hr := single_le_sum (fun j _ => norm_nonneg (Φ j)) (mem_univ r)
    simp only [Ψ,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hA.le]
    rw [←div_eq_inv_mul,div_le_one hA]
    dsimp [A]; linarith
  have he (r : ZMod q) : Φ r=(A:ℂ)*Ψ r := by simp [Ψ,←mul_assoc,Complex.ofReal_ne_zero.mpr hA.ne']
  have hz (s : ℂ) : ZMod.LFunction Φ s=(A:ℂ)*ZMod.LFunction Ψ s := by
    simp only [ZMod.LFunction]
    simp_rw [he,mul_assoc,←Finset.mul_sum]
    ring
  have H := (mean_sq_periodicLine_bounded Ψ hΨ hσ hσ').const_mul (A^2)
  simp only [hz,he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hA.le,mul_pow,
    intervalIntegral.integral_const_mul,mul_assoc,tsum_mul_left,mul_div_assoc]
  exact H

/-- Dirichlet characters of any fixed positive modulus satisfy the same
right-strip mean, including imprimitive and principal characters. -/
theorem mean_sq_LFunction_of_half_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1/2<σ) (hσ' : σ≤1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖χ.LFunction ((σ:ℂ)+t*I)‖^2)/T)
      atTop (𝓝 (∑' n : ℕ, ‖χ (n+1:ℕ)‖^2*((n+1:ℕ):ℝ)^(-2*σ))) :=
  mean_sq_periodicLFunction_of_half_lt χ hσ hσ'

/-- The strip diagonal for a character depends only on the stated modulus.
It equals the principal character's L-value at the doubled real part. -/
theorem strip_char_diagonal_eq_principal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1/2<σ) :
    (∑' n : ℕ, ‖χ (n+1:ℕ)‖^2*((n+1:ℕ):ℝ)^(-2*σ)) =
      (DirichletCharacter.LFunctionTrivChar q ((2*σ:ℝ):ℂ)).re := by
  let χ₀ := (1:DirichletCharacter ℂ q)
  let z := ((2*σ:ℝ):ℂ)
  have hz : 1<z.re := by change 1<2*σ; linarith
  have h := χ₀.LSeriesSummable_of_one_lt_re hz
  change _=(χ₀.LFunction z).re
  rw [DirichletCharacter.LFunction_eq_LSeries _ hz,LSeries,h.tsum_eq_zero_add,LSeries.term_zero,zero_add]
  have hs := ((summable_nat_add_iff 1).mpr h).hasSum
  apply (Complex.hasSum_re hs).congr_fun _ |>.tsum_eq
  intro n
  let m := n+1
  have hm : 0<m := Nat.succ_pos _
  have hreal : ((m:ℂ)^z)=(((m:ℝ)^(2*σ):ℝ):ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]; rfl
  symm
  change (LSeries.term _ z m).re=‖χ m‖^2*(m:ℝ)^(-2*σ)
  rw [LSeries.term_of_ne_zero hm.ne',hreal,show -2*σ= -(2*σ) by ring,Real.rpow_neg (Nat.cast_nonneg _)]
  by_cases hu : m.Coprime q
  · rw [norm_char_eq_one_of_coprime χ hu]
    simp [χ₀,MulChar.one_apply ((ZMod.isUnit_iff_coprime m q).mpr hu),←Complex.ofReal_inv]
  · rw [(char_nat_eq_zero_iff_not_coprime χ m).mpr hu,(char_nat_eq_zero_iff_not_coprime χ₀ m).mpr hu]
    simp

/-- The Euler factors removed at the primes dividing the modulus give the
explicit main term for every character with that modulus. -/
theorem mean_sq_LFunction_strip_euler_factors {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1/2<σ) (hσ' : σ≤1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖χ.LFunction ((σ:ℂ)+t*I)‖^2)/T)
      atTop (𝓝 (((∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-((2*σ:ℝ):ℂ))))*
        riemannZeta ((2*σ:ℝ):ℂ)).re)) := by
  have hs : ((2*σ:ℝ):ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs,←strip_char_diagonal_eq_principal χ hσ]
  exact mean_sq_LFunction_of_half_lt χ hσ hσ'

end AnalyticNumberTheory.DirichletLFunctions
