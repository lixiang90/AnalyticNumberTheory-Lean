import AnalyticNumberTheory.RiemannZeta.FourthMomentLog

/-!
# Short divisor polynomials in the fourth moment

Any fixed fraction of the height gives the same two-polynomial approximation
up to a square-mean error of order `T (log T)^3`.
-/

open Complex Real MeasureTheory Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.RiemannZeta

private theorem mainTerm_difference_mean {δ T : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) (hT : 2 ≤ T)
    (hx : 2 ≤ δ*T) (neg : Bool) :
    (∫ t in T..2*T, ‖fourthMomentMainTerm ⌈T⌉₊ neg t - fourthMomentMainTerm ⌊δ*T⌋₊ neg t‖^2) ≤
      (32*(1+4*π)/δ)*T*(1+Real.log T)^3 := by
  let X := ⌊δ*T⌋₊
  let Y := ⌈T⌉₊
  have hT0 : 0 < T := by linarith
  have hdt : 0 ≤ δ*T := by positivity
  have hX : 1 ≤ X := Nat.le_floor (by push_cast; linarith)
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast hX
  have hXY : X ≤ Y := by
    apply Nat.cast_le (α := ℝ) |>.mp
    exact (Nat.floor_le hdt).trans ((mul_le_of_le_one_left hT0.le hδ').trans (Nat.le_ceil T))
  have hY : (Y:ℝ) ≤ 2*T := by linarith [Nat.ceil_lt_add_one hT0.le]
  have htY : T ≤ (Y:ℝ) := Nat.le_ceil T
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hr : (Y:ℝ)/(X:ℝ) ≤ 4/δ := by
    apply (div_le_div_iff₀ hX0 hδ).mpr
    have hfl : δ*T < (X:ℝ)+1 := Nat.lt_floor_add_one _
    nlinarith [mul_le_mul_of_nonneg_right hY hδ.le]
  have hl : 1+Real.log Y ≤ 2*(1+Real.log T) := by
    have hh := Real.log_le_log (hT0.trans_le htY) hY
    rw [Real.log_mul (by norm_num) hT0.ne'] at hh
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hL := pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log Y) hl 3
  have hb : (2*T-T+2*π*Y) ≤ (1+4*π)*T := by nlinarith only [mul_le_mul_of_nonneg_left hY Real.pi_pos.le]
  have hh := divisorPolynomial_block_vertical (σ := 1/2) (by norm_num) hXY hX (by linarith : T ≤ 2*T)
  rw [show (2:ℝ)*(1/2)=1 by norm_num,Real.rpow_one] at hh
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hh
  simp_rw [norm_fourthMomentMainTerm_sub]
  apply hh.trans
  rw [show (Y:ℝ)*(1+Real.log Y)^3/(X:ℝ) = ((Y:ℝ)/(X:ℝ))*(1+Real.log Y)^3 by ring]
  apply (mul_le_mul hb (mul_le_mul hr hL (by positivity) (by positivity)) (by positivity) (by positivity)).trans_eq
  ring

/-- Replacing the cutoff by any fixed fraction of the height retains a lower-order
mean-square remainder. -/
theorem zeta_sq_sub_short_mainTerms_mean_sq {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ C > (0:ℝ), ∀ {T : ℝ}, 2 ≤ T → 2 ≤ δ*T →
    (∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)^2 -
      (fourthMomentMainTerm ⌊δ*T⌋₊ false t + fourthMomentMainTerm ⌊δ*T⌋₊ true t)‖^2) ≤
      C*T*(1+Real.log T)^3 := by
  obtain ⟨C,hC,h⟩ := zeta_sq_sub_fourthMomentMainTerms_mean_sq
  let A := 32*(1+4*π)/δ
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2*C+8*A,by positivity,?_⟩
  intro T hT hx
  let X := ⌊δ*T⌋₊
  let Y := ⌈T⌉₊
  let R (t : ℝ) := riemannZeta ((1/2:ℂ)+t*I)^2-(fourthMomentMainTerm Y false t+fourthMomentMainTerm Y true t)
  let D (neg : Bool) (t : ℝ) := fourthMomentMainTerm Y neg t-fourthMomentMainTerm X neg t
  have hab : T ≤ 2*T := by linarith
  have hR : ContinuousOn R (Icc T (2*T)) := ((continuous_riemannZeta_half.pow 2).sub
    ((continuous_fourthMomentMainTerm Y false).add (continuous_fourthMomentMainTerm Y true))).continuousOn
  have hc (neg : Bool) : ContinuousOn (D neg) (Icc T (2*T)) := ((continuous_fourthMomentMainTerm Y neg).sub
    (continuous_fourthMomentMainTerm X neg)).continuousOn
  have hd (neg : Bool) := mainTerm_difference_mean hδ hδ' hT hx neg
  have hboth := integral_norm_add_sq_le hab (hc false) (hc true) (hd false) (hd true)
  have hsum := integral_norm_add_sq_le hab hR ((hc false).add (hc true)) (h hT) hboth
  have he (t : ℝ) : riemannZeta ((1/2:ℂ)+t*I)^2 - (fourthMomentMainTerm X false t+fourthMomentMainTerm X true t) =
      R t+(D false t+D true t) := by dsimp only [R,D]; ring
  change (∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)^2 -(fourthMomentMainTerm X false t+fourthMomentMainTerm X true t)‖^2) ≤ _
  simp_rw [he]
  exact hsum.trans_eq (by dsimp [A]; ring)

end AnalyticNumberTheory.RiemannZeta
