import AnalyticNumberTheory.RiemannZeta.HurwitzDiagonalMean

/-!
# The square mean of Hurwitz zeta in the right half of the critical strip

For each real shift `0 < a ≤ 1` and each `1/2 < σ ≤ 1`, the mean square
on `[1,T]` tends to the absolutely convergent diagonal
`∑ (n+a)^(-2σ)`. Starting the integral at one includes the boundary `σ=1`.
-/

open Real Complex Finset MeasureTheory Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem verticalLine_continuousOn (a σ T : ℝ) : ContinuousOn
    (fun t : ℝ => HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((σ:ℂ)+t*I)) (Set.Icc 1 T) := by
  intro t ht
  have hs : (σ:ℂ)+t*I ≠ 1 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    linarith [ht.1]
  exact ((HurwitzZeta.differentiableAt_hurwitzZeta _ hs).continuousAt.comp
    (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop)).continuousWithinAt

/-- The square mean of the error in the length-`⌊T⌋+1` approximation tends to zero. -/
theorem tendsto_hurwitzZeta_long_error_squareMean {a σ : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1)
    (hσ : 1/2 < σ) (hσ' : σ ≤ 1) : Tendsto (fun T : ℝ => intervalSquareMean 1 T T
      (hurwitzVerticalPolynomial a σ (Icc 0 (⌊T⌋₊+1)) -
        fun t : ℝ => HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((σ:ℂ)+t*I))) atTop (𝓝 0) := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_dirichletPoly_error zero_lt_one (by linarith [Real.two_le_pi] : (1:ℝ)<2*π)
  let γ := 2*(1-σ)
  have hγ : 0≤γ := by dsimp [γ]; linarith
  have hγ' : γ<1 := by dsimp [γ]; linarith
  have h₁ := (tendsto_rpow_neg_atTop (by linarith : 0<1-γ)).const_mul (2*(3:ℝ)^γ)
  have h₂ := (tendsto_rpow_neg_atTop (by linarith : 0<2*σ)).const_mul (2*K^2)
  have hsum := h₁.add h₂
  simp only [mul_zero,add_zero] at hsum
  apply squeeze_zero' _ _ hsum
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    exact div_nonneg (intervalIntegral.integral_nonneg ht fun _ _ => sq_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    let N := ⌊T⌋₊+1
    let P := hurwitzVerticalPolynomial a σ (Icc 0 N)
    let Z (t : ℝ) := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((σ:ℂ)+t*I)
    have ht0 : 0<T := by linarith
    have hN : 0 < N := Nat.succ_pos _
    have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
    have hTN : T≤(N:ℝ) := by simpa [N] using (Nat.lt_floor_add_one T).le
    have hNT : (N:ℝ)+1≤3*T := by dsimp [N]; push_cast; linarith [Nat.floor_le ht0.le]
    let U := ((N:ℝ)+1)^(1-σ)
    let V := K*(N:ℝ)^(-σ)
    have hU : U^2 ≤ (3:ℝ)^γ*T^γ := by
      dsimp only [U]
      rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (by positivity),← Real.mul_rpow (by norm_num : (0:ℝ)≤3) ht0.le]
      push_cast
      rw [show (1-σ)*(2:ℝ)=γ by dsimp [γ]; ring]
      exact Real.rpow_le_rpow (by positivity) hNT hγ
    have hV : V^2 ≤ K^2*T^(-(2*σ)) := by
      dsimp only [V]; rw [mul_pow,← Real.rpow_natCast ((N:ℝ)^(-σ)) 2,← Real.rpow_mul hNr.le]
      push_cast
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [show -σ*(2:ℝ)= -(2*σ) by ring]
      exact Real.rpow_le_rpow_of_nonpos ht0 hTN (by linarith)
    have hp (t : ℝ) (hm : t∈Set.Icc (1:ℝ) T) : ‖P t-Z t‖^2 ≤ 2*U^2*t^(-2:ℝ)+2*V^2 := by
      have htp : 0<t := by linarith [hm.1]
      have h := H (N:=N) (σ:=σ) (t:=t) ha hN (by linarith) hσ'
        (by rw [abs_of_pos htp]; exact htp) (by rw [abs_of_pos htp,one_mul]; exact hm.2.trans hTN)
      rw [abs_of_pos htp] at h
      change ‖Z t-P t‖ ≤ U/t+V at h
      rw [norm_sub_rev]
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      have htinv : t^(-2:ℝ) = (t^2)⁻¹ := by rw [Real.rpow_neg htp.le,Real.rpow_two]
      rw [htinv]
      have he : (U/t)^2=U^2*(t^2)⁻¹ := by rw [div_pow,div_eq_mul_inv]
      nlinarith only [hs,sq_nonneg (U/t-V),he]
    have hc := ((continuous_hurwitzVerticalPolynomial ha.1 σ (Icc 0 N)).continuousOn.sub (verticalLine_continuousOn a σ T)).norm.pow 2
    have hi : IntervalIntegrable (fun t : ℝ => 2*U^2*t^(-2:ℝ)) volume 1 T :=
      (continuousOn_const.mul (continuousOn_id.rpow_const fun t hm => Or.inl (by dsimp; linarith [hm.1]))).intervalIntegrable_of_Icc ht
    have hh := intervalIntegral.integral_mono_on ht (hc.intervalIntegrable_of_Icc ht) (hi.add intervalIntegrable_const) hp
    have heval : (∫ t in (1:ℝ)..T, t^(-2:ℝ)) = 1-T⁻¹ := by
      rw [integral_rpow (Or.inr ⟨by norm_num,fun h => by rw [Set.uIcc_of_le ht] at h; linarith [h.1]⟩)]
      simp only [show (-2:ℝ)+1= -1 by norm_num,Real.rpow_neg_one]; ring
    rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const_mul,heval,
      intervalIntegral.integral_const,smul_eq_mul] at hh
    change (∫ t in (1:ℝ)..T, ‖P t-Z t‖^2)/T ≤ _
    apply (div_le_iff₀ ht0).mpr
    have hpow : T^(-(1-γ))*T = T^γ := by
      rw [←Real.rpow_add_one ht0.ne']; congr 1; ring
    have husa := mul_le_mul_of_nonneg_left (sub_le_self 1 (inv_nonneg.mpr ht0.le)) (show 0≤2*U^2 by positivity)
    have hvsa := mul_le_mul_of_nonneg_left (sub_le_self T zero_le_one) (show 0≤2*V^2 by positivity)
    change (∫ t in (1:ℝ)..T, ‖P t-Z t‖^2) ≤ (2*(3:ℝ)^γ*T^(-(1-γ))+2*K^2*T^(-(2*σ)))*T
    change (∫ t in (1:ℝ)..T, ‖P t-Z t‖^2) ≤ 2*U^2*(1-T⁻¹)+(T-1)*(2*V^2) at hh
    nlinarith only [hh,husa,hvsa,hU,mul_le_mul_of_nonneg_right hV ht0.le,
      congrArg (fun y : ℝ => 2*(3:ℝ)^γ*y) hpow]

/-- The complete mean-square main term for every real shift and every `1/2 < σ ≤ 1`. -/
theorem mean_sq_hurwitzZeta_of_half_lt {a σ : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1)
    (hσ : 1/2 < σ) (hσ' : σ ≤ 1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle)
      ((σ:ℂ)+t*I)‖^2)/T) atTop (𝓝 (∑' n : ℕ, ((n:ℝ)+a)^(-2*σ))) :=
  tendsto_squareMean_of_difference (eventually_ge_atTop (1:ℝ)) (eventually_gt_atTop 0)
    (Eventually.of_forall fun _T => (continuous_hurwitzVerticalPolynomial ha.1 σ _).continuousOn)
    (Eventually.of_forall (verticalLine_continuousOn a σ))
    (tendsto_long_hurwitzPolynomial_squareMean ha hσ) (tendsto_hurwitzZeta_long_error_squareMean ha hσ hσ')

/-- The real diagonal constant is the value of Hurwitz zeta at `2σ`. -/
theorem hurwitzZeta_re_eq_square_diagonal {a σ : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1) (hσ : 1/2 < σ) :
    (HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((2*σ:ℝ):ℂ)).re =
      ∑' n : ℕ, ((n:ℝ)+a)^(-2*σ) := by
  have h := Complex.hasSum_re (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨ha.1.le,ha.2⟩
    (s := ((2*σ:ℝ):ℂ)) (by change 1<2*σ; linarith))
  symm
  apply (h.congr_fun fun n => ?_).tsum_eq
  have hp := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha.1
  rw [←Complex.ofReal_natCast,←Complex.ofReal_add,←Complex.ofReal_cpow hp.le,
    ←Complex.ofReal_one,←Complex.ofReal_div,Complex.ofReal_re,
    show -2*σ= -(2*σ) by ring,Real.rpow_neg hp.le,one_div]

end AnalyticNumberTheory.RiemannZeta
