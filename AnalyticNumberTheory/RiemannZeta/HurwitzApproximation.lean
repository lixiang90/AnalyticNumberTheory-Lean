import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans

/-!
# The error of a vertical Hurwitz Dirichlet polynomial
-/

open Complex Real Finset
namespace AnalyticNumberTheory.RiemannZeta

/-- Uniform error with the pole-correction term estimated in norm, for an arbitrary real shift in the unit interval. -/
theorem hurwitzZeta_dirichletPoly_error {c : ℝ} (hc : 0 < c) (hc' : c < 2*π) :
    ∃ K > 0, ∀ {a : ℝ} {N : ℕ} {σ t : ℝ}, a ∈ Set.Ioc (0:ℝ) 1 → 0 < N → 0 < σ → σ ≤ 1 →
      0 < |t| → |t| ≤ c*N →
      let s := (σ:ℂ)+t*I
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s - ∑ m ∈ Icc 0 N, ((m:ℂ)+a)^(-s)‖ ≤
        ((N:ℝ)+1)^(1-σ)/|t|+K*(N:ℝ)^(-σ) := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_approx_dirichletPoly hc hc'
  refine ⟨K,hK,?_⟩
  intro a N σ t ha hN hσ hσ' ht hTN s
  have hr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : s ≠ 1 := by intro h; have h' := congrArg Complex.im h; simp [s] at h'; simp [h'] at ht
  have hz : 0 < (N:ℝ)+a := add_pos hr ha.1
  have hnorm : |t| ≤ ‖1-s‖ := by simpa [s] using Complex.abs_im_le_norm (1-s)
  have hmain := H ha (N:=N) hσ hs (hTN.trans (by nlinarith [mul_pos hc ha.1]))
  let D := ∑ m ∈ Icc 0 N, ((m:ℂ)+a)^(-s)
  let e := ((N:ℂ)+a)^(1-s)/(1-s)
  have he : ‖e‖ ≤ ((N:ℝ)+1)^(1-σ)/|t| := by
    dsimp [e]
    rw [norm_div, ← Complex.ofReal_natCast, ← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos hz]
    simp only [s,sub_re,one_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
    exact div_le_div₀ (by positivity)
      (Real.rpow_le_rpow hz.le (by linarith only [ha.2]) (by linarith)) ht hnorm
  have herr : K*((N:ℝ)+a)^(-σ) ≤ K*(N:ℝ)^(-σ) := by
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr (by linarith only [ha.1]) (by linarith)) hK.le
  have hb : ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s - (D-e)‖ ≤ K*((N:ℝ)+a)^(-σ) := hmain
  calc _ = ‖(HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s - (D-e)) + (-e)‖ := by congr 1; dsimp [D]; ring
       _ ≤ _ := (norm_add_le ..).trans (by rw [norm_neg,add_comm]; exact add_le_add he (hb.trans herr))

/-- Polar decomposition of a positive real Dirichlet monomial on the critical line. -/
theorem critical_monomial_eq {x : ℝ} (hx : 0<x) (t : ℝ) :
    (x:ℂ)^(-((1/2:ℂ)+t*I)) = (((√x)⁻¹:ℝ):ℂ)*Complex.exp (I*((-Real.log x:ℝ):ℂ)*t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),← Complex.ofReal_log hx.le]
  have hw : (√x)⁻¹ = Real.exp (Real.log x*(-1/2)) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx,← Real.exp_neg]; congr 1; ring
  rw [hw,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

end AnalyticNumberTheory.RiemannZeta
