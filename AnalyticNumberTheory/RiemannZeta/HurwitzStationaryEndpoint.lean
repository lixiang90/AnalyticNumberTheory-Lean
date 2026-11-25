import AnalyticNumberTheory.RiemannZeta.HurwitzFourierTails

/-!
# Fourier modes adjacent to the Hurwitz cutoff

At the last retained frequency and the first omitted frequency, the
stationary point can approach the cutoff from either side.
-/

noncomputable section
open Real Complex Filter Set MeasureTheory
namespace AnalyticNumberTheory.RiemannZeta

private lemma sqrt_im_le {s : ℂ} (ht : 1≤s.im) : Real.sqrt s.im≤s.im := by
  have h := Real.sq_sqrt (by linarith : 0≤s.im)
  have h' : 1≤Real.sqrt s.im := by simpa using Real.sqrt_le_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt s.im-1)]

private lemma power_at_cutoff {x : ℝ} (hx : 0<x) (σ : ℝ) : x^(-σ)*x=x^(1-σ) := by
  rw [show 1-σ= -σ+1 by ring,Real.rpow_add hx,Real.rpow_one]

/-- Incomplete oscillatory gamma integral when the stationary point is at
or to the right of the sharp endpoint. -/
theorem hurwitzMode_head_stationary {s : ℂ} {ω x : ℝ} (hx : 0<x) (hσ : 0≤s.re)
    (hσ' : s.re<1) (ht : 1≤s.im) (hcut : ω*x≤s.im) :
    ‖∫ u in 0..x,hurwitzMode s ω u‖ ≤ (16+8/(1-s.re))*x^(1-s.re)/Real.sqrt s.im := by
  have ht' : 0<s.im := by linarith
  have hx' : 0<x/2 := by positivity
  have hhalf : x/2≤x := by linarith
  have hσp : 0<1-s.re := by linarith
  have hs := Real.sqrt_pos.mpr ht'
  have h₀ := hurwitzMode_head_first (ω:=ω) hx' hσ hσ' ht'.le (show 0<s.im/2 by positivity)
    (fun v hv hv' => by
      by_cases hω : 0≤ω
      · nlinarith [mul_le_mul_of_nonneg_left hv' hω]
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hω) hv.le])
  have h₁ := hurwitzMode_second (ω:=ω) hx' hhalf hσ ht'
  have hstep : (x/2)^(-s.re)≤2*x^(-s.re) := by
    rw [show x/2=x*(2:ℝ)⁻¹ by ring,Real.mul_rpow hx.le (by norm_num),
      Real.inv_rpow (by norm_num : (0:ℝ)≤2),Real.rpow_neg (x:=2) (by norm_num : (0:ℝ)≤2),inv_inv]
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hσ'.le
    rw [Real.rpow_one] at hh
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le (-s.re))
  have H₀ : ‖∫ u in 0..x/2,hurwitzMode s ω u‖ ≤ 8/(1-s.re)*x^(1-s.re)/Real.sqrt s.im := by
    refine h₀.trans ?_
    calc
      _ ≤ 4*x^(1-s.re)/(s.im/2*(1-s.re)) := by gcongr
      _ = (8/(1-s.re)*x^(1-s.re))/s.im := by field_simp; ring
      _ ≤ _ := by gcongr; exact sqrt_im_le ht
  have H₁ : ‖∫ u in x/2..x,hurwitzMode s ω u‖ ≤ 16*x^(1-s.re)/Real.sqrt s.im := by
    refine h₁.trans ((mul_le_mul_of_nonneg_right hstep (by positivity)).trans ?_)
    rw [←power_at_cutoff hx]
    ring_nf
    exact le_rfl
  have hi := hurwitzMode_integrable_at_zero hσ' ω hx.le
  have hi' := hurwitzMode_integrable_at_zero hσ' ω hx'.le
  rw [←intervalIntegral.integral_add_adjacent_intervals hi' (hi'.symm.trans hi)]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add H₀ H₁
    _ = _ := by ring

/-- Incomplete oscillatory gamma tail when the stationary point lies at
or to the left of the sharp endpoint. -/
theorem hurwitzTail_stationary {s : ℂ} {ω x : ℝ} (hx : 0<x) (hσ : 0<s.re)
    (hσ' : s.re<1) (ht : 1≤s.im) (hcut : s.im≤|ω| * x) :
    ‖hurwitzTail s ω x‖ ≤ 24*x^(1-s.re)/Real.sqrt s.im := by
  have ht' : 0<s.im := by linarith
  have hw : 0 < |ω| := pos_of_mul_pos_left (ht'.trans_le hcut) hx.le
  have hx' : 0<2*x := by positivity
  have hs := Real.sqrt_pos.mpr ht'
  have hu := hurwitzTail_first hσ hσ' ht'.le (abs_pos.mp hw) hx' (show 0<s.im/(2*x) by positivity)
    (fun u h => by
      have H := abs_sub_abs_le_abs_sub ω (s.im/u)
      rw [abs_of_nonneg (div_nonneg ht'.le (hx'.trans_le h).le)] at H
      have hdiv := div_le_div_of_nonneg_left ht'.le hx' h
      have hfreq := (div_le_iff₀ hx).mpr hcut
      have hh : s.im/x=2*(s.im/(2*x)) := by ring
      linarith)
  have hl := hurwitzMode_second (ω:=ω) hx (show x≤2*x by linarith) hσ.le ht'
  have H : hurwitzTail s ω x=(∫ u in x..2*x,hurwitzMode s ω u)+hurwitzTail s ω (2*x) := by
    have hi := hurwitzMode_integrable_at_zero hσ' ω hx.le
    have hi' := hurwitzMode_integrable_at_zero hσ' ω hx'.le
    rw [hurwitzTail,hurwitzTail,←intervalIntegral.integral_add_adjacent_intervals hi (hi.symm.trans hi')]
    abel
  rw [H]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hl hu
    _ ≤ x^(-s.re)*(8*(2*x)/Real.sqrt s.im)+x^(-s.re)*(4/(s.im/(2*x))) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (show x≤2*x by linarith) (neg_nonpos.mpr hσ.le)) (by positivity))
    _ = 16*x^(1-s.re)/Real.sqrt s.im+8*x^(1-s.re)/s.im := by
      rw [←power_at_cutoff hx]; field_simp; ring
    _ ≤ 16*x^(1-s.re)/Real.sqrt s.im+8*x^(1-s.re)/Real.sqrt s.im := by
      gcongr; exact sqrt_im_le ht
    _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
