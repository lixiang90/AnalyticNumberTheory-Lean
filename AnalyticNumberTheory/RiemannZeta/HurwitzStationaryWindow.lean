import AnalyticNumberTheory.RiemannZeta.HurwitzUniformHeads
import AnalyticNumberTheory.RiemannZeta.HurwitzStationaryEndpoint

/-!
# Estimates inside and outside the transition window of the Hurwitz sum
-/
noncomputable section
open Real Complex Filter Set MeasureTheory
namespace AnalyticNumberTheory.RiemannZeta

private theorem cutoff_power {x : ℝ} (hx : 0<x) (σ : ℝ) : x^(1-σ)=x^(-σ)*x := by
  rw [show 1-σ= -σ+1 by ring,Real.rpow_add hx,Real.rpow_one]

private theorem half_power {x σ : ℝ} (hx : 0<x) (hσ : σ≤1) :
    (x/2)^(-σ)≤2*x^(-σ) := by
  rw [show x/2=x*(2:ℝ)⁻¹ by ring,Real.mul_rpow hx.le (by norm_num),
    Real.inv_rpow (by norm_num : (0:ℝ)≤2),Real.rpow_neg (x:=2) (by norm_num),inv_inv]
  have H := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hσ
  rw [Real.rpow_one] at H
  simpa [mul_comm] using mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hx.le (-σ))

private theorem inner_head {s : ℂ} {ω x : ℝ} (hx : 0<x) (hσ : s.re<1)
    (ht : 0<s.im) (hω : 0≤ω) (hcut : ω*x≤s.im) :
    ‖∫ u in 0..x/2,hurwitzMode s ω u‖ ≤ 8*x^(1-s.re)/s.im := by
  have hω' : ω*(x/2)≤s.im/2 := by linarith
  have H := hurwitzMode_head_uniform (ω:=ω) (show 0<x/2 by positivity) hσ (show 0<s.im/2 by positivity)
    (fun u hu hux => by
      have h := (mul_le_mul_of_nonneg_left hux hω).trans hω'
      rw [abs_of_nonpos (by linarith)];linarith)
  rw [abs_of_nonneg hω] at H
  apply H.trans
  calc
    _ ≤ x^(1-s.re)*(3/(s.im/2)+(s.im/2)/(s.im/2)^2) := by gcongr <;> linarith
    _ = _ := by field_simp;ring

/-- Uniform estimate for the two signs of a retained frequency with no
stationary point on the negative-frequency side. -/
theorem hurwitz_negative_head {s : ℂ} {ω x : ℝ} (hx : 0<x) (hσ : s.re<1) (ht : 0<s.im)
    (hω : ω≤0) (hcut : |ω| * x≤s.im) :
    ‖hurwitzTail s ω x-hurwitzDualMode s ω‖≤4*x^(1-s.re)/s.im := by
  rw [hurwitzTail,sub_sub_cancel_left,norm_neg]
  apply (hurwitzMode_head_uniform hx hσ ht (fun u hu _ => by
    rw [abs_of_nonpos (by linarith [mul_nonpos_of_nonpos_of_nonneg hω hu.le])]
    linarith [mul_nonpos_of_nonpos_of_nonneg hω hu.le])).trans
  calc
    _ ≤ x^(1-s.re)*(3/s.im+s.im/s.im^2) := by gcongr
    _ = _ := by field_simp;ring

/-- The head is O(x^{1−σ}/√t) uniformly up to the edges of the strip.
The stationary point is allowed to coincide with the endpoint. -/
theorem hurwitz_transition_head {s : ℂ} {ω x : ℝ} (hx : 0<x) (hσ : 0≤s.re) (hσ' : s.re<1)
    (ht : 1≤s.im) (hω : 0≤ω) (hcut : ω*x≤s.im) :
    ‖hurwitzTail s ω x-hurwitzDualMode s ω‖≤24*x^(1-s.re)/Real.sqrt s.im := by
  have ht' : 0<s.im := by linarith
  have H := inner_head hx hσ' ht' hω hcut
  have H' := hurwitzMode_second (ω:=ω) (show 0<x/2 by positivity) (show x/2≤x by linarith) hσ ht'
  have hi := hurwitzMode_integrable_at_zero hσ' ω hx.le
  have hi' := hurwitzMode_integrable_at_zero hσ' ω (show 0≤x/2 by positivity)
  rw [hurwitzTail,sub_sub_cancel_left,norm_neg,←intervalIntegral.integral_add_adjacent_intervals hi' (hi'.symm.trans hi)]
  apply (norm_add_le _ _).trans ((add_le_add H H').trans ?_)
  have hst : Real.sqrt s.im≤s.im := by nlinarith [Real.sq_sqrt ht'.le,Real.sqrt_le_sqrt ht,Real.sqrt_one]
  calc
    _ ≤ 8*x^(1-s.re)/Real.sqrt s.im+(2*x^(-s.re))*(8*x/Real.sqrt s.im) := by gcongr; exact half_power hx hσ'.le
    _ = _ := by rw [cutoff_power hx];ring

/-- Sum-of-powers majorant outside the transition window, where k is a
lower bound for the angular-frequency gap. -/
def hurwitzFarError (σ t x k : ℝ) := 40*x^(-σ)*(x/t+1/(x*k^2)+t/(x^2*k^3))

private theorem shell_cost {s : ℂ} {x k : ℝ} (hx : 0<x) (hk : 0<k) (hσ : 0≤s.re) (hσ' : s.re≤1)
    (ht : 0<s.im) :
    10*x^(1-s.re)/s.im+3*(s.re/(x*k)+s.im/(x*k)^2)*(2*x^(-s.re)*(4/k)) ≤
      hurwitzFarError s.re s.im x k := by
  dsimp [hurwitzFarError];rw [cutoff_power hx]
  have hp := Real.rpow_nonneg hx.le (-s.re)
  calc
    _ ≤ 10*(x^(-s.re)*x)/s.im+3*(1/(x*k)+s.im/(x*k)^2)*(2*x^(-s.re)*(4/k)) := by gcongr
    _ ≤ _ := by
      have h₁ := div_nonneg (show 0≤x^(-s.re)*x by positivity) ht.le
      have h₂ : 0≤x^(-s.re)/(x*k^2) := by positivity
      have h₃ : 0≤x^(-s.re)*s.im/(x^2*k^3) := by positivity
      linear_combination (norm:=field_simp <;> ring_nf <;> exact le_rfl) 30*h₁+16*h₂+16*h₃

/-- Lower incomplete integral with the signed endpoint term retained. -/
theorem hurwitz_low_far {s : ℂ} {ω x k : ℝ} (hx : 0<x) (hk : 0<k) (hσ : 0≤s.re) (hσ' : s.re<1)
    (ht : 0<s.im) (hω : 0≤ω) (hgap : k≤s.im/x-ω) :
    ‖hurwitzTail s ω x-hurwitzDualMode s ω+hurwitzEndpoint s ω x‖≤hurwitzFarError s.re s.im x k := by
  have hgap' : (k+ω)*x≤s.im := (le_div_iff₀ hx).mp (by linarith)
  have hcut : ω*x≤s.im := by nlinarith [mul_nonneg hk.le hx.le]
  have hxa : 0<x/2 := by positivity
  have hax : x/2≤x := by linarith
  have H₀ := inner_head hx hσ' ht hω hcut
  have H₁ := hurwitzMode_endpoint_error (s:=s) (ω:=ω) hxa hax hσ ht.le hω (mul_pos hx hk) hk
    (fun u hu => by have h := mul_le_mul_of_nonneg_left hu.2 hω;rw [abs_of_nonpos (by linarith)];nlinarith)
    (fun u hu => by have h := div_le_div_of_nonneg_left ht.le (hxa.trans_le hu.1) hu.2
                    rw [abs_of_nonpos (by linarith)];linarith)
    (.inl (fun u hu => by linarith [mul_le_mul_of_nonneg_left hu.2 hω]))
  have HE : ‖hurwitzEndpoint s ω (x/2)‖≤2*x^(1-s.re)/s.im := by
    rw [norm_hurwitzEndpoint _ _ hxa]
    have h : s.im/2≤|ω*(x/2)-s.im| := by rw [abs_of_nonpos (by nlinarith)]; nlinarith
    apply (div_le_div₀ (by positivity) (Real.rpow_le_rpow hxa.le hax (by linarith : 0≤1-s.re)) (by positivity : 0<s.im/2) h).trans_eq
    ring
  have hi := hurwitzMode_integrable_at_zero hσ' ω hx.le
  have hi' := hurwitzMode_integrable_at_zero hσ' ω hxa.le
  rw [hurwitzTail,sub_sub_cancel_left,←intervalIntegral.integral_add_adjacent_intervals hi' (hi'.symm.trans hi)]
  let J := ∫ u in x/2..x,hurwitzMode s ω u
  calc
    _ = ‖(-(∫ u in 0..x/2,hurwitzMode s ω u))+hurwitzEndpoint s ω (x/2)-
        (J-(hurwitzEndpoint s ω x-hurwitzEndpoint s ω (x/2)))‖ := by congr 1;dsimp [J];abel
    _ ≤ _ := (norm_sub_le ..).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 8*x^(1-s.re)/s.im+2*x^(1-s.re)/s.im+3*(s.re/(x*k)+s.im/(x*k)^2)*((x/2)^(-s.re)*(4/k)) := by simpa only [norm_neg,J] using add_le_add (add_le_add H₀ HE) H₁
    _ ≤ _ := (le_trans ?_ (shell_cost hx hk hσ hσ'.le ht))
  have hH := half_power hx hσ'.le
  have hj : 0≤3*(s.re/(x*k)+s.im/(x*k)^2) := by positivity
  calc
    _ ≤ 8*x^(1-s.re)/s.im+2*x^(1-s.re)/s.im+3*(s.re/(x*k)+s.im/(x*k)^2)*(2*x^(-s.re)*(4/k)) := by gcongr
    _ = _ := by ring


/-- Upper incomplete integral with the signed endpoint term retained. -/
theorem hurwitz_high_far {s : ℂ} {ω x k : ℝ} (hx : 0<x) (hk : 0<k) (hσ : 0<s.re) (hσ' : s.re<1)
    (ht : 0<s.im) (hgap : k≤ω-s.im/x) :
    ‖hurwitzTail s ω x+hurwitzEndpoint s ω x‖≤hurwitzFarError s.re s.im x k := by
  have hτ := div_pos ht hx
  have hω : 0<ω := by linarith
  have hgap' : (k+s.im/x)*x≤ω*x := mul_le_mul_of_nonneg_right (by linarith) hx.le
  rw [add_mul,div_mul_cancel₀ _ hx.ne'] at hgap'
  have hcut : s.im≤ω*x := by nlinarith [mul_nonneg hk.le hx.le]
  have hxb : 0<2*x := by positivity
  have hxb' : x≤2*x := by linarith
  have H₁ := hurwitzMode_endpoint_error (s:=s) (ω:=ω) hx hxb' hσ.le ht.le hω.le (mul_pos hx hk) hk
    (fun u hu => by have h := mul_le_mul_of_nonneg_left hu.1 hω.le;rw [abs_of_nonneg (by linarith)];nlinarith)
    (fun u hu => by have h := div_le_div_of_nonneg_left ht.le hx hu.1
                    rw [abs_of_nonneg (by linarith)];linarith)
    (.inr (fun u hu => by linarith [mul_le_mul_of_nonneg_left hu.1 hω.le]))
  have HE : ‖hurwitzEndpoint s ω (2*x)‖≤2*x^(1-s.re)/s.im := by
    rw [norm_hurwitzEndpoint _ _ hxb]
    have h : s.im≤|ω*(2*x)-s.im| := by rw [abs_of_nonneg (by nlinarith)];nlinarith
    have hp : (2*x)^(1-s.re)≤2*x^(1-s.re) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx.le]
      have H := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (show 1-s.re≤1 by linarith)
      rw [Real.rpow_one] at H
      gcongr
    exact div_le_div₀ (by positivity) hp ht h
  have HT : ‖hurwitzTail s ω (2*x)‖≤8*x^(1-s.re)/s.im := by
    have H := hurwitzTail_first hσ hσ' ht.le hω.ne' hxb (show 0<s.im/(2*x) by positivity)
      (fun u hu => by apply le_trans _ (le_abs_self _)
                      have h := div_le_div_of_nonneg_left ht.le hxb hu
                      have he : s.im/x=2*(s.im/(2*x)) := by ring
                      linarith)
    apply H.trans
    rw [cutoff_power hx]
    calc
      _ ≤ x^(-s.re)*(4/(s.im/(2*x))) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hx hxb' (neg_nonpos.mpr hσ.le)) (by positivity)
      _ = _ := by field_simp <;>ring
  let J := ∫ u in x..2*x,hurwitzMode s ω u
  have he : hurwitzTail s ω x=J+hurwitzTail s ω (2*x) := by
    have hi := hurwitzMode_integrable_at_zero hσ' ω hx.le
    have hi' := hurwitzMode_integrable_at_zero hσ' ω hxb.le
    rw [hurwitzTail,hurwitzTail,←intervalIntegral.integral_add_adjacent_intervals hi (hi.symm.trans hi')]
    dsimp only [J];abel
  rw [he]
  calc
    _ = ‖(J-(hurwitzEndpoint s ω (2*x)-hurwitzEndpoint s ω x))+
      (hurwitzEndpoint s ω (2*x)+hurwitzTail s ω (2*x))‖ := by congr 1;abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ _ := add_le_add H₁ (add_le_add HE HT)
    _ ≤ _ := le_trans ?_ (shell_cost hx hk hσ.le hσ'.le ht)
  have hA := Real.rpow_nonneg hx.le (-s.re)
  have hB : 0≤3*(s.re/(x*k)+s.im/(x*k)^2) := by positivity
  calc
    _ ≤ 3*(s.re/(x*k)+s.im/(x*k)^2)*(2*x^(-s.re)*(4/k))+
          (2*x^(1-s.re)/s.im+8*x^(1-s.re)/s.im) := by gcongr;linarith
    _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
