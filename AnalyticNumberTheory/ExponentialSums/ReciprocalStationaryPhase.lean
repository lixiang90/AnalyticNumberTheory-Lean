import AnalyticNumberTheory.AnalyticTools.FresnelIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Quadratic normal form for a reciprocal phase

For `r > 0`, the exact square completing the phase `t + r²/t` is
`w(t)=(t-r)/√t`. The Jacobian correction has a bounded monotone
multiplier, including when the saddle is an endpoint.
-/

open Real Complex MeasureTheory Set
namespace AnalyticNumberTheory.ExponentialSums

/-- The signed quadratic coordinate at the positive saddle `r`. -/
noncomputable def reciprocalSaddleCoordinate (r t : ℝ) := (t-r)/Real.sqrt t

private noncomputable def saddleJacobian (r t : ℝ) := (t+r)/(2*t*Real.sqrt t)

private theorem saddleCoordinate_deriv {r t : ℝ} (ht : 0<t) :
    HasDerivAt (reciprocalSaddleCoordinate r) (saddleJacobian r t) t := by
  have h := ((hasDerivAt_id t).sub_const r).div (Real.hasDerivAt_sqrt ht.ne') (Real.sqrt_pos.mpr ht).ne'
  apply h.congr_deriv
  change (1*Real.sqrt t-(t-r)*(1/(2*Real.sqrt t)))/(Real.sqrt t)^2 = (t+r)/(2*t*Real.sqrt t)
  rw [Real.sq_sqrt ht.le]
  field_simp
  nlinarith only [Real.sq_sqrt ht.le]

/-- Completing the square, with no Taylor remainder or endpoint restriction. -/
theorem reciprocalSaddleCoordinate_sq {r t : ℝ} (ht : 0<t) :
    2*r+(reciprocalSaddleCoordinate r t)^2 = t+r^2/t := by
  rw [reciprocalSaddleCoordinate,div_pow,Real.sq_sqrt ht.le]
  field_simp; ring

private noncomputable def saddleMultiplier (z : ℝ) := (2*z^3+z^2+z)/(z^3+z^2+z+1)

private noncomputable def saddleMultiplierDeriv (z : ℝ) :=
  (z^4+2*z^3+6*z^2+2*z+1)/(z^3+z^2+z+1)^2

private theorem saddleMultiplier_deriv {z : ℝ} (hz : 0≤z) :
    HasDerivAt saddleMultiplier (saddleMultiplierDeriv z) z := by
  have h3 := hasDerivAt_pow 3 z
  have h2 := hasDerivAt_pow 2 z
  have hnum := (((h3.const_mul 2).add h2).add (hasDerivAt_id z))
  have hden := (((h3.add h2).add (hasDerivAt_id z)).add_const 1)
  apply (hnum.div hden (by change z^3+z^2+z+1≠0; positivity)).congr_deriv
  dsimp [saddleMultiplierDeriv]; ring

private theorem continuousAt_saddleMultiplierDeriv {x : ℝ} (hx : 0≤x) :
    ContinuousAt saddleMultiplierDeriv x := by
  have h : (x^3+x^2+x+1)^2 ≠ 0 := by positivity
  unfold saddleMultiplierDeriv
  fun_prop (disch := exact h)

private theorem saddleMultiplier_bounds {z : ℝ} (hz : 0≤z) :
    0≤saddleMultiplier z ∧ saddleMultiplier z≤2 := by
  unfold saddleMultiplier
  refine ⟨by positivity,(div_le_iff₀ (by positivity)).mpr ?_⟩
  nlinarith only [sq_nonneg z,hz]

private theorem saddleMultiplier_identity {r t : ℝ} (hr : 0<r) (ht : 0<t) :
    1-Real.sqrt r*saddleJacobian r t =
      saddleMultiplier (Real.sqrt t/Real.sqrt r) * reciprocalSaddleCoordinate r t * saddleJacobian r t := by
  let x := Real.sqrt t
  let y := Real.sqrt r
  have hx : 0<x := Real.sqrt_pos.mpr ht
  have hy : 0<y := Real.sqrt_pos.mpr hr
  have hx2 : x^2=t := Real.sq_sqrt ht.le
  have hy2 : y^2=r := Real.sq_sqrt hr.le
  change 1-y*((t+r)/(2*t*x))=saddleMultiplier (x/y)*((t-r)/x)*((t+r)/(2*t*x))
  rw [←hx2,←hy2]; dsimp [saddleMultiplier]
  field_simp
  ring

private theorem saddle_e_deriv {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => e (f t)) ((2*Real.pi*Complex.I)*f'*e (f x)) x := by
  have H := (((h.ofReal_comp.const_mul ((2:ℂ)*Real.pi)).mul_const Complex.I).cexp)
  convert H using 1 <;> unfold e <;> ring

set_option maxHeartbeats 1400000 in
/-- Replacing the Jacobian of the reciprocal phase by its value at the
saddle costs at most `1/(π v)`, uniformly for all positive endpoints. -/
theorem reciprocal_stationary_phase_reduction {a b r v : ℝ} (ha : 0<a) (hab : a≤b)
    (hr : 0<r) (hv : 0<v) :
    ‖(∫ t in a..b,e (v*(t+r^2/t))) -
      e (2*v*r)*Real.sqrt r*(∫ y in reciprocalSaddleCoordinate r a..reciprocalSaddleCoordinate r b,e (v*y^2))‖ ≤
      1/(Real.pi*v) := by
  let w := reciprocalSaddleCoordinate r
  let w' := saddleJacobian r
  let z (t : ℝ) := Real.sqrt t/Real.sqrt r
  let z' (t : ℝ) := (1/(2*Real.sqrt t))/Real.sqrt r
  let c (t : ℝ) := saddleMultiplier (z t)
  let c' (t : ℝ) := saddleMultiplierDeriv (z t)*z' t
  let g (t : ℝ) := e (v*(w t)^2)
  let g' (t : ℝ) := (4*Real.pi*Complex.I*v)*(w t*w' t:ℝ)*g t
  let K := (4*Real.pi*Complex.I*v:ℂ)
  have hK : K≠0 := by dsimp [K]; simp [Real.pi_ne_zero,hv.ne']
  have hU (t : ℝ) (ht : t∈uIcc a b) : 0<t := ha.trans_le ((uIcc_of_le hab ▸ ht).1)
  have hww (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt w (w' t) t := saddleCoordinate_deriv (hU t ht)
  have hz0 (t : ℝ) : 0≤z t := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hz (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt z (z' t) t := (Real.hasDerivAt_sqrt (hU t ht).ne').div_const _
  have hc (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt c (c' t) t := (saddleMultiplier_deriv (hz0 t)).comp t (hz t ht)
  have hc0 (t : ℝ) : 0≤c t ∧ c t≤2 := saddleMultiplier_bounds (hz0 t)
  have hc'0 (t : ℝ) : 0≤c' t := by
    dsimp only [c',saddleMultiplierDeriv,z']; have := hz0 t; positivity
  have hg (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt g (g' t) t := by
    have H := saddle_e_deriv (((hww t ht).pow 2).const_mul v)
    convert H using 1; dsimp [g',g]; push_cast; ring
  have hcw : ContinuousOn w' (uIcc a b) := by
    unfold w' saddleJacobian
    apply ContinuousOn.div (f:=fun t : ℝ => t+r) (g:=fun t : ℝ => 2*t*Real.sqrt t) (by fun_prop) (by fun_prop)
    intro t ht; have hp := hU t ht; positivity
  have hCc : ContinuousOn c' (uIcc a b) := by
    intro t ht
    have hzC := (hz t ht).continuousAt
    have hrat := continuousAt_saddleMultiplierDeriv (hz0 t)
    have hden : 2*Real.sqrt t≠0 := mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hU t ht)).ne'
    have hDC : ContinuousAt z' t := by
      unfold z'; exact (continuousAt_const.div (continuousAt_const.mul Real.continuous_sqrt.continuousAt) hden).div_const _
    exact ((hrat.comp hzC).mul hDC).continuousWithinAt
  have hgc : ContinuousOn g (uIcc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hgp : ContinuousOn g' (uIcc a b) :=
    let hw : ContinuousOn w (uIcc a b) := fun t ht => (hww t ht).continuousAt.continuousWithinAt
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hw.mul hcw))).mul hgc
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a:=a) (b:=b)
    (u:=fun t => (c t:ℂ)) (u':=fun t => (c' t:ℂ)) (v:=g) (v':=g')
    (fun t ht => (hc t ht).ofReal_comp) hg (Complex.continuous_ofReal.comp_continuousOn hCc).intervalIntegrable hgp.intervalIntegrable
  have hn (t : ℝ) : ‖g t‖=1 := norm_e _
  have hvar : ‖∫ t in a..b,(c' t:ℂ)*g t‖ ≤ c b-c a := by
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq
    simp only [norm_mul,hn,Complex.norm_real,Real.norm_of_nonneg (hc'0 _),mul_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hc hCc.intervalIntegrable
  have hbd (t : ℝ) : ‖(c t:ℂ)*g t‖=c t := by rw [norm_mul,hn,Complex.norm_real,Real.norm_of_nonneg (hc0 t).1,mul_one]
  have hparts : ‖∫ t in a..b,(c t:ℂ)*g' t‖ ≤ 4 := by
    rw [hi]
    have H := (norm_sub_le ((c b:ℂ)*g b-(c a:ℂ)*g a) _).trans (add_le_add le_rfl hvar)
    have H' := norm_sub_le ((c b:ℂ)*g b) ((c a:ℂ)*g a)
    rw [hbd,hbd] at H'
    linarith only [H,H',(hc0 b).2]
  have hcor : (∫ t in a..b,(((1-Real.sqrt r*w' t:ℝ):ℂ))*g t) =
      K⁻¹ * ∫ t in a..b,(c t:ℂ)*g' t := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro t ht
    change ((1-Real.sqrt r*w' t:ℝ):ℂ)*g t=K⁻¹*((c t:ℂ)*(K*(w t*w' t:ℝ)*g t))
    rw [show 1-Real.sqrt r*w' t=c t*w t*w' t from saddleMultiplier_identity hr (hU t ht)]
    push_cast; field_simp [hK]
  have hsub := intervalIntegral.integral_deriv_smul_comp (a:=a) (b:=b) hww hcw
    (g:=fun y => e (v*y^2)) (by unfold e; fun_prop)
  have hsub' : (∫ t in a..b,(w' t:ℂ)*g t) = ∫ y in w a..w b,e (v*y^2) := by
    simpa only [Complex.real_smul,Function.comp_def,g] using hsub
  have hphase (t : ℝ) (ht : t∈uIcc a b) : e (v*(t+r^2/t)) = e (2*v*r)*g t := by
    rw [←reciprocalSaddleCoordinate_sq (r:=r) (hU t ht)]
    dsimp only [g,w]; rw [←e_add]; congr 1; ring
  rw [intervalIntegral.integral_congr hphase,intervalIntegral.integral_const_mul,←hsub',mul_assoc (e (2*v*r)) (Real.sqrt r:ℂ),←mul_sub,norm_mul,norm_e,one_mul]
  have H : (∫ t in a..b,g t)-(Real.sqrt r:ℂ)*(∫ t in a..b,(w' t:ℂ)*g t) =
      ∫ t in a..b,(((1-Real.sqrt r*w' t:ℝ):ℂ))*g t := by
    have hcont : ContinuousOn (fun t => (Real.sqrt r:ℂ)*((w' t:ℂ)*g t)) (uIcc a b) :=
      continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hcw).mul hgc)
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub hgc.intervalIntegrable hcont.intervalIntegrable]
    apply intervalIntegral.integral_congr; intro t _; dsimp only; push_cast; ring
  rw [H,hcor,norm_mul,norm_inv]
  apply (mul_le_mul_of_nonneg_left hparts (by positivity)).trans_eq
  dsimp [K]; rw [norm_mul,norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg hv.le,Real.norm_of_nonneg Real.pi_pos.le]
  norm_num; ring

/-- The leading oscillation at the positive saddle of a reciprocal phase.
The quantity on the right is bounded uniformly for endpoint saddles and
decays as either endpoint moves farther away in the quadratic coordinate. -/
theorem reciprocal_stationary_phase {a b r v : ℝ} (ha : 0<a) (har : a≤r)
    (hrb : r≤b) (hv : 0<v) :
    ‖(∫ t in a..b,e (v*(t+r^2/t))) -
      e (2*v*r)*Real.sqrt r*((Real.sqrt v)⁻¹:ℝ)*((1+Complex.I)/2)‖ ≤
      1/(Real.pi*v) + Real.sqrt r*(Real.sqrt v)⁻¹*
        (3/(1-Real.sqrt v*reciprocalSaddleCoordinate r a) +
         3/(1+Real.sqrt v*reciprocalSaddleCoordinate r b)) := by
  have hr := ha.trans_le har
  let w := reciprocalSaddleCoordinate r
  let Q := ∫ y in w a..w b,e (v*y^2)
  let k := e (2*v*r)*(Real.sqrt r:ℂ)
  have h₁ := reciprocal_stationary_phase_reduction ha (har.trans hrb) hr hv
  have h₂ := AnalyticTools.norm_scaled_fresnel_sub_le
    (show w a≤0 from div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr har) (Real.sqrt_nonneg _))
    (show 0≤w b from div_nonneg (sub_nonneg.mpr hrb) (Real.sqrt_nonneg _)) hv
  have hk : ‖k‖=Real.sqrt r := by
    simp only [k,norm_mul,norm_e,one_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  let s := (∫ t in a..b,e (v*(t+r^2/t)))
  let m := (((Real.sqrt v)⁻¹:ℝ):ℂ)*((1+Complex.I)/2)
  change ‖s-k*(((Real.sqrt v)⁻¹:ℝ):ℂ)*((1+Complex.I)/2)‖ ≤ _
  rw [mul_assoc k]
  change ‖s-k*m‖ ≤ _
  calc
    ‖s-k*m‖ ≤ ‖s-k*Q‖ + ‖k*Q-k*m‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖s-k*Q‖ + Real.sqrt r*‖Q-m‖ := by rw [←mul_sub,norm_mul,hk]
    _ ≤ _ := by
      rw [mul_assoc (Real.sqrt r)]
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg _))

end AnalyticNumberTheory.ExponentialSums
