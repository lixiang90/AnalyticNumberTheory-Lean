import AnalyticNumberTheory.DivisorProblems.SawtoothApproximation
import AnalyticNumberTheory.AnalyticTools.Summation.WeightedIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Sharp Fourier truncation of the sawtooth

The partial sine series is integrated from the midpoint of a period.
Its derivative is the Dirichlet kernel minus one, giving a pointwise
error controlled by the distance to the nearest integer.
-/

open Real Complex MeasureTheory Set
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

/-- The finite harmonic sine sum, with the normalization of the centered
fractional part. -/
noncomputable def sawtoothSineSum (H : ℕ) (x : ℝ) : ℝ :=
  ∑ n∈Finset.Ioc 0 H, Real.sin (2*Real.pi*n*x)/(Real.pi*n)

private theorem dirichlet_sine (H : ℕ) (t : ℝ) :
    Real.sin t * (1+2*∑ n∈Finset.Ioc 0 H,Real.cos (2*(n:ℝ)*t)) =
      Real.sin ((2*(H:ℝ)+1)*t) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le H),Nat.cast_succ]
    have h := Real.sin_sub_sin ((2*((H:ℝ)+1)+1)*t) ((2*(H:ℝ)+1)*t)
    rw [show (((2*((H:ℝ)+1)+1)*t)+((2*(H:ℝ)+1)*t))/2=2*((H:ℝ)+1)*t by ring,
      show (((2*((H:ℝ)+1)+1)*t)-((2*(H:ℝ)+1)*t))/2=t by ring] at h
    linarith only [ih,h]

private theorem sawtooth_primitive {H : ℕ} {x : ℝ} (hx : 0<x) (hx' : x≤1/2) :
    x-1/2+sawtoothSineSum H x =
      -(∫ t in x..(1/2:ℝ),Real.sin (((2*(H:ℝ)+1)*Real.pi)*t)/Real.sin (Real.pi*t)) := by
  let f (t : ℝ) := t-1/2+sawtoothSineSum H t
  let L := (2*(H:ℝ)+1)*Real.pi
  have hs {t : ℝ} (ht : t∈Icc x (1/2:ℝ)) : 0<Real.sin (Real.pi*t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hx.trans_le ht.1)) (by nlinarith only [mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le,Real.pi_pos])
  have hf (t : ℝ) (ht : t∈uIcc x (1/2:ℝ)) : HasDerivAt f (Real.sin (L*t)/Real.sin (Real.pi*t)) t := by
    have ht' := uIcc_of_le hx' ▸ ht
    have hd (n : ℕ) (hn : n∈Finset.Ioc 0 H) :
        HasDerivAt (fun t : ℝ => Real.sin (2*Real.pi*n*t)/(Real.pi*n)) (2*Real.cos (2*Real.pi*n*t)) t := by
      have hn' : (n:ℝ)≠0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
      apply ((((hasDerivAt_id t).const_mul (2*Real.pi*n)).sin).div_const (Real.pi*n)).congr_deriv
      simp only [id_eq]; field_simp [hn',Real.pi_ne_zero]
    have hsum := HasDerivAt.fun_sum hd
    apply (((hasDerivAt_id t).sub_const (1/2:ℝ)).fun_add hsum).congr_deriv
    rw [←Finset.mul_sum]
    apply (eq_div_iff (hs ht').ne').mpr
    have he := dirichlet_sine H (Real.pi*t)
    rw [mul_comm (Real.sin _)] at he
    simp_rw [show ∀ n : ℕ, 2*(n:ℝ)*(Real.pi*t)=2*Real.pi*n*t by intro n; ring] at he
    rw [show L*t=(2*(H:ℝ)+1)*(Real.pi*t) by dsimp [L]; ring]
    exact he
  have hc : ContinuousOn (fun t => Real.sin (L*t)/Real.sin (Real.pi*t)) (Icc x (1/2:ℝ)) :=
    ContinuousOn.div (f:=fun t : ℝ => Real.sin (L*t)) (g:=fun t : ℝ => Real.sin (Real.pi*t)) (by fun_prop) (by fun_prop) (fun t ht => (hs ht).ne')
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hf (hc.intervalIntegrable_of_Icc hx')
  have hmid : f (1/2)=0 := by
    dsimp [f,sawtoothSineSum]; rw [sub_self,zero_add]
    apply Finset.sum_eq_zero; intro n _
    rw [show 2*Real.pi*n*(1/2:ℝ)=(n:ℝ)*Real.pi by ring,Real.sin_nat_mul_pi,zero_div]
  rw [hmid,zero_sub] at hint
  change f x= - _
  exact eq_neg_of_add_eq_zero_left (by rw [hint]; ring)

private theorem sawtooth_fourier_midpoint {H : ℕ} {x : ℝ} (hx : 0<x) (hx' : x≤1/2) :
    |x-1/2+sawtoothSineSum H x|≤2/(((2*(H:ℝ)+1)*Real.pi)*Real.sin (Real.pi*x)) := by
  let L := (2*(H:ℝ)+1)*Real.pi
  have hL : 0<L := by dsimp [L]; positivity
  let f (u : ℝ) : ℂ := Real.sin (L*u)
  let w (u : ℝ) := (Real.sin (Real.pi*u))⁻¹
  let w' (u : ℝ) := -(Real.cos (Real.pi*u)*Real.pi)/(Real.sin (Real.pi*u))^2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hangle {t : ℝ} (ht : t∈Icc x (1/2:ℝ)) : 0<Real.pi*t ∧ Real.pi*t≤Real.pi/2 :=
    ⟨mul_pos Real.pi_pos (hx.trans_le ht.1), by nlinarith only [mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le]⟩
  have hs {t : ℝ} (ht : t∈Icc x (1/2:ℝ)) : 0<Real.sin (Real.pi*t) :=
    Real.sin_pos_of_pos_of_lt_pi (hangle ht).1 (by linarith [(hangle ht).2,Real.pi_pos])
  have hder (t : ℝ) (ht : t∈Icc x (1/2:ℝ)) : HasDerivAt w (w' t) t := by
    apply ((((hasDerivAt_id t).const_mul Real.pi).sin).inv (hs ht).ne').congr_deriv
    dsimp [w']; ring
  have hcw : ContinuousOn w' (Icc x (1/2:ℝ)) := ContinuousOn.div
    (f:=fun t : ℝ => -(Real.cos (Real.pi*t)*Real.pi)) (g:=fun t : ℝ => (Real.sin (Real.pi*t))^2)
    (by fun_prop) (by fun_prop) (fun t ht => pow_ne_zero _ (hs ht).ne')
  have hneg (t : ℝ) (ht : t∈Icc x (1/2:ℝ)) : w' t≤0 := by
    have hcos := Real.cos_nonneg_of_mem_Icc (x:=Real.pi*t) ⟨by linarith [(hangle ht).1,Real.pi_pos],(hangle ht).2⟩
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hcos Real.pi_pos.le)) (sq_nonneg _)
  have hprimitive (t : ℝ) (ht : t∈Icc x (1/2:ℝ)) : ‖∫ u in x..t,f u‖≤2/L := by
    dsimp only [f]; rw [intervalIntegral.integral_ofReal,Complex.norm_real,Real.norm_eq_abs]
    rw [intervalIntegral.integral_comp_mul_left Real.sin hL.ne',smul_eq_mul,integral_sin,abs_mul,abs_inv,abs_of_pos hL]
    have h := abs_sub (Real.cos (L*x)) (Real.cos (L*t))
    calc _ ≤ L⁻¹*(1+1) := by gcongr; linarith [Real.abs_cos_le_one (L*x),Real.abs_cos_le_one (L*t)]
         _ = _ := by ring
  have HH := norm_integral_decreasing_weight hx' f w w' (fun _ _ => hc.continuousAt) hc.stronglyMeasurable
    hder hcw hneg (inv_nonneg.mpr (hs (right_mem_Icc.mpr hx')).le) hprimitive
  have he : (∫ t in x..(1/2:ℝ),(w t:ℂ)*f t) = ((∫ t in x..(1/2:ℝ),
      Real.sin (L*t)/Real.sin (Real.pi*t):ℝ):ℂ) := by
    rw [←intervalIntegral.integral_ofReal]; apply intervalIntegral.integral_congr; intro t _
    dsimp only [w,f]; push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs] at HH
  rw [sawtooth_primitive hx hx',abs_neg]
  apply HH.trans_eq
  change (Real.sin (Real.pi*x))⁻¹*(2/L)=2/(L*Real.sin (Real.pi*x))
  simp only [div_eq_mul_inv,mul_inv]; ring

private theorem sawtooth_fourier_near {x : ℝ} (hx : 0≤x) (hx' : x≤1/2) (H : ℕ) :
    |x-1/2+sawtoothSineSum H x|≤6/(1+(H:ℝ)*x) := by
  by_cases h : (H:ℝ)*x≤1
  · have hsum : |sawtoothSineSum H x|≤(H:ℝ)*(2*x) := by
      calc
        |sawtoothSineSum H x| ≤ ∑ n∈Finset.Ioc 0 H,|Real.sin (2*Real.pi*n*x)/(Real.pi*n)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n∈Finset.Ioc 0 H,2*x := Finset.sum_le_sum (fun n hn => by
          have hn' : 0<(n:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
          rw [abs_div,abs_of_pos (mul_pos Real.pi_pos hn')]
          apply (div_le_iff₀ (mul_pos Real.pi_pos hn')).mpr
          apply Real.abs_sin_le_abs.trans
          rw [abs_of_nonneg (by positivity)]; ring_nf; rfl)
        _ = _ := by simp
    have hnorm := (abs_add_le (x-1/2) (sawtoothSineSum H x)).trans (add_le_add le_rfl hsum)
    rw [abs_of_nonpos (sub_nonpos.mpr hx')] at hnorm
    apply hnorm.trans
    apply (le_div_iff₀ (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_left h (show 0≤(H:ℝ)*x by positivity)
    nlinarith only [h,hmul,hx,mul_nonneg (show 0≤(H:ℝ)*x by positivity) hx]
  · have hp : 0<(H:ℝ)*x := by linarith
    have hx0 : 0<x := by by_contra! hh; have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α:=ℝ) H) hh; linarith
    let L := (2*(H:ℝ)+1)*Real.pi
    have hL : (H:ℝ)≤L := by dsimp [L]; nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) H) (sub_nonneg.mpr Real.pi_gt_three.le),Real.pi_gt_three,Nat.cast_nonneg (α:=ℝ) H]
    have hsin := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hx)
      (show Real.pi*x≤Real.pi/2 by nlinarith only [mul_le_mul_of_nonneg_left hx' Real.pi_pos.le])
    rw [show 2/Real.pi*(Real.pi*x)=2*x by field_simp] at hsin
    have hden := mul_le_mul hL hsin (mul_nonneg (by norm_num) hx) (by dsimp [L]; positivity)
    apply (sawtooth_fourier_midpoint hx0 hx').trans
    apply (div_le_div_iff₀ (by
      change 0<L*Real.sin (Real.pi*x); nlinarith only [hden,hp]) (by positivity)).mpr
    change 2*(1+(H:ℝ)*x)≤6*(L*Real.sin (Real.pi*x))
    nlinarith only [hden,hp,not_le.mp h]

private theorem sawtoothSineSum_periodic (H : ℕ) (x : ℝ) (j : ℤ) :
    sawtoothSineSum H (x+j)=sawtoothSineSum H x := by
  unfold sawtoothSineSum
  apply Finset.sum_congr rfl; intro n _
  rw [show 2*Real.pi*n*(x+j)=2*Real.pi*n*x+((n:ℤ)*j:ℤ)*(2*Real.pi) by push_cast; ring,
    Real.sin_add_int_mul_two_pi]

private theorem sawtoothSineSum_reflect (H : ℕ) (x : ℝ) :
    sawtoothSineSum H (1-x) = -sawtoothSineSum H x := by
  rw [show 1-x=-x+(1:ℤ) by push_cast; ring,sawtoothSineSum_periodic]
  unfold sawtoothSineSum; rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro n _; rw [mul_neg,Real.sin_neg,neg_div]

/-- Pointwise truncation of the sawtooth Fourier series, valid also at
the jump discontinuities, with no excluded frequencies or endpoints. -/
theorem abs_sawtooth_add_sineSum_le (H : ℕ) (x : ℝ) :
    |sawtooth x+sawtoothSineSum H x| ≤ 6/(1+(H:ℝ)*distToInt x) := by
  let y := Int.fract x
  have hy : 0≤y := Int.fract_nonneg x
  have hy' : y<1 := Int.fract_lt_one x
  have hper : sawtoothSineSum H x=sawtoothSineSum H y := by
    simpa only [y,Int.fract_add_floor] using sawtoothSineSum_periodic H y ⌊x⌋
  rw [hper,distToInt_eq_min]
  change |y-1/2+sawtoothSineSum H y| ≤ 6/(1+(H:ℝ)*min y (1-y))
  by_cases h : y≤1/2
  · rw [min_eq_left (by linarith)]; exact sawtooth_fourier_near hy h H
  · rw [min_eq_right (by linarith)]
    have H' := sawtooth_fourier_near (sub_nonneg.mpr hy'.le) (by linarith : 1-y≤1/2) H
    rw [sawtoothSineSum_reflect,show 1-y-1/2+ -sawtoothSineSum H y= -(y-1/2+sawtoothSineSum H y) by ring,abs_neg] at H'
    exact H'

end AnalyticNumberTheory.DivisorProblems
