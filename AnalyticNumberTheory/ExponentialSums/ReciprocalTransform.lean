import AnalyticNumberTheory.ExponentialSums.ReciprocalStationaryPhase
import AnalyticNumberTheory.ExponentialSums.SharpPoissonSummation

/-!
# The reciprocal-phase van der Corput transform

The saddle of the phase `A/t+v*t` lies at `√(A/v)`. Its main term has
amplitude `A^(1/4) v^(-3/4)` and phase `2√(Av)`.
-/

open Real Complex MeasureTheory Set
namespace AnalyticNumberTheory.ExponentialSums

/-- The oscillatory contribution of the positive saddle. -/
noncomputable def reciprocalSaddleTerm (A v : ℝ) : ℂ :=
  e (2*Real.sqrt (A*v)) *
    ((A^(1/4:ℝ)*v^(-(3/4):ℝ):ℝ):ℂ) * ((1+Complex.I)/2)

private theorem saddle_term_normalization {r v : ℝ} (hr : 0<r) (hv : 0<v) :
    reciprocalSaddleTerm (v*r^2) v =
      e (2*v*r)*(Real.sqrt r:ℂ)*((Real.sqrt v)⁻¹:ℝ)*((1+Complex.I)/2) := by
  have hs : Real.sqrt (v*r^2*v)=v*r := by
    rw [show v*r^2*v=(v*r)^2 by ring,Real.sqrt_sq (mul_nonneg hv.le hr.le)]
  have hpow : (v*r^2)^(1/4:ℝ)*v^(-(3/4):ℝ)=Real.sqrt r*(Real.sqrt v)⁻¹ := by
    rw [Real.mul_rpow hv.le (sq_nonneg r), ←Real.rpow_natCast r 2,←Real.rpow_mul hr.le,
      show ((2:ℕ):ℝ)*(1/4)=1/2 by norm_num, ←Real.sqrt_eq_rpow]
    rw [mul_right_comm,←Real.rpow_add hv,show (1:ℝ)/4+ -(3/4) = -(1/2) by norm_num,
      Real.rpow_neg hv.le,←Real.sqrt_eq_rpow,mul_comm]
  unfold reciprocalSaddleTerm; rw [hs,hpow,Complex.ofReal_mul,mul_assoc (2:ℝ)]; ring

/-- The modulus of an endpoint contribution is at most the reciprocal
square root of the local curvature scale. -/
theorem norm_reciprocalSaddleTerm_at_slope_le {A t : ℝ} (hA : 0<A) (ht : 0<t) :
    ‖reciprocalSaddleTerm A (A/t^2)‖ ≤ Real.sqrt (t^3/A) := by
  let v := A/t^2
  have hv : 0<v := by dsimp [v]; positivity
  have he : v*t^2=A := div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')
  have H := saddle_term_normalization ht hv
  rw [he] at H
  change ‖reciprocalSaddleTerm A v‖≤_
  rw [H,norm_mul,norm_mul,norm_mul,norm_e,one_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.norm_of_nonneg (by positivity : 0≤(Real.sqrt v)⁻¹)]
  have hc : ‖(1+Complex.I)/2‖≤1 := by
    rw [norm_div]; norm_num
    have h := norm_add_le (1:ℂ) Complex.I
    simp only [norm_one,Complex.norm_I] at h; linarith
  apply (mul_le_of_le_one_right (by positivity) hc).trans_eq
  rw [←div_eq_mul_inv,←Real.sqrt_div ht.le]
  congr 1; dsimp [v]; field_simp

private theorem saddle_endpoint_error {r v t : ℝ} (hr : 0<r) (hv : 0<v)
    (ht : 0<t) (hrt : r≤2*t) :
    (Real.sqrt r*(Real.sqrt v)⁻¹) * (3/(1+Real.sqrt v*|reciprocalSaddleCoordinate r t|)) ≤
      18*(1+Real.sqrt r*(Real.sqrt v)⁻¹)/(1+|v-v*r^2/t^2|) := by
  let M := Real.sqrt r*(Real.sqrt v)⁻¹
  let d := Real.sqrt v*|reciprocalSaddleCoordinate r t|
  let h := |v-v*r^2/t^2|
  have hM : 0≤M := by dsimp [M]; positivity
  have hd : 0≤d := by dsimp [d]; positivity
  have hh : 0≤h := abs_nonneg _
  have hsr := Real.sqrt_pos.mpr hr
  have hst := Real.sqrt_pos.mpr ht
  have hsv := Real.sqrt_pos.mpr hv
  have h₁ : Real.sqrt r/Real.sqrt t≤2 := by
    apply (div_le_iff₀ hst).mpr
    nlinarith only [Real.sq_sqrt hr.le,Real.sq_sqrt ht.le,hrt,ht,hsr,hst,sq_nonneg (Real.sqrt r-2*Real.sqrt t)]
  have h₂ : (t+r)/t≤3 := (div_le_iff₀ ht).mpr (by linarith)
  have hdist : h = v*|t-r| *(t+r)/t^2 := by
    dsimp only [h]
    rw [show v-v*r^2/t^2=v*(t-r)*(t+r)/t^2 by field_simp; ring,
      abs_div,abs_mul,abs_mul,abs_of_pos hv,abs_of_pos (add_pos ht hr),abs_of_nonneg (sq_nonneg t)]
  have hid : M*h = d*((Real.sqrt r/Real.sqrt t)*((t+r)/t)) := by
    rw [hdist]
    dsimp only [M,d,reciprocalSaddleCoordinate]
    rw [abs_div,abs_of_pos hst]
    field_simp
    ring_nf; rw [Real.sq_sqrt ht.le,Real.sq_sqrt hv.le]; ring
  have hmh : M*h≤d*6 := by
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ hd
    exact (mul_le_mul h₁ h₂ (by positivity) (by norm_num)).trans_eq (by norm_num)
  change M*(3/(1+d))≤18*(1+M)/(1+h)
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hmh,hM,hd,mul_nonneg hM hd]

/-- The saddle asymptotic in the spectral coordinate.  On a dyadic
interval the endpoint errors decrease with the distance of the frequency
to the two endpoint slopes. -/
theorem reciprocal_saddle_integral_bound {a b r v : ℝ} (ha : 0<a) (har : a≤r)
    (hrb : r≤b) (hba : b≤2*a) (hv : 0<v) :
    ‖(∫ t in a..b,e ((v*r^2)/t+v*t)) - reciprocalSaddleTerm (v*r^2) v‖ ≤
      1/(Real.pi*v) + 18*(1+Real.sqrt r*(Real.sqrt v)⁻¹)*
        (1/(1+|v-v*r^2/a^2|)+1/(1+|v-v*r^2/b^2|)) := by
  have hr := ha.trans_le har
  have hb := hr.trans_le hrb
  have hL : reciprocalSaddleCoordinate r a≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr har) (Real.sqrt_nonneg _)
  have hR : 0≤reciprocalSaddleCoordinate r b := div_nonneg (sub_nonneg.mpr hrb) (Real.sqrt_nonneg _)
  have H := reciprocal_stationary_phase ha har hrb hv
  have L := saddle_endpoint_error hr hv ha (hrb.trans hba)
  have R := saddle_endpoint_error hr hv hb (by linarith)
  rw [abs_of_nonpos hL,mul_neg,←sub_eq_add_neg] at L
  rw [abs_of_nonneg hR] at R
  rw [saddle_term_normalization hr hv,show (fun t : ℝ => e ((v*r^2)/t+v*t))=(fun t : ℝ => e (v*(t+r^2/t))) by funext t; congr 1; ring]
  apply H.trans; rw [mul_add (Real.sqrt r*(Real.sqrt v)⁻¹),mul_add (18*(1+Real.sqrt r*(Real.sqrt v)⁻¹))]
  rw [mul_one_div,mul_one_div]
  linarith only [L,R]

private theorem reciprocal_phase_derivatives {a b : ℝ} (ha : 0<a) (A v : ℝ) :
    (∀ t∈Icc a b,HasDerivAt (fun u : ℝ => 2*Real.pi*(A/u+v*u))
      (2*Real.pi*(v-A/t^2)) t) ∧
    (∀ t∈Icc a b,HasDerivAt (fun u : ℝ => 2*Real.pi*(v-A/u^2))
      (4*Real.pi*A/t^3) t) ∧ ContinuousOn (fun t : ℝ => 4*Real.pi*A/t^3) (Icc a b) := by
  have hp {t : ℝ} (ht : t∈Icc a b) := ha.trans_le ht.1
  refine ⟨?_,?_,ContinuousOn.div (f:=fun _ : ℝ => 4*Real.pi*A) (g:=fun t : ℝ => t^3) continuousOn_const (continuousOn_id.pow 3) (fun t ht => pow_ne_zero 3 (hp ht).ne')⟩
  · intro t ht
    have h : HasDerivAt (fun u : ℝ => A/u) (-A/t^2) t := by
      simpa only [id_eq,zero_mul,mul_one,zero_sub] using
        (hasDerivAt_const t A).fun_div (hasDerivAt_id t) (hp ht).ne'
    apply ((h.fun_add ((hasDerivAt_id t).const_mul v)).const_mul (2*Real.pi)).congr_deriv
    ring
  · intro t ht
    have h := (hasDerivAt_const t A).fun_div (hasDerivAt_pow 2 t) (pow_ne_zero _ (hp ht).ne')
    apply ((h.const_sub v).const_mul (2*Real.pi)).congr_deriv
    field_simp [(hp ht).ne']; ring

private theorem reciprocal_phase_abs {a b A v : ℝ} (ha : 0<a) (hab : a≤b) (hA : 0<A) :
    ‖∫ t in a..b,e (A/t+v*t)‖ ≤ 8*Real.sqrt (b^3/A) := by
  have hb := ha.trans_le hab
  obtain ⟨h,h',hc⟩ := reciprocal_phase_derivatives (b:=b) ha A v
  have hz : 0<A/b^3 := by positivity
  have H := vanDerCorput_integral_second_deriv hab hz h h' hc (fun t ht => by
    have hp := ha.trans_le ht.1
    rw [abs_of_nonneg (by positivity : 0≤4*Real.pi*A/t^3)]
    have hg : A/b^3≤A/t^3 := by gcongr; exact ht.2
    apply hg.trans; apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hA.le,hA])
  have hid : 8/Real.sqrt (A/b^3)=8*Real.sqrt (b^3/A) := by
    rw [Real.sqrt_div hA.le,Real.sqrt_div (by positivity),div_div_eq_mul_div]; ring
  simpa only [e,Complex.ofReal_mul,Complex.ofReal_ofNat,hid] using H

private theorem reciprocal_phase_first {a b A v δ : ℝ} (ha : 0<a) (hab : a≤b)
    (hA : 0<A) (hδ : 0<δ) (hgap : ∀ t∈Icc a b,δ≤|v-A/t^2|) :
    ‖∫ t in a..b,e (A/t+v*t)‖ ≤ 1/δ := by
  obtain ⟨h,h',hc⟩ := reciprocal_phase_derivatives (b:=b) ha A v
  have H := vanDerCorput_integral_first_deriv hab (show 0<2*Real.pi*δ by positivity) h h' hc
    (Or.inl (fun t ht => by have := ha.trans_le ht.1; positivity))
    (fun t ht => by rw [abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]; gcongr; exact hgap t ht)
  have hb : 4/(2*Real.pi*δ) ≤ 1/δ := by
    apply (div_le_div_iff₀ (by positivity) hδ).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hδ.le,hδ]
  simpa only [e,Complex.ofReal_mul,Complex.ofReal_ofNat] using H.trans hb

/-- The local saddle contribution, with zero main term outside the range
of slopes. Both ends of the frequency window are included. -/
theorem reciprocal_transform_integral {a b A : ℝ} (ha : 0<a) (hab : a≤b) (hba : b≤2*a)
    (hA : 0<A) (v : ℝ) :
    ‖(∫ t in a..b,e (A/t+v*t)) -
      (if A/b^2≤v ∧ v≤A/a^2 then reciprocalSaddleTerm A v else 0)‖ ≤
      (if A/b^2≤v ∧ v≤A/a^2 then 1/(Real.pi*v) else 0) +
      18*(1+Real.sqrt (b^3/A))*(1/(1+|v-A/a^2|)+1/(1+|v-A/b^2|)) := by
  have hb := ha.trans_le hab
  have slope (t : ℝ) (ht : t∈Icc a b) : A/b^2≤A/t^2 ∧ A/t^2≤A/a^2 := by
    have hp := ha.trans_le ht.1
    exact ⟨by gcongr; exact ht.2,by gcongr; exact ht.1⟩
  let G := Real.sqrt (b^3/A)
  have hG : 0≤G := Real.sqrt_nonneg _
  have hnon {δ : ℝ} (hd : 0<δ) (hh : ∀ t∈Icc a b,δ≤|v-A/t^2|) :
      ‖∫ t in a..b,e (A/t+v*t)‖ ≤ 18*(1+G)/(1+δ) := by
    by_cases hs : δ≤1
    · apply (reciprocal_phase_abs ha hab hA).trans
      apply (le_div_iff₀ (by positivity)).mpr
      change 8*G*(1+δ)≤18*(1+G)
      nlinarith only [mul_le_mul_of_nonneg_left hs hG,hG]
    · apply (reciprocal_phase_first ha hab hA hd hh).trans
      apply (div_le_div_iff₀ hd (by positivity)).mpr
      nlinarith only [not_le.mp hs,mul_nonneg hG hd.le]
  split_ifs with H
  · have hv := lt_of_lt_of_le (by positivity : 0<A/b^2) H.1
    let r := Real.sqrt (A/v)
    have hr : 0<r := Real.sqrt_pos.mpr (by positivity)
    have hsq : r^2=A/v := Real.sq_sqrt (by positivity)
    have hA' : v*r^2=A := by rw [hsq]; field_simp
    have har : a≤r := by
      have hh := (le_div_iff₀ (by positivity : 0<a^2)).mp H.2
      by_contra! hlt
      have hh' : r^2<a^2 := by gcongr
      nlinarith only [mul_lt_mul_of_pos_left hh' hv,hA',hh]
    have hrb : r≤b := by
      have hh := (div_le_iff₀ (by positivity : 0<b^2)).mp H.1
      by_contra! hlt
      have hh' : b^2<r^2 := by gcongr
      nlinarith only [mul_lt_mul_of_pos_left hh' hv,hA',hh]
    have hmr : Real.sqrt r*(Real.sqrt v)⁻¹ ≤ G := by
      rw [←div_eq_mul_inv,←Real.sqrt_div hr.le]
      apply Real.sqrt_le_sqrt
      apply (div_le_div_iff₀ hv hA).mpr
      rw [←hA']; nlinarith only [mul_le_mul_of_nonneg_left (show r^3≤b^3 by gcongr) hv.le]
    have H₁ := reciprocal_saddle_integral_bound ha har hrb hba hv
    rw [hA'] at H₁
    apply H₁.trans
    gcongr
  · rw [sub_zero,zero_add]
    rw [not_and_or,not_le,not_le] at H
    rcases H with H|H
    · have he := hnon (sub_pos.mpr H) (fun t ht => by
        rw [abs_of_nonpos (sub_nonpos.mpr (H.le.trans (slope t ht).1))]; linarith [(slope t ht).1])
      rw [abs_of_neg (sub_neg.mpr H),neg_sub,mul_add,mul_one_div,mul_one_div]
      exact he.trans (le_add_of_nonneg_left (by positivity))
    · have he := hnon (sub_pos.mpr H) (fun t ht => by
        rw [abs_of_nonneg (sub_nonneg.mpr ((slope t ht).2.trans H.le))]; linarith [(slope t ht).2])
      rw [abs_of_pos (sub_pos.mpr H),mul_add,mul_one_div,mul_one_div]
      exact he.trans (le_add_of_nonneg_right (by positivity))

end AnalyticNumberTheory.ExponentialSums
