import AnalyticNumberTheory.SieveMethods.LinearSieveMonotonicity

/-!
# Contraction of the two-prime linear sieve kernel

An accepted pair in the lower sieve satisfies log p₁ + 3 log p₂ < Y.
After passage to the inverse logarithmic variable the associated integral
has operator norm bounded by 9/10 with exponential weight. A rational
majorant suffices to make the contraction strict.
-/
noncomputable section
open Real Set MeasureTheory
namespace AnalyticNumberTheory.SieveMethods

private theorem log_sym_bounds {x : ℝ} (hx : 1≤x) :
    2*(x-1)/(x+1)≤log x ∧ log x≤(x-x⁻¹)/2 := by
  let F := fun t : ℝ => log t-2*(t-1)/(t+1)
  let G := fun t : ℝ => (t-t⁻¹)/2-log t
  have hF (t : ℝ) (ht : 0<t) : HasDerivAt F ((t-1)^2/(t*(t+1)^2)) t := by
    have h := (Real.hasDerivAt_log ht.ne').sub ((((hasDerivAt_id' t).sub_const 1).const_mul 2).div
      ((hasDerivAt_id' t).add_const 1) (by linarith))
    convert h using 1
    field_simp [ht.ne',show t+1≠0 by linarith]; ring
  have hG (t : ℝ) (ht : 0<t) : HasDerivAt G ((t-1)^2/(2*t^2)) t := by
    have h := (((hasDerivAt_id' t).sub ((hasDerivAt_id' t).inv ht.ne')).div_const 2).sub (Real.hasDerivAt_log ht.ne')
    convert h using 1
    field_simp [ht.ne']; ring
  have hm (f d : ℝ → ℝ) (hd : ∀t : ℝ, 0<t → HasDerivAt f (d t) t)
      (hn : ∀t : ℝ,0<t → 0≤d t) : f 1≤f x := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (1:ℝ)) _ _ _ (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
    · exact fun t ht => (hd t (zero_lt_one.trans_le ht)).continuousAt.continuousWithinAt
    · rw [interior_Ici]; exact fun t ht => (hd t (zero_lt_one.trans ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro t ht; rw [(hd t (zero_lt_one.trans ht)).deriv]; exact hn t (zero_lt_one.trans ht)
  have hh₁ := hm F _ hF (fun t ht => by positivity)
  have hh₂ := hm G _ hG (fun t ht => by positivity)
  simp [F,G] at hh₁ hh₂
  exact ⟨hh₁,hh₂⟩

private theorem rational_contraction {u : ℝ} (hu : 2≤u) (hu' : u≤4) :
    exp (u-2)/u*(log (3/(u-1))+1/3)≤9/10 := by
  have hp : 0<u-1 := by linarith
  have hp' : 0<6-u := by linarith
  have hv : 1≤(u+2)/(6-u) := (one_le_div hp').mpr (by linarith)
  have h₀ := (log_sym_bounds hv).1
  have hh : 2*(u+2)/(6-u)+2≠0 := by positivity
  have hden : (u+2)/(6-u)+1≠0 := by linarith
  have hr : 2*((u+2)/(6-u)-1)/((u+2)/(6-u)+1)=(u-2)/2 := by
    field_simp [hp'.ne',hden]; ring
  rw [hr] at h₀
  have he : exp (u-2)≤((u+2)/(6-u))^2 := by
    rw [←Real.exp_log (show 0<(u+2)/(6-u) by positivity),←Real.exp_nat_mul,Real.exp_le_exp]
    push_cast; linarith
  have hl := (log_sym_bounds (show (1:ℝ)≤3/(u-1) from (one_le_div hp).mpr (by linarith))).2
  have hlog : 0≤log (3/(u-1))+1/3 := add_nonneg (Real.log_nonneg ((one_le_div hp).mpr (by linarith))) (by norm_num)
  apply (mul_le_mul (div_le_div_of_nonneg_right he (by linarith)) (add_le_add_left hl _) hlog (by positivity)).trans
  rw [inv_div]
  have hc : 0≤64*(4-u)^4+1184*(u-2)*(4-u)^3+2640*(u-2)^2*(4-u)^2+
      1224*(u-2)^3*(4-u)+216*(u-2)^4 := by positivity [sub_nonneg.mpr hu,sub_nonneg.mpr hu']
  field_simp [hp.ne',hp'.ne',show 0<u by linarith]
  nlinarith only [hc]

/-- Continuum kernel after summing over the second prime. -/
def linearSievePairKernel (t : ℝ) : ℝ := exp (-(max 3 (t-1)))/(t-1)

theorem linearSievePairKernel_integrable {u : ℝ} (hu : 2≤u) : IntegrableOn linearSievePairKernel (Ioi u) := by
  apply ((integrableOn_exp_neg_Ioi u).const_mul (exp 1)).mono' (by apply Measurable.aestronglyMeasurable; unfold linearSievePairKernel; fun_prop)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  have ht' : 1≤t-1 := by linarith [mem_Ioi.mp ht]
  rw [linearSievePairKernel,Real.norm_eq_abs,abs_of_nonneg (by positivity [zero_lt_one.trans_le ht']),←Real.exp_add]
  apply (div_le_self (exp_pos _).le ht').trans
  exact Real.exp_le_exp.mpr (by linarith [le_max_right (3:ℝ) (t-1)])

private theorem kernel_tail {u : ℝ} (hu : 4≤u) :
    (∫t in Ioi u,linearSievePairKernel t)≤exp (1-u)/(u-1) := by
  have hi := (integrableOn_exp_neg_Ioi u).const_mul (exp 1/(u-1))
  have hh := setIntegral_mono_on (linearSievePairKernel_integrable (by linarith : 2≤u)) hi measurableSet_Ioi
    (fun t (ht : t∈Ioi u) => by
      rw [linearSievePairKernel,max_eq_right (by linarith [mem_Ioi.mp ht] : (3:ℝ)≤t-1)]
      rw [show -(t-1)=1+ -t by ring,Real.exp_add]
      calc exp 1*exp (-t)/(t-1)≤exp 1*exp (-t)/(u-1) := by gcongr <;> linarith [mem_Ioi.mp ht]
           _ = _ := by ring)
  rw [integral_const_mul,integral_exp_neg_Ioi] at hh
  rw [show exp (1-u)/(u-1)=exp 1/(u-1)*exp (-u) by rw [Real.exp_sub,Real.exp_neg]; ring]
  exact hh

/-- Explicit contraction, uniform for all u≥2. -/
theorem linearSieve_pair_integral {u : ℝ} (hu : 2≤u) :
    exp 1*(∫t in Ioi u,linearSievePairKernel t) ≤ (9/10:ℝ)*u*exp (-u) := by
  have hpos : 0<u := by linarith
  by_cases h : 4≤u
  · apply (mul_le_mul_of_nonneg_left (kernel_tail h) (exp_pos _).le).trans
    have he : exp (2:ℝ)≤9 := by
      rw [show (2:ℝ)=(2:ℕ)*1 by norm_num,Real.exp_nat_mul]
      have hE := Real.exp_one_lt_d9
      nlinarith only [sq_nonneg (exp 1-2.72),mul_self_le_mul_self (exp_pos 1).le (show exp 1≤3 by linarith)]
    have hp : exp (2:ℝ)/(u-1)≤9/10*u := (div_le_iff₀ (by linarith)).mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0≤u-1 by linarith)])
    apply le_trans _ (mul_le_mul_of_nonneg_right hp (exp_pos _).le)
    rw [show 1-u=1+ -u by ring,Real.exp_add,show (2:ℝ)=1+1 by norm_num,Real.exp_add]; ring_nf
    exact le_rfl
  have hu' := (not_le.mp h).le
  have hint : (∫t in u..4,linearSievePairKernel t)=exp (-3)*log (3/(u-1)) := by
    calc _ = ∫t in u..4,exp (-3)*(t-1)⁻¹ := by
          apply intervalIntegral.integral_congr; intro t ht; rw [uIcc_of_le hu'] at ht
          simp only [linearSievePairKernel,max_eq_left (by linarith [ht.2] : t-1≤3),div_eq_mul_inv]
         _ = _ := by
          rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right (fun t : ℝ => t⁻¹) 1,
            integral_inv_of_pos (by linarith) (by norm_num)]
          norm_num
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (linearSievePairKernel_integrable hu) hu'
  rw [hint] at hsplit
  have hh := kernel_tail (u:=4) le_rfl
  norm_num at hh
  have hraw : (∫t in Ioi u,linearSievePairKernel t)≤exp (-3)*(log (3/(u-1))+1/3) := by linarith
  apply (mul_le_mul_of_nonneg_left hraw (exp_pos _).le).trans
  have hnum := rational_contraction hu hu'
  rw [div_mul_eq_mul_div,div_le_iff₀ hpos] at hnum
  apply le_trans _ (mul_le_mul_of_nonneg_right hnum (exp_pos (-u)).le)
  rw [show u-2=u+(-2) by ring,Real.exp_add,Real.exp_neg u]
  have he : exp 1*exp (-3)=exp (-2:ℝ) := by rw [←Real.exp_add]; norm_num
  field_simp [Real.exp_ne_zero]; rw [he,mul_comm]
end AnalyticNumberTheory.SieveMethods
