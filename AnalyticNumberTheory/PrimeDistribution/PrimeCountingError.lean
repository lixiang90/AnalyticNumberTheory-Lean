import AnalyticNumberTheory.PrimeDistribution.VonKoch

/-!
# The prime counting error and the Riemann hypothesis

Abel summation transfers the von Koch bound to θ and π. In the reverse direction
the same summation formula recovers the Chebyshev error from the prime count.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Asymptotics Topology
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The logarithmic integral normalized at 2 has derivative 1/log x for x>1. -/
theorem hasDerivAt_logIntegral {x : ℝ} (hx : 1 < x) :
    HasDerivAt logIntegral (Real.log x)⁻¹ x := by
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Ioi 1) :=
    (Real.continuousOn_log.mono (fun t ht => (by linarith [show 1 < t from ht] : 0 < t).ne')).inv₀
      (fun _ ht => (Real.log_pos ht).ne')
  have hsub : uIcc (2 : ℝ) x ⊆ Ioi 1 := fun _ ht => (lt_min (by norm_num) hx).trans_le ht.1
  have hint := (hcont.mono hsub).intervalIntegrable (μ := volume)
  exact intervalIntegral.integral_hasDerivAt_right hint
    Real.measurable_log.inv.stronglyMeasurable.stronglyMeasurableAtFilter
    (hcont.continuousAt (Ioi_mem_nhds hx))

/-- Reverse Abel error identity for the same lower endpoint 2 used in logIntegral. -/
theorem theta_sub_id_eq_primePi_error_abel {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.theta x-x = (primePi x-logIntegral x)*Real.log x -
      (∫ t in (2 : ℝ)..x, (primePi t-logIntegral t)/t) - 2 := by
  have ht₁ {t : ℝ} (ht : t ∈ uIcc (2 : ℝ) x) : 1 < t := by
    rw [uIcc_of_le hx] at ht
    linarith [ht.1]
  have hi : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 2 x) :=
    continuousOn_id.inv₀ (fun _ ht => (zero_lt_one.trans (ht₁ ht)).ne')
  have hl : ContinuousOn logIntegral (uIcc 2 x) := fun _ ht =>
    (hasDerivAt_logIntegral (ht₁ ht)).continuousAt.continuousWithinAt
  have hli : IntervalIntegrable (fun t => logIntegral t/t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hl t ht).div continuousWithinAt_id (zero_lt_one.trans (ht₁ ht)).ne'
  have hpi : IntervalIntegrable (fun t => primePi t/t) volume 2 x := by
    simpa only [div_eq_mul_inv,Pi.mul_apply] using (primePi_mono.intervalIntegrable (μ := volume) (a := 2) (b := x)).mul_continuousOn hi
  have hd (t : ℝ) (ht : t ∈ uIcc (2 : ℝ) x) :
      HasDerivAt (fun y => logIntegral y*Real.log y-y) (logIntegral t/t) t := by
    have hp := ht₁ ht
    apply (((hasDerivAt_logIntegral hp).mul (Real.hasDerivAt_log (zero_lt_one.trans hp).ne')).fun_sub
      (hasDerivAt_id' t)).congr_deriv
    field_simp [(Real.log_pos hp).ne']
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hli
  have h₂ : logIntegral 2 = 0 := by simp [logIntegral]
  rw [h₂,zero_mul,zero_sub] at hFTC
  simp only [sub_div]
  rw [intervalIntegral.integral_sub hpi hli,theta_eq_primePi_mul_log_sub_integral hx,hFTC]
  ring

/-- A power bound for the ψ error transfers to θ with the same logarithmic factor,
uniformly for every x ≥ 2. -/
theorem abs_theta_sub_id_le_zetaSupRe_log_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.theta x-x| ≤ C*(x^zetaSupRe*(Real.log x)^2) := by
  obtain ⟨C,hC,H⟩ := abs_psi_sub_id_le_zetaSupRe_log_sq
  let D := (Real.log 4+4)*3
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C+4*D,by positivity,?_⟩
  intro x hx
  have hl : 1/2 ≤ Real.log x := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hx)
  have hsq : 1 ≤ 4*(Real.log x)^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) hl]
  have hx₀ : 0 ≤ x^zetaSupRe := Real.rpow_nonneg (by linarith) _
  have hs : Real.sqrt x ≤ x^zetaSupRe := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) half_le_zetaSupRe
  calc
    _ = |(Chebyshev.psi x-x)-(Chebyshev.psi x-Chebyshev.theta x)| := by congr 1; ring
    _ ≤ |Chebyshev.psi x-x| + |Chebyshev.psi x-Chebyshev.theta x| := abs_sub _ _
    _ ≤ C*(x^zetaSupRe*(Real.log x)^2) + D*Real.sqrt x := add_le_add (H x hx) (abs_psi_sub_theta_le_mul_sqrt x)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hs hD.le,
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hD.le hx₀)]

private theorem integral_abs_bound_rpow {x β C : ℝ} (hx : 2 ≤ x) (hβ : 0 < β) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (H : ∀ t ∈ Ioc (2:ℝ) x, |f t| ≤ C*t^(β-1)) :
    |∫ t in (2:ℝ)..x, f t| ≤ C*x^β/β := by
  have hi : IntervalIntegrable (fun t : ℝ => C*t^(β-1)) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (show t ≠ 0 from (zero_lt_two.trans_le ht.1).ne')))
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := f) hx
    (Filter.Eventually.of_forall (fun t ht => by simpa only [Real.norm_eq_abs] using H t ht)) hi
  rw [intervalIntegral.integral_const_mul, integral_rpow (.inl (by linarith)),
    show β-1+1 = β by ring, Real.norm_eq_abs] at h
  apply h.trans
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.rpow_nonneg (by norm_num) _)) hC) hβ.le

set_option maxHeartbeats 600000 in
/-- With Θ the supremal zero real part, the usual inclusive prime count differs from
the logarithmic integral by O(x^Θ log x), uniformly for all x ≥ 2. -/
theorem abs_primePi_sub_logIntegral_le_zetaSupRe_log :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |primePi x-logIntegral x| ≤ C*(x^zetaSupRe*Real.log x) := by
  obtain ⟨C,hC,H⟩ := abs_theta_sub_id_le_zetaSupRe_log_sq
  let d := 2/Real.log 2
  have hd : 0 < d := div_pos two_pos (Real.log_pos one_lt_two)
  refine ⟨5*C+2*d,by positivity,?_⟩
  intro x hx
  let β := zetaSupRe
  have hβ : 1/2 ≤ β := half_le_zetaSupRe
  have hβ₀ : 0 < β := by linarith
  have hl : 1/2 ≤ Real.log x := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hx)
  have hl₀ : 0 < Real.log x := by linarith
  have hxβ : 1 ≤ x^β := Real.one_le_rpow (by linarith) hβ₀.le
  have hmain : |(Chebyshev.theta x-x)/Real.log x| ≤ C*(x^β*Real.log x) := by
    rw [abs_div,abs_of_pos hl₀, div_le_iff₀ hl₀]
    apply (H x hx).trans_eq
    ring
  have hi := integral_abs_bound_rpow hx hβ₀ hC.le (f := fun t => (Chebyshev.theta t-t)/(t*(Real.log t)^2))
    (fun t ht => by
      have ht₀ : 0 < t := by linarith [ht.1]
      have hlog := Real.log_pos (by linarith [ht.1] : 1 < t)
      rw [abs_div,abs_of_pos (mul_pos ht₀ (sq_pos_of_pos hlog)), div_le_iff₀ (mul_pos ht₀ (sq_pos_of_pos hlog))]
      apply (H t ht.1.le).trans_eq
      rw [Real.rpow_sub_one ht₀.ne']
      field_simp
      rfl)
  have hi' : C*x^β/β ≤ 2*C*x^β := by
    rw [div_le_iff₀ hβ₀]
    nlinarith only [mul_le_mul_of_nonneg_left hβ (show 0 ≤ 2*C*x^β by positivity)]
  have hprod : 1/2 ≤ x^β*Real.log x := by nlinarith [mul_le_mul_of_nonneg_left hxβ hl₀.le]
  rw [show primePi x-logIntegral x = _ from primePi_sub_li_eq_theta_sub_id_abel hx]
  calc
    _ ≤ (|(Chebyshev.theta x-x)/Real.log x|+|d|) +
        |∫ t in (2:ℝ)..x, (Chebyshev.theta t-t)/(t*(Real.log t)^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ C*(x^β*Real.log x)+d+2*C*x^β := by
      rw [abs_of_pos hd]; exact add_le_add (add_le_add hmain (le_refl _)) (hi.trans hi')
    _ ≤ (5*C+2*d)*(x^β*Real.log x) := by
      have hxpos : 0 ≤ 4*C*x^β := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hprod hd.le, mul_le_mul_of_nonneg_left hl hxpos]

/-- The RH prime-counting estimate in its usual square-root times one logarithm form. -/
theorem primePi_error_isBigO_sqrt_log_of_rh (hRH : RiemannHypothesisProp) :
    (fun x : ℝ => primePi x-logIntegral x) =O[atTop] fun x : ℝ => Real.sqrt x*Real.log x := by
  obtain ⟨C,_,H⟩ := abs_primePi_sub_logIntegral_le_zetaSupRe_log
  have hs := zetaSupRe_eq_half_iff_riemannHypothesis.mpr (riemannHypothesisProp_iff_mathlib.mp hRH)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  have hl := Real.log_nonneg (by linarith : 1 ≤ x)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) hl),hs,← Real.sqrt_eq_rpow] using H x hx

private theorem sqrt_isBigO_sqrt_log_sq :
    Real.sqrt =O[atTop] fun x : ℝ => Real.sqrt x*(Real.log x)^2 := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
  have hsq : 1 ≤ (Real.log x)^2 := by nlinarith [sq_nonneg (Real.log x-1)]
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log x))),one_mul] using
    le_mul_of_one_le_right (Real.sqrt_nonneg x) hsq

/-- RH is equivalent to the square-root times log² error for the sum of log p over primes. -/
theorem riemannHypothesisProp_iff_theta_error_isBigO_sqrt_log_sq :
    RiemannHypothesisProp ↔ (fun x : ℝ => Chebyshev.theta x-x) =O[atTop]
      fun x : ℝ => Real.sqrt x*(Real.log x)^2 := by
  rw [riemannHypothesisProp_iff_psi_error_isBigO_sqrt_log_sq]
  have hg := psi_sub_theta_isBigO_sqrt.trans sqrt_isBigO_sqrt_log_sq
  constructor
  · intro h
    have he (x : ℝ) : Chebyshev.theta x-x = (Chebyshev.psi x-x)-(Chebyshev.psi x-Chebyshev.theta x) := by ring
    simp_rw [he]
    exact h.sub hg
  · intro h
    have he (x : ℝ) : Chebyshev.psi x-x = (Chebyshev.theta x-x)+(Chebyshev.psi x-Chebyshev.theta x) := by ring
    simp_rw [he]
    exact h.add hg

private theorem uniform_primePi_error_of_isBigO
    (H : (fun x : ℝ => primePi x-logIntegral x) =O[atTop] fun x : ℝ => Real.sqrt x*Real.log x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → |primePi x-logIntegral x| ≤ C*(Real.sqrt x*Real.log x) := by
  obtain ⟨D,hD⟩ := Asymptotics.isBigO_iff.mp H
  obtain ⟨T,hT⟩ := eventually_atTop.mp hD
  let U := max 2 T
  have hc : ContinuousOn logIntegral (Icc 2 U) := fun _ hx =>
    (hasDerivAt_logIntegral (one_lt_two.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let C := max (max 1 D) (2*(primePi U + |M|))
  have hC₁ : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC := zero_lt_one.trans_le hC₁
  refine ⟨C,hC,?_⟩
  intro x hx
  have hl : 1/2 ≤ Real.log x := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hx)
  have hsq : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  have hq : 1/2 ≤ Real.sqrt x*Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (show 0 ≤ Real.log x by linarith)]
  rcases le_or_gt T x with hxT | hxT
  · have ho := hT x hxT
    simp only [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x*Real.log x)] at ho
    exact ho.trans (mul_le_mul_of_nonneg_right ((le_max_right 1 D).trans (le_max_left _ _)) (by linarith))
  · have hxu : x ≤ U := hxT.le.trans (le_max_right _ _)
    have hm := hM x ⟨hx,hxu⟩
    rw [Real.norm_eq_abs] at hm
    have hlocal := (abs_sub (primePi x) (logIntegral x)).trans (add_le_add
      ((abs_of_nonneg (primePi_nonneg x)).le.trans (primePi_mono hxu)) (hm.trans (le_abs_self M)))
    have hb : 2*(primePi U+|M|) ≤ C := le_max_right _ _
    apply hlocal.trans
    nlinarith only [hb,mul_le_mul_of_nonneg_left hq hC.le]

/-- The prime-counting form of von Koch's criterion, with the logarithmic integral based
at 2 and the inclusive count at every prime. -/
theorem riemannHypothesisProp_iff_primePi_error_isBigO_sqrt_log :
    RiemannHypothesisProp ↔ (fun x : ℝ => primePi x-logIntegral x) =O[atTop]
      fun x : ℝ => Real.sqrt x*Real.log x := by
  refine ⟨primePi_error_isBigO_sqrt_log_of_rh,?_⟩
  intro H
  obtain ⟨C,hC,HC⟩ := uniform_primePi_error_of_isBigO H
  apply riemannHypothesisProp_iff_theta_error_isBigO_sqrt_log_sq.mpr
  refine Asymptotics.IsBigO.of_bound (5*C+8) ?_
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  have hL : 1/2 ≤ Real.log x := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hx)
  have hl : 0 ≤ Real.log x := by linarith
  have hX := Real.one_le_sqrt.mpr (show 1 ≤ x by linarith)
  let Q := Real.sqrt x*(Real.log x)^2
  have hQ : (Real.log x)^2 ≤ Q := le_mul_of_one_le_left (sq_nonneg _) hX
  have hQ₁ : 1 ≤ 4*Q := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) hL]
  have hQ₂ : Real.sqrt x*Real.log x ≤ 2*Q := by
    have hh : Real.log x ≤ 2*(Real.log x)^2 := by nlinarith [mul_nonneg hl (by linarith : 0 ≤ 2*Real.log x-1)]
    dsimp only [Q]
    nlinarith only [mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg x)]
  have hi := integral_abs_bound_rpow hx (by norm_num : (0:ℝ) < 1/2) (mul_nonneg hC.le hl)
    (f := fun t => (primePi t-logIntegral t)/t) (fun t ht => by
      have ht₀ := zero_lt_two.trans ht.1
      rw [abs_div,abs_of_pos ht₀,Real.rpow_sub_one ht₀.ne',← Real.sqrt_eq_rpow,div_le_iff₀ ht₀]
      apply (HC t ht.1.le).trans
      have hmono := Real.log_le_log ht₀ ht.2
      have he : C*(Real.sqrt t*Real.log x) = C*Real.log x*(Real.sqrt t/t)*t := by field_simp
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg t)) hC.le).trans_eq he)
  rw [← Real.sqrt_eq_rpow] at hi
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log x)))]
  rw [theta_sub_id_eq_primePi_error_abel hx]
  calc
    _ ≤ |(primePi x-logIntegral x)*Real.log x|+
        |∫ t in (2:ℝ)..x, (primePi t-logIntegral t)/t|+2 :=
      (abs_sub _ _).trans (by rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]; gcongr; exact abs_sub _ _)
    _ ≤ (5*C+8)*Q := by
      rw [abs_mul,abs_of_nonneg hl]
      have hfirst : |primePi x-logIntegral x| * Real.log x ≤ C*Q := by
        apply (mul_le_mul_of_nonneg_right (HC x hx) hl).trans_eq
        dsimp only [Q]; ring
      nlinarith only [hfirst,hi,mul_le_mul_of_nonneg_left hQ₂ (show 0 ≤ 2*C by positivity),hQ₁]

end AnalyticNumberTheory.PrimeDistribution
