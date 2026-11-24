import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The first moment on a dyadic interval of the critical line

Integrating a Dirichlet polynomial keeps its constant coefficient. Every other
coefficient is divided by its logarithmic frequency. A polynomial of length
`⌈T⌉` therefore approximates the first moment on `[T,2T]` with an error of
order `√T`.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

set_option maxHeartbeats 800000

/-- A telescoping square-root bound for positive coefficients after the constant term. -/
theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Ioc 1 N, (√(n:ℝ))⁻¹ ≤ 2 * √(N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    have h := Finset.sum_Ioc_succ_top (f := fun n : ℕ => (√(n:ℝ))⁻¹) (a := 1) (b := N) (by omega)
    rw [h, Nat.cast_succ]
    have ha := Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    have hb := Real.sq_sqrt (show 0 ≤ (N:ℝ)+1 by positivity)
    have hm : √(N:ℝ) ≤ √((N:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
    have hm' : 0 ≤ (√((N:ℝ)+1)-√(N:ℝ))^2 := sq_nonneg _
    have hh : (√((N:ℝ)+1))⁻¹ ≤ 2*(√((N:ℝ)+1)-√(N:ℝ)) := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith only [ha,hb,hm']
    linarith

private theorem norm_integral_critical_term {n : ℕ} (hn : 1 < n) (a b : ℝ) :
    ‖∫ t in a..b, (n:ℂ)^(-(1/2+(t:ℂ)*I))‖ ≤ (2/Real.log 2)*(√(n:ℝ))⁻¹ := by
  have hnR : (1:ℝ) < n := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog := Real.log_pos hnR
  let c : ℂ := -(Real.log n:ℂ)*I
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlog.ne')) Complex.I_ne_zero
  have he (t : ℝ) : ‖Complex.exp (c*t)‖ = 1 := by
    rw [Complex.norm_exp]
    suffices (c*t).re = 0 by rw [this, Real.exp_zero]
    simp only [c, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have hphase (t : ℝ) : (n:ℂ)^(-(1/2+(t:ℂ)*I)) =
      (n:ℂ)^(-(1/2:ℂ)) * Complex.exp (c*t) := by
    rw [Complex.cpow_def_of_ne_zero hnC, Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_add,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
    congr 1
    dsimp [c]
    ring
  simp_rw [hphase]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc, norm_mul, norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    show (-(1/2:ℂ)).re = -(1/2:ℝ) by norm_num, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have hcn : ‖c‖ = Real.log n := by simp only [c, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  rw [hcn, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc _ ≤ (1+1)/(Real.log n) := div_le_div_of_nonneg_right (by simpa only [he] using norm_sub_le (Complex.exp (c*b)) (Complex.exp (c*a))) hlog.le
       _ ≤ _ := by
         rw [one_add_one_eq_two]
         exact div_le_div_of_nonneg_left (by norm_num) (Real.log_pos (by norm_num))
           (Real.log_le_log (by norm_num) (by exact_mod_cast hn))

/-- First moment of the unweighted critical-line Dirichlet polynomial, on any oriented interval. -/
theorem norm_integral_criticalDirichletPoly_sub_length_le (N : ℕ) (hN : 1 ≤ N) (a b : ℝ) :
    ‖(∫ t in a..b, dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I)) - ((b-a:ℝ):ℂ)‖ ≤
      (4/Real.log 2)*√(N:ℝ) := by
  have hrepr (t : ℝ) : dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I) =
      1 + ∑ n ∈ Ioc 1 N, (n:ℂ)^(-(1/2+(t:ℂ)*I)) := by
    simp [dirichletPoly, Finset.Icc_eq_cons_Ioc hN]
  have hcont (n : ℕ) (hn : n ∈ Ioc 1 N) : Continuous fun t : ℝ => (n:ℂ)^(-(1/2+(t:ℂ)*I)) := by
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1).ne'
    simp_rw [Complex.cpow_def_of_ne_zero hnC]
    fun_prop
  have hi := fun n hn => (hcont n hn).intervalIntegrable (μ := volume) a b
  have hsum : IntervalIntegrable (fun t : ℝ => ∑ n ∈ Ioc 1 N, (n:ℂ)^(-(1/2+(t:ℂ)*I))) volume a b := by
    exact (continuous_finsetSum _ hcont).intervalIntegrable ..
  simp_rw [hrepr]
  rw [intervalIntegral.integral_add intervalIntegrable_const hsum,
    intervalIntegral.integral_finsetSum hi, intervalIntegral.integral_const]
  simp only [Complex.real_smul, mul_one, add_sub_cancel_left]
  calc _ ≤ ∑ n ∈ Ioc 1 N, ‖∫ t in a..b, (n:ℂ)^(-(1/2+(t:ℂ)*I))‖ := norm_sum_le _ _
       _ ≤ ∑ n ∈ Ioc 1 N, (2/Real.log 2)*(√(n:ℝ))⁻¹ :=
         sum_le_sum (fun n hn => norm_integral_critical_term (Finset.mem_Ioc.mp hn).1 a b)
       _ ≤ _ := by
         rw [← Finset.mul_sum, show (4/Real.log 2)*√(N:ℝ) = (2/Real.log 2)*(2*√(N:ℝ)) by ring]
         exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity)


/-- A length-⌈T⌉ Dirichlet sum approximates zeta uniformly on a critical dyadic interval. -/
theorem critical_approx_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T → ∀ t ∈ Set.Icc T (2*T),
      ‖riemannZeta (1/2+(t:ℂ)*I) -
        dirichletPoly (fun _ => 1) ⌈T⌉₊ (1/2+(t:ℂ)*I)‖ ≤ C/√T := by
  obtain ⟨K,hK,h⟩ := riemannZeta_approx_dirichletPoly_sub_bound (c := 2) (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨2+K,by positivity,?_⟩
  intro T hT t ht
  let N := ⌈T⌉₊
  have hT0 : 0 < T := by linarith
  have hTN : T ≤ N := Nat.le_ceil _
  have hN0 : (1:ℝ) ≤ N := hT.trans hTN
  have hN : 1 ≤ N := by exact_mod_cast hN0
  have hN' : (N:ℝ) ≤ 2*T := by linarith [Nat.ceil_lt_add_one hT0.le]
  have hrt : √T ≤ √(N:ℝ) := Real.sqrt_le_sqrt hTN
  have hrt0 := Real.sqrt_pos.mpr hT0
  have hrtN : √(N:ℝ) ≤ 2*√T := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ) ≤ N),Real.sq_sqrt hT0.le, Real.sqrt_nonneg (N:ℝ), Real.sqrt_nonneg T]
  have htt : |t| = t := abs_of_nonneg (hT0.le.trans ht.1)
  have H := h hN (σ := 1/2) (t := t) (by norm_num) (by simpa [htt] using hT.trans ht.1)
    (by rw [htt]; linarith [ht.2])
  rw [show (1-(1/2):ℝ) = 1/2 by norm_num, Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, htt] at H
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at H
  apply H.trans
  have hfirst : √(N:ℝ)/t ≤ (2*√T)/T := div_le_div₀ (by positivity) hrtN hT0 ht.1
  have hsecond := mul_le_mul_of_nonneg_left (inv_anti₀ hrt0 hrt) hK.le
  calc _ ≤ 2*√T/T + K*(√T)⁻¹ := add_le_add hfirst hsecond
       _ = _ := by field_simp; nlinarith [Real.sq_sqrt hT0.le]

/-- The first complex moment of the Riemann zeta function on the critical line equals the
length of the interval, with a square-root error. -/
theorem norm_integral_riemannZeta_half_sub_length_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T →
      ‖(∫ t in T..(2*T), riemannZeta (1/2+(t:ℂ)*I)) - (T:ℂ)‖ ≤ C*√T := by
  obtain ⟨C,hC,h⟩ := critical_approx_dyadic
  refine ⟨C+8/Real.log 2, by positivity,?_⟩
  intro T hT
  let N := ⌈T⌉₊
  let P (t : ℝ) := dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I)
  let Z (t : ℝ) := riemannZeta (1/2+(t:ℂ)*I)
  have hT0 : 0 < T := by linarith
  have hab : T ≤ 2*T := by linarith
  have hN0 : (1:ℝ) ≤ N := hT.trans (Nat.le_ceil _)
  have hN : 1 ≤ N := by exact_mod_cast hN0
  have hP : Continuous P := by simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using continuous_dirichletPoly_one N (1/2)
  have hZ : Continuous Z := continuous_riemannZeta_half
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2*T) (f := fun t => Z t-P t)
    (C := C/√T) (fun t ht => h hT t (Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le hab] using ht)))
  rw [intervalIntegral.integral_sub (hZ.intervalIntegrable ..) (hP.intervalIntegrable ..), abs_of_nonneg (sub_nonneg.mpr hab)] at he
  have hp := norm_integral_criticalDirichletPoly_sub_length_le N hN T (2*T)
  rw [show 2*T-T=T by ring] at hp he
  have hsq : √(N:ℝ) ≤ 2*√T := by
    have hlt : (N:ℝ) < T+1 := Nat.ceil_lt_add_one hT0.le
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ) ≤ N),Real.sq_sqrt hT0.le, Real.sqrt_nonneg (N:ℝ), Real.sqrt_nonneg T]
  have he' : C / √T * T = C*√T := by field_simp; nlinarith [Real.sq_sqrt hT0.le]
  rw [he'] at he
  calc _ ≤ ‖(∫ t in T..(2*T), Z t)-(∫ t in T..(2*T), P t)‖ + ‖(∫ t in T..(2*T), P t)-(T:ℂ)‖ := by
         simpa only [dist_eq_norm] using dist_triangle (∫ t in T..(2*T), Z t) (∫ t in T..(2*T), P t) (T:ℂ)
       _ ≤ _ := by
         have hp' := hp.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
         change ‖(∫ t in T..(2*T), P t)-(T:ℂ)‖ ≤ _ at hp'
         exact (add_le_add he hp').trans_eq (by ring)


/-- The absolute first moment of Hardy's real-valued function is at least `T-O(√T)`. -/
theorem integral_abs_hardyZ_dyadic_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T →
      T-C*√T ≤ ∫ t in T..(2*T), |hardyZ t| := by
  obtain ⟨C,hC,h⟩ := norm_integral_riemannZeta_half_sub_length_le
  refine ⟨C,hC,?_⟩
  intro T hT
  let z (t : ℝ) := riemannZeta (1/2+(t:ℂ)*I)
  have htriangle := norm_sub_norm_le (T:ℂ) (∫ t in T..(2*T), z t)
  rw [norm_sub_rev] at htriangle
  have ht : ‖(T:ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [ht] at htriangle
  simp_rw [abs_hardyZ]
  have hm := intervalIntegral.norm_integral_le_integral_norm (f := z) (μ := volume) (by linarith : T ≤ 2*T)
  have hbound := h hT
  change ‖(∫ t in T..(2*T), z t)-(T:ℂ)‖ ≤ _ at hbound
  change _ ≤ ∫ t in T..(2*T), ‖z t‖
  linarith

/-- In particular the absolute first moment is bounded below linearly on every sufficiently
high dyadic interval. -/
theorem eventually_half_le_integral_abs_hardyZ :
    ∀ᶠ T : ℝ in atTop, T/2 ≤ ∫ t in T..(2*T), |hardyZ t| := by
  obtain ⟨C,hC,h⟩ := integral_abs_hardyZ_dyadic_lower
  filter_upwards [eventually_ge_atTop (max 1 ((2*C)^2))] with T hT
  have h1 := (le_max_left _ _).trans hT
  have h2 := (le_max_right _ _).trans hT
  have hroot : 2*C ≤ √T := Real.le_sqrt_of_sq_le h2
  refine le_trans ?_ (h h1)
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ T), mul_nonneg (Real.sqrt_nonneg T) (sub_nonneg.mpr hroot)]

end AnalyticNumberTheory.RiemannZeta
