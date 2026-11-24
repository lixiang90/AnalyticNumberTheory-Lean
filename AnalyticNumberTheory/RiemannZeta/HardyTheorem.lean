import AnalyticNumberTheory.RiemannZeta.HardyDirichletIntegrals
import AnalyticNumberTheory.RiemannZeta.HardyGammaPhase

/-!
# Infinitely many critical-line zeros of the Riemann zeta function

The absolute first moment of Hardy's function on a dyadic interval grows
linearly. The signed first moment is of order at most `T^(3/4)`. On an
interval where the function keeps one sign these estimates are incompatible.
-/

open Complex Real Finset Filter MeasureTheory Set
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

private theorem signed_moment_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ {T : ℝ}, 2 ≤ T →
      |∫ t in T..(2*T), hardyZ t| ≤ B*(√T*√(√T)) := by
  obtain ⟨C,hC,h⟩ := critical_approx_dyadic
  refine ⟨C+20+80+40/Real.log 2,by positivity,?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hab : T ≤ 2*T := by linarith
  have hs1 : 1 ≤ √T := by simpa using Real.sqrt_le_sqrt hT1
  have hq1 : 1 ≤ √(√T) := by simpa using Real.sqrt_le_sqrt hs1
  let N := ⌈T⌉₊
  let M := ⌈2*√T⌉₊
  have hn1 : 1 ≤ N := by exact_mod_cast hT1.trans (Nat.le_ceil _)
  have hns : √(N:ℝ) ≤ 2*√T := by
    have hceil : (N:ℝ) < T+1 := Nat.ceil_lt_add_one hT0.le
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.sqrt_nonneg T,Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ) ≤ N),Real.sq_sqrt hT0.le]
  have hms : √(M:ℝ) ≤ 2*√(√T) := by
    have hceil : (M:ℝ) < 2*√T+1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith [Real.sqrt_nonneg (M:ℝ),Real.sqrt_nonneg (√T),Real.sq_sqrt (Nat.cast_nonneg M : (0:ℝ) ≤ M),Real.sq_sqrt (Real.sqrt_nonneg T)]
  let P (t : ℝ) := dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I)
  let H (t : ℝ) := Complex.exp ((hardyPhase t:ℂ)*I)
  let Z (t : ℝ) := riemannZeta (1/2+(t:ℂ)*I)
  let U := hardyGammaUnit
  have hbd (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      ‖(hardyZ t:ℂ) - H t*P t‖ ≤ (C+20)/√T := by
    have hh := h hT1 t ht
    change ‖Z t-P t‖ ≤ _ at hh
    have hg := norm_hardyGammaUnit_sub_exp_le (hT.trans ht.1)
    change ‖U t-H t‖ ≤ _ at hg
    have hp := norm_criticalDirichletPoly_le N hn1 t
    change ‖P t‖ ≤ _ at hp
    have hpu : ‖P t‖ ≤ 5*√T := by linarith
    rw [hardyZ_eq_gammaUnit_mul_zeta]
    change ‖U t * Z t - H t * P t‖ ≤ _
    rw [show U t*Z t-H t*P t = U t*(Z t-P t)+(U t-H t)*P t by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_hardyGammaUnit,one_mul]
    have hG := hg.trans (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hT0 ht.1)
    apply (add_le_add hh (mul_le_mul hG hpu (norm_nonneg _) (by positivity))).trans_eq
    field_simp
    nlinarith [Real.sq_sqrt hT0.le]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2*T)
    (f := fun t => (hardyZ t:ℂ)-H t*P t) (C := (C+20)/√T)
    (fun t ht => hbd t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)))
  have hp : Continuous P := by simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using continuous_dirichletPoly_one N (1/2)
  have hl : ContinuousOn Real.log (Icc T (2*T)) := fun t ht => (Real.continuousAt_log (hT0.trans_le ht.1).ne').continuousWithinAt
  have hc : ContinuousOn H (Icc T (2*T)) := by dsimp [H,hardyPhase]; fun_prop
  have hiZ : IntervalIntegrable (fun t : ℝ => (hardyZ t:ℂ)) volume T (2*T) := (Complex.continuous_ofReal.comp continuous_hardyZ).intervalIntegrable ..
  have hiP : IntervalIntegrable (fun t => H t*P t) volume T (2*T) := (hc.mul hp.continuousOn).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_sub hiZ hiP,abs_of_nonneg (sub_nonneg.mpr hab),show 2*T-T=T by ring] at he
  have hs := norm_integral_hardyPhase_mul_dirichletPoly_le N hn1 hT1
  change ‖∫ t in T..(2*T), H t*P t‖ ≤ 16*√T*(1+2*√(M:ℝ))+(8/Real.log 2)*(1+2*√(N:ℝ)) at hs
  have hs' : ‖∫ t in T..(2*T), H t*P t‖ ≤ 80*(√T*√(√T))+(40/Real.log 2)*√T := by
    apply hs.trans
    apply add_le_add
    · have h := mul_le_mul_of_nonneg_left (show 1+2*√(M:ℝ) ≤ 5*√(√T) by linarith) (by positivity : 0 ≤ 16*√T)
      nlinarith only [h]
    · have h := mul_le_mul_of_nonneg_left (show 1+2*√(N:ℝ) ≤ 5*√T by linarith) (by positivity : 0 ≤ 8/Real.log 2)
      exact h.trans_eq (by ring)
  have hi : (∫ t in T..(2*T), (hardyZ t:ℂ)) = ((∫ t in T..(2*T), hardyZ t):ℝ) := by
    rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
    exact integral_complex_ofReal
  rw [show (C+20)/√T*T=(C+20)*√T by field_simp; nlinarith [Real.sq_sqrt hT0.le]] at he
  have hnr := norm_sub_norm_le (∫ t in T..(2*T), (hardyZ t:ℂ)) (∫ t in T..(2*T), H t*P t)
  have hcomp : ‖∫ t in T..(2*T), (hardyZ t:ℂ)‖ ≤ (C+20)*√T + (80*(√T*√(√T))+(40/Real.log 2)*√T) := by linarith only [hnr,he,hs']
  rw [hi,Complex.norm_real,Real.norm_eq_abs] at hcomp
  apply hcomp.trans
  have hq : √T ≤ √T*√(√T) := le_mul_of_one_le_right (Real.sqrt_nonneg T) hq1
  have hcc := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ C+20+40/Real.log 2)
  linarith only [hcc]

/-- Hardy's signed first moment on a dyadic interval has order at most three quarters. -/
theorem integral_hardyZ_dyadic_isBigO :
    (fun T : ℝ => ∫ t in T..(2*T), hardyZ t) =O[atTop] (fun T : ℝ => T^(3/4:ℝ)) := by
  obtain ⟨B,hB,h⟩ := signed_moment_bound
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨B, ?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  rw [Real.norm_eq_abs,Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hT0 _)]
  apply (h hT).trans_eq
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hT0.le,← Real.rpow_add hT0]
  norm_num


private theorem integral_abs_eq_abs_integral_of_nonvanishing {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hne : ∀ t ∈ Icc a b, f t ≠ 0) :
    (∫ t in a..b, |f t|) = |∫ t in a..b, f t| := by
  rcases lt_or_gt_of_ne (hne a ⟨le_rfl,hab⟩) with hneg | hpos
  · have hn (t : ℝ) (ht : t ∈ Icc a b) : f t ≤ 0 := by
      by_contra! hp
      obtain ⟨u,hu,hu0⟩ := intermediate_value_Icc ht.1 hf.continuousOn (show 0 ∈ Icc (f a) (f t) from ⟨hneg.le,hp.le⟩)
      exact hne u ⟨hu.1,hu.2.trans ht.2⟩ hu0
    have hsub : (∫ t in a..b, |f t|) = ∫ t in a..b, -f t := intervalIntegral.integral_congr
      fun t ht => abs_of_nonpos (hn t (by simpa only [uIcc_of_le hab] using ht))
    rw [hsub, intervalIntegral.integral_neg, abs_of_nonpos]
    have hnn := intervalIntegral.integral_nonneg (μ := volume) (f := fun t => -f t) hab (fun t ht => neg_nonneg.mpr (hn t ht))
    rwa [intervalIntegral.integral_neg, neg_nonneg] at hnn
  · have hp (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ f t := by
      by_contra! hn
      obtain ⟨u,hu,hu0⟩ := intermediate_value_Icc' ht.1 hf.continuousOn (show 0 ∈ Icc (f t) (f a) from ⟨hn.le,hpos.le⟩)
      exact hne u ⟨hu.1,hu.2.trans ht.2⟩ hu0
    have hsub : (∫ t in a..b, |f t|) = ∫ t in a..b, f t := intervalIntegral.integral_congr
      fun t ht => abs_of_nonneg (hp t (by simpa only [uIcc_of_le hab] using ht))
    rw [hsub, abs_of_nonneg (intervalIntegral.integral_nonneg hab hp)]

/-- Every sufficiently high dyadic interval contains the height of a critical-line zero. -/
theorem eventually_exists_critical_zero_dyadic :
    ∀ᶠ T : ℝ in atTop, ∃ t ∈ Icc T (2*T), riemannZeta (1/2+(t:ℂ)*I) = 0 := by
  obtain ⟨B,hB,h⟩ := signed_moment_bound
  filter_upwards [eventually_half_le_integral_abs_hardyZ,
    eventually_ge_atTop (max 2 (((2*B+1)^2)^2))] with T hlow hlarge
  have hT := (le_max_left _ _).trans hlarge
  have hT0 : 0 < T := by linarith
  have hx := Real.le_sqrt_of_sq_le ((le_max_right _ _).trans hlarge)
  have hx' := Real.le_sqrt_of_sq_le hx
  have hsmall : |∫ t in T..(2*T), hardyZ t| < T/2 := by
    refine (h hT).trans_lt ?_
    have hq : 0 < √(√T) := by positivity
    have hh : 2*B < √(√T) := by linarith
    have h₁ := mul_lt_mul_of_pos_right hh hq
    have h₂ := mul_lt_mul_of_pos_right h₁ (Real.sqrt_pos.mpr hT0)
    nlinarith only [h₂,Real.sq_sqrt hT0.le,Real.sq_sqrt (Real.sqrt_nonneg T),
      congrArg (fun x : ℝ => x*√T) (Real.sq_sqrt (Real.sqrt_nonneg T))]
  by_contra! hno
  have hne : ∀ t ∈ Icc T (2*T), hardyZ t ≠ 0 := fun t ht hh => hno t ht ((hardyZ_eq_zero_iff t).mp hh)
  have heq := integral_abs_eq_abs_integral_of_nonvanishing (show T≤2*T by linarith) continuous_hardyZ hne
  linarith

/-- Hardy's theorem, with positive critical-line zeros at arbitrarily large heights. -/
theorem exists_critical_zero_above (A : ℝ) :
    ∃ t : ℝ, A < t ∧ riemannZeta (1/2+(t:ℂ)*I) = 0 := by
  obtain ⟨T,hT,hT'⟩ := (eventually_exists_critical_zero_dyadic.and (eventually_gt_atTop A)).exists
  obtain ⟨t,ht,hz⟩ := hT
  exact ⟨t,hT'.trans_le ht.1,hz⟩

/-- Infinitely many zeros of the Riemann zeta function lie on the positive critical half-line. -/
theorem hardy_critical_zeros_infinite :
    {t : ℝ | 0 < t ∧ riemannZeta (1/2+(t:ℂ)*I) = 0}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro A
  obtain ⟨t,ht,hz⟩ := exists_critical_zero_above (max 0 A)
  exact ⟨t,⟨(le_max_left _ _).trans_lt ht,hz⟩,(le_max_right _ _).trans_lt ht⟩

end AnalyticNumberTheory.RiemannZeta
