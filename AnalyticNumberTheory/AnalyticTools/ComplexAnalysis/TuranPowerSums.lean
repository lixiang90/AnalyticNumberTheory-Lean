import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Turán power sums at large consecutive exponents

A circle of controlled distance from all the moduli separates a distinguished
unit root from the smaller roots. On that circle the generating function of
the high power sums can be bounded using the coefficients of its denominator.
-/

noncomputable section

open Finset Complex MeasureTheory Metric Polynomial intervalIntegral
open scoped Classical Interval Real Polynomial

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private lemma log_distance_integral_lower {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    -2 ≤ ∫ t in (1/2:ℝ)..(3/4:ℝ), Real.log (t-a) := by
  rw [intervalIntegral.integral_comp_sub_right]
  have h := intervalIntegral.integral_mono_interval (c:=(-1:ℝ)) (d:=1)
    (a:=1/2-a) (b:=3/4-a) (f:=fun x : ℝ => -Real.log x)
    (by linarith [ha.2]) (by linarith) (by linarith [ha.1]) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      change 0 ≤ -Real.log x
      apply neg_nonneg.mpr
      rw [←Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (abs_le.mpr ⟨hx.1.le,hx.2⟩))
    intervalIntegrable_log'.neg
  simp only [intervalIntegral.integral_neg] at h
  have hfull : (∫ x in (-1:ℝ)..1, Real.log x) = -2 := by
    rw [integral_log]; norm_num
  linarith

/-- A radius in `[1/2,3/4]` with product separation from any finite family of
real numbers in `[0,1]`. Repeated radii are allowed. -/
theorem exists_radius_prod_distance {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, a i ∈ Set.Icc (0:ℝ) 1) :
    ∃ r ∈ Set.Icc (1/2:ℝ) (3/4), Real.exp (-(8*(S.card:ℝ)+1)) ≤ ∏ i ∈ S, |r-a i| := by
  let g (t : ℝ) := ∑ i ∈ S, Real.log (t-a i)
  have hi (i : ι) : IntervalIntegrable (fun t => Real.log (t-a i)) volume (1/2:ℝ) (3/4:ℝ) := by
    simpa only [sub_add_cancel] using
      (intervalIntegrable_log' (a:=1/2-a i) (b:=3/4-a i)).comp_sub_right (a i)
  have hlow : -2*(S.card:ℝ) ≤ ∫ t in (1/2:ℝ)..(3/4:ℝ), g t := by
    rw [show (∫ t in (1/2:ℝ)..(3/4:ℝ), g t) = ∑ i ∈ S, (∫ t in (1/2:ℝ)..(3/4:ℝ), Real.log (t-a i))
      from intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    simpa only [sum_const,nsmul_eq_mul,mul_comm (S.card:ℝ)] using sum_le_sum fun i h => log_distance_integral_lower (ha i h)
  have hg : IntervalIntegrable g volume (1/2:ℝ) (3/4:ℝ) := by
    have he : g = (∑ i ∈ S, fun t => Real.log (t-a i)) := by ext t; simp [g]
    rw [he]
    exact IntervalIntegrable.sum S (fun i _ => hi i)
  by_contra! h
  have hub : (∫ t in (1/2:ℝ)..(3/4:ℝ), g t) ≤ ∫ _t in (1/2:ℝ)..(3/4:ℝ), -(8*(S.card:ℝ)+1) := by
    apply intervalIntegral.integral_mono_ae_restrict (by norm_num) hg intervalIntegrable_const
    have hne : ∀ᵐ x : ℝ ∂volume, ∀ i ∈ S, x ≠ a i := by
      apply (ae_ball_iff (S:=(S:Set ι)) S.countable_toSet).mpr
      exact fun i _ => volume.ae_ne (a i)
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht ht'
    have hlt := h t ht
    have hprod : 0 < ∏ i ∈ S, |t-a i| := prod_pos fun i hi => abs_pos.mpr (sub_ne_zero.mpr (ht' i hi))
    have hl := Real.log_lt_log hprod hlt
    rw [Real.log_exp,Real.log_prod (fun i hi => (abs_pos.mpr (sub_ne_zero.mpr (ht' i hi))).ne')] at hl
    simpa only [g,Real.log_abs] using hl.le
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hub
  linarith

private lemma quotient_at_root (P : ℂ[X]) {z w : ℂ} (hz : P.eval z = 0) (hw : w ≠ z) :
    P.eval w / (w-z) = ∑ k ∈ range (P.natDegree+1), P.coeff k * ∑ j ∈ range k, z^j*w^(k-1-j) := by
  apply (div_eq_iff (sub_ne_zero.mpr hw)).mpr
  rw [sum_mul]
  have he (k : ℕ) : (∑ j ∈ range k, z^j*w^(k-1-j))*(w-z) = w^k-z^k := by
    have h := geom_sum₂_mul z w k
    linear_combination -h
  simp_rw [mul_assoc, he, mul_sub]
  rw [sum_sub_distrib,←eval_eq_sum_range,←eval_eq_sum_range,hz,sub_zero]

private lemma high_resolvent_numerator {ι : Type*} (S : Finset ι) (b z : ι → ℂ)
    (M : ℕ) (w : ℂ) (hw : ∀ i ∈ S, w ≠ z i)
    (P : ℂ[X]) (hP : ∀ i ∈ S, P.eval (z i) = 0) :
    P.eval w * (∑ i ∈ S, b i * z i^(M+1) / (w-z i)) =
      ∑ k ∈ range (P.natDegree+1), P.coeff k *
        ∑ j ∈ range k, w^(k-1-j)*(∑ i ∈ S, b i*z i^(M+1+j)) := by
  rw [mul_sum]
  calc
    _ = ∑ i ∈ S, ∑ k ∈ range (P.natDegree+1), ∑ j ∈ range k,
        P.coeff k * (w^(k-1-j)*(b i*z i^(M+1+j))) := by
      refine sum_congr rfl fun i hi => ?_
      rw [show P.eval w * (b i*z i^(M+1)/(w-z i)) = (b i*z i^(M+1))*(P.eval w/(w-z i)) by ring,
        quotient_at_root P (hP i hi) (hw i hi), mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [←mul_assoc,mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add]; ring
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm,mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum,mul_sum]

private lemma bound_resolvent_numerator {ι : Type*} (S : Finset ι) (b z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (M : ℕ) {w : ℂ} (hw₁ : ‖w‖ ≤ 1)
    (hw : ∀ i ∈ S, w ≠ z i) {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ j < S.card, ‖∑ i ∈ S, b i*z i^(M+1+j)‖ ≤ B) :
    ‖∏ i ∈ S, (w-z i)‖ * ‖∑ i ∈ S, b i*z i^(M+1)/(w-z i)‖ ≤ (S.card:ℝ)*2^S.card*B := by
  let P : ℂ[X] := ∏ i ∈ S, (X-C (z i))
  have hdeg : P.natDegree = S.card := by
    simp [P,natDegree_prod_of_monic (h:=fun i _ => monic_X_sub_C (z i))]
  have hmahler : P.mahlerMeasure = 1 := by
    have H (U : Finset ι) (hu : ∀ i ∈ U, ‖z i‖ ≤ 1) :
        (∏ i ∈ U, (X-C (z i))).mahlerMeasure = 1 := by
      induction U using Finset.induction_on with
      | empty => simp [Polynomial.mahlerMeasure_one]
      | insert i U hi ih =>
        rw [prod_insert hi,Polynomial.mahlerMeasure_mul,Polynomial.mahlerMeasure_X_sub_C,
          max_eq_left (hu i (mem_insert_self ..)),one_mul]
        exact ih (fun j hj => hu j (mem_insert_of_mem hj))
    exact H S hz
  have hcoeff (k : ℕ) : ‖P.coeff k‖ ≤ S.card.choose k := by
    simpa only [hdeg,hmahler,mul_one] using P.norm_coeff_le_choose_mul_mahlerMeasure k
  have hroot (i : ι) (hi : i ∈ S) : P.eval (z i) = 0 := by
    simp only [P,eval_prod,eval_sub,eval_X,eval_C]
    exact prod_eq_zero hi (sub_self _)
  have he := high_resolvent_numerator S b z M w hw P hroot
  rw [hdeg] at he
  have hPw : P.eval w = ∏ i ∈ S, (w-z i) := by simp only [P,eval_prod,eval_sub,eval_X,eval_C]
  rw [←hPw,←norm_mul,he]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ k ∈ range (S.card+1), (S.card.choose k:ℝ)*((S.card:ℝ)*B) := by
      refine sum_le_sum fun k hk => ?_
      rw [norm_mul]
      apply mul_le_mul (hcoeff k) _ (norm_nonneg _) (Nat.cast_nonneg _)
      apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ _j ∈ range k, B := by
          refine sum_le_sum fun j hj => ?_
          rw [norm_mul,norm_pow]
          exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hw₁) (hB j (by simp only [mem_range] at hk hj; omega)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
        _ ≤ _ := by simp; gcongr; exact_mod_cast (Nat.le_of_lt_succ (mem_range.mp hk))
    _ = _ := by
      rw [←sum_mul, ←Nat.cast_sum, Nat.sum_range_choose]
      push_cast; ring

private def shiftKernel (z : ℂ) (m : ℕ) (w : ℂ) : ℂ := z^m/w^m/(w-z)

private lemma sphere_norm {r : ℝ} {w : ℂ} (hw : w ∈ sphere 0 r) : ‖w‖ = r := by
  simpa only [mem_sphere,dist_zero_right] using hw

private lemma shiftKernel_cont {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ ≠ r) (m : ℕ) :
    ContinuousOn (shiftKernel z m) (sphere 0 r) := by
  intro w hw
  have hn := sphere_norm hw
  have hw₀ : w ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hr)
  have hwz : w-z ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hz hn)
  unfold shiftKernel
  fun_prop (disch := first | assumption | positivity)

private lemma circle_shiftKernel_step {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) (k : ℕ) :
    (∮ w in C(0,r), shiftKernel z (k+1) w) = (∮ w in C(0,r), shiftKernel z k w) -
      z^k * (∮ w in C(0,r), (w-(0:ℂ))^(-(k+1:ℤ))) := by
  have hcont : CircleIntegrable (fun w : ℂ => z^k * (w-0)^(-(k+1:ℤ))) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    intro w hw
    have hw₀ : w-0 ≠ 0 := by simpa using norm_pos_iff.mp ((sphere_norm hw).symm ▸ hr)
    exact continuousWithinAt_const.mul ((continuousWithinAt_id.sub continuousWithinAt_const).zpow₀ _ (Or.inl hw₀))
  rw [← circleIntegral.integral_const_mul, ←circleIntegral.integral_sub
    ((shiftKernel_cont hr hz k).circleIntegrable hr.le) hcont]
  apply circleIntegral.integral_congr hr.le
  intro w hw
  have hn := sphere_norm hw
  have hw₀ : w ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hr)
  have hwz : w-z ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hz hn)
  simp only [shiftKernel,sub_zero,show -(k+1:ℤ) = -((k+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,pow_succ]
  field_simp; ring

set_option maxHeartbeats 450000 in
private theorem circle_integral_shiftKernel {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r)
    (m : ℕ) : (∮ w in C(0,r), shiftKernel z (m+1) w) =
      if r < ‖z‖ then -(2*Real.pi*I) else 0 := by
  let A : ℂ := 2*Real.pi*I
  have hzero : (∮ w in C(0,r), (w-z)⁻¹) = if r < ‖z‖ then 0 else A := by
    split_ifs with h
    · have hdiff : DifferentiableOn ℂ (fun w : ℂ => (w-z)⁻¹) (closedBall 0 r) := by
        apply (differentiableOn_id.sub_const z).inv
        intro w hw
        apply sub_ne_zero.mpr
        rintro rfl
        exact (not_lt_of_ge (by simpa only [mem_closedBall,dist_zero_right] using hw : ‖w‖ ≤ r)) h
      exact (hdiff.diffContOnCl_ball (Set.Subset.rfl)).circleIntegral_eq_zero hr.le
    · apply circleIntegral.integral_sub_inv_of_mem_ball
      simpa only [mem_ball,dist_zero_right] using lt_of_le_of_ne (le_of_not_gt h) hz
  induction m with
  | zero =>
    rw [circle_shiftKernel_step hr hz 0]
    have hbase : shiftKernel z 0 = fun w => (w-z)⁻¹ := by funext w; simp [shiftKernel]
    rw [hbase,hzero]
    simp only [Nat.cast_zero,zero_add,zpow_neg_one,pow_zero,one_mul,circleIntegral.integral_sub_center_inv 0 hr.ne']
    split_ifs <;> simp [A]
  | succ m ih =>
    rw [circle_shiftKernel_step hr hz, circleIntegral.integral_sub_zpow_of_ne (by omega : -((m+1:ℕ)+1:ℤ) ≠ -1),
      mul_zero,sub_zero,ih]

private lemma weighted_contour_lower {ι : Type*} (S : Finset ι) (b : ι → ℕ) (z : ι → ℂ)
    {i₀ : ι} (hi₀ : i₀ ∈ S) (hb : 1 ≤ b i₀) {r : ℝ} (hr : 0 < r) (hr₀ : r < ‖z i₀‖)
    (havoid : ∀ i ∈ S, ‖z i‖ ≠ r) (M : ℕ) :
    1 ≤ ‖(2*Real.pi*I:ℂ)⁻¹ • (∮ w in C(0,r), ∑ i ∈ S, (b i:ℂ)*shiftKernel (z i) (M+1) w)‖ := by
  let A : ℂ := 2*Real.pi*I
  let D := S.filter (fun i => r < ‖z i‖)
  have hd : i₀ ∈ D := mem_filter.mpr ⟨hi₀,hr₀⟩
  have hmass : 1 ≤ ∑ i ∈ D, b i := hb.trans (single_le_sum (fun _ _ => Nat.zero_le _) hd)
  have hA : A ≠ 0 := by dsimp only [A]; exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hci : (∮ w in C(0,r), ∑ i ∈ S, (b i:ℂ)*shiftKernel (z i) (M+1) w) =
      -A*(∑ i ∈ D, (b i:ℂ)) := by
    rw [circleIntegral.integral_fun_sum (f:=fun i w => (b i:ℂ)*shiftKernel (z i) (M+1) w) (fun i hi => ((continuousOn_const.mul
      (shiftKernel_cont hr (havoid i hi) (M+1))).circleIntegrable hr.le))]
    simp_rw [circleIntegral.integral_const_mul]
    rw [mul_sum,sum_filter]
    refine sum_congr rfl fun i hi => ?_
    rw [circle_integral_shiftKernel hr (havoid i hi)]
    dsimp only [A]; split_ifs <;> ring
  rw [hci,smul_eq_mul]
  change 1 ≤ ‖A⁻¹*(-A*_)‖
  rw [←mul_assoc, mul_neg, inv_mul_cancel₀ hA, neg_one_mul,norm_neg,←Nat.cast_sum,
    Complex.norm_natCast]
  exact_mod_cast hmass

/-- A Turán power-sum bound with positive integral weights and one unit root.
For every starting exponent `M`, the next `card S` powers contain a sum of
size at least `exp (−M−10 card S−2)`. This form allows repeated roots. -/
theorem turan_high_power_sum {ι : Type*} (S : Finset ι) (b : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) {i₀ : ι} (hi₀ : i₀ ∈ S) (hb : 1 ≤ b i₀)
    (hunit : ‖z i₀‖ = 1) (M : ℕ) :
    ∃ k ∈ Ioc M (M+S.card), Real.exp (-(M+10*(S.card:ℝ)+2)) ≤
      ‖∑ i ∈ S, (b i:ℂ)*z i^k‖ := by
  let N := S.card
  have hN : 0 < N := card_pos.mpr ⟨i₀,hi₀⟩
  let f (j : ℕ) := ‖∑ i ∈ S, (b i:ℂ)*z i^(M+1+j)‖
  obtain ⟨j,hj,hmax⟩ := (range N).exists_max_image f (nonempty_range_iff.mpr hN.ne')
  let B := f j
  have hB : 0 ≤ B := norm_nonneg _
  have hB' (j' : ℕ) (hj' : j' < N) : f j' ≤ B := hmax j' (mem_range.mpr hj')
  obtain ⟨r,hr,hsep⟩ := exists_radius_prod_distance S (fun i => ‖z i‖)
    (fun i hi => ⟨norm_nonneg _,hz i hi⟩)
  have hr₀ : 0 < r := by linarith [hr.1]
  have hr₁ : r ≤ 1 := by linarith [hr.2]
  let E := Real.exp (-(8*(N:ℝ)+1))
  have hE : 0 < E := Real.exp_pos _
  have hsep' : E ≤ ∏ i ∈ S, |r-‖z i‖| := hsep
  have havoid (i : ι) (hi : i ∈ S) : ‖z i‖ ≠ r := by
    intro he
    have hzero := prod_eq_zero (f:=fun i => |r-‖z i‖|) hi (show |r-‖z i‖|=0 by simp [he])
    linarith
  let F (w : ℂ) := ∑ i ∈ S, (b i:ℂ)*shiftKernel (z i) (M+1) w
  let G := (N:ℝ)*2^N*B
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hFw (w : ℂ) (hw : w ∈ sphere 0 r) : ‖F w‖ ≤ (G/E)*2^(M+1) := by
    have hn := sphere_norm hw
    have hw₀ : w ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hr₀)
    have hwz (i : ι) (hi : i ∈ S) : w ≠ z i := by rintro rfl; exact havoid i hi hn
    have hnumer := bound_resolvent_numerator S (fun i => (b i:ℂ)) z hz M (hn.trans_le hr₁) hwz hB hB'
    have hden : E ≤ ‖∏ i ∈ S, (w-z i)‖ := by
      rw [norm_prod]
      apply hsep'.trans (prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => ?_))
      rw [←hn]; exact abs_norm_sub_norm_le w (z i)
    have hres : ‖∑ i ∈ S, (b i:ℂ)*z i^(M+1)/(w-z i)‖ ≤ G/E := by
      apply (le_div_iff₀ hE).mpr
      exact (mul_comm ..).le.trans ((mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hnumer)
    have hfact : F w = (∑ i ∈ S, (b i:ℂ)*z i^(M+1)/(w-z i))*(w⁻¹)^(M+1) := by
      rw [sum_mul]
      exact sum_congr rfl fun i hi => by dsimp only [shiftKernel]; rw [inv_pow]; ring
    rw [hfact,norm_mul,norm_pow,norm_inv,hn]
    apply mul_le_mul hres _ (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_le_iff_one_le_mul₀ hr₀]; linarith [hr.1]
  have hcont := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr₀.le hFw
  have hdet := weighted_contour_lower S b z hi₀ hb hr₀ (by rw [hunit]; linarith [hr.2]) havoid M
  have hone : 1 ≤ G/E*2^(M+1) := hdet.trans (hcont.trans (mul_le_of_le_one_left (by positivity) hr₁))
  have hmul : 1 ≤ (2:ℝ)^(M+1)*Real.exp (8*(N:ℝ)+1)*(N:ℝ)*2^N*B := by
    dsimp only [E,G] at hone
    rw [Real.exp_neg,div_inv_eq_mul] at hone
    linarith only [hone]
  have hpow (n : ℕ) : (2:ℝ)^n ≤ Real.exp n := by
    rw [show Real.exp n = (Real.exp 1)^n by rw [←Real.exp_nat_mul]; simp]
    apply pow_le_pow_left₀ (by norm_num)
    linarith [Real.add_one_le_exp (1:ℝ)]
  have hN' : (N:ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N:ℝ)]
  have hmajor : (2:ℝ)^(M+1)*Real.exp (8*(N:ℝ)+1)*(N:ℝ)*2^N ≤ Real.exp (M+10*(N:ℝ)+2) := by
    calc
      _ ≤ Real.exp (M+1:ℕ)*Real.exp (8*(N:ℝ)+1)*Real.exp N*Real.exp N := by gcongr <;> apply hpow
      _ = _ := by simp only [←Real.exp_add]; push_cast; congr 1; ring
  refine ⟨M+1+j,mem_Ioc.mpr ⟨by omega, by have h:=mem_range.mp hj; change _ ≤ M+N; omega⟩,?_⟩
  change Real.exp (-(M+10*(N:ℝ)+2)) ≤ B
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  exact hmul.trans ((mul_le_mul_of_nonneg_right hmajor hB).trans_eq (mul_comm ..))

/-- Scale-invariant form of the large-exponent power-sum bound. -/
theorem turan_high_power_sum_scaled {ι : Type*} (S : Finset ι) (b : ι → ℕ) (z : ι → ℂ)
    {i₀ : ι} (hi₀ : i₀ ∈ S) (hb : 1 ≤ b i₀) (hmax : ∀ i ∈ S, ‖z i‖ ≤ ‖z i₀‖)
    (hu : 0 < ‖z i₀‖) (M : ℕ) :
    ∃ k ∈ Ioc M (M+S.card), Real.exp (-(M+10*(S.card:ℝ)+2))*‖z i₀‖^k ≤
      ‖∑ i ∈ S, (b i:ℂ)*z i^k‖ := by
  let R := ‖z i₀‖
  let v (i : ι) := z i/(R:ℂ)
  have hn (i : ι) : ‖v i‖ = ‖z i‖/R := by
    rw [show v i = _ from rfl,norm_div,Complex.norm_real,Real.norm_of_nonneg hu.le]
  obtain ⟨k,hk,H⟩ := turan_high_power_sum S b v
    (fun i hi => by rw [hn]; exact (div_le_one hu).mpr (hmax i hi)) hi₀ hb
    (by rw [hn]; exact div_self hu.ne') M
  refine ⟨k,hk,?_⟩
  have he : (∑ i ∈ S, (b i:ℂ)*v i^k) = (∑ i ∈ S, (b i:ℂ)*z i^k)/(R:ℂ)^k := by
    rw [sum_div]
    exact sum_congr rfl fun i _ => by dsimp only [v]; rw [div_pow]; ring
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le] at H
  exact (le_div_iff₀ (pow_pos hu _)).mp H

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
