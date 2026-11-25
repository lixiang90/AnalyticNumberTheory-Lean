import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleDecomposition
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exponential decay of the radial Hurwitz heads

The lower diagonal from the origin has fixed negative argument. This
suppresses the finitely many Fourier modes before the contour turns
toward the balanced saddle.
-/
noncomputable section
open Real Complex Set MeasureTheory Finset
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem arg_one_sub_I_le : ((1:ℂ)-I).arg≤ -(2/3) := by
  let z := (1:ℂ)-I
  have hnorm : ‖z‖≤3/2 := by
    have hh : ‖z‖^2=2 := by rw [←Complex.normSq_eq_norm_sq];norm_num [z,Complex.normSq_apply]
    nlinarith [norm_nonneg z]
  have hr : z.re=1 := by norm_num [z]
  have hi : z.im= -1 := by norm_num [z]
  have hn : 0<‖z‖ := (hr ▸ zero_lt_one).trans_le (Complex.re_le_norm z)
  have harg := Complex.arg_neg_iff.mpr (by rw [hi];norm_num : z.im<0)
  have H := Real.sin_le (neg_nonneg.mpr harg.le)
  rw [Real.sin_neg,Complex.sin_arg,hi] at H
  have H' : (-1:ℝ)/‖z‖≤ -(2/3) := (div_le_iff₀ hn).mpr (by linarith)
  change z.arg≤_;linarith

private theorem radial_mode_majorant {s : ℂ} {x b ω u : ℝ} (hx : 8≤x) (hb : b≤x+1/2)
    (hσ : s.re=1/2) (ht : s.im=2*Real.pi*x^2) (hω : ω≤2*Real.pi*x) (hu : u∈Set.Ioc 0 (b/2)) :
    ‖fourierPowerMode s ω ((1-I)*u)‖≤u^(-(1/2:ℝ))*Real.exp (-x^2/4) := by
  let z : ℂ := (1-I)*u
  have hr : z.re=u := by simp [z,mul_re]
  have hi : z.im= -u := by simp [z,mul_im]
  have hpos : 0<z.re := hr ▸ hu.1
  have hz : z≠0 := by intro he;simpa [he] using hpos
  have ha : z.arg≤ -(2/3) := by dsimp [z];rw [Complex.arg_mul_real hu.1];exact arg_one_sub_I_le
  rw [norm_fourierPowerMode s ω hz,hσ]
  apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hu.1 (hr ▸ Complex.re_le_norm z) (by norm_num)) _ (Real.exp_nonneg _) (Real.rpow_nonneg hu.1.le _)
  apply Real.exp_le_exp.mpr
  rw [show ((1-I)*(u:ℂ)).im= -u from hi,ht]
  have h₁ := mul_le_mul_of_nonneg_right ha (show 0≤2*Real.pi*x^2 by positivity)
  have h₂ := mul_le_mul hω hu.2 hu.1.le (by positivity : 0≤2*Real.pi*x)
  have h₃ := mul_le_mul_of_nonneg_left hb (show 0≤Real.pi*x by positivity)
  have h₄ := mul_le_mul_of_nonneg_left (show x/2≤x^2/12 by nlinarith) Real.pi_pos.le
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg x)]

/-- The radial heads have exponentially small total size at the balanced
cutoff. All constants are independent of the Hurwitz shift. -/
theorem norm_hurwitzRadialHeads_balanced {s : ℂ} {x b : ℝ} (hx : 8≤x) (hb : b≤x+1/2) (hb' : 0<b)
    (hσ : s.re=1/2) (ht : s.im=2*Real.pi*x^2) (a : ℝ) {q : ℕ} (hq : (q:ℝ)≤x) :
    ‖hurwitzRadialHeads s a b q‖ ≤ 4*x^2*Real.exp (-x^2/4) := by
  let E := Real.exp (-x^2/4)
  have hE : 0≤E := Real.exp_nonneg _
  have hmode (j : ℕ) (hj : j∈range q) :
      ‖∫ u in (0:ℝ)..(b/2),fourierPowerMode s (hurwitzOmega j) ((1-I)*u)‖≤2*x*E := by
    have hj' : (j:ℝ)+1≤q := by exact_mod_cast (show j+1≤q from mem_range.mp hj)
    have hω : hurwitzOmega j≤2*Real.pi*x := mul_le_mul_of_nonneg_left (hj'.trans hq) (by positivity)
    have hp : 0<b/2 := by positivity
    let f (u : ℝ) := fourierPowerMode s (hurwitzOmega j) ((1-I)*u)
    have hg : IntervalIntegrable (fun u : ℝ => u^(-(1/2:ℝ))*E) volume 0 (b/2) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(1/2:ℝ))).mul_const E
    have hm : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 (b/2))) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
      unfold f fourierPowerMode
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.cpow_const (by fun_prop)
      intro u hu;left;simpa [mul_re] using hu.1
    have hdom := (ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=b/2))).mono
      (fun u hu => radial_mode_majorant hx hb hσ ht hω hu)
    have hi : IntegrableOn f (Set.Ioc 0 (b/2)) := hg.1.mono' hm hdom
    rw [intervalIntegral.integral_of_le hp.le]
    apply (norm_integral_le_integral_norm _).trans ((integral_mono_ae hi.norm hg.1 hdom).trans _)
    rw [←intervalIntegral.integral_of_le hp.le,intervalIntegral.integral_mul_const,integral_rpow (Or.inl (by norm_num))]
    norm_num [Real.zero_rpow (by norm_num : (1/2:ℝ)≠0)]
    have hbase : (b/2)^(1/2:ℝ)≤x := by
      rw [←Real.sqrt_eq_rpow];apply Real.sqrt_le_iff.mpr;constructor <;> nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hbase hE]
  unfold hurwitzRadialHeads
  apply (norm_sum_le _ _).trans
  have hn : ‖(1:ℂ)-I‖≤2 := (norm_sub_le _ _).trans (by norm_num)
  calc _ ≤ ∑ _j∈range q,4*x*E := by
            apply sum_le_sum;intro j hj;rw [norm_mul,norm_hurwitzShift,one_mul,norm_mul]
            exact (mul_le_mul hn (hmode j hj) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
       _ ≤ _ := by simp;dsimp [E];nlinarith [mul_le_mul_of_nonneg_right hq (show 0≤4*x*Real.exp (-x^2/4) by positivity)]

end AnalyticNumberTheory.RiemannZeta
