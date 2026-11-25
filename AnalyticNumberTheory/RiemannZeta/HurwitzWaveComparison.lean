import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalWaves
import AnalyticNumberTheory.RiemannZeta.HurwitzMeanSquare
import AnalyticNumberTheory.AnalyticTools.FourthRootMeanComparison

/-!
# Comparing shifted zeta with its rotating waves in mean square
-/
noncomputable section
open Real Complex Finset MeasureTheory Set Filter
open scoped Interval Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

theorem hurwitzWaveSum_sq_intervalIntegrable (a : ℝ) (N : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => ‖hurwitzWaveSum a N t‖^2) volume u v := by
  let S := hurwitzWaveIndices N
  let D := ∑i∈S,(Real.sqrt (hurwitzWaveFrequency a i))⁻¹
  have hmeas : Measurable (hurwitzWaveSum a N) := by
    unfold hurwitzWaveSum;apply Finset.measurable_fun_sum
    intro i _;exact (continuous_hurwitzWave a i).measurable.indicator measurableSet_Ici
  have hb (t : ℝ) : ‖hurwitzWaveSum a N t‖≤D := by
    apply (norm_sum_le ..).trans;apply sum_le_sum
    intro i _;change ‖if hurwitzWaveEntry a i≤t then _ else 0‖≤_
    split_ifs
    · exact (norm_hurwitzWave a i t).le
    · simp
  apply intervalIntegrable_iff.mpr
  have hI : IntervalIntegrable (fun _ : ℝ => D^2) volume u v := continuous_const.intervalIntegrable ..
  apply hI.def'.mono' (hmeas.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with t;rw [Real.norm_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2

theorem continuous_hurwitz_critical_line (a : ℝ) : Continuous (fun t : ℝ => HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr;intro t
  apply (HurwitzZeta.differentiableAt_hurwitzZeta _ ?_).continuousAt.comp (f:=fun t : ℝ => (1/2:ℂ)+t*I) (by fun_prop)
  intro he;have hh := congrArg Complex.re he;norm_num at hh

private theorem wave_error {a t : ℝ} (ha : a∈Ioc (0:ℝ) 1) (ht : 8*Real.pi≤t)
    {N : ℕ} (hN : ⌊Real.sqrt (t/(2*Real.pi))⌋₊+1≤N) :
    |‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖-‖hurwitzWaveSum a N t‖|≤
      ((612+2*Real.Gamma (1/2))*(2*Real.pi)^(1/4:ℝ))*t^(-(1/4:ℝ)) := by
  let x := Real.sqrt (t/(2*Real.pi))
  let E := Complex.exp ((hardyPhase t:ℂ)*I)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)
  have hp : 0<t := (by positivity : 0<8*Real.pi).trans_le ht
  have hπ : 0<2*Real.pi := by positivity
  have hx : 2≤x := Real.le_sqrt_of_sq_le ((le_div_iff₀ hπ).mpr (by linarith))
  have hxt : x^2=t/(2*Real.pi) := Real.sq_sqrt (by positivity)
  have hmain := hurwitz_critical_rotated_error (t:=t) ha hx (by rw [hxt];field_simp)
  have he := hurwitzWaveSum_eq ha hp.le (by linarith : 1≤x) hN
  change ‖E*Z-_‖≤_ at hmain
  rw [←he] at hmain
  have hw := abs_norm_sub_norm_le (E*Z) (hurwitzWaveSum a N t)
  rw [norm_mul,show ‖E‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul] at hw
  apply (hw.trans hmain).trans_eq
  dsimp only [x];rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity : 0≤t/(2*Real.pi)),
    show (1/2:ℝ)*(-(1/2))= -(1/4) by norm_num,Real.div_rpow hp.le hπ.le,Real.rpow_neg hπ.le,div_inv_eq_mul];ring

/-- Integrated comparison on the classical square-root truncation,
uniform in the upper endpoint for each fixed shift. -/
theorem hurwitz_wave_mean_comparison {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
    let N := ⌊Real.sqrt (T/(2*Real.pi))⌋₊+1
    |(∫t in (8*Real.pi)..T,‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2)-
      ∫t in (8*Real.pi)..T,‖hurwitzWaveSum a N t‖^2|≤C*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)) := by
  let b := 8*Real.pi
  let z := fun t : ℝ => ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖
  let D := (612+2*Real.Gamma (1/2))*(2*Real.pi)^(1/4:ℝ)
  have hc : Continuous z := (continuous_hurwitz_critical_line a).norm
  have hb : 1≤b := by dsimp [b];linarith [Real.pi_gt_three]
  have hD : 0<D := by dsimp [D];have := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ));positivity
  refine ⟨2+4*D^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop b,(mean_sq_hurwitzZeta_half ha).eventually_lt_const (by norm_num : (1:ℝ)<2)] with T ht hH
  intro N
  have hT : 1<T := by dsimp [b] at ht;linarith [Real.pi_gt_three]
  have ht₀ := zero_lt_one.trans hT
  change (∫t in (1:ℝ)..T,z t^2)/(T*Real.log T)<2 at hH
  rw [div_lt_iff₀ (mul_pos ht₀ (Real.log_pos hT)),←intervalIntegral.integral_add_adjacent_intervals (f:=fun t => z t^2)
    ((hc.pow 2).intervalIntegrable (μ:=volume) 1 b) ((hc.pow 2).intervalIntegrable (μ:=volume) b T)] at hH
  have hz₀ : 0≤∫t in (1:ℝ)..b,z t^2 := intervalIntegral.integral_nonneg hb (fun _ _ => sq_nonneg _)
  have hZ : (∫t in b..T,z t^2)≤2*T*Real.log (T+2) := by
    linarith [mul_le_mul_of_nonneg_left (Real.log_le_log ht₀ (show T≤T+2 by linarith)) (show 0≤2*T by positivity)]
  rw [←intervalIntegral.integral_sub (f:=fun t=>z t^2) (g:=fun t=>‖hurwitzWaveSum a N t‖^2)
    ((hc.pow 2).intervalIntegrable ..) (hurwitzWaveSum_sq_intervalIntegrable a N b T)]
  apply fourth_root_mean_square_comparison le_rfl ht hc (by norm_num : (0:ℝ)<2) hD hZ
  intro t htt
  apply wave_error ha htt.1
  apply Nat.succ_le_succ;apply Nat.floor_mono;apply Real.sqrt_le_sqrt;exact div_le_div_of_nonneg_right htt.2 (by positivity)

end AnalyticNumberTheory.RiemannZeta
