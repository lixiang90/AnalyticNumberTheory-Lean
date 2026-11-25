import AnalyticNumberTheory.DirichletLFunctions.PrimitiveMomentDiagonal
import AnalyticNumberTheory.DirichletLFunctions.CriticalMeanSquare
import AnalyticNumberTheory.AnalyticTools.FourthRootMeanComparison

/-!
# Comparing a primitive character moment with its reduced diagonal
-/
noncomputable section
open Real Complex Finset Set MeasureTheory Filter
open scoped Interval Topology
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

theorem continuous_character_critical_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => χ.LFunction ((1/2:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t;have he : (1/2:ℂ)+(t:ℂ)*I≠1 := by intro h;have hh := congrArg Complex.re h;norm_num at hh
  exact (ZMod.differentiableAt_LFunction χ _ (Or.inl he)).continuousAt.comp
    (f:=fun t : ℝ => (1/2:ℂ)+t*I) (by fun_prop)

private theorem primitive_wave_energy {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi*q≤T →
    let N := primitiveCriticalLength q T
    let P := weightedHardyPolynomial (Real.sqrt q) (primitiveWaveWeight χ) N
    |(∫t in (8*Real.pi*q)..T,‖P t‖^2)-
      ∫t in (8*Real.pi*q)..T,primitiveCriticalDiagonal χ t|≤C*Real.sqrt T*(1+Real.log T) := by
  let D := 16/Real.log 2+8
  have hD : 0<D := by dsimp [D];positivity
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  refine ⟨32+8*D*Real.sqrt q,by positivity,?_⟩
  intro T ht N P
  let b := 8*Real.pi*q
  have hb : 0<b := by dsimp [b];positivity
  have hp := hb.trans_le ht
  have htq : (q:ℝ)≤T := by nlinarith [mul_le_mul_of_nonneg_right (show 1≤8*Real.pi by linarith [Real.pi_gt_three]) hq.le]
  have hN : 1≤N := by
    apply (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr;norm_num
    apply (le_div_iff₀ (by positivity : 0<2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hq₁ hp.le,mul_le_mul_of_nonneg_left hq₁ (show 0≤8*Real.pi by positivity)]
  have hscale : (N:ℝ)≤Real.sqrt q*Real.sqrt T := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans
    rw [←Real.sqrt_mul hq.le];apply Real.sqrt_le_sqrt
    exact div_le_self (mul_nonneg hq.le hp.le) (by linarith [Real.pi_gt_three])
  have hNT : (N:ℝ)≤T := hscale.trans (by
    calc Real.sqrt q*Real.sqrt T ≤ Real.sqrt T*Real.sqrt T := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt htq) (Real.sqrt_nonneg _)
         _ = T := Real.mul_self_sqrt hp.le)
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hN) hNT
  have hL : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
  have hm {t : ℝ} (htT : t≤T) : primitiveCriticalLength q t≤N :=
    Nat.floor_mono (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htT hq.le) (by positivity)))
  have H := weighted_hardy_energy_bound (Real.sqrt_pos.mpr hq) (primitiveWaveWeight χ)
    (fun i => (norm_primitiveWaveWeight hχ i).trans_le (χ.norm_le_one _)) hb ht N hN
  have he : (∫t in b..T,‖P t‖^2-weightedHardyDiagonal (Real.sqrt q) (primitiveWaveWeight χ) N t)=
      (∫t in b..T,‖P t‖^2)-(∫t in b..T,primitiveCriticalDiagonal χ t) := by
    rw [←intervalIntegral.integral_sub (f:=fun t=>‖P t‖^2) (g:=primitiveCriticalDiagonal χ)
      (weightedHardyPolynomial_sq_intervalIntegrable ..) (primitiveCriticalDiagonal_monotone χ).intervalIntegrable]
    apply intervalIntegral.integral_congr;intro t h;rw [uIcc_of_le (show b≤T from ht)] at h
    dsimp only;rw [weightedHardyDiagonal_primitive hχ (hb.le.trans h.1) (hm h.2)]
  rw [←he];apply H.trans
  have h₁ := mul_le_mul_of_nonneg_left (show 1+Real.log N≤1+Real.log T by linarith) (show 0≤32*Real.sqrt T by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (mul_le_mul hscale (show 1+Real.log N≤1+Real.log T by linarith) hL (by positivity)) (show 0≤8*D by positivity)
  dsimp only [D] at *;linarith only [h₁,h₂]

set_option maxHeartbeats 800000 in
/-- The integrated error between the primitive critical-line square
and its moving diagonal. -/
theorem primitive_moment_diagonal_comparison {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
      |(∫t in (8*Real.pi*q)..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)-
        ∫t in (8*Real.pi*q)..T,primitiveCriticalDiagonal χ t|≤C*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)) := by
  obtain ⟨D,hD,HD⟩ := primitive_critical_polynomial_error hχ
  obtain ⟨B,hB,HB⟩ := primitive_wave_energy hχ
  let b := 8*Real.pi*q
  let z := fun t : ℝ => ‖χ.LFunction ((1/2:ℂ)+t*I)‖
  let k := (q.totient/q:ℝ)
  have hc : Continuous z := (continuous_character_critical_line χ).norm
  have hq : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hk : 0≤k := by dsimp [k];positivity
  have hb : 8*Real.pi≤b := by dsimp [b];exact le_mul_of_one_le_right (by positivity) hq
  have hb₁ : 1≤b := by linarith [Real.pi_gt_three]
  refine ⟨(k+1)+4*D^2+5*B,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop b,(mean_sq_LFunction_half χ).eventually_lt_const (show k<k+1 by linarith)] with T ht hH
  have hT : 1<T := by linarith [Real.pi_gt_three]
  have hp := zero_lt_one.trans hT
  change (∫t in (1:ℝ)..T,z t^2)/(T*Real.log T)<k+1 at hH
  rw [div_lt_iff₀ (mul_pos hp (Real.log_pos hT)),←intervalIntegral.integral_add_adjacent_intervals (f:=fun t=>z t^2)
    ((hc.pow 2).intervalIntegrable (μ:=volume) 1 b) ((hc.pow 2).intervalIntegrable (μ:=volume) b T)] at hH
  have hz₀ : 0≤∫t in (1:ℝ)..b,z t^2 := intervalIntegral.integral_nonneg hb₁ (fun _ _ => sq_nonneg _)
  have hZ : (∫t in b..T,z t^2)≤(k+1)*T*Real.log (T+2) := by
    linarith [mul_le_mul_of_nonneg_left (Real.log_le_log hp (show T≤T+2 by linarith)) (show 0≤(k+1)*T by positivity)]
  let N := primitiveCriticalLength q T
  let P := weightedHardyPolynomial (Real.sqrt q) (primitiveWaveWeight χ) N
  have Hd (t : ℝ) (htt : t∈Set.Icc b T) : |z t-‖P t‖|≤D*t^(-(1/4:ℝ)) := by
    have hN : primitiveCriticalLength q t≤N := Nat.floor_mono (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htt.2 (Nat.cast_nonneg q)) (by positivity)))
    have he : P t=primitiveCriticalPolynomial χ (primitiveCriticalLength q t) t :=
      weightedHardyPolynomial_primitive χ (by linarith [htt.1] : 0≤t) hN
    rw [he];exact HD htt.1
  have H := fourth_root_mean_square_comparison (p:=fun t => ‖P t‖) (T:=T) hb ht hc (show 0<k+1 by positivity) hD hZ Hd
  rw [intervalIntegral.integral_sub (f:=fun t=>z t^2) (g:=fun t=>‖P t‖^2)
    ((hc.pow 2).intervalIntegrable ..) (weightedHardyPolynomial_sq_intervalIntegrable ..)] at H
  let V := T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))
  have hL : 1≤Real.sqrt (Real.log (T+2)) := Real.le_sqrt_of_sq_le (by
    rw [one_pow,←Real.log_exp 1];apply Real.log_le_log (Real.exp_pos _);linarith [Real.exp_one_lt_d9,Real.pi_gt_three])
  have hR : Real.sqrt T*(1+Real.log T)≤5*V := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp (1/4:ℝ));rw [Real.log_rpow hp] at h
    have he : Real.sqrt T*T^(1/4:ℝ)=T^(3/4:ℝ) := by rw [Real.sqrt_eq_rpow,←Real.rpow_add hp];norm_num
    have h₀ := mul_le_mul_of_nonneg_left (show 1+Real.log T≤5*T^(1/4:ℝ) by linarith [Real.one_le_rpow hT.le (by norm_num : 0≤(1/4:ℝ))]) (Real.sqrt_nonneg T)
    have hh : T^(3/4:ℝ)≤V := le_mul_of_one_le_right (by positivity) hL
    linarith only [h₀,he,hh]
  have J : |(∫t in b..T,‖P t‖^2)-∫t in b..T,primitiveCriticalDiagonal χ t|≤B*Real.sqrt T*(1+Real.log T) := HB ht
  change |(∫t in b..T,z t^2)-(∫t in b..T,‖P t‖^2)|≤((k+1)+4*D^2)*T^(3/4:ℝ)*_ at H
  rw [mul_assoc] at H
  change |(∫t in b..T,z t^2)-(∫t in b..T,‖P t‖^2)|≤((k+1)+4*D^2)*V at H
  change |(∫t in b..T,z t^2)-(∫t in b..T,primitiveCriticalDiagonal χ t)|≤((k+1)+4*D^2+5*B)*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))
  rw [show ((k+1)+4*D^2+5*B)*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))=((k+1)+4*D^2+5*B)*V by dsimp [V];ring]
  linarith only [H,J,mul_le_mul_of_nonneg_left hR hB.le,abs_sub_le (∫t in b..T,z t^2) (∫t in b..T,‖P t‖^2) (∫t in b..T,primitiveCriticalDiagonal χ t)]

end AnalyticNumberTheory.DirichletLFunctions
