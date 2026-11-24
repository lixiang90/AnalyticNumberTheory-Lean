import AnalyticNumberTheory.AnalyticTools.DyadicIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing from dyadic means to a global asymptotic

A normalized increment with limit zero sums to an error of smaller
order for a positive nondecreasing weight. This applies to every
fixed power of the logarithm.
-/

open Real Filter MeasureTheory Set
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private theorem dyadic_small {G w : ℝ → ℝ} (hc : ContinuousOn G (Ici 1))
    (hw : MonotoneOn w (Ici 1)) (hw1 : ∀ T, 2≤T → 0<w T)
    (hinf : Tendsto (fun T : ℝ => T*w T) atTop atTop)
    (hd : Tendsto (fun T : ℝ => (G (2*T)-G T)/(T*w T)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => G T/(T*w T)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds] at hd ⊢
  intro ε hε
  obtain ⟨s,hs⟩ := eventually_atTop.1 (hd (ε/2) (half_pos hε))
  let A := max s 2
  have hA : 2≤A := le_max_right ..
  have hA' : 0<A := by linarith
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image
    ((hc.norm).mono (show Icc A (2*A) ⊆ Ici 1 from fun x hx => by change 1≤x; linarith [hx.1]))
  have hinterval (T : ℝ) (ht : A≤T) : |G (2*T)-G T| ≤ (ε/2)*(T*w T) := by
    have h := hs T ((le_max_left ..).trans ht)
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos (mul_pos (by linarith) (hw1 _ (hA.trans ht)))] at h
    exact ((div_lt_iff₀ (mul_pos (by linarith) (hw1 _ (hA.trans ht)))).mp h).le
  have hbase {T : ℝ} (hlo : A≤T) (h : T≤2*A) : |G T|≤ B+(ε/2)*(T*w T) := by
    have hh : |G T| ≤ B := hB ⟨T,⟨hlo,h⟩,rfl⟩
    have hnon := (hw1 T (hA.trans hlo)).le
    linarith only [hh,mul_nonneg (half_pos hε).le (mul_nonneg (hA'.le.trans hlo) hnon)]
  have hbound (n : ℕ) (T : ℝ) (hlo : A≤T) (hhi : T≤2^n*(2*A)) :
      |G T| ≤ B+(ε/2)*(T*w T) := by
    induction n generalizing T with
    | zero => apply hbase hlo; simpa only [pow_zero,one_mul] using hhi
    | succ n ih =>
      by_cases h : T≤2*A
      · exact hbase hlo h
      · have ht : 0<T := hA'.trans_le hlo
        have hh : A≤T/2 := by linarith
        have hi : T/2≤2^n*(2*A) := by rw [pow_succ] at hhi; linarith only [hhi]
        have hh' := ih (T/2) hh hi
        have hd' := hinterval (T/2) hh
        rw [show 2*(T/2)=T by ring] at hd'
        have hs := hw (show T/2∈Ici 1 by change 1≤T/2; linarith) (show T∈Ici 1 by change 1≤T; linarith) (by linarith)
        have he : |G T| ≤ |G T-G (T/2)|+|G (T/2)| := by
          simpa only [sub_add_cancel] using abs_add_le (G T-G (T/2)) (G (T/2))
        nlinarith only [he,hd',hh',mul_le_mul_of_nonneg_left hs (show 0≤(ε/2)*T by positivity)]
  have hb := (tendsto_const_nhds.div_atTop hinf (a:=B)).eventually_lt_const (half_pos hε)
  filter_upwards [eventually_ge_atTop A,hb] with T hT hB'
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (T/(2*A)) (by norm_num : (1:ℝ)<2)
  have hh := hbound n T hT ((div_lt_iff₀ (by positivity)).mp hn).le
  have hden := mul_pos (show 0<T by linarith) (hw1 _ (hA.trans hT))
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hden,div_lt_iff₀ hden]
  nlinarith only [hh,(div_lt_iff₀ hden).mp hB']

/-- A dyadic integral asymptotic with normalization `T (log T)^k`
gives the same leading constant for integration from one. -/
theorem integral_from_one_of_dyadic_asymptotic {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) {c : ℝ}
    (h : Tendsto (fun T : ℝ => (∫ t in T..2*T, f t)/(T*(Real.log T)^k)) atTop (𝓝 c)) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, f t)/(T*(Real.log T)^k)) atTop (𝓝 c) := by
  let w := fun T : ℝ => (Real.log T)^k
  let G := fun T : ℝ => (∫ t in (1:ℝ)..T, f t)-c*(T*w T)
  have hw : MonotoneOn w (Ici 1) := by
    intro a ha b _ hab
    exact pow_le_pow_left₀ (Real.log_nonneg ha) (Real.log_le_log (by change 1≤a at ha; linarith) hab) _
  have hw1 (T : ℝ) (hT : 2≤T) : 0<w T := pow_pos (Real.log_pos (by linarith)) _
  have hc : ContinuousOn G (Ici 1) := (intervalIntegral.continuous_primitive (μ:=volume) (fun a b => hf.intervalIntegrable a b) 1).continuousOn.sub
    (continuousOn_const.mul (continuousOn_id.mul ((continuousOn_id.log (fun t ht => by change 1≤t at ht; change t≠0; linarith)).pow k)))
  have hinf : Tendsto (fun T : ℝ => T*w T) atTop atTop := by
    apply tendsto_atTop_mono' _ _ (tendsto_id (α:=ℝ))
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with T ht
    have hT : 0<T := (Real.exp_pos _).trans_le ht
    have hl : 1≤Real.log T := by simpa using Real.log_le_log (Real.exp_pos _) ht
    exact le_mul_of_one_le_right hT.le (one_le_pow₀ hl)
  have hr : Tendsto (fun T : ℝ => Real.log (2*T)/Real.log T) atTop (𝓝 1) := by
    apply (show Tendsto (fun T : ℝ => Real.log 2/Real.log T+1) atTop (𝓝 1) by
      simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop (a:=Real.log 2)).add_const 1).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    rw [Real.log_mul (by norm_num) (by linarith),add_div,div_self (Real.log_pos hT).ne']
  have hr' : Tendsto (fun T : ℝ => (2*T*w (2*T)-T*w T)/(T*w T)) atTop (𝓝 1) := by
    apply (show Tendsto (fun T : ℝ => 2*(Real.log (2*T)/Real.log T)^k-1) atTop (𝓝 1) by
      simpa only [one_pow, mul_one,show (2:ℝ)-1=1 by norm_num] using ((hr.pow k).const_mul 2).sub_const 1).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    dsimp [w]; rw [div_pow]; field_simp [show T≠0 by linarith,(Real.log_pos ht).ne'] <;> ring
  have hinc : Tendsto (fun T : ℝ => (G (2*T)-G T)/(T*w T)) atTop (𝓝 0) := by
    apply (show Tendsto (fun T : ℝ => (∫ t in T..2*T, f t)/(T*w T) -
        c*((2*T*w (2*T)-T*w T)/(T*w T))) atTop (𝓝 0) by simpa using h.sub (hr'.const_mul c)).congr
    intro T
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (a:=(1:ℝ)) (b:=T) (c:=2*T)
      (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)
    dsimp [G]; rw [← hsplit]; ring
  have hsmall := dyadic_small hc hw hw1 hinf hinc
  apply (show Tendsto (fun T : ℝ => G T/(T*w T)+c) atTop (𝓝 c) by simpa using hsmall.add_const c).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
  dsimp [G,w]; field_simp [show T≠0 by linarith,(Real.log_pos ht).ne'] <;> ring

end AnalyticNumberTheory.AnalyticTools
