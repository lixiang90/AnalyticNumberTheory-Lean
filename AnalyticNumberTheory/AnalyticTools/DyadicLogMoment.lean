import AnalyticNumberTheory.AnalyticTools.DyadicAsymptotics

/-!
# Transferring a logarithmic remainder from dyadic intervals

A dyadic integral with main term cT(log T)^(k+1) and error of size
T(log T)^k has the same global main term and error order from height zero.
The estimate applies to signed continuous integrands and all endpoints T ≥ 2.
-/

open Real Filter MeasureTheory Set
open scoped Topology Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- The logarithm raised to a positive integer power changes by at most
one lower power when its argument is doubled. -/
private theorem log_pow_doubling (k : ℕ) {T : ℝ} (hT : 2≤T) :
    |(log (2*T))^(k+1)-(log T)^(k+1)| ≤
      (log 2*(k+1)*(2:ℝ)^k)*(log T)^k := by
  have ht : 0<T := by linarith
  have h₂ : 0≤log 2 := log_nonneg (by norm_num)
  have hl : log 2≤log T := log_le_log (by norm_num) hT
  have hl' : 0≤log T := h₂.trans hl
  have hsum : 0≤log 2+log T := add_nonneg h₂ hl'
  rw [log_mul (by norm_num) ht.ne']
  have H := abs_pow_sub_pow_le (log 2+log T) (log T) (k+1)
  rw [add_sub_cancel_right,abs_of_nonneg h₂,abs_of_nonneg hsum,abs_of_nonneg hl',
    max_eq_left (le_add_of_nonneg_left h₂),Nat.add_sub_cancel] at H
  refine H.trans ?_
  have hc := pow_le_pow_left₀ hsum (show log 2+log T≤2*log T by linarith) k
  rw [mul_pow] at hc
  push_cast at H ⊢
  exact (mul_le_mul_of_nonneg_left hc (show 0≤log 2*((k:ℝ)+1) by positivity)).trans_eq (by ring)

/-- Quantitative transfer of a logarithmic main term of any positive degree.
The dyadic error can hold only eventually. Continuity covers the compact
initial range in the resulting estimate. -/
theorem log_moment_of_dyadic {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) (c : ℝ)
    (H : ∃ D : ℝ, 0<D ∧ ∀ᶠ T : ℝ in atTop,
      |(∫t in T..2*T,f t)-c*T*(log T)^(k+1)|≤D*T*(1+log T)^k) :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ}, 2≤T →
      |(∫t in (0:ℝ)..T,f t)-c*T*(log T)^(k+1)|≤C*T*(log T)^k := by
  obtain ⟨D,hD,HD⟩ := H
  obtain ⟨X,hX⟩ := eventually_atTop.mp HD
  let A := max (max X 2) (exp 1)
  let e := log 2*(k+1)*(2:ℝ)^k
  let K := D*2^k+2 * |c| * e
  let W := fun t : ℝ => (log t)^k
  let G := fun t : ℝ => (∫v in (0:ℝ)..t,f v)-c*t*(log t)^(k+1)
  have hA : 2≤A := (le_max_right X 2).trans (le_max_left ..)
  have he : 0≤e := by dsimp [e];positivity
  have hK : 0<K := add_pos_of_pos_of_nonneg (mul_pos hD (by positivity)) (by positivity)
  have hstep (T : ℝ) (ht : A≤T) : |G (2*T)-G T| ≤ K*T*W T := by
    have ht2 := hA.trans ht
    have ht0 : 0≤T := by linarith
    have hl : 1≤log T := (Real.le_log_iff_exp_le (by linarith)).mpr ((le_max_right ..).trans ht)
    have hfirst := hX T ((le_max_left X 2).trans ((le_max_left ..).trans ht))
    have hpow := pow_le_pow_left₀ (show 0≤1+log T by linarith) (show 1+log T≤2*log T by linarith) k
    rw [mul_pow] at hpow
    have h₁ := hfirst.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hD.le ht0))
    have h₂ := mul_le_mul_of_nonneg_left (log_pow_doubling k ht2) (show 0≤2 * |c| * T by positivity)
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (a:=(0:ℝ)) (b:=T) (c:=2*T)
      (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)
    have hid : G (2*T)-G T=((∫t in T..2*T,f t)-c*T*(log T)^(k+1))-
        (2*c*T)*((log (2*T))^(k+1)-(log T)^(k+1)) := by dsimp [G];rw [←hi];ring
    rw [hid]
    apply (abs_sub ..).trans
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg ht0,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact (add_le_add h₁ h₂).trans_eq (by dsimp [K,e,W];ring)
  have hG : ContinuousOn G (Ici 2) := (intervalIntegral.continuous_primitive (μ:=volume)
      (fun a b => hf.intervalIntegrable a b) 0).continuousOn.sub
    ((continuousOn_const.mul continuousOn_id).mul ((continuousOn_id.log (fun t ht => by change 2≤t at ht;change t≠0;linarith)).pow (k+1)))
  have hW : ContinuousOn W (Ici 2) := (continuousOn_id.log (fun t ht => by change 2≤t at ht;change t≠0;linarith)).pow k
  have hWpos (t : ℝ) (ht : 2≤t) : 0<W t := pow_pos (log_pos (by linarith)) k
  have hWmono {s t : ℝ} (hs : 2≤s) (hst : s≤t) : W s≤W t :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hst) k
  have hc : ContinuousOn (fun t : ℝ => |G t|/(t*W t)) (Ici 2) :=
    hG.abs.div (continuousOn_id.mul hW) (fun t ht => by
      change 2≤t at ht; exact (mul_pos (by linarith) (hWpos t ht)).ne')
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.mono (show Icc 2 (2*A)⊆Ici 2 by
    intro t ht;exact ht.1))
  let C := max B K
  have hC : 0<C := hK.trans_le (le_max_right ..)
  have hbase {T : ℝ} (ht : 2≤T) (hlo : T≤2*A) : |G T|≤C*T*W T := by
    have h := hB ⟨T,⟨ht,hlo⟩,rfl⟩
    change |G T|/(T*W T)≤B at h
    exact ((div_le_iff₀ (mul_pos (by linarith) (hWpos T ht))).mp (h.trans (le_max_left B K))).trans_eq (by ring)
  have hbound (n : ℕ) {T : ℝ} (ht : 2≤T) (hn : T≤(2:ℝ)^n*(2*A)) : |G T|≤C*T*W T := by
    induction n generalizing T with
    | zero => exact hbase ht (by simpa using hn)
    | succ n ih =>
      by_cases hsmall : T≤2*A
      · exact hbase ht hsmall
      have hhalf : A≤T/2 := by linarith
      have hh := ih (hA.trans hhalf) (show T/2≤(2:ℝ)^n*(2*A) by rw [pow_succ] at hn;linarith only [hn])
      have hd := hstep (T/2) hhalf
      rw [show 2*(T/2)=T by ring] at hd
      have h₂ := mul_le_mul_of_nonneg_right (le_max_right B K) (show 0≤(T/2)*W (T/2) from
        mul_nonneg (by linarith) (hWpos _ (hA.trans hhalf)).le)
      have h₃ := mul_le_mul_of_nonneg_left (hWmono (hA.trans hhalf) (show T/2≤T by linarith))
        (show 0≤C*T by positivity)
      have he : |G T|≤|G T-G (T/2)|+|G (T/2)| := by simpa using abs_add_le (G T-G (T/2)) (G (T/2))
      change K*((T/2)*W (T/2)) ≤ C*((T/2)*W (T/2)) at h₂
      linarith only [he,hd,hh,h₂,h₃]
  refine ⟨C,hC,?_⟩
  intro T ht
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (T/(2*A)) (by norm_num : (1:ℝ)<2)
  exact hbound n ht ((div_lt_iff₀ (by linarith : 0<2*A)).mp hn).le

/-- A dyadic fourth-logarithmic moment estimate gives the same global
leading coefficient with a cubic logarithmic error for every T ≥ 2. -/
theorem fourth_log_moment_of_dyadic {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ)
    (H : ∃ D : ℝ,0<D ∧ ∀ᶠ T : ℝ in atTop,
      |(∫t in T..2*T,f t)-c*T*(log T)^4|≤D*T*(1+log T)^3) :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ}, 2≤T →
      |(∫t in (0:ℝ)..T,f t)-c*T*(log T)^4|≤C*T*(log T)^3 :=
  log_moment_of_dyadic hf 3 c H

end AnalyticNumberTheory.AnalyticTools
