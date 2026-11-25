import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalLogIntegral

/-!
# Horizontal logarithmic means inside an analytic disk

These estimates use the segment from one half to two, centered at its
right endpoint. The disk stays inside the positive half-plane when translated
vertically, as needed for the logarithmic mean of the zeta function.
-/

open Complex Real Set Filter Metric Finset MeasureTheory
open scoped Topology Interval
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Integral of the log modulus along the segment from one half to two. -/
noncomputable def horizontalLogMean (f : ℂ→ℂ) (t : ℝ) : ℝ :=
  ∫ x in (1/2:ℝ)..2, Real.log ‖f ((x:ℂ)+(t:ℂ)*I)‖

private theorem segment_distance {x t T : ℝ} (hx : x∈Set.Icc (1/2:ℝ) 2) :
    ‖((x:ℂ)+(t:ℂ)*I)-(2+(T:ℂ)*I)‖ ≤ 3/2+|t-T| := by
  rw [show ((x:ℂ)+(t:ℂ)*I)-(2+(T:ℂ)*I) = ((x-2:ℝ):ℂ)+((t-T:ℝ):ℂ)*I by push_cast;ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hx.2)]
  linarith [hx.1]

/-- Continuity in height of the horizontal logarithmic mean. Zeros may lie
on the central segment or on neighboring segments. -/
theorem continuousAt_horizontalLogMean {f : ℂ→ℂ} {T M : ℝ} (hM : 0<M)
    (hf : AnalyticOnNhd ℂ f (closedBall (2+(T:ℂ)*I) (7/4)))
    (hc : f (2+(T:ℂ)*I)≠0) (hb : ∀ z∈sphere (2+(T:ℂ)*I) (7/4), ‖f z/f (2+(T:ℂ)*I)‖≤M) :
    ContinuousAt (horizontalLogMean f) T := by
  let c : ℂ := 2+(T:ℂ)*I
  let U := closedBall c (13/8)
  let J := Set.Icc (T-1/16) (T+1/16)
  have hsub : U⊆closedBall c (7/4) := closedBall_subset_closedBall (by norm_num)
  have hrect (x : ℝ) (hx : x∈Set.Icc (1/2:ℝ) 2) (t : ℝ) (ht : t∈J) : (x:ℂ)+(t:ℂ)*I∈U := by
    rw [show U=closedBall c (13/8) by rfl,mem_closedBall,dist_eq_norm]
    apply (segment_distance hx).trans
    have ht' : |t-T|≤1/16 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    linarith only [ht']
  obtain ⟨Z,g,_,_,hg,hn,_,H⟩ := disk_log_norm_factorization (r:=13/8) (by norm_num) (by norm_num) hM hf hc hb
  let m := analyticOrderNatAt f
  have hgc : ContinuousOn g U := (hg.mono hsub).continuousOn
  have hlog := hgc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))
  have hJ : J∈𝓝 T := Icc_mem_nhds (by linarith) (by linarith)
  have hreg := (continuousOn_horizontalIntegral (by norm_num : (1/2:ℝ)≤2)
    (by linarith : T-1/16≤T+1/16) hlog hrect).continuousAt hJ
  have hsing : Continuous (fun t : ℝ => ∑ u∈Z,(m u:ℝ)*(∫ x in (1/2:ℝ)..2,horizontalLogKernel u t x)) :=
    continuous_finsetSum _ (fun u _ => continuous_const.mul (continuous_integral_horizontalLogKernel u _ _))
  apply (hsing.continuousAt.add hreg).congr_of_eventuallyEq
  filter_upwards [hJ] with t ht
  exact (integral_log_norm_of_factors Z m hgc hn H (by norm_num) (fun x hx => hrect x hx t ht)).2

/-- The horizontal logarithmic mean grows at most logarithmically in the
outer-circle bound, provided every enclosed zero is at least one unit from
the center. The constants are uniform in the function and in height. -/
theorem abs_horizontalLogMean_le :
    ∃ C : ℝ, 0<C ∧ ∀ {f : ℂ→ℂ} {T M : ℝ}, 1≤M →
      let c : ℂ := 2+(T:ℂ)*I
      AnalyticOnNhd ℂ f (closedBall c (7/4)) → f c≠0 →
      (∀ z∈sphere c (7/4), ‖f z/f c‖≤M) →
      (∀ u∈zeroSet f c (13/8), 1≤‖c-u‖) →
      |horizontalLogMean f T|≤ C*(|Real.log ‖f c‖|+Real.log M) := by
  obtain ⟨K,hK,hkern⟩ := horizontalLogKernel_integral_abs_bound (a:=1/2) (b:=2) (K:=4) (by norm_num) (by norm_num)
  let L := Real.log (14/13)
  have hL : 0<L := Real.log_pos (by norm_num)
  let A := K+3+36*Real.log 13
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨38+A/L,by positivity,?_⟩
  intro f T M hM c hf hc hb hsep
  have hm := zero_lt_one.trans_le hM
  obtain ⟨Z,g,hZ,hN,hg,hn,hgb,H⟩ := disk_log_norm_factorization (r:=13/8) (by norm_num) (by norm_num) hm hf hc hb
  let m := analyticOrderNatAt f
  let N := ∑ u∈Z,m u
  have hN' : (N:ℝ)≤Real.log M/L := by
    dsimp only [N,L,m];push_cast;norm_num at hN ⊢;exact hN
  have hsub : closedBall c (13/8)⊆closedBall c (7/4) := closedBall_subset_closedBall (by norm_num)
  have hz (x : ℝ) (hx : x∈Set.Icc (1/2:ℝ) 2) : (x:ℂ)+(T:ℂ)*I∈closedBall c (3/2) := by
    rw [mem_closedBall,dist_eq_norm]
    simpa only [sub_self,abs_zero,add_zero] using segment_distance (T:=T) (t:=T) hx
  have hsub' : closedBall c (3/2)⊆closedBall c (13/8) := closedBall_subset_closedBall (by norm_num)
  have hrr := integral_log_norm_of_factors Z m (hg.mono hsub).continuousOn hn H (by norm_num : (1/2:ℝ)≤2)
    (fun x hx => hsub' (hz x hx))
  have hmem {u : ℂ} (hu : u∈Z) : u∈zeroSet f c (13/8) := hZ ▸ (show u∈(Z:Set ℂ) from hu)
  have hd {u : ℂ} (hu : u∈Z) : ‖c-u‖≤13/8 := by
    rw [norm_sub_rev,←dist_eq_norm];exact (mem_closedBall.mp (hmem hu).1)
  have hclog : |Real.log ‖g c‖| ≤ |Real.log ‖f c‖|+2*N := by
    have hcn : c∉Z := fun h => hc (hmem h).2
    have he := H c (mem_closedBall_self (by norm_num)) hcn
    have hsum : |∑ u∈Z, (m u:ℝ)*Real.log ‖c-u‖|≤2*N := by
      apply (abs_sum_le_sum_abs ..).trans
      calc _ ≤ ∑ u∈Z,(m u:ℝ)*2 := by
             apply sum_le_sum
             intro u hu
             rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Real.log_nonneg (hsep u (hmem hu)))]
             exact mul_le_mul_of_nonneg_left ((Real.log_le_self (norm_nonneg _)).trans ((hd hu).trans (by norm_num))) (Nat.cast_nonneg _)
           _ = _ := by dsimp [N];push_cast;rw [←sum_mul,mul_comm]
    change Real.log ‖f c‖=(∑ u∈Z,(m u:ℝ)*Real.log ‖c-u‖)+Real.log ‖g c‖ at he
    rw [show Real.log ‖g c‖=Real.log ‖f c‖-∑ u∈Z,(m u:ℝ)*Real.log ‖c-u‖ by linarith only [he] ]
    exact (abs_sub ..).trans (add_le_add le_rfl hsum)
  have hreg : |∫ x in (1/2:ℝ)..2,Real.log ‖g ((x:ℂ)+(T:ℂ)*I)‖| ≤
      (|Real.log ‖f c‖|+2*N+24*(Real.log M+N*Real.log 13))*(3/2) := by
    have Hreg := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun x : ℝ => Real.log ‖g ((x:ℂ)+(T:ℂ)*I)‖) (a:=1/2) (b:=2)
      (C:=|Real.log ‖f c‖|+2*N+24*(Real.log M+N*Real.log 13)) (fun x hx => by
        have hx' : x∈Set.Icc (1/2:ℝ) 2 := by rw [uIoc_of_le (by norm_num)] at hx;exact Ioc_subset_Icc_self hx
        have hlog := abs_log_norm_sub_le_of_ne_zero (r:=3/2) (R:=13/8) (M:=M*13^N) (by norm_num) (by norm_num)
          (hg.differentiableOn.mono (ball_subset_closedBall.trans hsub)) (fun u hu => hn u (ball_subset_closedBall hu))
          (fun u hu => (hgb u (hsub (ball_subset_closedBall hu))).trans_eq (by norm_num [N,m])) (hz x hx')
        rw [Real.log_mul hm.ne' (by positivity),Real.log_pow] at hlog
        norm_num at hlog
        rw [Real.norm_eq_abs]
        have htri := abs_sub_le (Real.log ‖g ((x:ℂ)+(T:ℂ)*I)‖) (Real.log ‖g c‖) 0
        simp only [sub_zero] at htri
        linarith only [htri,hlog,hclog])
    norm_num at Hreg ⊢
    exact Hreg
  have hsing : |∑ u∈Z,(m u:ℝ)*(∫ x in (1/2:ℝ)..2,horizontalLogKernel u T x)|≤K*N := by
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ u∈Z,(m u:ℝ)*K := by
           apply sum_le_sum
           intro u hu
           have hu' : ‖u-(T:ℂ)*I‖≤4 := by
             have he : u-(T:ℂ)*I=(u-c)+2 := by dsimp [c];ring
             rw [he];apply (norm_add_le ..).trans
             rw [norm_sub_rev];norm_num;linarith only [hd hu]
           rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
           apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
           apply le_trans _ (hkern u T hu')
           simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
             (f:=horizontalLogKernel u T) (μ:=volume) (by norm_num : (1/2:ℝ)≤2)
         _ = _ := by dsimp [N];push_cast;rw [←sum_mul,mul_comm]
  unfold horizontalLogMean
  rw [hrr.2]
  apply (abs_add_le ..).trans ((add_le_add hsing hreg).trans ?_)
  have HN := mul_le_mul_of_nonneg_left hN' hA
  have hb₀ := abs_nonneg (Real.log ‖f c‖)
  have hm₀ := Real.log_nonneg hM
  have hpad := mul_nonneg hb₀ (div_nonneg hA hL.le)
  dsimp only [A] at HN hpad ⊢
  simp only [div_eq_mul_inv] at HN hpad ⊢
  linarith only [HN,hb₀,hm₀,hpad]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
