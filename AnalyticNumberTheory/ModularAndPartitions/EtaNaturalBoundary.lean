import AnalyticNumberTheory.ModularAndPartitions.PartitionNaturalBoundary
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The real line as the natural boundary of Dedekind eta

At every rational point the vertical limit is zero. An analytic
extension at a real point would therefore have zeros accumulating
there, contradicting nonvanishing in the upper half-plane.
-/

open Complex Real Set Filter
open scoped Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private noncomputable def etaCuspParameter (q : ℚ) (t : ℝ) : ℂ := (((t⁻¹:ℝ):ℂ)-q.num*I)/q.den

private theorem etaCusp_parameter_pos (q : ℚ) {t : ℝ} (ht : 0<t) :
    0<(etaCuspParameter q t).re := by
  simp only [etaCuspParameter,div_eq_mul_inv,←Complex.ofReal_natCast,←Complex.ofReal_inv,Complex.mul_re,
    Complex.ofReal_im,Complex.ofReal_re,Complex.sub_re,Complex.I_re,Complex.intCast_im,neg_zero,sub_zero,mul_zero,zero_mul]
  exact mul_pos (inv_pos.mpr ht) (inv_pos.mpr (by exact_mod_cast q.den_pos))

private theorem etaCuspPoint_eq (q : ℚ) (t : ℝ) :
    I*etaCuspParameter q t=(q:ℂ)+((t⁻¹:ℝ):ℂ)/q.den*I := by
  rw [etaCuspParameter,Rat.cast_def]
  linear_combination (-(q.num:ℂ)/(q.den:ℂ))*Complex.I_mul_I

private theorem etaCuspPoint_tends (q : ℚ) :
    Tendsto (fun t : ℝ => I*etaCuspParameter q t) atTop (𝓝 (q:ℂ)) := by
  simp only [etaCuspPoint_eq]
  have H : Tendsto (fun t : ℝ => ((t⁻¹:ℝ):ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  simpa using (tendsto_const_nhds (x:=(q:ℂ))).add ((H.div_const _).mul_const I)

private theorem etaCuspPoint_vanishes (q : ℚ) :
    Tendsto (fun t : ℝ => ModularForm.eta (I*etaCuspParameter q t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have H := etaCuspPoint_tends q
  have H' : Tendsto (etaCuspParameter q) atTop (𝓝 ((-I)*(q:ℂ))) := by
    simpa only [←mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul] using H.const_mul (-I)
  have hcont : Continuous (fun u : ℂ => ‖Complex.exp (-(π:ℂ)*u/12)‖) := by fun_prop
  have he := hcont.continuousAt.tendsto.comp H'
  have hF := (tendsto_norm_partitionGenFun_at_rat q).inv_tendsto_atTop
  have hL := he.mul hF
  rw [mul_zero] at hL
  apply hL.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),(tendsto_norm_partitionGenFun_at_rat q).eventually_gt_atTop 0] with t ht hF'
  have Hmul := congrArg norm (eta_mul_partitionGenFun_nome (etaCusp_parameter_pos q ht))
  simp only [norm_mul] at Hmul
  change ‖ModularForm.eta (I*etaCuspParameter q t)‖*‖partitionGenFun (partitionCuspNome q.num q.den ((t⁻¹:ℝ):ℂ))‖=_ at Hmul
  change ‖Complex.exp (-(π:ℂ)*etaCuspParameter q t/12)‖*_ = _
  rw [←Hmul,Pi.inv_apply,mul_inv_cancel_right₀ hF'.ne']

/-- The vertical limit of Dedekind eta at every rational boundary point is zero. -/
theorem tendsto_eta_at_rational (q : ℚ) :
    Tendsto (fun y : ℝ => ModularForm.eta ((q:ℂ)+(y:ℂ)*I)) (𝓝[>] 0) (𝓝 0) := by
  have hden : 0<(q.den:ℝ) := by exact_mod_cast q.den_pos
  have hT := tendsto_inv_nhdsGT_zero.atTop_div_const hden
  apply ((etaCuspPoint_vanishes q).comp hT).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  dsimp
  rw [etaCuspPoint_eq]
  congr 1
  push_cast
  field_simp [show (q.den:ℂ)≠0 by exact_mod_cast q.den_nz]

private theorem tends_vertical (x : ℝ) :
    Tendsto (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) (𝓝[>] 0) (𝓝 (x:ℂ)) := by
  have H : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) := by fun_prop
  simpa using H.continuousAt.continuousWithinAt.tendsto (x:=0) (s:=Ioi 0)

/-- No holomorphic function near any real point can agree with Dedekind
eta on the upper half-plane near that point. -/
theorem eta_no_analytic_extension (x : ℝ) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g (x:ℂ)) :
    ¬(g =ᶠ[𝓝[{z : ℂ | 0<z.im}] (x:ℂ)] ModularForm.eta) := by
  intro heq
  have he : ∀ᶠ z in 𝓝 (x:ℂ), 0<z.im → g z=ModularForm.eta z :=
    eventually_nhdsWithin_iff.mp heq
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.mp (hg.eventually_analyticAt.and he)
  have hgq (q : ℚ) (hq : dist (q:ℂ) x<r) : g (q:ℂ)=0 := by
    have h := tends_vertical (q:ℝ)
    simp only [Complex.ofReal_ratCast] at h
    apply tendsto_nhds_unique (((H hq).1.continuousAt.tendsto).comp h)
    apply (tendsto_eta_at_rational q).congr'
    filter_upwards [h.eventually (Metric.isOpen_ball.mem_nhds (show (q:ℂ)∈Metric.ball (x:ℂ) r from hq)),self_mem_nhdsWithin] with y hy hpos
    exact ((H hy).2 (by simpa [Complex.add_im] using hpos)).symm
  obtain ⟨u,_,hu,htu⟩ := Real.exists_seq_rat_strictMono_tendsto x
  have ht : Tendsto (fun n => (u n:ℂ)) atTop (𝓝 (x:ℂ)) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp htu
  have ht' : Tendsto (fun n => (u n:ℂ)) atTop (𝓝[≠] (x:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall fun n he => ?_⟩
    exact (hu n).ne (by exact_mod_cast congrArg Complex.re he)
  have Hzero := hg.frequently_zero_iff_eventually_zero.mp (ht'.frequently (p:=fun z => g z=0)
    ((ht.eventually (Metric.ball_mem_nhds (x:ℂ) hr)).mono fun n hn => hgq (u n) hn).frequently)
  obtain ⟨y,hy,hmatch,hzero⟩ := ((show ∀ᶠ y in 𝓝[>] (0:ℝ), 0<y from self_mem_nhdsWithin).and
    (((tends_vertical x).eventually he).and ((tends_vertical x).eventually Hzero))).exists
  have hy' : 0<((x:ℂ)+(y:ℂ)*I).im := by simpa using (show 0<y from hy)
  exact (eta_ne_zero_of_im_pos hy') ((hmatch hy').symm.trans hzero)

end AnalyticNumberTheory.ModularAndPartitions
