import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# A Hankel contour for Mellin transforms

The circular part uses a continuously lifted argument from zero to
`2π`. Cauchy's theorem in the logarithmic coordinate gives exactly the
jump in the Mellin integral across the positive real ray.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- One counterclockwise turn of the lifted Mellin integrand, with
logarithmic radius `X`. -/
noncomputable def hankelMellinArc (K : ℂ→ℂ) (s : ℂ) (X : ℝ) : ℂ :=
  I * ∫ θ : ℝ in 0..2*π,Complex.exp (s*((X:ℂ)+θ*I))*K (Complex.exp ((X:ℂ)+θ*I))

private noncomputable def hankelLogKernel (K : ℂ→ℂ) (s w : ℂ) : ℂ := Complex.exp (s*w)*K (Complex.exp w)

private theorem hankelLogKernel_upper (K : ℂ→ℂ) (s : ℂ) (t : ℝ) :
    hankelLogKernel K s ((t:ℂ)+((2*π:ℝ):ℂ)*I)=
    Complex.exp (s*(2*π*I))*hankelLogKernel K s t := by
  unfold hankelLogKernel; push_cast
  rw [mul_add,Complex.exp_add,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]; ring

private theorem hankelLogKernel_substitute {K : ℂ→ℂ} {s : ℂ} {x X : ℝ} (hx : x≤X)
    (hK : ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X → DifferentiableAt ℂ K u) :
    (∫ t : ℝ in x..X,hankelLogKernel K s t)=
      ∫ t : ℝ in Real.exp x..Real.exp X,K t*(t:ℂ)^(s-1) := by
  let g (t : ℝ) : ℂ := K t*(t:ℂ)^(s-1)
  have hc : ContinuousOn g (Real.exp '' uIcc x X) := by
    rintro _ ⟨v,hv,rfl⟩
    rw [uIcc_of_le hx] at hv
    have hp := Real.exp_pos v
    have hu : ‖((Real.exp v:ℝ):ℂ)‖=Real.exp v := by simp [abs_of_pos hp]
    exact (((hK _ (hu.symm ▸ hp) (hu.symm ▸ Real.exp_le_exp.mpr hv.2)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).mul
      (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp.ne'))).continuousWithinAt
  have H := intervalIntegral.integral_deriv_smul_comp' (g:=g) (fun v _ => Real.hasDerivAt_exp v)
    Real.continuous_exp.continuousOn hc
  refine Eq.trans (intervalIntegral.integral_congr (fun t _ => ?_)) H
  change _=(Real.exp t) • (K (Real.exp t)*(((Real.exp t:ℝ):ℂ)^(s-1)))
  rw [Complex.real_smul,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ←Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp,Complex.ofReal_exp]
  unfold hankelLogKernel
  rw [show (t:ℂ)*(s-1)=s*t-t by ring,Complex.exp_sub]; field_simp

/-- Exact deformation between two finite radii in a punctured disk. -/
theorem hankelMellinArc_sub {K : ℂ→ℂ} {s : ℂ} {x X : ℝ} (hx : x≤X)
    (hK : ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X → DifferentiableAt ℂ K u) :
    hankelMellinArc K s X-hankelMellinArc K s x =
      (Complex.exp (s*(2*π*I))-1)*
      ∫ t : ℝ in Real.exp x..Real.exp X,K t*(t:ℂ)^(s-1) := by
  let F := hankelLogKernel K s
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (x:ℂ)
    ((X:ℂ)+(2*π:ℝ)*I) (by
      intro w hw
      have hw' : w.re∈uIcc x X := by simpa using hw.1
      have hwr := (uIcc_of_le hx ▸ hw').2
      have hu : ‖Complex.exp w‖≤Real.exp X := by rwa [Complex.norm_exp,Real.exp_le_exp]
      exact (((Complex.differentiableAt_exp.comp w ((differentiableAt_const s).mul differentiableAt_id)).mul
        ((hK _ (norm_pos_iff.mpr (Complex.exp_ne_zero _)) hu).comp w Complex.differentiableAt_exp))).differentiableWithinAt)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.mul_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add,zero_smul,
    smul_eq_mul,Complex.ofReal_zero,F,hankelLogKernel_upper,intervalIntegral.integral_const_mul] at H
  rw [←hankelLogKernel_substitute hx hK]
  unfold hankelMellinArc
  change _-Complex.exp (s*(2*π*I))*(∫ t : ℝ in x..X,hankelLogKernel K s t)+
    I*(∫ y : ℝ in 0..2*π,hankelLogKernel K s ((X:ℂ)+y*I))-
    I*(∫ y : ℝ in 0..2*π,hankelLogKernel K s ((x:ℂ)+y*I))=0 at H
  dsimp only [hankelLogKernel] at *
  linear_combination H


/-- Shrinking the circular part to zero is valid to the right of a
double pole. The norm bound is uniform in the argument of the kernel. -/
theorem tendsto_hankelMellinArc_atBot {K : ℂ→ℂ} {s : ℂ} {X C : ℝ}
    (hs : 2<s.re) (hb : ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X → ‖u‖^2*‖K u‖≤C) :
    Tendsto (hankelMellinArc K s) atBot (𝓝 0) := by
  let A := Real.exp (2*π*|s.im|)
  have hlim : Tendsto (fun x : ℝ => Real.exp ((s.re-2)*x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos (sub_pos.mpr hs)).mpr tendsto_id)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (hlim.const_mul (C*A*(2*π))))
  filter_upwards [eventually_le_atBot X] with x hx
  have hθ (θ : ℝ) (hθ : θ∈uIoc 0 (2*π)) :
      ‖Complex.exp (s*((x:ℂ)+θ*I))*K (Complex.exp ((x:ℂ)+θ*I))‖≤
        C*A*Real.exp ((s.re-2)*x) := by
    rw [uIoc_of_le (by positivity)] at hθ
    let u := Complex.exp ((x:ℂ)+θ*I)
    have hu : ‖u‖=Real.exp x := by simp [u,Complex.norm_exp]
    have hb' := hb u (hu.symm ▸ Real.exp_pos _) (hu.symm ▸ Real.exp_le_exp.mpr hx)
    rw [hu] at hb'
    have hy : -(s.im*θ)≤2*π*|s.im| := by
      nlinarith only [mul_le_mul_of_nonneg_right (neg_le_abs s.im) hθ.1.le,
        mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg s.im)]
    have hM : ‖Complex.exp (s*((x:ℂ)+θ*I))‖≤Real.exp (s.re*x+2*π*|s.im|) := by
      simp only [Complex.norm_exp,Real.exp_le_exp,Complex.mul_re,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,mul_one,sub_zero,add_zero,zero_add]; linarith
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans
    have he : Real.exp (s.re*x+2*π*|s.im|)=(Real.exp x)^2*(A*Real.exp ((s.re-2)*x)) := by
      dsimp [A]; rw [pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]; congr 1; ring
    rw [he]
    change (Real.exp x)^2*(A*Real.exp ((s.re-2)*x))*‖K u‖≤_
    have hA : 0≤A := (Real.exp_pos _).le
    nlinarith only [mul_le_mul_of_nonneg_right hb' (mul_nonneg hA (Real.exp_pos ((s.re-2)*x)).le)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hθ
  rw [hankelMellinArc,norm_mul,Complex.norm_I,one_mul]
  simp only [sub_zero,abs_of_pos (by positivity : 0<2*π)] at h
  exact h.trans_eq (by ring)

/-- The Hankel circle is the discontinuity of the Mellin integral over
the part of the positive ray it surrounds. -/
theorem hankelMellinArc_eq {K : ℂ→ℂ} {s : ℂ} {X C : ℝ}
    (hs : 2<s.re)
    (hK : ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X → DifferentiableAt ℂ K u)
    (hb : ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X → ‖u‖^2*‖K u‖≤C)
    (hi : IntegrableOn (fun t : ℝ => K t*(t:ℂ)^(s-1)) (Ioc 0 (Real.exp X))) :
    hankelMellinArc K s X=(Complex.exp (s*(2*π*I))-1)*
      ∫ t : ℝ in 0..Real.exp X,K t*(t:ℂ)^(s-1) := by
  have hr := Real.exp_pos X
  have hc := intervalIntegral.continuousOn_primitive_interval_left
    (show IntegrableOn (fun t : ℝ => K t*(t:ℂ)^(s-1)) (uIcc 0 (Real.exp X)) from by
      rwa [uIcc_of_le hr.le,integrableOn_Icc_iff_integrableOn_Ioc])
  have he : Tendsto Real.exp atBot (𝓝[uIcc 0 (Real.exp X)] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot,?_⟩
    filter_upwards [eventually_le_atBot X] with x hx
    rw [uIcc_of_le hr.le]; exact ⟨(Real.exp_pos x).le,Real.exp_le_exp.mpr hx⟩
  have hl := (tendsto_const_nhds (x:=hankelMellinArc K s X)).sub (tendsto_hankelMellinArc_atBot hs hb)
  have hR := ((hc 0 left_mem_uIcc).tendsto.comp he).const_mul (Complex.exp (s*(2*π*I))-1)
  rw [sub_zero] at hl
  exact tendsto_nhds_unique (hl.congr' ((eventually_le_atBot X).mono fun _ hx => hankelMellinArc_sub hx hK)) hR


set_option backward.isDefEq.respectTransparency false in
/-- Holomorphic dependence on the weight of the circular part. -/
theorem differentiable_hankelMellinArc (K : ℂ→ℂ) (X : ℝ)
    (hK : ∀ u : ℂ, ‖u‖=Real.exp X → ContinuousAt K u) :
    Differentiable ℂ (fun s => hankelMellinArc K s X) := by
  let w (θ : ℝ) : ℂ := (X:ℂ)+θ*I
  let g (θ : ℝ) := K (Complex.exp (w θ))
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun θ =>
    (hK _ (by simp [w,Complex.norm_exp])).comp ((Complex.continuous_exp.comp hw).continuousAt)
  let F (s : ℂ) (θ : ℝ) := Complex.exp (s*w θ)*g θ
  let D (p : ℂ×ℝ) := Complex.exp (p.1*w p.2)*w p.2*g p.2
  have hF (s : ℂ) : Continuous (F s) := ((continuous_const.mul hw).cexp).mul hg
  have hD : Continuous D := (((continuous_fst.mul (hw.comp continuous_snd)).cexp).mul
    (hw.comp continuous_snd)).mul (hg.comp continuous_snd)
  intro s
  have hπ : (0:ℝ)≤2*π := by positivity
  let μ := volume.restrict (Ioc (0:ℝ) (2*π))
  obtain ⟨B,hB⟩ := ((isCompact_closedBall s 1).prod (isCompact_Icc (a:=(0:ℝ)) (b:=2*π))).exists_bound_of_continuousOn hD.continuousOn
  have HD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (F:=F)
    (F':=fun z θ => D (z,θ)) (bound:=fun _ => B) (Metric.ball_mem_nhds s zero_lt_one)
    (Eventually.of_forall fun z => (hF z).aestronglyMeasurable)
    ((hF s).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((ae_restrict_mem measurableSet_Ioc).mono fun θ hθ z hz =>
      hB (z,θ) ⟨Metric.ball_subset_closedBall hz,Ioc_subset_Icc_self hθ⟩)
    (integrable_const B) (Eventually.of_forall fun θ z _ => by
      simpa only [F,D,one_mul,id_eq] using (((hasDerivAt_id z).mul_const (w θ)).cexp.mul_const (g θ)))
  unfold hankelMellinArc
  simp_rw [intervalIntegral.integral_of_le hπ]
  exact HD.2.differentiableAt.const_mul I

end AnalyticNumberTheory.AnalyticTools
