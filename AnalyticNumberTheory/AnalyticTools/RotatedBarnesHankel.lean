import AnalyticNumberTheory.AnalyticTools.BarnesHankel
import AnalyticNumberTheory.AnalyticTools.RotatedBarnes

/-!
# Hankel contours in arbitrary convergent directions

Rotating a small circular contour and its two infinite sides permits
Barnes periods with arbitrary angle strictly less than `π`.
-/

open Complex Real Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- The geometric kernel pulled back under the ray parametrization. -/
noncomputable def tiltedBarnesKernel (a b ω u : ℂ) := barnesComplexKernel a b (ω*u)

/-- Admissible radius of the circle before rotation and scaling. -/
def TiltedBarnesRadius (a b ω : ℂ) (X : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X → DifferentiableAt ℂ (tiltedBarnesKernel a b ω) u ∧
    ‖u‖^2*‖tiltedBarnesKernel a b ω u‖≤C

theorem exists_tiltedBarnesRadius (a : ℂ) {b ω : ℂ} (hb : b≠0) (hω : ω≠0) :
    ∃ X, TiltedBarnesRadius a b ω X := by
  obtain ⟨r,C,hr,H⟩ := exists_barnesKernel_disk a hb
  have hw := norm_pos_iff.mpr hω
  refine ⟨Real.log (r/‖ω‖),C/‖ω‖^2,?_⟩
  intro u hu hur
  rw [Real.exp_log (div_pos hr hw),le_div_iff₀ hw] at hur
  have h := H (ω*u) (by rw [norm_mul]; positivity) (by rwa [norm_mul,mul_comm])
  refine ⟨h.1.comp _ ((differentiableAt_const _).mul differentiableAt_id),?_⟩
  rw [le_div_iff₀ (sq_pos_of_pos hw)]
  rw [norm_mul,mul_pow] at h
  dsimp [tiltedBarnesKernel]; nlinarith only [h.2]

theorem TiltedBarnesRadius.mono {a b ω : ℂ} {x X : ℝ} (h : TiltedBarnesRadius a b ω X) (hx : x≤X) :
    TiltedBarnesRadius a b ω x := by
  obtain ⟨C,hC⟩ := h; exact ⟨C,fun u hu hur => hC u hu (hur.trans (Real.exp_le_exp.mpr hx))⟩

private theorem tilted_norm (w : ℂ) (t : ℝ) :
    ‖Complex.exp (-w*(t:ℂ))‖=Real.exp (-w.re*t) := by simp [Complex.norm_exp,Complex.mul_re]

private theorem tiltedKernel_eq (a b ω : ℂ) (t : ℝ) :
    tiltedBarnesKernel a b ω t=Complex.exp (-(a*ω)*t)/((1-Complex.exp (-(b*ω)*t))*(1-Complex.exp (-ω*t))) := by
  dsimp [tiltedBarnesKernel,barnesComplexKernel]; ring_nf

private theorem tilted_cont (a : ℂ) {b ω : ℂ} (hb : 0<(b*ω).re) (hω : 0<ω.re) :
    ContinuousOn (fun t : ℝ => tiltedBarnesKernel a b ω t) (Ioi 0) := by
  intro t ht; change 0<t at ht
  have hne (v : ℂ) (hv : 0<v.re) : 1-Complex.exp (-v*t)≠0 := by
    apply sub_ne_zero.mpr; intro he
    have hn := tilted_norm v t
    rw [←he,norm_one] at hn
    linarith [Real.exp_lt_one_iff.mpr (show -v.re*t<0 by nlinarith only [mul_pos hv ht])]
  simp_rw [tiltedKernel_eq]
  fun_prop (disch := exact mul_ne_zero (hne _ hb) (hne _ hω))

private theorem tilted_decay {a b ω : ℂ} (hb : 0<(b*ω).re) (hω : 0<ω.re) :
    (fun t : ℝ => tiltedBarnesKernel a b ω t) =O[atTop] fun t : ℝ => Real.exp (-(a*ω).re*t) := by
  let A := 1-Real.exp (-(b*ω).re)
  let B := 1-Real.exp (-ω.re)
  have hA : 0<A := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb))
  have hB : 0<B := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hω))
  refine isBigO_iff.mpr ⟨(A*B)⁻¹,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  have hbound (v : ℂ) (hv : 0<v.re) : 1-Real.exp (-v.re)≤‖1-Complex.exp (-v*t)‖ := by
    have H := norm_sub_norm_le (1:ℂ) (Complex.exp (-v*t))
    rw [norm_one,tilted_norm] at H
    exact (sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith)) _).trans H
  rw [tiltedKernel_eq,norm_div,norm_mul,tilted_norm,Real.norm_of_nonneg (Real.exp_pos _).le,
    div_eq_mul_inv,mul_comm (A*B)⁻¹]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (mul_pos hA hB)
    (mul_le_mul (hbound _ hb) (hbound _ hω) hB.le (norm_nonneg _))) (Real.exp_pos _).le

private theorem tilted_integrable {a b ω s : ℂ} {X : ℝ} (ha : 0<(a*ω).re) (hb : 0<(b*ω).re)
    (hω : 0<ω.re) (hX : TiltedBarnesRadius a b ω X) (hs : 2<s.re) :
    IntegrableOn (fun t : ℝ => tiltedBarnesKernel a b ω t*(t:ℂ)^(s-1)) (Ioi 0) := by
  obtain ⟨C,H⟩ := hX
  have hzero : (fun t : ℝ => tiltedBarnesKernel a b ω t) =O[𝓝[>] 0] fun t : ℝ => t^(-(2:ℝ)) := by
    refine isBigO_iff.mpr ⟨C,?_⟩
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (Real.exp_pos X))] with t (ht : 0<t) (htr : t<Real.exp X)
    have hn : ‖(t:ℂ)‖=t := by simp [abs_of_pos ht]
    have h := (H t (hn.symm ▸ ht) (hn.symm ▸ htr.le)).2
    rw [hn] at h
    rw [Real.rpow_neg ht.le,Real.rpow_two,Real.norm_of_nonneg (by positivity),←div_eq_mul_inv,
      le_div_iff₀ (sq_pos_of_pos ht)]
    simpa only [mul_comm] using h
  have h := mellinConvergent_of_isBigO_rpow_exp ha ((tilted_cont a hb hω).locallyIntegrableOn measurableSet_Ioi)
    (tilted_decay hb hω) hzero hs
  simpa only [MellinConvergent,smul_eq_mul,mul_comm] using h

/-- The circular Hankel contour on the tilted ray. -/
noncomputable def tiltedBarnesHankel (a b ω : ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  hankelMellinArc (tiltedBarnesKernel a b ω) s X+
    (Complex.exp (s*(2*π*I))-1)*∫ t : ℝ in Ioi (Real.exp X),tiltedBarnesKernel a b ω t*(t:ℂ)^(s-1)

theorem differentiable_tiltedBarnesHankel {a b ω : ℂ} {X : ℝ} (ha : 0<(a*ω).re) (hb : 0<(b*ω).re)
    (hω : 0<ω.re) (hX : TiltedBarnesRadius a b ω X) : Differentiable ℂ (tiltedBarnesHankel a b ω X) := by
  obtain ⟨C,H⟩ := hX
  apply Differentiable.add
  · exact differentiable_hankelMellinArc _ _ fun u hu => (H u (hu.symm ▸ Real.exp_pos X) hu.le).1.continuousAt
  · apply Differentiable.mul
    · fun_prop
    · exact differentiable_mellinTail ha (Real.exp_pos _) ((tilted_cont a hb hω).mono
        (Ici_subset_Ioi.mpr (Real.exp_pos X))) (tilted_decay hb hω)

theorem tiltedBarnesHankel_eq {a b ω s : ℂ} {X : ℝ} (ha : 0<(a*ω).re) (hb : 0<(b*ω).re)
    (hω : ω.re=1) (hX : TiltedBarnesRadius a b ω X) (hs : 2<s.re) :
    tiltedBarnesHankel a b ω X s=(Complex.exp (s*(2*π*I))-1)*(Complex.Gamma s*
      ∑' p : ℕ×ℕ,(barnesVector a b p*ω)^(-s)) := by
  have hi := tilted_integrable ha hb (by rw [hω]; norm_num) hX hs
  obtain ⟨C,H⟩ := hX
  have h₁ := hi.mono_set (show Ioc 0 (Real.exp X)⊆Ioi 0 from fun _ ht => ht.1)
  have h₂ := hi.mono_set (Ioi_subset_Ioi (Real.exp_pos X).le)
  have h := hankelMellinArc_eq hs (fun u hu hr => (H u hu hr).1) (fun u hu hr => (H u hu hr).2) h₁
  have hm : (∫ t : ℝ in Ioi 0,tiltedBarnesKernel a b ω t*(t:ℂ)^(s-1))=_ := integral_rotatedBarnesKernel ha hb hω hs
  rw [tiltedBarnesHankel,h,intervalIntegral.integral_of_le (Real.exp_pos X).le,←hm,
    ←Ioc_union_Ioi_eq_Ioi (Real.exp_pos X).le,setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h₁ h₂,mul_add]

end AnalyticNumberTheory.AnalyticTools
