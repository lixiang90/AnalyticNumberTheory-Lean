import AnalyticNumberTheory.AnalyticTools.BarnesDoubleZeta
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform

/-!
# Analytic estimates for the Barnes kernel

The geometric denominators have simple zeros at the origin. Removing
both of them gives uniform bounds in a punctured complex disk.
-/

open Complex Real Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- Holomorphic extension of the geometric Mellin kernel off its poles. -/
noncomputable def barnesComplexKernel (a b u : ℂ) : ℂ :=
  Complex.exp (-a*u)/((1-Complex.exp (-b*u))*(1-Complex.exp (-u)))

private noncomputable def barnesSlope (b : ℂ) := dslope (fun u : ℂ => 1-Complex.exp (-b*u)) 0

private theorem barnesSlope_zero (b : ℂ) : barnesSlope b 0=b := by
  rw [barnesSlope,dslope_same]
  have h := ((hasDerivAt_id (0:ℂ)).const_mul (-b)).cexp
  change deriv ((fun _ : ℂ => (1:ℂ))-(fun x : ℂ => Complex.exp (-b*id x))) 0=b
  rw [((hasDerivAt_const 0 (1:ℂ)).sub h).deriv]
  simp

private theorem barnesSlope_continuous (b : ℂ) : Continuous (barnesSlope b) := by
  apply continuous_iff_continuousAt.mpr; intro u
  have h : AnalyticAt ℂ (fun v : ℂ => 1-Complex.exp (-b*v)) u := by fun_prop
  exact (h.dslope 0).continuousAt

private theorem mul_barnesSlope (b u : ℂ) : u*barnesSlope b u=1-Complex.exp (-b*u) := by
  simpa [barnesSlope,smul_eq_mul] using sub_smul_dslope (fun v : ℂ => 1-Complex.exp (-b*v)) 0 u

/-- A disk centered at zero in which the origin is the only pole and
the kernel times the square of the radius is bounded. -/
theorem exists_barnesKernel_disk (a : ℂ) {b : ℂ} (hb : b≠0) : ∃ r C : ℝ, 0<r ∧
    ∀ u : ℂ, 0<‖u‖ → ‖u‖≤r → DifferentiableAt ℂ (barnesComplexKernel a b) u ∧
      ‖u‖^2*‖barnesComplexKernel a b u‖≤C := by
  let q (u : ℂ) := barnesSlope b u*barnesSlope 1 u
  let f (u : ℂ) := Complex.exp (-a*u)/q u
  have hq : Continuous q := (barnesSlope_continuous b).mul (barnesSlope_continuous 1)
  have h₀ : q 0≠0 := by simpa [q,barnesSlope_zero] using hb
  have hf : ContinuousAt f 0 := by exact (Complex.continuous_exp.comp
    (continuous_const.mul continuous_id)).continuousAt.div hq.continuousAt h₀
  have ev : ∀ᶠ u in 𝓝 (0:ℂ), q u≠0 ∧ ‖f u‖<‖f 0‖+1 :=
    (hq.continuousAt.eventually_ne h₀).and (hf.norm.eventually_lt_const (by linarith))
  obtain ⟨δ,hδ,hδ'⟩ := Metric.mem_nhds_iff.mp ev
  refine ⟨δ/2,‖f 0‖+1,by positivity,?_⟩
  intro u hu huδ
  have ⟨hqu,hfu⟩ := hδ' (show u∈Metric.ball 0 δ by simpa using (by linarith : ‖u‖<δ))
  have he : (1-Complex.exp (-b*u))*(1-Complex.exp (-u))=u^2*q u := by
    rw [←mul_barnesSlope b u,show 1-Complex.exp (-u)=u*barnesSlope 1 u by simpa using (mul_barnesSlope 1 u).symm]
    dsimp only [q]; ring
  have hn : u≠0 := norm_pos_iff.mp hu
  have hd : (1-Complex.exp (-b*u))*(1-Complex.exp (-u))≠0 := he ▸ mul_ne_zero (pow_ne_zero _ hn) hqu
  refine ⟨?_,?_⟩
  · unfold barnesComplexKernel; fun_prop (disch := exact hd)
  · have hid : u^2*barnesComplexKernel a b u=f u := by
      dsimp only [barnesComplexKernel,f]; rw [he]; field_simp
    simpa only [←norm_pow,←norm_mul,hid] using (show ‖f u‖≤‖f 0‖+1 from hfu.le)

/-- On the whole positive ray the Barnes kernel has no poles. -/
theorem continuousOn_barnesKernel (a : ℂ) {b : ℂ} (hb : 0<b.re) :
    ContinuousOn (barnesKernel a b) (Ioi 0) := by
  intro t ht
  change 0<t at ht
  have h₁ : ‖Complex.exp (-b*t)‖<1 := by
    rw [Complex.norm_exp,←Real.exp_zero,Real.exp_lt_exp]; simp [Complex.mul_re]; positivity
  have h₂ : ‖Complex.exp (-(t:ℂ))‖<1 := by simpa [Complex.norm_exp] using ht
  have h₃ : 1-Complex.exp (-b*t)≠0 := sub_ne_zero.mpr (fun he => by rw [←he,norm_one] at h₁; exact lt_irrefl _ h₁)
  have h₄ : 1-Complex.exp (-(t:ℂ))≠0 := sub_ne_zero.mpr (fun he => by rw [←he,norm_one] at h₂; exact lt_irrefl _ h₂)
  have hD := mul_ne_zero h₃ h₄
  unfold barnesKernel; fun_prop (disch := exact hD)


/-- Exponential decay of the Barnes kernel at infinity. -/
theorem barnesKernel_isBigO_atTop {a b : ℂ} (hb : 0<b.re) :
    barnesKernel a b =O[atTop] fun t : ℝ => Real.exp (-a.re*t) := by
  let A := 1-Real.exp (-b.re)
  let B := 1-Real.exp (-1)
  have hA : 0<A := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb))
  have hB : 0<B := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  refine isBigO_iff.mpr ⟨(A*B)⁻¹,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  have h₁ : ‖Complex.exp (-b*t)‖≤Real.exp (-b.re) := by
    rw [Complex.norm_exp,Real.exp_le_exp]; simp [Complex.mul_re]; nlinarith
  have h₂ : ‖Complex.exp (-(t:ℂ))‖≤Real.exp (-1) := by simpa [Complex.norm_exp] using ht
  have h₃ := norm_sub_norm_le (1:ℂ) (Complex.exp (-b*t))
  have h₄ := norm_sub_norm_le (1:ℂ) (Complex.exp (-(t:ℂ)))
  rw [norm_one] at h₃ h₄
  have h₅ : A≤‖1-Complex.exp (-b*t)‖ := (sub_le_sub_left h₁ 1).trans h₃
  have h₆ : B≤‖1-Complex.exp (-(t:ℂ))‖ := (sub_le_sub_left h₂ 1).trans h₄
  simp only [barnesKernel,norm_div,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.neg_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [div_eq_mul_inv,mul_comm (A*B)⁻¹]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (mul_pos hA hB)
    (mul_le_mul h₅ h₆ hB.le (norm_nonneg _))) (Real.exp_pos _).le

/-- Double-pole bound at the endpoint of the real Mellin integral. -/
theorem barnesKernel_isBigO_atZero (a : ℂ) {b : ℂ} (hb : b≠0) :
    barnesKernel a b =O[𝓝[>] 0] fun t : ℝ => t^(-(2:ℝ)) := by
  obtain ⟨r,C,hr,H⟩ := exists_barnesKernel_disk a hb
  refine isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hr)] with t (ht : 0<t) (htr : t<r)
  have hn : ‖(t:ℂ)‖=t := by simp [abs_of_pos ht]
  have h := (H t (hn.symm ▸ ht) (hn.symm ▸ htr.le)).2
  rw [hn] at h
  rw [Real.rpow_neg ht.le,Real.rpow_two,Real.norm_of_nonneg (by positivity),←div_eq_mul_inv,
    le_div_iff₀ (sq_pos_of_pos ht)]
  simpa only [barnesComplexKernel,barnesKernel,mul_comm] using h

/-- Absolute convergence of the positive-axis Mellin integral. -/
theorem integrableOn_barnesMellin {a b s : ℂ} (ha : 0<a.re) (hb : 0<b.re) (hs : 2<s.re) :
    IntegrableOn (fun t : ℝ => barnesKernel a b t*(t:ℂ)^(s-1)) (Ioi 0) := by
  have h := mellinConvergent_of_isBigO_rpow_exp ha
    ((continuousOn_barnesKernel a hb).locallyIntegrableOn measurableSet_Ioi)
    (barnesKernel_isBigO_atTop hb) (barnesKernel_isBigO_atZero a (fun h => by subst b; simp at hb)) hs
  simpa only [MellinConvergent,smul_eq_mul,mul_comm] using h

end AnalyticNumberTheory.AnalyticTools
