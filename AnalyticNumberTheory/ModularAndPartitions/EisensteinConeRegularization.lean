import AnalyticNumberTheory.ModularAndPartitions.EisensteinZeroWeight
import AnalyticNumberTheory.ModularAndPartitions.EisensteinConeHolomorphy
import Mathlib.Analysis.Calculus.DSlope

/-!
# Regular values of the continued Eisenstein cone series

The winding factor has a simple zero at each integer. At each common
zero of the period and the winding factor their derivative quotient
gives the analytic value of the cone series.
-/

open Complex Real Set Filter
open UpperHalfPlane hiding I
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

/-- The zeros of the winding factor are precisely the integer weights. -/
theorem eisensteinWinding_eq_zero_iff (s : ℂ) :
    eisensteinWinding s=0 ↔ ∃ n : ℤ, s=(n:ℂ) := by
  rw [eisensteinWinding,sub_eq_zero,Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨-n,?_⟩
    push_cast
    apply mul_left_cancel₀ (show 2*(π:ℂ)*I≠0 from
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    linear_combination -hn
  · rintro ⟨n,rfl⟩
    refine ⟨-n,?_⟩
    push_cast; ring

private theorem winding_analytic (a : ℂ) : AnalyticAt ℂ eisensteinWinding a := by
  exact (show Differentiable ℂ eisensteinWinding by unfold eisensteinWinding; fun_prop).analyticAt a

private theorem winding_simple {a : ℂ} (ha : eisensteinWinding a=0) :
    deriv eisensteinWinding a≠0 := by
  change Complex.exp (-π*I*a)-Complex.exp (π*I*a)=0 at ha
  have H := (((hasDerivAt_id a).const_mul (-(π:ℂ)*I)).cexp.fun_sub
    (((hasDerivAt_id a).const_mul ((π:ℂ)*I)).cexp))
  change deriv (fun s : ℂ => Complex.exp (-π*I*s)-Complex.exp (π*I*s)) a≠0
  simp only [id_eq,mul_one] at H
  rw [H.deriv,sub_eq_zero.mp ha]
  rw [show Complex.exp (π*I*a)*(-(π:ℂ)*I)-Complex.exp (π*I*a)*(π*I)=
    (-2*(π:ℂ)*I)*Complex.exp (π*I*a) by ring]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (Complex.exp_ne_zero _)

private theorem winding_ne_of_dslope {a s : ℂ} (ha : eisensteinWinding a=0) (hs : s≠a)
    (hd : dslope eisensteinWinding a s≠0) : eisensteinWinding s≠0 := by
  have H := sub_smul_dslope eisensteinWinding a s
  simpa [smul_eq_mul,ha] using (H ▸ mul_ne_zero (sub_ne_zero.mpr hs) hd :
    eisensteinWinding s-eisensteinWinding a≠0)

/-- The winding factor is nonzero on a punctured neighborhood of every weight. -/
theorem eventually_eisensteinWinding_ne_zero (a : ℂ) :
    ∀ᶠ s in 𝓝[≠] a,eisensteinWinding s≠0 := by
  by_cases ha : eisensteinWinding a=0
  · have hd : dslope eisensteinWinding a a≠0 := by rw [dslope_same]; exact winding_simple ha
    have he := ((winding_analytic a).dslope a).continuousAt.eventually_ne hd
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hsa
    exact winding_ne_of_dslope ha hsa hs
  · exact ((winding_analytic a).continuousAt.eventually_ne ha).filter_mono nhdsWithin_le_nhds

private theorem period_zero_of_winding_zero (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {a : ℂ} (hw : eisensteinWinding a=0) (h₁ : a≠1) (h₂ : a≠2) :
    eisensteinPeriod γ z a=0 := by
  obtain ⟨m,rfl⟩ := (eisensteinWinding_eq_zero_iff a).mp hw
  cases m with
  | ofNat n =>
    change (n:ℂ)≠1 at h₁
    change (n:ℂ)≠2 at h₂
    change eisensteinPeriod γ z (n:ℂ)=0
    by_cases hn : n=0
    · subst n; simp [eisensteinPeriod,eisensteinG_zero]
    have h₃ : 3≤n := by
      have hn₁ : n≠1 := by exact_mod_cast h₁
      have hn₂ : n≠2 := by exact_mod_cast h₂
      omega
    rw [eisensteinPeriod,eisensteinG_nat_modular h₃,Complex.cpow_neg,Complex.cpow_natCast]
    field_simp [denom_ne_zero (γ : GL (Fin 2) ℝ) z]; ring
  | negSucc n =>
    obtain ⟨X,H⟩ := eisensteinPeriod_eq_tiltedHankel γ z hc
    rw [H]
    simp only [Int.cast_negSucc,Complex.Gamma_neg_nat_eq_zero,inv_zero,mul_zero,zero_mul]

/-- The continued cone sum with its removable singularities filled in. -/
noncomputable def eisensteinConeRegularized (γ : SL(2,ℤ)) (z : ℍ) (s : ℂ) : ℂ :=
  if eisensteinWinding s=0 ∧ eisensteinPeriod γ z s=0
  then deriv (eisensteinPeriod γ z) s / deriv eisensteinWinding s
  else eisensteinConeContinuation γ z s

/-- Filling removable values leaves the punctured germ of the cone series unchanged. -/
theorem eisensteinConeRegularized_eventuallyEq (γ : SL(2,ℤ)) (z : ℍ) (a : ℂ) :
    eisensteinConeRegularized γ z =ᶠ[𝓝[≠] a] eisensteinConeContinuation γ z := by
  filter_upwards [eventually_eisensteinWinding_ne_zero a] with s hs
  simp [eisensteinConeRegularized,hs]

/-- The continued cone sum is analytic at every weight except for its two poles. -/
theorem analyticAt_eisensteinConeRegularized (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {a : ℂ} (h₁ : a≠1) (h₂ : a≠2) : AnalyticAt ℂ (eisensteinConeRegularized γ z) a := by
  have hP := (differentiable_eisensteinPeriod γ z).analyticAt a
  have hW := winding_analytic a
  by_cases hw : eisensteinWinding a=0
  · have hp := period_zero_of_winding_zero γ z hc hw h₁ h₂
    have hd : dslope eisensteinWinding a a≠0 := by rw [dslope_same]; exact winding_simple hw
    apply ((hP.dslope a).div (hW.dslope a) hd).congr
    filter_upwards [(hW.dslope a).continuousAt.eventually_ne hd] with s hs
    by_cases ha : s=a
    · subst s; simp [eisensteinConeRegularized,hw,hp,dslope_same]
    · have hn := winding_ne_of_dslope hw ha hs
      simp only [Pi.div_apply,dslope_of_ne _ ha,slope_def_field,hp,hw,sub_zero,
        eisensteinConeRegularized,hn,false_and,ite_false,eisensteinConeContinuation]
      field_simp [sub_ne_zero.mpr ha]
  · apply (hP.div hW hw).congr
    filter_upwards [hW.continuousAt.eventually_ne hw] with s hs
    simp [eisensteinConeRegularized,eisensteinConeContinuation,hs]

/-- In the entire half-plane of absolute convergence, including all integer
weights at least three, regularization recovers the original series. -/
theorem eisensteinConeRegularized_eq_sum (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {s : ℂ} (hs : 2<s.re) :
    eisensteinConeRegularized γ z s=eisensteinConeSum (γ 1 0) (γ 1 1) z s := by
  have h₁ : s≠1 := by rintro rfl; norm_num at hs
  have h₂ : s≠2 := by rintro rfl; norm_num at hs
  have hA := (analyticAt_eisensteinConeRegularized γ z hc h₁ h₂).continuousAt.tendsto
  have hU : {t : ℂ | 2<t.re}∈𝓝 s := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hB := ((differentiableOn_eisensteinConeSum (γ 1 0) (γ 1 1) z).differentiableAt hU).continuousAt.tendsto
  apply tendsto_nhds_unique (l:=𝓝[≠] s) (hA.mono_left nhdsWithin_le_nhds)
  apply (hB.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [(nhdsWithin_le_nhds hU : {t : ℂ | 2<t.re}∈𝓝[≠] s),eventually_eisensteinWinding_ne_zero s] with t ht hw
  simp [eisensteinConeRegularized,hw,eisensteinConeContinuation_eq_sum γ z hc ht hw]

/-- The regularized value at weight zero in terms of the classical Dedekind sum. -/
theorem eisensteinConeRegularized_zero (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    eisensteinConeRegularized γ z 0=(denom γ z+(denom γ z)⁻¹)/(12*(γ 1 0:ℂ))-
      (dedekindSum (γ 1 1) (γ 1 0).natAbs:ℂ)-1/4 := by
  apply tendsto_nhds_unique (l:=𝓝[≠] (0:ℂ)) ((analyticAt_eisensteinConeRegularized γ z hc (a:=0) (by norm_num) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  exact (eisensteinConeContinuation_limit_zero_dedekind γ z hc).congr' (eisensteinConeRegularized_eventuallyEq γ z 0).symm

/-- The normalized cone series is meromorphic on the entire weight plane. -/
theorem meromorphicAt_eisensteinConeRegularized (γ : SL(2,ℤ)) (z : ℍ) (a : ℂ) :
    MeromorphicAt (eisensteinConeRegularized γ z) a :=
  (meromorphicAt_eisensteinConeContinuation γ z a).congr (eisensteinConeRegularized_eventuallyEq γ z a).symm

/-- The residue of the regularized cone series at weight one. -/
theorem eisensteinConeRegularized_residue_one (γ : SL(2,ℤ)) (z : ℍ) :
    Tendsto (fun s => (s-1)*eisensteinConeRegularized γ z s) (𝓝[≠] 1)
      (𝓝 ((1-(denom γ z)⁻¹)/2)) := by
  apply (eisensteinConeContinuation_residue_one γ z).congr'
  filter_upwards [eisensteinConeRegularized_eventuallyEq γ z 1] with s hs
  rw [hs]

/-- The residue of the regularized cone series at weight two. -/
theorem eisensteinConeRegularized_residue_two (γ : SL(2,ℤ)) (z : ℍ) :
    Tendsto (fun s => (s-2)*eisensteinConeRegularized γ z s) (𝓝[≠] 2)
      (𝓝 ((γ 1 0:ℂ)/denom γ z)) := by
  apply (eisensteinConeContinuation_residue_two γ z).congr'
  filter_upwards [eisensteinConeRegularized_eventuallyEq γ z 2] with s hs
  rw [hs]

end AnalyticNumberTheory.ModularAndPartitions
