import AnalyticNumberTheory.ModularAndPartitions.EisensteinPeriods
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic continuation of Eisenstein cone sums

The arithmetic cone has a simple pole at weight two. Its residue is
`c/(cz+d)`; multiplying by the winding factor gives precisely the
quasimodular correction to the Eisenstein series.
-/

open Complex Real Set Filter
open UpperHalfPlane hiding I
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

/-- The multiplier relating the two logarithm branches. -/
noncomputable def eisensteinWinding (s : ℂ) : ℂ :=
  Complex.exp (-π*I*s)-Complex.exp (π*I*s)

private theorem differentiable_eisensteinWinding : Differentiable ℂ eisensteinWinding := by
  unfold eisensteinWinding; fun_prop

/-- A meromorphic continuation of the cone sum, away from the zeros of
the winding factor. The values at poles follow the field convention for division. -/
noncomputable def eisensteinConeContinuation (γ : SL(2,ℤ)) (z : ℍ) (s : ℂ) : ℂ :=
  eisensteinPeriod γ z s/eisensteinWinding s

theorem meromorphicAt_eisensteinConeContinuation (γ : SL(2,ℤ)) (z : ℍ) (s : ℂ) :
    MeromorphicAt (eisensteinConeContinuation γ z) s :=
  ((differentiable_eisensteinPeriod γ z).analyticAt _).meromorphicAt.fun_div
    (differentiable_eisensteinWinding.analyticAt s).meromorphicAt

theorem eisensteinConeContinuation_eq_sum (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {s : ℂ} (hs : 2<s.re) (hw : eisensteinWinding s≠0) :
    eisensteinConeContinuation γ z s=eisensteinConeSum (γ 1 0) (γ 1 1) z s := by
  rw [eisensteinConeContinuation,eisensteinPeriod_eq_cone γ z hc hs]
  change eisensteinWinding s*_/eisensteinWinding s=_
  field_simp

/-- The continuation realizes the modular transformation at every
nonintegral complex weight. -/
theorem eisensteinG_modular_of_winding_ne_zero (γ : SL(2,ℤ)) (z : ℍ) {s : ℂ}
    (hw : eisensteinWinding s≠0) :
    (denom γ z)^(-s)*eisensteinG ((γ • z : ℍ):ℂ) s=
      eisensteinG z s+eisensteinWinding s*eisensteinConeContinuation γ z s := by
  rw [eisensteinConeContinuation,mul_div_cancel₀ _ hw,eisensteinPeriod]; ring

private theorem winding_deriv (s : ℂ) :
    HasDerivAt eisensteinWinding ((-π*I)*Complex.exp (-π*I*s)-(π*I)*Complex.exp (π*I*s)) s := by
  have h := (((hasDerivAt_id s).const_mul (-(π:ℂ)*I)).cexp.fun_sub (((hasDerivAt_id s).const_mul ((π:ℂ)*I)).cexp))
  apply h.congr_deriv; simp only [mul_one,id_eq]; ring

private theorem residue_coneContinuation (γ : SL(2,ℤ)) (z : ℍ) {a d : ℂ}
    (ha : eisensteinWinding a=0) (hd : d≠0) (hD : HasDerivAt eisensteinWinding d a) :
    Tendsto (fun s => (s-a)*eisensteinConeContinuation γ z s) (𝓝[≠] a)
      (𝓝 (eisensteinPeriod γ z a/d)) := by
  have H := ((differentiable_eisensteinPeriod γ z a).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).div hD.tendsto_slope hd
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change eisensteinPeriod γ z s/slope eisensteinWinding a s=_
  rw [slope_def_field,ha,sub_zero,eisensteinConeContinuation,div_div_eq_mul_div]
  ring

private theorem piI_ne : (π:ℂ)*I≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero

private theorem exp_two_weights :
    Complex.exp (-π*I*2)=1 ∧ Complex.exp (π*I*2)=1 := by
  rw [show -((π:ℂ))*I*2= -(2*π*I) by ring,Complex.exp_neg,
    show (π:ℂ)*I*2=2*π*I by ring,Complex.exp_two_pi_mul_I]; simp

/-- The pole of the continued cone sum at weight two, in residue-limit form. -/
theorem eisensteinConeContinuation_residue_two (γ : SL(2,ℤ)) (z : ℍ) :
    Tendsto (fun s => (s-2)*eisensteinConeContinuation γ z s) (𝓝[≠] 2)
      (𝓝 ((γ 1 0:ℂ)/denom γ z)) := by
  have hD := winding_deriv 2
  rw [exp_two_weights.1,exp_two_weights.2,mul_one,mul_one] at hD
  have hd : -(π:ℂ)*I-π*I≠0 := by rw [show -(π:ℂ)*I-π*I= -2*(π*I) by ring]; exact mul_ne_zero (by norm_num) piI_ne
  have H := residue_coneContinuation γ z (a:=2) (by rw [eisensteinWinding,exp_two_weights.1,exp_two_weights.2,sub_self]) hd hD
  convert H using 2
  rw [eisensteinPeriod,eisensteinG_two_modular,Complex.cpow_neg,Complex.cpow_ofNat]
  have hden := denom_ne_zero (γ : GL (Fin 2) ℝ) z
  field_simp [hden,hd]
  ring

/-- The residue of the cone sum at weight one. -/
theorem eisensteinConeContinuation_residue_one (γ : SL(2,ℤ)) (z : ℍ) :
    Tendsto (fun s => (s-1)*eisensteinConeContinuation γ z s) (𝓝[≠] 1)
      (𝓝 ((1-(denom γ z)⁻¹)/2)) := by
  have he : Complex.exp (-π*I*1)= -1 := by
    rw [mul_one,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]; norm_num
  have hD := winding_deriv 1
  rw [he,mul_one,Complex.exp_pi_mul_I] at hD
  have hcoef : (-(π:ℂ)*I)*(-1)-(π*I)*(-1)=2*(π*I) := by ring
  rw [hcoef] at hD
  have hd : (2:ℂ)*(π*I)≠0 := mul_ne_zero (by norm_num) piI_ne
  have H := residue_coneContinuation γ z (a:=1) (by rw [eisensteinWinding,he,mul_one,Complex.exp_pi_mul_I,sub_self]) hd hD
  convert H using 2
  rw [eisensteinPeriod,eisensteinG_one,eisensteinG_one,Complex.cpow_neg_one]
  field_simp [hd,piI_ne]
  ring

end AnalyticNumberTheory.ModularAndPartitions
