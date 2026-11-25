import AnalyticNumberTheory.ModularAndPartitions.EisensteinConeRegularization
import Mathlib.Analysis.Meromorphic.Order

/-!
# Exact pole orders of the continued Eisenstein cone

For a positive lower-left matrix entry both residues are nonzero, so
weights one and two are simple poles, and these are the entire polar set.
-/

open Complex Real Set Filter
open UpperHalfPlane hiding I
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

private theorem order_neg_one_of_residue {f : ℂ → ℂ} {a r : ℂ} (hf : MeromorphicAt f a)
    (hr : r≠0) (hres : Tendsto (fun s => (s-a)*f s) (𝓝[≠] a) (𝓝 r)) :
    meromorphicOrderAt f a= -1 := by
  have hlin : MeromorphicAt (fun s : ℂ => s-a) a := by fun_prop
  have h := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hlin.mul hf)).mp ⟨r,hr,hres⟩
  rw [meromorphicOrderAt_mul hlin hf,meromorphicOrderAt_id_sub_const] at h
  cases he : meromorphicOrderAt f a with
  | top => simp [he] at h
  | coe j =>
    rw [he] at h
    have h' : (1:ℤ)+j=0 := by exact_mod_cast h
    have hj : j= -1 := by omega
    rw [hj]; rfl

/-- Weight one is a genuine simple pole when the lower-left entry is positive. -/
theorem meromorphicOrderAt_eisensteinConeRegularized_one (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    meromorphicOrderAt (eisensteinConeRegularized γ z) 1= -1 := by
  apply order_neg_one_of_residue (meromorphicAt_eisensteinConeRegularized γ z 1) _ (eisensteinConeRegularized_residue_one γ z)
  apply div_ne_zero _ (by norm_num)
  refine sub_ne_zero.mpr fun h => ?_
  have hden : denom γ z=1 := by simpa using congrArg Inv.inv h.symm
  have him := congrArg Complex.im hden
  change (((γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ))).im=(1:ℂ).im at him
  simp only [Complex.add_im,Complex.mul_im,Complex.intCast_re,Complex.intCast_im,zero_mul,add_zero,Complex.one_im] at him
  exact (mul_pos (show 0<(γ 1 0:ℝ) by exact_mod_cast hc) z.im_pos).ne' him

/-- Weight two is a genuine simple pole when the lower-left entry is positive. -/
theorem meromorphicOrderAt_eisensteinConeRegularized_two (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) :
    meromorphicOrderAt (eisensteinConeRegularized γ z) 2= -1 := by
  apply order_neg_one_of_residue (meromorphicAt_eisensteinConeRegularized γ z 2) _ (eisensteinConeRegularized_residue_two γ z)
  exact div_ne_zero (Int.cast_ne_zero.mpr hc.ne') (denom_ne_zero (γ : GL (Fin 2) ℝ) z)

/-- The normalized cone series is analytic exactly away from its two simple poles. -/
theorem analyticAt_eisensteinConeRegularized_iff (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) (a : ℂ) :
    AnalyticAt ℂ (eisensteinConeRegularized γ z) a ↔ a≠1 ∧ a≠2 := by
  refine ⟨fun h => ⟨?_,?_⟩,fun h => analyticAt_eisensteinConeRegularized γ z hc h.1 h.2⟩
  · rintro rfl
    have H := h.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_eisensteinConeRegularized_one γ z hc] at H
    have he : ¬((0:WithTop ℤ)≤((-1:ℤ):WithTop ℤ)) := by exact_mod_cast (show ¬(0:ℤ)≤ -1 by decide)
    exact he H
  · rintro rfl
    have H := h.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_eisensteinConeRegularized_two γ z hc] at H
    have he : ¬((0:WithTop ℤ)≤((-1:ℤ):WithTop ℤ)) := by exact_mod_cast (show ¬(0:ℤ)≤ -1 by decide)
    exact he H

end AnalyticNumberTheory.ModularAndPartitions
