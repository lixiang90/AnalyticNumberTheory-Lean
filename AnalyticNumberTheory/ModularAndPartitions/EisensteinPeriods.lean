import AnalyticNumberTheory.ModularAndPartitions.EisensteinBranches
import AnalyticNumberTheory.ModularAndPartitions.EisensteinIntegralWeights

/-!
# Periods of the complex-weight Eisenstein series

Multiplication by the modular denominator winds one sector of lattice
vectors across the logarithm cut. On the half-plane of convergence the
period is an absolutely convergent sum over that sector. After multiplication
by the winding factor it continues to an entire function of the weight.
-/

open Complex Real Matrix Set
open UpperHalfPlane hiding I
open scoped UpperHalfPlane MatrixGroups Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private def latticeAction (γ : SL(2,ℤ)) : (Fin 2→ℤ) ≃ (Fin 2→ℤ) where
  toFun v := v ᵥ* γ
  invFun v := v ᵥ* ↑(γ⁻¹)
  left_inv v := by
    have h := congrArg (fun g : SL(2,ℤ) => g.1) (mul_inv_cancel γ)
    change γ.1*(γ⁻¹).1=1 at h
    change (v ᵥ* γ.1) ᵥ* (γ⁻¹).1=v; rw [vecMul_vecMul,h,vecMul_one]
  right_inv v := by
    have h := congrArg (fun g : SL(2,ℤ) => g.1) (inv_mul_cancel γ)
    change (γ⁻¹).1*γ.1=1 at h
    change (v ᵥ* (γ⁻¹).1) ᵥ* γ.1=v; rw [vecMul_vecMul,h,vecMul_one]

private def latticeVector (z : ℍ) (v : Fin 2→ℤ) : ℂ := (v 0:ℂ)*z+v 1

private theorem denom_mul_latticeVector (γ : SL(2,ℤ)) (z : ℍ) (v : Fin 2→ℤ) :
    denom γ z*latticeVector (γ • z) v=latticeVector z (latticeAction γ v) := by
  change _=latticeVector z (v ᵥ* γ)
  have hn := denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have H := EisensteinSeries.eisSummand_SL2_apply (-1) v γ z
  norm_num only [EisensteinSeries.eisSummand,neg_neg,zpow_one,_root_.zpow_neg_one] at H
  unfold latticeVector; rw [H,←mul_assoc,mul_inv_cancel₀ hn,one_mul]

private theorem latticeSum_eq_vector (z : ℍ) {s : ℂ} (hs : s≠0) :
    eisensteinLatticeSum z s=∑' v : Fin 2→ℤ,eisensteinInversePower (latticeVector z v) s := by
  rw [eisensteinLatticeSum,←(finTwoArrowEquiv ℤ).tsum_eq (f:=fun v : ℤ×ℤ => eisensteinLatticeTerm z s v.1 v.2)]
  apply tsum_congr; intro v
  exact eisensteinLatticeTerm_eq_inversePower z hs _ _

private theorem summable_vector_inversePower (z : ℍ) {s : ℂ} (hs : 2<s.re) :
    Summable (fun v : Fin 2→ℤ => eisensteinInversePower (latticeVector z v) s) := by
  have hn : s≠0 := by intro h; norm_num [h] at hs
  apply ((finTwoArrowEquiv ℤ).summable_iff.mpr (summable_eisensteinLatticeTerm z hs)).congr
  intro v
  exact eisensteinLatticeTerm_eq_inversePower z hn _ _

/-- The sector of lattice vectors whose modular denominator crosses the
lower logarithm cut. The sum uses the vector after multiplication by the denominator. -/
noncomputable def eisensteinSectorSum (γ : SL(2,ℤ)) (z : ℍ) (s : ℂ) : ℂ :=
  ∑' v : Fin 2→ℤ, if eisensteinBranchCrossing (denom γ z) (latticeVector (γ • z) v)
    then eisensteinInversePower (latticeVector z (latticeAction γ v)) s else 0

/-- The entire continuation of the sector sum times its winding factor. -/
noncomputable def eisensteinPeriod (γ : SL(2,ℤ)) (z : ℍ) (s : ℂ) : ℂ :=
  (denom γ z)^(-s)*eisensteinG ((γ • z : ℍ):ℂ) s-eisensteinG z s

/-- The Eisenstein period is entire as a function of the complex weight. -/
theorem differentiable_eisensteinPeriod (γ : SL(2,ℤ)) (z : ℍ) :
    Differentiable ℂ (eisensteinPeriod γ z) := by
  apply Differentiable.sub _ (differentiable_eisensteinG_weight z.im_pos)
  apply Differentiable.mul _ (differentiable_eisensteinG_weight (γ • z).im_pos)
  exact differentiable_id.neg.const_cpow (Or.inl (denom_ne_zero _ _))

/-- The complex-weight modular transformation law on the half-plane of
absolute convergence, with its explicit sector and branch multiplier. -/
theorem eisensteinPeriod_eq_sector (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {s : ℂ} (hs : 2<s.re) :
    eisensteinPeriod γ z s=(Complex.exp (-2*π*I*s)-1)*eisensteinSectorSum γ z s := by
  let f (v : Fin 2→ℤ) := eisensteinInversePower (latticeVector z (latticeAction γ v)) s
  let U := {v : Fin 2→ℤ | eisensteinBranchCrossing (denom γ z) (latticeVector (γ • z) v)}
  let B := Complex.exp (-2*π*I*s)-1
  have hn : s≠0 := by intro h; norm_num [h] at hs
  have hj : 0<(denom γ z).im := by
    simpa [denom,Complex.mul_im] using mul_pos (Int.cast_pos.mpr hc : 0<(γ 1 0:ℝ)) z.im_pos
  have hf : Summable f := (summable_vector_inversePower z hs).comp_injective (latticeAction γ).injective
  have hU : Summable (U.indicator f) := hf.indicator _
  have hterm (v : Fin 2→ℤ) :
      (denom γ z)^(-s)*eisensteinInversePower (latticeVector (γ • z) v) s=f v+B*U.indicator f v := by
    rw [eisensteinInversePower_mul hj,denom_mul_latticeVector]
    change (if v∈U then _ else _)*f v=_
    by_cases h : v∈U
    · rw [if_pos h,indicator_of_mem h]; dsimp [B]; ring
    · rw [if_neg h,indicator_of_notMem h]; ring
  have he : (∑' v,f v)=eisensteinLatticeSum z s := by
    rw [latticeSum_eq_vector z hn]
    exact (latticeAction γ).tsum_eq (fun v => eisensteinInversePower (latticeVector z v) s)
  rw [eisensteinPeriod,eisensteinG_eq_latticeSum _ hs,eisensteinG_eq_latticeSum _ hs,
    latticeSum_eq_vector (γ • z) hn,←tsum_mul_left]
  simp_rw [hterm]
  rw [hf.tsum_add (hU.mul_left B),tsum_mul_left,he,add_sub_cancel_left]
  rfl

/-- The positive cone `k ≥ 0, c l > d k` in the coordinates of the
original lattice. It includes the positive real axis. -/
noncomputable def eisensteinConeSum (c d : ℤ) (z : ℍ) (s : ℂ) : ℂ :=
  ∑' v : Fin 2→ℤ,if 0≤v 0 ∧ d*v 0<c*v 1 then (latticeVector z v)^(-s) else 0

private theorem crossing_iff_indices (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0) (v : Fin 2→ℤ) :
    eisensteinBranchCrossing (denom γ z) (latticeVector (γ • z) v) ↔
      0<v 0 ∧ (latticeAction γ v) 0≤0 := by
  have hj : 0<(denom γ z).im := by
    simpa [denom,Complex.mul_im] using mul_pos (Int.cast_pos.mpr hc : 0<(γ 1 0:ℝ)) z.im_pos
  rw [eisensteinBranchCrossing_iff hj,denom_mul_latticeVector]
  have hi (u : ℍ) (w : Fin 2→ℤ) : (latticeVector u w).im=(w 0:ℝ)*u.im := by simp [latticeVector,Complex.mul_im]
  rw [hi,hi,mul_pos_iff_of_pos_right (γ • z).im_pos,Int.cast_pos]
  congr 1
  rw [←zero_mul z.im, mul_le_mul_iff_of_pos_right z.im_pos,Int.cast_nonpos]

private theorem sector_eq_positiveCone (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {s : ℂ} (hs : s≠0) :
    eisensteinSectorSum γ z s=eisensteinReflection s*eisensteinConeSum (γ 1 0) (γ 1 1) z s := by
  let E := (Equiv.neg (Fin 2→ℤ)).trans (latticeAction γ).symm
  have hE (v : Fin 2→ℤ) : latticeAction γ (E v) = -v := (latticeAction γ).apply_symm_apply _
  have hE0 (v : Fin 2→ℤ) : (E v) 0=γ 1 0*v 1-γ 1 1*v 0 := by
    change ((-v) ᵥ* (γ⁻¹).1) 0=_
    rw [SpecialLinearGroup.SL2_inv_expl]
    simp only [vecMul,dotProduct,Fin.sum_univ_two,Pi.neg_apply]
    change -(v 0)*(γ 1 1)+(-(v 1))*(-(γ 1 0))=_
    ring
  rw [eisensteinSectorSum,←E.tsum_eq,eisensteinConeSum,←tsum_mul_left]
  apply tsum_congr
  intro v
  rw [if_congr (crossing_iff_indices γ z hc (E v)) rfl rfl,hE0,hE]
  simp only [Pi.neg_apply,neg_nonpos]
  by_cases h : 0≤v 0 ∧ γ 1 1*v 0 < γ 1 0*v 1
  · rw [if_pos ⟨sub_pos.mpr h.2,h.1⟩,if_pos h]
    have hpow := (eisensteinLatticeTerm_eq_inversePower z hs (-(v 0)) (-(v 1))).symm
    change eisensteinInversePower ((-(v 0):ℤ)*((z:ℂ))+(-(v 1):ℤ)) s=_
    rw [hpow,eisensteinLatticeTerm]
    have h0 : ¬(-(v 0)=0 ∧ -(v 1)=0) := by
      rintro ⟨a,b⟩; simp only [neg_eq_zero] at a b
      have := h.2; simp [a,b] at this
    have h1 : ¬(0< -(v 0) ∨ -(v 0)=0 ∧ 0< -(v 1)) := by
      rintro (p|⟨p,q⟩)
      · omega
      · have ha : v 0=0 := by omega
        have hb := h.2; rw [ha,mul_zero] at hb
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hc.le (by omega : v 1≤0))) hb
    rw [if_neg h0,if_neg h1]
    unfold latticeVector; push_cast; ring_nf
  · rw [if_neg (by rintro ⟨p,q⟩; exact h ⟨q,sub_pos.mp p⟩),if_neg h,mul_zero]

/-- Explicit modular transformation for `Re s>2`. The arithmetic cone
has ordinary linear inequalities in the two integer coordinates. -/
theorem eisensteinPeriod_eq_cone (γ : SL(2,ℤ)) (z : ℍ) (hc : 0<γ 1 0)
    {s : ℂ} (hs : 2<s.re) :
    eisensteinPeriod γ z s=(Complex.exp (-π*I*s)-Complex.exp (π*I*s))*
      eisensteinConeSum (γ 1 0) (γ 1 1) z s := by
  rw [eisensteinPeriod_eq_sector γ z hc hs,sector_eq_positiveCone γ z hc (by intro h; norm_num [h] at hs),
    ←mul_assoc]
  congr 1
  rw [sub_mul,eisensteinReflection,←Complex.exp_add,one_mul]
  congr 2; ring

end AnalyticNumberTheory.ModularAndPartitions
