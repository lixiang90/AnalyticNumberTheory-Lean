import AnalyticNumberTheory.ModularAndPartitions.EisensteinLattice
import AnalyticNumberTheory.ModularAndPartitions.EisensteinLambert
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Analytic continuation of the complex-weight Eisenstein function

The reflection factor cancels the pole of zeta at weight one. The other
part of the Fourier expansion is entire by local uniform convergence
of the Lambert series.
-/

open Complex Real Set Filter
open scoped Topology UpperHalfPlane
namespace AnalyticNumberTheory.ModularAndPartitions

/-- The constant Fourier coefficient, with its removable value at weight one. -/
noncomputable def eisensteinConstant : ℂ→ℂ :=
  Function.update (fun s => (1+eisensteinReflection s)*riemannZeta s) 1 (-π*I)

private theorem reflection_deriv_one :
    HasDerivAt (fun s : ℂ => 1+eisensteinReflection s) (-π*I) 1 := by
  have H := (((hasDerivAt_id (1:ℂ)).const_mul ((π:ℂ)*I)).cexp).const_add (1:ℂ)
  convert H using 1 <;> simp [eisensteinReflection,Complex.exp_pi_mul_I] <;> ring

theorem differentiable_eisensteinConstant : Differentiable ℂ eisensteinConstant := by
  have hoff {s : ℂ} (hs : s≠1) : DifferentiableAt ℂ eisensteinConstant s := by
    apply ((show DifferentiableAt ℂ (fun s : ℂ => 1+eisensteinReflection s) s by
      unfold eisensteinReflection; fun_prop).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    simp [eisensteinConstant,Function.update_of_ne ht]
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · apply AnalyticAt.differentiableAt
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with t ht; exact hoff ht
    · rw [eisensteinConstant,continuousAt_update_same]
      have H := reflection_deriv_one.tendsto_slope.mul riemannZeta_residue_one
      rw [mul_one] at H
      apply H.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t≠1 := ht
      simp only [slope_def_field,eisensteinReflection,mul_one,Complex.exp_pi_mul_I,add_neg_cancel,
        sub_zero]
      field_simp [sub_ne_zero.mpr ht']
  · exact hoff hs

/-- The nome in the Eisenstein Fourier expansion. -/
noncomputable def eisensteinNome (z : ℂ) : ℂ := Complex.exp (2*π*I*z)

theorem norm_eisensteinNome_lt_one {z : ℂ} (hz : 0<z.im) : ‖eisensteinNome z‖<1 := by
  simpa only [eisensteinNome] using UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨z,hz⟩ : ℍ)

/-- The analytic continuation of the Eisenstein lattice sum. -/
noncomputable def eisensteinG (z s : ℂ) : ℂ :=
  eisensteinConstant s+(1+eisensteinReflection s)*(-2*π*I)^s*(Complex.Gamma s)⁻¹*
    eisensteinLambert (eisensteinNome z) s

/-- The continued Eisenstein function is entire in the weight. -/
theorem differentiable_eisensteinG_weight {z : ℂ} (hz : 0<z.im) :
    Differentiable ℂ (eisensteinG z) := by
  apply differentiable_eisensteinConstant.add
  apply Differentiable.mul _ (differentiable_eisensteinLambert_weight (norm_eisensteinNome_lt_one hz))
  apply Differentiable.mul _ Complex.differentiable_one_div_Gamma
  unfold eisensteinReflection
  have hn : -2*(π:ℂ)*I≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  apply Differentiable.mul (by fun_prop)
  exact differentiable_id.const_cpow (Or.inl hn)

/-- For each complex weight, the dependence on the upper half-plane is holomorphic. -/
theorem differentiableOn_eisensteinG_upperHalfPlane (s : ℂ) :
    DifferentiableOn ℂ (fun z => eisensteinG z s) {z | 0<z.im} := by
  intro z hz
  apply DifferentiableWithinAt.const_add
  apply DifferentiableWithinAt.const_mul
  exact (differentiableOn_eisensteinLambert_nome s).comp (by unfold eisensteinNome; fun_prop)
    (fun _ h => norm_eisensteinNome_lt_one h) z hz

/-- The connection with the absolutely convergent double lattice sum. -/
theorem eisensteinG_eq_latticeSum (z : ℍ) {s : ℂ} (hs : 2<s.re) :
    eisensteinG z s=eisensteinLatticeSum z s := by
  have hne : s≠1 := by intro h; simp [h] at hs
  rw [eisensteinG,eisensteinConstant,Function.update_of_ne hne,eisensteinLatticeSum_eq_upper_rows z hs,
    eisensteinLambert_eq_iterated (norm_eisensteinNome_lt_one z.im_pos),mul_add]
  congr 1
  have he (m : ℕ+) : (∑' n : ℤ,((m:ℂ)*(z:ℂ)+n)^(-s))=
      ((-2*π*I)^s/Complex.Gamma s)*∑' n : ℕ+,((n:ℕ):ℂ)^(s-1)*(eisensteinNome z)^(m*n:ℕ) := by
    have hm : 0<((m:ℕ):ℝ) := by exact_mod_cast m.2
    have H := AnalyticTools.lipschitz_summation (s:=s) (z:=(m:ℂ)*(z:ℂ)) (by linarith)
      (by simpa [Complex.mul_im] using mul_pos hm z.im_pos)
    apply H.trans
    congr 1
    apply tsum_congr; intro n
    rw [eisensteinNome,←Complex.exp_nat_mul]
    push_cast; ring_nf
  simp_rw [he]
  rw [tsum_mul_left]; ring

/-- At weight one the nonconstant Fourier terms vanish. -/
@[simp] theorem eisensteinG_one (z : ℂ) : eisensteinG z 1= -π*I := by
  simp [eisensteinG,eisensteinConstant,eisensteinReflection,Complex.exp_pi_mul_I]

end AnalyticNumberTheory.ModularAndPartitions
